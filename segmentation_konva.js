(function () {
    "use strict";

    let stage, imageLayer, annotationLayer, transformer;
    let bgImage = null;
    let originalWidth = 0;
    let originalHeight = 0;
    let currentZoom = 1.0;
    let currentTool = 'select';
    let isDrawing = false;
    let drawingShape = null;
    let shapeStartPoint = null;
    let polygonPoints = [];
    let polygonRedoStack = [];
    let polygonActiveLine = null;
    let isDrawingPolygon = false; // Separate flag for polygon – stays true while drawing, unaffected by mouseUp
    let activeDrawingCircles = [];
    let clipboardNodes = [];
    const BRAND_COLOR = "#1d55e8";

    let defaultMaskOpacity = 0.5;
    let brushSize = 30;
    let lastBrushPos = null;  // Tracks last brush/eraser position for shift+click straight lines

    // ── Live Timer ──────────────────────────────────────────────────────────
    let taskTimerInterval = null;
    let hasTaskStarted = false;

    let imgFilterState = {
        brightness: 100,
        contrast: 100,
        saturation: 100
    };

    let lastPersistedState = null;

    // Undo/Redo stacks
    let historyStack = [];
    let redoStack = [];
    const MAX_HISTORY = 30;
    let shouldPersistUndoRedoState = true;
    const TOOL_STORAGE_NAMESPACE = 'segmentation';
    let cachedCoverage = 0.00;
    let isCalculatingCoverage = false;
    let coverageDebounceTimeout = null;
    window.IS_LOADING_STATE = false;

    let saveSocket = null;
    let isSocketConnected = false;

    function initSaveWebSocket() {
        const taskId = window.SEGMENTATION_CONFIG.taskId;
        if (!taskId) return;
        const wsProtocol = window.location.protocol === "https:" ? "wss:" : "ws:";
        const wsUrl = `${wsProtocol}//${window.location.host}/ws/task/${taskId}/save-mask/`;
        
        saveSocket = new WebSocket(wsUrl);
        
        saveSocket.onopen = () => {
            isSocketConnected = true;
            console.log('Save WebSocket connected');
        };
        
        saveSocket.onclose = () => {
            isSocketConnected = false;
            setTimeout(initSaveWebSocket, 3000); // Reconnect
        };
        
        saveSocket.onmessage = (e) => {
            const data = JSON.parse(e.data);
            const statusEl = document.getElementById('saveStatus');
            window.isSaving = false;
            
            if (data.status === 'success' || data.success) {
                window.hasUnsavedChanges = false;
                if (statusEl) {
                    statusEl.innerHTML = '<i class="bi bi-check-circle"></i> Saved';
                    statusEl.classList.add('text-success', 'text-muted');
                    statusEl.classList.remove('text-warning', 'text-danger');
                    
                    if (window.saveStatusTimeout) {
                        clearTimeout(window.saveStatusTimeout);
                    }
                    window.saveStatusTimeout = setTimeout(() => {
                        const el = document.getElementById('saveStatus');
                        if (el && !window.isSaving) {
                            el.innerHTML = 'Live Session';
                            el.className = 'text-primary';
                        }
                    }, 3000);
                }
            } else {
                if (statusEl) {
                    statusEl.innerHTML = '<i class="bi bi-x-circle"></i> Failed to save';
                    statusEl.classList.add('text-danger');
                    statusEl.classList.remove('text-success', 'text-warning', 'text-muted');
                }
            }
        };
    }

    function flashButtonState(btnId) {
        const btn = document.getElementById(btnId);
        if (!btn) return;
        btn.classList.add('active');
        setTimeout(() => {
            btn.classList.remove('active');
        }, 150);
    }

    function formatCoverage(pct) {
        const complete = pct >= 100;
        const display = complete ? 100 : Math.min(99.99, Math.floor(pct * 100) / 100);
        return display.toFixed(2);
    }

    const MAX_PROCESS_SIZE = 4096;
    const MASK_SUPERSAMPLE = 2; // render masks at up to 2x image resolution so
    // edges aren't a chunky staircase when zoomed in

    function getProcessingScale(width, height) {
        return Math.min(
            MAX_PROCESS_SIZE / width,
            MAX_PROCESS_SIZE / height,
            1
        );
    }

    /**
     * Returns the lock state that a newly drawn shape should inherit for a
     * given dataset (label). If any existing sibling of the same label is
     * already unlocked (locked === false), the new shape should also start
     * unlocked so the user's intended state is preserved.
     */
    function getDatasetLockState(datasetId) {
        if (!datasetId || !annotationLayer) return true;
        const siblings = annotationLayer.getChildren().filter(o =>
            o !== transformer &&
            String(o.getAttr('datasetId')) === String(datasetId) &&
            o.visible() !== false &&
            !o.getAttr('isUndoSubtractor')
        );
        // If any existing sibling is explicitly unlocked, inherit that state.
        if (siblings.some(o => o.getAttr('locked') === false)) return false;
        return true; // default: locked
    }

    // Higher-resolution scale used only when rasterizing masks for display, so
    // polygon/circle edges stay crisp (no jagged zig-zag) when zoomed in —
    // without any imageSmoothing blur. Capped so the canvas never exceeds
    // MAX_PROCESS_SIZE in either dimension.
    function getMaskRenderScale(width, height) {
        return Math.min(
            MAX_PROCESS_SIZE / width,
            MAX_PROCESS_SIZE / height,
            MASK_SUPERSAMPLE
        );
    }

    // ── VECTOR ERASE ─────────────────────────────────────────────────────────
    // Vector shapes (polygon/circle/rect) keep an `_eraserPaths` list and use a
    // custom sceneFunc that draws the shape, then punches the eraser strokes with
    // destination-out. Because these shapes have fill+stroke and opacity < 1,
    // Konva renders them through an isolated buffer canvas, so the destination-out
    // only affects this shape — and it stays a crisp vector at every zoom level
    // (no rasterized mask, no zig-zag).

    // Punch a node's own `_eraserPaths` holes directly onto `ctx`, assuming `ctx`
    // is already in the node's local (untransformed) coordinate frame — i.e. the
    // same frame used by node.points()/radiusX()/etc. No x/y offset is applied.
    function punchEraserHolesLocal(ctx, node) {
        const erasers = node.getAttr('_eraserPaths');
        if (!erasers || !erasers.length) return;
        ctx.save();
        ctx.globalCompositeOperation = 'destination-out';
        ctx.strokeStyle = 'rgba(0,0,0,1)';
        ctx.fillStyle = 'rgba(0,0,0,1)';
        ctx.lineCap = 'round';
        ctx.lineJoin = 'round';
        erasers.forEach(ep => {
            const pts = ep.points;
            if (!pts || pts.length < 2) return;
            const lw = ep.strokeWidth || 1;
            if (pts.length === 2) {
                ctx.beginPath();
                ctx.arc(pts[0], pts[1], lw / 2, 0, Math.PI * 2);
                ctx.fill();
            } else {
                ctx.beginPath();
                ctx.moveTo(pts[0], pts[1]);
                for (let i = 2; i < pts.length; i += 2) ctx.lineTo(pts[i], pts[i + 1]);
                ctx.lineWidth = lw;
                ctx.stroke();
            }
        });
        ctx.restore();
    }

    function drawEraserHoles(context, shape) {
        punchEraserHolesLocal(context._context, shape);
    }

    // Punch `subNode`'s pristine vector geometry as a destination-out hole
    // directly onto `ctx` (crisp at any zoom — no raster resampling), then
    // restore whatever pixels `subNode`'s OWN `_eraserPaths` had erased, so an
    // already-erased part of a locked shape doesn't keep clipping whatever
    // it's subtracted from. `ctx` must already be positioned/scaled so that
    // drawing at (offsetX, offsetY) with scale (scaleX, scaleY) reproduces
    // subNode's own local-frame geometry (radiusX/Y, width/height, points()).
    // The restore step works at ctx.canvas's native pixel resolution (no
    // intermediate small canvas), so it never needs to be stretched either.
    function punchSubtractorHole(ctx, subNode, offsetX = 0, offsetY = 0, scaleX = 1, scaleY = 1) {
        const cls = subNode.getClassName();
        const erasers = subNode.getAttr('_eraserPaths');
        const hasOwnHoles = !!(erasers && erasers.length);

        let snapshot = null;
        if (hasOwnHoles && cls !== 'Image') {
            snapshot = document.createElement('canvas');
            snapshot.width = ctx.canvas.width;
            snapshot.height = ctx.canvas.height;
            snapshot.getContext('2d').drawImage(ctx.canvas, 0, 0);
        }

        ctx.save();
        ctx.translate(offsetX, offsetY);
        if (scaleX !== 1 || scaleY !== 1) ctx.scale(scaleX, scaleY);

        if (cls === 'Ellipse') {
            ctx.beginPath();
            ctx.ellipse(0, 0, subNode.radiusX() || 0, subNode.radiusY() || 0, 0, 0, Math.PI * 2);
            ctx.closePath();
            ctx.fill();
        } else if (cls === 'Rect') {
            ctx.beginPath();
            ctx.rect(0, 0, subNode.width() || 0, subNode.height() || 0);
            ctx.closePath();
            ctx.fill();
        } else if (cls === 'Line') {
            const pts = subNode.points();
            if (pts && pts.length >= 2) {
                ctx.beginPath();
                ctx.moveTo(pts[0], pts[1]);
                for (let i = 2; i < pts.length; i += 2) ctx.lineTo(pts[i], pts[i + 1]);
                if (subNode.closed()) {
                    ctx.closePath();
                    ctx.fill();
                    ctx.lineWidth = 1;
                    ctx.stroke();
                } else if (subNode.strokeWidth()) {
                    ctx.lineWidth = subNode.strokeWidth() || 1;
                    ctx.lineCap = subNode.lineCap() || 'round';
                    ctx.lineJoin = subNode.lineJoin() || 'round';
                    ctx.stroke();
                }
            }
        } else if (cls === 'Image') {
            const imgEl = subNode.image();
            if (imgEl) ctx.drawImage(imgEl, 0, 0, subNode.width(), subNode.height());
        }

        if (hasOwnHoles && snapshot && typeof ctx.getTransform === 'function') {
            // Build, at ctx.canvas's native resolution, a copy of the pre-punch
            // pixels masked down to just the erased-hole stroke areas, then
            // composite that back — restoring exactly what the erase removed.
            const restore = document.createElement('canvas');
            restore.width = ctx.canvas.width;
            restore.height = ctx.canvas.height;
            const rctx = restore.getContext('2d');
            rctx.drawImage(snapshot, 0, 0);
            rctx.globalCompositeOperation = 'destination-in';
            rctx.fillStyle = 'rgba(0,0,0,1)';
            rctx.strokeStyle = 'rgba(0,0,0,1)';
            rctx.lineCap = 'round';
            rctx.lineJoin = 'round';
            rctx.setTransform(ctx.getTransform());
            erasers.forEach(ep => {
                const pts = ep.points;
                if (!pts || pts.length < 2) return;
                const lw = ep.strokeWidth || 1;
                if (pts.length === 2) {
                    rctx.beginPath();
                    rctx.arc(pts[0], pts[1], lw / 2, 0, Math.PI * 2);
                    rctx.fill();
                } else {
                    rctx.beginPath();
                    rctx.moveTo(pts[0], pts[1]);
                    for (let i = 2; i < pts.length; i += 2) rctx.lineTo(pts[i], pts[i + 1]);
                    rctx.lineWidth = lw;
                    rctx.stroke();
                }
            });

            ctx.save();
            ctx.setTransform(1, 0, 0, 1, 0, 0);
            ctx.globalCompositeOperation = 'source-over';
            ctx.drawImage(restore, 0, 0);
            ctx.restore();
        }

        ctx.restore();
    }

    function drawSubtractorNodes(context, shape) {
        const subtractorIds = shape.getAttr('_subtractorNodes');
        if (!subtractorIds || !subtractorIds.length) return;

        const layer = shape.getLayer();
        if (!layer) return;

        const ctx = context._context;
        ctx.save();

        // Convert coordinates from shape's local space to layer space
        const inv = shape.getTransform().copy().invert();
        ctx.transform(inv.m[0], inv.m[1], inv.m[2], inv.m[3], inv.m[4], inv.m[5]);

        ctx.globalCompositeOperation = 'destination-out';
        ctx.fillStyle = 'rgba(0,0,0,1)';
        ctx.strokeStyle = 'rgba(0,0,0,1)';

        subtractorIds.forEach(id => {
            const subNode = layer.findOne('#' + id);
            if (!subNode) return;

            ctx.save();
            const subT = subNode.getTransform();
            ctx.transform(subT.m[0], subT.m[1], subT.m[2], subT.m[3], subT.m[4], subT.m[5]);
            // ctx is now in subNode's own local frame (its transform is fully
            // applied), so punch/restore at (0,0) with no extra scale.
            punchSubtractorHole(ctx, subNode, 0, 0, 1, 1);
            ctx.restore();
        });

        ctx.restore();
    }

    const ERASABLE_SCENE_FUNCS = {
        Ellipse: function (context, shape) {
            context.beginPath();
            context.ellipse(0, 0, shape.radiusX(), shape.radiusY(), 0, 0, Math.PI * 2, false);
            context.closePath();
            context.fillStrokeShape(shape);
            drawEraserHoles(context, shape);
            drawSubtractorNodes(context, shape);
        },
        Rect: function (context, shape) {
            context.beginPath();
            context.rect(0, 0, shape.width(), shape.height());
            context.closePath();
            context.fillStrokeShape(shape);
            drawEraserHoles(context, shape);
            drawSubtractorNodes(context, shape);
        },
        Line: function (context, shape) {
            const pts = shape.points();
            if (pts.length >= 2) {
                context.beginPath();
                context.moveTo(pts[0], pts[1]);
                for (let i = 2; i < pts.length; i += 2) context.lineTo(pts[i], pts[i + 1]);
                if (shape.closed()) context.closePath();
            }
            context.fillStrokeShape(shape);
            drawEraserHoles(context, shape);
            drawSubtractorNodes(context, shape);
        }
    };

    // A vector shape eligible for vector-erase (polygon/circle/rect/brush).
    function isVectorBoundaryShape(node) {
        const cls = node.getClassName();
        return (cls === 'Ellipse' || cls === 'Rect' || cls === 'Line') &&
            node.getAttr('datasetId') !== 'eraser' &&
            !!node.getAttr('labelName');
    }

    // Place a newly drawn annotation just below the transformer so newer shapes
    // render above older ones (last-drawn = highest z-index among shapes).
    function addAnnotationShape(shape) {
        annotationLayer.add(shape);
        if (transformer && transformer.getParent() === annotationLayer) {
            transformer.moveToTop();
        }
    }

    // Punch eraser holes (destination-out) for a vector shape onto an already
    // scaled 2d context, in IMAGE coordinates (eraser points are stored in the
    // shape's local space). Used for export/rasterization (renderNodesToCanvas).
    function punchEraserHolesImageSpace(ctx, node) {
        const erasers = node.getAttr('_eraserPaths');
        if (!erasers || !erasers.length) return;
        const ox = node.x() || 0;
        const oy = node.y() || 0;
        const sx = node.scaleX() || 1;
        const sy = node.scaleY() || 1;
        ctx.save();
        ctx.globalCompositeOperation = 'destination-out';
        ctx.strokeStyle = 'rgba(0,0,0,1)';
        ctx.fillStyle = 'rgba(0,0,0,1)';
        ctx.lineCap = 'round';
        ctx.lineJoin = 'round';
        erasers.forEach(ep => {
            const pts = ep.points;
            if (!pts || pts.length < 2) return;
            const lw = (ep.strokeWidth || 1) * sx;
            if (pts.length === 2) {
                ctx.beginPath();
                ctx.arc(ox + pts[0] * sx, oy + pts[1] * sy, lw / 2, 0, Math.PI * 2);
                ctx.fill();
            } else {
                ctx.beginPath();
                ctx.moveTo(ox + pts[0] * sx, oy + pts[1] * sy);
                for (let i = 2; i < pts.length; i += 2) {
                    ctx.lineTo(ox + pts[i] * sx, oy + pts[i + 1] * sy);
                }
                ctx.lineWidth = lw;
                ctx.stroke();
            }
        });
        ctx.restore();
    }

    // Attach the hole-punching sceneFunc so existing eraser paths render.
    function makeShapeErasable(shape) {
        if (!shape.getAttr('_eraserPaths')) shape.setAttr('_eraserPaths', []);
        if (!shape.getAttr('_subtractorNodes')) shape.setAttr('_subtractorNodes', []);
        const fn = ERASABLE_SCENE_FUNCS[shape.getClassName()];
        if (fn) shape.sceneFunc(fn);
        // Force rendering through an isolated buffer canvas so the eraser's
        // destination-out only affects THIS shape (not other shapes below it),
        // regardless of the shape's opacity.
        shape._useBufferCanvas = function () { return true; };
    }

    // Append an eraser stroke (in image/layer coords) to every overlapping vector
    // shape, converted into that shape's local coordinates. Returns true if at
    // least one vector shape was affected.
    function eraseVectorShapes(eraserPath) {
        if (!eraserPath) return false;
        const eraserBox = eraserPath.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
        const eraserPts = eraserPath.points();
        const eraserStroke = eraserPath.strokeWidth() || 1;

        let affected = false;
        annotationLayer.getChildren().forEach(node => {
            if (node === transformer || node === eraserPath) return;
            if (node.getAttr('locked')) return;
            if (!isVectorBoundaryShape(node)) return;

            const box = node.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
            const intersects = !(eraserBox.x > box.x + box.width ||
                eraserBox.x + eraserBox.width < box.x ||
                eraserBox.y > box.y + box.height ||
                eraserBox.y + eraserBox.height < box.y);
            if (!intersects) return;

            // Convert eraser points (layer coords) to the shape's local coords.
            const inv = node.getTransform().copy().invert();
            const localPts = [];
            for (let i = 0; i < eraserPts.length; i += 2) {
                const p = inv.point({ x: eraserPts[i], y: eraserPts[i + 1] });
                localPts.push(p.x, p.y);
            }
            const scaleX = node.scaleX() || 1;
            const list = node.getAttr('_eraserPaths') || [];
            list.push({ points: localPts, strokeWidth: eraserStroke / scaleX });
            node.setAttr('_eraserPaths', list);
            makeShapeErasable(node);
            affected = true;
        });

        return affected;
    }

    function detectCanvasLimit() {
        const canvas = document.createElement('canvas');
        try {
            canvas.width = 8192;
            canvas.height = 8192;
            canvas.getContext('2d').fillRect(0, 0, 1, 1);
            return true;
        } catch (e) {
            return false;
        }
    }

    // Setup functions
    function initKonva() {
        Konva.pixelRatio = 1;

        const container = document.getElementById('konva-container');
        if (!container) return;

        if (!detectCanvasLimit()) {
            Swal.fire({
                icon: "warning",
                title: "Large Image Warning",
                text: "Your browser/GPU may have difficulty rendering high-resolution canvases. Performance could be degraded.",
                confirmButtonColor: BRAND_COLOR
            });
        }

        const width = container.clientWidth || 800;
        const height = container.clientHeight || 600;

        stage = new Konva.Stage({
            container: 'konva-container',
            width: width,
            height: height,
        });

        imageLayer = new Konva.Layer();
        annotationLayer = new Konva.Layer();

        annotationLayer.on('beforeDraw', function () {
            const ctx = annotationLayer.getContext()._context;
            if (ctx) {
                ctx.imageSmoothingEnabled = false;
                ctx.webkitImageSmoothingEnabled = false;
                ctx.mozImageSmoothingEnabled = false;
                ctx.msImageSmoothingEnabled = false;
            }

            // Seal gaps between adjacent shapes with 1px same-color stroke
            annotationLayer.getChildren().forEach(node => {
                if (isVectorBoundaryShape(node) && !node.getAttr('isBrushStroke')) {
                    const fillColor = node.fill();
                    const isPolygon = node.getClassName() === 'Line' && node.closed();
                    const sealWidth = isPolygon ? 2 : 1;  // 2 px for polygons, 1 px for rects/circles
                    
                    if (node.strokeWidth() !== sealWidth) {
                        node.strokeWidth(sealWidth);
                    }
                    if (node.stroke() !== fillColor) {
                        node.stroke(fillColor);
                    }
                }
            });
        });

        stage.add(imageLayer);
        stage.add(annotationLayer);
        
        // Apply opacity via CSS so shapes can be 100% opaque internally (prevents darker overlaps)
        if (annotationLayer.getCanvas() && annotationLayer.getCanvas()._canvas) {
            annotationLayer.getCanvas()._canvas.style.opacity = defaultMaskOpacity;
        }

        transformer = new Konva.Transformer({
            borderEnabled: false,
            enabledAnchors: [],
            rotateEnabled: false,
        });
        annotationLayer.add(transformer);

        const imageUrl = window.SEGMENTATION_CONFIG.imageUrl;
        const loaderEl = document.getElementById('loader');
        const loaderTextEl = loaderEl ? loaderEl.querySelector('span') : null;

        function setLoaderProgress(pct) {
            if (!loaderTextEl) return;
            loaderTextEl.textContent = (pct === null) ? 'Loading...' : `Loading... ${pct}%`;
        }

        function hideImageLoader() {
            if (loaderEl) loaderEl.style.display = 'none';
        }

        // Called with the full-resolution source (ImageBitmap or HTMLImageElement).
        // Always the uploaded image at its real pixel dimensions — no blurry
        // placeholder is ever shown, only the actual image once it's ready.
        function onImageSourceReady(source) {
            originalWidth  = source.width;
            originalHeight = source.height;

            // Restrict all annotations to stay strictly within the image boundaries
            annotationLayer.clip({
                x: 0,
                y: 0,
                width: originalWidth,
                height: originalHeight
            });

            bgImage = new Konva.Image({
                x: 0,
                y: 0,
                image: source,
                width: originalWidth,
                height: originalHeight,
            });
            imageLayer.add(bgImage);
            imageLayer.batchDraw();

            // Center image & fit to screen
            resetZoom();

            const minDimension = Math.min(originalWidth, originalHeight);
            const dynamicMax = Math.max(50, Math.floor(minDimension / 5));
            const dynamicDefault = Math.max(2, Math.floor(minDimension / 35));

            const brushSlider = document.getElementById('brushSlider');
            if (brushSlider) {
                brushSlider.max = dynamicMax;
                brushSlider.value = dynamicDefault;
            }

            if (window.setBrushSize) {
                window.setBrushSize(dynamicDefault);
            }

            // Load initial saved state
            const persistedUndoRedo = getPreferredRestoreSnapshot();
            window.IS_LOADING_STATE = true;
            if (persistedUndoRedo && persistedUndoRedo.currentState) {
                const parsed = JSON.parse(persistedUndoRedo.currentState);
                historyStack = persistedUndoRedo.historyStack.slice();
                redoStack = persistedUndoRedo.redoStack.slice();
                loadSavedState(parsed).then(() => {
                    window.IS_LOADING_STATE = false;
                });
            } else {
                loadSavedState().then(() => {
                    window.IS_LOADING_STATE = false;
                });
            }

            // Start the live session timer after the image is ready
            startLiveTimer();
            injectCoverageUI();
            updateCoverageDisplay();
        }

        // Single full-quality decode, off the main thread via createImageBitmap.
        // The download is streamed (not buffered via res.blob()) purely so the
        // loader can show real percentage progress instead of sitting frozen —
        // the image itself is never downscaled or shown at reduced quality.
        const imageLoadStartedAt = new Date();
        const imageLoadStartMark = performance.now();
        console.log(`[image-load] start ${imageLoadStartedAt.toLocaleTimeString()} — ${imageUrl}`);

        fetch(imageUrl)
            .then(function (res) {
                if (!res.ok) throw new Error('fetch ' + res.status);

                const total = parseInt(res.headers.get('Content-Length') || '0', 10);
                if (!res.body || !total) return res.blob();

                const reader = res.body.getReader();
                const chunks = [];
                let received = 0;

                return new Promise(function (resolve, reject) {
                    function pump() {
                        reader.read().then(function (result) {
                            if (result.done) {
                                resolve(new Blob(chunks));
                                return;
                            }
                            chunks.push(result.value);
                            received += result.value.length;
                            setLoaderProgress(Math.min(99, Math.round((received / total) * 100)));
                            pump();
                        }).catch(reject);
                    }
                    pump();
                });
            })
            .then(function (blob) {
                return createImageBitmap(blob);
            })
            .then(function (bitmap) {
                logImageLoadFinished();
                hideImageLoader();
                onImageSourceReady(bitmap);
            })
            .catch(function () {
                // Fallback for browsers without createImageBitmap (old Safari etc.)
                const img = new Image();
                img.onload = function () {
                    logImageLoadFinished();
                    hideImageLoader();
                    onImageSourceReady(img);
                };
                img.src = imageUrl;
            });

        function logImageLoadFinished() {
            const endedAt = new Date();
            const seconds = ((performance.now() - imageLoadStartMark) / 1000).toFixed(2);
            console.log(`[image-load] end ${endedAt.toLocaleTimeString()} — took ${seconds}s`);
        }

        // Bind events
        setupStageEvents();
        setupKeyboardShortcuts();
    }

    const DOT_CURSOR = "url('data:image/svg+xml;utf8," + encodeURIComponent(
        '<svg xmlns="http://www.w3.org/2000/svg" width="10" height="10">' +
        '<circle cx="5" cy="5" r="3" fill="black" stroke="white" stroke-width="1"/>' +
        '</svg>'
    ) + "') 5 5, auto";

    function updateCursor() {
        if (!stage) return;
        const container = stage.container();
        if (currentTool === 'select') {
            container.style.cursor = 'default';
        } else if (currentTool === 'brush' || currentTool === 'eraser') {
            container.style.cursor = DOT_CURSOR;
        } else if (currentTool === 'paint') {
            container.style.cursor = 'cell';
        } else {
            container.style.cursor = 'crosshair';
        }
    }

    function setupStageEvents() {
        // Zoom on wheel
        stage.on('wheel', function (e) {
            e.evt.preventDefault();
            const oldScale = stage.scaleX();
            const pointer = stage.getPointerPosition();
            if (!pointer) return;

            const mousePointTo = {
                x: (pointer.x - stage.x()) / oldScale,
                y: (pointer.y - stage.y()) / oldScale,
            };

            const zoomSpeed = 1.1;
            let newScale = e.evt.deltaY > 0 ? oldScale / zoomSpeed : oldScale * zoomSpeed;

            // Restrict zoom limits
            newScale = Math.max(0.05, Math.min(100, newScale));

            stage.scale({ x: newScale, y: newScale });

            const newPos = {
                x: pointer.x - mousePointTo.x * newScale,
                y: pointer.y - mousePointTo.y * newScale,
            };
            stage.position(newPos);
            stage.batchDraw();

            currentZoom = newScale;
            updateZoomDisplay();
            updateCursor();
        });

        // Dragging & Alt dragging
        let isDraggingStage = false;
        let lastPos = { x: 0, y: 0 };

        stage.on('mousedown', function (e) {
            const evt = e.evt;
            const isMiddleMouse = evt.button === 1;
            const isAltDrag = evt.altKey;

            if (isMiddleMouse || isAltDrag) {
                isDraggingStage = true;
                lastPos = { x: evt.clientX, y: evt.clientY };
                stage.container().style.cursor = 'grabbing';
                return;
            }

            // Drawing Tool Down
            if (isDraggingStage) return;
            handleDrawingMouseDown(e);
        });

        stage.on('mousemove', function (e) {
            const evt = e.evt;
            if (isDraggingStage) {
                const dx = evt.clientX - lastPos.x;
                const dy = evt.clientY - lastPos.y;
                stage.position({
                    x: stage.x() + dx,
                    y: stage.y() + dy
                });
                stage.batchDraw();
                lastPos = { x: evt.clientX, y: evt.clientY };
                return;
            }

            handleDrawingMouseMove(e);
            updateFloatingLabel();
        });

        stage.on('mouseup', function (e) {
            if (isDraggingStage) {
                isDraggingStage = false;
                updateCursor();
                return;
            }

            // Track last brush/eraser position for shift+click straight line
            if (currentTool === 'brush' || currentTool === 'eraser') {
                const relPtr = getRelativePointerPosition();
                if (relPtr) {
                    lastBrushPos = {
                        x: Math.max(0, Math.min(originalWidth, relPtr.x)),
                        y: Math.max(0, Math.min(originalHeight, relPtr.y))
                    };
                }
            }

            handleDrawingMouseUp();
        });

        // Selection & Deselection Click Handler
        stage.on('click tap', function (e) {
            if (['rect', 'circle', 'polygon', 'magic', 'brush', 'eraser', 'paint'].includes(currentTool)) {
                return;
            }

            // Clicked empty space
            if (e.target === stage || e.target === bgImage) {
                transformer.nodes([]);
                const panel = document.getElementById('attributePanel');
                if (panel) panel.style.display = 'none';
                annotationLayer.batchDraw();
                updateOpacitySliderFromSelection();
                updateLayerList();
                updateFloatingLabel();
                return;
            }

            // Clicked shape in annotationLayer
            if (e.target.getLayer() === annotationLayer && e.target !== transformer) {
                const shape = e.target;
                if (shape.getAttr('locked')) {
                    return;
                }

                transformer.nodes([shape]);

                if (window.renderAttributeForm) {
                    window.renderAttributeForm(shape.attrs);
                }

                annotationLayer.batchDraw();
                updateOpacitySliderFromSelection();
                updateLayerList();
                updateFloatingLabel();
            }
        });

        // Track drag & transform end for undo-redo history and autosave
        stage.on('dragend', function (e) {
            if (e.target.getLayer() === annotationLayer && e.target !== transformer) {
                saveHistory();
                triggerAutoSave();
                updateLayerList();
            }
        });

        transformer.on('transformend', function () {
            saveHistory();
            triggerAutoSave();
            updateLayerList();
        });

        stage.on('dragmove transform wheel', function () {
            updateFloatingLabel();
        });

        transformer.on('transform dragmove', function () {
            updateFloatingLabel();
        });
    }

    function handleDrawingMouseDown(e) {
        if (currentTool === 'select') return;

        if (!window.CURRENT_LABEL || window.CURRENT_LABEL.id === null || window.CURRENT_LABEL.id === undefined) {
            if (['rect', 'circle', 'polygon', 'magic', 'brush', 'paint'].includes(currentTool)) {
                Swal.fire({
                    title: 'No Label Selected',
                    text: 'Please select a label from the label picker menu first!',
                    icon: 'warning',
                    confirmButtonColor: '#1d55e8'
                });
                return;
            }
        }

        const relativePointer = getRelativePointerPosition();
        if (!relativePointer) return;

        let x = relativePointer.x;
        let y = relativePointer.y;

        if (['brush', 'eraser', 'paint'].includes(currentTool)) {
            if (x < 0 || x > originalWidth || y < 0 || y > originalHeight) return;
        } else {
            x = Math.max(0, Math.min(originalWidth, x));
            y = Math.max(0, Math.min(originalHeight, y));
        }

        if (['rect', 'circle', 'polygon'].includes(currentTool) && e.evt.shiftKey) {
            runSAMShape(x, y, currentTool);
            return;
        }

        if (currentTool === 'rect') {
            saveHistory();
            isDrawing = true;
            shapeStartPoint = { x, y };

            drawingShape = new Konva.Rect({
                x: x,
                y: y,
                width: 0,
                height: 0,
                fill: window.CURRENT_LABEL.color,
                opacity: 1.0,
                stroke: window.CURRENT_LABEL.color,
                strokeWidth: 2,
                strokeScaleEnabled: false,
                draggable: false,
            });
            drawingShape.setAttr('labelName', window.CURRENT_LABEL.name);
            drawingShape.setAttr('labelColor', window.CURRENT_LABEL.color);
            drawingShape.setAttr('datasetId', window.CURRENT_LABEL.id);
            drawingShape.setAttr('id', `shape_${Date.now()}`);
            drawingShape.setAttr('locked', getDatasetLockState(window.CURRENT_LABEL.id));
            drawingShape.setAttr('isBoundary', true);

            addAnnotationShape(drawingShape);
            annotationLayer.batchDraw();
        } else if (currentTool === 'circle') {
            saveHistory();
            isDrawing = true;
            shapeStartPoint = { x, y };

            drawingShape = new Konva.Ellipse({
                x: x,
                y: y,
                radiusX: 0,
                radiusY: 0,
                fill: window.CURRENT_LABEL.color,
                opacity: 1.0,
                stroke: window.CURRENT_LABEL.color,
                strokeWidth: 2,
                strokeScaleEnabled: false,
                draggable: false,
            });
            drawingShape.setAttr('labelName', window.CURRENT_LABEL.name);
            drawingShape.setAttr('labelColor', window.CURRENT_LABEL.color);
            drawingShape.setAttr('datasetId', window.CURRENT_LABEL.id);
            drawingShape.setAttr('id', `shape_${Date.now()}`);
            drawingShape.setAttr('locked', getDatasetLockState(window.CURRENT_LABEL.id));
            drawingShape.setAttr('isBoundary', true);

            addAnnotationShape(drawingShape);
            annotationLayer.batchDraw();
        } else if (currentTool === 'polygon') {
            // Only save history on the FIRST point (matches legacy segmentation_tool.js behaviour).
            // Saving on every click would pollute the undo stack, causing Ctrl+Z to restore
            // entire canvas snapshots instead of removing individual polygon points.
            if (polygonPoints.length === 0) {
                saveHistory();
                isDrawingPolygon = true;
            }
            polygonPoints.push(x, y);
            polygonRedoStack = []; // new click invalidates redo
            if (!polygonActiveLine) {
                polygonActiveLine = new Konva.Line({
                    points: [...polygonPoints, x, y],
                    stroke: window.CURRENT_LABEL.color,
                    strokeWidth: 2,
                    strokeScaleEnabled: false,
                    closed: false,
                });
                addAnnotationShape(polygonActiveLine);
            } else {
                polygonActiveLine.points([...polygonPoints, x, y]);
            }
            updateActiveDrawingCircles(polygonPoints, window.CURRENT_LABEL.color);
            annotationLayer.batchDraw();
        } else if (currentTool === 'magic') {
            runSAMMagic(Math.round(x), Math.round(y));
        } else if (currentTool === 'brush' || currentTool === 'eraser') {
            if (currentTool === 'brush' && (!window.CURRENT_LABEL || !window.CURRENT_LABEL.color || window.CURRENT_LABEL.id === null || window.CURRENT_LABEL.id === undefined)) {
                Swal.fire({
                    title: 'No Label Selected',
                    text: 'Please select a label from the label picker menu first!',
                    icon: 'warning',
                    confirmButtonColor: '#1d55e8'
                });
                return;
            }
            const relativePointer = getRelativePointerPosition();
            if (!relativePointer) return;
            const sx = Math.max(0, Math.min(originalWidth, relativePointer.x));
            const sy = Math.max(0, Math.min(originalHeight, relativePointer.y));

            // ── SHIFT + CLICK: draw a straight line from last brush position ──
            if (e.evt && e.evt.shiftKey && lastBrushPos) {
                saveHistory();

                const color = currentTool === 'brush' ? window.CURRENT_LABEL.color : 'rgba(0,0,0,1)';
                const compOp = currentTool === 'brush' ? 'source-over' : 'destination-out';

                const straightLine = new Konva.Line({
                    points: [lastBrushPos.x, lastBrushPos.y, sx, sy],
                    stroke: color,
                    strokeWidth: brushSize / stage.scaleX(),
                    lineCap: 'round',
                    lineJoin: 'round',
                    globalCompositeOperation: compOp,
                    opacity: 1.0,
                    draggable: false,
                });

                straightLine.setAttr('labelName', currentTool === 'brush' ? window.CURRENT_LABEL.name : 'Eraser');
                straightLine.setAttr('labelColor', currentTool === 'brush' ? window.CURRENT_LABEL.color : 'rgba(0,0,0,1)');
                straightLine.setAttr('datasetId', currentTool === 'brush' ? window.CURRENT_LABEL.id : 'eraser');
                straightLine.setAttr('id', `shape_${Date.now()}`);
                straightLine.setAttr('isBrushStroke', true);
                if (currentTool === 'brush') {
                    straightLine.setAttr('locked', getDatasetLockState(window.CURRENT_LABEL.id));
                }

                if (currentTool === 'eraser') {
                    annotationLayer.add(straightLine);
                    straightLine.moveToTop();
                } else {
                    addAnnotationShape(straightLine);
                }
                annotationLayer.batchDraw();

                lastBrushPos = { x: sx, y: sy };

                // Immediately finalize the straight stroke
                if (currentTool === 'eraser') {
                    eraseVectorShapes(straightLine);
                    applyEraserToMasks(straightLine);
                } else {
                    const datasetId = straightLine.getAttr('datasetId');
                    applyLockedLayerClipping(straightLine, function () {
                        if (datasetId) mergeLabelBrushStrokes(datasetId);
                        updateLayerList();
                        triggerAutoSave();
                    });
                }
                return;
            }

            // Normal brush stroke start
            saveHistory();
            isDrawing = true;
            shapeStartPoint = { x: sx, y: sy };

            const color = currentTool === 'brush' ? window.CURRENT_LABEL.color : 'rgba(0,0,0,1)';
            const compOp = currentTool === 'brush' ? 'source-over' : 'destination-out';

            drawingShape = new Konva.Line({
                points: [sx, sy, sx, sy],
                stroke: color,
                strokeWidth: brushSize / stage.scaleX(),
                lineCap: 'round',
                lineJoin: 'round',
                globalCompositeOperation: compOp,
                opacity: 1.0,
                draggable: false,
            });

            drawingShape.setAttr('labelName', currentTool === 'brush' ? window.CURRENT_LABEL.name : 'Eraser');
            drawingShape.setAttr('labelColor', currentTool === 'brush' ? window.CURRENT_LABEL.color : 'rgba(0,0,0,1)');
            drawingShape.setAttr('datasetId', currentTool === 'brush' ? window.CURRENT_LABEL.id : 'eraser');
            drawingShape.setAttr('id', `shape_${Date.now()}`);
            drawingShape.setAttr('isBrushStroke', true);
            if (currentTool === 'eraser') {
                drawingShape.setAttr('isEraser', true);
            }
            if (currentTool === 'brush') {
                drawingShape.setAttr('locked', getDatasetLockState(window.CURRENT_LABEL.id));
            }
            if (currentTool === 'eraser') {
                annotationLayer.add(drawingShape);
                drawingShape.moveToTop();
            } else {
                addAnnotationShape(drawingShape);
            }
            annotationLayer.batchDraw();
        } else if (currentTool === 'paint') {
            if (!window.CURRENT_LABEL || !window.CURRENT_LABEL.color || window.CURRENT_LABEL.id === null || window.CURRENT_LABEL.id === undefined) {
                Swal.fire({
                    title: 'No Label Selected',
                    text: 'Please select a label from the label picker menu first!',
                    icon: 'warning',
                    confirmButtonColor: '#1d55e8'
                });
                return;
            }
            saveHistory();
            const fillColor = window.CURRENT_LABEL.color;
            performFloodFill(Math.round(x), Math.round(y), fillColor);
        }
    }

    function handleDrawingMouseMove(e) {
        if (!isDrawing || !drawingShape) {
            // Update temporary polygon stretch line
            if (currentTool === 'polygon' && polygonActiveLine) {
                const relativePointer = getRelativePointerPosition();
                if (relativePointer) {
                    const x = Math.max(0, Math.min(originalWidth, relativePointer.x));
                    const y = Math.max(0, Math.min(originalHeight, relativePointer.y));

                    if (e.evt && e.evt.buttons === 1) {
                        if (polygonPoints.length >= 2) {
                            const lastX = polygonPoints[polygonPoints.length - 2];
                            const lastY = polygonPoints[polygonPoints.length - 1];
                            const dist = Math.sqrt(Math.pow(lastX - x, 2) + Math.pow(lastY - y, 2));
                            if (dist > 5) {
                                polygonPoints.push(x, y);
                                polygonRedoStack = [];
                            }
                        }
                    }
                    polygonActiveLine.points([...polygonPoints, x, y]);
                    annotationLayer.batchDraw();
                }
            }
            return;
        }

        const relativePointer = getRelativePointerPosition();
        if (!relativePointer) return;

        let x = relativePointer.x;
        let y = relativePointer.y;

        if (['brush', 'eraser'].includes(currentTool)) {
            if (x < 0 || x > originalWidth || y < 0 || y > originalHeight) return;
        } else {
            x = Math.max(0, Math.min(originalWidth, x));
            y = Math.max(0, Math.min(originalHeight, y));
        }

        if (currentTool === 'rect') {
            const width = x - shapeStartPoint.x;
            const height = y - shapeStartPoint.y;
            drawingShape.width(Math.abs(width));
            drawingShape.height(Math.abs(height));
            drawingShape.x(width > 0 ? shapeStartPoint.x : x);
            drawingShape.y(height > 0 ? shapeStartPoint.y : y);
        } else if (currentTool === 'circle') {
            const rx = Math.abs(x - shapeStartPoint.x) / 2;
            const ry = Math.abs(y - shapeStartPoint.y) / 2;
            drawingShape.x(Math.min(x, shapeStartPoint.x) + rx);
            drawingShape.y(Math.min(y, shapeStartPoint.y) + ry);
            drawingShape.radiusX(rx);
            drawingShape.radiusY(ry);
        } else if (currentTool === 'brush' || currentTool === 'eraser') {
            const pts = drawingShape.points();
            if (pts.length >= 2) {
                const lastX = pts[pts.length - 2];
                const lastY = pts[pts.length - 1];
                // Only add a point if mouse moved at least 2 pixels (dist^2 < 4)
                if (Math.pow(lastX - x, 2) + Math.pow(lastY - y, 2) < 4) {
                    return;
                }
            }
            drawingShape.points(pts.concat([x, y]));
        }
        annotationLayer.batchDraw();
    }

    function handleDrawingMouseUp() {
        if (!isDrawing) return;
        isDrawing = false;

        const finishedShape = drawingShape;

        // Cleanup values or make them positive
        if (currentTool === 'rect' && finishedShape) {
            if (finishedShape.width() === 0 || finishedShape.height() === 0) {
                finishedShape.destroy();
                drawingShape = null;
                shapeStartPoint = null;
                annotationLayer.batchDraw();
                return;
            }
        } else if (currentTool === 'circle' && finishedShape) {
            if (finishedShape.radiusX() === 0 || finishedShape.radiusY() === 0) {
                finishedShape.destroy();
                drawingShape = null;
                shapeStartPoint = null;
                annotationLayer.batchDraw();
                return;
            }
        }

        // ── BRUSH CLOSED STROKE DETECTION ──────────────────────────────────
        // Mirror segmentation_tool.js: if the stroke's start and end points
        // are closer than max(30, brushSize*1.5) pixels, fill the closed path.
        if ((currentTool === 'brush') && finishedShape && finishedShape.getAttr('isBrushStroke')) {
            const pts = finishedShape.points();
            if (pts.length >= 4) {
                const startX = pts[0], startY = pts[1];
                const endX = pts[pts.length - 2], endY = pts[pts.length - 1];
                const dist = Math.sqrt(Math.pow(startX - endX, 2) + Math.pow(startY - endY, 2));
                const threshold = Math.max(30, brushSize * 1.5);
                if (dist < threshold) {
                    // Close the path by adding fill color
                    finishedShape.closed(true);
                    finishedShape.fill(window.CURRENT_LABEL ? window.CURRENT_LABEL.color : finishedShape.stroke());
                }
            }
        }

        drawingShape = null;
        shapeStartPoint = null;
        annotationLayer.batchDraw();

        if (finishedShape && currentTool === 'eraser') {
            // Vector shapes get the eraser punched as a vector hole (stays crisp);
            // raster masks (brush/SAM) are handled by applyEraserToMasks.
            eraseVectorShapes(finishedShape);
            applyEraserToMasks(finishedShape);
        } else if (finishedShape && ['rect', 'circle', 'brush'].includes(currentTool)) {
            // Keep rect/circle/brush as smooth vector shapes (NOT rasterized masks) so
            // their edges stay crisp at any zoom level — like Dataloop. They are
            // serialized/exported as vectors via getMetadata / renderNodesToCanvas.
            makeShapeErasable(finishedShape);  // enable vector (hole-punch) erasing
            applyLockedLayerClipping(finishedShape, function () {
                updateLayerList();
                triggerAutoSave();
            });
        } else {
            updateLayerList();
            triggerAutoSave();
        }
    }

    function getRelativePointerPosition() {
        const pointer = stage.getPointerPosition();
        if (!pointer) return null;
        return {
            x: (pointer.x - stage.x()) / stage.scaleX(),
            y: (pointer.y - stage.y()) / stage.scaleY(),
        };
    }

    // Tools handling
    window.setTool = function (tool) {
        // Tools outside the project's configured tool set (and the 'select' cursor tool,
        // which is always available) are a no-op — this gates both toolbar clicks and
        // keyboard shortcuts through one choke point.
        if (tool !== 'select' && Array.isArray(window.ENABLED_TOOLS) && window.ENABLED_TOOLS.length && !window.ENABLED_TOOLS.includes(tool)) {
            return;
        }

        currentTool = tool;
        lastBrushPos = null; // reset straight-line anchor on every tool switch
        updateCursor();

        // Trigger lazy task-start on the very first tool interaction
        startTaskOnce();

        // Close polygon if switching tools
        if (tool !== 'polygon' && polygonPoints.length > 0) {
            finishPolygon();
        }

        polygonRedoStack = [];
        updateActiveDrawingCircles([]);

        // Clear active selection if not in select tool
        if (tool !== 'select' && transformer) {
            transformer.nodes([]);
            const panel = document.getElementById('attributePanel');
            if (panel) panel.style.display = 'none';
            annotationLayer.batchDraw();
        }

        // Highlight toolbar button in UI
        const TOOL_IDS = ['btn-select', 'btn-magic', 'btn-brush', 'btn-paint', 'btn-rect', 'btn-circle', 'btn-polygon', 'btn-eraser'];
        TOOL_IDS.forEach(id => {
            const btn = document.getElementById(id);
            if (btn) btn.classList.remove('active');
        });
        const activeBtn = document.getElementById(`btn-${tool}`);
        if (activeBtn) activeBtn.classList.add('active');
    };

    window.updateToolbarState = function () {
        const hasLabel = !!window.CURRENT_LABEL;
        const toolsNeedingLabel = [
            'btn-brush',
            'btn-rect',
            'btn-circle',
            'btn-polygon',
            'btn-paint',
            'btn-magic'
        ];

        toolsNeedingLabel.forEach(btnId => {
            const btn = document.getElementById(btnId);
            if (!btn) return;

            if (!hasLabel) {
                btn.style.opacity = '0.4';
                btn.style.cursor = 'not-allowed';
                btn.setAttribute('data-disabled', 'true');
            } else {
                btn.style.opacity = '1';
                btn.style.cursor = 'pointer';
                btn.removeAttribute('data-disabled');
            }
        });
    };

    window.updateBrushColor = function (color) {
        if (!window.CURRENT_LABEL) {
            window.CURRENT_LABEL = { name: '', color: color, id: null, attributes: {} };
        } else {
            window.CURRENT_LABEL.color = color;
        }
        window.updateToolbarState();
    };

    function updateActiveDrawingCircles(points, color) {
        activeDrawingCircles.forEach(c => c.destroy());
        activeDrawingCircles = [];
        if (!points || !points.length) return;

        const r = 3.5 / (stage ? (stage.scaleX() || 1) : 1);

        for (let i = 0; i < points.length; i += 2) {
            const circle = new Konva.Circle({
                x: points[i],
                y: points[i + 1],
                radius: r,
                fill: '#ffffff',
                stroke: color || BRAND_COLOR,
                strokeWidth: 1.5,
                strokeScaleEnabled: false,
                listening: false,
                excludeFromExport: true
            });
            annotationLayer.add(circle);
            activeDrawingCircles.push(circle);
        }
    }

    function finishPolygon() {
        isDrawingPolygon = false; // polygon drawing is done

        if (polygonPoints.length < 6) {
            if (polygonActiveLine) polygonActiveLine.destroy();
            polygonPoints = [];
            polygonActiveLine = null;
            updateActiveDrawingCircles([]);
            annotationLayer.batchDraw();
            return;
        }

        saveHistory();
        if (polygonActiveLine) polygonActiveLine.destroy();

        const polygon = new Konva.Line({
            points: polygonPoints,
            fill: window.CURRENT_LABEL.color,
            opacity: 1.0,
            stroke: window.CURRENT_LABEL.color,
            strokeWidth: 2,
            strokeScaleEnabled: false,
            closed: true,
        });

        polygon.setAttr('labelName', window.CURRENT_LABEL.name);
        polygon.setAttr('labelColor', window.CURRENT_LABEL.color);
        polygon.setAttr('datasetId', window.CURRENT_LABEL.id);
        polygon.setAttr('id', `shape_${Date.now()}`);
        polygon.setAttr('locked', getDatasetLockState(window.CURRENT_LABEL.id));
        polygon.setAttr('isBoundary', true);

        addAnnotationShape(polygon);
        annotationLayer.batchDraw();

        polygonPoints = [];
        polygonRedoStack = [];
        polygonActiveLine = null;
        updateActiveDrawingCircles([]);

        // Keep the polygon as a smooth vector shape (NOT a rasterized mask) so
        // its edges stay crisp at any zoom — like Dataloop. It is serialized and
        // exported as a vector via getMetadata / renderNodesToCanvas.
        makeShapeErasable(polygon);  // enable vector (hole-punch) erasing
        applyLockedLayerClipping(polygon, function () {
            updateLayerList();
            triggerAutoSave();
        });
    }

    function traceContourMoore(grid, width, height) {
        let startX = -1, startY = -1;
        for (let y = 0; y < height; y++) {
            for (let x = 0; x < width; x++) {
                if (grid[y * width + x] === 1) {
                    startX = x;
                    startY = y;
                    break;
                }
            }
            if (startX !== -1) break;
        }

        if (startX === -1) return [];

        const points = [];
        let cx = startX;
        let cy = startY;

        const dx = [0, 1, 1, 1, 0, -1, -1, -1];
        const dy = [-1, -1, 0, 1, 1, 1, 0, -1];
        let backtrackDir = 6;

        let nextX = cx;
        let nextY = cy;
        let iterations = 0;
        const maxIterations = width * height * 4;

        points.push({ x: cx, y: cy });

        while (iterations < maxIterations) {
            iterations++;
            let foundNext = false;
            let checkDir = (backtrackDir + 1) % 8;

            for (let i = 0; i < 8; i++) {
                const nx = cx + dx[checkDir];
                const ny = cy + dy[checkDir];

                if (nx >= 0 && nx < width && ny >= 0 && ny < height) {
                    if (grid[ny * width + nx] === 1) {
                        nextX = nx;
                        nextY = ny;
                        backtrackDir = (checkDir + 4) % 8;
                        foundNext = true;
                        break;
                    }
                }
                checkDir = (checkDir + 1) % 8;
            }

            if (!foundNext) break;
            if (nextX === startX && nextY === startY) break;

            points.push({ x: nextX, y: nextY });
            cx = nextX;
            cy = nextY;
        }

        return points;
    }

    function traceMaskToPoints(base64Mask, serverBbox, callback) {
        const img = new Image();
        img.onload = function () {
            const tempCanvas = document.createElement('canvas');
            tempCanvas.width = img.naturalWidth;
            tempCanvas.height = img.naturalHeight;
            const tempCtx = tempCanvas.getContext('2d', { willReadFrequently: true });
            tempCtx.drawImage(img, 0, 0);

            const objW = tempCanvas.width;
            const objH = tempCanvas.height;
            const imageData = tempCtx.getImageData(0, 0, objW, objH);
            const data = imageData.data;

            const grid = new Uint8Array(objW * objH);
            for (let y = 0; y < objH; y++) {
                for (let x = 0; x < objW; x++) {
                    grid[y * objW + x] = data[(y * objW + x) * 4] > 10 ? 1 : 0;
                }
            }

            const contourPoints = traceContourMoore(grid, objW, objH);

            if (contourPoints.length < 2) {
                callback(null);
                return;
            }

            const scaleX = serverBbox[2] / objW;
            const scaleY = serverBbox[3] / objH;

            const offsetX = serverBbox[0];
            const offsetY = serverBbox[1];
            const absolutePoints = contourPoints.map(p => ({
                x: p.x * scaleX + offsetX,
                y: p.y * scaleY + offsetY
            }));

            const simplifiedPoints = simplifyPoints(absolutePoints, 1.5);
            callback(simplifiedPoints);
        };
        img.src = base64Mask;
    }

    async function runSAMShape(x, y, shapeType) {
        if (isNaN(x) || isNaN(y)) {
            Swal.fire({ title: 'Error', text: 'Invalid click coordinates.', icon: 'error' });
            return;
        }

        const taskId = window.SEGMENTATION_CONFIG.taskId;
        const label = window.CURRENT_LABEL;
        if (!label || label.id === null || label.id === undefined) {
            Swal.fire({ title: 'No Label Selected', text: 'Please select a label from the dataset list first!', icon: 'warning', confirmButtonColor: BRAND_COLOR });
            window.setTool('select');
            return;
        }

        const labelColor = label.color;
        const labelName = label.name;

        const loader = document.getElementById('sam-loader');
        if (loader) loader.style.display = 'flex';

        try {
            const response = await fetch(`/api/segmenter/task/${taskId}/pre-segment/?x=${x}&y=${y}`);
            const data = await response.json();

            if (data.status === 'success') {
                const serverBbox = Array.isArray(data.bbox) && data.bbox.length === 4 ? data.bbox : null;

                if (!serverBbox) {
                    if (loader) loader.style.display = 'none';
                    Swal.fire({ title: 'Server out of sync', text: 'The annotation server returned a mask without a bbox. Restart the dev server and try again.', icon: 'warning' });
                    return;
                }

                const createAndAddShape = (shapeObj) => {
                    addAnnotationShape(shapeObj);
                    annotationLayer.batchDraw();

                    applyLockedLayerClipping(shapeObj, function () {
                        if (window.updateLayerList) window.updateLayerList();
                        if (loader) $(loader).fadeOut(300);
                        saveHistory();
                        triggerAutoSave();
                        window.setTool(currentTool);
                        mergeLabelBrushStrokes(label.id);
                    });
                };

                const commonProps = {
                    id: `shape_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`,
                    fill: labelColor,
                    stroke: labelColor,
                    strokeWidth: 0,
                    draggable: false,
                    opacity: 1.0,
                    labelName: labelName,
                    labelColor: labelColor,
                    datasetId: label.id,
                    attributes: label.attributes || {},
                    locked: true,
                    isBoundary: true,
                    erasable: true
                };

                if (shapeType === 'rect') {
                    const rect = new Konva.Rect({
                        ...commonProps,
                        x: serverBbox[0],
                        y: serverBbox[1],
                        width: serverBbox[2],
                        height: serverBbox[3]
                    });
                    createAndAddShape(rect);
                } else if (shapeType === 'circle') {
                    const ellipse = new Konva.Ellipse({
                        ...commonProps,
                        x: serverBbox[0] + serverBbox[2] / 2,
                        y: serverBbox[1] + serverBbox[3] / 2,
                        radiusX: serverBbox[2] / 2,
                        radiusY: serverBbox[3] / 2
                    });
                    createAndAddShape(ellipse);
                } else if (shapeType === 'polygon') {
                    const base64Mask = `data:image/png;base64,${data.mask}`;
                    traceMaskToPoints(base64Mask, serverBbox, function (points) {
                        if (!points || points.length < 2) {
                            if (loader) loader.style.display = 'none';
                            Swal.fire('Trace Failed', 'Failed to trace the boundaries from SAM mask.', 'warning');
                            return;
                        }

                        const flattenedPoints = [];
                        points.forEach(p => {
                            flattenedPoints.push(p.x, p.y);
                        });

                        const shapeObj = new Konva.Line({
                            ...commonProps,
                            points: flattenedPoints,
                            closed: true
                        });
                        createAndAddShape(shapeObj);
                    });
                }
            } else {
                throw new Error(data.message || "AI failed to find an object.");
            }
        } catch (error) {
            if (loader) loader.style.display = 'none';
            Swal.fire({ title: 'Error', text: error.message || 'AI Model failed.', icon: 'error' });
        }
    }

    // SAM Magic tool integration
    async function runSAMMagic(x, y) {
        const label = window.CURRENT_LABEL;
        if (!label || label.id === null || label.id === undefined) {
            Swal.fire({ title: 'No Label Selected', text: 'Please select a label from the dataset list first!', icon: 'warning', confirmButtonColor: BRAND_COLOR });
            window.setTool('select');
            return;
        }
        const taskId = window.SEGMENTATION_CONFIG.taskId;
        const labelColor = label.color;
        const labelName = label.name;

        const loader = document.getElementById('sam-loader');
        if (loader) loader.style.display = 'flex';

        try {
            const response = await fetch(`/api/segmenter/task/${taskId}/pre-segment/?x=${x}&y=${y}`);
            const data = await response.json();

            if (data.status === 'success') {
                const base64Mask = `data:image/png;base64,${data.mask}`;
                const serverBbox = data.bbox;

                const img = new Image();
                img.onload = function () {
                    saveHistory();

                    traceMaskToPoints(base64Mask, serverBbox, function (points) {
                        if (!points || points.length < 2) {
                            if (loader) $(loader).fadeOut(300);
                            Swal.fire('Trace Failed', 'Failed to trace the boundaries from SAM mask.', 'warning');
                            return;
                        }

                        const flattenedPoints = [];
                        points.forEach(p => {
                            flattenedPoints.push(p.x, p.y);
                        });

                        const maskNode = new Konva.Line({
                            points: flattenedPoints,
                            closed: true,
                            fill: labelColor,
                            stroke: labelColor,
                            strokeWidth: 0,
                            opacity: 1.0,
                            draggable: false,
                            labelName: labelName,
                            labelColor: labelColor,
                            datasetId: window.CURRENT_LABEL.id,
                            attributes: window.CURRENT_LABEL.attributes || {},
                            id: `shape_${Date.now()}`,
                            isBoundary: true,
                            locked: true,
                            erasable: true
                        });

                        addAnnotationShape(maskNode);
                        annotationLayer.batchDraw();

                        if (loader) $(loader).fadeOut(300);

                        const datasetId = window.CURRENT_LABEL.id;
                        applyLockedLayerClipping(maskNode, function () {
                            if (datasetId) mergeLabelBrushStrokes(datasetId);
                            updateLayerList();
                            triggerAutoSave();
                        });
                    });
                };
                img.src = base64Mask;
            } else {
                if (loader) $(loader).fadeOut(300);
                Swal.fire('SAM Error', data.message || 'AI segmentation failed.', 'error');
            }
        } catch (e) {
            if (loader) $(loader).fadeOut(300);
            console.error(e);
        }
    }

    function hexToRgb(hex) {
        const shorthandRegex = /^#?([a-f\d])([a-f\d])([a-f\d])$/i;
        hex = hex.replace(shorthandRegex, (m, r, g, b) => r + r + g + g + b + b);
        const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
        return result ? {
            r: parseInt(result[1], 16),
            g: parseInt(result[2], 16),
            b: parseInt(result[3], 16)
        } : null;
    }

    function performFloodFill(startX, startY, colorHex) {
        const w = originalWidth;
        const h = originalHeight;

        if (!w || !h) {
            console.error("Original dimensions not found. Cannot fill.");
            return;
        }

        try {
            const scale = getProcessingScale(w, h);
            const scaledW = Math.floor(w * scale) || 1;
            const scaledH = Math.floor(h * scale) || 1;
            const scaledStartX = Math.round(startX * scale);
            const scaledStartY = Math.round(startY * scale);

            if (scaledStartX < 0 || scaledStartY < 0 || scaledStartX >= scaledW || scaledStartY >= scaledH) return;

            // In Konva, we filter visible annotation nodes to snapshot them
            const visibleNodes = annotationLayer.getChildren().filter(node => node !== transformer && node.visible());

            // Render all visible masks to an offscreen canvas at scaled scale
            const snapshotCanvas = renderNodesToCanvas(visibleNodes, w, h, scale);
            const ctx = snapshotCanvas.getContext('2d', { willReadFrequently: true });
            const imageData = ctx.getImageData(0, 0, scaledW, scaledH);
            const data = imageData.data;

            const getIdx = (x, y) => (y * scaledW + x) * 4;
            const startIdx = getIdx(scaledStartX, scaledStartY);
            const targetR = data[startIdx];
            const targetG = data[startIdx + 1];
            const targetB = data[startIdx + 2];
            const targetA = data[startIdx + 3];

            const fillRGB = hexToRgb(colorHex);
            if (!fillRGB) return;

            // Early exit if clicking on essentially the same color
            if (
                Math.abs(targetR - fillRGB.r) < 5 &&
                Math.abs(targetG - fillRGB.g) < 5 &&
                Math.abs(targetB - fillRGB.b) < 5 &&
                targetA > 200
            ) return;

            const maskCanvas = document.createElement('canvas');
            maskCanvas.width = scaledW;
            maskCanvas.height = scaledH;
            const maskCtx = maskCanvas.getContext('2d');
            const maskImgData = maskCtx.createImageData(scaledW, scaledH);
            const maskData = maskImgData.data;

            const stack = [[scaledStartX, scaledStartY]];
            const seen = new Uint8Array(scaledW * scaledH);
            let minX = scaledW, minY = scaledH, maxX = 0, maxY = 0;
            let filled = 0;

            // Tolerance configuration
            const COLOR_TOLERANCE = 50;      // Base RGB tolerance
            const ALPHA_TOLERANCE = 100;     // Base alpha tolerance
            const EDGE_COLOR_TOLERANCE = 80; // Wider tolerance for anti-aliased edges
            const EDGE_ALPHA_THRESHOLD = 255;// Fill any pixel that isn't fully opaque

            while (stack.length) {
                const [x, y] = stack.pop();
                if (x < 0 || y < 0 || x >= scaledW || y >= scaledH) continue;

                const key = y * scaledW + x;
                if (seen[key]) continue;
                seen[key] = 1;

                const i = getIdx(x, y);
                const r = data[i], g = data[i + 1], b = data[i + 2], a = data[i + 3];

                let shouldFill = false;

                if (targetA < 20) {
                    // We clicked on a transparent/empty area.
                    // Fill all non-fully-opaque pixels to capture anti-aliased edges.
                    shouldFill = a < EDGE_ALPHA_THRESHOLD;
                } else {
                    // We clicked on a solid-ish area.
                    // Use standard tolerance, but be more lenient with low-alpha pixels
                    // that are likely anti-aliased boundaries.
                    const colorDiff = Math.abs(r - targetR) + Math.abs(g - targetG) + Math.abs(b - targetB);
                    const alphaDiff = Math.abs(a - targetA);

                    if (a < 250 && colorDiff < EDGE_COLOR_TOLERANCE && a > 0) {
                        // Anti-aliased edge pixel: fill it even if alpha differs significantly
                        shouldFill = true;
                    } else {
                        shouldFill = colorDiff < COLOR_TOLERANCE && alphaDiff < ALPHA_TOLERANCE;
                    }
                }

                if (!shouldFill) continue;

                maskData[i] = fillRGB.r;
                maskData[i + 1] = fillRGB.g;
                maskData[i + 2] = fillRGB.b;
                maskData[i + 3] = 255;

                filled++;
                minX = Math.min(minX, x);
                minY = Math.min(minY, y);
                maxX = Math.max(maxX, x);
                maxY = Math.max(maxY, y);

                stack.push([x + 1, y], [x - 1, y], [x, y + 1], [x, y - 1]);
            }

            if (!filled) return;

            // ── MORPHOLOGICAL CLOSING: dilate then erode ─────────────
            // After flood fill, before cropping — dilate by 1 pixel
            function dilateMask(visited, data, scaledW, scaledH, targetId) {
                const dilated = new Uint16Array(visited);
                for (let y = 1; y < scaledH - 1; y++) {
                    for (let x = 1; x < scaledW - 1; x++) {
                        const idx = y * scaledW + x;
                        if (visited[idx] === targetId) {
                            // Spread to neighbors
                            const neighbors = [idx - 1, idx + 1, idx - scaledW, idx + scaledW];
                            neighbors.forEach(ni => {
                                if (visited[ni] === 0 && data[ni * 4 + 3] > 0) {
                                    dilated[ni] = targetId;
                                }
                            });
                        }
                    }
                }
                return dilated;
            }

            function erodeMask(imgData, width, height, radius) {
                const src = new Uint8ClampedArray(imgData.data);
                const dst = imgData.data;
                for (let y = 0; y < height; y++) {
                    for (let x = 0; x < width; x++) {
                        const i = (y * width + x) * 4 + 3;
                        if (src[i] > 0) {
                            let allNeighbors = true;
                            for (let dy = -radius; dy <= radius && allNeighbors; dy++) {
                                for (let dx = -radius; dx <= radius && allNeighbors; dx++) {
                                    const ny = y + dy, nx = x + dx;
                                    if (ny >= 0 && ny < height && nx >= 0 && nx < width) {
                                        if (src[(ny * width + nx) * 4 + 3] === 0) {
                                            allNeighbors = false;
                                        }
                                    }
                                }
                            }
                            if (!allNeighbors) {
                                dst[i] = 0;
                                dst[i - 3] = 0;
                                dst[i - 2] = 0;
                                dst[i - 1] = 0;
                            }
                        }
                    }
                }
            }

            // dilateMask(maskImgData, scaledW, scaledH, 1);
            // erodeMask(maskImgData, scaledW, scaledH, 1);

            // Vector Trace: Extract a binary grid from the alpha channel
            const grid = new Uint8Array(scaledW * scaledH);
            for (let y = 0; y < scaledH; y++) {
                for (let x = 0; x < scaledW; x++) {
                    grid[y * scaledW + x] = maskData[(y * scaledW + x) * 4 + 3] > 10 ? 1 : 0;
                }
            }

            // Trace the outer boundary using the Moore Neighborhood algorithm
            const contourPoints = traceContourMoore(grid, scaledW, scaledH);
            
            if (!contourPoints || contourPoints.length < 2) return;

            // Scale the points back to original absolute coordinates
            const absolutePoints = contourPoints.map(p => ({
                x: p.x / scale,
                y: p.y / scale
            }));

            // Simplify to reduce the number of vertices and make the polygon smooth
            const simplifiedPoints = simplifyPoints(absolutePoints, 1.5);
            
            const flattenedPoints = [];
            simplifiedPoints.forEach(p => {
                flattenedPoints.push(p.x, p.y);
            });

            const shapeObj = new Konva.Line({
                points: flattenedPoints,
                closed: true,
                fill: window.CURRENT_LABEL.color,
                stroke: window.CURRENT_LABEL.color,
                strokeWidth: 0,
                opacity: 1.0,
                draggable: false,
                labelName: window.CURRENT_LABEL.name,
                labelColor: window.CURRENT_LABEL.color,
                datasetId: window.CURRENT_LABEL.id,
                attributes: window.CURRENT_LABEL.attributes || {},
                id: `shape_${Date.now()}`,
                isBoundary: true, // Marking it as a vector boundary like other tools
                locked: true,
                erasable: true
            });

            addAnnotationShape(shapeObj);

            applyLockedLayerClipping(shapeObj, function () {
                mergeLabelBrushStrokes(window.CURRENT_LABEL.id);
                annotationLayer.batchDraw();
                if (window.updateLayerList) updateLayerList();
                triggerAutoSave();
            });
        } catch (err) {
            console.error("Error in performFloodFill:", err);
        }
    }



    // Zooming
    window.resetZoom = function () {
        const container = document.getElementById('konva-container');
        if (!container || !originalWidth || !originalHeight) return;

        const containerWidth = container.clientWidth;
        const containerHeight = container.clientHeight;

        const scaleX = containerWidth / originalWidth;
        const scaleY = containerHeight / originalHeight;
        const scale = Math.min(scaleX, scaleY) * 0.9;

        stage.scale({ x: scale, y: scale });
        stage.position({
            x: (containerWidth - originalWidth * scale) / 2,
            y: (containerHeight - originalHeight * scale) / 2,
        });
        stage.batchDraw();

        currentZoom = scale;
        updateZoomDisplay();
        updateCursor();
    };

    window.changeZoom = function (delta) {
        const factor = delta > 0 ? 1.1 : 0.9;
        const newZoom = Math.max(0.05, Math.min(100, currentZoom * factor));

        stage.scale({ x: newZoom, y: newZoom });
        stage.batchDraw();

        currentZoom = newZoom;
        updateZoomDisplay();
        updateCursor();
    };

    function updateZoomDisplay() {
        const zoomDisplay = document.getElementById("zoomDisplay");
        if (zoomDisplay) {
            zoomDisplay.innerText = Math.round(currentZoom * 100) + "%";
        }
    }

    // Save & Load
    async function saveMask(isSubmitting = false, isAutoSave = false, suppressDialog = false) {
        if (!originalWidth || !originalHeight) {
            if (!isAutoSave) Swal.fire('Error', 'Image not loaded yet.', 'error');
            return false;
        }

        window.isSaving = true;

        if (window.saveStatusTimeout) {
            clearTimeout(window.saveStatusTimeout);
        }

        const statusEl = document.getElementById('saveStatus');
        if (statusEl) {
            statusEl.innerHTML = '<i class="bi bi-arrow-repeat spin"></i> Saving...';
            statusEl.classList.remove('text-success', 'text-muted');
            statusEl.classList.add('text-warning');
        }

        const combinedMaskCanvas = renderNodesToCanvas(getExportableAnnotationNodes({ includeHidden: true }), originalWidth, originalHeight);
        const combinedDataUrl = combinedMaskCanvas.toDataURL('image/png');

        // Build metadata once and reuse it for both `metadata` and `canvas_state`
        // (canvas_state is just its JSON string) — avoids serializing the whole
        // annotation set, including embedded image data URLs, twice per save.
        const metadata = getMetadata();
        const canvasState = JSON.stringify(metadata);
        const taskId = window.SEGMENTATION_CONFIG.taskId;
        const payload = {
            all_labels_mask: combinedDataUrl,
            separated_masks: {},
            metadata: metadata,
            is_auto_save: isAutoSave,
            canvas_state: canvasState
        };

        lastPersistedState = payload.canvas_state;

        if (isSocketConnected && saveSocket && saveSocket.readyState === WebSocket.OPEN) {
            // Using WebSocket
            saveSocket.send(JSON.stringify(payload));
            if (!isAutoSave && !suppressDialog) {
                Swal.fire({
                    icon: 'success',
                    title: 'Saved',
                    text: 'Progress Saved!.',
                    timer: 1500,
                    showConfirmButton: false
                });
            }
            return true;
        }

        // Fallback to fetch if websocket is disconnected
        const url = `/api/workflow/task/${taskId}/save-mask/`;
        try {
            const response = await fetch(url, {
                method: "POST",
                headers: {
                    "Content-Type": "application/json",
                    "X-CSRFToken": getCSRFToken()
                },
                body: JSON.stringify(payload)
            });
            const data = await response.json();

            if (data.success || data.status === 'success') {
                window.isSaving = false;
                window.hasUnsavedChanges = false;
                if (statusEl) {
                    statusEl.innerHTML = '<i class="bi bi-check-circle"></i> Saved';
                    statusEl.classList.add('text-success', 'text-muted');
                    statusEl.classList.remove('text-warning', 'text-danger');
                    
                    if (window.saveStatusTimeout) {
                        clearTimeout(window.saveStatusTimeout);
                    }
                    window.saveStatusTimeout = setTimeout(() => {
                        const el = document.getElementById('saveStatus');
                        if (el && !window.isSaving) {
                            el.innerHTML = 'Live Session';
                            el.className = 'text-primary';
                        }
                    }, 3000);
                }

                if (!isAutoSave && !suppressDialog) {
                    Swal.fire({
                        icon: 'success',
                        title: 'Saved',
                        text: 'Progress Saved!',
                        timer: 1500,
                        showConfirmButton: false
                    });
                }
                return true;
            } else {
                throw new Error(data.message || 'Save failed');
            }
        } catch (err) {
            window.isSaving = false;
            if (statusEl) {
                statusEl.innerHTML = '<i class="bi bi-x-circle"></i> Failed to save';
                statusEl.classList.add('text-danger');
                statusEl.classList.remove('text-success', 'text-warning', 'text-muted');
            }
            if (!isAutoSave) Swal.fire('Save Failed', err.message || 'An error occurred while saving.', 'error');
            return false;
        } finally {
            window.isSaving = false;
        }
    }

    window.saveMask = saveMask;
    window.saveMaskWithRetry = function (_retryCount = 0, _maxRetries = 3, isAutoSave = true) {
        return saveMask(false, isAutoSave);
    };

    window.submitTask = async function () {
        const originalVisibilities = new Map();
        annotationLayer.getChildren().forEach(node => {
            if (node !== transformer) {
                originalVisibilities.set(node, node.visible());
            }
        });

        showAllAnnotations();

        const coverage = calculateMaskedCoverage();
        if (coverage < 100) {
            Swal.fire({
                title: 'Incomplete Coverage',
                customClass: {
                    title: 'text-primary'
                },
                text: `Image coverage is ${formatCoverage(coverage)}%. Please annotate 100% of the image before submitting.`,
                icon: 'warning',
                confirmButtonText: 'OK',
                confirmButtonColor: BRAND_COLOR
            });
            restoreVisibilities(originalVisibilities);
            return;
        }

        const hasAnnotations = getExportableAnnotationNodes().some(node =>
            node.getAttr('labelName') &&
            node.globalCompositeOperation() !== 'destination-out'
        );

        if (!hasAnnotations) {
            const result = await Swal.fire({
                title: 'No Annotations',
                text: 'You have not drawn anything. Submit as Empty?',
                customClass: { title: 'text-primary' },
                icon: 'warning',
                showCancelButton: true,
                showDenyButton: true,
                confirmButtonText: 'Submit & Next',
                denyButtonText: 'Submit',
                cancelButtonText: 'Cancel',
                confirmButtonColor: BRAND_COLOR,
                denyButtonColor: '#6c757d'
            });

            if (result.isConfirmed) {
                await submitTaskToAPI(true, true, originalVisibilities, false);
            } else if (result.isDenied) {
                await submitTaskToAPI(true, true, originalVisibilities, true);
            } else {
                restoreVisibilities(originalVisibilities);
            }
            return;
        }

        const errors = validateAnnotations();
        if (errors.length > 0) {
            Swal.fire({
                title: 'Missing Attributes',
                html: `<div class="text-left text-danger small"><ul>${errors.map(e => `<li>${e}</li>`).join('')}</ul></div>`,
                icon: 'error',
                confirmButtonColor: BRAND_COLOR
            });
            restoreVisibilities(originalVisibilities);
            return;
        }

        await submitTaskToAPI(false, false, originalVisibilities);
    };

    function triggerAutoSave() {
        const statusEl = document.getElementById('saveStatus');

        if (window.isSaving) {
            return;
        }

        if (hasStateChanged()) {
            saveMask(false, true);
        } else {
            if (statusEl) {
                statusEl.innerHTML = '<i class="bi bi-check-circle"></i> Saved';
                statusEl.classList.add('text-success', 'text-muted');
                statusEl.classList.remove('text-warning', 'text-danger');
                window.hasUnsavedChanges = false;
                
                if (window.saveStatusTimeout) {
                    clearTimeout(window.saveStatusTimeout);
                }
                window.saveStatusTimeout = setTimeout(() => {
                    const el = document.getElementById('saveStatus');
                    if (el && !window.isSaving) {
                        el.innerHTML = 'Live Session';
                        el.className = 'text-primary';
                    }
                }, 3000);
            }
        }
    }
    window.triggerAutoSave = triggerAutoSave;

    function hasStateChanged() {
        const currentState = serializeCanvasState();
        return currentState !== lastPersistedState;
    }

    function saveState() {
        saveHistory();
    }
    window.saveState = saveState;

    function getExportableAnnotationNodes(options = {}) {
        if (!annotationLayer) return [];
        const includeHidden = !!options.includeHidden;
        return annotationLayer.getChildren().filter(node =>
            node !== transformer &&
            !node.getAttr('isUndoSubtractor') &&
            (includeHidden || node.visible()) &&
            !node.getAttr('isUnmaskedOverlay') &&
            !node.getAttr('excludeFromExport')
        );
    }

    function getMarkingCount() {
        const seenDatasetIds = new Set();
        let count = 0;

        getExportableAnnotationNodes({ includeHidden: true }).forEach(node => {
            if (!node.getAttr('labelName')) return;
            if (node.globalCompositeOperation() === 'destination-out') return;

            const datasetId = node.getAttr('datasetId');
            if (datasetId != null) {
                const key = String(datasetId);
                if (seenDatasetIds.has(key)) return;
                seenDatasetIds.add(key);
            }
            count++;
        });

        return count;
    }
    window.getMarkingCount = getMarkingCount;

    function showAllAnnotations() {
        annotationLayer.getChildren().forEach(node => {
            if (
                node !== transformer &&
                !node.getAttr('isUnmaskedOverlay') &&
                !node.getAttr('excludeFromExport')
            ) {
                node.visible(true);
            }
        });
        annotationLayer.batchDraw();
        updateLayerList();
    }

    function restoreVisibilities(visibilitiesMap) {
        if (!visibilitiesMap) return;

        visibilitiesMap.forEach((visible, node) => {
            if (node && (!node.isDestroyed || !node.isDestroyed())) {
                node.visible(visible);
            }
        });
        annotationLayer.batchDraw();
        updateLayerList();
    }

    function validateAnnotations() {
        const errors = [];
        const configs = (typeof window.AVAILABLE_DATASETS !== 'undefined') ? window.AVAILABLE_DATASETS : [];

        getExportableAnnotationNodes().forEach((node, idx) => {
            if (!node.getAttr('labelName')) return;
            if (node.globalCompositeOperation() === 'destination-out') return;

            const config = configs.find(d =>
                String(d.id) === String(node.getAttr('datasetId')) ||
                d.label_name === node.getAttr('labelName') ||
                d.name === node.getAttr('labelName')
            );

            if (!config || !config.attributes || config.attributes.length === 0) return;

            const objAttrs = node.getAttr('attributes') || {};
            const missing = [];

            config.attributes.forEach(attrDef => {
                const attrName = attrDef.name;
                const val = objAttrs[attrName];

                if (!attrDef.is_mandatory) return;

                if (val === undefined || val === null || String(val).trim() === "") {
                    missing.push(attrName);
                }
            });

            if (missing.length > 0) {
                errors.push(`Shape #${idx + 1} (${node.getAttr('labelName')}) is missing: ${missing.join(', ')}`);
            }
        });

        return errors;
    }

    function notifyTaskSubmitted(taskId) {
        stopPersistingUndoRedoState();
        if (typeof BroadcastChannel === 'undefined') return;

        const channel = new BroadcastChannel("production_tasks");
        channel.postMessage({
            type: "TASK_SUBMITTED",
            taskId: taskId
        });
        channel.close();
    }

    async function submitTaskToAPI(isNonWorkable = false, skipConfirmation = false, originalVisibilities = null, goToList = null) {
        const taskId = window.SEGMENTATION_CONFIG.taskId;

        if (!skipConfirmation) {
            const result = await Swal.fire({
                title: isNonWorkable ? 'Submit as Empty?' : 'Submit Task?',
                customClass: { title: 'text-primary' },
                text: isNonWorkable ? "You have not drawn anything. This will mark the task as non-workable." : "This will mark the task as SUBMITTED.",
                icon: 'question',
                showCancelButton: true,
                showDenyButton: true,
                confirmButtonText: 'Submit & Next',
                denyButtonText: 'Submit',
                cancelButtonText: 'Cancel',
                confirmButtonColor: BRAND_COLOR,
                denyButtonColor: '#6c757d'
            });

            if (result.isConfirmed) {
                goToList = false;
            } else if (result.isDenied) {
                goToList = true;
            } else {
                restoreVisibilities(originalVisibilities);
                return;
            }
        }

        try {
            if (!isNonWorkable) {
                // Autosave has almost always already persisted the current canvas
                // (especially at 100% coverage). Only run the expensive full-res
                // mask render + toDataURL + upload again if the state actually
                // changed since the last save; otherwise go straight to submit.
                if (hasStateChanged()) {
                    const saved = await saveMask(true, false, true);
                    if (!saved) {
                        throw new Error('Error saving files!');
                    }
                }
            }

            const response = await fetch(`/api/workflow/task/${taskId}/submit/`, {
                method: "POST",
                headers: {
                    "Content-Type": "application/json",
                    "X-CSRFToken": getCSRFToken()
                },
                body: JSON.stringify({
                    marking_count: isNonWorkable ? 0 : getMarkingCount(),
                    is_non_workable: isNonWorkable,
                    go_to_list: goToList
                })
            });

            const data = await response.json();

            if (data.success || data.status === 'success') {
                await Swal.fire({
                    icon: 'success',
                    title: 'Submitted',
                    text: 'Task completed.',
                    timer: 1000,
                    showConfirmButton: false
                });

                notifyTaskSubmitted(taskId);

                const stageToken = window.SEGMENTATION_CONFIG.stageToken;
                if (!goToList && data.next_task_token) {
                    window.location.href = `/workflow/task/access/${data.next_task_token}/`;
                } else if (!goToList && data.redirect_url) {
                    window.location.href = data.redirect_url;
                } else {
                    window.location.href = `/workflow/access/${stageToken}/`;
                }
            } else {
                throw new Error(data.message || 'Submission failed');
            }
        } catch (err) {
            Swal.fire('Error', err.message || 'Submission failed', 'error');
            restoreVisibilities(originalVisibilities);
        }
    }

    // Fabric.js Serializer Adapter (so backend parsing does not break)
    function getMetadata() {
        const nodes = annotationLayer.getChildren().filter(node =>
            node !== transformer &&
            !node.getAttr('isUnmaskedOverlay') &&
            !node.getAttr('excludeFromExport') &&
            node.visible() !== false &&
            !node.getAttr('isUndoSubtractor') &&
            !!node.getAttr('labelName')             // skip orphaned nodes — don't persist them
        );
        const fabricObjects = nodes.map(node => {
            const type = node.getClassName().toLowerCase();
            const labelName = node.getAttr('labelName');
            const labelColor = node.getAttr('labelColor');
            const datasetId = node.getAttr('datasetId');
            const id = node.id();

            if (type === 'rect') {
                return {
                    type: 'rect',
                    left: node.x(),
                    top: node.y(),
                    width: node.width(),
                    height: node.height(),
                    scaleX: node.scaleX() || 1,
                    scaleY: node.scaleY() || 1,
                    labelName: labelName,
                    labelColor: labelColor,
                    datasetId: datasetId,
                    id: id,
                    locked: node.getAttr('locked') || false,
                    opacity: node.opacity(),
                    attributes: node.getAttr('attributes') || {},
                    command: node.getAttr('command') || '',
                    isBoundary: node.getAttr('isBoundary') || false,
                    eraserPaths: node.getAttr('_eraserPaths') || [],
                    subtractorNodes: node.getAttr('_subtractorNodes') || [],
                    visible: node.visible(),
                    isUndoSubtractor: node.getAttr('isUndoSubtractor') || false
                };
            } else if (type === 'ellipse') {
                return {
                    type: 'ellipse',
                    left: node.x() - node.radiusX() * (node.scaleX() || 1),
                    top: node.y() - node.radiusY() * (node.scaleY() || 1),
                    rx: node.radiusX(),
                    ry: node.radiusY(),
                    scaleX: node.scaleX() || 1,
                    scaleY: node.scaleY() || 1,
                    labelName: labelName,
                    labelColor: labelColor,
                    datasetId: datasetId,
                    id: id,
                    locked: node.getAttr('locked') || false,
                    opacity: node.opacity(),
                    attributes: node.getAttr('attributes') || {},
                    command: node.getAttr('command') || '',
                    isBoundary: node.getAttr('isBoundary') || false,
                    eraserPaths: node.getAttr('_eraserPaths') || [],
                    subtractorNodes: node.getAttr('_subtractorNodes') || [],
                    visible: node.visible(),
                    isUndoSubtractor: node.getAttr('isUndoSubtractor') || false
                };
            } else if (type === 'line') {
                const pts = node.points();
                const pointsObj = [];
                for (let i = 0; i < pts.length; i += 2) {
                    pointsObj.push({ x: pts[i], y: pts[i + 1] });
                }
                const isClosed = node.closed();
                return {
                    type: isClosed ? 'polygon' : 'polyline',
                    points: pointsObj,
                    left: Math.min(...pts.filter((_, idx) => idx % 2 === 0)),
                    top: Math.min(...pts.filter((_, idx) => idx % 2 === 1)),
                    scaleX: 1,
                    scaleY: 1,
                    labelName: labelName,
                    labelColor: labelColor,
                    datasetId: datasetId,
                    id: id,
                    locked: node.getAttr('locked') || false,
                    opacity: node.opacity(),
                    attributes: node.getAttr('attributes') || {},
                    command: node.getAttr('command') || '',
                    globalCompositeOperation: node.globalCompositeOperation(),
                    isBoundary: node.getAttr('isBoundary') || false,
                    eraserPaths: node.getAttr('_eraserPaths') || [],
                    eraserPaths: node.getAttr('_eraserPaths') || [],
                    subtractorNodes: node.getAttr('_subtractorNodes') || [],
                    visible: node.visible(),
                    isUndoSubtractor: node.getAttr('isUndoSubtractor') || false,
                    strokeWidth: node.strokeWidth(),
                    isBrushStroke: node.getAttr('isBrushStroke') || false
                };
            } else if (type === 'image') {
                let imgSrc = node.getAttr('_srcCache') || '';
                if (!imgSrc) {
                    const img = node.image();
                    if (img) {
                        imgSrc = img.src || (img.toDataURL ? img.toDataURL() : '');
                    }
                    if (imgSrc) node.setAttr('_srcCache', imgSrc);
                }
                return {
                    type: 'image',
                    src: imgSrc,
                    left: node.x(),
                    top: node.y(),
                    width: node.width(),
                    height: node.height(),
                    scaleX: node.scaleX() || 1,
                    scaleY: node.scaleY() || 1,
                    labelName: labelName,
                    labelColor: labelColor,
                    datasetId: datasetId,
                    id: id,
                    locked: node.getAttr('locked') || false,
                    opacity: node.opacity(),
                    attributes: node.getAttr('attributes') || {},
                    command: node.getAttr('command') || '',
                    isMask: node.getAttr('isMask') || false,
                    isBoundary: node.getAttr('isBoundary') || false,
                    eraserPaths: node.getAttr('_eraserPaths') || [],
                    subtractorNodes: node.getAttr('_subtractorNodes') || [],
                    visible: node.visible(),
                    isUndoSubtractor: node.getAttr('isUndoSubtractor') || false
                };
            }
            return null;
        }).filter(Boolean);

        const runtimeConfig = window.SEGMENTATION_CONFIG || {};
        const savedState = runtimeConfig.savedState;
        const existingTimestamp = savedState && savedState.meta && savedState.meta.timestamp;
        const canvasJSON = {
            version: "5.3.0",
            objects: fabricObjects
        };

        return {
            meta: {
                original_width: originalWidth,
                original_height: originalHeight,
                timestamp: existingTimestamp || new Date().toISOString()
            },
            fabricJSON: canvasJSON,
            shapes: convertFabricToShapes(canvasJSON)
        };
    }

    function convertFabricToShapes(fabricJSON) {
        const shapes = [];

        fabricJSON.objects.forEach(obj => {
            if (obj.type === 'image') return;

            const shape = {
                type: obj.type,
                left: obj.left || 0,
                top: obj.top || 0,
                width: obj.width || 0,
                height: obj.height || 0,
                fill: obj.fill,
                stroke: obj.stroke,
                strokeWidth: obj.strokeWidth || 0,
                labelName: obj.labelName,
                labelColor: obj.labelColor,
                datasetId: obj.datasetId,
                attributes: obj.attributes || {},
                command: obj.command || ''
            };

            if (obj.type === 'rect') {
                shape.points = [
                    { x: obj.left, y: obj.top },
                    { x: obj.left + obj.width * (obj.scaleX || 1), y: obj.top },
                    { x: obj.left + obj.width * (obj.scaleX || 1), y: obj.top + obj.height * (obj.scaleY || 1) },
                    { x: obj.left, y: obj.top + obj.height * (obj.scaleY || 1) }
                ];
            } else if (obj.type === 'ellipse') {
                shape.radiusX = obj.rx;
                shape.radiusY = obj.ry;
                shape.center = { x: obj.left + obj.rx * (obj.scaleX || 1), y: obj.top + obj.ry * (obj.scaleY || 1) };
            } else if (obj.type === 'polygon' || obj.type === 'polyline') {
                shape.points = obj.points;
            }

            shapes.push(shape);
        });

        return shapes;
    }

    // Load state
    function loadSavedState(stateToUse = null) {
        return new Promise((resolveMain) => {
            if (!transformer || !transformer.getParent()) {
                transformer = new Konva.Transformer({
                    borderEnabled: false,
                    enabledAnchors: [],
                    rotateEnabled: false,
                });
                annotationLayer.add(transformer);
            }

            const savedState = stateToUse || window.SEGMENTATION_CONFIG.savedState;
            if (!savedState || !savedState.fabricJSON || !savedState.fabricJSON.objects) {
                updateLayerList();
                resolveMain();
                return;
            }

            const objects = savedState.fabricJSON.objects;
            if (objects.length === 0) {
                updateLayerList();
                resolveMain();
                return;
            }

            const promises = objects.map(obj => {
                return new Promise((resolve) => {
                    const isVisible = obj.visible !== false;
                    const isUndoSub = obj.isUndoSubtractor || false;

                    if (obj.type === 'rect') {
                        const rect = new Konva.Rect({
                            x: obj.left,
                            y: obj.top,
                            width: obj.width,
                            height: obj.height,
                            scaleX: obj.scaleX || 1,
                            scaleY: obj.scaleY || 1,
                            fill: obj.labelColor,
                            opacity: 1.0,
                            stroke: obj.labelColor,
                            strokeWidth: 2,
                            strokeScaleEnabled: false,
                            visible: isVisible
                        });
                        rect.setAttrs({
                            labelName: obj.labelName,
                            labelColor: obj.labelColor,
                            datasetId: obj.datasetId,
                            id: obj.id,
                            locked: obj.locked || false,
                            attributes: obj.attributes || {},
                            command: obj.command || '',
                            isBoundary: true,
                            isUndoSubtractor: isUndoSub
                        });
                        rect.setAttr('_eraserPaths', obj.eraserPaths || []);
                        rect.setAttr('_subtractorNodes', obj.subtractorNodes || []);
                        makeShapeErasable(rect);
                        addAnnotationShape(rect);
                        resolve();
                    } else if (obj.type === 'ellipse' || obj.type === 'circle') {
                        const rx = obj.rx || obj.radius || (obj.width / 2);
                        const ry = obj.ry || obj.radius || (obj.height / 2);
                        const ellipse = new Konva.Ellipse({
                            x: obj.left + rx * (obj.scaleX || 1),
                            y: obj.top + ry * (obj.scaleY || 1),
                            radiusX: rx,
                            radiusY: ry,
                            scaleX: obj.scaleX || 1,
                            scaleY: obj.scaleY || 1,
                            fill: obj.labelColor,
                            opacity: 1.0,
                            stroke: obj.labelColor,
                            strokeWidth: 2,
                            strokeScaleEnabled: false,
                            visible: isVisible
                        });
                        ellipse.setAttrs({
                            labelName: obj.labelName,
                            labelColor: obj.labelColor,
                            datasetId: obj.datasetId,
                            id: obj.id,
                            locked: obj.locked || false,
                            attributes: obj.attributes || {},
                            command: obj.command || '',
                            isBoundary: true,
                            isUndoSubtractor: isUndoSub
                        });
                        ellipse.setAttr('_eraserPaths', obj.eraserPaths || []);
                        ellipse.setAttr('_subtractorNodes', obj.subtractorNodes || []);
                        makeShapeErasable(ellipse);
                        addAnnotationShape(ellipse);
                        resolve();
                    } else if ((obj.type === 'polygon' || obj.type === 'polyline') && obj.points) {
                        const flatPts = [];
                        obj.points.forEach(p => flatPts.push(p.x, p.y));
                        const poly = new Konva.Line({
                            points: flatPts,
                            fill: obj.type === 'polygon' ? obj.labelColor : null,
                            opacity: 1.0,
                            stroke: obj.labelColor,
                            strokeWidth: obj.strokeWidth ? obj.strokeWidth : (obj.type === 'polygon' && obj.isBrushStroke !== true ? 2 : brushSize),
                            strokeScaleEnabled: obj.type === 'polygon' && obj.isBrushStroke !== true ? false : true,
                            lineCap: 'round',
                            lineJoin: 'round',
                            closed: obj.type === 'polygon',
                            globalCompositeOperation: obj.globalCompositeOperation || 'source-over',
                            visible: isVisible
                        });
                        poly.setAttrs({
                            labelName: obj.labelName,
                            labelColor: obj.labelColor,
                            datasetId: obj.datasetId,
                            id: obj.id,
                            locked: obj.locked || false,
                            attributes: obj.attributes || {},
                            command: obj.command || '',
                            isBoundary: true,
                            isUndoSubtractor: isUndoSub,
                            isBrushStroke: obj.isBrushStroke !== undefined ? obj.isBrushStroke : (obj.type === 'polyline')
                        });
                        if (obj.type === 'polygon' || obj.type === 'polyline') {
                            poly.setAttr('_eraserPaths', obj.eraserPaths || []);
                            poly.setAttr('_subtractorNodes', obj.subtractorNodes || []);
                            makeShapeErasable(poly);
                        }
                        addAnnotationShape(poly);
                        resolve();
                    } else if (obj.type === 'image') {
                        const imgObj = new Image();
                        imgObj.onload = function () {
                            const imgNode = new Konva.Image({
                                imageSmoothingEnabled: false,
                                x: obj.left,
                                y: obj.top,
                                image: imgObj,
                                width: obj.width,
                                height: obj.height,
                                scaleX: obj.scaleX || 1,
                                scaleY: obj.scaleY || 1,
                                opacity: 1.0,
                                visible: isVisible
                            });
                            imgNode.setAttrs({
                                labelName: obj.labelName,
                                labelColor: obj.labelColor,
                                datasetId: obj.datasetId,
                                id: obj.id,
                                locked: obj.locked || false,
                                attributes: obj.attributes || {},
                                command: obj.command || '',
                                isMask: obj.isMask || false,
                                isBoundary: obj.isBoundary || false,
                                isUndoSubtractor: isUndoSub
                            });
                            addAnnotationShape(imgNode);
                            resolve();
                        };
                        imgObj.onerror = function () {
                            resolve();
                        };
                        imgObj.src = obj.src || window.SEGMENTATION_CONFIG.mask_path || '';
                    } else {
                        resolve();
                    }
                });
            });

            Promise.all(promises).then(() => {
                annotationLayer.batchDraw();
                updateLayerList();
                resolveMain();
            });
        });
    }

    // Undo/Redo Implementation
    function saveHistory() {
        const metadata = getMetadata();
        const json = JSON.stringify(metadata);

        if (historyStack.length > 0 && historyStack[historyStack.length - 1] === json) {
            persistUndoRedoState();
            return;
        }

        historyStack.push(json);
        if (historyStack.length > MAX_HISTORY) {
            historyStack.shift();
        }
        redoStack = []; // Clear redo stack on new action
        persistUndoRedoState();
    }

    function normalizeCanvasNodes() {
        try {
            annotationLayer.getChildren().forEach(node => {
                if (!node) return;
                if (!isFinite(node.x()) || !isFinite(node.y())) {
                    node.x(node.x() || 0);
                    node.y(node.y() || 0);
                }
            });
        } catch (err) {
            console.error('normalizeCanvasNodes error:', err);
        }
    }

    window.rejectTask = function (reason) {
        const taskId = window.SEGMENTATION_CONFIG.taskId;

        fetch(`/api/workflow/task/${taskId}/reject/`, {
            method: "POST",
            headers: {
                "Content-Type": "application/json",
                "X-CSRFToken": getCSRFToken()
            },
            body: JSON.stringify({ reason: reason })
        })
            .then(res => res.json())
            .then(data => {
                if (data.success || data.status === 'success') {
                    Swal.fire({
                        icon: 'success',
                        title: 'Task Rejected',
                        text: 'The task has been sent back for rework.',
                        timer: 1500,
                        showConfirmButton: false
                    }).then(() => {
                        notifyTaskSubmitted(taskId);
                        if (data.next_task_token) {
                            window.location.href = `/workflow/task/access/${data.next_task_token}/`;
                        } else if (data.redirect_url) {
                            window.location.href = data.redirect_url;
                        } else {
                            const stageToken = window.SEGMENTATION_CONFIG.stageToken;
                            window.location.href = `/workflow/access/${stageToken}/`;
                        }
                    });
                } else {
                    throw new Error(data.message);
                }
            })
            .catch(err => {
                Swal.fire('Error', err.message || 'Rejection failed', 'error');
            });
    };

    window.segmentationCanvas = {
        getObjects: function () {
            if (!annotationLayer) return [];
            return annotationLayer.getChildren().filter(node =>
                node !== transformer &&
                !node.getAttr('isUnmaskedOverlay') &&
                !node.getAttr('excludeFromExport')
            ).map(node => {
                return {
                    labelName: node.getAttr('labelName'),
                    isMask: node.getAttr('isMask') || false,
                    globalCompositeOperation: node.globalCompositeOperation ? node.globalCompositeOperation() : 'source-over',
                    get command() {
                        return node.getAttr('command') || '';
                    },
                    set command(val) {
                        node.setAttr('command', val);
                    }
                };
            });
        }
    };

    window.undo = function () {
        flashButtonState('btn-undo');

        // Use isDrawingPolygon (not isDrawing) — isDrawing resets to false on mouseUp
        // for rect/brush/etc. and would break the polygon undo check.
        if (currentTool === 'polygon' && isDrawingPolygon) {
            if (polygonPoints.length >= 2) {
                const y = polygonPoints.pop();
                const x = polygonPoints.pop();
                polygonRedoStack.push({ x, y });

                if (polygonPoints.length < 2) {
                    // No valid point left — destroy line and exit polygon drawing mode
                    if (polygonActiveLine) polygonActiveLine.destroy();
                    polygonActiveLine = null;
                    isDrawingPolygon = false;
                } else if (polygonActiveLine) {
                    polygonActiveLine.points([...polygonPoints]);
                }
                updateActiveDrawingCircles(polygonPoints, window.CURRENT_LABEL ? window.CURRENT_LABEL.color : undefined);
                annotationLayer.batchDraw();
            }
            return;
        }

        if (historyStack.length === 0) return;
        const currentStateStr = JSON.stringify(getMetadata());

        function getComparableString(stateStr) {
            try {
                const state = JSON.parse(stateStr);
                const objs = (state.fabricJSON && state.fabricJSON.objects) || [];
                const cleanObjs = objs.map(o => {
                    const copy = { ...o };
                    delete copy.isUndoSubtractor;
                    delete copy.eraserPaths;
                    delete copy.subtractorNodes;
                    return copy;
                });
                return JSON.stringify(cleanObjs);
            } catch (e) {
                return stateStr;
            }
        }

        const currentComparable = getComparableString(currentStateStr);
        let prevStateStr = null;

        while (historyStack.length > 0) {
            const popped = historyStack.pop();
            const poppedComparable = getComparableString(popped);
            
            if (poppedComparable === currentComparable) {
                if (redoStack.length === 0 || redoStack[redoStack.length - 1] !== popped) {
                    redoStack.push(popped);
                }
            } else {
                prevStateStr = popped;
                break;
            }
        }

        if (!prevStateStr) {
            return;
        }

        if (redoStack.length === 0 || redoStack[redoStack.length - 1] !== currentStateStr) {
            redoStack.push(currentStateStr);
        }

        const prevState = JSON.parse(prevStateStr);
        const prevObjs = (prevState.fabricJSON || {}).objects || [];
        const prevIds = new Set(prevObjs.map(o => o.id).filter(Boolean));

        const nodesToSubtract = annotationLayer.getChildren().filter(node => {
            if (node === transformer) return false;
            const id = node.id();
            return id && !prevIds.has(id) && node.getAttr('locked') !== false && node.visible() !== false && node.getAttr('labelName');
        });

        const nodesToKeep = nodesToSubtract.map(node => {
            const clone = node.clone();
            clone.visible(false);
            clone.setAttr('isUndoSubtractor', true);
            return clone;
        });

        annotationLayer.destroyChildren();
        window.IS_LOADING_STATE = true;
        window.SEGMENTATION_CONFIG.savedState = prevState;
        loadSavedState().then(() => {
            window.IS_LOADING_STATE = false;
            
            // Add the cloned subtractor nodes back to the layer and update intersecting shapes
            nodesToKeep.forEach(clone => {
                annotationLayer.add(clone);
                
                const cloneBox = clone.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                annotationLayer.getChildren().forEach(olderNode => {
                    if (olderNode === transformer || olderNode === clone || olderNode.getAttr('isUndoSubtractor')) return;
                    if (!isVectorBoundaryShape(olderNode)) return;
                    if (olderNode.getAttr('locked') !== false) return; // FIX: DO NOT CUT LOCKED SHAPES
                    
                    const olderBox = olderNode.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                    const intersects = !(cloneBox.x > olderBox.x + olderBox.width ||
                        cloneBox.x + cloneBox.width < olderBox.x ||
                        cloneBox.y > olderBox.y + olderBox.height ||
                        cloneBox.y + cloneBox.height < olderBox.y);
                        
                    if (intersects) {
                        if (clone.getAttr('datasetId') === olderNode.getAttr('datasetId')) return;
                        
                        const subtractors = olderNode.getAttr('_subtractorNodes') || [];
                        if (subtractors.indexOf(clone.id()) === -1) {
                            subtractors.push(clone.id());
                        }
                        olderNode.setAttr('_subtractorNodes', subtractors);
                        makeShapeErasable(olderNode);
                    }
                });
            });

            if (transformer && transformer.getParent() === annotationLayer) {
                transformer.moveToTop();
            }

            normalizeCanvasNodes();
            triggerAutoSave();
            persistUndoRedoState();
        });
    };


    window.redo = function () {
        flashButtonState('btn-redo');

        if (currentTool === 'polygon' && isDrawingPolygon) {
            if (polygonRedoStack.length > 0) {
                const pt = polygonRedoStack.pop();
                polygonPoints.push(pt.x, pt.y);
                if (polygonActiveLine) {
                    // Update the guide line with re-added point
                    polygonActiveLine.points([...polygonPoints, pt.x, pt.y]);
                } else {
                    // Re-create line if it was destroyed when all points were removed
                    polygonActiveLine = new Konva.Line({
                        points: [...polygonPoints, pt.x, pt.y],
                        stroke: window.CURRENT_LABEL ? window.CURRENT_LABEL.color : '#fff',
                        strokeWidth: 2,
                        strokeScaleEnabled: false,
                        closed: false,
                    });
                    addAnnotationShape(polygonActiveLine);
                    isDrawingPolygon = true; // resume drawing mode
                }
                updateActiveDrawingCircles(polygonPoints, window.CURRENT_LABEL ? window.CURRENT_LABEL.color : undefined);
                annotationLayer.batchDraw();
            }
            return;
        }

        if (redoStack.length === 0) return;
        const nextStateStr = redoStack.pop();

        historyStack.push(JSON.stringify(getMetadata()));

        const nextState = JSON.parse(nextStateStr);
        annotationLayer.destroyChildren();
        window.IS_LOADING_STATE = true;
        window.SEGMENTATION_CONFIG.savedState = nextState;
        loadSavedState().then(() => {
            window.IS_LOADING_STATE = false;
            normalizeCanvasNodes();
            triggerAutoSave();
            persistUndoRedoState();
        });
    };

    function serializeCanvasState() {
        return JSON.stringify(getMetadata());
    }

    function getUndoRedoStorageKey() {
        const runtimeConfig = window.SEGMENTATION_CONFIG || {};
        if (!runtimeConfig.taskId) return null;
        return `vision_annotator:undo_redo:${TOOL_STORAGE_NAMESPACE}:${runtimeConfig.taskId}`;
    }

    function trimHistoryForPersistence(entries, limit) {
        if (!Array.isArray(entries)) return [];
        if (limit <= 0) return [];
        return entries.slice(-limit);
    }

    function persistUndoRedoState() {
        const storageKey = getUndoRedoStorageKey();
        if (!shouldPersistUndoRedoState || !storageKey || window.IS_LOADING_STATE) return;

        const attempts = [
            { history: MAX_HISTORY, redo: MAX_HISTORY },
            { history: 5, redo: 5 },
            { history: 3, redo: 3 },
            { history: 1, redo: 1 },
            { history: 0, redo: 0 }
        ];

        for (const attempt of attempts) {
            try {
                const payload = {
                    version: 1,
                    updatedAt: new Date().toISOString(),
                    historyStack: trimHistoryForPersistence(historyStack, attempt.history),
                    redoStack: trimHistoryForPersistence(redoStack, attempt.redo),
                    currentState: serializeCanvasState()
                };
                localStorage.setItem(storageKey, JSON.stringify(payload));
                return;
            } catch (err) {
                if (attempt === attempts[attempts.length - 1]) {
                    console.warn('Failed to persist segmentation undo/redo state:', err);
                }
            }
        }
    }

    function readPersistedUndoRedoState() {
        const storageKey = getUndoRedoStorageKey();
        if (!storageKey) return null;

        try {
            const raw = localStorage.getItem(storageKey);
            if (!raw) return null;

            const parsed = JSON.parse(raw);
            if (!parsed || typeof parsed.currentState !== 'string') {
                return null;
            }

            return {
                currentState: parsed.currentState,
                updatedAt: parsed.updatedAt || null,
                historyStack: Array.isArray(parsed.historyStack)
                    ? parsed.historyStack.filter(item => typeof item === 'string')
                    : [],
                redoStack: Array.isArray(parsed.redoStack)
                    ? parsed.redoStack.filter(item => typeof item === 'string')
                    : []
            };
        } catch (err) {
            console.warn('Failed to read segmentation undo/redo state:', err);
            return null;
        }
    }

    function clearPersistedUndoRedoState() {
        const storageKey = getUndoRedoStorageKey();
        if (!storageKey) return;

        try {
            localStorage.removeItem(storageKey);
        } catch (err) {
            console.warn('Failed to clear segmentation undo/redo state:', err);
        }
    }

    function stopPersistingUndoRedoState() {
        shouldPersistUndoRedoState = false;
        clearPersistedUndoRedoState();
    }

    function getServerSavedStateTimestamp() {
        const runtimeConfig = window.SEGMENTATION_CONFIG || {};
        const savedState = runtimeConfig.savedState;
        const ts = savedState && savedState.meta && savedState.meta.timestamp;
        const parsed = ts ? Date.parse(ts) : NaN;
        return Number.isNaN(parsed) ? null : parsed;
    }

    function getPreferredRestoreSnapshot() {
        const persisted = readPersistedUndoRedoState();
        if (!persisted) return null;

        // If the server has no saved state (e.g. user deleted the JSON), treat the
        // server as authoritative and discard any stale localStorage snapshot so the
        // canvas starts empty instead of restoring the deleted data.
        const runtimeConfig = window.SEGMENTATION_CONFIG || {};
        const savedState = runtimeConfig.savedState;
        const serverHasObjects = savedState &&
            savedState.fabricJSON &&
            Array.isArray(savedState.fabricJSON.objects) &&
            savedState.fabricJSON.objects.length > 0;

        if (!serverHasObjects) {
            clearPersistedUndoRedoState();
            return null;
        }

        const serverTimestamp = getServerSavedStateTimestamp();
        const localTimestamp = persisted.updatedAt ? Date.parse(persisted.updatedAt) : NaN;

        if (serverTimestamp && !Number.isNaN(localTimestamp) && localTimestamp < serverTimestamp) {
            clearPersistedUndoRedoState();
            return null;
        }

        return persisted;
    }

    // Range Sliders, Filters and Opacity Adjustments
    window.setBrushSize = function (size) {
        brushSize = parseInt(size);
        const display = document.getElementById('brushSizeDisplay');
        if (display) {
            display.innerText = brushSize + 'px';
        }
        const slider = document.getElementById('brushSlider');
        if (slider) {
            slider.value = brushSize;
        }
        updateCursor();
    };

    window.openImageSettings = function () {
        const modal = document.getElementById('imageSettingsModal');
        if (modal) {
            $(modal).modal('show');
        }
    };

    $(document).on('click', function (e) {
        const modal = $('#imageSettingsModal');
        if (modal.hasClass('show')) {
            if (!$(e.target).closest('#imageSettingsModal').length && !$(e.target).closest('[onclick="openImageSettings()"]').length) {
                modal.modal('hide');
            }
        }
    });

    window.resetImageFilters = function () {
        // ── Reset image filter sliders ────────────────────────────────────────
        imgFilterState = {
            brightness: 100,
            contrast: 100,
            saturation: 100
        };

        const rangeBrightness = document.getElementById('range-brightness');
        const rangeContrast = document.getElementById('range-contrast');
        const rangeSaturation = document.getElementById('range-saturation');
        if (rangeBrightness) rangeBrightness.value = 100;
        if (rangeContrast) rangeContrast.value = 100;
        if (rangeSaturation) rangeSaturation.value = 100;

        applyFilters();

        // ── Reset Active Opacity back to 50% ─────────────────────────────────
        if (typeof window.setMaskOpacity === 'function') {
            window.setMaskOpacity(0.5);
        } else {
            defaultMaskOpacity = 0.5;
            const opSlider = document.getElementById('opacitySlider');
            const opDisplay = document.getElementById('opacityDisplay');
            if (opSlider) opSlider.value = 0.5;
            if (opDisplay) opDisplay.innerText = '50%';
        }

        // ── Reset Stroke Width (brush size) back to 30px ─────────────────────
        if (typeof window.setBrushSize === 'function') {
            window.setBrushSize(30);
        } else {
            brushSize = 30;
            const brushSlider = document.getElementById('brushSlider');
            const brushDisplay = document.getElementById('brushSizeDisplay');
            if (brushSlider) brushSlider.value = 30;
            if (brushDisplay) brushDisplay.innerText = '30px';
        }
    };


    window.updateFilterFromUI = function () {
        imgFilterState.brightness = parseInt(document.getElementById('range-brightness').value);
        imgFilterState.contrast = parseInt(document.getElementById('range-contrast').value);
        imgFilterState.saturation = parseInt(document.getElementById('range-saturation').value);

        applyFilters();
    };

    function adjustFilterValue(type, amount) {
        imgFilterState[type] = Math.max(0, Math.min(300, imgFilterState[type] + amount));
        const slider = document.getElementById(`range-${type}`);
        if (slider) slider.value = imgFilterState[type];
        applyFilters();
    }
    window.adjustFilterValue = adjustFilterValue;

    function applyFilters() {
        const valB = document.getElementById('val-brightness');
        const valC = document.getElementById('val-contrast');
        const valS = document.getElementById('val-saturation');
        if (valB) valB.innerText = imgFilterState.brightness + "%";
        if (valC) valC.innerText = imgFilterState.contrast + "%";
        if (valS) valS.innerText = imgFilterState.saturation + "%";

        const filterString = `
            brightness(${imgFilterState.brightness}%) 
            contrast(${imgFilterState.contrast}%) 
            saturate(${imgFilterState.saturation}%)
        `;

        if (imageLayer) {
            const canvasEl = imageLayer.getCanvas()._canvas;
            if (canvasEl) {
                canvasEl.style.filter = filterString;
            }
        }
    }

    window.setMaskOpacity = function (value) {
        const newOpacity = parseFloat(value);
        const display = document.getElementById('opacityDisplay');
        if (display) {
            display.innerText = Math.round(newOpacity * 100) + '%';
        }
        const slider = document.getElementById('opacitySlider');
        if (slider) {
            slider.value = newOpacity;
        }

        const selectedNodes = transformer.nodes();
        if (selectedNodes.length > 0) {
            selectedNodes.forEach(node => {
                node.opacity(newOpacity);
            });
            annotationLayer.batchDraw();
            triggerAutoSave();
        } else {
            annotationLayer.show();
            defaultMaskOpacity = newOpacity;
            if (annotationLayer && annotationLayer.getCanvas() && annotationLayer.getCanvas()._canvas) {
                annotationLayer.getCanvas()._canvas.style.opacity = newOpacity;
            }
        }
    };

    function updateOpacitySliderFromSelection() {
        const selectedNodes = transformer.nodes();
        const slider = document.getElementById('opacitySlider');
        const display = document.getElementById('opacityDisplay');
        if (selectedNodes.length > 0) {
            const op = selectedNodes[0].opacity();
            if (slider) slider.value = op;
            if (display) display.innerText = Math.round(op * 100) + '%';
        } else {
            if (slider) slider.value = defaultMaskOpacity;
            if (display) display.innerText = Math.round(defaultMaskOpacity * 100) + '%';
        }
    }

    // Convert Mask to Polygon
    window.convertToPolygon = function () {
        const selectedNodes = transformer.nodes();
        if (selectedNodes.length === 0) {
            Swal.fire("Select a Mask", "Please click on the mask you want to convert.", "warning");
            return;
        }

        const activeObj = selectedNodes[0];
        if (activeObj.getClassName().toLowerCase() === 'line' && activeObj.closed()) {
            Swal.fire("Already a Polygon", "This object is already a polygon.", "info");
            return;
        }

        const objW = originalWidth;
        const objH = originalHeight;
        const scale = getProcessingScale(objW, objH);
        const scaledW = Math.floor(objW * scale) || 1;
        const scaledH = Math.floor(objH * scale) || 1;
        const objCanvas = renderNodesToCanvas([activeObj], objW, objH, scale);

        const objCtx = objCanvas.getContext('2d');
        const imageData = objCtx.getImageData(0, 0, scaledW, scaledH);
        const data = imageData.data;

        let opaqueCount = 0;
        for (let i = 3; i < data.length; i += 4) {
            if (data[i] > 10) opaqueCount++;
        }

        if (opaqueCount === 0) {
            Swal.fire("Empty Mask", "No visible pixels found to trace.", "warning");
            return;
        }

        const grid = new Uint8Array(scaledW * scaledH);
        for (let y = 0; y < scaledH; y++) {
            for (let x = 0; x < scaledW; x++) {
                grid[y * scaledW + x] = data[(y * scaledW + x) * 4 + 3] > 10 ? 1 : 0;
            }
        }

        const leftEdge = [];
        const rightEdge = [];

        for (let y = 0; y < scaledH; y++) {
            let leftX = -1, rightX = -1;
            for (let x = 0; x < scaledW; x++) {
                if (grid[y * scaledW + x] === 1) {
                    if (leftX === -1) leftX = x;
                    rightX = x;
                }
            }
            if (leftX !== -1) {
                leftEdge.push({ x: leftX / scale, y: y / scale });
                rightEdge.push({ x: rightX / scale, y: y / scale });
            }
        }

        if (leftEdge.length < 2) {
            Swal.fire("Conversion Failed", "Insufficient boundary data.", "error");
            return;
        }

        const contourPoints = [];
        for (let i = 0; i < leftEdge.length; i++) {
            contourPoints.push(leftEdge[i]);
        }
        for (let i = rightEdge.length - 1; i >= 0; i--) {
            if (rightEdge[i].x !== leftEdge[i].x) {
                contourPoints.push(rightEdge[i]);
            }
        }

        const simplifiedPoints = simplifyPoints(contourPoints, 1.5);

        const absolutePoints = [];
        simplifiedPoints.forEach(p => {
            absolutePoints.push(Math.round(p.x));
            absolutePoints.push(Math.round(p.y));
        });

        saveHistory();

        const newPolygon = new Konva.Line({
            points: absolutePoints,
            fill: activeObj.getAttr('labelColor'),
            stroke: activeObj.getAttr('labelColor'),
            strokeWidth: 2,
            strokeScaleEnabled: false,
            closed: true,
            opacity: 1.0,
        });

        newPolygon.setAttrs({
            labelName: activeObj.getAttr('labelName'),
            labelColor: activeObj.getAttr('labelColor'),
            datasetId: activeObj.getAttr('datasetId'),
            id: `shape_${Date.now()}`,
            attributes: activeObj.getAttr('attributes') || {},
            isBoundary: true,
            locked: activeObj.getAttr('locked') !== false
        });

        transformer.nodes([]);
        activeObj.destroy();
        addAnnotationShape(newPolygon);
        annotationLayer.batchDraw();

        const datasetId = newPolygon.getAttr('datasetId');
        applyLockedLayerClipping(newPolygon, function () {
            if (datasetId) mergeLabelBrushStrokes(datasetId);
            updateLayerList();
            triggerAutoSave();
        });
    };

    function simplifyPoints(points, tolerance) {
        if (points.length <= 2) return points;
        const sqTolerance = tolerance * tolerance;
        let maxSqDist = 0, index = 0;
        const first = points[0], last = points[points.length - 1];

        for (let i = 1; i < points.length - 1; i++) {
            const sqDist = getSqSegDist(points[i], first, last);
            if (sqDist > maxSqDist) { index = i; maxSqDist = sqDist; }
        }

        if (maxSqDist > sqTolerance) {
            const left = simplifyPoints(points.slice(0, index + 1), tolerance);
            const right = simplifyPoints(points.slice(index), tolerance);
            return left.slice(0, left.length - 1).concat(right);
        }
        return [first, last];
    }

    function getSqSegDist(p, p1, p2) {
        let x = p1.x, y = p1.y, dx = p2.x - x, dy = p2.y - y;
        if (dx !== 0 || dy !== 0) {
            const t = ((p.x - x) * dx + (p.y - y) * dy) / (dx * dx + dy * dy);
            if (t > 1) { x = p2.x; y = p2.y; }
            else if (t > 0) { x += dx * t; y += dy * t; }
        }
        dx = p.x - x; dy = p.y - y;
        return dx * dx + dy * dy;
    }

    // Convert Polygon to Mask (Raster Image)
    window.convertToMask = function () {
        const selectedNodes = transformer.nodes();
        if (selectedNodes.length === 0) {
            Swal.fire("Select a Polygon", "Please click on the polygon you want to convert.", "warning");
            return;
        }

        const activeObj = selectedNodes[0];
        const className = activeObj.getClassName();
        const isClosed = (typeof activeObj.closed === 'function') ? activeObj.closed() : activeObj.getAttr('closed');
        if (className.toLowerCase() !== 'line' || !isClosed) {
            Swal.fire("Not a Polygon", "The selected object is not a polygon.", "info");
            return;
        }

        saveHistory();

        // Clear selection
        transformer.nodes([]);

        const maskNode = convertShapeToMaskImage(activeObj);
        if (maskNode) {
            const datasetId = maskNode.getAttr('datasetId');
            applyLockedLayerClipping(maskNode, function () {
                if (datasetId) mergeLabelBrushStrokes(datasetId);
                updateLayerList();
                triggerAutoSave();
            });
        } else {
            updateLayerList();
            triggerAutoSave();
        }

        if (window.setTool) window.setTool('select');
    };

    window.saveAttributeValue = function (shapeId, attrName, value) {
        const selectedNodes = transformer.nodes();
        if (selectedNodes.length > 0) {
            selectedNodes.forEach(node => {
                let attrs = node.getAttr('attributes') || {};
                attrs[attrName] = value;
                node.setAttr('attributes', attrs);
            });
            saveHistory();
            triggerAutoSave();
            updateLayerList();
        }
    };

    window.saveMultiAttributeValue = function (shapeId, attrName) {
        var checkboxes = document.querySelectorAll('.multi-attr-check[data-attr-name="' + attrName + '"]:checked');
        var values = Array.from(checkboxes).map(function (cb) { return cb.value; });
        var joined = values.join(', ');

        const selectedNodes = transformer.nodes();
        if (selectedNodes.length > 0) {
            selectedNodes.forEach(node => {
                let attrs = node.getAttr('attributes') || {};
                attrs[attrName] = joined;
                node.setAttr('attributes', attrs);
            });
            saveHistory();
            triggerAutoSave();
            updateLayerList();
        }

        var checkEl = document.querySelector('.multi-attr-check[data-attr-name="' + attrName + '"]');
        if (checkEl) {
            var triggerId = checkEl.getAttribute('data-trigger-id');
            if (triggerId) {
                var triggerEl = document.getElementById(triggerId);
                if (triggerEl) {
                    var valueSpan = triggerEl.querySelector('.ms-value');
                    if (valueSpan) {
                        valueSpan.textContent = joined || 'Not selected';
                    }
                }
            }
        }
    };

    function recolorKonvaImage(konvaImg, hexColor) {
        const element = konvaImg.image();
        if (!element) return;

        const rgb = hexToRgb(hexColor);
        if (!rgb) return;

        const width = element.width || konvaImg.width();
        const height = element.height || konvaImg.height();
        if (!width || !height) return;

        const canvasElement = document.createElement('canvas');
        canvasElement.width = width;
        canvasElement.height = height;
        const ctx = canvasElement.getContext('2d');

        ctx.drawImage(element, 0, 0, width, height);

        const imgData = ctx.getImageData(0, 0, width, height);
        const data = imgData.data;
        for (let i = 0; i < data.length; i += 4) {
            if (data[i + 3] > 0) {
                data[i] = rgb.r;
                data[i + 1] = rgb.g;
                data[i + 2] = rgb.b;
            }
        }
        ctx.putImageData(imgData, 0, 0);

        konvaImg.image(canvasElement);
    }

    window.updateAnnotationLabel = function (shapeId, newDatasetId) {
        const configs = (typeof window.AVAILABLE_DATASETS !== 'undefined') ? window.AVAILABLE_DATASETS : [];
        const newConfig = configs.find(d => String(d.id) === String(newDatasetId));
        if (!newConfig) return;

        let targetObj = null;
        if (shapeId) {
            targetObj = annotationLayer.getChildren().find(o => o.getAttr('id') === shapeId);
        } else {
            const nodes = transformer.nodes();
            if (nodes.length > 0) targetObj = nodes[0];
        }

        if (targetObj) {
            saveHistory();

            const oldDatasetId = targetObj.getAttr('datasetId');
            const objectsToUpdate = (oldDatasetId != null)
                ? annotationLayer.getChildren().filter(o =>
                    o !== transformer && String(o.getAttr('datasetId')) === String(oldDatasetId))
                : [targetObj];

            objectsToUpdate.forEach(obj => {
                obj.setAttrs({
                    labelName: newConfig.label_name || newConfig.name,
                    labelColor: newConfig.color,
                    datasetId: newConfig.id,
                    attributes: {}
                });

                const type = obj.getClassName().toLowerCase();
                if (type === 'rect' || type === 'ellipse' || type === 'line') {
                    if (obj.fill()) obj.fill(newConfig.color);
                    obj.stroke(newConfig.color);
                } else if (type === 'image') {
                    obj.setAttr('labelColor', newConfig.color);
                    recolorKonvaImage(obj, newConfig.color);
                }
            });

            annotationLayer.batchDraw();
            triggerAutoSave();
            updateLayerList();

            const nodes = transformer.nodes();
            if (nodes.length > 0 && nodes[0] === targetObj && typeof window.renderAttributeForm === 'function') {
                window.renderAttributeForm(targetObj.attrs);
            }
        }
    };

    function clearAllHoverShadows() {
        if (!annotationLayer) return;
        annotationLayer.getChildren()
            .filter(s => s.getAttr('_hoverShadowActive'))
            .sort((a, b) => (a.getAttr('_originalZIndex') || 0) - (b.getAttr('_originalZIndex') || 0))
            .forEach(s => {
                s.setAttrs({
                    shadowColor: s.getAttr('_originalShadowColor'),
                    shadowBlur: s.getAttr('_originalShadowBlur'),
                    shadowOpacity: s.getAttr('_originalShadowOpacity'),
                    shadowOffsetX: s.getAttr('_originalShadowOffsetX'),
                    shadowOffsetY: s.getAttr('_originalShadowOffsetY'),
                    shadowEnabled: s.getAttr('_originalShadowEnabled')
                });
                const zIndex = s.getAttr('_originalZIndex');
                if (typeof zIndex === 'number') s.zIndex(zIndex);
                s.setAttr('_originalShadowColor', undefined);
                s.setAttr('_originalShadowBlur', undefined);
                s.setAttr('_originalShadowOpacity', undefined);
                s.setAttr('_originalShadowOffsetX', undefined);
                s.setAttr('_originalShadowOffsetY', undefined);
                s.setAttr('_originalShadowEnabled', undefined);
                s.setAttr('_originalZIndex', undefined);
                s.setAttr('_hoverShadowActive', false);
            });
    }



    function updateFloatingLabel() {
        const labelEl = document.getElementById('floating-annotation-label');
        if (!labelEl) return;

        const activeNodes = transformer.nodes();
        if (activeNodes.length === 0 || currentTool !== 'select') {
            labelEl.style.display = 'none';
            return;
        }

        const activeNode = activeNodes[0];
        const labelName = activeNode.getAttr('labelName');
        if (!labelName) {
            labelEl.style.display = 'none';
            return;
        }

        let clientRect;
        try {
            clientRect = activeNode.getClientRect();
        } catch (e) {
            const pos = activeNode.getAbsolutePosition();
            clientRect = { x: pos.x, y: pos.y, width: 0, height: 0 };
        }

        const type = activeNode.getClassName().toLowerCase();
        let iconHtml = '<i class="bi bi-tag-fill"></i>';
        if (type === 'rect') iconHtml = '<i class="bi bi-bounding-box"></i>';
        else if (type === 'ellipse' || type === 'circle') iconHtml = '<i class="bi bi-circle"></i>';
        else if (type === 'line' && activeNode.closed()) iconHtml = '<i class="bi bi-hexagon"></i>';
        else if (type === 'line' && !activeNode.closed()) iconHtml = '<i class="bi bi-brush"></i>';

        labelEl.innerHTML = `${iconHtml} <span>${labelName}</span>`;
        labelEl.style.backgroundColor = activeNode.getAttr('labelColor') || '#1d55e8';
        labelEl.style.display = 'flex';
        labelEl.style.transform = 'none';

        const labelWidth = labelEl.offsetWidth;
        const labelHeight = labelEl.offsetHeight;

        const parentEl = labelEl.offsetParent || document.body;
        const parentRect = parentEl.getBoundingClientRect();

        const stageContainer = stage.container();
        const stageRect = stageContainer.getBoundingClientRect();

        const screenX = stageRect.left + clientRect.x + clientRect.width / 2;
        const screenY = stageRect.top + clientRect.y;

        labelEl.style.left = (screenX - parentRect.left - labelWidth / 2) + 'px';
        labelEl.style.top = (screenY - parentRect.top - labelHeight - 6) + 'px';
    }

    window.updateFloatingLabel = updateFloatingLabel;

    window.deleteSelected = function () {
        flashButtonState('btn-delete');
        const selectedNodes = transformer.nodes();
        if (selectedNodes.length > 0) {
            Swal.fire({
                title: 'Confirm Delete',
                text: `Are you sure you want to delete the selected annotation(s)?`,
                icon: 'warning',
                showCancelButton: true,
                confirmButtonColor: '#d33',
                cancelButtonColor: '#3085d6',
                confirmButtonText: 'Yes, delete it!',
                cancelButtonText: 'Cancel'
            }).then((result) => {
                if (result.isConfirmed) {
                    const vectorSelected = [];
                    const rasterSelected = [];
                    selectedNodes.forEach(s => {
                        if (isVectorBoundaryShape(s)) vectorSelected.push(s);
                        else rasterSelected.push(s);
                    });

                    vectorSelected.forEach(node => {
                        node.visible(false);
                        node.setAttr('isUndoSubtractor', true);
                        
                        const delBox = node.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                        annotationLayer.getChildren().forEach(olderNode => {
                            if (olderNode === transformer || olderNode === node || selectedNodes.includes(olderNode) || olderNode.getAttr('isUndoSubtractor')) return;
                            if (!isVectorBoundaryShape(olderNode)) return;
                            if (olderNode.getAttr('locked') !== false) return; // DO NOT CUT LOCKED SHAPES
                            
                            const olderBox = olderNode.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                            const intersects = !(delBox.x > olderBox.x + olderBox.width ||
                                delBox.x + delBox.width < olderBox.x ||
                                delBox.y > olderBox.y + olderBox.height ||
                                delBox.y + delBox.height < olderBox.y);
                                
                            if (intersects) {
                                if (node.getAttr('datasetId') === olderNode.getAttr('datasetId')) return;
                                
                                const subtractors = olderNode.getAttr('_subtractorNodes') || [];
                                if (subtractors.indexOf(node.id()) === -1) {
                                    subtractors.push(node.id());
                                }
                                olderNode.setAttr('_subtractorNodes', subtractors);
                                makeShapeErasable(olderNode);
                            }
                        });
                    });

                    const unlockedRasterSelected = rasterSelected.filter(s => s.getAttr('locked') === false);
                    if (unlockedRasterSelected.length > 0) {
                        cleanupSubtractorNodesOnDelete(unlockedRasterSelected);
                    }

                    saveHistory();
                    transformer.nodes(transformer.nodes().filter(n => n.getParent()));
                    rasterSelected.forEach(node => node.destroy());
                    transformer.nodes([]);
                    const panel = document.getElementById('attributePanel');
                    if (panel) panel.style.display = 'none';
                    annotationLayer.batchDraw();
                    updateLayerList();
                    triggerAutoSave();
                }
            });
        } else {
            const children = annotationLayer.getChildren().filter(node => node !== transformer);
            if (children.length > 0) {
                const lastChild = children[children.length - 1];
                
                if (isVectorBoundaryShape(lastChild)) {
                    lastChild.visible(false);
                    lastChild.setAttr('isUndoSubtractor', true);
                    
                    const delBox = lastChild.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                    annotationLayer.getChildren().forEach(olderNode => {
                        if (olderNode === transformer || olderNode === lastChild || olderNode.getAttr('isUndoSubtractor')) return;
                        if (!isVectorBoundaryShape(olderNode)) return;
                        if (olderNode.getAttr('locked') !== false) return; // DO NOT CUT LOCKED SHAPES
                        
                        const olderBox = olderNode.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                        const intersects = !(delBox.x > olderBox.x + olderBox.width ||
                            delBox.x + delBox.width < olderBox.x ||
                            delBox.y > olderBox.y + olderBox.height ||
                            delBox.y + delBox.height < olderBox.y);
                            
                        if (intersects) {
                            if (lastChild.getAttr('datasetId') === olderNode.getAttr('datasetId')) return;
                            
                            const subtractors = olderNode.getAttr('_subtractorNodes') || [];
                            if (subtractors.indexOf(lastChild.id()) === -1) {
                                subtractors.push(lastChild.id());
                            }
                            olderNode.setAttr('_subtractorNodes', subtractors);
                            makeShapeErasable(olderNode);
                        }
                    });
                } else if (lastChild.getAttr('locked') === false) {
                    cleanupSubtractorNodesOnDelete([lastChild]);
                }

                saveHistory();
                transformer.nodes(transformer.nodes().filter(n => n.getParent()));
                if (!isVectorBoundaryShape(lastChild)) {
                    lastChild.destroy();
                }
                annotationLayer.batchDraw();
                updateLayerList();
                triggerAutoSave();
            }
        }
    };

    function getSelectedExportableNodes() {
        return transformer.nodes().filter(node =>
            node &&
            !node.getAttr('isUnmaskedOverlay') &&
            !node.getAttr('excludeFromExport')
        );
    }

    function getNodesBounds(nodes) {
        if (!nodes || nodes.length === 0) return null;

        let minX = Infinity;
        let minY = Infinity;
        let maxX = -Infinity;
        let maxY = -Infinity;

        nodes.forEach(node => {
            const rect = node.getClientRect({ relativeTo: annotationLayer });
            minX = Math.min(minX, rect.x);
            minY = Math.min(minY, rect.y);
            maxX = Math.max(maxX, rect.x + rect.width);
            maxY = Math.max(maxY, rect.y + rect.height);
        });

        if (!isFinite(minX) || !isFinite(minY) || !isFinite(maxX) || !isFinite(maxY)) return null;
        return { x: minX, y: minY, width: maxX - minX, height: maxY - minY };
    }

    function clampMoveDelta(bounds, dx, dy) {
        let nextDx = dx;
        let nextDy = dy;

        if (!bounds || !originalWidth || !originalHeight) {
            return { dx: nextDx, dy: nextDy };
        }

        if (bounds.x + nextDx < 0) nextDx = -bounds.x;
        if (bounds.x + bounds.width + nextDx > originalWidth) nextDx = originalWidth - (bounds.x + bounds.width);
        if (bounds.y + nextDy < 0) nextDy = -bounds.y;
        if (bounds.y + bounds.height + nextDy > originalHeight) nextDy = originalHeight - (bounds.y + bounds.height);

        return { dx: nextDx, dy: nextDy };
    }

    function nudgeSelectedAnnotations(dx, dy) {
        if (currentTool !== 'select') return false;

        const selectedNodes = getSelectedExportableNodes().filter(node => !node.getAttr('locked'));
        if (selectedNodes.length === 0) return false;

        const delta = clampMoveDelta(getNodesBounds(selectedNodes), dx, dy);
        if (delta.dx === 0 && delta.dy === 0) return false;

        saveHistory();
        selectedNodes.forEach(node => {
            node.x(node.x() + delta.dx);
            node.y(node.y() + delta.dy);
        });
        annotationLayer.batchDraw();
        updateLayerList();
        triggerAutoSave();
        return true;
    }

    function copyToClipboard() {
        const selectedNodes = getSelectedExportableNodes();
        if (selectedNodes.length === 0) return;
        clipboardNodes = selectedNodes.map(node => node.clone());
    }

    function pasteFromClipboard() {
        if (!clipboardNodes.length) return;

        saveHistory();
        transformer.nodes([]);

        const pastedNodes = clipboardNodes.map(node => {
            const clone = node.clone({
                x: node.x() + 20,
                y: node.y() + 20,
                id: `shape_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`
            });
            clone.setAttr('_checkboxSelected', false);
            annotationLayer.add(clone);
            return clone;
        });

        clipboardNodes.forEach(node => {
            node.x(node.x() + 20);
            node.y(node.y() + 20);
        });

        transformer.nodes(pastedNodes.filter(node => !node.getAttr('locked')));
        annotationLayer.batchDraw();
        updateLayerList();
        triggerAutoSave();
    }

    function toggleSelectedVisibility() {
        const selectedNodes = getSelectedExportableNodes();
        if (selectedNodes.length === 0) return false;

        selectedNodes.forEach(node => node.visible(!node.visible()));
        transformer.nodes(selectedNodes.filter(node => node.visible()));
        annotationLayer.batchDraw();
        updateLayerList();
        return true;
    }

    function toggleSidebar(side) {
        if (side === 'left') {
            $('.left-sidebar').toggleClass('collapsed');
        } else if (side === 'right') {
            $('.right-sidebar').toggleClass('collapsed');
        } else {
            const isAnyCollapsed = $('.left-sidebar.collapsed, .right-sidebar.collapsed').length > 0;
            if (isAnyCollapsed) {
                $('.left-sidebar, .right-sidebar').removeClass('collapsed');
            } else {
                $('.left-sidebar, .right-sidebar').addClass('collapsed');
            }
        }

        setTimeout(() => {
            if (!stage) return;
            const container = document.getElementById('konva-container');
            if (!container) return;
            stage.size({
                width: container.clientWidth || stage.width(),
                height: container.clientHeight || stage.height()
            });
            stage.batchDraw();
            resetZoom();
        }, 350);
    }
    window.toggleSidebar = toggleSidebar;

    function setupKeyboardShortcuts() {
        document.addEventListener('keydown', function (e) {
            if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA') return;

            const isModalOpen = document.querySelector('.modal.show');
            if (isModalOpen && isModalOpen.id !== 'imageSettingsModal') return;

            if (window.SEGMENTATION_CONFIG.readOnly) {
                const key = e.key.toUpperCase();
                if (key === 'F' || (key === 'F' && e.shiftKey)) {
                    e.preventDefault();
                    window.resetZoom();
                } else if (e.key === '[') {
                    e.preventDefault();
                    toggleSidebar('left');
                } else if (e.key === ']') {
                    e.preventDefault();
                    toggleSidebar('right');
                } else if (e.key === '\\') {
                    e.preventDefault();
                    toggleSidebar('both');
                } else if (key === 'K') {
                    e.preventDefault();
                    if (typeof window.openShortcutsModal === 'function') {
                        window.openShortcutsModal();
                    } else {
                        $('#shortcutsModal').modal('show');
                    }
                }
                return;
            }

            const key = e.key.toUpperCase();
            if (key === 'C' && (e.ctrlKey || e.metaKey)) {
                e.preventDefault();
                copyToClipboard();
            } else if (key === 'V' && (e.ctrlKey || e.metaKey)) {
                e.preventDefault();
                pasteFromClipboard();
            } else if (key === 'V') window.setTool('select');
            else if (key === 'B') window.setTool('brush');
            else if (key === 'E') window.setTool('eraser');
            else if (key === 'R') window.setTool('rect');
            else if (key === 'C') window.setTool('circle');
            else if (key === 'P') window.setTool('polygon');
            else if (key === 'M') window.setTool('magic');
            else if (key === 'F' && e.shiftKey) window.resetZoom();
            else if (key === 'F' && !e.shiftKey && !e.ctrlKey && !e.metaKey) window.setTool('paint');
            else if (key === 'Z' && (e.ctrlKey || e.metaKey) && e.shiftKey) {
                e.preventDefault();
                window.redo();
            } else if (key === 'Z' && (e.ctrlKey || e.metaKey)) {
                e.preventDefault();
                window.undo();
            } else if (key === 'Y' && (e.ctrlKey || e.metaKey)) {
                e.preventDefault();
                window.redo();
            } else if (key === 'ENTER' && currentTool === 'polygon') {
                finishPolygon();
            } else if (key === 'U') {
                e.preventDefault();
                window.countUnmaskedPixels();
            } else if (key === 'S' && !e.ctrlKey && !e.metaKey) {
                e.preventDefault();
                window.saveMask(false, false);
            } else if (key === 'K') {
                e.preventDefault();
                if (typeof window.openShortcutsModal === 'function') {
                    window.openShortcutsModal();
                } else {
                    $('#shortcutsModal').modal('show');
                }
            } else if (e.key === '[') {
                e.preventDefault();
                toggleSidebar('left');
            } else if (e.key === ']') {
                e.preventDefault();
                toggleSidebar('right');
            } else if (e.key === '\\') {
                e.preventDefault();
                toggleSidebar('both');
            } else if (key === 'H' && e.shiftKey) {
                e.preventDefault();
                showAllAnnotations();
            } else if (key === 'H') {
                e.preventDefault();
                toggleSelectedVisibility();
            } else if (e.key === 'ArrowUp') {
                if (nudgeSelectedAnnotations(0, e.shiftKey ? -10 : -1)) e.preventDefault();
            } else if (e.key === 'ArrowDown') {
                if (nudgeSelectedAnnotations(0, e.shiftKey ? 10 : 1)) e.preventDefault();
            } else if (e.key === 'ArrowLeft') {
                if (nudgeSelectedAnnotations(e.shiftKey ? -10 : -1, 0)) e.preventDefault();
            } else if (e.key === 'ArrowRight') {
                if (nudgeSelectedAnnotations(e.shiftKey ? 10 : 1, 0)) e.preventDefault();
            } else if (key === 'ESCAPE') {
                e.preventDefault();
                updateActiveDrawingCircles([]);
                if (isDrawingPolygon) {
                    if (polygonActiveLine) {
                        polygonActiveLine.destroy();
                        polygonActiveLine = null;
                    }
                    polygonPoints = [];
                    polygonRedoStack = [];
                    isDrawingPolygon = false;
                }
                if (isDrawing) {
                    if (drawingShape) {
                        drawingShape.destroy();
                        drawingShape = null;
                    }
                    isDrawing = false;
                }
                window.setTool('select');
                window.updateToolbarState();
                transformer.nodes([]);
                annotationLayer.getChildren().forEach(s => {
                    if (s !== transformer) {
                        s.setAttrs({
                            shadowColor: undefined,
                            shadowBlur: undefined,
                            shadowOpacity: undefined,
                            shadowOffsetX: undefined,
                            shadowOffsetY: undefined,
                            shadowEnabled: undefined
                        });
                    }
                });
                annotationLayer.batchDraw();
                updateLayerList();
            } else if (key === 'DELETE' || key === 'BACKSPACE') {
                window.deleteSelected();
            }

            // Image Adjust keybinds
            const STEP = 10;
            if (e.key === "1") adjustFilterValue('brightness', STEP);
            else if (e.key === "2") adjustFilterValue('brightness', -STEP);
            else if (e.key === "4") adjustFilterValue('contrast', STEP);
            else if (e.key === "5") adjustFilterValue('contrast', -STEP);
            else if (e.key === "7") adjustFilterValue('saturation', STEP);
            else if (e.key === "8") adjustFilterValue('saturation', -STEP);
            else if (e.key === "0") window.resetImageFilters();
        });
    }

    // Dataset List Selection
    window.handleDatasetSelect = function (id) {
        if (window.CURRENT_LABEL && String(window.CURRENT_LABEL.id) === String(id)) {
            window.CURRENT_LABEL = null;
            document.querySelectorAll('.dataset-item').forEach(el => el.classList.remove('active'));
            window.updateToolbarState();
            return;
        }

        const ds = window.AVAILABLE_DATASETS.find(d => String(d.id) === String(id));
        if (!ds) return;

        window.CURRENT_LABEL = {
            name: ds.name || ds.label_name,
            color: ds.color,
            id: ds.id,
            attributes: ds.attributes || {}
        };

        document.querySelectorAll('.dataset-item').forEach(el => el.classList.remove('active'));
        const activeItem = document.getElementById(`label-${id}`);
        if (activeItem) activeItem.classList.add('active');
        window.updateToolbarState();
    };

    function getAttributeAnswerColor(key, val) {
        const str = String(key) + '::' + String(val);
        let hash = 2166136261;
        for (let i = 0; i < str.length; i++) {
            hash ^= str.charCodeAt(i);
            hash = Math.imul(hash, 16777619);
        }
        const hue = (hash >>> 0) % 360;
        return {
            solid: `hsl(${hue}, 60%, 40%)`,
            tint: `hsl(${hue}, 75%, 95%)`
        };
    }

    // Creation-order key parsed from a shape's `shape_<timestamp>` id. Shapes
    // without a parseable timestamp sort last (keeping their relative order).
    function getNodeDrawOrder(node) {
        const id = String(node.getAttr('id') || '');
        const m = id.match(/(\d{10,})/);
        return m ? parseInt(m[1], 10) : Number.MAX_SAFE_INTEGER;
    }

    function updateLayerList() {
        const listContainer = document.getElementById('layerList');
        if (!listContainer) return;

        const nodes = annotationLayer.getChildren().filter(node =>
            node !== transformer &&
            !node.getAttr('isUndoSubtractor') &&
            !node.getAttr('isUnmaskedOverlay') &&
            !node.getAttr('excludeFromExport') &&
            !node.getAttr('isEraser') &&           // exclude eraser strokes
            node.getAttr('datasetId') !== 'eraser' &&
            !!node.getAttr('labelName')             // skip orphaned/corrupted nodes
        );

        // Show shapes in ascending draw order (first-drawn first). The creation
        // timestamp embedded in each `shape_<timestamp>` id is stable across
        // save/reload, unlike the z-order which flips on reload.
        nodes.sort((a, b) => getNodeDrawOrder(a) - getNodeDrawOrder(b));

        // Clean up any hover-glow shadows from old DOM list before rebuilding
        let shadowsCleared = false;
        nodes
            .filter(node => node.getAttr('_hoverShadowActive'))
            .sort((a, b) => (a.getAttr('_originalZIndex') || 0) - (b.getAttr('_originalZIndex') || 0))
            .forEach(node => {
                node.setAttrs({
                    shadowColor: node.getAttr('_originalShadowColor'),
                    shadowBlur: node.getAttr('_originalShadowBlur'),
                    shadowOpacity: node.getAttr('_originalShadowOpacity'),
                    shadowOffsetX: node.getAttr('_originalShadowOffsetX'),
                    shadowOffsetY: node.getAttr('_originalShadowOffsetY'),
                    shadowEnabled: node.getAttr('_originalShadowEnabled')
                });
                const zIndex = node.getAttr('_originalZIndex');
                if (typeof zIndex === 'number') node.zIndex(zIndex);
                node.setAttr('_originalShadowColor', undefined);
                node.setAttr('_originalShadowBlur', undefined);
                node.setAttr('_originalShadowOpacity', undefined);
                node.setAttr('_originalShadowOffsetX', undefined);
                node.setAttr('_originalShadowOffsetY', undefined);
                node.setAttr('_originalShadowEnabled', undefined);
                node.setAttr('_originalZIndex', undefined);
                node.setAttr('_hoverShadowActive', false);
                shadowsCleared = true;
            });
        if (shadowsCleared) {
            annotationLayer.batchDraw();
        }

        const markingCountDisplay = document.getElementById('markingCountDisplay');
        if (markingCountDisplay) {
            markingCountDisplay.innerText = getMarkingCount();
        }

        if (nodes.length === 0) {
            const selectAllCheckbox = document.getElementById('selectAllLayers');
            if (selectAllCheckbox) {
                selectAllCheckbox.checked = false;
                selectAllCheckbox.disabled = true;
            }
            listContainer.innerHTML = '<div class="text-center py-5 opacity-50"><i class="bi bi-stack h4 d-block mb-2"></i><span class="small">No shapes drawn yet</span></div>';
            updateCoverageDisplay();
            return;
        }

        const selectAllCheckbox = document.getElementById('selectAllLayers');
        const bulkDeleteBtn = document.getElementById('bulkDeleteLayers');
        const bulkVisBtn = document.getElementById('bulkVisibilityLayers');

        if (selectAllCheckbox) {
            selectAllCheckbox.disabled = false;
            const checkedCount = nodes.filter(obj => obj.getAttr('_checkboxSelected')).length;
            selectAllCheckbox.checked = checkedCount > 0 && checkedCount === nodes.length;
            selectAllCheckbox.indeterminate = checkedCount > 0 && checkedCount < nodes.length;
        }

        const activeNodes = transformer.nodes();
        const hasChecked = nodes.some(obj => obj.getAttr('_checkboxSelected') || activeNodes.includes(obj));

        if (bulkDeleteBtn) {
            bulkDeleteBtn.disabled = !hasChecked;
            bulkDeleteBtn.style.opacity = hasChecked ? '1' : '0.5';
            bulkDeleteBtn.style.cursor = hasChecked ? 'pointer' : 'default';
        }

        if (bulkVisBtn) {
            bulkVisBtn.disabled = !hasChecked;
            bulkVisBtn.style.opacity = hasChecked ? '1' : '0.5';
            bulkVisBtn.style.cursor = hasChecked ? 'pointer' : 'default';
        }

        listContainer.innerHTML = '';

        // Group nodes by datasetId
        const labelsMap = {};
        nodes.forEach(node => {
            const labelName = node.getAttr('labelName') || 'Unknown';
            const labelColor = node.getAttr('labelColor') || '#ccc';
            const datasetId = node.getAttr('datasetId') || 'unknown';

            if (!labelsMap[datasetId]) {
                labelsMap[datasetId] = {
                    name: labelName,
                    color: labelColor,
                    nodes: []
                };
            }
            labelsMap[datasetId].nodes.push(node);
        });

        Object.keys(labelsMap).forEach(datasetId => {
            const group = labelsMap[datasetId];
            const representative = group.nodes[0];
            const labelName = group.name;
            const labelColor = group.color;
            const siblings = group.nodes;

            const item = document.createElement('div');
            item.className = 'layer-item d-flex align-items-center';
            item.style.minHeight = '38px';
            item.setAttribute('data-obj-id', representative.getAttr('id') || '');

            const attrParts = [];
            siblings.forEach(s => {
                const attrs = s.getAttr('attributes');
                if (attrs && typeof attrs === 'object') {
                    Object.entries(attrs).forEach(([k, v]) => {
                        if (v) {
                            attrParts.push(k);
                            attrParts.push(v);
                        }
                    });
                }
                const cmd = s.getAttr('command');
                if (cmd) {
                    attrParts.push(cmd);
                }
            });
            const attrText = attrParts.join(' ');
            item.setAttribute('data-search-text', (labelName + ' ' + attrText).toLowerCase());

            item.onmouseenter = () => {
                let changed = false;
                siblings.forEach(s => {
                    if (!s.visible() || activeNodes.includes(s)) return;

                    // Save original shadow settings
                    if (!s.getAttr('_hoverShadowActive')) {
                        s.setAttr('_hoverShadowActive', true);
                        s.setAttr('_originalShadowColor', s.shadowColor());
                        s.setAttr('_originalShadowBlur', s.shadowBlur());
                        s.setAttr('_originalShadowOpacity', s.shadowOpacity());
                        s.setAttr('_originalShadowOffsetX', s.shadowOffsetX());
                        s.setAttr('_originalShadowOffsetY', s.shadowOffsetY());
                        s.setAttr('_originalShadowEnabled', s.shadowEnabled());
                        // Raise above any overlapping shapes drawn later so the glow
                        // isn't immediately painted over by whatever sits on top of it.
                        s.setAttr('_originalZIndex', s.getZIndex());
                        s.moveToTop();
                    }

                    s.setAttrs({
                        shadowColor: s.getAttr('labelColor') || labelColor,
                        shadowBlur: 30,
                        shadowOpacity: 1,
                        shadowOffsetX: 0,
                        shadowOffsetY: 0,
                        shadowEnabled: true
                    });
                    changed = true;
                });
                if (changed) annotationLayer.batchDraw();
            };
            item.onmouseleave = () => {
                let changed = false;
                siblings
                    .filter(s => s.getAttr('_hoverShadowActive'))
                    .sort((a, b) => (a.getAttr('_originalZIndex') || 0) - (b.getAttr('_originalZIndex') || 0))
                    .forEach(s => {
                        s.setAttrs({
                            shadowColor: s.getAttr('_originalShadowColor'),
                            shadowBlur: s.getAttr('_originalShadowBlur'),
                            shadowOpacity: s.getAttr('_originalShadowOpacity'),
                            shadowOffsetX: s.getAttr('_originalShadowOffsetX'),
                            shadowOffsetY: s.getAttr('_originalShadowOffsetY'),
                            shadowEnabled: s.getAttr('_originalShadowEnabled')
                        });
                        const zIndex = s.getAttr('_originalZIndex');
                        if (typeof zIndex === 'number') s.zIndex(zIndex);
                        s.setAttr('_originalShadowColor', undefined);
                        s.setAttr('_originalShadowBlur', undefined);
                        s.setAttr('_originalShadowOpacity', undefined);
                        s.setAttr('_originalShadowOffsetX', undefined);
                        s.setAttr('_originalShadowOffsetY', undefined);
                        s.setAttr('_originalShadowEnabled', undefined);
                        s.setAttr('_originalZIndex', undefined);
                        s.setAttr('_hoverShadowActive', false);
                        changed = true;
                    });
                if (changed) annotationLayer.batchDraw();
            };

            // Highlight the row if ANY sibling is selected
            const isActive = siblings.some(s => activeNodes.includes(s));
            if (isActive) {
                item.classList.add('active');
            }

            // Checkbox
            const checkbox = document.createElement('input');
            checkbox.type = 'checkbox';
            checkbox.className = 'layer-checkbox';
            checkbox.style.marginRight = '10px';
            checkbox.style.cursor = 'pointer';
            checkbox.checked = siblings.every(s => !!s.getAttr('_checkboxSelected'));
            checkbox.onclick = (e) => {
                e.stopPropagation();
                siblings.forEach(s => { s.setAttr('_checkboxSelected', checkbox.checked); });
                updateLayerList();
            };

            // Color Box
            const colorBox = document.createElement('span');
            colorBox.className = 'color-indicator';
            colorBox.style.width = '6px';
            colorBox.style.height = '18px';
            colorBox.style.backgroundColor = labelColor;
            colorBox.style.borderRadius = '10px';
            colorBox.style.marginRight = '12px';
            colorBox.style.flexShrink = '0';

            // Text / Attributes display
            const textContainer = document.createElement('div');
            textContainer.className = 'flex-grow-1';
            textContainer.style.overflow = 'visible';

            let attrString = "";
            if (representative.getAttr('attributes') && typeof representative.getAttr('attributes') === 'object') {
                const ignoredKeys = ['isBrushStroke', 'strokeWidth', 'globalCompositeOperation', 'eraserPaths'];
                attrString = Object.entries(representative.getAttr('attributes'))
                    .filter(([key, val]) => !ignoredKeys.includes(key) && val && val.toString().trim() !== "")
                    .map(([key, val]) => {
                        const c = getAttributeAnswerColor(key, val);
                        return `
                        <div class="mb-1">
                            <div class="fw-bold" style="font-size: 10px; color: #666; line-height: 1.2;">${key}</div>
                            <div style="font-size: 11px; color: ${c.solid}; padding: 2px 8px; line-height: 1.3; border-left: 3px solid ${c.solid}; background: ${c.tint}; border-radius: 0 4px 4px 0; margin-top: 2px; display: inline-block; font-weight: 600;">${val}</div>
                        </div>
                    `;
                    })
                    .join('');
            }

            textContainer.innerHTML = `
                <div style="min-height: 18px;"></div>
                ${attrString ? `<div class="text-muted mt-1" style="word-break: break-word;">${attrString}</div>` : ''}
            `;

            // Click on row selects the representative/siblings
            item.onclick = () => {
                if (window.SEGMENTATION_CONFIG.readOnly) return;
                const selectableSiblings = siblings.filter(s => !s.getAttr('locked'));
                if (selectableSiblings.length > 0) {
                    transformer.nodes(selectableSiblings);
                    if (window.renderAttributeForm) {
                        window.renderAttributeForm(representative.attrs);
                    }
                    annotationLayer.batchDraw();
                    updateLayerList();
                    updateOpacitySliderFromSelection();
                }
            };

            // Visibility Button
            const isVisible = siblings.some(s => s.visible());
            const visibilityBtn = document.createElement('button');
            visibilityBtn.className = 'visibility-layer-btn btn btn-xs border-0 p-0';
            visibilityBtn.style.marginLeft = '10px';
            visibilityBtn.innerHTML = isVisible ? '<i class="bi bi-eye" style="font-size:11px;"></i>' : '<i class="bi bi-eye-slash text-muted" style="font-size:11px;"></i>';
            visibilityBtn.title = isVisible ? 'Hide Layer' : 'Show Layer';
            visibilityBtn.style.background = 'transparent';
            visibilityBtn.style.color = isVisible ? '#1d55e8' : '#6c757d';
            visibilityBtn.style.cursor = 'pointer';

            visibilityBtn.onclick = (e) => {
                e.stopPropagation();
                // Deselect before hiding
                if (siblings.some(s => activeNodes.includes(s))) {
                    transformer.nodes([]);
                }
                const nextVisible = !isVisible;
                siblings.forEach(s => s.visible(nextVisible));
                annotationLayer.batchDraw();
                updateLayerList();
            };

            // Lock Button
            const isLocked = siblings.some(s => !!s.getAttr('locked'));
            const lockBtn = document.createElement('button');
            lockBtn.className = 'lock-layer-btn btn btn-xs border-0 p-0';
            lockBtn.style.marginLeft = '10px';
            lockBtn.innerHTML = isLocked ? '<i class="bi bi-lock-fill" style="font-size:11px; color: #dc3545;"></i>' : '<i class="bi bi-unlock" style="font-size:11px; color: #6c757d;"></i>';
            lockBtn.title = isLocked ? 'Unlock Layer' : 'Lock Layer';
            lockBtn.style.background = 'transparent';
            lockBtn.style.cursor = 'pointer';

            if (window.SEGMENTATION_CONFIG.readOnly) {
                lockBtn.style.display = 'none';
            } else {
                lockBtn.onclick = (e) => {
                    e.stopPropagation();
                    const nextLocked = !isLocked;
                    siblings.forEach(s => {
                        s.setAttr('locked', nextLocked);
                        if (nextLocked) {
                            // If in transformer, remove it
                            const currentSel = transformer.nodes();
                            transformer.nodes(currentSel.filter(n => n !== s));
                        }
                    });
                    annotationLayer.batchDraw();
                    updateLayerList();
                    triggerAutoSave();
                };
            }

            // Command Button
            const buttonsContainer = document.createElement('div');
            buttonsContainer.className = 'd-flex align-items-center';

            const commandBtn = document.createElement('button');
            commandBtn.className = 'command-layer-btn btn btn-xs border-0 p-0';
            commandBtn.style.cssText = 'margin-left:10px;background:transparent;cursor:pointer;padding:0;flex-shrink:0;';
            const commandTitle = representative.getAttr('command') || 'Add command';
            commandBtn.innerHTML = '<i class="bi bi-chat-square-text" style="color:#1d55e8;font-size:11px;"></i>';
            commandBtn.setAttribute('data-toggle', 'tooltip');
            commandBtn.setAttribute('data-placement', 'left');
            commandBtn.setAttribute('title', commandTitle);
            $(commandBtn).tooltip({ trigger: 'hover', boundary: 'viewport' });

            const config = window.SEGMENTATION_CONFIG || {};
            const stageTypeUpper = (config.stageType || '').toUpperCase();
            const stageNameUpper = (config.stageName || '').toUpperCase();
            const isProduction = stageTypeUpper === 'PRODUCTION' || stageNameUpper.startsWith('PRO');

            if ((window.SEGMENTATION_CONFIG.readOnly || isProduction) && !representative.getAttr('command')) {
                commandBtn.style.display = 'none';
            }

            commandBtn.onclick = (e) => {
                e.stopPropagation();
                if (!window.SEGMENTATION_CONFIG.readOnly && !isProduction && typeof window.openAnnotationCommandModal === 'function') {
                    const mockObj = new Proxy({
                        id: representative.getAttr('id'),
                        labelName: representative.getAttr('labelName'),
                    }, {
                        get(target, prop) {
                            if (prop === 'command') {
                                return representative.getAttr('command');
                            }
                            return target[prop];
                        },
                        set(target, prop, value) {
                            if (prop === 'command') {
                                siblings.forEach(s => s.setAttr('command', value));
                                annotationLayer.batchDraw();
                                return true;
                            }
                            target[prop] = value;
                            return true;
                        },
                        deleteProperty(target, prop) {
                            if (prop === 'command') {
                                siblings.forEach(s => s.setAttr('command', undefined));
                                annotationLayer.batchDraw();
                                return true;
                            }
                            delete target[prop];
                            return true;
                        }
                    });
                    window.openAnnotationCommandModal(mockObj);
                }
            };

            // Edit Classification Button
            const editBtn = document.createElement('button');
            editBtn.className = 'edit-layer-btn btn btn-xs border-0 p-0';
            editBtn.style.marginLeft = '10px';
            editBtn.innerHTML = '<i class="bi bi-pencil-square" style="font-size:11px;"></i>';
            editBtn.title = 'Edit Classification';
            editBtn.style.background = 'transparent';
            editBtn.style.color = '#1d55e8';
            editBtn.style.cursor = 'pointer';

            if (!window.SEGMENTATION_CONFIG.readOnly && !isLocked) {
                editBtn.onclick = (e) => {
                    e.stopPropagation();
                    if (typeof window.openClassificationModal === 'function') {
                        const mockObj = {
                            id: representative.getAttr('id'),
                            datasetId: representative.getAttr('datasetId'),
                            labelName: representative.getAttr('labelName')
                        };
                        window.openClassificationModal(mockObj);
                    }
                };
            } else {
                editBtn.style.display = 'none';
            }

            // Delete Button
            const deleteBtn = document.createElement('button');
            deleteBtn.className = 'delete-layer-btn btn btn-xs border-0 p-0';
            deleteBtn.style.marginLeft = '6px';
            deleteBtn.innerHTML = '<i class="bi bi-x-lg" style="font-size:11px;"></i>';
            deleteBtn.title = 'Delete Layer';
            deleteBtn.style.background = 'transparent';
            deleteBtn.style.color = '#dc3545';
            deleteBtn.style.cursor = 'pointer';

            if (!window.SEGMENTATION_CONFIG.readOnly && !isLocked) {
                deleteBtn.onclick = (e) => {
                    e.stopPropagation();
                    deleteLayerObject(representative, siblings);
                };
            } else {
                deleteBtn.style.display = 'none';
            }

            buttonsContainer.appendChild(commandBtn);
            buttonsContainer.appendChild(editBtn);
            buttonsContainer.appendChild(deleteBtn);

            const itemLabel = document.createElement('div');
            itemLabel.className = 'layer-item-label';
            itemLabel.innerHTML = `${labelName}`;
            item.appendChild(itemLabel);

            item.appendChild(colorBox);
            item.appendChild(checkbox);
            item.appendChild(textContainer);
            item.appendChild(visibilityBtn);
            item.appendChild(lockBtn);
            item.appendChild(buttonsContainer);

            listContainer.appendChild(item);
        });

        if (selectAllCheckbox) {
            selectAllCheckbox.onclick = () => {
                const checked = selectAllCheckbox.checked;
                nodes.forEach(n => n.setAttr('_checkboxSelected', checked));
                updateLayerList();
            };
        }

        const bulkDeleteHandler = () => {
            const checkedNodes = nodes.filter(n => n.getAttr('_checkboxSelected'));
            if (checkedNodes.length === 0) return;
            Swal.fire({
                title: 'Confirm Bulk Delete',
                text: `Are you sure you want to delete the selected ${checkedNodes.length} annotations?`,
                icon: 'warning',
                showCancelButton: true,
                confirmButtonColor: '#d33',
                cancelButtonColor: '#3085d6',
                confirmButtonText: 'Yes, delete them!',
                cancelButtonText: 'Cancel'
            }).then((result) => {
                if (result.isConfirmed) {
                    saveHistory();
                    const currentSel = transformer.nodes();
                    transformer.nodes(currentSel.filter(n => !checkedNodes.includes(n)));
                    checkedNodes.forEach(n => n.destroy());
                    annotationLayer.batchDraw();
                    triggerAutoSave();
                    updateLayerList();
                }
            });
        };

        const bulkVisHandler = () => {
            const checkedNodes = nodes.filter(n => n.getAttr('_checkboxSelected'));
            if (checkedNodes.length === 0) return;
            const anyVisible = checkedNodes.some(n => n.visible());
            const nextVis = !anyVisible;
            checkedNodes.forEach(n => n.visible(nextVis));
            annotationLayer.batchDraw();
            updateLayerList();
        };

        if (bulkDeleteBtn) {
            bulkDeleteBtn.onclick = bulkDeleteHandler;
        }
        if (bulkVisBtn) {
            bulkVisBtn.onclick = bulkVisHandler;
        }

        updateFloatingLabel();
        updateCoverageDisplay();
    }
    window.updateLayerList = updateLayerList;

    // Render a shape as a fully-opaque solid mask, ignoring any holes (_eraserPaths /
    // _subtractorNodes).  Used to compute the "original territory" of a deleted shape so
    // its footprint can be subtracted from overlapping shapes.
    function renderNodeSolid(node, width, height, scale) {
        const canvas = document.createElement('canvas');
        canvas.width = Math.floor(width * scale) || 1;
        canvas.height = Math.floor(height * scale) || 1;
        const ctx = canvas.getContext('2d');
        ctx.imageSmoothingEnabled = false;
        if (scale !== 1) ctx.scale(scale, scale);

        const type = node.getClassName().toLowerCase();

        if (type === 'rect') {
            const sx = node.scaleX() || 1, sy = node.scaleY() || 1;
            ctx.fillStyle = 'rgba(255,255,255,1)';
            ctx.fillRect(node.x(), node.y(), node.width() * sx, node.height() * sy);
        } else if (type === 'ellipse' || type === 'circle') {
            const rx = (type === 'circle' ? node.radius() : node.radiusX()) * (node.scaleX() || 1);
            const ry = (type === 'circle' ? node.radius() : node.radiusY()) * (node.scaleY() || 1);
            ctx.fillStyle = 'rgba(255,255,255,1)';
            ctx.beginPath();
            ctx.ellipse(node.x(), node.y(), rx, ry, 0, 0, 2 * Math.PI);
            ctx.fill();
        } else if (type === 'line') {
            const pts = node.points();
            if (node.closed() && pts.length >= 6) {
                ctx.fillStyle = 'rgba(255,255,255,1)';
                ctx.beginPath();
                ctx.moveTo(pts[0], pts[1]);
                for (let i = 2; i < pts.length; i += 2) ctx.lineTo(pts[i], pts[i + 1]);
                ctx.closePath();
                ctx.fill();
            }
        } else if (type === 'image') {
            const img = node.image();
            if (img) {
                const sx = node.scaleX() || 1, sy = node.scaleY() || 1;
                ctx.drawImage(img, node.x(), node.y(), node.width() * sx, node.height() * sy);
            }
        }
        return canvas;
    }

    // Pixel-subtract solidMaskCanvas from subNode.  The subNode is destroyed and
    // replaced with a Konva.Image containing only the surviving pixels.
    // Returns true if any pixels were actually removed.
    // Pixel-subtract solidMaskCanvas from subNode.  The subNode is destroyed and
    // replaced with a Konva.Image containing only the surviving pixels.
    // Returns true if any pixels were actually removed.
    function subtractShapeFromNode(subNode, solidMaskCanvas, scale) {
        if (!subNode || !subNode.getParent()) return false;
        const w = originalWidth, h = originalHeight;
        const scaledW = Math.floor(w * scale) || 1;
        const scaledH = Math.floor(h * scale) || 1;

        const subCanvas = renderNodesToCanvas([subNode], w, h, scale);
        const subCtx = subCanvas.getContext('2d');

        // Count opaque pixels before the subtraction so we can detect a no-op.
        const beforeData = subCtx.getImageData(0, 0, scaledW, scaledH).data;
        let beforeCount = 0;
        for (let i = 3; i < beforeData.length; i += 4) if (beforeData[i] > 0) beforeCount++;

        // IMPORTANT: renderNodesToCanvas leaves a scale() transform on the context.
        // Reset to identity so drawImage operates in physical pixel coordinates;
        // without this the solidMaskCanvas is drawn at the wrong scale.
        subCtx.setTransform(1, 0, 0, 1, 0, 0);
        subCtx.globalCompositeOperation = 'destination-out';
        subCtx.imageSmoothingEnabled = false;
        subCtx.drawImage(solidMaskCanvas, 0, 0);
        subCtx.globalCompositeOperation = 'source-over';

        const afterData = subCtx.getImageData(0, 0, scaledW, scaledH).data;
        let minX = scaledW, minY = scaledH, maxX = 0, maxY = 0, afterCount = 0;
        for (let y = 0; y < scaledH; y++) {
            for (let x = 0; x < scaledW; x++) {
                if (afterData[(y * scaledW + x) * 4 + 3] > 0) {
                    afterCount++;
                    if (x < minX) minX = x;
                    if (y < minY) minY = y;
                    if (x > maxX) maxX = x;
                    if (y > maxY) maxY = y;
                }
            }
        }

        // Nothing was erased — leave the node completely untouched.
        if (afterCount === beforeCount) return false;

        const labelName = subNode.getAttr('labelName');
        const labelColor = subNode.getAttr('labelColor');
        const datasetId = subNode.getAttr('datasetId');
        const nodeId = subNode.id();
        const attributes = subNode.getAttr('attributes') || {};
        const opacity = subNode.opacity();
        const locked = subNode.getAttr('locked') !== false;

        subNode.destroy();

        if (afterCount === 0) return true; // fully erased

        const cropW = maxX - minX + 1;
        const cropH = maxY - minY + 1;
        const cropCanvas = document.createElement('canvas');
        cropCanvas.width = cropW;
        cropCanvas.height = cropH;
        const cropCtx = cropCanvas.getContext('2d');
        cropCtx.imageSmoothingEnabled = false;
        cropCtx.drawImage(subCanvas, minX, minY, cropW, cropH, 0, 0, cropW, cropH);

        const dataUrl = cropCanvas.toDataURL();
        const newNode = new Konva.Image({
            imageSmoothingEnabled: false,
            x: minX / scale,
            y: minY / scale,
            image: cropCanvas,
            width: cropW / scale,
            height: cropH / scale,
            opacity: opacity,
        });
        if (nodeId) newNode.id(nodeId);
        newNode.setAttrs({
            labelName, labelColor, datasetId,
            attributes, isMask: true, isBoundary: true, locked,
            src: dataUrl,
            _srcCache: dataUrl,
        });
        makeShapeErasable(newNode);
        addAnnotationShape(newNode);
        return true;
    }

    // When shapes are deleted, subtract their combined pixel footprint from every
    // annotation node of a different label so the intersection area is cleanly erased.
    function cleanupSubtractorNodesOnDelete(deletedNodes) {
        if (!originalWidth || !originalHeight || !deletedNodes || !deletedNodes.length) return;

        const scale = getProcessingScale(originalWidth, originalHeight);
        const scaledW = Math.floor(originalWidth * scale) || 1;
        const scaledH = Math.floor(originalHeight * scale) || 1;

        const deletedIds = new Set(deletedNodes.map(n => n.id()).filter(Boolean));
        const deletedDatasetIds = new Set(
            deletedNodes.map(n => n.getAttr('datasetId')).filter(Boolean)
        );

        // Build one combined solid mask covering all shapes being deleted.
        const solidCanvas = document.createElement('canvas');
        solidCanvas.width = scaledW;
        solidCanvas.height = scaledH;
        const solidCtx = solidCanvas.getContext('2d');
        solidCtx.imageSmoothingEnabled = false;
        deletedNodes.forEach(node => {
            const m = renderNodeSolid(node, originalWidth, originalHeight, scale);
            solidCtx.drawImage(m, 0, 0);
        });

        // Guard: if the mask is entirely empty there is nothing to subtract.
        const maskData = solidCtx.getImageData(0, 0, scaledW, scaledH).data;
        let hasMask = false;
        for (let i = 3; i < maskData.length; i += 4) {
            if (maskData[i] > 0) { hasMask = true; break; }
        }
        if (!hasMask) return;

        // Collect every remaining node that belongs to a different label AND is UNLOCKED!
        const others = annotationLayer.getChildren().filter(node => {
            if (node === transformer || !node.getParent()) return false;
            const id = node.id();
            if (id && deletedIds.has(id)) return false;
            if (node.getAttr('locked') !== false) return false; // ONLY crop unlocked layers
            const ds = node.getAttr('datasetId');
            return ds && !deletedDatasetIds.has(ds);
        });

        others.forEach(node => subtractShapeFromNode(node, solidCanvas, scale));
    }

    function deleteLayerObject(representative, siblings) {
        if (!representative || window.SEGMENTATION_CONFIG.readOnly) return;

        const labelName = representative.getAttr('labelName') || 'this annotation';

        Swal.fire({
            title: 'Confirm Delete',
            text: `Are you sure you want to delete "${labelName}"?`,
            icon: 'warning',
            showCancelButton: true,
            confirmButtonColor: '#d33',
            cancelButtonColor: '#3085d6',
            confirmButtonText: 'Yes, delete it!',
            cancelButtonText: 'Cancel'
        }).then((result) => {
            if (result.isConfirmed) {
                // Separate deleted siblings into vector shapes vs raster images
                const vectorSiblings = [];
                const rasterSiblings = [];
                siblings.forEach(s => {
                    if (isVectorBoundaryShape(s)) vectorSiblings.push(s);
                    else rasterSiblings.push(s);
                });

                // Process vector siblings: keep them on layer but make them hidden subtractors
                vectorSiblings.forEach(node => {
                    node.visible(false);
                    node.setAttr('isUndoSubtractor', true);
                    
                    const delBox = node.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                    annotationLayer.getChildren().forEach(olderNode => {
                        if (olderNode === transformer || olderNode === node || siblings.includes(olderNode) || olderNode.getAttr('isUndoSubtractor')) return;
                        if (!isVectorBoundaryShape(olderNode)) return;
                        if (olderNode.getAttr('locked') !== false) return; // DO NOT CUT LOCKED SHAPES
                        
                        const olderBox = olderNode.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                        const intersects = !(delBox.x > olderBox.x + olderBox.width ||
                            delBox.x + delBox.width < olderBox.x ||
                            delBox.y > olderBox.y + olderBox.height ||
                            delBox.y + delBox.height < olderBox.y);
                            
                        if (intersects) {
                            if (node.getAttr('datasetId') === olderNode.getAttr('datasetId')) return;
                            
                            const subtractors = olderNode.getAttr('_subtractorNodes') || [];
                            if (subtractors.indexOf(node.id()) === -1) {
                                subtractors.push(node.id());
                            }
                            olderNode.setAttr('_subtractorNodes', subtractors);
                            makeShapeErasable(olderNode);
                        }
                    });
                });

                // Process raster siblings: use legacy raster cleanup
                const unlockedRasterSiblings = rasterSiblings.filter(s => s.getAttr('locked') === false);
                if (unlockedRasterSiblings.length > 0) {
                    cleanupSubtractorNodesOnDelete(unlockedRasterSiblings);
                }

                saveHistory();
                
                // Remove any transformer references
                transformer.nodes(transformer.nodes().filter(n => n.getParent()));
                const currentSel = transformer.nodes();
                transformer.nodes(currentSel.filter(n => !siblings.includes(n)));
                
                rasterSiblings.forEach(s => s.destroy());
                
                annotationLayer.batchDraw();
                triggerAutoSave();
                updateLayerList();

                var panel = document.getElementById('attributePanel');
                if (panel) panel.style.display = 'none';
            }
        });
    }

    function applyLayerSearchFilter() {
        const searchInput = document.getElementById('layerSearchInput');
        if (!searchInput) return;
        const query = (searchInput.value || '').trim().toLowerCase();
        const items = document.querySelectorAll('#layerList .layer-item');

        // Single pass: build both lookup maps and clear prior search state together.
        // Previously this called getChildren() three times (two separate forEach loops
        // plus one filter() per DOM item), causing O(N²) work at 1000+ annotations.
        const nodesById = {};
        const siblingsByDatasetId = {};
        let needsDraw = false;

        annotationLayer.getChildren().forEach(node => {
            if (node === transformer) return;
            const id = node.getAttr('id');
            if (id) nodesById[id] = node;
            const dsId = node.getAttr('datasetId');
            if (dsId) {
                if (!siblingsByDatasetId[dsId]) siblingsByDatasetId[dsId] = [];
                siblingsByDatasetId[dsId].push(node);
            }
            if (node.getAttr('_searchHighlightActive')) {
                clearSearchHighlight(node);
                needsDraw = true;
            }
            if (node.getAttr('_hiddenBySearch')) {
                node.visible(node.getAttr('_visibleBeforeSearch') !== false);
                node.setAttr('_hiddenBySearch', undefined);
                node.setAttr('_visibleBeforeSearch', undefined);
                needsDraw = true;
            }
        });

        if (!query) {
            items.forEach(item => item.style.setProperty('display', '', ''));
            if (needsDraw) {
                annotationLayer.batchDraw();
            }
            return;
        }

        const matches = [];
        items.forEach(item => {
            const objId = item.getAttribute('data-obj-id');
            const representative = objId ? nodesById[objId] : null;
            const text = item.getAttribute('data-search-text') || '';
            const isMatch = text.includes(query);

            const dsId = representative ? representative.getAttr('datasetId') : null;
            const siblings = (dsId && siblingsByDatasetId[dsId]) || [];

            if (isMatch) {
                item.style.setProperty('display', '', '');
                if (representative) {
                    matches.push({ representative, siblings });
                }
            } else {
                item.style.setProperty('display', 'none', 'important');
                siblings.forEach(s => {
                    if (!s.getAttr('_hiddenBySearch')) {
                        s.setAttr('_visibleBeforeSearch', s.visible());
                        s.setAttr('_hiddenBySearch', true);
                        s.visible(false);
                        needsDraw = true;
                    }
                });
            }
        });

        matches.forEach(({ representative, siblings }) => {
            siblings.forEach(s => {
                applySearchHighlight(s, representative.getAttr('labelColor') || '#1d55e8');
            });
            needsDraw = true;
        });

        if (needsDraw) {
            annotationLayer.batchDraw();
        }
    }

    function applySearchHighlight(node, color) {
        if (node.getAttr('_searchHighlightActive')) return;

        if (node.getAttr('_originalShadowColor') === undefined) {
            node.setAttr('_originalShadowColor', node.shadowColor());
            node.setAttr('_originalShadowBlur', node.shadowBlur());
            node.setAttr('_originalShadowOpacity', node.shadowOpacity());
            node.setAttr('_originalShadowOffsetX', node.shadowOffsetX());
            node.setAttr('_originalShadowOffsetY', node.shadowOffsetY());
            node.setAttr('_originalShadowEnabled', node.shadowEnabled());
        }

        node.setAttrs({
            shadowColor: color,
            shadowBlur: 20,
            shadowOpacity: 0.8,
            shadowOffsetX: 0,
            shadowOffsetY: 0,
            shadowEnabled: true,
            _searchHighlightActive: true
        });
    }

    function clearSearchHighlight(node) {
        if (!node.getAttr('_searchHighlightActive')) return;

        node.setAttrs({
            shadowColor: node.getAttr('_originalShadowColor'),
            shadowBlur: node.getAttr('_originalShadowBlur'),
            shadowOpacity: node.getAttr('_originalShadowOpacity'),
            shadowOffsetX: node.getAttr('_originalShadowOffsetX'),
            shadowOffsetY: node.getAttr('_originalShadowOffsetY'),
            shadowEnabled: node.getAttr('_originalShadowEnabled'),
            _searchHighlightActive: undefined
        });
        node.setAttr('_originalShadowColor', undefined);
        node.setAttr('_originalShadowBlur', undefined);
        node.setAttr('_originalShadowOpacity', undefined);
        node.setAttr('_originalShadowOffsetX', undefined);
        node.setAttr('_originalShadowOffsetY', undefined);
        node.setAttr('_originalShadowEnabled', undefined);
    }

    let _layerSearchDebounceTimer = null;
    document.addEventListener('input', function (e) {
        if (e.target && e.target.id === 'layerSearchInput') {
            clearTimeout(_layerSearchDebounceTimer);
            _layerSearchDebounceTimer = setTimeout(applyLayerSearchFilter, 150);
        }
    });

    window.applyLayerSearchFilter = applyLayerSearchFilter;

    function injectCoverageUI() {
        const backBtn = document.querySelector('a[title="Back to Workflow"]') || document.querySelector('.bi-arrow-left')?.closest('a');
        if (backBtn && !document.getElementById('pixelCoverageContainer')) {
            const container = document.createElement('span');
            container.id = 'pixelCoverageContainer';
            container.style.marginRight = '10px';
            container.style.display = 'inline-flex';
            container.style.flexDirection = 'column';
            container.style.alignItems = 'center';
            container.style.gap = '2px';

            container.innerHTML = `
                <strong id="pixelCoverageVal" class="text-primary font-monospace" style="font-size: 0.72rem; line-height: 1;">0.00%</strong>
                <div class="progress" style="width: 70px; height: 5px; background-color: var(--bs-progress-bg, rgba(29, 85, 232, 0.12)); border-radius: 3px; overflow: hidden; margin-bottom: 0;">
                    <div id="pixelCoverageBar" class="progress-bar bg-primary" role="progressbar" style="width: 0%; height: 100%; transition: width 0.3s ease;"></div>
                </div>
            `;
            backBtn.parentNode.insertBefore(container, backBtn);
        }
    }

    function updateCoverageDisplay() {
        if (!originalWidth || !originalHeight) return;

        let coverageValEl = document.getElementById('pixelCoverageVal');
        if (!coverageValEl) {
            injectCoverageUI();
            coverageValEl = document.getElementById('pixelCoverageVal');
        }

        if (coverageDebounceTimeout) {
            clearTimeout(coverageDebounceTimeout);
        }

        coverageDebounceTimeout = setTimeout(() => {
            if (isCalculatingCoverage) return;
            isCalculatingCoverage = true;

            try {
                const percentage = calculateMaskedCoverage();
                cachedCoverage = percentage;

                const displayCoverage = formatCoverage(percentage);

                if (coverageValEl) {
                    coverageValEl.textContent = displayCoverage + '%';
                }

                const coverageBarEl = document.getElementById('pixelCoverageBar');
                if (coverageBarEl) {
                    coverageBarEl.style.width = displayCoverage + '%';
                    coverageBarEl.setAttribute('aria-valuenow', displayCoverage);
                }
            } catch (err) {
                console.error("Error calculating pixel coverage:", err);
            } finally {
                isCalculatingCoverage = false;
            }
        }, 300);
    }

    function calculateMaskedCoverage() {
        if (!originalWidth || !originalHeight) return 0;

        try {
            const scale = getProcessingScale(originalWidth, originalHeight);
            const scaledW = Math.floor(originalWidth * scale) || 1;
            const scaledH = Math.floor(originalHeight * scale) || 1;

            const snap = renderNodesToCanvas(getExportableAnnotationNodes(), originalWidth, originalHeight, scale);
            const snapCtx = snap.getContext('2d', { willReadFrequently: true });
            const data = snapCtx.getImageData(0, 0, scaledW, scaledH).data;

            let maskedPixels = 0;
            const total = scaledW * scaledH;

            for (let i = 0; i < total; i++) {
                if (data[i * 4 + 3] > 0) {
                    maskedPixels++;
                }
            }

            return (maskedPixels / total) * 100;
        } catch (err) {
            console.error("Error in calculateMaskedCoverage:", err);
            return 0;
        }
    }

    function renderNodesToCanvas(nodes, width, height, scale = 1) {
        const canvas = document.createElement('canvas');
        canvas.width = Math.floor(width * scale) || 1;
        canvas.height = Math.floor(height * scale) || 1;
        const ctx = canvas.getContext('2d');
        ctx.imageSmoothingEnabled = false;
        ctx.webkitImageSmoothingEnabled = false;
        ctx.mozImageSmoothingEnabled = false;
        ctx.msImageSmoothingEnabled = false;
        if (scale !== 1) {
            ctx.scale(scale, scale);
        }

        let tmp = null;
        let tctx = null;

        nodes.forEach(node => {
            if (!node.visible()) return;

            const type = node.getClassName().toLowerCase();

            // Erasable vector shapes with holes are rendered in isolation (own
            // canvas) so the destination-out holes don't bleed into other shapes,
            // then composited 1:1 onto the main canvas.
            const eraserPaths = node.getAttr('_eraserPaths');
            const subtractors = node.getAttr('_subtractorNodes');
            const hasEraser = eraserPaths && eraserPaths.length;
            const hasSubtractors = subtractors && subtractors.length;

            if ((hasEraser || hasSubtractors) &&
                (type === 'rect' || type === 'ellipse' || type === 'line')) {
                
                if (!tmp) {
                    tmp = document.createElement('canvas');
                    tmp.width = canvas.width;
                    tmp.height = canvas.height;
                    tctx = tmp.getContext('2d');
                    tctx.imageSmoothingEnabled = false;
                } else {
                    tctx.clearRect(0, 0, tmp.width, tmp.height);
                }
                
                tctx.save();
                if (scale !== 1) tctx.scale(scale, scale);
                // Draw base fill in image space.
                if (type === 'line') {
                    const points = node.points();
                    if (points && points.length >= 4) {
                        tctx.beginPath();
                        tctx.moveTo(points[0], points[1]);
                        for (let i = 2; i < points.length; i += 2) tctx.lineTo(points[i], points[i + 1]);
                        if (node.closed()) {
                            tctx.closePath();
                            tctx.fillStyle = node.fill() || '#000000';
                            tctx.fill();
                            tctx.lineWidth = 1;
                            tctx.strokeStyle = node.fill() || '#000000';
                            tctx.stroke();
                        } else {
                            tctx.strokeStyle = node.stroke() || '#000000';
                            tctx.lineWidth = node.strokeWidth() || 1;
                            tctx.lineCap = node.lineCap() || 'round';
                            tctx.lineJoin = node.lineJoin() || 'round';
                            tctx.stroke();
                        }
                    }
                } else if (type === 'rect') {
                    tctx.beginPath();
                    tctx.rect(node.x(), node.y(), node.width() * (node.scaleX() || 1), node.height() * (node.scaleY() || 1));
                    tctx.fillStyle = node.fill() || '#000000';
                    tctx.fill();
                } else {
                    const rx = node.radiusX() * (node.scaleX() || 1);
                    const ry = node.radiusY() * (node.scaleY() || 1);
                    tctx.beginPath();
                    tctx.ellipse(node.x(), node.y(), rx, ry, 0, 0, 2 * Math.PI);
                    tctx.fillStyle = node.fill() || '#000000';
                    tctx.fill();
                }
                
                if (hasEraser) punchEraserHolesImageSpace(tctx, node);
                
                if (hasSubtractors) {
                    const layer = node.getLayer();
                    if (layer) {
                        tctx.save();
                        tctx.globalCompositeOperation = 'destination-out';
                        tctx.fillStyle = '#000000';
                        tctx.strokeStyle = '#000000';
                        subtractors.forEach(id => {
                            const subNode = layer.findOne('#' + id);
                            if (subNode) {
                                const subType = subNode.getClassName().toLowerCase();
                                tctx.save();
                                if (subType === 'line' || subType === 'rect' || subType === 'ellipse') {
                                    // Punch the subtractor's own crisp vector geometry, then
                                    // restore whatever it erased of itself — an already-erased
                                    // part of this subtractor must not keep cutting a hole in
                                    // whatever it's subtracted from. Line points are already
                                    // absolute (node x/y default to 0), matching how it's
                                    // drawn elsewhere in this function; Rect/Ellipse are
                                    // relative to node x/y.
                                    const baseX = subType === 'line' ? 0 : subNode.x();
                                    const baseY = subType === 'line' ? 0 : subNode.y();
                                    punchSubtractorHole(tctx, subNode, baseX, baseY, subNode.scaleX() || 1, subNode.scaleY() || 1);
                                } else if (subType === 'circle') {
                                    const rx = subNode.radius() * (subNode.scaleX() || 1);
                                    const ry = subNode.radius() * (subNode.scaleY() || 1);
                                    tctx.beginPath();
                                    tctx.ellipse(subNode.x(), subNode.y(), rx, ry, 0, 0, 2 * Math.PI);
                                    tctx.fill();
                                    tctx.lineWidth = 1;
                                    tctx.stroke();
                                }
                                tctx.restore();
                            }
                        });
                        tctx.restore();
                    }
                }

                // Composite the isolated result onto the main canvas 1:1.
                ctx.save();
                ctx.setTransform(1, 0, 0, 1, 0, 0);
                if (typeof node.globalCompositeOperation === 'function') {
                    ctx.globalCompositeOperation = node.globalCompositeOperation();
                }
                ctx.drawImage(tmp, 0, 0);
                ctx.restore();
                return;
            }

            ctx.save();

            if (typeof node.globalCompositeOperation === 'function') {
                ctx.globalCompositeOperation = node.globalCompositeOperation();
            } else if (node.globalCompositeOperation) {
                ctx.globalCompositeOperation = node.globalCompositeOperation;
            }

            if (type === 'line') {
                const points = node.points();
                if (points && points.length >= 4) {
                    ctx.beginPath();
                    ctx.moveTo(points[0], points[1]);
                    for (let i = 2; i < points.length; i += 2) {
                        ctx.lineTo(points[i], points[i + 1]);
                    }
                    if (node.closed()) {
                        // Closed polygon — fill and add 1px stroke seal
                        ctx.closePath();
                        ctx.fillStyle = node.fill() || '#000000';
                        ctx.fill();
                        ctx.lineWidth = 1;
                        ctx.strokeStyle = node.fill() || '#000000';
                        ctx.stroke();
                    } else {
                        ctx.strokeStyle = node.stroke() || '#000000';
                        ctx.lineWidth = node.strokeWidth() || 1;
                        ctx.lineCap = node.lineCap() || 'round';
                        ctx.lineJoin = node.lineJoin() || 'round';
                        ctx.stroke();
                    }
                }
            } else if (type === 'rect') {
                const scaleX = node.scaleX() || 1;
                const scaleY = node.scaleY() || 1;
                ctx.beginPath();
                ctx.rect(node.x(), node.y(), node.width() * scaleX, node.height() * scaleY);
                if (node.fill()) {
                    ctx.fillStyle = node.fill();
                    ctx.fill();
                    ctx.lineWidth = 1;
                    ctx.strokeStyle = node.fill();
                    ctx.stroke();
                }
            } else if (type === 'ellipse' || type === 'circle') {
                const rx = (type === 'circle' ? node.radius() : node.radiusX()) * (node.scaleX() || 1);
                const ry = (type === 'circle' ? node.radius() : node.radiusY()) * (node.scaleY() || 1);
                ctx.beginPath();
                ctx.ellipse(node.x(), node.y(), rx, ry, 0, 0, 2 * Math.PI);
                if (node.fill()) {
                    ctx.fillStyle = node.fill();
                    ctx.fill();
                    ctx.lineWidth = 1;
                    ctx.strokeStyle = node.fill();
                    ctx.stroke();
                }
            } else if (type === 'image') {
                const img = node.image();
                if (img) {
                    const scaleX = node.scaleX() || 1;
                    const scaleY = node.scaleY() || 1;
                    ctx.drawImage(img, node.x(), node.y(), node.width() * scaleX, node.height() * scaleY);
                }
            }
            ctx.restore();
        });

        return canvas;
    }

    window.countUnmaskedPixels = function () {
        if (!originalWidth || !originalHeight || !annotationLayer) return;

        annotationLayer.getChildren().forEach(node => {
            if (node.getAttr('isUnmaskedOverlay')) {
                node.destroy();
            }
        });

        try {
            const scale = getProcessingScale(originalWidth, originalHeight);
            const scaledW = Math.floor(originalWidth * scale) || 1;
            const scaledH = Math.floor(originalHeight * scale) || 1;

            const maskNodes = annotationLayer.getChildren().filter(node =>
                node !== transformer &&
                node.visible() &&
                !node.getAttr('isUnmaskedOverlay') &&
                !node.getAttr('excludeFromExport')
            );

            const snap = renderNodesToCanvas(maskNodes, originalWidth, originalHeight, scale);
            const snapCtx = snap.getContext('2d', { willReadFrequently: true });
            const data = snapCtx.getImageData(0, 0, scaledW, scaledH).data;

            const overlayCanvas = document.createElement('canvas');
            overlayCanvas.width = scaledW;
            overlayCanvas.height = scaledH;
            const overlayCtx = overlayCanvas.getContext('2d');
            const overlayImgData = overlayCtx.createImageData(scaledW, scaledH);
            const overlayData = overlayImgData.data;

            let unmasked = 0;
            const total = scaledW * scaledH;
            for (let i = 0; i < total; i++) {
                if (data[i * 4 + 3] === 0) {
                    unmasked++;
                    overlayData[i * 4] = 255;
                    overlayData[i * 4 + 1] = 30;
                    overlayData[i * 4 + 2] = 30;
                    overlayData[i * 4 + 3] = 220;
                }
            }
            overlayCtx.putImageData(overlayImgData, 0, 0);

            if (unmasked === 0) {
                Swal.fire({
                    icon: 'success',
                    title: 'Fully Covered!',
                    text: 'All pixels are masked.',
                    timer: 2000,
                    showConfirmButton: false
                });
                annotationLayer.batchDraw();
                return;
            }

            const overlayNode = new Konva.Image({
                imageSmoothingEnabled: false,
                x: 0,
                y: 0,
                image: overlayCanvas,
                width: originalWidth,
                height: originalHeight,
                opacity: 0,
                listening: false
            });
            overlayNode.setAttrs({
                isUnmaskedOverlay: true,
                excludeFromExport: true
            });

            annotationLayer.add(overlayNode);
            overlayNode.moveToTop();

            let count = 0;
            function flash() {
                if (count >= 3) {
                    overlayNode.destroy();
                    annotationLayer.batchDraw();
                    return;
                }

                const fadeIn = new Konva.Tween({
                    node: overlayNode,
                    opacity: 0.8,
                    duration: 0.35,
                    onFinish: function () {
                        const fadeOut = new Konva.Tween({
                            node: overlayNode,
                            opacity: 0,
                            duration: 0.35,
                            onFinish: function () {
                                count++;
                                setTimeout(flash, 120);
                            }
                        });
                        fadeOut.play();
                    }
                });
                fadeIn.play();
            }

            flash();
        } catch (err) {
            console.error("Error in countUnmaskedPixels:", err);
        }
    };

    function convertShapeToMaskImage(shape) {
        if (!originalWidth || !originalHeight || !shape) return null;

        try {
            const scale = getMaskRenderScale(originalWidth, originalHeight);
            const w = originalWidth;
            const h = originalHeight;
            const scaledW = Math.floor(w * scale) || 1;
            const scaledH = Math.floor(h * scale) || 1;

            // Render shape to offscreen canvas
            const shapeCanvas = renderNodesToCanvas([shape], w, h, scale);
            const ctx = shapeCanvas.getContext('2d');
            const imgData = ctx.getImageData(0, 0, scaledW, scaledH);
            const data = imgData.data;

            let minX = scaledW, minY = scaledH, maxX = 0, maxY = 0, hasPixels = false;
            for (let y = 0; y < scaledH; y++) {
                for (let x = 0; x < scaledW; x++) {
                    if (data[(y * scaledW + x) * 4 + 3] > 0) {
                        hasPixels = true;
                        if (x < minX) minX = x;
                        if (x > maxX) maxX = x;
                        if (y < minY) minY = y;
                        if (y > maxY) maxY = y;
                    }
                }
            }

            if (!hasPixels) {
                shape.destroy();
                annotationLayer.batchDraw();
                return null;
            }

            const cropW = maxX - minX + 1;
            const cropH = maxY - minY + 1;
            const cropCanvas = document.createElement('canvas');
            cropCanvas.width = cropW;
            cropCanvas.height = cropH;
            const cropCtx = cropCanvas.getContext('2d');
            const cropImgData = cropCtx.createImageData(cropW, cropH);

            for (let cy = 0; cy < cropH; cy++) {
                for (let cx = 0; cx < cropW; cx++) {
                    const si = ((minY + cy) * scaledW + (minX + cx)) * 4;
                    const di = (cy * cropW + cx) * 4;
                    cropImgData.data[di] = data[si];
                    cropImgData.data[di + 1] = data[si + 1];
                    cropImgData.data[di + 2] = data[si + 2];
                    // Keep the natural anti-aliased edge alpha so shape edges are
                    // clean instead of a jagged binary staircase — no display
                    // smoothing (imageSmoothingEnabled stays false).
                    cropImgData.data[di + 3] = data[si + 3];
                }
            }
            cropCtx.putImageData(cropImgData, 0, 0);

            // Cache attrs before destroying
            const oldOpacity = shape.opacity();
            const labelName = shape.getAttr('labelName');
            const labelColor = shape.getAttr('labelColor');
            const datasetId = shape.getAttr('datasetId');
            const id = shape.getAttr('id') || `shape_${Date.now()}`;
            const attributes = shape.getAttr('attributes') || {};
            const _srcCache = cropCanvas.toDataURL();

            const maskNode = new Konva.Image({
                imageSmoothingEnabled: false,
                x: minX / scale,
                y: minY / scale,
                image: cropCanvas,
                width: cropW / scale,
                height: cropH / scale,
                opacity: 1.0,
            });

            maskNode.setAttrs({
                labelName: labelName,
                labelColor: labelColor,
                datasetId: datasetId,
                id: id,
                attributes: attributes,
                isMask: true,
                isBoundary: true,
                locked: shape.getAttr('locked') !== false,
                _srcCache
            });

            addAnnotationShape(maskNode);

            // Destroy source only after successfully creating and placing the replacement maskNode
            shape.destroy();
            annotationLayer.batchDraw();

            return maskNode;
        } catch (err) {
            console.error("Mask conversion exception:", err);
            Swal.fire({
                icon: "error",
                title: "Mask Creation Failed",
                text: "Large image processing exceeded available memory."
            });
            return null;
        }
    }
    /**
     * Subtracts newObj from all currently unlocked segmentation masks.
     * This ensures that when a new label dataset is drawn, any unlocked overlapping
     * layers will have their overlapping pixels erased.
     */
    function subtractNewObjFromUnlocked(newObj, onComplete) {
        if (!originalWidth || !originalHeight || !newObj) {
            if (onComplete) onComplete();
            return;
        }

        try {
            const scale = getProcessingScale(originalWidth, originalHeight);
            const w = originalWidth;
            const h = originalHeight;
            const scaledW = Math.floor(w * scale) || 1;
            const scaledH = Math.floor(h * scale) || 1;

            const allNodes = annotationLayer.getChildren().filter(node => node !== transformer && node !== newObj);

            // Filter for unlocked, visible shapes of different labels
            const unlockedObjs = allNodes.filter(o => {
                if (o.getAttr('locked') || o.visible() === false) return false;
                // Same-label objects should merge, not clip each other
                const newObjDatasetId = newObj.getAttr('datasetId');
                const oDatasetId = o.getAttr('datasetId');
                if (newObjDatasetId && oDatasetId &&
                    String(newObjDatasetId) === String(oDatasetId)) {
                    return false;
                }
                if (o.getClassName().toLowerCase() === 'image' && !o.getAttr('isMask')) return false;
                if (o.globalCompositeOperation && o.globalCompositeOperation() === 'destination-out') return false;
                if (o.getAttr('labelName') || o.getAttr('isMask') || o.getAttr('isMaskGroup') || o.getAttr('isBoundary')) return true;
                return false;
            });

            if (unlockedObjs.length === 0) {
                if (onComplete) onComplete();
                return;
            }

            // Render subtractor (newObj) to offscreen canvas
            const subCanvas = renderNodesToCanvas([newObj], w, h, scale);
            const subData = subCanvas.getContext('2d').getImageData(0, 0, scaledW, scaledH);

            let index = 0;
            function processNext() {
                if (index >= unlockedObjs.length) {
                    // All unlocked layers subtracted!
                    // Temporarily remove newObj, save history, and restore newObj.
                    const wasInLayer = annotationLayer.getChildren().indexOf(newObj) !== -1;
                    if (wasInLayer) {
                        const newObjIndex = annotationLayer.getChildren().indexOf(newObj);
                        const oldLoading = window.IS_LOADING_STATE;
                        window.IS_LOADING_STATE = true;

                        newObj.remove(); // Removes from parent
                        saveHistory();

                        annotationLayer.add(newObj);
                        newObj.setZIndex(newObjIndex);

                        window.IS_LOADING_STATE = oldLoading;
                        annotationLayer.batchDraw();
                    } else {
                        saveHistory();
                    }

                    if (onComplete) onComplete();
                    return;
                }

                const unlockedObj = unlockedObjs[index];
                index++;

                // Render target (unlockedObj) to offscreen canvas
                const targetCanvas = renderNodesToCanvas([unlockedObj], w, h, scale);
                const targetCtx = targetCanvas.getContext('2d');
                const targetData = targetCtx.getImageData(0, 0, scaledW, scaledH);

                // Check if there is actual pixel overlap
                let intersects = false;
                for (let i = 3; i < targetData.data.length; i += 4) {
                    if (targetData.data[i] > 0 && subData.data[i] > 0) {
                        intersects = true;
                        break;
                    }
                }

                if (!intersects) {
                    processNext();
                    return;
                }

                // Perform subtraction: destination-out
                targetCtx.globalCompositeOperation = 'destination-out';
                targetCtx.imageSmoothingEnabled = false;
                targetCtx.webkitImageSmoothingEnabled = false;
                targetCtx.mozImageSmoothingEnabled = false;
                targetCtx.msImageSmoothingEnabled = false;
                targetCtx.drawImage(subCanvas, 0, 0);

                // Scan remaining pixels of the target
                const remainingData = targetCtx.getImageData(0, 0, scaledW, scaledH);
                let minX = scaledW, minY = scaledH, maxX = 0, maxY = 0;
                let hasRemainingPixels = false;

                for (let y = 0; y < scaledH; y++) {
                    for (let x = 0; x < scaledW; x++) {
                        const idx = (y * scaledW + x) * 4;
                        if (remainingData.data[idx + 3] > 0) {
                            hasRemainingPixels = true;
                            if (x < minX) minX = x;
                            if (x > maxX) maxX = x;
                            if (y < minY) minY = y;
                            if (y > maxY) maxY = y;
                        }
                    }
                }

                // Cache properties before destroying
                const oldOpacity = unlockedObj.opacity() || defaultMaskOpacity;
                const labelName = unlockedObj.getAttr('labelName');
                const labelColor = unlockedObj.getAttr('labelColor');
                const datasetId = unlockedObj.getAttr('datasetId');
                const attributes = unlockedObj.getAttr('attributes') || {};
                const unlockedObjLocked = unlockedObj.getAttr('locked') || false;
                const unlockedObjId = unlockedObj.getAttr('id') || `shape_${Date.now()}`;

                const targetIndex = annotationLayer.getChildren().indexOf(unlockedObj);
                unlockedObj.destroy();

                if (!hasRemainingPixels) {
                    annotationLayer.batchDraw();
                    processNext();
                    return;
                }

                // Crop to new bounding box
                const cropW = maxX - minX + 1;
                const cropH = maxY - minY + 1;
                const cropCanvas = document.createElement('canvas');
                cropCanvas.width = cropW;
                cropCanvas.height = cropH;
                const cropCtx = cropCanvas.getContext('2d');
                const cropImgData = cropCtx.createImageData(cropW, cropH);

                for (let cy = 0; cy < cropH; cy++) {
                    for (let cx = 0; cx < cropW; cx++) {
                        const srcIdx = ((minY + cy) * scaledW + (minX + cx)) * 4;
                        const dstIdx = (cy * cropW + cx) * 4;
                        if (remainingData.data[srcIdx + 3] > 0) {
                            cropImgData.data[dstIdx] = remainingData.data[srcIdx];
                            cropImgData.data[dstIdx + 1] = remainingData.data[srcIdx + 1];
                            cropImgData.data[dstIdx + 2] = remainingData.data[srcIdx + 2];
                            cropImgData.data[dstIdx + 3] = 255;
                        }
                    }
                }
                cropCtx.putImageData(cropImgData, 0, 0);

                const _srcCache = cropCanvas.toDataURL();
                const imgNode = new Konva.Image({
                    imageSmoothingEnabled: false,
                    x: minX / scale,
                    y: minY / scale,
                    image: cropCanvas,
                    width: cropW / scale,
                    height: cropH / scale,
                    opacity: 1.0,
                });

                imgNode.setAttrs({
                    labelName: labelName,
                    labelColor: labelColor,
                    datasetId: datasetId,
                    attributes: attributes,
                    isMask: true,
                    isBoundary: true,
                    locked: unlockedObjLocked,
                    id: unlockedObjId,
                    _srcCache
                });

                annotationLayer.add(imgNode);
                if (targetIndex !== -1) {
                    imgNode.setZIndex(targetIndex);
                }
                annotationLayer.batchDraw();
                processNext();
            }

            processNext();
        } catch (err) {
            console.error("Error in subtractNewObjFromUnlocked:", err);
            if (onComplete) onComplete();
        }
    }

    function applyLockedLayerClipping(newObj, onComplete) {
        if (!originalWidth || !originalHeight || !newObj) {
            if (onComplete) onComplete();
            return;
        }

        try {
            const scale = getProcessingScale(originalWidth, originalHeight);
            const w = originalWidth;
            const h = originalHeight;
            const scaledW = Math.floor(w * scale) || 1;
            const scaledH = Math.floor(h * scale) || 1;

            const olderNodes = annotationLayer.getChildren().filter(node => 
                node !== transformer && node !== newObj && 
                !!node.getAttr('labelName') &&
                node.getAttr('labelName') !== newObj.getAttr('labelName') &&
                node.visible() !== false &&
                !node.getAttr('isUndoSubtractor')
            );
            
            const olderUnlockedObjs = olderNodes.filter(o => o.getAttr('locked') === false);
            const olderLockedObjs = olderNodes.filter(o => o.getAttr('locked') !== false);

            // Phase 1: newObj cuts holes in olderUnlockedObjs
            let index = 0;
            const subCanvas = olderUnlockedObjs.length > 0 ? renderNodesToCanvas([newObj], w, h, scale) : null;
            const subData = subCanvas ? subCanvas.getContext('2d').getImageData(0, 0, scaledW, scaledH) : null;

            function processPhase1() {
                if (index >= olderUnlockedObjs.length) {
                    processPhase2();
                    return;
                }
                const olderObj = olderUnlockedObjs[index++];
                
                if (isVectorBoundaryShape(olderObj)) {
                    const newBox = newObj.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                    const oBox = olderObj.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                    const intersects = !(newBox.x > oBox.x + oBox.width ||
                        newBox.x + newBox.width < oBox.x ||
                        newBox.y > oBox.y + oBox.height ||
                        newBox.y + newBox.height < oBox.y);
                    if (intersects) {
                        let subId = newObj.id();
                        if (!subId) {
                            subId = `shape_${Date.now()}_${Math.random().toString(36).substring(2, 9)}`;
                            newObj.id(subId);
                        }
                        const subtractors = olderObj.getAttr('_subtractorNodes') || [];
                        if (subtractors.indexOf(subId) === -1) subtractors.push(subId);
                        olderObj.setAttr('_subtractorNodes', subtractors);
                        makeShapeErasable(olderObj);
                    }
                    processPhase1();
                    return;
                }

                const targetCanvas = renderNodesToCanvas([olderObj], w, h, scale);
                const targetCtx = targetCanvas.getContext('2d');
                const targetData = targetCtx.getImageData(0, 0, scaledW, scaledH);
                
                let intersects = false;
                for (let i = 3; i < targetData.data.length; i += 4) {
                    if (targetData.data[i] > 0 && subData.data[i] > 0) {
                        intersects = true;
                        break;
                    }
                }
                
                if (!intersects) {
                    processPhase1();
                    return;
                }
                
                targetCtx.globalCompositeOperation = 'destination-out';
                targetCtx.imageSmoothingEnabled = false;
                targetCtx.webkitImageSmoothingEnabled = false;
                targetCtx.mozImageSmoothingEnabled = false;
                targetCtx.msImageSmoothingEnabled = false;
                targetCtx.drawImage(subCanvas, 0, 0);
                
                const remainingData = targetCtx.getImageData(0, 0, scaledW, scaledH);
                let minX = scaledW, minY = scaledH, maxX = 0, maxY = 0;
                let hasRemainingPixels = false;
                
                for (let y = 0; y < scaledH; y++) {
                    for (let x = 0; x < scaledW; x++) {
                        const idx = (y * scaledW + x) * 4;
                        if (remainingData.data[idx + 3] > 0) {
                            hasRemainingPixels = true;
                            if (x < minX) minX = x;
                            if (x > maxX) maxX = x;
                            if (y < minY) minY = y;
                            if (y > maxY) maxY = y;
                        }
                    }
                }
                
                const oldOpacity = olderObj.opacity() || defaultMaskOpacity;
                const labelName = olderObj.getAttr('labelName');
                const labelColor = olderObj.getAttr('labelColor');
                const datasetId = olderObj.getAttr('datasetId');
                const attributes = olderObj.getAttr('attributes') || {};
                const olderObjLocked = olderObj.getAttr('locked') || false;
                const olderObjId = olderObj.getAttr('id') || `shape_${Date.now()}`;
                const targetIndex = annotationLayer.getChildren().indexOf(olderObj);
                
                olderObj.destroy();
                
                if (!hasRemainingPixels) {
                    processPhase1();
                    return;
                }
                
                const cropW = maxX - minX + 1;
                const cropH = maxY - minY + 1;
                const cropCanvas = document.createElement('canvas');
                cropCanvas.width = cropW;
                cropCanvas.height = cropH;
                const cropCtx = cropCanvas.getContext('2d');
                const cropImgData = cropCtx.createImageData(cropW, cropH);
                
                for (let cy = 0; cy < cropH; cy++) {
                    for (let cx = 0; cx < cropW; cx++) {
                        const srcIdx = ((minY + cy) * scaledW + (minX + cx)) * 4;
                        const dstIdx = (cy * cropW + cx) * 4;
                        if (remainingData.data[srcIdx + 3] > 0) {
                            cropImgData.data[dstIdx] = remainingData.data[srcIdx];
                            cropImgData.data[dstIdx + 1] = remainingData.data[srcIdx + 1];
                            cropImgData.data[dstIdx + 2] = remainingData.data[srcIdx + 2];
                            cropImgData.data[dstIdx + 3] = 255;
                        }
                    }
                }
                cropCtx.putImageData(cropImgData, 0, 0);

                const _srcCache = cropCanvas.toDataURL();
                const imgNode = new Konva.Image({
                    imageSmoothingEnabled: false,
                    x: minX / scale,
                    y: minY / scale,
                    image: cropCanvas,
                    width: cropW / scale,
                    height: cropH / scale,
                    opacity: 1.0,
                });

                imgNode.setAttrs({
                    labelName: labelName,
                    labelColor: labelColor,
                    datasetId: datasetId,
                    attributes: attributes,
                    isMask: true,
                    isBoundary: true,
                    locked: olderObjLocked,
                    id: olderObjId,
                    _srcCache
                });
                
                annotationLayer.add(imgNode);
                if (targetIndex !== -1) imgNode.setZIndex(targetIndex);
                
                processPhase1();
            }

            function processPhase2() {
                if (olderLockedObjs.length === 0) {
                    finalize();
                    return;
                }

                if (isVectorBoundaryShape(newObj)) {
                    let subId = newObj.id();
                    if (!subId) {
                        subId = `shape_${Date.now()}_${Math.random().toString(36).substring(2, 9)}`;
                        newObj.id(subId);
                    }
                    const subtractors = newObj.getAttr('_subtractorNodes') || [];
                    const newBox = newObj.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                    
                    olderLockedObjs.forEach(lockedObj => {
                        const wasVisible = lockedObj.visible();
                        if (!wasVisible) lockedObj.visible(true);

                        const oBox = lockedObj.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                        const intersects = !(newBox.x > oBox.x + oBox.width ||
                            newBox.x + newBox.width < oBox.x ||
                            newBox.y > oBox.y + oBox.height ||
                            newBox.y + newBox.height < oBox.y);
                        
                        if (intersects) {
                            let lockedId = lockedObj.id();
                            if (!lockedId) {
                                lockedId = `shape_${Date.now()}_${Math.random().toString(36).substring(2, 9)}`;
                                lockedObj.id(lockedId);
                            }
                            if (subtractors.indexOf(lockedId) === -1) subtractors.push(lockedId);
                        }

                        if (!wasVisible) lockedObj.visible(false);
                    });
                    
                    if (subtractors.length > 0) {
                        newObj.setAttr('_subtractorNodes', subtractors);
                        makeShapeErasable(newObj);
                    }
                    finalize();
                    return;
                }

                const targetCanvas = renderNodesToCanvas([newObj], w, h, scale);
                const targetCtx = targetCanvas.getContext('2d');
                let clippedSomething = false;

                olderLockedObjs.forEach(lockedObj => {
                    const wasVisible = lockedObj.visible();
                    if (!wasVisible) lockedObj.visible(true);

                    const oBox = lockedObj.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                    const newBox = newObj.getClientRect({ relativeTo: annotationLayer, skipShadow: true });
                    const intersects = !(newBox.x > oBox.x + oBox.width ||
                        newBox.x + newBox.width < oBox.x ||
                        newBox.y > oBox.y + oBox.height ||
                        newBox.y + newBox.height < oBox.y);
                    
                    if (intersects) {
                        const lCanvas = renderNodesToCanvas([lockedObj], w, h, scale);
                        targetCtx.globalCompositeOperation = 'destination-out';
                        targetCtx.imageSmoothingEnabled = false;
                        targetCtx.webkitImageSmoothingEnabled = false;
                        targetCtx.mozImageSmoothingEnabled = false;
                        targetCtx.msImageSmoothingEnabled = false;
                        targetCtx.drawImage(lCanvas, 0, 0);
                        clippedSomething = true;
                    }

                    if (!wasVisible) lockedObj.visible(false);
                });

                if (!clippedSomething) {
                    finalize();
                    return;
                }

                const targetData = targetCtx.getImageData(0, 0, scaledW, scaledH);
                let minX = scaledW, minY = scaledH, maxX = 0, maxY = 0;
                let hasRemainingPixels = false;

                for (let y = 0; y < scaledH; y++) {
                    for (let x = 0; x < scaledW; x++) {
                        const idx = (y * scaledW + x) * 4;
                        if (targetData.data[idx + 3] > 0) {
                            hasRemainingPixels = true;
                            if (x < minX) minX = x;
                            if (x > maxX) maxX = x;
                            if (y < minY) minY = y;
                            if (y > maxY) maxY = y;
                        }
                    }
                }

                const oldOpacity = newObj.opacity() || defaultMaskOpacity;
                const labelName = newObj.getAttr('labelName');
                const labelColor = newObj.getAttr('labelColor');
                const datasetId = newObj.getAttr('datasetId');
                const attributes = newObj.getAttr('attributes') || {};
                const isBrushStroke = newObj.getAttr('isBrushStroke') || false;
                const newObjLocked = newObj.getAttr('locked') || false;
                const newObjId = newObj.getAttr('id') || `shape_${Date.now()}`;
                
                const targetIndex = annotationLayer.getChildren().indexOf(newObj);
                newObj.destroy();

                if (!hasRemainingPixels) {
                    finalize();
                    return;
                }

                const cropW = maxX - minX + 1;
                const cropH = maxY - minY + 1;
                const cropCanvas = document.createElement('canvas');
                cropCanvas.width = cropW;
                cropCanvas.height = cropH;
                const cropCtx = cropCanvas.getContext('2d');
                const cropImgData = cropCtx.createImageData(cropW, cropH);

                for (let cy = 0; cy < cropH; cy++) {
                    for (let cx = 0; cx < cropW; cx++) {
                        const srcIdx = ((minY + cy) * scaledW + (minX + cx)) * 4;
                        const dstIdx = (cy * cropW + cx) * 4;
                        if (targetData.data[srcIdx + 3] > 0) {
                            cropImgData.data[dstIdx] = targetData.data[srcIdx];
                            cropImgData.data[dstIdx + 1] = targetData.data[srcIdx + 1];
                            cropImgData.data[dstIdx + 2] = targetData.data[srcIdx + 2];
                            cropImgData.data[dstIdx + 3] = 255;
                        }
                    }
                }
                cropCtx.putImageData(cropImgData, 0, 0);

                const _srcCache = cropCanvas.toDataURL();
                const imgNode = new Konva.Image({
                    imageSmoothingEnabled: false,
                    x: minX / scale,
                    y: minY / scale,
                    image: cropCanvas,
                    width: cropW / scale,
                    height: cropH / scale,
                    opacity: 1.0,
                });

                imgNode.setAttrs({
                    labelName: labelName,
                    labelColor: labelColor,
                    datasetId: datasetId,
                    attributes: attributes,
                    isMask: true,
                    isBoundary: true,
                    locked: newObjLocked,
                    id: newObjId,
                    _srcCache
                });
                if (isBrushStroke) imgNode.setAttr('isBrushStroke', true);

                annotationLayer.add(imgNode);
                if (targetIndex !== -1) imgNode.setZIndex(targetIndex);

                finalize();
            }

            function finalize() {
                if (transformer && transformer.getParent() === annotationLayer) {
                    transformer.moveToTop();
                }
                annotationLayer.batchDraw();
                saveHistory();
                if (onComplete) onComplete();
            }

            // Start the pipeline
            processPhase1();

        } catch (err) {
            console.error("Error in applyLockedLayerClipping:", err);
            Swal.fire({
                icon: "error",
                title: "Locked Clipping Failed",
                text: "Large image processing exceeded available memory."
            });
            if (onComplete) onComplete();
        }
    }
    function mergeLabelBrushStrokes(datasetId) {
        if (!datasetId || !originalWidth || !originalHeight) return;

        try {
            const scale = getMaskRenderScale(originalWidth, originalHeight);
            const w = originalWidth;
            const h = originalHeight;
            const scaledW = Math.floor(w * scale) || 1;
            const scaledH = Math.floor(h * scale) || 1;

            const mergeableObjs = annotationLayer.getChildren().filter(o =>
                o !== transformer &&
                String(o.getAttr('datasetId')) === String(datasetId) &&
                o.globalCompositeOperation() !== 'destination-out' &&
                (o.getAttr('isBrushStroke') || o.getAttr('isMask'))
            );

            if (mergeableObjs.length <= 1) return; // Nothing to merge

            // Render all to single canvas
            const snapshotCanvas = renderNodesToCanvas(mergeableObjs, w, h, scale);
            const ctx = snapshotCanvas.getContext('2d', { willReadFrequently: true });
            const imageData = ctx.getImageData(0, 0, scaledW, scaledH);
            const data = imageData.data;

            // Find bounding box of ALL merged pixels
            let minX = scaledW, minY = scaledH, maxX = 0, maxY = 0;
            let hasPixels = false;

            for (let y = 0; y < scaledH; y++) {
                for (let x = 0; x < scaledW; x++) {
                    if (data[(y * scaledW + x) * 4 + 3] > 0) {
                        hasPixels = true;
                        minX = Math.min(minX, x);
                        minY = Math.min(minY, y);
                        maxX = Math.max(maxX, x);
                        maxY = Math.max(maxY, y);
                    }
                }
            }

            if (!hasPixels) return;

            // Get label properties
            const labelName = mergeableObjs[0].getAttr('labelName');
            const labelColor = mergeableObjs[0].getAttr('labelColor');
            const attributes = mergeableObjs[0].getAttr('attributes') || {};

            const hasUnlocked = annotationLayer.getChildren().filter(o =>
                o !== transformer &&
                String(o.getAttr('datasetId')) === String(datasetId)
            ).some(o => o.getAttr('locked') === false);
            const isLocked = !hasUnlocked;

            // Destroy originals
            mergeableObjs.forEach(o => o.destroy());

            // Crop to bounding box with padding
            const pad = 2;
            const cropMinX = Math.max(0, minX - pad);
            const cropMinY = Math.max(0, minY - pad);
            const cropMaxX = Math.min(scaledW - 1, maxX + pad);
            const cropMaxY = Math.min(scaledH - 1, maxY + pad);
            const cropW = cropMaxX - cropMinX + 1;
            const cropH = cropMaxY - cropMinY + 1;

            const cropCanvas = document.createElement('canvas');
            cropCanvas.width = cropW;
            cropCanvas.height = cropH;
            const cropCtx = cropCanvas.getContext('2d');

            // Copy the EXACT pixels — no component splitting!
            cropCtx.drawImage(
                snapshotCanvas,
                cropMinX, cropMinY, cropW, cropH,
                0, 0, cropW, cropH
            );

            // Create single merged image
            const dataUrl = cropCanvas.toDataURL();
            const mergedImg = new Konva.Image({
                imageSmoothingEnabled: false,
                x: cropMinX / scale,
                y: cropMinY / scale,
                image: cropCanvas,
                width: cropW / scale,
                height: cropH / scale,
                opacity: 1.0,
            });

            mergedImg.setAttrs({
                labelName: labelName,
                labelColor: labelColor,
                datasetId: datasetId,
                attributes: attributes,
                id: `shape_${Date.now()}`,
                isMask: true,
                isBoundary: true,
                locked: isLocked,
                src: dataUrl,
                _srcCache: dataUrl
            });

            addAnnotationShape(mergedImg);
            annotationLayer.batchDraw();
            updateLayerList();

        } catch (err) {
            console.error("Error in mergeLabelBrushStrokes:", err);
        }
    }

    function applyEraserToMasks(eraserPath) {
        if (!originalWidth || !originalHeight || !eraserPath) return;

        try {
            const scale = getMaskRenderScale(originalWidth, originalHeight);
            const w = originalWidth;
            const h = originalHeight;
            const scaledW = Math.floor(w * scale) || 1;
            const scaledH = Math.floor(h * scale) || 1;

            const allNodes = annotationLayer.getChildren().filter(node =>
                node !== transformer &&
                node !== eraserPath &&
                !node.getAttr('locked')
            );

            const datasetIds = [...new Set(
                allNodes.filter(o =>
                    o.getAttr('datasetId') &&
                    o.getAttr('datasetId') !== 'eraser' &&
                    o.globalCompositeOperation() !== 'destination-out' &&
                    (o.getAttr('isBrushStroke') || o.getAttr('isMask'))
                    && !isVectorBoundaryShape(o)
                ).map(o => String(o.getAttr('datasetId')))
            )];

            if (datasetIds.length === 0) {
                eraserPath.destroy();
                annotationLayer.batchDraw();
                updateLayerList();
                triggerAutoSave();
                return;
            }

            const newMasks = [];

            datasetIds.forEach(dsId => {
                const labelObjs = allNodes.filter(o =>
                    String(o.getAttr('datasetId')) === dsId &&
                    o.globalCompositeOperation() !== 'destination-out' &&
                    (o.getAttr('isBrushStroke') || o.getAttr('isMask'))
                    && !isVectorBoundaryShape(o)
                );

                if (labelObjs.length === 0) return;

                const refObj = labelObjs[0];
                const labelName = refObj.getAttr('labelName');
                const labelColor = refObj.getAttr('labelColor');
                const datasetId = refObj.getAttr('datasetId');
                const attributes = refObj.getAttr('attributes') || {};

                // Render labelObjs and eraserPath together
                const snapshotCanvas = renderNodesToCanvas([...labelObjs, eraserPath], w, h, scale);
                const ctx = snapshotCanvas.getContext('2d', { willReadFrequently: true });
                const imageData = ctx.getImageData(0, 0, scaledW, scaledH);
                const data = imageData.data;

                // Keep the natural anti-aliased edges from the destination-out
                // composite (no binary thresholding) so the erased shape stays
                // smooth instead of turning into a jagged staircase. Only drop
                // fully/near-transparent stray pixels.
                for (let i = 3; i < data.length; i += 4) {
                    if (data[i] < 10) {
                        data[i - 3] = 0;
                        data[i - 2] = 0;
                        data[i - 1] = 0;
                        data[i] = 0;
                    }
                }

                ctx.putImageData(imageData, 0, 0);

                let minX = scaledW, minY = scaledH, maxX = 0, maxY = 0;
                let hasContent = false;

                for (let py = 0; py < scaledH; py++) {
                    for (let px = 0; px < scaledW; px++) {
                        if (data[(py * scaledW + px) * 4 + 3] > 0) {
                            if (px < minX) minX = px;
                            if (py < minY) minY = py;
                            if (px > maxX) maxX = px;
                            if (py > maxY) maxY = py;
                            hasContent = true;
                        }
                    }
                }

                newMasks.push({
                    labelObjs,
                    hasContent,
                    minX, minY, maxX, maxY,
                    snapshotCanvas,
                    labelName, labelColor, datasetId, attributes,
                    locked: refObj.getAttr('locked') || false
                });
            });

            // Destroy the eraser path
            eraserPath.destroy();

            // Replace original objects with the new erased masks
            newMasks.forEach(entry => {
                entry.labelObjs.forEach(o => o.destroy());

                if (!entry.hasContent) return; // Completely erased

                const cropW = entry.maxX - entry.minX + 1;
                const cropH = entry.maxY - entry.minY + 1;

                const cropCanvas = document.createElement('canvas');
                cropCanvas.width = cropW;
                cropCanvas.height = cropH;
                const cropCtx = cropCanvas.getContext('2d');

                cropCtx.imageSmoothingEnabled = false;
                cropCtx.webkitImageSmoothingEnabled = false;
                cropCtx.mozImageSmoothingEnabled = false;
                cropCtx.msImageSmoothingEnabled = false;
                cropCtx.drawImage(
                    entry.snapshotCanvas,
                    entry.minX, entry.minY, cropW, cropH,
                    0, 0, cropW, cropH
                );

                // Drop fully-transparent stray pixels but KEEP anti-aliased edge
                // alpha so the erased shape stays smooth (no jagged staircase).
                const cropImageData = cropCtx.getImageData(0, 0, cropW, cropH);
                const cropData = cropImageData.data;
                let needsCleanup = false;
                for (let i = 3; i < cropData.length; i += 4) {
                    if (cropData[i] < 1) {
                        cropData[i - 3] = 0;
                        cropData[i - 2] = 0;
                        cropData[i - 1] = 0;
                        cropData[i] = 0;
                        needsCleanup = true;
                    }
                }
                if (needsCleanup) {
                    cropCtx.putImageData(cropImageData, 0, 0);
                }

                const _srcCache = cropCanvas.toDataURL();
                const imgNode = new Konva.Image({
                    imageSmoothingEnabled: false,
                    x: entry.minX / scale,
                    y: entry.minY / scale,
                    image: cropCanvas,
                    width: cropW / scale,
                    height: cropH / scale,
                    opacity: 1.0,
                });

                imgNode.setAttrs({
                    labelName: entry.labelName,
                    labelColor: entry.labelColor,
                    datasetId: entry.datasetId,
                    attributes: entry.attributes,
                    isMask: true,
                    isBoundary: true,
                    locked: entry.locked,
                    id: `shape_${Date.now()}`,
                    _srcCache
                });

                addAnnotationShape(imgNode);
            });

            annotationLayer.batchDraw();
            updateLayerList();
            triggerAutoSave();
        } catch (err) {
            console.error("Error in applyEraserToMasks:", err);
        }
    }

    function getCSRFToken() {
        let cookieValue = null;
        if (document.cookie && document.cookie !== '') {
            const cookies = document.cookie.split(';');
            for (let i = 0; i < cookies.length; i++) {
                const cookie = cookies[i].trim();
                if (cookie.substring(0, 10) === 'csrftoken=') {
                    cookieValue = decodeURIComponent(cookie.substring(10));
                    break;
                }
            }
        }
        return cookieValue;
    }

    /* ──────────────────────────────────────────────────────────────────────
       LIVE SESSION TIMER
       Mirrors the same logic from segmentation_tool.js exactly.
    ────────────────────────────────────────────────────────────────────── */
    function startLiveTimer(forcedStartTime) {
        const timerDisplay = document.getElementById('taskTimer');
        if (!timerDisplay) return;

        const config = window.SEGMENTATION_CONFIG || {};
        const startTime = forcedStartTime || config.startTime;
        const accumulatedTime = config.accumulatedTime || 0;
        const pad = n => String(n).padStart(2, '0');

        // If there is no valid start time yet, just show the static accumulated value
        if (!startTime || isNaN(new Date(startTime).getTime())) {
            const initialSeconds = accumulatedTime;
            const h = Math.floor(initialSeconds / 3600);
            const m = Math.floor((initialSeconds % 3600) / 60);
            const s = initialSeconds % 60;
            timerDisplay.textContent = `${pad(h)}:${pad(m)}:${pad(s)}`;
            return;
        }

        // Clear any existing tick
        if (taskTimerInterval) {
            clearInterval(taskTimerInterval);
            taskTimerInterval = null;
        }

        const start = new Date(startTime).getTime();
        const baseSeconds = accumulatedTime;

        // Tick immediately, then every second
        function tick() {
            const diff = Math.max(0, Date.now() - start);
            const diffSeconds = Math.floor(diff / 1000);
            const totalSeconds = baseSeconds + diffSeconds;

            const h = Math.floor(totalSeconds / 3600);
            const m = Math.floor((totalSeconds % 3600) / 60);
            const s = totalSeconds % 60;

            timerDisplay.textContent = `${pad(h)}:${pad(m)}:${pad(s)}`;
        }

        tick();
        taskTimerInterval = setInterval(tick, 1000);
    }

    function startTaskOnce() {
        if (hasTaskStarted) return;
        const config = window.SEGMENTATION_CONFIG || {};
        const taskId = config.taskId;
        if (!taskId) return;

        hasTaskStarted = true;

        fetch(`/api/workflow/task/${taskId}/start/`, {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json',
                'X-CSRFToken': getCSRFToken()
            }
        })
            .then(res => res.json())
            .then(data => {
                if (data.success || data.status === 'success') {
                    if (data.accumulated_time !== undefined) {
                        config.accumulatedTime = data.accumulated_time;
                    }
                    if (data.start_time) {
                        config.startTime = data.start_time;
                        startLiveTimer(data.start_time);
                    }
                }
            })
            .catch(err => console.error('[Konva] Error starting task:', err));
    }

    document.addEventListener('click', function (e) {
        if (e.target && e.target.id === 'fileIdInfoIcon') {
            const fileId = window.SEGMENTATION_CONFIG && window.SEGMENTATION_CONFIG.fileId;
            if (!fileId) {
                Swal.fire({
                    icon: 'error',
                    title: 'No File ID Found',
                    text: 'There is no unique file ID associated with this image.',
                    confirmButtonColor: BRAND_COLOR
                });
                return;
            }

            if (navigator.clipboard && window.isSecureContext) {
                navigator.clipboard.writeText(fileId).then(showSuccessAlert).catch(fallbackCopy);
            } else {
                fallbackCopy();
            }

            function fallbackCopy() {
                try {
                    const textArea = document.createElement('textarea');
                    textArea.value = fileId;
                    textArea.style.position = 'fixed';
                    document.body.appendChild(textArea);
                    textArea.focus();
                    textArea.select();
                    const successful = document.execCommand('copy');
                    document.body.removeChild(textArea);
                    if (successful) {
                        showSuccessAlert();
                    } else {
                        throw new Error('execCommand failed');
                    }
                } catch (err) {
                    Swal.fire({
                        icon: 'error',
                        title: 'Copy Failed',
                        text: 'Unable to copy file ID. Please select and copy manually: ' + fileId,
                        confirmButtonColor: BRAND_COLOR
                    });
                }
            }

            function showSuccessAlert() {
                Swal.fire({
                    icon: 'success',
                    title: 'Job ID',
                    html: `<strong>${fileId}</strong> has been copied to your clipboard.`,
                    timer: 2500,
                    showConfirmButton: false,
                    toast: true,
                    position: 'top-end'
                });
            }
        }
    });

    $(document).ready(function () {
        initKonva();

        // Auto-start task timer on page load (mirrors segmentation_tool.js DOMContentLoaded hook)
        startTaskOnce();
        window.updateToolbarState();

        window.addEventListener('beforeunload', function (e) {
            persistUndoRedoState();
            if (window.hasUnsavedChanges) {
                e.preventDefault();
                e.returnValue = 'You have unsaved changes';
                return 'You have unsaved changes';
            }
        });
    });

})();
