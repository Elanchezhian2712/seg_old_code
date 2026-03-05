const imageCanvas = document.getElementById('imageCanvas');
const imgCtx = imageCanvas ? imageCanvas.getContext('2d') : null;

const canvas = new fabric.Canvas('fabricCanvas', {
    isDrawingMode: false,
    selection: true,
    backgroundColor: 'transparent',
    preserveObjectStacking: true
});

window.segmentationCanvas = canvas;

function getCurrentLabelData() {
    if (!window.CURRENT_LABEL) return null;
    return {
        name: window.CURRENT_LABEL.name,
        color: window.CURRENT_LABEL.color,
        id: window.CURRENT_LABEL.id,
        attributes: window.CURRENT_LABEL.attributes || {}
    };
}

canvas.on('mouse:down', function (opt) {
    const pointer = canvas.getPointer(opt.e);

    if ((currentTool === tools.BRUSH || currentTool === tools.ERASER) && opt.e.shiftKey && lastBrushPos) {

        canvas.isDrawingMode = false;

        let strokeColor, strokeWidth;

        if (currentTool === tools.ERASER) {
            strokeColor = 'white';
            strokeWidth = brushSize;
        } else {
            const rgb = hexToRgb(window.CURRENT_LABEL.color);
            strokeColor = `rgb(${rgb.r}, ${rgb.g}, ${rgb.b})`;
            strokeWidth = brushSize;
        }

        const pathData = `M ${lastBrushPos.x} ${lastBrushPos.y} L ${pointer.x} ${pointer.y}`;
        const straightPath = new fabric.Path(pathData, {
            fill: null,
            stroke: strokeColor,
            strokeWidth: strokeWidth,
            strokeLineCap: 'round',
            strokeLineJoin: 'round',
            selectable: false,
            evented: false
        });

        canvas.add(straightPath);

        canvas.fire('path:created', { path: straightPath });

        lastBrushPos = { x: pointer.x, y: pointer.y };

        setTimeout(() => {
            canvas.isDrawingMode = true;
        }, 50);

        return;
    }

    if (!pointer || typeof pointer.x !== 'number' || typeof pointer.y !== 'number') {
        console.error('Invalid pointer coordinates:', pointer);
        return;
    }

    const clickX = Math.round(pointer.x);
    const clickY = Math.round(pointer.y);

    if (!isFinite(clickX) || !isFinite(clickY)) {
        console.error('Coordinates are NaN or Infinity:', clickX, clickY);
        return;
    }

    if (currentTool === tools.MAGIC) {
        if (!window.CURRENT_LABEL) {
            Swal.fire({
                title: 'No Label Selected',
                text: 'Please select a label from the dataset list first!',
                icon: 'warning',
                confirmButtonColor: '#4b49ac'
            });
            setTool(tools.SELECT);
            return;
        }

        // console.log(`Magic Click at -> X: ${clickX}, Y: ${clickY}`);
        runSAMMagic(clickX, clickY);
        opt.e.preventDefault();
        opt.e.stopPropagation();
        return;
    }



    shapeDrawingMouseDown(opt);
});

/* ------------------------------
   STATE MANAGEMENT
------------------------------ */
const tools = {
    SELECT: "select",
    BRUSH: "brush",
    ERASER: "eraser",
    RECT: "rect",
    CIRCLE: "circle",
    POLYGON: "polygon",
    PAINT: "paint",
    MAGIC: "magic"
};

let currentTool = tools.SELECT;
let brushSize = 10;
let currentZoom = 1.0;
let originalWidth = 0;
let originalHeight = 0;

// Pan/Drag state for zoomed canvas
let isPanning = false;
let lastPanX = 0;
let lastPanY = 0;

// Undo/Redo stacks
let historyStack = [];
let redoStack = [];
const MAX_HISTORY = 10;

// Polygon state
let polygonPoints = [];
let polygonRedoStack = [];
let polygonLineGroup = null;
let isDrawingPolygon = false;

// Shape drawing state
let isDrawingShape = false;
let shapeStartPoint = null;
let currentShape = null;
let lastBrushPos = null;

// timer
let taskTimerInterval = null;


const IGNORED_VALIDATION_ATTR = "Select Type";
const BRAND_COLOR = "#4b49ac";

/* ------------------------------
   TOOL SELECTION
------------------------------ */
let hasTaskStarted = false;

function startTaskOnce() {
    if (hasTaskStarted) return;
    const taskId = window.SEGMENTATION_CONFIG.taskId;
    // const isReadOnly = (window.SEGMENTATION_CONFIG && window.SEGMENTATION_CONFIG.readOnly);

    // if (isReadOnly) return;

    hasTaskStarted = true;
    // console.log("Lazy Start: Triggering task start API...");

    fetch(`/api/workflow/task/${taskId}/start/`, {
        method: "POST",
        headers: {
            "Content-Type": "application/json",
            "X-CSRFToken": getCSRFToken()
        }
    }).then(res => res.json())
        .then(data => {
            if (data.status === 'success') {
                // console.log("Task marked as IN_PROGRESS successfully.");
                if (data.start_time) {
                    startLiveTimer(data.start_time);
                }
            }
        }).catch(err => console.error("Error starting task:", err));
}

function setTool(tool) {
    startTaskOnce();

    const toolsRequiringLabel = [
        tools.BRUSH,
        tools.ERASER,
        tools.RECT,
        tools.CIRCLE,
        tools.POLYGON,
        tools.PAINT,
        tools.MAGIC
    ];

    if (toolsRequiringLabel.includes(tool) && !window.CURRENT_LABEL) {
        Swal.fire({
            title: 'No Label Selected',
            text: 'Please select a label from the Label Picker first!',
            icon: 'warning',
            confirmButtonColor: BRAND_COLOR,
            confirmButtonText: 'OK'
        });

        currentTool = tools.SELECT;
        document.querySelectorAll('.sidebar-btn').forEach(btn => {
            btn.classList.remove('active');
        });
        document.getElementById('btn-select')?.classList.add('active');
        return;
    }

    currentTool = tool;
    lastBrushPos = null;

    document.querySelectorAll('.sidebar-btn').forEach(btn => {
        btn.classList.remove('active');
    });
    document.getElementById(`btn-${tool}`)?.classList.add('active');

    if (tool !== tools.POLYGON) {
        clearPolygon();
    }

    canvas.isDrawingMode = (tool === tools.BRUSH || tool === tools.ERASER);

    if (tool === tools.MAGIC) {
        canvas.defaultCursor = 'crosshair';
        canvas.selection = false;
        canvas.discardActiveObject();
    }

    if (tool === tools.SELECT) {
        const isReadOnly = (window.SEGMENTATION_CONFIG && window.SEGMENTATION_CONFIG.readOnly);
        canvas.selection = !isReadOnly;

        canvas.getObjects().forEach((obj) => {
            if (isReadOnly) {
                obj.selectable = false;
                obj.evented = false;
                obj.hasControls = false;
                obj.hasBorders = false;
                obj.lockMovementX = true;
                obj.lockMovementY = true;
                return;
            }

            const isEraserPath = obj.globalCompositeOperation === 'destination-out';

            if (isEraserPath) {
                obj.selectable = false;
                obj.evented = false;
            } else if (obj.type !== 'image' || obj.isMask) {
                obj.selectable = true;
                obj.evented = true;
                obj.hasControls = true;
                obj.hasBorders = true;
                obj.lockMovementX = false;
                obj.lockMovementY = false;
            } else {
                obj.selectable = false;
                obj.evented = false;
            }
        });


    } else if (tool === tools.BRUSH) {

        canvas.selection = false;

        const rgb = hexToRgb(window.CURRENT_LABEL.color);

        canvas.freeDrawingBrush = new fabric.PencilBrush(canvas);
        canvas.freeDrawingBrush.color = `rgb(${rgb.r}, ${rgb.g}, ${rgb.b})`;
        canvas.freeDrawingBrush.width = brushSize;
        canvas.freeDrawingBrush.globalCompositeOperation = 'source-over';

        canvas.discardActiveObject();

        canvas.getObjects().forEach(obj => {
            obj.selectable = false;
            obj.evented = false;
        });
    }
    else if (tool === tools.ERASER) {
        canvas.selection = false;

        canvas.freeDrawingBrush = new fabric.PencilBrush(canvas);
        canvas.freeDrawingBrush.width = brushSize;
        canvas.freeDrawingBrush.color = 'rgba(255, 255, 255, 1)';

        canvas.discardActiveObject();

        canvas.getObjects().forEach(obj => {
            obj.selectable = false;
            obj.evented = false;
        });
    }
    else {
        canvas.selection = false;
        canvas.discardActiveObject();
        canvas.getObjects().forEach(obj => {
            obj.selectable = false;
            obj.evented = false;
        });
    }

    canvas.renderAll();
}


function updateToolbarState() {
    const hasLabel = !!window.CURRENT_LABEL;

    const toolsNeedingLabel = [
        'btn-brush',
        'btn-eraser',
        'btn-rect',
        'btn-circle',
        'btn-polygon',
        'btn-paint',
        'btn-magic'
    ];

    toolsNeedingLabel.forEach(btnId => {
        const btn = document.getElementById(btnId);
        if (btn) {
            if (!hasLabel) {
                btn.style.opacity = '0.4';
                btn.style.cursor = 'not-allowed';
                btn.setAttribute('data-disabled', 'true');
            } else {
                btn.style.opacity = '1';
                btn.style.cursor = 'pointer';
                btn.removeAttribute('data-disabled');
            }
        }
    });
}

/* ------------------------------
   BRUSH SIZE & OPACITY
------------------------------ */
let defaultMaskOpacity = 0.5;

function setBrushSize(size) {
    brushSize = parseInt(size);
    const display = document.getElementById('brushSizeDisplay');
    if (display) {
        display.innerText = brushSize + 'px';
    }

    if (canvas.freeDrawingBrush) {
        canvas.freeDrawingBrush.width = brushSize;
    }
}

function setMaskOpacity(value) {
    const newOpacity = parseFloat(value);
    const display = document.getElementById('opacityDisplay');
    if (display) {
        display.innerText = Math.round(newOpacity * 100) + '%';
    }

    const activeObjects = canvas.getActiveObjects();

    if (activeObjects.length > 0) {
        activeObjects.forEach(obj => {
            if (obj.labelName || obj.isMask || obj.isMaskGroup) {
                obj.set('opacity', newOpacity);
            }
        });
        canvas.requestRenderAll();
        triggerAutoSave();
    } else {
        defaultMaskOpacity = newOpacity;
    }
}

function updateOpacitySliderFromSelection() {
    const activeObjects = canvas.getActiveObjects();
    const slider = document.getElementById('opacitySlider');

    if (!slider) return;

    if (activeObjects.length > 0) {
        const firstObj = activeObjects[0];
        if (firstObj.labelName || firstObj.isMask || firstObj.isMaskGroup) {
            const objOpacity = firstObj.opacity || 0.5;
            slider.value = objOpacity;
            document.getElementById('opacityDisplay').innerText = Math.round(objOpacity * 100) + '%';
        }
    } else {
        slider.value = defaultMaskOpacity;
        document.getElementById('opacityDisplay').innerText = Math.round(defaultMaskOpacity * 100) + '%';
    }

    updateActionButtonsState();
}

function updateActionButtonsState() {
    const activeObj = canvas.getActiveObject();
    const btnConvert = document.getElementById('btn-convert');
    const btnMask = document.getElementById('btn-mask');

    if (!btnConvert || !btnMask) return;

    [btnConvert, btnMask].forEach(btn => {
        btn.style.opacity = '0.3';
        btn.style.pointerEvents = 'none';
        btn.classList.remove('active');
    });

    if (activeObj) {
        if (activeObj.isMask || activeObj.isMaskGroup || activeObj.type === 'path' || (activeObj.type === 'image' && activeObj.isMask)) {
            btnConvert.style.opacity = '1';
            btnConvert.style.pointerEvents = 'auto';
            btnConvert.title = "Convert to Polygon";
        }

        else if (activeObj.type === 'polygon') {
            btnMask.style.opacity = '1';
            btnMask.style.pointerEvents = 'auto';
            btnMask.title = "Convert to Mask";
        }
    }
}



/* ------------------------------
   ZOOM FUNCTIONS
------------------------------ */
function changeZoom(delta) {
    const newZoom = Math.max(0.1, Math.min(30.0, currentZoom + delta));
    applyZoom(newZoom, null);
}

function resetZoom() {
    const container = document.getElementById('canvasContainer');
    if (!container || !originalWidth || !originalHeight) {
        applyZoom(1.0);
        return;
    }

    const containerWidth = container.clientWidth;
    const containerHeight = container.clientHeight;

    const scaleX = containerWidth / originalWidth;
    const scaleY = containerHeight / originalHeight;

    let zoomLevel = Math.min(scaleX, scaleY) * 0.9;
    applyZoom(zoomLevel);
}

function applyZoom(zoomLevel, mousePoint = null) {
    const container = document.getElementById('canvasContainer');
    if (!container || !originalWidth || !originalHeight) return;

    const oldZoom = currentZoom;

    currentZoom = zoomLevel;

    const scaleRatio = currentZoom / oldZoom;

    let focusX, focusY;

    if (mousePoint) {
        focusX = mousePoint.x;
        focusY = mousePoint.y;
    } else {
        focusX = container.clientWidth / 2;
        focusY = container.clientHeight / 2;
    }

    const absoluteX = container.scrollLeft + focusX;
    const absoluteY = container.scrollTop + focusY;

    const newWidth = originalWidth * currentZoom;
    const newHeight = originalHeight * currentZoom;

    const zoomDisplay = document.getElementById("zoomDisplay");
    if (zoomDisplay) {
        zoomDisplay.innerText = Math.round(currentZoom * 100) + "%";
    }

    canvas.setZoom(currentZoom);
    canvas.setWidth(newWidth);
    canvas.setHeight(newHeight);

    imageCanvas.style.width = newWidth + 'px';
    imageCanvas.style.height = newHeight + 'px';

    const canvasWrapper = document.getElementById('canvasWrapper');
    canvasWrapper.style.width = newWidth + 'px';
    canvasWrapper.style.height = newHeight + 'px';
    container.scrollLeft = (absoluteX * scaleRatio) - focusX;
    container.scrollTop = (absoluteY * scaleRatio) - focusY;

    canvas.renderAll();
}

/* ------------------------------
   PAN/DRAG FUNCTIONALITY
------------------------------ */
let isAltPressed = false;

(function () {
    const container = document.getElementById('canvasContainer');
    if (!container) return;

    let lockedScrollLeft = 0;
    let lockedScrollTop = 0;
    let isMouseDownOnCanvas = false;

    container.addEventListener('mousedown', function (e) {
        if (isAltPressed || e.button === 1) return;
        isMouseDownOnCanvas = true;
        lockedScrollLeft = container.scrollLeft;
        lockedScrollTop = container.scrollTop;
    });

    container.addEventListener('scroll', function () {
        if (isMouseDownOnCanvas && !isPanning) {
            container.scrollLeft = lockedScrollLeft;
            container.scrollTop = lockedScrollTop;
        }
    });

    document.addEventListener('mouseup', function () {
        isMouseDownOnCanvas = false;
    });
})();

document.addEventListener('keydown', (e) => {
    if (e.key === 'Alt' && e.target.tagName !== 'INPUT' && !isAltPressed) {
        e.preventDefault();
        isAltPressed = true;
        canvas.defaultCursor = 'grab';
        canvas.hoverCursor = 'grab';
    }
});

document.addEventListener('keyup', (e) => {
    if (e.key === 'Alt') {
        isAltPressed = false;
        canvas.defaultCursor = 'default';
        canvas.hoverCursor = 'move';
    }
});

// Pan with mouse drag
canvas.on('mouse:down', function (opt) {
    const evt = opt.e;

    if ((evt.button === 1 || (isAltPressed && evt.button === 0)) &&
        currentTool === tools.SELECT) {
        isPanning = true;
        lastPanX = evt.clientX;
        lastPanY = evt.clientY;
        canvas.defaultCursor = 'grabbing';
        canvas.selection = false;
        opt.e.preventDefault();
        return;
    }
});

canvas.on('mouse:move', function (opt) {
    if (isPanning) {
        const evt = opt.e;
        const canvasWrapper = document.getElementById('canvasWrapper');
        const container = document.getElementById('canvasContainer');

        if (canvasWrapper && container) {
            const deltaX = evt.clientX - lastPanX;
            const deltaY = evt.clientY - lastPanY;

            container.scrollLeft -= deltaX;
            container.scrollTop -= deltaY;

            lastPanX = evt.clientX;
            lastPanY = evt.clientY;
        }

        opt.e.preventDefault();
        opt.e.stopPropagation();
    }
});

canvas.on('mouse:up', function (opt) {
    if (isPanning) {
        isPanning = false;
        canvas.defaultCursor = isAltPressed ? 'grab' : 'default';
        canvas.selection = currentTool === tools.SELECT;
        return;
    }

    if (currentTool === tools.BRUSH || currentTool === tools.ERASER) {
        const pointer = canvas.getPointer(opt.e);
        lastBrushPos = { x: pointer.x, y: pointer.y };
    }

    shapeDrawingMouseUp(opt);
});

canvas.on('mouse:wheel', function (opt) {
    const delta = opt.e.deltaY;
    let zoom = canvas.getZoom();
    zoom *= 0.999 ** delta;

    if (zoom > 30) zoom = 30;
    if (zoom < 0.1) zoom = 0.1;

    const container = document.getElementById('canvasContainer');
    const rect = container.getBoundingClientRect();

    const mousePoint = {
        x: opt.e.clientX - rect.left,
        y: opt.e.clientY - rect.top
    };

    applyZoom(zoom, mousePoint);

    opt.e.preventDefault();
    opt.e.stopPropagation();
});

/* ------------------------------
   SHAPE DRAWING (RECT, CIRCLE) 
------------------------------ */
let shapeDrawingMouseDown, shapeDrawingMouseMove, shapeDrawingMouseUp;

shapeDrawingMouseDown = function (options) {

    if (currentTool === tools.BRUSH || currentTool === tools.ERASER || currentTool === tools.MAGIC) {
        saveState();
        return;
    }

    if (currentTool === tools.SELECT) {
        return;
    }

    if (currentTool === tools.POLYGON) {
        handlePolygonClick(options);
        return;
    }

    if (currentTool === tools.RECT || currentTool === tools.CIRCLE) {

        const label = getCurrentLabelData();

        if (!label) {
            Swal.fire({
                title: 'No Label Selected',
                text: 'Please select a label from the dataset list first!',
                icon: 'warning',
                confirmButtonText: 'OK',
                confirmButtonColor: '#4b49ac'
            });
            return;
        }

        isDrawingShape = true;
        const pointer = canvas.getPointer(options.e);
        shapeStartPoint = pointer;

        saveState();

        const commonProps = {
            left: pointer.x,
            top: pointer.y,
            fill: label.color,
            stroke: label.color,
            strokeWidth: 1,
            selectable: false,
            evented: false,
            opacity: defaultMaskOpacity,
            erasable: true,
            labelName: label.name,
            labelColor: label.color,
            datasetId: label.id,
            attributes: label.attributes
        };

        if (currentTool === tools.RECT) {
            currentShape = new fabric.Rect({
                ...commonProps,
                width: 0,
                height: 0
            });
        } else if (currentTool === tools.CIRCLE) {
            currentShape = new fabric.Ellipse({
                ...commonProps,
                rx: 0,
                ry: 0
            });
        }
        canvas.add(currentShape);
        canvas.renderAll();
    }
};

shapeDrawingMouseMove = function (options) {
    if (currentTool === tools.SELECT) {
        return;
    }

    if (!isDrawingShape || !currentShape) return;

    const pointer = canvas.getPointer(options.e);

    if (currentTool === tools.RECT) {
        const width = pointer.x - shapeStartPoint.x;
        const height = pointer.y - shapeStartPoint.y;

        currentShape.set({
            width: Math.abs(width),
            height: Math.abs(height),
            left: width > 0 ? shapeStartPoint.x : pointer.x,
            top: height > 0 ? shapeStartPoint.y : pointer.y
        });
    } else if (currentTool === tools.CIRCLE) {
        const rx = Math.abs(pointer.x - shapeStartPoint.x) / 2;
        const ry = Math.abs(pointer.y - shapeStartPoint.y) / 2;

        currentShape.set({
            rx: rx,
            ry: ry,
            left: Math.min(pointer.x, shapeStartPoint.x),
            top: Math.min(pointer.y, shapeStartPoint.y)
        });
    }

    canvas.renderAll();
};
shapeDrawingMouseUp = function (options) {
    if (currentTool === tools.SELECT) return;

    if (isDrawingShape && currentShape) {

        if (currentShape.width === 0 || currentShape.height === 0) {
            canvas.remove(currentShape);
            canvas.renderAll();
            isDrawingShape = false;
            currentShape = null;
            return;
        }

        currentShape.set({
            evented: true,
            selectable: true,
            hasControls: true,
            hasBorders: true,
            opacity: defaultMaskOpacity,
            erasable: true,
            isBoundary: true
        });

        const finishedShape = currentShape;

        isDrawingShape = false;
        currentShape = null;
        shapeStartPoint = null;

        canvas.renderAll();
        updateLayerList();

        setTimeout(() => {
            setTool(tools.SELECT);
            canvas.setActiveObject(finishedShape);
            canvas.renderAll();
            updateLayerList();
        }, 10);
    }
};


// canvas.on('mouse:down', shapeDrawingMouseDown);
canvas.on('mouse:move', shapeDrawingMouseMove);
// canvas.on('mouse:up', shapeDrawingMouseUp);

/* ------------------------------
   POLYGON TOOL
------------------------------ */
function handlePolygonClick(options) {
    const pointer = canvas.getPointer(options.e);

    if (polygonPoints.length === 0) {
        saveState();
        isDrawingPolygon = true;
    }

    if (polygonPoints.length >= 3) {
        const firstPoint = polygonPoints[0];
        const distance = Math.sqrt(
            Math.pow(pointer.x - firstPoint.x, 2) +
            Math.pow(pointer.y - firstPoint.y, 2)
        );

        if (distance < 10) {
            finishPolygon();
            return;
        }
    }

    polygonPoints.push({ x: pointer.x, y: pointer.y });
    polygonRedoStack = [];
    updatePolygonPreview();
}

function updatePolygonPreview() {
    if (polygonLineGroup) {
        canvas.remove(polygonLineGroup);
    }

    if (polygonPoints.length === 0) return;

    const lines = [];
    for (let i = 0; i < polygonPoints.length - 1; i++) {
        lines.push(new fabric.Line([
            polygonPoints[i].x, polygonPoints[i].y,
            polygonPoints[i + 1].x, polygonPoints[i + 1].y
        ], {
            stroke: 'white',
            strokeWidth: 2,
            selectable: false,
            evented: false
        }));
    }

    polygonPoints.forEach(point => {
        lines.push(new fabric.Circle({
            left: point.x - 3,
            top: point.y - 3,
            radius: 3,
            fill: 'white',
            stroke: 'black',
            strokeWidth: 1,
            selectable: false,
            evented: false
        }));
    });

    polygonLineGroup = new fabric.Group(lines, {
        selectable: false,
        evented: false
    });

    canvas.add(polygonLineGroup);
    canvas.renderAll();
}


function finishPolygon() {
    if (polygonPoints.length < 3) return;

    if (!window.CURRENT_LABEL || !window.CURRENT_LABEL.color) {
        Swal.fire({
            title: 'No Label Selected',
            text: 'Please select a label from the dataset list first!',
            icon: 'warning',
            confirmButtonText: 'OK',
            confirmButtonColor: '#4b49ac'
        });
        clearPolygon();
        return;
    }

    const shapeColor = window.CURRENT_LABEL.color;
    const label = getCurrentLabelData();

    const polygon = new fabric.Polygon(polygonPoints, {
        fill: shapeColor,
        stroke: shapeColor,
        strokeWidth: 1,
        opacity: defaultMaskOpacity,
        selectable: true,
        evented: true,
        hasControls: true,
        hasBorders: true,
        erasable: true,
        objectCaching: false,
        labelName: label.name,
        labelColor: label.color,
        datasetId: label.id,
        attributes: label.attributes,
        isBoundary: true
    });





    canvas.add(polygon);
    setTool(tools.SELECT);
    setTimeout(() => {
        polygon.setCoords();
        canvas.setActiveObject(polygon);
        canvas.fire('selection:created', { selected: [polygon] });
        canvas.requestRenderAll();
        updateLayerList();
    }, 0);

    clearPolygon();

}

function clearPolygon() {
    if (polygonLineGroup) {
        canvas.remove(polygonLineGroup);
        polygonLineGroup = null;
    }
    polygonPoints = [];
    polygonRedoStack = [];
    isDrawingPolygon = false;
    canvas.renderAll();
}

//Polygon Editing Controls 

function polygonPositionHandler(dim, finalMatrix, fabricObject) {
    const pointIndex = this.pointIndex;
    const x = fabricObject.points[pointIndex].x - fabricObject.pathOffset.x;
    const y = fabricObject.points[pointIndex].y - fabricObject.pathOffset.y;

    return fabric.util.transformPoint(
        { x: x, y: y },
        fabric.util.multiplyTransformMatrices(
            fabricObject.canvas.viewportTransform,
            fabricObject.calcTransformMatrix()
        )
    );
}

function actionHandler(eventData, transform, x, y) {
    const polygon = transform.target;
    const currentControl = polygon.controls[polygon.__corner];
    const mouseLocalPosition = polygon.toLocalPoint(new fabric.Point(x, y), 'center', 'center');
    const polygonBaseSize = polygon._getNonTransformedDimensions();
    const size = polygon._getTransformedDimensions(0, 0);
    const finalPointPosition = {
        x: (mouseLocalPosition.x * polygonBaseSize.x) / size.x + polygon.pathOffset.x,
        y: (mouseLocalPosition.y * polygonBaseSize.y) / size.y + polygon.pathOffset.y
    };

    polygon.points[currentControl.pointIndex] = finalPointPosition;
    return true;
}

function anchorWrapper(anchorIndex, fn) {
    return function (eventData, transform, x, y) {
        const fabricObject = transform.target;

        const fullTransform = fabric.util.multiplyTransformMatrices(
            fabricObject.canvas.viewportTransform,
            fabricObject.calcTransformMatrix()
        );
        const absolutePoint = fabric.util.transformPoint({
            x: fabricObject.points[anchorIndex].x - fabricObject.pathOffset.x,
            y: fabricObject.points[anchorIndex].y - fabricObject.pathOffset.y
        }, fullTransform);

        const actionPerformed = fn(eventData, transform, x, y);
        fabricObject._setPositionDimensions({});

        const newFullTransform = fabric.util.multiplyTransformMatrices(
            fabricObject.canvas.viewportTransform,
            fabricObject.calcTransformMatrix()
        );
        const newAbsolutePoint = fabric.util.transformPoint({
            x: fabricObject.points[anchorIndex].x - fabricObject.pathOffset.x,
            y: fabricObject.points[anchorIndex].y - fabricObject.pathOffset.y
        }, newFullTransform);

        const drift = {
            x: (absolutePoint.x - newAbsolutePoint.x) / fabricObject.canvas.getZoom(),
            y: (absolutePoint.y - newAbsolutePoint.y) / fabricObject.canvas.getZoom()
        };
        fabricObject.set({
            left: fabricObject.left + drift.x,
            top: fabricObject.top + drift.y
        });
        fabricObject.setCoords();

        return actionPerformed;
    };
}

function editPolygon(polygon) {
    if (!polygon._originalControls) {
        polygon._originalControls = Object.assign({}, polygon.controls);
    }

    polygon.controls = {};
    polygon.cornerStyle = 'circle';
    polygon.cornerColor = 'rgba(0,153,255,0.5)';
    polygon.cornerSize = 10;
    polygon.transparentCorners = false;
    polygon.hasBorders = false;

    for (let i = 0; i < polygon.points.length; i++) {
        polygon.controls['p' + i] = new fabric.Control({
            positionHandler: polygonPositionHandler,
            actionHandler: anchorWrapper(i > 0 ? i - 1 : polygon.points.length - 1, actionHandler),
            actionName: 'modifyPolygon',
            pointIndex: i
        });
    }

    polygon.isEditMode = true;
    polygon.hasBorders = false;
    polygon.hasRotatingPoint = false;
    polygon.lockMovementX = true;
    polygon.lockMovementY = true;
    polygon.lockScalingX = true;
    polygon.lockScalingY = true;
    polygon.lockRotation = true;
    polygon.objectCaching = false;

    polygon.set({
        strokeWidth: 2,
        stroke: polygon.labelColor,
        strokeDashArray: [5, 5]
    });

    canvas.requestRenderAll();

    const badge = document.getElementById('polygon-edit-badge');
    if (badge) badge.classList.add('active');
}

function exitPolygonEditMode(polygon) {
    if (!polygon || !polygon.isEditMode) return;

    if (polygon._originalControls) {
        polygon.controls = polygon._originalControls;
        delete polygon._originalControls;
    } else {
        polygon.controls = fabric.Object.prototype.controls;
    }

    polygon.isEditMode = false;
    const matrix = polygon.calcTransformMatrix();
    const absolutePoints = polygon.points.map(p => {
        return fabric.util.transformPoint({
            x: p.x - polygon.pathOffset.x,
            y: p.y - polygon.pathOffset.y
        }, matrix);
    });

    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    absolutePoints.forEach(p => {
        if (p.x < minX) minX = p.x;
        if (p.y < minY) minY = p.y;
        if (p.x > maxX) maxX = p.x;
        if (p.y > maxY) maxY = p.y;
    });



    const newPoints = absolutePoints.map(p => ({
        x: p.x - minX,
        y: p.y - minY
    }));

    const newPolygon = new fabric.Polygon(newPoints, {
        left: minX,
        top: minY,
        fill: polygon.fill,
        stroke: polygon.stroke,
        strokeWidth: 1,
        opacity: polygon.opacity,
        objectCaching: false,
        selectable: true,
        evented: true,
        hasControls: true,
        hasBorders: true,
        labelName: polygon.labelName,
        labelColor: polygon.labelColor,
        datasetId: polygon.datasetId,
        attributes: polygon.attributes || {},
        isBoundary: true,
        erasable: true
    });

    polygon.hasControls = false;
    polygon.hasBorders = false;

    canvas.remove(polygon);
    canvas.add(newPolygon);
    canvas.setActiveObject(newPolygon);
    canvas.requestRenderAll();

    const badge = document.getElementById('polygon-edit-badge');
    if (badge) badge.classList.remove('active');

    triggerAutoSave();
    saveState();
}

function togglePolygonEditMode(polygon) {
    if (!polygon || polygon.type !== 'polygon') {
        console.warn('Selected object is not a polygon');
        return;
    }

    if (polygon.isEditMode) {
        exitPolygonEditMode(polygon);
    } else {
        editPolygon(polygon);
    }
}

// canvas.on('mouse:dblclick', function () {
//     if (currentTool === tools.POLYGON) {
//         finishPolygon();
//     }
// });


canvas.on('mouse:dblclick', function (options) {
    if (currentTool === tools.POLYGON && isDrawingPolygon) {
        finishPolygon();
        return;
    }

    const target = canvas.findTarget(options.e);
    if (target && target.type === 'polygon') {
        options.e.preventDefault();
        options.e.stopPropagation();

        togglePolygonEditMode(target);

        // if (target.isEditMode) {
        //     Swal.fire({
        //         toast: true,
        //         position: 'top-end',
        //         icon: 'info',
        //         title: 'Edit Mode ON',
        //         text: 'Drag vertices to reshape. Double-click to exit.',
        //         showConfirmButton: false,
        //         timer: 2000
        //     });
        // }
    }
});


canvas.on('selection:cleared', function (e) {
    canvas.getObjects().forEach(obj => {
        if (obj.type === 'polygon' && obj.isEditMode) {
            exitPolygonEditMode(obj);
        }
    });
});

canvas.on('selection:updated', function (e) {
    if (e.deselected) {
        e.deselected.forEach(obj => {
            if (obj.type === 'polygon' && obj.isEditMode) {
                exitPolygonEditMode(obj);
            }
        });
    }
});


canvas.on('object:modified', function (e) {
    const obj = e.target;

    if (obj && obj.type === 'polygon') {
        // console.log('Polygon modified, saving state');
        saveState();
        triggerAutoSave();
    }
});

/* ------------------------------
   UNDO / REDO
------------------------------ */
function saveState() {
    const json = JSON.stringify(canvas.toJSON([
        'selectable',
        'evented',
        'erasable',
        'isMask',
        'isMaskGroup',
        'isBoundary',
        'labelName',
        'labelColor',
        'opacity',
        'datasetId',
        'attributes',
        'globalCompositeOperation',
        'excludeFromExport'
    ]));

    if (historyStack.length > 0 && historyStack[historyStack.length - 1] === json) {
        return;
    }

    historyStack.push(json);

    if (historyStack.length > MAX_HISTORY) {
        historyStack.shift();
    }

    redoStack = [];
}

function undo() {
    if (currentTool === tools.POLYGON && isDrawingPolygon) {
        if (polygonPoints.length > 0) {
            const removedPoint = polygonPoints.pop();
            polygonRedoStack.push(removedPoint);
            // console.log("Removed last polygon point. Remaining:", polygonPoints.length);

            if (polygonPoints.length === 0) {
                clearPolygon();
            } else {
                updatePolygonPreview();
            }
        }
        return;
    }

    if (historyStack.length === 0) return;

    const currentState = JSON.stringify(canvas.toJSON([
        'selectable',
        'evented',
        'erasable',
        'isMask',
        'isMaskGroup',
        'isBoundary',
        'labelName',
        'labelColor',
        'opacity',
        'datasetId',
        'attributes',
        'globalCompositeOperation',
        'excludeFromExport'
    ])
    );
    redoStack.push(currentState);

    const previousState = historyStack.pop();
    canvas.loadFromJSON(previousState, function () {
        canvas.renderAll();
        setTool(currentTool);
    });
}

function redo() {
    if (currentTool === tools.POLYGON && isDrawingPolygon) {
        if (polygonRedoStack.length > 0) {
            const restoredPoint = polygonRedoStack.pop();
            polygonPoints.push(restoredPoint);
            updatePolygonPreview();
            // console.log("Restored polygon point. Total:", polygonPoints.length);
        }
        return;
    }

    if (redoStack.length === 0) return;

    const currentState = JSON.stringify(canvas.toJSON([
        'selectable',
        'evented',
        'erasable',
        'isMask',
        'isMaskGroup',
        'isBoundary',
        'labelName',
        'labelColor',
        'opacity',
        'datasetId',
        'attributes',
        'globalCompositeOperation',
        'excludeFromExport'
    ])
    );
    historyStack.push(currentState);

    const nextState = redoStack.pop();
    canvas.loadFromJSON(nextState, function () {
        canvas.renderAll();
        setTool(currentTool);
    });
}

// canvas.on('path:created', function (e) {
//     if (currentTool === tools.ERASER) {
//         e.path.set({
//             globalCompositeOperation: 'destination-out',
//             selectable: false,
//             evented: false,
//             excludeFromExport: true
//         });
//         canvas.renderAll();
//         return;
//     }

//     const label = getCurrentLabelData();

//     if (label) {
//         e.path.set({
//             opacity: defaultMaskOpacity, 
//             isBoundary: true,
//             erasable: true,
//             labelName: label.name,
//             labelColor: label.color,
//             datasetId: label.id,           
//             attributes: label.attributes   
//         });
//     }

//     lastBoundaryObject = e.path;
//     canvas.requestRenderAll();
//     updateLayerList();
// });


canvas.on('path:created', function (e) {
    const newPath = e.path;

    if (currentTool === tools.ERASER) {
        newPath.set({
            globalCompositeOperation: 'destination-out',
            selectable: false,
            evented: false,
            excludeFromExport: true,
            opacity: 1
        });
        canvas.renderAll();

        applyEraserToMasks(newPath);
        return;
    }

    const label = getCurrentLabelData();
    if (!label) return;

    const pathData = newPath.path;
    let isClosed = false;

    if (pathData && pathData.length > 2) {
        const start = pathData[0];
        const end = pathData[pathData.length - 1];

        const startX = start[1];
        const startY = start[2];
        const endX = end[end.length - 2];
        const endY = end[end.length - 1];

        const dist = Math.sqrt(Math.pow(startX - endX, 2) + Math.pow(startY - endY, 2));

        if (dist < 25) {
            newPath.set({
                fill: label.color,
                fillRule: 'evenodd'
            });
            isClosed = true;
        } else {
            newPath.set({ fill: null });
        }
    }

    newPath.set({
        opacity: 1,
        stroke: label.color,
        strokeWidth: brushSize,
        strokeLineCap: 'round',
        strokeLineJoin: 'round',
        isBoundary: true,
        erasable: true,
        labelName: label.name,
        labelColor: label.color,
        datasetId: label.id,
        attributes: label.attributes
    });


    newPath.set('opacity', defaultMaskOpacity);

    canvas.requestRenderAll();
    updateLayerList();

    if (window.mergeTimeout) clearTimeout(window.mergeTimeout);
    window.mergeTimeout = setTimeout(() => {
        mergeLabelBrushStrokes(label.id);
    }, 400);
});

/* ------------------------------
   APPLY ERASER TO MASKS 
------------------------------ */
function applyEraserToMasks(eraserPath) {
    const objects = canvas.getObjects();
    const w = originalWidth;
    const h = originalHeight;

    const datasetIds = [...new Set(
        objects.filter(o =>
            o !== eraserPath &&
            o.datasetId &&
            o.globalCompositeOperation !== 'destination-out' &&
            (o.type === 'path' || (o.type === 'image' && o.isMask) || o.isBoundary)
        ).map(o => String(o.datasetId))
    )];

    if (datasetIds.length === 0) {
        canvas.remove(eraserPath);
        canvas.renderAll();
        return;
    }

    const oldZoom = canvas.getZoom();
    const oldVpt = canvas.viewportTransform.slice();
    const oldW = canvas.getWidth();
    const oldH = canvas.getHeight();

    canvas.setZoom(1);
    canvas.setViewportTransform([1, 0, 0, 1, 0, 0]);
    canvas.setWidth(w);
    canvas.setHeight(h);

    const newMasks = [];

    datasetIds.forEach(dsId => {
        const labelObjs = objects.filter(o =>
            o !== eraserPath &&
            String(o.datasetId) === dsId &&
            o.globalCompositeOperation !== 'destination-out' &&
            (o.type === 'path' || (o.type === 'image' && o.isMask) || o.isBoundary)
        );

        if (labelObjs.length === 0) return;

        const refObj = labelObjs[0];
        const labelName = refObj.labelName;
        const labelColor = refObj.labelColor;
        const datasetId = refObj.datasetId;
        const attributes = refObj.attributes;

        const restoreStates = [];
        objects.forEach(o => {
            restoreStates.push({ obj: o, visible: o.visible, opacity: o.opacity });
            o.visible = false;
        });

        labelObjs.forEach(o => {
            o.visible = true;
            o.set('opacity', 1);
        });
        eraserPath.visible = true;
        eraserPath.set('opacity', 1);

        canvas.renderAll();

        const snapshotCanvas = canvas.toCanvasElement(1.0, {
            format: 'png',
            enableRetinaScaling: false
        });

        restoreStates.forEach(s => {
            s.obj.visible = s.visible;
            s.obj.set('opacity', s.opacity);
        });

        const ctx = snapshotCanvas.getContext('2d', { willReadFrequently: true });
        const imageData = ctx.getImageData(0, 0, w, h);
        const data = imageData.data;

        let minX = w, minY = h, maxX = 0, maxY = 0;
        let hasContent = false;

        for (let py = 0; py < h; py++) {
            for (let px = 0; px < w; px++) {
                if (data[(py * w + px) * 4 + 3] > 0) {
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
            w, h
        });
    });

    canvas.setZoom(oldZoom);
    canvas.setViewportTransform(oldVpt);
    canvas.setWidth(oldW);
    canvas.setHeight(oldH);

    canvas.remove(eraserPath);

    newMasks.forEach(entry => {
        entry.labelObjs.forEach(o => canvas.remove(o));

        if (!entry.hasContent) return; // Completely erased

        const cropW = entry.maxX - entry.minX + 1;
        const cropH = entry.maxY - entry.minY + 1;

        const cropCanvas = document.createElement('canvas');
        cropCanvas.width = cropW;
        cropCanvas.height = cropH;
        const cropCtx = cropCanvas.getContext('2d');
        cropCtx.drawImage(entry.snapshotCanvas, entry.minX, entry.minY, cropW, cropH, 0, 0, cropW, cropH);

        const img = new fabric.Image(cropCanvas, {
            left: entry.minX,
            top: entry.minY,
            opacity: defaultMaskOpacity,
            selectable: true,
            evented: true,
            isMask: true,
            isBoundary: true,
            erasable: true,
            labelName: entry.labelName,
            labelColor: entry.labelColor,
            datasetId: entry.datasetId,
            attributes: entry.attributes
        });

        canvas.add(img);
    });

    canvas.renderAll();
    updateLayerList();
}

/* ------------------------------
   MERGE BRUSH STROKES (Uniform Opacity)
------------------------------ */
function mergeLabelBrushStrokes(datasetId) {
    if (!datasetId || !originalWidth || !originalHeight) return;

    const objects = canvas.getObjects();

    const mergeableObjs = objects.filter(o =>
        String(o.datasetId) === String(datasetId) &&
        o.globalCompositeOperation !== 'destination-out' &&
        (o.type === 'path' || (o.type === 'image' && o.isMask))
    );

    if (mergeableObjs.length < 2) return;

    const w = originalWidth;
    const h = originalHeight;

    const oldZoom = canvas.getZoom();
    const oldVpt = canvas.viewportTransform.slice();
    const oldW = canvas.getWidth();
    const oldH = canvas.getHeight();

    canvas.setZoom(1);
    canvas.setViewportTransform([1, 0, 0, 1, 0, 0]);
    canvas.setWidth(w);
    canvas.setHeight(h);

    const restoreStates = [];
    objects.forEach(o => {
        restoreStates.push({ obj: o, visible: o.visible, opacity: o.opacity });
        o.visible = false;
    });

    mergeableObjs.forEach(o => {
        o.visible = true;
        o.set('opacity', 1);
    });

    canvas.renderAll();

    const snapshotCanvas = canvas.toCanvasElement(1.0, {
        format: 'png',
        enableRetinaScaling: false
    });

    restoreStates.forEach(s => {
        s.obj.visible = s.visible;
        s.obj.set('opacity', s.opacity);
    });
    canvas.setZoom(oldZoom);
    canvas.setViewportTransform(oldVpt);
    canvas.setWidth(oldW);
    canvas.setHeight(oldH);
    canvas.renderAll();

    const ctx = snapshotCanvas.getContext('2d', { willReadFrequently: true });
    const imageData = ctx.getImageData(0, 0, w, h);
    const data = imageData.data;

    let minX = w, minY = h, maxX = 0, maxY = 0;
    let hasContent = false;

    for (let py = 0; py < h; py++) {
        for (let px = 0; px < w; px++) {
            if (data[(py * w + px) * 4 + 3] > 0) {
                if (px < minX) minX = px;
                if (py < minY) minY = py;
                if (px > maxX) maxX = px;
                if (py > maxY) maxY = py;
                hasContent = true;
            }
        }
    }

    if (!hasContent) return;

    const pad = 2;
    minX = Math.max(0, minX - pad);
    minY = Math.max(0, minY - pad);
    maxX = Math.min(w - 1, maxX + pad);
    maxY = Math.min(h - 1, maxY + pad);

    const cropW = maxX - minX + 1;
    const cropH = maxY - minY + 1;
    if (cropW <= 0 || cropH <= 0) return;

    const cropCanvas = document.createElement('canvas');
    cropCanvas.width = cropW;
    cropCanvas.height = cropH;
    const cropCtx = cropCanvas.getContext('2d');
    cropCtx.drawImage(snapshotCanvas, minX, minY, cropW, cropH, 0, 0, cropW, cropH);

    const labelName = mergeableObjs[0].labelName;
    const labelColor = mergeableObjs[0].labelColor;
    const attributes = mergeableObjs[0].attributes || {};

    const wasLoading = window.IS_LOADING_STATE;
    window.IS_LOADING_STATE = true;
    mergeableObjs.forEach(o => canvas.remove(o));

    const mergedImg = new fabric.Image(cropCanvas, {
        left: minX,
        top: minY,
        width: cropW,
        height: cropH,
        opacity: defaultMaskOpacity,
        selectable: true,
        evented: true,
        isMask: true,
        isBoundary: true,
        erasable: true,
        labelName: labelName,
        labelColor: labelColor,
        datasetId: datasetId,
        attributes: attributes
    });

    canvas.add(mergedImg);
    canvas.renderAll();
    window.IS_LOADING_STATE = wasLoading;
    updateLayerList();
}

function getToolIconHtml(obj) {
    if (obj.isMask || obj.isMaskGroup) {
        return '<i class="bi bi-paint-bucket"></i>';
    }

    switch (obj.type) {
        case 'rect':
            return '<i class="bi bi-bounding-box"></i>';
        case 'ellipse':
        case 'circle':
            return '<i class="bi bi-circle"></i>';
        case 'polygon':
            return '<i class="bi bi-hexagon"></i>';
        case 'path':
            return '<i class="bi bi-brush"></i>';
        default:
            return '<i class="bi bi-tag-fill"></i>';
    }
}

function updateFloatingLabel() {
    const activeObj = canvas.getActiveObject();
    const labelEl = document.getElementById('floating-annotation-label');

    if (!activeObj || !activeObj.labelName || canvas.isDrawingMode) {
        labelEl.style.display = 'none';
        return;
    }

    const rect = activeObj.getBoundingRect();

    const iconHtml = getToolIconHtml(activeObj);
    labelEl.innerHTML = `${iconHtml} <span>${activeObj.labelName}</span>`;

    labelEl.style.backgroundColor = activeObj.labelColor || '#4b49ac';
    labelEl.style.display = 'flex';

    const labelWidth = labelEl.offsetWidth;
    const leftPos = rect.left + (rect.width / 2) - (labelWidth / 2);
    const topPos = rect.top - 8;

    labelEl.style.left = leftPos + 'px';
    labelEl.style.top = topPos + 'px';
}

canvas.on({
    'selection:created': updateFloatingLabel,
    'selection:updated': updateFloatingLabel,
    'selection:cleared': () => document.getElementById('floating-annotation-label').style.display = 'none',
    'object:moving': () => { updateFloatingLabel(); startTaskOnce(); },
    'object:scaling': () => { updateFloatingLabel(); startTaskOnce(); },
    'mouse:wheel': updateFloatingLabel
});


/* ------------------------------
   DELETE SELECTED
------------------------------ */
function deleteSelected() {
    const activeObjects = canvas.getActiveObjects();
    // console.log('>>> DELETE called. Active objects:', activeObjects.length);

    if (!activeObjects || activeObjects.length === 0) {
        // console.log('No objects selected to delete');
        return;
    }

    // console.log('Deleting objects:', activeObjects.map(obj => obj.type));
    saveState();

    canvas.discardActiveObject();

    activeObjects.forEach(obj => {
        canvas.remove(obj);
    });

    canvas.requestRenderAll();

    if (window.updateLayerList) window.updateLayerList();

    // console.log('Deleted objects:', activeObjects.length);
}
/* ------------------------------
   PAINT BUCKET (FLOOD FILL)
------------------------------ */
canvas.on('mouse:down', function (opt) {
    if (currentTool !== tools.PAINT) return;

    const pointer = canvas.getPointer(opt.e);
    const x = Math.round(pointer.x);
    const y = Math.round(pointer.y);

    if (!window.CURRENT_LABEL || !window.CURRENT_LABEL.color) {
        Swal.fire({
            title: 'No Label Selected',
            text: 'Please select a label from the dataset list first!',
            icon: 'warning',
            confirmButtonText: 'OK',
            confirmButtonColor: BRAND_COLOR
        });
        return;
    }

    saveState();

    const fillColor = window.CURRENT_LABEL.color;
    performFloodFill(x, y, fillColor);
});


function dilateMask(maskCtx, imageData, w, h, radius = 1) {
    const src = new Uint8ClampedArray(imageData.data);
    const dst = imageData.data;

    for (let y = 0; y < h; y++) {
        for (let x = 0; x < w; x++) {
            const idx = (y * w + x) * 4;
            if (src[idx + 3] > 0) continue;

            for (let dy = -radius; dy <= radius; dy++) {
                for (let dx = -radius; dx <= radius; dx++) {
                    const nx = x + dx;
                    const ny = y + dy;
                    if (nx < 0 || ny < 0 || nx >= w || ny >= h) continue;

                    const nIdx = (ny * w + nx) * 4;
                    if (src[nIdx + 3] > 0) {
                        dst[idx] = src[nIdx];
                        dst[idx + 1] = src[nIdx + 1];
                        dst[idx + 2] = src[nIdx + 2];
                        dst[idx + 3] = 255;
                        dx = dy = radius + 1;
                    }
                }
            }
        }
    }
}
function performFloodFill(startX, startY, colorHex) {
    const w = originalWidth;
    const h = originalHeight;

    if (!w || !h) {
        console.error("Original dimensions not found. Cannot fill.");
        return;
    }

    if (startX < 0 || startY < 0 || startX >= w || startY >= h) return;

    const currentZoom = canvas.getZoom();
    const currentVpt = canvas.viewportTransform.slice();
    const currentW = canvas.getWidth();
    const currentH = canvas.getHeight();

    const bgObj = canvas.getObjects().find(o => o.type === 'image' && !o.isMask);
    const bgWasVisible = bgObj ? bgObj.visible : true;
    if (bgObj) bgObj.set('visible', false);

    const restoreList = [];
    canvas.getObjects().forEach(obj => {
        if ((obj.isBoundary || obj.isMask || obj.isMaskGroup) && obj.visible) {
            restoreList.push({ obj: obj, opacity: obj.opacity });
            obj.set('opacity', 1);
        }
    });

    canvas.setZoom(1);
    canvas.setViewportTransform([1, 0, 0, 1, 0, 0]);
    canvas.setWidth(w);
    canvas.setHeight(h);
    canvas.renderAll();

    const snapshotCanvas = canvas.toCanvasElement(1.0, {
        format: 'png',
        enableRetinaScaling: false
    });

    const ctx = snapshotCanvas.getContext('2d', { willReadFrequently: true });
    const imageData = ctx.getImageData(0, 0, w, h);
    const data = imageData.data;

    canvas.setZoom(currentZoom);
    canvas.setViewportTransform(currentVpt);
    canvas.setWidth(currentW);
    canvas.setHeight(currentH);
    if (bgObj) bgObj.set('visible', bgWasVisible);
    restoreList.forEach(item => item.obj.set('opacity', item.opacity));
    canvas.renderAll();

    const getIdx = (x, y) => (y * w + x) * 4;
    const startIdx = getIdx(startX, startY);
    const targetR = data[startIdx];
    const targetG = data[startIdx + 1];
    const targetB = data[startIdx + 2];
    const targetA = data[startIdx + 3];

    const fillRGB = hexToRgb(colorHex);

    if (
        Math.abs(targetR - fillRGB.r) < 5 &&
        Math.abs(targetG - fillRGB.g) < 5 &&
        Math.abs(targetB - fillRGB.b) < 5 &&
        targetA > 200
    ) return;

    const maskCanvas = document.createElement('canvas');
    maskCanvas.width = w;
    maskCanvas.height = h;
    const maskCtx = maskCanvas.getContext('2d');
    const maskImgData = maskCtx.createImageData(w, h);
    const maskData = maskImgData.data;

    const stack = [[startX, startY]];
    const seen = new Uint8Array(w * h);
    let minX = w, minY = h, maxX = 0, maxY = 0;
    let filled = 0;

    while (stack.length) {
        const [x, y] = stack.pop();
        if (x < 0 || y < 0 || x >= w || y >= h) continue;

        const key = y * w + x;
        if (seen[key]) continue;
        seen[key] = 1;

        const i = getIdx(x, y);
        const r = data[i], g = data[i + 1], b = data[i + 2], a = data[i + 3];

        let shouldFill = false;
        if (targetA < 20) {
            shouldFill = a < 220;
        } else {
            shouldFill =
                Math.abs(r - targetR) +
                Math.abs(g - targetG) +
                Math.abs(b - targetB) < 50 &&
                Math.abs(a - targetA) < 100;
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

    dilateMask(maskCtx, maskImgData, w, h, 1);

    const pad = 2;
    minX = Math.max(0, minX - pad);
    minY = Math.max(0, minY - pad);
    maxX = Math.min(w, maxX + pad);
    maxY = Math.min(h, maxY + pad);

    const cropW = maxX - minX;
    const cropH = maxY - minY;
    if (cropW <= 0 || cropH <= 0) return;

    const cropCanvas = document.createElement('canvas');
    cropCanvas.width = cropW;
    cropCanvas.height = cropH;
    const cropCtx = cropCanvas.getContext('2d');
    const cropData = cropCtx.createImageData(cropW, cropH);

    for (let y = 0; y < cropH; y++) {
        for (let x = 0; x < cropW; x++) {
            const s = ((minY + y) * w + (minX + x)) * 4;
            const d = (y * cropW + x) * 4;
            if (maskData[s + 3]) {
                cropData.data.set(maskData.slice(s, s + 4), d);
            }
        }
    }
    cropCtx.putImageData(cropData, 0, 0);

    fabric.Image.fromURL(cropCanvas.toDataURL(), img => {
        const label = getCurrentLabelData();

        img.set({
            left: minX,
            top: minY,
            opacity: 1,
            selectable: true,
            evented: true,
            erasable: true,
            isMask: true,
            labelName: label ? label.name : window.CURRENT_LABEL.name,
            labelColor: label ? label.color : window.CURRENT_LABEL.color,
            datasetId: label ? label.id : null,
            attributes: label ? label.attributes : {}
        });

        img.set('opacity', defaultMaskOpacity);
        canvas.add(img);
        canvas.setActiveObject(img);

        canvas.requestRenderAll();
        saveState();
        updateLayerList();

        const mergeId = label ? label.id : null;
        if (mergeId) mergeLabelBrushStrokes(mergeId);
    });
}




function getMetadata() {
    const canvasJSON = canvas.toJSON([
        'selectable',
        'evented',
        'globalCompositeOperation',
        'isMask',
        'isMaskGroup',
        'isBoundary',
        'labelName',
        'labelColor',
        'opacity',
        'datasetId',
        'attributes',
        'erasable'
    ]);
    return {
        meta: {
            original_width: originalWidth,
            original_height: originalHeight,
            timestamp: new Date().toISOString()
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
            strokeWidth: obj.strokeWidth || 0
        };

        if (obj.type === 'rect') {
            shape.points = [
                { x: obj.left, y: obj.top },
                { x: obj.left + obj.width, y: obj.top },
                { x: obj.left + obj.width, y: obj.top + obj.height },
                { x: obj.left, y: obj.top + obj.height }
            ];
        } else if (obj.type === 'ellipse') {
            shape.radiusX = obj.rx;
            shape.radiusY = obj.ry;
            shape.center = { x: obj.left + obj.rx, y: obj.top + obj.ry };
        } else if (obj.type === 'polygon') {
            shape.points = obj.points;
        } else if (obj.type === 'path') {
            shape.path = obj.path;
        }

        shapes.push(shape);
    });

    return shapes;
}


/* ======================================================
   IMAGE FILTER LOGIC (Brightness, Contrast, Saturation)
   ====================================================== */

let imgFilterState = {
    brightness: 100,
    contrast: 100,
    saturation: 100
};

function openImageSettings() {
    const modal = document.getElementById('imageSettingsModal');
    if (modal && window.bootstrap && window.bootstrap.Modal) {
        const bsModal = new bootstrap.Modal(modal);
        bsModal.show();
    }
}

function updateFilterFromUI() {
    imgFilterState.brightness = parseInt(document.getElementById('range-brightness').value);
    imgFilterState.contrast = parseInt(document.getElementById('range-contrast').value);
    imgFilterState.saturation = parseInt(document.getElementById('range-saturation').value);

    applyFilters();
}

function adjustFilterValue(type, amount) {
    imgFilterState[type] = Math.max(0, Math.min(300, imgFilterState[type] + amount));

    document.getElementById(`range-${type}`).value = imgFilterState[type];

    applyFilters();
}

function resetImageFilters() {
    imgFilterState = { brightness: 100, contrast: 100, saturation: 100 };

    ['brightness', 'contrast', 'saturation'].forEach(type => {
        document.getElementById(`range-${type}`).value = 100;
    });

    applyFilters();
}

function applyFilters() {
    document.getElementById('val-brightness').innerText = imgFilterState.brightness + "%";
    document.getElementById('val-contrast').innerText = imgFilterState.contrast + "%";
    document.getElementById('val-saturation').innerText = imgFilterState.saturation + "%";

    const filterString = `
        brightness(${imgFilterState.brightness}%) 
        contrast(${imgFilterState.contrast}%) 
        saturate(${imgFilterState.saturation}%)
    `;

    const imgCanvas = document.getElementById('imageCanvas');
    if (imgCanvas) {
        imgCanvas.style.filter = filterString;
    }
}

/* ------------------------------
   KEYBOARD SHORTCUTS
------------------------------ */
document.addEventListener("keydown", e => {


    if (e.target.tagName === "INPUT" || e.target.tagName === "TEXTAREA") return;

    const isModalOpen = document.querySelector('.modal.show');
    if (isModalOpen && isModalOpen.id !== 'imageSettingsModal') return;

    if (window.SEGMENTATION_CONFIG.readOnly) {
        return;
    }

    const key = e.key.toLowerCase();
    const STEP = 10;

    if (e.key === "1") adjustFilterValue('brightness', STEP);
    else if (e.key === "2") adjustFilterValue('brightness', -STEP);

    else if (e.key === "4") adjustFilterValue('contrast', STEP);
    else if (e.key === "5") adjustFilterValue('contrast', -STEP);

    else if (e.key === "7") adjustFilterValue('saturation', STEP);
    else if (e.key === "8") adjustFilterValue('saturation', -STEP);

    else if (e.key === "0") resetImageFilters();


    if (e.key === "v") setTool(tools.SELECT);
    else if (e.key === "b") setTool(tools.BRUSH);
    if (e.key === "e") {
        if (currentTool !== tools.ERASER) {
            const activeObj = canvas.getActiveObject();
            if (activeObj && activeObj.type === 'polygon') {
                e.preventDefault();
                togglePolygonEditMode(activeObj);
                return;
            }
        }
        setTool(tools.ERASER);
    }
    else if (e.key === "r") setTool(tools.RECT);
    else if (e.key === "f") setTool(tools.PAINT);
    else if (e.key === "c") setTool(tools.CIRCLE);
    else if (e.key === "g") setTool(tools.POLYGON);
    else if (e.key === "Delete" || e.key === "Backspace") {
        e.preventDefault();
        deleteSelected();
    }
    else if (e.key === "z" && !e.ctrlKey) undo();
    else if (e.key === "y" && !e.ctrlKey) redo();
    else if (e.key === "s" && !e.ctrlKey) {
        e.preventDefault();
        saveMask();
    }
    else if (e.key === "k") {
        openShortcutsModal();
    }
    else if (e.key === "Enter" && currentTool === tools.POLYGON) {
        finishPolygon();
    }



    if (e.key === "Escape") {
        const activeObj = canvas.getActiveObject();
        if (activeObj && activeObj.type === 'polygon' && activeObj.isEditMode) {
            e.preventDefault();
            exitPolygonEditMode(activeObj);
        }
    }
});

/* ===============================
   INITIALIZATION
================================ */
// console.log("SEGMENTATION_CONFIG:", window.SEGMENTATION_CONFIG);
const config = window.SEGMENTATION_CONFIG || {};
const { imageUrl, taskId, startTime } = config;


// if (!startTime || isNaN(new Date(startTime).getTime())) {
//     console.log("Lazy Start active: startTime will be set once work begins.");
// }

// if (!imageUrl) console.warn("SEGMENTATION_CONFIG missing or invalid (imageUrl not found).");

// console.log("imageUrl:", imageUrl);
// console.log("taskId:", taskId);
// console.log("startTime:", startTime);

if (config.isRework) {
    const modalEl = document.getElementById('reworkReasonModal');
    if (modalEl) {
        const storageKey = `seenRework_${taskId}`;
        if (!sessionStorage.getItem(storageKey)) {
            setTimeout(() => {
                const modal = new bootstrap.Modal(modalEl);
                modal.show();
                sessionStorage.setItem(storageKey, 'true');
            }, 500);
        }
    }
}

function startLiveTimer(forcedStartTime) {
    const timerDisplay = document.getElementById('taskTimer');
    if (!timerDisplay) return;

    const timeToUse = forcedStartTime || startTime;

    if (!timeToUse || isNaN(new Date(timeToUse).getTime())) {
        timerDisplay.textContent = "00:00:00";
        return;
    }

    if (taskTimerInterval) {
        clearInterval(taskTimerInterval);
        taskTimerInterval = null;
    }

    const start = new Date(timeToUse).getTime();

    taskTimerInterval = setInterval(() => {
        const diff = Math.max(0, Date.now() - start);

        const hours = Math.floor(diff / 3600000);
        const minutes = Math.floor((diff % 3600000) / 60000);
        const seconds = Math.floor((diff % 60000) / 1000);

        const pad = n => String(n).padStart(2, '0');
        timerDisplay.textContent =
            `${pad(hours)}:${pad(minutes)}:${pad(seconds)}`;
    }, 1000);
}


const img = new Image();
img.crossOrigin = "anonymous";

if (!imageUrl) {
    console.error("Aborting image load: imageUrl is missing/undefined");
}

img.onerror = function () {
    console.error("Failed to load image:", imageUrl);
    alert(`Failed to load image: ${imageUrl}\nPlease check if the file exists and is accessible.`);
};

img.onload = () => {
    const w = img.naturalWidth || img.width;
    const h = img.naturalHeight || img.height;

    // console.log("✅ Image loaded successfully (Natural):", w, "x", h, "Rendered:", img.width, "x", img.height);

    originalWidth = w;
    originalHeight = h;


    const minDimension = Math.min(w, h);

    const dynamicMax = Math.max(50, Math.floor(minDimension / 5));

    const dynamicDefault = Math.max(2, Math.floor(minDimension / 35));

    const brushSlider = document.getElementById('brushSlider');
    if (brushSlider) {
        brushSlider.max = dynamicMax;
        brushSlider.value = dynamicDefault;
    }

    setBrushSize(dynamicDefault);

    imageCanvas.width = originalWidth;
    imageCanvas.height = originalHeight;
    imgCtx.drawImage(img, 0, 0, originalWidth, originalHeight);
    // console.log("✅ Background rendered on imageCanvas");

    canvas.setWidth(originalWidth);
    canvas.setHeight(originalHeight);
    canvas.backgroundColor = null;
    // console.log("✅ Fabric canvas set to transparent (backgroundColor: null)");

    if (config.savedState && config.savedState.fabricJSON) {
        // console.log("Found saved state.", config.savedState);
        const jsonToLoad = config.savedState.fabricJSON;

        // if (jsonToLoad.objects) {
        //     console.log(`Saved Objects count: ${jsonToLoad.objects.length}`);
        //     jsonToLoad.objects.forEach((o, i) => console.log(`Object ${i}: type=${o.type}, visible=${o.visible}, opacity=${o.opacity}`));
        // }

        window.IS_LOADING_STATE = true;

        canvas.loadFromJSON(jsonToLoad, function () {
            // console.log("Canvas loaded from JSON.");
            window.IS_LOADING_STATE = false;

            const isReadOnly = config.readOnly;
            canvas.getObjects().forEach(obj => {
                if (obj.globalCompositeOperation === 'destination-out') {
                    canvas.remove(obj);
                    return;
                }
                obj.set({
                    selectable: !isReadOnly,
                    evented: !isReadOnly,
                    hasControls: !isReadOnly,
                    hasBorders: !isReadOnly,
                    lockMovementX: isReadOnly,
                    lockMovementY: isReadOnly,
                    lockRotation: isReadOnly,
                    lockScalingX: isReadOnly,
                    lockScalingY: isReadOnly
                });

                if (typeof obj.opacity === 'undefined') {
                    obj.set('opacity', defaultMaskOpacity);
                }

                if (obj.type === 'image' && (obj.labelName || obj.datasetId)) {
                    obj.isMask = true;
                }
            });

            canvas.renderAll();

            setTool(tools.SELECT);

            if (window.updateLayerList) updateLayerList();
        });
    } else {
        canvas.renderAll();
    }

    const btnSelect = document.getElementById('btn-select');
    if (btnSelect) {
        btnSelect.click();
    }

    if (window.CURRENT_LABEL && window.CURRENT_LABEL.color) {
        window.updateBrushColor(window.CURRENT_LABEL.color);
    }

    startLiveTimer();
};


if (imageUrl) {
    requestAnimationFrame(function () {
        img.src = imageUrl;
    });
}
// console.log("Loading image from:", imageUrl);

window.updateBrushColor = function (color) {
    if (!color) return;
    // console.log("Updating brush color to:", color);

    const rgb = hexToRgb(color);
    const rgba = `rgba(${rgb.r}, ${rgb.g}, ${rgb.b})`;
    const stroke = `rgb(${rgb.r}, ${rgb.g}, ${rgb.b})`;

    fabric.Object.prototype.transparentCorners = false;

    if (canvas.freeDrawingBrush) {
        canvas.freeDrawingBrush.color = stroke;
        canvas.freeDrawingBrush.width = brushSize;
        canvas.freeDrawingBrush.globalCompositeOperation = 'source-over';

    }

    window.CURRENT_COLOR_RGBA = rgba;
    window.CURRENT_COLOR_STROKE = stroke;
};

function hexToRgb(hex) {
    const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
    return result
        ? { r: parseInt(result[1], 16), g: parseInt(result[2], 16), b: parseInt(result[3], 16) }
        : { r: 0, g: 0, b: 0 };
}


window.CURRENT_COLOR_RGBA = 'rgba(0, 100, 255, 0.8)';
window.CURRENT_COLOR_STROKE = 'rgb(0, 100, 255)';

/* ------------------------------
   IMAGE ENHANCEMENTS
------------------------------ */
window.updateImageFilters = function () {
    const contrast = document.getElementById('contrastSlider').value;
    const saturation = document.getElementById('saturationSlider').value;
    const brightness = document.getElementById('brightnessSlider').value;

    // console.log(`Filters - Contrast: ${contrast}, Saturation: ${saturation}, Brightness: ${brightness}`);

    document.getElementById('contrastDisplay').innerText = contrast + '%';
    document.getElementById('saturationDisplay').innerText = saturation + '%';
    document.getElementById('brightnessDisplay').innerText = brightness + '%';

    const imgCanvas = document.getElementById('imageCanvas');
    if (imgCanvas) {
        const filterString = `contrast(${contrast}%) saturate(${saturation}%) brightness(${brightness}%)`;
        // console.log("Applying filter:", filterString);
        imgCanvas.style.filter = filterString;
    } else {
        console.error("❌ imageCanvas element not found!");
    }
};

/* ------------------------------
   LAYER HISTORY
------------------------------ */
function updateLayerList() {
    const listContainer = document.getElementById('layerList');
    if (!listContainer) return;

    listContainer.innerHTML = '';

    const objects = canvas.getObjects();
    const maskObjects = objects.filter(obj => {
        if (obj.type === 'image' && !obj.isMask) return false;
        if (obj.globalCompositeOperation === 'destination-out') return false;
        if (obj.labelName || obj.isMask || obj.isMaskGroup) return true;
        return false;
    });

    if (maskObjects.length === 0) {
        listContainer.innerHTML = '<div class="text-muted text-center p-3 small">No shapes drawn yet.</div>';
        return;
    }

    [...maskObjects].reverse().forEach((obj) => {
        let labelName = obj.labelName || 'Mask';
        let labelColor = obj.labelColor || '#666666';

        const item = document.createElement('div');
        item.className = 'd-flex align-items-center p-2 border-bottom small';
        item.style.cursor = 'pointer';
        item.style.transition = 'background-color 0.2s';

        if (canvas.getActiveObjects().includes(obj)) {
            item.style.backgroundColor = '#e8f0fe';
            item.style.borderLeft = '3px solid #4b49ac';
        } else {
            item.style.backgroundColor = '#fff';
            item.style.borderLeft = '3px solid transparent';
        }

        // Color Box
        const colorBox = document.createElement('span');
        colorBox.style.width = '12px';
        colorBox.style.height = '12px';
        colorBox.style.backgroundColor = labelColor;
        colorBox.style.border = '1px solid rgba(0,0,0,0.2)';
        colorBox.style.borderRadius = '2px';
        colorBox.style.marginRight = '8px';
        colorBox.style.flexShrink = '0';

        // Text (Label + Attributes)
        const textContainer = document.createElement('div');
        textContainer.className = 'flex-grow-1';
        textContainer.style.overflow = 'hidden';

        const typeIcon = getTypeIcon(obj.type);

        let attrString = "";
        if (obj.attributes && typeof obj.attributes === 'object') {
            attrString = Object.entries(obj.attributes)
                .filter(([_, val]) => val && val.toString().trim() !== "")
                .map(([key, val]) => `${key}: ${val}`)
                .join(', ');
        }

        textContainer.innerHTML = `
            <div class="d-flex justify-content-between align-items-center">
                <span style="font-weight: 600; color: #333;">${typeIcon} ${labelName}</span>
            </div>
            ${attrString ? `<div class="text-muted text-truncate" style="font-size: 11px; margin-top: 2px;">${attrString}</div>` : ''}
        `;

        const opacityBadge = document.createElement('span');
        opacityBadge.className = 'badge badge-light border ms-2';
        opacityBadge.style.fontSize = '10px';
        opacityBadge.textContent = Math.round((obj.opacity || 0.5) * 100) + '%';

        item.appendChild(colorBox);
        item.appendChild(textContainer);
        item.appendChild(opacityBadge);

        if (!window.SEGMENTATION_CONFIG.readOnly) {
            item.onclick = (e) => {
                canvas.discardActiveObject();
                canvas.setActiveObject(obj);
                canvas.requestRenderAll();
                updateLayerList();
            };
        } else {
            item.style.cursor = 'default';
        }

        listContainer.appendChild(item);
    });
}

function getTypeIcon(type) {
    const icons = {
        'rect': '<i class="bi bi-bounding-box"></i>',
        'circle': '<i class="bi bi-circle"></i>',
        'ellipse': '<i class="bi bi-circle"></i>',
        'polygon': '<i class="bi bi-hexagon"></i>',
        'path': '<i class="bi bi-brush"></i>',
        'group': '<i class="bi bi-layers-half"></i>',
        'image': '<i class="bi bi-tag-fill"></i>'
    };
    return icons[type] || '<i class="bi bi-record-circle"></i>';
}


/* ------------------------------
   AUTO SAVE
------------------------------ */
let autoSaveTimeout;
const AUTO_SAVE_DELAY = 1000;

function triggerAutoSave() {
    const statusEl = document.getElementById('saveStatus');
    if (statusEl) {
        statusEl.innerHTML = '<i class="bi bi-arrow-repeat spin"></i> Saving...';
        statusEl.classList.remove('text-success', 'text-muted');
        statusEl.classList.add('text-warning');
    }

    if (autoSaveTimeout) clearTimeout(autoSaveTimeout);

    autoSaveTimeout = setTimeout(() => {
        saveMask(false, true);
    }, AUTO_SAVE_DELAY);
}

canvas.on('object:added', (e) => {
    if (window.IS_LOADING_STATE) return;
    updateLayerList();
    triggerAutoSave();
});
canvas.on('object:removed', (e) => {
    if (window.IS_LOADING_STATE) return;
    updateLayerList();
    triggerAutoSave();
});
canvas.on('selection:created', (e) => {
    // console.log('Selection created');
    updateLayerList();
    updateOpacitySliderFromSelection();
});

canvas.on('selection:updated', (e) => {
    // console.log('Selection updated');
    updateLayerList();
    updateOpacitySliderFromSelection();
});

canvas.on('selection:cleared', (e) => {
    // console.log('Selection cleared');
    updateLayerList();
    updateOpacitySliderFromSelection();
    if (!window._attributeShownByLabel) {
        var panel = document.getElementById('attributePanel');
        if (panel) panel.style.display = 'none';
    }
});

function syncLabelFromSelection(e) {
    const activeObj = e.selected ? e.selected[0] : canvas.getActiveObject();

    if (activeObj && activeObj.labelName && activeObj.datasetId) {
        window.CURRENT_LABEL = {
            name: activeObj.labelName,
            color: activeObj.labelColor,
            id: activeObj.datasetId,
            attributes: activeObj.attributes || {}
        };

        // console.log("Synced label from selection:", window.CURRENT_LABEL);

        document.querySelectorAll('.dataset-item').forEach(el => el.classList.remove('active'));
        const activeEl = document.getElementById('label-' + activeObj.datasetId);
        if (activeEl) activeEl.classList.add('active');

        if (window.updateBrushColor) {
            window.updateBrushColor(activeObj.labelColor);
        }

        if (typeof window.renderAttributeForm === 'function') {
            window.renderAttributeForm({
                id: activeObj.id,
                labelName: activeObj.labelName,
                labelColor: activeObj.labelColor,
                datasetId: activeObj.datasetId,
                attributes: activeObj.attributes || {}
            });
        }
    }
}

canvas.on('selection:created', syncLabelFromSelection);
canvas.on('selection:updated', syncLabelFromSelection);


/* ======================================================
   ALGORITHMS: Geometry Helpers
   ====================================================== */
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

/* ======================================================
   MAIN FUNCTION: Convert Mask -> Polygon
   ====================================================== */
function convertToPolygon() {
    const activeObj = canvas.getActiveObject();

    if (!activeObj) {
        Swal.fire("Select a Mask", "Please click on the mask you want to convert.", "warning");
        return;
    }

    if (activeObj.type === 'polygon') {
        Swal.fire("Already a Polygon", "This object is already a polygon.", "info");
        return;
    }

    // console.log("🛠️ convertToPolygon - Active Object:", activeObj.type,
    //     "left:", activeObj.left, "top:", activeObj.top,
    //     "width:", activeObj.width, "height:", activeObj.height,
    //     "scaleX:", activeObj.scaleX, "scaleY:", activeObj.scaleY);

    // --- Render the object to its own local canvas ---
    const originalOpacity = activeObj.opacity;

    activeObj.set('opacity', 1);

    const objCanvas = activeObj.toCanvasElement({
        enableRetinaScaling: false
    });

    activeObj.set('opacity', originalOpacity);

    const objW = objCanvas.width;
    const objH = objCanvas.height;
    // console.log('🛠️ convertToPolygon - Object canvas: ' + objW + ' x ' + objH);

    const objCtx = objCanvas.getContext('2d', { willReadFrequently: true });
    const imageData = objCtx.getImageData(0, 0, objW, objH);
    const data = imageData.data;

    // Count opaque pixels for diagnostics
    let opaqueCount = 0;
    for (let i = 3; i < data.length; i += 4) {
        if (data[i] > 10) opaqueCount++;
    }
    // console.log('🛠️ convertToPolygon - Opaque pixels: ' + opaqueCount + ' / ' + (objW * objH));

    if (opaqueCount === 0) {
        Swal.fire("Empty Mask", "No visible pixels found to trace.", "warning");
        return;
    }

    // Build binary grid
    const grid = new Uint8Array(objW * objH);
    for (let y = 0; y < objH; y++) {
        for (let x = 0; x < objW; x++) {
            grid[y * objW + x] = data[(y * objW + x) * 4 + 3] > 10 ? 1 : 0;
        }
    }

    // Find the starting boundary pixel
    let startX = -1, startY = -1;
    findStart: for (let y = 0; y < objH; y++) {
        for (let x = 0; x < objW; x++) {
            if (grid[y * objW + x] === 1) {
                if (x === 0 || x === objW - 1 || y === 0 || y === objH - 1 ||
                    grid[y * objW + (x - 1)] === 0 ||
                    grid[y * objW + (x + 1)] === 0 ||
                    grid[(y - 1) * objW + x] === 0 ||
                    grid[(y + 1) * objW + x] === 0) {
                    startX = x;
                    startY = y;
                    break findStart;
                }
            }
        }
    }

    if (startX === -1) {
        findAny: for (let y = 0; y < objH; y++) {
            for (let x = 0; x < objW; x++) {
                if (grid[y * objW + x] === 1) {
                    startX = x; startY = y;
                    break findAny;
                }
            }
        }
    }

    if (startX === -1) {
        Swal.fire("Empty Mask", "No visible pixels found.", "warning");
        return;
    }

    // console.log('🛠️ convertToPolygon - Start boundary: (' + startX + ', ' + startY + ')');

    // --- Scanline Boundary Extraction ---
    // For each row, find the leftmost and rightmost opaque pixel.
    // Left edges form the left side (top to bottom).
    // Right edges form the right side (bottom to top).
    // Combined, they form a closed polygon outline.
    const leftEdge = [];
    const rightEdge = [];

    for (let y = 0; y < objH; y++) {
        let leftX = -1, rightX = -1;
        for (let x = 0; x < objW; x++) {
            if (grid[y * objW + x] === 1) {
                if (leftX === -1) leftX = x;
                rightX = x;
            }
        }
        if (leftX !== -1) {
            leftEdge.push({ x: leftX, y: y });
            rightEdge.push({ x: rightX, y: y });
        }
    }

    if (leftEdge.length < 2) {
        Swal.fire("Conversion Failed", "Insufficient boundary data.", "error");
        return;
    }

    // Build closed polygon: left edge top→bottom, then right edge bottom→top
    const contourPoints = [];
    for (let i = 0; i < leftEdge.length; i++) {
        contourPoints.push(leftEdge[i]);
    }
    for (let i = rightEdge.length - 1; i >= 0; i--) {
        // Avoid duplicate if left and right are the same pixel
        if (rightEdge[i].x !== leftEdge[i].x) {
            contourPoints.push(rightEdge[i]);
        }
    }

    // console.log('🛠️ convertToPolygon - Scanline boundary points: ' + contourPoints.length);

    const simplifiedPoints = simplifyPoints(contourPoints, 1.5);
    // console.log('🛠️ convertToPolygon - Simplified: ' + simplifiedPoints.length);

    // Offset from local object space to absolute image space
    const offsetX = activeObj.left;
    const offsetY = activeObj.top;
    const absolutePoints = simplifiedPoints.map(p => ({
        x: p.x + offsetX,
        y: p.y + offsetY
    }));

    // console.log('🛠️ convertToPolygon - Offset: (' + offsetX + ', ' + offsetY + '), first: (' + absolutePoints[0].x + ', ' + absolutePoints[0].y + ')');

    const newPolygon = new fabric.Polygon(absolutePoints, {
        fill: activeObj.labelColor,
        stroke: activeObj.labelColor,
        strokeWidth: 0,
        opacity: defaultMaskOpacity,
        objectCaching: false,
        selectable: true,
        evented: true,
        hasControls: true,
        hasBorders: true,
        labelName: activeObj.labelName,
        labelColor: activeObj.labelColor,
        datasetId: activeObj.datasetId,
        attributes: activeObj.attributes || {},
        isBoundary: true
    });

    if (newPolygon.pathOffset) {
        // console.log('🛠️ convertToPolygon - pathOffset correction: left ' +
        //     newPolygon.left + ' -> ' + newPolygon.pathOffset.x +
        //     ', top ' + newPolygon.top + ' -> ' + newPolygon.pathOffset.y);
        newPolygon.set({
            left: newPolygon.pathOffset.x,
            top: newPolygon.pathOffset.y,
            originX: 'center',
            originY: 'center'
        });
        newPolygon.setCoords();
    }

    canvas.remove(activeObj);
    canvas.add(newPolygon);
    canvas.setActiveObject(newPolygon);
    canvas.renderAll();

    Swal.close();
    if (window.updateLayerList) window.updateLayerList();
    updateActionButtonsState();
    saveState();
}

/* ======================================================
    Convert Polygon -> Mask (Improved)
   ====================================================== */
function convertToMask() {
    const activeObj = canvas.getActiveObject();

    if (!activeObj) {
        Swal.fire("Select a Polygon", "Please click on the polygon you want to convert.", "warning");
        return;
    }

    if (activeObj.type !== 'polygon') {
        Swal.fire("Not a Polygon", "The selected object is not a polygon.", "info");
        return;
    }
    const originalOpacity = activeObj.opacity;
    activeObj.set('opacity', 1);
    const startLeft = activeObj.left;
    const startTop = activeObj.top;

    const dataURL = activeObj.toDataURL({
        format: 'png',
        multiplier: 1,
        enableRetinaScaling: false
    });

    activeObj.set('opacity', originalOpacity);

    fabric.Image.fromURL(dataURL, function (img) {

        img.set({
            left: startLeft,
            top: startTop,
            scaleX: 1,
            scaleY: 1,
            opacity: originalOpacity,

            selectable: true,
            evented: true,
            hasControls: true,
            hasBorders: true,

            isMask: true,
            isBoundary: true,
            type: 'image',

            labelName: activeObj.labelName,
            labelColor: activeObj.labelColor,
            datasetId: activeObj.datasetId,
            attributes: activeObj.attributes || {}
        });

        canvas.remove(activeObj);
        canvas.add(img);
        canvas.setActiveObject(img);
        canvas.renderAll();

        if (window.updateLayerList) window.updateLayerList();
        updateActionButtonsState();

        // console.log("Converted Polygon to Mask (Raster Image).");

        setTimeout(() => {
            if (window.updateLayerList) window.updateLayerList();
            updateActionButtonsState();
        }, 50);
    });
}


function notifyTaskSubmitted(taskId) {
    const channel = new BroadcastChannel("production_tasks");

    channel.postMessage({
        type: "TASK_SUBMITTED",
        taskId: taskId
    });

    channel.close();
}


/* ------------------------------
   SUBMIT WORKFLOW
------------------------------ */

async function saveMask(isSubmitting = false, isAutoSave = false) {
    const statusEl = document.getElementById('saveStatus');

    if (isAutoSave && statusEl) {
        statusEl.innerHTML = '<i class="bi bi-arrow-repeat spin"></i> Saving...';
        statusEl.classList.remove('text-success', 'text-muted');
        statusEl.classList.add('text-warning');
    }

    const oldVpt = canvas.viewportTransform.slice();
    const oldZoom = canvas.getZoom();
    const oldW = canvas.getWidth();
    const oldH = canvas.getHeight();

    canvas.setZoom(1);
    canvas.setViewportTransform([1, 0, 0, 1, 0, 0]);
    canvas.setWidth(originalWidth);
    canvas.setHeight(originalHeight);

    const objects = canvas.getObjects();
    const hideAll = () => objects.forEach(o => o.visible = false);

    hideAll();
    objects.forEach(o => {
        if (o.isMask || o.labelName || o.isBoundary || o.globalCompositeOperation === 'destination-out') o.visible = true;
    });

    canvas.renderAll();
    const combinedDataUrl = canvas.toDataURL({ format: 'png', multiplier: 1 });

    const datasetMasks = {};
    const datasetIds = [...new Set(objects.map(o => o.datasetId).filter(id => id))];

    datasetIds.forEach(dsId => {
        hideAll();
        const dsObjs = objects.filter(o => o.datasetId === dsId);
        const eraserObjs = objects.filter(o => o.globalCompositeOperation === 'destination-out');
        if (dsObjs.length > 0) {
            dsObjs.forEach(o => o.visible = true);
            eraserObjs.forEach(o => o.visible = true);
            const name = dsObjs[0].labelName || `Dataset_${dsId}`;
            canvas.renderAll();
            datasetMasks[name] = canvas.toDataURL({ format: 'png', multiplier: 1 });
        }
    });

    objects.forEach(o => o.visible = true);
    canvas.setWidth(oldW);
    canvas.setHeight(oldH);
    canvas.setZoom(oldZoom);
    canvas.setViewportTransform(oldVpt);
    canvas.renderAll();

    const metadata = getMetadata();

    try {
        const response = await fetch(`/api/workflow/task/${taskId}/save-mask/`, {
            method: "POST",
            headers: {
                "Content-Type": "application/json",
                "X-CSRFToken": getCSRFToken()
            },
            body: JSON.stringify({
                all_labels_mask: combinedDataUrl,
                separated_masks: datasetMasks,
                metadata: metadata
            })
        });

        const data = await response.json();

        if (data.status === 'success') {
            if (isAutoSave && statusEl) {
                statusEl.innerHTML = '<i class="bi bi-check-circle"></i> Saved';
                statusEl.classList.remove('text-warning', 'text-muted');
                statusEl.classList.add('text-success');
                setTimeout(() => {
                    statusEl.classList.remove('text-success');
                    statusEl.classList.add('text-muted');
                }, 1000);
            } else if (!isSubmitting) {
                Swal.fire({ icon: 'success', title: 'Saved', text: 'Draft Saved!', timer: 1500, showConfirmButton: false });
            }
        } else {
            throw new Error(data.message);
        }
    } catch (err) {
        console.error("Save error:", err);
        if (isAutoSave && statusEl) {
            statusEl.innerHTML = '<i class="bi bi-exclamation-circle"></i> Save Failed';
            statusEl.classList.remove('text-warning', 'text-muted');
            statusEl.classList.add('text-danger');
        } else {
            Swal.fire({ icon: 'error', title: 'Error', text: 'Error saving files!' });
        }
    }
}

function validateAnnotations() {
    const objects = canvas.getObjects();
    const errors = [];
    const configs = (typeof window.AVAILABLE_DATASETS !== 'undefined') ? window.AVAILABLE_DATASETS : [];

    // console.log("--- Starting Validation ---");

    objects.forEach((obj, idx) => {
        if (obj.type === 'image' && !obj.isMask) return;
        if (obj.globalCompositeOperation === 'destination-out') return;
        if (!obj.labelName) return;

        const config = configs.find(d =>
            String(d.id) === String(obj.datasetId) ||
            d.label_name === obj.labelName
        );

        if (!config) return;

        if (config.attributes && config.attributes.length > 0) {
            const objAttrs = obj.attributes || {};
            const missing = [];

            config.attributes.forEach(attrDef => {
                const attrName = attrDef.name;
                const val = objAttrs[attrName];

                if (!attrDef.is_mandatory) {
                    return;
                }

                if (val === undefined || val === null || String(val).trim() === "") {
                    missing.push(attrName);
                }
            });

            if (missing.length > 0) {
                errors.push(`Shape #${idx + 1} (${obj.labelName}) is missing: ${missing.join(', ')}`);
            }
        }
    });

    return errors;
}


async function submitTaskToAPI() {
    const taskId = window.SEGMENTATION_CONFIG.taskId;

    const validationErrors = validateAnnotations();
    if (validationErrors.length > 0) {
        let errorHtml = '<ul class="text-left" style="font-size: 14px; color: #dc3545;">';
        validationErrors.forEach(err => {
            errorHtml += `<li>${err}</li>`;
        });
        errorHtml += '</ul>';

        Swal.fire({
            icon: 'error',
            title: 'Missing Mandatory Attributes!',
            html: `<p>Please answer all required fields before submitting:</p>${errorHtml}`,
            confirmButtonColor: BRAND_COLOR
        });
        return;
    }

    const result = await Swal.fire({
        title: 'Submit Task?',
        text: "This will mark the task as SUBMITTED.",
        icon: 'question',
        showCancelButton: true,
        confirmButtonColor: BRAND_COLOR,
        cancelButtonColor: '#d33',
        confirmButtonText: 'Yes, Submit!'
    });

    if (!result.isConfirmed) return;

    try {
        await saveMask(true);

        const response = await fetch(`/api/workflow/task/${taskId}/submit/`, {
            method: "POST",
            headers: {
                "Content-Type": "application/json",
                "X-CSRFToken": getCSRFToken()
            }
        });

        const data = await response.json();

        if (data.status === 'success') {
            await Swal.fire({
                icon: 'success',
                title: 'Submitted',
                text: 'Task complete.',
                timer: 1000,
                showConfirmButton: false
            });

            notifyTaskSubmitted(taskId);

            if (data.next_task_token) {
                window.location.href = `/workflow/task/access/${data.next_task_token}/`;
            } else {
                const batchToken = window.SEGMENTATION_CONFIG.batchToken;
                window.location.href = `/workflow/batch/access/${batchToken}/`;
            }
        } else {
            throw new Error(data.message);
        }
    } catch (err) {
        Swal.fire('Error', err.message || 'Submission failed', 'error');
    }
}

function getCSRFToken() {
    return document.cookie.split("; ").find(row => row.startsWith("csrftoken"))?.split("=")[1];
}


window.submitTask = function () {

    const hasAnnotations = canvas.getObjects().some(obj => {
        return obj.labelName && obj.visible && obj.globalCompositeOperation !== 'destination-out';
    });

    if (!hasAnnotations) {

        if (window.CURRENT_LABEL) {
            Swal.fire({
                title: 'Forgot to Draw?',
                html: `You selected <b>${window.CURRENT_LABEL.name}</b> settings, but you didn't draw anything on the image.`,
                icon: 'warning',
                confirmButtonText: 'OK'
            });
            return;
        }

        Swal.fire({
            title: 'No Annotations',
            text: 'You have not drawn anything. Submit as Empty?',
            icon: 'warning',
            showCancelButton: true,
            confirmButtonText: 'OK',
            confirmButtonColor: BRAND_COLOR
        });
        return;
    }


    const errors = validateAnnotations();
    if (errors.length > 0) {
        Swal.fire({
            title: 'Missing Attributes',
            html: `<div class="text-left text-danger small"><ul>${errors.map(e => `<li>${e}</li>`).join('')}</ul></div>`,
            icon: 'error'
        });
        return;
    }

    submitTaskToAPI();
};


// SAM AI
async function runSAMMagic(arg1, arg2) {
    let x, y;

    if (arg1 && (arg1.clientX || arg1.type)) {
        const e = arg1;

        // console.log(`Screen Click: ${e.clientX}, ${e.clientY}`);

        if (typeof window.segmentationCanvas !== 'undefined') {
            window.segmentationCanvas.calcOffset();

            const pointer = window.segmentationCanvas.getPointer(e);
            x = Math.round(pointer.x);
            y = Math.round(pointer.y);
        } else {
            const targetCanvas = window.segmentationCanvas || window.canvas;
            if (targetCanvas) {
                targetCanvas.calcOffset();
                const pointer = targetCanvas.getPointer(e);
                x = Math.round(pointer.x);
                y = Math.round(pointer.y);
            } else {
                console.error("SAM Error: Canvas not found for coordinate extraction");
                return;
            }
        }
    } else if (typeof arg1 === 'number' && typeof arg2 === 'number') {
        x = arg1;
        y = arg2;
    } else {
        // console.error("SAM Error: Invalid arguments passed to runSAMMagic", arg1);
        return;
    }

    if (isNaN(x) || isNaN(y)) {
        console.error("SAM Error: Invalid coordinates calculated", x, y);
        Swal.fire('Error', 'Invalid click coordinates.', 'error');
        return;
    }

    const taskId = window.SEGMENTATION_CONFIG.taskId;
    const labelColor = window.CURRENT_LABEL.color;
    const labelName = window.CURRENT_LABEL.name;

    // Swal.fire({
    //     title: 'AI is thinking...',
    //     html: `Segmenting object at point (${x}, ${y})`,
    //     allowOutsideClick: false,
    //     didOpen: () => { Swal.showLoading(); }
    // });

    Swal.fire({
        title: '',
        html: `
            <style>
                /* This targets the spinner and makes it purple */
                .swal2-loader {
                    border-top-color: #4b49ac !important;
                    border-left-color: rgba(75, 73, 172, 0.2) !important;
                    border-right-color: rgba(75, 73, 172, 0.2) !important;
                    border-bottom-color: rgba(75, 73, 172, 0.2) !important;
                }
            </style>
        `,
        width: '120px',
        background: 'transparent',
        allowOutsideClick: false,
        showConfirmButton: false,
        didOpen: () => {
            Swal.showLoading();
        }
    });

    try {
        const response = await fetch(`/api/segmenter/task/${taskId}/pre-segment/?x=${x}&y=${y}`);
        const data = await response.json();

        if (data.status === 'success') {
            const base64Mask = `data:image/png;base64,${data.mask}`;

            fabric.Image.fromURL(base64Mask, function (img) {
                img.filters.push(new fabric.Image.filters.RemoveColor({
                    color: '#000000',
                    distance: 0.1
                }));
                img.filters.push(new fabric.Image.filters.BlendColor({
                    color: labelColor,
                    mode: 'tint',
                    alpha: 1
                }));
                img.applyFilters();

                const tempCanvas = img.toCanvasElement();
                const tempCtx = tempCanvas.getContext('2d');
                const imageData = tempCtx.getImageData(0, 0, tempCanvas.width, tempCanvas.height);
                const pixels = imageData.data;

                let minX = tempCanvas.width, minY = tempCanvas.height, maxX = 0, maxY = 0;
                let foundPixels = false;

                for (let y = 0; y < tempCanvas.height; y++) {
                    for (let x = 0; x < tempCanvas.width; x++) {
                        const alpha = pixels[(y * tempCanvas.width + x) * 4 + 3];
                        if (alpha > 0) {
                            if (x < minX) minX = x;
                            if (y < minY) minY = y;
                            if (x > maxX) maxX = x;
                            if (y > maxY) maxY = y;
                            foundPixels = true;
                        }
                    }
                }

                if (foundPixels) {
                    img.set({
                        left: minX,
                        top: minY,
                        width: maxX - minX,
                        height: maxY - minY,
                        srcX: minX,
                        srcY: minY,
                        cropX: minX,
                        cropY: minY
                    });
                }

                img.set({
                    selectable: true,
                    evented: true,
                    opacity: defaultMaskOpacity,
                    isMask: true,
                    labelName: labelName,
                    labelColor: labelColor,
                    datasetId: window.CURRENT_LABEL.id,
                    attributes: window.CURRENT_LABEL.attributes || {}
                });

                const targetCanvas = window.segmentationCanvas || window.canvas;
                targetCanvas.add(img);
                targetCanvas.setActiveObject(img);
                targetCanvas.renderAll();

                if (window.updateLayerList) window.updateLayerList();
                Swal.close();
                saveState();
                setTool(tools.SELECT);
                mergeLabelBrushStrokes(window.CURRENT_LABEL.id);
            });
        } else {
            throw new Error(data.message || "AI failed to find an object.");
        }
    } catch (error) {
        console.error("SAM Error:", error);
        Swal.fire('Error', error.message || 'AI Model failed.', 'error');
    }
}

/* ------------------------------
   REJECT TASK
------------------------------ */
window.rejectTask = function (reason) {
    const taskId = window.SEGMENTATION_CONFIG.taskId;

    // Swal.fire({
    //     title: 'Rejecting Task...',
    //     allowOutsideClick: false,
    //     didOpen: () => { Swal.showLoading(); }
    // });

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
            if (data.status === 'success') {
                Swal.fire({
                    icon: 'success',
                    title: 'Task Rejected',
                    text: 'The task has been sent back for rework.',
                    timer: 1500,
                    showConfirmButton: false
                }).then(() => {
                    notifyTaskSubmitted(taskId);
                    if (data.next_task_token) {
                        // console.log("Auto-Next: Redirecting to next task...");
                        window.location.href = `/workflow/task/access/${data.next_task_token}/`;
                    } else {
                        const batchToken = window.SEGMENTATION_CONFIG.batchToken;
                        window.location.href = `/workflow/batch/access/${batchToken}/`;
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



// Initialize toolbar state on page load
window.addEventListener('DOMContentLoaded', function () {
    if (typeof updateToolbarState === 'function') {
        updateToolbarState();
    }
    if (!window.CURRENT_LABEL) {
        setTimeout(() => {
            const labelPicker = document.querySelector('.dataset-list');
            if (labelPicker && labelPicker.children.length > 0) {
                // Swal.fire({
                //     title: 'Get Started',
                //     text: 'Select a label from the Label Picker to begin annotating',
                //     icon: 'info',
                //     confirmButtonColor: '#4b49ac',
                //     timer: 3000,
                //     showConfirmButton: false,
                //     toast: true,
                //     position: 'top-end'
                // });
            }
        }, 1000);
    }
});