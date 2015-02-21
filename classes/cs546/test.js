var canvas = document.getElementById("canvas");
var canvasWidth = canvas.width;
var canvasHeight = canvas.height;
var ctx = canvas.getContext("2d");
var canvasData = ctx.getImageData(0, 0, canvasWidth, canvasHeight);

function Point (x, y) {
		this.x = x;
		this.y = y;
}

function pointDistance (pt1, pt2) {
		var dx = pt2.x - pt1.x;
		var dy = pt2.y - pt1.y;
		return Math.sqrt(dx*dx + dy*dy);
}

function Color (r, g, b, a) {
		this.r = r;
		this.g = g;
		this.b = b;
		this.a = a;
}

function colorInterpolate (c1, c2, p, c) {
		var p2 = p < 0.0 ? 0.0 : p > 1.0 ? 1.0 : p;
		var p1 = 1.0 - p2;
		c.r = p1*c1.r + p2*c2.r;
		c.g = p1*c1.g + p2*c2.g;
		c.b = p1*c1.b + p2*c2.b;
		c.a = p1*c1.a + p2*c2.a;
}

function drawPixel (pt, col) {
		var index = (pt.x + pt.y * canvasWidth) * 4;
		canvasData.data[index + 0] = col.r;
    canvasData.data[index + 1] = col.g;
    canvasData.data[index + 2] = col.b;
    canvasData.data[index + 3] = col.a;
}

// function drawPixel (x, y, r, g, b, a) {
//     var index = (x + y * canvasWidth) * 4;

//     canvasData.data[index + 0] = r;
//     canvasData.data[index + 1] = g;
//     canvasData.data[index + 2] = b;
//     canvasData.data[index + 3] = a;
// }

function Line (pt1, pt2, col1, col2) {
		this.pt1 = pt1;
		this.pt2 = pt2;
		this.col1 = col1;
		this.col2 = col2;
}

function drawLine (line) {
		var pt1 = line.pt1;
		var pt2 = line.pt2;
		var col1 = line.col1;
		var col2 = line.col2;

		var dx = Math.abs(pt2.x - pt1.x);
    var dy = Math.abs(pt2.y - pt1.y);
		var sx = (pt1.x < pt2.x) ? 1 : -1;
    var sy = (pt1.y < pt2.y) ? 1 : -1;
		var err = dx - dy;
		var dist = pointDistance(pt1, pt2);
		
		var point = new Point(pt1.x, pt1.y);
		var color = new Color(col1.r, col1.g, col1.b, col1.a);

		while (true) {
				var p = pointDistance(pt1, point) / dist;
				colorInterpolate(col1, col2, p, color);
				drawPixel(point, color);

				if ((point.x == pt2.x) && (point.y == pt2.y)) break;
				var e2 = 2 * err;
				if (e2 >-dy) { err -= dy; point.x += sx; }
				if (e2 < dx) { err += dx; point.y += sy; }
		}
}

// function drawLine (x1, y1, x2, y2, r, g, b, a) {
// 		var dx = Math.abs(x2-x1);
//     var dy = Math.abs(y2-y1);
//     var sx = (x1 < x2) ? 1 : -1;
//     var sy = (y1 < y2) ? 1 : -1;
//     var err = dx-dy;

//     while (true) {
//         drawPixel(x1, y1, r, g, b, a);

//         if ((x1==x2) && (y1==y2)) break;
//         var e2 = 2*err;
//         if (e2 >-dy){ err -= dy; x1  += sx; }
//         if (e2 < dx){ err += dx; y1  += sy; }
//     }
// }

function updateCanvas(data) {
    ctx.putImageData(data, 0, 0);
}

function alphaComposition(colorA, colorB, c) {
		var d = Math.floor(c * a);
		var r = Math.floor((colorA.a * colorA.r) / 255.0 - (colorA.a - 255.0) * d * colorB.r / 65025.0);
		var g = Math.floor((colorA.a * colorA.g) / 255.0 - (colorA.a - 255.0) * d * colorB.g / 65025.0);
		var b = Math.floor((colorA.a * colorA.b) / 255.0 - (colorA.a - 255.0) * d * colorB.b / 65025.0);
		var a = Math.floor(colorA.a + d - colorA.a * d / 255.0);
		return new Color(r, g, b, a);
}

// function alphaComposition(cA, aA, cB, aB) {
//     return Math.floor((aA * cA) / 255.0 - (aA - 255) * aB * cB / 65025.0);
// }

function drawPixel(point, c, colorB) {
		var index = (x + y * canvasWidth) * 4;
		
		var r = canvasData.data[index + 0];
    var g = canvasData.data[index + 1];
    var b = canvasData.data[index + 2];
    var a = canvasData.data[index + 3];

		var colorA = new Color(r, g, b, a);
		var pixelc = alphaComposition(colorA, colorB, c);
		
		canvasData.data[index + 0] = pixelc.r;
		canvasData.data[index + 1] = pixelc.g;
		canvasData.data[index + 2] = pixelc.b;
		canvasData.data[index + 3] = pixelc.a;
}

function plot(x, y, c, r, g, b, a) {
    var index = (x + y * canvasWidth) * 4;

    var rA = canvasData.data[index + 0];
    var gA = canvasData.data[index + 1];
    var bA = canvasData.data[index + 2];
    var aA = canvasData.data[index + 3];

    var rB = r;
    var gB = g;
    var bB = b;
    var aB = Math.floor(c * a);
    
    canvasData.data[index + 0] = alphaComposition(rA, aA, rB, aB);
    canvasData.data[index + 1] = alphaComposition(gA, aA, gB, aB);
    canvasData.data[index + 2] = alphaComposition(bA, aA, bB, aB);
    canvasData.data[index + 3] = Math.floor(aA + aB - aA * aB / 255.0);
}

function ipart(x) {
    return Math.floor(x);
}

function round(x) {
    return Math.round(x);
}

function fpart(x) {
    return (x < 0) ? (1 - (x - Math.floor(x))) : (x - Math.floor(x));
}

function rfpart(x) {
    return 1 - fpart(x);
}

function drawLineAA(x0, y0, x1, y1, r, g, b, a) {
    var steep = Boolean(Math.abs(y1 - y0) > Math.abs(x1 - x0));
    
    if (steep) {
        y0 = [x0, x0 = y0][0];
        y1 = [x1, x1 = y1][0];
    }
    if (x0 > x1) {
        x1 = [x0, x0 = x1][0];
        y1 = [y0, y0 = y1][0];
    }

    var dx = x1 - x0;
    var dy = y1 - y0;
    var gradient = dy / dx;

    // handle first endpoint
    var xend = Math.round(x0);
    var yend = y0 + gradient * (xend - x0);
    var xgap = rfpart(x0 + 0.5);
    var xpxl1 = xend; // this will be used in the main loop
    var ypxl1 = ipart(yend);
    if (steep) {
        plot(ypxl1    , xpxl1, rfpart(yend) * xgap, r, g, b, a);
        plot(ypxl1 + 1, xpxl1,  fpart(yend) * xgap, r, g, b, a);
    } else {
        plot(xpxl1, ypxl1    , rfpart(yend) * xgap, r, g, b, a);
        plot(xpxl1, ypxl1 + 1,  fpart(yend) * xgap, r, g, b, a);
    }
    var intery = yend + gradient;

    // handle second endpoint
    xend = Math.round(x1);
    yend = y1 + gradient * (xend - x1);
    xgap = fpart(x1 + 0.5);
    var xpxl2 = xend; //this will be used in the main loop
    var ypxl2 = ipart(yend);
    if (steep) {
        plot(ypxl2  , xpxl2, rfpart(yend) * xgap, r, g, b, a);
        plot(ypxl2+1, xpxl2,  fpart(yend) * xgap, r, g, b, a);
    } else {
        plot(xpxl2, ypxl2,  rfpart(yend) * xgap, r, g, b, a);
        plot(xpxl2, ypxl2+1, fpart(yend) * xgap, r, g, b, a);
    }

    // main loop
    for (x = xpxl1+1; x <= xpxl2; x++) {
        if (steep) {
            plot(ipart(intery)  , x, rfpart(intery), r, g, b, a);
            plot(ipart(intery)+1, x,  fpart(intery), r, g, b, a);
        } else {
            plot(x, ipart(intery)  , rfpart(intery), r, g, b, a);
            plot(x, ipart(intery)+1,  fpart(intery), r, g, b, a);
        }
        intery = intery + gradient;
    }
}

var lineCount = 100;
var xArray = [];
var yArray = [];
for (i = 0; i < lineCount; i++) {
    xArray[i] = Math.floor(canvasWidth * Math.random());
    yArray[i] = Math.floor(canvasHeight * Math.random());
}

for (i = 0; i < lineCount-1; i++) {
    drawLineAA(xArray[i], yArray[i], xArray[i+1], yArray[i+1], 0, 0, 0, Math.floor(255 * (i / lineCount)));
}
updateCanvas(canvasData);

function resetCanvas() {
    for (var x = 0; x < canvas.width; x++) {
        for (var y = 0; y < canvas.height; y++) {
            drawPixel(x, y, 255, 255, 255, 0);
        }
    }
    updateCanvas(canvasData);
}

var antialiasing = false;

var mainloop = function() {
    resetCanvas();
    if (antialiasing) {
        for (i = 0; i < lineCount-1; i++) {
            drawLineAA(xArray[i], yArray[i], xArray[i+1], yArray[i+1], 0, 0, 0, Math.floor(255 * (i / lineCount)));
        }
        updateCanvas(canvasData);
        antialiasing = false;
    } else {
        for (i = 0; i < lineCount-1; i++) {
            drawLine(xArray[i], yArray[i], xArray[i+1], yArray[i+1], 0, 0, 0, Math.floor(255 * (i / lineCount)));
        }
        updateCanvas(canvasData);
        antialiasing = true;
    }
};

setInterval(mainloop, 3000);
