var canvas = document.getElementById("canvas");
var canvasWidth = canvas.width;
var canvasHeight = canvas.height;
var ctx = canvas.getContext("2d");
var canvasData = ctx.getImageData(0, 0, canvasWidth, canvasHeight);

function Point (x, y) {
		this.x = x;
		this.y = y;
}

function Color (r, g, b, a) {
		this.r = r;
		this.g = g;
		this.b = b;
		this.a = a;
}

function Line (pt1, pt2, col1, col2) {
		this.pt1 = pt1;
		this.pt2 = pt2;
		this.col1 = col1;
		this.col2 = col2;
}

var debug = {
		print : function (msg) {
				document.write(msg);
		},
		printPoint : function (pt) {
				this.print("(" + pt.x + ", " + pt.y + ")");
		},
		printColor : function (color) {
				this.print("(");
				this.print(color.r + ", ");
				this.print(color.g + ", ");
				this.print(color.b + ", ");
				this.print(color.a + ")");
		}
};

function pointDistance (pt1, pt2) {
		var dx = pt2.x - pt1.x;
		var dy = pt2.y - pt1.y;
		return Math.sqrt(dx*dx + dy*dy);
}

function colorInterpolate (c1, c2, p, c) {
		var p2 = p < 0.0 ? 0.0 : p > 1.0 ? 1.0 : p;
		var p1 = 1.0 - p2;
		c.r = Math.floor(p1*c1.r + p2*c2.r);
		c.g = Math.floor(p1*c1.g + p2*c2.g);
		c.b = Math.floor(p1*c1.b + p2*c2.b);
		c.a = Math.floor(p1*c1.a + p2*c2.a);
		return c;
}

function drawPixel (pt, col) {
		var index = (pt.x + pt.y * canvasWidth) * 4;
		canvasData.data[index + 0] = col.r;
    canvasData.data[index + 1] = col.g;
    canvasData.data[index + 2] = col.b;
    canvasData.data[index + 3] = col.a;
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
				color = colorInterpolate(col1, col2, p, color);
				drawPixel(point, color);

				if ((point.x == pt2.x) && (point.y == pt2.y)) break;
				var e2 = 2 * err;
				if (e2 >-dy) { err -= dy; point.x += sx; }
				if (e2 < dx) { err += dx; point.y += sy; }
		}
}

function alphaComposition(cA, cB, c) {
		var d = Math.floor(c * cB.a);
		var r = Math.floor((cA.a*cA.r) / 255.0 - (cA.a-255.0) * d * cB.r / 65025.0);
		var g = Math.floor((cA.a*cA.g) / 255.0 - (cA.a-255.0) * d * cB.g / 65025.0);
		var b = Math.floor((cA.a*cA.b) / 255.0 - (cA.a-255.0) * d * cB.b / 65025.0);
		var a = Math.floor(cA.a + d - cA.a * d / 255.0);
		return new Color(r, g, b, a);
}

function drawPixelAA (point, c, colorB) {
		var index = (point.x + point.y * canvasWidth) * 4;
		
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

function drawLineAA (line) {
		var x0 = line.pt1.x, y0 = line.pt1.y;
		var x1 = line.pt2.x, y1 = line.pt2.y;
		var r0 = line.col1.r, g0 = line.col1.g, b0 = line.col1.b, a0 = line.col1.a;
		var r1 = line.col2.r, g1 = line.col2.g, b1 = line.col2.b, a1 = line.col2.a;

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
				drawPixelAA(new Point(ypxl1,   xpxl1), rfpart(yend) * xgap, line.col1);
				drawPixelAA(new Point(ypxl1+1, xpxl1),  fpart(yend) * xgap, line.col1);
    } else {
				drawPixelAA(new Point(xpxl1, ypxl1),   rfpart(yend) * xgap, line.col1);
				drawPixelAA(new Point(xpxl1, ypxl1+1),  fpart(yend) * xgap, line.col1);
    }
    var intery = yend + gradient;

    // handle second endpoint
    xend = Math.round(x1);
    yend = y1 + gradient * (xend - x1);
    xgap = fpart(x1 + 0.5);
    var xpxl2 = xend; //this will be used in the main loop
    var ypxl2 = ipart(yend);
    if (steep) {
				drawPixelAA(new Point(ypxl2,   xpxl2), rfpart(yend) * xgap, line.col2);
				drawPixelAA(new Point(ypxl2+1, xpxl2),  fpart(yend) * xgap, line.col2);
    } else {
				drawPixelAA(new Point(xpxl2, ypxl2),  rfpart(yend) * xgap, line.col2);
				drawPixelAA(new Point(xpxl2, ypxl2+1), fpart(yend) * xgap, line.col2);
    }

    // main loop
    for (x = xpxl1+1; x <= xpxl2; x++) {
				var p1, p2, point, color, dist, p;
        if (steep) {
						p1 = new Point(ipart(intery), x);
						p2 = new Point(ipart(intery)+1, x);
						point = new Point((p1.x+p2.x)/2.0, (p1.y+p2.y)/2.0);
						color = new Color(255, 255, 255, 255);
						dist = pointDistance(line.pt1, point);
						
						p = pointDistance(pt1, point) / dist;
						color = colorInterpolate(line.col1, line.col2, p, color);

						debug.print("<br>" + p + ", ");
						debug.printColor(color);

						drawPixelAA(p1, rfpart(intery), color);
						drawPixelAA(p2,  fpart(intery), color);
        } else {
						p1 = new Point(x, ipart(intery));
						p2 = new Point(x, ipart(intery)+1);
						point = new Point((p1.x+p2.x)/2.0, (p1.y+p2.y)/2.0);
						color = new Color(255, 255, 255, 255);
						dist = pointDistance(line.pt1, point);
						
						p = pointDistance(pt1, point) / dist;
						color = colorInterpolate(line.col1, line.col2, p, color);

						debug.print("<br>" + p + ", ");
						debug.printColor(color);

						drawPixelAA(p1, rfpart(intery), color);
						drawPixelAA(p2,  fpart(intery), color);
        }
        intery = intery + gradient;
    }
}

function updateCanvas (data) {
    ctx.putImageData(data, 0, 0);
}

function drawSomeStuff () {
		var color1 = new Color(255, 0, 0, 255);
		var color2 = new Color(0, 0, 255, 255);
		for (i = 0; i < canvasHeight; i+=500) {
				var pt1 = new Point(0, i);
				var pt2 = new Point(canvasWidth-1-i, 0);
				var line = new Line(pt1, pt2, color1, color2);
				drawLineAA(line);
		}
}

debug.print("<br>");

var pt1 = new Point(1, 1);
var col1 = new Color(255, 0, 0, 255);

debug.printPoint(pt1);
debug.print(", ");
debug.printColor(col1);

drawSomeStuff();

updateCanvas(canvasData);
