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
				colorInterpolate(col1, col2, p, color);
				drawPixel(point, color);

				if ((point.x == pt2.x) && (point.y == pt2.y)) break;
				var e2 = 2 * err;
				if (e2 >-dy) { err -= dy; point.x += sx; }
				if (e2 < dx) { err += dx; point.y += sy; }
		}
}

function updateCanvas (data) {
    ctx.putImageData(data, 0, 0);
}

function drawSomeStuff () {
		var color1 = new Color(255, 0, 0, 255);
		var color2 = new Color(0, 0, 255, 255);
		for (i = 0; i < canvasHeight; i+=5) {
				var pt1 = new Point(0, i);
				var pt2 = new Point(canvasWidth-1-i, 0);
				var line = new Line(pt1, pt2, color1, color2);
				drawLine(line);
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
