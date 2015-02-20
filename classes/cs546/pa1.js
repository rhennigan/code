var PRIMITIVES = {
  LINE: 'line',
  CIRCLE: 'circle',
  ELLIPSE: 'ellipse',
  RECTANGLE: 'rectangle',
  POLYGON: 'polygon',
  POLYLINE: 'polyline'
}

function Point(x, y) {
  this.x = x || 0;
  this.y = y || 0;
}

function pointDistance(pt1, pt2) {
  var dx = pt2.x - pt1.x;
  var dy = pt2.y - pt1.y;
  return Math.sqrt(dx * dx + dy * dy);
}

function Color(r, g, b, a) {
  this.r = r || 0;
  this.g = g || 0;
  this.b = b || 0;
  this.a = a || 0;
}

function Pixel(point, color, c) {
  this.point = point || new Point();
  this.color = color || new Color();
  this.c = c || 0;
}

Pixel.prototype.moveTo = function(x, y) {
  this.point.x = x;
  this.point.y = y;
  return this;
};

Pixel.prototype.move = function(x, y) {
  this.point.x += x;
  this.point.y += y;
  return this;
};

Pixel.prototype.drawNAA = function(cdata, width) {
  var index = (this.point.x + this.point.y * width) * 4;
  cdata.data[index + 0] = this.color.r;
  cdata.data[index + 1] = this.color.g;
  cdata.data[index + 2] = this.color.b;
  cdata.data[index + 3] = this.color.a;
};

function alphaComposition(cA, cB, c) {
  var d = Math.floor(c * cB.a);
  var r = Math.floor((cA.a * cA.r) / 255.0 - (cA.a - 255.0) * d * cB.r / 65025.0);
  var g = Math.floor((cA.a * cA.g) / 255.0 - (cA.a - 255.0) * d * cB.g / 65025.0);
  var b = Math.floor((cA.a * cA.b) / 255.0 - (cA.a - 255.0) * d * cB.b / 65025.0);
  var a = Math.floor(cA.a + d - cA.a * d / 255.0);
  return new Color(r, g, b, a);
}

Pixel.prototype.drawAA = function(cdata, width) {
  var index = (this.point.x + this.point.y * width) * 4;
  var colorB = this.color;
  var c = this.c;

  var r = cdata.data[index + 0];
  var g = cdata.data[index + 1];
  var b = cdata.data[index + 2];
  var a = cdata.data[index + 3];

  var colorA = new Color(r, g, b, a);
  var pixelc = alphaComposition(colorA, colorB, c);

  cdata.data[index + 0] = pixelc.r;
  cdata.data[index + 1] = pixelc.g;
  cdata.data[index + 2] = pixelc.b;
  cdata.data[index + 3] = pixelc.a;
};

Pixel.prototype.draw = function(cdata, width) {
  if (antialiasing) {
    this.drawAA(cdata, width);
  } else {
    this.drawNAA(cdata, width);
  }
};

function Line(pt1, pt2, col1, col2) {
  this.pt1 = pt1 || new Point();
  this.pt2 = pt2 || new Point();
  this.col1 = col1 || new Color();
  this.col2 = col2 || new Color();
  this.type = PRIMITIVES.LINE;
}

function colorInterpolate(c1, c2, p) {
  var c = new Color();
  var p2 = p < 0.0 ? 0.0 : p > 1.0 ? 1.0 : p;
  var p1 = 1.0 - p2;
  c.r = Math.floor(p1 * c1.r + p2 * c2.r);
  c.g = Math.floor(p1 * c1.g + p2 * c2.g);
  c.b = Math.floor(p1 * c1.b + p2 * c2.b);
  c.a = Math.floor(p1 * c1.a + p2 * c2.a);
  return c;
}

Line.prototype.drawNAA = function(cdata, width) {
  var pt1 = this.pt1;
  var pt2 = this.pt2;
  var col1 = this.col1;
  var col2 = this.col2;

  var dx = Math.abs(pt2.x - pt1.x);
  var dy = Math.abs(pt2.y - pt1.y);
  var sx = (pt1.x < pt2.x) ? 1 : -1;
  var sy = (pt1.y < pt2.y) ? 1 : -1;
  var err = dx - dy;
  var dist = pointDistance(pt1, pt2);

  var pixel = new Pixel(new Point(pt1.x, pt1.y),
    new Color(col1.r, col1.g, col1.b, col1.a));

  while (true) {
    var p = pointDistance(pt1, pixel.point) / dist;
    pixel.color = colorInterpolate(col1, col2, p);
    pixel.draw(cdata, width);

    if ((pixel.point.x == pt2.x) && (pixel.point.y == pt2.y)) break;
    var e2 = 2 * err;
    if (e2 > -dy) {
      err -= dy;
      pixel.point.x += sx;
    }
    if (e2 < dx) {
      err += dx;
      pixel.point.y += sy;
    }
  }
};

function ipart(x) {
  return Math.floor(x);
}

function round(x) {
  return Math.round(x);
}

function fpart(x) {
  return x < 0 ? 1 - (x - Math.floor(x)) : x - Math.floor(x);
}

function rfpart(x) {
  return 1 - fpart(x);
}

Line.prototype.drawAA = function(cdata, width) {
  var line = this;
  var x0 = line.pt1.x,
    y0 = line.pt1.y;
  var x1 = line.pt2.x,
    y1 = line.pt2.y;
  var r0 = line.col1.r,
    g0 = line.col1.g,
    b0 = line.col1.b,
    a0 = line.col1.a;
  var r1 = line.col2.r,
    g1 = line.col2.g,
    b1 = line.col2.b,
    a1 = line.col2.a;

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

  var pixel = new Pixel(new Point(), new Color());

  var drawPixelAA = function(pt, c, col) {
    pixel.moveTo(pt.x, pt.y);
    pixel.c = c;
    pixel.color = col;
    pixel.draw(cdata, width);
  };

  if (steep) {
    drawPixelAA(new Point(ypxl1, xpxl1), rfpart(yend) * xgap, line.col1);
    drawPixelAA(new Point(ypxl1 + 1, xpxl1), fpart(yend) * xgap, line.col1);
  } else {
    drawPixelAA(new Point(xpxl1, ypxl1), rfpart(yend) * xgap, line.col1);
    drawPixelAA(new Point(xpxl1, ypxl1 + 1), fpart(yend) * xgap, line.col1);
  }
  var intery = yend + gradient;

  // handle second endpoint
  xend = Math.round(x1);
  yend = y1 + gradient * (xend - x1);
  xgap = fpart(x1 + 0.5);
  var xpxl2 = xend; //this will be used in the main loop
  var ypxl2 = ipart(yend);
  if (steep) {
    drawPixelAA(new Point(ypxl2, xpxl2), rfpart(yend) * xgap, line.col2);
    drawPixelAA(new Point(ypxl2 + 1, xpxl2), fpart(yend) * xgap, line.col2);
  } else {
    drawPixelAA(new Point(xpxl2, ypxl2), rfpart(yend) * xgap, line.col2);
    drawPixelAA(new Point(xpxl2, ypxl2 + 1), fpart(yend) * xgap, line.col2);
  }

  // main loop
  for (x = xpxl1 + 1; x <= xpxl2; x++) {
    var p1, p2, point, color, dist, p;
    if (steep) {
      p1 = new Point(ipart(intery), x);
      p2 = new Point(ipart(intery) + 1, x);
      point = new Point((p1.x + p2.x) / 2.0, (p1.y + p2.y) / 2.0);
      color = new Color(255, 255, 255, 255);
      dist = pointDistance(line.pt1, line.pt2);

      p = pointDistance(line.pt1, point) / dist;
      color = colorInterpolate(line.col1, line.col2, p, color);

      drawPixelAA(p1, rfpart(intery), color);
      drawPixelAA(p2, fpart(intery), color);
    } else {
      p1 = new Point(x, ipart(intery));
      p2 = new Point(x, ipart(intery) + 1);
      point = new Point((p1.x + p2.x) / 2.0, (p1.y + p2.y) / 2.0);
      color = new Color(255, 255, 255, 255);
      dist = pointDistance(line.pt1, line.pt2);

      p = pointDistance(line.pt1, point) / dist;
      color = colorInterpolate(line.col1, line.col2, p, color);

      drawPixelAA(p1, rfpart(intery), color);
      drawPixelAA(p2, fpart(intery), color);
    }
    intery = intery + gradient;
  }
};

Line.prototype.draw = function(cdata, width) {
  if (antialiasing) {
    this.drawAA(cdata, width);
  } else {
    this.drawNAA(cdata, width);
  }
};

function Circle(center, radius, color) {
  this.center = center || new Point();
  this.radius = radius || 0;
  this.color = color || new Color();
  this.type = 'circle';
}

Circle.prototype.draw = function(cdata, width) {
  var x0 = Math.round(this.center.x);
  var y0 = Math.round(this.center.y);
  var radius = Math.round(this.radius);

  var x = radius;
  var y = 0;
  var radiusError = 1 - x;

  var pixel = new Pixel(new Point(), this.color);

  while (x >= y) {
    pixel.moveTo(x + x0, y + y0).draw(cdata, width);
    pixel.moveTo(x + x0, y + y0).draw(cdata, width);
    pixel.moveTo(y + x0, x + y0).draw(cdata, width);
    pixel.moveTo(-x + x0, y + y0).draw(cdata, width);
    pixel.moveTo(-y + x0, x + y0).draw(cdata, width);
    pixel.moveTo(-x + x0, -y + y0).draw(cdata, width);
    pixel.moveTo(-y + x0, -x + y0).draw(cdata, width);
    pixel.moveTo(x + x0, -y + y0).draw(cdata, width);
    pixel.moveTo(y + x0, -x + y0).draw(cdata, width);

    y++;

    if (radiusError < 0) {
      radiusError += 2 * y + 1;
    } else {
      x--;
      radiusError += 2 * (y - x) + 1;
    }
  }
};

function Ellipse(center, a, b, color) {
  this.center = center || new Point();
  this.a = a || 0;
  this.b = b || 0;
  this.color = color || new Color();
  this.type = 'ellipse';
}

Ellipse.prototype.draw = function(cdata, width) {
  var pixel = new Pixel(new Point(), this.color);

  var ellipsePlotPoints = function(xc, yc, x, y) {
    pixel.moveTo(xc + x, yc + y).draw(cdata, width);
    pixel.moveTo(xc - x, yc + y).draw(cdata, width);
    pixel.moveTo(xc + x, yc - y).draw(cdata, width);
    pixel.moveTo(xc - x, yc - y).draw(cdata, width);
  };

  var xc = this.center.x;
  var yc = this.center.y;
  var a = this.a;
  var b = this.b;

  var a2 = a * a;
  var b2 = b * b;
  var twoa2 = 2 * a2;
  var twob2 = 2 * b2;
  var p;
  var x = 0;
  var y = b;
  var px = 0;
  var py = twoa2 * y;

  /* Plot the initial point in each quadrant. */
  ellipsePlotPoints(xc, yc, x, y);

  /* Region 1 */
  p = Math.round(b2 - (a2 * b) + (0.25 * a2));
  while (px < py) {
    x++;
    px += twob2;
    if (p < 0)
      p += b2 + px;
    else {
      y--;
      py -= twoa2;
      p += b2 + px - py;
    }
    ellipsePlotPoints(xc, yc, x, y);
  }

  /* Region 2 */
  p = Math.round(b2 * (x + 0.5) * (x + 0.5) + a2 * (y - 1) * (y - 1) - a2 * b2);
  while (y > 0) {
    y--;
    py -= twoa2;
    if (p > 0)
      p += a2 - py;
    else {
      x++;
      px += twob2;
      p += a2 - py + px;
    }
    ellipsePlotPoints(xc, yc, x, y);
  }
};

function Rectangle(pt1, pt2, color) {
  this.pt1 = pt1 || new Point();
  this.pt2 = pt2 || new Point();
  this.color = color || new Color();
  this.type = 'rectangle';
}

Rectangle.prototype.draw = function(cdata, width) {
  var topLeft = new Point(this.pt1.x, this.pt1.y);
  var topRight = new Point(this.pt2.x, this.pt1.y);
  var bottomLeft = new Point(this.pt1.x, this.pt2.y);
  var bottomRight = new Point(this.pt2.x, this.pt2.y);

  var c = this.color;

  var topLine = new Line(topLeft, topRight, c, c);
  var bottomLine = new Line(bottomLeft, bottomRight, c, c);
  var leftLine = new Line(topLeft, bottomLeft, c, c);
  var rightLine = new Line(topRight, bottomRight, c, c);

  topLine.draw(cdata, width);
  bottomLine.draw(cdata, width);
  leftLine.draw(cdata, width);
  rightLine.draw(cdata, width);
};

function Polygon(vertices, color) {
  this.vertices = vertices || new List();
  this.color = color || new Color();
  this.type = 'polygon';
}

Polygon.prototype.draw = function(cdata, width) {
  var rem = this.vertices;
  var line = new Line();
  line.col1 = this.color;
  line.col2 = this.color;

  while (!rem.isEmpty()) {
    var vert1 = rem.head;
    var vert2 = rem.tail.isEmpty() ? this.vertices.head : rem.tail.head;

    line.pt1 = vert1;
    line.pt2 = vert2;
    // console.log(line);
    line.draw(cdata, width);
    rem = rem.tail;
  }
};

function Polyline(vertices, color) {
  this.vertices = vertices || new List();
  this.color = color || new Color();
  this.type = 'polyline';
}

Polyline.prototype.draw = function(cdata, width) {
  var rem = this.vertices;
  var line = new Line();
  line.col1 = this.color;
  line.col2 = this.color;

  while (!rem.isEmpty()) {
    var vert1 = rem.head;
    var vert2 = rem.tail.isEmpty() ? rem.head : rem.tail.head;

    line.pt1 = vert1;
    line.pt2 = vert2;
    console.log(line);
    line.draw(cdata, width);
    rem = rem.tail;
  }
};

var antialiasing = false;
var drawMode = 'line';



function changeMode(mode) {
  $("#" + drawMode).css("background-color", "#cccccc");
  $("#" + mode).css("background-color", "#888888");
  drawMode = mode;
  console.log(drawMode);
  var p;
  if (mode == 'polygon') {
    p = new Polygon(new List(), new Color(0, 0, 0, 255));
    canvasState.shapes.push(p);
  } else if (mode == 'polyline') {
    p = new Polyline(new List(), new Color(0, 0, 0, 255));
    canvasState.shapes.push(p);
  }
}

function CanvasState(canvas) {
  this.canvas = canvas;
  this.width = canvas.width;
  this.height = canvas.height;
  this.ctx = canvas.getContext("2d");
  this.data = this.ctx.getImageData(0, 0, canvas.width, canvas.height);

  var stylePaddingLeft, stylePaddingTop, styleBorderLeft, styleBorderTop;
  if (document.defaultView && document.defaultView.getComputedStyle) {
    var gcs = document.defaultView.getComputedStyle(canvas, null);
    this.stylePaddingLeft = parseInt(gcs['paddingLeft'], 10) || 0;
    this.stylePaddingTop = parseInt(gcs['paddingTop'], 10) || 0;
    this.styleBorderLeft = parseInt(gcs['borderLeftWidth'], 10) || 0;
    this.styleBorderTop = parseInt(gcs['borderTopWidth'], 10) || 0;
  }

  var html = document.body.parentNode;
  this.htmlTop = html.offsetTop;
  this.htmlLeft = html.offsetLeft;

  this.antialiasing = false;
  this.drawMode = 'line';
  this.valid = false;
  this.shapes = [];
  this.dragging = false;

  var myState = this;

  canvas.addEventListener('selectstart', function(e) {
    e.preventDefault();
    return false;
  }, false);

  canvas.addEventListener('mousedown', function(e) {
    var mouse = myState.getMouse(e);
    var shape;
    if (drawMode == 'polygon' || drawMode == 'polyline') {
      var n = myState.shapes.length - 1;
      if (n == -1) {
        var p;
        if (drawMode == 'polygon') {
          p = new Polygon(new List(), new Color(0, 0, 0, 255));
          canvasState.shapes.push(p);
        } else if (drawMode == 'polyline') {
          p = new Polyline(new List(), new Color(0, 0, 0, 255));
          canvasState.shapes.push(p);
        }
      }
      shape = myState.shapes[n];
      var pt = new Point(mouse.x, mouse.y);
      shape.vertices = List.cons(pt)(shape.vertices);
    } else {
      shape = makeShape(mouse);
      myState.shapes.push(shape);
    }
    // console.log(typeof shape);
    myState.dragging = true;
    myState.valid = false;
    return;
  }, true);

  canvas.addEventListener('mousemove', function(e) {
    if (myState.dragging) {
      var n = myState.shapes.length - 1;
      var mouse = myState.getMouse(e);
      dragShape(mouse, myState.shapes[n]);
      // var mx = mouse.x;
      // var my = mouse.y;
      // myState.shapes[n].pt2.x = mx;
      // myState.shapes[n].pt2.y = my;
      myState.valid = false;
    }
  }, true);

  canvas.addEventListener('mouseup', function(e) {
    myState.dragging = false;
  }, true);

  canvas.addEventListener('dblclick', function(e) {
    var p;
    if (drawMode == 'polygon') {
      p = new Polygon(new List(), new Color(0, 0, 0, 255));
      canvasState.shapes.push(p);
    } else if (drawMode == 'polyline') {
      p = new Polyline(new List(), new Color(0, 0, 0, 255));
      canvasState.shapes.push(p);
    }
  }, true);

  this.interval = 30;

  setInterval(function() {
    myState.draw();
  }, myState.interval);
}

function makeShape(mouse) {
  var pt1, pt2, color, center;
  color = new Color(0, 0, 0, 255);

  switch (drawMode) {
    case 'line':
      pt1 = new Point(mouse.x, mouse.y);
      pt2 = new Point(mouse.x, mouse.y);
      var line = new Line(pt1, pt2, color, color);
      return line;

    case 'circle':
      center = new Point(mouse.x, mouse.y);
      var circle = new Circle(center, 1, color);
      return circle;

    case 'ellipse':
      center = new Point(mouse.x, mouse.y);
      var ellipse = new Ellipse(center, 1, 1, color);
      return ellipse;

    case 'rectangle':
      pt1 = new Point(mouse.x, mouse.y);
      pt2 = new Point(mouse.x, mouse.y);
      var rectangle = new Rectangle(pt1, pt2, color);
      return rectangle;

    default:
      alert('fixme');
      return null;
  }
}

function dragShape(mouse, shape) {
  switch (drawMode) {
    case 'line':
    case 'rectangle':
      shape.pt2.x = mouse.x;
      shape.pt2.y = mouse.y;
      break;

    case 'circle':
      shape.radius = pointDistance(shape.center, new Point(mouse.x, mouse.y));
      break;

    case 'ellipse':
      shape.a = Math.abs(mouse.x - shape.center.x);
      shape.b = Math.abs(mouse.y - shape.center.y);
      break;

    case 'polygon':
    case 'polyline':
      shape.vertices.head.x = mouse.x;
      shape.vertices.head.y = mouse.y;
      break;

    default:
      alert('fixme');
      return null;
  }
};

CanvasState.prototype.clear = function() {
  this.ctx.clearRect(0, 0, this.width, this.height);
  this.data = this.ctx.getImageData(0, 0, this.width, this.height);
  this.ctx.putImageData(this.data, 0, 0);
};

CanvasState.prototype.draw = function() {
  if (!this.valid) {
    var ctx = this.ctx;
    var shapes = this.shapes;
    var N = shapes.length;

    this.clear();

    for (var i = 0; i < N; i++) {
      var shape = shapes[i];
      shape.draw(this.data, this.width);
      ctx.putImageData(this.data, 0, 0);
    }

    this.valid = true;
  }
};

CanvasState.prototype.getMouse = function(e) {
  var element = this.canvas,
    offsetX = 0,
    offsetY = 0,
    mx, my;

  if (element.offsetParent !== undefined) {
    do {
      offsetX += element.offsetLeft;
      offsetY += element.offsetTop;
    } while ((element = element.offsetParent));
  }

  offsetX += this.stylePaddingLeft + this.styleBorderLeft + this.htmlLeft;
  offsetY += this.stylePaddingTop + this.styleBorderTop + this.htmlTop;

  mx = e.pageX - offsetX;
  my = e.pageY - offsetY;

  return {
    x: mx,
    y: my
  };
};

var canvasState, fractalCanvasState;

function reset() {
  canvasState.clear();
  canvasState.shapes = [];
  canvasState.valid = false;
}

function undo() {
  canvasState.shapes.pop();
  redraw();
}

function redraw() {
  canvasState.valid = false;
}

function init() {
  var canvas = document.getElementById("drawCanvas");
  canvasState = new CanvasState(canvas);
}

init();

// function updateCanvas (ctx, data) {
//   ctx.putImageData(data, 0, 0);
// }

// var canvas = document.getElementById("drawCanvas");
// var canvasWidth = canvas.width;
// var canvasHeight = canvas.height;
// var ctx = canvas.getContext("2d");
// var canvasData = ctx.getImageData(0, 0, canvasWidth, canvasHeight);

// var pix = new Pixel(new Point(1,1), new Color(0,0,0,255));
// for (var i = 0; i < 100; i++) {
//    pix.move(1,0).draw(canvasData, canvasWidth);
// }

// var c1 = new Color(255, 0, 0, 255);
// console.log(c1);
// var line1 = new Line(new Point(10, 20),
//                     new Point(400, 30),
//                     new Color(255, 0, 0, 255),
//                     new Color(0, 0, 255, 255));
// console.log(line1);

// line1.draw(canvasData, canvasWidth);
// updateCanvas(ctx, canvasData);

// var circle1 = new Circle(new Point(200, 250), 100,
//                         new Color(0, 0, 0, 255));
// console.log(circle1);
// circle1.draw(canvasData, canvasWidth);
// updateCanvas(ctx, canvasData);


// var ellipse1 = new Ellipse(new Point(300, 150),
//                           25, 50,
//                           new Color(0, 255, 0, 255));
// console.log(ellipse1);
// ellipse1.draw(canvasData, canvasWidth);
// updateCanvas(ctx, canvasData);

// var rectangle1 = new Rectangle(new Point(10, 10),
//                               new Point(90, 50),
//                               new Color(255, 255, 0, 255));
// console.log(rectangle1);
// rectangle1.draw(canvasData, canvasWidth);
// updateCanvas(ctx, canvasData);

// var vertices1 = new List();
// vertices1 = List.cons (new Point(383, 124)) (vertices1);
// vertices1 = List.cons (new Point(223, 423)) (vertices1);
// vertices1 = List.cons (new Point(123, 300)) (vertices1);

// var polygon1 = new Polygon(vertices1, new Color(0,0,0,255));
// console.log(polygon1);
// polygon1.draw(canvasData, canvasWidth);
// updateCanvas(ctx, canvasData);

// var polyline1 = new Polyline(vertices1, new Color(255,0,0,255));
// console.log(polyline1);
// polyline1.draw(canvasData, canvasWidth);
// updateCanvas(ctx, canvasData);