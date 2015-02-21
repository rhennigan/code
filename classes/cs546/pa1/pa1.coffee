class Geometry

Geometry::distance = ({x: x1, y: y1}, {x: x2, y: y2}) ->
  dx = x2 - x1
  dy = y2 - y1
  Math.sqrt(dx * dx + dy * dy)

###############################################################################

class Color
  r: 255
  g: 255
  b: 255
  a: 255

  constructor: (r = @r, g = @g, b = @b, a = @a) ->
    @r = r
    @g = g
    @b = b
    @a = a

  write: (x, y, canvas, p = 0) ->
    index = (x + y * canvas.width) * 4
    if canvas.antialiasing
      colorB = this
      [r, g, b, a] = canvas.data.data[index .. index + 3]
      colorA = new Color r, g, b, a
      c = Color.alphaBlend colorA, colorB p
      canvas.data.data[index .. index + 3] = [c.r, c.g, c.b, c.a]
    else
      canvas.data.data[index] = @r
      canvas.data.data[index] = @g
      canvas.data.data[index] = @b
      canvas.data.data[index] = @a


Color::interpolate = (c1, c2, p) ->
  p2 = if p < 0.0 then 0.0 else if p > 1.0 then 1.0 else p
  p1 = 1.0 - p2
  r = Math.floor(p1*c1.r + p2*c2.r)
  g = Math.floor(p1*c1.g + p2*c2.g)
  b = Math.floor(p1*c1.b + p2*c2.b)
  a = Math.floor(p1*c1.a + p2*c2.a)
  new Color r, g, b, a

Color::alphaBlend = (c1, c2, p) ->
  d = Math.floor(p * c2.a)
  r = Math.floor((c1.a * c1.r) / 255.0 - (c1.a - 255.0) * d * c2.r / 65025.0)
  g = Math.floor((c1.a * c1.g) / 255.0 - (c1.a - 255.0) * d * c2.g / 65025.0)
  b = Math.floor((c1.a * c1.b) / 255.0 - (c1.a - 255.0) * d * c2.b / 65025.0)
  a = Math.floor(c1.a + d - c1.a * d / 255.0)
  new Color r, g, b, a

###############################################################################

class Line 
  pt1: {x: 0, y: 0}
  pt2: {x: 0, y: 0}
  col1: new Color()
  col2: new Color()

  constructor: (pt1 = @pt1, pt2 = @pt2, col1 = @col1, col2 = col1) ->
    @pt1 = pt1;
    @pt2 = pt2;
    @col1 = col1;
    @col2 = col2;

  distance: ->
    Geometry::distance(@pt1, @pt2)

  draw: (canvas) ->
    if canvas.antialiasing
      ipart = (x) -> Math.floor x
      round = (x) -> Math.round x
      fpart = (x) -> if x < 0 then 1 - (x - ipart(x)) else x - ipart(x)
      rfpart = (x) -> 1 - fpart(x)

      [x0, y0] = [@pt1.x, @pt1.y]
      [x1, y1] = [@pt2.x, @pt2.y]
      [r0, g0, b0, a0] = [@col1.r, @col1.g, @col1.b, @col1.a]
      [r1, g1, b1, a1] = [@col2.r, @col2.g, @col2.b, @col2.a]

      steep = Math.abs(y1 - y0) > Math.abs(x1 - x0)

      [x0, y0, x1, y1] = [y0, x0, y1, x1] if steep
      [x0, x1, y0, y1] = [x1, x0, y1, y0] if x0 > x1

      [dx, dy] = [x1 - x0, y1 - y0]
      gradient = dy / dx

      # handle first endpoint
      xend = round x0
      yend = y0 + gradient * (xend - x0)
      xgap = rfpart(x0 + 0.5)
      xpxl1 = xend # this will be used in the main loop
      ypxl1 = ipart yend

      if steep
        @col1.write ypxl1, xpxl1, canvas, rfpart(yend) * xgap
        @col1.write ypxl1 + 1, xpxl1, canvas, fpart(yend) * xgap
      else
        @col1.write xpxl1, ypxl1, canvas, rfpart(yend) * xgap
        @col1.write xpxl1, ypxl1 + 1, canvas, fpart(yend) * xgap

      intery = yend + gradient

      # handle second endpoint
      xend = round x1
      yend = y1 + gradient * (xend - x1)
      xgap = fpart(x1 + 0.5)
      xpxl2 = xend # this will be used in the main loop
      ypxl2 = ipart(yend)

      if steep
        @col2.write ypxl2, xpxl2, canvas, rfpart(yend) * xgap
        @col2.write ypxl2 + 1, xpxl2, canvas, fpart(yend) * xgap
      else
        @col2.write xpxl2, ypxl2, canvas, rfpart(yend) * xgap
        @col2.write xpxl2, ypxl2 + 1, canvas, fpart(yend) * xgap

      # main loop
      for x in [xpxl1 + 1 .. xpxl2]
        if steep
          p1 = {x: ipart(intery), y: x}
          p2 = {x: ipart(intery + 1), y: x}
          
        else
          p1 = {x: x, y: ipart(intery)}
          p2 = {x: x, y: ipart(intery) + 1}

        point = {x: (p1.x + p2.x) / 2.0, y: (p1.y + p2.y) / 2.0}
        p = Geometry::distance(@pt1, point) / @distance()
        color = Color.interpolate(@col1, @col2, p)
        color.write(p1.x, p1.y, canvas, rfpart(intery))
        color.write(p2.x, p2.y, canvas, fpart(intery))

      intery += gradient

    else # antialiasing is off
      dx = Math.abs(@pt2.x - @pt1.x)
      dy = Math.abs(@pt2.y - @pt1.y)
      sx = if @pt1.x < @pt2.x then 1 else -1
      sy = if @pt1.y < @pt2.y then 1 else -1
      err = dx - dy
      dist = @distance()
      pix = 
        point: 
          x: @pt1.x
          y: @pt1.y
        color: new Color(@col1.r, @col1.g, @col1.b, @col1.a)

      step = () =>
        console.log @pt1
        console.log pix.point
        p = Geometry::distance(@pt1, pix.point) / dist
        pix.color = Color::interpolate(@col1, @col2, p)
        pix.color.write(pix.point.x, pix.point.y, canvas)

        e2 = 2 * err
        if e2 > -dy
          err -= dy
          pix.point.x += sx
        if e2 < dx
          err += dx
          pix.point.y += sy

        return

      step() until pix.point.x == @pt2.x and pix.point.y == @pt2.y

###############################################################################

class DrawingCanvas
  width: 32
  height: 32
  refreshRate: 1000/30
  antialiasing: false
  drawMode: 'line'
  graphicsPrimitives: []
  modified: false
  polyInProgress: false
  data: null

  constructor: ->
    @createCanvas()
    @resizeCanvas()
    @createDrawingContext()
    @setupEventHandlers()
    @clearCanvas()
    @refresh()

  createCanvas: ->
    @canvas = document.createElement 'canvas'
    document.body.appendChild @canvas

  resizeCanvas: ->
    @canvas.width = @width
    @canvas.height = @height

  createDrawingContext: ->
    @drawingContext = @canvas.getContext '2d'

  setupEventHandlers: ->
    @getMousePos = -> 
      rect = @canvas.getBoundingClientRect()
      x: event.clientX - rect.left
      y: event.clientY - rect.top

    @canvas.addEventListener "click", (e) => @getMousePos(e)

  clearCanvas: ->
    @drawingContext.clearRect 0, 0, @width, @height
    @data = @drawingContext.getImageData 0, 0, @width, @height
    @drawingContext.putImageData @data, 0, 0
    @modified = true

  refresh: ->
    if @modified
      @clearCanvas()
      shape.draw() for shape in @graphicsPrimitives
      @drawingContext.putImageData(@data, 0, 0)
      @modified = false
    setTimeout @refresh, @refreshRate

  reset: ->
    @clearCanvas()
    @graphicsPrimitives = []

  undo: ->
    @graphicsPrimitives.pop()
    @modified = true

window.DrawingCanvas = DrawingCanvas
canvas = new DrawingCanvas()

# line = new Line({x:1, y:1}, {x:25, y:30}, new Color(255, 0, 0))
# console.log canvas
# line.draw(canvas)
# canvas.modified = true
# canvas.refresh()
# console.log canvas.data

for i in [0...canvas.width]
  for j in [0...canvas.height]
    color = new Color(Math.random()*255,Math.random()*255,Math.random()*255,255)
    color.write(i,j,canvas)
console.log canvas.data
canvas.drawingContext.putImageData(canvas.data.data, 0, 0)
