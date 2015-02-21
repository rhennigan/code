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
      [r, g, b, a] = canvas.data[index .. index + 3]
      colorA = new Color r, g, b, a
      c = Color::alphaBlend colorA colorB p
      canvas.data[index .. index + 3] = [c.r, c.g, c.b, c.a]
    else
      canvas.data[index .. index + 3] = [@r, @g, @b, @a]


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

  length: ->
    dx = @pt2.x - @pt1.x
    dy = @pt2.y - @pt1.y
    Math.sqrt (dx*dx + dy*dy)

  draw: (canvas) ->
    if canvas.antialiasing
      ipart = (x) -> Math.floor(x)
      round = (x) -> Math.round(x)
      fpart = (x) -> if x < 0 then 1 - (x - ipart(x)) else x - ipart(x)
      rfpart = (x) -> 1 - fpart(x)

      [x0, y0] = [@pt1.x, @pt1.y]
      [x1, y1] = [@pt2.x, @pt2.y]
      [r0, g0, b0, a0] = [@col1.r, @col1.g, @col1.b, @col1.a]
      [r1, g1, b1, a1] = [@col2.r, @col2.g, @col2.b, @col2.a]

      steep = Math.abs(y1 - y0) > Math.abs(x1 - x0)

    else
      drawLine(this)


###############################################################################

class DrawingCanvas
  width: 512
  height: 512
  refreshRate: 1000/30
  antialiasing: false
  drawMode: 'line'
  graphicsPrimitives: []
  modified: false
  polyInProgress: false

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
      @modified = false
    setTimeout @refresh, @refreshRate

  reset: ->
    @clearCanvas()
    @graphicsPrimitives = []

  undo: ->
    @graphicsPrimitives.pop()
    @modified = true

  # getMousePos: (event) ->
  #   rect = @canvas.getBoundingClientRect()
  #   x: event.clientX - rect.left
  #   y: event.clientY - rect.top
  #   console.log "(#{x}, #{y})"

window.DrawingCanvas = DrawingCanvas

line = new Line({x:10, y:20}, {x:30, y:50}, new Color(100, 150, 200))
console.log(line)