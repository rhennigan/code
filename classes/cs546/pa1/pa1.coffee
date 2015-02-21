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

class Line 
  pt1: {x: 0, y: 0}
  pt2: {x: 0, y: 0}
  col1: new Color()
  col2: new Color()

  constructor: (pt1 = @pt1, pt2 = @pt2, col1 = @col1, col2 = @col2) ->
    @pt1 = pt1;
    @pt2 = pt2;
    @col1 = col1;
    @col2 = col2;

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