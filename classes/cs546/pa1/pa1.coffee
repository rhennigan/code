class DrawingCanvas
  width = 512
  height = 512
  refreshRate = 1000/30
  antialiasing = false
  drawMode = 'line'
  graphicsPrimitives = []

  constructor: ->
    @createCanvas()
    @resizeCanvas()
    @createDrawingContext()

    @refresh()

  createCanvas: ->
    @canvas = document.createElement 'drawingCanvas'
    document.body.appendChild @canvas

  resizeCanvas: ->
    @canvas.width = @width
    @canvas.height = @height