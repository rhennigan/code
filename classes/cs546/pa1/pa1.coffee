class CanvasState
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