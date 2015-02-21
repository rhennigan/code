class DrawingCanvas
  width: 512
  height: 512
  refreshRate: 1000/30
  antialiasing: false
  drawMode: 'line'
  graphicsPrimitives: []

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

  createDrawingContext: ->
    @drawingContext = @canvas.getContext '2d'

  clearCanvas: ->
    @drawingContext.clearRect 0, 0, @width, @height
    @data = @drawingContext.getImageData 0, 0, @width, @height
    @drawingContext.putImageData @data, 0, 0

  refresh: ->
    @clearCanvas()
    shape.draw() for shape in @graphicsPrimitives
    setTimeout @refresh, @refreshRate
