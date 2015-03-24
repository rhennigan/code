SVG_SIZE = 400
SVG_STROKE = 0.5

###############################################################################

loadObject =  (url, store, cb, cbErr) ->
  req = new XMLHttpRequest()
  req.open('GET', url, true)

  req.onreadystatechange = () ->
    if req.readyState == 4
      if req.status == 200
        cb(store, req.responseText)
      else
        cbErr(url)

  req.send(null)

###############################################################################

parseVertex = (vertexString) ->
  split = vertexString.split(' ')
  [x, y, z] = split[1..3]
  {
    x: parseFloat(x)
    y: parseFloat(y)
    z: parseFloat(z)
  }

###############################################################################

parseFace = (faceString) ->
  split = faceString.split(' ')
  parseInt(i) - 1 for i in split[1..]

###############################################################################

Array::max = () -> 
  Math.max.apply(null, @)

Array::min = () -> 
  Math.min.apply(null, @)

getVertexRanges = (vertices) ->
  xs = for v in vertices
    v.x
  ys = for v in vertices
    v.y
  zs = for v in vertices
    v.z

  {
    x1: xs.min()
    x2: xs.max()

    y1: ys.min()
    y2: ys.max()

    z1: zs.min()
    z2: zs.max()
  }

# getVertexRanges = (vertices) ->
#   x1 = y1 = z1 = +Infinity
#   x2 = y2 = z2 = -Infinity

#   clampL = (n, n1) ->
#     if n < n1 then n else n1

#   clampR = (n, n2) ->
#     if n > n2 then n else n2

#   for vertex in vertices
#     [x1, x2] = [clampL(vertex.x, x1), clampR(vertex.x, x2)]
#     [y1, y2] = [clampL(vertex.y, y1), clampR(vertex.y, y2)]
#     [z1, z2] = [clampL(vertex.z, z1), clampR(vertex.z, z2)]

#   {x1: x1, x2: x2, y1: y1, y2: y2, z1: z1, z2: z2}

###############################################################################

rescaleVertices = (vertices, size) ->
  r = getVertexRanges(vertices)
  console.log r

  rx = r.x2 - r.x1
  ry = r.y2 - r.y1
  rz = r.z2 - r.z1

  rm = Math.max(rx, ry, rz)
  s = size / rm

  for v in vertices
    {
      x: size - s * (v.x - r.x1)
      y: size - s * (v.y - r.y1)
      z: size - s * (v.z - r.z1)
    }

###############################################################################

orthoProj = (vertices) ->
  {
    xy: {x: v.x, y: v.y} for v in vertices
    xz: {x: v.x, y: v.z} for v in vertices
    yz: {x: v.y, y: v.z} for v in vertices
  }

###############################################################################

union = (a) ->
  seen = Object.create(null)
  out = []
  len = a.length
  j = 0
  for i in [0...len]
    item = a[i]
    if seen[item] isnt 1 then [seen[item], out[j++]] = [1, item]
  out

###############################################################################

class Line 
  p1: 0
  p2: 0

  constructor: (p1 = @p1, p2 = @p2) ->
    @p1 = p1
    @p2 = p2

  toString: () ->
    "(#{@p1.toString()}, #{@p2.toString()})"

###############################################################################

createMeshLines = (faces) ->
  lines = []

  for face in faces
    len = face.length
    for i in [0...len]
      v1 = Math.min(face[i], face[(i+1)%len])
      v2 = Math.max(face[i], face[(i+1)%len])
      lines.push(new Line(v1, v2))

  union(lines)

###############################################################################

createSVGLine = (p1, p2, stroke) ->
  line = document.createElementNS('http://www.w3.org/2000/svg', 'line')
  line.setAttribute('x1', p1.x)
  line.setAttribute('y1', p1.y)
  line.setAttribute('x2', p2.x)
  line.setAttribute('y2', p2.y)
  line.setAttribute('stroke-width', stroke)
  line.setAttribute('stroke', 'black')
  line

###############################################################################

callback = (obj, txt) -> 
  lines = txt.split('\n')
  for line in lines
    if line[0] == 'v'
      obj.vertices.push(parseVertex(line))
    if line[0] == 'f'
      obj.faces.push(parseFace(line))

  rescaled = rescaleVertices(obj.vertices, SVG_SIZE)
  op = orthoProj(rescaled)

  [svgXY, svgXZ, svgYZ] = 
    for i in [1..3]
      svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg')
      svg.setAttribute('width', SVG_SIZE)
      svg.setAttribute('height', SVG_SIZE)
      svg
  
  container = document.getElementById('container')

  meshLines = createMeshLines(obj.faces)
  console.log op.xy[0]

  for line in meshLines
    lineXY = createSVGLine(op.xy[line.p1], op.xy[line.p2], SVG_STROKE)
    lineXZ = createSVGLine(op.xz[line.p1], op.xz[line.p2], SVG_STROKE)
    lineYZ = createSVGLine(op.yz[line.p1], op.yz[line.p2], SVG_STROKE)
    svgXY.appendChild(lineXY)
    svgXZ.appendChild(lineXZ)
    svgYZ.appendChild(lineYZ)

  container.appendChild(svgXY)
  container.appendChild(svgXZ)
  container.appendChild(svgYZ)

###############################################################################

err = (url) ->
  alert "failed to load #{url}"

###############################################################################

main = () ->
  object3D = {vertices: [], faces: []}
  # loadObject('objects/UtahTeapot.obj', object3D, callback, err)
  loadObject('objects/Horse.obj', object3D, callback, err)
  console.log getVertexRanges(object3D.vertices)
  arr = [1, 5, 1, 25, 25,2,31,5,35,235,46,32]
  console.log arr.max()

main()

