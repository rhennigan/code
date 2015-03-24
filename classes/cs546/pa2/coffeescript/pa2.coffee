SVG_SIZE = 300
SVG_STROKE = 0.25

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

getVertexRanges = (vertices) ->
  x1 = y1 = z1 = +Infinity
  x2 = y2 = z2 = -Infinity

  clampL = (n, n1) ->
    if n < n1 then n else n1

  clampR = (n, n2) ->
    if n > n2 then n else n2

  for vertex in vertices
    [x1, x2] = [clampL(vertex.x, x1), clampR(vertex.x, x2)]
    [y1, y2] = [clampL(vertex.y, y1), clampR(vertex.y, y2)]
    [z1, z2] = [clampL(vertex.z, z1), clampR(vertex.z, z2)]

  {x1: x1, x2: x2, y1: y1, y2: y2, z1: z1, z2: z2}

###############################################################################

rescaleVertices = (vertices, size) ->
  r = getVertexRanges(vertices)

  rx = r.x2 - r.x1
  ry = r.y2 - r.y1
  rz = r.z2 - r.z1

  rm = Math.max(rx, ry, rz)
  s = size / rm

  for v in vertices
    {
      x: s * (v.x - r.x1)
      y: s * (v.y - r.y1)
      z: s * (v.z - r.z1)
    }

###############################################################################

orthoProj = (vertices) ->
  {
    xy: {x: v.x, y: v.y} for v in vertices
    xz: {x: v.x, y: v.z} for v in vertices
    yz: {x: v.y, y: v.z} for v in vertices
  }

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
  console.log op

  [svgXY, svgXZ, svgYZ] = 
    for i in [1..3]
      svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg')
      svg.setAttribute('width', SVG_SIZE)
      svg.setAttribute('height', SVG_SIZE)
      svg
  
  container = document.getElementById('container')

  for face in obj.faces
    line1 = createSVGLine(op.xy[face[0]], op.xy[face[1]], SVG_STROKE)
    line2 = createSVGLine(op.xy[face[1]], op.xy[face[2]], SVG_STROKE)
    line3 = createSVGLine(op.xy[face[2]], op.xy[face[0]], SVG_STROKE)
    svgXY.appendChild(line1)
    svgXY.appendChild(line2)
    svgXY.appendChild(line3)

  for face in obj.faces
    line1 = createSVGLine(op.xz[face[0]], op.xz[face[1]], SVG_STROKE)
    line2 = createSVGLine(op.xz[face[1]], op.xz[face[2]], SVG_STROKE)
    line3 = createSVGLine(op.xz[face[2]], op.xz[face[0]], SVG_STROKE)
    svgXZ.appendChild(line1)
    svgXZ.appendChild(line2)
    svgXZ.appendChild(line3)

  container.appendChild(svgXY)

###############################################################################

err = (url) ->
  alert "failed to load #{url}"

###############################################################################

main = () ->
  objectText = {vertices: [], faces: []}
  loadObject('objects/SpaceShuttle.obj', objectText, callback, err)

main()