SVG_SIZE = 300

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

compareBy = 
  x: (v1, v2) ->
    if v1.x < v2.x then -1 else if v1.x > v2.x then 1 else 0
  y: (v1, v2) ->
    if v1.y < v2.y then -1 else if v1.y > v2.y then 1 else 0
  z: (v1, v2) ->
    if v1.z < v2.z then -1 else if v1.z > v2.z then 1 else 0

###############################################################################

createSVGLine = (x1, y1, x2, y2, stroke) ->
  line = document.createElementNS('http://www.w3.org/2000/svg', 'line')
  line.setAttribute('x1', x1)
  line.setAttribute('y1', y1)
  line.setAttribute('x2', x2)
  line.setAttribute('y2', y2)
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
  [svgXY, svgXZ, svgYZ] = 
    for i in [1..3]
      svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg')
      svg.setAttribute('width', SVG_SIZE)
      svg.setAttribute('height', SVG_SIZE)
      svg
  
  container = document.getElementById('container')

  for i in [0..20]
    line = createSVGLine(1, 25*i, 25*i, 25*i, 1)
    svgXY.appendChild(line)

  console.log svgXY

  container.appendChild(svgXY)

###############################################################################

err = (url) ->
  alert "failed to load #{url}"

###############################################################################

objectText = {vertices: [], faces: []}

loadObject('objects/SpaceShuttle.obj', objectText, callback, err)
