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

getVertexRanges = (obj) ->
  x1 = y1 = z1 = +Infinity
  x2 = y2 = z2 = -Infinity

  clampL = (n, n1) ->
    if n < n1 then n else n1

  clampR = (n, n2) ->
    if n > n2 then n else n2

  for vertex in obj.vertices
    [x1, x2] = [clampL(vertex.x, x1), clampR(vertex.x, x2)]
    [y1, y2] = [clampL(vertex.y, y1), clampR(vertex.y, y2)]
    [z1, z2] = [clampL(vertex.z, z1), clampR(vertex.z, z2)]

  {x1: x1, x2: x2, y1: y1, y2: y2, z1: z1, z2: z2}

###############################################################################

rescaleVertices = (obj) ->
  r = getVertexRanges(obj)

  rx = r.x2 - r.x1
  ry = r.y2 - r.y1
  rz = r.z2 - r.z1

  rm = Math.max(rx, ry, rz)

###############################################################################

callback = (obj, txt) -> 
  lines = txt.split('\n')
  for line in lines
    if line[0] == 'v'
      obj.vertices.push(parseVertex(line))
    if line[0] == 'f'
      obj.faces.push(parseFace(line))

  ranges = getVertexRanges(obj)

  console.log ranges

###############################################################################

err = (url) ->
  alert "failed to load #{url}"

###############################################################################

objectText = {vertices: [], faces: []}

loadObject('objects/SpaceShuttle.obj', objectText, callback, err)
