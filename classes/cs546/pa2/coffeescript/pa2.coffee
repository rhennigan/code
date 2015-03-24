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

parseVertex = (vertexString) ->
  split = vertexString.split(' ')
  [x, y, z] = split[1..3]
  {
    x: parseFloat(x)
    y: parseFloat(y)
    z: parseFloat(z)
  }

parseFace = (faceString) ->
  split = faceString.split(' ')
  parseInt(i) - 1 for i in split[1..]

getVertexRanges = (obj) ->
  x1 = Infinity
  x2 = -Infinity

  for vertex in obj.vertices
    if vertex.x < x1
      x1 = vertex.x
    if vertex.x > x2
      x2 = vertex.x

  {x1: x1, x2: x2}

callback = (obj, txt) -> 
  lines = txt.split('\n')
  for line in lines
    if line[0] == 'v'
      obj.vertices.push(parseVertex(line))
    if line[0] == 'f'
      obj.faces.push(parseFace(line))

  console.log getVertexRanges(obj)

err = (url) ->
  alert "failed to load #{url}"

objectText = {vertices: [], faces: []}

loadObject('objects/SpaceShuttle.obj', objectText, callback, err)
