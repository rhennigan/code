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

callback = (obj, txt) -> 
  vertices = []
  faces = []

  lines = txt.split('\n')
  for line in lines
    if line[0] == 'v'
      vertices.push(parseVertex(line))
    if line[0] == 'f'
      faces.push(parseFace(line))

  obj = {vertices: vertices, faces: faces}
  console.log obj

err = (url) ->
  alert "failed to load #{url}"

objectText = {text: null}

loadObject('objects/SpaceShuttle.obj', objectText, callback, err)
