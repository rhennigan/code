class IO

  load: (url, store, cb, cbErr) ->
    req = new XMLHttpRequest()
    req.open('GET', url, true)

    req.onreadystatechange = () ->
      if req.readyState == 4
        if req.status == 200
          cb(store, req.responseText)
        else
          cbErr(url)

    req.send(null)

callback = (obj, txt) -> 
  vertices = []
  faces = []

  lines = txt.split('\n')
  for line in lines
    if line[0] == 'v'
      vertices.push(line)
    if line[0] == 'f'
      faces.push(line)

  obj = {vertices: vertices, faces: faces}
  console.log obj
  console.log lines

err = (url) ->
  alert "failed to load #{url}"

objectText = {text: null}

IO::load('objects/SpaceShuttle.obj', objectText, callback, err)
