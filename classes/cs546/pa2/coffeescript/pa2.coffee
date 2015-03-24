class IO

IO::load = (url, store, cb, cbErr) ->
  req = new XMLHttpRequest()
  req.open('GET', url, true)

  req.onreadystatechange = () ->
    if req.readyState == 4
      if req.status == 200
        cb(store, req.responseText)
      else
        cbErr(url)

  req.send(null)

cb = (obj, txt) -> 
  obj.text = txt.split('\n')
  console.log obj
  console.log objectText

err = (url) ->
  alert "failed to load #{url}"

objectText = {text: null}

# IO::load('objects/SpaceShuttle.obj', $("#test"), cb, err)
IO::load('objects/SpaceShuttle.obj', objectText, cb, err)
