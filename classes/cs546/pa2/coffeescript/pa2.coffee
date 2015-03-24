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

cb = (sh, txt) -> 
  sh.text(txt)
  console.log sh

err = (url) ->
  alert "failed to load #{url}"

objectText = {text: null}

IO::load('objects/SpaceShuttle.obj', $("#test"), cb, err)