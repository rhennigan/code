class IO

IO::load = (url, cb, cbErr) ->
  req = new XMLHttpRequest()
  req.open('GET', url, true)

  req.onreadystatechange = () ->
    if req.readyState == 4
      if req.status == 200
        cb(req.responseText)
      else
        cbErr(url)

  req.send(null)

vertexShader = {text: null}
fragmentShader = {text: null}

cb = (sh, txt) -> 
  sh.text = txt
  console.log sh

err = (url) ->
  alert "failed to load #{url}"

IO::load('vertex.glsl', cb, err)
# IO::loads = (urls, cb, cbErr) ->
#   numUrls = urls.length
#   numComplete = 0
#   result = []

#   partialCallback = (txt, idx) ->
#     result[idx] = txt
#     numComplete++
#     if numComplete is numUrls then cb(result)

#   for i in [0...numUrls]
#     load(urls[i], i, partialCallback, cbErr)