class IO

IO::load = (url, data, cb, cbErr) ->
  req = new XMLHttpRequest()
  req.open('GET', url, true)

  req.onreadystatechange = () ->
    if req.readyState == 4
      if req.status == 200
        cb(req.responseText, data)
      else
        cbErr(url)

  req.send(null)

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