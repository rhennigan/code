points = RandomReal[{-1, 1}, {4, 2}];
first = First[points];
last = Last[points];
segment = RandomReal[{-10, 10}, {2, 2}];
Graphics[{
  Opacity[.5], Gray, Line[points],
  Opacity[1],
  Red, Point[first],
  Green, Point[last],
  Blue, Line[segment]
  }]
\!\(\*
GraphicsBox[{}]\)
segment = {{200, 50}, {50, 310}} // N;
points = {{50, 200},
    {150, 200},
    {200, 113},
    {250, 200},
    {350, 200}} // N;
first = First[points]
last = Last[points]
Graphics[{
  Opacity[.5], Gray, Line[points],
  Opacity[1],
  Red, Point[first],
  Green, Point[last],
  Blue, Line[segment]
  }]
{50., 200.}
{350., 200.}
\!\(\*
GraphicsBox[{}]\)
12*1.2
14.4
segmentDistance = EuclideanDistance @@ segment
300.167
polyLineDistance = EuclideanDistance @@ {First[points], Last[points]}
300.
Graphics[Point[# - first & /@ points]]
\!\(\*
GraphicsBox[{}]\)
scaledPoints = 
 segmentDistance/polyLineDistance*(# - first) & /@ points
{{0., 0.}, {100.056, 0.}, {150.083, -87.0483}, {200.111, 
  0.}, {300.167, 0.}}
scaledPoints = segmentDistance*Normalize[# - first] & /@ points
{{0., 0.}, {300.167, 0.}, {259.653, -150.599}, {300.167, 
  0.}, {300.167, 0.}}
u = Last[scaledPoints] - First[scaledPoints]
v = Last[segment] - First[segment]
{300.167, 0.}
{-150., 260.}
theta = ArcCos[u.v/(Norm[u] Norm[v])]
2.09407
rotate[{x_, y_}, t_] := {x Cos[t] - y Sin[t], y Cos[t] + x Sin[t]}
Norm[rotate[Last[scaledPoints], theta] - v]
2.84217*10^-14
Norm[rotate[Last[scaledPoints], -theta] - v]
520.
If[
 Norm[rotate[Last[scaledPoints], theta] - v] > 
  Norm[rotate[Last[scaledPoints], -theta] - v],
 theta = -theta
 ]
rotatedPoints = rotate[#, theta] & /@ scaledPoints
{{0., 0.}, {-50., 86.6667}, {0.4, 173.5}, {-100., 173.333}, {-150., 
  260.}}
translatedPoints = # + First[segment] & /@ rotatedPoints
{{200., 50.}, {150., 136.667}, {200.4, 223.5}, {100., 223.333}, {50., 
  310.}}
Graphics[Point[translatedPoints]]
\!\(\*
GraphicsBox[{}]\)
Graphics[{
  Opacity[.5], Gray, Line[translatedPoints],
  Opacity[1],
  Red, Point[First[translatedPoints]],
  Green, Point[Last[translatedPoints]],
  Orange, PointSize[Large], Point[translatedPoints], ,
  Blue, Line[segment]
  }]
\!\(\*
GraphicsBox[{}]\)
rotate[{300, 0}, 60 Degree] + {50, 100} // N
{200., 359.808}
173*2
346

rotate[{100, 0}, 60 Degree] // N
{50., 86.6025}
200 - 87
113
Graphics[
 {
  Red, Arrow[{{200, 50}, {50, 310}}],
  Green, Arrow[{{50, 310}, {350, 310}}],
  Blue, Arrow[{{350, 310}, {0, 0}}]
  }
 ]
\!\(\*
GraphicsBox[{}]\)
List @@@ MyColors /@ Range[6]*255
{{12, 90, 129}, {214, 74, 39}, {102, 203, 57}, {142, 173, 171}, {153, 
  52, 198}, {215, 224, 229}}