RotationTransform[\[Theta]][{x, y}]
{x Cos[\[Theta]] - y Sin[\[Theta]], y Cos[\[Theta]] + x Sin[\[Theta]]}
FullSimplify[Cos[x Cos[\[Theta]] - y Sin[\[Theta]] + \[Phi]], 
  Assumptions -> {Element[{x, y, \[Theta], \[Phi]}, 
     Reals]}] // TraditionalForm
cos(x cos(\[Theta]) - y sin(\[Theta]) + \[Phi])
randomWave := With[
  {\[Theta] = RandomReal[{0, Pi}], \[Phi] = RandomReal[{-Pi, Pi}]},
  Cos[#[[1]] Cos[\[Theta]] - #[[2]] Sin[\[Theta]] + \[Phi]] &
  ]
waves = Table[randomWave, {10}];
grf = Function[{x, y}, Evaluate[Total[#[{x, y}] & /@ waves]]];
Plot3D[grf[x, y], {x, -2 Pi, 2 Pi}, {y, -2 Pi, 2 Pi}]
\!\(\*
Graphics3DBox[{}]\)
waveOctave = Function[{x, y, \[Psi], \[Sigma]},
   Total[#[{x, y}] & /@ Table[
      With[{
        \[Theta] = RandomReal[{-Pi, Pi}],
        \[Phi] = RandomReal[{-Pi, Pi}]},
       \[Sigma] Cos[
          2.0 \[Psi] (#[[1]] Cos[\[Theta]] - #[[
                2]] Sin[\[Theta]]) + \[Phi]] &
       ], {25}]]];
octaves = 
  Table[Function[{x, y}, Evaluate[waveOctave[x, y, 2^i, 2^-i]]], {i, 
    0, 10}];
Table[Plot3D[octaves[[k]][x, y], {x, -Pi, Pi}, {y, -Pi, Pi}, 
  BoxRatios -> {1, 1, .25},
  PlotPoints -> 50,
  MaxRecursion -> 1,
  ImageSize -> 512,
  PlotRange -> {-Pi, Pi}], {k, 3}]
{
Graphics3DBox[], 
Graphics3DBox[], 
Graphics3DBox[]}
Table[Plot3D[
  Sum[octave[x, y], {octave, octaves[[;; k]]}], {x, -Pi, Pi}, {y, -Pi,
    Pi}, BoxRatios -> {1, 1, .25},
  PlotPoints -> 50,
  MaxRecursion -> 1,
  ImageSize -> 512,
  PlotRange -> All], {k, 3}]
{
Graphics3DBox[], 
Graphics3DBox[], 
Graphics3DBox[]}
Table[ArrayPlot[
  Table[Sum[octave[x, y], {octave, octaves[[;; k]]}], {y, -Pi, Pi, 
    2 Pi/100}, {x, -Pi, Pi, 2 Pi/100}]], {k, 6}]
{
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[]}
waveOctave = Function[{x, y, \[Psi], \[Sigma]},
   Evaluate[Total[#[{x, y}] & /@ Table[
       With[{
         \[Theta] = RandomReal[{-Pi, Pi}],
         \[Phi] = RandomReal[{-Pi, Pi}]},
        \[Sigma] Cos[
           2.0 \[Psi] (#[[1]] Cos[\[Theta]] - #[[
                 2]] Sin[\[Theta]]) + \[Phi]] &
        ], {5}]]]];
{a, b} = RandomVariate[NormalDistribution[2, .5], 2];
f = 1 + RandomVariate[NormalDistribution[]];
cosines = 
  Table[Abs[
    waveOctave[f x, f y, 
     a *= RandomVariate[NormalDistribution[2, .5]], 
     b /= RandomVariate[NormalDistribution[2, .5]]]], {i, 8}];
fractalWaves = Function[{x, y}, Evaluate[-Log[Total[cosines]]]];
Function[{x, 
  y}, -Log[Abs[
     1.06132 Cos[2.36321 + 6.74304 (-0.637504 x - 2.98032 y)] + 
      1.06132 Cos[2.18306 + 6.74304 (-3.02717 x + 0.353547 y)] + 
      1.06132 Cos[3.02326 - 6.74304 (-2.97737 x + 0.651169 y)] + 
      1.06132 Cos[2.7158 + 6.74304 (2.77426 x + 1.26184 y)] + 
      1.06132 Cos[2.5687 + 6.74304 (1.97133 x + 2.32435 y)]] + 
    Abs[0.524502 Cos[2.36321 + 10.9861 (-0.637504 x - 2.98032 y)] + 
      0.524502 Cos[2.18306 + 10.9861 (-3.02717 x + 0.353547 y)] + 
      0.524502 Cos[3.02326 - 10.9861 (-2.97737 x + 0.651169 y)] + 
      0.524502 Cos[2.7158 + 10.9861 (2.77426 x + 1.26184 y)] + 
      0.524502 Cos[2.5687 + 10.9861 (1.97133 x + 2.32435 y)]] + 
    Abs[0.337976 Cos[2.36321 + 28.6048 (-0.637504 x - 2.98032 y)] + 
      0.337976 Cos[2.18306 + 28.6048 (-3.02717 x + 0.353547 y)] + 
      0.337976 Cos[3.02326 - 28.6048 (-2.97737 x + 0.651169 y)] + 
      0.337976 Cos[2.7158 + 28.6048 (2.77426 x + 1.26184 y)] + 
      0.337976 Cos[2.5687 + 28.6048 (1.97133 x + 2.32435 y)]] + 
    Abs[0.228857 Cos[2.36321 + 51.3515 (-0.637504 x - 2.98032 y)] + 
      0.228857 Cos[2.18306 + 51.3515 (-3.02717 x + 0.353547 y)] + 
      0.228857 Cos[3.02326 - 51.3515 (-2.97737 x + 0.651169 y)] + 
      0.228857 Cos[2.7158 + 51.3515 (2.77426 x + 1.26184 y)] + 
      0.228857 Cos[2.5687 + 51.3515 (1.97133 x + 2.32435 y)]] + 
    Abs[0.116607 Cos[2.36321 + 101.983 (-0.637504 x - 2.98032 y)] + 
      0.116607 Cos[2.18306 + 101.983 (-3.02717 x + 0.353547 y)] + 
      0.116607 Cos[3.02326 - 101.983 (-2.97737 x + 0.651169 y)] + 
      0.116607 Cos[2.7158 + 101.983 (2.77426 x + 1.26184 y)] + 
      0.116607 Cos[2.5687 + 101.983 (1.97133 x + 2.32435 y)]] + 
    Abs[0.0689976 Cos[2.36321 + 236.27 (-0.637504 x - 2.98032 y)] + 
      0.0689976 Cos[2.18306 + 236.27 (-3.02717 x + 0.353547 y)] + 
      0.0689976 Cos[3.02326 - 236.27 (-2.97737 x + 0.651169 y)] + 
      0.0689976 Cos[2.7158 + 236.27 (2.77426 x + 1.26184 y)] + 
      0.0689976 Cos[2.5687 + 236.27 (1.97133 x + 2.32435 y)]] + 
    Abs[0.0557988 Cos[2.36321 + 487.461 (-0.637504 x - 2.98032 y)] + 
      0.0557988 Cos[2.18306 + 487.461 (-3.02717 x + 0.353547 y)] + 
      0.0557988 Cos[3.02326 - 487.461 (-2.97737 x + 0.651169 y)] + 
      0.0557988 Cos[2.7158 + 487.461 (2.77426 x + 1.26184 y)] + 
      0.0557988 Cos[2.5687 + 487.461 (1.97133 x + 2.32435 y)]] + 
    Abs[0.0221037 Cos[2.36321 + 955.847 (-0.637504 x - 2.98032 y)] + 
      0.0221037 Cos[2.18306 + 955.847 (-3.02717 x + 0.353547 y)] + 
      0.0221037 Cos[3.02326 - 955.847 (-2.97737 x + 0.651169 y)] + 
      0.0221037 Cos[2.7158 + 955.847 (2.77426 x + 1.26184 y)] + 
      0.0221037 Cos[2.5687 + 955.847 (1.97133 x + 2.32435 y)]]]]
SetDirectory["/home/rhennigan/Pictures/noise"];
ParallelDo[
 Block[{waveOctave, a, b, f, cosines, fractalWaves, color, cf, img},
  waveOctave = Function[{x, y, \[Psi], \[Sigma]},
    Evaluate[Total[#[{x, y}] & /@ Table[
        With[{
          \[Theta] = RandomReal[{-Pi, Pi}],
          \[Phi] = RandomReal[{-Pi, Pi}]},
         \[Sigma] Cos[
            2.0 \[Psi] (#[[1]] Cos[\[Theta]] - #[[
                  2]] Sin[\[Theta]]) + \[Phi]] &
         ], {100}]]]];
  {a, b} = RandomVariate[NormalDistribution[2, .5], 2];
  f = 1 + RandomVariate[NormalDistribution[]];
  cosines = 
   Table[Abs[
     waveOctave[f x, f y, 
      a *= RandomVariate[NormalDistribution[2, .5]], 
      b /= RandomVariate[NormalDistribution[2, .5]]]], {i, 8}];
  fractalWaves = Function[{x, y}, Evaluate[-Log[Total[cosines]]]];
  color = ColorData[RandomChoice[ColorData["Gradients"]]];
  cf = Function[{x, y, z}, Evaluate@color[z]];
  img = Plot3D[fractalWaves[x, y], {x, 0, 1}, {y, 0, 1},
    BoxRatios -> {1, 1, .1},
    PlotPoints -> 100,
    MaxRecursion -> 4,
    ImageSize -> 2048,
    (*ColorFunction\[Rule]Function[{x,y,z},Hue[.65(1-z)]],*)
    
    ColorFunction -> cf,
    Mesh -> None,
    PlotRange -> All];
  Export["noise_" <> ToString[i] <> ".png", img]
  ], {i, 890, 10000}]
$Aborted
With[{w = 256, h = 256}, 
 Image[Rescale[
   ParallelTable[fractalWaves[x/w, y/h], {x, w}, {y, h}]]]]
Plot[PDF[ExponentialDistribution[1], x], {x, 0, 10}]
\!\(\*
GraphicsBox[{}]\)
With[{\[Theta] = 1.0, \[Phi] = 1.0}, 
 Plot3D[Cos[
     1 (#[[1]] Cos[\[Theta]] - #[[2]] Sin[\[Theta]]) + \[Phi]] &[{x, 
    y}], {x, -3 Pi, 3 Pi}, {y, -3 Pi, 3 Pi}]]
\!\(\*
Graphics3DBox[{}]\)
randomWave2 := With[
  {
   \[Theta] = RandomReal[{-Pi, Pi}],
   \[Phi] = RandomReal[{-Pi, Pi}],
   \[Psi] = RandomVariate[ExponentialDistribution[1]],
   \[Sigma] = RandomVariate[NormalDistribution[]]
   },
  Cos[\[Psi] (#[[1]] Cos[\[Theta]] - #[[
          2]] Sin[\[Theta]]) + \[Phi]] &
  ]
waves2 = Table[randomWave2, {500}];
grf2 = Function[{x, y}, Evaluate[Total[#[{x, y}] & /@ waves2]]];
Plot3D[grf2[x, y], {x, -3 Pi, 3 Pi}, {y, -3 Pi, 3 Pi}, 
 BoxRatios -> {1, 1, .2}, PlotPoints -> 50, MaxRecursion -> 2, 
 ImageSize -> 800]
Image[Rescale[
  ParallelTable[Abs[grf2[.25 x, .25 y]], {x, 512}, {y, 512}]]]
Image[Rescale[ParallelTable[grf2[.25 x, .25 y], {x, 512}, {y, 512}]]]
Cos[x Cos[\[Theta]] - y Sin[\[Theta]] + \[Phi]] // TraditionalForm
cos(x cos(\[Theta]) - y sin(\[Theta]) + \[Phi])
FullSimplify[
   Sum[Subscript[\[Sigma], i]
        Cos[2 Pi Subscript[\[Psi], 
          i] (#[[1]] Cos[Subscript[\[Theta], i]] - #[[2]] Sin[
              Subscript[\[Theta], i]]) + Subscript[\[Phi], i]] &[{x, 
      y}], {i, 1, n}], 
   Assumptions -> {Element[{x, y, \[Sigma], \[Psi], \[Phi], \[Theta]},
       Reals]}] /. {\[Sigma] -> \[Alpha]} // TraditionalForm
\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(i = 1\), \(n\)]\(
\*SubscriptBox[\(\[Alpha]\), \(i\)]\ \(cos(2\ \[Pi]\ 
\*SubscriptBox[\(\[Psi]\), \(i\)]\ \((x\ \(cos(
\*SubscriptBox[\(\[Theta]\), \(i\)])\) - y\ \(sin(
\*SubscriptBox[\(\[Theta]\), \(i\)])\))\) + 
\*SubscriptBox[\(\[Phi]\), \(i\)])\)\)\)
ExampleData /@ ExampleData["ColorTexture"]
{
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[]}
img = Image[
  Abs[Fourier[
    ImageData[
     ImageApply[
      Block[{x = Mean[#]}, If[x < 0.0, 0.0, If[x > 1.0, 1.0, x]]] &, 
      ImageResize[
GraphicsBox[], 256]]]]]]
\!\(\*
GraphicsBox[{}]\)
5
f = FourierDCT[{1, 2, 3, 4, 5}]
{6.7082, -2.22703, 3.19189*10^-16, -0.200811, 0.}
Plot[Evaluate[Sum[Cos[x f[[i]]], {i, 1, Length[f]}]], {x, 1, 5}]
\!\(\*
GraphicsBox[{}]\)
n = 1000;
per1 = 12.34;
per2 = 46.12;
mag1 = 1.25;
mag2 = 0.77;
pdata = Table[
    mag1 Cos[2 \[Pi] x/per1] + mag2 Cos[2 \[Pi] x/per2], {x, n}] + 
   RandomReal[.2, {n}];
ListPlot[pdata]
\!\(\*
GraphicsBox[{}]\)
f = FourierDCT[pdata];
pos = Position[f, Max[f]][[1, 1]]
163
N[pos/Pi]
51.8845
Show[ListLogPlot[f], Graphics[{Red, Point[{pos, Log[f[[pos]]]}]}], 
 PlotRange -> All]
\!\(\*
GraphicsBox[{}]\)
fr = Abs[Fourier[pdata Exp[2 Pi I (pos - 2) N[Range[0, n - 1]]/n], 
    FourierParameters -> {0, 2/n}]];
frpos = Position[fr, Max[fr]][[1, 1]]
522
Show[ListPlot[fr], Graphics[{Red, Point[{frpos, fr[[frpos]]}]}], 
 PlotRange -> All]
\!\(\*
GraphicsBox[{}]\)
ClearAll[n]
inv = Subscript[u, r] /. 
  First[Solve[Subscript[v, s] == 1/Sqrt[n] \!\(\*
UnderoverscriptBox["\[Sum]", 
RowBox[{
StyleBox["r", "TI"], "=", "1"}], 
StyleBox["n", "TI"],
LimitsPositioning->True]\(\*
SubscriptBox[
StyleBox["u", "TI"], 
StyleBox["r", "TI"]] \*
SuperscriptBox[
StyleBox["E", "TI"], 
RowBox[{"2", "\[Pi]", " ", "I", 
RowBox[{"(", 
RowBox[{
StyleBox["r", "TI"], "-", "1"}], ")"}], 
RowBox[{
RowBox[{"(", 
RowBox[{
StyleBox["s", "TI"], "-", "1"}], ")"}], "/", 
StyleBox["n", "TI"]}]}]]\)\), Subscript[u, r]]]
-((E^(-((2 I \[Pi])/
   n)) (E^((2 I \[Pi])/n) - E^((2 I \[Pi] s)/n)) Sqrt[n] Subscript[v, 
  s])/(-1 + E^(2 I \[Pi] s)))
FullSimplify[inv]
((-1 + E^((2 I \[Pi] (-1 + s))/n)) Sqrt[n] Subscript[v, s])/(-1 + E^(
 2 I \[Pi] s))
ClearAll[f]
n = 25;
xg = N[Range[0, n - 1]]/n;
fg = Range[n];
fp = ListPlot[Transpose[{xg, fg}], PlotRange -> All]
\!\(\*
GraphicsBox[{}]\)
cc = FourierDCT[fg, 3]/Sqrt[n];
Sum[cc[[r]]*Cos[Pi (r - 1/2) x], {r, Length[cc]}]
12.8224 Cos[(\[Pi] x)/2] - 13.2603 Cos[(3 \[Pi] x)/2] + 
 5.74903 Cos[(5 \[Pi] x)/2] - 5.07298 Cos[(7 \[Pi] x)/2] + 
 3.32275 Cos[(9 \[Pi] x)/2] - 3.06301 Cos[(11 \[Pi] x)/2] + 
 2.2765 Cos[(13 \[Pi] x)/2] - 2.13815 Cos[(15 \[Pi] x)/2] + 
 1.68136 Cos[(17 \[Pi] x)/2] - 1.59362 Cos[(19 \[Pi] x)/2] + 
 1.28752 Cos[(21 \[Pi] x)/2] - 1.22538 Cos[(23 \[Pi] x)/2] + 
 1. Cos[(25 \[Pi] x)/2] - 0.952428 Cos[(27 \[Pi] x)/2] + 
 0.774673 Cos[(29 \[Pi] x)/2] - 0.73602 Cos[(31 \[Pi] x)/2] + 
 0.588059 Cos[(33 \[Pi] x)/2] - 0.555099 Cos[(35 \[Pi] x)/2] + 
 0.426303 Cos[(37 \[Pi] x)/2] - 0.397015 Cos[(39 \[Pi] x)/2] + 
 0.28046 Cos[(41 \[Pi] x)/2] - 0.253467 Cos[(43 \[Pi] x)/2] + 
 0.144218 Cos[(45 \[Pi] x)/2] - 0.118488 Cos[(47 \[Pi] x)/2] + 
 0.0126636 Cos[(49 \[Pi] x)/2]
Show[fp, Plot[
  Sum[cc[[r]]*Cos[Pi (r - 1/2) x], {r, Length[cc]}], {x, 0, 1}, 
  PlotRange -> All], PlotRange -> All]
\!\(\*
GraphicsBox[{}]\)
data = ImageData[ImageApply[Mean, ImageResize[
GraphicsBox[], 128]]];
t = FourierDCT[data];
f = Abs[Diagonal[t]]^2;
ListLogPlot[f, Joined -> True, PlotRange -> All]
\!\(\*
GraphicsBox[{}]\)
randomWave[freq_, amp_] := With[
  {\[Theta] = RandomReal[{0, Pi}], \[Phi] = RandomReal[{-Pi, Pi}]},
  amp Cos[
     freq (#[[1]] Cos[\[Theta]] - #[[2]] Sin[\[Theta]]) + \[Phi]] &
  ]
waves = Flatten[
   Table[randomWave[N[i/Length[f]], f[[i]]], {i, Length[f]}, {25}]];
grf = Function[{x, y}, Evaluate[Total[#[{x, y}] & /@ waves]]];
ArrayPlot[Table[grf[x, y], {x, 1, 64}, {y, 1, 64}]]
\!\(\*
GraphicsBox[{}]\)
truncate[data_, f_] :=
  Module[{i, j},
   {i, j} = Floor[Dimensions[data]/Sqrt[f]];
   PadRight[Take[data, i, j], Dimensions[data], 0.]
   ];
{ArrayPlot[FourierDCT[truncate[t, 4], 3]], 
 ArrayPlot[FourierDCT[truncate[t, 9], 3]], 
 ArrayPlot[FourierDCT[truncate[t, 16], 3]]}
{
GraphicsBox[], 
GraphicsBox[], 
GraphicsBox[]}
cc = FourierDCT[fg, 3];
ArrayPlot[cc]
\!\(\*
GraphicsBox[{}]\)
{rs, cs} = Dimensions[cc]
{43, 32}
f = Function[{x, y}, 
   Evaluate[
    Sum[cc[[r, c]]*Cos[Pi (c - 1/2) x] + 
      cc[[r, c]]*Cos[Pi (r - 1/2) y] , {r, rs}, {c, cs}]]];
Plot3D[With[{r = 8, c = 8}, 
  cc[[r, c]]*Cos[Pi (c - 1/2) x] + 
   cc[[r, c]]*Cos[Pi (r - 1/2) y] ], {x, 0, 1}, {y, 0, 1}]
\!\(\*
Graphics3DBox[{}]\)
f = Function[{x, y}, 
   Evaluate[
    Sum[cc[[r, c]]*Cos[Pi (r - 1/2) y] + 
      cc[[r, c]]*Cos[Pi (c - 1/2) x], {r, rs}, {c, cs}]]];
ArrayPlot[Table[f[x/cs, y/rs], {y, rs}, {x, cs}]]
\!\(\*
GraphicsBox[{}]\)
Plot3D[f[x, y], {x, 0, 1}, {y, 0, 1}]
\!\(\*
Graphics3DBox[{}]\)
Image[Rescale[
  Table[Sum[cc[[r]]*Cos[Pi (r - 1/2) x], {r, Length[cc]}], {x, 0, 1, 
    1/First[Dimensions[cc]]}]]]
\!\(\*
GraphicsBox[{}]\)
r1 = 10;
r2 = 12;

d2 = ColorNegate[Image[DiskMatrix[r2]]]
d1 = ImagePad[Image[DiskMatrix[r1]], 2, Black]
\!\(\*
GraphicsBox[{}]\)
\!\(\*
GraphicsBox[{}]\)
psd = ImageData[Blur[ImagePad[ColorNegate[ImageAdd[d2, d1]], 15], 3]];
inv = InverseFourier[psd]
Out[102]
{rs, cs} = Dimensions[inv]
{55, 55}
With[{c = 10, r = 10}, 
  Log@Abs[Fourier[
     psd Exp[2 Pi I (c - 2) N[Range[0, cs - 1]]/cs] + 
      Exp[2 Pi I (r - 2) N[Range[0, rs - 1]]/rs]]]] // ArrayPlot
\!\(\*
GraphicsBox[{}]\)
N[cs/(pos - 2 + 2 (frpos - 1)/cs)]
u = ImageData[ImageApply[Mean, ImageResize[
GraphicsBox[], 512]]];
{m, n} = Dimensions[u];
zc = ConstantArray[0, {m, 1}];
zr = ConstantArray[0, {1, n}];
Lu = Plus[
   ArrayPad[u[[1 ;; m - 1, ;;]] - u[[2 ;; m, ;;]], {{0, 1}, {0, 0}}],
   ArrayPad[u[[2 ;; m, ;;]] - u[[1 ;; m - 1, ;;]], {{1, 0}, {0, 0}}],
   ArrayPad[u[[;; , 1 ;; n - 1]] - u[[;; , 2 ;; n]], {{0, 0}, {0, 1}}],
   ArrayPad[
    u[[;; , 2 ;; n]] - u[[;; , 1 ;; n - 1]], {{0, 0}, {1, 0}}]
   ];
lu = Lu*(-1)^Table[i + j, {i, m}, {j, n}];
mp = Fourier[lu, FourierParameters -> {1, 1}];
fudgeFactor = 100;
abs = fudgeFactor*Log[1 + Abs@mp];
Labeled[Image[abs/Max[abs], ImageSize -> 300], 
 Style["Magnitude spectrum", 18]]
Labeled[
GraphicsBox[], \!\(\*
StyleBox["\<\"Magnitude spectrum\"\>",
StripOnInput->False,
FontSize->18]\)]
DensityPlot
periodicDFTforGabor[u_] := Module[
  {m, n, zc, zr, Lu, lu, mp, cx, cy, c},
  {m, n} = Dimensions[u];
  zc = ConstantArray[0, {m, 1}];
  zr = ConstantArray[0, {1, n}];
  Lu = Plus[
    ArrayPad[
     u[[1 ;; m - 1, ;;]] - u[[2 ;; m, ;;]], {{0, 1}, {0, 0}}],
    ArrayPad[
     u[[2 ;; m, ;;]] - u[[1 ;; m - 1, ;;]], {{1, 0}, {0, 0}}],
    ArrayPad[
     u[[;; , 1 ;; n - 1]] - u[[;; , 2 ;; n]], {{0, 0}, {0, 1}}],
    ArrayPad[u[[;; , 2 ;; n]] - u[[;; , 1 ;; n - 1]], {{0, 0}, {1, 0}}]
    ];
  lu = Lu*(-1)^Table[i + j, {i, m}, {j, n}];
  mp = Fourier[lu, FourierParameters -> {1, 1}];
  cx = 2 Cos[2 Pi/m*N[Range[0, m - 1]]];
  cy = 2 Cos[2 Pi/n*N[Range[0, n - 1]]];
  c = ReplacePart[
    Block[{ones = 4 ConstantArray[1, {m, n}]}, 
     Table[ones[[i, j]] - cx[[i]] - cy[[j]], {i, m}, {j, n}]], {1, 
      1} -> 1.0];
  mp[[1, 1]] = 0.0;
  If[Mod[m, 2] == 0, mp[[1, ;;]] = ConstantArray[0, n]];
  If[Mod[n, 2] == 0, mp[[;; , 1]] = ConstantArray[0, m]];
  mp
  ]
dfth = periodicDFTforGabor[u];
s = Flatten[Abs[dfth]^2];
phase = Arg[dfth];
q = Range[2, Floor[Log[2, Sqrt[m^2 + (n^2)]]]]
{2, 3, 4, 5}
lq = Length[q]
4
eps = 0.05;
a =