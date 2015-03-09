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
waves = Table[randomWave, {500}];
grf = Function[{x, y}, Evaluate[Total[#[{x, y}] & /@ waves]]];
RandomChoice[ColorData["Gradients"]]
"FallColors"
SetDirectory["/home/rhennigan/Pictures/noise"];
ParallelDo[Block[{waveOctave, a, b, f, fractalWaves, color, cf, img},
  waveOctave = Function[{x, y, \[Psi], \[Sigma]},
    Evaluate[Total[#[{x, y}] & /@ Table[
        With[{
          \[Theta] = RandomReal[{-Pi, Pi}],
          \[Phi] = RandomReal[{-Pi, Pi}]},
         \[Sigma] Cos[
            2.0 \[Psi] (#[[1]] Cos[\[Theta]] - #[[
                  2]] Sin[\[Theta]]) + \[Phi]] &
         ], {50}]]]];
  {a, b} = RandomVariate[NormalDistribution[2, .5], 2];
  f = 1 + RandomVariate[NormalDistribution[]];
  fractalWaves = 
   Function[{x, y}, 
    Evaluate[-Log[Sum[Abs[waveOctave[f x, f y, a^i, b^-i]], {i, 8}]]]];
  color = ColorData[RandomChoice[ColorData["Gradients"]]];
  cf = Function[{x, y, z}, Evaluate@color[z]];
  img = Plot3D[fractalWaves[x, y], {x, 0, 1}, {y, 0, 1},
    BoxRatios -> {1, 1, .1},
    PlotPoints -> 50,
    MaxRecursion -> 4,
    ImageSize -> 2048,
    (*ColorFunction\[Rule]Function[{x,y,z},Hue[.65(1-z)]],*)
    
    ColorFunction -> cf,
    Mesh -> None,
    PlotRange -> All];
  Export["noise_" <> ToString[i] <> ".png", img]
  ], {i, 1000}]
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