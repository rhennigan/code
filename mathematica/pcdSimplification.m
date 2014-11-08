(* ::Package:: *)

Needs["JLink`"];
With[
	{pathToJavaPlex = "D:\\Google Drive\\Projects\\pcdSimplification\\lib"},
	AddToClassPath[pathToJavaPlex];
	InstallJava[];
	ReinstallJava[JVMArguments -> "-Xmx16384m"];
	LoadJavaClass["edu.stanford.math.plex4.api.Plex4"];
	apiPlex4=JavaNew["edu.stanford.math.plex4.api.Plex4"];
	LoadJavaClass["edu.stanford.math.plex4.examples.PointCloudExamples"];
	examplesPointCloudExamples=JavaNew["edu.stanford.math.plex4.examples.PointCloudExamples"];
	LoadJavaClass["edu.stanford.math.plex4.metric.impl.ExplicitMetricSpace"];
];

ShiftedRescale[points_] := Module[
	{ranges, min, i},
	ranges = {Min[#], Max[#]} & /@ Transpose[points];
	min = Min[ranges];
	Table[(#[[i]] - ranges[[i, 1]])/(ranges[[i, 2]] - min), {i, Length[ranges]}] & /@ points
]

FlatError[points_] := Module[
	{dimension, principalComponents},
	dimension = Length[Transpose[points]];
	If[Length[points] < dimension + 1,
		0,
		(
		principalComponents = PrincipalComponents[points];
		(*Total[#^2&/@principalComponents[[All,dimension]]]/Total[#^2&/@Flatten[principalComponents]]*)
		(*Variance[principalComponents[[All, dimension]]]/Variance[Flatten[principalComponents]]*)
		Variance[principalComponents[[All, dimension]]]
		)
	]
]

FlatError2[points_] := Module[
	{dimension, principalComponents},
	dimension = Length[Transpose[points]];
	If[Length[points] < dimension + 1,
		0,
		(
		principalComponents = PrincipalComponents[points];
		(*Total[#^2&/@principalComponents[[All,dimension]]]/Total[#^2&/@Flatten[principalComponents]]*)
		Variance[principalComponents[[All, dimension]]]/Variance[Flatten[principalComponents]]
		(*Variance[principalComponents[[All, dimension]]]*)
		)
	]
]

PartitionPointCloud[points_,threshold_]:=Module[
	{error,clusters},
	error=FlatError[points];
	If[error<threshold,
		{points},
		clusters=FindClusters[points,2];
		Flatten[
			PartitionPointCloud[#,threshold]&/@clusters,
			1
		]
	]
]

AppendNextPoint[accumulatedPoints_, cluster_] := Module[
	{pt},
	Join[
		{Last[SortBy[cluster, Total[Table[Norm[# - pt], {pt, accumulatedPoints}]] &]]},
		accumulatedPoints
	]
]

DecomposeCluster[cluster_, nf_] := Module[
	{len, dim},
	len = Length[cluster];
	dim = Length[Transpose[cluster]];
	If[len > dim,
		First[nf[Mean[#]]]& /@ FindClusters[cluster, dim],
		cluster
	]
]

SimplifyPointCloud[points_, threshold_] := Module[
	{clusters, simplified, nf},
	nf = Nearest[points];
	clusters = PartitionPointCloud[points, threshold];
	simplified = Flatten[DecomposeCluster[#, nf]& /@ clusters, 1];
	simplified
]

DelaunayComplex[points_]:=Module[
	{randInt, qhullDir, tempDir, formattedOutput, inputFile, outputFile, qdelaunay, options, out},
	randInt = ToString[RandomInteger[{10^15, 10^16 - 1}]];
	qhullDir = FileNameJoin[{$UserBaseDirectory, "Applications"}];
	tempDir = $TemporaryDirectory;
	formattedOutput = Join[{{Length[Transpose[points]]}}, {{Length[points]}}, points];
	inputFile = Export[FileNameJoin[{tempDir, "input" <> randInt <> ".tsv"}], formattedOutput, "TSV"];
	outputFile = FileNameJoin[{tempDir, "output" <> randInt <> ".txt"}];
	qdelaunay = FileNameJoin[{qhullDir, "qdelaunay"}];
	options = " Qt s i ";
	Run[qdelaunay <> options <> " <" <> inputFile <> " >" <> outputFile];
	out = 1 + Import[outputFile, "Table"];
	Rest[out]
]

FullComplex[points_]:=Rest[Union[Sort /@ Flatten[Subsets[#, Length[#]] & /@ DelaunayComplex[points], 1]]]

SimplexArea[simplex_, data_] := Module[
	{vertices, n, matrix, i, j},
	vertices = If[data == {}, simplex, data[[simplex]]];
	n = Length[vertices] - 1;
	matrix = ReplacePart[PadLeft[Table[Norm[vertices[[i]] - vertices[[j]]]^2, {i, n + 1}, {j, n + 1}], {n + 2, n + 2}, 1], {1, 1} -> 0];
	Chop[Sqrt[(-1)^(n + 1)/(2^n (n!)^2)*Det[matrix]]]
]

GetDistanceFunction[points_, interpolationPoints_] := Module[
	{limits, ranges, dim, variables, nearestFunction, pointCloudDistance, interpolationRegion, distanceFunctionBase, distanceFunction},
	limits = {Min[#], Max[#]} & /@ Transpose[points];
	ranges = #[[2]] - #[[1]] & /@ limits;
	dim = Length[limits];
	variables = Table[Symbol["x" <> ToString[i]], {i, dim}];
	nearestFunction = Nearest[points];
	pointCloudDistance[point_] := Norm[point - First[nearestFunction[point]]];
	Off[Nearest::neard];
	interpolationRegion = Table[{variables[[i]], limits[[i, 1]] - .1 ranges[[i]], limits[[i, 2]] + .1 ranges[[i]]}, {i, dim}];
	distanceFunctionBase = FunctionInterpolation[
      pointCloudDistance[variables], ##, 
      InterpolationOrder -> 1, 
      InterpolationPoints -> interpolationPoints
      ] & @@ interpolationRegion;
    distanceFunction[x_List] := distanceFunctionBase[##] & @@ x;
    distanceFunction
]

GetKernelFunction[points_, bandwidth_, kernel_, interpolationPoints_] := Module[
	{limits, ranges, dim, variables, dist, pdf, interpolationRegion, kernelFunctionBase, kernelFunction},
	limits = {Min[#], Max[#]} & /@ Transpose[points];
	ranges = #[[2]] - #[[1]] & /@ limits;
	dim = Length[limits];
	variables = Table[Symbol["x" <> ToString[i]], {i, dim}];
	dist = SmoothKernelDistribution[points, bandwidth, kernel,
		InterpolationPoints -> interpolationPoints
		];
	pdf[vars_List] := PDF[dist, vars];
	interpolationRegion = Table[{variables[[i]], limits[[i, 1]] - .1 ranges[[i]], limits[[i, 2]] + .1 ranges[[i]]}, {i, dim}];
	kernelFunctionBase = FunctionInterpolation[
		pdf[variables], ##,
		InterpolationOrder -> 1,
		InterpolationPoints -> interpolationPoints
		] & @@ interpolationRegion;
	kernelFunction[x_List] := kernelFunctionBase[##] & @@ x;
	kernelFunction
]

SimplexMaxDistance[simplex_, data_] := If[Length[simplex] == 1,
	0,
	Max[EuclideanDistance @@@ Subsets[data[[simplex]], {2}]]
]

SimplexDistance[simplex_, data_, kernelFunction_, dt_] := If[
	Length[simplex] == 1,
	0,
	Module[
	{vertices, base, others, sides, dim, steps, tLimits, testPts, maxPt, u},
	vertices = data[[simplex]];
	base = First[vertices];
	others = Rest[vertices];
	sides = Table[v - base, {v, others}];
	dim = Length[vertices] - 1;
	steps = dt/Norm[#] & /@ sides;
	tLimits = Table[{u[i], 0, 1 - Total[Table[u[j], {j, i - 1}]], steps[[i]]}, {i, 1, dim}];
	testPts = Flatten[Table[(base + Total[Table[u[i]*sides[[i]], {i, dim}]]), ##] & @@ tLimits, dim - 1];
	maxPt = Last[SortBy[testPts, kernelFunction]];
	kernelFunction[maxPt]
	]
]

SimplexDensityMinVal[simplex_,data_,kernelFunction_]:=Module[
	{vertices,base,others,sides,dim,limits,eq,u,v,i,j},
	vertices = data[[simplex]];
	base = First[vertices];
	others = Rest[vertices];
	sides = Table[v - base, {v, others}];
	dim = Length[vertices] - 1;
	limits = Table[0 <= u[i] <= 1 - Total[Table[u[j], {j, i - 1}]], {i, 1, dim}];
	eq = kernelFunction[##] & @@ (base + Total[Table[u[i]*sides[[i]], {i, dim}]]);
	NMinValue[{eq, And @@ limits}, Table[u[i], {i, dim}]]
]

SimplexDensity[simplex_,data_,kernelFunction_]:=Module[
	{vertices,base,others,sides,dim,limits,eq,u},
	vertices = data[[simplex]];
	base = First[vertices];
	others = Rest[vertices];
	sides = Table[v - base, {v, others}];
	dim = Length[vertices] - 1;
	limits = Table[{u[i], 0, 1 - Total[Table[u[j], {j, i - 1}]]}, {i, 1, dim}];
	eq = kernelFunction[##] & @@ (base + Total[Table[u[i]*sides[[i]], {i, dim}]]);
	NIntegrate[eq, ##] & @@ limits
]

SimplexWeight[simplex_,data_,kernelFunction_]:=Module[
	{vertices},
	vertices = data[[simplex]];
	If[
		Length[vertices] == 1,
		(kernelFunction[##] & @@ First[vertices]),
		SimplexDensity[simplex, data, kernelFunction]/SimplexArea[simplex, data]
	]
]

DrawSimplex[simplex_,data_]:=Module[
	{vertices},
	vertices = data[[simplex]];
	Which[
		Length[vertices] == 1, Point[vertices],
		Length[vertices] == 2, Line[vertices],
		Length[vertices] == 3, Polygon[vertices],
		Length[vertices] == 4, Polygon /@ (Subsets[vertices, {3}]),
		True, {}
		]
]

AddNoise[points_, sigma_] := Module[
	{dim, noise, n},
	dim = Length[Transpose[points]];
	n = Length[points];
	noise = RandomVariate[MultinormalDistribution[Array[0&, dim], IdentityMatrix[dim]*sigma], n];
	points + noise
]

RandomSimplexPoints[simplex_, data_, n_] := Module[
	{vertices, sdim, exps, weights},
	vertices = If[data == {}, simplex, data[[simplex]]];
	sdim = Length[vertices];
	exps = RandomReal[ExponentialDistribution[1], {n, sdim}];
	weights = #/Total[#] & /@ exps;
	#.vertices & /@ weights
]

RandomizedSimplexDensity[simplex_, data_, count_, kernelFunction_] := Module[
	{randomPts},
	randomPts = RandomSimplexPoints[simplex, data, count];
	Mean[kernelFunction /@ randomPts]
]

CenteredSimplexDensity[simplex_, data_, kernelFunction_] := (
	kernelFunction[Mean[data[[simplex]]]]
)

GetCorrectedFiltration[complex_, data_, count_, kernelFunction_] := Module[
	{filtration, max, hashTable, SimplexAgeCorrection},
	filtration = Map[{#, RandomizedSimplexDensity[#, data, count, kernelFunction]} &, complex];
	max = Max[filtration[[All, 2]]];
	filtration[[All, 2]] = Round[(max - filtration[[All, 2]]) * Length[filtration]];
	Scan[(hashTable[#[[1]]] = Last[#]) &, filtration];
	SimplexAgeCorrection[simplex_] := Module[
		{subSimplices},
		subSimplices = Subsets[simplex][[2 ;; -2]];
		(hashTable[#] = Min[{hashTable[simplex], hashTable[#]}]) & /@ subSimplices
	];
	Scan[SimplexAgeCorrection, complex];
	SortBy[{#, hashTable[#]} & /@ complex, First]
]


GetFaces[simplex_] := {#, simplex[[2]]} & /@ Rest[Subsets[simplex[[1]]]]

MulticoreSimplify[points_, threshold_] := Module[
	{kernelCount, kernelAssignments, simplifiedAssignments},
	kernelCount = Length[Kernels[]];
	If[kernelCount == 0,
		LaunchKernels[];
		kernelCount = Length[Kernels[]];
	];
	kernelAssignments = FindClusters[points, kernelCount];
	simplifiedAssignments = ParallelMap[SimplifyPointCloud[#, threshold]&, kernelAssignments];
	Flatten[simplifiedAssignments, 1]
]
  
SimplifyPointCloudOld[points_, threshold_]:=Module[
	{clusters, nf, simplified},
	clusters = PartitionPointCloud[points, threshold];
	nf = Nearest[points];
	simplified = First[nf[Mean[#]]] & /@ clusters;
	simplified
]

(*------------------------------------------------------------------------------------------------*)
(*-------------------------------===( Example Point Cloud Data )===-------------------------------*)
(*------------------------------------------------------------------------------------------------*)

GetRandomManifoldPoints[n_, sourcePoints_, sourceFaces_] := Module[
	{triangleVertices, simplices, areas, normedAreas, dist, simplex, i},
	triangleVertices = Map[sourcePoints[[#]] &, sourceFaces, -2];
	areas = SimplexArea[#, {}]& /@ triangleVertices;
	normedAreas = Chop[areas/Total[areas]];
	dist = EmpiricalDistribution[normedAreas -> Range[Length[normedAreas]]];
	simplices = triangleVertices[[RandomVariate[dist, n]]];
	Table[
		Module[
		{vec, opp, w},
		vec = Table[simplex[[i]] - simplex[[1]], {i, 2, Length[simplex]}];
		opp = simplex[[1]] + Total[vec];
		w = RandomReal[{0, 1}, 2];
		If[Total[w] > 1,
			opp - Total[Table[w[[i]]*vec[[i]], {i, 1, Length[vec]}]],
			simplex[[1]] + Total[Table[w[[i]]*vec[[i]], {i, 1, Length[vec]}]]]
		], {simplex, simplices}
	]
]

PointCloudExample["Circle", count_, noise_] := Module[
	{points, noisePoints},
	points = {Cos[#], Sin[#]} & /@ RandomReal[{0, 2 Pi}, count];
	noisePoints = RandomVariate[MultinormalDistribution[{0, 0}, IdentityMatrix[2]*noise], count];
	points + noisePoints
]

PointCloudExample[{"Geometry3D", object_}, count_, noise_:0, radius_: 1] := Module[
	{sourcePoints, polygonData, polygonTypes, triangleData, sourceFaces, sample, noisePoints, points, bb1, bb2, shift, shifted, scale},
	sourcePoints = N@ExampleData[{"Geometry3D", object}, "VertexData"];
	polygonData = ExampleData[{"Geometry3D", object}, "PolygonData"];
	polygonTypes = Union[Length /@ polygonData];
	triangleData = If[
		polygonTypes == {3},
		polygonData,
		Flatten[
			Table[#[[{1, i, i + 1}]], {i, 2, Length[#] - 1}] & /@ polygonData,
			 1]
	];
	sourceFaces = Union[Sort /@ triangleData];
	sample = GetRandomManifoldPoints[count, sourcePoints, sourceFaces];
	{bb1, bb2} = Transpose[{Min[#], Max[#]} & /@ Transpose[sample]];
	shift = Mean[{bb1, bb2}];
	shifted = # - shift & /@ sample;
	scale = radius * 2 / Max[bb2 - bb1];
	points = scale * shifted;
	noisePoints = If[noise == 0,
		0,
		RandomVariate[MultinormalDistribution[{0, 0, 0}, IdentityMatrix[3] * noise], count]
	];
	points + noisePoints
]

PointCloudExample[{"ParametricPlot3D", p_}, count_, noise_: 0, radius_: 1] := Module[
	{sourcePoints, polygonData, polygonTypes, triangleData, sourceFaces, sample, noisePoints, points, bb1, bb2, shift, shifted, scale},
	sourcePoints = Flatten[Cases[p, GraphicsComplex[pts_, __] -> pts, -1], 1];
	polygonData = Flatten[Cases[p, Polygon[x__] -> x, -1], 1];
	polygonTypes = Union[Length /@ polygonData];
	triangleData = If[
		polygonTypes == {3},
		polygonData,
		Flatten[
			Table[#[[{1, i, i + 1}]], {i, 2, Length[#] - 1}] & /@ polygonData,
			 1]
	];
	sourceFaces = Union[Sort /@ triangleData];
	sample = GetRandomManifoldPoints[count, sourcePoints, sourceFaces];
	{bb1, bb2} = Transpose[{Min[#], Max[#]} & /@ Transpose[sample]];
	shift = Mean[{bb1, bb2}];
	shifted = # - shift & /@ sample;
	scale = radius * 2 / Max[bb2 - bb1];
	points = scale * shifted;
	noisePoints = If[noise == 0,
		0,
		RandomVariate[MultinormalDistribution[{0, 0, 0}, IdentityMatrix[3] * noise], count]
	];
	points + noisePoints
]

(*------------------------------------------------------------------------------------------------*)
(*---------------------------------===( JavaPlex Integration )===---------------------------------*)
(*------------------------------------------------------------------------------------------------*)

FormatForJavaPlex[indexedComplex_] := Module[
	{max},
	max = Max[indexedComplex[[All, 2]]];
	SortBy[{#[[1, 1]], 
		Length[indexedComplex]*(max - Max[#[[All, 2]]])/max} & /@ 
		GatherBy[Flatten[GetFaces /@ RandomSample[indexedComplex], 1], 
			First], {Last[#] &, Length[First[#]] &}]
]

GenerateMatlabCode[simplified_, faces_, dimension_, coefficients_] := Module[
	{commands1, commands2, commands},
	commands1 = "stream.addVertex(" <> ToString[#] <> ");\n" & /@ Range[Length[simplified]];
	commands2 = "stream.addElement(" <> StringReplace[ToString[#[[1]]], {"{" -> "[", "}" -> "]"}] <> 
	", " <> ToString[#[[2]]] <> ");\n" & /@ faces;
	commands = "clc;clear;close all;\n" <>
	"stream = api.Plex4.createExplicitSimplexStream();\n" <>
	StringJoin[commands1] <>
	StringJoin[commands2] <>
	"stream.ensureAllFaces();\n" <>
	"stream.finalizeStream();\n" <>
	"num_simplices = stream.getSize()
	persistence = api.Plex4.getModularSimplicialAlgorithm(3,2);
	intervals = persistence.computeIntervals(stream);
	infinite_barcodes = intervals.getInfiniteIntervals();
	betti_numbers_array = infinite_barcodes.getBettiSequence()
	options.filename = 'torus';
	options.max_filtration_value = " <> 
	ToString[Max[faces[[All, 2]]]] <> ";
	plot_barcodes(intervals, options);
   ";
   Export["commands.m", StringJoin[commands], "TEXT"]
]

GetStream[filteredComplex_] := Module[
	{vertices, simplices, stream},
	vertices = Select[filteredComplex, Length[#[[1]]] == 1 &];
	simplices = Complement[filteredComplex, vertices];
	stream = Plex4@createExplicitSimplexStream[];
	Scan[stream@addVertex[#[[1, 1]], #[[2]]] &, vertices];
	Scan[stream@addElement[#[[1]], #[[2]]] &, simplices];
	stream@finalizeStream[];
	stream
]

GetBarcodes[stream_, maxDim_, p_] := Module[
	{persistence, intervals, outString, split, dim},
	persistence = apiPlex4@getModularSimplicialAlgorithm[maxDim, p];
	intervals = persistence@computeAnnotatedIntervals[stream];
	outString = intervals@toString[];
	split = StringSplit[outString, "Dimension"];
	Table[
		Module[
			{splitIntervals, splitIntervalsAndElements},
			splitIntervals = StringSplit[split[[dim + 1]], "\n"][[2 ;;]];
			splitIntervalsAndElements = StringSplit[#, ":"] & /@ splitIntervals;
			With[
				{
					r1 = {"[" -> "{", "(" -> "{", "]" -> "}", ")" -> "}", "infinity" -> "\[Infinity]"},
					r2 = {"[" -> "\[Sigma]["}
				},
				{ToExpression[StringReplace[#[[1]], r1]], ToExpression[StringReplace[#[[2]], r2]]} & /@ splitIntervalsAndElements
			]
		], {dim, 0, Length[split] - 1}
	]
]

PlotBarcodes[barcodes_, range_: 0, options_: {}] := Module[
	{xValues, max, plotMax, dim},
	xValues = barcodes[[All, All, 1]];
	max = 0.5 * Max[Map[EuclideanDistance @@ # &, xValues /. {\[Infinity] -> 0}, {2}]];
	plotMax = If[range == 0,
		Max[xValues /. {\[Infinity] -> -\[Infinity]}] + 1,
		range
		];
	GraphicsColumn[
		Table[
			Module[
				{currentXValues, lineCoordinates, lines},
				currentXValues = xValues[[dim + 1]];
				lineCoordinates = MapIndexed[Transpose[{#1, #2[[{1, 1}]]}] &, currentXValues] /. {\[Infinity] -> plotMax};
				(*max = Max[EuclideanDistance @@@ lineCoordinates];*)
				lines = {
					(*AbsoluteThickness[(EuclideanDistance@@#)/max],*)
					Blend[{
						White, 
						CustomColor[3], 
						Lighter[CustomColor[1]],
						CustomColor[1], 
						CustomColor[2]
						},
						Max[{0.1, Min[{1, ((EuclideanDistance @@ #) / max)}]}]^1.0
					],
					Line[{{Min[{#[[1, 1]], plotMax}], #[[1, 2]]},{Min[{#[[2, 1]], plotMax}], #[[2, 2]]}}]
					}& /@ lineCoordinates;
				Graphics[
					{
						AbsoluteThickness[2],
						lines
					},
					##,
					Axes -> False,
					Frame -> True,
					FrameTicks -> {{None, None}, {Automatic, Automatic}},
					FrameTicksStyle -> AbsoluteThickness[2],
					AxesOrigin -> {Automatic, 0},
					AxesStyle -> AbsoluteThickness[2],
					LabelStyle -> {FontFamily -> "Myriad Pro Cond Bold", 14},
					PlotLabel -> Style["Dimension " <> ToString[dim], {FontFamily -> "Myriad Pro Cond", 18, Bold}],
					ImageSize -> {1000, 250},
					AspectRatio -> 0.21,
					PlotRange -> {{0, plotMax}, {-0.1 * Length[lines], 1.1 * Length[lines]}}
				] & @@ options
			],
			{dim, 0, Length[barcodes] - 1}
		],
		Spacings -> {0, Scaled[0.1]}
	]
]

PlotBarcodes[barcodes_, {minval_,maxval_}] := Module[
	{xValues, max, plotMax, dim,range,options},
range=0;
options={};
	xValues = barcodes[[All, All, 1]];
	max = 0.5 * Max[Map[EuclideanDistance @@ # &, xValues /. {\[Infinity] -> 0}, {2}]];
	plotMax = If[range == 0,
		Max[xValues /. {\[Infinity] -> -\[Infinity]}] + 1,
		range
		];
	GraphicsColumn[
		Table[
			Module[
				{currentXValues, lineCoordinates, lines},
				currentXValues = xValues[[dim + 1]];
				lineCoordinates = MapIndexed[Transpose[{#1, #2[[{1, 1}]]}] &, currentXValues] /. {\[Infinity] -> plotMax};
				(*max = Max[EuclideanDistance @@@ lineCoordinates];*)
				lines = {
					(*AbsoluteThickness[(EuclideanDistance@@#)/max],*)
					Blend[{
						White, 
						CustomColor[3], 
						Lighter[CustomColor[1]],
						CustomColor[1], 
						CustomColor[2]
						},
						Max[{0.1, Min[{1, ((EuclideanDistance @@ #) / max)}]}]^1.0
					],
					Line[{{Min[{#[[1, 1]], plotMax}], #[[1, 2]]},{Min[{#[[2, 1]], plotMax}], #[[2, 2]]}}]
					}& /@ lineCoordinates;
				Graphics[
					{
						AbsoluteThickness[2],
						lines
					},
					##,
					Axes -> False,
					Frame -> True,
					FrameTicks -> {{None, None}, {Automatic, Automatic}},
					FrameTicksStyle -> AbsoluteThickness[2],
					AxesOrigin -> {Automatic, 0},
					AxesStyle -> AbsoluteThickness[2],
					LabelStyle -> {FontFamily -> "Myriad Pro Cond Bold", 14},
					PlotLabel -> Style["Dimension " <> ToString[dim], {FontFamily -> "Myriad Pro Cond", 18, Bold}],
					ImageSize -> {1000, 250},
					AspectRatio -> 0.21,
					PlotRange -> {{minval, maxval}, {-0.1 * Length[lines], 1.1 * Length[lines]}}
				] & @@ options
			],
			{dim, 0, Length[barcodes] - 1}
		],
		Spacings -> {0, Scaled[0.1]}
	]
]

(*------------------------------------------------------------------------------------------------*)
(*-----------------------------------===( Currently Unused )===-----------------------------------*)
(*------------------------------------------------------------------------------------------------*)

FlatErrorOld[points_]:=Module[
	{dimension,principalComponents},
	dimension=Length[Transpose[points]];
	If[Length[points]<dimension+1,
		0,
		(
		principalComponents=PrincipalComponents[points];
		Total[#^2&/@principalComponents[[All,dimension]]]/Total[#^2&/@Flatten[principalComponents]]
		)
	]
]

DecomposeClusterOld[cluster_] := Module[
	{dim},
	dim = Length[Transpose[cluster]];
	Nest[AppendNextPoint[#, cluster] &,
		Nearest[cluster, Mean[cluster]],
		dim
	]
]

(*------------------------------------------------------------------------------------------------*)
(*-----------------------------===( Functions Mentioned in Paper )===-----------------------------*)
(*------------------------------------------------------------------------------------------------*)

(*ad[X_ /; NumberQ[X]] := 1
ad[X_ /; Depth[X] == 2] := First[Dimensions[X]]
ad[X_List] := Dimensions[X]
\[LeftBracketingBar]X_\[RightBracketingBar] := Length[X]
mean[X_] := Mean[X]
shift[M_] := # - mean[M] & /@ M

cov[X_, Y_] := \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(k = 1\), \(ad[X]\)]\(\((\((X[\([k]\)] - mean[X])\) \((Y[\([k]\)] - mean[Y])\))\)/ad[X]\n\n
covm[M_]\)\) := 
 Table[cov[M[[All, r]], M[[All, c]]], {r, ad[M][[2]]}, {c, 
   ad[M][[2]]}]
   
zm[i_] := ConstantArray[0, {i, i}]
pad[M_, n_] := PadRight[M, {n, n}]
svd[M_] := SingularValueDecomposition[M]
usvd[M_] := svd[M][[1]]
pc[M_] := (shift[M]).(usvd[covm[shift[M]]])

var[A_List /; Depth[A] == 2] := \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(k = 1\), \(ad[A]\)]\(
\*SuperscriptBox[\((A[\([k]\)] - mean[A])\), \(2\)]/\((ad[A]\  - \ 1)\)\n
var[M_List\  /; \ Depth[M]\  == \ 3]\)\) := \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(k = 1\), \(\[LeftBracketingBar]M\[RightBracketingBar]\)]\(
\*SuperscriptBox[\((M[\([k]\)] - mean[M])\), \(2\)]/\((\[LeftBracketingBar]M\[RightBracketingBar]\  - \ 1)\)\n\n
accumulator[xs___, \ {}]\)\) := xs
accumulator[{}, {y_, ys___}] := accumulator[{y}, {ys}]
accumulator[{xs__}, {y_, ys___}] := 
 accumulator[Append[{xs}, Last[{xs}] + y], {ys}]
accumulate[list_List] := accumulator[{}, list]

reverse[{}] := {}
reverse[{x_, xs___}] := Append[reverse[{xs}], x]

error[M_, d_Integer] := 
 accumulate[Reverse[var[pc[M]]]/Total[var[pc[M]]]][[d]]*)

(*------------------------------------------------------------------------------------------------*)
(*-----------------------------------------===( Misc )===-----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

Comment[comment_, lineWidth_] := Module[
	{line, separator, offsetLeft, offsetRight, leftHeader, rightHeader},
	line[len_] := StringJoin[Array["-" &, len]];
	separator = "\n(*" <> line[lineWidth - 4] <> "*)\n";
	offsetLeft = Round[lineWidth/2] - StringLength[comment]/2;
	leftHeader = "(*" <> line[offsetLeft - 7] <> "===( ";
	offsetRight = lineWidth - StringLength[leftHeader] - StringLength[comment];
	rightHeader = " )===" <> line[offsetRight - 7] <> "*)";
	StringJoin[{separator, leftHeader, comment, rightHeader, separator}]
]

CustomColor[i_] := {
	RGBColor[4/85, 6/17, 43/85],
	RGBColor[214/255, 74/255, 13/85],
	RGBColor[2/5, 203/255, 19/85],
	RGBColor[142/255, 173/255, 57/85],
	RGBColor[3/5, 52/255, 66/85],
	RGBColor[43/51, 224/255, 229/255]
	}[[i]]
	
(*------------------------------------------------------------------------------------------------*)
(*------------------------------------===( End of Package )===------------------------------------*)
(*------------------------------------------------------------------------------------------------*)
