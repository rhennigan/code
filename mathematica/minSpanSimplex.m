(* ::Package:: *)

<<"E:\\GDrive\\Projects\\pcdSimplification\\pcdSimplification.m"
Needs["ComputationalGeometry`"]
Needs["RLink`"];
UninstallR[];
InstallR["RHomeLocation" -> "E:\\Apps\\R\\R-2.14.0"];
REvaluate["library(diptest)"];
dip[data_]:=((REvaluate["dip.test"][data])[[1,2,1]]);
ClusterDipTest[cluster_]:=dip[cluster.GetPrincipalAxis[cluster]]

AverageClusterRadius[cluster_]:=Module[
{m},
m=Mean[cluster];
Mean[Norm[#-m]&/@cluster]
]

PContainmentRadius[cluster_,p_]:=Module[
{m},
m=Mean[cluster];
Quantile[Norm[#-m]&/@cluster,p,{{0, 0}, {0, 1}}]
]

Shift[cluster_]:=Module[{m=Mean[cluster]},#-m&/@cluster]

GetPrincipalAxis[cluster_]:=Module[
{dim,principalDimension,shift,initialDirection},
dim=Length[First[cluster]];
principalDimension=Last[Ordering[Variance[cluster]]];
shift=Shift[cluster];
initialDirection=IdentityMatrix[dim][[principalDimension]];
FixedPoint[Normalize[Total[shift.#*shift]]&,initialDirection,50]
]

SplitCluster[address_,cluster_]:=(
GetCluster[address]={};
{}
)/;Length[cluster]==0

SplitCluster[address_,{point_}]:=(
GetCluster[address]={point};
GetPoint[address]=point;
GetAddress[point]=address;
GetAddress[{point}]=address;
)

SplitCluster[address_,cluster_]:=Module[
{
mean,shift,principalComponents,
splitLocation,order,
leftIndex,rightIndex,
leftCluster,rightCluster,
leftAddress,rightAddress
},

GetCluster[address]=cluster;
GetAddress[cluster]=address;

(*principalComponents=PrincipalComponents[cluster];
order=Ordering[principalComponents\[LeftDoubleBracket]All,1\[RightDoubleBracket]];*)
mean=Mean[cluster];
shift=#-mean&/@cluster;
principalComponents=shift.GetPrincipalAxis[shift];
order=Ordering[principalComponents];

splitLocation=Ceiling[Length[cluster]/2];
(*order=Ordering[principalComponents\[LeftDoubleBracket]All,1\[RightDoubleBracket]];*)
(*order=Ordering[principalComponents];*)

leftIndex=order[[;;splitLocation]];
rightIndex=order[[splitLocation+1;;]];

leftCluster=cluster[[leftIndex]];
rightCluster=cluster[[rightIndex]];

leftAddress=address*2;
rightAddress=address*2+1;

If[address<1024,Sow[{AbsoluteTime[],address->{leftAddress,rightAddress}}]];

SplitCluster[leftAddress,leftCluster];
SplitCluster[rightAddress,rightCluster];
]/;Length[cluster]>1

SplitCluster[points_]:=(
Clear[GetPoint,GetAddress,GetCluster];
First[Last[Reap[SplitCluster[1,points]]]]
)

MakeClusters[depth_]:=Module[
{clusterIndex},
clusterIndex=Range[2^(depth),2^(depth+1)-1];
GetCluster/@clusterIndex
]

RefineClusters[{cluster1_,cluster2_}]:=Module[
{pt1,pt2,line,cp1,cp2,split1,split2},
pt1=Mean[cluster1];
pt2=Mean[cluster2];
Sow[{pt1,pt2}];
line=Normalize[pt2-pt1];
cp1=cluster1.line;
cp2=cluster2.line;
split1=Floor[Length[cluster1]/2];
split2=Ceiling[Length[cluster2]/2];
{
cluster1[[Ordering[cp1][[split1+1;;]]]],
cluster2[[Ordering[cp2][[;;split2]]]]
}
]

ClusterProjectionDistance[cluster1_,cluster2_]:=0/;cluster1==cluster2
ClusterProjectionDistance[cluster1_,cluster2_]:=Min[EuclideanDistance@@@First[Last[Reap[FixedPointList[RefineClusters,{cluster1,cluster2}]]]]]

MeanNormalize[cluster_]:=Module[
{center},
center=Mean[cluster];
#-center&/@cluster
]

TrueClusterDistance[cluster1_,cluster2_]:=Min[Table[EuclideanDistance[pt1,pt2],{pt1,cluster1},{pt2,cluster2}]]

RefineClustersC=Compile[{{clusters,_Real,3}},
Module[
{
cluster1,cluster2,
combined,center,
shiftedCluster1,shiftedCluster2,
pt1,pt2,
line,
cp1,cp2,cp1points,cp2points,
inner1,inner2,
axisDist1,axisDist2,
projError1,projError2,
error1,error2,
split1,split2
},

cluster1=clusters[[1]];
cluster2=clusters[[2]];

combined=Join[cluster1,cluster2];
center=Mean[combined];

shiftedCluster1=#-center&/@cluster1;
shiftedCluster2=#-center&/@cluster2;

pt1=Mean[shiftedCluster1];
pt2=Mean[shiftedCluster2];

line=Normalize[pt2-pt1];

cp1=shiftedCluster1.line;
cp2=shiftedCluster2.line;
cp1points=#*line&/@cp1;
cp2points=#*line&/@cp2;

inner1=Max[cp1];
inner2=Min[cp2];

axisDist1=Abs[cp1-inner1];
axisDist2=Abs[cp2-inner2];

projError1=Norm/@(shiftedCluster1-cp1points);
projError2=Norm/@(shiftedCluster2-cp2points);

error1=2.0axisDist1+projError1;
error2=2.0axisDist2+projError2;

split1=Ceiling[Length[cluster1]/2];
split2=Ceiling[Length[cluster2]/2];

{
cluster1[[Ordering[error1][[;;split1]]]],
cluster2[[Ordering[error2][[;;split2]]]]
}
]
];

ClusterProjectionDistanceC[cluster1_,cluster2_]:=Module[
{len1,len2,c1,c2,sequence,centroids},
{len1,len2}=Length/@{cluster1,cluster2};
{c1,c2}=If[len1==len2,{cluster1,cluster2},
RandomSample[#][[;;Min[{len1,len2}]]]&/@{cluster1,cluster2}
];
sequence=FixedPointList[RefineClustersC,{c1,c2}];
centroids=Map[Mean,sequence,{2}];
Min[EuclideanDistance@@@centroids]
]

SimplexContent[vertices_]:=Module[
{n,matrix,i,j},
n=Length[vertices]-1;
matrix=ReplacePart[
PadLeft[
Table[
Norm[vertices[[i]]-vertices[[j]]]^2,
{i,n+1},{j,n+1}
],{n+2,n+2},1
],{1,1}->0
];
Chop[Sqrt[((-1)^(n+1) Det[matrix])/(2^n (n!)^2)]]
]

RefineClustersGeneralC=Compile[{{clusters,_Real,3}},
Module[
{combined,center,shiftedClusters,pts,len},
combined=Flatten[clusters,1];
center=Mean[combined];
shiftedClusters=Map[#-center&,clusters,{2}];
pts=Mean/@shiftedClusters;
len=Length[clusters];
Table[
Module[
{pt1,pt2,line,cp,cpPoints,inner,axisDist,projError,error,split},
pt1=pts[[i]];
pt2=Mean[Delete[pts,i]];
line=Normalize[pt2-pt1];
cp=shiftedClusters[[i]].line;
cpPoints=#*line&/@cp;
inner=Max[cp];
axisDist=Abs[cp-inner];
projError=Norm/@(shiftedClusters[[i]]-cpPoints);
error=2.0axisDist+projError;
split=Ceiling[Length[clusters[[i]]]/2];
clusters[[i,Ordering[error][[;;split]]]]
],{i,len}]
]
];

RefineClustersGeneral[clusters_]:=Module[
{combined,center,shiftedClusters,pts,len},
combined=Flatten[clusters,1];
center=Mean[combined];
shiftedClusters=Map[#-center&,clusters,{2}];
pts=Mean/@shiftedClusters;
len=Length[clusters];
Table[
Module[
{pt1,pt2,line,cp,cpPoints,inner,axisDist,projError,error,split},
pt1=pts[[i]];
pt2=Mean[Delete[pts,i]];
line=Normalize[pt2-pt1];
cp=shiftedClusters[[i]].line;
cpPoints=#*line&/@cp;
inner=Max[cp];
axisDist=Abs[cp-inner];
projError=Norm/@(shiftedClusters[[i]]-cpPoints);
error=2.0axisDist+projError;
split=Ceiling[Length[clusters[[i]]]/2];
clusters[[i,Ordering[error][[;;split]]]]
],{i,len}]
]

SpanningSimplexSequenceC[clusters_]:=Module[
{len,c,sequence},
len=Length/@clusters;
c=If[Equal@@len,clusters,
RandomSample[#][[;;Min[len]]]&/@clusters
];
sequence=FixedPointList[RefineClustersGeneralC,c];
Map[Mean,sequence,{2}]
]

SpanningSimplexSequence[clusters_]:=Module[
{sequence},
sequence=FixedPointList[RefineClustersGeneral,clusters];
Map[Mean,sequence,{2}]
]

MinSpanningSimplexContent[clusters_]:=Module[
{d,scale},
d=Length[clusters];
scale=Sqrt[2^(-1+d)/d] Gamma[d];
scale*Min[SimplexContent/@SpanningSimplexSequence[clusters]]
]

MinSpanningSimplexContentFull[clusters_]:=Max[MinSpanningSimplexContent/@Subsets[clusters,{2,Infinity}]]

AverageClusterDiameter[cluster_]:=Module[
{n,m},
n=Length[cluster];
m=Mean[cluster];
Sqrt[2/n Total[Norm[#-m]^2&/@cluster]]
]

GetConvexHullVertices=#[[ConvexHull[#]]]&;

HullArea[hullVertices_]:=Module[
{center,triangles},
center=Mean[hullVertices];
triangles=Table[Prepend[RotateLeft[hullVertices,i][[1;;2]],center],{i,Length[hullVertices]}];
Total[SimplexContent/@triangles]
]

ClusterHullArea[cluster_]:=HullArea[GetConvexHullVertices[cluster]]

PrincipalAxisVariance[cluster_]:=Module[
{shift,principalAxis,projection},
shift=MeanNormalize[cluster];
principalAxis=GetPrincipalAxis[shift];
projection=shift.principalAxis;
Variance[projection]
]

PrincipalAxisMaxMin[cluster_]:=Module[
{shift,principalAxis,projection},
shift=MeanNormalize[cluster];
principalAxis=GetPrincipalAxis[shift];
projection=shift.principalAxis;
Max[projection]-Min[projection]
]

PrincipalAxisStdDev[cluster_]:=Module[
{shift,principalAxis,projection},
shift=MeanNormalize[cluster];
principalAxis=GetPrincipalAxis[shift];
projection=shift.principalAxis;
StandardDeviation[projection]
]

TotalClusterVariance[cluster_]:=Total[Variance[cluster]]/Length[cluster]

UpdateClusterVariance[points_]:=Module[
{fullClusterIndex},
fullClusterIndex=Range[Min[GetAddress/@points]-1];
Scan[(SavedClusterVariance[#]=TotalClusterVariance[GetCluster[#]])&,fullClusterIndex]
]

ClusterVarianceConsistency[point_,count_]:=Total[Abs[Differences[SavedClusterVariance/@ParentNodes[GetAddress[point],0,count]]]]

ClusterVarianceConsistency[point_]:=Total[Abs[Differences[SavedClusterVariance/@ParentNodes[GetAddress[point],0,Infinity]]]]

FilterOutliers[points_,p_]:=Module[
{cvc,sortedPts},
cvc=ClusterVarianceConsistency/@points;
sortedPts=points[[Ordering[cvc]]];
sortedPts[[;;Round[p*Length[sortedPts]]]]
]

FilterOutliers[points_,p_,count_]:=Module[
{cvc,sortedPts},
cvc=ClusterVarianceConsistency[#,count]&/@points;
sortedPts=points[[Ordering[cvc]]];
sortedPts[[;;Round[p*Length[sortedPts]]]]
]

GoUp[1]:=1
GoUp[address_]:=Floor[address/2]
GoDownL[address_]:=2address
GoDownR[address_]:=2address+1
Transfer[address_]:=GoDownL[GoUp[address]]/;OddQ[address]
Transfer[address_]:=GoDownR[GoUp[address]]/;EvenQ[address]
CurrentLevel[address_]:=Floor[Log[2,address]+1]

NextUp[address_]:=Transfer[GoUp[address]]

ParentNodes[address_]:=FixedPointList[GoUp,address][[2;;-2]]

ParentNodes[address_,offset_,count_]:=Module[
{nodes,lowLimit,highLimit,a,b},
nodes=FixedPointList[GoUp,address];
lowLimit=2;
highLimit=Length[nodes]-1;
a=Max[{1,Min[{lowLimit+offset,highLimit-2}]}];
b=Max[{a+1,Min[{a+count-1,highLimit}]}];
nodes[[a;;b]]
]

InitialSearchNodes[address_]:=Module[{parentNodePath=FixedPointList[GoUp,address]},
Reverse[Complement[FixedPointList[NextUp,Transfer[address]],parentNodePath]]]

UpdateDistance[address_,node_,distance_]:=(
DistanceTable[address,node]=distance;
)

(*SearchDown[address_]:=If[
CurrentLevel[address]<maxLevel,
Flatten[{address,SearchDown/@{GoDownL[address],GoDownR[address]}}],
address
]*)

SearchDown[address_,maxLevel_]:=If[
CurrentLevel[address]<maxLevel,
Flatten[{address,SearchDown[#,maxLevel]&/@{GoDownL[address],GoDownR[address]}}],
address
]

(*VisitNode[address_,node_]:=Module[
{distance},
distance=ClusterProjectionDistance[GetCluster[address],GetCluster[node]];
UpdateDistance[address,node,distance];
If[
DistanceTable[address,node]<maxDistance&&CurrentLevel[address]<maxLevel,
VisitNode[address,GoDownL[node]];
VisitNode[address,GoDownR[node]];,
UpdateDistance[address,#,distance]&/@SearchDown[node]
]
]*)

VisitNode[address_,node_,maxDistance_,maxLevel_]:=Module[
{distance},
distance=MinSpanningSimplexContent[{GetCluster[address],GetCluster[node]}];
UpdateDistance[address,node,distance];
If[
DistanceTable[address,node]<maxDistance&&CurrentLevel[address]<maxLevel,
VisitNode[address,GoDownL[node],maxDistance,maxLevel];
VisitNode[address,GoDownR[node],maxDistance,maxLevel];,
UpdateDistance[address,#,distance]&/@SearchDown[node,maxLevel]
]
]

GetMaxPersistenceRadius[filteredPoints_,scale_]:=Module[
{clusterDepth,bottomClusters,pairs,separations},
clusterDepth=CurrentLevel[Min[GetAddress/@filteredPoints]]-1;
bottomClusters={2^(clusterDepth-1),2^(clusterDepth)-1};
pairs=Table[{i,i+1},{i,bottomClusters[[1]],bottomClusters[[2]],2}];
separations=MinSpanningSimplexContentFull[GetCluster/@#]&/@pairs;
scale*Quantile[separations,.95]
]
