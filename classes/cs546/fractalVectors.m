(* ::Package:: *)

(* ::Input:: *)
(*points=RandomReal[{-1,1},{4,2}];*)
(*first=First[points];*)
(*last=Last[points];*)
(*segment=RandomReal[{-10,10},{2,2}];*)
(*Graphics[{*)
(*Opacity[.5],Gray,Line[points],*)
(*Opacity[1],*)
(*Red,Point[first],*)
(*Green,Point[last],*)
(*Blue,Line[segment]*)
(*}]*)


(* ::Input:: *)
(*segment={{200,50},{50,310}}//N;*)
(*points={{50,200},*)
(*{150,200},*)
(*{200,113},*)
(*{250,200},*)
(*{350,200}}//N;*)


(* ::Input:: *)
(*first=First[points]*)
(*last=Last[points]*)
(*Graphics[{*)
(*Opacity[.5],Gray,Line[points],*)
(*Opacity[1],*)
(*Red,Point[first],*)
(*Green,Point[last],*)
(*Blue,Line[segment]*)
(*}]*)


(* ::Input:: *)
(*12*1.2*)


(* ::Input:: *)
(*segmentDistance=EuclideanDistance@@segment*)


(* ::Input:: *)
(*polyLineDistance=EuclideanDistance@@{First[points],Last[points]}*)


(* ::Input:: *)
(*Graphics[Point[#-first&/@points]]*)


(* ::Input:: *)
(*scaledPoints=segmentDistance/polyLineDistance*(#-first)&/@points*)


(* ::Input:: *)
(*scaledPoints=segmentDistance*Normalize[#-first]&/@points*)


(* ::Input:: *)
(*u=Last[scaledPoints]-First[scaledPoints]*)
(*v=Last[segment]-First[segment]*)


(* ::Input:: *)
(*theta=ArcCos[u.v/(Norm[u]Norm[v])]*)


(* ::Input:: *)
(*rotate[{x_,y_},t_]:={x Cos[t]-y Sin[t],y Cos[t]+x Sin[t]}*)


(* ::Input:: *)
(*Norm[rotate[Last[scaledPoints],theta]-v]*)


(* ::Input:: *)
(*Norm[rotate[Last[scaledPoints],-theta]-v]*)


(* ::Input:: *)
(*If[*)
(*Norm[rotate[Last[scaledPoints],theta]-v]>Norm[rotate[Last[scaledPoints],-theta]-v],*)
(*theta=-theta*)
(*]*)


(* ::Input:: *)
(*rotatedPoints=rotate[#,theta]&/@scaledPoints*)


(* ::Input:: *)
(*translatedPoints=#+First[segment]&/@rotatedPoints*)


(* ::Input:: *)
(*Graphics[Point[translatedPoints]]*)


(* ::Input:: *)
(*Graphics[{*)
(*Opacity[.5],Gray,Line[translatedPoints],*)
(*Opacity[1],*)
(*Red,Point[First[translatedPoints]],*)
(*Green,Point[Last[translatedPoints]],*)
(*Orange,PointSize[Large],Point[translatedPoints],,*)
(*Blue,Line[segment]*)
(*}]*)


(* ::Input:: *)
(*rotate[{300,0},60Degree]+{50,100}//N*)


(* ::Input:: *)
(*173*2*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*rotate[{100,0},60Degree]//N*)


(* ::Input:: *)
(*200-87*)


(* ::Input:: *)
(*Graphics[*)
(*{*)
(*Red,Arrow[{{200,50},{50,310}}],*)
(*Green,Arrow[{{50,310},{350,310}}],*)
(*Blue,Arrow[{{350,310},{0,0}}]*)
(*}*)
(*]*)


(* ::Input:: *)
(*List@@@MyColors/@Range[6]*255*)
