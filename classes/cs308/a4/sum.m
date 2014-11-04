(* ::Package:: *)

SetOptions[Streams["stdout"], FormatType->TextForm];
Timing[Sum[1.0 / i, {i, 10000000}]] //
	Print["sum = ", #2, " (computed in ", #1, " seconds)"]& @@ #&;
Quit[]
