(* Mathematica Package         *)
(* Created by IntelliJ IDEA    *)

(* :Title: testing     *)
(* :Context: testing`  *)
(* :Author: rhennigan            *)
(* :Date: 4/16/2015              *)

(* :Package Version: 1.0       *)
(* :Mathematica Version:       *)
(* :Copyright: (c) 2015 rhennigan *)
(* :Keywords:                  *)
(* :Discussion:                *)

BeginPackage["testing`"]
(* Exported symbols added here with SymbolName::usage *)

FactorExpression::usage = ""

Begin["`Private`"] (* Begin Private Context *)

inReals[exp_] := Module[
  {allSymbols, symbols, membership},
  allSymbols = Cases[exp, _Symbol, Infinity];
  symbols = Union[allSymbols];
  membership = Element[symbols, Reals];
  Return[membership];
]

simplify[exp_] := Module[
  {assumption, simplified},
  assumption = inReals[exp];
  simplified = Simplify[exp, assumption];
  Return[simplified];
]

commutativeSubsets[exp_] := Module[
  {productQ},
  productQ = Head[exp] === Times && Length[exp] > 2;
  If[productQ,
    Module[{subproductSets, subproducts},
      subproductSets = Subsets[List @@ exp, {2, Infinity}];
      subproducts = Times @@@ subproducts;
      Sow /@ subproducts
    ],
    Sow[exp]
  ];
  Return[exp];
]

mostRedundantFactor[exp_] := Module[
  {subexpressions, subexpressionCounts, factor, count},
  subexpressions = (First @* Last) @ Reap[Map[commutativeSubsets, exp, Infinity]];
  subexpressionCounts = Select[Tally[subexpressions], Depth[ #[[1]] ] > 1 &];
  {factor, count} = First[MaximalBy[subexpressionCounts, Last]];
  Return[{factor, count}];
]

factorExpression[exp_, varCount_] := Module[
  {factor, count, result},
  {factor, count} = mostRedundantFactor[exp];
  result = If[count > 1,
    Module[{newVar, newExp},
      newVar = Symbol["v" <> ToString[varCount + 1]];
      Sow[{newVar, factor}];
      newExp = exp /. factor -> newVar;
      factorExpression[newExp, varCount + 1]
    ],
    exp;
  ];
  Return[result];
]

factor[exp_, varCount_] := Module[
  {subexpression, count, newVar, newExp},
  {subexpression, count} = First[factorExp[exp]];
  If[count > 1,
    newVar = Symbol["v" <> ToString[varCount + 1]];
    Sow[{newVar, subexpression}];
    newExp = simp[exp /. subexpression -> newVar];
    factor[newExp, varCount + 1],
    exp
  ]
]
factor[exp_] := Reap[factor[exp, 0]]

FactorExpression[exp_] := factor[exp]

End[] (* End Private Context *)

EndPackage[]