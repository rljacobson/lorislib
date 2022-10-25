(* Loris Package *)

(* :Title: Simplification *)
(* :Context: Std`Simplification` *)
(* :Author: Robert Jacobson *)
(* :Date: 2022-10-21 *)

(* :Package Version: 0.1 *)
(* :Loris Version: 0.1.0 *)
(* :Copyright: (c) 2022 Robert Jacobson *)
(* :Keywords: simplify, simplification *)
(* :Discussion: A small collection of algebraic and trigonometric simplification rules. *)

(* For new style packages see: https://mathematica.stackexchange.com/a/176489) *)

Package["Std`Simplification`"]

(* Import other packages *)
PackageImport["Std`Definitions`"]

(*

ToDo: Write algebraic manipulation functions: Together, Apart, Collect, Factor, Cancel, Expand
Todo: Write advanced algebraic manipulation functions: Decompose, HornerForm, FactorList, PolynomialGCD,
      PolynomialQuotient, PolynomialRemainder, PolynomialReduce, …

*)


(*
  Automatic Simplification Rules
  Rules that should apply automatically every time.
*)
$AutomaticSimplificationDownValues = {
  Exp[1] :> E,
  Power[a_, 1] :> a,
  Ln[1] :> 0
};
$AutomaticSimplificationUpValues = {
  (* Basic Algebraic Rules *)
  Plus[x_ * a_ , y_ * b_, exp___] :> (a + b) * x + Plus[exp] /; And[SameQ[x, y], NumberQ[a], NumberQ[b]],
  (a_ * x__) / (b_ * y__) :> Times[x] / Times[y] /; SameQ[a, b],


  (* Logs and Exponentials *)
  a_^y_ * b_^z_ * exp___ :> a^(y + z) * Times[exp] /; SameQ[a, b],
  (* Note that we do not combine sums of Logs despite the above. *)
  (* Function Inverses *)
  a_^Log[b_, x_] :> x /; SameQ[a, b],
  Log[a_, b_^x_] :> x /; SameQ[a, b],
  (*  a_^Ln[x_] :> x^Ln[a] /; NumberQ[a]&&Not[NumberQ[x]],*)
  Log[a_, b_^x_] :> x /; SameQ[a, b],
  E^Ln[x_] :> x,
  Ln[E^x_] :> x,
  Ln[E] :> 1,

  (* Square root - Loris has no concept of roots being fractional exponents. *)
  Sqrt[x_^2] :> x /; x > 0, (* `X>0 ^= True` to take advantage of this. *)
  x_^y_ > 0 :> True /; NumberQ[y] && EvenQ[y],

  (* Trigonometric functions *)
  Sin[x_]^2 + Cos[y_]^2 :> 1 /; SameQ[x, y],
  1 - Sin[x_]^2 :> Cos[x]^2,
  1 - Cos[x_]^2 :> Sin[x]^2,
  Sec[x_]^2 - Tan[y_]^2 :> 1 /; SameQ[x, y],
  Tan[x_]^2 + 1 :> Sec[x]^2,
  Sec[x_]^2 - 1 :> Tan[x]^2,
  Csc[x_]^2 - Cot[y_]^2 :> 1 /; SameQ[x, y],
  Cot[x_]^2 + 1 :> Csc[x]^2,
  Csc[x_]^2 - 1 :> Cot[x]^2
};



(* Definitions *)

(*
Simplification Rules
Rules that go beyond the standard automatically applied rules. Each rule is two directional.
*)
$SimplifcationUpValues = {

  a_^f_ :> Exp[Ln[a]*f],
  Ln[a_*b__] :> Ln[a] + Ln[Times[b]],
  Ln[a_^x_]:>x*Ln[a],
  (a_^b_)^c_ :> a^(b*c)

};

