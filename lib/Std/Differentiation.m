(* Loris Package *)

(* :Title: Differentiation *)
(* :Context: Differentiation` *)
(* :Author: Robert Jacobson *)
(* :Date: 2022-10-23 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: 13.1 *)
(* :Copyright: (c) 2022 Robert Jacobson *)
(* :Keywords: *)
(* :Discussion: *)

(* For new style packages see: https://mathematica.stackexchange.com/a/176489) *)

Package["Std`Differentiation`"]

(* Import other packages *)
PackageImport["Std`Definitions`"]


(* Differentiation of pure functions. Sort of. Until we can have non-symbolic heads. *)
Derivative[f_, x_]:= SymbolicApply[f, D, Sequence[x, x]];
SetAttributes[Derivative, HoldAll];


$DifferentiationDownValues = {
  (* Freshman  Calculus *)
  D[x_, y_] :> 0 /; FreeQ[x, y]
  (*
  The Chain Rule is a down-value, because function composition is implicit. The problem is with functions of arity
  greater than one. If the outer function is, for example, `Log[a, x]`, this pattern doesn't match. Of course, every
  rule is already written  in terms of the Chain Rule, so this issue is moot.
  *)
(*  D[f_[g_[x_]], y_] :> Derivative[f, g[x]] * D[g[x], y] /; OccursQ[x, y] *)(* Chain Rule *)

};

$DifferentiationUpValues = {
  (* Freshman  Calculus *)
  D[x_^n_, y_] :> n*x_^(n-1)*D[x, y] /; OccursQ[x, y] && FreeQ[n, y] && Not[n===0], (*Power Rule*)
  (*D[x_*y_*exp___, z_] :> x*D[y*exp, z] /; FreeQ[x, z], Folded into product rule *)(* Constant Multiple Rule *)
  D[x_+y_+exp___, z_] :> D[x, z] + D[y + exp, z], (* Linearity *)
  D[x_*y_*exp___, z_] :> x*D[y*exp, z] + D[x, z]*y*exp, (* Product Rule *)
  D[x_/y_, z_] :> (D[x, z]*y - x*D[y, z])/y^2 /;  OccursQ[y, z], (* Quotient Rule *)
  (* The Chain Rule is a down-value, because function composition is implicit. *)


  (* Trig Functions *)
  D[Sin[x_], y_] :> Cos[x]*D[x, y] /; OccursQ[x, y],
  D[Cos[x_], y_] :> -Sin[x]*D[x, y] /; OccursQ[x, y],
  D[Tan[x_], y_] :> Sec[x]^2*D[x, y] /; OccursQ[x, y],
  D[Sec[x_], y_] :> Sec[x]*Tan[x]*D[x, y] /; OccursQ[x, y],

  (* Logs and Exponentials *)
  (*  Constant with a function in the exponent. *)
  D[x_^y_, z_] :> x^y*Ln[x] /; FreeQ[x, z] && OccursQ[y, z],
  (* Exp is defined as its own function, and x^y is not automatically converted. *)
  D[Exp[x_], y_] :> Exp[x]*D[x, y] /; OccursQ[x, y],

  (* Function  with a function in the exponent. Needed because x^y is not automatically converted to Exp[Ln[x]*y]. *)
  (*x^y*((y*D[x, z])/x + Ln[x]*D[y, z]) /; OccursQ[y, z] && OccursQ[x, z],*)
  D[x_^y_, z_] :> D[Exp[Ln[x]*y], z] /; OccursQ[x, z] && OccursQ[y, z],
  (* Natural log. *)
  D[Ln[x_], y_] :> D[x, y]/x /; OccursQ[x, y]
  (*
  Log of a function with a function in the base. -- This case is automatically converted to Quotient Rule on
  Ln[y]/Ln[x].
  D[Log[x_, y_], z_] :> -((Ln[y]*D[x,z])/(Ln[x]^2*x)) + D[y, z]/(Ln[x]*y) /; OccursQ[y, z] && OccursQ[x, z]
  *)

};
