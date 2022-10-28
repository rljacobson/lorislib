(*
Quick and dirty preamble until I bootstrap the module system. Very soon `*Values` will be "sorted" according to
generality to the extent that is possible. For now, we just have them manually in an order of increasing generality.
*)

(** Definitions **)

(* Applies f to a formal symbolic version of g and then evaluates the result at x. *)
(*SymbolicApply[f_, g_, x_]:=ReplaceAll[D[f[Hold[tmp]], Hold[tmp]], Hold[tmp]^:=g[x]];*)
(*SetAttributes[SymbolicApply, HoldAll];*)

(* Differentiation of pure functions. Sort of. Until we can have non-symbolic heads. *)
(*Derivative[f_, x_]:= SymbolicApply[f, D, Sequence[x, x]];*)
(*SetAttributes[Derivative, HoldAll];*)

(* Removes `Hold` from any held expressions. *)
ReleaseHold[exp_] := exp/.{Hold[x_]->x};
SetAttributes[ReleaseHold, HoldAll];

FreeQ[exp1_, exp2_] := Not[OccursQ[exp1, exp2]];
SetAttributes[FreeQ, HoldAll];

(*Ln[x_]:=Log[x];*)

NumberQ[n_]:=If[Head[n]==Real, True, If[Head[n]==Integer, True, False]];
Subtract[x_, rest_]:=Plus[x, Minus[rest]];
Sqrt[x_]:=Root[2, x]; (* Poorly named, perhaps.*)

Log[E, x_]^:=Ln[x]; (* Maybe these should be additional simplification rules? *)
Log[a_, x_]:=Ln[x]/Ln[a]; (* Maybe these should be additional simplification rules? Mathematica uses this definition. *)
Power[E, x_]^:=Exp[x];



(** Simplifcation **)

Exp[1] := E;
Power[a_, 1] := a;
Ln[1] := 0;
Ln[E] ^:= 1;

(* Basic Algebraic Rules *)
Plus[x_ * a_ , y_ * b_, exp___] ^:= (a + b) * x + Plus[exp] /; And[SameQ[x, y], NumberQ[a], NumberQ[b]];
Plus[x_ , y_ * b_, exp___] ^:= (1 + b) * x + Plus[exp] /; Or[And[SameQ[x, y], NumberQ[b]], And[SameQ[x, b], NumberQ[y]]];
(a_ * x__) / (b_ * y__) ^:= Times[x] / Times[y] /; SameQ[a, b];
a_ / (b_ * y__) ^:= 1 / Times[y] /; SameQ[a, b];
(a_ * x__) / (b_ ) ^:= Times[x] /; SameQ[a, b];

(* Logs and Exponentials *)
a_^y_ * b_^z_ * exp___ ^:= a^(y + z) * Times[exp] /; SameQ[a, b];
(* Note that we do not combine sums of Logs despite the above. *)
(* Function Inverses *)
a_^Log[b_, x_] ^:= x /; SameQ[a, b];
Log[a_, b_^x_] ^:= x /; SameQ[a, b];
(*  a_^Ln[x_] ^:= x^Ln[a] /; NumberQ[a]&&Not[NumberQ[x]],*)
E^Ln[x_] ^:= x;
Ln[E^x_] ^:= x;

(* Square root - Loris has no concept of roots being fractional exponents. *)
(*Sqrt[x_^2] ^:= x /; x > 0; *)(* `X>0 ^= True` to take advantage of this. *)
(*x_^y_ > 0 ^:= True /; NumberQ[y] && EvenQ[y];*)

(* Trigonometric functions *)
Sin[x_]^2 + Cos[y_]^2 ^:= 1 /; SameQ[x, y];
1 - Sin[x_]^2 ^:= Cos[x]^2;
1 - Cos[x_]^2 ^:= Sin[x]^2;
Sec[x_]^2 - Tan[y_]^2 ^:= 1 /; SameQ[x, y];
Tan[x_]^2 + 1 ^:= Sec[x]^2;
Sec[x_]^2 - 1 ^:= Tan[x]^2;
Csc[x_]^2 - Cot[y_]^2 ^:= 1 /; SameQ[x, y];
Cot[x_]^2 + 1 ^:= Csc[x]^2;
Csc[x_]^2 - 1 ^:= Cot[x]^2;

(* Logs and Exponentials *)
a_^f_ ^:= Exp[Ln[a]*f];
Ln[a_*b__] ^:= Ln[a] + Ln[Times[b]];
Ln[a_^x_]^:=x*Ln[a];
(a_^b_)^c_ ^:= a^(b*c); (*Note: `^` is right associative.*)


(** Differential Calculus **)

(* Freshman  Calculus *)
D[x_, y_] := 1 /; SameQ[x, y];
D[x_, y_] := 0 /; FreeQ[x, y];
(*
The Chain Rule is a down-value, because function composition is implicit. The problem is with functions of arity
greater than one. If the outer function is, for example, `Log[a, x]`, this pattern doesn't match. Of course, every
rule is already written  in terms of the Chain Rule, so this issue is moot.
*)
(*  D[f_[g_[x_]], y_] := Derivative[f, g[x]] * D[g[x], y] /; OccursQ[x, y] *)(* Chain Rule *)

D[x_^n_, y_] ^:= n*x^(n-1)*D[x, y] /; OccursQ[x, y] && FreeQ[n, y] && Not[n===0]; (*Power Rule*)
(*D[x_*y_*exp___, z_] ^:= x*D[y*exp, z] /; FreeQ[x, z], Folded into product rule *)(* Constant Multiple Rule *)
D[x_+y_+exp___, z_] ^:= D[x, z] + D[y + exp, z]; (* Linearity *)
D[x_*y_*exp___, z_] ^:= x*D[y*exp, z] + D[x, z]*y*exp; (* Product Rule *)
D[x_/y_, z_] ^:= (D[x, z]*y - x*D[y, z])/y^2 /;  OccursQ[y, z]; (* Quotient Rule *)
(* The Chain Rule is a down-value, because function composition is implicit. *)


(* Trig Functions *)
D[Sin[x_], y_] ^:= Cos[x]*D[x, y] /; OccursQ[x, y];
D[Cos[x_], y_] ^:= -Sin[x]*D[x, y] /; OccursQ[x, y];
D[Tan[x_], y_] ^:= Sec[x]^2*D[x, y] /; OccursQ[x, y];
D[Sec[x_], y_] ^:= Sec[x]*Tan[x]*D[x, y] /; OccursQ[x, y];

(* Logs and Exponentials *)
(*  Constant with a function in the exponent. *)
D[x_^y_, z_] ^:= x^y*Ln[x] /; FreeQ[x, z] && OccursQ[y, z];
(* Exp is defined as its own function, and x^y is not automatically converted. *)
D[Exp[x_], y_] ^:= Exp[x]*D[x, y] /; OccursQ[x, y];

(* Function  with a function in the exponent. Needed because x^y is not automatically converted to Exp[Ln[x]*y]. *)
(*x^y*((y*D[x, z])/x + Ln[x]*D[y, z]) /; OccursQ[y, z] && OccursQ[x, z],*)
D[x_^y_, z_] ^:= D[Exp[Ln[x]*y], z] /; OccursQ[x, z] && OccursQ[y, z];
(* Natural log. *)
D[Ln[x_], y_] ^:= D[x, y]/x /; OccursQ[x, y]
(*
Log of a function with a function in the base. -- This case is automatically converted to Quotient Rule on
Ln[y]/Ln[x].
D[Log[x_, y_], z_] ^:= -((Ln[y]*D[x,z])/(Ln[x]^2*x)) + D[y, z]/(Ln[x]*y) /; OccursQ[y, z] && OccursQ[x, z]
*)



(* MAKE SURE THE SCRIPT DOES NOT END IN A SEMICOLON. *)
