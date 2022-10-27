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

(*ReleaseHold[exp_] := exp/.{Hold[x_]->x};*)
(*SetAttributes[ReleaseHold, HoldAll];*)

FreeQ[exp1, exp2] := Not[OccursQ[exp1_, exp2_]];
SetAttributes[OccursQ, HoldAll];
SetAttributes[FreeQ, HoldAll];

NumberQ[n_]:=If[Head[n]===Real, True, If[Head[n]===Integer, True, False]];
Subtract[x_, rest_]:=Plus[x, Minus[rest]];

(* Basic Algebraic Rules *)
Plus[x___ * a_ , y___ * b_] ^:= (a + b) * Times[x] + Plus[exp] /; And[SameQ[x, y], NumberQ[a], NumberQ[b]]
(*Plus[x_ , y___ * b_] ^:= (1 + b) * x + Plus[exp] /; Or[And[SameQ[x, y], NumberQ[b]], And[SameQ[x, b], NumberQ[y]]];*)
(*(a_ * x__) / (b_ * y__) ^:= Times[x] / Times[y] /; SameQ[a, b];*)
(*a_ / (b_ * y__) ^:= 1 / Times[y] /; SameQ[a, b];*)
(*(a_ * x__) / (b_ ) ^:= Times[x] /; SameQ[a, b];*)

