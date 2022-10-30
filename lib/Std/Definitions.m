(* Loris Package *)

(* :Title: Definitions *)
(* :Context: Std`Definitions` *)
(* :Author: Robert Jacobson *)
(* :Date: 2022-10-23 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: 13.1 *)
(* :Copyright: (c) 2022 Robert Jacobson *)
(* :Keywords: *)
(* :Discussion: *)


Package["Std`Definitions`"]

PackageExport["ReleaseHold"]
PackageExport["SymbolicApply"]
PackageExport["OccursQ"]
(* For benefit of WL IntelliJ plugin only. *)
PackageExport["Ln"]

SetAttributes[ESimpleExamples]  = {HoldAll};
SetAttributes[EFurtherExamples] = {HoldAll};
SetAttributes[EKnownFailures]   = {HoldAll};

(* Applies f to a formal symbolic version of g and then evaluates the result at x. *)
SymbolicApply[f_, g_, x_]:=ReplaceAll[D[f[Hold[tmp]], Hold[tmp]], Hold[tmp]:>g[x]];
SetAttributes[SymbolicApply, HoldAll];

(* Removes `Hold` from any held expressions. *)
ReleaseHold[exp_] := exp/.{Hold[x_]->x};
SetAttributes[ReleaseHold, HoldAll];

OccursQ[exp1_, exp2_] := Not[FreeQ[exp1, exp2]];
SetAttributes[OccursQ, HoldAll];

(*Ln[x_]:=Log[x]*)

(*Todo: SetAttributes for these.*)
NumberQ[n_]:=If[Head[n]==Real, True, If[Head[n]==Integer, True, False]];
Subtract[x_, rest_]:=Plus[x, Minus[rest]];
Sqrt[x_]:=Root[2, x]; (* Poorly named, perhaps.*)

Log[E, x_]^:=Ln[x]; (* Maybe these should be additional simplification rules? *)
Log[a_, x_]:=Ln[x]/Ln[a]; (* Maybe these should be additional simplification rules? Mathematica uses this definition. *)
Power[E, x_]^:=Exp[x];
