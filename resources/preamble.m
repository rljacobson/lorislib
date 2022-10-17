Condition[f_[x_, y_], z_]:=f_[x_, y_, z_];

(* Definitions *)
Subtract[x_, rest___]:=Plus[x_, Times[-1, Plus[rest___]]].
Sqrt[x_]:=Root[2, x_]; (* Poorly named, perhaps. *)
Ln[x_]:=Log[E, x_];
Exp[x_]:=Power[E, x_];

(* Simplifications *)
a_*x_ + b_*y_ ^:= (a_ + b_)*x_ /; And[SameQ[x_, y_], NumberQ[a_], NumberQ[b_]];
(a_*x_)/(b_*y_) ^:= a_ / b_ /; SameQ[x_, y_];

(* Differentiation *)
D[x_, y_] := 0 /; NumberQ[x_];                           (* Constants. No matching on `Head` *)
D[x_, y_] := 1 /; SameQ[x_, y_];                         (* Identity *)
D[x_^n_, y_] ^:= n*x_^(n-1)*D[x_, y_] /; Occurs[y_, x_]; (* Power Rule *)

D[Sin[x_], y_] ^:= Cos[x_]*D[x_, y_] /; Occurs[y_, x_];
D[Cos[x_], y_] ^:= -Sin[x_]*D[x_, y_] /; Occurs[y_, x_];
D[Tan[x_], y_] ^:= Sec[x_]^2*D[x_, y_] /; Occurs[y_, x_];
D[Sec[x_], y_] ^:= Sec[x_]*Tan[x_]*D[x_, y_] /; Occurs[y_, x_];
