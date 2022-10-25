(* Loris Package *)

(* :Title: Integration *)
(* :Context: Std`Integration` *)
(* :Author: Robert Jacobson *)
(* :Date: 2022-10-21 *)

(* :Package Version: 0.1 *)
(* :Loris Version: 0.1.0 *)
(* :Copyright: (c) 2022 Robert Jacobson *)
(* :Keywords: calculus, integration, integral *)
(* :Discussion: A small collection of algebraic and trigonometric integration rules. Very simple integration of
polynomials and Taylor series. *)



Package["Std`Integration`"]

(* Export functions *)
PackageExport["Series"]
PackageExport["Integrate"]
PackageExport["O"]

$IntegrationUpValues = {
  Integrate[O[n_], x_] :> O[n+1] /; FreeQ[n, x],
  Integrate[x_^n_*exp___, y_] :> x^(n+1)/(n+1)*exp /; SameQ[x, y] && FreeQ[exp, y] && FreeQ[n, y],
  Integrate[x_ + y__, z_] :> Integrate[x, z] + Integrate[Plus[y], z]
};

(*Series[f_, {x_, c_, n_}]:= Built-in*)
