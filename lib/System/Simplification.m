(* Loris Language Package *)

(* :Title: Simplification *)
(* :Context: Simplification` *)
(* :Author: Robert Jacobson *)
(* :Date: 2022-10-21 *)

(* :Package Version: 0.1 *)
(* :Loris Version: 0.1.0 *)
(* :Copyright: (c) 2022 Robert Jacobson *)
(* :Keywords: simplify, simplification *)
(* :Discussion: A small collection of algebraic and trigonometric simplification rules. *)

(* For new style packages see: https://mathematica.stackexchange.com/a/176489) *)
(* Declare package context *)
Package["System`"]

(* Import other packages *)
(*PackageImport["GeneralUtilities`"]*)

(* Keep function package private *)
PackageScope["simplifyRules"]
simplifyRules = {

};

UpSetDelayed[Plus[Times[a_, x_], Times[b_, y_]], Times[Plus[a, b], x_], And[SameQ[x, y], NumberQ[a], NumberQ[b]]];


(* Export functions *)
PackageExport["Simplify"]
Simplify[exp_] := "Hello World";
