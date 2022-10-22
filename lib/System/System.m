(* Loris Package *)

(* :Title: System *)
(* :Context: System` *)
(* :Author: Robert Jacobson *)
(* :Date: 2022-10-21 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: 13.1 *)
(* :Copyright: (c) 2022 Robert Jacobson *)
(* :Keywords: *)
(* :Discussion: *)

(* For new style packages see: https://mathematica.stackexchange.com/a/176489) *)
(* Declare package context *)
Package["System`"]

(* Import other packages *)
PackageImport["GeneralUtilities`"]

(* Keep function package private *)
PackageScope["privateFunc"]
privateFunc[x_] := x^2;

(* Export functions *)
PackageExport["exportedFunc"]
exportedFunc[] := "Hello World";
