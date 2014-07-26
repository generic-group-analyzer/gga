(*s Some routines for unbounded verification of signatures *)

(*i*)
open Util
(*i*)

type dbidx = int

type query_idx = int

type var =
  | RVar   of string
  | IRVar  of string * dbidx
  | Coeff  of string
  | ICoeff of string * dbidx
  | Poly   of string
  | IPoly  of string * dbidx

let pp_var fmt v =
  match v with
  | RVar  s     -> F.fprintf fmt "%s" s
  | IRVar(s,i)  -> F.fprintf fmt "%s_{i_%i}" s i
  | Coeff(s)    -> F.fprintf fmt "\\alpha^{%s}" s
  | ICoeff(s,i) -> F.fprintf fmt "\\alpha^{%s}_{i%i}" s i
  | Poly(s)     -> F.fprintf fmt "%s" s
  | IPoly(s,i)  -> F.fprintf fmt "%s_{i%i}" s i


type term =
  | Prod of term * term
  | Sum of dbidx list * term
  | Add of term * term
  | Var of var

let test () =
  let v = Coeff("m") in
  output_file "test.md" (fsprintf "\\\\(%a\\\\)\n" pp_var v)
