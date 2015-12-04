(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype div tuple bigop ssralg poly polydiv finfun.
From mathcomp Require Import generic_quotient.

From Newtonsums Require Import auxresults valuation revpoly fraction.

(* This file gathers results on reverse of polynomial and fractions *)
(* to avoid cylic dependencies between revpoly.v and fraction.v *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Local Scope ring_scope.
Open Local Scope quotient_scope.

Reserved Notation "{ 'fracpoly' T }" (at level 0, format "{ 'fracpoly'  T }").
Reserved Notation "x %:F" (at level 2, format "x %:F").
Reserved Notation "p \FPo q" (at level 50, format "p  \FPo  q").

Section FracRev.

Variable (K : fieldType).

Lemma tofrac_revp (p : {poly K}) : 
  (revp p) %:F = (p %:F \FPo 'X^-1) * ('X  %:F ^+(size p).-1).
Proof.
have [peq0 | pN0] := boolP (p == 0).
move/eqP : peq0 => peq0 ; rewrite peq0 comp_fracpoly0 mul0r.
  apply/eqP; rewrite raddf_eq0 ?revp_eq0 //.
  exact: tofrac_inj.
rewrite comp_poly_XV revp_sumE mulr_suml rmorph_sum /=; apply: eq_bigr => i _.
rewrite tofrac_scale -mulrA; congr (_ * _); rewrite mulrC.
rewrite -exprB; last 2 first.
+ by rewrite -ltnS prednK // size_poly_gt0.
+ rewrite unitfE raddf_eq0 ?polyX_eq0 //.
  exact: tofrac_inj.
by rewrite -subn1 -addn1 subnDA rmorphX subnAC.
Qed.

Lemma tofracpolyXV_eq0 (p : {poly K}) : (p%:F \FPo 'X^-1 == 0) = (p == 0).
Proof.
rewrite -revp_eq0 -[RHS](rmorph_eq0 [injmorphism of @tofrac]) /=.
by rewrite tofrac_revp mulf_eq0 orbC expf_eq0 rmorph_eq0 polyX_eq0 andbF.
Qed.

Lemma fracpolyXV_eq0 (f : {fracpoly K}) :
    (f \FPo 'X^-1 == 0) = (f == 0).
Proof.
have [[p q] /= -> /andP [a_neq0 cpq]] := fracpolyE f.
rewrite comp_frac_frac // !mulf_eq0 !invr_eq0.
by rewrite !tofracpolyXV_eq0 !rmorph_eq0.
Qed.

Lemma nocomp_fracpolyXV (f : {fracpoly K}) : nocomp_fracpoly f 'X^-1 = false.
Proof.
have [->|f_neq0]:= eqVneq f 0; first by rewrite nocomp_polyF.
by apply/negP => /comp_fracpoly_dflt; apply/eqP; rewrite fracpolyXV_eq0.
Qed.

End FracRev.

