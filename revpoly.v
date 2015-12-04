(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  Theory of reverse polynomial and relation to roots and multiplicity.     *)
(*****************************************************************************)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype finset finfun.
From mathcomp
Require Import div tuple finfun bigop ssralg poly polydiv zmodp.
From Newtonsums Require Import auxresults valuation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "p \FPo q" (at level 50, format "p  \FPo  q").
Local Notation "p ^ f" := (map_poly f p).

Definition revp (R : ringType) (p : {poly R}) := Poly (rev p).

Hint Resolve valp_leq.


Section RevPoly.

Variable (R : ringType).
Implicit Types (p q : {poly R}).

Lemma size_revp_leq p : size (revp p) <= size p.
Proof. by rewrite -[size p]size_rev size_Poly. Qed.
Hint Resolve size_revp_leq.

Lemma coef_revp p n : n < size p -> (revp p)`_n = p`_(size p - n.+1).
Proof. by move=> n_small; rewrite coef_Poly nth_rev. Qed.

Lemma revpE p : revp p = \poly_(i < size p - valp p) p`_(size p - i.+1).
Proof.
apply/polyP=> i; have [i_sm|i_big] := ltnP i (size p); last first.
  rewrite !nth_default // ?(leq_trans _ i_big) //.
  by rewrite (leq_trans (size_poly _ _)) ?leq_subr.
rewrite coef_poly leq_leq_subCr // coef_revp //.
by case: ltnP => // /valp_coef_eq0.
Qed.

Lemma revpEsizep p : revp p = \poly_(i < size p) p`_(size p - i.+1).
Proof.
rewrite poly_def [RHS](bigID (fun i : 'I__ => i < size p - valp p)) /=.
rewrite big_ord_narrow ?leq_subr //= addrC big1 ?add0r ?revpE ?poly_def //.
move=> i; rewrite -leqNgt -ltnS leq_ltn_subCl // => /valp_coef_eq0 ->.
by rewrite scale0r.
Qed.

Lemma revp0 : revp 0 = 0 :> {poly R}.
Proof. by rewrite revpE size_poly0 valp0 subnn poly_def big_ord0. Qed.

Lemma size_revp p : size (revp p) = (size p - valp p)%N.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite revp0 size_poly0 valp0.
rewrite revpE size_poly_eq // prednK ?subn_gt0 ?valp_small // ?subKn //.
by rewrite coef_valp_neq0.
Qed.

Lemma revp_eq0 p : (revp p == 0) = (p == 0).
Proof.
by rewrite -size_poly_eq0 size_revp subn_eq0 (geq_leqif (valp_leqif _)).
Qed.

Lemma lead_coef_revp p : lead_coef (revp p) = p`_(valp p).
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite revp0 coef0 lead_coef0.
rewrite revpE lead_coef_poly ?prednK ?subn_gt0 ?valp_small // ?subKn //.
by rewrite coef_valp_neq0.
Qed.

Lemma size_revp_eq0 p : (size (revp p) == 0%N) = (p == 0).
Proof. by rewrite size_revp subn_eq0 (geq_leqif (valp_leqif _)). Qed.

Definition c0N0 := [qualify p : {poly R} | p`_0 != 0].

Lemma c0N0_neq0 : {in c0N0, forall p, p != 0}.
Proof. by move=> p; apply: contraNneq => ->; rewrite coef0. Qed.

Lemma coef0_revp p : (revp p)`_0 = lead_coef p.
Proof. by rewrite coef_Poly nth0 /lead_coef nth_last head_rev. Qed.

Lemma coef0_revp_eq0 p :((revp p)`_0 == 0) = (p == 0).
Proof. by rewrite coef0_revp lead_coef_eq0. Qed.

Lemma c0N0_size_revp : {in c0N0, forall p, size (revp p) = size p}.
Proof. by move=> p p_c0N0; rewrite size_revp valp_eq0 // subn0. Qed.

Lemma valp_rev p : valp (revp p) = 0%N.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite revp0 valp0.
by rewrite valp_eq0 // coef0_revp_eq0.
Qed.

Lemma revp_involutive : {in c0N0, involutive (@revp R)}.
Proof.
by move=> p ?; rewrite /revp (@PolyK _ 0) ?last_rev -?nth0 // revK polyseqK.
Qed.

Fact revp_proof (p : {poly R}) : size (revp p) <= size p.
Proof. by rewrite size_revp leq_subLR leq_addl. Qed.

Lemma revpMXn p (n : nat) : revp (p * 'X^n) = revp p.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite mul0r.
rewrite !revpE size_polyMXn //= valpMXn // subnDr.
rewrite !poly_def; apply: eq_bigr => /= i _; congr (_ *: _).
rewrite coefMXn ifF -?subnDA ?subnDr // addnC -addnBA -?ltn_subRL ?subnn //.
by rewrite (leq_trans (ltn_ord i)) // ?leq_subr.
Qed.

Lemma revpMX p (n : nat) : revp (p * 'X) = revp p.
Proof. by rewrite -['X]expr1 revpMXn. Qed.

Lemma revp_sumE p : revp p = \sum_(j < size p) p`_j *: 'X^(size p - j.+1).
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite revp0 size_poly0 big_ord0.
rewrite revpEsizep poly_def (reindex_inj rev_ord_inj) /=.
by apply: eq_bigr => //= i i_small; rewrite subnS subnBA // addnC addnK.
Qed.

Lemma size_revp_leqif p : size (revp p) <= size p ?= iff (valp p == 0%N).
Proof.
apply/leqifP; rewrite size_revp.
have [->|vp_gt0] := posnP; first by rewrite subn0.
by rewrite leq_ltn_subCl // subnn.
Qed.

End RevPoly.

Section MoreRevPoly.

Lemma revp_map_id0 (R R' : ringType) (f : R -> R') (p : {poly R}) :
 f 0 = 0 -> f (lead_coef p) != 0 -> revp (p ^ f) = (revp p) ^ f.
Proof.
move=> f0_eq0 f_lc_neq0; rewrite !revpEsizep size_map_poly_id0 //.
by apply/polyP=> i; rewrite ?(coef_map_id0, coef_poly) //; case: ifP.
Qed.

Lemma revp_inj_map (R R' : ringType) (f : R -> R') (p : {poly R}) :
  injective f -> f 0 = 0 -> revp (p ^ f) = (revp p) ^ f.
Proof.
have [->|p_eq0] := eqVneq p 0; first by rewrite !(map_poly0, revp0).
move=> f_inj f0_eq0; apply: revp_map_id0 => //.
by rewrite -f0_eq0 inj_eq // lead_coef_eq0.
Qed.

Lemma revp_map (R R' : ringType) (f : {injmorphism R -> R'}) (p : {poly R}) :
  revp (p ^ f) = (revp p) ^ f.
Proof. by rewrite revp_inj_map // rmorph0. Qed.

Lemma revpZ_id0 (R : ringType) (p : {poly R}) (c : R) :
  c * lead_coef p != 0 -> revp (c *: p) = c *: (revp p).
Proof.
move=> cpN0; have [->|cN0] := eqVneq c 0; first by rewrite !scale0r revp0.
by rewrite -!map_poly_mul revp_map_id0 ?mulr0.
Qed.

Lemma revpZ (R : idomainType) (p : {poly R}) (c : R) :
  revp (c *: p) = c *: (revp p).
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite ?(scaler0, revp0).
have [->|cN0] := eqVneq c 0; first by rewrite !scale0r revp0.
by rewrite revpZ_id0 // mulf_neq0 // ?lead_coef_eq0.
Qed.

Lemma rev_monicZ (R : ringType) (p : {poly R}) (c : R) :
  p \is monic -> revp (c *: p) = c *: (revp p).
Proof.
have [->|cN0] := eqVneq c 0; first by rewrite !scale0r revp0.
by move=> p_monic; rewrite revpZ_id0 // (monicP p_monic) mulr1.
Qed.

Lemma revpM_id0 (R : ringType) (p q : {poly R}) :
  (lead_coef p) * (lead_coef q) != 0 ->
  revp (p * q) = (revp p) * (revp q).
Proof.
have [|m {p} p pN0 p0N0] := valpXP p; first by rewrite ?(revp0, mul0r).
have [|n {q} q qN0 q0N0] := valpXP q; first by rewrite ?(revp0, mulr0).
rewrite !lead_coefMXn => lplq_neq0.
rewrite mulrA -[p * _ * _]mulrA -commr_polyXn mulrA -mulrA -exprD !revpMXn.
apply/polyP => i; have [i_small|i_big] := ltnP i (size (p * q)); last first.
  rewrite !nth_default ?(leq_trans (size_revp_leq _)) //.
  rewrite (leq_trans (size_mul_leq _ _)) // (leq_trans _ i_big) //.
  rewrite size_proper_mul // -ltnS.
  rewrite !prednK ?addn_gt0 ?lt0n ?size_revp_eq0 ?size_poly_eq0 ?pN0 //.
  by rewrite !c0N0_size_revp //.
rewrite coef_revp // !coefMD !c0N0_size_revp //.
rewrite (reindex_inj rev_ord_inj); apply: eq_bigr => j _.
rewrite (reindex_inj rev_ord_inj); apply: eq_big => [k|k _]; last first.
  by rewrite !coef_revp.
rewrite -(inj_eq (@addnI (j.+1 + k.+1)%N)) addnACA !subnKC // eq_sym.
rewrite -(inj_eq (@addIn i.+1)) -addnA subnK //addnC.
rewrite !(addnS, addSn) -addSn eqSS size_proper_mul //.
by rewrite prednK ?addn_gt0 ?size_poly_gt0 ?pN0 // (inj_eq (@addnI _)).
Qed.

Lemma revpM (R : idomainType) (p q : {poly R}) :
  revp (p * q) = (revp p) * (revp q).
Proof.
have [->|pN0] := eqVneq p 0; first by rewrite !(revp0, mul0r).
have [->|qN0] := eqVneq q 0; first by rewrite !(revp0, mulr0).
by rewrite revpM_id0 // mulf_neq0 ?lead_coef_eq0.
Qed.

End MoreRevPoly.





