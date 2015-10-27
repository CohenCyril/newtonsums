(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  Theory of reverse polynomial and relation to roots and multiplicity.     *)
(*****************************************************************************)

(* From Ssreflect Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From MathComp Require Import div tuple finfun bigop ssralg poly polydiv.
From Newtonsums Require Import auxresults. *)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype finset finfun.
From mathcomp
Require Import  div tuple finfun bigop ssralg poly polydiv zmodp.
From Newtonsums Require Import auxresults.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Local Notation "p ^ f" := (map_poly f p).

Definition revp (R : ringType) (p : {poly R}) := Poly (rev p).

Section Valuation.

Variable (R : ringType).
Implicit Types (p : {poly R}).

Definition valp p : nat :=
  if size p is n.+1 then [arg min_(i < (ord_max : 'I_n.+1) | p`_i != 0) i]
  else 0%N.

Lemma valp_small p : p != 0 -> valp p < size p.
Proof. by rewrite -size_poly_gt0 /valp; case: size. Qed.

CoInductive valp_spec p : nat -> Prop :=
| ValpSpec0 of p = 0 : valp_spec p 0
| ValpSpecN0 n of p != 0 & p`_n != 0
  & (forall m, m < n -> p`_m = 0) : valp_spec p n.

Lemma valpP p : valp_spec p (valp p).
Proof.
rewrite /valp; case size_p: size => [|m].
  by constructor; apply/size_poly_leq0P; rewrite size_p.
have p_neq0 : p != 0  by rewrite -size_poly_eq0 size_p.
have [|/= i pi_neq0 i_min] := arg_minP.
  by rewrite /= -[m]/m.+1.-1 -size_p -lead_coefE lead_coef_eq0.
constructor => // k; rewrite ltnNge; apply/contraNeq.
have [k_small|k_big] := ltnP k m.+1; last first.
  by rewrite nth_default ?eqxx // size_p.
by move=> /(i_min (Ordinal k_small)).
Qed.

Lemma valp0 : valp 0 = 0%N.
Proof. by case: valpP => // n; rewrite coef0 eqxx. Qed.

Lemma valp_eqn n p : p`_n != 0 -> (forall m, m < n -> p`_m = 0) -> valp p = n.
Proof.
move=> pn_neq0 n_min; have [p_eq0|n' p_neq0 pn'_neq0 n'_min] := valpP.
  by rewrite p_eq0 coef0 eqxx in pn_neq0.
have [/n_min /eqP /negPn|/n'_min /eqP /negPn|//] := ltngtP n' n;
by rewrite ?pn_neq0 ?pn'_neq0.
Qed.

Lemma valp_coef_eq0 p n : n < valp p -> p`_n = 0.
Proof. by case: valpP => // m ? pm_neq0 m_small /m_small. Qed.

Lemma valp_eq0E p : p != 0 -> (valp p == 0%N) = (p`_0 != 0).
Proof.
case: valpP => [->|[|n] p_neq0 pn_neq0 n_min _]; first by rewrite !eqxx.
  by rewrite eqxx pn_neq0.
by rewrite n_min ?eqxx.
Qed.

Lemma valp_eq0 p : p`_0 != 0 -> valp p = 0%N.
Proof. by move=> /valp_eqn ->. Qed.

Lemma coef_valp_neq0 p : p != 0 -> p`_(valp p) != 0.
Proof. by case: valpP => // ->; rewrite eqxx. Qed.

Lemma valp_leq p : valp p <= size p.
Proof.
case: valpP => //= n ? pn_neq0 _; rewrite leqNgt.
by apply: contra pn_neq0 => ?; rewrite nth_default // ltnW.
Qed.

Lemma valp_leqif p : valp p <= size p ?= iff (p == 0).
Proof.
apply/leqifP; have [->|p_neq0] := altP eqP; first by rewrite valp0 size_poly0.
by rewrite valp_small.
Qed.

Lemma valpC c : valp c%:P = 0%N.
Proof. by have [->|?] := altP (c =P 0); rewrite ?valp0 ?valp_eq0 ?coefC. Qed.

Lemma valpMXn p n : p != 0 -> valp (p * 'X^n) = (valp p + n)%N.
Proof.
move=> p_neq0; apply: valp_eqn=> [|m m_small]; rewrite coefMXn ?addnK.
  by rewrite addnC -ltn_subRL subnn /= coef_valp_neq0.
by have [//|le_nm] := ltnP m n; rewrite valp_coef_eq0 ?leq_ltn_subLR // addnC.
Qed.

Lemma valpXn n : valp 'X^n = n.
Proof. by rewrite -['X^n]mul1r valpMXn ?oner_eq0 ?valpC. Qed.

CoInductive valpXn_spec p : {poly R} -> nat -> Prop :=
| ValpSpecXn0 : valpXn_spec p 0 0
| ValpSpecXnN0 n (q : {poly R}) of q != 0 & q`_0 != 0 :
    valpXn_spec p (q * 'X^n) n.

Lemma valpXP p : valpXn_spec p p (valp p).
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite valp0; constructor.
pose q := (\poly_(i < size p) p`_(i + valp p)).
have q0N0 : q`_0 != 0 by rewrite coef_poly size_poly_gt0 p_neq0 coef_valp_neq0.
have q_neq0 : q != 0 by apply: contraNneq q0N0 => ->; rewrite coef0.
suff {2}-> : p = q * 'X^(valp p) by constructor.
apply/polyP => i; rewrite coefMXn; have [i_small|i_inter] := ltnP.
  by rewrite valp_coef_eq0.
rewrite coef_poly ?subnK //; case: ltnP => //= i_big.
by rewrite nth_default // (leq_trans i_big) ?leq_subr.
Qed.

Lemma valpM_id0 (p q : {poly R}) : p`_(valp p) * q`_(valp q) != 0 ->
                  valp (p * q) = (valp p + valp q)%N.
Proof.
case: valpXP=> [|m {p} p pN0 p0N0]; rewrite ?coef0 ?(mulr0, mul0r) ?eqxx //.
case: valpXP=> [|n {q} q qN0 q0N0]; rewrite ?coef0 ?(mulr0, mul0r) ?eqxx //.
rewrite !coefMXn ?ltnn ?subnn -coef0M => p0q0_neq0.
have pq_neq : p * q != 0 by apply: contraNneq p0q0_neq0 => ->; rewrite coef0.
rewrite mulrA -[(p * _ * _)]mulrA -commr_polyXn mulrA -mulrA -exprD.
by rewrite valpMXn // valp_eq0.
Qed.

Lemma valpN p : valp (- p) = valp p.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite oppr0.
apply: valp_eqn=> [|m]; rewrite coefN ?oppr_eq0 ?coef_valp_neq0 //.
by move=> /valp_coef_eq0 ->; rewrite oppr0.
Qed.

Lemma leqif_valpD (p q : {poly R}) : p != 0 -> q != 0 -> p + q != 0 ->
  minn (valp p) (valp q) <= valp (p + q) ?= iff
  ((valp p == valp q) ==> (p`_(valp p) + q`_(valp q) != 0)).
Proof.
wlog le_mn : p q / valp p <= valp q => [hwlog|]; last rewrite (minn_idPl _) //.
  have /orP [le_mn|le_nm] := leq_total (valp p) (valp q); first exact: hwlog.
  move=> *; rewrite minnC addrC eq_sym [_`__ + _]addrC.
  by apply: (hwlog q p) => //; rewrite addrC.
case: valpXP=> [|m {p} p pN0 p0N0] in le_mn *; rewrite ?eqxx => //= _.
case: valpXP=> [|n {q} q qN0 q0N0] in le_mn *; rewrite ?eqxx => //= _.
rewrite !coefMXn ?ltnn ?subnn -coefD.
move: le_mn; rewrite leq_eqVlt => /orP [/eqP eq_mn|lt_mn].
  rewrite eq_mn eqxx -mulrDl implyTb.
  rewrite -lead_coef_eq0 lead_coefMXn lead_coef_eq0 => pDq_eq0.
  rewrite valpMXn // -{1}[n]add0n -[X in _ <= _ ?= iff X]andbT.
  apply: leqif_add; last exact/leqif_refl.
  apply/leqifP; rewrite [0%N == _]eq_sym; case: (altP eqP) => pq0 /=.
    by rewrite lt0n valp_eq0E // negbK pq0.
  by rewrite valp_eq0.
rewrite ltn_eqF // implyFb => H; apply/leqifP; move: H.
rewrite -(subnK lt_mn) addnS -addSn exprD mulrA -mulrDl; set r := p + _.
have r0N0 : r`_0 != 0 by rewrite coefD coefMXn // addr0.
have rN0 : r != 0 by apply: contraNneq r0N0 => ->; rewrite coef0.
by rewrite valpMXn // valp_eq0.
Qed.

Lemma valpD (p q : {poly R}) : p != 0 -> q != 0 ->
  ((valp p == valp q) ==> (p`_(valp p) + q`_(valp q) != 0)) ->
  valp (p + q) = minn (valp p) (valp q).
Proof.
move=> p_neq0 q_neq0 Hpq; apply/eqP; rewrite eq_sym leqif_valpD //.
apply: contraTN Hpq; rewrite addrC addr_eq0 => /eqP ->.
by rewrite valpN coefN subrr !eqxx.
Qed.

End Valuation.

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
