(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  Theory of reverse polynomial and relation to roots and multiplicity.     *)
(*****************************************************************************)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype finset finfun.
From mathcomp
Require Import div tuple finfun bigop ssralg poly polydiv zmodp.
From Newtonsums Require Import auxresults.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

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