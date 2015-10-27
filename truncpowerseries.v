(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  some doc here                                                            *)
(*****************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp Require Import div tuple finfun bigop finset fingroup perm ssralg poly.
From mathcomp Require Import polydiv mxpoly binomial bigop ssralg finalg zmodp.
From mathcomp Require Import matrix mxalgebra polyXY ring_quotient.
From Newtonsums Require Import auxresults fraction polydec revpoly.

Import FracField.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Open Local Scope quotient_scope.

Reserved Notation "x %:F" (at level 2, format "x %:F").
Reserved Notation "r ~i" (at level 2, format "r ~i").

Local Notation "p ^ f" := (map_poly f p).

Section extra_mod_poly.

Variables (K : fieldType).


Fact leq_modpXn m (p : {poly K}) : size (p %% 'X^m) <= m.
Proof.
by rewrite -ltnS (leq_trans (ltn_modpN0 _ _)) // -?size_poly_eq0 size_polyXn.
Qed.
                                       
Lemma poly_modXn_small (a b : nat) (E : nat -> K) : a <= b ->
  \poly_(i < a) E i %% 'X^b = \poly_(i < a) E i.
Proof.
move => a_leq_b.
by rewrite modp_small // size_polyXn ; apply: (leq_trans (size_poly _ _)).
Qed.

Lemma coef_modXn m (p : {poly K}) i : (p %% 'X^m)`_i =
  if i < m then p`_i else 0.
Proof.
have [lt_i_m|le_m_i] := ltnP i m; last first.
  by rewrite nth_default // (leq_trans (leq_modpXn _ _)).
have /polyP /(_ i) := divp_eq p 'X^m.
by rewrite coefD coefMXn lt_i_m add0r.
Qed.

Lemma poly_coef m (p : {poly K}) : \poly_(i < m) p`_i = p %% 'X^m.
Proof. by apply/polyP => i ; rewrite coef_poly coef_modXn. Qed.

Lemma modpXnXn m n : 'X^m %% 'X^n = if m < n then 'X^m else 0 : {poly K}.
Proof.
have [le_mn|le_nm] := ltnP; first by rewrite modp_small ?size_polyXn.
by rewrite modp_eq0 // dvdp_exp2l.
Qed.

Fact modp_summ (I : Type) (r : seq I) (P : pred I)
               (F : I -> {poly K}) (p : {poly K}) :
               (\sum_(i <- r | P i) F i) %% p = \sum_(i <- r | P i) (F i %% p).
Proof. by rewrite (big_morph ((@modp _)^~ p) (modp_add _) (mod0p _) _). Qed.

Lemma poly_modp (a b : nat) (E : nat -> K) : b <= a ->
  \poly_(i < a) E i %% 'X^b =  \poly_(i < b) E i.
Proof.
move => le_ba; rewrite !poly_def modp_summ.
rewrite (big_ord_widen a (fun i => _ i *: _ i)) // [RHS]big_mkcond /=.
apply: eq_bigr => i _; rewrite modp_scalel modpXnXn.
by case: ifP; rewrite // scaler0.
Qed.

Lemma modCp a (p : {poly K}) : size p > 1 -> a%:P %% p = a%:P.
Proof.
move=> p_big; rewrite modp_small // size_polyC.
by rewrite (leq_ltn_trans (leq_b1 _)).
Qed.

Lemma modCXn a n : 0 < n -> a%:P %% 'X^n = a%:P :> {poly K}.
Proof. by move=> n_gt0; rewrite modCp ?size_polyXn. Qed.

Fact modp_modp (p u v : {poly K}) : u %| v -> (p %% v) %% u = p %% u.
Proof.
move => dvdp_u_v.
have [ -> | v_neq0 ] := eqVneq v 0 ; first by rewrite modp0.
rewrite (divp_eq p v) modp_addl_mul_small ?ltn_modp //.
by rewrite modp_add [X in X + _]modp_eq0 ?dvdp_mull // add0r.
Qed.

Fact modpXn_eqC n a (p : {poly K}) : n > 0 -> p %% 'X^n = a%:P -> p`_0 = a.
Proof.
move: n=> [//|n] _; rewrite {2}(divp_eq p 'X^n.+1) => ->.
rewrite coefD -!horner_coef0 hornerM_comm ; last exact: mulrC.
by rewrite hornerXn expr0n -leqn0 ltn0 mulr0 hornerC add0r.
Qed.

Fact coef0M (p q : {poly K}) : (p * q)`_0 = p`_0 * q`_0.
(* Proof. by rewrite coefM big_ord_recl big_ord0 addr0. Qed. *)
Proof. by rewrite -!horner_coef0 hornerM. Qed.

End extra_mod_poly.

Section extra_poly.

Variables (R : ringType).

Lemma leq_size_deriv (p : {poly R}) : size p^`() <= (size p).-1.
Proof.
have [->|pN0] := eqVneq p 0; first by rewrite deriv0 size_poly0.
by rewrite -ltnS prednK // ?lt_size_deriv // size_poly_gt0. 
Qed.

End extra_poly.

Delimit Scope tfps_scope with tfps.
Local Open Scope tfps_scope.

Section TruncatedPowerSeries.

Variables (K : fieldType) (n : nat).

Record tfps := MkTfps
{
  truncated_tfps :> {poly K};
  _ :  size truncated_tfps <= n.+1
}.

Definition tfps_of of phant K := tfps.
Local Notation "'{tfps}'" := (tfps_of (Phant K)).

Canonical tfps_subType := [subType for truncated_tfps].
Definition tfps_eqMixin := [eqMixin of tfps by <:].
Canonical tfps_eqType := EqType {tfps} tfps_eqMixin.
Definition tfps_choiceMixin := [choiceMixin of tfps by <:].
Canonical tfps_choiceType := ChoiceType {tfps} tfps_choiceMixin.

Definition Tfps_of (p : {poly K}) (p_small : size p <= n.+1) : {tfps} :=
  MkTfps p_small.

Definition Tfps (p : {poly K}) := Tfps_of (leq_modpXn _ p).

Definition tfps_of_fun (f : nat -> K) := Tfps_of (size_poly _ f).

Notation "[ 'tfps' s => F ]" := (tfps_of_fun (fun s => F))
  (at level 0, s ident, only parsing) : tfps_scope.

Implicit Types (f g : {tfps}).

Lemma size_tfps f : size (val f) <= n.+1.
Proof. by case: f. Qed.
Hint Resolve size_tfps.

Lemma tfps_nth_default f j : j > n ->  f`_j = 0.
Proof. by move=> j_big; rewrite nth_default // (leq_trans _ j_big). Qed.

(* zmodType structure *)

Fact zero_tfps_subproof : size (0 : {poly K}) <= n.+1.
Proof. by rewrite size_poly0. Qed.

Definition zero_tfps := Tfps_of zero_tfps_subproof.

Lemma add_tfps_subproof f1 f2 :
  size (val f1 + val f2) <= n.+1.
Proof. by rewrite (leq_trans (size_add _ _)) // geq_max !size_tfps. Qed.

Definition add_tfps f1 f2 := Tfps_of (add_tfps_subproof f1 f2).

Lemma opp_tfps_proof f : size (- val f) <= n.+1.
Proof. by rewrite size_opp. Qed.

Definition opp_tfps f := Tfps_of (opp_tfps_proof f).

Fact add_tfpsA : associative add_tfps.
Proof. by move => p1 p2 p3; apply: val_inj; apply: addrA. Qed.

Fact add_tfpsC : commutative add_tfps.
Proof. by move => p1 p2; apply: val_inj; apply: addrC. Qed.

Fact add_tfps0x : left_id zero_tfps add_tfps.
Proof. by move => p; apply: val_inj; apply: add0r. Qed.

Fact add_tfpsK : left_inverse zero_tfps opp_tfps add_tfps.
Proof. by move => p; apply: val_inj; apply: addNr. Qed.

Definition tfps_zmodMixin :=
                          ZmodMixin add_tfpsA add_tfpsC add_tfps0x add_tfpsK.
Canonical tfps_zmodType := ZmodType {tfps} tfps_zmodMixin.

Lemma Tfps0 : Tfps 0 = 0.
Proof. by apply: val_inj => /=; rewrite mod0p. Qed.

Lemma val_TfpsC c : val (Tfps c%:P) = c%:P.
Proof. by rewrite /= modCXn. Qed.

(* ringType structure *)

Fact one_tfps_proof : size (1 : {poly K}) <= n.+1.
Proof. by rewrite size_polyC (leq_trans (leq_b1 _)). Qed.

Definition one_tfps : {tfps} := Tfps_of one_tfps_proof.

Definition mul_tfps f1 f2 := Tfps (val f1 * val f2).

Definition hmul_tfps f1 f2 := [tfps j => f1`_j * f2`_j].

Local Notation "p1 *h p2" := (hmul_tfps p1 p2) (at level 2).

Lemma hmul_tfpsC : commutative hmul_tfps.
Proof.
by move=> p1 p2; apply/val_inj/polyP => /= i; rewrite !coef_poly mulrC.
Qed.

Lemma hmul_tfpsA : associative hmul_tfps.
Proof.
move=> p1 p2 p3; apply/val_inj/polyP => /= i.
by rewrite // !coef_poly; case: (i < n.+1) => //; apply: mulrA.
Qed.

Lemma hmul_tfps0r (p : {tfps}) : 0 *h p = 0.
Proof.
by apply/val_inj/polyP => i /=; rewrite coef_poly coef0 mul0r if_same.
Qed.

Lemma hmul_tfpsr0 (p : {tfps}) : p *h 0 = 0.
Proof. by rewrite hmul_tfpsC hmul_tfps0r. Qed.

Fact left_id_one_tfps_mul_tfps : left_id one_tfps mul_tfps.
Proof.
move => p; apply val_inj; rewrite /= mul1r.
by rewrite modp_small // size_polyXn ltnS.
Qed.

Fact mul_tfpsC : commutative mul_tfps.
Proof. by move => p1 p2 ; apply val_inj => /= ; rewrite mulrC. Qed.

Fact left_distributive_mul_tfps : left_distributive mul_tfps add_tfps.
Proof. by move => p1 p2 p3; apply val_inj => /= ; rewrite mulrDl modp_add. Qed.

Fact mul_tfpsA : associative mul_tfps.
Proof.
move => p1 p2 p3 ; apply: val_inj.
by rewrite /= [in RHS]mulrC !modp_mul mulrA mulrC.
Qed.

Fact one_tfps_not_zero : one_tfps != 0.
Proof. by rewrite -val_eqE oner_neq0. Qed.

Definition tfps_ringMixin := ComRingMixin mul_tfpsA mul_tfpsC
        left_id_one_tfps_mul_tfps left_distributive_mul_tfps one_tfps_not_zero.

Canonical tfps_ringType := RingType {tfps} tfps_ringMixin.

Canonical tfps_comRingType := ComRingType {tfps} mul_tfpsC.

Fact val_tfps_exp f (m : nat) :
  val (f ^+ m) = (val f ^+ m) %% 'X^n.+1.
Proof.
elim: m => [|m ihm] //=; first by rewrite expr0 modCXn.
by rewrite exprS /= ihm modp_mul -exprS.
Qed.

(* comUnitRingType structure *)

Lemma tfps_coefK f : [tfps s => f`_s] = f.
Proof.
apply/val_inj/polyP=> j; rewrite coef_poly ltnS.
by have  [//|j_big] := leqP; rewrite tfps_nth_default.
Qed.

Lemma coef_tfps s (f : nat -> K) :
  [tfps s => f s]`_s = if s <= n then f s else 0.
Proof. by rewrite coef_poly. Qed.

Lemma coef_Tfps p s : (Tfps p)`_s = if s <= n then p`_s else 0.
Proof. by rewrite coef_modXn. Qed.

Fixpoint coef_inv_rec (p : {poly K}) (m i : nat) : K :=
  match m with
    | O => p`_(locked 0%N) ^-1
    | S m => if i == 0%N then p`_(locked 0%N) ^-1
             else - p`_(locked 0%N) ^-1 * \sum_(k < i) p`_(i - k)
                                        * coef_inv_rec p m k
  end.

Definition coef_inv (p : {poly K}) (i : nat) : K := coef_inv_rec p i i.

Lemma coef_inv_recE (p : {poly K}) (m i : nat) : i <= m ->
                                             coef_inv_rec p m i = coef_inv p i.
Proof.
rewrite /coef_inv; elim: m {-2}m (leqnn m) i => [ k | m IHm ].
  by rewrite leqn0 => /eqP -> i ; rewrite leqn0 => /eqP ->.
case => [ k i | k ] ; first by rewrite leqn0 => /eqP ->.
rewrite ltnS => le_km [ // | i ] ; rewrite ltnS => le_ik /=.
congr (_ * _) ; apply: eq_bigr => l _.
by rewrite !IHm 1?(leq_trans (leq_ord _)) // (leq_trans le_ik).
Qed.

Lemma coef_inv0 (p: {poly K}) : coef_inv p 0 = p`_0 ^-1.
Proof. by rewrite /coef_inv /= -lock. Qed.

Lemma coef_invS (p: {poly K}) (j : nat) : coef_inv p j.+1 =
                -(p`_0 ^-1) * (\sum_(k < j.+1) p`_(j.+1 - k) * (coef_inv p k)).
Proof.
rewrite /coef_inv /= -lock; congr (_ * _) ; apply: eq_bigr => k _.
by rewrite coef_inv_recE // leq_ord.
Qed.

Definition unit_tfps : pred {tfps} :=
  fun p => ((val p)`_0 \in GRing.unit).

Definition inv_tfps f := if f \in unit_tfps then [tfps s => coef_inv f s] else f.

Fact coef_inv_tfps_subproof f (j : nat) : f \in unit_tfps ->
  (inv_tfps f)`_j =
  if j > n then 0 else
  if j == 0%N then f`_0 ^-1 else
  - (f`_0 ^-1) * (\sum_(k < j) f`_(j - k) * (inv_tfps f)`_k).
Proof.
have [j_big|j_small] := ltnP; first by rewrite tfps_nth_default.
move=> f_unit; rewrite /inv_tfps f_unit !coef_tfps.
case: j => [|j] in j_small *; first by rewrite coef_inv0.
rewrite j_small coef_invS.
congr (_ * _); apply: eq_bigr => i _; rewrite coef_tfps ifT //.
by rewrite (leq_trans _ j_small) // leqW ?leq_ord.
Qed.

Fact nonunit_inv_tfps : {in [predC unit_tfps], inv_tfps =1 id}.
Proof. by move=> p; rewrite inE /inv_tfps /= => /negPf ->. Qed.

Fact unit_tfpsP f1 f2 : f2 * f1 = 1 -> unit_tfps f1.
Proof.
move=> /val_eqP /eqP /= /modpXn_eqC - /(_ isT).
rewrite coef0M mulrC => f10Mf20_eq1.
by apply/unitrPr; exists f2`_0.
Qed.

Fact tfps_mulVr : {in unit_tfps, left_inverse 1 inv_tfps *%R}.
Proof.
move=> f f_unit; apply: val_inj; rewrite /inv_tfps f_unit /=.
rewrite -poly_coef; apply/polyP => i ; rewrite coef_poly.
have [ i_small | i_big ] := ltnP i n.+1 ; last first.
  by rewrite coefC gtn_eqF // (leq_trans _ i_big).
rewrite coefC ; case: i => [|i] in i_small *.
  by rewrite coef0M coef_poly /= coef_inv0 mulVr.
rewrite coefM big_ord_recr coef_poly i_small subnn.
apply: canLR (addNKr _) _; rewrite addr0.
apply: canLR (mulrVK _) _; rewrite // mulrC mulrN -mulNr.
rewrite coef_invS; congr (_ * _); apply: eq_bigr => j _ /=.
by rewrite mulrC coef_poly (leq_trans _ i_small) 1?leqW.
Qed.

Definition tfps_comUnitRingMixin := ComUnitRingMixin
  tfps_mulVr unit_tfpsP nonunit_inv_tfps.

Canonical unit_tfpsRingType := UnitRingType {tfps} tfps_comUnitRingMixin.

Lemma coef_inv_tfps f (j : nat) : f \is a GRing.unit -> f^-1`_j =
  if j > n then 0 else
  if j == 0%N then f`_0 ^-1
  else - (f`_0 ^-1) * (\sum_(k < j) f`_(j - k) * f^-1`_k).
Proof. exact: coef_inv_tfps_subproof. Qed.

Lemma hmul_tfpsr1 f : f *h 1 = Tfps (f`_0)%:P.
Proof.
apply/val_inj/polyP => s; rewrite coef_tfps coef_Tfps !coefC.
by case: s => [|s]; rewrite ?mulr1 ?mulr0.
Qed.

Lemma hmul_tfps1r f : 1 *h f = Tfps (f`_0)%:P.
Proof. by rewrite hmul_tfpsC hmul_tfpsr1. Qed.

Canonical tfps_comUnitRingType := [comUnitRingType of {tfps}].

Lemma unit_tfpsE f : (f \in GRing.unit) = (f`_0 != 0).
Proof. by rewrite qualifE /= /unit_tfps unitfE. Qed.

Definition exp f :=
  if f`_0 != 0 then 0 else
  Tfps (\sum_(i < n.+1) ((i`! %:R) ^-1) *: (val f ^+i)).

Definition log f :=
  if f`_0 != 1 then 0 else
  Tfps (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: ((1 - val f) ^+i)).

Definition coef0_is_0 : pred_class := fun f : {tfps} => f`_0 == 0.

Lemma coef0_is_0E f : (f \in coef0_is_0) = (f`_0 == 0).
Proof. by rewrite -topredE. Qed.

Fact nth0_mul_tfps f g : (f * g)`_0 = f`_0 * g`_0.
Proof. by rewrite coef_Tfps coef0M. Qed.

Fact c0_is_0_idealr : idealr_closed coef0_is_0.
Proof.
split => [|| a p q ]; rewrite ?coef0_is_0E ?coefC ?eqxx ?oner_eq0 //.
move=> /eqP p0_eq0 /eqP q0_eq0.
by rewrite coefD q0_eq0 addr0 nth0_mul_tfps p0_eq0 mulr0.
Qed.

Fact c0_is_0_key : pred_key coef0_is_0. Proof. by []. Qed.

Canonical c0_is_0_keyed := KeyedPred c0_is_0_key.
Canonical c0_is_0_opprPred := OpprPred c0_is_0_idealr.
Canonical c0_is_0_addrPred := AddrPred c0_is_0_idealr.
Canonical c0_is_0_zmodPred := ZmodPred c0_is_0_idealr.

Definition c0_is_0_ntideal := idealr_closed_nontrivial c0_is_0_idealr.

Canonical coef0_is_0_ideal := MkIdeal c0_is_0_zmodPred c0_is_0_ntideal.

Fact c0_is_0_prime : prime_idealr_closed coef0_is_0.
Proof. by move => x y; rewrite -!topredE /= /coef0_is_0 nth0_mul_tfps mulf_eq0. Qed.

Canonical coef0_is_0_pideal := MkPrimeIdeal coef0_is_0_ideal c0_is_0_prime.

Definition coef0_is_1 : pred_class := fun f : {tfps} => f`_0 == 1.

Lemma coef0_is_1E f : (f \in coef0_is_1) = (f`_0 == 1).
Proof. by rewrite -topredE. Qed.

Lemma coef0_1subp_is_0 f :
  f \in coef0_is_1 -> (1 - f) \in coef0_is_0.
Proof.
rewrite ?coef0_is_0E ?coef0_is_1E.
rewrite -!horner_coef0 -!horner_evalE rmorphB /= !horner_evalE hornerC.
by move=> /eqP -> ; rewrite subrr.
Qed.

Lemma c0_is_1_unit f : f \in coef0_is_1 -> f \is a GRing.unit.
Proof. by rewrite coef0_is_1E unit_tfpsE => /eqP ->; rewrite oner_eq0. Qed.

Lemma mul_c0_is_1_closed : {in coef0_is_1 &, forall f g, f * g \in coef0_is_1}.
Proof.
by move=> f g; rewrite !coef0_is_1E nth0_mul_tfps => /eqP -> /eqP ->; rewrite mulr1.
Qed.

Fact nth0_inv f : (f ^-1)`_0 = (f`_0)^-1.
Proof.
have [f_unit|] := boolP (f \is a GRing.unit); first by rewrite coef_inv_tfps.
move=> fNunit; have := fNunit; rewrite -unitrV; move: fNunit.
by rewrite !unit_tfpsE !negbK => /eqP -> /eqP ->; rewrite invr0.
Qed.

Fact inv_c0_is_1_closed : {in coef0_is_1, forall p, p^-1 \in coef0_is_1}.
Proof.
by move=> f; rewrite !coef0_is_1E => /eqP p0_is_1; rewrite nth0_inv p0_is_1 invr1.
Qed.

Fact c0_is_1_div_closed : divr_closed coef0_is_1.
Proof.
split => [ | p q p0_is_1 q0_is_1 ]; first by rewrite coef0_is_1E coefC eqxx.
by rewrite mul_c0_is_1_closed ?inv_c0_is_1_closed.
Qed.

Fact c0_is_1_key : pred_key coef0_is_1. Proof. by []. Qed.
Canonical c0_is_1_keyed := KeyedPred c0_is_1_key.

Canonical c0_is_1_mulPred := MulrPred c0_is_1_div_closed.
Canonical c0_is_1_divPred := DivrPred c0_is_1_div_closed.

Lemma exp_coef0_is_0 f : f \in coef0_is_0 ->
  exp f = Tfps (\sum_(i < n.+1) ((i`! %:R) ^-1) *: ((val f) ^+i)).
Proof. by rewrite coef0_is_0E /exp => ->. Qed.

Lemma exp_coef0_isnt_0 f : f \notin coef0_is_0 -> exp f = 0.
Proof. by rewrite coef0_is_0E /exp => /negPf ->. Qed.

Lemma log_coef0_is_1 f : f \in coef0_is_1 ->
  log f = Tfps (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: ((1 - (val f)) ^+i)).
Proof. by rewrite coef0_is_1E /log => ->. Qed.

Lemma log_coef0_isnt_1 f : f \notin coef0_is_1 -> log f = 0.
Proof. by rewrite coef0_is_1E /log => /negPf ->. Qed.

Lemma log1 : log 1 = 0.
Proof.
apply/val_inj/polyP=> j; rewrite log_coef0_is_1 ?rpred1 // coef0 coef_Tfps.
case: ifP => // j_small; rewrite coefN big1 ?coef0 ?oppr0 //.
by move=> [|i]; rewrite subrr expr0n ?eqxx ?invr0 ?scale0r ?scaler0.
Qed.

Fact modp_exp_eq0 (p : {poly K}) (m : nat) : p`_0 = 0 -> n < m ->
  (p ^+ m) %% 'X^n.+1 = 0.
Proof.
rewrite -horner_coef0 => /polyXsubCP p0_eq0 n_lt_m.
rewrite polyC0 subr0 in p0_eq0.
apply/modp_eq0P.
by rewrite (dvdp_trans (dvdp_exp2l ('X : {poly K}) n_lt_m)) // dvdp_exp2r.
Qed.

Lemma widen_log_coef0_is_1 (p : tfps) : p \in coef0_is_1 ->
  log p = Tfps ((- \sum_(1 <= i < n.+2) ((i %:R) ^-1) *: ((1 - (val p)) ^+i))).
Proof.
move => p0_eq1.
rewrite log_coef0_is_1 // ; apply: val_inj => /=.
rewrite (big_nat_recr n.+1) /= ; last exact: ltn0Sn.
rewrite [RHS]modNp modp_add modp_scalel modp_exp_eq0 ?leqnn // ; last first.
  move: p0_eq1 ; rewrite -!horner_coef0 -!horner_evalE rmorphB /=.
  by rewrite !horner_evalE hornerC horner_coef0 ; move/eqP -> ; rewrite subrr.
by rewrite scaler0 addr0 modNp.
Qed.

Lemma coef0_is_1_unit (p : tfps): p \in coef0_is_1-> unit_tfps p.
Proof. by rewrite /unit_tfps=> /eqP ->;rewrite unitfE oner_eq0. Qed.

Fact add_tfps_is_coef0_is_0 (p q : tfps) :
  p \in coef0_is_0 -> q \in coef0_is_0 -> ((p : {tfps}) + q) \in coef0_is_0.
Proof.
rewrite !coef0_is_0E coefD.
by move/eqP -> ; move/eqP -> ; rewrite add0r.
Qed.

Fact polyXP (p : {poly K}) : reflect (p`_0 = 0) ('X %| p).
Proof. rewrite -['X]subr0 -polyC0 -horner_coef0 ; exact: polyXsubCP. Qed.

Fact modp_mul_piqj (p q : {poly K}) (i j : nat) : p`_0 = 0 -> q`_0 = 0 ->
  n < i+j -> (p ^+i * q ^+j) %% 'X^n.+1 = 0.
Proof.
move => p0_eq0 q0_eq0 n_lt_addij.
apply/modp_eq0P.
rewrite (dvdp_trans (dvdp_exp2l ('X : {poly K}) n_lt_addij)) // exprD.
by rewrite dvdp_mul // dvdp_exp2r // ; apply/polyXP.
Qed.

Lemma coef0_exp (p : tfps) :
                                    p \in coef0_is_0 -> (exp p)`_0 = 1.
Proof.
move => p0_eq0.
rewrite exp_coef0_is_0 // coef_modXn ltn0Sn -horner_coef0.
rewrite -horner_evalE rmorph_sum /=.
rewrite (eq_bigr (fun i => ((nat_of_ord i) == 0%N)%:R)) => [ | [i _] _ ] /=.
+ rewrite -(big_mkord predT (fun i => ((i == _)%:R))) big_ltn ; last first.
    exact: ltnS.
  rewrite eqxx /= -natr_sum big_nat_cond.
  rewrite (eq_big (fun i => (0 < i < n.+1)) (fun i => 0%N)) => [ | i | i ].
- by rewrite big1_eq addr0.
- by rewrite andbT.
  by rewrite andbT => /andP [/lt0n_neq0/negbTE -> _].
+ rewrite linearZ /= rmorphX /= horner_evalE horner_coef0.
  move: p0_eq0 ; rewrite coef0_is_0E => /eqP ->.
  rewrite expr0n ; case: i => [ | i'].
- by rewrite fact0 invr1 mul1r.
- by rewrite eqn0Ngt -leqNgt ltn0 mulr0.
Qed.

Lemma coef0_log (p : tfps) :
  p \in coef0_is_1 -> (log p)`_0 = 0.
Proof.
move => p0_eq1.
rewrite log_coef0_is_1 // coef_modXn ltn0Sn -horner_coef0.
rewrite -horner_evalE rmorphN rmorph_sum /=.
rewrite big_nat_cond (eq_bigr (fun i => (i == 0%N)%:R)).
+ rewrite -[1%N]add0n big_addn (eq_bigr (fun i => 0)) => [ | i _] ; last first.
    by rewrite addn1.
  by rewrite big1_eq oppr0.
+ move => i /andP [/andP [Hi _] _] /=.
  rewrite linearZ rmorphX rmorphB /= !horner_evalE hornerC horner_coef0.
  move: p0_eq1 ; rewrite coef0_is_1E => /eqP ->.
  by rewrite subrr expr0n eqn0Ngt Hi /= mulr0.
Qed.

Lemma exp_coef0_is_1 (p : tfps) :
  p \in coef0_is_0 -> (exp p) \in coef0_is_1.
Proof. by move => H ; rewrite coef0_is_1E coef0_exp. Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Fact natmul_inj (m : nat) : (m%:R == 0 :> K) = (m == 0%N).
Proof. by move/(charf0P K)/(_ m) : char_K_is_zero. Qed.

Lemma natmul_eq (R : idomainType) (a b : nat) :
                   [char R] =i pred0 -> a%:R = GRing.natmul (1 : R) b -> a = b.
Proof.
move => H_char ; move/eqP.
have [ a_lt_b | b_lt_a | -> ] := ltngtP a b ; last by [].
+ rewrite eq_sym -subr_eq0 -natrB ; last by apply: ltnW.
  move/(charf0P R)/(_ (b-a)%N) : H_char ->.
  by rewrite subn_eq0 leqNgt a_lt_b.
+ rewrite -subr_eq0 -natrB ; last by apply: ltnW.
  move/(charf0P R)/(_ (a-b)%N) : H_char ->.
  by rewrite subn_eq0 leqNgt b_lt_a.
Qed.

Definition swap (R : Type) (x : R * R) := (x.2, x.1).

Lemma swap_inj (R : Type) : involutive (@swap R).
Proof. by move => [x1 x2]. Qed.

Lemma triangular_swap (R : Type) (idx : R) (op : Monoid.com_law idx)
                 (m : nat) (P : 'I_m -> 'I_m -> bool) (F : nat -> nat -> R) :
  \big[op/idx]_(i < m) \big[op/idx]_(j < m | P i j) F i j =
  \big[op/idx]_(j < m) \big[op/idx]_(i < m | P i j) F i j.
Proof. by rewrite !pair_big_dep (reindex_inj (inv_inj (@swap_inj _))). Qed.

Lemma index_translation (R : Type) (idx : R) (op : Monoid.law idx)
                                                   (m j : nat) (F : nat -> R) :
  \big[op/idx]_(i < m - j) F i =
  \big[op/idx]_(k < m | j <= k)  F (k - j)%N.
Proof.
rewrite -(big_mkord predT F) /= (big_mknat _ j m (fun k => F (k - j)%N)).
rewrite -{2}[j]add0n (big_addn 0 m j _ _).
by apply: eq_bigr => i _ ; rewrite addnK.
Qed.

Lemma aux_triangular_index_bigop (R : Type) (idx : R) (op : Monoid.com_law idx)
                                              (m : nat) (F : nat -> nat -> R) :
  \big[op/idx]_(i < m) \big[op/idx]_(j < m | i + j < m) F i j =
  \big[op/idx]_(k < m) \big[op/idx]_(l < k.+1) F l (k - l)%N.
Proof.
evar (G : 'I_m -> R) ; rewrite [LHS](eq_bigr G) => [|i _] ; last first.
+ rewrite (eq_bigl (fun j => nat_of_ord j < (m - (nat_of_ord i))%N))=> [|j /=].
- rewrite big_ord_narrow => [ | _ /= ] ; first exact: leq_subr.
  by rewrite index_translation ; symmetry ; rewrite /G ; reflexivity.
- by rewrite ltn_subRL.
+ rewrite /G (triangular_swap _ (fun i k => (nat_of_ord i) <= (nat_of_ord k))
                                (fun i k => F i (k - i)%N)).
  apply: eq_big => [ // | i _].
  rewrite (eq_bigl (fun i0 => (nat_of_ord i0) < i.+1)) => [ | j ] ; last first.
- by rewrite -ltnS.
- by rewrite big_ord_narrow.
Qed.

Lemma triangular_index_bigop (R : Type) (idx : R) (op : Monoid.com_law idx)
                             (m m': nat) (F : nat -> nat -> R) :
  m' <= m ->
  \big[op/idx]_(i < m) \big[op/idx]_(j < m | i + j < m') F i j =
  \big[op/idx]_(k < m') \big[op/idx]_(l < k.+1) F l (k - l)%N.
Proof.
move => leq_m'm.
rewrite -(subnKC leq_m'm) big_split_ord /=.
rewrite [X in op _ X]big1_seq => [|i _]; last first.
  rewrite big_hasC // ; apply/hasPn => x _.
  by rewrite -[X in _ < X]addn0 -addnA ltn_add2l ltn0.
rewrite Monoid.Theory.simpm /= -aux_triangular_index_bigop.
apply: eq_bigr => i _ ; rewrite subnKC //.
rewrite (eq_bigl (fun j => (i + (nat_of_ord j) < m') && ((nat_of_ord j) < m'))) ; last first.
  move => j; symmetry.
  rewrite andb_idr //; apply: contraLR; rewrite -!leqNgt => leq_m'j.
  by rewrite (leq_trans leq_m'j) // leq_addl.
by rewrite big_ord_narrow_cond.
Qed.

Fact bigID_ord (R : Type) (idx : R) (op : Monoid.com_law idx) (m : nat)
                                         (P : pred nat) (F : nat -> R) :
\big[op/idx]_(i < m) F i = op (\big[op/idx]_(i < m | P i) F i) (\big[op/idx]_(i < m | ~~ P i) F i).
Proof. by apply: bigID. Qed. 

Fact big_ord_rev (R : Type) (idx : R) (op : Monoid.com_law idx) (m : nat)
  (P : nat -> bool) (F : nat -> R) :
  \big[op/idx]_(i < m | P i) F i =
  \big[op/idx]_(i < m | P (m - i.+1)%N) F (m - i.+1)%N.
Proof.
rewrite -(big_mkord P F) big_nat_rev (big_mkord _ _).
by apply: eq_bigr ; rewrite add0n.
Qed.

Lemma exp_is_morphism :
                {in coef0_is_0 &, {morph exp : p q / p + q >-> p * q}}.
Proof.
move => p q p0_eq0 q0_eq0 /=.
rewrite exp_coef0_is_0 ?add_tfps_is_coef0_is_0 //.
rewrite exp_coef0_is_0 ?add_tfps_is_coef0_is_0 //.
rewrite !exp_coef0_is_0 //.
apply: val_inj => /= ; apply: val_inj => /=.
rewrite modp_mul mulrC modp_mul -mulrC.
rewrite coef0_is_0E -!horner_coef0 in p0_eq0 q0_eq0.
move/eqP: q0_eq0 ; move/eqP : p0_eq0.
move: p q => [p pr] [q qr] /=.
rewrite !horner_coef0 => p0_eq0 q0_eq0.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in i'`!%:R^-1 *:
         (\sum_(j < i'.+1) p ^+ (i' - j) * q ^+ j *+ 'C(i', j)))) ; last first.
  by move => i _ ; rewrite exprDn.
rewrite (big_distrl _ _ _) /=.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in (\sum_(j < i' .+1)
        ((j`! * (i' -j)`!)%:R) ^-1 *: (p ^+ (i' - j) * q ^+ j)))) ; last first.
  move => [i i_lt_Sn] _ /=.
  rewrite scaler_sumr ; apply: eq_bigr => [ /= [j j_lt_Si]] _ /=.
  rewrite -mulrnAl scalerAl -scaler_nat scalerA -scalerAl ; congr(_ *: _).
  have factr_neq0 k : k`!%:R != 0 :> K
                              by rewrite (proj1 (charf0P _)) // -lt0n fact_gt0.
  apply: (mulfI (factr_neq0 i)) ; rewrite mulVKf //.
  have den_neq0 :  (j`! * (i - j)`!)%:R != 0 :> K by rewrite natrM mulf_neq0.
  by apply: (mulIf den_neq0) ; rewrite mulfVK // -natrM bin_fact.
rewrite [in RHS](eq_bigr (fun i => let i' := (nat_of_ord i) in (\sum_(j < n.+1)
                    ((i'`! * j`!)%:R^-1) *: (p ^+ i' * q ^+ j)))) ; last first.
  move => i _.
  rewrite (big_distrr _ _ _) /=.
  apply: eq_bigr => j _ /=.
  rewrite -scalerAl -scalerCA -scalerAl scalerA -invrM ?unitfE ; last 2 first.
  + move/(charf0P K)/(_ (j`!)%N) : char_K_is_zero ->.
    by rewrite -lt0n fact_gt0.
  + move/(charf0P K)/(_ (i`!)%N) : char_K_is_zero ->.
    by rewrite -lt0n fact_gt0.
  by rewrite -natrM mulnC.
have -> : (\sum_(i < n.+1) \sum_(j < n.+1)
  (i`! * j`!)%:R^-1 *: (p ^+ i * q ^+ j)) %% 'X^n.+1 =
  (\sum_(i < n.+1) \sum_(j < n.+1 | i+j <= n)
  (i`! * j`!)%:R^-1 *: (p ^+ i * q ^+ j)) %% 'X^n.+1.
  rewrite !modp_summ ; apply: eq_bigr => [[i i_lt_Sn]] _ /=.
  rewrite !modp_summ.
  rewrite (bigID_ord _ _ (fun j => i + j <= n)
        (fun x => ((i`! * x`!)%:R^-1 *: (p ^+ i * q ^+ x)) %% 'X^n.+1)) /=.
  rewrite -[RHS]addr0 ; congr (_ + _).
  rewrite -(big_mkord (fun j => ~~ (i + j <= n))
                      (fun j => ((i`! * j`!)%:R^-1 *: (p ^+ i * q ^+ j)) %% 'X^n.+1)).
  apply: big1_seq => /= m.
  rewrite -ltnNge ; move/andP => [ n_lt_addim _].
  apply/modp_eq0P.
  rewrite dvdp_scaler ; last first.
  rewrite invr_eq0.
    move/(charf0P K)/(_ (i`! * m`!)%N) : char_K_is_zero ->.
    by rewrite muln_eq0 negb_or -!lt0n !fact_gt0.
    by apply/modp_eq0P ; rewrite modp_mul_piqj.
apply: (congr1 (fun x => polyseq x)).
apply: (congr1 (fun x => modp x (GRing.exp (polyX K) (S n)))).
rewrite [in RHS](eq_bigr (fun i => let i' := (nat_of_ord i) in \sum_(j < n.+1 |
        i' + j < n.+1) (i'`! * j`!)%:R^-1 *: (p ^+ i' * q ^+ j))) ; last first.    
 move => i _.
  by apply: eq_bigr.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in \sum_(j < i'.+1)
           (j`! * (i' - j)`!)%:R^-1 *: (p ^+ j * q ^+ (i' - j)))) ; last first.
  move => i _.
  rewrite /= (big_ord_rev _ i.+1 predT
             (fun j => (j`! * (i - j)`!)%:R^-1 *: (p ^+ (i - j) * q ^+ j))) /=.
  apply: eq_bigr => j _.
  by rewrite !subSS subnBA -1?ltnS // !addKn mulnC.
by rewrite (triangular_index_bigop _
                      (fun i j => (i`! * j`!)%:R^-1 *: (p ^+ i * q ^+ j))) /= ;
  last exact: ltnSn.
Qed.

(* unitAlgType structure *)

Definition scale_tfps (c : K) (p : {tfps}) := Tfps (c *: (val p)).

Fact scale_tfpsA a b (p : {tfps}) :
     scale_tfps a (scale_tfps b p) = scale_tfps (a * b) p.
Proof.
apply: val_inj => /=.
by rewrite modp_scalel modp_mod -modp_scalel scalerA.
Qed.

Fact scale_1tfps : left_id (1 : K) scale_tfps.
Proof.
move => x; apply: val_inj => /=.
by rewrite scale1r modp_small // size_polyXn ltnS.
Qed.

Fact scale_tfpsDl p: {morph scale_tfps^~ p : a b / a + b}.
Proof.
move => a b ; apply: val_inj => /=.
by rewrite scalerDl modp_add.
Qed.

Fact scale_tfpsDr (a : K) : {morph scale_tfps a : p q / p + q}.
Proof. by move => p q ; apply: val_inj => /= ; rewrite scalerDr modp_add. Qed.

Fact scale_tfpsAl (a : K) (p q : {tfps}) :
                       scale_tfps a ((p : {tfps}) * q) = scale_tfps a p * q.
Proof.
apply: val_inj => /=.
rewrite modp_scalel modp_small; last by rewrite ltn_modp expf_neq0 // polyX_eq0.
by rewrite [in RHS]mulrC modp_mul [in RHS]mulrC -modp_scalel -scalerAl.
Qed.

Definition tfps_lmodMixin :=
                             LmodMixin scale_tfpsA scale_1tfps
                                       scale_tfpsDr scale_tfpsDl.

Canonical tfps_lmodType :=
                      Eval hnf in LmodType K {tfps} tfps_lmodMixin.

Canonical tfps_lalgType :=
                        Eval hnf in LalgType K {tfps} scale_tfpsAl.

Canonical tfps_algType := CommAlgType K {tfps}.

Canonical unit_tfpsAlgType :=Eval hnf in [unitAlgType K of {tfps}].

Fact leqnaddsubn (m : nat) : m <= (m.-1).+1.
Proof. case: m => /= [ // | m] ; exact: ltnSn. Qed.

Lemma dvdp_scaler2 (R : idomainType) (c : R) (a b : {poly R}):
                                                     (a %| b) -> (a %| c *: b).
Proof.
have [ -> | c_neq0] := eqVneq c 0.
+ by rewrite scale0r dvdp0.
+ by rewrite dvdp_scaler.
Qed.

Fact big_distrr_nat (R : Type) (zero : R) (times : Monoid.mul_law zero)
  (plus : Monoid.add_law zero times) (a b : nat) (x : R)
  (P : pred nat) (F : nat -> R) :
  \big[plus/zero]_(a <= i < b | P i) times x (F i) =
  times x (\big[plus/zero]_(a <= i < b | P i) F i).
Proof. by rewrite -[a]add0n !big_addn !big_mkord big_distrr. Qed.

Lemma unit_tfpsE2 (p : {tfps}) :
                                      (p \is a GRing.unit) = ((val p)`_0 != 0).
Proof. by rewrite unit_tfpsE. Qed.

Fact tfps_of_poly_proof (m : nat) (p : {poly K}) :
                                m <= n -> size (\poly_(j < m.+1) p`_j) <= n.+1.
Proof. by move => m_leq_n; rewrite (leq_trans (size_poly _ _)) // ltnS. Qed.

End TruncatedPowerSeries.

Notation "{ 'tfps' K n }" := (tfps_of n (Phant K))
  (at level 0, K at next level, format "{ 'tfps'  K  n }").

Notation "[ 'tfps' s => F ]" := (tfps_of_fun _ (fun s => F))
  (at level 0, s ident, only parsing) : tfps_scope.

Hint Resolve size_tfps.

Definition forget_precision (K : fieldType) (m n : nat) (p : {tfps K m}) :=
                                        Tfps n p.

Definition divX (K : fieldType) (m : nat) (p : {tfps K m}) :=
  Tfps m (p %/ 'X).

Section MapTfps.

Variables (K K' : fieldType) (n : nat) (f : {rmorphism K -> K'}).

Definition map_tfps (p : {tfps K n}) :=
  Tfps n (map_poly f (val p)).

Lemma map_tfpsM (p q : {tfps K n}) :
           map_tfps (p * q) = (map_tfps p) * (map_tfps q).
Proof.
apply: val_inj => /=.
rewrite map_modp rmorphX /= map_polyX modp_mod rmorphM /= modp_mul.
by rewrite [in RHS]mulrC modp_mul mulrC.
Qed.

Lemma map_tfps1 : map_tfps 1 = 1.
Proof.
apply: val_inj => /=.
rewrite rmorph1 modp_small // size_polyXn size_polyC.
by apply: (leq_trans (leq_b1 _)).
Qed.

Fact map_tfps_is_additive : additive map_tfps.
Proof.
move => x y; apply: val_inj => /=.
by rewrite rmorphB /= modp_add modNp.
Qed.

Canonical map_tfps_additive := Additive map_tfps_is_additive.

Fact map_tfps_is_multiplicative : multiplicative map_tfps.
Proof.
split => [ x y | ].
+ exact: map_tfpsM.
+ exact: map_tfps1.
Qed.

Canonical map_tfps_rmorphism :=
                                AddRMorphism map_tfps_is_multiplicative.

Lemma map_tfpsZ (c : K) (p : {tfps K n}) :
                    (map_tfps (c *: p)) =  (f c) *: (map_tfps p).
Proof.
apply: val_inj => /=.
rewrite map_modp rmorphX /= map_polyX linearZ /=.
by rewrite [in LHS]modp_scalel.
Qed.

Locate "%:P".

Local Notation "c %:S" := (Tfps n (c %:P)) (at level 2).

Lemma mul_cst (c1 c2 : K) : (c1 * c2) %:S = (c1 %:S) * (c2 %:S).
Proof.
apply: val_inj => /= ; rewrite polyC_mul modp_mul.
by rewrite [in RHS]mulrC modp_mul mulrC.
Qed.

Lemma map_tfpsC (c : K) : map_tfps (c %:S) = (f c) %:S.
Proof.
apply: val_inj => /=.
by rewrite map_modp rmorphX /= map_polyX map_polyC modp_mod.
Qed.

Canonical map_tfps_linear := let R := ({tfps K n}) in
       AddLinear (map_tfpsZ : scalable_for (f \; *:%R) map_tfps).

Canonical map_tfps_lrmorphism := [lrmorphism of map_tfps].

Local Notation "p ^f" := (map_tfps p).
Local Notation "p *h q" := (hmul_tfps p q) (at level 2).

Lemma map_tfps_mul (p q : tfps K n) : (p *h q) ^f = (p ^f) *h (q ^f).
Proof.
apply: val_inj => /= ; rewrite -polyP => i.
rewrite coef_modXn coef_map 2!coef_poly !coef_modXn.
case: (i < n.+1) => //=.
by rewrite rmorphM !coef_map.
Qed.

Lemma map_tfps_injective : injective map_tfps.
Proof.
move => x y.
move/val_eqP => /=.
rewrite modp_small; last by rewrite size_polyXn size_map_poly ltnS size_tfps.
rewrite modp_small; last by rewrite size_polyXn size_map_poly ltnS size_tfps.
move/val_eqP => H.
move: (map_poly_inj f H).
by apply: val_inj.
Qed.

End MapTfps.


Lemma pw_is_cst (K : fieldType) (p : tfps K 0%N) : p = Tfps _ ((p`_0) %:P).
Proof.
rewrite -horner_coef0 ; apply: val_inj => /=.
rewrite expr1 modp_small; last first.
  by rewrite size_polyX size_polyC; apply: (leq_trans (leq_b1 _)).
by rewrite horner_coef0; apply: size1_polyC; rewrite size_tfps.
Qed.

Lemma map_tfps_divX (K K' : fieldType) (f : {rmorphism K -> K'})
  (m : nat) (p : tfps K m) :
  map_tfps f (divX p) = divX (map_tfps f p).
Proof.
apply: val_inj => /=.
rewrite map_modp rmorphX /= map_polyX modp_mod map_divp map_polyX.
by rewrite [(_ ^ _ %% _)]modp_small // size_polyXn size_map_poly ltnS size_tfps.
Qed.

Section Truncated_Tfps.

Variables (K : fieldType) (n : nat).

Fact tfps0 : Tfps n (0 : {poly K}) = 0.
Proof. apply: val_inj ; exact: mod0p. Qed.

Fact tfps1 : Tfps n (1 : {poly K}) = 1.
Proof.
apply: val_inj => /=.
rewrite modp_small // size_polyXn size_polyC.
by apply: (leq_trans (leq_b1 _)).
Qed.

Fact Tfps_is_additive : additive (@Tfps K n).
Proof. by move => p q ; apply: val_inj => /= ; rewrite modp_add modNp. Qed.

Canonical Tfps_additive := Additive Tfps_is_additive.

Lemma Tfps_is_multiplicative: multiplicative (@Tfps K n).
Proof.
split => [p q | ].
+ by apply: val_inj => /= ; rewrite modp_mul [in RHS]mulrC modp_mul mulrC.
+ exact: tfps1.
Qed.

Canonical Tfps_rmorphism := AddRMorphism Tfps_is_multiplicative.

Lemma TfpsM (p q : {poly K}) : Tfps n (p * q) = (Tfps n p) * (Tfps n q).
Proof. by rewrite rmorphM. Qed.

Lemma TfpsZ (c : K) (p : {poly K}): (Tfps n (c *: p))=  c *:(Tfps n p).
Proof. by apply: val_inj => /=; rewrite -modp_scalel modp_mod. Qed.

Canonical Tfps_linear := AddLinear TfpsZ.

Canonical Tfps_lrmorphism := [lrmorphism of (Tfps n)].

Lemma nth0_Tfps (p : {poly K}) : (Tfps n p)`_0 = p`_0.
Proof. by rewrite coef_modXn ltn0Sn. Qed.

Lemma p0_is_0 (m : nat) (p : {tfps K m}) :
                ((Tfps n p) \in (@coef0_is_0 K n)) = (p \in (@coef0_is_0 K m)).
Proof. by rewrite !coef0_is_0E !nth0_Tfps. Qed.

Lemma Tfps_is_unit (p : {poly K}) :
                                 ((Tfps n p) \is a GRing.unit) = (p`_0 != 0).
Proof. by rewrite unit_tfpsE2 nth0_Tfps. Qed.

Lemma TfpsE (p : {poly K}) : p %% 'X^ n.+1 = Tfps n p.
Proof. by apply: val_inj => /=. Qed.

Fact nth0_eq_nth0 (p q : {poly K}) : p %= q -> (p`_0 != 0) = (q`_0 != 0).
Proof.
move => p_eqp_q.
rewrite -!horner_coef0 ; apply: negb_inj ; rewrite !negbK.
apply/(sameP eqP).
apply/(equivP eqP).
apply: (rwP2 (polyXsubCP _ _)).
apply: (aux_equivb (polyXsubCP _ _)).
by rewrite !polyC0 !subr0 ; apply: eqp_dvdr.
Qed.

Definition deriv_tfps : {tfps K n} -> {tfps K n.-1} :=
    fun f => [tfps s => f`_s.+1 *+ s.+1].

Definition prim_tfps (n : nat) : {tfps K n} -> {tfps K n.+1} :=
    fun f => [tfps s => f`_s.-1 *+ (s != 0%N) / s%:R].

Lemma p_neq0 (R: ringType) (p : {poly R}):
                                        (exists (x : R), p.[x] != 0) -> p != 0.
Proof.
move => [x px_neq0].
move: px_neq0 ; apply: contra => /eqP ->.
by rewrite horner0.
Qed.

Fact one_sub_CX_0_eq_1 (a : K) : (1 - a *: 'X).[0] = 1.
Proof.
rewrite -horner_evalE rmorphB /= !horner_evalE.
by rewrite -mul_polyC hornerCM hornerX mulr0 hornerC subr0.
Qed.

Fact truncated_tfps0 : truncated_tfps (0 : {tfps K n}) = 0.
Proof. by []. Qed.

Fact truncated_tfps1 : truncated_tfps (1 : {tfps K n}) = 1.
Proof. by []. Qed.

Fact mod_tfps (m : nat) (f : {tfps K n}) : n <= m -> (val f) %% 'X^m.+1 = (val f).
Proof.
move => leq_nm.
by rewrite modp_small // size_polyXn ltnS (leq_trans (size_tfps _)).
Qed.

Fact mod_deriv_tfps (m : nat) (f : {tfps K n}) : n <= m -> ((val f)^`()) %% 'X^m = (val f)^`().
Proof.
move => leq_nm; rewrite modp_small // size_polyXn ltnS.
rewrite (leq_trans _ leq_nm) // (leq_trans (leq_size_deriv _)) //.
have [->//|sfN0] := eqVneq (size (val f)) 0%N.
by rewrite -ltnS prednK ?size_tfps // lt0n.
Qed.

End Truncated_Tfps.

Lemma truncate_map_poly (K K' : fieldType) (m : nat)
                        (f : {rmorphism K -> K'}) (p : {poly K}) :
                     @Tfps K' m (p ^ f) = map_tfps f (Tfps m p).
Proof. by apply: val_inj => /=; rewrite map_modp map_polyXn modp_mod. Qed.

Section Powerderiv.

Variable (K : fieldType).

(* Definition powerderiv (n : nat) (p : {tfps K n}) := Tfps n.-1 ((val p) ^`()). *)

Definition primitive (a : K) (p : {poly K}) :=
            \poly_(i < (size p).+1) (if i == 0%N then a else p`_i.-1 / (i%:R)).

(* canonical primitive *)
Definition can_primitive := primitive 0.
Local Notation "\int p" := (can_primitive p) (at level 2).

Lemma primitiveE (a : K) (p : {poly K}) :
                                      primitive a p = (can_primitive p) + a%:P.
Proof.
apply/polyP => i.
rewrite coefD !coef_poly coefC ; case: i => [ | i] ; first by rewrite add0r.
by rewrite addr0.
Qed.

Lemma aux_coef_can_prim (p : {poly K}) (i : nat) :
                        (\int p)`_i = if i == 0%N then 0 else p`_i.-1 / (i%:R).
Proof.
case: i => [ | i ] ; first by rewrite eqxx /can_primitive /primitive coef_poly.
rewrite /can_primitive /primitive succnK eqn0Ngt ltn0Sn coef_poly.
rewrite eqn0Ngt ltn0Sn /= -{3}[p]coefK coef_poly ltnS.
by case: (i < size p) => // ; rewrite mul0r.
Qed.

Lemma nth0_primitive (p : {poly K}) (a : K) : (primitive a p)`_0 = a.
Proof. by rewrite coef_poly eqxx. Qed.

Lemma coef0_can_prim (p : {poly K}) : (\int p)`_0 = 0.
Proof. by rewrite aux_coef_can_prim eqxx. Qed.

Lemma coef_can_prim (p : {poly K}) (i : nat) :
                                    i != 0%N -> (\int p)`_i = p`_i.-1 / (i%:R).
Proof. by rewrite aux_coef_can_prim ; move/negbTE ->. Qed.

Lemma can_primC (c : K) : \int (c%:P) = c *: 'X.
Proof.
apply/polyP => i.
rewrite /can_primitive /primitive coef_poly size_polyC -[c *: 'X]coefK.
have [-> | c_neq0 ] := eqVneq c 0.
  by rewrite eqxx /= scale0r size_poly0 coef_poly ltn0 ; case: i.
rewrite c_neq0 /= coef_poly size_scale // size_polyX coefZ coefX.
case: i => [ | i ] ; first by rewrite !eqxx mulr0.
by rewrite coefC ; case: i => [ | i ] ; rewrite ?invr1.
Qed.

Lemma can_primX : \int 'X = (2%:R) ^-1 *: 'X ^+2.
Proof.
rewrite /can_primitive /primitive size_polyX ; apply/polyP => i.
rewrite coef_poly coefZ coefXn coefX.
case: i => [ | i ] ; first by rewrite mulr0.
rewrite eqn0Ngt ltn0Sn /= ; case: i => [ | i ] ; first by rewrite mul0r mulr0.
case: i => [ | i ] ; first by rewrite mul1r mulr1.
by rewrite mulr0.
Qed.

Fact aux_eqSnSm (a b : nat) : (a.+1 == b.+1) = (a == b).
Proof.
apply/eqP/eqP ; last by move ->.
by move/succn_inj.
Qed.

Lemma prim_tfpsXn (m : nat): \int ('X ^+ m) = (m.+1 %:R) ^-1 *: 'X ^+ m.+1.
Proof.
rewrite /can_primitive /primitive size_polyXn ; apply/polyP => i.
rewrite coefZ !coefXn coef_poly !coefXn.
have [-> | /negbTE i_neq_Sm ] := eqVneq i m.+1.
  by rewrite eqxx ltnSn mulr1 eqxx mul1r.
rewrite i_neq_Sm /= mulr0 ; case: (i < m.+2) => [] //.
have [ -> | /negbTE i_neq0 ] := eqVneq i 0%N ; first by rewrite eqxx.
rewrite i_neq0 ; move/negbT : i_neq0 ; move/negbT : i_neq_Sm.
case: i => [ // | i ].
by rewrite aux_eqSnSm => /negbTE -> _ ; rewrite mul0r.
Qed.

Fact coefK2 (R : ringType) (p : {poly R}) (m : nat) :
                                         size p <= m -> \poly_(i < m) p`_i = p.
Proof.
move => leq_sizep_m.
rewrite -[p]coefK ; apply/polyP => i.
rewrite !coef_poly.
have [ lt_i_sizep | leq_sizep_i ] := ltnP i (size p).
  by rewrite (leq_trans lt_i_sizep leq_sizep_m).
by case: (_ < _).
Qed.

Fact widen_poly (R : ringType) (p : {poly R}) (m : nat) :
                   size p <= m -> \poly_(i < size p) p`_i = \poly_(i < m) p`_i.
Proof. by move => leq_sizep_m ; rewrite coefK coefK2. Qed.

Fact can_prim_is_linear : linear can_primitive.
Proof.
move => k p q ; apply/polyP => i.
case: i => [ | i]; first by rewrite coefD coefZ !coef0_can_prim mulr0 addr0.
by rewrite !(aux_coef_can_prim, coefD, coefZ) mulrDl -mulrA.
Qed.

Canonical can_prim_additive := Additive can_prim_is_linear.
Canonical can_prim_linear := Linear can_prim_is_linear.

Lemma can_prim0 : can_primitive 0 = 0.
Proof. exact: linear0. Qed.

Lemma can_primD : {morph can_primitive : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma can_primN : {morph can_primitive : p / - p}.
Proof. exact: linearN. Qed.

Lemma can_primB : {morph can_primitive : p q / p - q}.
Proof. exact: linearB. Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Lemma size_prim_cneq0 (a : K) (p : {poly K}) :
                                  a != 0 -> size (primitive a p) = (size p).+1.
Proof.
move => a_neq0.
rewrite size_poly_eq //=.
have [ -> | /negbTE p_neq0 ] := eqVneq p 0 ; first by rewrite size_poly0 eqxx.
rewrite size_poly_eq0 p_neq0 -lead_coefE mulf_neq0 //.
  by rewrite lead_coef_eq0 p_neq0.
by rewrite invr_eq0 natmul_inj // size_poly_eq0 p_neq0.
Qed.

Lemma size_prim_pneq0 (a : K) (p : {poly K}) :
                                  p != 0 -> size (primitive a p) = (size p).+1.
Proof.
move => /negbTE p_neq0.
rewrite size_poly_eq //= size_poly_eq0 p_neq0 -lead_coefE mulf_neq0 //.
  by rewrite lead_coef_eq0 p_neq0.
by rewrite invr_eq0 natmul_inj // size_poly_eq0 p_neq0.
Qed.

Lemma leq_size_prim (a : K) (p : {poly K}) :
  size (primitive a p) <= (size p).+1.
Proof.
have [ -> | p_neq0 ] := eqVneq p 0.
  by rewrite primitiveE can_prim0 add0r size_poly0 size_polyC leq_b1.
by rewrite size_prim_pneq0.
Qed.

Lemma cancel_deriv_prim (a : K) : cancel (primitive a) (@deriv K).
Proof.
move => p.
rewrite /primitive -{3}[p]coefK ; apply/polyP => i.
rewrite coef_deriv !coef_poly ltnS.
case: (i < size p) ; last by rewrite mul0rn.
rewrite eqn0Ngt ltn0Sn /= -mulr_natr mulrAC -mulrA divrr ?mulr1 //.
by rewrite unitfE natmul_inj.
Qed.

Fact size_deriv (p : {poly K}) : size (p ^`()) = (size p).-1.
Proof.
have [lt_sp_1 | le_sp_1] := ltnP (size p) 2.
  move: (size1_polyC lt_sp_1) => ->.
  by rewrite derivC size_poly0 size_polyC ; case: (_ != _).
rewrite size_poly_eq // !prednK ; last first.
  move: (ltn_predK le_sp_1) => H.
  by move: le_sp_1 ; rewrite -{1}H -[X in _ < X]add1n -add1n leq_add2l.
rewrite -mulr_natr mulf_eq0 ; apply/norP ; split.
  by rewrite -lead_coefE lead_coef_eq0 -size_poly_gt0 (ltn_trans _ le_sp_1).
move: (charf0P K) => char_K_property.
move/char_K_property : char_K_is_zero => char_K.
rewrite char_K -lt0n.
move: (ltn_predK le_sp_1) => H.
by move: le_sp_1 ; rewrite -{1}H -[X in _ < X]add1n -add1n leq_add2l.
Qed.

Lemma deriv0_polyC (p : {poly K}) : deriv p == 0 -> size p <= 1.
Proof.
rewrite -size_poly_eq0 size_deriv ; case: (size p) => [ | s ] //=.
by move/eqP ->.
Qed.

Lemma deriv_poly_eq0 (p : {poly K}) : p`_0 == 0 -> p^`() == 0 -> p = 0.
Proof.
move/eqP => p0_eq0 derivp_eq0.
by move: (size1_polyC (deriv0_polyC derivp_eq0)) ; rewrite p0_eq0.
Qed.

Lemma deriv_poly_eq (p q : {poly K}) : p`_0 == q`_0 -> p^`() == q^`() -> p = q.
Proof.
rewrite -subr_eq0 -coefB -[p^`() == q^`()]subr_eq0 -derivB.
move => coef0_eq0 deriv_eq0 ; apply/eqP.
rewrite -subr_eq0 ; apply/eqP ; move: coef0_eq0 deriv_eq0.
exact: deriv_poly_eq0.
Qed.

(* Lemma can_prim_deriv (p : {poly K}) :
                                    can_primitive (deriv p) = p - ((p`_0) %:P).
Proof.
apply: deriv_poly_eq.
  by rewrite coef0_can_prim coefB coefC eqxx subrr.
by rewrite cancel_deriv_prim derivB derivC subr0.
Qed. *)

Fact prim_tfps_is_linear (n : nat) : linear (@prim_tfps K n).
Proof.
move => k p q; apply: val_inj => /=.
apply/polyP => i.
rewrite coefD coef_modXn coefZ !coef_poly.
case: (i < _) => /=; last by rewrite addr0.
rewrite coefD mulrnDl mulrDl; congr (_ + _); rewrite coef_modXn coefZ.
case: i => [|i /=]; first by rewrite eqxx mulr0n invr0 !mulr0.
have [_|/leq_sizeP big_i] := ltnP i n.+1; first by rewrite mulrA.
rewrite mul0rn mul0r big_i; first by rewrite mul0rn mul0r mulr0.
by rewrite size_tfps.  
Qed.

(* Canonical prim_tfps_is_additive (n : nat) :=
                                    Additive (@prim_tfps K n). *)

Canonical prim_tfps_linear (n : nat) :=
                                      Linear (@prim_tfps_is_linear n).

Lemma prim_tfpsK (n : nat) :
  cancel (@prim_tfps K n) (@deriv_tfps K n.+1).
Proof.
move => p; apply: val_inj; apply/polyP => i; rewrite coef_poly.
have [small_i|/leq_sizeP big_i] := ltnP i n.+1; last by rewrite big_i // size_tfps.
rewrite coef_poly /= ltnS small_i mulr1n -mulr_natr -mulrA [X in _ * X]mulrC.
by rewrite divrr ?mulr1 // unitfE natmul_inj //.
Qed.

Lemma coef0_prim_tfps_is_0 (n : nat) (p : {tfps K n}) :
                                (prim_tfps p) \in (@coef0_is_0 K n.+1).
Proof. by rewrite coef0_is_0E coef_poly eqxx mulr0n invr0 mulr0. Qed.

Lemma coef0_prim_tfps (n : nat) (p : tfps K n) : (prim_tfps p)`_0 = 0.
Proof. by apply/eqP; rewrite -coef0_is_0E coef0_prim_tfps_is_0. Qed.

Variable (n : nat).

Local Notation "c %:S" := (Tfps n (c %:P)) (at level 2).
Local Notation "c %:FPS" := (Tfps n.+1 (c %:P)) (at level 2).

Lemma deriv_tfpsK (p : {tfps K n.+1}) : prim_tfps (deriv_tfps p) = p - ((p`_0) %:FPS).
Proof.
apply: val_inj; apply/polyP => i; rewrite coef_poly.
have [|/leq_sizeP big_i] := ltnP i n.+2; last by rewrite big_i.
case: i => [_|i].
  by rewrite eqxx mulr0n mul0r coefB nth0_Tfps coefC eqxx subrr.
rewrite ltnS => small_i.
rewrite coef_poly coefB !coef_Tfps -lt0n ltn0Sn small_i coefC -mulr_natr mulr1.
by rewrite -mulr_natr -mulrA divrr ?unitfE ?natmul_inj // mulr1 subr0.
Qed.

Lemma deriv_modp (m : nat) (p : {poly K}) :
    (p %% 'X ^+ m.+1)^`() = (p ^`()) %% 'X ^+ m.
Proof.
rewrite {2}[p](divp_eq _ ('X^m.+1)) derivD derivM !modp_add.
rewrite -addrA [X in X + _]modp_eq0 ; last first.
rewrite dvdp_mull // dvdp_Pexp2l ?leqnSn // size_polyX //.
rewrite add0r [X in X + _]modp_eq0 ; last first.
  by rewrite dvdp_mull // derivXn /= -scaler_nat dvdp_scaler2.
rewrite add0r [RHS]modp_small // size_polyXn.
have [-> | p_modXSm_neq0] := eqVneq (p %% 'X^m.+1) 0.
+ by rewrite deriv0 size_poly0.
+ by rewrite (leq_trans _ (leq_modpXn m.+1 p)) // lt_size_deriv.
Qed.

Local Notation "p `d" := (deriv_tfps p) (at level 2).

Lemma deriv_tfps0 (m : nat) : (0 : {tfps K m}) `d = 0.
Proof.
apply: val_inj => /=; rewrite polyseq0; apply/polyP => i.
by rewrite coef_poly coefC mul0rn; case: (_ < _); case: i. 
Qed.

Lemma deriv_tfpsC (c : K) : c %:S `d = 0.
Proof.
apply: val_inj => /=; apply/polyP => i.
rewrite coefC.
rewrite coef_poly.
rewrite coef_poly coefC mul0rn; case: (_ < _); case: i. 

    by apply: val_inj => /=; rewrite deriv_modp derivC !mod0p.
Qed.

Lemma deriv_tfpsD (p q : {tfps K n}) : (p + q)`d = p `d + q `d.
Proof. by apply: val_inj => /=; rewrite derivD modp_add.
Qed.

Lemma deriv_tfpsN (p : {tfps K n}) : (- p)`d = - (p `d).
Proof. by apply: val_inj => /=; rewrite derivN modNp. Qed.

Lemma deriv_tfpsB (p q : {tfps K n}) : (p - q)`d = p `d - q `d.
Proof. by apply: val_inj => /=; rewrite derivB modp_add modNp. Qed.

Lemma deriv_tfpsZ (c : K) (p : {tfps K n}) : (c *: p) `d = c *: (p `d).
Proof.
apply: val_inj => /=; rewrite deriv_modp linearZ /= modp_scalel /=.
move: p; case: n => // p. 
by rewrite [p]pw_is_cst expr1 -horner_coef0 !deriv_modp !derivC !mod0p.
Qed.

Fact deriv_tfps1 : (1 : {tfps K n}) `d = 0.
Proof. by apply: val_inj => /=; rewrite derivC mod0p. Qed.

End Powerderiv.

Local Notation "p `d" := (deriv_tfps p) (at level 2).

Fact modp_mul2 (F : fieldType) (p q m : {poly F}):
                                            ((p %% m) * q) %% m = (p * q) %% m.
Proof. by rewrite mulrC modp_mul mulrC. Qed.

Lemma deriv_tfpsM (K :fieldType) (n : nat) (p q : {tfps K n}) :
          (p * q) `d = (p `d) * (Tfps n.-1 q) + (Tfps n.-1 p) * (q `d).
Proof.
move : p q ; case: n => /= [p q | m p q].
  by rewrite [p]pw_is_cst [q]pw_is_cst -mul_cst !deriv_tfpsC mul0r mulr0 addr0.
apply: val_inj => /=.
rewrite deriv_modp derivM modp_mul modp_mul2 -modp_add modp_mod !modp_add !modp_mul.
by congr (_ + _); rewrite mulrC [in RHS]mulrC modp_mul.
Qed.

Fact truncate_truncated_tfpsV (K :fieldType) (n : nat) (p : {tfps K n}) :
  p`_0 != 0 ->
  Tfps n (truncated_tfps p^-1) = (Tfps n (truncated_tfps p)) ^-1.
Proof.
move => p0_neq0.
have /val_eqP /eqP pdivp : (p / p = 1).
  by rewrite divrr // unit_tfpsE.
have H: (Tfps n (truncated_tfps p)) \is a GRing.unit.
  by rewrite unit_tfpsE nth0_Tfps.
apply: (mulrI H) ; rewrite divrr // ; apply: val_inj => /=.
by rewrite modp_mul modp_mul2.
Qed.

Fact truncate_truncated_tfpsV2 (K :fieldType) (n m : nat) (p : {tfps K n}) :
  m <= n -> p`_0 != 0 ->
  Tfps m (truncated_tfps p^-1) = (Tfps m (truncated_tfps p)) ^-1.
Proof.
move => leq_m_n p0_neq0.
have /val_eqP /eqP pdivp : (p / p = 1).
  apply: divrr.
  by rewrite unit_tfpsE.
have H: (Tfps m (truncated_tfps p)) \is a GRing.unit.
  by rewrite unit_tfpsE nth0_Tfps.
apply: (mulrI H) ; rewrite divrr // ; apply: val_inj => /=.
rewrite modp_mul modp_mul2 -(@modp_modp K _ 'X^m.+1 'X^n.+1) ; last first.
  by rewrite dvdp_exp2l.
have -> : (truncated_tfps p * truncated_tfps p^-1) %% 'X^n.+1 = 1 by [].
apply: modp_small.
by rewrite size_polyC size_polyXn ; apply: (leq_trans (leq_b1 _)).
Qed.

Lemma deriv_tfpsV (K :fieldType) (n : nat) (p : {tfps K n}) :
  p`_0 != 0 ->
  (p ^-1) `d = - (p `d) / (Tfps n.-1 (p ^+ 2)).
Proof.
move => p0_neq0.
move/eqP: (eq_refl (p / p)).
rewrite {2}divrr ; last first.
  by rewrite unit_tfpsE.
move/(congr1 (@deriv_tfps K n)).
rewrite deriv_tfpsM deriv_tfps1.
move/eqP ; rewrite addrC addr_eq0 mulrC.
move/eqP/(congr1 (fun x => x / (Tfps n.-1 p))).
rewrite -mulrA divrr; last by rewrite unit_tfpsE nth0_Tfps.
rewrite mulr1 => ->.
rewrite !mulNr ; congr (- _).
rewrite -mulrA ; congr (_ * _).
rewrite truncate_truncated_tfpsV2 // ; last exact: leq_pred.
rewrite -invrM ?unit_tfpsE ?nth0_Tfps // ; congr (_ ^-1).
rewrite -rmorphM /= ; apply: val_inj => /=.
rewrite modp_modp // dvdp_exp2l //.
by apply: (leq_trans (leq_pred _)).
Qed.

Fact tfps_trunc_mul (K :fieldType) (m n : nat) (p q : {tfps K m}) : n <= m ->
Tfps n (truncated_tfps (p * q)) = (Tfps n (truncated_tfps p)) * (Tfps n (truncated_tfps q)).
Proof.
move => leq_nm; apply: val_inj => /=.
by rewrite modp_modp ?dvdp_exp2l // modp_mul [in RHS]mulrC modp_mul mulrC //.
Qed.
                                                                      
Lemma deriv_tfpsdiv (K :fieldType) (n : nat) (p q : {tfps K n}) :
  q`_0 != 0 ->
  (p / q) `d = (p `d * Tfps n.-1 q - Tfps n.-1 p * q `d)
                                                    / (Tfps n.-1 (q ^+ 2)).
Proof.
move => q0_neq0.
rewrite deriv_tfpsM deriv_tfpsV // mulrBl mulrA mulrN mulNr.
congr (_ - _) ; rewrite -mulrA ; congr (_ * _).
rewrite truncate_truncated_tfpsV2 // ; last exact: leq_pred.
rewrite expr2 tfps_trunc_mul ?leq_pred // invrM ?Tfps_is_unit ?nth_Tfps //.
by rewrite mulrA divrr ?Tfps_is_unit ?nth_Tfps // mul1r.
Qed.

Section CompSeries.
Variable (K : fieldType).

Definition comp_series (m : nat) (q p : {tfps K m}) :=
  if q \in (@coef0_is_0 K m) then Tfps m (comp_poly q p) else 0.

Notation "p \So q" := (comp_series q p) (at level 2).
Notation "p `d" := (deriv_tfps p) (at level 2).

Fact deriv_size1 (R : ringType) (p : {poly R}) : size p <= 1 -> deriv p = 0.
Proof. by move => H_size ; rewrite (size1_polyC H_size) derivC. Qed.

Section Variable_n.
Variable (n : nat).
Local Notation "c %:S" := (Tfps n (c %:P)) (at level 2).

Lemma comp_series_coef0_neq0 (p q : {tfps K n}) :
                                      q \notin (@coef0_is_0 K n) -> p \So q = 0.
Proof. by move/negbTE => p0_neq0 ; rewrite /comp_series p0_neq0. Qed.

Lemma comp_series_coef0_eq0 (p q : {tfps K n}) :
                q \in (@coef0_is_0 K n) -> p \So q = Tfps n (comp_poly q p).
Proof. by move => p0_eq0 ; rewrite /comp_series p0_eq0. Qed.

Section Variable_p.

Variable (p : {tfps K n}).

Lemma pwC_in_coef0_is_0 (c : K) : reflect (c = 0) (c %:S \in @coef0_is_0 K n).
Proof. by rewrite coef0_is_0E nth0_Tfps coefC eqxx; apply: eqP. Qed.

Lemma comp_series0r : p \in (@coef0_is_0 K n) ->  p \So 0 = 0.
Proof.
rewrite comp_series_coef0_eq0 ; last exact: (rpred0 (c0_is_0_keyed K n)).
rewrite truncated_tfps0 comp_poly0r coef0_is_0E => /eqP ->.
by rewrite rmorph0.
Qed.

Lemma comp_seriesr0 : 0 \So p = 0.
Proof.
have [ p0_eq0 | p0_neq0 ] := boolP (p \in (@coef0_is_0 K n)).
+ by rewrite comp_series_coef0_eq0 // comp_poly0 rmorph0.
+ by rewrite comp_series_coef0_neq0.
Qed.

Lemma comp_seriesC (c : K) : c%:S \So p =
                                        (c * (p \in (@coef0_is_0 K n)) %:R) %:S.
Proof.
have [ p0_eq0 | p0_neq0 ] := boolP (p \in (@coef0_is_0 K n)).
+ rewrite comp_series_coef0_eq0 //=.
  rewrite modp_small; last by rewrite size_polyXn size_polyC; apply: (leq_trans (leq_b1 _)).
  by rewrite comp_polyC mulr1.
+ by rewrite mulr0 Tfps0 comp_series_coef0_neq0.
Qed.

Hypothesis (p0_is_0 : p \in (@coef0_is_0 K n)).

Fact comp_series_is_additive : additive (comp_series p).
Proof.
move => u v.
rewrite !comp_series_coef0_eq0 //.
by apply: val_inj => /=; rewrite rmorphB /= modp_add modNp.
Qed.

Fact comp_series_is_linear : linear (comp_series p).
Proof.
move => a q r.
by rewrite !comp_series_coef0_eq0 // !rmorphD /= modp_scalel mod_tfps // !linearZ.
Qed.

End Variable_p.
End Variable_n.

Lemma deriv_tfps_comp (m : nat) (p q : {tfps K m}): p \in (@coef0_is_0 K m) ->
  deriv_tfps (q \So p) = (q `d \So (Tfps m.-1 p)) * p `d.
Proof.
move: p q ; case: m => [ p q p0_eq0 | m p q p0_eq0 ].
+ apply: val_inj => /=.
  rewrite deriv_size1 ; last exact: (size_tfps _).
  rewrite deriv_size1 ; last first.
- move: (pw_is_cst p) ; rewrite -horner_coef0.
  move/(congr1 val) => /= ->.
- by rewrite expr1 modp_small ?size_polyX size_polyC ?ltnS leq_b1.
  by rewrite mod0p mulr0 mod0p.
+ rewrite /= comp_series_coef0_eq0 // comp_series_coef0_eq0 ?p0_is_0 //.
  apply: val_inj => /=.
  rewrite deriv_modp deriv_comp modp_mod modp_mul.
  rewrite mulrC -[LHS]modp_mul mulrC; congr (modp _) ; congr (_ * _). 
  rewrite [q^`() %% 'X^m.+1]modp_small ; last first.
  rewrite size_polyXn (leq_ltn_trans (leq_size_deriv _)) //.
  have [ -> // | ] := eqVneq (size q) 0%N.
  by rewrite -lt0n => sp_gt0; rewrite prednK // size_tfps.
  rewrite (divp_eq (truncated_tfps p) 'X^m.+1) modp_add modp_mull add0r modp_mod.
  rewrite !comp_polyE !modp_summ /= ; apply: eq_bigr => i _.
  rewrite !modp_scalel ; congr (_ *: _).
  rewrite exprDn big_ord_recr /= subnn expr0 mul1r binn mulr1n modp_add.
  rewrite modp_summ /= (eq_bigr (fun j => 0)) => [ | j _].
    by rewrite big1_eq add0r.
  rewrite -scaler_nat modp_scalel ; apply/eqP.
  rewrite scaler_eq0 ; apply/orP ; right.
  apply/eqP ; apply: modp_eq0.
  by rewrite dvdp_mulr // exprMn dvdp_mull // dvdp_exp // subn_gt0.
Qed.

End CompSeries.
