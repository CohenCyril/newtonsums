(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  some doc here                                                            *)
(*****************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype div tuple finfun bigop finset fingroup.
From mathcomp Require Import perm ssralg poly polydiv mxpoly binomial bigop.
From mathcomp Require Import finalg zmodp matrix mxalgebra polyXY ring_quotient.
From Newtonsums Require Import auxresults fraction polydec revpoly.

Import FracField.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Open Local Scope quotient_scope.

Local Notation "p ^ f" := (map_poly f p).

Section MorePolyTheory.

Variable (R : ringType).

Lemma leq_size_deriv (p : {poly R}) : size p^`() <= (size p).-1.
Proof.
have [->|pN0] := eqVneq p 0; first by rewrite deriv0 size_poly0.
by rewrite -ltnS prednK // ?lt_size_deriv // size_poly_gt0. 
Qed.

Fact polyXP (K : fieldType) (p : {poly K}) : reflect (p`_0 = 0) ('X %| p).
Proof. by rewrite -['X]subr0 -polyC0 -horner_coef0; apply: polyXsubCP. Qed.

Lemma p_neq0 (p : {poly R}): (exists (x : R), p.[x] != 0) -> p != 0.
Proof.
by move => [x px_neq0]; move: px_neq0; apply: contra => /eqP ->; rewrite horner0.
Qed.

Fact nth0_eq_nth0 (K : fieldType) (p q : {poly K}) : 
    p %= q -> (p`_0 == 0) = (q`_0 == 0).
Proof.
move => p_eqp_q; rewrite -!horner_coef0.
apply/(sameP eqP).
apply/(equivP eqP).
apply: (rwP2 (polyXsubCP _ _)).
apply: (aux_equivb (polyXsubCP _ _)).
by apply: eqp_dvdr.
Qed.

(* could be useful ? *)
(* Lemma deriv_poly_eq (K : fieldType) (p q : {poly K}) : 
    p`_0 == q`_0 -> p^`() == q^`() -> p = q.
Proof.
rewrite -subr_eq0 -coefB -[p^`() == q^`()]subr_eq0 -derivB.
move => coef0_eq0 deriv_eq0 ; apply/eqP.
rewrite -subr_eq0 ; apply/eqP ; move: coef0_eq0 deriv_eq0.
exact: deriv_poly_eq0.
Qed. *)

End MorePolyTheory.

Section ModPolyTheory.

Variable (K : fieldType).

Fact leq_modpXn m (p : {poly K}) : size (p %% 'X^m) <= m.
Proof.
by rewrite -ltnS (leq_trans (ltn_modpN0 _ _)) // -?size_poly_eq0 size_polyXn.
Qed.

Lemma coef_modXn m (p : {poly K}) i : (p %% 'X^m)`_i =
  if i < m then p`_i else 0.
Proof.
have [lt_i_m|le_m_i] := ltnP; last first.
  by rewrite nth_default // (leq_trans (leq_modpXn _ _)).
have /polyP /(_ i) := divp_eq p 'X^m.
by rewrite coefD coefMXn lt_i_m add0r.
Qed.

Fact modp_sumn (I : Type) (r : seq I) (P : pred I)
               (F : I -> {poly K}) (p : {poly K}) :
               (\sum_(i <- r | P i) F i) %% p = \sum_(i <- r | P i) (F i %% p).
Proof. by rewrite (big_morph ((@modp _)^~ p) (modp_add _) (mod0p _) _). Qed.

Fact modCXn a n : 0 < n -> a%:P %% 'X^n = a%:P :> {poly K}.
Proof. 
move=> lt_0n. 
by rewrite modp_small // size_polyC size_polyXn (leq_ltn_trans (leq_b1 _)).
Qed.

Fact modp_modp (p u v : {poly K}) : u %| v -> (p %% v) %% u = p %% u.
Proof.
move => dvdp_u_v.
have [ -> | v_neq0 ] := eqVneq v 0 ; first by rewrite modp0.
rewrite (divp_eq p v) modp_addl_mul_small ?ltn_modp //.
by rewrite modp_add [X in X + _]modp_eq0 ?dvdp_mull // add0r.
Qed.

Fact modp_mul2 (F : fieldType) (p q m : {poly F}):
                                              ((p %% m) * q) %% m = (p * q) %% m.
Proof. by rewrite mulrC modp_mul mulrC. Qed.

Fact coef0M (p q : {poly K}) : (p * q)`_0 = p`_0 * q`_0.
(* Proof. by rewrite coefM big_ord_recl big_ord0 addr0. Qed. *)
Proof. by rewrite -!horner_coef0 hornerM. Qed.

Fact modX_eq0 (p : {poly K}) (n m : nat) : p`_0 = 0 -> n < m ->
  (p ^+ m) %% 'X^n.+1 = 0.
Proof.
rewrite -horner_coef0 => /polyXsubCP p0_eq0 n_lt_m.
rewrite polyC0 subr0 in p0_eq0.
apply/modp_eq0P.
by rewrite (dvdp_trans (dvdp_exp2l ('X : {poly K}) n_lt_m)) // dvdp_exp2r.
Qed.

(* to remove *)
Fact modp_mul_piqj (p q : {poly K}) n i j : p`_0 = 0 -> q`_0 = 0 ->
  n < i+j -> (p ^+i * q ^+j) %% 'X^n.+1 = 0.
Proof.
move => p0_eq0 q0_eq0 n_lt_addij.
apply/modp_eq0P.
rewrite (dvdp_trans (dvdp_exp2l ('X : {poly K}) n_lt_addij)) // exprD.
by rewrite dvdp_mul // dvdp_exp2r // ; apply/polyXP.
Qed.

End ModPolyTheory.

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

Definition Tfpsp (p : {poly K}) := Tfps_of (leq_modpXn _ p).

Definition tfps_of_fun (f : nat -> K) := Tfps_of (size_poly _ f).

Notation "[ 'tfps' s => F ]" := (tfps_of_fun (fun s => F))
  (at level 0, s ident, only parsing) : tfps_scope.

Implicit Types (f g : {tfps}).

Lemma size_tfps f : size (val f) <= n.+1.
Proof. by case: f. Qed.
Hint Resolve size_tfps.

Lemma tfps_nth_default f j : j > n ->  f`_j = 0.
Proof. by move=> j_big; rewrite nth_default // (leq_trans _ j_big). Qed.

Lemma tfps_coefK f : [tfps s => f`_s] = f.
Proof.
apply/val_inj/polyP=> j; rewrite coef_poly ltnS.
by have  [//|j_big] := leqP; rewrite tfps_nth_default.
Qed.

Lemma coef_tfps s (f : nat -> K) :
  [tfps s => f s]`_s = if s <= n then f s else 0.
Proof. by rewrite coef_poly. Qed.

Lemma eq_tfps (f g : {tfps}) :
  (forall i : 'I_n.+1, f`_i = g`_i) <-> (f = g).
Proof.
split=> [eq_s|-> //]; apply/val_inj/polyP => i /=.
have [i_small|i_big] := ltnP i n.+1; first by rewrite (eq_s (Ordinal i_small)).
by rewrite -[f]tfps_coefK -[g]tfps_coefK !coef_tfps leqNgt i_big.
Qed.

(* zmodType structure *)

Fact zero_tfps_subproof : size (0 : {poly K}) <= n.+1.
Proof. by rewrite size_poly0. Qed.

Definition zero_tfps := Tfps_of zero_tfps_subproof.

Lemma add_tfps_subproof f g :
  size (val f + val g) <= n.+1.
Proof. by rewrite (leq_trans (size_add _ _)) // geq_max !size_tfps. Qed.

Definition add_tfps f g := Tfps_of (add_tfps_subproof f g).

Lemma opp_tfps_proof f : size (- val f) <= n.+1.
Proof. by rewrite size_opp. Qed.

Definition opp_tfps f := Tfps_of (opp_tfps_proof f).

Fact add_tfpsA : associative add_tfps.
Proof. by move => f1 f2 f3; apply/val_inj; apply: addrA. Qed.

Fact add_tfpsC : commutative add_tfps.
Proof. by move => f1 f2; apply/val_inj; apply: addrC. Qed.

Fact add_tfps0f : left_id zero_tfps add_tfps.
Proof. by move => f; apply/val_inj; apply: add0r. Qed.

Fact add_tfpsK : left_inverse zero_tfps opp_tfps add_tfps.
Proof. by move => f; apply/val_inj; apply: addNr. Qed.

Definition tfps_zmodMixin :=
                              ZmodMixin add_tfpsA add_tfpsC add_tfps0f add_tfpsK.
Canonical tfps_zmodType := ZmodType {tfps} tfps_zmodMixin.

Lemma Tfpsp0 : Tfpsp 0 = 0.
Proof. by apply/val_inj => /=; rewrite mod0p. Qed.

(* to remove *)
Lemma val_TfpspC c : val (Tfpsp c%:P) = c%:P.
Proof. by rewrite /= modCXn. Qed.

(* ringType structure *)

Fact one_tfps_proof : size (1 : {poly K}) <= n.+1.
Proof. by rewrite size_polyC (leq_trans (leq_b1 _)). Qed.

Definition one_tfps : {tfps} := Tfps_of one_tfps_proof.

Definition mul_tfps f g := Tfpsp (val f * val g).

Definition hmul_tfps f g := [tfps j => f`_j * g`_j].

Local Notation "f *h g" := (hmul_tfps f g) (at level 2).

Lemma hmul_tfpsC : commutative hmul_tfps.
Proof.
by move=> f1 f2; apply/val_inj/polyP => /= i; rewrite !coef_poly mulrC.
Qed.

Lemma hmul_tfpsA : associative hmul_tfps.
Proof.
move=> f1 f2 f3; apply/val_inj/polyP => /= i.
by rewrite // !coef_poly; case: (_ < _) => //; apply: mulrA.
Qed.

Lemma hmul_tfps0r f : 0 *h f = 0.
Proof.
by apply/val_inj/polyP=> i /=; rewrite coef_poly coef0 mul0r if_same.
Qed.

Lemma hmul_tfpsr0 f : f *h 0 = 0.
Proof. by rewrite hmul_tfpsC hmul_tfps0r. Qed.

Fact left_id_one_mul_tfps : left_id one_tfps mul_tfps.
Proof.
move=> p; apply val_inj; rewrite /= mul1r.
by rewrite modp_small // size_polyXn ltnS.
Qed.

Fact mul_tfpsC : commutative mul_tfps.
Proof. by move=> f1 f2; apply val_inj => /=; rewrite mulrC. Qed.

Fact left_distributive_mul_tfps : left_distributive mul_tfps add_tfps.
Proof. by move=> f1 f2 f3; apply val_inj => /=; rewrite mulrDl modp_add. Qed.

Fact mul_tfpsA : associative mul_tfps.
Proof.
move=> f1 f2 f3 ; apply/val_inj.
by rewrite /= [in RHS]mulrC !modp_mul mulrA mulrC.
Qed.

Fact one_tfps_not_zero : one_tfps != 0.
Proof. by rewrite -val_eqE oner_neq0. Qed.

Definition tfps_ringMixin := ComRingMixin mul_tfpsA mul_tfpsC
               left_id_one_mul_tfps left_distributive_mul_tfps one_tfps_not_zero.

Canonical tfps_ringType := RingType {tfps} tfps_ringMixin.

Canonical tfps_comRingType := ComRingType {tfps} mul_tfpsC.

(* comUnitRingType structure *)

Lemma coef_Tfpsp p s : (Tfpsp p)`_s = if s <= n then p`_s else 0.
Proof. by rewrite coef_modXn. Qed.

Fixpoint coef_inv_rec (p : {poly K}) (m i : nat) : K :=
  match m with
    | O => p`_(locked 0%N) ^-1
    | S m => if i == 0%N then p`_(locked 0%N) ^-1
             else - p`_(locked 0%N) ^-1 * \sum_(k < i) p`_(i - k)
                                        * coef_inv_rec p m k
  end.

Definition coef_inv (p : {poly K}) i : K := coef_inv_rec p i i.

Lemma coef_inv_recE (p : {poly K}) m i : i <= m ->
  coef_inv_rec p m i = coef_inv p i.
Proof.
rewrite /coef_inv; elim: m {-2}m (leqnn m) i=> [k | m IHm].
  by rewrite leqn0 => /eqP -> i ; rewrite leqn0 => /eqP ->.
case=> [k i |k];  first by rewrite leqn0 => /eqP ->.
rewrite ltnS => le_km [ // | i ] ; rewrite ltnS => le_ik /=.
congr (_ * _) ; apply: eq_bigr => l _.
by rewrite !IHm 1?(leq_trans (leq_ord _)) // (leq_trans le_ik).
Qed.

Lemma coef_inv0 (p: {poly K}) : coef_inv p 0 = p`_0 ^-1.
Proof. by rewrite /coef_inv /= -lock. Qed.

Lemma coef_invS (p: {poly K}) j : coef_inv p j.+1 =
    -(p`_0 ^-1) * (\sum_(k < j.+1) p`_(j.+1 - k) * (coef_inv p k)).
Proof.
rewrite /coef_inv /= -lock; congr (_ * _) ; apply: eq_bigr => k _.
by rewrite coef_inv_recE // leq_ord.
Qed.

Definition unit_tfps : pred {tfps} := fun f => (f`_0 \in GRing.unit).

Definition inv_tfps f :=
    if f \in unit_tfps then [tfps s => coef_inv f s] else f.

Fact coef_inv_tfps_subproof f i : f \in unit_tfps ->
  (inv_tfps f)`_i =
  if i > n then 0 else
  if i == 0%N then f`_0 ^-1 else
  - (f`_0 ^-1) * (\sum_(j < i) f`_(i - j) * (inv_tfps f)`_j).
Proof.
have [i_big|i_small] := ltnP; first by rewrite tfps_nth_default.
move=> f_unit; rewrite /inv_tfps f_unit !coef_tfps.
case: i => [|i] in i_small *; first by rewrite coef_inv0.
rewrite i_small coef_invS.
congr (_ * _); apply: eq_bigr => j _; rewrite coef_tfps ifT //.
by rewrite (leq_trans _ i_small) // leqW ?leq_ord.
Qed. 

Fact nonunit_inv_tfps : {in [predC unit_tfps], inv_tfps =1 id}.
Proof. by move=> f; rewrite inE /inv_tfps /= => /negPf ->. Qed.

Fact unit_tfpsP f g : g * f = 1 -> unit_tfps f.
Proof.
move=> /val_eqP /eqP.
move/(congr1 (fun x => (val x)`_O)).
rewrite coef_modXn coef0M coefC eqxx /unit_tfps mulrC => h. 
by apply/unitrPr; exists g`_0.
Qed.

Fact tfps_mulVr : {in unit_tfps, left_inverse 1 inv_tfps *%R}.
Proof.
move=> f f_unit; apply/val_inj; rewrite /inv_tfps f_unit /=.
apply/polyP => i; rewrite coef_modXn.
have [i_small | i_big] := ltnP; last first. 
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

Lemma coef_inv_tfps f i : f \is a GRing.unit -> f^-1`_i =
  if i > n then 0 else
  if i == 0%N then f`_0 ^-1
  else - (f`_0 ^-1) * (\sum_(j < i) f`_(i - j) * f^-1`_j).
Proof. exact: coef_inv_tfps_subproof. Qed.

Lemma hmul_tfpsr1 f : f *h 1 = Tfpsp (f`_0)%:P.
Proof.
apply/val_inj/polyP => s; rewrite coef_tfps coef_Tfpsp !coefC.
by case: s => [|s]; rewrite ?mulr1 ?mulr0.
Qed.

Lemma hmul_tfps1r f : 1 *h f = Tfpsp (f`_0)%:P.
Proof. by rewrite hmul_tfpsC hmul_tfpsr1. Qed.

Canonical tfps_comUnitRingType := [comUnitRingType of {tfps}].

Lemma unit_tfpsE f : (f \in GRing.unit) = (f`_0 != 0).
Proof. by rewrite qualifE /= /unit_tfps unitfE. Qed.

Definition coef0_is_0 : pred_class := fun f : {tfps} => f`_0 == 0.

Lemma coef0_is_0E f : (f \in coef0_is_0) = (f`_0 == 0).
Proof. by rewrite -topredE. Qed.

Definition coef0_is_1 : pred_class := fun f : {tfps} => f`_0 == 1.

Lemma coef0_is_1E f : (f \in coef0_is_1) = (f`_0 == 1).
Proof. by rewrite -topredE. Qed.

Definition exp f :=
  if f \notin coef0_is_0 then 0 else
  Tfpsp (\sum_(i < n.+1) ((i`! %:R) ^-1) *: (val f ^+i)).

Definition log f :=
  if f \notin coef0_is_1 then 0 else
  Tfpsp (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: ((1 - val f) ^+i)).

Fact nth0_mul_tfps f g : (f * g)`_0 = f`_0 * g`_0.
Proof. by rewrite coef_Tfpsp coef0M. Qed.

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
Proof. 
by move => x y; rewrite -!topredE /= /coef0_is_0 nth0_mul_tfps mulf_eq0. 
Qed.

Canonical coef0_is_0_pideal := MkPrimeIdeal coef0_is_0_ideal c0_is_0_prime.

(* to generalize *)
Lemma coef0_1subf_is_0 f :
  f \in coef0_is_1 -> (1 - f) \in coef0_is_0.
Proof.
rewrite ?coef0_is_0E ?coef0_is_1E.
rewrite -!horner_coef0 -!horner_evalE rmorphB /= !horner_evalE hornerC.
by move=> /eqP -> ; rewrite subrr.
Qed.

Lemma mul_c0_is_1_closed : {in coef0_is_1 &, forall f g, f * g \in coef0_is_1}.
Proof.
move=> f g; rewrite !coef0_is_1E nth0_mul_tfps => /eqP -> /eqP ->.
by rewrite mulr1.
Qed.

(* must be subsumed by canonical multiplicative group structure on coef0_is_1*)
Fact nth0_inv f : (f ^-1)`_0 = (f`_0)^-1.
Proof.
have [f_unit|] := boolP (f \is a GRing.unit); first by rewrite coef_inv_tfps.
move=> fNunit; have := fNunit; rewrite -unitrV; move: fNunit.
by rewrite !unit_tfpsE !negbK => /eqP -> /eqP ->; rewrite invr0.
Qed.

Fact inv_c0_is_1_closed : {in coef0_is_1, forall p, p^-1 \in coef0_is_1}.
Proof.
move=> f; rewrite !coef0_is_1E => /eqP p0_is_1.
by rewrite nth0_inv p0_is_1 invr1.
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
  exp f = Tfpsp (\sum_(i < n.+1) ((i`! %:R) ^-1) *: ((val f) ^+i)).
Proof. by rewrite /exp => ->. Qed.

Lemma exp_coef0_isnt_0 f : f \notin coef0_is_0 -> exp f = 0.
Proof. by rewrite /exp => /negPf ->. Qed.

Lemma exp0: exp 0 = 1.
Proof.
apply/val_inj/polyP=> j.
rewrite exp_coef0_is_0 ?rpred0 //=.
rewrite (eq_bigr (fun i => ((nat_of_ord i) == O)%:R))=> [|i]; last first.
  by case: (_ i) => [|k]; rewrite expr0n ?eqxx ?fact0 ?invr1 ?scale1r ? scaler0.
rewrite -(big_mkord predT (fun i => (i == _)%:R)) /=.
rewrite big_ltn // eqxx big_nat /= big1 => [|i /andP [hi _]]; last first.
  by rewrite eqn0Ngt hi.
rewrite addr0 modp_small ?size_polyXn ?size_polyC //. 
by apply: (leq_trans (leq_b1 _)).
Qed.

Lemma log_coef0_is_1 f : f \in coef0_is_1 ->
  log f = Tfpsp (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: ((1 - (val f)) ^+i)).
Proof. by rewrite /log => ->. Qed.

Lemma log_coef0_isnt_1 f : f \notin coef0_is_1 -> log f = 0.
Proof. by rewrite /log => /negPf ->. Qed.

Lemma log1 : log 1 = 0.
Proof.
apply/val_inj/polyP=> j; rewrite log_coef0_is_1 ?rpred1 // coef0 coef_Tfpsp.
case: ifP => // j_small; rewrite coefN big1 ?coef0 ?oppr0 //.
by move=> [|i]; rewrite subrr expr0n ?eqxx ?invr0 ?scale0r ?scaler0.
Qed.

(* Lemma log_coef0_is_1 f : f \in coef0_is_1 ->
  log f = Tfpsp ((- \sum_(1 <= i < n.+2) ((i %:R) ^-1) *: ((1 - (val f)) ^+i))).
Proof.
move => p0_eq1.
rewrite log_coef0_is_1 // ; apply/val_inj => /=.
rewrite (big_nat_recr n.+1) /=; last exact: ltn0Sn.
rewrite [RHS]modNp modp_add modp_scalel modX_eq0 ?leqnn // ; last first.
  move: p0_eq1 ; rewrite -!horner_coef0 -!horner_evalE rmorphB /=.
  by rewrite !horner_evalE hornerC horner_coef0 ; move/eqP -> ; rewrite subrr.
by rewrite scaler0 addr0 modNp.
Qed. *)

Fact add_coef0_is_0  f g :
  f \in coef0_is_0 -> g \in coef0_is_0 -> ((f : {tfps}) + g) \in coef0_is_0.
Proof.
by rewrite !coef0_is_0E coefD; move/eqP -> ; move/eqP -> ; rewrite add0r. Qed.

(* is there a better statement ? something like: *)
(* Lemma coef0_exp f : (exp f)`_0 = (f \notin coef0_is_0)%:R. *)
Lemma coef0_exp f : f \in coef0_is_0 -> (exp f)`_0 = 1.
Proof.
move => f0_eq0.
rewrite exp_coef0_is_0 // coef_modXn ltn0Sn -horner_coef0.
rewrite -horner_evalE rmorph_sum /=.
rewrite (eq_bigr (fun i => ((nat_of_ord i) == 0%N)%:R)) => [ | [i _] _ ] /=.
+ rewrite -(big_mkord predT (fun i => ((i == _)%:R))) big_ltn ?ltnS //. 
  rewrite eqxx /= -natr_sum big_nat_cond.
  rewrite (eq_big (fun i => (0 < i < n.+1)) (fun i => 0%N)) => [ | i | i ].
- by rewrite big1_eq addr0.
- by rewrite andbT.
  by rewrite andbT => /andP [/lt0n_neq0/negbTE -> _].
+ rewrite linearZ /= rmorphX /= horner_evalE horner_coef0.
  move: f0_eq0 ; rewrite coef0_is_0E => /eqP ->.
  rewrite expr0n ; case: i => [ | i'].
- by rewrite fact0 invr1 mul1r.
- by rewrite eqn0Ngt -leqNgt ltn0 mulr0.
Qed.

Lemma coef0_log f : (log f)`_0 = 0.
Proof.
have [f0_eq1|f0_neq1] := boolP (f \in coef0_is_1); last first.
  by rewrite log_coef0_isnt_1 // coefC.
rewrite log_coef0_is_1 // coef_modXn ltn0Sn -horner_coef0.
rewrite -horner_evalE rmorphN rmorph_sum /=.
rewrite big_nat_cond (eq_bigr (fun i => (i == 0%N)%:R)).
+ rewrite -[1%N]add0n big_addn (eq_bigr (fun i => 0)) => [ | i _] ; last first.
    by rewrite addn1.
  by rewrite big1_eq oppr0.
+ move => i /andP [/andP [Hi _] _] /=.
  rewrite linearZ rmorphX rmorphB /= !horner_evalE hornerC horner_coef0.
  move: f0_eq1 ; rewrite coef0_is_1E => /eqP ->.
  by rewrite subrr expr0n eqn0Ngt Hi /= mulr0.
Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Fact natmul_inj (m : nat) : (m%:R == 0 :> K) = (m == 0%N).
Proof. by move/(charf0P K)/(_ m) : char_K_is_zero. Qed.

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
  by rewrite index_translation; symmetry; rewrite /G; reflexivity.
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

(* to remove *)
Fact bigID_ord (R : Type) (idx : R) (op : Monoid.com_law idx) (m : nat)
                                         (P : pred nat) (F : nat -> R) :
\big[op/idx]_(i < m) F i = 
         op (\big[op/idx]_(i < m | P i) F i) (\big[op/idx]_(i < m | ~~ P i) F i).
Proof. by apply: bigID. Qed. 

(* to remove *)
Fact big_ord_rev (R : Type) (idx : R) (op : Monoid.com_law idx) (m : nat)
  (P : nat -> bool) (F : nat -> R) :
  \big[op/idx]_(i < m | P i) F i =
  \big[op/idx]_(i < m | P (m - i.+1)%N) F (m - i.+1)%N.
Proof.
rewrite -(big_mkord P F) big_nat_rev (big_mkord _ _).
by apply: eq_bigr ; rewrite add0n.
Qed.

Lemma exp_is_morphism :
                {in coef0_is_0 &, {morph exp : f g / f + g >-> f * g}}.
Proof.
move => f g f0_eq0 g0_eq0 /=.
rewrite ?(exp_coef0_is_0, add_coef0_is_0) //.
apply/val_inj => /=; apply/val_inj => /=.
rewrite modp_mul mulrC modp_mul -mulrC.
rewrite coef0_is_0E -!horner_coef0 in f0_eq0 g0_eq0.
move/eqP: g0_eq0 ; move/eqP : f0_eq0.
move: f g => [f fr] [g gr] /=.
rewrite !horner_coef0 => f0_eq0 g0_eq0.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in i'`!%:R^-1 *:
         (\sum_(j < i'.+1) f ^+ (i' - j) * g ^+ j *+ 'C(i', j)))) ; last first.
  by move => i _ ; rewrite exprDn.
rewrite (big_distrl _ _ _) /=.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in (\sum_(j < i' .+1)
        ((j`! * (i' -j)`!)%:R) ^-1 *: (f ^+ (i' - j) * g ^+ j)))) ; last first.
  move => [i i_lt_Sn] _ /=.
  rewrite scaler_sumr ; apply: eq_bigr => [ /= [j j_lt_Si]] _ /=.
  rewrite -mulrnAl scalerAl -scaler_nat scalerA -scalerAl ; congr(_ *: _).
  have factr_neq0 k : k`!%:R != 0 :> K
                              by rewrite (proj1 (charf0P _)) // -lt0n fact_gt0.
  apply: (mulfI (factr_neq0 i)) ; rewrite mulVKf //.
  have den_neq0 :  (j`! * (i - j)`!)%:R != 0 :> K by rewrite natrM mulf_neq0.
  by apply: (mulIf den_neq0) ; rewrite mulfVK // -natrM bin_fact.
rewrite [in RHS](eq_bigr (fun i => let i' := (nat_of_ord i) in (\sum_(j < n.+1)
                    ((i'`! * j`!)%:R^-1) *: (f ^+ i' * g ^+ j)))) ; last first.
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
  (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j)) %% 'X^n.+1 =
  (\sum_(i < n.+1) \sum_(j < n.+1 | i+j <= n)
  (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j)) %% 'X^n.+1.
  rewrite !modp_sumn ; apply: eq_bigr => [[i i_lt_Sn]] _ /=.
  rewrite !modp_sumn.
  rewrite (bigID_ord _ _ (fun j => i + j <= n)
        (fun x => ((i`! * x`!)%:R^-1 *: (f ^+ i * g ^+ x)) %% 'X^n.+1)) /=.
  rewrite -[RHS]addr0 ; congr (_ + _).
  rewrite -(big_mkord (fun j => ~~ (i + j <= n))
                      (fun j => ((i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j)) %% 'X^n.+1)).
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
        i' + j < n.+1) (i'`! * j`!)%:R^-1 *: (f ^+ i' * g ^+ j))) ; last first.    
  move => i _.
  by apply: eq_bigr.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in \sum_(j < i'.+1)
           (j`! * (i' - j)`!)%:R^-1 *: (f ^+ j * g ^+ (i' - j)))) ; last first.
  move => i _.
  rewrite /= (big_ord_rev _ i.+1 predT
             (fun j => (j`! * (i - j)`!)%:R^-1 *: (f ^+ (i - j) * g ^+ j))) /=.
  apply: eq_bigr => j _.
  by rewrite !subSS subnBA -1?ltnS // !addKn mulnC.
by rewrite (triangular_index_bigop _
                      (fun i j => (i`! * j`!)%:R^-1 *: (f ^+ i * g ^+ j))) /=;
  last exact: ltnSn.
Qed.

(* unitAlgType structure *)

Definition scale_tfps (c : K) f := Tfpsp (c *: (val f)).

Fact scale_tfpsA a b f : scale_tfps a (scale_tfps b f) = scale_tfps (a * b) f.
Proof. 
by apply/val_inj => /=; rewrite modp_scalel modp_mod -modp_scalel scalerA.
Qed.

Fact scale_1tfps : left_id (1 : K) scale_tfps.
Proof.
move=> x; apply/val_inj => /=.
by rewrite scale1r modp_small // size_polyXn ltnS.
Qed.

Fact scale_tfpsDl f: {morph scale_tfps^~ f : a b / a + b}.
Proof.
move=> a b ; apply/val_inj => /=.
by rewrite scalerDl modp_add.
Qed.

Fact scale_tfpsDr (a : K) : {morph scale_tfps a : f g / f + g}.
Proof. by move=> f g; apply/val_inj => /=; rewrite scalerDr modp_add. Qed.

Fact scale_tfpsAl (a : K) f g : scale_tfps a (f * g) = scale_tfps a f * g.
Proof.
apply/val_inj => /=.
rewrite modp_scalel modp_small; last by rewrite ltn_modp expf_neq0 // polyX_eq0.
by rewrite [in RHS]mulrC modp_mul [in RHS]mulrC -modp_scalel -scalerAl.
Qed.

Definition tfps_lmodMixin := LmodMixin scale_tfpsA scale_1tfps
                                       scale_tfpsDr scale_tfpsDl.

Canonical tfps_lmodType := Eval hnf in LmodType K {tfps} tfps_lmodMixin.

Canonical tfps_lalgType := Eval hnf in LalgType K {tfps} scale_tfpsAl.

Canonical tfps_algType := CommAlgType K {tfps}.

Canonical unit_tfpsAlgType := Eval hnf in [unitAlgType K of {tfps}].

Fact val_mul_tfps f g : val (f * g) = (val f) * (val g) %% 'X^n.+1.
Proof. by []. Qed.

Fact val_exp_tfps f (m : nat) :
  val (f ^+ m) = (val f ^+ m) %% 'X^n.+1.
Proof.
elim: m => [|m ihm] //=; first by rewrite expr0 modCXn.
by rewrite exprS /= ihm modp_mul -exprS.
Qed.

End TruncatedPowerSeries.

Notation "{ 'tfps' K n }" := (tfps_of n (Phant K))
  (at level 0, K at next level, format "{ 'tfps'  K  n }").

Notation "[ 'tfps' s => F ]" := (tfps_of_fun _ (fun s => F))
  (at level 0, s ident, only parsing) : tfps_scope.

Hint Resolve size_tfps.

Definition divfX (K : fieldType) (m : nat) (f : {tfps K m}) := 
    Tfpsp m.-1 (f %/ 'X).

Lemma divfXE (K : fieldType) (m : nat) (f : {tfps K m}) : 
  f \in (@coef0_is_0 K m) -> divfX f = [tfps i => f`_i.+1].
Proof.
move/eqP/polyXP; rewrite dvdp_eq /divfX; move/eqP => h.
rewrite [in RHS]h; apply/eq_tfps => i.
by rewrite coef_poly coef_modXn coefMX.
Qed.

Section MapTfps.

Variables (K L : fieldType) (n : nat) (f : {rmorphism K -> L}).

Definition map_tfps (g : {tfps K n}) := Tfpsp n (map_poly f (val g)).

Lemma map_tfpsM (g h : {tfps K n}) :
           map_tfps (g * h) = (map_tfps g) * (map_tfps h).
Proof.
apply/val_inj => /=.
rewrite map_modp rmorphX /= map_polyX modp_mod rmorphM modp_mul.
by rewrite [in RHS]mulrC modp_mul mulrC.
Qed.

Fact map_tfps_is_additive : additive map_tfps.
Proof.
move => x y; apply/val_inj => /=.
by rewrite rmorphB /= modp_add modNp.
Qed.

Canonical map_tfps_additive := Additive map_tfps_is_additive.

Fact map_tfps_is_multiplicative : multiplicative map_tfps.
Proof. 
split => [x y|]; first by rewrite map_tfpsM //.
apply/val_inj => /=.
rewrite rmorph1 modp_small // size_polyC size_polyXn.
by rewrite (leq_ltn_trans (leq_b1 _)).
Qed.

Canonical map_tfps_rmorphism := AddRMorphism map_tfps_is_multiplicative.

Lemma map_tfpsZ (c : K) g : (map_tfps (c *: g)) =  (f c) *: (map_tfps g).
Proof.
apply/val_inj => /=.
by rewrite map_modp rmorphX /= map_polyX linearZ [in LHS]modp_scalel.
Qed.

Local Notation "c %:S" := (Tfpsp n (c %:P)) (at level 2).

(* to remove ? *)
Lemma mul_cst (c d : K) : (c * d) %:S = (c %:S) * (d %:S).
Proof.
apply/val_inj => /=; rewrite polyC_mul modp_mul.
by rewrite [in RHS]mulrC modp_mul mulrC.
Qed.

Canonical map_tfps_linear := let R := ({tfps K n}) in
                       AddLinear (map_tfpsZ : scalable_for (f \; *:%R) map_tfps).

Canonical map_tfps_lrmorphism := [lrmorphism of map_tfps].

Local Notation "g ^f" := (map_tfps g).
Local Notation "g *h h" := (hmul_tfps g h) (at level 2).

Lemma map_hmul g h : (g *h h) ^f = (g ^f) *h (h ^f).
Proof.
apply/val_inj => /=; rewrite -polyP => i.
rewrite coef_modXn coef_map 2!coef_poly !coef_modXn.
by case: (i < n.+1) => //=; rewrite rmorphM !coef_map.
Qed.

Lemma map_tfps_injective : injective map_tfps.
Proof.
move => x y; move/val_eqP => /=.
rewrite ?(modp_small, (size_polyXn, size_map_poly, ltnS, size_tfps)) //.
by move/val_eqP => H; move: (map_poly_inj f H); apply/val_inj.
Qed.

End MapTfps.

(* use notation %:S in RHS*)
Lemma tfps_is_cst (K : fieldType) (g : tfps K 0%N) : g = Tfpsp _ ((g`_0) %:P).
Proof.
apply/val_inj => /=.
rewrite expr1 modp_small; last first.
  by rewrite size_polyX size_polyC (leq_ltn_trans (leq_b1 _)).
by apply: size1_polyC; rewrite size_tfps.
Qed.

Lemma map_tfps_divfX (K L : fieldType) (f : {rmorphism K -> L})
  (m : nat) (g : tfps K m) :
  map_tfps f (divfX g) = divfX (map_tfps f g).
Proof.
apply/val_inj => /=.
rewrite map_modp rmorphX /= map_polyX modp_mod map_divp map_polyX.
by rewrite [(_ ^ _ %% _)]modp_small // size_polyXn size_map_poly ltnS size_tfps.
Qed.

Section Truncated_Tfps.

Variables (K : fieldType) (n : nat).

Fact tfps0 : Tfpsp n (0 : {poly K}) = 0.
Proof. by apply/val_inj => /=; rewrite mod0p. Qed.

Fact tfps1 : Tfpsp n (1 : {poly K}) = 1.
Proof.
apply/val_inj => /=.
by rewrite modp_small // size_polyC size_polyXn (leq_ltn_trans (leq_b1 _)).
Qed.

Fact Tfpsp_is_additive : additive (@Tfpsp K n).
Proof. by move => f g; apply/val_inj => /=; rewrite modp_add modNp. Qed.

Canonical Tfpsp_additive := Additive Tfpsp_is_additive.

Lemma Tfpsp_is_multiplicative: multiplicative (@Tfpsp K n).
Proof.
split => [f g|]; last exact: tfps1.
by apply/val_inj => /=; rewrite modp_mul [in RHS]mulrC modp_mul mulrC.
Qed.

Canonical Tfpsp_rmorphism := AddRMorphism Tfpsp_is_multiplicative.

Fact TfpspZ (c : K) (p : {poly K}): (Tfpsp n (c *: p))=  c *:(Tfpsp n p).
Proof. by apply/val_inj => /=; rewrite -modp_scalel modp_mod. Qed.

Canonical Tfpsp_linear := AddLinear TfpspZ.

Canonical Tfpsp_lrmorphism := [lrmorphism of (Tfpsp n)].

Lemma nth0_Tfpsp (p : {poly K}) : (Tfpsp n p)`_0 = p`_0.
Proof. by rewrite coef_modXn ltn0Sn. Qed.

Lemma Tfpsp_is_unit (p : {poly K}) :
                                    ((Tfpsp n p) \is a GRing.unit) = (p`_0 != 0).
Proof. by rewrite unit_tfpsE nth0_Tfpsp. Qed.

Lemma TfpspE (p : {poly K}) : p %% 'X^ n.+1 = Tfpsp n p.
Proof. by apply/val_inj => /=. Qed.

Definition deriv_tfps : {tfps K n} -> {tfps K n.-1} :=
    fun f => [tfps s => f`_s.+1 *+ s.+1].

Definition prim_tfps (n : nat) : {tfps K n} -> {tfps K n.+1} :=
    fun f => [tfps s => f`_s.-1 *+ (s != 0%N) / s%:R].

(* to remove *)
Fact one_sub_CX_0_eq_1 (a : K) : (1 - a *: 'X).[0] = 1.
Proof.
rewrite -horner_evalE rmorphB /= !horner_evalE.
by rewrite -mul_polyC hornerCM hornerX mulr0 hornerC subr0.
Qed.

Fact mod_tfps (m : nat) (f : {tfps K n}) : n <= m -> f %% 'X^m.+1 = (val f).
Proof.
move => leq_nm.
by rewrite modp_small // size_polyXn ltnS (leq_trans (size_tfps _)).
Qed.

Fact mod_deriv_tfps (m : nat) (f : {tfps K n}) : n <= m -> 
  (val f)^`() %% 'X^m = (val f)^`().
Proof.
move => leq_nm; rewrite modp_small // size_polyXn ltnS.
rewrite (leq_trans _ leq_nm) // (leq_trans (leq_size_deriv _)) //.
have [->//|sfN0] := eqVneq (size (val f)) 0%N.
by rewrite -ltnS prednK ?size_tfps // lt0n.
Qed.

Lemma deriv_tfpsE (f : {tfps K n}) : deriv_tfps f = Tfpsp n.-1 (val f)^`().
Proof. 
by apply/val_inj; apply/polyP => i; rewrite coef_poly coef_modXn coef_deriv. 
Qed.

Lemma Tfpsp_Tfpsp (m : nat) (p : {poly K}) : m <= n ->
  Tfpsp m (Tfpsp n p) = Tfpsp m p. 
Proof. by move=> le_mn; apply/val_inj=> /=; rewrite modp_modp // dvdp_exp2l. Qed.

End Truncated_Tfps.

Lemma truncate_map_poly (K K' : fieldType) (m : nat)
                        (f : {rmorphism K -> K'}) (p : {poly K}) :
                     @Tfpsp K' m (p ^ f) = map_tfps f (Tfpsp m p).
Proof. by apply/val_inj => /=; rewrite map_modp map_polyXn modp_mod. Qed.

Section Powerderiv.

Variable (K : fieldType).

Definition prim (p : {poly K}) :=
    \poly_(i < (size p).+1) (p`_i.-1 *+ (i != 0%N) / (i%:R)).

Local Notation "\int p" := (prim p) (at level 2).

Lemma aux_coef_prim (p : {poly K}) (i : nat) :
                        (\int p)`_i = if i == 0%N then 0 else p`_i.-1 / (i%:R).
Proof.
case: i => [| i]; first by rewrite eqxx coef_poly invr0 mulr0.
rewrite succnK eqn0Ngt ltn0Sn coef_poly.
rewrite eqn0Ngt ltn0Sn /= -{3}[p]coefK coef_poly ltnS.
by case: (i < size p) => //; rewrite mul0r.
Qed.

Lemma coef0_prim (p : {poly K}) : (\int p)`_0 = 0.
Proof. by rewrite aux_coef_prim eqxx. Qed.

Lemma coef_prim (p : {poly K}) (i : nat) :
                                    i != 0%N -> (\int p)`_i = p`_i.-1 / (i%:R).
Proof. by rewrite aux_coef_prim ; move/negbTE ->. Qed.

Lemma primC (c : K) : \int (c%:P) = c *: 'X.
Proof.
apply/polyP => i.
rewrite /prim /prim coef_poly size_polyC -[c *: 'X]coefK.
have [-> | c_neq0 ] := eqVneq c 0.
  rewrite eqxx /= scale0r size_poly0 coef_poly ltn0; case: i => [|i].
    by rewrite invr0 mulr0.
    by rewrite coefC.
rewrite c_neq0 /= coef_poly size_scale // size_polyX coefZ coefX.
congr if_expr; case: i => [|i]; first by rewrite invr0 !mulr0.
rewrite coefC mulr1n.
case: i => [|i]; first by rewrite !eqxx invr1.
by rewrite /= mul0r mulr0.
Qed.

Lemma primX : \int 'X = (2%:R) ^-1 *: 'X ^+2.
Proof.
rewrite /prim /prim size_polyX ; apply/polyP => i.
rewrite coef_poly coefZ coefXn coefX.
case: i => [|i]; first by rewrite invr0 !mulr0.
rewrite eqn0Ngt ltn0Sn /=; case: i => [ | i ] ; first by rewrite mul0r mulr0.
case: i => [|i]; first by rewrite mul1r mulr1.
by rewrite mulr0.
Qed.

Lemma prim_tfpsXn (m : nat): \int ('X ^+ m) = (m.+1 %:R) ^-1 *: 'X ^+ m.+1.
Proof.
rewrite /prim /prim size_polyXn ; apply/polyP => i.
rewrite coefZ !coefXn coef_poly !coefXn.
have [-> | /negbTE i_neq_Sm ] := eqVneq i m.+1.
  by rewrite eqxx ltnSn mulr1 eqxx mul1r.
rewrite i_neq_Sm /= mulr0 ; case: (i < m.+2) => [] //.
have [ -> | /negbTE i_neq0 ] := eqVneq i 0%N; first by rewrite eqxx invr0 mulr0.
rewrite i_neq0 ; move/negbT : i_neq0 ; move/negbT : i_neq_Sm.
case: i => [ // | i ].
by rewrite (inj_eq succn_inj) => /negbTE -> _ ; rewrite mul0r.
Qed.

Fact prim_is_linear : linear prim.
Proof.
move => k p q ; apply/polyP => i.
case: i => [ | i]; first by rewrite coefD coefZ !coef0_prim mulr0 addr0.
by rewrite !(aux_coef_prim, coefD, coefZ) mulrDl -mulrA.
Qed. 

Canonical prim_additive := Additive prim_is_linear.
Canonical prim_linear := Linear prim_is_linear.

(* tests *)
Fact prim0 : prim 0 = 0.
Proof. exact: linear0. Qed.

Fact primD : {morph prim : p q / p + q}.
Proof. exact: linearD. Qed.

Fact primN : {morph prim : p / - p}.
Proof. exact: linearN. Qed.

Fact primB : {morph prim : p q / p - q}.
Proof. exact: linearB. Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Lemma pred_size_prim (p : {poly K}) : (size (prim p)).-1 = size p.
Proof.
have [->|/negbTE p_neq0] := eqVneq p 0; first by rewrite prim0 size_poly0.
rewrite size_poly_eq // size_poly_eq0 p_neq0 -lead_coefE mulf_neq0 //.
  by rewrite lead_coef_eq0 p_neq0.
by rewrite invr_eq0 natmul_inj // size_poly_eq0 p_neq0.
Qed.

Lemma primK : cancel prim (@deriv K).
Proof.
move => p.
rewrite /prim -{3}[p]coefK ; apply/polyP => i.
rewrite coef_deriv !coef_poly ltnS.
case: (_ < _); last by rewrite mul0rn.
by rewrite eqn0Ngt ltn0Sn -mulr_natr mulrAC -mulrA divff ?natmul_inj // mulr1.
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

Fact prim_tfps_is_linear (n : nat) : linear (@prim_tfps K n).
Proof.
move => k p q; apply/val_inj => /=.
apply/polyP => i.
rewrite coefD coef_modXn coefZ !coef_poly.
case: (i < _) => /=; last by rewrite addr0.
rewrite coefD mulrnDl mulrDl; congr (_ + _); rewrite coef_modXn coefZ.
case: i => [|i /=]; first by rewrite eqxx mulr0n invr0 !mulr0.
have [_|/leq_sizeP big_i] := ltnP; first by rewrite mulrA.
rewrite mul0rn mul0r big_i; first by rewrite mul0rn mul0r mulr0.
by rewrite size_tfps.  
Qed.

Canonical prim_tfps_linear (n : nat) := Linear (@prim_tfps_is_linear n).

Lemma prim_tfpsK (n : nat) : cancel (@prim_tfps K n) (@deriv_tfps K n.+1).
Proof.
move => p; apply/val_inj; apply/polyP => i; rewrite coef_poly.
have [small_i|/leq_sizeP big_i] := ltnP; last by rewrite big_i // size_tfps.
rewrite coef_poly /= ltnS small_i mulr1n -mulr_natr -mulrA [X in _ * X]mulrC.
by rewrite divff ?natmul_inj // mulr1.
Qed.

Lemma coef0_prim_tfps_is_0 (n : nat) (p : {tfps K n}) :
                                (prim_tfps p) \in (@coef0_is_0 K n.+1).
Proof. by rewrite coef0_is_0E coef_poly eqxx mulr0n invr0 mulr0. Qed.

Lemma coef0_prim_tfps (n : nat) (p : tfps K n) : (prim_tfps p)`_0 = 0.
Proof. by apply/eqP; rewrite -coef0_is_0E coef0_prim_tfps_is_0. Qed.

Variable (n : nat).
Local Notation "c %:S" := (Tfpsp n (c %:P)) (at level 2).
Local Notation "c %:S" := (Tfpsp n (c %:P)) (at level 2).
Local Notation "c %:FPS" := (Tfpsp n.+1 (c %:P)) (at level 2).

(* change this statement to {in coef0_is_0 ... cancel} *)
Lemma deriv_tfpsK (f : {tfps K n.+1}) : 
  prim_tfps (deriv_tfps f) = f - ((f`_0) %:FPS).
Proof.
apply/val_inj; apply/polyP => i; rewrite coef_poly.
have [|/leq_sizeP big_i] := ltnP; last by rewrite big_i.
case: i => [_|i].
  by rewrite eqxx mulr0n mul0r coefB nth0_Tfpsp coefC eqxx subrr.
rewrite ltnS => small_i.
rewrite coef_poly coefB !coef_Tfpsp -lt0n ltn0Sn small_i coefC -mulr_natr mulr1.
by rewrite -mulr_natr -mulrA divff ?natmul_inj // mulr1 subr0.
Qed.

(* can be generalized with R ? *)
Lemma deriv_modp (m : nat) (p : {poly K}) :
    (p %% 'X ^+ m.+1)^`() = (p ^`()) %% 'X ^+ m.
Proof.
rewrite {2}[p](divp_eq _ ('X^m.+1)) derivD derivM !modp_add.
rewrite -addrA [X in X + _]modp_eq0 ; last first.
rewrite dvdp_mull // dvdp_Pexp2l ?leqnSn // size_polyX //.
rewrite add0r [X in X + _]modp_eq0 ; last first.
  rewrite dvdp_mull // derivXn /= -scaler_nat. 
  have [->|Sm_neq0] := eqVneq (m.+1)%:R (0 : K).
    by rewrite scale0r dvdp0.
  by rewrite dvdp_scaler.
rewrite add0r [RHS]modp_small // size_polyXn.
have [-> | p_modXSm_neq0] := eqVneq (p %% 'X^m.+1) 0.
+ by rewrite deriv0 size_poly0.
+ by rewrite (leq_trans _ (leq_modpXn m.+1 p)) // lt_size_deriv.
Qed.

Local Notation "f `d" := (deriv_tfps f) (at level 2).

Fact deriv_tfps0 (m : nat) : (0 : {tfps K m}) `d = 0.
Proof.
apply/val_inj => /=; rewrite polyseq0; apply/polyP => i.
by rewrite coef_poly coefC mul0rn; case: (_ < _); case: i. 
Qed.

(* I can simplify this proof ? *)
Lemma deriv_tfpsC (c : K) : c %:S `d = 0.
Proof.
apply/val_inj => /=; apply/polyP => i.
rewrite modp_small; last first.
  by rewrite size_polyC size_polyXn (leq_ltn_trans (leq_b1 _)).
rewrite coef_poly coefC if_same polyseqC.
by case: (_ < _) => //; case: (_ == _); rewrite /= ?nth_nil mul0rn.
Qed.

Fact deriv_tfpsD (f g : {tfps K n}) : (f + g)`d = f `d + g `d.
Proof.
apply/val_inj; apply/polyP => i; rewrite coefD !coef_poly coefD.
by case: (_ < _) => //=; rewrite ?addr0 // -mulrnDl.
Qed.

Fact deriv_tfpsN (f : {tfps K n}) : (- f)`d = - (f `d).
Proof.
apply/val_inj; apply/polyP => i; rewrite coefN !coef_poly.
by case: (_ < _) => //; rewrite ?oppr0 //; rewrite -mulNrn coefN.
Qed.

Fact deriv_tfpsB (f g : {tfps K n}) : (f - g)`d = f `d - g `d.
Proof.
apply/val_inj; apply/polyP => i; rewrite coefB !coef_poly coefB.
by case: (_ < _) => //=; rewrite ?subr0 // -mulrnBl.
Qed.

Fact deriv_tfpsZ (c : K) (f : {tfps K n}) : (c *: f) `d = c *: (f `d).
Proof.
apply/val_inj; apply/polyP => i.
rewrite coef_poly coef_modXn !coefZ coef_modXn !coefZ coef_poly.
congr if_expr; rewrite [in RHS]fun_if mulr0 ltnS.
rewrite [LHS](@fun_if _ _ (fun x => x *+i.+1)) mul0rn.
move: f; case: n => [p|m p]; last by congr if_expr; rewrite mulrnAr.
by rewrite [p]tfps_is_cst coef_Tfpsp mul0rn mulr0 if_same.
Qed.

Fact onefE : (1 : {tfps K n}) = 1 %:S.
Proof.
apply/val_inj => /=.
by rewrite modp_small // ?size_polyC ?size_polyXn (leq_ltn_trans (leq_b1 _)).
Qed.

End Powerderiv.

Local Notation "f `d" := (deriv_tfps f) (at level 2).

Lemma deriv_tfpsM (K :fieldType) (n : nat) (f g : {tfps K n}) :
          (f * g) `d = (f `d) * (Tfpsp n.-1 g) + (Tfpsp n.-1 f) * (g `d).
Proof.
move : f g ; case: n => /= [f g | m f g].
  rewrite [f]tfps_is_cst [g]tfps_is_cst -mul_cst !deriv_tfpsC mul0r mulr0.
  by rewrite addr0.
apply/val_inj; rewrite !deriv_tfpsE //=.   
rewrite deriv_modp derivM modp_mul modp_mul2 -modp_add modp_mod !modp_add.
by rewrite !modp_mul; congr (_ + _); rewrite mulrC [in RHS]mulrC modp_mul.
Qed.

Fact TfpsVf m (K :fieldType) n (f : {tfps K n}) :
  m <= n ->
  Tfpsp m (f^-1) = (Tfpsp m f) ^-1.
Proof.
move=> leq_mn.
have [/eqP p0_eq0|p0_neq0] := eqVneq f`_0 0.
  by rewrite ?(invr_out, unit_tfpsE, nth0_Tfpsp, negbK).
apply: (@mulrI _ (Tfpsp m f)); rewrite ?divrr ?(unit_tfpsE, nth0_Tfpsp) //.
rewrite -rmorphM; apply/val_inj => /=.
rewrite -(@modp_modp K _ 'X^m.+1 'X^n.+1); last by rewrite dvdp_exp2l.
rewrite -val_mul_tfps divrr ?unit_tfpsE //.
by rewrite modp_small // size_polyC size_polyXn (leq_ltn_trans (leq_b1 _)).
Qed.

Lemma deriv_tfpsV (K :fieldType) (n : nat) (f : {tfps K n}) :
  f \notin (@coef0_is_0 _ _) ->
  (f ^-1) `d = - (f `d) / (Tfpsp n.-1 (f ^+ 2)).
Proof.
move => p0_neq0.
move/eqP: (eq_refl (f / f)).
rewrite {2}divrr ; last first.
  by rewrite unit_tfpsE.
move/(congr1 (@deriv_tfps K n)).
rewrite deriv_tfpsM onefE deriv_tfpsC.
move/eqP ; rewrite addrC addr_eq0 mulrC.
move/eqP/(congr1 (fun x => x / (Tfpsp n.-1 f))).
rewrite -mulrA divrr; last by rewrite unit_tfpsE nth0_Tfpsp.
rewrite mulr1 => ->.
rewrite !mulNr ; congr (- _).
rewrite -mulrA ; congr (_ * _).
rewrite TfpsVf // ?leq_pred // -invrM ?unit_tfpsE ?nth0_Tfpsp //; congr (_ ^-1).
rewrite -rmorphM /=; apply/val_inj => /=.
by rewrite modp_modp // dvdp_exp2l // (leq_ltn_trans (leq_pred _)).
Qed.
                                                             
Lemma deriv_div_tfps (K :fieldType) (n : nat) (f g : {tfps K n}) :
  g`_0 != 0 ->
  (f / g) `d = (f `d * Tfpsp n.-1 g - Tfpsp n.-1 f * g `d)
                                                    / (Tfpsp n.-1 (g ^+ 2)).
Proof.
move => g0_neq0.
rewrite deriv_tfpsM deriv_tfpsV // mulrBl mulrA mulrN mulNr.
congr (_ - _) ; rewrite -mulrA ; congr (_ * _).
rewrite TfpsVf // ; last exact: leq_pred.
rewrite expr2 ?leq_pred //. 
have -> : Tfpsp n.-1 (g * g) = Tfpsp n.-1 ((val g) * g).
  apply/val_inj => /=.
  rewrite modp_modp ?dvdp_exp2l //. 
  by clear g0_neq0 f g; case: n => //=. 
rewrite rmorphM /= invrM ?Tfpsp_is_unit ?nth_Tfpsp //.
by rewrite mulrA divrr ?Tfpsp_is_unit ?nth_Tfpsp // mul1r.
Qed. 

Section Canonical_deriv_tfps.

Variables (K :fieldType) (n : nat).

Lemma deriv_tfps_is_additive : additive (@deriv_tfps K n).
Proof. by move => f g; rewrite deriv_tfpsB. Qed.

Canonical deriv_tfps_additive := Additive deriv_tfps_is_additive.

Lemma deriv_tfps_is_linear : linear (@deriv_tfps K n).
Proof. by move => c f g; rewrite deriv_tfpsD deriv_tfpsZ. Qed.

Canonical deriv_tfps_linear := Additive deriv_tfps_is_linear.

End Canonical_deriv_tfps.

Section CompSeries.
Variable (K : fieldType).
  
Definition comp_tfps m (g p : {tfps K m}) :=
  if g \in (@coef0_is_0 K m) then Tfpsp m (comp_poly g p) else 0.

Notation "f \So g" := (comp_tfps g f) (at level 2).
Notation "f `d" := (deriv_tfps f) (at level 2).

Section Variable_n.
Variable (n : nat).
Local Notation "c %:S" := (Tfpsp n (c %:P)) (at level 2).

Lemma comp_tfps_coef0_neq0 (f g : {tfps K n}) :
                                      g \notin (@coef0_is_0 K n) -> f \So g = 0.
Proof. by move/negbTE => p0_neq0; rewrite /comp_tfps p0_neq0. Qed.

Lemma comp_tfps_coef0_eq0 (f g : {tfps K n}) :
                g \in (@coef0_is_0 K n) -> f \So g = Tfpsp n (comp_poly g f).
Proof. by move => f0_eq0 ; rewrite /comp_tfps f0_eq0. Qed.

Section Variable_p.

Lemma pwC_in_coef0_is_0 (c : K) : reflect (c = 0) (c %:S \in @coef0_is_0 K n).
Proof. by rewrite coef0_is_0E nth0_Tfpsp coefC eqxx; apply: eqP. Qed.

Variable (f : {tfps K n}).

Lemma comp_tfps0r : f \So 0 = (f`_0) %:S.
Proof. by rewrite comp_tfps_coef0_eq0 ?rpred0 // comp_poly0r. Qed.

Lemma comp_tfpsr0 : 0 \So f = 0.
Proof.
have [f0_eq0 | f0_neq0] := boolP (f \in (@coef0_is_0 K n)).
+ by rewrite comp_tfps_coef0_eq0 // comp_poly0 rmorph0.
+ by rewrite comp_tfps_coef0_neq0.
Qed.

(* is there a better statement ? *)
Lemma comp_tfpsC (c : K) : c%:S \So f =
                                        (c * (f \in (@coef0_is_0 K n))%:R) %:S.
Proof.
have [f0_eq0 | f0_neq0] := boolP (f \in (@coef0_is_0 K n)).
+ rewrite comp_tfps_coef0_eq0 //=.
  rewrite modp_small; last first.
    by rewrite size_polyC size_polyXn (leq_ltn_trans (leq_b1 _)).
  by rewrite comp_polyC mulr1.
+ by rewrite mulr0 Tfpsp0 comp_tfps_coef0_neq0.
Qed.

Lemma comp_tfpsCf (c : K) : f \So (c%:S) = (f`_0 * (c == 0)%:R) %:S.
Proof.
have [->| /negbTE c_neq0] := eqVneq c 0.
  by rewrite eqxx mulr1 rmorph0 comp_tfps0r.
rewrite comp_tfps_coef0_neq0; last first.
  by rewrite coef0_is_0E nth0_Tfpsp coefC eqxx negbT.
by rewrite c_neq0 mulr0 rmorph0.
Qed.

Hypothesis (f0_is_0 : f \in (@coef0_is_0 K n)).

Fact comp_tfps_is_additive : additive (comp_tfps f).
Proof.
move => u v; rewrite !comp_tfps_coef0_eq0 //.
by apply/val_inj; rewrite rmorphB /= modp_add modNp.
Qed.

Fact comp_tfps_is_linear : linear (comp_tfps f).
Proof.
move => a q r.
by rewrite !comp_tfps_coef0_eq0 // !rmorphD /= modp_scalel mod_tfps // !linearZ.
Qed.

End Variable_p.
End Variable_n.

Lemma deriv_tfps_comp (m : nat) (f g : {tfps K m}): f \in (@coef0_is_0 K m) ->
  deriv_tfps (g \So f) = (g `d \So (Tfpsp m.-1 f)) * f `d.
Proof.
rewrite !deriv_tfpsE //.
move: f g; case: m => [f g g0_eq0 | m f g g0_eq0].
+ apply/val_inj => /=.
  rewrite [f]tfps_is_cst [g]tfps_is_cst Tfpsp_Tfpsp // comp_tfpsC !deriv_modp.
  by rewrite !derivC !mod0p mulr0 mod0p.
+ rewrite /= comp_tfps_coef0_eq0 // comp_tfps_coef0_eq0 ?p0_is_0; last first.
    by rewrite coef0_is_0E nth0_Tfpsp -coef0_is_0E.
  apply/val_inj => /=.
  rewrite deriv_modp deriv_comp modp_mod modp_mul.
  rewrite mulrC -[LHS]modp_mul mulrC; congr (modp _) ; congr (_ * _). 
  rewrite [g^`() %% 'X^m.+1]modp_small ; last first.
  rewrite size_polyXn (leq_ltn_trans (leq_size_deriv _)) //.
  have [ -> // | ] := eqVneq (size g) 0%N.
  by rewrite -lt0n => sp_gt0; rewrite prednK // size_tfps.
  rewrite (divp_eq (val f) 'X^m.+1) modp_add modp_mull add0r modp_mod.
  rewrite !comp_polyE !modp_sumn /=; apply: eq_bigr => i _.
  rewrite !modp_scalel; congr (_ *: _).
  rewrite exprDn big_ord_recr /= subnn expr0 mul1r binn mulr1n modp_add.
  rewrite modp_sumn /= (eq_bigr (fun j => 0)) => [|j _].
    by rewrite big1_eq add0r.
  rewrite -scaler_nat modp_scalel; apply/eqP.
  rewrite scaler_eq0 ; apply/orP; right.
  apply/eqP; apply: modp_eq0.
  by rewrite dvdp_mulr // exprMn dvdp_mull // dvdp_exp // subn_gt0.
Qed.

End CompSeries.


Section RevSeries.

Variable (K : fieldType) (n : nat).

Definition rev_tfps (m : nat) (p : {tfps K n}) := 
  Tfpsp m (revp p). 

Lemma rev_tfps_unit (m : nat) (p : {tfps K n}) : p != 0 -> 
  (rev_tfps m p) \is a GRing.unit.
Proof. 
move: p => [ [s pr1] pr2 ] Hpneq0.
by rewrite unit_tfpsE nth0_Tfpsp coef0_revp lead_coef_eq0 Hpneq0. 
Qed.

End RevSeries.
