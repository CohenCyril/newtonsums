(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  some doc here                                                            *)
(*****************************************************************************)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype finfun fingroup perm.
From mathcomp 
Require Import div tuple bigop ssralg poly polydiv mxpoly ring_quotient.
From mathcomp 
Require Import binomial bigop ssralg finalg zmodp matrix mxalgebra polyXY.

From Newtonsums Require Import fraction truncpowerseries.

Import FracField.
Import CompFrac.
Import EvalRatFrac.
Import MapRatFrac.
Import EvalFrac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Open Local Scope quotient_scope.

Section ExpansibleFracpoly.

Variable (K : fieldType).

Structure expansibleFracpoly := ExpansibleFracpoly
{
  underlying_fracpoly :> {fracpoly K};
  _ : devs_in_pw underlying_fracpoly
}. 

Canonical expansibleFracpoly_subType := [subType for underlying_fracpoly].
Definition expansibleFracpoly_eqMixin := [eqMixin of expansibleFracpoly by <:].
Canonical expansibleFracpoly_eqType := 
                          EqType expansibleFracpoly expansibleFracpoly_eqMixin.
Definition expansibleFracpoly_choiceMixin := 
                                     [choiceMixin of expansibleFracpoly by <:].
Canonical expansibleFracpoly_choiceType := 
                  ChoiceType expansibleFracpoly expansibleFracpoly_choiceMixin.

Fact underlying_fracpolyP (x : expansibleFracpoly) : devs_in_pw x.
Proof. by case: x. Qed.

Hint Resolve underlying_fracpolyP.

(* zmodType structure *)

Fact devs_in_pw0 : devs_in_pw (0 : {fracpoly K}).
Proof. rewrite -tofrac0 ; exact: devs_in_pw_tofrac. Qed.

Definition expansible_zero := ExpansibleFracpoly devs_in_pw0.

Lemma expansible_add_proof (x1 x2 : expansibleFracpoly) : 
           devs_in_pw ((x1 : {fracpoly _}) + (x2 : {fracpoly _})).
Proof. exact: devs_in_pwD. Qed.

Definition expansible_add (x1 x2 : expansibleFracpoly) :=
  ExpansibleFracpoly (expansible_add_proof x1 x2).

Lemma expansible_opp_proof (x : expansibleFracpoly) : 
  devs_in_pw (- (x : {fracpoly K})).
Proof. 
move: x => [p pr].
move: (fracpolyE p) pr => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
rewrite Hx -mulNr -rmorphN /= devs_in_pwE // devs_in_pwE //.
by rewrite -scaleN1r coprimep_scalel // oppr_eq0 oner_eq0.
Qed.

Definition expansible_opp (x : expansibleFracpoly) :=
  ExpansibleFracpoly (expansible_opp_proof x).

Fact  expansible_addA : associative expansible_add.
Proof. by move => x1 x2 x3 ; apply: val_inj ; exact: addrA. Qed.

Fact expansible_addC : commutative expansible_add.
Proof. by move => x1 x2 ; apply: val_inj ; exact: addrC. Qed.

Fact expansible_add0x : left_id expansible_zero expansible_add.
Proof. by move => x ; apply: val_inj ; exact: add0r. Qed.

Fact expansible_addK : 
                    left_inverse expansible_zero expansible_opp expansible_add.
Proof. by move => x ; apply: val_inj ; exact: addNr. Qed.

Definition expansibleFracpoly_zmodMixin := 
  ZmodMixin expansible_addA expansible_addC expansible_add0x expansible_addK.
Canonical expansibleFracpoly_zmodType := 
                      ZmodType expansibleFracpoly expansibleFracpoly_zmodMixin.

(* ringType structure *)

Fact devs_in_pw1 : devs_in_pw (1 : {fracpoly K}).
Proof. by rewrite -tofrac1 devs_in_pw_tofrac. Qed.

Definition expansible_one := ExpansibleFracpoly devs_in_pw1.

Lemma expansible_mul_proof (x1 x2 : expansibleFracpoly) : 
           devs_in_pw ((x1 : {fracpoly _}) * (x2 : {fracpoly _})).
Proof. exact: devs_in_pwM. Qed.

Definition expansible_mul (x1 x2 : expansibleFracpoly) :=
                               ExpansibleFracpoly (expansible_mul_proof x1 x2).

Fact left_id_expansible_one_expansible_mul : 
                                         left_id expansible_one expansible_mul.
Proof. by move => p ; apply val_inj ; rewrite /= mul1r. Qed.

Fact expansible_mulC : commutative expansible_mul.
Proof. by move => p1 p2 ; apply val_inj => /= ; rewrite mulrC. Qed.

Fact left_distributive_expansible_mul : 
                               left_distributive expansible_mul expansible_add.
Proof. by move => x1 x2 x3 ; apply val_inj => /= ; rewrite mulrDl. Qed.

Fact expansible_mulA : associative expansible_mul.
Proof. 
move => x1 x2 x3 ; apply: val_inj.
by rewrite /= [in RHS]mulrC mulrA mulrC.
Qed. 

Fact expansible_one_not_zero : expansible_one != expansible_zero.
Proof. by rewrite -val_eqE oner_neq0. Qed.

Definition expansibleFracpoly_ringMixin := ComRingMixin expansible_mulA 
  expansible_mulC left_id_expansible_one_expansible_mul 
  left_distributive_expansible_mul expansible_one_not_zero.   

Canonical expansibleFracpoly_ringType := 
                      RingType expansibleFracpoly expansibleFracpoly_ringMixin.

Canonical expansibleFracpoly_comRingType := 
                                ComRingType expansibleFracpoly expansible_mulC.

(* comUnitRingType structure *)

Definition expansibleFracpoly_unit : pred expansibleFracpoly :=
                  fun x => (x != 0) && (devs_in_pw ((val x) ^-1)).

Definition aux_expansibleFracpoly_inv (x : expansibleFracpoly) :=
  if devs_in_pw ((val x) ^-1)
  then (val x)^-1 else (val x).

Lemma expansibleFracpoly_inv_proof (x : expansibleFracpoly) :
                        devs_in_pw (aux_expansibleFracpoly_inv x).
Proof.
rewrite /aux_expansibleFracpoly_inv.
by have [dev | not_dev] := boolP (devs_in_pw (val x)^-1).
Qed.

Definition expansibleFracpoly_inv (x : expansibleFracpoly) :=
  ExpansibleFracpoly (expansibleFracpoly_inv_proof x).

Fact nonunit_expansibleFracpoly_inv : 
            {in [predC expansibleFracpoly_unit], expansibleFracpoly_inv =1 id}.
Proof. 
move => x.
rewrite inE /expansibleFracpoly_inv /= (qualifE 0) negb_and negbK.
move/orP => [ /eqP -> | dev ].
+ apply val_inj => /=.
  rewrite /aux_expansibleFracpoly_inv.
  case: (devs_in_pw ((val _) ^-1)) ; by rewrite /= ?invr0.
+ move: x dev => [p pr] /= /negbTE H.
  apply val_inj => /=.
  by rewrite /aux_expansibleFracpoly_inv /= H.
Qed.

Fact expansibleFracpoly_unitP x1 x2 : expansible_mul x2 x1 = expansible_one -> 
  x1 \in expansibleFracpoly_unit.
Proof.
move/val_eqP ; rewrite (qualifE 0).
move: x1 => [p1 pr1] /= ; move: x2 => [p2 pr2] /= ; move/eqP => H.
apply/andP ; split ; first by move: (GRing.Field.intro_unit H).
move: pr1 pr2 H.
move: (fracpolyE p1) => [[u1 v1] /= Hp1] /andP [v1_neq0 coprime_u1_v1].
move: (fracpolyE p2) => [[u2 v2] /= Hp2] /andP [v2_neq0 coprime_u2_v2].
rewrite Hp1 Hp2 mulf_div [(u1%:F / v1%:F)^-1]invf_div.
rewrite devs_in_pwE // devs_in_pwE // => v10_neq0 v20_neq0.
move/(congr1 (fun x => x * (v2%:F * v1%:F))).
rewrite mul1r -!mulrA [X in _ * (_ * X)]mulrC divff ; last first.
  by apply: mulf_neq0 ; rewrite tofrac_eq0.
rewrite mulr1 -!rmorphM /=.
move/eqP ; rewrite tofrac_eq.
move/eqP/(congr1 (fun x => x.[0])).
rewrite !horner_coef0 !coef0M => H.
apply: devs_in_pw_div_tofrac.
apply/negP => /eqP u10_eq0.
move: H ; rewrite u10_eq0 mulr0.
move/eqP ; rewrite eq_sym mulf_eq0.
by rewrite -!horner_coef0 (negbTE v10_neq0) (negbTE v20_neq0).
Qed.

Fact expansibleFracpoly_mulVr : 
  {in expansibleFracpoly_unit, 
                         left_inverse 1 expansibleFracpoly_inv expansible_mul}.  
Proof.
move => x x_unit ; apply: val_inj => /=. 
rewrite /aux_expansibleFracpoly_inv.
move: x_unit ; rewrite (qualifE 0) => /andP [x_neq0 -> ].
by rewrite mulrC divff.
Qed.

Definition expansibleFracpoly_comUnitRingMixin := ComUnitRingMixin
  expansibleFracpoly_mulVr expansibleFracpoly_unitP 
                                                nonunit_expansibleFracpoly_inv.  

Canonical expansibleFracpoly_unitRingType := 
  UnitRingType expansibleFracpoly expansibleFracpoly_comUnitRingMixin.

Canonical expansibleFracpoly_comUnitRingType := 
                                       [comUnitRingType of expansibleFracpoly].

Fact underlying_fracpoly0 : underlying_fracpoly 0 = 0.
Proof. by[]. Qed.

Fact underlying_fracpoly1 : underlying_fracpoly 1 = 1.
Proof. by[]. Qed.

Fact underlying_fracpoly_is_additive : additive underlying_fracpoly.
Proof. by move => [p p_dev] [q q_dev]. Qed.

Canonical underlying_fracpoly_additive := 
                                      Additive underlying_fracpoly_is_additive.

Lemma underlying_fracpolyD : 
                  {morph underlying_fracpoly_additive : x y / x + y >-> x + y}.
Proof. by move => x y. Qed.


Variable (n : nat).

Definition expanse (x : expansibleFracpoly) := 
  to_powerseries n x.

Fact expanse0 : expanse 0 = 0.
Proof. exact: to_powerseries0. Qed.

Fact expanse1 : expanse 1 = 1.
Proof. exact: to_powerseries1. Qed.

Fact expanse_is_additive : additive expanse.
Proof.
move => [p p_dev] [q q_dev] ; apply: val_inj => /=.
by rewrite /expanse to_powerseriesB.
Qed.

Canonical expanse_additive := Additive expanse_is_additive.

Lemma expanse_is_multiplicative: multiplicative expanse.
Proof.
split => [[p p_dev] [q q_dev] | ].
+ by rewrite /expanse to_powerseriesM.
+ exact: expanse1.
Qed.

Canonical expanse_rmorphism := AddRMorphism expanse_is_multiplicative.

Lemma expanseE (x : expansibleFracpoly) : expanse x = 
         let (x1, x2) := projT1 (fracpolyE x) in truncate n x1 / truncate n x2.
Proof. move: x => [x pr] ; by rewrite /expanse /to_powerseries pr. Qed.

Lemma to_powerseries_expanse (x : expansibleFracpoly) : 
  to_powerseries n x = expanse x.
Proof. by []. Qed.

End ExpansibleFracpoly.
