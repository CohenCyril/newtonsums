(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype div tuple bigop ssralg poly polydiv finfun.
From mathcomp Require Import generic_quotient.

From Newtonsums Require Import auxresults valuation revpoly.

(* This file builds the field of fraction of any integral domain. *)
(* The main result of this file is the existence of the field *)
(* and of the tofrac function which is a injective ring morphism from R *)
(* to its fraction field {fraction R} *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Local Scope ring_scope.
Open Local Scope quotient_scope.

Reserved Notation "{ 'ratio' T }" (at level 0, format "{ 'ratio'  T }").
Reserved Notation "{ 'fraction' T }" (at level 0, format "{ 'fraction'  T }").
Reserved Notation "{ 'fracpoly' T }" (at level 0, format "{ 'fracpoly'  T }").
Reserved Notation "x %:F" (at level 2, format "x %:F").
Reserved Notation "x %:FP" (at level 2, format "x %:FP").
Reserved Notation "x ^:FP" (at level 2, format "x ^:FP").
Reserved Notation "p \FPo q" (at level 50, format "p  \FPo  q").

Section FracDomain.
Variable R : ringType.

(* ratios are pairs of R, such that the second member is nonzero *)
Inductive ratio := mkRatio { frac :> R * R; _ : frac.2 != 0 }.
Definition ratio_of of phant R := ratio.
Local Notation "{ 'ratio' T }" := (ratio_of (Phant T)).

Canonical ratio_subType := Eval hnf in [subType for frac].
Canonical ratio_of_subType := Eval hnf in [subType of {ratio R}].
Definition ratio_EqMixin := [eqMixin of ratio by <:].
Canonical ratio_eqType := EqType ratio ratio_EqMixin.
Canonical ratio_of_eqType := Eval hnf in [eqType of {ratio R}].
Definition ratio_ChoiceMixin := [choiceMixin of ratio by <:].
Canonical ratio_choiceType := ChoiceType ratio ratio_ChoiceMixin.
Canonical ratio_of_choiceType := Eval hnf in [choiceType of {ratio R}].

Lemma denom_ratioP : forall f : ratio, f.2 != 0. Proof. by case. Qed.

Definition ratio0 := (@mkRatio (0, 1) (oner_neq0 _)).
Definition Ratio x y : {ratio R} := insubd ratio0 (x, y).

Lemma numer_Ratio x y : y != 0 -> (Ratio x y).1 = x.
Proof. by move=> ny0; rewrite /Ratio /insubd insubT. Qed.

Lemma denom_Ratio x y : y != 0 -> (Ratio x y).2 = y.
Proof. by move=> ny0; rewrite /Ratio /insubd insubT. Qed.

Definition RatioK := (numer_Ratio, denom_Ratio).

CoInductive Ratio_spec (n d : R) : {ratio R} -> R -> R -> Type :=
  | RatioNull of d = 0 : Ratio_spec n d ratio0 n 0
  | RatioNonNull (d_neq0 : d != 0) :
    Ratio_spec n d (@mkRatio (n, d) d_neq0) n d.

Lemma RatioP n d : Ratio_spec n d (Ratio n d) n d.
Proof.
rewrite /Ratio /insubd; case: insubP=> /= [x /= d_neq0 hx|].
  have ->: x = @mkRatio (n, d) d_neq0 by apply: val_inj.
  by constructor.
by rewrite negbK=> /eqP hx; rewrite {2}hx; constructor.
Qed.

Lemma Ratio0 x : Ratio x 0 = ratio0.
Proof. by rewrite /Ratio /insubd; case: insubP; rewrite //= eqxx. Qed.

End FracDomain.

Notation "{ 'ratio' T }" := (ratio_of (Phant T)).
Identity Coercion type_fracdomain_of : ratio_of >-> ratio.

Notation "'\n_' x"  := (frac x).1
  (at level 8, x at level 2, format "'\n_' x").
Notation "'\d_' x"  := (frac x).2
  (at level 8, x at level 2, format "'\d_' x").

Module FracField.
Section FracField.

Variable R : idomainType.

Local Notation frac := (R * R).
Local Notation dom := (ratio R).
Local Notation domP := denom_ratioP.

Implicit Types x y z : dom.

(* We define a relation in ratios *)
Local Notation equivf_notation x y := (\n_x * \d_y == \d_x * \n_y).
Definition equivf x y := equivf_notation x y.

Lemma equivfE x y : equivf x y = equivf_notation x y.
Proof. by []. Qed.

Lemma equivf_refl : reflexive equivf.
Proof. by move=> x; rewrite /equivf mulrC. Qed.

Lemma equivf_sym : symmetric equivf.
Proof. by move=> x y; rewrite /equivf eq_sym; congr (_==_); rewrite mulrC. Qed.

Lemma equivf_trans : transitive equivf.
Proof.
move=> [x Px] [y Py] [z Pz]; rewrite /equivf /= mulrC => /eqP xy /eqP yz.
by rewrite -(inj_eq (mulfI Px)) mulrA xy -mulrA yz mulrCA.
Qed.

(* we show that equivf is an equivalence *)
Canonical equivf_equiv := EquivRel equivf equivf_refl equivf_sym equivf_trans.

Definition type := {eq_quot equivf}.
Definition type_of of phant R := type.
Notation "{ 'fraction' T }" := (type_of (Phant T)).

(* we recover some structure for the quotient *)
Canonical frac_quotType := [quotType of type].
Canonical frac_eqType := [eqType of type].
Canonical frac_choiceType := [choiceType of type].
Canonical frac_eqQuotType := [eqQuotType equivf of type].

Canonical frac_of_quotType := [quotType of {fraction R}].
Canonical frac_of_eqType := [eqType of {fraction R}].
Canonical frac_of_choiceType := [choiceType of {fraction R}].
Canonical frac_of_eqQuotType := [eqQuotType equivf of {fraction R}].

(* we explain what was the equivalence on the quotient *)
Lemma equivf_def (x y : ratio R) : x == y %[mod type]
                                    = (\n_x * \d_y == \d_x * \n_y).
Proof. by rewrite eqmodE. Qed.

Lemma equivf_r x : \n_x * \d_(repr (\pi_type x)) =
                                                 \d_x * \n_(repr (\pi_type x)).
Proof. by apply/eqP; rewrite -equivf_def reprK. Qed.

Lemma equivf_l x : \n_(repr (\pi_type x)) * \d_x =
                                                 \d_(repr (\pi_type x)) * \n_x.
Proof. by apply/eqP; rewrite -equivf_def reprK. Qed.

Lemma numer0 x : (\n_x == 0) = (x == (ratio0 R) %[mod_eq equivf]).
Proof. by rewrite eqmodE /= !equivfE // mulr1 mulr0. Qed.

Lemma Ratio_numden : forall x, Ratio \n_x \d_x = x.
Proof.
case=> [[n d] /= nd]; rewrite /Ratio /insubd; apply: val_inj=> /=.
by case: insubP=> //=; rewrite nd.
Qed.

Definition tofrac := lift_embed {fraction R} (fun x : R => Ratio x 1).
Canonical tofrac_pi_morph := PiEmbed tofrac.

Notation "x %:F"  := (@tofrac x).

Implicit Types a b c : type.

Definition addf x y : dom := Ratio (\n_x * \d_y + \n_y * \d_x) (\d_x * \d_y).
Definition add := lift_op2 {fraction R} addf.

Lemma pi_add : {morph \pi : x y / addf x y >-> add x y}.
Proof.
move=> x y; unlock add.
case: piP => x' /eqmodP /eqP eq_x; case: piP => y' /eqmodP /eqP eq_y.
apply/eqmodP/eqP; rewrite /addf /= !RatioK ?mulf_neq0 ?domP //.
rewrite mulrDr mulrDl mulrACA eq_x mulrACA; congr (_ + _).
by rewrite [_ * \d_y']mulrC mulrACA eq_y mulrACA [_ * \d_y]mulrC.
Qed.
Canonical pi_add_morph := PiMorph2 pi_add.

Definition oppf x : dom := Ratio (- \n_x) \d_x.
Definition opp := lift_op1 {fraction R} oppf.
Lemma pi_opp : {morph \pi : x / oppf x >-> opp x}.
Proof.
move=> x; unlock opp; apply/eqmodP; rewrite /= /equivf /oppf /=.
by rewrite !RatioK ?(domP,mulf_neq0) // mulNr mulrN -equivf_r.
Qed.
Canonical pi_opp_morph := PiMorph1 pi_opp.

Definition mulf x y : dom := Ratio (\n_x * \n_y) (\d_x * \d_y).
Definition mul := lift_op2 {fraction R} mulf.

Lemma pi_mul : {morph \pi : x y / mulf x y >-> mul x y}.
Proof.
move=> x y; unlock mul; apply/eqmodP=> /=.
rewrite equivfE /= /addf /= !RatioK ?mulf_neq0 ?domP //.
rewrite mulrAC !mulrA -mulrA equivf_r -equivf_l.
by rewrite mulrA ![_ * \d_y]mulrC !mulrA.
Qed.
Canonical pi_mul_morph := PiMorph2 pi_mul.

Definition invf x : dom := Ratio \d_x \n_x.
Definition inv := lift_op1 {fraction R} invf.

Lemma pi_inv : {morph \pi : x / invf x >-> inv x}.
Proof.
move=> x; unlock inv; apply/eqmodP=> /=; rewrite equivfE /invf eq_sym.
do 2?case: RatioP=> /= [/eqP|];
  rewrite ?mul0r ?mul1r -?equivf_def ?numer0 ?reprK //.
  by move=> hx /eqP hx'; rewrite hx' eqxx in hx.
by move=> /eqP ->; rewrite eqxx.
Qed.
Canonical pi_inv_morph := PiMorph1 pi_inv.

Lemma addA : associative add.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE.
rewrite /addf /= !RatioK ?mulf_neq0 ?domP // !mulrDl !mulrA !addrA.
by congr (\pi (Ratio (_ + _ + _) _)); rewrite mulrAC.
Qed.

Lemma addC : commutative add.
Proof.
by elim/quotW=> x; elim/quotW=> y; rewrite !piE /addf addrC [\d__ * _]mulrC.
Qed.

Lemma add0_l : left_id 0%:F add.
Proof.
elim/quotW=> x; rewrite !piE /addf !RatioK ?oner_eq0 //.
by rewrite mul0r mul1r mulr1 add0r Ratio_numden.
Qed.

Lemma addN_l : left_inverse 0%:F opp add.
Proof.
elim/quotW=> x; apply/eqP; rewrite piE /equivf.
rewrite /addf /oppf !RatioK ?(oner_eq0, mulf_neq0, domP) //.
by rewrite mulr1 mulr0 mulNr addNr.
Qed.

(* fractions form an abelian group *)
Definition frac_zmodMixin :=  ZmodMixin addA addC add0_l addN_l.
Canonical frac_zmodType := Eval hnf in ZmodType type frac_zmodMixin.

Lemma mulA : associative mul.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE.
by rewrite /mulf !RatioK ?mulf_neq0 ?domP // !mulrA.
Qed.

Lemma mulC : commutative mul.
Proof.
elim/quotW=> x; elim/quotW=> y; rewrite !piE /mulf.
by rewrite [_ * (\d_x)]mulrC [_ * (\n_x)]mulrC.
Qed.

Lemma mul1_l : left_id 1%:F mul.
Proof.
elim/quotW=> x; rewrite !piE /mulf.
by rewrite !RatioK ?oner_eq0 // !mul1r Ratio_numden.
Qed.

Lemma mul_addl : left_distributive mul add.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; apply/eqP.
rewrite !piE /equivf /mulf /addf !RatioK ?mulf_neq0 ?domP //; apply/eqP.
rewrite !(mulrDr, mulrDl) !mulrA; congr (_ * _ + _ * _).
  rewrite ![_ * \n_z]mulrC -!mulrA; congr (_ * _).
  rewrite ![\d_y * _]mulrC !mulrA; congr (_ * _ * _).
  by rewrite [X in _ = X]mulrC mulrA.
rewrite ![_ * \n_z]mulrC -!mulrA; congr (_ * _).
rewrite ![\d_x * _]mulrC !mulrA; congr (_ * _ * _).
by rewrite -mulrA mulrC [X in X * _] mulrC.
Qed.

Lemma nonzero1 : 1%:F != 0%:F :> type.
Proof. by rewrite piE equivfE !RatioK ?mul1r ?oner_eq0. Qed.

(* fractions form a commutative ring *)
Definition frac_comRingMixin :=
                               ComRingMixin mulA mulC mul1_l mul_addl nonzero1.
Canonical frac_ringType := Eval hnf in RingType type frac_comRingMixin.
Canonical frac_comRingType := Eval hnf in ComRingType type mulC.

Lemma mulV_l : forall a, a != 0%:F -> mul (inv a) a = 1%:F.
Proof.
elim/quotW=> x /=; rewrite !piE.
rewrite /equivf !RatioK ?oner_eq0 // mulr1 mulr0=> nx0.
apply/eqmodP; rewrite /= equivfE.
by rewrite !RatioK ?(oner_eq0, mulf_neq0, domP) // !mulr1 mulrC.
Qed.

Lemma inv0 : inv 0%:F = 0%:F.
Proof.
rewrite !piE /invf !RatioK ?oner_eq0 // /Ratio /insubd.
do 2?case: insubP; rewrite //= ?eqxx ?oner_eq0 // => u _ hu _.
by congr \pi; apply: val_inj; rewrite /= hu.
Qed.

(* fractions form a ring with explicit unit *)
Definition RatFieldUnitMixin := FieldUnitMixin mulV_l inv0.
Canonical frac_unitRingType := Eval hnf in UnitRingType type RatFieldUnitMixin.
Canonical frac_comUnitRingType := [comUnitRingType of type].

Lemma field_axiom : GRing.Field.mixin_of frac_unitRingType.
Proof. exact. Qed.

(* fractions form a field *)
Definition RatFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical frac_idomainType :=
  Eval hnf in IdomainType type (FieldIdomainMixin field_axiom).
Canonical frac_fieldType := FieldType type field_axiom.

End FracField.
End FracField.

Notation "{ 'fraction' T }" := (FracField.type_of (Phant T)).
Notation equivf := (@FracField.equivf _).
Hint Resolve denom_ratioP.

Section Canonicals.

Variable R : idomainType.

(* reexporting the structures *)
Canonical FracField.frac_quotType.
Canonical FracField.frac_eqType.
Canonical FracField.frac_choiceType.
Canonical FracField.frac_zmodType.
Canonical FracField.frac_ringType.
Canonical FracField.frac_comRingType.
Canonical FracField.frac_unitRingType.
Canonical FracField.frac_comUnitRingType.
Canonical FracField.frac_idomainType.
Canonical FracField.frac_fieldType.
Canonical FracField.tofrac_pi_morph.
Canonical frac_of_quotType := Eval hnf in [quotType of {fraction R}].
Canonical frac_of_eqType := Eval hnf  in [eqType of {fraction R}].
Canonical frac_of_choiceType := Eval hnf in [choiceType of {fraction R}].
Canonical frac_of_zmodType := Eval hnf in [zmodType of {fraction R}].
Canonical frac_of_ringType := Eval hnf in [ringType of {fraction R}].
Canonical frac_of_comRingType := Eval hnf in [comRingType of {fraction R}].
Canonical frac_of_unitRingType := Eval hnf in [unitRingType of {fraction R}].
Canonical frac_of_comUnitRingType :=
  Eval hnf in [comUnitRingType of {fraction R}].
Canonical frac_of_idomainType := Eval hnf in [idomainType of {fraction R}].
Canonical frac_of_fieldType := Eval hnf in [fieldType of {fraction R}].

End Canonicals.

Section FracFieldTheory.
Import FracField.

Variable R : idomainType.

Lemma Ratio_numden (x : {ratio R}) : Ratio \n_x \d_x = x.
Proof. exact: FracField.Ratio_numden. Qed.

(* exporting the embeding from R to {fraction R} *)
Local Notation tofrac := (@FracField.tofrac R).
Local Notation "x %:F" := (tofrac x).
Local Notation "x // y" := (x%:F / y%:F) (at level 40).

Lemma tofrac_is_rmorphism: rmorphism tofrac.
Proof.
unlock tofrac; [do ?split] => [p q|p q|]; rewrite [X in _ = X]piE //=.
  by rewrite /addf /oppf /= !RatioK ?oner_eq0 ?mulr1.
by rewrite /mulf !RatioK ?oner_eq0 ?mulr1.
Qed.

Canonical tofrac_additive := Additive tofrac_is_rmorphism.
Canonical tofrac_rmorphism := AddRMorphism tofrac_is_rmorphism.

(* tests *)
Fact tofrac0 : 0%:F = 0. Proof. exact: rmorph0. Qed.
Fact tofracN : {morph tofrac: x / - x}. Proof. exact: rmorphN. Qed.
Fact tofracD : {morph tofrac: x y / x + y}. Proof. exact: rmorphD. Qed.
Fact tofracB : {morph tofrac: x y / x - y}. Proof. exact: rmorphB. Qed.
Fact tofracMn n : {morph tofrac: x / x *+ n}. Proof. exact: rmorphMn. Qed.
Fact tofracMNn n : {morph tofrac: x / x *- n}. Proof. exact: rmorphMNn. Qed.
Fact tofrac1 : 1%:F = 1. Proof. exact: rmorph1. Qed.
Fact tofracM : {morph tofrac: x y  / x * y}. Proof. exact: rmorphM. Qed.
Fact tofracX n : {morph tofrac: x / x ^+ n}. Proof. exact: rmorphX. Qed.

Lemma tofrac_inj : injective tofrac.
Proof.
move=> p q /=; rewrite piE [RHS]piE => /eqmodP /eqP.
by rewrite !RatioK ?oner_eq0 // mulr1 mul1r.
Qed.

Canonical Structure tofrac_injmorphism := InjMorphism tofrac_inj.

Fact mulE (x y : {fraction R}) : x * y = mul x y.
Proof. by []. Qed.

Fact invE (x : {fraction R}) : x ^-1 = inv x.
Proof. by []. Qed.

Lemma fracE (x : {fraction R}) : {y | x = y.1 // y.2 & y.2 != 0}.
Proof.
elim/quotW: x => y; exists y; last exact: denom_ratioP.
rewrite !piE mulrC /=.
set rn := (Ratio \n_y 1).
set dn := (Ratio \d_y 1).
rewrite invE -pi_inv mulE -pi_mul /invf /dn /rn /mulf.
rewrite ?numer_Ratio ?denom_Ratio ?oner_neq0 ?(denom_ratioP y) //.
by rewrite mulr1 mul1r -{1}(Ratio_numden y).
Qed.

Lemma frac_eq0 (p q : R) : (p // q == 0) = (p == 0) || (q == 0).
Proof. by rewrite mulf_eq0 invr_eq0 !rmorph_eq0. Qed.

Lemma frac_neq0 (p q : R) : p != 0 -> q != 0 -> p // q != 0.
Proof. by rewrite frac_eq0 negb_or => -> ->. Qed.

End FracFieldTheory.

Notation tofrac := (@FracField.tofrac _).
Notation "'@'tofrac" := (@FracField.tofrac).
Notation "x %:F" := (@FracField.tofrac _ x).
Notation "x // y" := (x%:F / y%:F) (at level 40).

Notation "{ 'fracpoly' K }" := {fraction {poly K}}.
Definition tofracpoly {K : fieldType} : K -> {fracpoly K} := tofrac \o polyC.

Notation "x %:FP" := (tofracpoly x) : ring_scope.
Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Notation "p ^:FP" := (p ^ (@tofracpoly _)) : ring_scope.

Notation "''XF'" := ('X%:F) : ring_scope.
Notation "''X^+' n" := ('X%:F ^+ n)
 (at level 3, n at level 2, format "''X^+' n") : ring_scope.
Notation "''X^-' n" := ('X%:F ^- n)
 (at level 3, n at level 2, format "''X^-' n") : ring_scope.
Notation "''X^-1'" := ('X%:F)^-1 : ring_scope.

Canonical tofracpoly_is_additive (K : fieldType) :=
  [additive of @tofracpoly K].
Canonical tofracpoly_is_rmorphism (K : fieldType) :=
  [rmorphism of @tofracpoly K].
Canonical tofracpoly_is_injmorphism (K : fieldType) :=
  [injmorphism of @tofracpoly K].

Module RegMorphism.

Section ClassDef.

Variables (R : idomainType) (K : fieldType).

Definition mixin_of (f : R -> K) : Type  :=
  forall x,
  {y : R * R | x = y.1 // y.2 & f y.2 != 0} +
  forall y1 y2, x = y1 // y2 -> f y2 = 0.

Record class_of f : Type := Class {base : rmorphism f; mixin : mixin_of f}.
Local Coercion base : class_of >-> rmorphism.

Structure map (phRS : phant (R -> K)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.
Variables (phRS : phant (R -> K)) (f g : R -> K) (cF : map phRS).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone fM of phant_id g (apply cF) & phant_id fM class :=
  @Pack phRS f fM.

Definition pack (fM : mixin_of f) :=
  fun (bF : GRing.RMorphism.map phRS) fA & phant_id (GRing.RMorphism.class bF) fA =>
  Pack phRS (Class fA fM).

Canonical rmorphism := GRing.RMorphism.Pack phRS class.
Canonical additive := GRing.Additive.Pack phRS class.

End ClassDef.

Module Exports.
Notation regular_dec f := (mixin_of f).
Notation regmorphism f := (class_of f).
Coercion base : regmorphism >-> GRing.RMorphism.class_of.
Coercion mixin : regmorphism >-> mixin_of.
Coercion apply : map >-> Funclass.
Notation RegMorphism fM := (pack fM id).
Notation "{ 'regmorphism' fRS }" := (map (Phant fRS))
  (at level 0, format "{ 'regmorphism'  fRS }") : ring_scope.
Notation "[ 'regmorphism' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'regmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'regmorphism' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'regmorphism'  'of'  f ]") : form_scope.
Coercion additive : map >-> GRing.Additive.map.
Canonical additive.
Coercion rmorphism : map >-> GRing.RMorphism.map.
Canonical rmorphism.
End Exports.

End RegMorphism.
Include RegMorphism.Exports.

Section EvalInjective.

Variable (R : idomainType) (K : fieldType) (f : {injmorphism R -> K}).

Lemma injective_regular_dec : regular_dec f.
Proof.
move=> x; have [[x1 x2] /= -> x2_neq0] := fracE x.
by left; exists (x1, x2); rewrite //= rmorph_eq0.
Qed.

Canonical injective_is_regmorphism := RegMorphism injective_regular_dec.

End EvalInjective.

Section EvalFrac.

Variables (R : idomainType) (K : fieldType) (f : {regmorphism R -> K}).
Implicit Types (x : {fraction R}).

Definition freprP := RegMorphism.mixin (RegMorphism.class f).

Fact fpole_key : unit. Proof. exact: tt. Qed.
Definition fpole_of (phf: phantom (R -> K) f) := locked_with fpole_key
  (fun x => if freprP x is inr _ then true else false).
Local Notation fpole := (fpole_of (Phantom (R -> K) f)).
Canonical fpole_unlockable := [unlockable fun fpole].

Lemma fpoleP {x} : reflect (forall y1 y2, x = y1 // y2 -> f y2 = 0) (fpole x).
Proof.
rewrite unlock; case: freprP => [[y -> fy2]|]; constructor => //.
by move=> /(_ _ _ erefl); apply/eqP.
Qed.

Definition froot_of (phf: phantom (R -> K) f) x := (fpole x^-1).
Local Notation froot := (froot_of (Phantom (R -> K) f)).

Fact feval_key : unit. Proof. exact: tt. Qed.
(* feval theory *)
Definition feval_of (phf: phantom (R -> K) f) : _ -> K := locked_with feval_key
  (fun x =>
   let frepr x := if freprP x is inl (exist2 y _ _) then y else (0, 0) in
   f (frepr x).1 / f (frepr x).2).
Local Notation feval := (feval_of (Phantom (R -> K) f)).
Canonical feval_unlockable := [unlockable fun feval].

Inductive feval_spec x : {fraction R} ->  bool -> K -> Type :=
| HasPoleEval of fpole x : feval_spec x x true 0
| HasNoPoleEval y1 y2 of f y2 != 0 : feval_spec x (y1 // y2) false (f y1 / f y2).

Lemma fevalP x : feval_spec x x (fpole x) (feval x).
Proof.
rewrite !unlock.
case: freprP => [[y->]|]; rewrite ?rmorph0 ?mul0r; constructor => //.
exact/fpoleP.
Qed.

Lemma fpolePn {x : {fraction R}} :
   reflect (exists2 y, x = y.1 // y.2 & f y.2 != 0) (~~ fpole x).
Proof.
case: fevalP=> [/fpoleP fy2_eq0|y1 y2]; constructor; last by exists (y1, y2).
by move=> [y /fy2_eq0 ->]; rewrite eqxx.
Qed.

Lemma frootP {x} : reflect (forall y1 y2, x = y1 // y2 -> f y1 = 0) (froot x).
Proof.
apply: (equivP fpoleP); pose V := (congr1 (@GRing.inv _)).
by split=> fy0 y1 y2 /V; rewrite ?invrK invf_div; apply: fy0.
Qed.

Lemma frootPn {x} : reflect (exists2 y, x = y.1 // y.2 & (f y.1 != 0))
                            (~~ froot x).
Proof.
apply: (equivP fpolePn); pose V := (congr1 (@GRing.inv _)).
by split=> [] [y /V]; rewrite ?invrK invf_div => ->; exists (y.2, y.1).
Qed.

Lemma fpoleV x : fpole (x ^-1) = froot x. Proof. by []. Qed.

Lemma frootV x : froot (x ^-1) = fpole x.
Proof. by rewrite /froot invrK. Qed.

Lemma froot_div x y : froot (x / y) = fpole (y / x).
Proof. by rewrite /froot invf_div. Qed.

Lemma den_fpole_eq0 (x y : R) : fpole (x // y) -> f y = 0.
Proof. by move=> /fpoleP /(_ x) ->. Qed.

Lemma fpole_fracF (x y : R) : f y != 0 -> fpole (x // y) = false.
Proof. by apply: contraNF => /den_fpole_eq0 ->. Qed.

Lemma fpole_tofrac (x : R) : fpole x%:F = false.
Proof. by rewrite -[x%:F]divr1 fpole_fracF // rmorph1 oner_eq0. Qed.

Lemma fpole0 : fpole 0 = false.
Proof. by rewrite fpole_tofrac. Qed.

Lemma fpole1 : fpole 1 = false.
Proof. by rewrite fpole_tofrac. Qed.             

Fact felem_eq0F (x : R) : f x != 0 -> (x == 0) = false.
Proof. by apply: contraNF => /eqP ->; rewrite rmorph0. Qed.

Lemma fpole_frac (x y : R) : y != 0 -> f x != 0 -> fpole (x // y) = (f y == 0).
Proof.
move=> y_neq0 fx_neq0; have [fy_eq0|/fpole_fracF-> //] := altP eqP.
apply/fpoleP => x' y' /eq_divf_mul.
rewrite frac_neq0 // ?felem_eq0F // => /(_ isT).
rewrite -!rmorphM => /tofrac_inj /(congr1 f) /eqP.
by rewrite !rmorphM /= fy_eq0 mulr0 mulf_eq0 (negPf fx_neq0) /= => /eqP.
Qed.

Lemma froot_fracF (x y : R) : f x != 0 -> froot (x // y) = false.
Proof. by rewrite froot_div; apply: fpole_fracF. Qed.

Lemma froot0 : froot 0 = false. Proof. by rewrite /froot invr0 fpole0. Qed.

Lemma num_froot_eq0 (x y : R) : froot (x // y) -> f x = 0.
Proof. by apply: contraTeq => /froot_fracF ->. Qed.

Lemma froot_frac (x y : R) : x != 0 -> f y != 0 -> froot (x // y) = (f x == 0).
Proof. by rewrite froot_div; apply: fpole_frac. Qed.

Lemma froot_tofrac (x : R) : x != 0 -> froot x%:F = (f x == 0).
Proof.
by move=> x_neq0; rewrite -[x%:F]mulr1 -invr1 froot_frac ?rmorph1 ?oner_eq0.
Qed.

Lemma froot1 : froot 1 = false.
Proof. by rewrite froot_tofrac ?rmorph1 ?oner_eq0. Qed.

Lemma fpoleN x : fpole (- x) = fpole x.
Proof.
gen have fpoleN : x / fpole (- x) -> fpole x; last first.
  by apply/idP/idP => ?; apply/fpoleN; rewrite ?opprK.
case: (fevalP x) => // y1 y2 fy2; move=> /(congr1 negb) /= <-.
by rewrite -mulNr -rmorphN fpole_fracF.
Qed.

Lemma frootN x : froot (- x) = froot x.
Proof. by rewrite /froot invrN fpoleN. Qed.

(* Theory of feval *)

Lemma feval_frac (y z : R) : f z != 0 -> feval (y // z) = (f y) / (f z).
Proof.
move=> fz; have := erefl (y // z).
case: {-1}_ _ _ / fevalP fz => //= [/fpoleP /(_ _ _ erefl) /eqP -> //|].
move=> y' z' /= fz' fz /eqP; rewrite eq_divf ?rmorph_eq0 ?felem_eq0F //.
rewrite -!rmorphM rmorph_eq => /eqP eqyz'.
by apply/eqP; rewrite eq_divf // -!rmorphM eqyz'.
Qed.

Lemma feval_neq0P {x} : 
    reflect (exists2 y, x = y.1 // y.2 & (f y.1 != 0) && (f y.2 != 0)) 
            (feval x != 0).
Proof.
apply: (iffP idP) => [|[{x} x -> /andP [fx1 fx2]]]; last first.
  by rewrite feval_frac  // ?mulf_neq0 ?invr_eq0.
case: fevalP => [x_pole|{x} x1 x2 fx2_neq0]; rewrite ?eqxx //.
rewrite mulf_eq0 negb_or invr_eq0 fx2_neq0 andbT => fx1_neq0.
by exists (x1, x2); rewrite //= ?mulf_neq0 ?fx1_neq0.
Qed.

Lemma feval_eq0P {x} : 
    reflect (forall y1 y2, x = y1 // y2 -> (f y1 == 0) || (f y2 == 0))
            (feval x == 0).
Proof.
apply: (iffP idP)=> [fx_eq0 y1 y2 x_def|]; last first.
  by move=> Pf; apply/feval_neq0P => [[y /=]] /Pf; rewrite -negb_or => ->.
apply: contraTT fx_eq0; rewrite negb_or => fy1V20.
by apply/feval_neq0P; exists (y1, y2).
Qed.

Lemma fpoleM x y : feval y != 0 -> fpole (x * y) = fpole x.
Proof.
move=> /feval_neq0P=> [[{y} y -> /andP [fy1 fy2]]].
have [|{x} x1 x2 fx2] := fevalP x; last first.
  by rewrite mulf_div -!rmorphM /= fpole_fracF // rmorphM mulf_neq0.
apply: contraTT => /fpolePn [z] /(canRL (mulfK _)) ->; last first.
  by rewrite frac_neq0 ?felem_eq0F // => /(_ isT).
move=> fz2; rewrite invf_div mulf_div -!rmorphM /=.
by rewrite fpole_fracF // rmorphM mulf_neq0.
Qed.

Lemma feval_pole x : fpole x -> feval x = 0.
Proof. by case: fevalP. Qed.

Lemma feval_root  x : froot x -> feval x = 0.
Proof.
case: fevalP => // y1 y2 fy2.
have [-> _|y1_neq0] := eqVneq y1 0; first by rewrite rmorph0 mul0r.
by rewrite froot_frac => // /eqP ->; rewrite mul0r.
Qed.

Lemma feval_tofrac (x : R) : feval (x %:F) = f x.
Proof. by rewrite -[x%:F]divr1 feval_frac ?rmorph1 ?divr1 ?oner_eq0. Qed.

Lemma feval0 : feval 0 = 0. Proof. by rewrite feval_tofrac rmorph0. Qed.
Lemma feval1 : feval 1 = 1. Proof. by rewrite feval_tofrac rmorph1. Qed.

Lemma fevalN : {morph feval : x / - x}.
Proof.
move=> x; have [] := fevalP x; first by rewrite -fpoleN oppr0 => /feval_pole->.
by move=> y1 y2 fy2; rewrite -!mulNr -!rmorphN /= feval_frac.
Qed.

Fact feval_divN0 y z : feval z != 0 -> feval (y / z) = (feval y) / (feval z).
Proof.
case: fevalP; first by rewrite eqxx.
move=> {z} z1 z2 fz2; rewrite mulf_eq0 negb_or invr_eq0 fz2 andbT => fz1.
case: (fevalP y)=> [y_pole|{y} y1 y2 fy2]; rewrite ?mul0r /=; last first.
  rewrite !invfM !invrK ![_^-1 * _]mulrC !mulf_div -?rmorphM /=.
  by rewrite feval_frac //  rmorphM mulf_neq0.
by rewrite feval_pole // fpoleM // invf_div feval_frac ?mulf_neq0 ?invr_eq0.
Qed.

Lemma frootM x y : feval y != 0 -> froot (x * y) = froot x.
Proof.
move=> fy_neq0; rewrite /froot invfM fpoleM //.
by rewrite -div1r feval_divN0 ?feval1 ?div1r ?invr_eq0.
Qed.

Lemma feval_eq0 x : (feval x == 0) = [|| x == 0, froot x | fpole x].
Proof.
rewrite /froot; have [->|] /= := altP (x =P 0); first by rewrite feval0 eqxx.
case: fevalP => [|y1 y2 fy2]; rewrite ?eqxx ?(orbT,orbF) ?invf_div //.
rewrite ?frac_eq0 !mulf_eq0 negb_or invr_eq0 (negPf fy2) orbF.
by move => /andP [y10 y20]; rewrite fpole_frac.
Qed.

Lemma fevalV : {morph feval : x / x^-1}.
Proof.
move=> x; have [fx_eq0|fx_neq0] := eqVneq (feval x) 0.
  apply/eqP; rewrite fx_eq0 invr0 feval_eq0.
  by rewrite invr_eq0 frootV orbA orbAC -orbA -feval_eq0 fx_eq0.
by rewrite -div1r feval_divN0 // feval1 div1r.
Qed.

Lemma feval_N0div y z  : feval y != 0 -> feval (y / z) = (feval y) / (feval z).
Proof. by move=> ?;rewrite -invf_div -feval_divN0 // -fevalV invf_div. Qed.

Lemma fevalD : {in predC fpole &, {morph feval : x y / x + y}}.
Proof.
move=> x y; rewrite !inE.
have [[] // x1 x2 fx2 [] // y1 y2 fy2 _ _] := (fevalP x, fevalP y).
rewrite !addr_div ?unitfE ?rmorph_eq0 ?felem_eq0F -?rmorphM -?rmorphD //=.
by rewrite feval_frac // rmorphM mulf_neq0.
Qed.

Lemma fevalB : {in predC fpole &, {morph feval : x y / x - y}}.
Proof. by move=> x y /= ? ?; rewrite fevalD ?fevalN // inE fpoleN. Qed.

Lemma fevalM : {in predC fpole &, {morph feval : x y / x * y}}.
Proof.
move=> x y; rewrite !inE.
have [[] // x1 x2 fx2 [] // y1 y2 fy2 _ _] := (fevalP x, fevalP y).
by rewrite !mulf_div -!rmorphM /= feval_frac // rmorphM mulf_neq0.
Qed.

Lemma feval_div : {in predC fpole & predC froot, {morph feval : x y / x / y}}.
Proof. by move=> x y /= ? ?; rewrite fevalM ?fevalV // inE fpoleV. Qed.

End EvalFrac.

Notation "f .-pole" := (@fpole_of _ _ _ (Phantom (_ -> _) f))
  (at level 2, format "f .-pole") : ring_scope.
Notation "f .-root" := (@froot_of _ _ _ (Phantom (_ -> _) f))
  (at level 2, format "f .-root") : ring_scope.
Notation "f .-eval" := (@feval_of _ _ _ (Phantom (_ -> _) f))
  (at level 2, format "f .-eval") : ring_scope.

Section EvalFracInj.

Variable (R : idomainType) (K : fieldType) (f : {injmorphism R -> K}).

Lemma inj_fpole (x : {fraction R}) : f.-pole x = false.
Proof.
by apply/fpolePn; have [y] := fracE x; exists y; rewrite ?rmorph_eq0.
Qed.

Lemma injNfpole (x : {fraction R}) : ~~ f.-pole x.
Proof. by rewrite inj_fpole. Qed.
Hint Resolve injNfpole.

Lemma feval_rmorphism : rmorphism f.-eval.
Proof.
split; first by move=> x y; rewrite fevalD ?inE // -fevalN.
by split; [move=> x y; rewrite fevalM ?inE|rewrite feval1].
Qed.

Canonical feval_is_additive := Additive feval_rmorphism.
Canonical feval_is_rmorphism := AddRMorphism feval_rmorphism.

Lemma feval_inj : injective f.-eval.
Proof.
apply: raddf_inj => x /= /eqP; rewrite feval_eq0 /=.
by rewrite inj_fpole [f.-root _]inj_fpole ?orbF => /eqP.
Qed.

Canonical feval_is_injmorphism := InjMorphism feval_inj.

End EvalFracInj.

Section MapFrac.

Variable (R S : idomainType) (iota : {injmorphism R -> S}).
Let tofrac_map := [injmorphism of tofrac \o iota].
Definition map_frac_of (phiota : phantom (R -> S) iota) := tofrac_map.-eval.
Local Notation map_frac := (map_frac_of (Phantom (_ -> _) iota)).

Canonical map_frac_is_additive := [additive of map_frac].
Canonical map_frac_is_rmorphism := [rmorphism of map_frac].
Canonical map_frac_is_injmorphism := [injmorphism of map_frac].

Lemma map_fracE (x : R) : map_frac (x%:F) = (iota x)%:F.
Proof. by rewrite [LHS]feval_tofrac. Qed.

Lemma map_frac_frac (x y : R) : map_frac (x // y) = (iota x) // (iota y).
Proof. by rewrite fmorph_div /= !map_fracE. Qed.

Lemma map_frac_tofracV (x : R) : map_frac (x%:F^-1) = (iota x)%:F^-1.
Proof. by rewrite !fmorphV /= map_fracE. Qed.

End MapFrac.

Notation map_frac iota := (map_frac_of (Phantom (_ -> _) iota)).
Local Notation "p ^^ f" := (map_frac f p)
   (f at next level, at level 30).
Local Notation "p ^^^ f" := (map_frac (map_poly f) p)
   (f at next level, at level 30).

Section EvalFracPoly.

Variable (K : fieldType) (a: K).

Implicit Types (f g : {fracpoly K}).
Implicit Types (u v p q : {poly K}).

Lemma tofrac_scale (c : K) (p : {poly K}) : (c *: p)%:F = (c%:FP) * (p %:F).
Proof. by rewrite -mul_polyC rmorphM. Qed.

Lemma fracpolyE x :  {y : {poly K} * {poly K}
  | x = y.1 // y.2 & (y.2 != 0) && (coprimep y.1 y.2)}.
Proof.
have [[u v] /= -> v_neq0] := fracE x.
pose u' := u %/ gcdp u v; pose v' := v %/ gcdp u v.
have v'_neq0 : v' != 0 by rewrite dvdp_div_eq0 // dvdp_gcdr.
suff -> : u // v = u' // v'.
  by exists (u',v'); rewrite // v'_neq0 coprimep_div_gcd // v_neq0 orbT.
apply/eqP; rewrite eq_divf ?rmorph_eq0 // -!rmorphM rmorph_eq; apply/eqP.
by rewrite divp_mulA ?dvdp_gcdr // divp_mulAC ?dvdp_gcdl.
Qed.

Lemma fracpoly_eval_regmorphism : regular_dec (horner_eval a).
Proof.
move=> x; have [[u v] /= -> /andP[v_neq0 cuv]] := fracpolyE x.
have [->|u_neq0] := eqVneq u 0.
  by left; exists (0, 1); rewrite /= ?mul0r ?rmorph1 ?oner_eq0.
have [fv_eq0|?] := boolP (horner_eval a v == 0); last by left; exists (u, v).
right=> u' v' /eq_divf_mul; rewrite frac_neq0 -?rmorphM //= => /(_ isT).
move=> /tofrac_inj /(congr1 (horner_eval a)) /eqP.
rewrite !rmorphM /= (eqP fv_eq0) mulr0 mulf_eq0.
rewrite [_ == _]negbTE /=; first by move/eqP.
by apply: coprimep_root fv_eq0; rewrite coprimep_sym.
Qed.

Canonical fracpoly_eval_is_regmorphism :=
  RegMorphism fracpoly_eval_regmorphism.

Notation fppole := ((horner_eval a).-pole).
Notation fproot := ((horner_eval a).-root).
Notation fpeval := ((horner_eval a).-eval).

Lemma coprimep_fpole u v : v != 0 -> coprimep u v ->
  (fppole (u // v)) = (v.[a] == 0).
Proof.
move=> vN0; have [u0|uN0 cuv] := eqVneq u 0.
+ rewrite u0 mul0r fpole0 coprime0p => eqp_v1.
  symmetry; apply/negbTE; have: v %= 1 by [].
  rewrite [v]size1_polyC; last first.
    by have/eqP -> : size v == 1%N => //; rewrite size_poly_eq1.
  by rewrite !hornerC polyC_eqp1.
+ have [va0|?] := altP eqP; last by rewrite fpole_fracF.
  rewrite fpole_frac //= /horner_eval ?va0 ?eqxx //.
  by move/eqP: va0; apply: coprimep_root; rewrite coprimep_sym.
Qed.

Lemma coprimep_froot u v : u != 0 -> v != 0 -> coprimep u v ->
  (fproot (u // v)) = (u.[a] == 0).
Proof. by rewrite froot_div coprimep_sym => u0 v0; exact: coprimep_fpole. Qed.

Lemma coprimep_feval u v : coprimep u v ->
  (fpeval (u // v)) = (u.[a] / v.[a]).
Proof.
have [->|u_neq0] := eqVneq u 0; first by rewrite horner0 !mul0r feval0.
have [->|v_neq0] := eqVneq v 0; first by rewrite horner0 !invr0 !mulr0 feval0.
move=> cuv; have [va0|?] := eqVneq v.[a] 0; last by rewrite feval_frac.
by rewrite feval_pole ?coprimep_fpole ?va0 ?invr0 ?mulr0.
Qed.

Lemma fpeval_tofrac u : fpeval u%:F = u.[a].
Proof. by rewrite -[_%:F]divr1 coprimep_feval ?coprimep1 ?hornerC ?divr1. Qed.

Lemma fppoleM f g : fppole f -> fppole g -> fppole (f * g).
Proof.
have [[f1 f2] /= -> /andP[f2_neq0 cf]] := fracpolyE f.
have [[g1 g2] /= -> /andP[g2_neq0 cg]] := fracpolyE g.
have [->|f1_neq0] := eqVneq f1 0; first by rewrite !mul0r fpole0.
have [->|g1_neq0] := eqVneq g1 0; first by rewrite !mul0r mulr0 fpole0.
rewrite !coprimep_fpole // mulf_div -!rmorphM /= => f2a_eq0 g2a_eq0.
rewrite fpole_frac ?rmorphM //= ?mulf_eq0 ?negb_or ?f2a_eq0 ?f2_neq0 //.
apply/andP; split; [move: f2a_eq0|move: g2a_eq0];
by apply: coprimep_root; rewrite coprimep_sym.
Qed.

Lemma fppoleMF (f g : {fracpoly K}) :
  ~~ fppole f -> ~~ fppole g -> fppole (f * g) = false.
Proof.
have [[f1 f2] /= -> /andP[f2_neq0 cf]] := fracpolyE f.
have [[g1 g2] /= -> /andP[g2_neq0 cg]] := fracpolyE g.
have [->|f1_neq0] := eqVneq f1 0; first by rewrite !mul0r fpole0.
have [->|g1_neq0] := eqVneq g1 0; first by rewrite !mul0r mulr0 fpole0.
rewrite !coprimep_fpole // mulf_div -!rmorphM /= => f2a_eq0 g2a_eq0.
by rewrite fpole_fracF //= rmorphM mulf_eq0 negb_or f2a_eq0.
Qed.

Lemma fppoleX f n : n > 0 -> fppole (f ^+ n) = fppole f.
Proof.
case: n => // n _; elim: n => [|n IHn] //=; rewrite exprS.
have [polef|Npolef] := boolP (fppole f).
  by rewrite fppoleM ?IHn.
by rewrite fppoleMF ?IHn.
Qed.

Lemma fpevalX n : n > 0 -> {morph fpeval : f / f ^+ n}.
Proof.
case: n => // n _; elim: n => [|n IHn] //= f.
have [polef|Npolef] := boolP (fppole f).
  by rewrite !feval_pole ?expr0n ?fppoleX //=.
by rewrite exprS [RHS]exprS fevalM ?inE ?fppoleX //= IHn.
Qed.

Lemma XV_eq0 : ('X^-1 == 0 :> {fracpoly K}) = false.
Proof. by rewrite invr_eq0 rmorph_eq0 polyX_eq0. Qed.

Lemma fppole_XV : (fppole 'X^-1) = (a == 0).
Proof. by rewrite fpoleV froot_tofrac ?polyX_eq0 //= /horner_eval hornerX. Qed.

Lemma fpevalC (c : K) : fpeval (c %:FP) = c.
Proof. by rewrite feval_tofrac [LHS]hornerC. Qed.

End EvalFracPoly.

Notation "a .-fppole" := ((horner_eval a).-pole)
  (at level 2, format "a .-fppole") : ring_scope.
Notation "a .-fproot" := ((horner_eval a).-root)
  (at level 2, format "a .-fproot") : ring_scope.
Notation "a .-fpeval" := ((horner_eval a).-eval)
  (at level 2, format "a .-fpeval") : ring_scope.
Notation "f .<[ a ]>" := (a.-fpeval f)
  (at level 2, left associativity, format "f .<[ a ]>")  : ring_scope.

Section MapPolyFrac.

Variable (K L : fieldType) (iota : {injmorphism K -> L}).

Lemma map_fracpolyX : 'XF ^^^ iota = 'XF.
Proof. by rewrite map_fracE /= map_polyX. Qed.

Lemma map_fracpolyC (c : K) : (c %:FP) ^^^ iota = (iota c) %:FP.
Proof. by rewrite map_fracE /= map_polyC. Qed.

Lemma map_fracpolyXV : 'X^-1 ^^^ iota = 'X^-1.
Proof. by rewrite map_frac_tofracV /= map_polyX. Qed.

Lemma map_fracpolyXn n : 'X^+n ^^^ iota = 'X^+n.
Proof. by rewrite rmorphX /= map_fracpolyX. Qed.

Lemma map_fracpolyXVn n : 'X^-n ^^^ iota = 'X^-n.
Proof. by rewrite -!exprVn rmorphX fmorphV /= map_fracpolyX. Qed.

(* TODO: is it general enough? *)
Lemma to_fracpoly_map_iota (p : {poly K}) :
  (p ^ iota) ^:FP = (p ^:FP) ^ (map_frac (map_poly iota)).
Proof.
by rewrite -!map_poly_comp; apply: eq_map_poly => x /=; rewrite map_fracpolyC.
Qed.

End MapPolyFrac.

Section FPEvalMap.

Variables (K1 K2 : fieldType) (iota : {injmorphism K1 -> K2}) (a : K1).

Lemma fppole_map (f : {fracpoly K1}) :
  (iota a).-fppole (f ^^^ iota) = a.-fppole f.
Proof.
have [[p q] -> {f} /=  /andP [q_neq0 cpq]] := fracpolyE f.
have [->|p_neq0] := eqVneq p 0; first by rewrite mul0r !rmorph0 !fpole0.
rewrite fmorph_div /= !map_fracE !coprimep_fpole ?rmorph_eq0 ?coprimep_map //.
by rewrite horner_map rmorph_eq0.
Qed.

Lemma fpeval_map (f : {fracpoly K1}) : (f ^^^ iota).<[iota a]> = iota f.<[a]>.
Proof.
have [[p q] -> {f} /=  /andP [q_neq0 cpq]] := fracpolyE f.
rewrite fmorph_div /= !map_fracE !coprimep_feval ?coprimep_map //.
by rewrite !horner_map fmorph_div.
Qed.

End FPEvalMap.

Section CompFrac.
Variable (K : fieldType).
Implicit Types (f g h : {fracpoly K}).
Implicit Types (p q r : {poly K}).

Definition comp_fracpoly f g := (f ^^^ tofracpoly).<[g]>.
Definition nocomp_fracpoly f g := g.-fppole (f ^^^ tofracpoly).

Lemma horner_map_polyC p q : (p ^ polyC).[q] = p \Po q.
Proof. by []. Qed.

Notation "f \FPo g" := (comp_fracpoly f g) : ring_scope.

Lemma comp_poly_frac p f : p%:F \FPo f = (p ^ tofracpoly).[f].
Proof. by rewrite /comp_fracpoly map_fracE /= feval_tofrac /=. Qed.

Lemma comp_poly_fracE p f : p%:F \FPo f = \sum_(i < size p) (p`_i)%:FP * f ^+ i.
Proof.
rewrite comp_poly_frac horner_coef size_map_poly /=.
by apply: eq_bigr => i _; rewrite coef_map.
Qed.

Lemma comp_fracpolyC (c : K) f : (c %:FP) \FPo f = c %:FP.
Proof. by rewrite comp_poly_frac map_polyC hornerC. Qed.

Lemma comp_fracpoly0 f : 0 \FPo f = 0.
Proof. by rewrite comp_fracpolyC. Qed.

Lemma comp_fracpoly_dflt f g : nocomp_fracpoly f g -> f \FPo g = 0.
Proof. by move=> pole_fg; rewrite [LHS]feval_pole. Qed.

Lemma comp_fracpolyD f g h :
  ~~ nocomp_fracpoly f h -> ~~ nocomp_fracpoly g h ->
  (f + g) \FPo h = (f \FPo h) + (g \FPo h).
Proof. by move=> ??; rewrite /comp_fracpoly !rmorphD /= fevalD. Qed.

Lemma comp_fracpolyN f g :  (- f) \FPo g = - (f \FPo g).
Proof. by rewrite /comp_fracpoly !rmorphN /= fevalN. Qed.

Lemma comp_fracpolyM f g h :
  ~~ nocomp_fracpoly f h -> ~~ nocomp_fracpoly g h ->
  (f * g) \FPo h = (f \FPo h) * (g \FPo h).
Proof. by move=> ??; rewrite /comp_fracpoly !rmorphM /= fevalM. Qed.

Lemma comp_fracpolyXr f : f \FPo ('X %:F) = f.
Proof.
rewrite /comp_fracpoly; have [[p q] -> {f} /= /andP [p2_neq0 cp]] := fracpolyE f.
rewrite !fmorph_div /= !map_fracE coprimep_feval ?coprimep_map //=.
rewrite /tofracpoly !map_poly_comp !horner_map /= !horner_map_polyC.
by rewrite !comp_polyXr.
Qed.

Lemma comp_fracpoly_exp (m : nat) f  g : (f ^+ m) \FPo g = (f \FPo g) ^+ m.
Proof.
case: m => [|m]; first by rewrite !expr0 comp_fracpolyC.
by rewrite /comp_fracpoly !rmorphX /= fpevalX.
Qed.

Lemma comp_fracpolyV f g : (f ^-1) \FPo g = (f \FPo g) ^-1.
Proof. by rewrite /comp_fracpoly !fmorphV /= fevalV. Qed.

Lemma comp_fracpoly_div f g h : g \FPo h != 0 ->
  (f / g) \FPo h = (f \FPo h) / (g \FPo h).
Proof. by move=> ?; rewrite /comp_fracpoly !fmorph_div /= feval_divN0. Qed.

Lemma pole_comp_fracpolyPn f g : 
  reflect (exists2 c : K, c.-fppole f & g = c%:FP) (nocomp_fracpoly f g).
Proof.
rewrite /nocomp_fracpoly; apply: (iffP idP); last first.
  by move=> [c ? ->]; rewrite fppole_map.
have [[p q] -> {f} /= /andP [q_neq0 cp_pq]] := fracpolyE f.
have [->|p_neq0] := eqVneq p 0; first by rewrite mul0r !rmorph0 fpole0.
rewrite fmorph_div /= !map_fracE coprimep_fpole ?rmorph_eq0 ?coprimep_map //=.
have [[u v] -> {g} /= /andP [v_neq0 cp_uv]] := fracpolyE g => hq.
have H : \sum_(i < size q) q`_i *: u ^+ i * v ^+ ((size q).-1 - i) = 0.
  move: hq.
  rewrite -{1}[q]coefK poly_def rmorph_sum horner_sum /=.
  move/eqP/(congr1 ( *%R^~ ((v ^+ (size q).-1)%:F))); rewrite mul0r mulr_suml.
  rewrite (eq_bigr (fun i => (q`_(nat_of_ord i) 
                   *: u ^+i * v ^+((size q).-1 - i))%:F)) => [|i _] ; last first.
    rewrite linearZ hornerZ /= map_polyXn hornerXn expr_div_n.
    rewrite -scalerAl tofrac_scale -mulrA mulrAC rmorphM !rmorphX -mulrA.
    rewrite exprB // ?unitfE ?raddf_eq0 // ; last exact: tofrac_inj.
    by rewrite -ltnS prednK ?ltn_ord // size_poly_gt0. 
  move/eqP. rewrite -rmorph_sum raddf_eq0; last exact: tofrac_inj.
  by move/eqP.
have dvdv1 : v %| 1.
  move/(congr1 (fun x => x %% v)) : H.
  rewrite mod0p modp_sumn.
  rewrite -(big_mkord predT (fun i => (q`_i *: u ^+ i * v ^+ (_ - i) %% v))) /=.
  rewrite big_nat_rev big_ltn ?size_poly_gt0 // big_nat.
  rewrite (eq_bigr (fun i => 0)) => [|i /andP [hi1 hi2]]; last first.
    rewrite -modp_mul [X in _ * X]modp_eq0 ?dvdp_exp ?subn_gt0 //; last first.
      rewrite add0n subnS prednK ?subn_gt0 ?leq_subr // leq_subLR -ltnS -addnS.
      by rewrite prednK ?size_poly_gt0 // -[X in X < _]add0n ltn_add2r.
    by rewrite mulr0 mod0p.
  rewrite /= big1 // addr0 !add0n subn1 subnn expr0 mulr1; move/modp_eq0P.
  rewrite dvdp_scaler; last by rewrite -lead_coefE lead_coef_eq0.
  have [->|sq_neq0] := eqVneq (size q).-1 O.
    by rewrite expr0.
  move=> dvdp_vu.
  rewrite -(@coprimep_pexpl _ (size q).-1) in cp_uv; last by rewrite lt0n.
  move/coprimepP/(_ v): cp_uv => cp_uv.
  wlog: / v %= 1 => [H2|]; last by move/andP => [dvdp1 _].
  by rewrite H2 // cp_uv.
have [/andP [valp_gt0 /eqP ->]| /negbTE HF] := boolP ((0 < valp q) && (u == 0)).
  exists 0; rewrite ?mul0r //.
  rewrite coprimep_fpole // horner_coef0.
  move: valp_gt0; rewrite lt0n.
  apply: contraR => *.
  by rewrite valp_eq0.
have dvdu1 : u %| 1.
  move: H.
  rewrite -(big_mkord predT (fun i => q`_i *: u ^+ i * v ^+ (_ - i))).
  rewrite (big_cat_nat _ predT (fun i => q`_i *: 
              u ^+ i * v ^+ ((size q).-1 - i)) (leq0n (valp q))) /= ; last first.
    by rewrite ltnW // valp_small.
  rewrite big_nat.
  rewrite (eq_bigr (fun=> 0)) ?big1_eq ?add0r => [|i /andP [_ hi]]; last first.
    by rewrite valp_coef_eq0 // scale0r mul0r.
  rewrite big_nat.
  rewrite (eq_bigr (fun i => (u ^+ (valp q)) * (q`_i *: u ^+ (i - (valp q)) *
                      v ^+ ((size q).-1 - i)))) => [|i /andP [hi _]]; last first.
    rewrite mulrA; congr (_ * _); rewrite -scalerCA -scalerAl -exprD subnKC //.
  rewrite -mulr_sumr; move/eqP; rewrite mulf_eq0.
  rewrite expf_eq0 HF orFb -big_nat big_ltn ?valp_small // subnn expr0 big_nat.
  rewrite (eq_bigr (fun i => u * (q`_i *: u ^+ (i - valp q).-1 * 
                     v ^+ ((size q).-1 - i)) )) => [|i /andP [hi _]]; last first.
    rewrite mulrA; congr (_ * _). 
    by rewrite -scalerCA -scalerAl -exprS prednK // subn_gt0. 
  rewrite -mulr_sumr [X in _ + X]mulrC; move/eqP.
  move/(congr1 (fun x => x %% u)); rewrite mod0p modp_add modp_mull addr0.
  have [->|neq] := eqVneq (valp q) ((size q).-1).
    rewrite subnn expr0 mulr1 modp_scalel.
    move/eqP; rewrite scaler_eq0 -lead_coefE lead_coef_eq0.
    by move/negbTE : q_neq0 -> ; move/eqP/modp_eq0P.
  move/modp_eq0P; rewrite Gauss_dvdpl ?coprimep_pexpr ?subn_gt0 ?valp_small //.
    by rewrite dvdp_scaler ?coef_valp_neq0. 
  by rewrite ltn_neqAle neq andTb -ltnS prednK ?valp_small // size_poly_gt0.
rewrite !dvdp1 in dvdu1 dvdv1.
move: hq.
move/size_poly1P : dvdu1 => [c c_neq0 ->].
move/size_poly1P : dvdv1 => [d d_neq0 ->].
move=> hq.
exists (c / d); last by rewrite fmorph_div.
rewrite coprimep_fpole //. 
move: hq ; rewrite -rmorph_div /=; last first.
  by rewrite poly_unitE coefC size_polyC d_neq0 unitfE.
rewrite -rmorph_div ?unitfE // horner_map raddf_eq0 //. 
exact: (inj_comp (@tofrac_inj _) (@polyC_inj _)). 
Qed.

Lemma cst_nocomp_fracpoly f (c : K) : nocomp_fracpoly f (c%:FP) = c.-fppole f.
Proof. by rewrite /nocomp_fracpoly fppole_map. Qed.

Lemma Ncst_nocomp_fracpoly r f : size r > 1 -> ~~ nocomp_fracpoly f r%:F.
Proof.
rewrite /nocomp_fracpoly => r_gt1.
have [[p q] -> {f} /= /andP [p2_neq0 cp]] := fracpolyE f.
have [->|p_neq0] := eqVneq p 0; first by rewrite mul0r !rmorph0 fpole0.
rewrite !fmorph_div /= !map_fracE coprimep_fpole ?rmorph_eq0 ?coprimep_map //=.
rewrite /tofracpoly map_poly_comp /= horner_map /= rmorph_eq0.
rewrite horner_map_polyC -lead_coef_eq0 lead_coef_comp //.
rewrite mulf_neq0 ?expf_eq0 ?lead_coef_eq0 ?negb_and //.
by rewrite -size_poly_eq0 gtn_eqF ?orbT // (leq_trans _ r_gt1).
Qed.

Lemma comp_fracpolyX f : ('X %:F) \FPo f = f.
Proof. by rewrite comp_poly_frac map_polyX hornerX. Qed.

Lemma comp_fracpolyXn (m : nat) f : 'X^+m \FPo f = f ^+ m.
Proof. by rewrite comp_fracpoly_exp /= comp_fracpolyX. Qed.

Lemma comp_fracpoly_XV f : 'X^-1 \FPo f = f ^-1.
Proof. by rewrite comp_fracpolyV comp_fracpolyX. Qed.

Lemma comp_fracpoly_XV_XV : 'X^-1 \FPo 'X^-1 = 'XF.
Proof. by rewrite comp_fracpoly_XV invrK. Qed.

Lemma comp_poly_XV p : p%:F \FPo 'X^-1 = \sum_(i < size p) ((p`_i)%:FP) * 'X^-i.
Proof. by rewrite comp_poly_fracE; apply: eq_bigr => i _; rewrite exprVn. Qed.

Lemma nocomp_polyF p f : nocomp_fracpoly p%:F f = false.
Proof. by rewrite /nocomp_fracpoly map_fracE /= fpole_tofrac. Qed.

Lemma comp_frac_frac p q f : coprimep p q ->
  (p // q \FPo f) = (p%:F \FPo f) / (q%:F \FPo f).
Proof.
move=> cpq; rewrite /comp_fracpoly !fmorph_div /= !map_fracE /=.
by rewrite coprimep_feval ?coprimep_map // !fpeval_tofrac.
Qed. 

End CompFrac.

Notation "f \FPo g" := (comp_fracpoly f g) : ring_scope.

Section MoreCompFrac.

Variable  (K L : fieldType) (iota : {injmorphism K -> L}).

Lemma fracpoly_iota_comp_fracpoly (p q : {fracpoly K}) :
  (p \FPo q) ^^^ iota = (p ^^^ iota) \FPo (q ^^^ iota).
Proof.
have [ [ p1 p2 -> /= /andP [p2_neq0 coprime_p1_p2 ] ] ] := fracpolyE p.
rewrite fmorph_div /= !map_fracE !comp_frac_frac // ?fmorph_div ?coprimep_map //.
by rewrite !comp_poly_frac !to_fracpoly_map_iota !horner_map.
Qed.

End MoreCompFrac.

