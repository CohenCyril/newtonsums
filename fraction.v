(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat div seq choice fintype.
From mathcomp
Require Import tuple bigop ssralg poly polydiv generic_quotient.
From Newtonsums Require Import auxresults.

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
Reserved Notation "p \FPo q" (at level 2, format "p \FPo q").

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

Definition numden_Ratio := (numer_Ratio, denom_Ratio).

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
move=> x y; unlock add; apply/eqmodP; rewrite /= equivfE.
rewrite /addf /= !numden_Ratio ?mulf_neq0 ?domP //.
rewrite mulrDr mulrDl eq_sym; apply/eqP.
rewrite !mulrA ![_ * \n__]mulrC !mulrA equivf_l.
congr (_ + _); first by rewrite -mulrA mulrCA !mulrA.
rewrite -!mulrA [X in _ * X]mulrCA !mulrA equivf_l.
by rewrite mulrC !mulrA -mulrA mulrC mulrA.
Qed.
Canonical pi_add_morph := PiMorph2 pi_add.

Definition oppf x : dom := Ratio (- \n_x) \d_x.
Definition opp := lift_op1 {fraction R} oppf.
Lemma pi_opp : {morph \pi : x / oppf x >-> opp x}.
Proof.
move=> x; unlock opp; apply/eqmodP; rewrite /= /equivf /oppf /=.
by rewrite !numden_Ratio ?(domP,mulf_neq0) // mulNr mulrN -equivf_r.
Qed.
Canonical pi_opp_morph := PiMorph1 pi_opp.

Definition mulf x y : dom := Ratio (\n_x * \n_y) (\d_x * \d_y).
Definition mul := lift_op2 {fraction R} mulf.

Lemma pi_mul : {morph \pi : x y / mulf x y >-> mul x y}.
Proof.
move=> x y; unlock mul; apply/eqmodP=> /=.
rewrite equivfE /= /addf /= !numden_Ratio ?mulf_neq0 ?domP //.
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
rewrite /addf /= !numden_Ratio ?mulf_neq0 ?domP // !mulrDl !mulrA !addrA.
by congr (\pi (Ratio (_ + _ + _) _)); rewrite mulrAC.
Qed.

Lemma addC : commutative add.
Proof.
by elim/quotW=> x; elim/quotW=> y; rewrite !piE /addf addrC [\d__ * _]mulrC.
Qed.

Lemma add0_l : left_id 0%:F add.
Proof.
elim/quotW=> x; rewrite !piE /addf !numden_Ratio ?oner_eq0 //.
by rewrite mul0r mul1r mulr1 add0r Ratio_numden.
Qed.

Lemma addN_l : left_inverse 0%:F opp add.
Proof.
elim/quotW=> x; apply/eqP; rewrite piE /equivf.
rewrite /addf /oppf !numden_Ratio ?(oner_eq0, mulf_neq0, domP) //.
by rewrite mulr1 mulr0 mulNr addNr.
Qed.

(* fractions form an abelian group *)
Definition frac_zmodMixin :=  ZmodMixin addA addC add0_l addN_l.
Canonical frac_zmodType := Eval hnf in ZmodType type frac_zmodMixin.

Lemma mulA : associative mul.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE.
by rewrite /mulf !numden_Ratio ?mulf_neq0 ?domP // !mulrA.
Qed.

Lemma mulC : commutative mul.
Proof.
elim/quotW=> x; elim/quotW=> y; rewrite !piE /mulf.
by rewrite [_ * (\d_x)]mulrC [_ * (\n_x)]mulrC.
Qed.

Lemma mul1_l : left_id 1%:F mul.
Proof.
elim/quotW=> x; rewrite !piE /mulf.
by rewrite !numden_Ratio ?oner_eq0 // !mul1r Ratio_numden.
Qed.

Lemma mul_addl : left_distributive mul add.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; apply/eqP.
rewrite !piE /equivf /mulf /addf !numden_Ratio ?mulf_neq0 ?domP //; apply/eqP.
rewrite !(mulrDr, mulrDl) !mulrA; congr (_ * _ + _ * _).
  rewrite ![_ * \n_z]mulrC -!mulrA; congr (_ * _).
  rewrite ![\d_y * _]mulrC !mulrA; congr (_ * _ * _).
  by rewrite [X in _ = X]mulrC mulrA.
rewrite ![_ * \n_z]mulrC -!mulrA; congr (_ * _).
rewrite ![\d_x * _]mulrC !mulrA; congr (_ * _ * _).
by rewrite -mulrA mulrC [X in X * _] mulrC.
Qed.

Lemma nonzero1 : 1%:F != 0%:F :> type.
Proof. by rewrite piE equivfE !numden_Ratio ?mul1r ?oner_eq0. Qed.

(* fractions form a commutative ring *)
Definition frac_comRingMixin := 
                               ComRingMixin mulA mulC mul1_l mul_addl nonzero1.
Canonical frac_ringType := Eval hnf in RingType type frac_comRingMixin.
Canonical frac_comRingType := Eval hnf in ComRingType type mulC.

Lemma mulV_l : forall a, a != 0%:F -> mul (inv a) a = 1%:F.
Proof.
elim/quotW=> x /=; rewrite !piE.
rewrite /equivf !numden_Ratio ?oner_eq0 // mulr1 mulr0=> nx0.
apply/eqmodP; rewrite /= equivfE.
by rewrite !numden_Ratio ?(oner_eq0, mulf_neq0, domP) // !mulr1 mulrC.
Qed.

Lemma inv0 : inv 0%:F = 0%:F.
Proof.
rewrite !piE /invf !numden_Ratio ?oner_eq0 // /Ratio /insubd.
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

Lemma tofrac_is_additive: additive tofrac.
Proof.
move=> p q /=; unlock tofrac.
rewrite -[X in _ = _ + X]pi_opp -[X in _ = X]pi_add.
by rewrite /addf /oppf /= !numden_Ratio ?(oner_neq0, mul1r, mulr1).
Qed.

Canonical tofrac_additive := Additive tofrac_is_additive.

Lemma tofrac_is_multiplicative: multiplicative tofrac.
Proof.
split=> [p q|//]; unlock tofrac; rewrite -[X in _ = X]pi_mul.
by rewrite /mulf /= !numden_Ratio ?(oner_neq0, mul1r, mulr1).
Qed.

Canonical tofrac_rmorphism := AddRMorphism tofrac_is_multiplicative.

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

Lemma tofrac_eq (p q : R): (p%:F == q%:F) = (p == q).
Proof.
apply/eqP/eqP=> [|->//]; unlock tofrac=> /eqmodP /eqP /=.
by rewrite !numden_Ratio ?(oner_eq0, mul1r, mulr1).
Qed.

Lemma tofrac_eq0 (p : R): (p%:F == 0) = (p == 0).
Proof. by rewrite tofrac_eq. Qed.

Lemma tofrac_inj : injective tofrac.
Proof.
move => x y.
move/eqP ; rewrite tofrac_eq.
by move/eqP.
Qed.

Fact mulE (x y : {fraction R}) : x * y = mul x y.
Proof. by []. Qed.

Fact invE (x : {fraction R}) : x ^-1 = inv x.
Proof. by []. Qed.

Lemma fracE (x : {fraction R}) : {y | x = y.1%:F / y.2%:F & y.2 != 0}.
Proof. 
elim/quotW: x => y; exists y; last exact: denom_ratioP.
rewrite !piE mulrC /=.
set rn := (Ratio \n_y 1).
set dn := (Ratio \d_y 1).
rewrite invE -pi_inv mulE -pi_mul /invf /dn /rn /mulf.
rewrite ?numer_Ratio ?denom_Ratio ?oner_neq0 ?(denom_ratioP y) //.
by rewrite mulr1 mul1r -{1}(Ratio_numden y).
Qed.

End FracFieldTheory.

Local Notation tofrac := (@FracField.tofrac _).
Notation "x %:F" := (@FracField.tofrac _ x).

Module EvalFrac.
Section EvalFrac.
Import FracField.

Variables (K : fieldType) (R : idomainType) (f : {rmorphism R -> K}).

Definition has_pole x := forall y : R * R, x = y.1%:F / y.2%:F -> f y.2 = 0.

Definition has_non_trivial_root x := 
  forall y : R * R, x = y.1%:F / y.2%:F  -> f y.1 = 0.

Definition has_root x := (x == 0) \/ (has_non_trivial_root x).

Definition has_general_root x := (has_root x) \/ (has_pole x).

Hypothesis Hfrepr : forall (x : {fraction R}),
    {y : R * R | x = y.1%:F / y.2%:F & f y.2 != 0} + has_pole x.

Lemma Npole_tofrac (x : R) : ~ (has_pole x%:F).
Proof.
rewrite /has_pole => pole_x.
move: ((pole_x (x, 1))) => /=.
rewrite !rmorph1 invr1 mulr1 => H.
move/eqP: (H (erefl x%:F)).
apply/negP ; exact: oner_neq0.
Qed. 

Lemma Npole0 : ~ (has_pole 0).
Proof. 
rewrite -(rmorph0 [rmorphism of (@tofrac _)]).
exact: Npole_tofrac.
Qed.

Lemma nice_repr x : ~ has_pole x -> 
                                {y : R * R | x = y.1%:F / y.2%:F & f y.2 != 0}.
Proof. by case: (Hfrepr x). Qed.

Definition f_eval (x : {fraction R}) : K :=
  if Hfrepr x is inl y then f (projS1 y).1 / f (projS1 y).2 else 0.

Fact tofrac_neq0 x : f x != 0 -> x%:F != 0.
Proof. by rewrite tofrac_eq0; apply: contraNneq => ->; rewrite rmorph0. Qed.
Hint Resolve tofrac_neq0.

Lemma f_eval_pole (x : {fraction R}) : has_pole x -> f_eval x = 0.
Proof.
rewrite /f_eval; case: Hfrepr => // [[y ? f_y2_neq0]] /(_ y) f_y2_eq0 /=.
by rewrite f_y2_eq0 ?eqxx in f_y2_neq0 *.
Qed.

Lemma f_eval_div_frac (y z : R) :
  f z != 0 -> f_eval (y%:F / z%:F) = (f y) / (f z).
Proof.
move=> fz_eq0; rewrite /f_eval.
case : Hfrepr => [[[y' z'] /= [eq_yz_y'z' fz'_eq0]]|f_eq0]; last first.
  by rewrite (f_eq0 (y, _)) ?eqxx in fz_eq0.
symmetry; apply/eqP; move: eq_yz_y'z' => /eqP.
rewrite !eq_divf ?tofrac_neq0 // -![_ * _ == _]subr_eq0.
by rewrite -!rmorphM -!rmorphN -!rmorphD tofrac_eq0 => /eqP->; rewrite rmorph0.
Qed.

Lemma f_eval_frac (x : R) : f_eval (x %:F) = f x.
Proof.
have -> : x%:F = x%:F / 1%:F :> {fraction R} by rewrite rmorph1 divr1.
by rewrite f_eval_div_frac ?rmorph0 ?rmorph1 ?divr1 ?oner_eq0.
Qed.

Lemma f_eval0 : f_eval 0 = 0.
Proof. by rewrite -tofrac0 f_eval_frac rmorph0. Qed.

Lemma f_eval_root (x : {fraction R}) : has_root x -> f_eval x = 0.
Proof.
move => [/eqP -> | x_has_non_trivial_root] ; first exact: f_eval0.
move: (Hfrepr x) => [[[y1 y2] /= Hx fy2_neq0] | x_has_pole].
+ rewrite Hx f_eval_div_frac //.
  by rewrite (x_has_non_trivial_root (y1, y2) Hx) mul0r.
+ by apply: f_eval_pole.
Qed.

Fact aux_has_poleN (x : {fraction R}) : has_pole x -> has_pole (-x).
Proof.
move => x_pole [u1 u2] /= Hx.
have: x = u1%:F / (- u2%:F) by rewrite invrN mulrN -Hx opprK.
rewrite -tofracN => H.
apply/eqP ; rewrite -oppr_eq0 -rmorphN.
by move: (x_pole (_, _ ) H) => /= ->.
Qed.

Lemma has_poleN (x : {fraction R}) : has_pole (-x) <-> has_pole x.
Proof.
split ; last by exact: aux_has_poleN.
by move/aux_has_poleN; rewrite opprK.
Qed.

Lemma f_eval_div (y z : {fraction R}) :
  f_eval z != 0 -> f_eval (y / z) = (f_eval y) / (f_eval z).
Proof.
have [[[x1 x2] /= ]|x_pole] := Hfrepr (y / z) ; have [[[y1 y2] /= ]|y_pole] := 
  Hfrepr y ; have [[[z1 z2] /= ]|z_pole] := Hfrepr z.
+ move => Hz fz2_neq0 Hy fy2_neq0 Hx fx2_neq0.
  rewrite Hz f_eval_div_frac // mulf_eq0 => /norP [fz1_neq0 _].
  rewrite Hy !invf_div !mulf_div -!tofracM !f_eval_div_frac // ; 
    last by rewrite rmorphM ; apply: mulf_neq0 => //.
  by rewrite mulf_div !rmorphM.
+ move => Hy fy2_neq0 Hx fx2_neq0.
  by rewrite [f_eval z]f_eval_pole // eq_refl.
+ move => Hz fz2_neq0 Hx fx2_neq0 fz_neq0.
  have: z != 0 by move: fz_neq0 ; apply: contra => /eqP -> ; rewrite f_eval0.
  move => z_neq0.
  move: Hx.
  move/(congr1 (fun x => x * z)).
  rewrite mulrAC -mulrA divff // mulr1 Hz mulf_div -!tofracM => Hx.
  move: ((y_pole (_ ,_)) Hx) => /= /eqP.
  rewrite rmorphM mulf_eq0.
  move/negbTE in fz2_neq0. 
  move/negbTE in fx2_neq0. 
  by rewrite fz2_neq0 fx2_neq0.
+ move: (fracE z) => [[z1 z2] /= Hy].
  by rewrite [f_eval z]f_eval_pole // eqxx.
+ move => Hz fz2_neq0 Hy fy2_neq0. 
  rewrite Hz f_eval_div_frac // mulf_eq0 GRing.invr_eq0 => /norP [fz1_neq0 _].
  rewrite Hy !f_eval_div_frac // !invf_div.    
  rewrite !mulf_div -!tofracM f_eval_div_frac ; 
    last by rewrite rmorphM mulf_neq0 //.
  by rewrite -!rmorphM.
+ move => Hy fy2_neq0.
  by rewrite [f_eval _]f_eval_pole // eqxx. 
+ move => Hz fz2_neq0 fz_neq0.
  rewrite [f_eval (y / z)]f_eval_pole //. 
  by rewrite [f_eval y]f_eval_pole // mul0r. 
rewrite [f_eval (y / z)]f_eval_pole //. 
rewrite [f_eval y]f_eval_pole //. 
by rewrite mul0r.
Qed.

Lemma f_eval1 : f_eval 1 = 1.
Proof. by rewrite -tofrac1 f_eval_frac rmorph1. Qed.

Lemma f_eval_invx (x : {fraction R}) : has_pole x -> f_eval (x ^-1) = 0.
Proof.
move => x_pole.
have [[[a b] /= ]|invx_pole] := Hfrepr (x ^-1) ; 
  last by rewrite [f_eval _]f_eval_pole //.
rewrite -invf_div => Hinvx ; rewrite Hinvx.
move/invr_inj : Hinvx ; rewrite invf_div => Hx.
move: (x_pole (b, a)) => /= H.
move: (H Hx) => -Hfa Hfb.
by rewrite f_eval_div_frac // Hfa mul0r.
Qed.

Fact zero_has_root : has_root 0.
Proof. left; exact: eqxx. Qed.
Hint Resolve zero_has_root. 

Lemma invx_has_pole (x : {fraction R}) : x != 0 -> 
  ((has_pole (x ^-1)) <-> (has_root x)).
Proof.
move/eqP => x_neq0.
split.
  move => H; right; move => y.
  rewrite -invf_div -[x]invrK => /invr_inj Hinvx.
  by move: (H (y.2, y.1)) => ->.
move => [/eqP * // | x_root] => y.
rewrite -invf_div => /invr_inj Hx.
by move: (x_root (y.2, y.1)) => ->.
Qed.

Lemma f_eval_invx_eq0 (x : {fraction R}) : f_eval x = 0 -> f_eval (x ^-1) = 0.
Proof.
have [[[x1 x2] /= ]|x_pole] := Hfrepr (x) ; last by rewrite f_eval_invx.
have [[[x1' x2'] /= ]|invx_pole] := Hfrepr (x ^-1) ; last first.
  by rewrite [f_eval x ^-1]f_eval_pole.
move => Hinvx fx2'_neq0 Hx fx2_neq0 ; rewrite Hinvx.
have [fx1'_eq0 | fx1'_neq0] := eqVneq (f x1') 0.
  by rewrite f_eval_div_frac // fx1'_eq0 mul0r.
move/eqP : Hinvx ; rewrite -{1}invf_div (inj_eq invr_inj) => /eqP ->.
rewrite [f_eval (x2'%:F / x1'%:F)]f_eval_div_frac // => /eqP.
rewrite mulf_eq0 invr_eq0.
move/negbTE in fx2'_neq0 ; move/negbTE in fx1'_neq0.
by rewrite fx2'_neq0 fx1'_neq0.
Qed.

Lemma f_eval_inv (x : {fraction R}) : f_eval (x ^-1) = (f_eval x)^-1.
Proof.
have [[[x1 x2] /= ]|x_pole] := Hfrepr (x) ; last first. 
  by rewrite [f_eval x]f_eval_pole // (f_eval_invx x_pole) GRing.invr0. 
have [fx_eq0 | ] := eqVneq (f_eval x) 0. 
  by rewrite fx_eq0 invr0 (f_eval_invx_eq0 fx_eq0).
move => fx_neq0 Hx fx2_neq0.
have fx1_neq0 : (f x1) != 0.
  apply/eqP => fx1_eq0.
  by move: fx_neq0 ; rewrite Hx f_eval_div_frac // fx1_eq0 mul0r eqxx. 
by rewrite Hx invf_div f_eval_div_frac // invf_div f_eval_div_frac.
Qed.

Lemma f_evalM (x y : {fraction R}) :
          ~ has_pole x -> ~ has_pole y -> f_eval (x * y) = f_eval x * f_eval y.
Proof.
move => /nice_repr [[x1 x2]-> /= fx2_neq0] 
        /nice_repr [[y1 y2]-> /= fy2_neq0].
rewrite mulrACA -invfM -!rmorphM !f_eval_div_frac // !rmorphM ?mulf_neq0 //.
by rewrite mulrACA -invfM.
Qed.

Lemma f_evalD (x y : {fraction R}) :
          ~ has_pole x -> ~ has_pole y -> f_eval (x + y) = f_eval x + f_eval y.
Proof.
move => /nice_repr [[x1 x2]-> /= fx2_neq0] 
        /nice_repr [[y1 y2]-> /= fy2_neq0].
rewrite addf_div ; last 2 first.
  + move: fx2_neq0 ; apply: contra.
    by rewrite tofrac_eq0 => /eqP -> ; rewrite rmorph0.
  + move: fy2_neq0 ; apply: contra.
    by rewrite tofrac_eq0 => /eqP -> ; rewrite rmorph0.
rewrite -!rmorphM -rmorphD !f_eval_div_frac // ; last first.
  by rewrite rmorphM mulf_eq0 ; apply/norP.
by symmetry ; rewrite rmorphD !rmorphM addf_div.
Qed.

Lemma f_evalN (x : {fraction R}) : f_eval (-x) = -f_eval x.
Proof.
have [[[x1 x2] /= ]|x_pole] := Hfrepr (x) ; last first.
  move/has_poleN : (x_pole) => Nx_pole. (* does not work without parenthesis*)
  by rewrite !f_eval_pole // oppr0.
move -> => fx2_neq0.
rewrite -mulrN -invrN -tofracN !f_eval_div_frac ?rmorphN // ?invrN ?mulrN //. 
by rewrite oppr_eq0.
Qed.

Section Injective_f.

Hypothesis f_inj : injective f.

Lemma has_no_pole (x : {fraction R}) : ~ (has_pole x).
Proof.
have [[y1 y2] -> /= {x}] := fracE x => /eqP y_neq0 x_pole.
move: (x_pole (y1,y2)) => /= H.
move/eqP : (H (erefl _)) ; rewrite -(rmorph0 f).
by move/eqP/(f_inj).
Qed.
Hint Resolve has_no_pole.

Lemma frepr : forall (x : {fraction R}),
  {y : R * R | x = y.1%:F / y.2%:F & f y.2 != 0}.
Proof.
move => x.
have [[y1 y2] /= Hx y2_neq0] := fracE x.
exists ((y1, y2)) => //= ; rewrite -(rmorph0 f). 
move: y2_neq0 ; apply: contra.
by move/eqP/f_inj => ->.
Qed.

Fact f_eval_is_additive : additive f_eval.
Proof. move => x y ; by rewrite f_evalD // -f_evalN. Qed.

Canonical f_eval_additive := Additive f_eval_is_additive.

Fact f_eval_is_multiplicative : multiplicative f_eval.
Proof. 
split ; last by exact: f_eval1.
by move => x y ; rewrite f_evalM.
Qed.

Canonical f_eval_rmorphism := AddRMorphism f_eval_is_multiplicative.

End Injective_f.

End EvalFrac.
End EvalFrac.

Notation "{ 'fracpoly' K }" := {fraction {poly K}}.

Module EvalRatFrac.
Section EvalRatFrac.
Import EvalFrac.

Variable (K : fieldType).

Definition to_fracpoly : K -> {fracpoly K} := tofrac \o polyC. 

Notation "x %:FP" := (to_fracpoly x).

Canonical to_fracpoly_rmorphism := [rmorphism of to_fracpoly].

Lemma to_fracpoly_inj : injective to_fracpoly.
Proof.
apply: inj_comp; first exact: tofrac_inj.
by exact: polyC_inj.
Qed.

Local Notation "p ^ f" := (map_poly f p).
Local Notation "p ^:FP" := (p ^ to_fracpoly).

Lemma to_fracpoly0 : 0 ^:FP = 0.
Proof. exact: map_poly0. Qed.

Lemma to_fracpoly_eq0 x : (x ^:FP == 0) = (x == 0).
Proof.
apply/idP/idP ; last by move/eqP -> ; rewrite to_fracpoly0.
by rewrite -to_fracpoly0 ; move/eqP/(map_poly_inj [rmorphism of _]) ->.
Qed.

Lemma  map_to_fracpoly_scale (c : K) (p : {poly K}) : 
  (c *: p)^:FP = (c %:FP) *: (p ^:FP).
Proof. by rewrite linearZ_LR. Qed.

Variable (a : K).

Definition ev := [rmorphism of horner_eval a].

Lemma evC (c : K) : ev c%:P = c.
Proof. by rewrite /ev /= horner_evalE hornerC. Qed.

Lemma evX : ev 'X = a.
Proof. by rewrite /ev /= horner_evalE hornerX. Qed.

Fact aux_irreducible_has_pole (u v : {poly K}) :
  (u %:F / v %:F) != 0 -> ev v = 0 -> coprimep u v ->
  has_pole ev (u %:F / v %:F).
Proof.
move => x_neq0 ev_v_eq0 coprime_u_v [y1 y2] /=.
have v_neq0 : v%:F != 0.
  apply/negP => /eqP v_eq0.
  by move: x_neq0 ; rewrite v_eq0 invr0 mulr0 eqxx.
have [-> | y2_neq0] := eqVneq y2 0 ; first by rewrite horner_evalE hornerC.
have ev_u_neq0 : ev u != 0.
  rewrite /ev /= horner_evalE.
  apply/negP => /eqP /polyXsubCP ev_u_eq0.
  move/polyXsubCP : ev_v_eq0 => ev_v_eq0.
  move/coprimepP : coprime_u_v => coprime_u_v.
  move : (coprime_u_v ('X - a%:P)) => H.
  move : (H ev_u_eq0 ev_v_eq0).
  by rewrite polyXsubC_eqp1.
move/eqP ; rewrite eq_divf // ?tofrac_eq0 //.
rewrite -!tofracM tofrac_eq.
move/eqP/(congr1 ev).
rewrite !rmorphM ev_v_eq0 mulr0 => /eqP ; rewrite mulf_eq0.
move/negbTE : ev_u_neq0 => ->.
by rewrite orFb => /eqP ->.
Qed.

Lemma irreducible_has_pole (u v : {poly K}) :
  (u %:F / v %:F) != 0 -> coprimep u v ->
  reflect (has_pole ev (u %:F / v %:F)) (ev v == 0).
Proof.
move => x_neq0 coprime_u_v.
apply/(equivP eqP) ; split ; last first.
  move => H_pole.
  by apply: (H_pole (u, v)).
by move => * ; apply: aux_irreducible_has_pole.
Qed.

Fact coprimep01 (K' : fieldType ): coprimep (0 : {poly K}) (1 : {poly K}).
Proof. by rewrite coprimep_sym coprimep0 
                                      -size_poly_eq1 size_polyC oner_neq0. Qed.

Lemma fracpolyE (p : {fracpoly K}) : 
    {q : {poly K} * {poly K} | p = (q.1)%:F / (q.2)%:F & (q.2 != 0) && 
    (coprimep q.1 q.2)}.
Proof.
move: (fracE p) => [[u v] /= Hx] v_neq0.
have [p_eq0 | p_neq0] := eqVneq p 0.
  exists (0,1) ; first by rewrite p_eq0 tofrac0 !mul0r.
  rewrite oner_neq0 coprimep_sym coprimep0.
  by rewrite -size_poly_eq1 size_polyC oner_neq0.
pose u' := u %/ (gcdp u v) ; pose v' := v %/ (gcdp u v) ; exists (u', v').
+ apply/eqP ; rewrite Hx eq_divf ?tofrac_eq0 //= ; last first. 
    by rewrite dvdp_div_eq0 // dvdp_gcdr.
  move : (dvdp_gcdl u v) (dvdp_gcdr u v).
  rewrite !dvdp_eq => /eqP Hu /eqP Hv.
  by rewrite -!tofracM tofrac_eq Hv {1}Hu -mulrA [X in _ * X]mulrC.
+ apply/andP ; split.
- rewrite divp_eq0 ; apply/or3P ; case.
  -- by move/negbTE: v_neq0 ->.
  -- rewrite gcdp_eq0 => /andP [/eqP u_eq0 _].
     move: Hx ; rewrite u_eq0 rmorph0 mul0r => /eqP.
     by apply/negP.
- apply/negP ; rewrite -leqNgt.
  by apply: leq_gcdpr.
by apply: coprimep_div_gcd ; apply/orP ; right.
Qed.

Lemma associate_num_fracpolyE (p q : {poly K}) : q != 0 ->
  coprimep p q ->
  p %= (projT1 (fracpolyE (p %:F/ q %:F))).1.
Proof.
move => q_neq0 coprime_p_q.
move: (fracpolyE (p %:F/ q %:F)) => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
move/eqP: Hx.
rewrite eq_divf ?tofrac_eq0 // -!rmorphM tofrac_eq /eqp => /eqP H.
rewrite -(Gauss_dvdpl _ coprime_p_q) -H dvdp_mulIl.
by rewrite -(Gauss_dvdpl _ coprime_u_v) H dvdp_mulIl.
Qed.

Lemma associate_denom_fracpolyE (p q : {poly K}) : q != 0 ->
  coprimep p q ->
  q %= (projT1 (fracpolyE (p %:F/ q %:F))).2.
Proof.
move => q_neq0 coprime_p_q.
rewrite coprimep_sym in coprime_p_q.
move: (fracpolyE (p %:F/ q %:F)) => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
rewrite coprimep_sym in coprime_u_v.
move/eqP: Hx; rewrite eq_divf ?tofrac_eq0 // -!rmorphM tofrac_eq /eqp=> /eqP H.
rewrite -(Gauss_dvdpr _ coprime_p_q) H dvdp_mulIr.
by rewrite -(Gauss_dvdpr _ coprime_u_v) -H dvdp_mulIr.
Qed.

Fact eqp_neq0P (p q : {poly K}) : p != 0 -> 
                               reflect (exists (c : K), (p = c *: q)) (p %= q).
Proof.
move => p_neq0.
apply: (equivP (eqpP p q)) ; split.
+ move => [[c1 c2] /= /andP [c1_neq0 c2_neq0]] Hpq.
  exists (c2 / c1) ; apply: (scalerI c1_neq0).
  by rewrite Hpq scalerA mulrCA divff // mulr1.
+ move => [c H].
  exists (1, c) => /=.
- rewrite oner_neq0 andTb ; apply/negP => /eqP c_eq0.
  move: H ; rewrite c_eq0 scale0r.
  by move/eqP ; move/negbTE: p_neq0 ->.
- by rewrite scale1r.
Qed.

Lemma associate_fracpolyE (p q : {poly K}) : q != 0 -> coprimep p q ->
  let (u, v) := projT1 (fracpolyE (p %:F/ q %:F)) in
  exists (c : K), ((p == c *: u) && (q == c *: v)).
Proof.
move => q_neq0 coprime_p_q.
move: (associate_denom_fracpolyE q_neq0 coprime_p_q)
      (associate_num_fracpolyE q_neq0 coprime_p_q).
move: (fracpolyE (p %:F/ q %:F)) => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
move/(eqp_neq0P v q_neq0) => [cv /eqP Hcv].
have [p_eq0 | p_neq0] := eqVneq p 0.
+ move/eqP : Hx ; rewrite p_eq0 rmorph0 mul0r eq_sym mulf_eq0 invr_eq0. 
  rewrite !tofrac_eq0 ; move/negbTE : v_neq0 ->.
  rewrite orbF ; move/eqP => -> _.
  by exists cv ; rewrite scaler0 eqxx Hcv.
+ move/(eqp_neq0P u p_neq0) => [cu Hcu].
  move/eqP : Hx.
  rewrite eq_divf ?tofrac_eq0 // -!rmorphM tofrac_eq.
  move/eqP : Hcv => Hcv.
  rewrite {1}Hcu {1}Hcv -scalerCA -subr_eq0 -!scalerAl -scalerBl scaler_eq0.
  rewrite subr_eq0 mulf_eq0. 
  move/orP => [/eqP dsa | /orP [/eqP u_eq0 | /eqP v_eq0]].
- by exists cu ; rewrite Hcu dsa Hcv !eqxx.
- by move: p_neq0 ; rewrite Hcu u_eq0 scaler0 eqxx.
- by move: q_neq0 ; rewrite Hcv v_eq0 scaler0 eqxx.
Qed.

Lemma fracpoly_div_tofracl (p q : {poly K}) : q != 0 ->
  let (u, v) := projT1 (fracpolyE (p %:F/ q %:F)) in
  u %| p.
Proof.
move => q_neq0.
move: (fracpolyE (p %:F/ q %:F)) => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
move/eqP: Hx ; rewrite eq_divf ?tofrac_eq0 // -!rmorphM tofrac_eq => /eqP H.
by rewrite -(Gauss_dvdpl _ coprime_u_v) H dvdp_mulIl.
Qed.

Lemma fracpoly_div_tofracr (p q : {poly K}) : q != 0 ->
  let (u, v) := projT1 (fracpolyE (p %:F/ q %:F)) in
  v %| q.
Proof.
move => q_neq0.
move: (fracpolyE (p %:F/ q %:F)) => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
move/eqP: Hx ; rewrite eq_divf ?tofrac_eq0 // -!rmorphM tofrac_eq => /eqP H.
rewrite coprimep_sym in coprime_u_v.
by rewrite -(Gauss_dvdpr _ coprime_u_v) -H dvdp_mulIr.
Qed.

Lemma evrepr : forall (x : {fracpoly K}),
  {y : {poly K} * {poly K} | 
      x = y.1%:F / y.2%:F & (ev y.2 != 0) && (coprimep y.1 y.2)} 
  + has_pole ev x.
Proof.
move => x.
move: (fracpolyE x) => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
have [u_eq0 | u_neq0] := eqVneq u 0.
  left ; exists (0,1) ; first by rewrite Hx u_eq0 tofrac0 !mul0r.
  rewrite rmorph1 oner_neq0 coprimep_sym coprimep0.
  by rewrite -size_poly_eq1 size_polyC oner_neq0.
have [/eqP ev_v_eq0 | ev_V_neq0] := eqVneq (ev v) 0.
  right ; rewrite Hx ; apply/irreducible_has_pole => //.
  by rewrite mulf_eq0 invr_eq0 !tofrac_eq0 negb_or ; apply/andP.
by left ; exists (u, v) => //= ; apply/andP.
Qed.

Fact aux_evrepr : forall (x : {fracpoly K}),
  {y : {poly K} * {poly K} | x = y.1%:F / y.2%:F & (ev y.2 != 0)} 
  + has_pole ev x.
Proof.
move => x.
move : (evrepr x) => [[y Hx] /andP [ev_y2_neq0 _]| x_has_pole].
+ by left ; exists y.
+ by right.
Qed.

Definition fracpoly_ev := f_eval aux_evrepr.

Lemma fracpoly_ev_div (u v : {fracpoly K}) : 
  fracpoly_ev v != 0 ->fracpoly_ev (u / v) = (fracpoly_ev u) / (fracpoly_ev v).
Proof. by move => H ; rewrite /fracpoly_ev f_eval_div. Qed.

Lemma fracpoly_ev_frac (u : {poly K}) : fracpoly_ev u%:F = ev u.  
Proof. by rewrite /fracpoly_ev f_eval_frac. Qed.

Lemma fracpoly_ev0 : fracpoly_ev 0 = 0.
Proof. by rewrite /fracpoly_ev f_eval0. Qed.

Lemma irreducible_root (u v : {poly K}) : v != 0 -> coprimep u v ->
  reflect (has_root ev (u %:F / v %:F)) (ev u == 0).
Proof.
move => v_neq0 coprime_u_v.
apply/(equivP eqP) ; split ; last first.
+ move => [eq_0 | H_root].
- move: eq_0 ; rewrite mulf_eq0 invr_eq0 !tofrac_eq0.
  move/negbTE : v_neq0 ->.
  rewrite orbF ; move/eqP ->.
  exact: rmorph0.
- exact: (H_root (_, _)).
+ move => ev_u_eq0.
  have [x_eq0 | x_neq0] := eqVneq (u%:F / v%:F) 0.
- by left ; apply/eqP.
- right => [[y1 y2] /= H].
  have y2_neq0: y2 != 0.
-- apply/negP => /eqP y2_eq0.
   move: H ; rewrite y2_eq0 rmorph0 invr0 mulr0.
   by move/eqP ; move/negbTE : x_neq0  ->. 
-- have: u %| y1.
     rewrite -(Gauss_dvdpr _ coprime_u_v).
     move/eqP: H ; rewrite eq_divf ?tofrac_eq0 // -!rmorphM tofrac_eq.
     move/eqP ; rewrite [RHS]mulrC => <-.
     exact: dvdp_mulIl.
  rewrite horner_evalE dvdp_eq => /eqP ->.
  by rewrite hornerM -!horner_evalE ev_u_eq0 mulr0.
Qed. 

Lemma evrepr2 : forall (x : {fracpoly K}),
  {y : {poly K} * {poly K} | x = y.1%:F / y.2%:F & 
      (ev y.1 != 0) && (ev y.2 != 0) && (coprimep y.1 y.2)} 
  + has_pole ev x
  + has_root ev x.
Proof.
move => x.
move: (evrepr x) => [[[x1 x2] /= Hx] 
             /andP [ev_x2_neq0 H_coprime] | has_pole_x] ; last by left ; right.
have [ev_y2_eq0 | ev_y2_neq0] := eqVneq (horner_eval a x1) 0.
+ right ; rewrite Hx.
  apply/irreducible_root => // ; last by apply/eqP.
  apply/negP => /eqP x2_eq0.
  by move: ev_x2_neq0 ; rewrite x2_eq0 horner_evalE hornerC eqxx.
+ left ; left ; exists (x1, x2) => //.
  by rewrite ev_x2_neq0 ev_y2_neq0 H_coprime.
Qed. 

Lemma evrepr3 : forall (x : {fracpoly K}),
  {y : {poly K} * {poly K} | x = y.1%:F / y.2%:F & 
      (ev y.1 != 0) && (ev y.2 != 0) && (coprimep y.1 y.2)} 
  + has_pole ev x
  + has_non_trivial_root ev x
  + {x == 0}.
Proof.
move => x.
move: (evrepr2 x) => [[[[x1 x2] /= Hx] H | has_pole_x] | has_root_x].  
+ by left ; left ; left ; exists (x1, x2). 
+ by left ; left ; right.
+ have [x_eq0 | x_neq0] := boolP (x == 0).
- by right.
- left ; right ; case: has_root_x => //.
  by move/negbTE : x_neq0  ->.
Qed. 

Lemma fracpoly_ev_eq0 (x : {fracpoly K}) : 
                          reflect (has_general_root ev x) (fracpoly_ev x == 0).
Proof.
apply/(equivP eqP) ; split.
+ move: (evrepr3 x) => 
  [[[[[x1 x2] /= Hx] /andP [/andP [ev_x1_neq0 ev_x2_neq0] coprime_x1_x2] 
  | has_pole_x] | root_x] | x_eq0] ; last 3 first.
- by move => _ ; right.
- by move => _ ; left ; right.
- by move => _ ; left ; left.
  rewrite Hx fracpoly_ev_div ; last by rewrite fracpoly_ev_frac. 
  move/eqP ; rewrite mulf_eq0 invr_eq0 !fracpoly_ev_frac.
  by move/negbTE : ev_x1_neq0 -> ; move/negbTE : ev_x2_neq0 ->.
+ move => [x_has_root | x_has_pole].
- by apply: f_eval_root.
- by apply: f_eval_pole.
Qed.

Lemma fracpoly_ev_div_coprimep (p q : {poly K}) : coprimep p q ->
           fracpoly_ev (p%:F / q%:F) = (fracpoly_ev p%:F) / (fracpoly_ev q%:F).
Proof.
move => coprime_p_q.
set x:= p%:F / q%:F.
have [/eqP x_eq0 | x_neq0] := boolP (x == 0).
+ rewrite x_eq0 ; move/eqP: x_eq0.
  rewrite mulf_eq0 invr_eq0 => /orP [/eqP -> | /eqP ->].
- by rewrite fracpoly_ev0 mul0r.
- by rewrite !fracpoly_ev0 invr0 mulr0.
+ have [/eqP ev_q_eq0 | ev_q_neq0] := boolP (ev q == 0) ; last first.
    by rewrite fracpoly_ev_div fracpoly_ev_frac.
  rewrite !fracpoly_ev_frac ev_q_eq0 invr0 mulr0.
  move/eqP/(irreducible_has_pole x_neq0 coprime_p_q): ev_q_eq0.
  exact: f_eval_pole.
Qed.

Definition Xinv := 1/(('X : {poly K}) %:F).

Lemma Xinv_eq0 : (Xinv == 0) = false.
Proof. rewrite /Xinv mul1r invr_eq0 tofrac_eq0 ; exact: polyX_eq0. Qed.

Lemma pole_Xinv : reflect (has_pole ev Xinv) (a == 0).
Proof.
apply/(equivP eqP) ; split.
+ move => a_eq0 ; apply/irreducible_has_pole.
- by rewrite mulf_eq0 negb_or invr_eq0 !tofrac_eq0 oner_eq0 polyX_eq0.
- exact: coprime1p.
  by apply/eqP ; rewrite evX.
+ move/irreducible_has_pole ; rewrite mulf_neq0 ; last 2 first.
- by rewrite tofrac_eq0 oner_neq0.
- by rewrite invr_eq0 tofrac_eq0 polyX_eq0.
  rewrite coprime1p evX => H.
  by apply/eqP ; apply: H.
Qed.

Lemma fracpoly_evC (c : K) : fracpoly_ev (c %:FP) = c.
Proof. by rewrite /fracpoly_ev f_eval_frac evC. Qed.

End EvalRatFrac.
End EvalRatFrac.

Local Notation "x %:FP" := (EvalRatFrac.to_fracpoly x).
Local Notation "p ^ f" := (map_poly f p).
Local Notation "p ^:FP" := (p ^ (@EvalRatFrac.to_fracpoly _)). 

Module MapRatFrac.
Section MapRatFrac.
Import EvalFrac.
Import EvalRatFrac.

Variable (K : fieldType).

Let ev := [rmorphism of tofrac \o @map_poly _ _ (@to_fracpoly K)].

Lemma evX : ev 'X = 'X %:F.
Proof. by rewrite /ev /= map_polyX. Qed.

Lemma ev_inj : injective ev.
Proof. 
apply: inj_comp ; first exact: tofrac_inj.
exact: map_poly_inj.
Qed.

(*
Definition no_pole := (has_no_pole ev_inj).
Hint Resolve no_pole.
*)

Let ev_repr := (fun x => @inl _ (has_pole ev x) (frepr ev_inj x)).

Definition lift_fracpoly := f_eval_rmorphism ev_repr ev_inj.

Canonical lift_fracpoly_rmorphism := f_eval_rmorphism ev_repr ev_inj.

Lemma lift_fracpoly_tofrac (p : {poly K}) : 
  lift_fracpoly (p %:F) = (p ^:FP) %:F.
Proof. rewrite /lift_fracpoly ; exact: (f_eval_frac _). Qed.

Lemma tofrac_scale (c : K) (p : {poly K}) : (c *: p)%:F = (c%:P)%:F * (p %:F).
Proof. by rewrite -mul_polyC rmorphM. Qed.

Lemma lift_fracpoly_scale (c : K) (p : {poly K}) : 
lift_fracpoly (c *: p)%:F = 
  (lift_fracpoly (c%:P)%:F) * (lift_fracpoly (p %:F)).
Proof. 
by move/(congr1 lift_fracpoly): (tofrac_scale c p) ; rewrite rmorphM. 
Qed.

Lemma mul_fracpolyC (c : K) (p : {poly K}): (c *: p)%:F = ((c %:FP) * (p %:F)).
Proof. by rewrite -mul_polyC rmorphM. Qed.

Lemma lift_fracpoly_div (p q : {fracpoly K}) : lift_fracpoly (p / q) = 
(lift_fracpoly p) / (lift_fracpoly q).
Proof.
have [q_eq0 | q_neq0] := eqVneq q 0.
  by rewrite q_eq0 rmorph0 !invr0 !mulr0 rmorph0. 
by apply: rmorph_div ; rewrite unitfE.
Qed.

Lemma lift_fracpoly_X : lift_fracpoly ('X %:F) = 'X %:F.
Proof. by rewrite lift_fracpoly_tofrac map_polyX. Qed.

Lemma lift_fracpolyC (c : K) : lift_fracpoly (c %:FP) = (c %:FP) %:FP.
Proof. by rewrite lift_fracpoly_tofrac map_polyC. Qed.

Lemma lift_fracpoly_Xinv : 
                     lift_fracpoly (Xinv K) = Xinv [fieldType of {fracpoly K}].
Proof.
rewrite /Xinv -(rmorph1 [rmorphism of tofrac]) /=.
rewrite f_eval_div_frac ; last by rewrite evX tofrac_eq0 polyX_eq0.
by rewrite rmorph1 evX.
Qed.

End MapRatFrac.
End MapRatFrac.

(* Hint Resolve MapRatFrac.no_pole. *)

Module CompFrac.
Section CompFrac.
Import EvalFrac.
Import EvalRatFrac.
Import MapRatFrac.

Variable (K : fieldType).

Definition comp_fracpoly (r s : {fracpoly K}) := 
  fracpoly_ev r (@lift_fracpoly _ s).
Notation "p \FPo q" := (comp_fracpoly q p) 
                                (at level 2, format "p  \FPo  q") : ring_scope. 

Lemma comp_fracpoly0 p : 0 \FPo p = 0.
Proof. by rewrite /comp_fracpoly /fracpoly_ev rmorph0 f_eval0. Qed.

Lemma comp_fracpolyD p q r :
  ~ has_pole (ev r) (@lift_fracpoly _ p) -> 
  ~ has_pole (ev r) (@lift_fracpoly _ q) ->
  (p + q) \FPo r = (p \FPo r) + (q \FPo r).
Proof.
move => pole_r_p pole_r_q.
by rewrite /comp_fracpoly (rmorphD (@lift_fracpoly K)) [LHS]f_evalD. 
(* rewrite (rmorphD (@lift_fracpoly _)). INFINITE COMPUTATION ? *)
Qed.

Lemma comp_fracpolyN p r : ~ has_pole (ev r) (@lift_fracpoly _ p) -> 
  (-p) \FPo r = -(p \FPo r).
Proof.
move => pole_r_p.
by rewrite /comp_fracpoly (rmorphN (@lift_fracpoly K)) [LHS]f_evalN.
Qed.

Lemma comp_fracpolyM p q r :
  ~ has_pole (ev r) (@lift_fracpoly _ p) -> 
  ~ has_pole (ev r) (@lift_fracpoly _ q) ->
  (p * q) \FPo r = (p \FPo r) * (q \FPo r).
Proof.
move=> pole_r_p pole_r_q.
by rewrite /comp_fracpoly (rmorphM (@lift_fracpoly K)) [LHS]f_evalM.
Qed.

Lemma comp_fracpolyV p r :
  ~ has_pole (ev r) (@lift_fracpoly _ p) -> 
  (p ^-1) \FPo r = (p \FPo r) ^-1.
Proof.
move => pole_r_p.
have [p_eq0 | p_neq0] := boolP (p == 0).
  by move/eqP: p_eq0 -> ; rewrite invr0 comp_fracpoly0 invr0.
rewrite /comp_fracpoly (rmorphV (@lift_fracpoly K)) ; last by rewrite unitfE.
by rewrite [LHS]f_eval_inv.
Qed.

Lemma comp_fracpoly_div p q r : 
  f_eval (aux_evrepr r) ((lift_fracpoly K) q) != 0 ->
  (p / q) \FPo r = (p \FPo r) / (q \FPo r).
Proof.
move => eval_q_in_r_neq0.
by rewrite /comp_fracpoly lift_fracpoly_div fracpoly_ev_div.
Qed.

Lemma NcstNpole (r : {poly K}) (p : {fracpoly K}) : 
  (size r > 1) -> ~ has_pole (ev r %:F) (@lift_fracpoly _ p).
Proof.
move => Hsize H.
have [[p1 p2]] := fracE p => /= Hp p2_neq0.
move: Hp => /(congr1 (@lift_fracpoly _)).
rewrite rmorphM rmorphV; last by rewrite unitfE tofrac_eq0.
rewrite ![in RHS]lift_fracpoly_tofrac => H_lift_p.
move: ((H (p1^:FP, p2^:FP)) H_lift_p) => /=.
rewrite horner_evalE map_poly_comp_id0 // horner_map /= ; move/eqP.
rewrite tofrac_eq0 -lead_coef_eq0 lead_coef_comp // mulf_eq0 lead_coef_eq0.
move/negbTE : p2_neq0 => p2_neq0 ; rewrite p2_neq0 orFb ; apply/negP.
by rewrite expf_neq0 // lead_coef_eq0 -size_poly_gt0 (ltn_trans _ Hsize).
Qed.

Lemma nice_compfracpolyD (p q : {fracpoly K}) (r : {poly K}) : 
    (size r > 1) -> (p + q) \FPo (r %:F) = (p \FPo (r %:F)) + (q \FPo (r %:F)).
Proof.
move => size_r.
by rewrite -f_evalD ?(NcstNpole size_r) -?rmorphD // ; apply: NcstNpole. 
Qed.

Lemma comp_fracpolyX (p : {fracpoly K}) : ('X %:F) \FPo p = p.
Proof.
rewrite /comp_fracpoly /fracpoly_ev /lift_fracpoly /=.
by rewrite !(f_eval_frac _) /=  horner_evalE !map_polyX hornerX.
Qed.

Lemma comp_fracpolyC (c : K) (p : {fracpoly K}) : (c %:FP) \FPo p = c %:FP.
Proof. by rewrite /comp_fracpoly lift_fracpolyC fracpoly_evC. Qed.

Lemma comp_fracpolyXr (p : {fracpoly K}) : p \FPo ('X %:F) = p.
Proof.
have [[p1 p2]] := fracE p => /= Hp p2_neq0.
rewrite Hp /comp_fracpoly /fracpoly_ev /lift_fracpoly /=.
rewrite f_eval_div_frac /= ; last by rewrite tofrac_eq0 to_fracpoly_eq0.
rewrite f_eval_div ; last first.
  rewrite f_eval_frac /= horner_evalE map_poly_comp horner_map tofrac_eq0 /=.
  by rewrite -/(@comp_poly _ _ _) (comp_polyXr _).
rewrite !f_eval_frac /= !horner_evalE !map_poly_comp !horner_map /=.
by rewrite -!/(_ \Po 'X) !(comp_polyXr _).
(* by rewrite -![(_ ^ polyC).['X]]/(_ \Po 'X) !(comp_polyXr _). SUBSTITUTION *)
Qed.

Lemma comp_fracpolyXn (m : nat) (p : {fracpoly K}) : 
  (('X ^+m) %:F) \FPo p = p ^+m. 
Proof.
rewrite /comp_fracpoly /fracpoly_ev /= /lift_fracpoly /=.
rewrite !f_eval_frac /= horner_evalE !rmorphX /= horner_exp_comm !map_polyX.
+ by rewrite hornerX.
+ by rewrite /comm_poly mulrC.
Qed.

Lemma compXnXinv (m : nat) : (('X^m)%:F) \FPo (Xinv _) = (('X^m)%:F) ^-1.
Proof. by rewrite comp_fracpolyXn tofracX /Xinv mul1r exprVn. Qed. 

Lemma pole_Xinv0 : has_pole (ev 0) ((lift_fracpoly K) (Xinv K)).
Proof. rewrite lift_fracpoly_Xinv /= ; exact: pole_Xinv. Qed. 

Lemma comp_fracpoly_Xinv (p : {fracpoly K}) : (Xinv _) \FPo p = p ^-1.
Proof.
have [p_eq0 | p_neq0] := eqVneq p 0.
  rewrite p_eq0 invr0 /comp_fracpoly /fracpoly_ev ; apply: f_eval_pole.
  exact: pole_Xinv0.
rewrite comp_fracpoly_div ; last first.
  by rewrite -/(@fracpoly_ev _ _) -/(@comp_fracpoly _ _) comp_fracpolyX.
by rewrite comp_fracpolyC rmorph1 mul1r comp_fracpolyX.
Qed.

Lemma comp_fracpoly_Xinv_Xinv : (Xinv _) \FPo (Xinv _) = 'X %:F.
Proof. by rewrite comp_fracpoly_Xinv /Xinv mul1r invrK. Qed.

Lemma comp_p_invX (p : {poly K}) : (p %:F) \FPo (Xinv _) = 
  \sum_(0 <= i < size p) ((p`_i) %:FP) * ((Xinv _) ^+i).
Proof.
rewrite /comp_fracpoly lift_fracpoly_tofrac /fracpoly_ev f_eval_frac.
rewrite /to_fracpoly /= horner_evalE horner_poly (big_mkord predT).
by apply: eq_bigr. 
Qed. 

Lemma comp_fracpoly_eq0 (p q : {fracpoly K}) : 
  has_pole (ev q) (@lift_fracpoly _ p) -> (p \FPo q = 0). 
Proof. by apply: f_eval_pole. Qed.

Lemma NpoleFP (p : {poly K}) (q : {fracpoly K}): 
  ~ has_pole (ev q) (@lift_fracpoly _ p%:F).
Proof. by rewrite lift_fracpoly_tofrac ; apply: Npole_tofrac. Qed.

Lemma comp_fracpoly_frac_eq0 (p : {poly K}) (q : {fracpoly K}) :
  ~(has_pole (ev q) (@lift_fracpoly _ p%:F)).
Proof. exact: NpoleFP. Qed.

Lemma comp_fracpoly_div_frac (p1 p2 : {poly K}) (q : {fracpoly K}) :
  coprimep p1 p2 ->
  ((p1%:F / p2%:F) \FPo q) = (p1%:F \FPo q) / (p2%:F \FPo q).
Proof.
move => coprime_p1_p2.
rewrite /comp_fracpoly lift_fracpoly_div !lift_fracpoly_tofrac.
by rewrite fracpoly_ev_div_coprimep // coprimep_map.
Qed.

Lemma inv_comp_fracpoly (p q : {fracpoly K}) : (p \FPo q) ^-1 = (p ^-1 \FPo q).
Proof.
have [-> | p_neq0] := eqVneq p 0.
+ by rewrite invr0 comp_fracpoly0 invr0.
+ rewrite /comp_fracpoly /fracpoly_ev rmorphV.
- by rewrite f_eval_inv.
- by rewrite unitfE.
Qed.

End CompFrac.
End CompFrac.

