(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  some doc here                                                            *)
(*****************************************************************************)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype div tuple finfun bigop finset fingroup perm ssralg poly.
From mathcomp
Require Import polydiv mxpoly binomial bigop ssralg finalg zmodp matrix mxalgebra polyXY ring_quotient.
From Newtonsums Require Import auxresults fraction polydec revpoly truncpowerseries expansiblefracpoly finmap.

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

Reserved Notation "x %:F" (at level 2, format "x %:F").
Reserved Notation "p \FPo q" (at level 2, format "p \FPo q").
Reserved Notation "r ~i" (at level 2, format "r ~i").


Section NewtonRepresentation.

Variables (K L : fieldType) (n : nat) (iota : {rmorphism K -> L}).

Local Notation "p ^ f" := (map_poly f p).

Fact iota_eq0 x : (iota x == 0) = (x == 0).
Proof. exact: fmorph_eq0. Qed.

Hint Resolve iota_eq0.

Fact size_map_iota_p (p : {poly K}) : size (p ^ iota) = size p.
Proof. rewrite size_map_inj_poly //; [exact: fmorph_inj | exact: rmorph0]. Qed.

Fact lead_coef_map_iota_p (p : {poly K}) : 
  lead_coef (p ^ iota) = iota (lead_coef p).
Proof. rewrite lead_coef_map_inj //; [exact: fmorph_inj | exact: rmorph0]. Qed.

Definition tofrac_iota := 
         [rmorphism of (@tofrac [idomainType of {poly L}]) \o (map_poly iota)].

Notation "x ~i"  := (tofrac_iota x) (at level 2, format "x ~i").

Lemma tofrac_iota_inj : injective tofrac_iota.
Proof.
apply: inj_comp ; first exact: tofrac_inj.
exact: map_poly_inj.
Qed.

Lemma tofrac_iota_eq0 x : (tofrac_iota x == 0) = (x == 0).
Proof. rewrite -(rmorph0 tofrac_iota) ; exact: (inj_eq tofrac_iota_inj). Qed.

Definition tofrac_iota_repr := 
          (fun x => @inl _ (has_pole tofrac_iota x) (frepr tofrac_iota_inj x)).

Definition fracpoly_iota := f_eval_rmorphism tofrac_iota_repr tofrac_iota_inj.

Notation "x ~~i"  := (fracpoly_iota x) (at level 2, format "x ~~i").

Lemma devs_in_pw_fracpoly_iota (x : {fracpoly K}) : 
  devs_in_pw (x ~~i) = devs_in_pw x.
Proof.
move: (fracpolyE x) => [ [u v] /= Hx ] /andP [ v_neq0 coprime_u_v ].
rewrite Hx devs_in_pwE // f_eval_div_frac ; last first.
  rewrite raddf_eq0 //.
  exact: tofrac_iota_inj.
rewrite devs_in_pwE ; last 2 first.
  + by rewrite map_poly_eq0.
  + by rewrite coprimep_map.
by rewrite -{1}[0](rmorph0 iota) horner_map fmorph_eq0.
Qed.

Lemma fracpoly_iota_div (p q : {fracpoly K}) : (p / q) ~~i = (p ~~i) / (q ~~i).
Proof.
have [ q_eq0 | q_neq0] := eqVneq (q ~~i) 0.
+ move/eqP: q_eq0 ; rewrite fmorph_eq0 => /eqP ->.
  by rewrite invr0 mulr0 rmorph0 invr0 mulr0.
+ by rewrite /fracpoly_iota /= f_eval_div.
Qed.

Lemma map_powerseries_to_powerseries (x : {fracpoly K}) :
          map_powerseries iota (to_powerseries n x) = to_powerseries n (x ~~i).
Proof.
move: (fracpolyE x) => [ [u v] /= Hx ] /andP [ v_neq0 coprime_u_v ].
rewrite Hx f_eval_div_frac ; last first.
  rewrite raddf_eq0 //. 
  exact: tofrac_iota_inj.
have [ v0_eq0 | v0_neq0 ] := eqVneq v`_0 0.
+ rewrite to_powerseries_eq0 // ; rewrite to_powerseries_eq0 // ; last 2 first.
- rewrite -horner_coef0 -{1}[0](rmorph0 iota) horner_map. 
  apply/eqP ; rewrite fmorph_eq0 horner_coef0.
  by apply/eqP.
- by rewrite coprimep_map.
  by rewrite rmorph0.
+ rewrite to_powerseries_coprimep // to_powerseries_coprimep // ; last 2 first.
- by rewrite -horner_coef0 -{1}[0](rmorph0 iota) 
                                            horner_map fmorph_eq0 horner_coef0. 
- by rewrite coprimep_map.
by rewrite !truncate_map_poly rmorph_div // truncate_is_unit.
Qed.

Fact proof_map_expansible (x : expansibleFracpoly K): (devs_in_pw ((val x) ~~i)).
Proof. 
by rewrite devs_in_pw_fracpoly_iota underlying_fracpolyP. 
Qed.

Definition map_expansible (x : expansibleFracpoly K) :=
  ExpansibleFracpoly (proof_map_expansible x).

Lemma map_powerseries_expanse (x : expansibleFracpoly K) :
             map_powerseries iota (expanse n x) = expanse n (map_expansible x).
Proof. by rewrite -!to_powerseries_expanse map_powerseries_to_powerseries. Qed.

Fact rev_powerseries_proof (p : (powerseries K n)) : size (revp p) <= n.+1.
Proof. move: p => [ p pr ]; rewrite (leq_trans (revp_proof _)) //. Qed.

Definition rev_powerseries (p : (powerseries K n)) := 
  Powerseries (rev_powerseries_proof p). 

Lemma rev_ps_unit (p : (powerseries K n)) : p != 0 -> 
  powerseries_unit (rev_powerseries p).
Proof. 
move: p => [ [s pr1] pr2 ] Hpneq0.
by rewrite /powerseries_unit coef0_rev unitfE lead_coef_eq0 Hpneq0. 
Qed.

Lemma horner_prod_comm (s : seq {poly L}) (x : L) : 
  (\prod_(q <- s) (q)).[x] = \prod_(q <- s) (q.[x]).
Proof. by rewrite -horner_evalE rmorph_prod. Qed.

Local Notation "p \FPo q" := (comp_fracpoly q p) 
  (at level 2, format "p  \FPo  q") : ring_scope. 
Local Notation "x %:FP" := (EvalRatFrac.to_fracpoly x). 
Local Notation "p ^ f" := (map_poly f p).
Local Notation "p ^:FP" := (p ^ (@EvalRatFrac.to_fracpoly _)). 

Lemma tofrac_iota_tofrac (p : {poly K}) : (p %:F)~~i = p ~i.
Proof. by rewrite /fracpoly_iota /= f_eval_frac. Qed. 

Lemma fracpoly_iota_eq0 (u : {fracpoly K}) : (u ~~i == 0) = (u == 0).
Proof. by rewrite fmorph_eq0. Qed.

(* Lemma comp_fracpoly_tofrac (p : {poly K}) (q : {fracpoly K}) :
  ((p %:F) \FPo q) ~~i = (p ~i) \FPo (q ~~i). *)

Lemma ev_map (p : {poly K}) (a : K) : ev (iota a) (p ^ iota) = iota (ev a p).
Proof. by rewrite /ev /= !horner_evalE horner_map. Qed.

Lemma fracpoly_ev_map (p : {fracpoly K}) (a : K) :
  fracpoly_ev (iota a) (p ~~i) = iota (fracpoly_ev a p).
Proof.
have [ [ p1 p2 Hp /andP [ p2_neq0 coprime_p1_p2 ] ] ] := fracpolyE p.
rewrite /= in Hp p2_neq0 coprime_p1_p2.
rewrite Hp fmorph_div !tofrac_iota_tofrac /tofrac_iota [LHS]/=.
rewrite !fracpoly_ev_div_coprimep // ; last by rewrite coprimep_map.
by rewrite !fracpoly_ev_frac !ev_map fmorph_div.
Qed.

Lemma evE (K' : fieldType) (a : K') (p : {poly K'}) : ev a p = p.[a].
Proof. by rewrite /ev /= horner_evalE. Qed.

Lemma fracpoly_iota_to_fracpoly (x : K) : (iota x)%:FP = (x %:FP) ~~i.
Proof. by rewrite tofrac_iota_tofrac /to_fracpoly /= -map_polyC. Qed.

Lemma to_fracpoly_map_iota (p : {poly K}) :
  (p ^ iota) ^:FP = (p ^:FP) ^ fracpoly_iota.
Proof.
rewrite -!map_poly_comp /=.
move: p ; apply: eq_map_poly => x /=.
exact: fracpoly_iota_to_fracpoly.
Qed.

Lemma fracpoly_iota_comp_fracpoly (p q : {fracpoly K}) :
  (p \FPo q)~~i = (p ~~i) \FPo (q ~~i).
Proof.
have [ [ p1 p2 Hp /andP [p2_neq0 coprime_p1_p2 ] ] ] := fracpolyE p.
rewrite /= in Hp p2_neq0 coprime_p1_p2.
rewrite Hp comp_fracpoly_div_frac // fmorph_div fracpoly_iota_div.
rewrite !tofrac_iota_tofrac comp_fracpoly_div_frac ; last first.
  by rewrite coprimep_map.
congr (_ / _).
+ rewrite /comp_fracpoly !lift_fracpoly_tofrac !fracpoly_ev_frac !evE.
  have -> : (p1 ^ iota)^:FP = (p1^:FP) ^ fracpoly_iota ; last first.
    by rewrite horner_map.
  exact: to_fracpoly_map_iota.
+ rewrite /comp_fracpoly !lift_fracpoly_tofrac !fracpoly_ev_frac !evE.
  have -> : (p2 ^ iota)^:FP = (p2^:FP) ^ fracpoly_iota ; last first.
    by rewrite horner_map.
  exact: to_fracpoly_map_iota.
Qed.

Lemma revp_p_Xinv (K' : fieldType) (p : {poly K'}) : 
             (p %:F) \FPo (Xinv _) * (('X %:F) ^+((size p).-1)) = (revp p) %:F.
Proof.
have [ peq0 | pneq0 ] := boolP (p == 0).
  move/eqP : peq0 => peq0 ; rewrite peq0 comp_fracpoly0 mul0r.
  symmetry ; apply/eqP.
  by rewrite tofrac_eq0 revp_eq0.
rewrite comp_p_invX big_distrl /= revp_sum (big_mkord predT) /= rmorph_sum.
apply: eq_bigr => [ [ i i_lt_size_p ] ] _ /=.
rewrite /Xinv mul_fracpolyC -mulrA ; congr (_ * _).
rewrite mul1r exprVn mulrC -exprB ; last 2 first.
+ move: pneq0 ; rewrite -size_poly_gt0 => size_p_gt0.
  by rewrite -(leq_add2r 1) !addn1 prednK.
+ by rewrite unitfE tofrac_eq0 polyX_eq0.
rewrite -rmorphX ; apply/eqP.
by rewrite tofrac_eq.
Qed.

Lemma fracpoly_iota_p (p : {poly K}) : (p%:F ~~i) = (p ^iota)%:F.
Proof. by rewrite /fracpoly_iota /= f_eval_frac /tofrac_iota /=. Qed.

Lemma fracpoly_iota_X : ('X%:F ~~i) = 'X%:F.
Proof. by rewrite fracpoly_iota_p map_polyX. Qed.

Lemma fracpoly_iota_Xinv : (Xinv K) ~~i = (Xinv L).
Proof. 
rewrite /Xinv rmorphM rmorph1 !mul1r rmorphV; last first.
  by rewrite GRing.unitfE tofrac_eq0 polyX_eq0.
apply: invr_inj ; rewrite !invrK.
exact: fracpoly_iota_X.
Qed.

Local Notation "a ^` " := (deriv a) (at level 2, format "a ^` ").

Lemma deriv_prod (K' : fieldType) (I : eqType) rI (F : I -> {poly K'}) : 
  (\prod_(i <- rI) (F i)) ^` = \sum_(i <- rI) (F i) ^` 
  * (\prod_(j <- (rem i rI)) (F j)).
Proof.
elim: rI => [ | a l iH ] ; first by rewrite !big_nil ; exact: derivC.
rewrite !big_cons rem_cons derivM iH ; congr (_ + _).
rewrite big_distrr [LHS]/= !big_seq ; apply: eq_big => // i i_in_l. 
rewrite mulrA [X in X * _]mulrC -mulrA ; congr (_ * _).
have [a_eq_i | a_neq_i] := boolP (a == i).
  move/eqP : a_eq_i ->.
  by rewrite /= eqxx (eq_big_perm _ (perm_to_rem i_in_l)) big_cons. 
move/negbTE : a_neq_i => /= ->.
by rewrite big_cons. 
Qed.

Fact in_rem (I : eqType) (rI : seq I) (a b : I) : a \in (rem b rI) -> a \in rI.
Proof. exact: (mem_subseq (rem_subseq _ _)). Qed.

Definition newton (K' : fieldType) (p : {poly K'}) := 
  (revp (deriv p))%:F / (revp p)%:F.

Lemma newton0 (K' : fieldType) : newton (0 : {poly K'}) = 0.
Proof. by rewrite /newton deriv0 revp0 rmorph0 mul0r. Qed. 

Lemma newton_eq (p q: {poly K}): p %= q -> newton p = newton q.
Proof.
move/eqpP => [ [ a b ] /= /andP [ a_neq0 b_neq0 ] ].
move/(congr1 (fun x => a^-1 *: x)).
rewrite !scalerA mulrC divff // scale1r => ->.
rewrite /newton !derivZ !revp_scale -!mul_polyC rmorphM [X in _ / X]rmorphM /=.
rewrite -mulf_div divff ?mul1r //. 
rewrite tofrac_eq0 polyC_eq0 ; apply: mulf_neq0 => //.
by rewrite invr_eq0.
Qed.

Lemma newton_devs_in_pw (K' : fieldType)(p : {poly K'}): devs_in_pw (newton p).
Proof.
have [ -> | p_neq0 ] := eqVneq p 0 ; first by rewrite newton0 devs_in_pw0.
by rewrite devs_in_pw_div_tofrac // coef0_rev lead_coef_eq0.
Qed.

Definition enewton (K' : fieldType) (p : {poly K'}) :=
  ExpansibleFracpoly (newton_devs_in_pw p).

Lemma newton_map_poly (p : {poly K}) : newton (p ^ iota) = (newton p) ~~i.
Proof.
by rewrite /newton fracpoly_iota_div deriv_map !tofrac_iota_tofrac !revp_map.
Qed.

Definition newton_powerseries (K' : fieldType) (m : nat) (p : {poly K'}) := 
  to_powerseries m (newton p).

Lemma map_powerseries_newton_powerseries (p : {poly K}) : 
  map_powerseries iota (newton_powerseries n p) = newton_powerseries n (p ^ iota).
Proof.
by rewrite /newton_powerseries newton_map_poly -map_powerseries_to_powerseries.
Qed.

Lemma newton_powerseries0 (m : nat) : newton_powerseries m (0 : {poly K}) = 0.
Proof. by rewrite /newton_powerseries newton0 to_powerseries0. Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Hint Resolve char_K_is_zero.

Fact aux_revp_p_Xinv (K' : fieldType) (p : {poly K'}) : 
(p%:F) \FPo (Xinv K') = ('X%:F ^- (size p).-1) * (revp p)%:F.
Proof.
have lr: (GRing.lreg ('X%:F ^+ (size p).-1)) => [ t | ].
  by apply/lregP ; rewrite expf_neq0 // tofrac_eq0 polyX_eq0.
apply: lr ; rewrite mulrA divff.
  by rewrite mul1r mulrC revp_p_Xinv.
by rewrite expf_neq0 // tofrac_eq0 polyX_eq0.
Qed.

Fact polyXn_eq0 : forall (K' : fieldType), forall (n' : nat), 0 < n' ->
  (('X : {poly K'}) ^+ n' == 0) = false.
Proof. by move => R n' Hn' ; rewrite expf_eq0 polyX_eq0 Hn'. Qed.

Fact three_cases (K' : fieldType) (p : {poly K'}) : 
                   (p == 0) + {c : K' | p = c%:P & c != 0} + ((size p).-1 > 0).
Proof.
have [ lt_size_p_1 | le_size_p_1 ] := ltnP (size p) 2.
+ left.
  move: (size1_polyC lt_size_p_1) ->.
  have [c_eq0 | c_neq0] := boolP (p`_0 == 0).
- by left ; rewrite polyC_eq0.
- by right ; exists p`_0.
+ by right ; rewrite -(ltn_add2r 1) !addn1 prednK // (ltn_trans (ltnSn _)).
Qed.

Lemma comp_fracpoly_poly_Xinv_eq0 (K' : fieldType) (p : {poly K'}) :
  (p%:F \FPo (Xinv _) == 0) = (p == 0).
Proof.
move: (three_cases p) => [ [ p_eq0 | [c [ p_eq_cst Hc ] ] ] | p_neq_cst ].
+ move/eqP: p_eq0 ->.
  by rewrite rmorph0 comp_fracpoly0 !eqxx.
+ by rewrite p_eq_cst comp_fracpolyC tofrac_eq0 !polyC_eq0.
+ rewrite aux_revp_p_Xinv mulf_eq0 tofrac_eq0 revp_eq0 invr_eq0.
  by rewrite -rmorphX tofrac_eq0 polyXn_eq0 // orFb.
Qed. 

Lemma Xinv_Npole (K' : fieldType) (p : {fracpoly K'}) : 
                               ~ has_pole (ev (Xinv K')) (@lift_fracpoly K' p).
Proof.
have [p_eq0 | p_neq0] := eqVneq p 0 => [ | H_has_pole ].
  by rewrite p_eq0 rmorph0 ; apply Npole0.
move: (comp_fracpoly_eq0 H_has_pole).
move: (fracE p) => [ [ p1 p2 ] /= Hp p2_neq0 ].
rewrite Hp comp_fracpoly_div ; last first.
+ have -> : f_eval (aux_evrepr (Xinv K')) ((lift_fracpoly K') p2%:F) =
  (p2 %:F) \FPo  (Xinv K').
    by rewrite /comp_fracpoly /fracpoly_ev.
  rewrite aux_revp_p_Xinv mulf_neq0 //.
- by rewrite invr_eq0 expf_neq0 // tofrac_eq0 polyX_eq0.
- by rewrite tofrac_eq0 revp_eq0.
+ move/eqP ; rewrite mulf_eq0 invr_eq0 !comp_fracpoly_poly_Xinv_eq0.
  move/negbTE : p2_neq0 ->.
  rewrite orbF ; move/eqP => p1_eq_0.
  by move: p_neq0 ; rewrite Hp p1_eq_0 rmorph0 mul0r eqxx.
Qed. 

Hint Resolve Xinv_Npole.

Lemma to_powerseries_map_poly (p : {fracpoly K}) (m : nat) :
  to_powerseries m p ^ iota = to_powerseries m p~~i.
Proof.
move: (fracpolyE p) => [ [ u v ] /= Hx ] /andP [ v_neq0 coprime_u_v ].
rewrite Hx f_eval_div_frac ; last first.
  rewrite raddf_eq0 // ; exact: tofrac_iota_inj.
have [dev | not_dev] := boolP (devs_in_pw (u%:F / v%:F)) ; last first.
+ have v0_neq0 : ~~ (v`_0 != 0).
- by move: not_dev ; rewrite -horner_coef0 devs_in_pwE.
  have not_devi: ~~ devs_in_pw (u~i / v~i).
- rewrite devs_in_pwE.
  -- by rewrite -{1}(rmorph0 iota) horner_map fmorph_eq0 horner_coef0.
  -- by rewrite map_poly_eq0.
  -- by rewrite coprimep_map.
  rewrite /to_powerseries.
  move/negbTE : not_dev -> ; move/negbTE : not_devi ->.
  exact: rmorph0.
+ have v0_neq0 : v`_0 != 0 by move: dev ; rewrite -horner_coef0 devs_in_pwE.
  rewrite to_powerseries_coprimep // to_powerseries_coprimep ; last 2 first.
- rewrite -horner_coef0 -{1}(rmorph0 iota).
  by rewrite horner_map fmorph_eq0 horner_coef0.
- by rewrite coprimep_map.
  rewrite !truncate_map_poly.
  have -> : 
  map_powerseries iota (truncate m u) / map_powerseries iota (truncate m v)
  = map_powerseries iota ((truncate m u) / (truncate m v)).
- by rewrite rmorph_div // truncate_is_unit.
  by [].
Qed.

Lemma poly_poly (R : ringType) (E : nat -> R) (m1 m2 : nat) :
  \poly_(j < m1) (\poly_(k < m2) E k)`_j = \poly_(j < minn m1 m2 ) E j.
Proof.
apply/polyP => j.
rewrite !coef_poly.
have [ j_lt_min | min_leq_j ] := ltnP j (minn m1 m2).
+ rewrite leq_min in j_lt_min.
  by move/andP : j_lt_min => [-> ->].
+ rewrite geq_min leqNgt [X in _ || X]leqNgt in min_leq_j.
  move/orP : min_leq_j => [ /negbTE -> | /negbTE -> ] //.
  by case: (_ < _).
Qed.

(* Lemma geometric_series (a : K) (m : nat) :
  to_powerseries m (((1-a *: 'X)%:F) ^-1) 
  = powerseries_of_poly (\poly_(j < m.+1) (a ^+ j)) (leqnn _). *)
Lemma geometric_series (K' : fieldType) (a : K') (m : nat) :
  to_powerseries m (((1-a *: 'X)%:F) ^-1) = truncate m (\poly_(j < m.+1) (a ^+ j)).
Proof.
have dev: devs_in_pw (1 - a *: 'X)%:F^-1 by exact: devs_in_pw_inv_1_sub_CX.
rewrite to_powerseries_inv_tofrac ; last first.
  by rewrite -horner_coef0 one_sub_CX_0_eq_1 oner_neq0.
have Hunit: (truncate m (1 - a *: 'X)) \is a GRing.unit.
  by rewrite truncate_is_unit -horner_coef0 one_sub_CX_0_eq_1 oner_neq0.
apply: (mulrI Hunit) ; rewrite divrr ; last first.
  by rewrite truncate_is_unit -horner_coef0 one_sub_CX_0_eq_1 oner_neq0.
rewrite -rmorphM /= ; apply: val_inj => /=.
rewrite poly_def -[1 - a *: 'X]opprK opprB mulNr modp_opp.
have -> : \sum_(i < m.+1) a ^+ i *: 'X^i = \sum_(i < m.+1) (a*:'X) ^+i.
  apply: eq_big => // i _.
  by rewrite exprZn.
rewrite -subrX1 modp_add exprZn -mul_polyC modp_mull add0r -modp_opp opprK.
by rewrite modp_small // size_polyXn size_polyC oner_neq0.
Qed.

Lemma geometric_series2 (K' : fieldType) (a : K') (m : nat) :
  to_powerseries m (((1-a *: 'X)%:F) ^-1) = \poly_(j < m.+1) (a ^+ j) :> {poly K'}.
Proof. 
rewrite geometric_series /= modp_small // size_polyXn.
exact: size_poly.
Qed.

Lemma geometric_series3 (K' : fieldType) (a : K') (m : nat) :
  truncation (to_powerseries m (((1-a *: 'X)%:F) ^-1)) = \poly_(j < m.+1) (a ^+ j) :> {poly K'}.
Proof. by rewrite geometric_series2. Qed.

Fact truncate_poly2 (K' : fieldType) (n' m : nat) (E : nat -> K') : n < m ->
   truncate n (\poly_(i < m.+1) E i) = \poly_(i < n.+1) E i :> {poly K'}.
Proof. by move => n_lt_m ; rewrite truncate_poly. Qed.

Fact poly_size_leq (p : {poly K}) (m : nat) : 
  size p <= m -> p = \poly_(i < m) p`_i.
Proof.
move => leq_sizep_m.
by rewrite -{1}(@modp_small _ p ('X ^+ m)) ?size_polyXn // coefK_mod.
Qed.

Fact aux_eq_modp (p q : {poly K}) (m : nat) : size q <= m ->
  p %% 'X ^+m.+1 = q -> p %% 'X ^+m = q.
Proof.
move => leq_sizeq_m.
move/(congr1 (fun x => x %% 'X^m)).
by rewrite modp_modp ?dvdp_exp2l // [X in _ = X]modp_small // size_polyXn.
Qed.

Local Notation "p `d" := (powerderiv p) (at level 2).
Local Notation "c %:S" := (Powerseries (constP n c)) (at level 2).

(* Lemma constP01 : (Powerseries (constP 0 (1 : K))) = 1.
Proof. by apply: val_inj. Qed. *)
(* to replace by constP1*)

Lemma constP1 (m : nat) : (Powerseries (constP m (1 : K))) = 1.
Proof. by apply: val_inj. Qed.

Lemma exponential_cst (m : nat) (c : K) : 
exponential (Powerseries (constP m c)) = (Powerseries (constP m (c == 0)%:R)).
Proof.
have [p0_eq_0 | p0_neq_0] := 
                         boolP ((Powerseries (constP m c)) \in coef0_is_0 K m).
+ rewrite exponential_coef0_is_0 //.
  move: p0_eq_0 ; rewrite inE -horner_coef0 hornerC => /eqP ->.
  apply: val_inj => /=.
  rewrite eqxx /= -(big_mkord predT (fun i => i`!%:R^-1 *: 0%:P ^+ i)).
  rewrite big_ltn // fact0 expr0 invr1 big_nat_cond.
  rewrite (eq_bigr (fun i => 0))=> [ | i /andP [/andP [Hi _] _] ] ; last first.
    by rewrite expr0n eqn0Ngt Hi /= scaler0. 
  rewrite scale1r big1_eq addr0 modp_small //.
  by rewrite size_polyXn size_polyC oner_eq0.
+ rewrite exponential_coef0_isnt_0 //.
  move: p0_neq_0 ; rewrite inE -horner_coef0 hornerC => /negbTE ->.
  by apply: val_inj.
Qed.

Lemma powerderiv_exponential (m : nat) (p : powerseries K m) : 
                    (exponential p)`d = p `d * (truncate m.-1 (exponential p)).
Proof.
move: p ; case: m => [p | m p ].
  by rewrite [p]pw_is_cst powerderivC mul0r exponential_cst powerderivC.
have [p0_eq0 | p0_neq0] := boolP (p \in (coef0_is_0 K m.+1)) ; last first.
  by rewrite exponential_coef0_isnt_0 // powerderiv0 truncate0 mulr0.
rewrite exponential_coef0_is_0 // ; apply: val_inj => /=.
rewrite deriv_modp modp_modp ?dvdp_exp2l //.
rewrite (deriv_sum m.+2 (fun i => i`!%:R^-1 *: truncation p ^+ i)).
rewrite (eq_bigr (fun i => if (nat_of_ord i) == 0%N then 0 
                           else (truncation p)^` * ((nat_of_ord i).-1`!%:R^-1 
           *: truncation p ^+ (nat_of_ord i).-1))) /= => [ | i _] ; last first.
  move: i => [i _] /=.
  case: i => [ | i ] ; first by rewrite eqxx !derivCE scaler0.
  rewrite !derivCE eqn0Ngt ltn0Sn /= -scaler_nat scalerA -scalerCA -scalerAl.
  rewrite factS natrM invrM ?unitfE ?natmul_inj // ; 
                                                last by rewrite -lt0n fact_gt0.
  by rewrite mulrAC -mulrA divff ?natmul_inj -?lt0n ?fact_gt0 // mulr1.
rewrite [X in _ * (modp X _)]big_ord_recr /= modp_add modp_scalel.
rewrite modp_exp_eq0 // ; last by move: p0_eq0 ; rewrite inE => /eqP ->.
rewrite scaler0 addr0 modp_mul.
rewrite -(big_mkord predT (fun i => if i == 0%N then 0 
          else (truncation p)^` * ((i.-1)`!%:R^-1 *: (truncation p) ^+ i.-1))).
rewrite big_ltn // eqxx add0r -[1%N]add0n big_addn.
rewrite subn1 succnK mulr_sumr big_mkord /=.
congr (modp _) ; apply: eq_bigr => [i _].
by rewrite eqn0Ngt addn1 ltn0Sn /=.
Qed.

Lemma powerderiv_logarithm (m : nat) (p : powerseries K m) : 
       p \in (coef0_is_1 K m) -> (logarithm p) `d = (p `d) / (truncate m.-1 p).
Proof.
move: p ; case: m => [ p | m' p p0_is_1 ].
  rewrite inE => /eqP p0_eq_1.
  rewrite [p]pw_is_cst -!horner_coef0 /= powerderivC horner_coef0 p0_eq_1.
  by rewrite constP1 logarithm1 powerderiv0 mul0r.
have p_unit : p \is a GRing.unit.
  by rewrite powerseries_unitE ; apply: coef0_is_1_unit.
have trp_unit : truncate m' p \is a GRing.unit.
  rewrite truncate_is_unit.
  by move: p0_is_1 ; rewrite inE => /eqP -> ; rewrite oner_eq0.
apply: (mulIr trp_unit).
rewrite -mulrA [X in _ =_ * X]mulrC divrr // mulr1 logarithm_coef0_is_1 //.
apply: val_inj => /=.
rewrite deriv_modp derivN deriv_sum_nat modNp modp_summ big_nat_cond.
rewrite (eq_bigr (fun i : nat => (- p ^` * (1 - p) ^+ i.-1) %% 'X^m'.+1))
  => [ | i /andP [ /andP [i_neq0 _] _]] ; last first.
  rewrite lt0n in i_neq0.
  rewrite derivZ deriv_exp derivB derivC sub0r -scaler_nat scalerA mulrC.
  rewrite divff ?natmul_inj // scale1r -truncationN addrC -truncationaddC.
  rewrite addrC truncationexp -modp_mul modp_modp ?dvdp_exp2l // modp_mul.
  by apply: val_inj => /=.
rewrite -big_nat_cond -modp_summ big_distrr_nat /= ?(mulNr, modNp) opprK.
rewrite -[1%N]add0n big_addn mulrC -modp_mul modp_summ.
rewrite (congr_big_nat 0 m'.+1 predT 
      (fun i => truncation (1 - p) ^+ i %% 'X^m'.+1)) //= => [ | i _] ; last first.
  by rewrite addn1 succnK truncationexp modp_modp // dvdp_exp2l.
rewrite /= -modp_summ big_mkord modp_mul.
rewrite -(@modp_small _ (truncation p)^` ('X ^+m'.+1)) ; last first.
  rewrite size_polyXn.
  have H : size (truncation p)^` < size (truncation p).
    apply: lt_size_deriv.
    by apply: p_neq0 ; exists 0 ; rewrite horner_coef0 -powerseries_unitE2.
  by rewrite (leq_trans H) // truncationP.
rewrite modp_mul mulrC modp_mul mulrC mulrCA -modp_mul.
have onesubp : (truncation p) = - ((1  - (truncation p)) -1).
  by rewrite addrAC subrr sub0r opprK.
rewrite [X in X * (bigop _ _ _)]onesubp mulNr -subrX1 modNp.
rewrite modp_add modp_exp_eq0 // ; last first.
  rewrite -horner_coef0 -horner_evalE rmorphB /= !horner_evalE hornerC horner_coef0.
  move: p0_is_1 ; rewrite inE => /eqP ->.
  by rewrite subrr.
by rewrite add0r modNp opprK modp_mul mulr1 modp_mod.
Qed.

Lemma p_cst (p : {poly K}) : p ^` = 0 -> {c : K | p = c %:P}.
Proof.
move/eqP ; rewrite -size_poly_eq0 size_deriv ; last exact: char_K_is_zero.
move/eqP => H_size_p.
exists p`_0 ; apply: size1_polyC.
by rewrite (leq_trans (leqSpred _)) // H_size_p. 
Qed.

Lemma p_eq0 (p : {poly K}) : p ^` = 0 -> {x : K | p.[x] = 0} -> p = 0.
Proof.
move/p_cst => [c ->] [x Hp].
rewrite hornerC in Hp.
by rewrite Hp.
Qed.

Lemma pw_cst (m : nat) (p : powerseries K m) : p `d = 0 -> 
  {c : K | p = (Powerseries (constP m c))}.
Proof.
move/eqP ; rewrite -val_eqE /= => /eqP derivp_eq0.
move: (p_cst derivp_eq0) => [c Hc].
by exists c ; apply: val_inj => /=.
Qed.

Lemma pw_eq0 (m : nat) (p : powerseries K m) : 
                                p `d = 0 -> {x : K | (val p).[x] = 0} -> p = 0.
Proof.
move/eqP ; rewrite -val_eqE /=.
move/eqP => derivp_eq0 H.
apply: val_inj => //=.
by apply: p_eq0.
Qed.

Lemma pw_eq (m : nat) (p q : powerseries K m) : 
                   p `d = q `d -> {x : K | (val p).[x] = (val q).[x]} -> p = q.
Proof.
move => H [x Hx].
apply/eqP ; rewrite -subr_eq0 ; apply/eqP.
apply: pw_eq0 ; first by rewrite powerderivB H subrr.
by exists x ; rewrite -horner_evalE rmorphB /= horner_evalE Hx subrr.
Qed.

Lemma cancel_log_exp : 
               {in coef0_is_0 K n, cancel (@exponential K n) (@logarithm K n)}.
Proof.
move => p p0_eq0 /=.
apply/eqP ; rewrite -subr_eq0 ; apply/eqP.
apply: pw_eq0.
+ rewrite powerderivB powerderiv_logarithm ?exponential_coef0_is_1 //. 
  rewrite powerderiv_exponential -mulrA divrr ; last first.
- rewrite powerseries_unitE truncate_is_unit. 
  move: (exponential_coef0_is_1 p0_eq0) ; rewrite inE => /eqP ->.
  exact: oner_neq0.
- by rewrite mulr1 subrr.
+ exists 0.
  rewrite -horner_evalE rmorphB /= !horner_evalE !horner_coef0. 
  rewrite coef0_logarithm ; last by rewrite inE coef0_exponential.
  move: p0_eq0 ; rewrite inE => /eqP ->.
  exact: subr0.
Qed.

Lemma exponential_inj : {in coef0_is_0 K n &, injective (@exponential K n)}.
Proof.
move => p q p0_eq0 q0_eq0 /= H.
have : p `d * (truncate n.-1 (exponential p)) = 
                                        q `d * (truncate n.-1 (exponential p)).
  by rewrite {2}H -!powerderiv_exponential H.
move/mulIr => H_deriv.
apply: pw_eq.
+ apply: H_deriv.
  by rewrite truncate_is_unit coef0_exponential // oner_neq0.
+ exists 0 ; rewrite !horner_coef0.
  move: p0_eq0 q0_eq0 ; rewrite /coef0_is_0 !inE => /eqP ->.
  by move => /eqP ->.
Qed.

Lemma logarithm_inj : {in coef0_is_1 K n &, injective (@logarithm K n)}.
Proof.
move => p q p0_eq0 q0_eq0 /= Hlog.
have H: (p/q) `d = 0.
  rewrite powerderivdiv ; last first.
    move: q0_eq0.
    rewrite /coef0_is_0 !inE => /eqP ->.
    exact: oner_neq0.
  have -> : p `d * truncate n.-1 q - truncate n.-1 p * q `d = 0 ; 
    last by rewrite mul0r.
  apply/eqP.
  rewrite subr_eq0 [truncate n.-1 p * q `d]mulrC.
  rewrite -eq_divr ?truncate_is_unit ; last 2 first.
      move: p0_eq0 ; rewrite /coef0_is_0 !inE => /eqP ->.
      exact: oner_neq0.
    move: q0_eq0 ; rewrite /coef0_is_0 !inE => /eqP ->.
    exact: oner_neq0.
  move/(congr1 (@powerderiv K n)) : Hlog.
  by rewrite !powerderiv_logarithm // => ->.
move: (pw_cst H) => [c Hpq].
have Hc : c = 1.
  move: Hpq.
  move/(congr1 (fun x => x * q)).
  rewrite mulrAC -mulrA divrr ; last first.
    rewrite powerseries_unitE.
    by apply: coef0_is_1_unit.
  rewrite mulr1 ; move/val_eqP => /=.
  rewrite modp_small ; last first.
    rewrite mul_polyC size_polyXn.
    apply: (leq_trans (size_scale_leq _ _)).
    exact: truncationP.
  move/eqP.
  move/(congr1 (fun x => x.[0])).
  rewrite !horner_coef0 coef0M.
  move: p0_eq0 ; rewrite /coef0_is_1 inE => /eqP ->.
  move: q0_eq0 ; rewrite /coef0_is_1 inE => /eqP ->.
  by rewrite mulr1 coefC eqxx.
move: Hpq ; rewrite Hc.
move/(congr1 (fun x => x * q)).
rewrite mulrAC -mulrA divrr ; last first.
  rewrite powerseries_unitE.
  by apply: coef0_is_1_unit.
rewrite mulr1.
move/val_eqP => /=.
rewrite mul1r modp_small // ; last first.
  rewrite size_polyXn.
  exact: truncationP.
move/eqP => H2.
by apply: val_inj.
Qed.

Lemma cancel_exp_log : 
               {in coef0_is_1 K n, cancel (@logarithm K n) (@exponential K n)}.
Proof.
move => p p0_eq1 /=.
apply: logarithm_inj => //.
  apply: exponential_coef0_is_1.
  by rewrite /coef0_is_0 inE coef0_logarithm.
rewrite cancel_log_exp //.
by rewrite /coef0_is_0 inE coef0_logarithm.
Qed.

Lemma newton_powerseries_map_iota (p : {poly K}) (m : nat) :
  (newton_powerseries m p) ^ iota = newton_powerseries m (p ^ iota).
Proof. 
by rewrite to_powerseries_map_poly /newton_powerseries newton_map_poly.
Qed.

Lemma newton_powerseries_map_iota2 (p : {poly K}) (m : nat) :
map_powerseries iota (newton_powerseries m p) = newton_powerseries m (p ^ iota).
Proof. 
apply: val_inj => /=.
exact: newton_powerseries_map_iota.
Qed.

End NewtonRepresentation.

Variables (L : closedFieldType) (n : nat).

Section Newton.

Variables (K : fieldType) (iota : {rmorphism K -> L}).

Local Notation "p ^ f" := (map_poly f p).

Definition iroots (p : {poly K}) := roots (p ^ iota).

Lemma iroots0 : iroots 0 = [::].
Proof. by rewrite /iroots rmorph0 roots0. Qed.

Fact factorization (p : {poly K}) : p ^ iota = 
(iota (lead_coef p)) *: \prod_(r <- iroots p) ('X - r%:P).
Proof. by rewrite (roots_factor_theorem_f (p ^ iota)) lead_coef_map. Qed.

Lemma coef0_iroots (p : {poly K}) : iota p`_0 = 
  (iota (lead_coef p)) * (\prod_(r <- iroots p) -r).
Proof.
rewrite -coef_map_id0 ; last exact: rmorph0.
rewrite factorization -horner_coef0 -horner_evalE linearZ /= rmorph_prod.
congr (_ * _) ; apply: eq_bigr => i _.
by rewrite /= horner_evalE hornerXsubC add0r. 
Qed.

Fact irootsP (p : {poly K}) : p != 0 -> iroots p =i root (p ^ iota).
Proof. move => p_neq0 x ; by rewrite /iroots rootsP // map_poly_eq0. Qed.

Local Notation "x =p y"  := (perm_eq x y) (at level 70, no associativity).

Lemma perm_eq_roots (p q : {poly L}) : p %= q -> (roots p) =p (roots q).
Proof.
move/eqpP => [[a b] /= /andP [a_neq0 b_neq0] H].
move: (@perm_eq_roots_mulC L a p a_neq0) ; rewrite perm_eq_sym => Hp.
apply: (perm_eq_trans Hp).
by rewrite H perm_eq_roots_mulC.
Qed.

Lemma perm_eq_iroots (p q : {poly K}) : p %= q -> (iroots p) =p (iroots q).
Proof. move => H ; by apply: perm_eq_roots ; rewrite eqp_map. Qed.

Fact prodXsubC_neq0 (R : ringType) (s : seq R) :
  \prod_(i <- s) ('X - i%:P) != 0.
Proof. apply: monic_neq0 ; exact: monic_prod_XsubC. Qed.

Lemma lead_coef_revp (p : {poly K}) : p`_0 != 0 -> 
  iota (lead_coef (revp p)) = 
  (iota (lead_coef p)) * (\prod_(r <- iroots p) (-r)).
Proof.
move => H ; rewrite -coef0_iroots.
have -> : lead_coef (revp p) = p`_0 ; last by [].
rewrite lead_coef_rev //.
move/leqifP: (size_revp_leqif p) ; rewrite H orbT. 
by move/eqP.
Qed.

Notation "x ~~i"  := (fracpoly_iota iota x) (at level 2, format "x ~~i").
Notation "p \FPo q" := (comp_fracpoly q p) (at level 2, format "p \FPo q").
Notation "x %:FP" := (EvalRatFrac.to_fracpoly x). 
Notation "p ^:FP" := (p ^ (@EvalRatFrac.to_fracpoly _)). 

Lemma comp_p_q (p : {poly K}) (q : {fracpoly K}) : 
  ((p ^iota) %:F) \FPo (q ~~i) 
  = ((iota (lead_coef p))%:FP) * \prod_(r <- iroots p) ((q ~~i) - (r%:FP)). 
Proof.
have [peq0 | pneq0] := boolP (p == 0).
  move/eqP: peq0 => -> /=.
  by rewrite lead_coef0 !rmorph0 comp_fracpoly0 mul0r. 
have p_fact := (factorization p).
rewrite p_fact /comp_fracpoly /= f_eval_frac 
        /fracpoly_ev f_eval_frac /= horner_evalE.
rewrite linearZ_LR /= rmorph_prod hornerZ /= ; congr (_ * _).
rewrite -horner_evalE rmorph_prod.
apply: eq_bigr => i _.
rewrite rmorphB /= map_polyX map_polyC horner_evalE.
exact: hornerXsubC.
Qed.

Lemma size_roots (p : {poly K}) : size (iroots p) = (size p).-1.
Proof. by rewrite /iroots roots_size size_map_iota_p. Qed.

Hint Resolve iota_eq0.

Lemma revp_factorization (p : {poly K}) : ((revp p) ^ iota) = 
    (iota (lead_coef p)) *: (\prod_(r <- iroots p) (1 - r*:'X)).
Proof.
have [p_eq0 | p_neq0] := boolP (p == 0).
  move/eqP : p_eq0 ->.
  by rewrite revp0 lead_coef0 !rmorph0 scale0r.
apply/eqP ; rewrite -tofrac_eq -revp_map ; 
                                          last by move => x ; rewrite iota_eq0.
rewrite -revp_p_Xinv size_map_iota_p -(fracpoly_iota_Xinv iota) comp_p_q /=. 
rewrite -mul_polyC rmorphM /= -mulrA ; apply/eqP ; congr (_ * _).
have -> : 'X%:F ^+ (size p).-1 = \prod_(r <- iroots p) 'X%:F.
  move => t.
  rewrite (big_const_seq 1 (@GRing.mul _) (iroots p) predT 'X%:F).
  have -> : count predT (iroots p) = (size p).-1 
    by rewrite count_predT size_roots. 
  exact: Monoid.iteropE. 
rewrite -big_split /= rmorph_prod.
apply: eq_big => //= i _.
rewrite mulrBl rmorphD /= fracpoly_iota_Xinv /Xinv -mulrA [X in 1 * X]mulrC.
rewrite mulrV ; last by rewrite unitfE tofrac_eq0 polyX_eq0.
by rewrite mul1r rmorphN /= tofrac_scale.
Qed.

Lemma prod_const (R : ringType) (I : Type) (s : seq I) (a : R) :
  \prod_(i <- s) a = a ^+ (size s).
Proof. by rewrite big_const_seq iter_mul count_predT mulr1. Qed.

Lemma prod_cond_const (R : ringType) (I : Type) (s : seq I) (P : pred I) 
  (a : R) : \prod_(i <- s | P i) a = a ^+ (count P s).
Proof. by rewrite -big_filter prod_const size_filter. Qed.

Definition mu (x : L) (p : {poly K}) := polyorder.multiplicity x (p ^ iota).

Lemma revp_factorization2 (p : {poly K}) : ((revp p) ^ iota) = 
  (iota (lead_coef p)) * (-1)^+((size p).-1 - (mu 0 p)) 
  * (\prod_(r <- iroots p | r != 0) r)
  *: (\prod_(r <- iroots p | r != 0) ('X - (r ^-1)%:P)). 
Proof.
rewrite revp_factorization -mulrA -scalerA.
have [-> | p_neq0] := eqVneq p 0 ; first by rewrite lead_coef0 rmorph0 !scale0r.
congr (_ *: _).
rewrite (bigID (fun r => (r == 0)) predT _) /=.
rewrite (eq_bigr (fun r => 1)) => [ | r /eqP -> ] ; 
                                                 last by rewrite scale0r subr0.
rewrite big1_eq mul1r -scalerA -scaler_prod.
have <- : \prod_(i <- iroots p | i != 0) -(1 : L) = 
                                                (-1) ^+ ((size p).-1 - mu 0 p).
  rewrite prod_cond_const ; congr (_ ^+ _).
  rewrite -size_roots -(count_predC (fun x => x == 0)) addnC.
  have -> : mu 0 p = count (eq_op^~ 0) (iroots p).
    rewrite /mu roots_mu ; last by rewrite map_poly_eq0.
    by apply: eq_in_count.
  rewrite -addnBA // subnn addn0.
  by apply: eq_in_count.
rewrite -scaler_prod ; apply: eq_bigr => r Hr.
by rewrite scalerBr scaleN1r opprB -[r *: (r^-1)%:P]mul_polyC -polyC_mul divff.
Qed.

Local Notation "x =p y"  := (perm_eq x y) (at level 70, no associativity).

Lemma zero_in_iroots (p : {poly K}) : p != 0 -> (0 \in (iroots p)) = (root p 0).
Proof.
move => p_neq0.
rewrite rootsP ; last by rewrite map_poly_eq0.
by rewrite (qualifE 0) -{1}[0](rmorph0 iota) horner_map fmorph_eq0.
Qed.

Fact pneq0 (p : {poly K}) : ~~ (root p 0) -> p != 0.
Proof. apply: contra => /eqP -> ; exact: root0. Qed.

Lemma roots_revp (p : {poly K}) : ~~ root p 0 -> 
  iroots (revp p) =p map (GRing.inv) (iroots p).
Proof.
move => zeroNroot.
have p_neq0 : p != 0 by apply: pneq0.
rewrite {1}/iroots revp_factorization2 roots_mulC ; last first.
  apply: mulf_neq0.
    apply: mulf_neq0 ; first by rewrite fmorph_eq0 lead_coef_eq0.
    apply: expf_neq0.
    by rewrite oppr_eq0 oner_eq0.
  rewrite prodf_seq_neq0.
  apply/allP => x.
  by rewrite implybb.
rewrite (eq_bigl (fun r => r^-1 != 0)) => [ | r] ; last by rewrite /= invr_eq0.
rewrite big_seq_cond (eq_bigl (fun x => x \in iroots p)) ; last first.
  move => x /=.
  apply: andb_idr => Hx.
  rewrite invr_eq0 ; apply/negP => /eqP x_eq0.
  rewrite x_eq0 in Hx.
  move: Hx.
  rewrite zero_in_iroots //.
  by move/negbTE : zeroNroot ->.
rewrite -big_seq -(big_map (fun r => r^-1) predT (fun x => ('X - x%:P))).
exact: perm_eq_roots_factors.
Qed.

Lemma deriv_p_over_p (p : {poly K}) : p != 0 -> 
((p ^`())%:F / (p%:F)) ~~i = \sum_(r <- iroots p) (('X - r%:P)%:F) ^-1.
Proof.
move => p_neq0.
have p_fact := (factorization p).
rewrite /fracpoly_iota /= f_eval_div_frac ; last first.
  by rewrite raddf_eq0 // ; exact: tofrac_iota_inj.
rewrite /tofrac_iota /= -deriv_map p_fact derivZ -!mul_polyC !rmorphM /=.
rewrite -mulf_div divff ; 
  last by rewrite tofrac_eq0 polyC_eq0 fmorph_eq0 lead_coef_eq0. 
rewrite mul1r deriv_prod rmorph_sum big_distrl /= !big_seq.
apply: eq_big => // i i_in_roots.
rewrite derivXsubC mul1r.
rewrite [X in _ / X%:F](big_rem i) i_in_roots //=.
rewrite [X in _ / (_ * X)%:F]big_seq_cond.
rewrite (eq_bigl (fun j => j \in rem i (iroots p))) ; last first.
  move => j /=.
  apply: andb_idr.
  exact: in_rem.
rewrite -(big_seq _ _ _ _) rmorphM /= invrM ; last 2 first.
+ by rewrite unitfE tofrac_eq0 polyXsubC_eq0.
+ rewrite unitfE tofrac_eq0 ; exact: prodXsubC_neq0.
rewrite mulrA divff ; last first.
  rewrite tofrac_eq0 ; exact: prodXsubC_neq0.
by rewrite mul1r.
Qed.

Fact roots_C (p : {poly K}) : size p == 1%N -> (iroots p) = [::].
Proof.
move/eqP => H_size_p.
have p_neq0: p != 0 by rewrite -size_poly_gt0 H_size_p.
move/eqP : H_size_p ; rewrite -(size_map_iota_p iota). 
move/(elimTn (closed_rootP (p ^ iota))) => H.
apply/nilP ; rewrite /nilp -all_pred0.
apply/allP => x ; rewrite irootsP //.
apply/implyP ; rewrite implybF.
apply/negP => H2.
have: exists x : L, root (p ^ iota) x by exists x.
exact: H.
Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Hint Resolve Xinv_Npole.

Lemma newton_roots (p : {poly K}) : p != 0 -> (newton p) ~~i = 
  \sum_(r <- iroots p) (1 - r *: 'X)%:F ^-1.
Proof.
move => p_neq0.
have [lt_size_p_1 | le_size_p_1] := ltnP (size p) 2.
+ have size_p_eq1: size p == 1%N
    by apply: n_eq1 ; [by rewrite size_poly_eq0 | by []].
  move: (size1_polyC lt_size_p_1) => {1} ->.
  rewrite /newton derivC revp0 rmorph0 mul0r rmorph0.
  symmetry ; move: (roots_C size_p_eq1) ->.
  by apply: big_nil.
+ rewrite /newton -!revp_p_Xinv size_deriv // -mulf_div.
  have <- : (size p).-2 .+1 = (size p).-1.
    apply: prednK.
    move: le_size_p_1 ; by case: (size p).
  rewrite exprS -pred_Sn invfM [X in _ * (_ * X)]mulrC.
  rewrite [X in _ * X]mulrA divff ; last first.
    apply: expf_neq0.
    by rewrite tofrac_eq0 polyX_eq0.
  have -> : ((p^`() )%:F) \FPo (Xinv K) / (p%:F) \FPo (Xinv K) = 
            ((p^`() %:F) / (p%:F)) \FPo (Xinv K).
    by rewrite comp_fracpolyM // comp_fracpolyV. 
  rewrite rmorphM fracpoly_iota_comp_fracpoly deriv_p_over_p // 
                                                         fracpoly_iota_Xinv.
  have -> : (\sum_(r <- iroots p) ('X - r%:P)%:F^-1) \FPo (Xinv L)
      = \sum_(r <- iroots p) ((('X - r%:P)%:F^-1) \FPo (Xinv L)).
    - apply: big_morph ; first by move => x y ; apply: comp_fracpolyD.
    - exact: comp_fracpoly0.
  rewrite big_distrl /=.
  apply: eq_big => // x _.
  rewrite -inv_comp_fracpoly {2}/Xinv mul1r -invrM ; last 2 first.
  - by rewrite unitfE tofrac_eq0 polyX_eq0.
  - by rewrite unitfE comp_fracpoly_poly_Xinv_eq0 polyXsubC_eq0.
  apply: invr_inj.
  rewrite !invrK rmorphD /= comp_fracpolyD //. 
  rewrite comp_fracpolyX rmorphN /= comp_fracpolyN //.
  rewrite comp_fracpolyC /Xinv /to_fracpoly /= mul1r mulrBr.
  rewrite divff ; last by rewrite tofrac_eq0 polyX_eq0.
  by rewrite mulrC rmorphD rmorphN /= rmorph1 mul_fracpolyC.
Qed.

Lemma newton_powerseries_coef (p : {poly K}) (m : nat) :
  p != 0 ->
  (newton_powerseries m p) ^ iota 
                               = \poly_(j < m.+1) (\sum_(r <- iroots p) r ^+j).
Proof.
move => p0_neq0.
rewrite /newton_powerseries to_powerseries_map_poly newton_roots // poly_def.
have -> : \sum_(i < m.+1) (\sum_(r <- iroots p) r ^+ i) *: 'X^i =
          \sum_(i < m.+1) (\sum_(r <- iroots p) (r ^+ i *: 'X^i)).
  apply: eq_big => // i _.
  by rewrite scaler_suml.
rewrite exchange_big /=.
have -> : \sum_(j0 <- iroots p) \sum_(i < m.+1) j0 ^+ i *: 'X^i
        = \sum_(j0 <- iroots p) (\poly_(i < m.+1) j0 ^+ i).
  apply: eq_bigr => // i _.
  by rewrite poly_def.
have -> : \sum_(r <- iroots p) (1 - r *: 'X)%:F^-1 = 
          \sum_(r <- iroots p)
          (ExpansibleFracpoly (devs_in_pw_inv_1_sub_CX r)) 
                                                  :> {fracpoly L} ; last first.
  rewrite to_powerseries_expanse rmorph_sum /expanse.
  rewrite (big_morph _ (@truncationD L m) (@truncation0 L m)).
  apply: eq_bigr => i _.
  exact: geometric_series2.
rewrite (big_morph (@underlying_fracpoly L) 
                          (@underlying_fracpolyD L) (@underlying_fracpoly0 L)).
by apply: eq_bigr. 
Qed. 

Local Notation "p ^ f" := (map_powerseries f p).

Lemma newton_powerseries_coef2 (p : {poly K}) (m : nat) :
  p != 0 ->
  (newton_powerseries m p) ^ iota =
  Powerseries (size_poly m.+1 (fun j => (\sum_(r <- iroots p) r ^+j))).
Proof.
move => p_neq0.
apply: val_inj => /=.
exact: newton_powerseries_coef.
Qed.

Lemma newton_powerseries_coef0 (p : {poly K}) (m : nat) :
    (newton_powerseries m p)`_0 = ((size p).-1)%:R.
Proof.
have [ -> | p_neq0 ] := eqVneq p 0 ;
  first by rewrite newton_powerseries0 coef0 size_poly0.
move: (newton_powerseries_coef2 m p_neq0).
move/(congr1 (fun x => (truncation x)`_0)).
rewrite coef_map_id0 ; last exact: rmorph0.
rewrite coef_poly -!horner_coef0 /=.
rewrite (eq_bigr (fun x => 1)) => [ | r _] ; last exact: expr0.
rewrite big_const_seq count_predT size_roots iter_add add0r => H.
apply: (fmorph_inj iota).
by rewrite H rmorph_nat.
Qed.

Local Notation "p ^ f" := (map_poly f p).

Definition composed_sum (p q : {poly K}) :=
  if (p == 0) then (q ^ iota) else
  if (q == 0) then (p ^ iota) else
  \prod_(r <- [seq s+t | s <- iroots p, t <- iroots q]) ('X - r%:P).

Lemma composed_sumP (p q : {poly K}) : p != 0 -> q != 0 -> composed_sum p q = 
             \prod_(r <- [seq s+t | s <- iroots p, t <- iroots q]) ('X - r%:P).
Proof.
move/negbTE => p_neq0 /negbTE q_neq0.
by rewrite /composed_sum p_neq0 q_neq0.
Qed.

Lemma composed_sum0p (p : {poly K}) : composed_sum 0 p = (p ^ iota).
Proof. by rewrite /composed_sum eqxx. Qed.

Lemma composed_sump0 (p : {poly K}) : composed_sum p 0 = (p ^ iota).
Proof.
rewrite /composed_sum.
have [ -> | p_neq0] := eqVneq p 0 ; first by rewrite eqxx.
by rewrite (negbTE p_neq0) eqxx.
Qed.

Lemma composed_sum_is_prod (p q : {poly K}) :
  p != 0 -> q != 0 -> composed_sum p q =
  \prod_(r <- [seq s+t | s <- iroots p, t <- iroots q]) ('X - r%:P).
Proof. rewrite /composed_sum ; by move/negbTE -> ; move/negbTE ->. Qed.

Lemma size_composed_sum (p q : {poly K}) : p != 0 -> q != 0 -> 
  (size (composed_sum p q)).-1 = (((size p).-1) * ((size q).-1))%N.
Proof.
move => p_neq0 q_neq0.
by rewrite composed_sumP // size_prod_XsubC size_allpairs !size_roots.
Qed.

Definition composed_product (p q : {poly K}) :=
   if (p == 0) || (q == 0) then 0 else
   \prod_(r <- [seq s*t | s <- iroots p, t <- iroots q]) ('X - r%:P).

Lemma composed_product0p (p : {poly K}) : composed_product 0 p = 0.
Proof. by rewrite /composed_product eqxx. Qed.

Lemma composed_productp0 (p : {poly K}) : composed_product p 0 = 0.
Proof. by rewrite /composed_product eqxx orbT. Qed.

Lemma composed_product_is_prod (p q : {poly K}) :
  p != 0 -> q != 0 ->  composed_product p q =
             \prod_(r <- [seq s*t | s <- iroots p, t <- iroots q]) ('X - r%:P).
Proof. rewrite /composed_product ; by move/negbTE -> ; move/negbTE ->. Qed.

Lemma composed_product_neq0 (p q : {poly K}) :
  p != 0 -> q != 0 -> composed_product p q != 0.
Proof.
move => p_neq0 q_neq0.
rewrite composed_product_is_prod // prodf_seq_neq0.
apply/allP => x _.
by rewrite polyXsubC_eq0.
Qed.

Local Notation "x =p y"  := (perm_eq x y) (at level 70, no associativity).

Fact perm_eq_nil (T : eqType) (s : seq T) : (s =p [::]) = (s == [::]).
Proof.
apply/idP/idP ; last by move/eqP ->.
move => H ; apply/eqP.
by apply: perm_eq_small.
Qed.

Lemma roots_composed_product (p q : {poly K}) :
  roots (composed_product p q) =p [seq s*t | s <- iroots p, t <- iroots q].
Proof.
have [p_eq0 | p_neq0] := eqVneq p 0.
+ rewrite p_eq0 composed_product0p roots0 perm_eq_sym perm_eq_nil.
  by rewrite -size_eq0 size_allpairs iroots0 /= mul0n.
+ have [q_eq0 | q_neq0] := eqVneq q 0.
  rewrite q_eq0 composed_productp0 roots0 perm_eq_sym perm_eq_nil.
  by rewrite -size_eq0 size_allpairs iroots0 /= muln0.
rewrite composed_product_is_prod //.
exact: perm_eq_roots_factors.
Qed.

Lemma roots_composed_sum(p q : {poly K}) :
  p != 0 -> q != 0 ->
  roots (composed_sum p q) =p [seq s+t | s <- iroots p, t <- iroots q].
Proof.
move => p_neq0 q_neq0.
rewrite composed_sum_is_prod // ; exact: perm_eq_roots_factors.
Qed.

End Newton.

Lemma map_poly_idfun (R : ringType) : map_poly (@idfun R) =1 @idfun {poly R}.
Proof. exact: coefK. Qed.

Lemma iroots_idfun (p : {poly L}) : 
  iroots [rmorphism of (@idfun L)] p = roots p.
Proof. by rewrite /iroots map_poly_idfun. Qed.

Section Conversion.

Variable (K : fieldType) (iota : {rmorphism K -> L}).

Local Notation "p ^ f" := (map_powerseries f p).

Lemma map_powerseries_idfun (K' : fieldType) (m : nat) : 
       map_powerseries [rmorphism of (@idfun K')] =1 @idfun (powerseries K' m).
Proof. move => p ; apply: val_inj ; exact: map_poly_idfun. Qed.

Hypothesis char_L_is_zero : [char L] =i pred0.

Hint Resolve char_L_is_zero.

Lemma char_K_is_zero : [char K] =i pred0.
Proof. move => x ; by rewrite -(fmorph_char iota). Qed.

Hint Resolve char_K_is_zero.

Lemma nth_newton_powerseries (p : {poly L}) (m i : nat) : p != 0 ->
  (newton_powerseries m p)`_i = if i < m.+1 then
  (\sum_(r <- iroots [rmorphism of (@idfun L)] p) r ^+i) else 0.
Proof.
move => p_neq0.
have -> : val (newton_powerseries m p) = map_poly [rmorphism of (@idfun L)] 
                                                      (newton_powerseries m p).
  by rewrite map_poly_id.
by rewrite /= newton_powerseries_coef // coef_poly.
Qed.

Local Notation "x =p y"  := (perm_eq x y) (at level 70, no associativity).

Lemma iroots_composed_product (p q : {poly K}) :
   iroots [rmorphism of @idfun L] (composed_product iota p q) 
                         =p [seq s*t | s <- iroots iota p, t <- iroots iota q].
Proof. rewrite iroots_idfun ; exact: roots_composed_product. Qed.

Lemma iroots_composed_sum (p q : {poly K}) : p != 0 -> q != 0 ->
   iroots [rmorphism of @idfun L] (composed_sum iota p q) 
                       =p [seq s + t | s <- iroots iota p, t <- iroots iota q].
Proof.
move => p_neq0 q_neq0.
rewrite iroots_idfun ; exact: roots_composed_sum.
Qed.

Lemma eq_big_allpairs (R : Type) (idx : R) (op : Monoid.com_law idx) 
  (I : eqType) (r1 r2 : seq I) (F : I -> R) (h : I -> I -> I) :
  \big[op/idx]_(k <- [seq h i j | i <- r1, j <-r2]) F k = 
  \big[op/idx]_(i <- r1) (\big[op/idx]_(j <- r2) F (h i j)).
Proof.
elim: r1 ; first by rewrite big_nil ; apply: big_nil.
move => a l iH /=.
by rewrite big_cat iH big_map big_cons.
Qed.
 
Lemma newton_composed_product (p q : {poly K}) :
  let m := ((size p).-1 * (size p).-1)%N in
  newton_powerseries m (composed_product iota p q) =
  (powerhadmul (newton_powerseries m p) (newton_powerseries m q)) ^ iota.
Proof.
rewrite /=.
set m := ((size p).-1 * (size p).-1)%N.
have [p_eq0 | p_neq0 ] := eqVneq p 0.
  rewrite p_eq0 newton_powerseries0 powerhadmul0r rmorph0 composed_product0p.
  exact: newton_powerseries0.
have [q_eq0 | q_neq0 ] := eqVneq q 0.  
  rewrite q_eq0 newton_powerseries0 powerhadmulr0 rmorph0 composed_productp0.
  exact: newton_powerseries0.
have -> : newton_powerseries m (composed_product iota p q) =
    newton_powerseries m (composed_product iota p q) ^ [rmorphism of (@idfun L)]
  by rewrite map_powerseries_idfun.
rewrite map_powerseries_mul !newton_powerseries_coef2 // ; 
                                          last by apply: composed_product_neq0.
apply: val_inj => /=.
rewrite -polyP => i.
rewrite !coef_poly ; case: (i < m.+1) => //.
rewrite (big_distrl _ _ _) /=.
rewrite (eq_big_perm [seq s * t | s <- iroots iota p, t <- iroots iota q])
                                         ; last exact: iroots_composed_product.
rewrite /= eq_big_allpairs /=.
apply: eq_bigr => j _ ; rewrite (big_distrr _ _ _) /=.
apply: eq_bigr => k _ ; rewrite exprMn_comm //.
exact: mulrC.
Qed.

Definition expX (K' : fieldType) (m : nat) := 
  aux_exponential m ('X : {poly K'}).

Lemma expX0 (K' : fieldType) : expX K' 0%N = 1.
Proof.
apply: val_inj => /=.
rewrite /expX /aux_exponential coefX eqxx ; apply: val_inj => /=.
rewrite expr1 big_ord_recr big_ord0 Monoid.simpm /= expr0 fact0 invr1 scale1r.
rewrite modp_small // size_polyC size_polyX.
by apply: (leq_b1 _).
Qed.

Lemma nth_expX (K' : fieldType) (m i : nat) : 
  (expX K' m)`_i = if i < m.+1 then i`!%:R^-1 else 0.
Proof.
rewrite /expX /aux_exponential coefX [(0 == 1)%N]eq_sym eqn0Ngt lt0n /=.
rewrite eqxx /= modp_small ; last first.
  rewrite size_polyXn.
  apply: (leq_trans (size_sum _ predT (fun i0 => 
                              (nat_of_ord i0)`!%:R^-1 *: 'X^(nat_of_ord i0)))).
  apply/bigmax_leqP => j _.
  apply: (leq_trans (size_scale_leq _ _)).
  by rewrite size_polyXn.
by rewrite -(poly_def m.+1 (fun i0 => i0`!%:R^-1)) coef_poly.
Qed.

Lemma map_iota_expX (m : nat) : expX K m ^ iota = expX L m.
Proof.
rewrite /expX /aux_exponential !coefX [(0 == 1)%N]eq_sym eqn0Ngt lt0n !eqxx.
apply: val_inj => /=.
rewrite map_modp map_polyXn rmorph_sum /=.
congr (modp _).
apply: eq_bigr => i _.
rewrite linearZ /= map_polyXn //= rmorphV ; last first.
  rewrite unitfE.
  move/(charf0P K) : char_K_is_zero ->.
  by rewrite -lt0n fact_gt0.
by rewrite rmorph_nat.
Qed.

Lemma powerhadmul_p_expX (K' : fieldType) (m : nat ) (p : powerseries K' m) : 
  powerhadmul p (expX K' m) = 
  Powerseries (size_poly m.+1 (fun i => p`_i / i`!%:R)).
Proof.
apply: val_inj => /=.
apply/polyP => i.
rewrite !coef_poly nth_expX.
by case: (i < m.+1).
Qed.

Definition aux_pwX (K' : fieldType) (m : nat) := 
  if (m == 0%N) then (1 : K')%:P else 'X.

Fact pwX_proof (K' : fieldType) (m : nat) : size (aux_pwX K' m) <= m.+1.
Proof.
rewrite /aux_pwX.
case: m => [|m /=]; first by rewrite eqxx size_polyC leq_b1.
by rewrite size_polyX.
Qed.

Definition pwX (K' : fieldType) (m : nat) := Powerseries (pwX_proof K' m).

Fact pwX2_proof (K' : fieldType) (m : nat) :
  size ('X : {poly K'}) <= m.+2.
Proof. by rewrite size_polyX. Qed.

Definition pwX2 (K' : fieldType) (m : nat) := Powerseries (pwX2_proof K' m).

Fact pwX2_in_coef0_is_0 (K' : fieldType) (m : nat) :
  (pwX2 K' m) \in (coef0_is_0 K' m.+1).
Proof. by rewrite inE coefX. Qed.

Lemma pwX_in_coef0_is_0 (K' : fieldType) (m : nat) : 
  (pwX K' m.+1) \in (coef0_is_0 K' m.+1).
Proof. by rewrite inE coefX. Qed.

Lemma pwXS (K' : fieldType) (m : nat) : (pwX K' m.+1) = (pwX2 K' m).
Proof. by apply: val_inj => /=. Qed.

Lemma aux_newton_composed_sum (K' : fieldType) (f : {rmorphism K' -> L}) (m : nat)
  (s t : seq K') (p : powerseries K' m) : p \in (coef0_is_0 K' m) ->
  \sum_(w <- [seq u + v | u <- s, v <- t]) (exponential (w *: p)) = 
  (\sum_(u <- s) (exponential (u *: p))) 
                               * (\sum_(v <- t) (exponential (v *: p))).
Proof.
move => p0_eq0.
have H : [char K'] =i pred0.
  move => x.
  rewrite -(fmorph_char f).
  by move: x.
rewrite eq_big_allpairs /=.
have -> : \sum_(i <- s) \sum_(j <- t) exponential ((i + j) *: p) =
   \sum_(i <- s) \sum_(j <- t) (exponential (i *: p)) * (exponential (j *: p)).
  apply: eq_bigr => i _.
  apply: eq_bigr => j _.
  rewrite scalerDl exponential_is_morphism // ; rewrite -mulr_algr mulrC.
  apply: (@idealMr _ _ (prime_idealr_zmod (coef0_is_0_pideal K' m)) 
                                            (c0_is_0_keyed K' m) i%:A p) => //.
  apply: (@idealMr _ _ (prime_idealr_zmod (coef0_is_0_pideal K' m)) 
                                            (c0_is_0_keyed K' m) j%:A p) => //.
rewrite exchange_big /= mulr_sumr.
apply: eq_big => // i _.
by  rewrite mulr_suml.
Qed.

Lemma sum_exp_kX (m : nat) (p : {poly L}) : 
  powerhadmul (newton_powerseries m.+1 p) (expX L m.+1) = 
  \sum_(r <- iroots [rmorphism of @idfun L] p) (exponential (r *: (pwX2 L m))).
Proof.
have [ -> | p_neq0] := eqVneq p 0.
  by rewrite newton_powerseries0 powerhadmul0r iroots0 big_nil.
rewrite powerhadmul_p_expX.
apply: val_inj => /=.
rewrite poly_def.
have -> : \sum_(i < m.+2) ((newton_powerseries m.+1 p)`_i / i`!%:R) *: 'X^i =
     \sum_(i < m.+2) ((\sum_(r <- iroots [rmorphism of @idfun L] p) r ^+ i) / i`!%:R) *: 'X^i.
  apply: eq_bigr => i _.
  congr (_ *: _).
  congr (_ / _).
  rewrite nth_newton_powerseries ?ltn_ord //.
have -> : \sum_(i < m.+2)
   ((\sum_(r <- iroots [rmorphism of @idfun L] p) r ^+ i) / i`!%:R) *: 'X^i =
\sum_(i < m.+2)
   ((\sum_(r <- iroots [rmorphism of @idfun L] p) ((r *: 'X) ^+ i) / i`!%:R)).
  apply: eq_bigr => i _.
  have -> : \sum_(r <- iroots [rmorphism of @idfun L] p) ((r *: 'X) ^+ i) / i`!%:R= 
  \sum_(r <- iroots [rmorphism of @idfun L] p) ((r ^+i) *: ('X ^+ i)) / i`!%:R.
    apply: eq_bigr => j _.
    by rewrite exprZn.
  rewrite /= mulr_suml scaler_suml ; apply: eq_bigr => j _.
  rewrite -polyC1 -scaler_nat invrZ ; last 2 first.
      rewrite unitfE.
      move/(charf0P L) : char_L_is_zero ->.
      by rewrite -lt0n fact_gt0.
  rewrite polyC1. 
  by rewrite unitrE divr1.
  rewrite -scalerAr divr1.
  rewrite scalerA.
  by rewrite mulrC.
rewrite exchange_big /=.
rewrite (big_morph (@truncation L m.+1) (@truncationD L m.+1) (@truncation0 L m.+1)).
apply: eq_big => //= i _.
rewrite /aux_exponential.
rewrite coefZ coefX /= mulr0 eqxx.
apply: val_inj => /=.
rewrite modp_small ; last first.
rewrite size_polyXn.
apply: (leq_trans (size_sum _ _ _)) => /=. 
apply/bigmax_leqP => j _.
apply: (leq_trans (size_scale_leq _ _)).
apply: (leq_trans (size_exp_leq _ _)).
have [ -> | i_neq0] := eqVneq i 0.
  by rewrite scale0r size_poly0 /= mul0n.
by rewrite size_scale // size_polyX /= mul1n.
congr (polyseq _).
apply: eq_big => //= j _.
rewrite -scaler_nat invrZ ; last 2 first.
rewrite unitfE.
  move/(charf0P L) : char_L_is_zero ->.
  rewrite -lt0n.
  by rewrite fact_gt0.
  by rewrite unitrE divr1.
by rewrite -scalerCA divr1.
Qed.

Lemma newton_composed_sum (p q : {poly K}) :
  p != 0 -> q != 0 ->
  let m := ((size p).-1 * (size p).-1)%N in
  powerhadmul (newton_powerseries m (composed_sum iota p q)) (expX L m) =
  ((powerhadmul (newton_powerseries m p) (expX K m)) 
                    * (powerhadmul (newton_powerseries m q) (expX K m))) ^ iota.
Proof.
move => p_neq0 q_neq0 /=.
set m := ((size p).-1 * (size p).-1)%N.
case: m => [|m].
  rewrite !expX0.
  apply: val_inj => /=.
  rewrite expr1.
  rewrite map_modp.
  rewrite map_polyX.
  rewrite rmorphM.
  rewrite !poly_def.
  rewrite !big_ord_recr !big_ord0 !Monoid.simpm.
  rewrite !expr0.
  rewrite !coefC.  
  rewrite eqxx.
  rewrite !mulr1. 
  rewrite !(newton_powerseries_coef0 [rmorphism of (@idfun L)]) //.
  rewrite !(newton_powerseries_coef0 iota) //.
  rewrite /=.
  rewrite size_composed_sum //.
  rewrite natrM.
  rewrite !linearZ /=.
  rewrite rmorph1.
  rewrite !rmorph_nat.
  rewrite mulr_algr.
  rewrite scalerA.
  rewrite mulrC.
  rewrite modp_small //.
  rewrite size_polyX.
  apply: (leq_trans (size_scale_leq _ _)).
  rewrite size_polyC.
  exact: leq_b1.
rewrite rmorphM /=.
rewrite !map_powerseries_mul.
rewrite map_iota_expX.
rewrite !newton_powerseries_map_iota2.
rewrite !sum_exp_kX. 
rewrite (eq_big_perm [seq s + t | s <- iroots iota p, t <- iroots iota q]) /= ;
  last exact: iroots_composed_sum.
rewrite !iroots_idfun.
apply: (aux_newton_composed_sum [rmorphism of @idfun L]).
exact: pwX2_in_coef0_is_0.
Qed.

Local Notation "c %:S" := (Powerseries (constP n c)) (at level 2).

Notation "x ~~i"  := (fracpoly_iota iota x) (at level 2, format "x ~~i").
Notation "x %:FP" := (EvalRatFrac.to_fracpoly x). 

Fact deriv_rev_over_rev_dev (p : {poly K}) :
  devs_in_pw ((((revp p) ^`())%:F / ((revp p)%:F)) ~~i).
Proof.
have [-> | p_neq0] := eqVneq p 0.
  by rewrite revp0 deriv0 tofrac0 mul0r rmorph0 devs_in_pw0.
rewrite /=.
rewrite f_eval_div_frac ; last first.
  by rewrite /tofrac_iota /= tofrac_eq0 map_poly_eq0 revp_eq0.
apply: devs_in_pw_div_tofrac.
rewrite -horner_coef0 -{1}[0](rmorph0 iota) horner_map fmorph_eq0 horner_coef0.
by rewrite coef0_rev lead_coef_eq0.
Qed.

Fact deriv_rev_over_rev_dev2 (K' : fieldType) (p : {poly K'}) :
  devs_in_pw (((revp p) ^`())%:F / ((revp p)%:F)).
Proof.
have [-> | p_neq0] := eqVneq p 0.
  by rewrite revp0 deriv0 tofrac0 mul0r devs_in_pw0.
rewrite /=.
apply: devs_in_pw_div_tofrac.
by rewrite coef0_rev lead_coef_eq0.
Qed.

Fact deriv_rev_over_rev_dev_221 (p : {poly K}) :
  ExpansibleFracpoly (deriv_rev_over_rev_dev2 (map_poly iota p)) = 
  ExpansibleFracpoly (deriv_rev_over_rev_dev p).
Proof.
have [-> | p_neq0] := eqVneq p 0.
  rewrite map_poly0.
  apply: val_inj => /=.
  by rewrite !revp0 !deriv0 !rmorph0 !mul0r f_eval_frac rmorph0.
apply: val_inj => /=.
rewrite !revp_map ; last by move => x ; rewrite iota_eq0.
rewrite f_eval_div_frac ; last first.
  by rewrite tofrac_iota_eq0 revp_eq0.
by rewrite deriv_map.
Qed.

Fact devs_in_pw_C_div_1_sub_CX (K' : fieldType) (a b : K') :
  devs_in_pw (a%:FP * (1 - b *: 'X)%:F^-1).
Proof.
apply: devs_in_pwM.
  exact: devs_in_pw_to_fracpoly.
exact: devs_in_pw_inv_1_sub_CX.
Qed.

Fact aux_conversion1 (p : {poly K}) : ~~ (root p 0) ->
   ExpansibleFracpoly (deriv_rev_over_rev_dev p) = 
  - \sum_(i <- iroots iota p)  
  (ExpansibleFracpoly (devs_in_pw_C_div_1_sub_CX i i)).
Proof.
move => zeroNroot.
apply: val_inj => /=.
rewrite deriv_p_over_p ; last first.
  rewrite revp_eq0. 
  by apply: pneq0.
rewrite (eq_big_perm [seq x^-1 | x <- iroots iota p]) ; 
                                                    last by rewrite roots_revp.
rewrite big_map big_seq (eq_bigr (fun r => - (r%:FP * (1 - r *: 'X)%:F^-1))) 
                                                     => [ | r Hr] ; last first.
  rewrite -invf_div ; apply: invr_inj ; rewrite !invrK.
  have r_neq0 : r != 0.
    apply/eqP => r_eq0.
    move: Hr ; rewrite r_eq0.
    rewrite zero_in_iroots ; last by apply: pneq0.
    by apply/negP.
  rewrite invrN invrK -mulNr -tofracN opprB.
  have H : r%:FP != 0 by rewrite tofrac_eq0 polyC_eq0.
  apply: (mulIf H). 
  rewrite mulrAC -mulrA divff // mulr1 /to_fracpoly /= -tofracM.
  apply/eqP ; rewrite tofrac_eq.
  by rewrite mulrBl mulrC mul_polyC -polyC_mul mulrC divff.
rewrite -big_seq sumrN ; congr (- _) ; symmetry.
by apply: big_morph.
Qed.

Fact scalerpws (K' : fieldType) (m : nat) (a : K') (p : powerseries K' m) : 
  (to_powerseries m a%:FP) * p = a *: p.
Proof.
rewrite to_powerseries_tofrac truncateC.
apply: val_inj => /=.
rewrite mul_polyC modp_small // (leq_ltn_trans (size_scale_leq _ _)) //.
rewrite size_polyXn.
exact: truncationP.
Qed.

Fact aux_conversion2 (m : nat) (p : {poly K}) :
  ~~ (root p 0) ->
  expanse m (ExpansibleFracpoly (deriv_rev_over_rev_dev p)) =
  - Powerseries (size_poly m.+1 (fun i => (\sum_(r <- iroots iota p) r ^+i.+1))).
Proof.
move => zeroNroot.
rewrite aux_conversion1 // rmorphN rmorph_sum /=.
apply: val_inj => /=.
rewrite poly_def (eq_bigr (fun i => \sum_(r <- iroots iota p) 
                   r ^+ (nat_of_ord i).+1 *: 'X^(nat_of_ord i))) => [ | i _] ; 
                                                   last by rewrite scaler_suml.
rewrite exchange_big /=.
have -> : truncation
  (\sum_(i <- iroots iota p)
      expanse m
        (ExpansibleFracpoly (devs_in_pw_C_div_1_sub_CX i i))) = 
  \sum_(i <- iroots iota p) (truncation (expanse m
        (ExpansibleFracpoly (devs_in_pw_C_div_1_sub_CX i i)))).
  by apply: big_morph => //.
rewrite -!sumrN ; apply: eq_bigr => i _.
rewrite -to_powerseries_expanse to_powerseriesM ; last 2 first.
  + exact: devs_in_pw_to_fracpoly.
  + exact: devs_in_pw_inv_1_sub_CX.
rewrite geometric_series scalerpws -truncateZ ; congr (- _).
rewrite poly_def scaler_sumr /=.
rewrite (eq_bigr (fun j => i ^+ (nat_of_ord j).+1 *: 'X^(nat_of_ord j)))
                                                      => [ | j _] ; last first.
  by rewrite scalerA -exprS.
rewrite -(poly_def m.+1 (fun j => i ^+ j.+1)).
apply: modp_small ; rewrite size_polyXn.
exact: size_poly.
Qed.
(* TODO : generalize ! *)

Fact aux_conversion3 (p : {poly K}) : 
map_expansible iota (ExpansibleFracpoly (deriv_rev_over_rev_dev2 p)) = 
ExpansibleFracpoly (deriv_rev_over_rev_dev2 (map_poly iota p)).
Proof.
have [ -> | p_neq0] := eqVneq p 0.
  apply: val_inj => /=.
  rewrite !revp0 map_poly0 !deriv0 !rmorph0 mul0r !revp0 deriv0 !rmorph0 mul0r.
  by rewrite f_eval_frac rmorph0.
apply: val_inj => /=.
rewrite f_eval_div_frac ; last by rewrite tofrac_iota_eq0 revp_eq0.
rewrite revp_map ; last by move => x ; rewrite iota_eq0.
by rewrite !deriv_map.
Qed.

End Conversion.

Section MoreConversion.

Variable (K : fieldType) (iota : {rmorphism K -> L}).

Hypothesis char_L_is_zero : [char L] =i pred0.

Hint Resolve char_L_is_zero.
Hint Resolve (char_K_is_zero iota char_L_is_zero).

Local Notation "c %:S" := (Powerseries (constP n.+1 c)) (at level 2).

Fact aux_conversion4 (p : {poly K}) : ~~ root p 0 ->
  expanse n (ExpansibleFracpoly (deriv_rev_over_rev_dev2 p))
  = divX (((size p) .-1)%:R %:S - (newton_powerseries n.+1 p)).
Proof.
move => zeroNroot.
apply: (@map_powerseries_injective _ _ n iota).
rewrite map_powerseries_expanse /=.
rewrite (@map_powerseries_divX K L iota n.+1) rmorphB /=.
rewrite map_powerseriesC map_powerseries_newton_powerseries aux_conversion3.
rewrite deriv_rev_over_rev_dev_221 aux_conversion2 //.
apply: val_inj => /=.
rewrite -newton_powerseries_map_iota newton_powerseries_coef // 
                                                        ; last by apply: pneq0.
rewrite !poly_def.
rewrite -(big_mkord predT (fun i => 
                                  (\sum_(r <- iroots iota p) r ^+ i) *: 'X^i)).
rewrite big_ltn // expr0.
rewrite [\sum_(r <- iroots iota p) r ^+ 0](eq_bigr (fun r => 1)) => [ | r _]; 
  last by rewrite expr0.
rewrite big_const_seq iter_add add0r count_predT size_roots opprD addrA.
rewrite rmorph_nat alg_polyC subrr sub0r big_add1 /=.
rewrite (eq_bigr (fun i => ((\sum_(r <- iroots iota p) r ^+ i.+1) 
                                      *: 'X^i) * 'X)) => [ | i _] ; last first.
  by rewrite exprSr scalerAl.
rewrite -mulr_suml divp_opp mulpK ; last by rewrite polyX_eq0.
by rewrite big_mkord.
Qed.

(*
Definition conversion (p : powerseries K n.+1) := 
exponential (can_powerprim 
                           (char_K_is_zero iota char_L_is_zero) 
                           (divX (((size p) .-1)%:R %:S - p))).
*)

Local Notation "p `d" := (powerderiv p) (at level 2).

Lemma exp_prim_derivp_over_p (m : nat) (p : powerseries K m.+1) :
  p \in (coef0_is_1 K m.+1) ->
  p = exponential (can_powerprim 
                                          (char_K_is_zero iota char_L_is_zero)
                                                    ((p `d) / (truncate m p))).
Proof.
move => p0_eq1.
apply: logarithm_inj => //.
  apply: exponential_coef0_is_1.
  exact: coef0_can_powerprim_is_0.
rewrite cancel_log_exp // ; last first.
  exact: coef0_can_powerprim_is_0.
apply: pw_eq => // ; last first.
  exists 0.
  rewrite !horner_coef0.
  rewrite coef0_logarithm //.
  by rewrite coef0_can_powerprim.
rewrite powerderiv_logarithm //.
by rewrite cancel_powerderiv_powerprim.
Qed.

(*
Definition conversion (p : powerseries K n.+1) := 
exponential (can_powerprim 
                           (char_K_is_zero iota char_L_is_zero) 
                           (divX (((size p) .-1)%:R %:S - p))).
*)

Definition conversion (p : powerseries K n.+1) := 
exponential (can_powerprim 
                           (char_K_is_zero iota char_L_is_zero) 
                           (divX ((p`_0) %:S - p))).

(*
Lemma newton_conversion_lemma (p : {poly K}) : 
  revp p = exponential (can_powerprim 
  (char_K_is_zero iota char_L_is_zero) 
  (divX (((size p) .-1)%:R %:S - (newton_powerseries n.+1 p)))).
*)

Lemma newton_conversion (p : powerseries K n.+1) : 
  ~~ (root p 0) ->
  (val p) \is monic ->
  rev_powerseries p = conversion (newton_powerseries n.+1 p).
Proof.
move => Nrootp0 p_monic.
rewrite /conversion.
rewrite [LHS]exp_prim_derivp_over_p ; last first.
  rewrite /coef0_is_1 inE.
  by rewrite coef0_rev -monicE.
congr (exponential _).
congr (can_powerprim _).
rewrite (newton_powerseries_coef0 iota) //.
rewrite -aux_conversion4 //.
rewrite -to_powerseries_expanse.
rewrite to_powerseries_div_tofrac ; last first.
rewrite coef0_rev.
move/monicP : p_monic ->.
apply: oner_neq0.
apply: val_inj => /=.
by rewrite modp_mul2.
Qed.

End MoreConversion.
