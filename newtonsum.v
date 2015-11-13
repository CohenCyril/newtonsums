(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  some doc here                                                            *)
(*****************************************************************************)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype div tuple finfun.
From mathcomp
Require Import  bigop finset fingroup perm ssralg poly.
From mathcomp
Require Import polydiv mxpoly binomial bigop ssralg finalg zmodp matrix. 
From mathcomp 
Require Import mxalgebra polyXY ring_quotient.
From Newtonsums 
Require Import auxresults fraction polydec revpoly truncpowerseries.
From Newtonsums 
Require Import expansiblefracpoly.

Import FracField.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Open Local Scope quotient_scope.

Section NewtonRepresentation.

Variables (K L : fieldType) (* (n : nat) *) (iota : {injmorphism K -> L}).
  
Hint Resolve tofrac_inj.

Local Notation "p ^ f" := (map_poly f p).

Fact size_map_iota_p (p : {poly K}) : size (p ^ iota) = size p.
Proof. by rewrite size_map_inj_poly // rmorph0. Qed.
(* rewrite size_map_inj_poly //; [exact: fmorph_inj | exact: rmorph0]. *)

Fact lead_coef_map_iota_p (p : {poly K}) : 
  lead_coef (p ^ iota) = iota (lead_coef p).
Proof. by rewrite lead_coef_map_inj // rmorph0. Qed.
(* Proof. rewrite lead_coef_map_inj //; [exact: fmorph_inj| exact: rmorph0]. Qed. *)


(* Definition tofrac_iota := 
         [rmorphism of (@tofrac [idomainType of {poly L}]) \o (map_poly iota)].

Notation "x ~i"  := (tofrac_iota x) (at level 2, format "x ~i"). *)

(* Lemma tofrac_iota_inj : injective tofrac_iota.
Proof.
apply: inj_comp ; first exact: tofrac_inj.
exact: map_poly_inj.
Qed.

Lemma tofrac_iota_eq0 x : (tofrac_iota x == 0) = (x == 0).
Proof. rewrite -(rmorph0 tofrac_iota) ; exact: (inj_eq tofrac_iota_inj). Qed.

Definition tofrac_iota_repr := 
          (fun x => @inl _ (has_pole tofrac_iota x) (frepr tofrac_iota_inj x)).

Definition fracpoly_iota := f_eval_rmorphism tofrac_iota_repr tofrac_iota_inj.

Notation "x ~~i"  := (fracpoly_iota x) (at level 2, format "x ~~i"). *)

Local Notation "p ^ f" := (map_poly f p) : ring_scope.

(* remove both after recompilation *)
Notation "p ^:FP" := (p ^ (@tofracpoly _)) : ring_scope.
Notation "f \FPo g" := (comp_fracpoly f g) : ring_scope.

Local Notation "p ^^ f" := (map_frac f p)  (f at next level, at level 30).
Local Notation "p ^^^ f" := (map_frac (map_poly f) p)
                              (f at next level, at level 30).

(* Tests 
Variables (x : {fracpoly K}) (y : {poly K}) (a : K) (b : {fraction K}).
Check (y ^ iota).
Check (a %:FP).
Check (map_frac iota). 
Check (b ^^ iota).
Check (x ^^^ iota). *)

Lemma devs_fracpoly_iota (x : {fracpoly K}) : 
    (0.-fppole) (x ^^^ iota) = (0.-fppole) x.
Proof. by rewrite -[0](rmorph0 iota); apply: fppole_map. Qed.

Lemma fracpoly_iota_div (p q : {fracpoly K}) : 
    (p / q) ^^^ iota = (p ^^^ iota) / (q ^^^ iota).
Proof. exact: fmorph_div. Qed.

Lemma mapf_Tfpsfp (n : nat) (x : {fracpoly K}) :
    map_tfps iota (Tfpsfp n x) = Tfpsfp n (x ^^^ iota).
Proof.
move: (fracpolyE x) => [ [u v] /= Hx ] /andP [ v_neq0 coprime_u_v ].
rewrite Hx fmorph_div /= !map_fracE /=.
have [ v0_eq0 | v0_neq0 ] := eqVneq v`_0 0; last first.
+ rewrite Tfpsfp_frac // Tfpsfp_frac; last first.
    by rewrite coef_map raddf_eq0 //; apply: fmorph_inj.
+ by rewrite rmorph_div /= ?Tfpsp_is_unit // !truncate_map_poly.
by rewrite !Tfpsfp_eq0 // ?coef_map ?v0_eq0 /= ?rmorph0 // coprimep_map. 
Qed.

Lemma horner_prod_comm (s : seq {poly L}) (x : L) : 
  (\prod_(q <- s) (q)).[x] = \prod_(q <- s) (q.[x]).
Proof. by rewrite -horner_evalE rmorph_prod. Qed.

(* Lemma ev_map (p : {poly K}) (a : K) : ev (iota a) (p ^ iota) = iota (ev a p).
Proof. by rewrite /ev /= !horner_evalE horner_map. Qed.

Lemma fracpoly_ev_map (p : {fracpoly K}) (a : K) :
  fracpoly_ev (iota a) (p ~~i) = iota (fracpoly_ev a p).
Proof.
have [ [ p1 p2 Hp /andP [ p2_neq0 coprime_p1_p2 ] ] ] := fracpolyE p.
rewrite /= in Hp p2_neq0 coprime_p1_p2.
rewrite Hp fmorph_div !map_frac_tofrac /tofrac_iota [LHS]/=.
rewrite !fracpoly_ev_div_coprimep // ; last by rewrite coprimep_map.
by rewrite !fracpoly_ev_frac !ev_map fmorph_div.
Qed.

Lemma evE (K' : fieldType) (a : K') (p : {poly K'}) : ev a p = p.[a].
Proof. by rewrite /ev /= horner_evalE. Qed. *)
Locate "^^^".

(* TODO: is it general enough? *)
Lemma to_fracpoly_map_iota (p : {poly K}) :
  (p ^ iota) ^:FP = (p ^:FP) ^ (map_frac (map_poly iota)).
Proof.
by rewrite -!map_poly_comp; apply: eq_map_poly => x /=; rewrite map_fracpolyC.
Qed.

Lemma fracpoly_iota_comp_fracpoly (p q : {fracpoly K}) :
  (p \FPo q) ^^^ iota = (p ^^^ iota) \FPo (q ^^^ iota).
Proof.
have [ [ p1 p2 -> /= /andP [p2_neq0 coprime_p1_p2 ] ] ] := fracpolyE p.
rewrite fracpoly_iota_div !map_fracE !comp_frac_frac // ?fmorph_div /=;
  last by rewrite coprimep_map.
by rewrite !comp_poly_frac !to_fracpoly_map_iota !horner_map.
Qed.

Lemma deriv_prod (K' : fieldType) (I : eqType) rI (F : I -> {poly K'}) : 
  (\prod_(i <- rI) (F i)) ^`() = \sum_(i <- rI) (F i) ^`() 
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

(* Fact in_rem (I : eqType) (rI : seq I) (a b : I) : 
    a \in (rem b rI) -> a \in rI.
Proof. exact: (mem_subseq (rem_subseq _ _)). Qed. *)

Definition newton (K' : fieldType) (p : {poly K'}) := 
  (revp (deriv p))%:F / (revp p)%:F.

Lemma newtonC (K' : fieldType) (c : K') : newton c%:P = 0.
Proof. by rewrite /newton derivC revp0 rmorph0 mul0r. Qed.

Lemma newton0 (K' : fieldType) : newton (0 : {poly K'}) = 0.
Proof. by rewrite newtonC. Qed.

Lemma newton_eq (p q: {poly K}): p %= q -> newton p = newton q.
Proof.
move/eqpP => [ [ a b ] /= /andP [ a_neq0 b_neq0 ] ].
move/(congr1 (fun x => a^-1 *: x)).
rewrite !scalerA mulrC divff // scale1r => ->.
rewrite /newton !derivZ !revpZ -!mul_polyC rmorphM [X in _ / X]rmorphM /=.
rewrite -mulf_div divff ?mul1r // raddf_eq0; last exact: tofrac_inj.
by rewrite polyC_eq0 mulf_neq0 // invr_eq0.
Qed.

Lemma newton_devs (K' : fieldType) (p : {poly K'}): devs (newton p).
Proof.
have [-> | p_neq0] := eqVneq p 0; first by rewrite newton0 -unfold_in rpred0.
by apply: (contra (@devs_frac _ _ _)); rewrite coef0_revp lead_coef_eq0.
Qed.

Lemma newton_map_poly (p : {poly K}) : newton (p ^ iota) = (newton p) ^^^ iota.
Proof.
by rewrite /newton fracpoly_iota_div deriv_map !map_fracE !revp_map.
Qed.

Definition newton_tfps (K' : fieldType) (m : nat) (p : {poly K'}) := 
  Tfpsfp m (newton p).

(* Lemma map_tfps_newton_tfps (p : {poly K}) : 
  map_tfps iota (newton_tfps n p) = newton_tfps n (p ^ iota).
Proof.
by rewrite /newton_tfps newton_map_poly -mapf_Tfpsfp.
Qed. *)

Lemma newton_tfps0 (m : nat) : newton_tfps m (0 : {poly K}) = 0.
Proof. by rewrite /newton_tfps newton0 Tfpsfp0. Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Hint Resolve char_K_is_zero.

Fact aux_revp_p_Xinv (K' : fieldType) (p : {poly K'}) : 
(p%:F) \FPo 'X^-1 = ('XF ^- (size p).-1) * (revp p)%:F.
Proof.
have lr: (GRing.lreg ('X%:F ^+ (size p).-1)) => [ t | ].
  by apply/lregP ; rewrite expf_neq0 // raddf_eq0 //= polyX_eq0. 
apply: lr ; rewrite mulrA divff; first by rewrite mul1r mulrC -tofrac_revp.
by rewrite expf_neq0 // raddf_eq0 //= polyX_eq0.
Qed.

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

Fact polyXn_eq0 : forall (R : idomainType), forall (n' : nat), 0 < n' ->
  (('X : {poly R}) ^+ n' == 0) = false.
Proof. by move => R n' Hn' ; rewrite expf_eq0 polyX_eq0 Hn'. Qed.

Lemma comp_fracpoly_poly_Xinv_eq0 (K' : fieldType) (p : {poly K'}) :
  (p%:F \FPo 'X^-1 == 0) = (p == 0).
Proof.
move: (three_cases p) => [ [ p_eq0 | [c [ p_eq_cst Hc ] ] ] | p_neq_cst ].
+ move/eqP: p_eq0 ->.
  by rewrite rmorph0 comp_fracpoly0 !eqxx.
+ rewrite p_eq_cst comp_fracpolyC // raddf_eq0 //= ?polyC_eq0 //.
  exact: (inj_comp (@tofrac_inj _) (@polyC_inj _)).
+ rewrite aux_revp_p_Xinv mulf_eq0 raddf_eq0 //= revp_eq0 invr_eq0.
  by rewrite -rmorphX raddf_eq0 //= polyXn_eq0 // orFb.
Qed. 

(* Lemma Xinv_Npole (K' : fieldType) (p : {fracpoly K'}) : 
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
- by rewrite invr_eq0 expf_neq0 // raddf_eq0 polyX_eq0.
- by rewrite raddf_eq0 revp_eq0.
+ move/eqP ; rewrite mulf_eq0 invr_eq0 !comp_fracpoly_poly_Xinv_eq0.
  move/negbTE : p2_neq0 ->.
  rewrite orbF ; move/eqP => p1_eq_0.
  by move: p_neq0 ; rewrite Hp p1_eq_0 rmorph0 mul0r eqxx.
Qed. 

Hint Resolve Xinv_Npole. *)

Lemma map_Tfpsfp (p : {fracpoly K}) (n : nat) :
  Tfpsfp n p ^ iota = Tfpsfp n (p ^^^ iota).
Proof.
move/eqP: (mapf_Tfpsfp n p).
rewrite -val_eqE /= modp_small; last first. 
  by rewrite size_polyXn ltnS size_map_poly size_tfps.
by move => /eqP ->.
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

Section Variable_m.
Variable (m : nat).

Local Open Scope tfps_scope.
Local Notation "c %:S" := (Tfpsp m (c %:P)) (at level 2).

Lemma eq_tfps (K' : fieldType) (s s' : {tfps K' m}) :
  (forall i : 'I_m.+1, s`_i = s'`_i) <-> (s = s').
Proof.
split=> [eq_s|-> //]; apply/val_inj/polyP => i /=.
have [i_small|i_big] := ltnP i m.+1; first by rewrite (eq_s (Ordinal i_small)).
by rewrite -[s]tfps_coefK -[s']tfps_coefK !coef_tfps leqNgt i_big.
Qed.

(* Lemma eq_tfps_of_fun (K' : fieldType) (f g : nat -> K') : *)
(*   (forall i : 'I_m.+1, f i = g i) <-> *)
(*   ([tfps i => f i] = [tfps i => g i] :> {tfps K' m}). *)
(* Proof. *)
(* by rewrite -eq_tfps; split=> H i; have := H i; rewrite !coef_tfps leq_ord. *)
(* Qed. *)


Lemma geometric_series (K' : fieldType) (a : K') :
  Tfpsfp m (((1 - a *: 'X)%:F) ^-1) = [tfps j => a ^+ j].
Proof.
have dev: devs (1 - a *: 'X)%:F^-1. exact: devs_inv1subCX.
rewrite Tfpsfp_inv_tofrac; last first.
  by rewrite -horner_coef0 one_sub_CX_0_eq_1 oner_neq0.
have Hunit: (Tfpsp m (1 - a *: 'X)) \is a GRing.unit.
  by rewrite Tfpsp_is_unit -horner_coef0 one_sub_CX_0_eq_1 oner_neq0.
apply: (mulrI Hunit); rewrite divrr ; last first.
  by rewrite Tfpsp_is_unit -horner_coef0 one_sub_CX_0_eq_1 oner_neq0.
apply/val_inj=> /=; rewrite modp_mul2.
rewrite mulrBl mul1r /=; apply/polyP=> i.
rewrite coef_modXn !poly_def mulr_sumr /=.
rewrite [X in _ - X](eq_bigr (fun i => a ^+ (nat_of_ord i).+1 *: 
                                              'X^(nat_of_ord i).+1)); last first.
  by move=> j _; rewrite -scalerAr -scalerAl scalerA -exprS -exprSr.
rewrite -opprB -sumrB. 
rewrite -(big_mkord predT (fun i => a ^+ i.+1 *: 'X^i.+1 - a ^+ i *: 'X^i)) /=.
rewrite telescope_sumr // opprB coefB !coefZ !expr0 mul1r coefXn.
have [|] := ltnP i m.+1; last by rewrite coefC; case: i.
by rewrite ltn_neqAle => /andP [ /negbTE -> _]; rewrite mulr0 subr0. 
Qed.

(* Lemma geometric_series (K' : fieldType) (a : K') (m : nat) :
  Tfpsfp m (((1-a *: 'X)%:F) ^-1) = Tfpsp m (\poly_(j < m.+1) (a ^+ j)).
Proof.
have dev: devs (1 - a *: 'X)%:F^-1. exact: devs_inv1subCX.
rewrite Tfpsfp_inv_tofrac; last first.
  by rewrite -horner_coef0 one_sub_CX_0_eq_1 oner_neq0.
have Hunit: (Tfpsp m (1 - a *: 'X)) \is a GRing.unit.
  by rewrite Tfpsp_is_unit -horner_coef0 one_sub_CX_0_eq_1 oner_neq0.
apply: (mulrI Hunit) ; rewrite divrr ; last first.
  by rewrite Tfpsp_is_unit -horner_coef0 one_sub_CX_0_eq_1 oner_neq0.
rewrite -rmorphM /= ; apply: val_inj => /=.
rewrite poly_def -[1 - a *: 'X]opprK opprB mulNr modp_opp.
have -> : \sum_(i < m.+1) a ^+ i *: 'X^i = \sum_(i < m.+1) (a*:'X) ^+i.
  apply: eq_big => // i _.
  by rewrite exprZn.
rewrite -subrX1 modp_add exprZn -mul_polyC modp_mull add0r -modp_opp opprK.
by rewrite modp_small // size_polyXn size_polyC oner_neq0.
Qed. *)

(* Lemma geometric_series2 (K' : fieldType) (a : K') :
  Tfpsfp m (((1-a *: 'X)%:F) ^-1) = \poly_(j < m.+1) (a ^+ j) :> {poly K'}.
Proof. 
rewrite geometric_series /= modp_small // size_polyXn.
exact: size_poly.
Qed.

Lemma geometric_series3 (K' : fieldType) (a : K') (m : nat) :
  (Tfpsfp m (((1-a *: 'X)%:F) ^-1)) = \poly_(j < m.+1) (a ^+ j) :> {poly K'}.
Proof. by rewrite geometric_series2. Qed. *)

Fact truncate_poly2 (K' : fieldType) (n n': nat) (E : nat -> K') : n < m ->
   Tfpsp n (\poly_(i < m.+1) E i) = \poly_(i < n.+1) E i :> {poly K'}.
Proof. by move => n_lt_m; rewrite /= poly_modp // ltnW. Qed.

Fact poly_size_leq (p : {poly K}) : 
  size p <= m -> p = \poly_(i < m) p`_i.
Proof.
move => leq_sizep_m.
by rewrite -{1}(@modp_small _ p ('X ^+ m)) ?size_polyXn // poly_coef.
Qed.

Fact aux_eq_modp (p q : {poly K}) : size q <= m ->
  p %% 'X ^+m.+1 = q -> p %% 'X ^+m = q.
Proof.
move => leq_sizeq_m.
move/(congr1 (fun x => x %% 'X^m)).
by rewrite modp_modp ?dvdp_exp2l // [X in _ = X]modp_small // size_polyXn.
Qed.

(* Local Notation "p `d" := (deriv_tfps p) (at level 2). *)
(* Local Notation "c %:S" := (Powerseries (constP n c)) (at level 2). *)

(* Lemma constP01 : (Powerseries (constP 0 (1 : K))) = 1.
Proof. by apply: val_inj. Qed. *)
(* to replace by constP1*)

(* Lemma constP1 (m : nat) : (Powerseries (constP m (1 : K))) = 1.
Proof. by apply: val_inj. Qed. *)

Lemma expC (c : K) : exp (c %:S) = (c == 0)%:R %:S.
Proof.
have [ /pwC_in_coef0_is_0 p0eq0 | p0N0] := boolP (c %:S \in (@coef0_is_0 K m)).
+ rewrite p0eq0 eqxx exp_coef0_is_0 //=; last by rewrite rmorph0 rpred0.
  rewrite mod0p -(big_mkord predT (fun i => i`!%:R^-1 *: 0%:P ^+ i)) /=.
  rewrite big_ltn // fact0 expr0 invr1 big_nat_cond.
  rewrite (eq_bigr (fun i => 0))=> [ | i /andP [/andP [Hi _] _] ] ; last first.
    by rewrite expr0n eqn0Ngt Hi /= scaler0.
  by rewrite scale1r big1_eq addr0.
+ rewrite exp_coef0_isnt_0 //.
  by move/pwC_in_coef0_is_0/eqP/negbTE: p0N0 => ->; rewrite rmorph0.
Qed.

End Variable_m.

Local Notation "f `d" := (deriv_tfps f) (at level 2).

Lemma deriv_exp (m : nat) (p : {tfps K m}) : 
  (exp p)`d = p `d * (Tfpsp m.-1 (exp p)).
Proof.
move: p ; case: m => /= [p | n p]. 
  by rewrite [p]tfps_is_cst deriv_tfpsC mul0r expC deriv_tfpsC.
have [p0_eq0 | p0_neq0] := boolP (p \in (@coef0_is_0 K n.+1)) ; last first.
  by rewrite exp_coef0_isnt_0 // deriv_tfps0 rmorph0 mulr0.
rewrite !exp_coef0_is_0 //= !deriv_tfpsE //=; apply: val_inj => /=.
rewrite deriv_modp modp_modp ?dvdp_exp2l // modp_modp ?dvdp_exp2l //.
rewrite deriv_sum -(big_mkord predT (fun i => i`!%:R^-1 *: _  ^+ i)) /=.
rewrite big_nat_recr //= modp_add modp_scalel.
rewrite modp_exp_eq0 //; last by apply/eqP; rewrite -coef0_is_0E.
rewrite scaler0 addr0 modp_mul modp_mul2 mulr_sumr.
rewrite -(big_mkord predT (fun i => (i`!%:R^-1 *: (val p) ^+ i)^`())) /=.
rewrite big_nat_recl // expr0 linearZ /= derivC scaler0 add0r.
congr (_ %% _); apply: eq_bigr => i _.
rewrite linearZ /= deriv_exp /= -scalerCA -scaler_nat.
rewrite scalerA -scalerAl; congr (_ *: _).
rewrite factS natrM /= invrM ?unitfE ?natmul_inj // -?lt0n ?fact_gt0 //.
rewrite -mulrA [X in _ * X]mulrC.
by rewrite divrr ?unitfE ?natmul_inj // -?lt0n ?fact_gt0 // mulr1.
Qed.

Lemma Tfpsp_modp (m n : nat) (p : {poly K}) : m < n ->
    Tfpsp m (p %% 'X^n) = Tfpsp m p.
Proof. by move=> lt_nm; apply/val_inj=> /=; rewrite modp_modp // dvdp_exp2l. Qed.

Lemma deriv_tfps_exp (m : nat) (f : {tfps K m}) (n : nat) :
    (f ^+ n)`d = f`d * (Tfpsp m.-1 f) ^+ n.-1 *+ n.
Proof.
elim: n => /= [|n IHn]; first by rewrite expr0 mulr0n deriv_tfps1.
rewrite exprS deriv_tfpsM {}IHn (mulrC (_ f)) val_tfps_exp /=.
rewrite mulrC -mulrnAr mulrCA -mulrDr -mulrnAr; congr (_ * _).
rewrite Tfpsp_modp; last by clear f; case: m.
rewrite rmorphX /= mulrnAr -exprS; case: n => /= [|n]; rewrite -?mulrS //.
by rewrite !expr0 mulr0n addr0.
Qed.

(* Lemma expfSn (m : nat) (f : {tfps K m.+1}) : 
    f \in (@coef0_is_0 _ _) -> f ^+ m = 0.
Proof.
move => H.
Set Printing Coercions. idtac.
apply: val_inj => /=.
rewrite val_tfps_exp.
Qed. *)

Lemma deriv_Tfps0p (f : {tfps K 0}) : f `d = 0.
Proof.
rewrite deriv_tfpsE; apply/val_inj => /=.
by rewrite deriv_tfps_size1 ?mod0p // size_tfps.
Qed.

(* Lemma deriv_Tfps0p (p : {poly K}) : (Tfpsp 0 p) `d = 0.
Proof.
rewrite deriv_tfpsE; apply/val_inj => /=.
by rewrite deriv_modp expr0 modp1 mod0p.
Qed. *)

Lemma deriv_log (m : nat) (f : {tfps K m}) : 
       f \in (@coef0_is_1 K m) -> (log f) `d = (f `d) / (Tfpsp m.-1 f).
Proof.
move: f; case: m => [|m]; move => f.
rewrite [f]tfps_is_cst coef0_is_1E nth0_Tfpsp coefC eqxx => /eqP ->.
by rewrite !deriv_Tfps0p mul0r.
move => f0_is_1.
rewrite log_coef0_is_1 // rmorphN rmorph_sum deriv_tfpsN raddf_sum -sumrN. 
rewrite big_nat.
rewrite (eq_bigr (fun i => (f `d) * ((1 - (Tfpsp m f)) ^+ i.-1))) => 
                                                  [|i /andP [hi _]]; last first.
+ rewrite linearZ rmorphX /= deriv_tfpsZ rmorphB rmorph1 deriv_tfps_exp. 
  rewrite deriv_tfpsB.
  rewrite rmorphB rmorph1 deriv_tfps1 sub0r /= Tfpsp_modp // -scaler_nat scalerA. 
  rewrite mulrC divrr ?unitfE ?natmul_inj //-?lt0n // scale1r mulNr opprK.
  congr (_ * _); apply: val_inj => /=.
  by rewrite modp_small // size_polyXn ltnS size_tfps.
+ rewrite -big_nat /= -mulr_sumr big_add1 /= big_mkord; congr (_ * _).
  have trp_unit : Tfpsp m f \is a GRing.unit.
    rewrite Tfpsp_is_unit.
    by move: f0_is_1 ; rewrite coef0_is_1E => /eqP -> ; rewrite oner_eq0.
  apply: (mulrI trp_unit); rewrite divrr //.
  rewrite -[X in X * _]opprK -[X in X * _]add0r -{1}(subrr 1).
  rewrite -addrA -linearB /= -[X in X * _]opprB mulNr -subrX1 opprB /=.
  apply/val_inj => /=.
  rewrite val_tfps_exp modp_exp_eq0 ?subr0 // coefB coef1 eqxx.
  rewrite coef0_is_1E in f0_is_1.
  rewrite nth0_Tfpsp; move/eqP : f0_is_1 ->.
  by rewrite subrr.
Qed.

Lemma p_cst (p : {poly K}) : p ^`() = 0 -> {c : K | p = c %:P}.
Proof.
move/eqP ; rewrite -size_poly_eq0 size_deriv ; last exact: char_K_is_zero.
move/eqP => H_size_p.
exists p`_0 ; apply: size1_polyC.
by rewrite (leq_trans (leqSpred _)) // H_size_p. 
Qed.

Lemma p_eq0 (p : {poly K}) : p ^`() = 0 -> {x : K | p.[x] = 0} -> p = 0.
Proof.
move/p_cst => [c ->] [x Hp].
rewrite hornerC in Hp.
by rewrite Hp.
Qed.

Section Variable_m_2.
Variable (m : nat).

Local Open Scope tfps_scope.
Local Notation "c %:S" := (Tfpsp m (c %:P)) (at level 2).

Lemma pw_cst (f : {tfps K m}) : f `d = 0 -> {c : K | f = c %:S}.
Proof.
move: f; case: m => [f _| n f]; first by rewrite [f]tfps_is_cst; exists (f`_0).
rewrite deriv_tfpsE; move/eqP ; rewrite -val_eqE /= => /eqP. 
rewrite modp_small => [derivp_eq0|]; last first.
+ rewrite size_polyXn.
  have [->|fN0] := eqVneq f 0; first by rewrite linear0 size_poly0.
  by rewrite (leq_trans (lt_size_deriv _)) // size_tfps. 
+ move: (p_cst derivp_eq0) => [c Hc].
  exists c; apply/val_inj => /=.
  rewrite modp_small ?size_polyXn ?size_polyC //.
  by apply: (leq_trans (leq_b1 _)).
Qed.

Lemma pw_eq0 (f : {tfps K m}) : 
    f `d = 0 -> {x : K | (val f).[x] = 0} -> f = 0.
Proof.
rewrite deriv_tfpsE /=; move/eqP ; rewrite -val_eqE /=.
have [-> _ _ // |fN0] := eqVneq f 0. 
rewrite modp_small ?size_polyXn ?(leq_trans (lt_size_deriv _)) ?size_tfps //.
  move/eqP => derivp_eq0; move: (p_cst derivp_eq0) => [c Hc].
  rewrite Hc; move => [x hx]; rewrite hornerC in hx.
  by apply/val_inj => /=; rewrite Hc hx.
by rewrite (leq_trans (size_tfps _)) //; clear fN0 f; case: m => [|n].
Qed.

Lemma pw_eq (f g : {tfps K m}) : 
                   f `d = g `d -> {x : K | (val f).[x] = (val g).[x]} -> f = g.
Proof.
move => H [x Hx].
apply/eqP ; rewrite -subr_eq0 ; apply/eqP.
apply: pw_eq0; first by rewrite deriv_tfpsB H subrr.
by exists x ; rewrite -horner_evalE rmorphB /= horner_evalE Hx subrr.
Qed.

End Variable_m_2.

Variable (m : nat).

Lemma cancel_log_exp : 
    {in @coef0_is_0 K m, cancel (@exp K m) (@log K m)}.
Proof.
move => f f0_eq0 /=.
  apply/eqP ; rewrite -subr_eq0 ; apply/eqP.
  apply: pw_eq0.
- rewrite deriv_tfpsB deriv_log ?exponential_coef0_is_1 // ?exp_coef0_is_1 //.
  rewrite deriv_exp -mulrA divrr ?mulr1 ?subrr // Tfpsp_is_unit coef0_exp //.
  exact: oner_neq0.
- exists 0.
  rewrite -horner_evalE rmorphB /= !horner_evalE !horner_coef0. 
  rewrite coef0_log ; last first. 
    rewrite exp_coef0_is_1 //.
  rewrite coef0_is_0E in f0_eq0.
  by move/eqP: f0_eq0 ->; rewrite subr0.
Qed.

Lemma exp_inj : {in @coef0_is_0 K m &, injective (@exp K m)}.
Proof.
move => p q p0_eq0 q0_eq0 /= H.
have : p `d * (Tfpsp m.-1 (exp p)) = 
                                        q `d * (Tfpsp m.-1 (exp p)).
  by rewrite {2}H -!deriv_exp H.
move/mulIr => H_deriv.
apply: pw_eq.
+ apply: H_deriv.
  by rewrite Tfpsp_is_unit coef0_exp // oner_neq0.
+ exists 0 ; rewrite !horner_coef0.
  by move: p0_eq0 q0_eq0 ; rewrite !coef0_is_0E => /eqP -> /eqP ->.
Qed.

Lemma log_inj : {in @coef0_is_1 K m &, injective (@log K m)}.
Proof.
move => p q p0_eq0 q0_eq0 /= Hlog.
have H: (p/q) `d = 0.
  rewrite deriv_tfpsdiv ; last first.
    move: q0_eq0.
    rewrite coef0_is_1E => /eqP ->.
    exact: oner_neq0.
  have -> : p `d * Tfpsp m.-1 q - Tfpsp m.-1 p * q `d = 0 ; 
    last by rewrite mul0r.
  apply/eqP.
  rewrite subr_eq0 [Tfpsp m.-1 p * q `d]mulrC.
  rewrite -eq_divr ?Tfpsp_is_unit ; last 2 first.
      move: p0_eq0 ; rewrite coef0_is_1E => /eqP ->.
      exact: oner_neq0.
      move: q0_eq0 ; rewrite /coef0_is_1E => /eqP ->.
      exact: oner_neq0.
  move/(congr1 (@deriv_tfps K m)) : Hlog.
  by rewrite !deriv_log // => ->.
move: (pw_cst H) => [c Hpq].
have Hc : c = 1.
  move: Hpq.
  move/(congr1 (fun x => x * q)).
  rewrite mulrAC -mulrA divrr ; last first.
    by apply: coef0_is_1_unit.
  rewrite mulr1 ; move/val_eqP => /=.
  rewrite modp_small ; last first.
    rewrite modp_small ?size_polyC ?size_polyXn; last first.
      by apply: (leq_trans (leq_b1 _)).
    rewrite mul_polyC.
    apply: (leq_trans (size_scale_leq _ _)).
    exact: size_tfps.
  move/eqP.
  move/(congr1 (fun x => x.[0])).
  rewrite !horner_coef0 coef0M.
  move: p0_eq0 ; rewrite coef0_is_1E => /eqP ->.
  move: q0_eq0 ; rewrite coef0_is_1E => /eqP ->.
  rewrite modp_small ?mulr1 ?coefC ?eqxx //.
  by rewrite size_polyC size_polyXn; apply: (leq_trans (leq_b1 _)).
move: Hpq ; rewrite Hc.
move/(congr1 (fun x => x * q)).
rewrite mulrAC -mulrA divrr ; last first.
  by apply: coef0_is_1_unit.
rewrite mulr1.
move/val_eqP => /=.
rewrite modp_mul2.
rewrite mul1r modp_small // ; last first.
  rewrite size_polyXn.
  exact: size_tfps.
move/eqP => H2.
by apply: val_inj.
Qed.

Lemma cancel_exp_log : 
               {in @coef0_is_1 K m, cancel (@log K m) (@exp K m)}.
Proof.
move => p p0_eq1 /=.
apply: log_inj => //.
  apply: exp_coef0_is_1.
  by rewrite coef0_is_0E; apply/eqP; rewrite coef0_log.
by rewrite cancel_log_exp // coef0_is_0E coef0_log.
Qed.

Lemma newton_tfps_map_iota (p : {poly K}) :
  (newton_tfps m p) ^ iota = newton_tfps m (p ^ iota).
Proof. 
by rewrite map_Tfpsfp /newton_tfps newton_map_poly.
Qed.

Lemma newton_tfps_map_iota2 (p : {poly K}) :
map_tfps iota (newton_tfps m p) = newton_tfps m (p ^ iota).
Proof. by apply: val_inj => /=; rewrite newton_tfps_map_iota mod_tfps. Qed.

End NewtonRepresentation.

Variables (L : closedFieldType) (n : nat).

Section Newton.

Variables (K : fieldType) (iota : {injmorphism K -> L}).

Local Notation "p ^ f" := (map_poly f p).
Local Open Scope tfps_scope.

Definition iroots (p : {poly K}) := roots (p ^ iota).

Lemma irootsC c : iroots c%:P = [::].
Proof. by rewrite /iroots map_polyC rootsC. Qed.

Lemma iroots0 : iroots 0 = [::]. Proof. by rewrite irootsC. Qed.

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
rewrite lead_coef_revp.
have [->|pN0] := eqVneq p 0; rewrite ?valp0 //.
rewrite -valp_eq0E // in H.
by move/eqP : H ->.
Qed.

(* Notation "x ~~i"  := (fracpoly_iota iota x) (at level 2, format "x ~~i").
Notation "p \FPo q" := (comp_fracpoly q p) (at level 2, format "p \FPo q").
Notation "x %:FP" := (EvalRatFrac.to_fracpoly x). 
Notation "p ^:FP" := (p ^ (@EvalRatFrac.to_fracpoly _)). *)

(* remove both after recompilation *)
Notation "p ^:FP" := (p ^ (@tofracpoly _)) : ring_scope.
Notation "f \FPo g" := (comp_fracpoly f g) : ring_scope.

Local Notation "p ^^ f" := (map_frac f p)  (f at next level, at level 30).
Local Notation "p ^^^ f" := (map_frac (map_poly f) p)
                              (f at next level, at level 30).

(* Variables (p : {poly K}) (q : {fracpoly K}).
Check ((p ^iota) %:F).
Check (q ^^^ iota). *)

Lemma comp_p_q (p : {poly K}) (q : {fracpoly K}) :  
  ((p ^iota) %:F) \FPo (q ^^^ iota) 
  = ((iota (lead_coef p))%:FP) * \prod_(r <- iroots p) ((q ^^^ iota) - (r%:FP)). 
Proof.
have [peq0 | pneq0] := boolP (p == 0).
  by move/eqP: peq0 => ->; rewrite lead_coef0 !rmorph0 comp_fracpoly0 mul0r. 
have p_fact := (factorization p).
rewrite p_fact /comp_fracpoly map_fracE /= linearZ_LR rmorph_prod /=.
rewrite fpeval_tofrac hornerZ; congr (_ * _).
rewrite -horner_evalE rmorph_prod; apply: eq_bigr => i _.
rewrite rmorphB /= map_polyX map_polyC horner_evalE.
exact: hornerXsubC.
Qed.

Lemma size_roots (p : {poly K}) : size (iroots p) = (size p).-1.
Proof. by rewrite /iroots roots_size size_map_iota_p. Qed.

Lemma revp_factorization (p : {poly K}) : ((revp p) ^ iota) = 
    (iota (lead_coef p)) *: (\prod_(r <- iroots p) (1 - r*:'X)).
Proof.
have [p_eq0 | p_neq0] := boolP (p == 0).
  by move/eqP : p_eq0 ->; rewrite revp0 lead_coef0 !rmorph0 scale0r.
apply/eqP; rewrite -(inj_eq (@tofrac_inj _)) -revp_map tofrac_revp. 
rewrite size_map_iota_p -(map_fracpolyXV iota) comp_p_q /=. 
rewrite -mul_polyC rmorphM /= -mulrA ; apply/eqP ; congr (_ * _).
have -> : 'X%:F ^+ (size p).-1 = \prod_(r <- iroots p) 'X%:F => [t|].
  rewrite (big_const_seq 1 (@GRing.mul _) (iroots p) predT 'X%:F).
  have -> : count predT (iroots p) = (size p).-1 
    by rewrite count_predT size_roots. 
  exact: Monoid.iteropE. 
rewrite -big_split rmorph_prod; apply: eq_big => //= i _.
rewrite mulrBl rmorphD /= map_fracpolyXV mulrC divrr; last first.
  rewrite unitfE raddf_eq0 ?polyX_eq0 //.
  exact: tofrac_inj.
by rewrite rmorphN /= tofrac_scale.
Qed.

Lemma prod_const (R : ringType) (I : Type) (s : seq I) (a : R) :
  \prod_(i <- s) a = a ^+ (size s).
Proof. 
rewrite big_const_seq count_predT.
elim: (size s) => [|m ih] //=. 
by rewrite ih exprS.
Qed.

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
((p ^`())%:F / (p%:F)) ^^^ iota = \sum_(r <- iroots p) (('X - r%:P)%:F) ^-1.
Proof.
move => pN0; rewrite map_frac_frac /= -deriv_map (factorization _) derivZ.
rewrite -!mul_polyC !rmorphM -mulf_div divff; last first.
  rewrite raddf_eq0; last exact: tofrac_inj.
  by rewrite polyC_eq0 fmorph_eq0 lead_coef_eq0. 
rewrite mul1r deriv_prod rmorph_sum big_distrl !big_seq.
apply: eq_big => // i i_in_roots.
rewrite derivXsubC mul1r /= [X in _ / X%:F](big_rem i) i_in_roots //.
rewrite [X in _ / (_ * X)%:F]big_seq_cond.
rewrite (eq_bigl (fun j => j \in rem i (iroots p))) ; last first.
  by move => j; apply: andb_idr; apply: (mem_subseq (rem_subseq _ _)).
rewrite -(big_seq _ _ _ _) rmorphM /= invrM ; last 2 first.
+ rewrite unitfE raddf_eq0; last exact: tofrac_inj.
  by rewrite polyXsubC_eq0.
+ rewrite unitfE raddf_eq0; last exact: tofrac_inj.
  exact: prodXsubC_neq0.
+ rewrite mulrA divff ?mul1r // raddf_eq0 ;last exact: tofrac_inj.
  exact: prodXsubC_neq0.
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

Lemma tofracpolyXV_eq0 (F : fieldType)  (p : {poly F}) : (p%:F \FPo 'X^-1 == 0) = (p == 0).
Proof.
rewrite -revp_eq0 -[RHS](rmorph_eq0 [injmorphism of @tofrac _]) /=.
by rewrite tofrac_revp mulf_eq0 orbC expf_eq0 rmorph_eq0 polyX_eq0 andbF.
Qed.

Lemma fracpolyXV_eq0 (F : fieldType) (f : {fracpoly F}) : (f \FPo 'X^-1 == 0) = (f == 0).
Proof.
have [[p q] /= -> /andP [a_neq0 cpq]] := fracpolyE f.
rewrite comp_frac_frac // !mulf_eq0 !invr_eq0.
by rewrite !tofracpolyXV_eq0 !rmorph_eq0.
Qed.

Lemma nocomp_fracpolyXV (F : fieldType) (f : {fracpoly F}) : nocomp_fracpoly f 'X^-1 = false.
Proof.
have [->|f_neq0]:= eqVneq f 0; first by rewrite nocomp_polyF.
by apply/negP => /comp_fracpoly_dflt; apply/eqP; rewrite fracpolyXV_eq0.
Qed.

Lemma newton_roots (p : {poly K}) : (newton p) ^^^ iota = 
  \sum_(r <- iroots p) (1 - r *: 'X)%:F ^-1.
Proof.
have [p_big|p_small] := ltnP 1 (size p); last first.
  by rewrite [p]size1_polyC // irootsC big_nil newtonC rmorph0.
have p_neq0 : p != 0 by rewrite -size_poly_gt0 (ltn_trans _ p_big).
have pred_sp_gt0 : 0 < (size p).-1 by rewrite -subn1 subn_gt0.
rewrite /newton !tofrac_revp size_deriv // -mulf_div.
have -> : (size p).-1 = (size p).-2.+1 by rewrite prednK.
rewrite -[X in _ * X]invf_div -expfB // subSnn expr1.
rewrite -comp_fracpoly_div ?tofracpolyXV_eq0 //.
rewrite fmorph_div /= fracpoly_iota_comp_fracpoly.
rewrite fmorphV /= !map_fracE /= map_polyX deriv_p_over_p //.
rewrite (@big_morph _ _ (fun x => x \FPo 'X^-1) 0 +%R); first last.
- by rewrite comp_fracpoly0.
- by move=> f g /=; rewrite comp_fracpolyD ?nocomp_fracpolyXV.
rewrite mulr_suml; apply: eq_bigr => i _; rewrite comp_fracpolyV -invfM.
rewrite comp_poly_frac !rmorphB /= map_polyX map_polyC /= hornerXsubC.
by rewrite mulrDl mulVf ?rmorph_eq0 ?polyX_eq0 // mulNr -mul_polyC rmorphM.
Qed.


Local Notation "p ^ f" := (map_tfps f p).

Lemma iota_newton_tfps (p : {poly K}) (m : nat) :
  newton_tfps m p ^ iota = [tfps j => \sum_(r <- iroots p) r ^+ j].
Proof.
apply/eq_tfps => i /=; rewrite coef_modXn ltn_ord coef_tfps leq_ord.
rewrite /newton_tfps map_Tfpsfp newton_roots.
elim: iroots=> [|r s ihs]; first by rewrite !big_nil Tfpsfp0 coef0.
rewrite !big_cons TfpsfpD /=; first last. 
- by rewrite rpred_sum // => x _; rewrite -?topredE /= ?devs_inv1subCX.
- by rewrite -?topredE /= ?devs_inv1subCX.
by rewrite geometric_series coefD coef_tfps leq_ord ihs.
Qed.

Lemma map_poly_tfps m (s : {tfps K m}) :
  map_poly iota (val s) = val (s ^ iota).
Proof.
by rewrite /= modp_small // size_polyXn ltnS size_map_poly size_tfps.
Qed.

Lemma newton_tfps_coef0 (p : {poly K}) (m : nat) :
    (newton_tfps m p)`_0 = ((size p).-1)%:R.
Proof.
apply: (@rmorph_inj _ _ iota).
rewrite -coef_map map_poly_tfps iota_newton_tfps coef_tfps /=.
rewrite rmorph_nat -size_roots -sum1_size natr_sum.
by apply: eq_bigr => r; rewrite expr0.
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

Lemma idfun_injective A : injective (@idfun A). Proof. done. Qed.
Canonical idfun_is_injmorphism (A : ringType) := InjMorphism (@idfun_injective A).

Lemma iroots_idfun (p : {poly L}) : 
  iroots [injmorphism of (@idfun L)] p = roots p.
Proof. by rewrite /iroots map_poly_idfun. Qed.

Section Conversion.

Variable (K : fieldType) (iota : {injmorphism K -> L}).

Local Notation "p ^ f" := (map_tfps f p).

Lemma map_powerseries_idfun (K' : fieldType) (m : nat) : 
       map_tfps [injmorphism of (@idfun K')] =1 @idfun {tfps K' m}.
Proof.
move => p; apply/val_inj => /=; rewrite modp_small ?map_poly_id //.
by rewrite size_polyXn ltnS size_tfps.
Qed.

Hypothesis char_L_is_zero : [char L] =i pred0.

Hint Resolve char_L_is_zero.

Lemma char_K_is_zero : [char K] =i pred0.
Proof. move => x ; by rewrite -(fmorph_char iota). Qed.

Hint Resolve char_K_is_zero.

Lemma nth_newton_tfps (p : {poly L}) (m i : nat) : p != 0 ->
  (newton_tfps m p)`_i = if i < m.+1 then
  (\sum_(r <- iroots [injmorphism of (@idfun L)] p) r ^+i) else 0.
Proof.
move => p_neq0.
have -> : val (newton_tfps m p) = map_tfps [rmorphism of (@idfun L)] 
                                                      (newton_tfps m p).
  by rewrite -map_poly_tfps map_poly_id.
by rewrite iota_newton_tfps //= coef_poly.
Qed.

Local Notation "x =p y"  := (perm_eq x y) (at level 70, no associativity).

Lemma iroots_composed_product (p q : {poly K}) :
   iroots [injmorphism of @idfun L] (composed_product iota p q) 
                         =p [seq s*t | s <- iroots iota p, t <- iroots iota q].
Proof. rewrite iroots_idfun ; exact: roots_composed_product. Qed.

Lemma iroots_composed_sum (p q : {poly K}) : p != 0 -> q != 0 ->
   iroots [injmorphism of @idfun L] (composed_sum iota p q) 
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
  newton_tfps m (composed_product iota p q) =
  (hmul_tfps (newton_tfps m p) (newton_tfps m q)) ^ iota.
Proof.
rewrite /=.
set m := ((size p).-1 * (size p).-1)%N.
have [p_eq0 | p_neq0 ] := eqVneq p 0.
  rewrite p_eq0 newton_tfps0 hmul_tfps0r rmorph0 composed_product0p.
  exact: newton_tfps0.
have [q_eq0 | q_neq0 ] := eqVneq q 0.  
  rewrite q_eq0 newton_tfps0 hmul_tfpsr0 rmorph0 composed_productp0.
  exact: newton_tfps0.
have -> : newton_tfps m (composed_product iota p q) =
    newton_tfps m (composed_product iota p q) ^ [rmorphism of (@idfun L)]
  by rewrite map_powerseries_idfun.
rewrite map_tfps_mul !iota_newton_tfps //; apply/eq_tfps => i /=.
rewrite !coef_poly ltn_ord.
rewrite (big_distrl _ _ _) /=.
rewrite (eq_big_perm [seq s * t | s <- iroots iota p, t <- iroots iota q])
                                         ; last exact: iroots_composed_product.
rewrite /= eq_big_allpairs /=.
apply: eq_bigr => j _ ; rewrite (big_distrr _ _ _) /=.
apply: eq_bigr => k _ ; rewrite exprMn_comm //.
exact: mulrC.
Qed.

Definition expX (K' : fieldType) (m : nat) := exp (Tfpsp m ('X : {poly K'})).

Lemma expX0 (K' : fieldType) : expX K' 0%N = 1.
Proof.
rewrite -exp0; congr exp; apply/eq_tfps => i /=.
by rewrite expr1 modpp.
Qed.

Lemma nth_expX (K' : fieldType) (m i : nat) : 
  (expX K' m)`_i = if i < m.+1 then i`!%:R^-1 else 0.
Proof.
rewrite /expX.
rewrite /exp.
rewrite coef_Tfpsp.
rewrite coefX.
rewrite /=.
rewrite eqxx /=.
rewrite coef_modXn.
congr if_expr.
have [->|m_neq0] := eqVneq m O.
rewrite expr1 modpp.
rewrite big_ord_recl /=.
rewrite big_ord0.
rewrite addr0.
rewrite expr0.
rewrite fact0.
rewrite (eq_bigr (fun i => (nat_of_ord i)`!%:R^-1 *: 
                                             'X ^+ (nat_of_ord i))); last first.
move => j _.
congr (_ *: _).
congr (_ ^+ _).
rewrite modp_small // size_polyX size_polyXn //.
rewrite coef_sum.

rewrite nth

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

Lemma hmul_tfps_p_expX (K' : fieldType) (m : nat ) (p : powerseries K' m) : 
  hmul_tfps p (expX K' m) = 
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
  (pwX2 K' m) \in (@coef0_is_0 K' m.+1).
Proof. by rewrite inE coefX. Qed.

Lemma pwX_in_coef0_is_0 (K' : fieldType) (m : nat) : 
  (pwX K' m.+1) \in (@coef0_is_0 K' m.+1).
Proof. by rewrite inE coefX. Qed.

Lemma pwXS (K' : fieldType) (m : nat) : (pwX K' m.+1) = (pwX2 K' m).
Proof. by apply: val_inj => /=. Qed.

Lemma aux_newton_composed_sum (K' : fieldType) (f : {rmorphism K' -> L}) (m : nat)
  (s t : seq K') (p : powerseries K' m) : p \in (@coef0_is_0 K' m) ->
  \sum_(w <- [seq u + v | u <- s, v <- t]) (exp (w *: p)) = 
  (\sum_(u <- s) (exp (u *: p))) 
                               * (\sum_(v <- t) (exp (v *: p))).
Proof.
move => p0_eq0.
have H : [char K'] =i pred0.
  move => x.
  rewrite -(fmorph_char f).
  by move: x.
rewrite eq_big_allpairs /=.
have -> : \sum_(i <- s) \sum_(j <- t) exp ((i + j) *: p) =
   \sum_(i <- s) \sum_(j <- t) (exp (i *: p)) * (exp (j *: p)).
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
  hmul_tfps (newton_tfps m.+1 p) (expX L m.+1) = 
  \sum_(r <- iroots [rmorphism of @idfun L] p) (exp (r *: (pwX2 L m))).
Proof.
have [ -> | p_neq0] := eqVneq p 0.
  by rewrite newton_tfps0 hmul_tfps0r iroots0 big_nil.
rewrite hmul_tfps_p_expX.
apply: val_inj => /=.
rewrite poly_def.
have -> : \sum_(i < m.+2) ((newton_tfps m.+1 p)`_i / i`!%:R) *: 'X^i =
     \sum_(i < m.+2) ((\sum_(r <- iroots [rmorphism of @idfun L] p) r ^+ i) / i`!%:R) *: 'X^i.
  apply: eq_bigr => i _.
  congr (_ *: _).
  congr (_ / _).
  rewrite nth_newton_tfps ?ltn_ord //.
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
  hmul_tfps (newton_tfps m (composed_sum iota p q)) (expX L m) =
  ((hmul_tfps (newton_tfps m p) (expX K m)) 
                    * (hmul_tfps (newton_tfps m q) (expX K m))) ^ iota.
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
  rewrite !(newton_tfps_coef0 [rmorphism of (@idfun L)]) //.
  rewrite !(newton_tfps_coef0 iota) //.
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
rewrite !newton_tfps_map_iota2.
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
  devs ((((revp p) ^`())%:F / ((revp p)%:F)) ~~i).
Proof.
have [-> | p_neq0] := eqVneq p 0.
  by rewrite revp0 deriv0 tofrac0 mul0r rmorph0 devs_in_pw0.
rewrite /=.
rewrite f_eval_div_frac ; last first.
  by rewrite /tofrac_iota /= raddf_eq0 map_poly_eq0 revp_eq0.
apply: devs_frac.
rewrite -horner_coef0 -{1}[0](rmorph0 iota) horner_map fmorph_eq0 horner_coef0.
by rewrite coef0_revp lead_coef_eq0.
Qed.

Fact deriv_rev_over_rev_dev2 (K' : fieldType) (p : {poly K'}) :
  devs (((revp p) ^`())%:F / ((revp p)%:F)).
Proof.
have [-> | p_neq0] := eqVneq p 0.
  by rewrite revp0 deriv0 tofrac0 mul0r devs_in_pw0.
rewrite /=.
apply: devs_frac.
by rewrite coef0_revp lead_coef_eq0.
Qed.

Fact deriv_rev_over_rev_dev_221 (p : {poly K}) :
  ExpansibleFracpoly (deriv_rev_over_rev_dev2 (map_poly iota p)) = 
  ExpansibleFracpoly (deriv_rev_over_rev_dev p).
Proof.
have [-> | p_neq0] := eqVneq p 0.
  rewrite map_poly0.
  apply: val_inj => /=.
  by rewrite !revp0 !deriv0 !rmorph0 !mul0r map_fracE rmorph0.
apply: val_inj => /=.
rewrite !revp_map ; last by move => x ; rewrite iota_eq0.
rewrite f_eval_div_frac ; last first.
  by rewrite tofrac_iota_eq0 revp_eq0.
by rewrite deriv_map.
Qed.

Fact devs_in_pw_C_div_1_sub_CX (K' : fieldType) (a b : K') :
  devs (a%:FP * (1 - b *: 'X)%:F^-1).
Proof.
apply: devs_in_pwM.
  exact: devs_in_pw_to_fracpoly.
exact: devs_inv1subCX.
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
  have H : r%:FP != 0 by rewrite raddf_eq0 polyC_eq0.
  apply: (mulIf H). 
  rewrite mulrAC -mulrA divff // mulr1 /to_fracpoly /= -tofracM.
  apply/eqP ; rewrite tofrac_eq.
  by rewrite mulrBl mulrC mul_polyC -polyC_mul mulrC divff.
rewrite -big_seq sumrN ; congr (- _) ; symmetry.
by apply: big_morph.
Qed.

Fact scalerpws (K' : fieldType) (m : nat) (a : K') (p : powerseries K' m) : 
  (Tfpsfp m a%:FP) * p = a *: p.
Proof.
rewrite to_powerseries_tofrac truncateC.
apply: val_inj => /=.
rewrite mul_polyC modp_small // (leq_ltn_trans (size_scale_leq _ _)) //.
rewrite size_polyXn.
exact: size_tfps.
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
  + exact: devs_inv1subCX.
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
  by rewrite map_fracE rmorph0.
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
  = divX (((size p) .-1)%:R %:S - (newton_tfps n.+1 p)).
Proof.
move => zeroNroot.
apply: (@map_powerseries_injective _ _ n iota).
rewrite map_powerseries_expanse /=.
rewrite (@map_powerseries_divX K L iota n.+1) rmorphB /=.
rewrite map_powerseriesC map_powerseries_newton_tfps aux_conversion3.
rewrite deriv_rev_over_rev_dev_221 aux_conversion2 //.
apply: val_inj => /=.
rewrite -newton_tfps_map_iota newton_tfps_coef // 
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

Local Notation "p `d" := (deriv_tfps p) (at level 2).

Lemma exp_prim_derivp_over_p (m : nat) (p : {tfps K m.+1}) :
  p \in (@coef0_is_1 K m.+1) ->
  p = exp (can_powerprim 
                                          (char_K_is_zero iota char_L_is_zero)
                                                    ((p `d) / (Tfpsp m p))).
Proof.
move => p0_eq1.
apply: log_inj => //.
  apply: exp_coef0_is_1.
  exact: coef0_can_powerprim_is_0.
rewrite cancel_log_exp // ; last first.
  exact: coef0_can_powerprim_is_0.
apply: pw_eq => // ; last first.
  exists 0.
  rewrite !horner_coef0.
  rewrite coef0_log //.
  by rewrite coef0_can_powerprim.
rewrite deriv_log //.
by rewrite cancel_powerderiv_powerprim.
Qed.

(*
Definition conversion (p : powerseries K n.+1) := 
exp (can_powerprim 
                           (char_K_is_zero iota char_L_is_zero) 
                           (divX (((size p) .-1)%:R %:S - p))).
*)

Definition conversion (p : powerseries K n.+1) := 
exp (can_powerprim 
                           (char_K_is_zero iota char_L_is_zero) 
                           (divX ((p`_0) %:S - p))).

(*
Lemma newton_conversion_lemma (p : {poly K}) : 
  revp p = exp (can_powerprim 
  (char_K_is_zero iota char_L_is_zero) 
  (divX (((size p) .-1)%:R %:S - (newton_tfps n.+1 p)))).
*)

Lemma newton_conversion (p : powerseries K n.+1) : 
  ~~ (root p 0) ->
  (val p) \is monic ->
  rev_powerseries p = conversion (newton_tfps n.+1 p).
Proof.
move => Nrootp0 p_monic.
rewrite /conversion.
rewrite [LHS]exp_prim_derivp_over_p ; last first.
  rewrite /coef0_is_1 inE.
  by rewrite coef0_revp -monicE.
congr (exp _).
congr (can_powerprim _).
rewrite (newton_tfps_coef0 iota) //.
rewrite -aux_conversion4 //.
rewrite -to_powerseries_expanse.
rewrite to_powerseries_div_tofrac ; last first.
rewrite coef0_revp.
move/monicP : p_monic ->.
apply: oner_neq0.
apply: val_inj => /=.
by rewrite modp_mul2.
Qed.

End MoreConversion.
