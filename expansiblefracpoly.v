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
Require Import binomial bigop ssralg finalg zmodp matrix mxalgebra polyXY generic_quotient.

From Newtonsums Require Import auxresults fraction truncpowerseries.

Import FracField.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Open Local Scope quotient_scope.

Section ExpansibleFracpoly.

Variable K : fieldType.

Definition fracpoly_of of phant K := {fracpoly K}.
Notation "{ 'fracpoly' K }" := (fracpoly_of (Phant K)).

Definition devs : pred_class := fun f : {fracpoly K} => (~~ (0.-fppole) f).

Lemma devs_invf (p : {poly K}) : p != 0 -> (0.-fppole) p%:F^-1 = (p`_0 == 0).
Proof. by move => p_neq0; rewrite fpoleV -horner_coef0 froot_tofrac. Qed.

Lemma devs_inv1subCX (a : K) : devs (1 - a *: 'X)%:F^-1.
Proof.
rewrite /devs devs_invf ; last first.
+ apply: p_neq0 ; exists 0.
  by rewrite one_sub_CX_0_eq_1 oner_neq0.
+ by rewrite -horner_coef0 one_sub_CX_0_eq_1 oner_neq0.
Qed.

Lemma devs_frac (p q : {poly K}) : (0.-fppole)(p // q) -> q`_0 == 0.
Proof. by move => ppq; rewrite -horner_coef0 -horner_evalE (den_fpole_eq0 ppq). Qed.

Lemma devsD (x y : {fracpoly K}) : devs x -> devs y -> devs (x + y).
Proof.
move: (fracpolyE x) => [[a b] /= Hx] /andP [b_neq0 coprime_a_b].
move: (fracpolyE y) => [[c d] /= Hy] /andP [d_neq0 coprime_c_d].
rewrite Hx Hy addf_div ?raddf_eq0 //; last 2 first.
+ exact: tofrac_inj.
+ exact: tofrac_inj.
rewrite /devs !coprimep_fpole // !horner_coef0 => b0_neq0 d0_neq0.
rewrite -!rmorphM -rmorphD /=.
have: (b * d)`_0 != 0 by rewrite coef0M mulf_neq0 // -horner_coef0.
by apply/contra; apply: devs_frac.
Qed.

Lemma devsM (x y : {fracpoly K}) : devs x -> devs y -> devs (x * y).
Proof.
move: (fracpolyE x) => [[a b] /= Hx] /andP [b_neq0 coprime_a_b].
move: (fracpolyE y) => [[c d] /= Hy] /andP [d_neq0 coprime_c_d].
rewrite Hx Hy mulf_div -!rmorphM /=.
rewrite /devs coprimep_fpole // coprimep_fpole // !horner_coef0 => b0_neq0 d0_neq0.
have: (b * d)`_0 != 0 by rewrite coef0M mulf_neq0 // -horner_coef0.
by apply/contra; apply: devs_frac.
Qed.

Lemma devsN (x : {fracpoly K}) : devs x -> devs (-x).
Proof. by rewrite /devs fpoleN. Qed.

Lemma devsB (x y : {fracpoly K}) : devs x -> devs y -> devs (x - y).
Proof. by move => dx dy; rewrite devsD // devsN. Qed.

Variable n : nat.

Definition Tfpsfp (x : {fracpoly K}) :=
  if (0.-fppole) x then 0
  else let (x1, x2) := projT1 (fracpolyE x) in (Tfpsp n x1) / (Tfpsp n x2).

Lemma Tfpsfp0 : Tfpsfp 0 = 0.
Proof.
rewrite /Tfpsfp ; case: ((0.-fppole) 0) => //=.
move: (fracpolyE (0 : {fracpoly K}))
                                   => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
move/eqP: Hx ; rewrite eq_sym mulf_eq0 invr_eq0 !raddf_eq0; last 2 first.
+ exact: tofrac_inj.
+ exact: tofrac_inj.
move/negbTE: v_neq0 -> ; rewrite orbF => /eqP ->.
by rewrite rmorph0 mul0r.
Qed.

Lemma Tfpsfp_frac (p q : {poly K}) :
     q`_0 != 0 -> Tfpsfp (p // q) = (Tfpsp n p) / (Tfpsp n q).
Proof.
move => q0_neq0 ; rewrite /Tfpsfp.
have -> : (0.-fppole) (p // q) = false.
  apply/negbTE; move: q0_neq0; apply/contra.
  exact: devs_frac.
have q_neq0 : q != 0 by apply: p_neq0; exists 0; rewrite horner_coef0.
move: (fracpolyE (p // q)) => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
have v0_neq0 : v`_0 != 0.
  rewrite -horner_coef0 -(@coprimep_fpole K _ _ _ v_neq0 coprime_u_v) -Hx.
  have -> : (0.-fppole) (p // q) = false.
    apply/negbTE; move: q0_neq0; apply/contra.
    exact: devs_frac.
  by [].
apply/eqP ; rewrite eq_divr ?Tfpsp_is_unit // -!rmorphM.
apply/eqP ; apply: (congr1 _) ; apply/eqP.
apply/eqP/tofrac_inj/eqP.
rewrite !rmorphM /= -eq_divf ?raddf_eq0 //; last 2 first.
+ exact: tofrac_inj.
+ exact: tofrac_inj.
by apply/eqP ; symmetry.
Qed.

Fact Tfpsfp1 : Tfpsfp 1 = 1.
Proof.
rewrite /Tfpsfp.
move: (fracpolyE (1 : {fracpoly K}))=> [[u v] /= Hx] /andP [v_neq0 cop_u_v].
have: exists (c : K), (u == c%:P) && (v == c%:P) && (c != 0).
  move/eqP: Hx ; rewrite eq_sym.
  move/eqP/(congr1 (fun x => x*v%:F)).
  rewrite mul1r mulrAC -mulrA divff ?mulr1; last first.
    by rewrite raddf_eq0 //; apply: tofrac_inj.
  move/tofrac_inj => u_eq_v.  
  move: cop_u_v ; rewrite u_eq_v coprimepp.
  move/size_poly1P => [c c_neq0 v_eq_cP] ; exists c.
  by rewrite c_neq0 andbb andbT v_eq_cP.
move => [c /andP [/andP [/eqP -> /eqP ->] c_neq0]].
by rewrite -tofrac1 fpole_tofrac divrr // Tfpsp_is_unit coefC eqxx.  
Qed.

Lemma Tfpsfp_tofrac (p : {poly K}) : Tfpsfp p %:F = Tfpsp n p.
Proof.
rewrite -[p%:F]divr1 -tofrac1 Tfpsfp_frac.
+ by rewrite tfps1 divr1.
+ by rewrite -horner_coef0 hornerC oner_neq0.
Qed.

Lemma Tfpsfp_inv_tofrac (p : {poly K}) :
                  p`_0 != 0 -> Tfpsfp ((p %:F) ^-1) = (Tfpsp n p) ^-1.
Proof.
move => p0_neq0.
rewrite -[p%:F^-1]mul1r -tofrac1 Tfpsfp_frac //.
  by rewrite tfps1 mul1r.
Qed.

Lemma TfpsfpM : {in devs &, {morph Tfpsfp: x y  / x * y}}.
Proof.
move => x y.
move: (fracpolyE x) => [[a b] /= Hx] /andP [b_neq0 coprime_a_b].
move: (fracpolyE y) => [[c d] /= Hy] /andP [d_neq0 coprime_c_d].
rewrite /devs -!topredE /= Hx Hy !coprimep_fpole // !horner_coef0 => b0_neq0 d0_neq0.
rewrite mulf_div -!rmorphM /= [LHS]Tfpsfp_frac ; last first.
  by rewrite coef0M mulf_neq0.
rewrite !Tfpsfp_frac // !rmorphM /=.
by rewrite mulr_div ?Tfpsp_is_unit.
Qed.

Lemma TfpsfpD : {in devs &, {morph Tfpsfp: x y  / x + y}}.
Proof.
move => x y ; rewrite -!topredE.
move: (fracpolyE x) => [[a b] /= Hx] /andP [b_neq0 coprime_a_b].
move: (fracpolyE y) => [[c d] /= Hy] /andP [d_neq0 coprime_c_d].
rewrite /devs Hx Hy !coprimep_fpole // !horner_coef0 => b0_neq0 d0_neq0.
rewrite addf_div ?raddf_eq0 //; last 2 first.
+ exact: tofrac_inj.
+ exact: tofrac_inj.
rewrite -!rmorphM -rmorphD [LHS]Tfpsfp_frac; last first.
  by rewrite coef0M mulf_neq0.
rewrite rmorphD !rmorphM /= !Tfpsfp_frac //.
by rewrite addr_div ?Tfpsp_is_unit.
Qed.

Lemma TfpsfpN : {in devs, {morph Tfpsfp: x / - x >-> - x}}.
Proof.
move => x ; rewrite -topredE.
move: (fracpolyE x) => [[a b] /= Hx] /andP [b_neq0 coprime_a_b].
rewrite /devs Hx !coprimep_fpole // => b0_neq0.
rewrite -mulNr -rmorphN [LHS]Tfpsfp_frac -?horner_coef0 //.
by rewrite Tfpsfp_frac -?horner_coef0 // rmorphN mulNr.
Qed.

Lemma TfpsfpB : {in devs &, {morph Tfpsfp: x y  / x - y}}.
Proof.
move => x y xd yd.
by rewrite -TfpsfpN // -TfpsfpD // /devs -topredE /= fpoleN.
Qed.

Lemma Tfpsfp_eq0 (u v : {poly K}) : v`_0 = 0 -> coprimep u v ->
  Tfpsfp (u // v) = 0.
Proof.
move => /eqP v0_eq0 coprime_u_v.
have [-> | v_neq0] := eqVneq v 0 ;
                          first by rewrite rmorph0 invr0 mulr0 Tfpsfp0.
by rewrite /Tfpsfp coprimep_fpole // horner_coef0 v0_eq0.
Qed.

Fact devs_subring_closed : GRing.subring_closed devs.
Proof.
split; first by rewrite /devs -topredE /= fpole1.
+ by move => f g; rewrite -!topredE; apply: devsB.
+ by move => f g; rewrite -!topredE; apply: devsM.
Qed.

Fact devs_key : pred_key devs. Proof. by []. Qed.

Canonical devs_keyed := KeyedPred devs_key.
Canonical devs_opprPred := OpprPred devs_subring_closed.
Canonical devs_addrPred := AddrPred devs_subring_closed.
Canonical devs_zmodPred := ZmodPred devs_subring_closed.
Canonical devs_mulrPred := MulrPred devs_subring_closed.
Canonical devs_subringPred := SubringPred devs_subring_closed.

End ExpansibleFracpoly.
