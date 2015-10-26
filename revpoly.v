(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  Theory of reverse polynomial and relation to roots and multiplicity.     *)
(*****************************************************************************)

(* From Ssreflect Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From MathComp Require Import div tuple finfun bigop ssralg poly polydiv.
From Newtonsums Require Import auxresults. *)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype div tuple finfun bigop ssralg poly polydiv.
From Newtonsums Require Import auxresults.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Local Notation "p ^ f" := (map_poly f p).


Section RevPoly.

Section MainRevPoly.

Definition revp (R : ringType) (p : {poly R}) := Poly (rev p).

Variable (R : ringType).

Fact last_map_eq0 (R' : ringType) (f : R -> R') (s : seq R) :
  (forall x, (f x == 0) = (x == 0)) ->
  (last 1 [seq f i | i <- s] == 0) = (last 1 s == 0).
Proof. 
move => H.
case/lastP : s => [ | l a ] ; first by rewrite !oner_eq0.
by rewrite last_rcons map_rcons last_rcons (H _).
Qed.

Lemma revp_map (R' : ringType) (f : R -> R') p : 
  (forall x, (f x == 0) = (x == 0)) -> revp (p ^ f) = (revp p) ^ f.
Proof.
move => H.
rewrite map_Poly_id0 ; last by apply/eqP ; rewrite (H _).
rewrite map_rev ; congr (Poly _) ; congr (rev _).
by rewrite map_polyE (@PolyK _ 1 _) // last_map_eq0 // ; case: p.
Qed.

Definition coef0_neq0 := [qualify p : {poly R} | p`_0 != 0].

Lemma revp_involutive : {in coef0_neq0, involutive (@revp R)}.
Proof.
move => p.
rewrite qualifE => p0_neq0.
rewrite /revp (@PolyK _ 0 (rev (polyseq _))).
  by rewrite revK polyseqK.
by rewrite last_rev -nth0.
Qed.

Fact revp_proof (p : {poly R}) : size (revp p) <= size p.
Proof. by rewrite /revp (leq_trans (size_Poly _)) // size_rev. Qed.

Lemma revp0 : @revp R 0 = 0.
Proof. 
apply/eqP ; rewrite -size_poly_leq0.
by apply: (leq_trans (@revp_proof 0)) ; rewrite size_poly0.
Qed.

Variable (p : {poly R}).

Lemma lead_coefMXn (n : nat) : lead_coef (p * 'X ^+ n) = lead_coef p.
Proof.
elim: n => [ | n iH ] ; first by rewrite expr0 mulr1.
by rewrite exprSr mulrA lead_coefMX.
Qed.

Lemma coef_revp (i : nat) : 
  i < size p -> (revp p)`_i = p`_((size p)-(i.+1)).
Proof. move => H; by rewrite /revp coef_Poly nth_rev. Qed.

Fact coef0_rev : (revp p)`_0 = lead_coef p.
Proof. by rewrite coef_Poly nth0 /lead_coef nth_last first_rev. Qed. 

Lemma revp_mulMXn (n : nat) : revp (p * 'X^n) = revp p.
Proof.
have [ -> | P_neq0 ] := eqVneq p 0 ; first by rewrite mul0r.
by rewrite /revp polyseqMXn // rev_ncons poly_nrcons. 
Qed.

Fact leq_size_revp : size (revp p) <= (size p).
Proof. by rewrite /revp (leq_trans (size_Poly _)) // size_rev. Qed.

Lemma revp_indexing : 
                        (revp p) = \poly_(j < size p) p`_(size p - j.+1).
Proof.
apply/polyP ; rewrite /eqfun => j.
rewrite coef_poly.
have [lt_j_s|le_s_j] := ltnP j (size p) ; first by apply: coef_revp.
move/leq_sizeP: leq_size_revp => /(_ j) H.
exact: (H _).
Qed.

Lemma revp_sum : 
             (revp p) = \sum_(j < size p) p`_j *: ('X ^+ ((size p).-1 -j)).
Proof.
rewrite revp_indexing poly_def.
rewrite -(big_mkord predT (fun i => p`_(_ - i.+1) *: 'X^i)).
rewrite -(big_mkord predT (fun j => p`_j *: 'X^(_ - j))).
rewrite big_nat_rev add0n. 
apply: eq_big_nat => //= i i_lt_size_p.
congr (_ *: _) ; last by rewrite subnS -!subn1 -subnDA addnC subnDA.
by rewrite subnS subKn.
Qed.

Lemma revp_eq0 : (revp p == 0) = (p == 0).
Proof.
apply/idP/idP.
  move/eqP => H.
  move: (@coef0 R O).
  by rewrite -{1}H {H} coef0_rev => /eqP ; rewrite lead_coef_eq0.
move/eqP => H ; rewrite -size_poly_leq0.
apply: (leq_trans (revp_proof _)).
by rewrite H size_poly0.
Qed.

Fact lead_coef_rev : 
                   size (revp p) = size p -> lead_coef (revp p) = p`_0.
Proof.
move => H.
have [ -> | p_neq0 ] := eqVneq p 0.
  by rewrite coef0 revp0 lead_coef0.
rewrite /lead_coef H coef_revp ; last by rewrite lt_pred size_poly_eq0.
rewrite prednK ; last by rewrite size_poly_gt0.
by rewrite subnn.
Qed.

Lemma size_revp_leqif : 
  size (revp p) <= size p ?= iff (p == 0) || (p`_0 != 0).
Proof. 
split ; first by rewrite /revp (leq_trans (size_Poly _)) // size_rev.
apply/idP/idP.
+ move/eqP => H.
  move/idP : (orbN (p == 0)). 
  move/orP => [Hp0 | Hpn0] ; first by rewrite Hp0.
  apply/orP ; right.
  move: Hpn0 ; apply: contra => /eqP p0_eq0.
  move: (lead_coef_rev H).
  rewrite p0_eq0 ; move/eqP.
  by rewrite lead_coef_eq0 revp_eq0.
+ move/orP => [ /eqP -> | p0_neq0 ] ; first by rewrite revp0.
  rewrite (@PolyK _ 0 (rev p)) ; first by rewrite size_rev. 
  by rewrite last_rev -nth0.
Qed. 

Lemma size_revp : p`_0 != 0 -> size (revp p) = size p.
Proof.
move => p0_neq0.
move: size_revp_leqif ; rewrite p0_neq0 orbT /=.
by move => [_ /eqP H].
Qed.

End MainRevPoly.

Lemma revp_scale (R : idomainType) (p : {poly R}) (c : R) : 
  revp (c *: p) = c *: (revp p).
Proof.
have [ -> | /negbTE c_neq0 ] := eqVneq c 0. 
  by rewrite !scale0r revp0.
rewrite -!map_poly_mul ; apply: revp_map => x.
by rewrite mulf_eq0 c_neq0 orFb.
Qed.

Lemma revp_scale2 (R : ringType) (p : {poly R}) (c : R) : 
             (c * (lead_coef p) != 0) -> revp (c *: p) = c *: (revp p).
Proof.
move => H.
have c_neq0 : c != 0.
  apply/eqP => c_eq0.
  by rewrite c_eq0 mul0r eqxx in H.
apply/polyP => i.
rewrite coefZ.
have Hsize : size (c *: p) = size p.
move: (@size_proper_mul R (c %:P) p).
  rewrite lead_coefC size_polyC c_neq0 mul_polyC /= => H2.
  by apply: H2.
have [ lt_i_sizep | leq_sizep_i ] := ltnP i (size p).
  by rewrite coef_revp ?Hsize // coef_revp // coefZ.
have leq_sizerevp_i : size (revp p) <= i.
  by apply: (leq_trans (size_revp_leqif _)).
move/leq_sizeP/(_ i) : leq_sizerevp_i.
rewrite leqnn => -> //.
rewrite mulr0.
have : size (revp (c *: p)) <= i.
  by rewrite (leq_trans (size_revp_leqif _)) // (leq_trans (size_scale_leq _ _)).
by move/leq_sizeP/(_ i) ; rewrite leqnn => ->.
Qed.

Lemma rev_monic_scale (R : ringType) (p : {poly R}) (c : R) : 
  p \is monic ->
  revp (c *: p) = c *: (revp p).
Proof.
move/monicP => p_monic.
have [ -> | c_neq0 ] := eqVneq c 0.
  by rewrite !scale0r revp0.
by rewrite revp_scale2 // p_monic mulr1.
Qed.

Lemma revpM (R : ringType) (p q : {poly R}) :
  (lead_coef p) * (lead_coef q) != 0 ->
  revp (p * q) = (revp p) * (revp q).
Proof.
move => lplq_neq0.
have p_neq0 : p != 0.
  by apply: contraNneq lplq_neq0 => -> ; rewrite lead_coef0 mul0r eqxx.
have q_neq0 : q != 0.
  by apply: contraNneq lplq_neq0 => -> ; rewrite lead_coef0 mulr0 eqxx.
move: (multiplicity_XsubC p 0) (multiplicity_XsubC q 0).
rewrite subr0 p_neq0 q_neq0 /=.
move => [a [u /idP/rootP /eqP u0_neq0]] Hp [b [v /idP/rootP /eqP v0_neq0]] Hq.
rewrite Hp Hq.
rewrite mulrA !revp_mulMXn -mulrA -commr_polyXn mulrA revp_mulMXn.
have u_neq0 : u != 0 by apply: contraNneq u0_neq0 => -> ; rewrite horner0 eqxx.
have v_neq0 : v != 0 by apply: contraNneq v0_neq0 => -> ; rewrite horner0 eqxx.
move: lplq_neq0 ; rewrite Hp Hq !lead_coefMXn.
move => lulv_neq0 {p q a b p_neq0 q_neq0 Hp Hq}.
rewrite revp_indexing -[RHS]coefK size_proper_mul //.
rewrite [in RHS](@widen_poly _ _ _ (size u + size v).-1) ; last 2 first.
+ apply: (leq_trans (size_mul_leq _ _)).
  rewrite size_revp -?horner_coef0 //.
  by rewrite size_revp -?horner_coef0.
+ move => j /andP [Hj _].
  move/leq_sizeP/(_ j) : Hj ; rewrite leqnn => -> //.
apply/polyP => k ; rewrite !coef_poly.
have [ lt_k_s | leq_s_k ] := ltnP k (size u + size v).-1 => //.
rewrite !coefM subnSK //=.
rewrite (bigID (fun j => ((nat_of_ord j) < size u)) predT) /=.
rewrite [X in _ + X](eq_bigr (fun i => 0)) => [ | i ] ; last first.
  rewrite -leqNgt => /leq_sizeP Hi.
  by rewrite (Hi i) // mul0r.
rewrite big1_eq addr0 [RHS](bigID (fun j => ((nat_of_ord j) < size u)) _) /=.
rewrite [X in _ + X](eq_bigr (fun i => 0)) => [ | i ] ; last first.
  rewrite -size_revp -?horner_coef0 // -leqNgt => /leq_sizeP Hi.
  by rewrite (Hi i) // mul0r.
rewrite big1_eq addr0.
rewrite (exchange_ord_cond _ _ _ (fun i => u`_i * v`_(_ - i))) /=.
rewrite (exchange_ord_cond _ _ _ (fun i => (_)`_i * (_)`_(k - i))) /=.
rewrite -(big_mkord (fun i => i < _) (fun i => (_)`_i * (_)`_(k - i))). 
rewrite [RHS]big_nat_rev /= add0n big_mkord.
rewrite (bigID (fun j=> ((size u + size v).-1 - k.+1 - (nat_of_ord j) < size v)) 
  (fun j => j < _)) /=.
rewrite [X in _ + X](eq_bigr (fun i => 0)) => [ | i ] ; last first.
  rewrite -leqNgt => /andP [_ /leq_sizeP Hi].
  by rewrite (Hi _) // mulr0.
rewrite big1_eq addr0.
rewrite [RHS](bigID (fun j=> k - (size u - (nat_of_ord j).+1) < size v) _) /=.
rewrite [X in _ + X](eq_bigr (fun i => 0)) => [ | i ] ; last first.
  rewrite -[size v]size_revp -?horner_coef0 // -leqNgt
                                                    => /andP [_ /leq_sizeP Hi].
  by rewrite (Hi _) // mulr0.
rewrite big1_eq addr0; apply: eq_big=> [i | i /andP [Hi H'i]] //= ; last first.
+ rewrite ltn_subRL ltnpredn in Hi ; move: H'i.
  rewrite aux_nat ; last by rewrite lt0n size_poly_eq0.
  rewrite aux_nat ; last by apply: ltn_addl ; rewrite lt0n size_poly_eq0.
  rewrite coef_revp ; last first.
    by rewrite -subn_gt0 subnBA // addnC addnK.
  rewrite coef_revp ; last first.
    rewrite subnBA // aux_nat ; last by rewrite lt0n size_poly_eq0.
    by rewrite addnS.
  rewrite addnA ltpredn ; last by rewrite size_poly_eq0.
  rewrite prednK ; last by rewrite lt0n size_poly_eq0.
  rewrite addSn => H2.
  congr (_ * _) ; first by rewrite subnS subnBA // addnC addnK.
  congr (nth _); rewrite [RHS]subnS subnBA ; last first.
    by rewrite leq_subLR addSn addnC.
  rewrite addnBA // [((size v) + _)%N]addnC -subnS -[i.+1]add1n subnDA subn1.
  by rewrite -!subnDA [(_ + i)%N]addnC.
+ rewrite andbC ltn_subRL.
  rewrite aux_nat ; last by rewrite lt0n size_poly_eq0.
  rewrite aux_nat ; last by apply: ltn_addl ; rewrite lt0n size_poly_eq0.
  rewrite aux_nat // addnA ltpredn ; last by rewrite size_poly_eq0.
  rewrite addnC ; congr andb.
- rewrite prednK ; last by rewrite lt0n size_poly_eq0.
  by rewrite addSn ltnS.
- rewrite subnBA // aux_nat ; last by rewrite lt0n size_poly_eq0.
  by rewrite ltnpredn addnS.
Qed.

End RevPoly.
 
