(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  some doc here                                                            *)
(*****************************************************************************)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype div tuple finfun.
From mathcomp
Require Import bigop finset fingroup perm ssralg poly.
From mathcomp
Require Import polydiv mxpoly binomial bigop ssralg finalg zmodp matrix. 
From mathcomp 
Require Import mxalgebra polyXY ring_quotient.
From Newtonsums 
Require Import auxresults valuation fraction revpoly fracrev polydec.
From Newtonsums 
Require Import truncpowerseries expansiblefracpoly.

Import FracField.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Local Notation "x =p y"  := (perm_eq x y) (at level 70, no associativity).

Local Notation "p ^^^ f" := (map_frac (map_poly f) p)
                              (f at next level, at level 30).

Local Notation Tfpsp := trXn.


Section MoreBigop.

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

End MoreBigop.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.

Section MorePoly.

Lemma deriv_prod (K : fieldType) (I : eqType) rI (F : I -> {poly K}) : 
  (\prod_(i <- rI) (F i)) ^`() = \sum_(i <- rI) (F i) ^`() 
  * (\prod_(j <- (rem i rI)) (F j)).
Proof.
elim: rI => [| a l iH]; first by rewrite !big_nil; exact: derivC.
rewrite !big_cons rem_cons derivM iH ; congr (_ + _).
rewrite big_distrr [LHS]/= !big_seq ; apply: eq_big => // i i_in_l. 
rewrite mulrA [X in X * _]mulrC -mulrA ; congr (_ * _).
have [a_eq_i | a_neq_i] := boolP (a == i).
  move/eqP : a_eq_i ->.
  by rewrite /= eqxx (eq_big_perm _ (perm_to_rem i_in_l)) big_cons. 
move/negbTE : a_neq_i => /= ->.
by rewrite big_cons. 
Qed.

Lemma horner_prod_comm (K : fieldType) (s : seq {poly K}) (x : K) : 
  (\prod_(q <- s) (q)).[x] = \prod_(q <- s) (q.[x]).
Proof. by rewrite -horner_evalE rmorph_prod. Qed.

End MorePoly.

Section PolynomialFractions.

Variables (K L : fieldType) (iota : {injmorphism K -> L}).
  
Hint Resolve tofrac_inj.

Fact size_map_iota_p (p : {poly K}) : size (p ^ iota) = size p.
Proof. by rewrite size_map_inj_poly // rmorph0. Qed.

Fact lead_coef_map_iota_p (p : {poly K}) : 
  lead_coef (p ^ iota) = iota (lead_coef p).
Proof. by rewrite lead_coef_map_inj // rmorph0. Qed.

Lemma devs_fracpoly_iota (x : {fracpoly K}) : 
    (0.-fppole) (x ^^^ iota) = (0.-fppole) x.
Proof. by rewrite -[0](rmorph0 iota); apply: fppole_map. Qed.

End PolynomialFractions.

(* Import truncpowerseries.Notations. *)
Local Open Scope tfps_scope.

Section NewtonRepresentation.

Definition newton (K : fieldType) (p : {poly K}) := 
  revp p^`() // revp p.

Lemma newtonC (K : fieldType) (c : K) : newton c%:P = 0.
Proof. by rewrite /newton derivC revp0 rmorph0 mul0r. Qed.

Lemma newton0 (K : fieldType) : newton 0 = 0 :> {fracpoly K}.
Proof. by rewrite newtonC. Qed.

Lemma newton_devs (K : fieldType) (p : {poly K}): devs (newton p).
Proof.
have [-> | p_neq0] := eqVneq p 0; first by rewrite newton0 -unfold_in rpred0.
by apply: (contra (@devs_frac _ _ _)); rewrite coef0_revp lead_coef_eq0.
Qed.

Definition newton_tfps (K : fieldType) (m : nat) (p : {poly K}) := 
  Tfpsfp m (newton p).

Variables (K L : fieldType) (iota : {injmorphism K -> L}).
  
(* Hint Resolve tofrac_inj. *)

Lemma newton_eq (p q: {poly K}): p %= q -> newton p = newton q.
Proof.
move/eqpP => [ [ a b ] /= /andP [ a_neq0 b_neq0 ] ].
move/(congr1 (fun x => a^-1 *: x)).
rewrite !scalerA mulrC divff // scale1r => ->.
rewrite /newton !derivZ !revpZ -!mul_polyC rmorphM [X in _ / X]rmorphM /=.
rewrite -mulf_div divff ?mul1r // raddf_eq0; last exact: tofrac_inj.
by rewrite polyC_eq0 mulf_neq0 // invr_eq0.
Qed.

Lemma newton_map_poly (p : {poly K}) : newton (p ^ iota) = (newton p) ^^^ iota.
Proof.
by rewrite /newton fmorph_div /= deriv_map !map_fracE !revp_map.
Qed.

Lemma newton_tfps0 (m : nat) : newton_tfps m (0 : {poly K}) = 0.
Proof. by rewrite /newton_tfps newton0 Tfpsfp0. Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Hint Resolve char_K_is_zero.

Section Variable_m.
Variable (m : nat).

Lemma geometric_series (K' : fieldType) (a : K') :
  Tfpsfp m (((1 - a *: 'X)%:F) ^-1) = [tfps j => a ^+ j].
Proof.
have dev: devs (1 - a *: 'X)%:F^-1 by apply: devs_inv1subCX.
rewrite Tfpsfp_inv_tofrac; last first.
  by rewrite coefB coefC coefZ coefX mulr0 subr0 oner_neq0. 
have Hunit: (Tfpsp m (1 - a *: 'X)) \is a GRing.unit.
  by rewrite Tfpsp_is_unit coefB coefC coefZ coefX mulr0 subr0 oner_neq0. 
apply: (mulrI Hunit); rewrite divrr; last first.
  by rewrite Tfpsp_is_unit coefB coefC coefZ coefX mulr0 subr0 oner_neq0. 
apply/val_inj=> /=.
rewrite -!trXn_modE modp_mul2 trXn_modE.
rewrite mulrBl mul1r /=; apply/polyP=> i.
rewrite coef_trXn !poly_def mulr_sumr /=.
rewrite [X in _ - X](eq_bigr (fun i => a ^+ (nat_of_ord i).+1 *: 
                                              'X^(nat_of_ord i).+1)); last first.
  by move=> j _; rewrite -scalerAr -scalerAl scalerA -exprS -exprSr.
rewrite -opprB -sumrB. 
rewrite -(big_mkord predT (fun i => a ^+ i.+1 *: 'X^i.+1 - a ^+ i *: 'X^i)) /=.
rewrite telescope_sumr // opprB coefB !coefZ !expr0 mul1r coefXn.
rewrite coef1; have [|] := ltnP; case: i => [|i] //=.
  by rewrite mulr0 subr0.
by rewrite ltn_neqAle eqSS => /andP [ /negbTE -> _]; rewrite mulr0 subr0.
Qed.

End Variable_m.

Lemma newton_tfps_map_iota (m : nat) (p : {poly K}) : 
    map_tfps iota (newton_tfps m p) = newton_tfps m (p ^ iota).
Proof. by rewrite map_Tfpsfp /newton_tfps newton_map_poly. Qed.

End NewtonRepresentation.

Section Newton.

Variables (K : fieldType) (L : closedFieldType) (f : {injmorphism K -> L}).

Definition iroots (p : {poly K}) := roots (p ^ f).

Fact irootsC c : iroots c%:P = [::].
Proof. by rewrite /iroots map_polyC rootsC. Qed.

Fact iroots0 : iroots 0 = [::]. Proof. by rewrite irootsC. Qed.

Fact factorization (p : {poly K}) : p ^ f = 
(f (lead_coef p)) *: \prod_(r <- iroots p) ('X - r%:P).
Proof. by rewrite (roots_factor_theorem_f (p ^ f)) lead_coef_map. Qed.

Fact coef0_iroots (p : {poly K}) : f p`_0 = 
  (f (lead_coef p)) * (\prod_(r <- iroots p) -r).
Proof.
rewrite -coef_map_id0 ; last exact: rmorph0.
rewrite factorization -horner_coef0 -horner_evalE linearZ /= rmorph_prod.
congr (_ * _) ; apply: eq_bigr => i _.
by rewrite /= horner_evalE hornerXsubC add0r. 
Qed.

Fact irootsP (p : {poly K}) : p != 0 -> iroots p =i root (p ^ f).
Proof. move => p_neq0 x ; by rewrite /iroots rootsP // map_poly_eq0. Qed.

Lemma perm_eq_roots (p q : {poly L}) : p %= q -> (roots p) =p (roots q).
Proof.
move/eqpP => [[a b] /= /andP [a_neq0 b_neq0] H].
move: (@perm_eq_roots_mulC L a p a_neq0) ; rewrite perm_eq_sym => Hp.
apply: (perm_eq_trans Hp).
by rewrite H perm_eq_roots_mulC.
Qed.

Lemma lead_coef_revp (p : {poly K}) : p`_0 != 0 -> 
  f (lead_coef (revp p)) = 
  (f (lead_coef p)) * (\prod_(r <- iroots p) (-r)).
Proof.
move => H ; rewrite -coef0_iroots.
have -> : lead_coef (revp p) = p`_0 ; last by [].
rewrite lead_coef_revp.
have [->|pN0] := eqVneq p 0; rewrite ?valp0 //.
rewrite -valp_eq0E // in H.
by move/eqP : H ->.
Qed.

Lemma comp_p_q (p : {poly K}) (q : {fracpoly K}) :  
  ((p ^ f) %:F) \FPo (q ^^^ f) 
  = ((f (lead_coef p))%:FP) * \prod_(r <- iroots p) ((q ^^^ f) - (r%:FP)). 
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

Fact  iroots_size (p : {poly K}) : size (iroots p) = (size p).-1.
Proof. by rewrite /iroots roots_size size_map_iota_p. Qed.

(* should be in revpoly with K a closed field *)
Lemma revp_factorization (p : {poly K}) : ((revp p) ^ f) = 
    (f (lead_coef p)) *: (\prod_(r <- iroots p) (1 - r*:'X)).
Proof.
have [p_eq0 | p_neq0] := boolP (p == 0).
  by move/eqP : p_eq0 ->; rewrite revp0 lead_coef0 !rmorph0 scale0r.
apply/eqP; rewrite -(inj_eq (@tofrac_inj _)) -revp_map tofrac_revp. 
rewrite size_map_iota_p -(map_fracpolyXV f) comp_p_q /=. 
rewrite -mul_polyC rmorphM /= -mulrA ; apply/eqP ; congr (_ * _).
have -> : 'X%:F ^+ (size p).-1 = \prod_(r <- iroots p) 'X%:F => [t|].
  rewrite (big_const_seq 1 (@GRing.mul _) (iroots p) predT 'X%:F).
  have -> : count predT (iroots p) = (size p).-1 
    by rewrite count_predT iroots_size. 
  exact: Monoid.iteropE. 
rewrite -big_split rmorph_prod; apply: eq_big => //= i _.
rewrite mulrBl rmorphD /= map_fracpolyXV mulrC divff; last first.
  by rewrite raddf_eq0 ?polyX_eq0 //; apply: tofrac_inj.
by rewrite rmorphN /= tofrac_scale.
Qed.

Definition mu (x : L) (p : {poly K}) := polyorder.multiplicity x (p ^ f).

(* should be in revpoly with K a closed field *)
Lemma revp_factorization2 (p : {poly K}) : ((revp p) ^ f) = 
  (f (lead_coef p)) * (-1)^+((size p).-1 - (mu 0 p)) 
  * (\prod_(r <- iroots p | r != 0) r)
  *: (\prod_(r <- iroots p | r != 0) ('X - (r ^-1)%:P)). 
Proof.
rewrite revp_factorization -mulrA -scalerA.
have [-> | p_neq0] := eqVneq p 0 ; first by rewrite lead_coef0 rmorph0 !scale0r.
congr (_ *: _).
rewrite (bigID (fun r => (r == 0)) predT _) /=.
rewrite (eq_bigr (fun r => 1)) => [|r /eqP ->]; last by rewrite scale0r subr0.
rewrite big1_eq mul1r -scalerA -scaler_prod.
have <- : \prod_(i <- iroots p | i != 0) -(1 : L) = 
                                                  (-1) ^+ ((size p).-1 - mu 0 p).
  rewrite prod_cond_const; congr (_ ^+ _).
  rewrite -iroots_size -(count_predC (fun x => x == 0)) addnC.
  have ->: mu 0 p = count (eq_op^~ 0) (iroots p).
    rewrite /mu roots_mu ; last by rewrite map_poly_eq0.
    by apply: eq_in_count.
  rewrite -addnBA // subnn addn0.
  by apply: eq_in_count.
rewrite -scaler_prod ; apply: eq_bigr => r Hr.
by rewrite scalerBr scaleN1r opprB -[r *: (r^-1)%:P]mul_polyC -polyC_mul divff.
Qed.

Fact zero_in_iroots (p : {poly K}) : p != 0 -> (0 \in (iroots p)) = (root p 0).
Proof.
move => p_neq0.
rewrite rootsP ?map_poly_eq0 //. 
by rewrite (qualifE 0) -{1}[0](rmorph0 f) horner_map fmorph_eq0.
Qed.

Fact pneq0 (p : {poly K}) : ~~ (root p 0) -> p != 0.
Proof. apply: contra => /eqP -> ; exact: root0. Qed.

(* is there a notation for GRing.inv ? *)
(* revpoly result without iota *)
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

(* should be in fraction with K a closed field *)
Lemma deriv_p_over_p (p : {poly K}) : p != 0 -> 
((p ^`())%:F / (p%:F)) ^^^ f = \sum_(r <- iroots p) (('X - r%:P)%:F) ^-1.
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
  by rewrite monic_neq0 // monic_prod_XsubC.
+ rewrite mulrA divff ?mul1r // raddf_eq0 ;last exact: tofrac_inj.
  by rewrite monic_neq0 // monic_prod_XsubC.
Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Lemma newton_roots (p : {poly K}) : (newton p) ^^^ f = 
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
- by move=> g h /=; rewrite comp_fracpolyD ?nocomp_fracpolyXV.
rewrite mulr_suml; apply: eq_bigr => i _; rewrite comp_fracpolyV -invfM.
rewrite comp_poly_frac !rmorphB /= map_polyX map_polyC /= hornerXsubC.
by rewrite mulrDl mulVf ?rmorph_eq0 ?polyX_eq0 // mulNr -mul_polyC rmorphM.
Qed.

Definition cadd (p q : {poly K}) :=
  if (p == 0) then (q ^ f) else
  if (q == 0) then (p ^ f) else
  \prod_(r <- [seq s+t | s <- iroots p, t <- iroots q]) ('X - r%:P).

Lemma caddP (p q : {poly K}) : p != 0 -> q != 0 -> cadd p q = 
               \prod_(r <- [seq s+t | s <- iroots p, t <- iroots q]) ('X - r%:P).
Proof.
move/negbTE => p_neq0 /negbTE q_neq0.
by rewrite /cadd p_neq0 q_neq0.
Qed.

Lemma cadd0p (p : {poly K}) : cadd 0 p = (p ^ f).
Proof. by rewrite /cadd eqxx. Qed.

Lemma caddp0 (p : {poly K}) : cadd p 0 = (p ^ f).
Proof.
rewrite /cadd.
have [ -> | p_neq0] := eqVneq p 0 ; first by rewrite eqxx.
by rewrite (negbTE p_neq0) eqxx.
Qed.

Lemma cadd_is_prod (p q : {poly K}) :
  p != 0 -> q != 0 -> cadd p q =
  \prod_(r <- [seq s+t | s <- iroots p, t <- iroots q]) ('X - r%:P).
Proof. rewrite /cadd ; by move/negbTE -> ; move/negbTE ->. Qed.

Lemma size_cadd (p q : {poly K}) : p != 0 -> q != 0 -> 
  (size (cadd p q)).-1 = (((size p).-1) * ((size q).-1))%N.
Proof.
move => p_neq0 q_neq0.
by rewrite caddP // size_prod_XsubC size_allpairs !iroots_size.
Qed.

Definition cmul (p q : {poly K}) :=
   if (p == 0) || (q == 0) then 0 else
   \prod_(r <- [seq s*t | s <- iroots p, t <- iroots q]) ('X - r%:P).

Lemma cmul0p (p : {poly K}) : cmul 0 p = 0.
Proof. by rewrite /cmul eqxx. Qed.

Lemma cmulp0 (p : {poly K}) : cmul p 0 = 0.
Proof. by rewrite /cmul eqxx orbT. Qed.

Lemma cmul_is_prod (p q : {poly K}) :
  p != 0 -> q != 0 ->  cmul p q =
             \prod_(r <- [seq s*t | s <- iroots p, t <- iroots q]) ('X - r%:P).
Proof. rewrite /cmul ; by move/negbTE -> ; move/negbTE ->. Qed.

Lemma cmul_neq0 (p q : {poly K}) :
  p != 0 -> q != 0 -> cmul p q != 0.
Proof.
move => p_neq0 q_neq0.
rewrite cmul_is_prod // prodf_seq_neq0.
apply/allP => x _.
by rewrite polyXsubC_eq0.
Qed.

Lemma roots_cmul (p q : {poly K}) :
  roots (cmul p q) =p [seq s*t | s <- iroots p, t <- iroots q].
Proof.
have [p_eq0 | p_neq0] := eqVneq p 0.
+ rewrite p_eq0 cmul0p roots0 perm_eq_sym perm_eq_nil.
  by rewrite -size_eq0 size_allpairs iroots0 /= mul0n.
+ have [q_eq0 | q_neq0] := eqVneq q 0.
  rewrite q_eq0 cmulp0 roots0 perm_eq_sym perm_eq_nil.
  by rewrite -size_eq0 size_allpairs iroots0 /= muln0.
rewrite cmul_is_prod //.
exact: perm_eq_roots_factors.
Qed.

Lemma roots_cadd(p q : {poly K}) :
  p != 0 -> q != 0 ->
  roots (cadd p q) =p [seq s+t | s <- iroots p, t <- iroots q].
Proof.
move => p_neq0 q_neq0.
rewrite cadd_is_prod //; exact: perm_eq_roots_factors.
Qed.

Local Notation "f ^ g" := (map_tfps g f). 

Lemma iota_newton_tfps (p : {poly K}) (m : nat) :
  newton_tfps m p ^ f = [tfps j => \sum_(r <- iroots p) r ^+ j].
Proof.
rewrite map_Tfpsfp /= newton_roots.
rewrite (big_morph_in (@devsD _) _ (@TfpsfpD _ _) (@Tfpsfp0 _ _)); last 2 first.
- exact: rpred0.
- apply/allP => x /=; move/mapP; rewrite filter_predT; move=> [y hy ->].
  exact: devs_inv1subCX.
apply/tfpsP => i /= le_im; rewrite coef_poly ltnS le_im.
rewrite (@big_morph _ _ (fun (x : {tfps L m}) => x`_i) 0 +%R); last 2 first.
- by move => x y; apply: coefD.
- exact: coef0.
by apply: eq_bigr => x _; rewrite geometric_series /= coef_poly ltnS le_im.
Qed.

Lemma map_poly_tfps m (s : {tfps K m}) :
  map_poly f (val s) = val (s ^ f).
Proof. by []. Qed.

Lemma newton_tfps_coef0 (p : {poly K}) (m : nat) :
    (newton_tfps m p)`_0 = ((size p).-1)%:R.
Proof.
apply: (@rmorph_inj _ _ f).
rewrite -coef_map map_poly_tfps iota_newton_tfps coef_tfps.
rewrite coef_tfps_of_fun /=.
rewrite rmorph_nat -iroots_size -sum1_size natr_sum.
by apply: eq_bigr => r; rewrite expr0.
Qed.

End Newton.

Section Conversion.

Variable (K : fieldType) (L : closedFieldType) (f : {injmorphism K -> L}). 

Local Notation "f ^ g" := (map_tfps g f).

Hypothesis char_L_is_zero : [char L] =i pred0.

Hint Resolve char_L_is_zero.

Lemma char_K_is_zero : [char K] =i pred0.
Proof. move => x ; by rewrite -(fmorph_char f). Qed. 

Hint Resolve char_K_is_zero. 

Lemma nth_newton_tfps (p : {poly L}) (m i : nat) : 
  (newton_tfps m p)`_i = if i < m.+1 then
  (\sum_(r <- iroots [injmorphism of idfun] p) r ^+i) else 0.
Proof.
rewrite coef_tfpsE.
have -> : val (newton_tfps m p) = 
       tfps (map_tfps [injmorphism of (@idfun L)] (newton_tfps m p)).
  by rewrite -map_poly_tfps map_poly_id.
by rewrite iota_newton_tfps //= coef_poly.
Qed.

Lemma iroots_idfun (p : {poly L}) : 
  iroots [injmorphism of (@idfun L)] p = roots p.
Proof. by rewrite /iroots map_poly_idfun. Qed.

Lemma iroots_cmul (p q : {poly K}) :
   iroots [injmorphism of @idfun L] (cmul f p q) 
                         =p [seq s*t | s <- iroots f p, t <- iroots f q].
Proof. rewrite iroots_idfun; exact: roots_cmul. Qed.

Lemma iroots_cadd (p q : {poly K}) : p != 0 -> q != 0 ->
   iroots [injmorphism of @idfun L] (cadd f p q) 
                       =p [seq s + t | s <- iroots f p, t <- iroots f q].
Proof.
move => p_neq0 q_neq0.
rewrite iroots_idfun ; exact: roots_cadd.
Qed.

Lemma eq_big_allpairs (R : Type) (idx : R) (op : Monoid.com_law idx) 
  (I : eqType) (r1 r2 : seq I) (F : I -> R) (h : I -> I -> I) :
  \big[op/idx]_(k <- [seq h i j | i <- r1, j <-r2]) F k = 
  \big[op/idx]_(i <- r1) (\big[op/idx]_(j <- r2) F (h i j)).
Proof.
elim: r1; first by rewrite big_nil; apply: big_nil.
move => a l iH /=.
by rewrite big_cat iH big_map big_cons.
Qed.
 
Lemma newton_cmul (p q : {poly K}) :
  let m := ((size p).-1 * (size p).-1)%N in
  newton_tfps m (cmul f p q) =
  (hmul_tfps (newton_tfps m p) (newton_tfps m q)) ^ f.
Proof.
rewrite /=.
set m := ((size p).-1 * (size p).-1)%N.
have [p_eq0 | p_neq0 ] := eqVneq p 0.
  rewrite p_eq0 newton_tfps0 hmul_tfps0r rmorph0 cmul0p.
  exact: newton_tfps0.
have [q_eq0 | q_neq0] := eqVneq q 0.  
  rewrite q_eq0 newton_tfps0 hmul_tfpsr0 rmorph0 cmulp0.
  exact: newton_tfps0.
have -> : newton_tfps m (cmul f p q) =
    newton_tfps m (cmul f p q) ^ [rmorphism of (@idfun L)].
  by rewrite map_tfps_idfun.
rewrite map_tfps_idfun /=.
rewrite map_hmul !iota_newton_tfps //.
apply/tfpsP => i /= le_im.
rewrite !coef_poly ltnS le_im.
rewrite (big_distrl _ _ _) /=.
rewrite nth_newton_tfps ltnS le_im.
rewrite (eq_big_perm [seq s * t | s <- iroots f p, t <- iroots f q]); last first.
exact: iroots_cmul.
rewrite /= eq_big_allpairs /=.
apply: eq_bigr => j _ ; rewrite (big_distrr _ _ _) /=.
apply: eq_bigr => k _ ; rewrite exprMn_comm //.
exact: mulrC.
Qed.

Definition expX (K' : fieldType) (m : nat) := exp (Tfpsp m ('X : {poly K'})).

Lemma expX0 (K' : fieldType) : expX K' 0%N = 1.
Proof.
rewrite -exp0; congr exp; apply/tfpsP => i /=.
rewrite leqn0 => /eqP ->.
by rewrite coef0 coef_trXn coefX.
Qed.

Lemma nth_expX (K' : fieldType) (m i : nat) : 
  (expX K' m)`_i = if i < m.+1 then i`!%:R^-1 else 0.
have [->|m_neq0] := eqVneq m O.
  case: i => [|i]; last by rewrite coef_tfps ltn0.
  by rewrite coef0_exp ?fact0 ?invr1 // coef0_eq0E coef_trXn coefX.
rewrite /expX /exp coef0_eq0E coef_trXn coefX eqxx /= coef_tfps ltnS.
rewrite coef_tfpsE raddf_sum.
rewrite (eq_bigr (fun i : 'I_m.+1 => i`!%:R^-1 *: 'X ^+ i)); last first.
  move => j _ /=.
  by rewrite -rmorphX /= trXnK // size_polyXn ltn_ord.
by rewrite -(@poly_def _ _ (fun i => i`!%:R^-1)) coef_poly ltnS; case: (_ <= _).
Qed.

(* can be generalized to (exp f) ^ iota = exp (f ^ iota) *)
Lemma map_iota_expX (m : nat) : expX K m ^ f = expX L m.
Proof.
rewrite /expX /exp !coef0_eq0E !coef0_trXn !coefX !eqxx /=.
rewrite rmorph_sum /=; apply: eq_bigr => i _.
rewrite linearZ ; congr (_ *: _).
  by rewrite rmorphV ?rmorph_nat // unitfE natmul_inj // -lt0n fact_gt0.
  rewrite !rmorphX /=.
by rewrite -trXn_map_poly map_polyX.
Qed.

Lemma hmul_tfps_p_expX (K' : fieldType) (m : nat ) (p : {tfps K' m}) :
  hmul_tfps p (expX K' m) = [tfps i => p`_i / i`!%:R].
Proof.
apply/val_inj => /=.
apply/polyP => i.
rewrite !coef_poly nth_expX.
by case: (i < m.+1).
Qed.

Lemma aux_newton_cadd (K' : fieldType) (g : {rmorphism K' -> L}) 
  (m : nat) (s t : seq K') (p : {tfps K' m}) : p \in (@coef0_eq0 K' m) ->
  \sum_(w <- [seq u + v | u <- s, v <- t]) (exp (w *: p)) = 
  (\sum_(u <- s) (exp (u *: p))) * (\sum_(v <- t) (exp (v *: p))).
Proof.
move => p0_eq0.
have H : [char K'] =i pred0.
  move => x.
  rewrite -(fmorph_char g).
  by move: x. (* strange *)
rewrite eq_big_allpairs /=.
have -> : \sum_(i <- s) \sum_(j <- t) exp ((i + j) *: p) =
   \sum_(i <- s) \sum_(j <- t) (exp (i *: p)) * (exp (j *: p)).
  apply: eq_bigr => i _; apply: eq_bigr => j _.
  by rewrite scalerDl expD // -mulr_algr mulrC idealMr.
rewrite exchange_big /= mulr_sumr.
apply: eq_big => // i _.
by rewrite mulr_suml.
Qed.

Lemma sum_exp_kX (m : nat) (p : {poly L}) :
  hmul_tfps (newton_tfps m.+1 p) (expX L m.+1) = 
  \sum_(r <- iroots [injmorphism of @idfun L] p) (exp (r *: (@Tfpsp L m.+1 'X))).
Proof.
have [ -> | p_neq0] := eqVneq p 0.
  by rewrite newton_tfps0 hmul_tfps0r iroots0 big_nil.
rewrite hmul_tfps_p_expX.
apply/val_inj => /=.
rewrite poly_def.
have -> : \sum_(i < m.+2) ((newton_tfps m.+1 p)`_i / i`!%:R) *: 'X^i =
     \sum_(i < m.+2) ((\sum_(r <- iroots [injmorphism of @idfun L] p) r ^+ i) 
                                                               / i`!%:R) *: 'X^i.
  apply: eq_bigr => i _; congr (_ *: _); congr (_ / _).
  rewrite nth_newton_tfps ?ltn_ord //.
have -> : \sum_(i < m.+2)
   ((\sum_(r <- iroots [injmorphism of @idfun L] p) r ^+ i) / i`!%:R) *: 'X^i =
\sum_(i < m.+2)
   ((\sum_(r <- iroots [injmorphism of @idfun L] p) ((r *: 'X) ^+ i) / i`!%:R)).
  apply: eq_bigr => i _.
  have -> : 
  \sum_(r <- iroots [injmorphism of @idfun L] p) ((r *: 'X) ^+ i) / i`!%:R = 
  \sum_(r <- iroots [injmorphism of @idfun L] p) ((r ^+i) *: ('X ^+ i)) / i`!%:R.
    by apply: eq_bigr => j _; rewrite exprZn.
  rewrite /= mulr_suml scaler_suml; apply: eq_bigr => j _.
  rewrite -polyC1 -scaler_nat invrZ ; last 2 first.
      rewrite unitfE; move/(charf0P L) : char_L_is_zero ->.
      by rewrite -lt0n fact_gt0.
  by rewrite polyC1 unitrE divr1.
  by rewrite -scalerAr divr1 scalerA mulrC.
rewrite exchange_big /=.
rewrite (@big_morph _ _ (fun (x : {tfps L m.+1}) => val x) 0 +%R) //=.
apply: eq_big => //= x _.
rewrite exp_coef0_eq0; last first.
  by rewrite coef0_eq0E coefZ coef0_trXn coefX /= mulr0.
rewrite raddf_sum /=; apply: eq_bigr => //= i _.
rewrite mulrC -scaler_nat -in_algE -rmorphV ?fact_unit //= mulr_algl.
congr (_ *: _).
rewrite -linearZ -rmorphX /= trXnK //.
rewrite exprZn; apply: (leq_trans (size_scale_leq _ _)).
by rewrite size_polyXn ltn_ord.
Qed.

Lemma newton_cadd (p q : {poly K}) :
  p != 0 -> q != 0 ->
  let m := ((size p).-1 * (size p).-1)%N in
  hmul_tfps (newton_tfps m (cadd f p q)) (expX L m) =
  ((hmul_tfps (newton_tfps m p) (expX K m)) 
                    * (hmul_tfps (newton_tfps m q) (expX K m))) ^ f.
Proof.
move => p_neq0 q_neq0 /=.
set m := ((size p).-1 * (size p).-1)%N.
case: m => [|m].
  rewrite !expX0; apply/val_inj => /=.
  rewrite !poly_def !big_ord_recr !big_ord0 !Monoid.simpm /= -!/(_`_0).
  rewrite !(newton_tfps_coef0 [injmorphism of (@idfun L)]) //.
  rewrite coef1 mulr1 expr0 size_cadd // scaler_nat.
  rewrite !hmul_tfpsr1 !(newton_tfps_coef0 f) //=.
  rewrite -tfpsCM -natrM -alg_tfpsC scaler_nat.
  by rewrite !raddfMn /= rmorph1.
rewrite rmorphM /= !map_hmul map_iota_expX !newton_tfps_map_iota.
rewrite !sum_exp_kX.
rewrite (eq_big_perm [seq s + t | s <- iroots f p, t <- iroots f q]) /= ;
  last exact: iroots_cadd.
rewrite !iroots_idfun.
apply: (aux_newton_cadd [rmorphism of @idfun L]).
by rewrite coef0_eq0E coef0_trXn coefX [in X in X == _]eq_sym. 
Qed.

Fact aux_conversion1 (p : {poly K}) : ~~ (root p 0) ->
   ((revp p)^`() // revp p) ^^^ f  = 
  - \sum_(i <- iroots f p) i%:FP * (1 - i *: 'X)%:F^-1.
Proof.
move => zeroNroot.
rewrite deriv_p_over_p; last by rewrite revp_eq0 pneq0. 
 rewrite (eq_big_perm [seq x^-1 | x <- iroots f p]) ; 
                                                    last by rewrite roots_revp.
rewrite big_map big_seq (eq_bigr (fun r => - (r%:FP * (1 - r *: 'X)%:F^-1))) 
                                                     => [ | r Hr] ; last first.
  rewrite -invf_div ; apply: invr_inj ; rewrite !invrK.
  have r_neq0 : r != 0.
    apply/eqP => r_eq0.
    move: Hr; rewrite r_eq0.
    rewrite zero_in_iroots; last by apply: pneq0.
    by apply/negP.
  rewrite invrN invrK -mulNr -tofracN opprB.
  have H : r%:FP != 0.
    rewrite raddf_eq0 //; last first. 
    exact: (inj_comp (@tofrac_inj _) (@polyC_inj _)). 
  apply: (mulIf H); rewrite mulrAC -mulrA divff // mulr1 /= -tofracM.
  apply/eqP; rewrite inj_eq; last exact: tofrac_inj.
  by rewrite mulrBl mulrC mul_polyC -polyC_mul mulrC divff.
by rewrite sumrN -big_seq.
Qed.

(* to generalize ? *)
Fact aux_conversion2 (m : nat) (p : {poly K}) :
  ~~ (root p 0) ->
  Tfpsfp m (((revp p)^`() // revp p) ^^^ f) =
  - [tfps i => \sum_(r <- iroots f p) r ^+i.+1].
Proof.
move => zeroNroot.
rewrite aux_conversion1 // TfpsfpN; last first.
  rewrite rpred_sum // => x _; apply: devsM.
    by rewrite /devs fpole_tofrac.
    exact: devs_inv1subCX. 
congr (- _).
rewrite (big_morph_in (@devsD _) _ (@TfpsfpD _ _) (@Tfpsfp0 _ _)); last 2 first.
- exact: rpred0.
- apply/allP => x /=; move/mapP; rewrite filter_predT; move=> [y hy ->].
  apply: devsM.
    by rewrite /devs fpole_tofrac.
    exact: devs_inv1subCX.
apply/tfpsP => i /= le_im; rewrite coef_poly ltnS le_im.
rewrite (@big_morph _ _ (fun (x : {tfps L m}) => x`_i) 0 +%R); last 2 first.
- by move => x y; apply: coefD.
- exact: coef0.
apply: eq_bigr => x _; rewrite TfpsfpM -?topredE /= ; last 2 first.
- by rewrite /devs fpole_tofrac.
- exact: devs_inv1subCX.
rewrite coef_trXn le_im geometric_series Tfpsfp_tofrac /=.
by rewrite trXnC mul_polyC coefZ coef_poly ltnS le_im -exprS.
Qed.

End Conversion.

Section MoreConversion.

Variables (K : fieldType) (L : closedFieldType) (f : {injmorphism K -> L}).
Variable (m' : nat).
Let m := m'.+1.

Hypothesis char_L_is_zero : [char L] =i pred0.

Hint Resolve char_L_is_zero.
Hint Resolve (char_K_is_zero f char_L_is_zero).

Fact aux_conversion4 (p : {poly K}) : ~~ root p 0 ->
  Tfpsfp m' ((revp p)^`() // revp p)
  = divfX (((size p).-1)%:R%:S - (newton_tfps m p)).
Proof.
move => zeroNroot.
apply: (@map_tfps_injective _ _ m' f).
rewrite map_Tfpsfp aux_conversion2 // (@map_tfps_divfX _ _ f m'.+1).
apply/tfpsP => i le_im'.
rewrite coef_divfX coefN coef_poly ltnS le_im'.
rewrite rmorphB coefB -!coef_tfpsE /= -!/(_`_i.+1).
rewrite [X in val X]/=  newton_tfps_map_iota nth_newton_tfps //.
rewrite !ltnS le_im'.
rewrite coef_map coef_tfpsC /= rmorph0 sub0r.
by rewrite iroots_idfun.
Qed.

Lemma exp_prim_derivp_over_p (s : {tfps K m}) :
  s \in coef0_eq1 ->
  s = exp (prim_tfps ((s^`()%tfps) / (trXnt m' s)))%tfps.
Proof.
move => s0_eq1; apply: log_inj => //.
  by rewrite coef0_eq1E coef0_exp // coef0_eq0E coef0_prim_tfps.
rewrite expK // ?coef0_eq0E ?coef0_prim_tfps //.
apply: deriv_tfps_eq => //.
  by rewrite deriv_log // prim_tfpsK.
by rewrite coef0_log // coef0_prim_tfps.
Qed.

Definition newton_inv (p : {tfps K m}) : {poly K} := 
  revp (tfps (exp (prim_tfps (divfX ((p`_0)%:S - p))))).

Lemma newton_tfpsK (p : {poly K}) :
  size p <= m.+1 ->  ~~ (root p 0) -> p \is monic ->
  newton_inv (newton_tfps m p) = p.
Proof.
move => sp_lt_Sm Nrootp0 p_monic; rewrite /newton_inv.
apply: (canLR_in (@revp_involutive _)).
  by rewrite qualifE -horner_coef0.
have -> : revp p = tfps (Tfpsp m (revp p)).
  rewrite trXnK //.
  by rewrite (leq_trans (size_revp_leq _)).
rewrite [Tfpsp _ _ in RHS]exp_prim_derivp_over_p; last first.
  by rewrite coef0_eq1E coef0_trXn coef0_revp -monicE.
congr (tfps (exp (prim_tfps _))).
rewrite (newton_tfps_coef0 f) // -aux_conversion4 //=.
rewrite Tfpsfp_frac; last first.
  by rewrite coef0_revp; move/monicP : p_monic ->; apply: oner_neq0.
rewrite /m; congr (_ / _).
  by apply tfps_inj; rewrite -deriv_trXn val_deriv_tfps.
by rewrite trXntE trXn_trXn.
Qed.

End MoreConversion.

