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
Local Open Scope quotient_scope.
Local Open Scope tfps_scope.

Local Notation "x =p y"  := (perm_eq x y) (at level 70, no associativity).

Local Notation "p ^^ f" := (map_frac f p)  (f at next level, at level 30).
Local Notation "p ^^^ f" := (map_frac (map_poly f) p)
                              (f at next level, at level 30). 

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

Variable (K : fieldType).

Hypothesis char_K_is_zero : [char K] =i pred0.

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
+ by rewrite rmorph_div /= ?Tfpsp_is_unit // !Tfps_map_poly. 
by rewrite !Tfpsfp_eq0 // ?coef_map ?v0_eq0 /= ?rmorph0 // coprimep_map. 
Qed.

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

End PolynomialFractions.

Import truncpowerseries.Notations.

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
by rewrite /newton fracpoly_iota_div deriv_map !map_fracE !revp_map.
Qed.

Lemma newton_tfps0 (m : nat) : newton_tfps m (0 : {poly K}) = 0.
Proof. by rewrite /newton_tfps newton0 Tfpsfp0. Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Hint Resolve char_K_is_zero.

(* can be simplified ? *)
Lemma comp_fracpoly_poly_Xinv_eq0 (K' : fieldType) (p : {poly K'}) :
  (p%:F \FPo 'X^-1 == 0) = (p == 0).
Proof.
apply/idP/idP; last by move/eqP ->; rewrite comp_fracpoly0.
move/eqP/(congr1 (fun x => x * 'X^+(size p).-1)).
rewrite mul0r -tofrac_revp; move/eqP.
rewrite raddf_eq0; last exact: tofrac_inj.
by rewrite revp_eq0.
Qed. 

Lemma map_Tfpsfp (p : {fracpoly K}) (n : nat) :
  Tfpsfp n p ^ iota = Tfpsfp n (p ^^^ iota).
Proof.
move/eqP: (mapf_Tfpsfp iota n p).
rewrite -val_eqE /= modp_small; last first. 
  by rewrite size_polyXn ltnS size_map_poly size_tfps.
by move => /eqP ->.
Qed.

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
apply/val_inj=> /=; rewrite modp_mul2.
rewrite mulrBl mul1r /=; apply/polyP=> i.
rewrite coef_modXn !poly_def mulr_sumr /=.
rewrite [X in _ - X](eq_bigr (fun i => a ^+ (nat_of_ord i).+1 *: 
                                              'X^(nat_of_ord i).+1)); last first.
  by move=> j _; rewrite -scalerAr -scalerAl scalerA -exprS -exprSr.
rewrite -opprB -sumrB. 
rewrite -(big_mkord predT (fun i => a ^+ i.+1 *: 'X^i.+1 - a ^+ i *: 'X^i)) /=.
rewrite telescope_sumr // opprB coefB !coefZ !expr0 mul1r coefXn.
have [|] := ltnP; last by rewrite coefC; case: i.
by rewrite ltn_neqAle => /andP [ /negbTE -> _]; rewrite mulr0 subr0. 
Qed.

End Variable_m.

Lemma deriv_exp (m : nat) (p : {tfps K m}) : 
  (exp p)^` () = (p^` ()%tfps) * (Tfpsp m.-1 (exp p)).
Proof.
move: p ; case: m => /= [p | n p]. 
  by rewrite [p]tfps_is_cst deriv_tfpsC mul0r expC deriv_tfpsC.
have [p0_eq0 | p0_neq0] := boolP (p \in (@coef0_is_0 K n.+1)) ; last first.
  by rewrite exp_coef0_isnt_0 // deriv_tfps0 rmorph0 mulr0.
rewrite !exp_coef0_is_0 //= !deriv_tfpsE //=; apply/val_inj => /=.
rewrite deriv_modp modp_modp ?dvdp_exp2l // modp_modp ?dvdp_exp2l //.
rewrite deriv_sum -(big_mkord predT (fun i => i`!%:R^-1 *: _  ^+ i)) /=.
rewrite big_nat_recr //= modp_add modp_scalel.
rewrite modX_eq0 //; last by apply/eqP; rewrite -coef0_is_0E.
rewrite scaler0 addr0 modp_mul modp_mul2 mulr_sumr.
rewrite -(big_mkord predT (fun i => deriv (i`!%:R^-1 *: (val p) ^+ i))) /=.
rewrite big_nat_recl // expr0 linearZ /= derivC scaler0 add0r.
congr (_ %% _); apply: eq_bigr => i _.
rewrite linearZ /= deriv_exp /= -scalerCA -scaler_nat.
rewrite scalerA -scalerAl; congr (_ *: _).
rewrite factS natrM /= invrM ?unitfE ?natmul_inj // -?lt0n ?fact_gt0 //.
rewrite -mulrA [X in _ * X]mulrC.
by rewrite divff ?natmul_inj // -?lt0n ?fact_gt0 // mulr1.
Qed.

Lemma Tfpsp_modp (m n : nat) (p : {poly K}) : m < n ->
    Tfpsp m (p %% 'X^n) = Tfpsp m p.
Proof. by move=> lt_nm; apply/val_inj=> /=; rewrite modp_modp // dvdp_exp2l. Qed.

Lemma deriv_tfps_exp (m : nat) (f : {tfps K m}) (n : nat) :
    (f ^+ n)^`() = f^`()%tfps * (Tfpsp m.-1 f) ^+ n.-1 *+ n.
Proof.
elim: n => /= [|n IHn]; first by rewrite expr0 mulr0n onefE deriv_tfpsC.
rewrite exprS deriv_tfpsM {}IHn (mulrC (_ f)) val_exp_tfps /=.
rewrite mulrC -mulrnAr mulrCA -mulrDr -mulrnAr; congr (_ * _).
rewrite Tfpsp_modp; last by clear f; case: m.
rewrite rmorphX /= mulrnAr -exprS; case: n => /= [|n]; rewrite -?mulrS //.
by rewrite !expr0 mulr0n addr0.
Qed.

Lemma deriv_Tfps0p (f : {tfps K 0}) : f ^` () = 0.
Proof.
by rewrite [f]tfps_is_cst deriv_tfpsE deriv_modp derivC mod0p rmorph0.
Qed.

Lemma deriv_log (m : nat) (f : {tfps K m}) : 
       f \in (@coef0_is_1 K m) -> (log f)^`() = (f )^`()%tfps / (Tfpsp m.-1 f).
Proof.
move: f; case: m => [|m]; move => f.
rewrite [f]tfps_is_cst coef0_is_1E nth0_Tfpsp coefC eqxx => /eqP ->.
by rewrite !deriv_Tfps0p mul0r.
move => f0_is_1.
rewrite log_coef0_is_1 // rmorphN rmorph_sum linearN raddf_sum -sumrN. 
rewrite big_nat.
rewrite (eq_bigr (fun i => f^`()%tfps * ((1 - (Tfpsp m f)) ^+ i.-1))) => 
                                                  [|i /andP [hi _]]; last first.
+ rewrite linearZ rmorphX /= deriv_tfpsZ rmorphB rmorph1 deriv_tfps_exp. 
  rewrite linearB rmorphB rmorph1 onefE /= deriv_tfpsC sub0r /= Tfpsp_modp //.
  rewrite -scaler_nat scalerA mulrC divff ?natmul_inj //-?lt0n // scale1r mulNr.
  rewrite  opprK; congr (_ * _); apply/val_inj => /=.
  by rewrite modp_small // size_polyXn ltnS size_tfps.
+ rewrite -big_nat /= -mulr_sumr big_add1 /= big_mkord; congr (_ * _).
  have trp_unit : Tfpsp m f \is a GRing.unit.
    rewrite Tfpsp_is_unit.
    by move: f0_is_1 ; rewrite coef0_is_1E => /eqP -> ; rewrite oner_eq0.
  apply: (mulrI trp_unit); rewrite divrr //.
  rewrite -[X in X * _]opprK -[X in X * _]add0r -{1}(subrr 1).
  rewrite -addrA -linearB /= -[X in X * _]opprB mulNr -subrX1 opprB /=.
  apply/val_inj => /=.
  rewrite val_exp_tfps modX_eq0 ?subr0 // coefB coef1 eqxx.
  rewrite coef0_is_1E in f0_is_1.
  rewrite nth0_Tfpsp; move/eqP : f0_is_1 ->.
  by rewrite subrr.
Qed.

Section Variable_m_2.
Variable (m : nat).

Local Open Scope tfps_scope.

Lemma pw_cst (f : {tfps K m}) : f ^` ()  = 0 -> {c : K | f = c %:S}.
Proof.
move: f; case: m => [f _| n f]; first by rewrite [f]tfps_is_cst; exists (f`_0).
rewrite deriv_tfpsE; move/eqP ; rewrite -val_eqE /= => /eqP. 
rewrite modp_small => [derivp_eq0|]; last first.
+ rewrite size_polyXn.
  have [->|fN0] := eqVneq f 0; first by rewrite linear0 size_poly0.
  by rewrite (leq_trans (lt_size_deriv _)) // size_tfps. 
+ move: (p_cst char_K_is_zero derivp_eq0) => [c Hc].
  by exists c; apply/val_inj => /=; rewrite modCXn.
Qed.

Lemma pw_eq0 (f : {tfps K m}) : 
    f ^` () = 0 -> {x : K | (val f).[x] = 0} -> f = 0.
Proof.
rewrite deriv_tfpsE /=; move/eqP ; rewrite -val_eqE /=.
have [-> _ _ // |fN0] := eqVneq f 0. 
rewrite modp_small ?size_polyXn ?(leq_trans (lt_size_deriv _)) ?size_tfps //.
  move/eqP => derivp_eq0; move: (p_cst char_K_is_zero derivp_eq0) => [c Hc].
  rewrite Hc; move => [x hx]; rewrite hornerC in hx.
  by apply/val_inj => /=; rewrite Hc hx.
by rewrite (leq_trans (size_tfps _)) //; clear fN0 f; case: m => [|n].
Qed.

Lemma pw_eq (f g : {tfps K m}) : 
               f ^` () = g ^` () -> {x : K | (val f).[x] = (val g).[x]} -> f = g.
Proof.
move => H [x Hx].
apply/eqP ; rewrite -subr_eq0 ; apply/eqP.
apply: pw_eq0; first by rewrite linearB /= H subrr.
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
- rewrite linearB /= deriv_log ?coef0_is_1E ?coef0_exp //.
  rewrite deriv_exp -mulrA divrr ?mulr1 ?subrr // Tfpsp_is_unit.
  by rewrite coef0_exp //; apply: oner_neq0.
- exists 0; rewrite -horner_evalE rmorphB /= !horner_evalE !horner_coef0.
  by rewrite coef0_log sub0r; apply/eqP; rewrite oppr_eq0 -coef0_is_0E.
Qed.

Lemma exp_inj : {in @coef0_is_0 K m &, injective (@exp K m)}.
Proof.
move => p q p0_eq0 q0_eq0 /= H.
have : p^`()%tfps * (Tfpsp m.-1 (exp p)) = q^`()%tfps * (Tfpsp m.-1 (exp p)).
  by rewrite {2}H -!deriv_exp H.
move/mulIr => H_deriv; apply: pw_eq.
+ apply: H_deriv.
  by rewrite Tfpsp_is_unit coef0_exp // oner_neq0.
+ exists 0 ; rewrite !horner_coef0.
  by move: p0_eq0 q0_eq0 ; rewrite !coef0_is_0E => /eqP -> /eqP ->.
Qed.

Lemma log_inj : {in @coef0_is_1 K m &, injective (@log K m)}.
Proof.
move => p q p0_eq0 q0_eq0 /= Hlog.
have H: (p/q) ^` () = 0.
  rewrite deriv_div_tfps; last first.
    by move: q0_eq0; rewrite coef0_is_1E => /eqP ->; apply: oner_neq0.
  have -> : p^`()%tfps * Tfpsp m.-1 q - Tfpsp m.-1 p * q^`()%tfps = 0 ; 
    last by rewrite mul0r.
  apply/eqP; rewrite subr_eq0 [Tfpsp m.-1 p * q^`()%tfps]mulrC.
  rewrite -eq_divr ?Tfpsp_is_unit ; last 2 first.
      by move: p0_eq0; rewrite coef0_is_1E => /eqP ->; apply: oner_neq0.
      by move: q0_eq0; rewrite coef0_is_1E => /eqP ->; apply: oner_neq0.
  by move/(congr1 (@deriv_tfps K m)) : Hlog; rewrite !deriv_log // => ->.
move: (pw_cst H) => [c Hpq].
have Hc : c = 1.
  move/(congr1 (fun x => x * q)): Hpq.
  rewrite mulrAC -mulrA divrr ; last first.
    rewrite unit_tfpsE.
    rewrite coef0_is_1E in q0_eq0.
    by move/eqP: q0_eq0 ->; apply: oner_neq0.
  rewrite mulr1; move/val_eqP => /=.
  rewrite modCXn // modp_small; last first.
    rewrite mul_polyC (leq_ltn_trans (size_scale_leq _ _)) //.
    by rewrite size_polyXn; apply: size_tfps.
  move/eqP; move/(congr1 (fun x => x.[0])).
  rewrite !horner_coef0 coef0M.
  move: p0_eq0; rewrite coef0_is_1E => /eqP ->.
  move: q0_eq0; rewrite coef0_is_1E => /eqP ->.
  by rewrite coefC eqxx mulr1.
move: Hpq; rewrite Hc; move/(congr1 (fun x => x * q)).
rewrite mulrAC -mulrA divrr ; last first.
  rewrite unit_tfpsE.
  rewrite coef0_is_1E in q0_eq0.
  by move/eqP: q0_eq0 ->; apply: oner_neq0.
rewrite mulr1; move/val_eqP => /=.
rewrite modp_mul2 mul1r modp_small //; last first.
  by rewrite size_polyXn; apply: size_tfps.
by move/eqP => H2; apply/val_inj.
Qed.

Lemma cancel_exp_log : {in @coef0_is_1 K m, cancel (@log K m) (@exp K m)}.
Proof.
move => p p0_eq1 /=.
apply: log_inj => //.
  rewrite coef0_is_1E.
  apply/eqP; rewrite coef0_exp //.
  by rewrite coef0_is_0E; apply/eqP; rewrite coef0_log.
by rewrite cancel_log_exp // coef0_is_0E coef0_log.
Qed.

Lemma newton_tfps_map_iota (p : {poly K}) : 
    (newton_tfps m p) ^ iota = newton_tfps m (p ^ iota).
Proof. by rewrite map_Tfpsfp /newton_tfps newton_map_poly. Qed.

Lemma newton_tfps_map_iota2 (p : {poly K}) :
map_tfps iota (newton_tfps m p) = newton_tfps m (p ^ iota).
Proof. by apply/val_inj => /=; rewrite newton_tfps_map_iota mod_tfps. Qed.

End NewtonRepresentation.

Section Newton.

Variables (K : fieldType) (L : closedFieldType) (iota : {injmorphism K -> L}).

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
rewrite mulrBl rmorphD /= map_fracpolyXV mulrC divff; last first.
  by rewrite raddf_eq0 ?polyX_eq0 //; apply: tofrac_inj.
by rewrite rmorphN /= tofrac_scale.
Qed.

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
rewrite (eq_bigr (fun r => 1)) => [|r /eqP ->]; last by rewrite scale0r subr0.
rewrite big1_eq mul1r -scalerA -scaler_prod.
have <- : \prod_(i <- iroots p | i != 0) -(1 : L) = 
                                                  (-1) ^+ ((size p).-1 - mu 0 p).
  rewrite prod_cond_const; congr (_ ^+ _).
  rewrite -size_roots -(count_predC (fun x => x == 0)) addnC.
  have ->: mu 0 p = count (eq_op^~ 0) (iroots p).
    rewrite /mu roots_mu ; last by rewrite map_poly_eq0.
    by apply: eq_in_count.
  rewrite -addnBA // subnn addn0.
  by apply: eq_in_count.
rewrite -scaler_prod ; apply: eq_bigr => r Hr.
by rewrite scalerBr scaleN1r opprB -[r *: (r^-1)%:P]mul_polyC -polyC_mul divff.
Qed.

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

Lemma tofracpolyXV_eq0 (F : fieldType)  (p : {poly F}) : 
    (p%:F \FPo 'X^-1 == 0) = (p == 0).
Proof.
rewrite -revp_eq0 -[RHS](rmorph_eq0 [injmorphism of @tofrac _]) /=.
by rewrite tofrac_revp mulf_eq0 orbC expf_eq0 rmorph_eq0 polyX_eq0 andbF.
Qed.

Lemma fracpolyXV_eq0 (F : fieldType) (f : {fracpoly F}) : 
    (f \FPo 'X^-1 == 0) = (f == 0).
Proof.
have [[p q] /= -> /andP [a_neq0 cpq]] := fracpolyE f.
rewrite comp_frac_frac // !mulf_eq0 !invr_eq0.
by rewrite !tofracpolyXV_eq0 !rmorph_eq0.
Qed.

Lemma nocomp_fracpolyXV (F : fieldType) (f : {fracpoly F}) :
    nocomp_fracpoly f 'X^-1 = false.
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
rewrite composed_sum_is_prod //; exact: perm_eq_roots_factors.
Qed.

Local Notation "f ^ g" := (map_tfps g f). 

Lemma iota_newton_tfps (p : {poly K}) (m : nat) :
  newton_tfps m p ^ iota = [tfps j => \sum_(r <- iroots p) r ^+ j].
Proof.
rewrite mapf_Tfpsfp /= newton_roots.
rewrite (big_morph_in (@devsD _) _ (@TfpsfpD _ _) (@Tfpsfp0 _ _)); last 2 first.
- exact: rpred0.
- apply/allP => x /=; move/mapP; rewrite filter_predT; move=> [y hy ->].
  exact: devs_inv1subCX.
apply/eq_tfps => i /=; rewrite coef_poly ltn_ord /=.
rewrite (@big_morph _ _ (fun (x : {tfps L m}) => x`_i) 0 +%R); last 2 first.
- by move => x y; apply: coefD.
- exact: coef0.
by apply: eq_bigr => x _; rewrite geometric_series /= coef_poly ltn_ord.
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

End Newton.

Section Conversion.

Variable (K : fieldType) (L : closedFieldType) (iota : {injmorphism K -> L}). 

Local Notation "f ^ g" := (map_tfps g f).

Hypothesis char_L_is_zero : [char L] =i pred0.

Hint Resolve char_L_is_zero.

Lemma char_K_is_zero : [char K] =i pred0.
Proof. move => x ; by rewrite -(fmorph_char iota). Qed. 

Hint Resolve char_K_is_zero. 

Lemma nth_newton_tfps (p : {poly L}) (m i : nat) : 
  (newton_tfps m p)`_i = if i < m.+1 then
  (\sum_(r <- iroots [injmorphism of idfun] p) r ^+i) else 0.
Proof.
have -> : val (newton_tfps m p) = 
                            map_tfps [injmorphism of (@idfun L)] (newton_tfps m p).
  by rewrite -map_poly_tfps map_poly_id.
by rewrite iota_newton_tfps //= coef_poly.
Qed.

Lemma iroots_idfun (p : {poly L}) : 
  iroots [injmorphism of (@idfun L)] p = roots p.
Proof. by rewrite /iroots map_poly_idfun. Qed.

Lemma iroots_composed_product (p q : {poly K}) :
   iroots [injmorphism of @idfun L] (composed_product iota p q) 
                         =p [seq s*t | s <- iroots iota p, t <- iroots iota q].
Proof. rewrite iroots_idfun; exact: roots_composed_product. Qed.

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
elim: r1; first by rewrite big_nil; apply: big_nil.
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
have [q_eq0 | q_neq0] := eqVneq q 0.  
  rewrite q_eq0 newton_tfps0 hmul_tfpsr0 rmorph0 composed_productp0.
  exact: newton_tfps0.
have -> : newton_tfps m (composed_product iota p q) =
    newton_tfps m (composed_product iota p q) ^ [rmorphism of (@idfun L)].
  by rewrite (@map_powerseries_idfun _ _).
rewrite (@map_powerseries_idfun _ _) /=.
rewrite map_hmul !iota_newton_tfps //; apply/eq_tfps => i /=.
rewrite !coef_poly ltn_ord.
rewrite (big_distrl _ _ _) /=.
rewrite nth_newton_tfps ltn_ord.
rewrite (eq_big_perm [seq s * t | s <- iroots iota p, t <- iroots iota q])
                                                                    ; last first.
exact: iroots_composed_product.
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
have [->|m_neq0] := eqVneq m O.
  case:i => [|i]; last by rewrite tfps_nth_default.
  by rewrite coef0_exp ?fact0 ?invr1 // coef0_is_0E coef_Tfpsp coefX.
rewrite /expX /exp coef0_is_0E coef_Tfpsp coefX eqxx /= coef_modXn.
rewrite (eq_bigr (fun i => (nat_of_ord i)`!%:R^-1 *: 
                                              'X ^+ (nat_of_ord i))); last first.
  by move => j _; rewrite modp_small // size_polyX size_polyXn !ltnS lt0n.
by rewrite -(@poly_def _ _ (fun i => i`!%:R^-1))  coef_poly; case: (_ < _).
Qed.

(* can be generalized to (exp f) ^ iota = exp (f ^ iota) *)
Lemma map_iota_expX (m : nat) : expX K m ^ iota = expX L m.
Proof.
rewrite /expX /exp !coef0_is_0E !nth0_Tfpsp !coefX !eqxx -Tfps_map_poly. 
rewrite rmorph_sum; congr Tfpsp; apply: eq_bigr => i _.
rewrite linearZ ; congr (_ *: _).
  by rewrite rmorphV ?rmorph_nat // unitfE natmul_inj // -lt0n fact_gt0.
by rewrite rmorphX /= map_modp map_polyX map_polyXn.
Qed.

Lemma hmul_tfps_p_expX (K' : fieldType) (m : nat ) (p : {tfps K' m}) : 
  hmul_tfps p (expX K' m) = [tfps i => p`_i / i`!%:R].
Proof.
apply/val_inj => /=.
apply/polyP => i.
rewrite !coef_poly nth_expX.
by case: (i < m.+1).
Qed.

Lemma aux_newton_composed_sum (K' : fieldType) (f : {rmorphism K' -> L}) 
  (m : nat) (s t : seq K') (p : {tfps K' m}) : p \in (@coef0_is_0 K' m) ->
  \sum_(w <- [seq u + v | u <- s, v <- t]) (exp (w *: p)) = 
  (\sum_(u <- s) (exp (u *: p))) * (\sum_(v <- t) (exp (v *: p))).
Proof.
move => p0_eq0.
have H : [char K'] =i pred0.
  move => x.
  rewrite -(fmorph_char f).
  by move: x. (* strange *)
rewrite eq_big_allpairs /=.
have -> : \sum_(i <- s) \sum_(j <- t) exp ((i + j) *: p) =
   \sum_(i <- s) \sum_(j <- t) (exp (i *: p)) * (exp (j *: p)).
  apply: eq_bigr => i _.
  apply: eq_bigr => j _.
  rewrite scalerDl exp_is_morphism // ; rewrite -mulr_algr mulrC.
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
rewrite exp_coef0_is_0; last first.
  by rewrite coef0_is_0E coef_modXn coefZ nth0_Tfpsp coefX /= mulr0. 
rewrite rmorph_sum /=.
rewrite (@big_morph _ _ (fun (x : {tfps L m.+1}) => val x) 0 +%R) //=. 
apply: eq_big => //= i _.
rewrite ['X %% _]modp_small ?size_polyX ?size_polyXn //.
rewrite modp_scalel ['X %% _]modp_small ?size_polyX ?size_polyXn //.
rewrite modp_scalel modp_small; last first.
  rewrite size_polyXn exprZn (leq_ltn_trans (size_scale_leq _ _)) //.
  by rewrite size_polyXn ltnS.
by rewrite mulrC -raddfMn polyC_inv mul_polyC.
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
  rewrite !expX0; apply/val_inj => /=.
  rewrite expr1 map_modp map_polyX rmorphM !poly_def.
  rewrite !big_ord_recr !big_ord0 !Monoid.simpm.
  rewrite !expr0 !coefC eqxx !mulr1. 
  rewrite !(newton_tfps_coef0 [injmorphism of (@idfun L)]) //.
  rewrite !(newton_tfps_coef0 iota) //=.
  rewrite size_composed_sum // natrM !linearZ /=.
  rewrite rmorph1 !rmorph_nat mulr_algr scalerA mulrC expr1 modp_mod.
  rewrite modp_small // size_polyX (leq_ltn_trans (size_scale_leq _ _)) //.
  rewrite size_polyC.
  exact: leq_b1.
rewrite rmorphM /= !map_hmul map_iota_expX !newton_tfps_map_iota2.
rewrite !sum_exp_kX. 
rewrite (eq_big_perm [seq s + t | s <- iroots iota p, t <- iroots iota q]) /= ;
  last exact: iroots_composed_sum.
rewrite !iroots_idfun.
apply: (aux_newton_composed_sum [rmorphism of @idfun L]).
by rewrite coef0_is_0E nth0_Tfpsp coefX [in X in X == _]eq_sym. 
Qed.

Fact deriv_rev_over_rev_dev (p : {poly K}) :
  devs ((((revp p) ^`())%:F / ((revp p)%:F)) ^^^ iota).
Proof.
have [-> | p_neq0] := eqVneq p 0.
  by rewrite revp0 deriv0 tofrac0 mul0r rmorph0 devs0.
rewrite /devs -(@rmorph0 _ _ iota) fppole_map (contra (@devs_frac _ _ _)) //.
by rewrite coef0_revp lead_coef_eq0.
Qed.

Fact deriv_rev_over_rev_dev2 (K' : fieldType) (p : {poly K'}) :
  devs (((revp p) ^`())%:F / ((revp p)%:F)).
Proof.
have [-> | p_neq0] := eqVneq p 0.
  by rewrite revp0 deriv0 tofrac0 mul0r devs0.
by rewrite /devs (contra (@devs_frac _ _ _)) // coef0_revp lead_coef_eq0.
Qed.

Fact aux_conversion1 (p : {poly K}) : ~~ (root p 0) ->
   ((revp p)^`() // revp p) ^^^ iota  = 
  - \sum_(i <- iroots iota p) i%:FP * (1 - i *: 'X)%:F^-1.
Proof.
move => zeroNroot.
rewrite deriv_p_over_p; last by rewrite revp_eq0 pneq0. 
 rewrite (eq_big_perm [seq x^-1 | x <- iroots iota p]) ; 
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
  Tfpsfp m (((revp p)^`() // revp p) ^^^ iota) = 
  - [tfps i => \sum_(r <- iroots iota p) r ^+i.+1].
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
apply/eq_tfps => i /=; rewrite coef_poly ltn_ord.
rewrite (@big_morph _ _ (fun (x : {tfps L m}) => x`_i) 0 +%R); last 2 first.
- by move => x y; apply: coefD.
- exact: coef0.
apply: eq_bigr => x _; rewrite TfpsfpM -?topredE /= ; last 2 first.
- by rewrite /devs fpole_tofrac.
- exact: devs_inv1subCX.
rewrite coef_modXn ltn_ord geometric_series Tfpsfp_tofrac /=.
by rewrite modCXn // mul_polyC coefZ coef_poly ltn_ord -exprS.
Qed.

Fact aux_conversion3 (p : {poly K}) : 
((revp p)^`() // revp p) ^^^ iota = 
(revp (map_poly iota p))^`() // revp (map_poly iota p).
Proof. by rewrite fracpoly_iota_div !map_fracE /= -deriv_map !revp_map. Qed.

End Conversion.

Section MoreConversion.

Variables (K : fieldType) (L : closedFieldType) (iota : {injmorphism K -> L}).
Variable (m' : nat).
Let m := m'.+1.

Hypothesis char_L_is_zero : [char L] =i pred0.

Hint Resolve char_L_is_zero.
Hint Resolve (char_K_is_zero iota char_L_is_zero).

Fact aux_conversion4 (p : {poly K}) : ~~ root p 0 ->
  Tfpsfp m' ((revp p)^`() // revp p)
  = divfX (((size p).-1)%:R%:S - (newton_tfps m p)).
Proof.
move => zeroNroot; apply: (@map_tfps_injective _ _ m' iota).
rewrite mapf_Tfpsfp aux_conversion2 // (@map_tfps_divfX _ _ iota m).
rewrite divfXE; last first.
  rewrite coef0_is_0E -map_poly_tfps coef_map coefB nth0_Tfpsp //.
  by rewrite (newton_tfps_coef0 iota) // coefC /= subrr rmorph0.
apply/eq_tfps => i.
rewrite coefN !coef_poly ltn_ord rmorphB coefB [X in X`_i.+1]/=.
rewrite [X in val X]/=  newton_tfps_map_iota2 nth_newton_tfps //.
rewrite ltnS ltn_ord map_modp map_polyXn modp_mod modp_small; last first.
  by rewrite size_map_poly size_polyC size_polyXn (leq_ltn_trans (leq_b1 _)).
by rewrite coef_map coefC /= rmorph0 sub0r /iroots map_poly_id.
Qed.

Lemma exp_prim_derivp_over_p (s : {tfps K m}) :
  s \in (@coef0_is_1 K m) ->
  s = exp (prim_tfps ((s^`()%tfps) / (Tfpsp m' s)))%tfps.
Proof.
move => s0_eq1; apply: log_inj => //.
  by rewrite coef0_is_1E coef0_exp // coef0_is_0E coef0_prim_tfps.
rewrite cancel_log_exp // ?coef0_is_0E ?coef0_prim_tfps //.
apply: pw_eq => //; last first.
  by exists 0; rewrite !horner_coef0 coef0_log // coef0_prim_tfps.
by rewrite deriv_log // prim_tfpsK.
Qed.

Definition newton_inv (p : {tfps K m}) : {poly K} := 
  revp (exp (prim_tfps (divfX ((p`_0)%:S - p)))).

Lemma newton_tfpsK (p : {poly K}) :
  size p <= m.+1 ->  ~~ (root p 0) -> p \is monic ->
  newton_inv (newton_tfps m p) = p.
Proof.
move => sp_lt_Sm Nrootp0 p_monic; rewrite /newton_inv.
apply: (canLR_in (@revp_involutive _)).
  by rewrite qualifE -horner_coef0.
have -> : revp p = Tfpsp m (revp p).
  apply: val_inj => /=; rewrite modp_small //= size_polyXn ltnS.
  by rewrite (leq_trans (size_revp_leq _)).
rewrite [Tfpsp _ _ in RHS]exp_prim_derivp_over_p; last first.
  by rewrite coef0_is_1E nth0_Tfpsp coef0_revp -monicE.
congr (exp (prim_tfps _)).
rewrite (newton_tfps_coef0 iota) // -aux_conversion4 //=.
rewrite modp_small; last first.
  by rewrite size_polyXn size_revp (leq_ltn_trans (leq_subr _ _)).
rewrite Tfpsfp_frac; last first.
  by rewrite coef0_revp; move/monicP : p_monic ->; apply: oner_neq0.
congr (_ / _).
rewrite deriv_tfpsE /= modp_small // size_polyXn size_revp.
by rewrite (leq_ltn_trans (leq_subr _ _)).
Qed.

End MoreConversion.
 