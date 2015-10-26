(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  some doc here                                                            *)
(*****************************************************************************)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp Require Import div tuple finfun bigop finset fingroup perm ssralg poly. 
From mathcomp Require Import polydiv mxpoly binomial bigop ssralg finalg zmodp. 
From mathcomp Require Import matrix mxalgebra polyXY ring_quotient.
From Newtonsums Require Import auxresults fraction polydec revpoly.

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

Local Notation "p ^ f" := (map_poly f p).

Section TruncatedPowerSerie.

Variables (K : fieldType) (n : nat).

Structure powerseries := Powerseries
{
  truncation :> {poly K};
  _ :  size truncation <= n.+1
}.

Canonical powerseries_subType := [subType for truncation].
Definition powerseries_eqMixin := [eqMixin of powerseries by <:].
Canonical powerseries_eqType := EqType powerseries powerseries_eqMixin.
Definition powerseries_choiceMixin := [choiceMixin of powerseries by <:].
Canonical powerseries_choiceType := 
  ChoiceType powerseries powerseries_choiceMixin.

Fact truncationP (p : powerseries) : size p <= n.+1.
Proof. by case: p. Qed.

Hint Resolve truncationP.

Fact truncation_powerseries (p : powerseries) :
  truncation p = val p.
Proof. by apply: val_inj. Qed.

(* zmodType structure *)

Fact constP (c : K) : size (c %:P) <= n.+1.
Proof. rewrite size_polyC; apply: (leq_trans (leq_b1 _)); exact: ltn0Sn. Qed.

Fact zeroP : size (0 : {poly K}) <= n.+1.
Proof. by rewrite size_poly0. Qed.

Definition powerzero := Powerseries zeroP.

Lemma poweradd_proof (p1 p2 : powerseries) : 
  size ((p1 : {poly _}) + p2) <= n.+1.
(* TASSI: can't we declare a Zmodule for powerseries by <: ? *)
Proof. by rewrite (leq_trans (size_add _ _)) // geq_max; apply/andP;split. Qed.

Definition poweradd (p1 p2 : powerseries):= Powerseries (poweradd_proof p1 p2).

Lemma poweropp_proof (p : powerseries) : size (- (p : {poly K})) <= n.+1.
Proof. by rewrite size_opp. Qed.

Definition poweropp (p : powerseries) := Powerseries (poweropp_proof p).

Fact poweraddA : associative poweradd.
Proof. by move => p1 p2 p3; apply: val_inj; exact: addrA. Qed.

Fact poweraddC : commutative poweradd.
Proof. by move => p1 p2; apply: val_inj; exact: addrC. Qed.

Fact poweradd0x : left_id powerzero poweradd.
Proof. by move => p; apply: val_inj; exact: add0r. Qed.

Fact poweraddK : left_inverse powerzero poweropp poweradd.
Proof. by move => p; apply: val_inj; exact: addNr. Qed.

Definition powerseries_zmodMixin := 
                          ZmodMixin poweraddA poweraddC poweradd0x poweraddK.
Canonical powerseries_zmodType := ZmodType powerseries powerseries_zmodMixin.

Lemma pwconst0 : Powerseries (constP 0) = (0 : powerseries).
Proof. by apply: val_inj => /=. Qed.

(* ringType structure *)

Fact powerone_proof : size (1 : {poly K}) <= n.+1.
Proof. by rewrite size_polyC (leq_trans (leq_b1 _)). Qed.

Definition powerone := Powerseries powerone_proof.

Fact leq_modpXn m (p : {poly K}) : size (p %% 'X^m) <= m.
Proof. 
by rewrite -ltnS (leq_trans (ltn_modpN0 _ _)) // -?size_poly_eq0 size_polyXn. 
Qed.

Definition powermul (p1 p2 : powerseries) :=
  Powerseries (leq_modpXn _ ((p1 : {poly _}) * p2)).

Fact powerhadmul_proof (p1 p2 : powerseries) : 
                   size (\poly_(i < n.+1) ((val p1)`_i * (val p2)`_i)) <= n.+1.
Proof. exact: size_poly. Qed.

Definition powerhadmul (p1 p2 : powerseries) := 
  Powerseries (powerhadmul_proof p1 p2).

Local Notation "p1 *h p2" := (powerhadmul p1 p2) (at level 2).

Lemma powerhadmulC : commutative powerhadmul.
Proof.
move => p1 p2 ; apply val_inj => /= ; rewrite -polyP => i.
by case: (i < n.+1) => // ; rewrite !coef_poly mulrC.
Qed.

Lemma powerhadmulA : associative powerhadmul.
Proof.
move => p1 p2 p3 ; apply val_inj => /= ; rewrite -polyP => i.
rewrite !coef_poly ; case: (i < n.+1) => //.
exact: mulrA.
Qed.

Lemma powerhadmul0r (p : powerseries) : 0 *h p = 0.
Proof.
apply val_inj => /= ; rewrite -polyP => i.
rewrite coef_poly coef0 ; case: (i < n.+1) => //.
exact: mul0r.
Qed.

Lemma powerhadmulr0 (p : powerseries) : p *h 0 = 0.
Proof.
apply val_inj => /= ; rewrite -polyP => i.
rewrite coef_poly coef0 ; case: (i < n.+1) => //.
exact: mulr0.
Qed.

Fact left_id_powerone_powermul : left_id powerone powermul.
Proof. 
move => p; apply val_inj; rewrite /= mul1r.
by rewrite modp_small // size_polyXn ltnS.
Qed.

Fact powermulC : commutative powermul.
Proof. by move => p1 p2 ; apply val_inj => /= ; rewrite mulrC. Qed.

Fact left_distributive_powermul : left_distributive powermul poweradd.
Proof. by move => p1 p2 p3; apply val_inj => /= ; rewrite mulrDl modp_add. Qed.

Fact powermulA : associative powermul.
Proof. 
move => p1 p2 p3 ; apply: val_inj.
by rewrite /= [in RHS]mulrC !modp_mul mulrA mulrC.
(*by move=> *; apply: val_inj; 
rewrite /= [in RHS]mulrC !modp_mul mulrA mulrC.*)
Qed. 

Fact powerone_not_zero : powerone != powerzero.
Proof. by rewrite -val_eqE oner_neq0. Qed.

Definition powerseries_ringMixin := ComRingMixin powermulA powermulC
        left_id_powerone_powermul left_distributive_powermul powerone_not_zero.   

Canonical powerseries_ringType := RingType powerseries powerseries_ringMixin.

Canonical powerseries_comRingType := ComRingType powerseries powermulC.

Fact powermul_truncation (p q : powerseries) :
               truncation (p * q) = (truncation p) * (truncation q) %% 'X^n.+1.
Proof. by []. Qed.

Fact truncation_exp (p : powerseries) (m : nat) :
  truncation (p ^+ m) = ((truncation p) ^+ m) %% 'X^n.+1.
Proof.
  elim: m => [ | m iH ].
    by rewrite !expr0 modp_small // size_polyC size_polyXn ltnS (leq_trans (leq_b1 _)).
  by rewrite exprS powermul_truncation iH modp_mul -exprS.
Qed.

Fact truncationaddC (p : powerseries) (c : K) : 
  truncation (p + Powerseries (constP c)) = 
                                         truncation p + Powerseries (constP c).
Proof. exact : val_inj. Qed.

Fact truncationN (p : powerseries) : truncation (- p) = - (truncation p).
Proof. exact : val_inj. Qed.

Fact truncationexp (p : powerseries) (m : nat) :
                         truncation (p ^+m) = (truncation p) ^+m %% 'X ^+ n.+1.
Proof.
elim: m => [/= | m iH].
+ by rewrite expr0 modp_small //= size_polyXn ltnS constP.
+ by rewrite exprS powermul_truncation iH modp_mul -exprS.
Qed.

Fact leq_size_mul (R : idomainType) (p q : {poly R}) :
  q != 0 -> size p <= size (p * q).
Proof.
move => q_neq0.
have [-> | p_neq0] := eqVneq p 0 ; first by rewrite mul0r.
by rewrite size_mul // -subn1 -addnBA ?size_poly_gt0 // leq_addr.
Qed.

Fact leq_size_pn (R : idomainType)(p : {poly R}) (a b : nat) : 0 < a <= b ->
  size (p ^+ a) <= size (p ^+ b).
Proof.
have [-> | p_neq0] := eqVneq p 0.
case: a=> [//|a]; case: b=> [//|b]; first by rewrite !expr0n !eqn0Ngt !ltn0Sn.
move => /andP [a_neq0 leq_a_b].
by rewrite -(subnKC leq_a_b) exprD leq_size_mul // expf_neq0.
Qed.

Fact modp_p_exp (R : idomainType) (p q : {poly R}) (a b : nat) : 0 < a <= b ->
  (p %% (q ^+ a)) %% (q ^+ b) = p %% (q ^+ a).
Proof.
case: (eqVneq q 0) => [ -> | q_neq0 ].
+ case: b => [ | b _].
- rewrite leqn0 => /andP [_ /eqP ->].
  by rewrite expr0n eqxx modp_mod.
- by rewrite [X in _ %% X]expr0n /= modp0.
+ move => H.
  by rewrite modp_small // (leq_trans _ (leq_size_pn q H)) // 
                                                            ltn_modp expf_neq0. 
Qed.

Fact modp_modp (p u v : {poly K}) : u %| v -> (p %% v) %% u = p %% u.
Proof.
move => dvdp_u_v.
have [ -> | v_neq0 ] := eqVneq v 0 ; first by rewrite modp0.
rewrite (divp_eq p v) modp_addl_mul_small ?ltn_modp //.
by rewrite modp_add [X in X + _]modp_eq0 ?dvdp_mull // add0r.
Qed.

(* comUnitRingType structure *)

Lemma powerseries_coefK (p : powerseries) : \poly_(i < n.+1) p`_i = p.
Proof.
rewrite -[RHS]coefK -polyP => j.
rewrite !coef_poly.
have [ j_lt_size_p | size_p_leq_j ] := ltnP j (size p).
+ by rewrite (leq_trans _ (truncationP p)).
+ by case: (j < n.+1) => // ; rewrite nth_default.
Qed.

Fixpoint coef_inv_rec (p : {poly K}) (m i : nat) : K :=
  match m with
    | O => p`_(locked 0%N) ^-1 
    | S m => if i == 0%N then p`_(locked 0%N) ^-1 
             else - p`_(locked 0%N) ^-1 * \sum_(k < i) p`_(i - k) 
                                        * coef_inv_rec p m k
  end.

Definition coef_inv (p : {poly K}) (i : nat) : K := coef_inv_rec p i i.

Lemma coef_inv_recE (p : {poly K}) (m i : nat) : i <= m -> 
                                             coef_inv_rec p m i = coef_inv p i.
Proof.
rewrite /coef_inv; elim: m {-2}m (leqnn m) i => [ k | m IHm ].
  by rewrite leqn0 => /eqP -> i ; rewrite leqn0 => /eqP ->.
case => [ k i | k ] ; first by rewrite leqn0 => /eqP ->.
rewrite ltnS => le_km [ // | i ] ; rewrite ltnS => le_ik /=.
congr (_ * _) ; apply: eq_bigr => l _.
by rewrite !IHm 1?(leq_trans (leq_ord _)) // (leq_trans le_ik).
Qed.

Lemma coef_inv0 (p: {poly K}) : coef_inv p 0 = p`_0 ^-1.
Proof. by rewrite /coef_inv /= -lock. Qed.

Lemma coef_invS (p: {poly K}) (j : nat) : coef_inv p j.+1 =
                -(p`_O ^-1) * (\sum_(k < j.+1) p`_(j.+1 - k) * (coef_inv p k)).
Proof.
rewrite /coef_inv /= -lock; congr (_ * _) ; apply: eq_bigr => k _.
by rewrite coef_inv_recE // leq_ord.
Qed.

Definition inv_poly (p : {poly K}) (s : nat) := \poly_(i < s) (coef_inv p i).

Definition powerseries_unit : pred powerseries :=
  fun p => ((val p)`_0 \in GRing.unit).

Definition powerseries_inv (p : powerseries) :=
  if p \in powerseries_unit then Powerseries (size_poly _ (coef_inv p)) else p.

Fact nonunit_powerseries_inv : 
  {in [predC powerseries_unit], powerseries_inv =1 id}.
Proof. by move=> p; rewrite inE /powerseries_inv /= => /negPf ->. Qed.

Fact pmodxn1 (p : {poly K}) : p %% 'X^n.+1 = 1 -> p`_0 = 1.
Proof.
(* rewrite [in _ `_0](divp_eq p 'X^n.+1) => ->. *)
rewrite {2}(divp_eq p 'X^n.+1) => ->.
(* move => Epm1; rewrite (divp_eq p 'X^n.+1) {}Epm1. *)
rewrite coefD -!horner_coef0 hornerM_comm ; last exact: mulrC. 
by rewrite hornerXn expr0n -leqn0 ltn0 mulr0 hornerC add0r.
Qed.

Fact coef0M (p q : {poly K}) : (p * q)`_0 = p`_0 * q`_0.
(* Proof. by rewrite coefM big_ord_recl big_ord0 addr0. Qed. *)
Proof. by rewrite -!horner_coef0 hornerM. Qed.

Fact powerseries_unitP p1 p2 : powermul p2 p1 = powerone -> 
  p1 \in powerseries_unit.
Proof.
move/val_eqP/eqP/pmodxn1 ; rewrite coef0M mulrC => Hp0q0.
by apply/unitrPr; exists p2`_0.
Qed.

Fact coef_pmodXn m (p : {poly K}) i : (p %% 'X^m)`_i = 
  if i < m then p`_i else 0.
Proof.
have [lt_i_m|le_m_i] := ltnP i m; last first.
  by rewrite nth_default // (leq_trans (leq_modpXn _ _)).
have /polyP /(_ i) := divp_eq p 'X^m.
by rewrite coefD coefMXn lt_i_m add0r.
Qed.

Fact coefK_mod m (p : {poly K}) : \poly_(i < m) p`_i = p %% 'X^m.
Proof. by apply/polyP => i ; rewrite coef_poly coef_pmodXn. Qed.

Fact poly_modp_small (a b : nat) (E : nat -> K) : a <= b ->
                                \poly_(i < a) E i %% 'X^b =  \poly_(i < a) E i.
Proof.
move => a_leq_b.
by rewrite modp_small // size_polyXn ; apply: (leq_trans (size_poly _ _)).
Qed.

Fact modp_summ (I : Type) (r : seq I) (P : pred I) 
               (F : I -> {poly K}) (p : {poly K}) :
               (\sum_(i <- r | P i) F i) %% p = \sum_(i <- r | P i) (F i %% p).
Proof.
apply: (big_morph (fun x => x %% p)).
+ by move => u v /= ; rewrite modp_add.
+ exact: mod0p.
Qed.

Fact poly_modp (a b : nat) (E : nat -> K) : b <= a ->
  \poly_(i < a) E i %% 'X^b =  \poly_(i < b) E i.
Proof.
move => b_leq_a.
rewrite !poly_def modp_summ /=.
rewrite (eq_bigr (fun i => E (nat_of_ord i) 
       *: ('X^(nat_of_ord i) %% 'X^b))) => [ | i _ ] ; last exact: modp_scalel.
rewrite -(big_mkord predT (fun i => E i *: ('X^i %% _))).
rewrite -(big_mkord predT (fun i => E i *: 'X^i)) /=.
rewrite (big_cat_nat _ _ (fun i => E i *: ('X^i %% _)) _ b_leq_a); last first.
  exact: leq0n.
rewrite big_nat /= (eq_big (fun i => (i < b)) 
                           (fun i => E i *: 'X^i)) => //= [|i Hi] ; last first.
  by rewrite modp_small // !size_polyXn.
rewrite big_nat [X in _ + X](eq_bigr (fun i => 0)) ; last first.
  move => i /andP [Hi _].
  rewrite -(@dvdp_Pexp2l K 'X) ?size_polyX // in Hi.
  by move/modp_eq0P : Hi -> ; rewrite scaler0.
by rewrite big1_eq addr0 [in RHS]big_nat.
Qed.

Fact powerseries_mulVr : 
                {in powerseries_unit, left_inverse 1 powerseries_inv powermul}. 
Proof.
move => p p_unit ; apply: val_inj => /= ; rewrite /powerseries_inv p_unit /=.
rewrite -coefK_mod; apply/polyP => i ; rewrite coef_poly.
have [ i_small | i_big ] := ltnP i n.+1 ; last first.
  by rewrite coefC gtn_eqF // (leq_trans _ i_big).
rewrite coefC ; case: i => [|i] in i_small *.
  by rewrite coef0M coef_poly /= coef_inv0 mulVr.
rewrite coefM big_ord_recr coef_poly i_small subnn.
apply: canLR (addNKr _) _; rewrite addr0.
apply: canLR (mulrVK _) _; rewrite // mulrC mulrN -mulNr.
rewrite coef_invS; congr (_ * _); apply: eq_bigr => j _ /=.
by rewrite mulrC coef_poly (leq_trans _ i_small) 1?leqW.
Qed.

Definition powerseries_comUnitRingMixin := ComUnitRingMixin
  powerseries_mulVr powerseries_unitP nonunit_powerseries_inv.  

Canonical powerseries_unitRingType := 
  UnitRingType powerseries powerseries_comUnitRingMixin.

Lemma powerhadmulr1 (p : powerseries) : p *h 1 = Powerseries (constP p`_0).
Proof.
rewrite -horner_coef0 ; apply: val_inj => /= ; apply/polyP => i.
rewrite coef_poly !coefC ; case: i => [ | i ].
  by rewrite eqxx mulr1 horner_coef0.
by rewrite horner_coef0 ; case: (i.+1 < n.+1) ; rewrite ?mulr0.
Qed.

Lemma powerhadmul1r (p : powerseries) : 1 *h p = Powerseries (constP p`_0).
Proof. by rewrite powerhadmulC powerhadmulr1. Qed.

Canonical powerseries_comUnitRingType := [comUnitRingType of powerseries].

Fact powerseries_unitE p : (p \in GRing.unit) = (p \in powerseries_unit).
Proof. by rewrite (qualifE 0). Qed.

Fact map_powerseries_proof 
  (K' : fieldType) (f : {rmorphism K -> K'}) (p : powerseries) :
  size (p ^ f) <= n.+1.
Proof. by move: p => [p' Hp] /= ; rewrite size_map_poly. Qed.

Definition aux_exponential (p : {poly K}) :=
  if p`_0 == 0 then
  Powerseries (leq_modpXn (n.+1) 
                                  (\sum_(i < n.+1) ((i`! %:R) ^-1) *: (p ^+i)))
  else 0.

Definition aux_logarithm (p : {poly K}) :=
  if p`_0 == 1 then
  Powerseries (leq_modpXn (n.+1) 
                       (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: ((1 - p) ^+i)))
  else 0.

Lemma exponential_proof (p : powerseries) : size (aux_exponential p) <= n.+1.
Proof. by case: (p == 0). Qed.

Lemma logarithm_proof (p : powerseries) : size (aux_logarithm p) <= n.+1.
Proof. by case: (p == 0). Qed.

Definition exponential (p : powerseries) := Powerseries (exponential_proof p).

Definition logarithm (p : powerseries) := Powerseries (logarithm_proof p).

Definition coef0_is_0 := [pred p : powerseries | p`_0 == 0].

Fact c0_is_0_ideal_key : pred_key coef0_is_0. 
Proof. by []. Qed.

Canonical c0_is_0_keyed := KeyedPred c0_is_0_ideal_key.

Fact nth0_powermul (p q : powerseries) : (p * q)`_0 = p`_0 * q`_0.
Proof. by rewrite powermul_truncation coef_pmodXn ltn0Sn coef0M. Qed.

Fact c0_is_0_idealr : idealr_closed coef0_is_0.
Proof.
split => [ | | a p q ].
+ by rewrite inE coefC eqxx.
+ by rewrite inE coefC eqxx oner_eq0.
+ rewrite inE => /eqP p0_eq0 ; rewrite inE => /eqP q0_eq0.
  by rewrite inE coefD q0_eq0 addr0 nth0_powermul p0_eq0 mulr0.
Qed.

Definition c0_is_0_zmod := idealr_closedB c0_is_0_idealr.

Canonical c0_is_0_opprPred := OpprPred c0_is_0_zmod.
Canonical c0_is_0_addrPred := AddrPred c0_is_0_zmod.
Canonical c0_is_0_zmodPred := ZmodPred c0_is_0_zmod.

Definition c0_is_0_ntideal := idealr_closed_nontrivial c0_is_0_idealr.

Canonical coef0_is_0_ideal := MkIdeal c0_is_0_zmodPred c0_is_0_ntideal.

Fact c0_is_0_prime : prime_idealr_closed coef0_is_0.
Proof. by move => x y; rewrite !inE nth0_powermul mulf_eq0. Qed.

Canonical coef0_is_0_pideal := MkPrimeIdeal coef0_is_0_ideal c0_is_0_prime.

Definition coef0_is_1 := [pred p : powerseries | p`_0 == 1].

Lemma coef0_1subp_is_0 (p : powerseries) : 
  p \in coef0_is_1 -> (1 - p) \in coef0_is_0.
Proof.
rewrite !inE -!horner_coef0 -!horner_evalE rmorphB /= !horner_evalE hornerC.
by move/eqP -> ; rewrite subrr.
Qed.

Lemma c0_is_1_unit (p : powerseries) : p \in coef0_is_1 -> p \is a GRing.unit.
Proof. 
rewrite powerseries_unitE inE (qualifE 1) ; move/eqP ->.
exact: unitr1.
Qed.

Lemma mul_c0_is_1_closed : {in coef0_is_1 &, forall p q, p * q \in coef0_is_1}.
Proof.
move => p q /=.
rewrite !inE nth0_powermul.
by move/eqP -> ; move/eqP -> ; rewrite mul1r.
Qed.

Fact nth0_inv (p : powerseries) : (p ^-1)`_0 = (p`_0)^-1.
Proof.
have [p_unit | p_non_unit] := boolP (p \is a GRing.unit).
+ move: p_unit ; rewrite unitrE.
  move/eqP.
  move/(congr1 (fun q => (truncation q)`_0)).
  rewrite nth0_powermul coefC eqxx mulrC => H.
  have p0_neq0 : p`_0 != 0 by move/GRing.Field.intro_unit : H.
  move/(congr1 (fun x => x / p`_0)) : H.
  by rewrite -mulrA divff // mulr1 GRing.div1r.
+ rewrite (GRing.invr_out p_non_unit).
  symmetry ; apply: GRing.invr_out.
  by move: p_non_unit ; rewrite powerseries_unitE (qualifE 0) unitfE.
Qed.

Fact inv_c0_is_1_closed : {in coef0_is_1, forall p, p^-1 \in coef0_is_1}.
Proof.
move => p.
rewrite inE => /eqP p0_is_1.
by rewrite inE nth0_inv p0_is_1 invr1.
Qed.

Fact c0_is_1_div_closed : divr_closed coef0_is_1.
Proof.
split => [ | p q p0_is_1 q0_is_1 ].
+ by rewrite inE coefC eqxx.
+ by rewrite mul_c0_is_1_closed ?inv_c0_is_1_closed.
Qed.

Definition c0_is_1_closedM := GRing.divr_closedM c0_is_1_div_closed.
Definition c0_is_1_closedV := GRing.divr_closedV c0_is_1_div_closed.

Canonical c0_is_1_div_pred := 
                        GRing.Pred.Default.div c0_is_1_closedM c0_is_1_closedV.

Lemma exponential_coef0_is_0 (p : powerseries) :
  p \in coef0_is_0 ->
  exponential p = Powerseries (leq_modpXn (n.+1) 
                           (\sum_(i < n.+1) ((i`! %:R) ^-1) *: ((val p) ^+i))).
Proof.
rewrite inE => p0_eq0.
by apply: val_inj => /= ; rewrite /aux_exponential p0_eq0.
Qed.

Lemma exponential_coef0_isnt_0 (p : powerseries) :
  ~~ (p \in coef0_is_0) -> exponential p = 0.
Proof.
rewrite inE ; move/negbTE => p0_neq0.
by apply: val_inj => /= ; rewrite /aux_exponential p0_neq0.
Qed.

Lemma logarithm_coef0_is_1 (p : powerseries) :
  p \in coef0_is_1 ->
  logarithm p = Powerseries (leq_modpXn (n.+1) 
                (- \sum_(1 <= i < n.+1) ((i %:R) ^-1) *: ((1 - (val p)) ^+i))).
Proof.
rewrite inE ; move => p0_eq1.
by apply: val_inj => /= ; rewrite /aux_logarithm p0_eq1.
Qed.                                                     

Lemma logarithm1 : logarithm 1 = 0.
Proof.
apply: val_inj => /=.
rewrite /aux_logarithm -horner_coef0 hornerC eqxx ; apply: val_inj => /=.
rewrite (eq_bigr (fun i => 0)) => [ | i _ ] ; last first.
  rewrite subrr ; case: i => [ | i ] ; first by rewrite invr0 scale0r. 
  by rewrite expr0n scaler0.
by rewrite big1_eq modp_small oppr0 // size_polyXn size_poly0.
Qed.

Fact modp_exp_eq0 (p : {poly K}) (m : nat) : p`_0 = 0 -> n < m ->
  (p ^+ m) %% 'X^n.+1 = 0.
Proof.
rewrite -horner_coef0 => /polyXsubCP p0_eq0 n_lt_m.
rewrite polyC0 subr0 in p0_eq0.
apply/modp_eq0P.
by rewrite (dvdp_trans (dvdp_exp2l ('X : {poly K}) n_lt_m)) // dvdp_exp2r.
Qed.

Lemma widen_logarithm_coef0_is_1 (p : powerseries) : p \in coef0_is_1 ->
  logarithm p = Powerseries (leq_modpXn (n.+1) 
                (- \sum_(1 <= i < n.+2) ((i %:R) ^-1) *: ((1 - (val p)) ^+i))).
Proof.
move => p0_eq1.
rewrite logarithm_coef0_is_1 // ; apply: val_inj => /=.
rewrite (big_nat_recr n.+1) /= ; last exact: ltn0Sn.
rewrite [RHS]modNp modp_add modp_scalel modp_exp_eq0 ?leqnn // ; last first.
  move: p0_eq1 ; rewrite inE -!horner_coef0 -!horner_evalE rmorphB /=. 
  by rewrite !horner_evalE hornerC horner_coef0 ; move/eqP -> ; rewrite subrr.
by rewrite scaler0 addr0 modNp.
Qed.

Lemma coef0_is_1_unit (p : powerseries): p \in coef0_is_1-> powerseries_unit p.
Proof. by rewrite /powerseries_unit inE=> /eqP ->;rewrite unitfE oner_eq0. Qed.

Fact poweradd_is_coef0_is_0 (p q : powerseries) :
                p \in coef0_is_0 -> q \in coef0_is_0 -> (p + q) \in coef0_is_0.
Proof.
rewrite !inE coefD.
by move/eqP -> ; move/eqP -> ; rewrite add0r.
Qed.

Fact polyXP (p : {poly K}) : reflect (p`_0 = 0) ('X %| p).
Proof. rewrite -['X]subr0 -polyC0 -horner_coef0 ; exact: polyXsubCP. Qed.

Fact modp_mul_piqj (p q : {poly K}) (i j : nat) : p`_0 = 0 -> q`_0 = 0 -> 
  n < i+j -> (p ^+i * q ^+j) %% 'X^n.+1 = 0.
Proof.
move => p0_eq0 q0_eq0 n_lt_addij.
apply/modp_eq0P.
rewrite (dvdp_trans (dvdp_exp2l ('X : {poly K}) n_lt_addij)) // exprD.
by rewrite dvdp_mul // dvdp_exp2r // ; apply/polyXP.
Qed.

Lemma coef0_exponential (p : powerseries) : 
                                    p \in coef0_is_0 -> (exponential p)`_0 = 1.
Proof.
move => p0_eq0.
rewrite exponential_coef0_is_0 // coef_pmodXn ltn0Sn -horner_coef0.
rewrite -horner_evalE rmorph_sum /=.
rewrite (eq_bigr (fun i => ((nat_of_ord i) == 0%N)%:R)) => [ | [i _] _ ] /=.
+ rewrite -(big_mkord predT (fun i => ((i == _)%:R))) big_ltn ; last first.
    exact: ltnS.
  rewrite eqxx /= -natr_sum big_nat_cond.
  rewrite (eq_big (fun i => (0 < i < n.+1)) (fun i => 0%N)) => [ | i | i ].
- by rewrite big1_eq addr0.
- by rewrite andbT.
  by rewrite andbT => /andP [/lt0n_neq0/negbTE -> _].
+ rewrite linearZ /= rmorphX /= horner_evalE horner_coef0.
  move: p0_eq0 ; rewrite inE => /eqP ->.
  rewrite expr0n ; case: i => [ | i'].
- by rewrite fact0 invr1 mul1r.
- by rewrite eqn0Ngt -leqNgt ltn0 mulr0.
Qed.

Lemma coef0_logarithm (p : powerseries) : 
  p \in coef0_is_1 -> (logarithm p)`_0 = 0.
Proof.
move => p0_eq1.
rewrite logarithm_coef0_is_1 // coef_pmodXn ltn0Sn -horner_coef0.
rewrite -horner_evalE rmorphN rmorph_sum /=.
rewrite big_nat_cond (eq_bigr (fun i => (i == 0%N)%:R)). 
+ rewrite -[1%N]add0n big_addn (eq_bigr (fun i => 0)) => [ | i _] ; last first.
    by rewrite addn1.
  by rewrite big1_eq oppr0.
+ move => i /andP [/andP [Hi _] _] /=.
  rewrite linearZ rmorphX rmorphB /= !horner_evalE hornerC horner_coef0.
  move: p0_eq1 ; rewrite inE => /eqP ->.
  by rewrite subrr expr0n eqn0Ngt Hi /= mulr0.
Qed.

Lemma exponential_coef0_is_1 (p : powerseries) : 
  p \in coef0_is_0 -> (exponential p) \in coef0_is_1.
Proof. by move => H ; rewrite inE coef0_exponential. Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Fact natmul_inj (m : nat) : (m%:R == 0 :> K) = (m == 0%N).
Proof. by move/(charf0P K)/(_ m) : char_K_is_zero. Qed.

Lemma natmul_eq (R : idomainType) (a b : nat) : 
                   [char R] =i pred0 -> a%:R = GRing.natmul (1 : R) b -> a = b.
Proof.
move => H_char ; move/eqP.
have [ a_lt_b | b_lt_a | -> ] := ltngtP a b ; last by [].
+ rewrite eq_sym -subr_eq0 -natrB ; last by apply: ltnW.
  move/(charf0P R)/(_ (b-a)%N) : H_char ->.
  by rewrite subn_eq0 leqNgt a_lt_b.
+ rewrite -subr_eq0 -natrB ; last by apply: ltnW.
  move/(charf0P R)/(_ (a-b)%N) : H_char ->.
  by rewrite subn_eq0 leqNgt b_lt_a.
Qed.

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
  by rewrite index_translation ; symmetry ; rewrite /G ; reflexivity.
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
rewrite (big_split_ord _ _ (fun i => i < m') 
                           (fun i => \big[op/idx]_(j < m | i + j < m') F i _)).
rewrite [X in op _ X]big1_seq => [ | i ] ; last first.
  rewrite -leqNgt => /andP [leq_m'_i _].
  apply: big_pred0 => j.
  by apply/negbTE ; rewrite -leqNgt (leq_trans leq_m'_i) // leq_addr.
rewrite Monoid.Theory.simpm.
rewrite -(big_ord_widen m 
                      (fun i => (\big[op/idx]_(j < m | i + j < m') F i _))) //.
rewrite (eq_bigr (fun i => 
          \big[op/idx]_(j < m' | (nat_of_ord i) + j < m') F (nat_of_ord i) j)).
  by apply: aux_triangular_index_bigop.
move => i _.
rewrite (eq_bigl (fun j => (i + (nat_of_ord j) < m') && ((nat_of_ord j) < m')) 
                 (fun j => F i (nat_of_ord j))) ; last first.
+ move => j /=. 
  symmetry ; rewrite andb_idr // -ltn_subRL => leq_addij_m'.
  by rewrite (leq_trans leq_addij_m') // leq_subr.
+ by rewrite (big_ord_widen_cond m (fun j => _ + j < _) (fun j => F _ j)).
Qed.

Lemma exponential_is_morphism : 
                {in coef0_is_0 &, {morph exponential : p q / p + q >-> p * q}}.
Proof.
move => p q p0_eq0 q0_eq0 /=.
rewrite exponential_coef0_is_0 ?poweradd_is_coef0_is_0 //.
rewrite exponential_coef0_is_0 ?poweradd_is_coef0_is_0 //.
rewrite !exponential_coef0_is_0 //.
apply: val_inj => /= ; apply: val_inj => /=.
rewrite modp_mul mulrC modp_mul -mulrC.
rewrite !inE -!horner_coef0 in p0_eq0 q0_eq0.
move/eqP: q0_eq0 ; move/eqP : p0_eq0.
move: p q => [p pr] [q qr] /=.
rewrite !horner_coef0 => p0_eq0 q0_eq0.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in i'`!%:R^-1 *: 
         (\sum_(j < i'.+1) p ^+ (i' - j) * q ^+ j *+ 'C(i', j)))) ; last first.
  by move => i _ ; rewrite exprDn.
rewrite (big_distrl _ _ _) /=.
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in (\sum_(j < i' .+1) 
        ((j`! * (i' -j)`!)%:R) ^-1 *: (p ^+ (i' - j) * q ^+ j)))) ; last first.
  move => [i i_lt_Sn] _ /=.
  rewrite scaler_sumr ; apply: eq_bigr => [ /= [j j_lt_Si]] _ /=.
  rewrite -mulrnAl scalerAl -scaler_nat scalerA -scalerAl ; congr(_ *: _).
  have factr_neq0 k : k`!%:R != 0 :> K 
                              by rewrite (proj1 (charf0P _)) // -lt0n fact_gt0.
  apply: (mulfI (factr_neq0 i)) ; rewrite mulVKf //.
  have den_neq0 :  (j`! * (i - j)`!)%:R != 0 :> K by rewrite natrM mulf_neq0.
  by apply: (mulIf den_neq0) ; rewrite mulfVK // -natrM bin_fact.
rewrite [in RHS](eq_bigr (fun i => let i' := (nat_of_ord i) in (\sum_(j < n.+1) 
                    ((i'`! * j`!)%:R^-1) *: (p ^+ i' * q ^+ j)))) ; last first.
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
  (i`! * j`!)%:R^-1 *: (p ^+ i * q ^+ j)) %% 'X^n.+1 =
  (\sum_(i < n.+1) \sum_(j < n.+1 | i+j <= n) 
  (i`! * j`!)%:R^-1 *: (p ^+ i * q ^+ j)) %% 'X^n.+1.
  rewrite !modp_summ ; apply: eq_bigr => [[i i_lt_Sn]] _ /=.
  rewrite !modp_summ.
  rewrite (big_split_ord _ _ (fun j => i + j <= n) 
            (fun x => ((i`! * x`!)%:R^-1 *: (p ^+ i * q ^+ x)) %% 'X^n.+1)) /=.
  rewrite -[RHS]addr0 ; congr (_ + _).
  rewrite -(big_mkord (fun j => ~~ (i + j <= n)) 
               (fun j => ((i`! * j`!)%:R^-1 *: (p ^+ i * q ^+ j)) %% 'X^n.+1)).
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
        i' + j < n.+1) (i'`! * j`!)%:R^-1 *: (p ^+ i' * q ^+ j))) ; last first.
  move => i _.
  by apply: eq_bigr. 
rewrite (eq_bigr (fun i => let i' := (nat_of_ord i) in \sum_(j < i'.+1) 
           (j`! * (i' - j)`!)%:R^-1 *: (p ^+ j * q ^+ (i' - j)))) ; last first.
  move => i _.
  rewrite /= (big_ord_rev _ i.+1 predT 
             (fun j => (j`! * (i - j)`!)%:R^-1 *: (p ^+ (i - j) * q ^+ j))) /=.
  apply: eq_bigr => j _.
  by rewrite !subSS subnBA -1?ltnS // !addKn mulnC.
by rewrite (triangular_index_bigop _ 
                      (fun i j => (i`! * j`!)%:R^-1 *: (p ^+ i * q ^+ j))) /= ; 
  last exact: ltnSn.
Qed.

(* unitAlgType structure *)

Fact scale_powerseries_proof (c : K) (p : powerseries) : 
  size (c *: (val p)) <= n.+1.
Proof. exact: (leq_trans (size_scale_leq _ _) _). Qed.

Definition scale_powerseries (c : K) (p : powerseries) := 
                                     Powerseries (scale_powerseries_proof c p).

Fact scale_powerseriesA a b (p : powerseries) : 
     scale_powerseries a (scale_powerseries b p) = scale_powerseries (a * b) p.
Proof. by apply: val_inj => /= ; rewrite scalerA. Qed.

Fact scale_1powerseries : left_id (1 : K) scale_powerseries.
Proof. by move => x ; apply: val_inj => /= ; rewrite scale1r. Qed.

Fact scale_powerseriesDr (a : K) : {morph scale_powerseries a : p q / p + q}.
Proof. by move => p q ; apply: val_inj => /= ; rewrite scalerDr. Qed.

Fact scale_powerseriesDl p: {morph scale_powerseries^~ p : a b / a + b}.
Proof. by move => a b ; apply: val_inj => /= ; rewrite scalerDl. Qed.

Fact scale_powerseriesAl (a : K) (p q : powerseries) : 
                       scale_powerseries a (p * q) = scale_powerseries a p * q.
Proof. by apply: val_inj => /= ; rewrite -scalerAl modp_scalel. Qed.

Definition powerseries_lmodMixin :=
                             LmodMixin scale_powerseriesA scale_1powerseries 
                                       scale_powerseriesDr scale_powerseriesDl.

Canonical powerseries_lmodType :=
                      Eval hnf in LmodType K powerseries powerseries_lmodMixin.

Canonical powerseries_lalgType :=
                        Eval hnf in LalgType K powerseries scale_powerseriesAl.

Canonical powerseries_algType := CommAlgType K powerseries.

Canonical powerseries_unitAlgType :=Eval hnf in [unitAlgType K of powerseries].

Fact leqnaddsubn (m : nat) : m <= (m.-1).+1.
Proof. case: m => /= [ // | m] ; exact: ltnSn. Qed.

Lemma dvdp_scaler2 (R : idomainType) (c : R) (a b : {poly R}): 
                                                     (a %| b) -> (a %| c *: b).
Proof.
have [ -> | c_neq0] := eqVneq c 0.
+ by rewrite scale0r dvdp0.
+ by rewrite dvdp_scaler.
Qed.

Fact big_distrr_nat (R : Type) (zero : R) (times : Monoid.mul_law zero)
  (plus : Monoid.add_law zero times) (a b : nat) (x : R)
  (P : pred nat) (F : nat -> R) :
  \big[plus/zero]_(a <= i < b | P i) times x (F i) = 
  times x (\big[plus/zero]_(a <= i < b | P i) F i).
Proof. by rewrite -[a]add0n !big_addn !big_mkord big_distrr. Qed.

Lemma powerseries_unitE2 (p : powerseries) : 
                                      (p \is a GRing.unit) = ((val p)`_0 != 0).
Proof. by rewrite powerseries_unitE (qualifE 1) unitfE. Qed.

Fact powerseries_of_poly_proof (m : nat) (p : {poly K}) :
                                m <= n -> size (\poly_(j < m.+1) p`_j) <= n.+1.
Proof. by move => m_leq_n; rewrite (leq_trans (size_poly _ _)) // ltnS. Qed.

Definition powerseries_of_poly (m : nat) (p : {poly K}) (pr : m <= n) :=
            Powerseries (powerseries_of_poly_proof (\poly_(j < m.+1) p`_j) pr).

End TruncatedPowerSerie.

Hint Resolve truncationP.

Fact forget_precision_proof (K : fieldType) (m : nat) (p : powerseries K m) :
  size p <= m.+2.
Proof. by apply: (leq_trans (truncationP _)). Qed.

Definition forget_precision (K : fieldType) (m : nat) (p : powerseries K m) :=
                                        Powerseries (forget_precision_proof p).

Fact proof_divX (K : fieldType) (m : nat) (p : powerseries K m) :
  size (p %/ 'X) <= m.-1.+1.
Proof.
move: p ; case: m => [p | m p] /=. 
  by rewrite (leq_trans (leq_divp _ _)) // truncationP.
have [ -> | p_neq0 ] := eqVneq p 0 ; first by rewrite div0p size_poly0.
rewrite -ltnS (@leq_trans (size p) _ _ _ _) //.
by rewrite ltn_divpl ?size_mul ?polyX_eq0 // size_polyX addn2.
Qed.

Definition divX (K : fieldType) (m : nat) (p : powerseries K m) :=  
  Powerseries (proof_divX p).

Section MapPowerseries.

Variables (K K' : fieldType) (n : nat) (f : {rmorphism K -> K'}).

Definition map_powerseries (p : powerseries K n) := 
  Powerseries (map_powerseries_proof f p).

Lemma map_powerseriesM (p q : powerseries K n) :
           map_powerseries (p * q) = (map_powerseries p) * (map_powerseries q).
Proof.
apply: val_inj => /=.
by rewrite -rmorphM map_modp map_polyXn.
Qed.

Lemma map_powerseries1 : map_powerseries 1 = 1.
Proof. by apply: val_inj => /= ; rewrite rmorph1. Qed.

Fact map_powerseries_is_additive : additive map_powerseries.
Proof. 
move => x y.
by apply: val_inj => /= ; rewrite rmorphB.
Qed.

Canonical map_powerseries_additive := Additive map_powerseries_is_additive.

Fact map_powerseries_is_multiplicative : multiplicative map_powerseries.
Proof. 
split => [ x y | ].
+ exact: map_powerseriesM.
+ exact: map_powerseries1.
Qed.

Canonical map_powerseries_rmorphism := 
                                AddRMorphism map_powerseries_is_multiplicative.

Lemma map_powerseriesZ (c : K) (p : powerseries K n) : 
                    (map_powerseries (c *: p)) =  (f c) *: (map_powerseries p).
Proof. by apply: val_inj => /= ; rewrite linearZ. Qed.

Local Notation "c %:S" := (Powerseries (constP n c)) (at level 2).

Lemma mul_cst (c1 c2 : K) : (c1 * c2) %:S = (c1 %:S) * (c2 %:S).
Proof. 
apply: val_inj => /=.
rewrite polyC_mul modp_small // size_polyXn -polyC_mul size_polyC. 
by apply: (leq_trans (leq_b1 _)).
Qed.

Lemma map_powerseriesC (c : K) : map_powerseries (c %:S) = (f c) %:S.
Proof. by apply: val_inj => /= ; rewrite map_polyC. Qed.

Canonical map_powerseries_linear := let R := (powerseries K n) in
       AddLinear (map_powerseriesZ : scalable_for (f \; *:%R) map_powerseries).

Canonical map_powerseries_lrmorphism := [lrmorphism of map_powerseries].

Local Notation "p ^f" := (map_powerseries p).
Local Notation "p *h q" := (powerhadmul p q) (at level 2).
  
Lemma map_powerseries_mul (p q : powerseries K n) : 
                                                (p *h q) ^f = (p ^f) *h (q ^f).
Proof.
apply: val_inj => /= ; rewrite -polyP => i.
rewrite coef_map 2!coef_poly ; case: (i < n.+1) ; last exact: rmorph0.
by rewrite /= rmorphM !coef_map. 
Qed.

Lemma map_powerseries_injective : injective map_powerseries.
Proof.
move => x y.
move/val_eqP => /= /eqP H.
move: (map_poly_inj f H) => eq_x_y.
by apply: val_inj.
Qed.

End MapPowerseries.

Lemma pw_is_cst (K : fieldType) (p : powerseries K 0%N) : 
                                           p = (Powerseries (constP 0%N p`_0)).
Proof.
rewrite -horner_coef0 ; apply: val_inj => /=.
by rewrite (size1_polyC (truncationP _)) hornerC.
Qed.

Lemma map_powerseries_divX (K K' : fieldType) (f : {rmorphism K -> K'}) 
  (m : nat) (p : powerseries K m) : 
  map_powerseries f (divX p) = divX (map_powerseries f p).
Proof. by apply: val_inj => /= ; rewrite map_divp map_polyX. Qed.

Section Truncation.

Variables (K : fieldType) (n : nat).

Fact truncnleqn (p : {poly K}) : size (p %% 'X^n.+1) <= n.+1.
Proof. 
by rewrite -ltnS (leq_trans (ltn_modpN0 _ _)) // -?size_poly_eq0 size_polyXn. 
Qed.

Definition truncate (p : {poly K}) := Powerseries (truncnleqn p).

Fact sizeC_leqn (c : K) : size c%:P <= n.+1.
Proof. by rewrite size_polyC ; apply: (leq_trans (leq_b1 _)). Qed.

Fact truncateC (c : K) : truncate c%:P = Powerseries (sizeC_leqn c).
Proof.
apply: val_inj => /=.
rewrite modp_small // size_polyC size_polyXn.
by apply: (leq_trans (leq_b1 _)).
Qed.

Fact truncate0 : truncate 0 = 0.
Proof. apply: val_inj ; exact: mod0p. Qed.

Fact truncate1 : truncate 1 = 1.
Proof. by rewrite truncateC ; apply: val_inj. Qed.

Fact truncate_is_additive : additive truncate.
Proof. by move => p q ; apply: val_inj => /= ; rewrite modp_add modNp. Qed.

Canonical truncate_additive := Additive truncate_is_additive.

Lemma truncate_is_multiplicative: multiplicative truncate.
Proof.
split => [p q | ].
+ by apply: val_inj => /= ; rewrite modp_mul [in RHS]mulrC modp_mul mulrC.
+ exact: truncate1.
Qed.

Canonical truncate_rmorphism := AddRMorphism truncate_is_multiplicative.

Lemma truncateM (p q : {poly K}) : 
                                truncate (p * q) = (truncate p) * (truncate q).
Proof. by rewrite rmorphM. Qed.

Lemma truncateZ (c : K) (p : {poly K}): (truncate (c *: p))=  c *:(truncate p).
Proof. by apply: val_inj => /= ; rewrite modp_scalel. Qed.

Canonical truncate_linear := AddLinear truncateZ.

Canonical truncate_lrmorphism := [lrmorphism of truncate].

Lemma nth0_truncate (p : {poly K}) : (truncate p)`_0 = p`_0.
Proof. by rewrite coef_pmodXn ltn0Sn. Qed.

Lemma p0_is_0 (m : nat) (p : powerseries K m) : 
                ((truncate p) \in (coef0_is_0 K n)) = (p \in (coef0_is_0 K m)).
Proof. by rewrite !inE nth0_truncate. Qed.

Lemma truncate_is_unit (p : {poly K}) :
                                 ((truncate p) \is a GRing.unit) = (p`_0 != 0).
Proof. by rewrite powerseries_unitE2 nth0_truncate. Qed.

Fact truncate_poly_proof (E : nat -> K) : size (\poly_(i < n.+1) E i) <= n.+1.
Proof. exact: size_poly. Qed.

Lemma truncate_poly (m : nat) (E : nat -> K) : n < m ->
         truncate (\poly_(i < m.+1) E i) = Powerseries (truncate_poly_proof E).
Proof.
move => m_lt_n. 
by apply: val_inj => /= ; rewrite poly_modp // ltnS ltnW.
Qed. 

Lemma truncateE (p : {poly K}) : p %% 'X^ n.+1 = truncate p.
Proof. by apply: val_inj => /=. Qed.
  
Definition devs_in_pw (x : {fracpoly K}) := ((projT1 (fracpolyE x)).2)`_0 != 0.

Fact nth0_eq_nth0 (p q : {poly K}) : p %= q -> (p`_0 != 0) = (q`_0 != 0).
Proof.
move => p_eqp_q.
rewrite -!horner_coef0 ; apply: negb_inj ; rewrite !negbK.
apply/(sameP eqP).
apply/(equivP eqP).
apply: (rwP2 (polyXsubCP _ _)).
apply: (aux_equivb (polyXsubCP _ _)).
by rewrite !polyC0 !subr0 ; apply: eqp_dvdr.
Qed. 

Lemma devs_in_pwE (p q : {poly K}) :
  q != 0 -> coprimep p q -> 
  devs_in_pw (p %:F / q %:F) = (q.[0] != 0).
Proof.
move => q_neq0 coprime_p_q.
rewrite /devs_in_pw -horner_coef0.
move: (associate_denom_fracpolyE q_neq0 coprime_p_q).
move: (fracpolyE (p %:F / q %:F))
                             => [[u v] /= Hx] /andP [v_neq0 coprime_u_v] eq_qv.
by rewrite -!rootE (eqp_root eq_qv).
Qed. 

Local Notation "x %:FP" := (EvalRatFrac.to_fracpoly x).

Lemma devs_in_pw_tofrac (p : {poly K}) :
                                             (devs_in_pw (p %:F)).
Proof.
rewrite -[p]mulr1 -invr1 rmorph_div /= ; last first.
  by rewrite poly_unitE size_polyC -horner_coef0 hornerC unitfE !oner_neq0.
by rewrite devs_in_pwE -?horner_coef0 ?hornerC ?oner_neq0 // coprimep1.
Qed.

Lemma devs_in_pw_to_fracpoly (c : K) :
                                             (devs_in_pw (c%:FP)).
Proof. exact: devs_in_pw_tofrac. Qed.

Lemma devs_in_pw_inv_p (p : {poly K}) : p != 0 ->
                                 (p`_0 != 0) = devs_in_pw p%:F^-1.
Proof.
move => p_neq0.
rewrite -[X in devs_in_pw X]mul1r -tofrac1.
by rewrite devs_in_pwE ?horner_coef0 // coprime1p.
Qed.

Lemma p_neq0 (R: ringType) (p : {poly R}): 
                                        (exists (x : R), p.[x] != 0) -> p != 0.
Proof.
move => [x px_neq0].
move: px_neq0 ; apply: contra => /eqP ->.
by rewrite horner0.
Qed.

Fact one_sub_CX_0_eq_1 (a : K) : (1 - a *: 'X).[0] = 1.
Proof.
rewrite -horner_evalE rmorphB /= !horner_evalE.
by rewrite -mul_polyC hornerCM hornerX mulr0 hornerC subr0.
Qed.

Lemma devs_in_pw_inv_1_sub_CX (a : K) : 
                                   devs_in_pw (1 - a *: 'X)%:F^-1.
Proof.
rewrite -devs_in_pw_inv_p ; last first.
+ apply: p_neq0 ; exists 0.
  by rewrite one_sub_CX_0_eq_1 oner_neq0.
+ by rewrite -horner_coef0 one_sub_CX_0_eq_1 oner_neq0.
Qed.

Lemma devs_in_pw_div_tofrac (p q : {poly K}) :
                          q`_0 != 0 -> devs_in_pw (p %:F / q %:F).
Proof.
move => q0_neq0.
have q_neq0 : q != 0 by apply: p_neq0 ; exists 0 ; rewrite horner_coef0.
move: (fracpoly_div_tofracr p q_neq0).
move: (fracpolyE (p%:F / q%:F)) => [[u v] /= H] /andP [v_neq0 coprime_u_v].
rewrite H => divp_v_q ; rewrite devs_in_pwE //.
move: q0_neq0 ; apply: contra ; rewrite -!horner_coef0.
move/eqP/polyXsubCP ; rewrite subr0 => X_div_v.
by apply/eqP/polyXsubCP ; rewrite subr0 (dvdp_trans X_div_v).
Qed.

Lemma devs_in_pwD (x y : {fracpoly K}) :
  devs_in_pw x -> devs_in_pw y ->
  devs_in_pw (x + y).
Proof.
move: (fracpolyE x) => [[a b] /= Hx] /andP [b_neq0 coprime_a_b].
move: (fracpolyE y) => [[c d] /= Hy] /andP [d_neq0 coprime_c_d].
rewrite Hx Hy addf_div ?tofrac_eq0 //. 
rewrite devs_in_pwE // devs_in_pwE // => b0_neq0 d0_neq0.
rewrite -!rmorphM -rmorphD devs_in_pw_div_tofrac //.
rewrite -horner_coef0 -horner_evalE rmorphM /= !horner_evalE. 
by rewrite mulf_neq0 // horner_coef0.
Qed.

Lemma devs_in_pwM (x y : {fracpoly K}) :
  devs_in_pw x -> devs_in_pw y ->
  devs_in_pw (x * y).
Proof.
move: (fracpolyE x) => [[a b] /= Hx] /andP [b_neq0 coprime_a_b].
move: (fracpolyE y) => [[c d] /= Hy] /andP [d_neq0 coprime_c_d].
rewrite Hx Hy mulf_div -!rmorphM /=.
rewrite devs_in_pwE // devs_in_pwE // => b0_neq0 d0_neq0.
rewrite devs_in_pw_div_tofrac //.
rewrite -horner_coef0 -horner_evalE rmorphM /= !horner_evalE. 
by rewrite mulf_neq0 // horner_coef0.
Qed.

Lemma devs_in_pwN (x : {fracpoly K}) :
  (devs_in_pw (-x)) = (devs_in_pw x).
Proof.
move: (fracpolyE x) => [[a b] /= Hx] /andP [b_neq0 coprime_a_b].
rewrite Hx /= -mulNr -rmorphN /=.
rewrite devs_in_pwE // ; last first.
  by rewrite -scaleN1r coprimep_scalel // oppr_eq0 oner_eq0.
by rewrite devs_in_pwE.
Qed.

Definition to_powerseries (x : {fracpoly K}) := 
  if (devs_in_pw x) 
  then let (x1, x2) := projT1 (fracpolyE x) in (truncate x1) / (truncate x2)
  else 0.

Lemma to_powerseries0 : to_powerseries 0 = 0.
Proof.
rewrite /to_powerseries ; case: (devs_in_pw 0) => //=.
move: (fracpolyE (0 : {fracpoly K})) 
                                   => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
move/eqP: Hx ; rewrite eq_sym mulf_eq0 invr_eq0 !tofrac_eq0.
move/negbTE: v_neq0 -> ; rewrite orbF => /eqP ->.
by rewrite rmorph0 mul0r.
Qed.

Lemma to_powerseries_coprimep (p q : {poly K}) :
  (q`_0 != 0) -> coprimep p q -> 
  to_powerseries (p %:F / q %:F) = (truncate p) / (truncate q).
Proof.
have [-> | q_neq0] := eqVneq q 0.
  by rewrite !rmorph0 !invr0 !mulr0 to_powerseries0.
move => q0_neq0 coprime_p_q.
rewrite /to_powerseries.
move: (associate_fracpolyE q_neq0 coprime_p_q).
move: (fracpolyE (p %:F / q %:F)) => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
move => [c /andP [/eqP Hp /eqP Hq]].
rewrite Hp Hq !linearZ /=.
have c_neq0 : c != 0.
  apply/negP => /eqP c_eq0.
  rewrite c_eq0 scale0r in Hq.
  by rewrite Hq eqxx in q_neq0.
rewrite devs_in_pwE ; last 2 first.
+ by rewrite scaler_eq0 (negbTE c_neq0) (negbTE v_neq0).
+ by rewrite coprimep_scalel // coprimep_scaler.
have v0_neq0 : v`_0 != 0. 
  by rewrite (@nth0_eq_nth0 v q) // Hq eqp_sym eqp_scale.
have -> : (c *: v).[0] != 0.
  by rewrite hornerZ horner_coef0 mulf_eq0 (negbTE c_neq0) orFb.
rewrite invrZ ?unitfE // ; last by rewrite truncate_is_unit.
by rewrite scalerCA scalerA divff // scale1r.
Qed.

Lemma to_powerseries_div_tofrac (p q : {poly K}) :
     q`_0 != 0 -> to_powerseries (p %:F / q %:F) = (truncate p) / (truncate q).
Proof.
move => q0_neq0 ; rewrite /to_powerseries.
have -> : devs_in_pw (p%:F / q%:F)
                              by rewrite devs_in_pw_div_tofrac //.
have q_neq0 : q != 0 by apply: p_neq0; exists 0; rewrite horner_coef0.
move: (fracpolyE (p%:F / q%:F)) => [[u v] /= Hx] /andP [v_neq0 coprime_u_v].
have v0_neq0 : v`_0 != 0.
  rewrite -horner_coef0 -(devs_in_pwE v_neq0 coprime_u_v) -Hx.
  by rewrite devs_in_pw_div_tofrac.
apply/eqP ; rewrite eq_divr ?truncate_is_unit // -!rmorphM.
apply/eqP ; apply: (congr1 _) ; apply/eqP.
rewrite -tofrac_eq !rmorphM /= -eq_divf ?tofrac_eq0 //.
by apply/eqP ; symmetry.
Qed.

Fact to_powerseries1 : to_powerseries 1 = 1.
Proof.
rewrite /to_powerseries.
move: (fracpolyE (1 : {fracpoly K}))=> [[u v] /= Hx] /andP [v_neq0 cop_u_v].
have: exists (c : K), (u == c%:P) && (v == c%:P) && (c != 0).
  move/eqP: Hx ; rewrite eq_sym.
  move/eqP/(congr1 (fun x => x*v%:F)).
  rewrite mul1r mulrAC -mulrA divff ?mulr1 ; last by rewrite tofrac_eq0.
  move/eqP ; rewrite tofrac_eq => /eqP u_eq_v.
  move: cop_u_v ; rewrite u_eq_v coprimepp.
  move/size_poly1P => [c c_neq0 v_eq_cP] ; exists c.
  by rewrite c_neq0 andbb andbT v_eq_cP.
move => [c /andP [/andP [/eqP -> /eqP ->] c_neq0]].
rewrite -tofrac1 devs_in_pw_tofrac divrr // truncateC. 
by rewrite powerseries_unitE (qualifE 0) unitfE coefC.
Qed.

Lemma to_powerseries_tofrac (p : {poly K}) : to_powerseries p %:F = truncate p.
Proof.
rewrite -[p%:F]divr1 -tofrac1 to_powerseries_coprimep.
+ by rewrite truncate1 divr1.
+ by rewrite -horner_coef0 hornerC oner_neq0.
exact: coprimep1.
Qed.

Lemma to_powerseries_inv_tofrac (p : {poly K}) :
                  p`_0 != 0 -> to_powerseries ((p %:F) ^-1) = (truncate p) ^-1.
Proof.
move => p0_neq0.
rewrite -[p%:F^-1]mul1r -tofrac1 to_powerseries_coprimep //.
  by rewrite truncate1 mul1r.
exact: coprime1p.
Qed.

Lemma to_powerseriesM : 
          {in devs_in_pw &, {morph to_powerseries: x y  / x * y}}.
Proof.
move => x y.
move: (fracpolyE x) => [[a b] /= Hx] /andP [b_neq0 coprime_a_b].
move: (fracpolyE y) => [[c d] /= Hy] /andP [d_neq0 coprime_c_d].
rewrite -!topredE /= Hx Hy !devs_in_pwE // => b0_neq0 d0_neq0.
rewrite mulf_div -!rmorphM /= [LHS]to_powerseries_div_tofrac ; last first.
  by rewrite -horner_coef0 -horner_evalE rmorphM /= !horner_evalE mulf_neq0. 
rewrite !to_powerseries_div_tofrac -?horner_coef0 // !rmorphM /=.
by rewrite mulr_div ?truncate_is_unit -?horner_coef0. 
Qed. 

Lemma to_powerseriesD : 
          {in devs_in_pw &, {morph to_powerseries: x y  / x + y}}.
Proof.
move => x y ; rewrite -!topredE.
move: (fracpolyE x) => [[a b] /= Hx] /andP [b_neq0 coprime_a_b].
move: (fracpolyE y) => [[c d] /= Hy] /andP [d_neq0 coprime_c_d].
rewrite Hx Hy !devs_in_pwE // => b0_neq0 d0_neq0.
rewrite addf_div ?tofrac_eq0 // -!rmorphM -rmorphD /=.
rewrite [LHS]to_powerseries_div_tofrac ; last first.
  by rewrite -horner_coef0 -horner_evalE rmorphM /= !horner_evalE mulf_neq0.
rewrite rmorphD !rmorphM /= !to_powerseries_div_tofrac -?horner_coef0 //.
by rewrite addr_div ?truncate_is_unit -?horner_coef0.
Qed.

Lemma to_powerseriesN :
         {in devs_in_pw, {morph to_powerseries: x / - x >-> - x}}.
Proof.
move => x ; rewrite -topredE.
move: (fracpolyE x) => [[a b] /= Hx] /andP [b_neq0 coprime_a_b].
rewrite Hx !devs_in_pwE // => b0_neq0.
rewrite -mulNr -rmorphN [LHS]to_powerseries_div_tofrac -?horner_coef0 //.
by rewrite to_powerseries_div_tofrac -?horner_coef0 // rmorphN mulNr.
Qed.

Lemma to_powerseriesB :
          {in devs_in_pw &, {morph to_powerseries: x y  / x - y}}.
Proof.
move => x y x_dev y_dev /=.
by rewrite -to_powerseriesN // to_powerseriesD // -topredE /= devs_in_pwN. 
Qed.

Lemma to_powerseries_eq0 (u v : {poly K}) : v`_0 = 0 -> coprimep u v ->
  to_powerseries (u%:F / v%:F) = 0.
Proof.
move => /eqP v0_eq0 coprime_u_v.
have [-> | v_neq0] := eqVneq v 0 ;
                          first by rewrite rmorph0 invr0 mulr0 to_powerseries0.
by rewrite /to_powerseries devs_in_pwE // horner_coef0 v0_eq0.
Qed.

Fact truncation0 : truncation (0 : powerseries K n) = 0.
Proof. by []. Qed.

Fact truncation1 : truncation (1 : powerseries K n) = 1.
Proof. by []. Qed.

Fact truncation_is_additive : additive (@truncation K n).
Proof. by move => p q ; apply: val_inj. Qed.

Canonical truncation_additive := Additive truncation_is_additive.

Fact truncationD : {morph (@truncation K n) : x y / x + y}.
Proof. by []. Qed.

End Truncation.

Lemma truncate_map_poly (K K' : fieldType) (m : nat) 
                        (f : {rmorphism K -> K'}) (p : {poly K}) :
                     @truncate K' m (p ^ f) = map_powerseries f (truncate m p).
Proof. by apply: val_inj => /= ; rewrite map_modp map_polyXn. Qed.

Section Powerderiv.

Variable (K : fieldType).

Fact leq_size_deriv (R : ringType) (p : {poly R}) : size p^`() <= (size p).-1.
Proof.
have [ -> | p_neq0 ] := eqVneq p 0.
+ by rewrite deriv0 size_poly0 leqnn.
+ by rewrite -(leq_add2r 1%N) !addn1 (leq_trans (lt_size_deriv _)) // leqSpred.
Qed.

Fact powerderiv_proof (n : nat) (p : powerseries K n) : 
                                                   size (val p)^`() <= n.-1.+1.
Proof. 
rewrite (leq_trans (leq_size_deriv _)) // (leq_trans _ (leqSpred _)) //.
rewrite -(leq_add2r 1%N) !addn1.
by move: (truncationP p) ; case: (size _).
Qed.

Definition powerderiv (n : nat) (p : powerseries K n) := 
                                              Powerseries (powerderiv_proof p).

Definition primitive (a : K) (p : {poly K}) := 
            \poly_(i < (size p).+1) (if i == 0%N then a else p`_i.-1 / (i%:R)).

Definition can_primitive := primitive 0.
Local Notation "\int p" := (can_primitive p) (at level 2).

Lemma primitiveE (a : K) (p : {poly K}) : 
                                      primitive a p = (can_primitive p) + a%:P.
Proof.
apply/polyP => i.
rewrite coefD !coef_poly coefC ; case: i => [ | i] ; first by rewrite add0r.
by rewrite addr0.
Qed.

Lemma aux_coef_can_prim (p : {poly K}) (i : nat) : 
                        (\int p)`_i = if i == 0%N then 0 else p`_i.-1 / (i%:R).
Proof.
case: i => [ | i ] ; first by rewrite eqxx /can_primitive /primitive coef_poly.
rewrite /can_primitive /primitive succnK eqn0Ngt ltn0Sn coef_poly.
rewrite eqn0Ngt ltn0Sn /= -{3}[p]coefK coef_poly ltnS.
by case: (i < size p) => // ; rewrite mul0r.
Qed.

Lemma coef0_can_prim (p : {poly K}) : (\int p)`_0 = 0.
Proof. by rewrite aux_coef_can_prim eqxx. Qed.

Lemma coef_can_prim (p : {poly K}) (i : nat) : 
                                    i != 0%N -> (\int p)`_i = p`_i.-1 / (i%:R).
Proof. by rewrite aux_coef_can_prim ; move/negbTE ->. Qed.

Lemma can_primC (c : K) : \int (c%:P) = c *: 'X.
Proof. 
apply/polyP => i.
rewrite /can_primitive /primitive coef_poly size_polyC -[c *: 'X]coefK.
have [-> | c_neq0 ] := eqVneq c 0.
  by rewrite eqxx /= scale0r size_poly0 coef_poly ltn0 ; case: i.
rewrite c_neq0 /= coef_poly size_scale // size_polyX coefZ coefX.
case: i => [ | i ] ; first by rewrite !eqxx mulr0.
by rewrite coefC ; case: i => [ | i ] ; rewrite ?invr1.
Qed.

Lemma can_primX : \int 'X = (2%:R) ^-1 *: 'X ^+2.
Proof. 
rewrite /can_primitive /primitive size_polyX ; apply/polyP => i.
rewrite coef_poly coefZ coefXn coefX.
case: i => [ | i ] ; first by rewrite mulr0.
rewrite eqn0Ngt ltn0Sn /= ; case: i => [ | i ] ; first by rewrite mul0r mulr0.
case: i => [ | i ] ; first by rewrite mul1r mulr1.
by rewrite mulr0.
Qed.

Fact aux_eqSnSm (a b : nat) : (a.+1 == b.+1) = (a == b).
Proof.
apply/eqP/eqP ; last by move ->.
by move/succn_inj.
Qed.

Lemma can_primXn (m : nat): \int ('X ^+ m) = (m.+1 %:R) ^-1 *: 'X ^+ m.+1.
Proof.
rewrite /can_primitive /primitive size_polyXn ; apply/polyP => i.
rewrite coefZ !coefXn coef_poly !coefXn.
have [-> | /negbTE i_neq_Sm ] := eqVneq i m.+1.
  by rewrite eqxx ltnSn mulr1 eqxx mul1r.
rewrite i_neq_Sm /= mulr0 ; case: (i < m.+2) => [] //.
have [ -> | /negbTE i_neq0 ] := eqVneq i 0%N ; first by rewrite eqxx.
rewrite i_neq0 ; move/negbT : i_neq0 ; move/negbT : i_neq_Sm.
case: i => [ // | i ].
by rewrite aux_eqSnSm => /negbTE -> _ ; rewrite mul0r.
Qed.

Fact coefK2 (R : ringType) (p : {poly R}) (m : nat) : 
                                         size p <= m -> \poly_(i < m) p`_i = p.
Proof.
move => leq_sizep_m.
rewrite -[p]coefK ; apply/polyP => i.
rewrite !coef_poly.
have [ lt_i_sizep | leq_sizep_i ] := ltnP i (size p).
  by rewrite (leq_trans lt_i_sizep leq_sizep_m).
by case: (_ < _).
Qed.

Fact widen_poly (R : ringType) (p : {poly R}) (m : nat) : 
                   size p <= m -> \poly_(i < size p) p`_i = \poly_(i < m) p`_i.
Proof. by move => leq_sizep_m ; rewrite coefK coefK2. Qed.

Fact can_prim_is_linear : linear can_primitive.
Proof.
move => k p q ; apply/polyP => i.
case: i => [ | i]; first by rewrite coefD coefZ !coef0_can_prim mulr0 addr0.
by rewrite !(aux_coef_can_prim, coefD, coefZ) mulrDl -mulrA. 
Qed.

Canonical can_prim_additive := Additive can_prim_is_linear.
Canonical can_prim_linear := Linear can_prim_is_linear.

Lemma can_prim0 : can_primitive 0 = 0.
Proof. exact: linear0. Qed.

Lemma can_primD : {morph can_primitive : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma can_primN : {morph can_primitive : p / - p}.
Proof. exact: linearN. Qed.

Lemma can_primB : {morph can_primitive : p q / p - q}.
Proof. exact: linearB. Qed.

Hypothesis char_K_is_zero : [char K] =i pred0.

Lemma size_prim_cneq0 (a : K) (p : {poly K}) : 
                                  a != 0 -> size (primitive a p) = (size p).+1.
Proof.
move => a_neq0.
rewrite size_poly_eq //=.
have [ -> | /negbTE p_neq0 ] := eqVneq p 0 ; first by rewrite size_poly0 eqxx.
rewrite size_poly_eq0 p_neq0 -lead_coefE mulf_neq0 //.
  by rewrite lead_coef_eq0 p_neq0.
by rewrite invr_eq0 natmul_inj // size_poly_eq0 p_neq0.
Qed.

Lemma size_prim_pneq0 (a : K) (p : {poly K}) : 
                                  p != 0 -> size (primitive a p) = (size p).+1.
Proof.
move => /negbTE p_neq0.
rewrite size_poly_eq //= size_poly_eq0 p_neq0 -lead_coefE mulf_neq0 //.
  by rewrite lead_coef_eq0 p_neq0.
by rewrite invr_eq0 natmul_inj // size_poly_eq0 p_neq0.
Qed.

Lemma leq_size_prim (a : K) (p : {poly K}) :
  size (primitive a p) <= (size p).+1.
Proof.
have [ -> | p_neq0 ] := eqVneq p 0.
  by rewrite primitiveE can_prim0 add0r size_poly0 size_polyC leq_b1.
by rewrite size_prim_pneq0.
Qed.

Lemma cancel_deriv_prim (a : K) : cancel (primitive a) (@deriv K).
Proof.
move => p.
rewrite /primitive -{3}[p]coefK ; apply/polyP => i. 
rewrite coef_deriv !coef_poly ltnS.
case: (i < size p) ; last by rewrite mul0rn.
rewrite eqn0Ngt ltn0Sn /= -mulr_natr mulrAC -mulrA divrr ?mulr1 //.
by rewrite unitfE natmul_inj.
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

Lemma deriv0_polyC (p : {poly K}) : deriv p == 0 -> size p <= 1.
Proof.
rewrite -size_poly_eq0 size_deriv ; case: (size p) => [ | s ] //=.
by move/eqP ->.
Qed.

Lemma deriv_poly_eq0 (p : {poly K}) : p`_0 == 0 -> p^`() == 0 -> p = 0.
Proof.
move/eqP => p0_eq0 derivp_eq0.
by move: (size1_polyC (deriv0_polyC derivp_eq0)) ; rewrite p0_eq0.
Qed.

Lemma deriv_poly_eq (p q : {poly K}) : p`_0 == q`_0 -> p^`() == q^`() -> p = q.
Proof.
rewrite -subr_eq0 -coefB -[p^`() == q^`()]subr_eq0 -derivB.
move => coef0_eq0 deriv_eq0 ; apply/eqP.
rewrite -subr_eq0 ; apply/eqP ; move: coef0_eq0 deriv_eq0.
exact: deriv_poly_eq0.
Qed.

Lemma can_prim_deriv (p : {poly K}) : 
                                    can_primitive (deriv p) = p - ((p`_0) %:P).
Proof.
apply: deriv_poly_eq.
  by rewrite coef0_can_prim coefB coefC eqxx subrr.
by rewrite cancel_deriv_prim derivB derivC subr0.
Qed.

Fact powerprim_proof (n : nat) (a : K) (p : powerseries K n) :
                                            size (primitive a (val p)) <= n.+2.
Proof. by rewrite (leq_trans (leq_size_prim _ _)) // ltnS truncationP. Qed.

Definition powerprim (a : K) (n : nat) (p : powerseries K n) := 
                                        Powerseries (powerprim_proof a p).

Definition can_powerprim := powerprim 0.

Fact can_powerprim_is_linear (n : nat) : linear (@can_powerprim n).
Proof.
move => k p q ; apply: val_inj => /=.
by rewrite -/can_primitive linearD linearZ.
Qed.

Canonical can_powerprim_additive (n : nat) := 
                                    Additive (@can_powerprim_is_linear n).
Canonical can_powerprim_linear (n : nat) := 
                                      Linear (@can_powerprim_is_linear n).

Lemma cancel_powerderiv_powerprim (n : nat) (a : K) : 
  cancel (@powerprim a n) (@powerderiv n.+1).
Proof.
move => p.
by apply: val_inj => /= ; rewrite cancel_deriv_prim.
Qed.

Lemma coef0_can_powerprim_is_0 (n : nat) (p : powerseries K n) : 
                                (can_powerprim p) \in (coef0_is_0 K n.+1).
Proof. by rewrite /coef0_is_0 inE coef_poly. Qed.

Lemma coef0_can_powerprim (n : nat) (p : powerseries K n) : 
  (can_powerprim p)`_0 = 0.
Proof. by rewrite coef_poly. Qed.

Variable (n : nat).

Local Notation "c %:S" := (Powerseries (constP n.+1 c)) (at level 2).

Lemma can_powerprim_powerderiv (p : powerseries K n.+1) : 
                          can_powerprim (powerderiv p) = p - ((p`_0) %:S).
Proof.
rewrite -horner_coef0 ; apply: val_inj => /= ; rewrite horner_coef0.
exact: can_prim_deriv.
Qed.

Lemma deriv_modp (m : nat) (p : {poly K}) : 
                                   (p %% 'X ^+ m.+1)^`() = (p ^`()) %% 'X ^+ m.
Proof.
rewrite {2}[p](divp_eq _ ('X^m.+1)) derivD derivM !modp_add.
rewrite -addrA [X in X + _]modp_eq0 ; last first.
rewrite dvdp_mull // dvdp_Pexp2l ?leqnSn // size_polyX //.
rewrite add0r [X in X + _]modp_eq0 ; last first.
  by rewrite dvdp_mull // derivXn /= -scaler_nat dvdp_scaler2.
rewrite add0r [RHS]modp_small // size_polyXn.
have [-> | p_modXSm_neq0] := eqVneq (p %% 'X^m.+1) 0.
+ by rewrite deriv0 size_poly0. 
+ by rewrite (leq_trans _ (leq_modpXn m.+1 p)) // lt_size_deriv.
Qed.

Local Notation "p `d" := (powerderiv p) (at level 2).
Local Notation "c %:S" := (Powerseries (constP n c)) (at level 2).

Lemma powerderiv0 (m : nat) : (0 : powerseries K m) `d = 0.
Proof. apply: val_inj ; exact: deriv0. Qed.

Lemma powerderivC (c : K) : c %:S `d = 0.
Proof. apply: val_inj ; exact: derivC. Qed.

Lemma powerderivD (p q : powerseries K n) : (p + q)`d = p `d + q `d.
Proof. apply: val_inj ; exact: derivD. Qed.

Lemma powerderivN (p : powerseries K n) : (- p)`d = - (p `d).
Proof. apply: val_inj ; exact: derivN. Qed.

Lemma powerderivB (p q : powerseries K n) : (p - q)`d = p `d - q `d.
Proof. apply: val_inj ; exact: derivB. Qed.

Lemma powerderivZ (c : K) (p : powerseries K n) : (c *: p) `d = c *: (p `d).
Proof. apply: val_inj ; exact: derivZ. Qed.

Fact powerderiv1 : (1 : powerseries K n) `d = 0.
Proof. apply: val_inj ; exact: derivC. Qed. 

End Powerderiv.

Local Notation "p `d" := (powerderiv p) (at level 2).

Fact modp_mul2 (F : fieldType) (p q m : {poly F}):
                                            ((p %% m) * q) %% m = (p * q) %% m.
Proof. by rewrite mulrC modp_mul mulrC. Qed.

Lemma powerderivM (K :fieldType) (n : nat) (p q : powerseries K n) : 
          (p * q) `d = (p `d) * (truncate n.-1 q) + (truncate n.-1 p) * (q `d).
Proof.
move : p q ; case: n => /= [p q | m p q].
  rewrite [p]pw_is_cst [q]pw_is_cst. 
  by rewrite -mul_cst !powerderivC mul0r mulr0 addr0.
apply: val_inj => /=.
by rewrite deriv_modp derivM modp_mul modp_mul2 -modp_add.
Qed. 

Fact truncate_truncationV (K :fieldType) (n : nat) (p : powerseries K n) : 
  p`_0 != 0 ->
  truncate n (truncation p^-1) = (truncate n (truncation p)) ^-1.
Proof.
move => p0_neq0.
have /val_eqP /eqP pdivp : (p / p = 1).
  by rewrite divrr // powerseries_unitE /powerseries_unit (qualifE 0) unitfE.
have H: (truncate n (truncation p)) \is a GRing.unit.
  by rewrite truncate_is_unit.
apply: (mulrI H) ; rewrite divrr // ; apply: val_inj => /=.
by rewrite modp_mul modp_mul2.
Qed.

Fact truncate_truncationV2 (K :fieldType) (n m : nat) (p : powerseries K n) : 
  m <= n -> p`_0 != 0 ->
  truncate m (truncation p^-1) = (truncate m (truncation p)) ^-1.
Proof.
move => leq_m_n p0_neq0.
have /val_eqP /eqP pdivp : (p / p = 1).
  apply: divrr.
  by rewrite powerseries_unitE /powerseries_unit (qualifE 0) unitfE.
have H: (truncate m (truncation p)) \is a GRing.unit.
  by rewrite truncate_is_unit.
apply: (mulrI H) ; rewrite divrr // ; apply: val_inj => /=.
rewrite modp_mul modp_mul2 -(@modp_modp K _ 'X^m.+1 'X^n.+1) ; last first.
  by rewrite dvdp_exp2l.
have -> : (truncation p * truncation p^-1) %% 'X^n.+1 = 1 by [].
apply: modp_small.
by rewrite size_polyC size_polyXn ; apply: (leq_trans (leq_b1 _)).
Qed.

Lemma powerderivV (K :fieldType) (n : nat) (p : powerseries K n) : 
  p`_0 != 0 ->
  (p ^-1) `d = - (p `d) / (truncate n.-1 (p ^+ 2)).
Proof.
move => p0_neq0.
move/eqP: (eq_refl (p / p)).
rewrite {2}divrr ; last first.
  by rewrite powerseries_unitE /powerseries_unit (qualifE 0) unitfE.
move/(congr1 (@powerderiv K n)).
rewrite powerderivM powerderiv1.
move/eqP ; rewrite addrC addr_eq0 mulrC.
move/eqP/(congr1 (fun x => x / (truncate n.-1 p))).
rewrite -mulrA divrr ; last by rewrite truncate_is_unit.
rewrite mulr1 => ->.
rewrite !mulNr ; congr (- _).
rewrite -mulrA ; congr (_ * _).
rewrite truncate_truncationV2 // ; last exact: leq_pred.
rewrite -invrM ?truncate_is_unit // ; congr (_ ^-1).
rewrite -rmorphM /= ; apply: val_inj => /=.
rewrite modp_modp // dvdp_exp2l //.
by apply: (leq_trans (leq_pred _)).
Qed.

Lemma powerderivdiv (K :fieldType) (n : nat) (p q : powerseries K n) : 
  q`_0 != 0 ->
  (p / q) `d = (p `d * truncate n.-1 q - truncate n.-1 p * q `d) 
                                                    / (truncate n.-1 (q ^+ 2)).
Proof.
move => q0_neq0.
rewrite powerderivM powerderivV // mulrBl mulrA mulrN mulNr.
congr (_ - _) ; rewrite -mulrA ; congr (_ * _).
rewrite truncate_truncationV2 // ; last exact: leq_pred.
rewrite expr2 powermul_truncation truncateE.
have -> : truncate n.-1 (q * q) = (truncate n.-1 q) * (truncate n.-1 q).
  rewrite -rmorphM /= ; apply: val_inj => /=.
  by rewrite modp_modp // dvdp_exp2l // ; apply: (leq_trans (leq_pred _)).
by rewrite invrM ?truncate_is_unit // mulrA divrr ?truncate_is_unit // mul1r.
Qed.

Section CompSerie.
Variable (K : fieldType).

Definition comp_series (m : nat) (q p : powerseries K m) :=
              if q \in (coef0_is_0 K m) then truncate m (comp_poly q p) else 0.

Notation "p \So q" := (comp_series q p) (at level 2).
Notation "p `d" := (powerderiv p) (at level 2).

Fact deriv_size1 (R : ringType) (p : {poly R}) : size p <= 1 -> deriv p = 0.
Proof. by move => H_size ; rewrite (size1_polyC H_size) derivC. Qed.

Section Variable_n.
Variable (n : nat).
Notation "c %:S" := (Powerseries (constP n c)) (at level 2).

Lemma comp_series_coef0_neq0 (p q : powerseries K n) : 
                                      q \notin (coef0_is_0 K n) -> p \So q = 0.
Proof. by move/negbTE => p0_neq0 ; rewrite /comp_series p0_neq0. Qed.

Lemma comp_series_coef0_eq0 (p q : powerseries K n) : 
                q \in (coef0_is_0 K n) -> p \So q = truncate n (comp_poly q p).
Proof. by move => p0_eq0 ; rewrite /comp_series p0_eq0. Qed.

Section Variable_p.

Variable (p : powerseries K n).

Lemma pwC_in_coef0_is_0 (c : K) : reflect (c = 0) (c %:S \in coef0_is_0 K n).
Proof. by rewrite /coef0_is_0 inE coefC eqxx ; apply: eqP. Qed.

Lemma comp_series0r : p \in (coef0_is_0 K n) ->  p \So 0 = 0.
Proof. 
rewrite inE => p0_eq0.
rewrite comp_series_coef0_eq0 ; last exact: (rpred0 (c0_is_0_keyed K n)).
rewrite truncation0 comp_poly0r truncateC -horner_coef0 ; apply: val_inj => /=.
by apply/eqP ; rewrite horner_coef0 polyC_eq0. 
Qed.

Lemma comp_seriesr0 : 0 \So p = 0.
Proof.
have [ p0_eq0 | p0_neq0 ] := boolP (p \in (coef0_is_0 K n)).
+ by rewrite comp_series_coef0_eq0 // comp_poly0 truncate0.
+ by rewrite comp_series_coef0_neq0.
Qed.

Lemma comp_seriesC (c : K) : c%:S \So p = 
                                        (c * (p \in (coef0_is_0 K n)) %:R) %:S.
Proof.
have [ p0_eq0 | p0_neq0 ] := boolP (p \in (coef0_is_0 K n)).
+ rewrite comp_series_coef0_eq0 //= comp_polyC mulr1 ; apply: val_inj => /=.
  by rewrite modp_small // size_polyC size_polyXn ; case: (_ != 0).
+ by rewrite comp_series_coef0_neq0 //= mulr0 pwconst0. 
Qed. 

Hypothesis (p0_is_0 : p \in (coef0_is_0 K n)).

Fact comp_series_is_linear : linear (comp_series p).
Proof.
move => a q r.
have [p0_eq0 | p0_neq0] := boolP (p \in (coef0_is_0 K n)).
+ rewrite comp_series_coef0_eq0 // rmorphD linearZ rmorphD /=.
  by rewrite truncateZ /comp_series p0_eq0.
+ by rewrite !comp_series_coef0_neq0 // addr0 scaler0.
Qed.

End Variable_p.
End Variable_n.

Lemma powerderiv_comp (m : nat) (p q : powerseries K m): p \in (coef0_is_0 K m) ->
  powerderiv (q \So p) = (q `d \So (truncate m.-1 p)) * p `d.
Proof.
move: p q ; case: m => [ p q p0_eq0 | m p q p0_eq0 ].
+ apply: val_inj => /=.
  rewrite deriv_size1 ; last exact: (truncationP _).
  rewrite deriv_size1 ; last first. 
- move: (pw_is_cst p) ; rewrite -horner_coef0.
  move/(congr1 val) => /= ->.
  by rewrite size_polyC leq_b1.
- by rewrite mulr0 mod0p.
+ rewrite /= comp_series_coef0_eq0 // comp_series_coef0_eq0 ?p0_is_0 //.
  apply: val_inj => /=.
  rewrite deriv_modp deriv_comp -[LHS]modp_mul2; congr (modp _); congr (_ * _).
  rewrite (divp_eq (truncation p) 'X^m.+1) modp_add modp_mull add0r modp_mod.
  rewrite !comp_polyE !modp_summ /= ; apply: eq_bigr => i _.
  rewrite !modp_scalel ; congr (_ *: _).
  rewrite exprDn big_ord_recr /= subnn expr0 mul1r binn mulr1n modp_add.
  rewrite modp_summ /= (eq_bigr (fun j => 0)) => [ | j _].
    by rewrite big1_eq add0r.
  rewrite -scaler_nat modp_scalel ; apply/eqP.
  rewrite scaler_eq0 ; apply/orP ; right.
  apply/eqP ; apply: modp_eq0.
  by rewrite dvdp_mulr // exprMn dvdp_mull // dvdp_exp // subn_gt0.
Qed.

End CompSerie.


