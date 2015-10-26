(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat div seq choice fintype.
From mathcomp
Require Import tuple bigop ssralg poly. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Local Scope ring_scope.


Fact aux_equivb (P : Prop) (b c : bool) : reflect P b -> b = c -> reflect P c.
Proof. by move => reflect_P_b b_eq_c ; rewrite b_eq_c in reflect_P_b. Qed.

Section MoreNatTheory.

Variable (a : nat).

Lemma lt_pred : (a.-1 < a) = (a != O).
Proof. case: a => [ | a' ] ; rewrite //= ; exact: ltnSn. Qed.

Fact n_eq1 : a != O -> a < 2 -> a == 1%N.
Proof. by case: a => // b ; case: b => // c. Qed.

Fact n_leq_Sn : a <= a.+1.
Proof. exact : leqnSn. Qed.

Variable (b : nat).

Fact ltnpredn : (a < b.-1) = (a.+1 < b).
Proof. by case: b. Qed.

Fact my_subnSK : (b - a.+1)%N = (b.-1 - a)%N.
Proof.
rewrite subnS ; case: b => [ | c ] ; first by rewrite sub0n //.
by rewrite subSKn.
Qed. 

Variable (c : nat).

Fact aux_nat : 0 < c -> (a - b < c) = (a < b + c).
Proof.
move => lt_0_c.
have [ lt_a_b | leq_b_a ] := ltnP a b ; last first.
  by rewrite addnC -(ltn_add2r b) subnK.
have -> : a < b + c by apply: ltn_addr.
by move/ltnW : lt_a_b ; rewrite -subn_eq0 => /eqP ->.
Qed.

Fact ltpredn : a != 0%N -> ((a+b).-1 < c+b) = (a.-1 < c).
Proof.
case: b => [ | b' ] ; first by rewrite !addn0.
by rewrite addnS /= addnS ltnS leq_add2r ; case: a.
Qed.

Lemma leq_subRL : a <= c -> (b <= c - a) = (a + b <= c).
Proof.
move => a_leq_c.
case: b => [ | b'] ; first by rewrite addn0 leq0n a_leq_c.
by rewrite addnS ltn_subRL.
Qed.

End MoreNatTheory.


Section MoreFieldTheory.
Variable (K : fieldType).

Lemma eq_divf (a b c d : K) : b != 0 -> d != 0 -> 
  (a / b == c / d) = (a * d == c * b).
Proof.
move => b_neq0 d_neq0.
rewrite -subr_eq0 -mulNr addf_div // mulf_eq0 invr_eq0 mulf_eq0.
by rewrite (negPf b_neq0) (negPf d_neq0) !orbF mulNr subr_eq0.
Qed.

Lemma addr_div (R : comUnitRingType) (x1 y1 x2 y2 : R) :
  (y1 \is a GRing.unit) ->
  (y2 \is a GRing.unit) -> x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) / (y1 * y2).
Proof.
move => y1_unit y2_unit.
rewrite invrM // mulrDl !mulrA.
rewrite !unitrE in y1_unit y2_unit.
rewrite mulrAC.
congr(_ + _) ; rewrite mulrAC ; congr(_ * _) ; rewrite -mulrA.
+ by move/eqP: y2_unit -> ; rewrite mulr1.
+ by move/eqP: y1_unit -> ; rewrite mulr1.
Qed.

Lemma eq_divr (R : comUnitRingType) (a b c d : R) : (b \is a GRing.unit) -> 
  (d \is a GRing.unit) ->
  (a / b == c / d) = (a * d == c * b).
Proof.
rewrite !unitrE => /eqP b_unit /eqP d_unit.
apply/eqP/eqP.
+ move/(congr1 ( *%R^~ b)).
  rewrite mulrAC -mulrA b_unit mulr1.
  move/(congr1 ( *%R^~ d)).
  by rewrite -mulrA mulrAC -!mulrA d_unit mulr1. 
+ move/(congr1 ( *%R^~ d^-1)).
  rewrite -mulrA d_unit mulr1 mulrAC -mulrA.
  move/(congr1 ( *%R^~ b^-1)).
  by rewrite -!mulrA b_unit mulr1.
Qed.

Lemma mulr_div (R : comUnitRingType) (x1 y1 x2 y2 : R) : y1 \is a GRing.unit ->
  y2 \is a GRing.unit ->
  (x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2).
Proof.
move => y1_unit y2_unit.
by rewrite mulrACA -invrM // ; congr (_ * _) ; rewrite mulrC.
Qed.

End MoreFieldTheory.


Local Notation "p ^ f" := (map_poly f p).

Section AuxiliaryResults.

Fact first_rev (T : Type) (s : seq T) (x : T) : head x (rev s) = last x s. 
Proof. case/lastP: s => [//= |t y]; rewrite rev_rcons last_rcons //=. Qed.

Fact last_rev (T : Type) (s : seq T) (x : T) : last x (rev s) = head x s.
Proof. case: s => [//= |t y /=]; rewrite rev_cons last_rcons //=. Qed.

Definition nrcons (T : Type) (n : nat) (x : T) := fun s => s ++ nseq n x.

Lemma rev_ncons (T : Type) (n : nat) (x : T) (s : seq T) : 
                                        rev (ncons n x s) = nrcons n x (rev s).
Proof. 
case: n => [ | n ]; first by rewrite /nrcons cats0.
apply: eq_from_nth => // [ | j ].
  by rewrite size_rev size_ncons /nrcons size_cat /= size_rev size_nseq addnC.
rewrite size_rev => Hj.
rewrite nth_rev // /nrcons nth_cat nth_ncons ltnS leq_subLR addnC addnS -addSn.
rewrite size_ncons leq_add2l addnC -subnDA subnDr size_rev. 
rewrite size_ncons in Hj.
have [ j_lt_s | s_leq_j ] := ltnP j (size s) ; first by rewrite nth_rev.
by rewrite nth_nseq ; case: (_ < _).
Qed.

Lemma rem_cons  (T : eqType) (s : seq T) (a : T) : rem a (a::s) = s.
Proof. by rewrite /= eqxx. Qed.

Variable (R : ringType).

Fact first_coef_poly (p : {poly R}) : p`_0 = head 0 p.
Proof. exact: nth0. Qed.

Lemma rmorph_sum_ord (R' : ringType) (f : {rmorphism R -> R'}) (n : nat)
  (E : nat -> R) : f (\sum_(i < n) E i) = \sum_(i < n) f (E i).
Proof. by apply: big_morph ; first exact: rmorphD ; rewrite rmorph0. Qed.

Fact map_poly_mul (c : R) p : p ^ ( *%R c) = c *: p.
Proof. by apply/polyP => i; rewrite coefZ coef_map_id0 ?mulr0. Qed.

Lemma poly_cons (l : seq R) (a : R) : Poly (a::l) = a%:P + (Poly l) * 'X.
Proof. by rewrite /Poly /= cons_poly_def addrC. Qed.

Lemma poly_rcons (s : seq R) : Poly (rcons s 0) = Poly s.
Proof.
elim: s => [ | a l iH] ; first by rewrite /= cons_poly_def mul0r add0r.
by rewrite rcons_cons !poly_cons iH.
Qed.

Lemma poly_nrcons (n : nat) (s : seq R) : Poly (nrcons n 0 s) = Poly s.
Proof. 
rewrite /nrcons; move : s ; elim: n => [s | m iH s]; first by rewrite cats0.
by rewrite -cat_rcons iH poly_rcons.
Qed.

Lemma widen_poly (E : nat -> R) (a b : nat) :
  a <= b ->
  (forall j, a <= j < b -> E j = 0) ->
  \poly_(i < a) E i = \poly_(i < b) E i.
Proof.           
move => leq_a_b H.
apply/polyP => k ; rewrite !coef_poly.
have [ lt_k_b | leq_b_k ] := ltnP k b ; last first.
   by rewrite ltnNge (leq_trans leq_a_b _).
have [ // | leq_a_k ] := ltnP k a.
by symmetry ; apply: H ; apply/andP ; split.
Qed.

Fact aux_iter_add (m : nat) (y x z : R) : 
                                 iter m (+%R x) (y+z) = (iter m (+%R x)) y + z.
Proof. by move: y z; elim: m => [// | m iH y z]; rewrite !iterSr addrA iH. Qed.

Fact iter_add (m : nat) (y x : R) : iter m (+%R x) y = y + x *+ m.
Proof.
elim: m => [ | m iH ] ; first by rewrite mulr0n addr0.
by rewrite iterSr addrC aux_iter_add iH mulrSr addrA. 
Qed.

Fact aux_iter_mul (m : nat) (y x z : R) : 
                             iter m ( *%R x) (y * z) = (iter m ( *%R x)) y * z.
Proof. by move: y z; elim: m=> [// | m iH y z ]; rewrite !iterSr mulrA iH. Qed.

Fact iter_mul (m : nat) (y x : R) : iter m ( *%R x) y = x ^+ m * y.
Proof.
move: x y ; elim: m => [ x y | m iH x y ] ; first by rewrite expr0 mul1r.  
by rewrite iterSr aux_iter_mul iH -exprSr.
Qed.

Fact deriv_sum_nat (a b : nat) (F : nat -> {poly R}) : 
                 deriv (\sum_(a <= i < b) F i) = \sum_(a <= i < b) deriv (F i).
Proof.
apply: big_morph ; last exact: deriv0.
exact: derivD.
Qed. 

Fact deriv_sum (b : nat) (F : nat -> {poly R}) :
                           deriv (\sum_(i < b) F i) = \sum_(i < b) deriv (F i).
Proof.
rewrite -(big_mkord predT _) -(big_mkord predT (fun i => (F i)^`())).
exact: deriv_sum_nat.
Qed.

End AuxiliaryResults.

Section MoreBigop.

Variables (R : Type) (idx : R).

Section CommutativeMonoid.

Variable (op : Monoid.com_law idx).

Lemma big_split_ord  (m : nat) (P : pred nat) (F : nat -> R) :
  \big[op/idx]_(i < m) F i = op (\big[op/idx]_(i < m | P i) F i)
                                           (\big[op/idx]_(i < m | ~~ P i) F i).
Proof.
rewrite -big_mkord -(big_mkord predT) -(big_mkord (fun i =>  ~~ P i)).
by rewrite (bigID P predT) (eq_bigl P F).
Qed.

Lemma big_ord_rev (m : nat) (P : nat -> bool) (F : nat -> R) :
  \big[op/idx]_(i < m | P i) F i =
                          \big[op/idx]_(i < m | P (m - i.+1)%N) F (m - i.+1)%N.
Proof.
rewrite -(big_mkord P F) big_nat_rev (big_mkord _ _).
by apply: eq_bigr ; rewrite add0n.
Qed.

End CommutativeMonoid.

Variable (op : Monoid.law idx).

Fact exchange_ord_cond (a b : nat) (F : nat -> R) :
  \big[op/idx]_(i < a | i < b) F i = \big[op/idx]_(i < b | i < a) F i.
Proof.
wlog le_b_a : a b / b <= a => [hwlog|].
  have /orP [le_a_b|le_b_a] := leq_total a b; last exact: hwlog.
  by symmetry; apply: hwlog.
rewrite big_ord_narrow /=; apply: eq_big => // i.
by rewrite (leq_trans _ le_b_a).
Qed.

Fact big_ord_lt_1 (F : nat -> R) : \big[op/idx]_(i < 1) F i = F 0%N.
Proof. by rewrite -(big_mkord predT F) big_nat1. Qed.

Lemma big_mknat (a b : nat) (F : nat -> R) :
  \big[op/idx]_(i < b | a <= i) F i = \big[op/idx]_(a <= i < b) F i.
Proof.
rewrite -(big_mkord (fun i => a <= i) F).
have [ /ltnW lt_b_a | leq_a_b ] := ltnP b a.
+ rewrite [RHS]big_geq // big_nat_cond.
  rewrite (eq_bigl pred0) => [ | i /= ] ; last first.
- apply/negP => /andP [lt_i_b leq_a_i].
  move: (leq_trans lt_i_b lt_b_a).
  by apply/negP ; rewrite -leqNgt.
- by rewrite big_pred0_eq.
+ rewrite (big_cat_nat _ _ _ (leq0n _) leq_a_b).
  rewrite big_nat_cond (eq_bigl pred0) => [ | i /= ] ; last first.
    by apply/negbTE ; rewrite ltnNge andbC andbN.
  rewrite big_pred0_eq Monoid.simpm big_nat_cond [RHS]big_nat_cond.
  by apply: eq_bigl => i /= ; case: (_ <= i).
Qed.

End MoreBigop.

