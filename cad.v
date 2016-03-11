(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(*****************************************************************************)
(*  some doc here                                                            *)
(*****************************************************************************)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp Require Import tuple finfun generic_quotient bigop finset perm ssralg poly.
From mathcomp Require Import polydiv ssrnum mxpoly binomial finalg zmodp.  
From mathcomp Require Import mxtens qe_rcf ordered_qelim mxpoly realalg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Import ord.

Local Open Scope nat_scope.
Local Open Scope ring_scope. 
Open Local Scope quotient_scope.

Section EqFormula.

Variable (T : eqType).

Fixpoint formula_eq (f1 f2 : formula T) := match f1, f2 with
  | Bool b1, Bool b2 => b1 == b2
  | Equal t1 u1, Equal t2 u2 => (t1 == t2) && (u1 == u2)
  | Lt t1 u1, Lt t2 u2 => (t1 == t2) && (u1 == u2)
  | Le t1 u1, Le t2 u2 => (t1 == t2) && (u1 == u2)
  | Unit t1, Unit t2 => (t1 == t2)
  | And f1 g1, And f2 g2 => (formula_eq f1 f2) && (formula_eq g1 g2)
  | Or f1 g1, Or f2 g2 => (formula_eq f1 f2) && (formula_eq g1 g2)
  | Implies f1 g1, Implies f2 g2 => (formula_eq f1 f2) && (formula_eq g1 g2)
  | Not f1, Not f2 => formula_eq f1 f2
  | Exists i1 f1, Exists i2 f2 => (i1 == i2) && (formula_eq f1 f2)
  | Forall i1 f1, Forall i2 f2 => (i1 == i2) && (formula_eq f1 f2)
  | _, _ => false
end.

Lemma formula_eqP : Equality.axiom formula_eq.
Proof.
move=> f1 f2; apply: (iffP idP) => [|<-]; last first.
  by elim: f1 {f2}=> x //= y; rewrite ?eqxx // => f ->; rewrite y.
elim: f1 f2.  
- by move=> b1 f //=; case: f => //=; move=> b2 /eqP ->.
- by move=> t1 t2 f; case: f => //= u1 u2 /andP [/eqP -> /eqP ->].
- by move=> t1 t2 f; case: f => //= u1 u2 /andP [/eqP -> /eqP ->].
- by move=> t1 t2 f; case: f => //= u1 u2 /andP [/eqP -> /eqP ->].
- by move=> t1 f //=; case: f => //=; move=> t2 /eqP ->.
- move=> f1 hf f2 hg f; case: f => //= g1 g2 /andP [h1 h2]. 
  by rewrite (hf g1) // (hg g2).
- move=> f1 hf f2 hg f; case: f => //= g1 g2 /andP [h1 h2]. 
  by rewrite (hf g1) // (hg g2).
- move=> f1 hf f2 hg f; case: f => //= g1 g2 /andP [h1 h2]. 
  by rewrite (hf g1) // (hg g2).
- by move=> f h1 g; case: g => //= g h2; rewrite (h1 g).
- by move=> i f1 h f2 /=; case: f2 => //= i2 g /andP [/eqP -> h2]; rewrite (h g).
- by move=> i f1 h f2 /=; case: f2 => //= i2 g /andP [/eqP -> h2]; rewrite (h g).
Qed.

Canonical formula_eqMixin := EqMixin formula_eqP.
Canonical formula_eqType := Eval hnf in EqType (formula T) formula_eqMixin.

End EqFormula.

Section ChoiceFormula.

Variable (T : choiceType).

Fixpoint encode_term (t : GRing.term T) := match t with 
  | GRing.Var i => GenTree.Node (2*i) [::]
  | GRing.Const x => GenTree.Leaf x
  | GRing.NatConst i => GenTree.Node ((2*i).+1) [::]
  | GRing.Add x y => GenTree.Node O ((encode_term x)::(encode_term y)::nil)
  | GRing.Opp x => GenTree.Node O ((encode_term x)::nil)
  | GRing.NatMul x i => GenTree.Node ((2*i).+2) ((encode_term x)::nil)
  | GRing.Mul x y => GenTree.Node 1 ((encode_term x)::(encode_term y)::nil)
  | GRing.Inv x => GenTree.Node 1 ((encode_term x)::nil)
  | GRing.Exp x i => GenTree.Node ((2*i).+3) ((encode_term x)::nil)
end.

Fixpoint decode_term (t : GenTree.tree T) := match t with
  | GenTree.Leaf x => GRing.Const x
  | GenTree.Node i s => match s with
    | [::] => if (i %% 2)%N == O then GRing.Var T (i %/ 2) else GRing.NatConst T ((i.-1) %/ 2)
    | e1::e2::l => if i == O then GRing.Add (decode_term e1) (decode_term e2) 
                             else GRing.Mul (decode_term e1) (decode_term e2)
    | e::l => if i == O then GRing.Opp (decode_term e) else 
              if i == 1%N then GRing.Inv (decode_term e) else 
              if (i %% 2)%N == O then GRing.NatMul (decode_term e) ((i.-2) %/ 2) 
                                 else GRing.Exp (decode_term e) ((i-3) %/ 2) 
    end
end.

Lemma encode_termK : cancel encode_term decode_term.
Proof.
move=> t.
elim: t.
move=> n /=.
+ by rewrite modnMr eqxx mulKn.
+ by move=> r. 
+ by move=> n /=; rewrite {1}mulnC -addn1 modnMDl mulKn.
+ by move=> t1 h1 t2 h2 /=; rewrite h1 h2.  
+ by move=> t h /=; rewrite h.
+ by move=> t h n /=; rewrite -addn2 {1}mulnC modnMDl h mulKn.
+ by move=> t1 h1 t2 h2 /=; rewrite h1 h2.
+ by move=> t h /=; rewrite h.
+ by move=> t h n /=; rewrite -addn3 {1}mulnC modnMDl /= h addnK mulKn.
Qed.

(* works *)
(* Definition my_tree := GenTree.tree T. *)
(* Canonical my_tree_of_eqType := [eqType of my_tree]. *)
(* Canonical my_tree_of_choiceType := [choiceType of my_tree]. *)

Definition my_term := GRing.term T.
Canonical my_term_of_eqType := [eqType of my_term].
Fail Canonical my_term_of_choiceType := [choiceType of my_term].

Definition my_term_ChoiceMixin := CanChoiceMixin encode_termK.
Canonical my_term_choiceType := ChoiceType my_term my_term_ChoiceMixin.

(* Definition my_formula := formula T. *)
Canonical my_formula_of_eqType := [eqType of formula T].

Fixpoint encode_formula (f : formula T) := match f with 
  | Bool b => GenTree.Node b [::]
  | Equal t1 t2 => GenTree.Node O ((encode_term t1)::(encode_term t2)::nil)
  | Lt t1 t2 => GenTree.Node 1 ((encode_term t1)::(encode_term t2)::nil)
  | Le t1 t2 => GenTree.Node 2 ((encode_term t1)::(encode_term t2)::nil)
  | Unit t => GenTree.Node O ((encode_term t)::nil)
  | And f1 f2 => GenTree.Node 3 ((encode_formula f1)::(encode_formula f2)::nil)
  | Or f1 f2 => GenTree.Node 4 ((encode_formula f1)::(encode_formula f2)::nil)
  | Implies f1 f2 => GenTree.Node 5 ((encode_formula f1)::(encode_formula f2)::nil)
  | Not f => GenTree.Node 1 ((encode_formula f)::nil)
  | Exists i f => GenTree.Node (2*i).+2 ((encode_formula f)::nil)
  | Forall i f => GenTree.Node (2*i).+3 ((encode_formula f)::nil)
end.

Fixpoint decode_formula (t : GenTree.tree T) := match t with
  | GenTree.Leaf x => Unit (Const x)
  | GenTree.Node i s => match s with
    | [::] => if i == O then Bool false else Bool true
    | e1::e2::l => match i with
      | 0 => Equal (decode_term e1) (decode_term e2)
      | 1 => Lt (decode_term e1) (decode_term e2)
      | 2 => Le (decode_term e1) (decode_term e2)
      | 3 => And (decode_formula e1) (decode_formula e2)
      | 4 => Or (decode_formula e1) (decode_formula e2)
      | _ => Implies (decode_formula e1) (decode_formula e2)
      end
    | e::l => if i == O then Unit (decode_term e) else 
              if i == 1%N then Not (decode_formula e) else 
              if (i %% 2)%N == O then Exists ((i.-2) %/ 2) (decode_formula e) 
                                 else Forall ((i-3) %/ 2) (decode_formula e)
    end
end.

Lemma encode_formulaK : cancel encode_formula decode_formula.
Proof.
move=> f.
elim: f.
+ by move=> b /=; case: b.
+ by move=> t1 t2 /=; rewrite !encode_termK.
+ by move=> t1 t2 /=; rewrite !encode_termK.
+ by move=> t1 t2 /=; rewrite !encode_termK.
+ by move=> t /=; rewrite !encode_termK.
+ by move=> f1 h1 f2 h2 /=; rewrite h1 h2.
+ by move=> f1 h1 f2 h2 /=; rewrite h1 h2.
+ by move=> f1 h1 f2 h2 /=; rewrite h1 h2.
+ by move=> f hf /=; rewrite hf.
+ by move=> i f hf /=; rewrite hf -addn2 {1}mulnC modnMDl mulKn /=.
+ by move=> i f hf /=; rewrite hf -addn3 {1}mulnC modnMDl /= addnK mulKn.
Qed.

Definition formula_ChoiceMixin := CanChoiceMixin encode_formulaK.
Canonical formula_choiceType := ChoiceType (formula T) formula_ChoiceMixin.

End ChoiceFormula.

Section Cad.

Variable R : rcfType. (* is also a realDomainType *)

Fixpoint nquantify (n : nat) (f : formula R) := match n with
  | O => f
  | S m => Forall m (nquantify m f)
end.

Variable (n : nat).

(* We define a relation in formulas *)
Local Notation equivf_notation f g := 
  (rcf_sat [::] (nquantify n ((f ==> g) /\ (g ==> f)))).
Definition equivf f g := equivf_notation f g.

Lemma equivf_refl : reflexive equivf.
Proof. 
move=> f; apply/rcf_satP.
by move: [::]; elim: n => [//= | m ih /= x x0].
Qed.

Lemma equivf_sym : symmetric equivf.
Proof.
move=> f g; rewrite /equivf; move: [::].
elim: n => [e |m ih e].
  by apply/rcf_satP/rcf_satP; move => [h1 h2]; split.
by apply/rcf_satP/rcf_satP => /= h x; apply/rcf_satP; 
    [rewrite -ih | rewrite ih]; apply/rcf_satP; apply: h.
Qed.

Lemma equivf_trans : transitive equivf.
Proof.
move=> f g h; rewrite /equivf; move: [::].
elim: n => [e |m ih e] /=.
  move/rcf_satP => [ /= h1 h2].
  move/rcf_satP => [ /= h3 h4].
  apply/rcf_satP; split => h5; first by apply: h3; apply: h1.
  by apply: h2; apply: h4.
move/rcf_satP => /= h1; move/rcf_satP => /= h2; apply/rcf_satP => /= x.
apply/rcf_satP; apply: ih; apply/rcf_satP.
  exact: h1.
  exact: h2.
Qed.

(* we show that equivf is an equivalence *)
Canonical equivf_equiv := EquivRel equivf equivf_refl equivf_sym equivf_trans.

Definition type := {eq_quot equivf}.
Definition type_of of phant R := type.
Notation "{ 'formula' T }" := (type_of (Phant T)).

Fixpoint fv_term (t : GRing.term R) : seq nat :=
  match t with
  | 'X_i => [::i]
  | t1 + t2 | t1 * t2 => undup (fv_term t1 ++ fv_term t2)
  | - t1 | t1 *+ _ | t1 ^+ _ | t1^-1 => fv_term t1
  | _ => [::]
  end%T.

Fixpoint fv_formula (f : ord.formula R) : seq nat :=
  match f with
  | Bool _ => [::]
  | (t1 == t2) | (t1 <% t2)| (t1 <=% t2)  => undup (fv_term t1 ++ fv_term t2)
  | (Unit t1) => fv_term t1
  | (f1 /\ f2) | (f1 \/ f2) | (f1 ==> f2) => undup (fv_formula f1 ++ fv_formula f2)
  | (~ f1) => fv_formula f1
  | ('exists 'X_i, f1) | ('forall 'X_i, f1) => rem i (fv_formula f1)
end%oT.

Definition nform : pred_class := fun f : formula R => 
  rformula f && all (fun x => (x < n)%N) (fv_formula f).

(* Lemma holds_rcons_zero (e : seq R) (f : formula R) : holds (rcons e 0) f<-> holds e f. *)
(* Proof. *)
(* eq_holds *)
(* Qed. *)

(* Lemma holds_cat_zeros (e : seq R) (f : formula R)  *)

Lemma holds_forall (i : nat) (e : seq R) (f : formula R) :  holds e (Forall i f) -> holds e f.
Proof.
move/(_ (nth 0 e i)); apply: eq_holds.
rewrite /GRing.same_env.
apply: (ftrans (@nth_set_nth _ _ _ _ _)) => j /=.
have [-> | ] := eqVneq i j; rewrite ?eqxx // eq_sym.
by move/negbTE ->.
Qed.

Lemma forall_is_true (f : formula R) : 
  (forall (e : seq R), holds e f) -> 
  forall (i : nat) (e : seq R), holds e (Forall i f).
Proof. by move=> h i e /= x. Qed.

(* Fact and_sym (e : seq R) (f g : formula R) : holds e (f /\ g) <-> holds e (g /\ f). *)
(* Proof. *)
(* rewrite /=. *)
(* Qed. *)

(* Lemma quantify_and (e : seq R) (f g : formula R) *)

End Cad.
 