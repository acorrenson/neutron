Require Import ZArith Psatz.
Require Import Lists.List.
Require Import Recdef.
Require Import Program.Wf.
Require Import Program.Equality.
Require Import Logic.FunctionalExtensionality.
Import ListNotations.

(* Logic language *)
Inductive logic : Set :=
  | Land  : logic -> logic -> logic
  | Lor   : logic -> logic -> logic
  | Limpl : logic -> logic -> logic
  | Lneg  : logic -> logic
  | Latom : nat -> logic.

(* Logic without impl *)
Inductive logic_1 : Set :=
  | L1and   : logic_1 -> logic_1 -> logic_1
  | L1or    : logic_1 -> logic_1 -> logic_1
  | L1neg   : logic_1 -> logic_1
  | L1atom  : nat -> logic_1.

(* Literals *)
Inductive literal : Set :=
  | Pos : nat -> literal
  | Neg : nat -> literal.

(* Logic_1 with distributed negations *)
Inductive logic_2 : Set :=
  | L2and   : logic_2 -> logic_2 -> logic_2
  | L2or    : logic_2 -> logic_2 -> logic_2
  | L2lit   : literal -> logic_2.

Definition clause := list literal.

Definition logic_3 := list clause.

(* Conversion algorithm from logic to logic_1 *)
Fixpoint remove_impl (l : logic) : logic_1 :=
  match l with
  | Land a b =>
    L1and (remove_impl a) (remove_impl b)
  | Lor a b =>
    L1or (remove_impl a) (remove_impl b)
  | Limpl a b =>
    L1or (L1neg (remove_impl a)) (remove_impl b)
  | Lneg a => L1neg (remove_impl a)
  | Latom a => L1atom a
  end.

(* Conversion algorithm from logic_1 to logic_2 *)
Fixpoint remove_neg' (sign : bool) (l : logic_1) : logic_2 :=
  match l with
  | L1and a b =>
    if sign then L2and (remove_neg' sign a) (remove_neg' sign b)
    else L2or (remove_neg' false a) (remove_neg' false b)
  | L1or a b =>
    if sign then L2or (remove_neg' sign a) (remove_neg' sign b)
    else L2and (remove_neg' false a) (remove_neg' false b)
  | L1neg a =>
    if sign then remove_neg' false a
    else remove_neg' true a
  | L1atom n =>
    if sign then L2lit (Pos n)
    else L2lit (Neg n)
  end.

Definition remove_neg := remove_neg' true.

Definition merge_clause (c : clause) (l : logic_3) :=
  map (fun c' => c ++ c') l.

Fixpoint merge (l1 : logic_3) (l2 : logic_3) : logic_3 :=
  match l1 with
  | [] => []
  | c::cs => (merge_clause c l2) ++ (merge cs l2)
  end.

Fixpoint cnf' (l : logic_2) : logic_3 :=
  match l with
  | L2and a b => (cnf' a) ++ (cnf' b)
  | L2or a b => merge (cnf' a) (cnf' b)
  | L2lit a => [[a]]
  end.

Definition cnf (l : logic) : logic_3 :=
    cnf' (remove_neg (remove_impl l)).


Fixpoint semL (l : logic) (v : nat -> bool) : bool :=
  match l with
  | Land a b =>
    andb (semL a v) (semL b v)
  | Lor a b =>
    orb (semL a v) (semL b v)
  | Limpl a b =>
    implb (semL a v) (semL b v)
  | Lneg a =>
    negb (semL a v)
  | Latom n => v n
  end.

Fixpoint semL1 (l : logic_1) (v : nat -> bool) : bool :=
  match l with
  | L1and a b =>
    andb (semL1 a v) (semL1 b v)
  | L1or a b =>
    orb (semL1 a v) (semL1 b v)
  | L1neg a =>
    negb (semL1 a v)
  | L1atom n => v n
  end.

Fixpoint semL2 (l : logic_2) (v : nat -> bool) : bool :=
  match l with
  | L2and a b =>
    andb (semL2 a v) (semL2 b v)
  | L2or a b =>
    orb (semL2 a v) (semL2 b v)
  | L2lit (Pos n) => v n
  | L2lit (Neg n) => negb (v n)
  end.

Fixpoint semC (c : clause) (v : nat -> bool) : bool :=
  match c with
  | [] => false
  | Pos n::xs => orb (v n) (semC xs v)
  | Neg n::xs => orb (negb (v n)) (semC xs v)
  end.

Fixpoint semL3 (l : logic_3) (v : nat -> bool) : bool :=
  match l with
  | [] => true
  | c::cs => andb (semC c v) (semL3 cs v)
  end.

Theorem remove_impl_correct:
  forall l v, semL l v = semL1 (remove_impl l) v.
Proof.
  intros.
  induction l; simpl.
  - rewrite IHl1, IHl2; reflexivity.
  - rewrite IHl1, IHl2; reflexivity.
  - rewrite IHl1, IHl2; unfold implb; destruct semL1; reflexivity.
  - rewrite IHl; reflexivity.
  - reflexivity.
Qed.

Lemma remove_neg_false_negb:
  forall l v, semL2 (remove_neg' false l) v = negb (semL2 (remove_neg' true l) v).
Proof.
  intros.
  induction l; simpl.
  - rewrite IHl1, IHl2, Bool.negb_andb; reflexivity.
  - rewrite IHl1, IHl2, Bool.negb_orb; reflexivity.
  - rewrite IHl, Bool.negb_involutive; reflexivity.
  - reflexivity.
Qed.

Theorem remove_neg_correct:
  forall l v, semL1 l v = semL2 (remove_neg l) v.
Proof.
  intros.
  induction l; simpl.
  - rewrite IHl1, IHl2; reflexivity.
  - rewrite IHl1, IHl2; reflexivity.
  - rewrite IHl. unfold remove_neg. simpl.
    rewrite remove_neg_false_negb; reflexivity.
  - reflexivity.
Qed.


Lemma merge_comm:
  forall l v, semL3 (merge l []) v = semL3 (merge [] l) v.
Proof.
  intros.
  induction l; simpl.
  - reflexivity.
  - rewrite IHl. simpl; reflexivity.
Qed.

Theorem semC_union:
  forall c1 c2 v, semC (c1 ++ c2) v = orb (semC c1 v) (semC c2 v).
Proof.
  intros.
  induction c1; simpl.
  - reflexivity.
  - destruct a; rewrite IHc1, Bool.orb_assoc; reflexivity.
Qed.

Theorem semL3_union:
  forall c1 c2 v, semL3 (c1 ++ c2) v = andb (semL3 c1 v) (semL3 c2 v).
Proof.
  intros.
  induction c1; simpl.
  - reflexivity.
  - rewrite IHc1, Bool.andb_assoc; reflexivity.
Qed.

Theorem merge_clause_correct:
  forall c l v, semL3 (merge_clause c l) v = orb (semC c v) (semL3 l v).
Proof.
  intros.
  induction l; simpl.
  - rewrite Bool.orb_comm. reflexivity.
  - rewrite semC_union, IHl, Bool.orb_andb_distrib_r; reflexivity.
Qed.

Theorem merge_correct:
  forall l1 l2 v, orb (semL3 l1 v) (semL3 l2 v) = semL3 (merge l1 l2) v.
Proof.
  intros.
  induction l1; simpl.
  - reflexivity.
  - rewrite semL3_union,
            merge_clause_correct,
            <- IHl1,
            Bool.orb_andb_distrib_l.
    reflexivity.
Qed.

Theorem cnf'_correct:
  forall l v, semL2 l v = semL3 (cnf' l) v.
Proof.
  intros.
  induction l; simpl.
  - rewrite semL3_union, IHl1, IHl2. reflexivity.
  - rewrite <- merge_correct, IHl1, IHl2. reflexivity.
  - destruct l; rewrite Bool.andb_comm, Bool.orb_comm; simpl; reflexivity.
Qed.

Theorem cnf_correct:
  forall l v, semL l v = semL3 (cnf l) v.
Proof.
  intros.
  unfold cnf.
  rewrite remove_impl_correct,
          remove_neg_correct,
          cnf'_correct.
  reflexivity.
Qed.