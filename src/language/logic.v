Require Import ZArith Psatz.
Require Import Lists.List.
Require Import Lists.ListSet.
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

Inductive logic_3 : Set :=.

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