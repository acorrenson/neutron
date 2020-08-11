Require Import ZArith Psatz.
Require Import Lists.List.
Require Import Recdef.
Require Import Program.Wf.
Require Import Program.Equality.
Require Import Logic.FunctionalExtensionality.
Import ListNotations.

Inductive logic_1 : Set :=
  | Land_1  : logic_1 -> logic_1 -> logic_1
  | Lor_1   : logic_1 -> logic_1 -> logic_1
  | Liff_1  : logic_1 -> logic_1 -> logic_1
  | Limpl_1 : logic_1 -> logic_1 -> logic_1
  | Lneg_1  : logic_1 -> logic_1
  | Latom_1 : nat -> logic_1.

Inductive logic_2 : Set :=
  | Land_2  : logic_2 -> logic_2 -> logic_2
  | Lor_2   : logic_2 -> logic_2 -> logic_2
  | Lneg_2  : logic_2 -> logic_2
  | Latom_2 : nat -> logic_2.


Fixpoint remove_impl (l : logic_1) : logic_2 :=
  match l with
  | Land_1 a b =>
    Land_2 (remove_impl a) (remove_impl b)
  | Lor_1 a b =>
    Lor_2 (remove_impl a) (remove_impl b)
  | Limpl_1 a b =>
    Lor_2 (Lneg_2 (remove_impl a)) (remove_impl b)
  | Liff_1 a b =>
    Land_2 (remove_impl a) (remove_impl b)
  | Lneg_1 a => Lneg_2 (remove_impl a)
  | Latom_1 a => Latom_2 a
  end.


Inductive rule_no_impl : logic_1 -> Prop :=
  | no_impl_and    : forall a b, rule_no_impl a -> rule_no_impl b -> rule_no_impl (Land_1 a b)
  | no_impl_or     : forall a b, rule_no_impl a -> rule_no_impl b -> rule_no_impl (Lor_1 a b)
  | no_impl_neg    : forall a, rule_no_impl a -> rule_no_impl (Lneg_1 a)
  | no_impl_atm    : forall n, rule_no_impl (Latom_1 n).

Program Fixpoint remove_impl' (l : logic_1) : {l' : logic_1 | rule_no_impl l'} :=
  match l with
  | Land_1 a b =>
    Land_1 (remove_impl' a) (remove_impl' b)
  | Lor_1 a b =>
    Lor_1 (remove_impl' a) (remove_impl' b)
  | Limpl_1 a b =>
    Lor_1 (Lneg_1 (remove_impl' a)) (remove_impl' b)
  | Liff_1 a b =>
    Land_1 (remove_impl' a) (remove_impl' b)
  | Lneg_1 a => Lneg_1 (remove_impl' a)
  | Latom_1 a => Latom_1 a
  end.

Next Obligation.
  apply no_impl_and; assumption.
Defined.

Next Obligation.
  apply no_impl_or; assumption.
Defined.

Next Obligation.
  apply no_impl_or.
  - apply no_impl_neg; assumption.
  - assumption.
Defined.

Next Obligation.
  apply no_impl_and; assumption.
Defined.

Next Obligation.
  apply no_impl_neg; assumption.
Defined.

Next Obligation.
  apply no_impl_atm.
Defined.

Inductive rule_no_neg : logic_1 -> Prop :=
  | no_neg_and    : forall a b, rule_no_neg a -> rule_no_neg b -> rule_no_neg (Land_1 a b)
  | no_neg_or     : forall a b, rule_no_neg a -> rule_no_neg b -> rule_no_neg (Lor_1 a b)
  | no_neg_neg    : forall n, rule_no_neg (Lneg_1 (Latom_1 n))
  | no_neg_atm    : forall n, rule_no_neg (Latom_1 n).

Definition test := fun (x : logic_1 | rule_no_impl x) => 0.

Program Fixpoint remove_neg (sign : bool) (e : logic_1) (P : rule_no_impl e) {struct e} : {l : logic_1 | rule_no_neg l} :=
  match e with
  | Land_1 a b =>
    if sign then Land_1 (remove_neg sign a _) (remove_neg sign b _)
    else Lor_1 (remove_neg false a _) (remove_neg false b _)
  | Lor_1 a b =>
    if sign then Lor_1 (remove_neg sign a _) (remove_neg sign b _)
    else Land_1 (remove_neg false a _) (remove_neg false b _)
  | Lneg_1 a =>
    remove_neg (negb sign) a _
  | Latom_1 n =>
    if sign then Latom_1 n
    else Lneg_1 (Latom_1 n)
  | _ => e
  end.


Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  inversion P.
  apply no_neg_and; assumption.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  apply no_neg_or; assumption.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  apply no_neg_or; assumption.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  apply no_neg_and; assumption.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  apply no_neg_atm.
Defined.

Next Obligation.
  apply no_neg_neg.
Defined.

Next Obligation.
  inversion P; subst.
  - eelim H2; auto.
  - eelim H; auto.
  - eelim H0; auto.
  - eelim H1; auto.
Defined.

Next Obligation.
  repeat split; intros; discriminate.
Defined.

Next Obligation.
  repeat split; intros; discriminate.
Defined.


Fixpoint semL (l : logic_1) (v : nat -> bool) :=
    match l with
    | Land_1 a b => andb (semL a v) (semL b v)
    | Lor_1 a b => orb (semL a v) (semL b v)
    | Liff_1 a b =>
      let sa := semL a v in
      let sb := semL b v in
      andb (implb sa sb) (implb sa sb)
    | Limpl_1 a b =>
      implb (semL a v) (semL b v)
    | Latom_1 x => v x
    | Lneg_1 a => negb (semL a v)
    end.

Theorem remove_impl'_correct:
  forall l, semL (proj1_sig (remove_impl' l)) = semL l.
Proof.
  intros; induction l; simpl; apply functional_extensionality; intro.
  - rewrite IHl1, IHl2; reflexivity.
  - rewrite IHl1, IHl2; reflexivity.
  - rewrite IHl1, IHl2.
    


Qed.

