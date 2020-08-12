Require Import ZArith Psatz.
Require Import Lists.List.
Require Import Recdef.
Require Import Program.Wf.
Require Import Program.Equality.
Require Import Logic.FunctionalExtensionality.
Import ListNotations.

Inductive logic : Set :=
  | Land  : logic -> logic -> logic
  | Lor   : logic -> logic -> logic
  | Limpl : logic -> logic -> logic
  | Lneg  : logic -> logic
  | Latom : nat -> logic.

Inductive rule_no_impl : logic -> Prop :=
  | no_impl_and    : forall a b, rule_no_impl a -> rule_no_impl b -> rule_no_impl (Land a b)
  | no_impl_or     : forall a b, rule_no_impl a -> rule_no_impl b -> rule_no_impl (Lor a b)
  | no_impl_neg    : forall a, rule_no_impl a -> rule_no_impl (Lneg a)
  | no_impl_atm    : forall n, rule_no_impl (Latom n).

Program Fixpoint remove_impl (l : logic) : {l' : logic | rule_no_impl l'} :=
  match l with
  | Land a b =>
    Land (remove_impl a) (remove_impl b)
  | Lor a b =>
    Lor (remove_impl a) (remove_impl b)
  | Limpl a b =>
    Lor (Lneg (remove_impl a)) (remove_impl b)
  | Lneg a => Lneg (remove_impl a)
  | Latom a => Latom a
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
  apply no_impl_neg; assumption.
Defined.

Next Obligation.
  apply no_impl_atm; assumption.
Defined.


Inductive rule_no_neg : logic -> Prop :=
  | no_neg_and    : forall a b, rule_no_neg a -> rule_no_neg b -> rule_no_neg (Land a b)
  | no_neg_or     : forall a b, rule_no_neg a -> rule_no_neg b -> rule_no_neg (Lor a b)
  | no_neg_neg    : forall n, rule_no_neg (Lneg (Latom n))
  | no_neg_atm    : forall n, rule_no_neg (Latom n).


Program Fixpoint remove_neg (sign : bool) (e : logic) (P : rule_no_impl e) {struct e} : {l : logic | rule_no_neg l} :=
  match e with
  | Land a b =>
    if sign then Land (remove_neg sign a _) (remove_neg sign b _)
    else Lor (remove_neg false a _) (remove_neg false b _)
  | Lor a b =>
    if sign then Lor (remove_neg sign a _) (remove_neg sign b _)
    else Land (remove_neg false a _) (remove_neg false b _)
  | Lneg a =>
    if sign then remove_neg false a _
    else remove_neg true a _
  | Latom n =>
    if sign then Latom n
    else Lneg (Latom n)
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


Fixpoint semL (l : logic) (v : nat -> bool) :=
    match l with
    | Land a b => andb (semL a v) (semL b v)
    | Lor a b => orb (semL a v) (semL b v)
    | Limpl a b =>
      implb (semL a v) (semL b v)
    | Latom x => v x
    | Lneg a => negb (semL a v)
    end.

Theorem remove_impl_correct:
  forall l, semL (proj1_sig (remove_impl l)) = semL l.
Proof.
  intros; induction l; simpl; apply functional_extensionality; intro.
  - rewrite IHl1, IHl2; reflexivity.
  - rewrite IHl1, IHl2; reflexivity.
  - rewrite IHl1, IHl2.
    destruct (semL l1 x); reflexivity.
  - rewrite IHl; reflexivity.
  - reflexivity.
Qed.

Lemma helper:
  forall l P v,
    semL (proj1_sig (remove_neg false l P)) v
    =
    negb (semL (proj1_sig (remove_neg true l P)) v).
Proof.
  intros.
  induction l.
  - simpl. rewrite IHl1, IHl2.
    rewrite Bool.negb_andb.
    reflexivity.
  - simpl. rewrite IHl1, IHl2.
    rewrite Bool.negb_orb.
    reflexivity.
  - inversion P.
  - simpl. rewrite IHl.
    rewrite Bool.negb_involutive.
    reflexivity.
  - simpl. reflexivity.
Qed.

Theorem remove_neg_correct:
  forall (l : logic),
  forall (P : rule_no_impl l),
  semL (proj1_sig (remove_neg true l P)) = semL l.
Proof.
  intros; induction l; simpl.
  - rewrite IHl1, IHl2; reflexivity.
  - rewrite IHl1, IHl2; reflexivity.
  - reflexivity.
  - apply functional_extensionality.
    intro.
    rewrite helper, IHl.
    reflexivity.
  - reflexivity.
Qed.

Inductive is_sum : logic -> Prop :=
  | is_sum_or :
    forall a b, is_sum a -> is_sum b -> is_sum (Lor a b)
  | is_sum_neg :
    forall n, is_sum (Lneg (Latom n))
  | is_sum_atm :
    forall n, is_sum (Latom n).

Inductive distributed : logic -> Prop :=
  | distributed_and :
    forall a b, distributed a -> distributed b -> distributed (Land a b)
  | distributed_or :
    forall a b, is_sum a -> is_sum b -> distributed (Lor a b).

Fixpoint variant (l : logic) : nat :=
  match l with
  | Land a b 
  | Lor a b 
  | Limpl a b => variant a + variant b
  | Lneg a => variant a
  | Latom _ => 1
  end.

Lemma variant_pos : 
  forall l, variant l > 0.
Proof.
  induction l; simpl; lia.
Qed.

(* Program Fixpoint merge (l1 : logic) (l2 : logic) (P : distributed l1) (Q : distributed l2) {measure (variant l1 + variant l2)} : {l' : logic | distributed l'} :=
  match l1 with
  | Land a b =>
    match l2 with
    | Lor _ _ => Land (merge a l2 _ _) (merge b l2 _ _)
    | Land a' b' =>
      Land (merge l1 a' _ _) (merge l1 b' _ _)
    | Lneg (Latom _) =>
      Land (merge a l2 _ _) (merge b l2 _ _)
    | Latom a => Lor l1 l2
    | _ => _
    end
  | Lor a b =>
    match l2 with
    | Lor _ _ => Lor l1 l2
    | Land a' b' =>
      Land (merge l1 a' _ _) (merge l1 b' _ _)
    | Lneg (Latom _) =>
      Land (merge a l2 _ _) (merge b l2 _ _)
    | Latom a => Lor l1 l2
    | _ => _
    end
    
  end. *)



Program Fixpoint merge (l1 : logic) (l2 : logic) (P : distributed l1) (Q : distributed l2) {measure (variant l1 + variant l2)} : {l' : logic | distributed l'} :=
  match l2 with
  | Land a b =>
    Land (merge l1 a _ _) (merge l1 b _ _)
  | Lor a b =>
    match l1 with
    | Lor a' b' => Lor l1 l2
    | Land a' b' =>
      Land (merge l2 a' _ _) (merge l2 b' _ _)
    | Lneg (Latom _) => Lor l1 l2
    | Latom a => Lor l1 l2
    | _ => _
    end
  | Lneg (Latom _) =>
    match l1 with
    | Lor a' b' => Lor l1 l2
    | Land a' b' =>
      Land (merge l2 a' _ _) (merge l2 b' _ _)
    | Lneg (Latom _) => Lor l1 l2
    | Latom a => Lor l1 l2
    | _ => _
    end
  | Latom _ =>
    match l1 with
    | Lor a' b' => Lor l1 l2
    | Land a' b' =>
      Land (merge l2 a' _ _) (merge l2 b' _ _)
    | Lneg (Latom _) => Lor l1 l2
    | Latom a => Lor l1 l2
    | _ => _
    end
  | _ => l1
  end.

Next Obligation.
  inversion Q; assumption.
Defined.

Next Obligation.
  simpl.
  apply Nat.add_le_lt_mono.
  - reflexivity.
  - apply Nat.lt_add_pos_r; apply variant_pos.
Defined.

Next Obligation.
  inversion Q; assumption.
Defined.

Next Obligation.
  simpl.
  apply Nat.add_le_lt_mono.
  - reflexivity.
  - apply Nat.lt_add_pos_l; apply variant_pos.
Defined.

Next Obligation.
  apply distributed_and.
  - elim merge.
    intros; simpl; assumption.
  - elim merge.
    intros; simpl; assumption.
Defined.

Next Obligation.
  apply distributed_or; apply is_sum_or; inversion P; inversion Q; assumption.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  simpl.
  assert (variant a > 0) by apply variant_pos.
  assert (variant a' > 0) by apply variant_pos.
  assert (variant b > 0) by apply variant_pos.
  assert (variant b' > 0) by apply variant_pos.
  lia.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  simpl.
  assert (variant a > 0) by apply variant_pos.
  assert (variant a' > 0) by apply variant_pos.
  assert (variant b > 0) by apply variant_pos.
  assert (variant b' > 0) by apply variant_pos.
  lia.
Defined.

Next Obligation.
  apply distributed_and.
  - elim merge.
    intros; simpl; assumption.
  - elim merge.
    intros; simpl; assumption.
Defined.

Next Obligation.
  apply distributed_or.
  - apply is_sum_neg.
  - apply is_sum_or; inversion Q; assumption.
Defined.

Next Obligation.
  apply distributed_or.
  - apply is_sum_atm.
  - apply is_sum_or; inversion Q; assumption.
Defined.

Next Obligation.
  esplit. apply Q.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  apply distributed_or.
  - inversion P; apply is_sum_or; assumption.
  - apply is_sum_neg.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  simpl.
  assert (variant a' > 0) by apply variant_pos.
  assert (variant b' > 0) by apply variant_pos.
  lia.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  simpl.
  assert (variant b' > 0) by apply variant_pos.
  assert (variant a' > 0) by apply variant_pos.
  lia.
Defined.

Next Obligation.
  apply distributed_and;
  elim merge; intro; simpl; tauto.
Defined.

Next Obligation.
  apply distributed_or.
  - apply is_sum_neg.
  - inversion P; apply is_sum_or; assumption.
Defined.

Next Obligation.
  apply distributed_or.
  - inversion P; apply is_sum_or; assumption.
  - apply is_sum_neg.
Defined.

Next Obligation.
  esplit; apply P.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  apply distributed_or.
  - inversion P; apply is_sum_or; assumption.
  - apply is_sum_atm.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  simpl.
  assert (variant b' > 0) by apply variant_pos.
  assert (variant a' > 0) by apply variant_pos.
  lia.
Defined.

Next Obligation.
  inversion P; assumption.
Defined.

Next Obligation.
  simpl.
  assert (variant b' > 0) by apply variant_pos.
  assert (variant a' > 0) by apply variant_pos.
  lia.
Defined.

Next Obligation.
  apply distributed_and;
  elim merge; intro; simpl; tauto.
Defined.

Next Obligation.
  apply distributed_or.
  - apply is_sum_neg.
  - apply is_sum_atm.
Defined.

Next Obligation.
  apply distributed_or; apply is_sum_atm.
Defined.

Next Obligation.
  esplit; apply P.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.

Next Obligation.
  repeat split; discriminate.
Defined.


Program Fixpoint distrib_or (l : logic) (P : rule_no_impl l) (Q : rule_no_neg l) : {l' : logic | distributed l'} :=
  match l with
  | Land a b =>
    Land (distrib_or a _ _) (distrib_or b _ _)
  | Lor a b =>
    Land (distrib_or a _ _) (distrib_or b _ _)
  end.
  
