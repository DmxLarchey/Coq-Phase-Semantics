(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.
Require Import Permutation.

Require Omega.

Set Implicit Arguments.

(* Various Permutation results *)

Reserved Notation "x '~!' y" (at level 70, no associativity).

Section perm_bang_t.

  Variables (X : Type) (bang : X -> X).

  Notation "'!' x" := (bang x) (at level 52). 

  Inductive perm_bang_t : list X -> list X -> Type :=
    | perm_bang_t_nil   :                          nil ~! nil
    | perm_bang_t_cons  : forall x l m, l ~! m -> x::l ~! x::m
    | perm_bang_t_swap  : forall x y l, !x::!y::l ~! !y::!x::l
    | perm_bang_t_trans : forall l m k, l ~! m -> m ~! k -> l ~! k
  where "x ~! y" := (perm_bang_t x y).

  Fact perm_bang_t_refl l : l ~! l.
  Proof.
    induction l; simpl; constructor; auto.
  Qed.
  
  Fact perm_bang_t_sym l m : l ~! m -> m ~! l.
  Proof.
    induction 1; try constructor; auto.
    apply perm_bang_t_trans with m; auto.
  Qed.
  
  Fact perm_bang_t_app a b l m : a ~! b -> l ~! m -> a++l ~! b++m.
  Proof.
    intros H1 H2.
    apply perm_bang_t_trans with (a++m).
    clear H1.
    induction a; simpl; auto; constructor; auto.
    clear H2.
    induction H1; simpl; auto.
    apply perm_bang_t_refl.
    constructor; auto.
    constructor.
    apply perm_bang_t_trans with (m0++m); auto.
  Qed.

  Hypothesis bang_inj : (forall x y, !x = !y -> x = y).

  Let Q m1 m2 := forall l1, m1 = map bang l1 
                             -> { l2 : list X | ((m2 = map bang l2))%type }.

  Let pmit : forall m1 m2, m1 ~! m2 -> Q m1 m2.
  Proof.
    apply perm_bang_t_rect; unfold Q; clear Q.
    * intros [ | ]; exists nil; simpl; split; auto; discriminate.
    * intros y m1 m2 H1 IH1 [ | x l1 ]; simpl; try discriminate.
      intros H2; injection H2; clear H2; intros H2 H3; subst y.
      destruct (IH1 _ H2) as (l2 & ?).
      exists (x::l2); simpl; subst; auto.
    * intros y1 y2 m1 [ | x2 [ | x1 l1 ] ]; try discriminate; simpl.
      intros H2; injection H2; clear H2; intros H1 H2 H3.
      apply bang_inj in H2; apply bang_inj in H3; subst.
      exists (x1::x2::l1); simpl; split; auto.
    * intros m1 m2 m3 H1 IH1 H2 IH2 l1 H3.
      destruct IH1 with (1 := H3) as (l2 & H4).
      destruct IH2 with (1 := H4) as (l3 & H6).
      exists l3; auto.
  Qed.

  Fact perm_bang_t_map_inv_t l m : map bang l ~! m -> { l' | m = map bang l' }.
  Proof. intro H; apply (@pmit _ _ H _ eq_refl). Qed.

  Reserved Notation "x '~~!' y" (at level 70, no associativity).

  Inductive perm_bang_t_l : list X -> list X -> Type :=
    | perm_bang_t_refl_l   :  forall l, l ~~! l
    | perm_bang_t_swap_l  : forall x y l1 l2, l1++!x::!y::l2 ~~! l1++!y::!x::l2
    | perm_bang_t_trans_l : forall l m k, l ~~! m -> m ~~! k -> l ~~! k
  where "x ~~! y" := (perm_bang_t_l x y).

  Lemma perm_bang_t_cons_l : forall x l1 l2, l1 ~~! l2 -> x :: l1 ~~! x :: l2.
  Proof.
  intros x l1 l2 HP.
  induction HP.
  - apply perm_bang_t_refl_l.
  - rewrite 2 app_comm_cons.
    apply perm_bang_t_swap_l.
  - eapply perm_bang_t_trans_l ; eassumption.
  Qed.

  Lemma perm_bang_t_perm_bang_t_l : forall l1 l2, l1 ~! l2 -> l1 ~~! l2.
  Proof.
    intros l1 l2 HP; induction HP.
    + apply perm_bang_t_refl_l.
    + apply perm_bang_t_cons_l; assumption.
    + rewrite <- (app_nil_l (!x::_)); rewrite <- app_nil_l.
      apply perm_bang_t_swap_l.
    + eapply perm_bang_t_trans_l; eassumption.
  Qed.

End perm_bang_t.

