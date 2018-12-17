(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Bool List Relations Wf Eqdep_dec Omega.

Set Implicit Arguments.

(* Notations for subset or subrel set theoretic operators *)

Notation "X '⊆' Y" := (forall x, X x -> Y x) (at level 75, format "X  ⊆  Y", no associativity).
Notation "X '≃' Y" := (X ⊆ Y /\ Y ⊆ X) (at level 75, format "X  ≃  Y", no associativity).

Fact inc1_refl X (A : X -> Prop) : A ⊆ A.
Proof. auto. Qed.

Fact inc1_trans X (A B C : X -> Prop) : A ⊆ B -> B ⊆ C -> A ⊆ C.
Proof. intros; auto. Qed.

Fact eq1_refl X (A : X -> Prop) : A ≃ A.
Proof. tauto. Qed.

Fact eq1_sym X (A B : X -> Prop) : A ≃ B -> B ≃ A.
Proof. tauto. Qed.

Fact eq1_trans X (A B C : X -> Prop) : A ≃ B -> B ≃ C -> A ≃ C.
Proof. intros [] [];  split; intros; auto. Qed.

Fact equal_eq1 X (A B : X -> Prop) : A = B -> A ≃ B.
Proof. intros []; auto. Qed.

(* intersection *)

Notation "A '∩' B" := (fun z => A z /\ B z) (at level 50, format "A  ∩  B", left associativity).
Notation "A '∪' B" := (fun z => A z \/ B z) (at level 50, format "A  ∪  B", left associativity).

(** ⊆ ≃ ∩ ∪ *)

Notation sg := (@eq _).

Fact sg_inc1 X (A : X -> Prop) : forall x, A x <-> sg x ⊆ A.
Proof. 
  intros x; split.
  + intros ? ? []; trivial.
  + intros H; apply H; auto. 
Qed.

