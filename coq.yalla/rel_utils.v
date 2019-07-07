(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Set Implicit Arguments.

(* Notations for subset or subrel set theoretic operators *)

Definition subset K (X Y : K -> Type) := forall x, X x -> Y x.

Notation "X '⊆' Y" := (subset X Y) (at level 75, format "X  ⊆  Y", no associativity).
Notation "X '≃' Y" := ((X ⊆ Y) * (Y ⊆ X))%type (at level 75, format "X  ≃  Y", no associativity).

Fact inc1_refl X (A : X -> Type) : A ⊆ A.
Proof. red; auto. Qed.

Fact inc1_trans X (A B C : X -> Type) : A ⊆ B -> B ⊆ C -> A ⊆ C.
Proof. intros H1 H2 x; auto. Qed.

Fact eq1_refl X (A : X -> Type) : A ≃ A.
Proof. split; red; auto. Qed.

Fact eq1_sym X (A B : X -> Type) : A ≃ B -> B ≃ A.
Proof. tauto. Qed.

Fact eq1_trans X (A B C : X -> _) : A ≃ B -> B ≃ C -> A ≃ C.
Proof. intros [] []; split; intros; red; auto. Qed.

Hint Resolve inc1_refl inc1_trans
             eq1_refl eq1_trans.

Hint Immediate eq1_sym.

Fact equal_eq1 X (A B : X -> _) : A = B -> A ≃ B.
Proof. intros []; split; red; auto. Qed.

(* intersection *)

Notation "A '∩' B" := (fun z => A z * B z : Type)%type (at level 50, format "A  ∩  B", left associativity).
Notation "A '∪' B" := (fun z => A z + B z : Type)%type (at level 50, format "A  ∪  B", left associativity).

(** ⊆ ≃ ∩ ∪ *)

Notation "X '≡' Y" := ((X->Y)*(Y->X))%type (at level 80, format "X  ≡  Y", no associativity).

Notation sg := (@eq _).

Fact sg_inc1 X (A : X -> Type) x : A x ≡ sg x ⊆ A. 
Proof. 
  split.
  + intros ? ? []; trivial.
  + intros H; apply H; auto. 
Qed.

