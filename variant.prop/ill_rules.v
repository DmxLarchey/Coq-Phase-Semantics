(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Omega.

Require Import utils ill_form.

Set Implicit Arguments.

Local Infix "~p" := (@Permutation _) (at level 70).

Reserved Notation "l '⊢' x" (at level 70, no associativity).

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ *)

Inductive ill_proof : list ill_form -> ill_form -> Type :=

  (* These are the SILL rules in the paper *)

  | in_llp_ax     : forall A,                         A::∅ ⊢ A

  | in_llp_perm   : forall Γ Δ A,              Γ ~p Δ     ->   Γ ⊢ A 
                                           (*-----------------------------*)
                                      ->                 Δ ⊢ A

  | in_llp_limp_l : forall Γ Δ A B C,          Γ ⊢ A      ->   B::Δ ⊢ C
                                           (*-----------------------------*)    
                                      ->           A -o B::Γ++Δ ⊢ C

  | in_llp_limp_r : forall Γ A B,                    A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->            Γ ⊢ A -o B

  | in_llp_with_l1 : forall Γ A B C,                  A::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C

  | in_llp_with_l2 : forall Γ A B C,                  B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ C
 
  | in_llp_with_r : forall Γ A B,               Γ ⊢ A     ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B

  | in_llp_bang_l : forall Γ A B,                    A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->            !A::Γ ⊢ B

  | in_llp_bang_r : forall Γ A,                       ‼Γ ⊢ A
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ !A

  | in_llp_weak : forall Γ A B,                        Γ ⊢ B
                                           (*-----------------------------*)
                                      ->           !A::Γ ⊢ B

  | in_llp_cntr : forall Γ A B,                    !A::!A::!A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->             !A::!A::Γ ⊢ B

  (* These are the other rule for a complete sequent calculus for the whole ILL *)

  | in_llp_cut : forall Γ Δ A B,                 Γ ⊢ A    ->   A::Δ ⊢ B
                                           (*-----------------------------*)    
                                      ->              Γ++Δ ⊢ B

  | in_llp_times_l : forall Γ A B C,               A::B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->            A⊗B::Γ ⊢ C
 
  | in_llp_times_r : forall Γ Δ A B,             Γ ⊢ A    ->   Δ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ++Δ ⊢ A⊗B

  | in_llp_plus_l :  forall Γ A B C,            A::Γ ⊢ C  ->  B::Γ ⊢ C 
                                           (*-----------------------------*)
                                      ->            A⊕B::Γ ⊢ C

  | in_llp_plus_r1 : forall Γ A B,                    Γ ⊢ A  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B

  | in_llp_plus_r2 : forall Γ A B,                    Γ ⊢ B  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B

  | in_llp_bot_l : forall Γ A,                     ⟘::Γ ⊢ A

  | in_llp_top_r : forall Γ,                          Γ ⊢ ⟙

  | in_llp_unit_l : forall Γ A,                       Γ ⊢ A  
                                           (*-----------------------------*)
                                      ->           𝝐 ::Γ ⊢ A

  | in_llp_unit_r :                                   ∅ ⊢ 𝝐

where "l ⊢ x" := (ill_proof l x).

Fixpoint ill_cut_free Γ A (p : Γ ⊢ A) :=
  match p with
    | in_llp_ax _          => True
    | in_llp_perm H1 p     => ill_cut_free p 
    | in_llp_limp_l p q    => ill_cut_free p /\ ill_cut_free q
    | in_llp_limp_r p      => ill_cut_free p 
    | in_llp_with_l1 _ p   => ill_cut_free p
    | in_llp_with_l2 _ p   => ill_cut_free p  
    | in_llp_with_r p q    => ill_cut_free p /\ ill_cut_free q
    | in_llp_bang_l p      => ill_cut_free p
    | in_llp_bang_r _ p    => ill_cut_free p 
    | in_llp_weak _ p      => ill_cut_free p 
    | in_llp_cntr p        => ill_cut_free p 
    | in_llp_cut _ _       => False
    | in_llp_times_l p     => ill_cut_free p  
    | in_llp_times_r p q   => ill_cut_free p /\ ill_cut_free q
    | in_llp_plus_l p q    => ill_cut_free p /\ ill_cut_free q
    | in_llp_plus_r1 _ p   => ill_cut_free p
    | in_llp_plus_r2 _ p   => ill_cut_free p
    | in_llp_bot_l _ _     => True
    | in_llp_top_r _       => True
    | in_llp_unit_l p      => ill_cut_free p
    | in_llp_unit_r        => True
  end. 

Definition ill_cf_provable Γ A := (∃ p : Γ ⊢ A, ill_cut_free p).

Notation "Γ '⊢cf' A" := (ill_cf_provable Γ A) (at level 70, no associativity).

Fact ill_cf_ax A : A::∅ ⊢cf A.
Proof. exists (in_llp_ax A); simpl; auto. Qed.

Fact ill_cf_perm Γ Δ A : Γ ~p Δ -> Γ ⊢cf A -> Δ ⊢cf A.
Proof. intros H1 [p]; exists (in_llp_perm H1 p); simpl; auto. Qed.

Fact ill_cf_limp_l Γ Δ A B C : Γ ⊢cf A -> B::Δ ⊢cf C -> A -o B::Γ++Δ ⊢cf C.
Proof. intros [p] [q]; exists (in_llp_limp_l p q); simpl; auto. Qed.

Fact ill_cf_limp_r Γ A B : A::Γ ⊢cf B -> Γ ⊢cf A -o B.
Proof. intros [p]; exists (in_llp_limp_r p); simpl; auto. Qed.

Fact ill_cf_with_l1 Γ A B C : A::Γ ⊢cf C -> A﹠B::Γ ⊢cf C.
Proof. intros [p]; exists (in_llp_with_l1 B p); simpl; auto. Qed.

Fact ill_cf_with_l2 Γ A B C : B::Γ ⊢cf C -> A﹠B::Γ ⊢cf C.
Proof. intros [p]; exists (in_llp_with_l2 A p); simpl; auto. Qed.

Fact ill_cf_with_r Γ A B : Γ ⊢cf A -> Γ ⊢cf B -> Γ ⊢cf A﹠B.
Proof. intros [p] [q]; exists (in_llp_with_r p q); simpl; auto. Qed.

Fact ill_cf_bang_l Γ A B : A::Γ ⊢cf B -> !A::Γ ⊢cf B.
Proof. intros [p]; exists (in_llp_bang_l p); simpl; auto. Qed.

Fact ill_cf_bang_r Γ A : ‼Γ ⊢cf A -> ‼Γ ⊢cf !A.
Proof. intros [p]; exists (in_llp_bang_r _ p); simpl; auto. Qed.

Fact ill_cf_weak Γ A B : Γ ⊢cf B -> !A::Γ ⊢cf B.
Proof. intros [p]; exists (in_llp_weak A p); simpl; auto. Qed.
  
Fact ill_cf_cntr Γ A B : !A::!A::!A::Γ ⊢cf B -> !A::!A::Γ ⊢cf B.
Proof. intros [p]; exists (in_llp_cntr p); simpl; auto. Qed.

Fact ill_cf_times_l Γ A B C : A::B::Γ ⊢cf C -> A⊗B::Γ ⊢cf C.
Proof. intros [p]; exists (in_llp_times_l p); simpl; auto. Qed.

Fact ill_cf_times_r Γ Δ A B : Γ ⊢cf A -> Δ ⊢cf B -> Γ++Δ ⊢cf A⊗B.
Proof. intros [p] [q]; exists (in_llp_times_r p q); simpl; auto. Qed.

Fact ill_cf_plus_l Γ A B C : A::Γ ⊢cf C -> B::Γ ⊢cf C -> A⊕B::Γ ⊢cf C.
Proof. intros [p] [q]; exists (in_llp_plus_l p q); simpl; auto. Qed.

Fact ill_cf_plus_r1 Γ A B : Γ ⊢cf A -> Γ ⊢cf A⊕B.
Proof. intros [p]; exists (in_llp_plus_r1 _ p); simpl; auto. Qed.

Fact ill_cf_plus_r2 Γ A B : Γ ⊢cf B -> Γ ⊢cf A⊕B.
Proof. intros [p]; exists (in_llp_plus_r2 _ p); simpl; auto. Qed.

Fact ill_cf_bot_l Γ A : ⟘::Γ ⊢cf A.
Proof. exists (in_llp_bot_l _ _); simpl; auto. Qed.

Fact ill_cf_top_r Γ : Γ ⊢cf ⟙.
Proof. exists (in_llp_top_r _); simpl; auto. Qed.

Fact ill_cf_unit_l Γ A : Γ ⊢cf A -> 𝝐 ::Γ ⊢cf A.
Proof. intros [p]; exists (in_llp_unit_l p); simpl; auto. Qed.

Fact ill_cf_unit_r : ∅ ⊢cf 𝝐.
Proof. exists (in_llp_unit_r); simpl; auto. Qed.

Fact ill_cf_weak_ctx Γ Δ A : Δ ⊢cf A -> ‼Γ++Δ ⊢cf A.
Proof.
  intros H.
  induction Γ as [ | B ga IH ]; simpl; auto.
  apply ill_cf_weak; auto.
Qed.

Fact ill_cf_cntr_ctx Γ Δ A : ‼Γ++‼Γ++‼Γ++Δ ⊢cf A -> ‼Γ++‼Γ++Δ ⊢cf A.
Proof.
  revert Δ.
  induction Γ as [ | B ga IH ]; simpl; auto; intros de H.
  apply ill_cf_perm with (‼ga++‼ga++!B::!B::de).
  { apply Permutation_sym, 
          Permutation_trans with (1 := Permutation_middle _ _ _),
          Permutation_app; auto.
    apply Permutation_trans with (1 := Permutation_middle (_::_) _ _); simpl.
    apply Permutation_middle. }
  apply IH.
  apply ill_cf_perm with (!B::!B::‼ga++‼ga++‼ga++de).
  { apply Permutation_sym; focus (!B); apply Permutation_sym.
    apply Permutation_cons_app; rewrite app_assoc; auto.
    rewrite <- app_ass. 
    apply Permutation_trans with (1 := Permutation_middle _ _ _).
    repeat rewrite app_ass; auto. }
  apply ill_cf_cntr.
  revert H; apply ill_cf_perm.
  constructor 2.
  apply Permutation_sym, Permutation_cons_app; auto.
  rewrite <- app_ass.
  apply Permutation_trans with (1 := Permutation_middle _ _ _).
  repeat rewrite app_ass; auto.
Qed.
