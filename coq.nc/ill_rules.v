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

Local Infix "~p" := (@perm_t _) (at level 70).

Reserved Notation "l '⊢' x" (at level 70, no associativity).

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ *)

Inductive ill_proof : list ill_form -> ill_form -> Type :=

  (* These are the SILL rules in the paper *)

  | in_llp_ax     : forall A,                         A::∅ ⊢ A

  | in_llp_perm   : forall Γ Δ A B C,              Γ++!A::!B::Δ ⊢ C 
                                           (*-----------------------------*)
                                      ->           Γ++!B::!A::Δ ⊢ C 

  | in_llp_limp_l : forall Γ Δ ϴ A B C,          Γ ⊢ A    ->  ϴ++B::Δ ⊢ C
                                           (*-----------------------------*)    
                                      ->           ϴ++Γ++A -o B::Δ ⊢ C

  | in_llp_limp_r : forall Γ A B,                    A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->            Γ ⊢ A -o B

  | in_llp_rimp_l : forall Γ Δ ϴ A B C,          Γ ⊢ A      ->  ϴ++B::Δ ⊢ C
                                           (*-----------------------------*)    
                                      ->           ϴ++B o- A::Γ++Δ ⊢ C

  | in_llp_rimp_r : forall Γ A B,                    Γ++A::nil ⊢ B
                                           (*-----------------------------*)
                                      ->            Γ ⊢ B o- A

  | in_llp_with_l1 : forall Γ Δ A B C,                 Γ++A::Δ ⊢ C 
                                           (*-----------------------------*)
                                      ->           Γ++A﹠B::Δ ⊢ C

  | in_llp_with_l2 : forall Γ Δ A B C,                  Γ++B::Δ ⊢ C 
                                           (*-----------------------------*)
                                      ->           Γ++A﹠B::Δ ⊢ C
 
  | in_llp_with_r : forall Γ A B,               Γ ⊢ A     ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B

  | in_llp_bang_l : forall Γ Δ A B,                 Γ++A::Δ ⊢ B
                                           (*-----------------------------*)
                                      ->            Γ++!A::Δ ⊢ B

  | in_llp_bang_r : forall Γ A,                       ‼Γ ⊢ A
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ !A

  | in_llp_weak : forall Γ Δ A B,                        Γ++Δ ⊢ B
                                           (*-----------------------------*)
                                      ->           Γ++!A::Δ ⊢ B

  | in_llp_cntr : forall Γ Δ A B,                    Γ++!A::!A::Δ ⊢ B
                                           (*-----------------------------*)
                                      ->             Γ++!A::Δ ⊢ B

  (* These are the other rule for a complete sequent calculus for the whole ILL *)

  | in_llp_cut : forall Γ Δ ϴ A B,               Γ ⊢ A    ->   Δ++A::ϴ ⊢ B
                                           (*-----------------------------*)    
                                      ->              Δ++Γ++ϴ ⊢ B

  | in_llp_times_l : forall Γ Δ A B C,               Γ++A::B::Δ ⊢ C 
                                           (*-----------------------------*)
                                      ->            Γ++A⊗B::Δ ⊢ C
 
  | in_llp_times_r : forall Γ Δ A B,             Γ ⊢ A    ->   Δ ⊢ B
                                           (*-----------------------------*)
                                      ->              Γ++Δ ⊢ A⊗B

  | in_llp_plus_l :  forall Γ Δ A B C,            Γ++A::Δ ⊢ C  ->  Γ++B::Δ ⊢ C 
                                           (*-----------------------------*)
                                      ->            Γ++A⊕B::Δ ⊢ C

  | in_llp_plus_r1 : forall Γ A B,                    Γ ⊢ A  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B

  | in_llp_plus_r2 : forall Γ A B,                    Γ ⊢ B  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B

  | in_llp_bot_l : forall Γ Δ A,                     Γ++⟘::Δ ⊢ A

  | in_llp_top_r : forall Γ,                          Γ ⊢ ⟙

  | in_llp_unit_l : forall Γ Δ A,                       Γ++Δ ⊢ A  
                                           (*-----------------------------*)
                                      ->           Γ++𝝐 ::Δ ⊢ A

  | in_llp_unit_r :                                   ∅ ⊢ 𝝐

where "l ⊢ x" := (ill_proof l x).

Fixpoint ill_cut_free Γ A (p : Γ ⊢ A) :=
  match p with
    | in_llp_ax _                => True
    | in_llp_perm  _ _ _ _ p     => ill_cut_free p 
    | in_llp_limp_l _ _ _ p q    => ill_cut_free p /\ ill_cut_free q
    | in_llp_limp_r p            => ill_cut_free p 
    | in_llp_rimp_l _ _ _ p q    => ill_cut_free p /\ ill_cut_free q
    | in_llp_rimp_r _ _ p        => ill_cut_free p 
    | in_llp_with_l1 _ _ _ _ p         => ill_cut_free p
    | in_llp_with_l2 _ _ _ _ p         => ill_cut_free p  
    | in_llp_with_r p q    => ill_cut_free p /\ ill_cut_free q
    | in_llp_bang_l _ _ _ p      => ill_cut_free p
    | in_llp_bang_r _ p    => ill_cut_free p 
    | in_llp_weak _ _ _ p      => ill_cut_free p 
    | in_llp_cntr _ _ _ p        => ill_cut_free p 
    | in_llp_cut _ _ _ _       => False
    | in_llp_times_l _ _ _ _ p     => ill_cut_free p  
    | in_llp_times_r p q   => ill_cut_free p /\ ill_cut_free q
    | in_llp_plus_l _ _ _ _ p q    => ill_cut_free p /\ ill_cut_free q
    | in_llp_plus_r1 _ p   => ill_cut_free p
    | in_llp_plus_r2 _ p   => ill_cut_free p
    | in_llp_bot_l _ _ _      => True
    | in_llp_top_r _       => True
    | in_llp_unit_l _ _ p      => ill_cut_free p
    | in_llp_unit_r        => True
  end. 

Definition ill_cf_provable Γ A := { p : Γ ⊢ A | ill_cut_free p }.

Notation "Γ '⊢cf' A" := (ill_cf_provable Γ A) (at level 70, no associativity).

Fact ill_cf_ax A : A::∅ ⊢cf A.
Proof. exists (in_llp_ax A); simpl; auto. Qed.

Fact ill_cf_perm Γ Δ A B C : Γ++!A::!B::Δ ⊢cf C -> Γ++!B::!A::Δ ⊢cf C. 
Proof. intros [p]; exists (in_llp_perm _ _ _ _ p); simpl; auto. Qed.

Fact ill_cf_limp_l Γ Δ ϴ A B C : Γ ⊢cf A -> ϴ++B::Δ ⊢cf C -> ϴ++Γ++A -o B::Δ ⊢cf C.
Proof. intros [p] [q]; exists (in_llp_limp_l _ _ _ p q); simpl; auto. Qed.

Fact ill_cf_limp_r Γ A B : A::Γ ⊢cf B -> Γ ⊢cf A -o B.
Proof. intros [p]; exists (in_llp_limp_r p); simpl; auto. Qed.

Fact ill_cf_rimp_l Γ Δ ϴ A B C : Γ ⊢cf A -> ϴ++B::Δ ⊢cf C -> ϴ++B o- A::Γ++Δ ⊢cf C.
Proof. intros [p] [q]; exists (in_llp_rimp_l _ _ _ p q); simpl; auto. Qed.

Fact ill_cf_rimp_r Γ A B : Γ++A::nil ⊢cf B -> Γ ⊢cf B o- A.
Proof. intros [p]; exists (in_llp_rimp_r _ _ p); simpl; auto. Qed.

Fact ill_cf_with_l1 Γ Δ A B C :  Γ++A::Δ ⊢cf C -> Γ++A﹠B::Δ ⊢cf C.
Proof. intros [p]; exists (in_llp_with_l1 _ _ _ _ p); simpl; auto. Qed.

Fact ill_cf_with_l2 Γ Δ A B C :  Γ++B::Δ ⊢cf C -> Γ++A﹠B::Δ ⊢cf C.
Proof. intros [p]; exists (in_llp_with_l2 _ _ _ _ p); simpl; auto. Qed.

Fact ill_cf_with_r Γ A B : Γ ⊢cf A -> Γ ⊢cf B -> Γ ⊢cf A﹠B.
Proof. intros [p] [q]; exists (in_llp_with_r p q); simpl; auto. Qed.

Fact ill_cf_bang_l Γ Δ A B : Γ++A::Δ ⊢cf B -> Γ++!A::Δ ⊢cf B.
Proof. intros [p]; exists (in_llp_bang_l _ _ _ p); simpl; auto. Qed.

Fact ill_cf_bang_r Γ A : ‼Γ ⊢cf A -> ‼Γ ⊢cf !A.
Proof. intros [p]; exists (in_llp_bang_r _ p); simpl; auto. Qed.

Fact ill_cf_weak Γ Δ A B : Γ++Δ ⊢cf B -> Γ++!A::Δ ⊢cf B.
Proof. intros [p]; exists (in_llp_weak _ _ _ p); simpl; auto. Qed.

Fact ill_cf_cntr Γ Δ A B : Γ++!A::!A::Δ ⊢cf B -> Γ++!A::Δ ⊢cf B.
Proof. intros [p]; exists (in_llp_cntr _ _ _ p); simpl; auto. Qed.

Fact ill_cf_times_l Γ Δ A B C : Γ++A::B::Δ ⊢cf C -> Γ++A⊗B::Δ ⊢cf C.
Proof. intros [p]; exists (in_llp_times_l _ _ _ _ p); simpl; auto. Qed.

Fact ill_cf_times_r Γ Δ A B : Γ ⊢cf A -> Δ ⊢cf B -> Γ++Δ ⊢cf A⊗B.
Proof. intros [p] [q]; exists (in_llp_times_r p q); simpl; auto. Qed.

Fact ill_cf_plus_l Γ Δ A B C : Γ++A::Δ ⊢cf C -> Γ++B::Δ ⊢cf C -> Γ++A⊕B::Δ ⊢cf C.
Proof. intros [p] [q]; exists (in_llp_plus_l _ _ _ _ p q); simpl; auto. Qed.

Fact ill_cf_plus_r1 Γ A B : Γ ⊢cf A -> Γ ⊢cf A⊕B.
Proof. intros [p]; exists (in_llp_plus_r1 _ p); simpl; auto. Qed.

Fact ill_cf_plus_r2 Γ A B : Γ ⊢cf B -> Γ ⊢cf A⊕B.
Proof. intros [p]; exists (in_llp_plus_r2 _ p); simpl; auto. Qed.

Fact ill_cf_bot_l Γ Δ A : Γ++⟘::Δ ⊢cf A.
Proof. exists (in_llp_bot_l _ _ _); simpl; auto. Qed.

Fact ill_cf_top_r Γ : Γ ⊢cf ⟙.
Proof. exists (in_llp_top_r _); simpl; auto. Qed.

Fact ill_cf_unit_l Γ Δ A : Γ++Δ ⊢cf A -> Γ++𝝐::Δ ⊢cf A.
Proof. intros [p]; exists (in_llp_unit_l _ _ p); simpl; auto. Qed.

Fact ill_cf_unit_r : ∅ ⊢cf 𝝐.
Proof. exists (in_llp_unit_r); simpl; auto. Qed.

Fact ill_cf_weak_ctx Γ ϴ Δ A : Γ++Δ ⊢cf A -> Γ++‼ϴ++Δ ⊢cf A.
Proof.
  intros H.
  induction ϴ as [ | B th IH ]; simpl; auto.
  apply ill_cf_weak; auto.
Qed.

Fact ill_cf_perm_ctx Γ Ω ϴ Δ C : Ω ~p ϴ -> Γ++‼Ω++Δ ⊢cf C -> Γ++‼ϴ++Δ ⊢cf C.
Proof.
  intros H; revert H Γ; induction 1 as [ | A Om Th H1 IH1 | A B Th | Th1 Th2 Th3 H1 IH1 H2 IH2 ]; simpl; intros Ga H; auto.
  + replace (Ga++!A::‼Th++Δ) with ((Ga++!A::nil)++‼Th++Δ) by solve list eq.
    apply IH1.
    rewrite app_ass; simpl; auto.
  + apply ill_cf_perm; auto.
Qed.

Fact ill_cf_cntr_ctx Γ ϴ Δ A : Γ++‼ϴ++‼ϴ++Δ ⊢cf A -> Γ++‼ϴ++Δ ⊢cf A.
Proof.
  revert Γ; induction ϴ as [ | B Th IH ]; simpl; auto; intros Ga H.
  replace (Ga++!B::‼Th++Δ) with ((Ga++!B::nil)++‼Th++Δ) by solve list eq.
  apply IH; rewrite app_ass; simpl.
  apply ill_cf_cntr.
  revert H.
  replace (Ga++!B::‼Th++!B::‼Th++Δ) with (Ga++‼(B::Th++B::Th)++Δ).
  2: { unfold ill_lbang; simpl; rewrite map_app; solve list eq. }
  replace (Ga++!B::!B::‼Th++‼Th++Δ) with (Ga++‼(B::B::Th++Th)++Δ).
  2: { unfold ill_lbang; simpl; rewrite map_app; solve list eq. }
  apply ill_cf_perm_ctx, perm_t_cons, perm_t_sym, perm_t_middle.
Qed.

