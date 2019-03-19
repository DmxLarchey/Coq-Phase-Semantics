(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Omega Bool.

Require Import utils ill_form.

Set Implicit Arguments.

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ *)

Reserved Notation "l '⊢' x [ a , b ]" (at level 70, no associativity).

(* First Boolean is commutative (or not) 
   Second Boolean is with or without cut. *)

  Inductive ill_proof : bool -> bool -> list ill_form -> ill_form -> Type :=

  (* These are the SILL rules in the paper *)

  | in_llp_ax     : forall s1 s2 A,                         A::∅ ⊢ A [s1,s2]


  | in_llp_cut : forall s1 Γ Δ ϴ A B,                       Γ ⊢ A [s1,true]
                                                 ->   Δ++A::ϴ ⊢ B [s1,true]
                                           (*-----------------------------*)    
                                      ->              Δ++Γ++ϴ ⊢ B [s1,true]

  | in_llp_perm : forall s1 s2 Γ Δ A,        Γ ~[s1] Δ ->   Γ ⊢ A [s1,s2]
                                                       ->   Δ ⊢ A [s1,s2]

 (*          Γ++!A::!B::Δ ⊢ C [false,s2]
                                               (*-----------------------------*)
                                            ->           Γ++!B::!A::Δ ⊢ C [false,s2]

  | in_llp_perm_co : forall s2 Γ Δ A B C,                Γ++A::B::Δ ⊢ C [true,s2]
                                               (*-----------------------------*)
                                            ->           Γ++B::A::Δ ⊢ C [true,s2]

 *)

  | in_llp_limp_l : forall s1 s2 Γ Δ ϴ A B C,                    Γ ⊢ A [s1,s2]
                                                       ->  ϴ++B::Δ ⊢ C [s1,s2]
                                           (*-----------------------------*)    
                                      ->           ϴ++Γ++A -o B::Δ ⊢ C [s1,s2]

  | in_llp_limp_r : forall s1 s2 Γ A B,                    A::Γ ⊢ B       [s1,s2]
                                           (*-----------------------------*)
                                                ->            Γ ⊢ A -o B  [s1,s2]

  | in_llp_rimp_l : forall s1 s2 Γ Δ ϴ A B C,                    Γ ⊢ A [s1,s2]
                                                ->         ϴ++B::Δ ⊢ C [s1,s2]
                                           (*-----------------------------*)    
                                      ->           ϴ++B o- A::Γ++Δ ⊢ C [s1,s2]

  | in_llp_rimp_r : forall s1 s2 Γ A B,              Γ++A::nil ⊢ B      [s1,s2]
                                           (*-----------------------------*)
                                      ->                     Γ ⊢ B o- A [s1,s2]

  | in_llp_with_l1 : forall s1 s2 Γ Δ A B C,           Γ++A::Δ ⊢ C [s1,s2]
                                           (*-----------------------------*)
                                      ->            Γ++A﹠B::Δ ⊢ C [s1,s2]

  | in_llp_with_l2 : forall s1 s2 Γ Δ A B C,          Γ++B::Δ ⊢ C [s1,s2] 
                                           (*-----------------------------*)
                                      ->           Γ++A﹠B::Δ ⊢ C [s1,s2]
 
  | in_llp_with_r : forall s1 s2 Γ A B,               Γ ⊢ A      [s1,s2]
                                      ->              Γ ⊢ B      [s1,s2]
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B   [s1,s2]

  | in_llp_bang_l : forall s1 s2 Γ Δ A B,            Γ++A::Δ ⊢ B [s1,s2]
                                           (*-----------------------------*)
                                      ->            Γ++!A::Δ ⊢ B [s1,s2]

  | in_llp_bang_r : forall s1 s2 Γ A,                 ‼Γ ⊢ A  [s1,s2] 
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ !A [s1,s2]

  | in_llp_weak : forall s1 s2 Γ Δ A B,                Γ++Δ ⊢ B [s1,s2]
                                           (*-----------------------------*)
                                      ->           Γ++!A::Δ ⊢ B [s1,s2]

  | in_llp_cntr : forall s1 s2 Γ Δ A B,          Γ++!A::!A::Δ ⊢ B [s1,s2]
                                           (*-----------------------------*)
                                      ->             Γ++!A::Δ ⊢ B [s1,s2]

  | in_llp_times_l : forall s1 s2 Γ Δ A B C,       Γ++A::B::Δ ⊢ C [s1,s2] 
                                           (*-----------------------------*)
                                      ->            Γ++A⊗B::Δ ⊢ C [s1,s2]
 
  | in_llp_times_r : forall s1 s2 Γ Δ A B,               Γ ⊢ A   [s1,s2]
                                      ->                 Δ ⊢ B   [s1,s2]
                                           (*-----------------------------*)
                                      ->              Γ++Δ ⊢ A⊗B [s1,s2]

  | in_llp_plus_l :  forall s1 s2 Γ Δ A B C,            Γ++A::Δ ⊢ C [s1,s2]
                                      ->                Γ++B::Δ ⊢ C [s1,s2] 
                                           (*-----------------------------*)
                                      ->              Γ++A⊕B::Δ ⊢ C [s1,s2]

  | in_llp_plus_r1 : forall s1 s2 Γ A B,              Γ ⊢ A   [s1,s2]  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B [s1,s2]

  | in_llp_plus_r2 : forall s1 s2 Γ A B,              Γ ⊢   B [s1,s2]  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B [s1,s2]

  | in_llp_bot_l : forall s1 s2 Γ Δ A,          Γ++⟘::Δ ⊢ A  [s1,s2]

  | in_llp_top_r : forall s1 s2 Γ,                         Γ ⊢ ⟙  [s1,s2]

  | in_llp_unit_l : forall s1 s2 Γ Δ A,               Γ++Δ ⊢ A [s1,s2]
                                           (*-----------------------------*)
                                      ->           Γ++𝝐 ::Δ ⊢ A [s1,s2]

  | in_llp_unit_r : forall s1 s2,                        ∅ ⊢ 𝝐  [s1,s2]

where "l ⊢ x [ s1 , s2 ]" := (ill_proof s1 s2 l x).

Notation "l ⊢ x '[comm,cut]'" := (ill_proof true true l x) (at level 70).
Notation "l ⊢ x '[comm,cutfree]'" := (ill_proof true false l x) (at level 70).
Notation "l ⊢ x '[nc,cut]'" := (ill_proof false true l x) (at level 70).
Notation "l ⊢ x '[nc,cutfree]'" := (ill_proof false false l x) (at level 70).

Fact ill_weak_ctx s1 s2 Γ ϴ Δ A : Γ++    Δ ⊢ A [s1,s2]  
                               -> Γ++‼ϴ++Δ ⊢ A [s1,s2].
Proof.
  intros H.
  induction ϴ as [ | B th IH ]; simpl; auto.
  apply in_llp_weak; auto.
Qed.

Fact ill_perm_ctx s1 s2 Γ Ω ϴ Δ C : Ω ~p ϴ 
                                -> Γ++‼Ω++Δ ⊢ C [s1,s2] 
                                -> Γ++‼ϴ++Δ ⊢ C [s1,s2].
Proof.
  intros H; revert H Γ; induction 1 as [ | A Om Th H1 IH1 | A B Th | Th1 Th2 Th3 H1 IH1 H2 IH2 ]; simpl; intros Ga H; auto.
  + replace (Ga++!A::‼Th++Δ) with ((Ga++!A::nil)++‼Th++Δ) by solve list eq.
    apply IH1; rewrite app_ass; simpl; auto.
  + revert H; apply in_llp_perm.
    apply ill_perm_t_app; auto.
    apply ill_perm_t_swap.
Qed.

Fact ill_cntr_ctx s1 s2 Γ ϴ Δ A : Γ++‼ϴ++‼ϴ++Δ ⊢ A [s1,s2] -> Γ++‼ϴ++Δ ⊢ A [s1,s2].
Proof.
  revert Γ; induction ϴ as [ | B Th IH ]; simpl; auto; intros Ga H.
  replace (Ga++!B::‼Th++Δ) with ((Ga++!B::nil)++‼Th++Δ) by solve list eq.
  apply IH; rewrite app_ass; simpl.
  apply in_llp_cntr.
  revert H.
  replace (Ga++!B::‼Th++!B::‼Th++Δ) with (Ga++‼(B::Th++B::Th)++Δ).
  2: { unfold ill_lbang; simpl; rewrite map_app; solve list eq. }
  replace (Ga++!B::!B::‼Th++‼Th++Δ) with (Ga++‼(B::B::Th++Th)++Δ).
  2: { unfold ill_lbang; simpl; rewrite map_app; solve list eq. }
  apply ill_perm_ctx, perm_t_cons, perm_t_sym, perm_t_middle.
Qed.

(*

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

*)

Section cut_free.

  Variable s : bool.

  (* [wc] := without cut, either commutative or non-commutative 
     [co,wc] := commutative and without cut
     [nc,wc] := non-commutative and without-cut *)

  Notation "Γ '⊢' A '[wc]'" := (ill_proof s false Γ A) (at level 70, no associativity).
  Notation "Γ '⊢' A '[co,wc]'" := (ill_proof true false Γ A) (at level 70, no associativity).
  Notation "Γ '⊢' A '[nc,wc]'" := (ill_proof false false Γ A) (at level 70, no associativity).

  Fact ill_cf_ax A : A::∅ ⊢ A [wc].
  Proof. apply in_llp_ax. Qed.

  Fact illnc_cf_perm Γ Δ A B C : Γ++!A::!B::Δ ⊢ C [nc,wc]
                              -> Γ++!B::!A::Δ ⊢ C [nc,wc].
  Proof. 
    apply in_llp_perm; simpl.
    apply perm_bang_t_app; auto.
    constructor 3.
  Qed.

  Fact ill_cf_perm Γ Δ A B C : Γ++A::B::Δ ⊢ C [co,wc]
                            -> Γ++B::A::Δ ⊢ C [co,wc].
  Proof. 
    apply in_llp_perm; simpl.
    apply perm_t_app.
    + apply perm_t_refl.
    + constructor 3.
  Qed.

  Fact ill_cf_limp_l Γ Δ ϴ A B C :           Γ ⊢ A [wc] 
                            ->         ϴ++B::Δ ⊢ C [wc]
                            -> ϴ++Γ++A -o B::Δ ⊢ C [wc].
  Proof. apply in_llp_limp_l. Qed.

(*
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

*)

  Fact ill_cf_perm_ctx Γ Ω ϴ Δ C : Ω ~p ϴ 
                                -> Γ++‼Ω++Δ ⊢ C [wc] 
                                -> Γ++‼ϴ++Δ ⊢ C [wc].
  Proof.
    intros H; revert H Γ; induction 1 as [ | A Om Th H1 IH1 | A B Th | Th1 Th2 Th3 H1 IH1 H2 IH2 ]; simpl; intros Ga H; auto.
    + replace (Ga++!A::‼Th++Δ) with ((Ga++!A::nil)++‼Th++Δ) by solve list eq.
      apply IH1; rewrite app_ass; simpl; auto.
    + revert H; destruct s.
      * apply ill_cf_perm.
      * apply illnc_cf_perm.
  Qed.

  Section ill_cf_perm_bang_t.

    Let gen Γ Δ Ω C : Γ ~! Δ -> Ω++Γ ⊢ C [wc] -> Ω++Δ ⊢ C [wc].
    Proof.
      intros H; revert H Ω C; induction 1 as [ | A Ga De H1 IH1 | A B Ga | Ga De Th ]; intros Om C; auto.
      + intros H.
        replace (Om++A::De) with ((Om++A::nil)++De).
        apply IH1.
        all: rewrite app_ass; auto.
      + apply ill_cf_perm_ctx with (Γ := Om) (Ω := _::_::nil) (ϴ := _::_::nil) (Δ := Ga).
        constructor; auto.
    Qed.

    Fact ill_cf_perm_bang_t Γ Δ C : Γ ~! Δ -> Γ ⊢ C [wc] -> Δ ⊢ C [wc].
    Proof. apply gen with (Ω := nil). Qed.

  End ill_cf_perm_bang_t.

 
End cut_free.

Section ill_commutative.

  Variable s : bool.

  Notation "Γ '⊢' A '[co]'" := (ill_proof true s Γ A) (at level 70, no associativity).

  Fact ill_co_imp1 A B : A -o B :: nil ⊢ B o- A [co].
  Proof.
    apply in_llp_rimp_r; simpl.
    apply in_llp_perm with (Γ := A::A -o B::nil).
    + constructor 3.
    + apply in_llp_limp_l with (ϴ := nil) (Γ := _::nil); simpl; constructor.
  Qed.

  Fact ill_co_imp2 A B : B o- A :: nil ⊢ A -o B [co].
  Proof.
    apply in_llp_limp_r; simpl.
    apply in_llp_perm with (Γ := B o- A :: A :: nil).
    + constructor 3.
    + apply in_llp_rimp_l with (ϴ := nil) (Γ := _::nil); simpl; constructor.
  Qed.

End ill_commutative.
