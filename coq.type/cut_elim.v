(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Permutation.

Require Import utils ill_form ill_rules phase_sem rules_algebra.

Set Implicit Arguments.

Section Cut_Admissibility.

  Hint Resolve ill_cf_perm.

  Notation sg := (@eq _).
  Infix "∘" := (Composes comp_ctx) (at level 50, no associativity).
  Infix "⊸" := (Magicwand comp_ctx) (at level 51, right associativity).

  Let cl := cl_ctx ill_cf_provable.

  Let cl_increase X : X ⊆ cl X.
  Proof. apply cl_ctx_increase. Qed.
 
  Let cl_mono X Y : X ⊆ Y -> cl X ⊆ cl Y.
  Proof. apply cl_ctx_mono. Qed.
  
  Let cl_idem X : cl (cl X) ⊆  cl X.
  Proof. apply cl_ctx_idem. Qed.

  Let cl_stable_l : forall X Y, cl X ∘ Y ⊆ cl (X ∘ Y).
  Proof. apply cl_ctx_stable_l, ill_cf_perm. Qed.
  
  Notation "↓" := (fun A Γ => Γ ⊢cf A).
  Notation K := (fun Δ => { Γ | Δ = ‼Γ }).

  Let dc_closed A : cl (↓A) ⊆ ↓A.
  Proof. apply dc_closed. Qed.

  Let v x := ↓ (£x).

  Let Hv x : cl (v x) ⊆ v x.
  Proof. apply dc_closed. Qed.

  Notation "'⟦' A '⟧'" := (Form_sem cl comp_ctx ∅ K v A) (at level 49).

  Let cl_sem_closed A : cl (⟦A⟧) ⊆ ⟦A⟧.
  Proof. apply closed_Form_sem; eauto. Qed.
 
  Section Okada.

    (** This is Okada's lemma which states that the interpretation ⟦A⟧
        of A is nearly identical to ↓A, 

               A::nil ∈ ⟦A⟧ ⊆ ↓A.

        a result which is similar to what happens in the Lidenbaum construction.
        Indeed, in Lidenbaum construction, one proves 

                 ⟦A⟧ ≃ ↓A

        but that result needs the cut-rule.  

        The MAJOR difference is that Okada's proof does not require 
        the use of cut. It is done by induction on A.

         But first, let us give the algebraic interpretation
         of the rules of the cut-free ILL sequent calculus *)

    Let rule_ax A : ↓A (A::∅). 
    Proof. apply ill_cf_ax. Qed.

    Let rule_limp_l A B : (↓A ⊸ cl (sg (B::∅))) (A -o B::∅). 
    Proof. 
      apply rule_limp_l_eq; eauto. 
      intros ? ?; apply ill_cf_limp_l. 
    Qed.

    Let rule_limp_r A B : sg (A::∅) ⊸ ↓B ⊆ ↓(A -o B).
    Proof. 
      apply rule_limp_r_eq; eauto. 
      intros ?; apply ill_cf_limp_r. 
    Qed.
 
    Let rule_times_l A B : cl (sg (A::B::nil)) (A⊗B::nil).
    Proof.
      apply rule_times_l_eq.
      intros ? ?; apply ill_cf_times_l.
    Qed.

    Let rule_times_r A B : ↓A ∘ ↓B ⊆ ↓(A⊗B).
    Proof.
      apply rule_times_r_eq; eauto.
      intros ? ?; apply ill_cf_times_r.
    Qed.

    Let rule_with_l1 A B : cl (sg (A::∅)) (A&B::∅).
    Proof.
      apply rule_with_l1_eq.
      intros ? ?; apply ill_cf_with_l1.
    Qed.
 
    Let rule_with_l2 A B : cl (sg (B::∅)) (A&B::∅).
    Proof.
      apply rule_with_l2_eq.
      intros ? ?; apply ill_cf_with_l2.
    Qed.

    Let rule_with_r A B : ↓A ∩ ↓B ⊆ ↓(A & B).
    Proof.
      apply rule_with_r_eq.
      intros ?; apply ill_cf_with_r.
    Qed.

    Let rule_plus_l A B : cl (sg (A::∅) ∪ sg (B::∅)) (A⊕B::∅).
    Proof.
      apply rule_plus_l_eq.
      intros ? ?; apply ill_cf_plus_l.
    Qed.

    Let rule_plus_r1 A B : ↓A ⊆ ↓(A⊕B).
    Proof.
      apply rule_plus_r1_eq.
      intro; apply ill_cf_plus_r1.
    Qed.

    Let rule_plus_r2 A B : ↓B ⊆ ↓(A⊕B).
    Proof.
      apply rule_plus_r2_eq.
      intro; apply ill_cf_plus_r2.
    Qed.

    Let rule_bang_l A : cl (sg (A::∅)) (!A::∅).
    Proof.
      apply rule_bang_l_eq.
      intros ? ?; apply ill_cf_bang_l.
    Qed.

    Let rule_bang_r A : K ∩ ↓A ⊆ ↓(!A).
    Proof.
      apply rule_bang_r_eq.
      intros ?; apply ill_cf_bang_r.
    Qed.

    Let rule_unit_l : cl (sg ∅) (𝝐::nil).
    Proof.
      apply rule_unit_l_eq.
      intros ?; apply ill_cf_unit_l.
    Qed.
    
    Let rule_unit_r : sg ∅ ⊆ ↓𝝐.
    Proof.
      apply rule_unit_r_eq.
      apply ill_cf_unit_r.
    Qed.

    Let rule_bot_l : cl (fun _ => False) (⟘::∅).
    Proof. 
      apply rule_bot_l_eq, ill_cf_bot_l.
    Qed.

    Let rule_top_r : (fun _ => True) ⊆ ↓⟙ .
    Proof.
      apply rule_top_r_eq, ill_cf_top_r. 
    Qed.

    Let mw_mono (X Y X' Y' : _ -> Type) : X ⊆ X' -> Y ⊆ Y' -> X' ⊸ Y ⊆ X ⊸ Y'.
    Proof. apply magicwand_monotone; auto. Qed.

    Let inc1_prop (K : Type) (X Y : K -> Type)  x : Y ⊆ X -> Y x -> X x.
    Proof. simpl; auto. Qed.

    Let cl_under_closed X Y : cl Y ⊆ Y -> X ⊆ Y -> cl X ⊆ Y.
    Proof. apply cl_closed; eauto. Qed.
 
    Lemma Okada_formula A : ((sg (A::nil) ⊆ ⟦A⟧) * (⟦A⟧ ⊆ ↓A))%type.
    Proof.
      induction A as [ | [] | A [H1 H2] | [] A [H1 H2] B [H3 H4] ]; auto.
      + split; simpl; auto.
        intros _ []; apply rule_ax.
      + split. 
        * intros _ []; apply rule_unit_l.
        * simpl; apply cl_under_closed; auto; apply rule_unit_r.
      + split.
        * intros _ []; apply rule_bot_l.
        * simpl; apply cl_under_closed; auto; intros _ [].
      + split; simpl; auto.
      + split.
        * intros _ [].
          simpl.
          intros De B H.
          apply H with (ϴ := !A::nil); split.
          - exists (A::nil); auto.
          - apply inc1_prop with (2 := @rule_bang_l _).
            apply cl_under_closed; auto.
        * simpl; apply cl_under_closed; auto.
          intros x []; apply rule_bang_r; split; auto.
      + split.
        * intros _ [].
          simpl; split.
          - apply cl_under_closed with (2 := H1); auto.
          - apply cl_under_closed with (2 := H3); auto.
        * intros Ga (? & ?); apply rule_with_r; auto.
      + split.
        * intros _ []; simpl.
          apply inc1_prop with (2 := @rule_limp_l _ _).
          apply mw_mono; auto; apply cl_under_closed; auto.
        * simpl; intros x Hx; apply rule_limp_r.
          revert Hx; apply mw_mono; auto.
      + split.
        * intros _ [].
          apply inc1_prop with (2 := @rule_times_l _ _).
          simpl; apply cl_mono.
          intros _ []; constructor 1 with (A::∅) (B::∅); auto.
          red; simpl; auto.
        * simpl; apply cl_under_closed; auto.
          intros x Hx; apply rule_times_r.
          revert Hx; apply composes_monotone; eauto.
      + split.
        * intros _ [].
          apply inc1_prop with (2 := @rule_plus_l _ _).
          simpl; apply cl_mono; eauto.
          intros _ [ [] | [] ]; auto.
        * simpl; apply cl_under_closed; auto.
          intros x [ Hx | Hx ]; auto.
    Qed.

  End Okada.

  Notation "'⟬߭' Γ '⟭'" := (list_Form_sem cl comp_ctx ∅ K v Γ) (at level 49).

  (* We lift the result to contexts, ie list of formulas *)

  Lemma Okada_ctx Γ: ⟬߭Γ⟭  Γ.
  Proof.
    induction Γ as [ | A ga Hga ]; simpl; 
      apply cl_increase; auto.
    constructor 1 with (A :: nil) ga; auto.
    + apply Okada_formula; auto.
    + apply Permutation_refl.
  Qed.

  (* And now we apply the soundness result of relational phase semantics *)

  Let ill_cf_sound := rules_sound ill_cf_perm ill_cf_weak_ctx ill_cf_cntr_ctx _ Hv.

  Theorem ill_cut_elimination Γ A : Γ ⊢ A -> { p : Γ ⊢ A | ill_cut_free p }.
  Proof.
    intros H; apply ill_cf_sound with (x := Γ) in H; auto.
    + apply Okada_formula in H; auto.
    + apply Okada_ctx.
  Qed.

End Cut_Admissibility.

Check ill_cut_elimination.
Print Assumptions ill_cut_elimination.

Recursive Extraction ill_cut_elimination.
