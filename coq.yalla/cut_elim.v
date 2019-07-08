(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation_Type genperm_Type.

Require Import phase_sem rules_algebra.
Require Import ill_def.

Set Implicit Arguments.

  Notation " x '~[' b ']' y " := (PEperm_Type b x y) (at level 70, format "x  ~[ b ]  y").

  Lemma P_perm : forall P Γ Δ A, Γ ~[ipperm P] Δ -> ill P Γ A -> ill P Δ A.
  Proof. intros; eapply ex_ir; eassumption. Qed.

  Lemma P_weak : forall P, forall ϴ Γ Δ A, ill P (ϴ++Δ) A -> ill P (ϴ++‼Γ++Δ) A.
  Proof. intros; apply wk_list_ilr; assumption. Qed.

  Lemma P_cntr : forall P, forall ϴ Γ Δ A, ill P (ϴ++‼Γ++‼Γ++Δ) A -> ill P (ϴ++‼Γ++Δ) A.
  Proof. intros; apply co_list_ilr; assumption. Qed.

  Hint Resolve P_perm P_weak P_cntr.


Section Okada.

  Variable P : ipfrag.
  Hypothesis P_axfree : projT1 (ipgax P) -> False.

  Instance PSILL : PhaseSpace (ipperm P) :=
    PS_ctx (ill P) (ipperm P) (@P_perm P) (@P_weak P) (@P_cntr P).
  Instance CLILL : ClosureOp := PSCL.

  Notation "↓" := (fun A Γ => ill P Γ A).

  Fact ILLdc_closed: forall A, cl (↓A) ⊆ ↓A.
  Proof. apply dc_closed. Qed.

  Hint Resolve ILLdc_closed.

  Fact ILLvdc_closed: forall x, cl (↓(£x)) ⊆ ↓(£x).
  Proof. intros; apply ILLdc_closed. Qed.

  Instance PMILL : PhaseModel P := {
    PMPS := PSILL;
    PMval := fun x => ↓(£x);
    PMval_closed := ILLvdc_closed
  }.

  Infix "∘" := (Composes PSCompose) (at level 50, no associativity).
  Infix "⊸" := (Magicwand_l PSCompose) (at level 51, right associativity).
  Infix "⟜" := (Magicwand_r PSCompose) (at level 52, left associativity).
  Notation v := PMval.
  Notation Hv := PMval_closed.
  Notation "'⟦' A '⟧'" := (Form_sem PMILL A) (at level 49).

  Let cl_sem_closed A : cl (⟦A⟧) ⊆ ⟦A⟧.
  Proof. apply closed_Form_sem; auto. Qed.

  Section Okada_Lemma.

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
    Proof. apply ax_exp_ill. Qed.

    Let rule_limp_l A B : (↓A ⊸ cl (sg (B::∅))) (A -o B::∅). 
    Proof.
      apply rule_limp_l_eq; eauto. 
      intros ? ? ? ?; apply lmap_ilr. 
    Qed.

    Let rule_limp_r A B : sg (A::∅) ⊸ ↓B ⊆ ↓(A -o B).
    Proof.
      apply rule_limp_r_eq; eauto. 
      intros ?; apply lmap_irr. 
    Qed.

    Let rule_neg_l A : (↓A ⊸ cl (sg (N::∅))) (ineg A::∅). 
    Proof.
      apply rule_neg_l_eq; eauto.
      intros; apply neg_map_rule; auto.
    Qed.

    Let rule_neg_r A : sg (A::∅) ⊸ ↓N ⊆ ↓(ineg A).
    Proof.
      apply rule_neg_r_eq; eauto. 
      intros ?; apply neg_irr. 
    Qed.

    Let rule_rimp_l A B : (cl (sg (B::∅)) ⟜ ↓A) (B o- A::∅).
    Proof.
      apply rule_rimp_l_eq; eauto. 
      intros ? ? ? ?; apply lpam_ilr. 
    Qed.

    Let rule_rimp_r A B : ↓B ⟜ sg (A::∅) ⊆ ↓(B o- A).
    Proof.
      apply rule_rimp_r_eq; eauto.
      intros ?; apply lpam_irr.
    Qed.

    Let rule_gen_l A : (cl (sg (N::∅)) ⟜ ↓A) (igen A::∅).
    Proof.
      apply rule_gen_l_eq; eauto. 
      intros; apply gen_pam_rule; auto.
    Qed.

    Let rule_gen_r A : ↓N ⟜ sg (A::∅) ⊆ ↓(igen A).
    Proof.
      apply rule_gen_r_eq; eauto.
      intros ?; apply gen_irr.
    Qed.

    Let rule_times_l A B : cl (sg (A::B::nil)) (A⊗B::nil).
    Proof.
      apply rule_times_l_eq.
      intros ? ? ?; apply tens_ilr.
    Qed.

    Let rule_times_r A B : ↓A ∘ ↓B ⊆ ↓(A⊗B).
    Proof.
      apply rule_times_r_eq; eauto.
      intros ? ?; apply tens_irr.
    Qed.

    Let rule_with_l1 A B : cl (sg (A::∅)) (A&B::∅).
    Proof.
      apply rule_with_l1_eq.
      intros ? ? ?; apply with_ilr1.
    Qed.

    Let rule_with_l2 A B : cl (sg (B::∅)) (A&B::∅).
    Proof.
      apply rule_with_l2_eq.
      intros ? ? ?; apply with_ilr2.
    Qed.

    Let rule_with_r A B : ↓A ∩ ↓B ⊆ ↓(A & B).
    Proof.
      apply rule_with_r_eq.
      intros ?; apply with_irr.
    Qed.

    Let rule_plus_l A B : cl (sg (A::∅) ∪ sg (B::∅)) (A⊕B::∅).
    Proof.
      apply rule_plus_l_eq.
      intros ? ?; apply plus_ilr.
    Qed.

    Let rule_plus_r1 A B : ↓A ⊆ ↓(A⊕B).
    Proof.
      apply rule_plus_r1_eq.
      intro; apply plus_irr1.
    Qed.

    Let rule_plus_r2 A B : ↓B ⊆ ↓(A⊕B).
    Proof.
      apply rule_plus_r2_eq.
      intro; apply plus_irr2.
    Qed.

    Let rule_bang_l A : cl (sg (A::∅)) (!A::∅).
    Proof.
      apply rule_bang_l_eq.
      intros ? ?; apply de_ilr.
    Qed.

    Let rule_bang_r A : PSExp ∩ ↓A ⊆ ↓(!A).
    Proof.
      apply rule_bang_r_eq.
      intros ?; apply oc_irr.
    Qed.

    Let rule_unit_l : cl (sg ∅) (𝝐::nil).
    Proof.
      apply rule_unit_l_eq.
      intros ?; apply one_ilr.
    Qed.

    Let rule_unit_r : sg ∅ ⊆ ↓𝝐.
    Proof.
      apply rule_unit_r_eq.
      apply one_irr.
    Qed.

    Let rule_zero_l : cl (fun _ => False) (⟘::∅).
    Proof.
      apply rule_zero_l_eq, zero_ilr.
    Qed.

    Let rule_top_r : (fun _ => True) ⊆ ↓⟙ .
    Proof.
      apply rule_top_r_eq, top_irr. 
    Qed.

    Let mwl_mono (X Y X' Y' : _ -> Type) : X ⊆ X' -> Y ⊆ Y' -> X' ⊸ Y ⊆ X ⊸ Y'.
    Proof. intros; apply magicwand_l_monotone; auto. Qed.

    Let mwr_mono (X Y X' Y' : _ -> Type) : X ⊆ X' -> Y ⊆ Y' -> Y ⟜ X' ⊆ Y' ⟜ X.
    Proof. intros; apply magicwand_r_monotone; auto. Qed.

    Let subset_prop (K : Type) (X Y : K -> Type)  x : Y ⊆ X -> Y x -> X x.
    Proof. simpl; auto. Qed.

    Let cl_under_closed X Y : cl Y ⊆ Y -> X ⊆ Y -> cl X ⊆ Y.
    Proof. apply cl_closed. Qed.

    Lemma Okada_formula A : ((sg (A::nil) ⊆ ⟦A⟧) * (⟦A⟧ ⊆ ↓A))%type.
    Proof.
      induction A; auto.
      + split; simpl; auto; try reflexivity.
        intros _ []; apply rule_ax.
      + split.
        * intros _ []; apply rule_unit_l.
        * simpl; apply cl_under_closed ; auto.
      + destruct IHA1 as [IHA1 IHA3].
        destruct IHA2 as [IHA2 IHA4].
        split.
        * intros _ [].
          apply subset_prop with (2 := @rule_times_l _ _).
          simpl; apply cl_ctx_mono.
          intros _ []; constructor 1 with (A1::∅) (A2::∅); auto.
          red; reflexivity.
        * simpl ; apply cl_under_closed; auto.
          intros x Hx; apply rule_times_r.
          revert Hx; apply composes_monotone; eauto.
      + destruct IHA1 as [IHA1 IHA3].
        destruct IHA2 as [IHA2 IHA4].
        split.
        * intros _ []; simpl.
          apply subset_prop with (2 := @rule_rimp_l _ _).
          apply mwr_mono; auto; apply cl_under_closed; auto.
        * simpl; intros x Hx; apply rule_rimp_r.
          revert Hx; apply mwr_mono; auto.
      + destruct IHA as [IHA1 IHA2].
        split.
        * intros _ []; simpl.
          eapply subset_prop ; [ | apply rule_gen_l ].
          apply mwr_mono; auto; apply cl_under_closed; auto.
          unfold N; intros _ []; apply rule_ax.
        * simpl; intros x Hx; apply rule_gen_r.
          revert Hx; apply mwr_mono; auto; reflexivity.
      + destruct IHA1 as [IHA1 IHA3].
        destruct IHA2 as [IHA2 IHA4].
        split.
        * intros _ []; simpl.
          apply subset_prop with (2 := @rule_limp_l _ _).
          apply mwl_mono; auto; apply cl_under_closed; auto.
        * simpl; intros x Hx; apply rule_limp_r.
          revert Hx; apply mwl_mono; auto.
      + destruct IHA as [IHA1 IHA2].
        split.
        * intros _ []; simpl.
          eapply subset_prop ; [ | apply rule_neg_l ].
          apply mwl_mono; auto; apply cl_under_closed; auto.
          unfold N; intros _ []; apply rule_ax.
        * simpl; intros x Hx; apply rule_neg_r.
          revert Hx; apply mwl_mono; auto; reflexivity.
      + split; simpl; red; unfold top; auto.
      + destruct IHA1 as [IHA1 IHA3].
        destruct IHA2 as [IHA2 IHA4].
        split.
        * intros _ [].
          simpl; split.
          - apply cl_under_closed with (2 := IHA1); auto.
          - apply cl_under_closed with (2 := IHA2); auto.
        * intros Ga (? & ?); apply rule_with_r; auto.
      + split.
        * intros _ []; apply rule_zero_l.
        * simpl; apply cl_under_closed; auto.
          intros _ [].
      + destruct IHA1 as [IHA1 IHA3].
        destruct IHA2 as [IHA2 IHA4].
        split.
        * intros _ [].
          apply subset_prop with (2 := @rule_plus_l _ _).
          simpl; apply cl_ctx_mono; auto.
          intros _ [ [] | [] ]; auto.
        * simpl; apply cl_under_closed; auto.
          intros x [ Hx | Hx ]; auto.
          - apply rule_plus_r1; auto.
          - apply rule_plus_r2; auto.
      + destruct IHA as [IHA1 IHA2].
        split.
        * intros _ []; simpl.
          intros Th De B H.
          apply H with (ϴ := !A::nil); split.
          - exists (A::nil); auto.
          - apply subset_prop with (2 := @rule_bang_l _).
            apply cl_under_closed; auto.
        * simpl; apply cl_under_closed; auto.
          intros x []; apply rule_bang_r; split; auto.
    Qed.

  End Okada_Lemma.

  Notation "'⟬߭' Γ '⟭'" := (list_Form_sem PMILL Γ) (at level 49).

  (* We lift the result to contexts, ie list of formulas *)

  Lemma Okada_ctx Γ: ⟬߭Γ⟭  Γ.
  Proof.
    induction Γ as [ | A ga Hga ]; simpl; 
      apply cl_increase; auto.
    constructor 1 with (A :: nil) ga; auto.
    + apply Okada_formula; auto.
    + apply PEperm_Type_refl.
  Qed.

End Okada.

(** The notation Γ ⊢ A [P] is for the type of proofs of the sequent Γ ⊢ A
    * in commutative ILL if ipperm P=true; ILLNC if ipperm P=false
    * with cut if ipcut P=true; cut-free if ipcut P=false
*)

Notation "l '⊢' x [ Q ]" := (ill Q l x) (at level 70, no associativity).

Section cut_admissibility.

  Variable P : ipfrag.
  Hypothesis P_axfree : projT1 (ipgax P) -> False.

  Instance PSILL_cfat : PhaseSpace (ipperm P) := PSILL (cutupd_ipfrag P false).
  Instance CL_cfat : ClosureOp := PSCL.

  Lemma ILLdc_closed_cfat : forall x,
    cl (fun ga => ill (cutupd_ipfrag P false) ga (£x)) ⊆ fun ga => ill (cutupd_ipfrag P false) ga (£x).
  Proof.
    intros x Ga H1; red in H1.
    replace Ga with (nil++Ga++nil); [ apply H1 | ]; intros; rewrite <- app_nil_end; auto.
  Qed.

  Instance PMILL_cfat : PhaseModel P := {
    PMPS := PSILL_cfat;
    PMval := fun x ga => ill (cutupd_ipfrag P false) ga (£x);
    PMval_closed := ILLdc_closed_cfat
  }.

  Theorem ill_cut_elimination Γ A : Γ ⊢ A [P] -> Γ ⊢ A [cutupd_ipfrag P false].
  Proof.
    intros pi.
    apply (ill_soundness PMILL_cfat) in pi; auto.
    apply Okada_formula, pi, Okada_ctx; auto.
  Qed.

End cut_admissibility.

(*
Check ill_cut_elimination.
Print Assumptions ill_cut_elimination.
*)

