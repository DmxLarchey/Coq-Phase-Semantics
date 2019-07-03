(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Permutation.

Require Import rel_utils ill_def phase_sem rules_algebra.

Set Implicit Arguments.

Section Okada.

(*  Hint Resolve ill_cf_perm_bang_t. *)

  Context {P : ipfrag}.
  Hypothesis P_axfree : (projT1 (ipgax P) -> False).

  Notation comp := (@comp_ctx P).

  Notation sg := (@eq _).
  Infix "∘" := (Composes comp) (at level 50, no associativity).
  Infix "⊸" := (Magicwand_l comp) (at level 51, right associativity).
  Infix "⟜" := (Magicwand_r comp) (at level 52, left associativity).

  Let cl := @cl_ctx P.

  Let cl_increase X : X ⊆ cl X.
  Proof. apply cl_ctx_increase. Qed.
 
  Let cl_mono X Y : X ⊆ Y -> cl X ⊆ cl Y.
  Proof. apply cl_ctx_mono. Qed.
  
  Let cl_idem X : cl (cl X) ⊆  cl X.
  Proof. apply cl_ctx_idem. Qed.

  Let cl_stable_l : forall X Y, cl X ∘ Y ⊆ cl (X ∘ Y).
  Proof. apply cl_ctx_stable_l; eauto. Qed.

  Let cl_stable_r : forall X Y, X ∘ cl Y ⊆ cl (X ∘ Y).
  Proof. apply cl_ctx_stable_r; eauto. Qed.
 
  Notation "↓" := (fun A Γ => ill P Γ A).
  Notation K := (fun Δ => { Γ | Δ = ‼Γ }).

  Let dc_closed A : cl (↓A) ⊆ ↓A.
  Proof. apply dc_closed. Qed.

  Let v x := ↓ (£x).

  Let Hv x : cl (v x) ⊆ v x.
  Proof. apply dc_closed. Qed.

  Notation "'⟦' A '⟧'" := (Form_sem cl comp ∅ K v A) (at level 49).

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
      intros ?; apply neg_ilr. 
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
      intros ?; apply gen_ilr. 
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

    Let rule_bang_r A : K ∩ ↓A ⊆ ↓(!A).
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

    Let rule_bot_l : cl (fun _ => False) (⟘::∅).
    Proof. 
      apply rule_bot_l_eq, zero_ilr.
    Qed.

    Let rule_top_r : (fun _ => True) ⊆ ↓⟙ .
    Proof.
      apply rule_top_r_eq, top_irr. 
    Qed.

    Let mwl_mono (X Y X' Y' : _ -> Type) : X ⊆ X' -> Y ⊆ Y' -> X' ⊸ Y ⊆ X ⊸ Y'.
    Proof. apply magicwand_l_monotone; auto. Qed.

    Let mwr_mono (X Y X' Y' : _ -> Type) : X ⊆ X' -> Y ⊆ Y' -> Y ⟜ X' ⊆ Y' ⟜ X.
    Proof. apply magicwand_r_monotone; auto. Qed.

    Let inc1_prop (K : Type) (X Y : K -> Type)  x : Y ⊆ X -> Y x -> X x.
    Proof. simpl; auto. Qed.

    Let cl_under_closed X Y : cl Y ⊆ Y -> X ⊆ Y -> cl X ⊆ Y.
    Proof. apply cl_closed; eauto. Qed.
 
    Lemma Okada_formula A : ((sg (A::nil) ⊆ ⟦A⟧) * (⟦A⟧ ⊆ ↓A))%type.
    Proof.
      induction A; auto.
      + split; simpl; auto.
        intros _ []; apply rule_ax.
      + split. 
        * intros _ []; apply rule_unit_l.
        * simpl; apply cl_under_closed; auto; apply rule_unit_r.
      + destruct IHA1 as [IHA1 IHA3].
        destruct IHA2 as [IHA2 IHA4].
        split.
        * intros _ [].
          apply inc1_prop with (2 := @rule_times_l _ _).
          simpl; apply cl_mono.
          intros _ []; constructor 1 with (A1::∅) (A2::∅); auto.
          red; simpl; auto.
        * simpl; apply cl_under_closed; auto.
          intros x Hx; apply rule_times_r.
          revert Hx; apply composes_monotone; eauto.
      + destruct IHA1 as [IHA1 IHA3].
        destruct IHA2 as [IHA2 IHA4].
        split.
        * intros _ []; simpl.
          apply inc1_prop with (2 := @rule_rimp_l _ _).
          apply mwr_mono; auto; apply cl_under_closed; auto.
        * simpl; intros x Hx; apply rule_rimp_r.
          revert Hx; apply mwr_mono; auto.
      + destruct IHA as [IHA1 IHA2].
        split.
        * intros _ []; simpl.
          eapply inc1_prop ; [ | apply rule_gen_l ].
          apply mwr_mono; auto; apply cl_under_closed; auto.
          unfold N; intros _ []; apply rule_ax.
        * simpl; intros x Hx; apply rule_gen_r.
          revert Hx; apply mwr_mono; auto.
      + destruct IHA1 as [IHA1 IHA3].
        destruct IHA2 as [IHA2 IHA4].
        split.
        * intros _ []; simpl.
          apply inc1_prop with (2 := @rule_limp_l _ _).
          apply mwl_mono; auto; apply cl_under_closed; auto.
        * simpl; intros x Hx; apply rule_limp_r.
          revert Hx; apply mwl_mono; auto.
      + destruct IHA as [IHA1 IHA2].
        split.
        * intros _ []; simpl.
          eapply inc1_prop ; [ | apply rule_neg_l ].
          apply mwl_mono; auto; apply cl_under_closed; auto.
          unfold N; intros _ []; apply rule_ax.
        * simpl; intros x Hx; apply rule_neg_r.
          revert Hx; apply mwl_mono; auto.
      + split; simpl; red; auto.
      + destruct IHA1 as [IHA1 IHA3].
        destruct IHA2 as [IHA2 IHA4].
        split.
        * intros _ [].
          simpl; split.
          - apply cl_under_closed with (2 := IHA1); auto.
          - apply cl_under_closed with (2 := IHA2); auto.
        * intros Ga (? & ?); apply rule_with_r; auto.
      + split.
        * intros _ []; apply rule_bot_l.
        * simpl; apply cl_under_closed; auto; intros _ [].
      + destruct IHA1 as [IHA1 IHA3].
        destruct IHA2 as [IHA2 IHA4].
        split.
        * intros _ [].
          apply inc1_prop with (2 := @rule_plus_l _ _).
          simpl; apply cl_mono; eauto.
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
          - apply inc1_prop with (2 := @rule_bang_l _).
            apply cl_under_closed; auto.
        * simpl; apply cl_under_closed; auto.
          intros x []; apply rule_bang_r; split; auto.
    Qed.

  End Okada.

  Notation "'⟬߭' Γ '⟭'" := (list_Form_sem cl comp ∅ K v Γ) (at level 49).

  (* We lift the result to contexts, ie list of formulas *)

  Lemma Okada_ctx Γ: ⟬߭Γ⟭  Γ.
  Proof.
    induction Γ as [ | A ga Hga ]; simpl; 
      apply cl_increase; auto.
    constructor 1 with (A :: nil) ga; auto.
    + apply Okada_formula; auto.
    + red; auto.
  Qed.

End Okada.

(** The notation Γ ⊢ A [comm,cut] is for the type of proofs of the sequent Γ ⊢ A
    * in commutative ILL if comm=true; ILLNC if comm=false
    * with cut if cut=true; cut-free if cut=false
*)

Notation "l '⊢' x [ Q ]" := (ill Q l x) (at level 70, no associativity).

Section NC_cut_admissibility.

  Context {P : ipfrag}.
  Hypothesis P_axfree : (projT1 (ipgax P) -> False).

  Theorem ill_nc_cut_elimination Γ A : ipperm P = false -> Γ ⊢ A [P] -> Γ ⊢ A [cutupd_ipfrag P false].
  Proof.
     intros HP H.
     eapply rules_nc_sound with (v := fun x ga => ill (cutupd_ipfrag P false) ga (£x)) in H; auto.
     + apply Okada_formula, H, Okada_ctx; auto.
     + intros x Ga H1; red in H1.
       replace Ga with (nil++Ga++nil); [ apply H1 | ]; intros; rewrite <- app_nil_end; auto.
  Qed.

End NC_cut_admissibility.

Section COMM_cut_admissibility.

  Context {P : ipfrag}.
  Hypothesis P_axfree : (projT1 (ipgax P) -> False).

  Theorem ill_comm_cut_elimination Γ A : ipperm P = true -> Γ ⊢ A [P] -> Γ ⊢ A [cutupd_ipfrag P false].
  Proof.
     intros HP H.
     eapply rules_comm_sound with (v := fun x ga => ill (cutupd_ipfrag P false) ga (£x)) in H; auto.
     + apply Okada_formula, H, Okada_ctx; auto.
     + auto.
     + intros x Ga H1; red in H1.
       replace Ga with (nil++Ga++nil); [ apply H1 | ]; intros; rewrite <- app_nil_end; auto.
  Qed.

End COMM_cut_admissibility.

Check ill_nc_cut_elimination.
Print Assumptions ill_nc_cut_elimination.

Check ill_comm_cut_elimination.
Print Assumptions ill_comm_cut_elimination.


