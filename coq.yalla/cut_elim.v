(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List_more List_Type genperm_Type.

Require Import orthogonality phase_sem rules_algebra.
Require Import ill_cut_at.

Set Implicit Arguments.

  Lemma P_perm : forall P Γ Δ A, PEperm_Type (ipperm P) Γ Δ -> ill P Γ A -> ill P Δ A.
  Proof. intros; eapply ex_ir; eassumption. Qed.

  Lemma P_weak : forall P, forall ϴ Γ Δ A, ill P (ϴ++Δ) A -> ill P (ϴ++‼Γ++Δ) A.
  Proof. intros; apply wk_list_ilr; assumption. Qed.

  Lemma P_cntr : forall P, forall ϴ Γ Δ A, ill P (ϴ++‼Γ++‼Γ++Δ) A -> ill P (ϴ++‼Γ++Δ) A.
  Proof. intros; apply co_list_ilr; assumption. Qed.

  Hint Resolve P_perm P_weak P_cntr.

  Definition gax_at_l P := forall a, Forall_Type iatomic (fst (projT2 (ipgax P) a)).
  Definition gax_at_r P := forall a, iatomic (snd (projT2 (ipgax P) a)).
  Definition gax_noN_l P := forall a, List_Type.In_Type N (fst (projT2 (ipgax P) a)) -> False.
  Definition gax_cut P := forall a b l1 l2,
                            fst (projT2 (ipgax P) b) = l1 ++ snd (projT2 (ipgax P) a) :: l2 -> 
                          { c | l1 ++ fst (projT2 (ipgax P) a) ++ l2 = fst (projT2 (ipgax P) c)
                                /\ snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) }.

Section Okada.

  Variable P : ipfrag.

  Instance PSILL : PhaseSpace (ipperm P) :=
    PS_ctx (ill P) (ipperm P) (@P_perm P) (@P_weak P) (@P_cntr P).
  Instance CLILL : ClosureOp := PSCL.

  Hint Resolve (@composes_monotone _ PScompose).

  Notation "↓" := (fun A Γ => ill P Γ A).

  Notation ILLval := (fun x => ↓(£x)).

  Fact ILLdc_closed: forall A, cl (↓A) ⊆ ↓A.
  Proof. apply dc_closed. Qed.

  Hint Resolve ILLdc_closed.

  Fact ILLvdc_closed: forall x, cl (↓(£x)) ⊆ ↓(£x).
  Proof. intros; apply ILLdc_closed. Qed.

  Hypothesis P_gax_noN_l : gax_noN_l P.
  Hypothesis P_gax_at_l : gax_at_l P.
  Hypothesis P_gax_at_r : gax_at_r P.
  Hypothesis P_gax_cut : gax_cut P.

(* TODO replace lcompose by list_form_presem ??? *)
  Let lcompose := fold_right (fun x y => composes PScompose x y) (sg PSunit).
  Fact ILLgax : forall a, list_form_presem PSILL ILLval (fst (projT2 (ipgax P) a))
                    ⊆ form_sem PSILL ILLval (snd (projT2 (ipgax P) a)).
  Proof.
    red in P_gax_at_l, P_gax_at_r.
    intros a; specialize P_gax_at_l with a; specialize P_gax_at_r with a.
    remember (snd (projT2 (ipgax P) a)) as b.
    destruct b; inversion P_gax_at_r; simpl.
    assert ({l : list IAtom | fst (projT2 (ipgax P) a) = map ivar l }) as [l Heq].
    { revert P_gax_at_l ; remember (fst (projT2 (ipgax P) a)) as L; clear.
      induction L; intros Hat.
      - exists nil; reflexivity.
      - inversion Hat; inversion H1; subst.
        destruct (IHL H2) as [l Heq]; subst.
        exists (x0 :: l); reflexivity. }
    rewrite Heq.
    replace (list_form_presem PSILL ILLval (map ivar l))
       with (lcompose (map ILLval l))
      by (clear; induction l; auto; simpl; rewrite IHl; auto).
    apply subset_trans with (cl (lcompose (map ILLval l))).
    { clear; induction l; try reflexivity.
    - simpl; unfold ldual, rdual; simpl.
      intros x H; unfold list_form_presem in H; simpl in H; subst.
      unfold ctx_orth; intros [[de1 de2] A] H.
      specialize H with nil; apply H; reflexivity.
    - revert IHl; simpl.
      remember (lcompose (map (fun x Γ => ill P Γ (£ x)) l)) as L1; clear HeqL1.
      remember (lcompose (map (fun x Γ => ill P Γ (£ x)) l)) as L2; clear HeqL2.
      remember (fun Γ : list iformula => ill P Γ (£ a)) as L0; clear HeqL0.
      intros IH.
      apply (@cl_increase _ _ (CL_ctx (ill P))). }
    apply cl_closed; [ apply subset_preorder | apply dc_closed | ].
    assert (ill P (nil ++ map ivar l) (ivar i)) as pi
      by (rewrite Heqb; rewrite <- Heq; apply gax_ir).
    apply subset_trans with (fun Γ => ill P (nil ++ Γ) (£ i)); [ | intros A H; auto ].
    revert pi; remember nil as l0; clear Heql0.
    revert l0; clear - P_gax_noN_l P_gax_cut; induction l; intros l0 pi.
    + simpl; intros l Heq; subst; auto.
    + intros Ga H.
      inversion H; subst.
      list_simpl in pi.
      assert (pi' := @cut_at _ P_gax_noN_l P_gax_cut _ _ _ _ _ X pi).
      rewrite app_assoc in pi'.
      apply IHl in pi'.
      apply pi' in X0.
      rewrite <- app_assoc in X0; auto.
  Qed.

  Instance PMILL : PhaseModel P := {
    PMPS := PSILL;
    PMval := ILLval;
    PMval_closed := ILLvdc_closed;
    PMgax := ILLgax
  }.

  Infix "∘" := (composes PScompose) (at level 50, no associativity).
  Infix "⊸" := (magicwand_l PScompose) (at level 51, right associativity).
  Infix "⟜" := (magicwand_r PScompose) (at level 53, left associativity).
  Notation v := PMval.
  Notation Hv := PMval_closed.
  Notation "⟦ A ⟧" := (form_sem PSILL ILLval A) (at level 49).

  Let cl_sem_closed A : cl (⟦A⟧) ⊆ ⟦A⟧.
  Proof. apply (@form_sem_closed _ PMILL); auto. Qed.

  Section Okada_Lemma.

    Let cl_under_closed X Y : cl Y ⊆ Y -> X ⊆ Y -> cl X ⊆ Y.
    Proof. apply cl_closed; apply subset_preorder. Qed.

    Lemma Okada_formula A : ((sg (A::nil) ⊆ ⟦A⟧) * (⟦A⟧ ⊆ ↓A))%type.
    Proof.
    induction A; simpl;
      try (destruct IHA as [IHA01 IHA02]);
      try (destruct IHA1 as [IHA11 IHA12]);
      try (destruct IHA2 as [IHA21 IHA22]);
     (split; [ |
      try (try (apply cl_under_closed; auto);
           intros x Hx; inversion Hx; subst; constructor; auto; fail)]).
    - intros x Hx; subst.
      apply ax_ir.
    - reflexivity.
    - unfold ldual, rdual, ctx_orth.
      intros x Hx [[de1 de2] A] Hy; subst; simpl.
      constructor.
      specialize Hy with nil; apply Hy; auto.
    - unfold ldual, rdual, ctx_orth.
      intros x Hx [[de1 de2] A] Hy; subst; simpl.
      constructor.
      specialize Hy with ((A1 :: nil) ++ A2 :: nil); apply Hy; auto.
      constructor; auto.
    - unfold magicwand_r.
      intros x Hx y Hy; subst.
      inversion Hy; subst.
      enough (sg (A2 o- A1 :: b) ⊆ ⟦A2⟧) as Hi by (apply Hi; reflexivity).
      apply cl_under_closed in IHA21; auto.
      etransitivity; [ | apply IHA21 ].
      intros x Hx; subst.
      unfold cl; simpl; unfold ldual, rdual, ctx_orth.
      intros [[si1 si2] C] H; simpl.
      apply lpam_ilr; auto.
      specialize H with (A2 :: nil); apply H; auto.
    - intros x Hx; constructor.
      apply IHA22, Hx; constructor; auto.
    - unfold magicwand_r.
      intros x Hx y Hy; subst.
      inversion Hy; subst; simpl.
      apply gen_ilr.
      apply IHA02; auto.
    - intros x Hx; constructor.
      apply Hx; constructor; auto.
    - unfold magicwand_l.
      intros x Hx y Hy; subst.
      inversion Hy; subst.
      enough (sg (a ++ A1 -o A2 :: nil) ⊆ ⟦A2⟧) as Hi by (apply Hi; reflexivity).
      apply cl_under_closed in IHA21; auto.
      etransitivity; [ | apply IHA21 ].
      intros x Hx; subst.
      unfold cl; simpl; unfold ldual, rdual, ctx_orth.
      intros [[si1 si2] C] H; list_simpl.
      apply lmap_ilr; auto.
      specialize H with (A2 :: nil); apply H; auto.
    - intros x Hx; constructor.
      apply IHA22, Hx.
      change (A1 :: x) with ((A1 :: nil) ++ x); constructor; auto.
    - unfold magicwand_l.
      intros x Hx y Hy; subst.
      inversion Hy; subst; simpl.
      apply neg_ilr.
      apply IHA02; auto.
    - intros x Hx; constructor.
      apply Hx.
      change (A :: x) with ((A :: nil) ++ x); constructor; auto.
    - apply top_greatest.
    - apply glb_in.
      + apply cl_under_closed in IHA11; auto.
        etransitivity; [ | apply IHA11 ].
        intros x Hx; subst.
        unfold cl; simpl; unfold ldual, rdual, ctx_orth.
        intros [[si1 si2] C] H; simpl.
        apply with_ilr1.
        specialize H with (A1 :: nil); apply H; auto.
      + apply cl_under_closed in IHA21; auto.
        etransitivity; [ | apply IHA21 ].
        intros x Hx; subst.
        unfold cl; simpl; unfold ldual, rdual, ctx_orth.
        intros [[si1 si2] C] H; simpl.
        apply with_ilr2.
        specialize H with (A2 :: nil); apply H; auto.
    - unfold ldual, rdual, ctx_orth.
      intros x Hx [[de1 de2] A] Hy; subst; simpl.
      constructor.
    - unfold ldual, rdual, ctx_orth.
      intros x Hx [[de1 de2] A] Hy; subst; simpl.
      constructor.
      + specialize Hy with (A1 :: nil); apply Hy; auto.
      + specialize Hy with (A2 :: nil); apply Hy; auto.
    - unfold ldual, rdual, ctx_orth.
      intros x Hx [[de1 de2] B] Hy; subst; simpl.
      specialize Hy with (!A :: nil); apply Hy; auto.
      split.
      + exists (A :: nil); reflexivity.
      + enough (sg (!A :: nil) ⊆ ⟦A⟧) as Hoc by (apply Hoc; reflexivity).
        apply cl_under_closed in IHA01; auto.
        etransitivity; [ | apply IHA01 ].
        intros x Hx; subst.
        unfold cl; simpl; unfold ldual, rdual, ctx_orth.
        intros [[si1 si2] C] H; simpl.
        apply de_ilr.
        specialize H with (A :: nil); apply H; auto.
    - apply cl_under_closed; auto.
      intros x Hx; inversion Hx; subst.
      inversion H; subst.
      constructor; auto.
    Qed.

  End Okada_Lemma.

  Notation "⟬߭ Γ ⟭" := (list_form_presem PSILL ILLval Γ) (at level 49).

  (* We lift the result to contexts, ie list of formulas *)

  Lemma Okada_ctx Γ: ⟬߭Γ⟭  Γ.
  Proof.
  induction Γ as [ | A ga Hga ]; unfold list_form_presem; simpl; auto.
  change (A :: ga) with ((A :: nil) ++ ga); constructor; auto.
  apply Okada_formula; auto.
  Qed.

End Okada.

(** The notation Γ ⊢ A [P] is for the type of proofs of the sequent Γ ⊢ A
    * in commutative ILL if ipperm P=true; ILLNC if ipperm P=false
    * with cut if ipcut P=true; cut-free if ipcut P=false
*)

Notation "l '⊢' x [ Q ]" := (ill Q l x) (at level 70, no associativity).

Section cut_admissibility.

  Variable P : ipfrag.
  Hypothesis P_gax_noN_l : gax_noN_l P.
  Hypothesis P_gax_at_l : gax_at_l P.
  Hypothesis P_gax_at_r : gax_at_r P.
  Hypothesis P_gax_cut : gax_cut P.

  Instance PSILL_cfat : PhaseSpace (ipperm P) := PSILL (cutupd_ipfrag P false).
  Instance CL_cfat : ClosureOp := PSCL.

  (* Coercion: the phase model relying on cut-free provability over P is a phase model for P *)
  Instance PMILL_cfat : PhaseModel P := {
    PMPS := PSILL_cfat;
    PMval := fun x ga => ill (cutupd_ipfrag P false) ga (£x);
    PMval_closed :=  @ILLvdc_closed (cutupd_ipfrag P false);
    PMgax := @ILLgax (cutupd_ipfrag P false) P_gax_noN_l P_gax_at_l P_gax_at_r P_gax_cut
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

