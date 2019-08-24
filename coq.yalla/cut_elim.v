(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(*   Adapted by Olivier Laurent [**]                          *)
(*                                                            *)
(*                              [**] Affiliation LIP -- CNRS  *)

Require Import List_more List_Type Permutation_Type genperm_Type.

Require Import orthogonality phase_sem.

Require Import ill_def.

Import SetNotations.

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

Section SyntacticModel.

  Variable P : ipfrag.

  Notation "Γ ⊢ A [ Q ]" := (ill Q Γ A) (at level 70, no associativity).
  Hint Resolve PEperm_Type_refl Permutation_Type_app_comm.

  Notation ctx_compose := (@app iformula).
  Notation ctx_unit := (@nil iformula).
  Notation adj_l := (fun ϴ H => match H with (Γ,Δ,A) => (Γ, ϴ ++ Δ, A) end).
  Notation adj_r := (fun ϴ H => match H with (Γ,Δ,A) => (Γ ++ ϴ, Δ, A) end).

  Notation ctx_hole := (list iformula * list iformula * iformula)%type.
  Infix "∘" := (composes ctx_compose) (at level 50, no associativity).

  Definition ctx_orth : list iformula -> ctx_hole -> Type :=
    fun ϴ H => match H with (Γ,Δ,A) => Γ ++ ϴ ++ Δ ⊢ A [P] end.

  Instance CL_ctx : ClosureOp := (@lclosure _ _ ctx_orth).
  Notation cl_ctx := (@cl _ _ CL_ctx).

  Lemma rel_associative_l_l : rel_associativity_l_l ctx_orth ctx_compose adj_r.
  Proof. intros X Y [[X1 Y1] A]; unfold ctx_orth; rewrite <- ? app_assoc; auto. Qed.

  Lemma rel_associative_l_r : rel_associativity_l_r ctx_orth ctx_compose adj_r.
  Proof. intros X Y [[X1 Y1] A]; unfold ctx_orth; rewrite <- ? app_assoc; auto. Qed.

  Lemma rel_associative_r_l : rel_associativity_r_l ctx_orth ctx_compose adj_l.
  Proof. intros X Y [[X1 Y1] A]; unfold ctx_orth; rewrite <- app_assoc; auto. Qed.

  Lemma rel_associative_r_r : rel_associativity_r_r ctx_orth ctx_compose adj_l.
  Proof. intros X Y [[X1 Y1] A]; unfold ctx_orth; rewrite <- app_assoc; auto. Qed.

  Fact cl_comm : ipperm P = true -> @cl_commutativity _ _ CL_ctx (composes ctx_compose).
  Proof.
  intros Hb Γ Δ ga H.
  inversion H; subst.
  unfold cl_ctx; simpl; unfold ldual, rdual, ctx_orth.
  intros [[ga de] A] H1.
  specialize H1 with (b ++ a).
  eapply P_perm; [ | apply H1; constructor; assumption ].
  rewrite Hb; simpl.
  apply Permutation_Type_app_head.
  apply Permutation_Type_app_tail.
  apply Permutation_Type_app_swap.
  Qed.

  Notation J := (fun Γ => cl_ctx (sg nil) Γ * cl_ctx (sg Γ ∘ sg Γ) Γ)%type.
  Notation K := (fun Γ => { Δ | Γ = ‼Δ }).

  Local Fact sub_monoid_1 : cl_ctx K nil.
  Proof. intros [[ga de] A] H; change de with (nil ++ de); apply H; exists nil; auto. Qed.

  Local Fact sub_monoid_2 : K ∘ K ⊆ K.
  Proof.
  intros ga H.
  inversion H.
  destruct H0 as [de1 Heq1]; subst.
  destruct H1 as [de2 Heq2]; subst.
  exists (de1 ++ de2).
  unfold ill_lbang.
  rewrite map_app; reflexivity.
  Qed.

  Local Fact sub_J_1 : K ⊆ J.
  Proof.
  intros ga H; inversion H; subst; split; unfold cl_ctx; simpl; unfold ldual, rdual, ctx_orth;
    intros [[de1 de2] A] H1.
  - apply P_weak.
    specialize H1 with ctx_unit; simpl in H1.
    apply H1; reflexivity.
  - apply P_cntr.
    specialize H1 with (‼ x ++ ‼ x); simpl in H1.
    rewrite <- ? app_assoc in H1.
    apply H1; constructor; reflexivity.
  Qed.

  Instance PS_ctx : PhaseSpace (ipperm P) :=
  { Web := list iformula;
    PSCL := CL_ctx;
    PScompose := (@app iformula);
    PSunit := nil;
    PSExp := K;
    PScl_stable_l := stable_l rel_associative_r_l rel_associative_r_r;
    PScl_stable_r := stable_r rel_associative_l_l rel_associative_l_r;
    PScl_associative_l := associative_l (m_rel_associativity_ll _ (@app_assoc _));
    PScl_associative_r := associative_r (m_rel_associativity_lr _ (@app_assoc _));
    PScl_neutral_l_1 := neutral_l_1 (m_rel_neutrality_l_1 _ (@app_nil_l _));
    PScl_neutral_l_2 := neutral_l_2 (m_rel_neutrality_l_2 _ (@app_nil_l _));
    PScl_neutral_r_1 := neutral_r_1 (m_rel_neutrality_r_1 _ (@app_nil_r _));
    PScl_neutral_r_2 := neutral_r_2 (m_rel_neutrality_r_2 _ (@app_nil_r _));
    PSsub_monoid_1 := sub_monoid_1;
    PSsub_monoid_2 := sub_monoid_2;
    PSsub_J := sub_J_1;
    PScl_commute := cl_comm }.

  Notation "↓" := (fun A Γ => Γ ⊢ A [P]).

  Fact dc_closed A : cl (↓A) ⊆ ↓A.
  Proof.
  intros ga Hga; red in Hga.
  simpl in Hga; unfold ldual, rdual, ctx_orth in Hga.
  replace ga with (nil++ga++nil) by (list_simpl; reflexivity).
  specialize Hga with (nil,nil,A).
  apply Hga.
  intro; rewrite <- app_nil_end; auto.
  Qed.

  Hint Resolve subset_preorder dc_closed.

  Definition ILLval P := (fun X Γ => ( Γ = ivar X :: nil )
                               + {a |  Γ = fst (projT2 (ipgax P) a) /\ ivar X = snd (projT2 (ipgax P) a) })%type.

  Hypothesis P_gax_noN_l : gax_noN_l P.
  Hypothesis P_gax_at_l : gax_at_l P.
  Hypothesis P_gax_at_r : gax_at_r P.
  Hypothesis P_gax_cut : gax_cut P.

  Lemma atlist_from_gax : forall a, { l | fst (projT2 (ipgax P) a) = map ivar l }.
  Proof.
  intros a.
  red in P_gax_at_l.
  specialize P_gax_at_l with a.
  revert P_gax_at_l ; remember (fst (projT2 (ipgax P) a)) as L; clear.
  induction L; intros Hat.
  - exists nil; reflexivity.
  - inversion Hat; inversion H1; subst.
    destruct (IHL H2) as [l Heq]; subst.
    exists (x0 :: l); reflexivity.
  Qed.

  Fact ILLgax : forall a, list_form_presem PS_ctx (ILLval P) (fst (projT2 (ipgax P) a))
                    ⊆ cl(form_presem PS_ctx (ILLval P) (snd (projT2 (ipgax P) a))).
  Proof.
  intros.
  etransitivity; [ | apply cl_increase ].
  destruct (atlist_from_gax a) as [l Heq].
  rewrite Heq.
  red in P_gax_at_r; specialize P_gax_at_r with a.
  remember (snd (projT2 (ipgax P) a)) as b.
  destruct b; inversion P_gax_at_r; subst.
  intros x Hx; right; rewrite Heqb.
  enough (forall l0 a l1 l2, map ivar l1 ++ map ivar l0 = fst (projT2 (ipgax P) a) ->
            list_form_presem PS_ctx (ILLval P) (map £ l0) l2 ->
            { c | map ivar l1 ++ l2 = fst (projT2 (ipgax P) c)
               /\ snd (projT2 (ipgax P) a) = snd (projT2 (ipgax P) c) }).
  { specialize X with l a nil x; list_simpl in X.
    symmetry in Heq; apply X in Heq; auto. }
  clear - P_gax_at_l P_gax_cut; induction l0; intros a' l1 l2 Heq Hsem; inversion Hsem; subst.
  - list_simpl in Heq.
    exists a'; split; list_simpl; auto.
  - simpl in X; destruct X; subst.
    + apply IHl0 with (a:=a') (l1 := l1 ++ a :: nil) in X0; list_simpl; auto.
      list_simpl in X0; destruct X0 as [c [Heq1 Heq2]].
      exists c; auto.
    + destruct s as [c [Heq1 Heq2]]; subst.
      red in P_gax_cut.
      specialize P_gax_cut with c a' (map ivar l1) (map ivar l0).
      rewrite <- Heq2 in P_gax_cut.
      symmetry in Heq; apply P_gax_cut in Heq.
      destruct Heq as [d [Heq3 Heq4]].
      destruct (atlist_from_gax c) as [l' Heq'].
      rewrite_all Heq'.
      apply IHl0 with (a:=d) (l1 := l1 ++ l') in X0; list_simpl; auto.
      list_simpl in X0; destruct X0 as [e [Heq5 Heq6]].
      exists e; split; auto.
      etransitivity; eassumption.
  Qed.

  Instance PMILL : PhaseModel P := {
    PMPS := PS_ctx;
    PMval := ILLval P;
    PMgax := ILLgax }.

  Infix "⊸" := (magicwand_l PScompose) (at level 51, right associativity).
  Infix "⟜" := (magicwand_r PScompose) (at level 53, left associativity).
  Notation v := PMval.
  Notation "⟦ A ⟧" := (form_presem PS_ctx (ILLval P) A) (at level 49).

  Hint Resolve (@PScl_stable_l _ PMPS) (@PScl_stable_r _ PMPS)
               magicwand_l_adj_l magicwand_l_adj_r magicwand_r_adj_l magicwand_r_adj_r.

  Section Okada_Lemma.

    Notation ILLcl_closed := (@cl_closed _ _ _ CL_ctx).
    Notation ILLcl_increase := (@cl_increase _ _ CL_ctx).

    Lemma Okada_var_1 X : sg (ivar X :: nil) ⊆ ⟦ivar X⟧.
    Proof. intros x Hx; subst; left; reflexivity. Qed.

    Lemma Okada_var_2 X : ⟦ivar X⟧ ⊆ ↓(ivar X).
    Proof.
    intros x Hx; inversion Hx; subst.
    - apply ax_ir.
    - destruct X0 as [a [Heq1 Heq2]]; subst; rewrite Heq2.
      apply gax_ir.
    Qed.

    Lemma Okada_formula A : ((sg (A :: nil) ⊆ cl(⟦A⟧)) * (⟦A⟧ ⊆ ↓A))%type.
    Proof.
    induction A; simpl;
      try (destruct IHA as [IHA01 IHA02]);
      try (destruct IHA1 as [IHA11 IHA12]);
      try (destruct IHA2 as [IHA21 IHA22]);
     (split; [ |
      try (try (apply ILLcl_closed; auto);
           intros x Hx; inversion Hx; subst; constructor; auto; fail)]).
    - etransitivity; [ apply Okada_var_1 | apply ILLcl_increase ].
    - apply Okada_var_2.
    - unfold ldual, rdual, ctx_orth.
      intros x Hx [[de1 de2] A] Hy; subst; simpl.
      constructor.
      specialize Hy with nil; apply Hy; auto.
    - transitivity (cl (cl (⟦ A1 ⟧) ∘ cl(⟦ A2 ⟧))).
      + transitivity (cl_ctx (sg (A1 :: nil) ∘ sg (A2 :: nil))).
        * unfold cl_ctx; simpl; unfold rdual, ctx_orth.
          intros x Hx [[de1 de2] A] Hy; subst.
          constructor.
          specialize Hy with ((A1 :: nil) ++ A2 :: nil); apply Hy; auto.
          split; auto.
        * apply cl_monotone.
          apply composes_monotone; assumption.
      + apply (@cl_le _ _ _ CL_ctx).
        apply cl_stable; auto.
    - unfold magicwand_r.
      etransitivity; [ | apply ILLcl_increase ].
      intros x Hx y Hy [[G D] B] Hz; inversion Hy; subst; simpl.
      apply lpam_ilr; auto.
      assert (rdual ctx_orth (cl_ctx (⟦ A2 ⟧)) (G, D, B)) as Hz2
        by (apply (fst (rtridual_eq ctx_orth _)); apply Hz).
      change (A2 :: D) with ((A2 :: nil) ++ D); apply Hz2; auto.
    - etransitivity; [ eapply (@cl_magicwand_r_3 _ _ _ CL_ctx) | ]; eauto.
      intros x Hx; constructor.
      apply ILLcl_closed in IHA22; auto.
      apply IHA22, Hx; constructor; auto.
    - unfold magicwand_r.
      etransitivity; [ | apply ILLcl_increase ].
      intros x Hx y Hy [[G D] B] Hz; inversion Hy; subst; simpl.
      apply gen_pam_rule; auto.
      change (N :: D) with ((N :: nil) ++ D); apply Hz.
      apply (@Okada_var_1 atN); auto.
    - etransitivity; [ eapply (@cl_magicwand_r_3 _ _ _ CL_ctx) | ]; eauto.
      intros x Hx; constructor.
      assert (IHN := @Okada_var_2 atN).
      apply ILLcl_closed in IHN; auto.
      apply IHN, Hx; constructor; auto.
    - unfold magicwand_l.
      etransitivity; [ | apply ILLcl_increase ].
      intros x Hx y Hy [[G D] B] Hz; inversion Hy; subst; simpl.
      rewrite <- ? app_assoc; apply lmap_ilr; auto.
      assert (rdual ctx_orth (cl_ctx (⟦ A2 ⟧)) (G, D, B)) as Hz2
        by (apply (fst (rtridual_eq ctx_orth _)); apply Hz).
      change (A2 :: D) with ((A2 :: nil) ++ D); apply Hz2; auto.
    - etransitivity; [ eapply (@cl_magicwand_l_3 _ _ _ CL_ctx) | ]; eauto.
      intros x Hx; constructor.
      apply ILLcl_closed in IHA22; auto.
      apply IHA22, Hx.
      change (A1 :: x) with ((A1 :: nil) ++ x); constructor; auto.
    - unfold magicwand_l.
      etransitivity; [ | apply ILLcl_increase ].
      intros x Hx y Hy [[G D] B] Hz; inversion Hy; subst; simpl.
      rewrite <- ? app_assoc; apply neg_map_rule; auto.
      change (N :: D) with ((N :: nil) ++ D); apply Hz.
      apply (@Okada_var_1 atN); auto.
    - etransitivity; [ eapply (@cl_magicwand_l_3 _ _ _ CL_ctx) | ]; eauto.
      intros x Hx; constructor.
      assert (IHN := @Okada_var_2 atN).
      apply ILLcl_closed in IHN; auto.
      apply IHN, Hx.
      change (A :: x) with ((A :: nil) ++ x); constructor; auto.
    - etransitivity; [ | apply ILLcl_increase ].
      apply top_greatest.
    - etransitivity; [ | apply ILLcl_increase ].
      apply glb_in.
      + apply cl_le in IHA11; auto.
        etransitivity; [ | apply IHA11 ].
        intros x Hx; subst.
        unfold cl; simpl; unfold ldual, rdual, ctx_orth.
        intros [[si1 si2] C] H; simpl.
        apply with_ilr1.
        specialize H with (A1 :: nil); apply H; auto.
      + apply cl_le in IHA21; auto.
        etransitivity; [ | apply IHA21 ].
        intros x Hx; subst.
        unfold cl; simpl; unfold ldual, rdual, ctx_orth.
        intros [[si1 si2] C] H; simpl.
        apply with_ilr2.
        specialize H with (A2 :: nil); apply H; auto.
    - unfold ldual, rdual, ctx_orth.
      intros x Hx; inversion Hx; subst; constructor; auto.
      + specialize X with (nil,nil,A1); list_simpl in X; apply X.
        intros y Hy; list_simpl.
        apply IHA12; auto.
      + specialize X0 with (nil,nil,A2); list_simpl in X0; apply X0.
        intros y Hy; list_simpl.
        apply IHA22; auto.
    - unfold ldual, rdual, ctx_orth.
      intros x Hx [[de1 de2] A] Hy; subst; simpl.
      constructor.
    - transitivity (lub (cl (⟦ A1 ⟧)) (cl(⟦ A2 ⟧))).
      + intros x Hx [[de1 de2] A] Hy; subst; simpl.
        unfold rdual, ctx_orth, lub in Hy.
        constructor.
        * specialize Hy with (A1 :: nil); apply Hy; auto.
        * specialize Hy with (A2 :: nil); apply Hy; auto.
      + apply lub_out; auto.
        * apply (@cl_idempotent _ _ CL_ctx).
        * apply (@cl_monotone _ _ CL_ctx).
          intros x; auto.
        * apply (@cl_monotone _ _ CL_ctx).
          intros x; auto.
    - etransitivity; [ | apply ILLcl_increase ].
      unfold ldual, rdual, ctx_orth.
      intros x Hx [[de1 de2] B] Hy; subst; simpl.
      specialize Hy with (!A :: nil); apply Hy; auto.
      split.
      + exists (A :: nil); reflexivity.
      + enough (sg (!A :: nil) ⊆ cl(⟦A⟧)) as Hoc by (apply Hoc; reflexivity).
        apply cl_le in IHA01; auto.
        etransitivity; [ | apply IHA01 ].
        intros x Hx; subst.
        unfold cl; simpl; unfold ldual, rdual, ctx_orth.
        intros [[si1 si2] C] H; simpl.
        apply de_ilr.
        specialize H with (A :: nil); apply H; auto.
    - apply ILLcl_closed; auto.
      intros x Hx; inversion Hx; subst.
      inversion H; subst.
      constructor; auto.
      unfold ldual, rdual, ctx_orth in X.
      specialize X with (nil,nil,A); list_simpl in X; apply X.
      intros y Hy; list_simpl.
      apply IHA02; auto.
    Qed.

    Notation "⟬߭ Γ ⟭" := (list_form_presem PS_ctx (ILLval P) Γ) (at level 49).

    (* We lift the result to contexts, ie list of formulas *)

    Lemma Okada_ctx Γ: cl (⟬߭Γ⟭)  Γ.
    Proof.
    induction Γ as [ | A ga Hga ]; unfold list_form_presem; simpl.
    - apply ILLcl_increase; reflexivity.
    - apply (@cl_stable _ _ _ CL_ctx); auto.
      change (A :: ga) with ((A :: nil) ++ ga); constructor; auto.
      apply Okada_formula; auto.
    Qed.

  End Okada_Lemma.

End SyntacticModel.


Section cut_admissibility.

  Variable P : ipfrag.
  Hypothesis P_gax_noN_l : gax_noN_l P.
  Hypothesis P_gax_at_l : gax_at_l P.
  Hypothesis P_gax_at_r : gax_at_r P.
  Hypothesis P_gax_cut : gax_cut P.

  (* Coercion: the phase model relying on cut-free provability over P is a phase model for P *)
  Instance PMILL_cfat : PhaseModel P := {
    PMPS := PS_ctx (cutupd_ipfrag P false);
    PMval := ILLval (cutupd_ipfrag P false);
    PMgax := @ILLgax (cutupd_ipfrag P false) P_gax_at_l P_gax_at_r P_gax_cut }.

  Theorem ill_cut_elimination Γ A : ill P Γ A -> ill (cutupd_ipfrag P false) Γ A.
  Proof.
    intros pi.
    apply (ill_soundness PMILL_cfat) in pi; auto.
    assert (gax_noN_l (cutupd_ipfrag P false)) as HgaxN_cf by assumption.
    assert (gax_at_l (cutupd_ipfrag P false)) as Hgax_at_l_cf by assumption.
    assert (gax_at_r (cutupd_ipfrag P false)) as Hgax_at_r_cf by assumption.
    assert (gax_cut (cutupd_ipfrag P false)) as Hgax_cut_cf by assumption.
    assert (HO := snd (Okada_formula HgaxN_cf Hgax_at_l_cf Hgax_at_r_cf Hgax_cut_cf A)).
    apply (@cl_closed _ _ _ PSCL) in HO; [ | apply dc_closed ].
    apply cl_le in pi.
    apply HO, pi, Okada_ctx; auto.
    apply subset_preorder.
  Qed.

End cut_admissibility.

