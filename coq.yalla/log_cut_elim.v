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

Require Import List_more List_Type_more Permutation_Type genperm_Type.

Require Import orthogonality log_phase_sem.

Require Import ill_def.
Import SetNotations. (* ⊆ ≃ ∩ ∪ ∅ *)
Definition ill_lbang := map ioc.
Notation "‼ x" := (ill_lbang x) (at level 55).


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
  Notation ctx_adj_l := (fun ϴ H => match H with (Γ,Δ,A) => (Γ, ϴ ++ Δ, A) end).
  Notation ctx_adj_r := (fun ϴ H => match H with (Γ,Δ,A) => (Γ ++ ϴ, Δ, A) end).

  Notation ctx_hole := (list iformula * list iformula * iformula)%type.
  Infix "∘" := (composes ctx_compose) (at level 50, no associativity).

  Definition ctx_orth : list iformula -> ctx_hole -> Type :=
    fun ϴ H => match H with (Γ,Δ,A) => Γ ++ ϴ ++ Δ ⊢ A [P] end.

  Instance CL_ctx : ClosureOp := (@lclosure _ _ ctx_orth).
  Notation cl_ctx := (@cl _ _ CL_ctx).

  Lemma cl_ctx_to_logic ϴ ϴ' : cl (sg ϴ') ϴ -> forall Γ Δ A,
    Γ ++ ϴ' ++ Δ ⊢ A [P] -> Γ ++ ϴ ++ Δ ⊢ A [P].
  Proof.
  unfold cl_ctx, CL_ctx, lclosure, ctx_orth, ldual, rdual.
  intros Hcl Γ Δ A pi.
  specialize Hcl with (Γ,Δ,A); apply Hcl.
  intros x Hx; subst; assumption.
  Qed.

  Lemma logic_to_cl_ctx ϴ ϴ' : (forall Γ Δ A, Γ ++ ϴ' ++ Δ ⊢ A [P] -> Γ ++ ϴ ++ Δ ⊢ A [P]) ->
    cl (sg ϴ') ϴ.
  Proof.
  unfold cl_ctx, CL_ctx, lclosure, ctx_orth, ldual, rdual.
  intros Hlog [[Γ Δ] A] Hcl.
  apply Hlog, Hcl; reflexivity.
  Qed.

  Lemma rel_associative_l_l : rel_associativity_l_l ctx_orth ctx_compose ctx_adj_r.
  Proof. intros X Y [[X1 Y1] A]; unfold ctx_orth; rewrite <- ? app_assoc; auto. Qed.

  Lemma rel_associative_l_r : rel_associativity_l_r ctx_orth ctx_compose ctx_adj_r.
  Proof. intros X Y [[X1 Y1] A]; unfold ctx_orth; rewrite <- ? app_assoc; auto. Qed.

  Lemma rel_associative_r_l : rel_associativity_r_l ctx_orth ctx_compose ctx_adj_l.
  Proof. intros X Y [[X1 Y1] A]; unfold ctx_orth; rewrite <- app_assoc; auto. Qed.

  Lemma rel_associative_r_r : rel_associativity_r_r ctx_orth ctx_compose ctx_adj_l.
  Proof. intros X Y [[X1 Y1] A]; unfold ctx_orth; rewrite <- app_assoc; auto. Qed.

  Fact cl_comm : ipperm P = true -> @cl_commutativity _ _ CL_ctx (composes ctx_compose).
  Proof.
  intros Hb Γ Δ ga H.
  inversion H; subst.
  unfold cl_ctx; simpl; unfold ldual, rdual, ctx_orth; intros [[ga de] A] H1.
  specialize H1 with (b ++ a).
  eapply P_perm; [ | apply H1; constructor; assumption ].
  rewrite Hb; simpl.
  apply Permutation_Type_app_head, Permutation_Type_app_tail, Permutation_Type_app_swap.
  Qed.

  Notation K := (fun Γ => { Δ | Γ = ‼Δ }).

  Local Fact str_sub_monoid_1 : K nil.
  Proof. exists nil; reflexivity. Qed.

  Local Fact sub_monoid_2 : K ∘ K ⊆ K.
  Proof.
  intros ga H; inversion H.
  destruct H0 as [de1 Heq1]; subst.
  destruct H1 as [de2 Heq2]; subst.
  exists (de1 ++ de2).
  unfold ill_lbang; rewrite map_app; reflexivity.
  Qed.

  Notation J := (fun Γ => cl_ctx (sg nil) Γ * cl_ctx (sg Γ ∘ sg Γ) Γ)%type.
  Local Fact sub_J : K ⊆ J.
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

  Local Fact sub_monoid_distr : @sub_monoid_distr_hyp _ subset (composes (@app iformula)) glb K.
  Proof.
  apply pwr_str_sub_monoid_distr.
  intros G D [S HS].
  unfold ill_lbang in HS.
  decomp_map_Type HS; subst; simpl.
  split; [ exists l0 | exists l1 ]; reflexivity.
  Qed.

  Instance PS_ctx : MPhaseSpace (ipperm P) := {
    Web := list iformula;
    PScompose := (@app iformula);
    PSunit := nil;
    PS_associative := (@app_assoc _);
    PS_neutral_l := (@app_nil_l _);
    PS_neutral_r := (@app_nil_r _);
    PSCL := CL_ctx;
    PScl_stable_l := stable_l rel_associative_r_l rel_associative_r_r;
    PScl_stable_r := stable_r rel_associative_l_l rel_associative_l_r;
    PSExp := K;
    PSsub_monoid_1 := str_sub_monoid_1;
    PSsub_monoid_2 := sub_monoid_2;
    PSsub_J := sub_J;
    PSsub_monoid_distr := sub_monoid_distr;
    PScl_commute := cl_comm }.

  Notation "↓" := (fun A Γ => Γ ⊢ A [P]).

  Fact dc_closed A : cl(↓A) ⊆ ↓A.
  Proof.
  intros ga Hga; simpl in Hga; unfold ldual, rdual, ctx_orth in Hga.
  specialize Hga with (nil,nil,A).
  replace ga with (nil++ga++nil) by (list_simpl; reflexivity).
  apply Hga.
  intro; rewrite app_nil_r; auto.
  Qed.

  Fact closure_sg_in_dc A : cl_ctx (sg (A :: nil)) ⊆ ↓A.
  (* the converse ↓A ⊆ cl_ctx (sg (A :: nil)) is exactly cut *)
  Proof. etransitivity; [ apply cl_monotone | apply dc_closed ]; apply sg_subset, ax_exp_ill. Qed.

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
  destruct (atlist_from_gax a) as [l Heq]; rewrite Heq.
  red in P_gax_at_r; specialize P_gax_at_r with a.
  remember (snd (projT2 (ipgax P) a)) as b.
  destruct b; inversion P_gax_at_r; subst.
  intros x Hx; right; rewrite Heqb.
  enough (forall l0 a l1 l2, map ivar l1 ++ map ivar l0 = fst (projT2 (ipgax P) a) ->
            list_form_presem PS_ctx (ILLval P) (map ivar l0) l2 ->
            { c | map ivar l1 ++ l2 = fst (projT2 (ipgax P) c)
               /\ snd (projT2 (ipgax P) a) = snd (projT2 (ipgax P) c) })
    by (specialize X with l a nil x; list_simpl in X; symmetry in Heq; apply X in Heq; auto).
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
      apply IHl0 with (a := d) (l1 := l1 ++ l') in X0; list_simpl; auto.
      list_simpl in X0; destruct X0 as [e [Heq5 Heq6]].
      exists e; split; auto.
      etransitivity; eassumption.
  Qed.

  Instance PMILL : MPhaseModel P := {
    PMPS := PS_ctx;
    PMval := ILLval P;
    PMgax := ILLgax }.

  Infix "⊸" := (magicwand_l PScompose) (at level 52, right associativity).
  Infix "⟜" := (magicwand_r PScompose) (at level 53, left associativity).
  Notation v := PMval.
  Notation "⟦ A ⟧" := (form_presem PS_ctx (ILLval P) A).
  Notation "⟬߭ Γ ⟭" := (list_form_presem PS_ctx (ILLval P) Γ).
  Notation "□" := (@cl _ _ PSCL).
  Notation "l ⊧  x" := (@list_compose _ PMPS l ⊆ x) (at level 70, no associativity).

  Hint Resolve (@PScl_stable_l _ PMPS) (@PScl_stable_r _ PMPS)
               magicwand_l_adj_l magicwand_l_adj_r magicwand_r_adj_l magicwand_r_adj_r.


  Lemma logic_to_plogic ϴ ϴ' : (forall Γ Δ A, Γ ++ ϴ' ++ Δ ⊢ A [P] -> Γ ++ ϴ ++ Δ ⊢ A [P]) ->
    forall Γ Δ A, Γ ++ (sg ϴ') :: Δ ⊧ □A -> Γ ++ sg ϴ :: Δ ⊧ □A.
  Proof. intros H Γ Δ A; apply list_compose_monot_sg_mnd, logic_to_cl_ctx; assumption. Qed.

  Lemma plogic_to_logic ϴ ϴ' : (forall Γ Δ A, Γ ++ (sg ϴ') :: Δ ⊧ □A -> Γ ++ sg ϴ :: Δ ⊧ □A) ->
    forall Γ Δ A, Γ ++ ϴ' ++ Δ ⊢ A [P] -> Γ ++ ϴ ++ Δ ⊢ A [P].
  Proof.
  intros H Γ Δ A.
  apply cl_ctx_to_logic.
  apply (@list_compose_cons_sg_to_sem _ PMPS) in H; assumption.
  Qed.


  Section Okada_Lemma.

    Notation ILLcl_closed := (@cl_closed _ _ _ CL_ctx).
    Notation ILLcl_increase := (@cl_increase _ _ CL_ctx).
    Notation ILLcl_monotone := (@cl_monotone _ _ CL_ctx).
    Notation ILLcl_le := (@cl_le _ _ _ CL_ctx).

    Hint Resolve glb_in glb_out_l glb_out_r.

    Lemma Okada_var_1 X : sg (ivar X :: nil) ⊆ ⟦ivar X⟧.
    Proof. intros x Hx; subst; left; reflexivity. Qed.

    Lemma Okada_var_2 X : ⟦ivar X⟧ ⊆ ↓(ivar X).
    Proof.
    intros x Hx; inversion Hx; subst.
    - apply ax_ir.
    - destruct X0 as [a [Heq1 Heq2]]; subst; rewrite Heq2.
      apply gax_ir.
    Qed.

    Lemma Okada_formula A : ((sg (A :: nil) ⊆ □(⟦A⟧)) * (⟦A⟧ ⊆ ↓A))%type.
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
    - apply sg_subset, logic_to_cl_ctx, one_ilr.
    - transitivity (cl (sg ((A1 :: nil) ++ A2 :: nil))).
      + apply sg_subset, logic_to_cl_ctx, tens_ilr.
      + apply ILLcl_le.
        etransitivity; [ | apply cl_stable ]; auto.
        simpl; change (A1 :: A2 :: nil) with ((A1 :: nil) ++ A2 :: nil).
        apply sg_subset in IHA11; apply sg_subset in IHA21.
        apply sg_subset; constructor; try assumption.
    - transitivity (cl(sg(A2::nil)) ⟜ ↓A1).
      + apply sg_subset.
        intros x Hx; inversion Hx; subst.
        apply logic_to_cl_ctx; intros; apply lpam_ilr; assumption.
      + etransitivity; [ | apply ILLcl_increase ].
        assert (Hmon := (@magicwand_r_monotone _ _ _ _ (@composes_monotone _ PScompose))); apply Hmon; auto.
        apply ILLcl_le; assumption.
    - etransitivity; [ eapply (@cl_magicwand_r_3 _ _ _ CL_ctx) | ]; eauto.
      transitivity (↓A2 ⟜ sg(A1::nil)).
      + assert (Hmon := (@magicwand_r_monotone _ _ _ _ (@composes_monotone _ PScompose))); apply Hmon; auto.
        apply ILLcl_closed; auto.
      + intros G HG; apply lpam_irr, HG; constructor; reflexivity.
    - transitivity (cl(sg(N::nil)) ⟜ ↓A).
      + apply sg_subset.
        intros x Hx; inversion Hx; subst.
        apply logic_to_cl_ctx; intros; apply gen_pam_rule; assumption.
      + etransitivity; [ | apply ILLcl_increase ].
        assert (Hmon := (@magicwand_r_monotone _ _ _ _ (@composes_monotone _ PScompose))); apply Hmon; auto.
        apply ILLcl_monotone, Okada_var_1.
    - etransitivity; [ eapply (@cl_magicwand_r_3 _ _ _ CL_ctx) | ]; eauto.
      transitivity (↓N ⟜ sg(A::nil)).
      + assert (Hmon := (@magicwand_r_monotone _ _ _ _ (@composes_monotone _ PScompose))); apply Hmon; auto.
        apply ILLcl_closed, Okada_var_2; auto.
      + intros G HG; apply gen_irr, HG; constructor; reflexivity.
    - transitivity (↓A1 ⊸ cl(sg(A2::nil))).
      + apply sg_subset.
        intros x Hx; inversion Hx; subst.
        apply logic_to_cl_ctx; intros; list_simpl; apply lmap_ilr; assumption.
      + etransitivity; [ | apply ILLcl_increase ].
        assert (Hmon := (@magicwand_l_monotone _ _ _ _ (@composes_monotone _ PScompose))); apply Hmon; auto.
        apply ILLcl_le; assumption.
    - etransitivity; [ eapply (@cl_magicwand_l_3 _ _ _ CL_ctx) | ]; eauto.
      transitivity (sg(A1::nil) ⊸ ↓A2).
      + assert (Hmon := (@magicwand_l_monotone _ _ _ _ (@composes_monotone _ PScompose))); apply Hmon; auto.
        apply ILLcl_closed; auto.
      + intros G HG; apply lmap_irr, HG.
        change (A1 :: G) with ((A1::nil) ++ G) ; constructor; reflexivity.
    - transitivity (↓A ⊸ cl(sg(N::nil))).
      + apply sg_subset.
        intros x Hx; inversion Hx; subst.
        apply logic_to_cl_ctx; intros; list_simpl; apply neg_map_rule; assumption.
      + etransitivity; [ | apply ILLcl_increase ].
        assert (Hmon := (@magicwand_l_monotone _ _ _ _ (@composes_monotone _ PScompose))); apply Hmon; auto.
        apply ILLcl_monotone, Okada_var_1.
    - etransitivity; [ eapply (@cl_magicwand_l_3 _ _ _ CL_ctx) | ]; eauto.
      transitivity (sg(A::nil) ⊸ ↓N).
      + assert (Hmon := (@magicwand_l_monotone _ _ _ _ (@composes_monotone _ PScompose))); apply Hmon; auto.
        apply ILLcl_closed, Okada_var_2; auto.
      + intros G HG; apply neg_irr, HG.
        change (A :: G) with ((A::nil) ++ G) ; constructor; reflexivity.
    - etransitivity; [ | apply ILLcl_increase ].
      apply top_greatest.
    - transitivity (cl (sg(A1 :: nil)) ∩ cl(sg(A2 :: nil))).
      + apply glb_in; apply sg_subset, logic_to_cl_ctx; [ apply with_ilr1 | apply with_ilr2 ].
      + etransitivity; [ | apply ILLcl_increase ].
        apply (@mglb_monotone _ _ subset_preorder glb); auto; apply ILLcl_le; assumption.
    - transitivity (cl(↓A1) ∩ cl(↓A2)).
      + apply (@mglb_monotone _ _ subset_preorder glb);auto; apply ILLcl_monotone; assumption.
      + etransitivity; [ apply (@mglb_monotone _ _ subset_preorder glb), dc_closed | ]; auto.
        intros G [pi1 pi2]; apply with_irr; [ apply pi1 | apply pi2 ].
    - unfold ldual, rdual, ctx_orth.
      intros x Hx [[de1 de2] A] Hy; subst; simpl.
      apply zero_ilr.
    - transitivity (lub (sg (A1::nil)) (sg(A2::nil))).
      + intros x Hx [[de1 de2] A] Hy; subst; simpl.
        unfold rdual, ctx_orth, lub in Hy.
        apply plus_ilr; cons2app; apply Hy; auto.
      + apply lub_out; auto; [ apply (@cl_idempotent _ _ CL_ctx) | | ];
          (etransitivity; [ eassumption | ]); apply ILLcl_monotone; intros ?; auto.
    - etransitivity; [ | apply ILLcl_increase ]; apply glb_in.
      + apply sg_subset; exists (A::nil); reflexivity.
      + transitivity (cl (sg (A :: nil))).
        * apply sg_subset, logic_to_cl_ctx; apply de_ilr.
        * apply ILLcl_le; assumption.
    - etransitivity; [ apply pre_store_monotone, ILLcl_monotone, IHA02 | ]; auto.
      etransitivity; [ apply pre_store_monotone, dc_closed | ]; auto.
      intros G [Hoc pi]; inversion Hoc; subst; apply oc_irr, pi.
    Qed.

    (* We lift the result to contexts, ie list of formulas *)

    Lemma Okada_ctx Γ: □⟬߭Γ⟭ Γ.
    Proof.
    induction Γ as [ | A Γ HG ]; unfold list_form_presem; simpl.
    - apply ILLcl_increase; reflexivity.
    - apply (@cl_stable _ _ _ CL_ctx); auto.
      change (A :: Γ) with ((A :: nil) ++ Γ); constructor; auto.
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
  Instance PMILL_cfat : MPhaseModel P := {
    PMPS := PS_ctx (cutrm_ipfrag P);
    PMval := ILLval (cutrm_ipfrag P);
    PMgax := @ILLgax (cutrm_ipfrag P) P_gax_at_l P_gax_at_r P_gax_cut }.

  Theorem ill_cut_elimination Γ A : ill P Γ A -> ill (cutrm_ipfrag P) Γ A.
  Proof.
    intros pi.
    apply (ill_soundness PMILL_cfat) in pi; auto.
    assert (gax_noN_l (cutrm_ipfrag P)) as HgaxN_cf by assumption.
    assert (gax_at_l (cutrm_ipfrag P)) as Hgax_at_l_cf by assumption.
    assert (gax_at_r (cutrm_ipfrag P)) as Hgax_at_r_cf by assumption.
    assert (gax_cut (cutrm_ipfrag P)) as Hgax_cut_cf by assumption.
    assert (HO := snd (Okada_formula HgaxN_cf Hgax_at_l_cf Hgax_at_r_cf Hgax_cut_cf A)).
    apply (@cl_closed _ _ _ PSCL) in HO; [ | apply dc_closed ].
    apply cl_le in pi.
    apply HO, pi, Okada_ctx; auto.
    apply subset_preorder.
  Qed.

End cut_admissibility.

