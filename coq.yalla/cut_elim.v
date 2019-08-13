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

Require Import ill_def.

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

(*
  Notation ILLval := (fun x => ↓(£x)).
*)
  Definition ILLval P := (fun X Γ => ( Γ = ivar X :: nil )
                               + {a |  Γ = fst (projT2 (ipgax P) a) /\ ivar X = snd (projT2 (ipgax P) a) })%type.

  Fact ILLdc_closed: forall A, cl (↓A) ⊆ ↓A.
  Proof. apply dc_closed. Qed.

  Hint Resolve ILLdc_closed.

  Hypothesis P_gax_noN_l : gax_noN_l P.
  Hypothesis P_gax_at_l : gax_at_l P.
  Hypothesis P_gax_at_r : gax_at_r P.
  Hypothesis P_gax_cut : gax_cut P.

  Lemma atlist_from_gax : forall a, {l | fst (projT2 (ipgax P) a) = map ivar l }.
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

  Fact ILLgax : forall a, list_form_presem PSILL (ILLval P) (fst (projT2 (ipgax P) a))
                    ⊆ cl(form_presem PSILL (ILLval P) (snd (projT2 (ipgax P) a))).
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
            list_form_presem PSILL (ILLval P) (map £ l0) l2 ->
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
    PMPS := PSILL;
    PMval := ILLval P;
    PMgax := ILLgax }.

  Infix "∘" := (composes PScompose) (at level 50, no associativity).
  Infix "⊸" := (magicwand_l PScompose) (at level 51, right associativity).
  Infix "⟜" := (magicwand_r PScompose) (at level 53, left associativity).
  Notation v := PMval.
  Notation "⟦ A ⟧" := (form_presem PSILL (ILLval P) A) (at level 49).

  Section Okada_Lemma.

    Let ILLcl_closed X Y : cl Y ⊆ Y -> X ⊆ Y -> cl X ⊆ Y.
    Proof. apply cl_closed; apply subset_preorder. Qed.

    Notation ILLcl_increase := (@cl_increase _ _ (CL_ctx (ill P))).


    Lemma Okada_var_1 : forall X, sg (ivar X :: nil) ⊆ ⟦ivar X⟧.
    Proof. intros X x Hx; subst; left; reflexivity. Qed.

    Lemma Okada_var_2 : forall X, ⟦ivar X⟧ ⊆ ↓(ivar X).
    Proof.
    intros X x Hx; inversion Hx; subst.
    - apply ax_ir.
    - destruct X0 as [a [Heq1 Heq2]]; subst; rewrite Heq2.
      apply gax_ir.
    Qed.

    Lemma Okada_formula A : ((sg (A :: nil) ⊆ ⟦A⟧) * (⟦A⟧ ⊆ ↓A))%type.
    Proof.
    induction A; simpl;
      try (destruct IHA as [IHA01 IHA02]);
      try (destruct IHA1 as [IHA11 IHA12]);
      try (destruct IHA2 as [IHA21 IHA22]);
     (split; [ |
      try (try (apply ILLcl_closed; auto);
           intros x Hx; inversion Hx; subst; constructor; auto; fail)]).
    - apply Okada_var_1.
    - apply Okada_var_2.
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
      enough (sg (A2 o- A1 :: b) ⊆ cl(⟦A2⟧)) as Hi by (apply Hi; reflexivity).
      apply cl_monotone in IHA21; auto.
      etransitivity; [ | apply IHA21 ].
      intros x Hx; subst.
      unfold cl; simpl; unfold ldual, rdual, ctx_orth.
      intros [[si1 si2] C] H; simpl.
      apply lpam_ilr; auto.
      specialize H with (A2 :: nil); apply H; auto.
    - intros x Hx; constructor.
      apply ILLcl_closed in IHA22; [ | apply ILLdc_closed ].
      apply IHA22, Hx; constructor; auto.
    - unfold magicwand_r.
      intros x Hx y Hy; subst.
      inversion Hy; subst.
      enough (sg (igen A :: b) ⊆ cl(⟦N⟧)) as Hi by (apply Hi; reflexivity).
      assert (IHN := @Okada_var_1 atN).
      apply cl_monotone in IHN; auto.
      etransitivity; [ | apply IHN ].
      intros x Hx; subst.
      unfold cl; simpl; unfold ldual, rdual, ctx_orth.
      intros [[si1 si2] C] H; simpl.
      apply gen_pam_rule; auto.
      specialize H with (N :: nil); apply H; auto.
(* TODO simplify ???
      unfold magicwand_r.
      intros x Hx y Hy; subst.
      inversion Hy; subst; simpl.
      apply gen_ilr.
      apply IHA02; auto.
*)
    - intros x Hx; constructor.
      assert (IHN := @Okada_var_2 atN).
      apply ILLcl_closed in IHN; [ | apply ILLdc_closed ].
      apply IHN, Hx; constructor; auto.
    - unfold magicwand_l.
      intros x Hx y Hy; subst.
      inversion Hy; subst.
      enough (sg (a ++ A1 -o A2 :: nil) ⊆ cl(⟦A2⟧)) as Hi by (apply Hi; reflexivity).
      apply cl_monotone in IHA21; auto.
      etransitivity; [ | apply IHA21 ].
      intros x Hx; subst.
      unfold cl; simpl; unfold ldual, rdual, ctx_orth.
      intros [[si1 si2] C] H; list_simpl.
      apply lmap_ilr; auto.
      specialize H with (A2 :: nil); apply H; auto.
    - intros x Hx; constructor.
      apply ILLcl_closed in IHA22; [ | apply ILLdc_closed ].
      apply IHA22, Hx.
      change (A1 :: x) with ((A1 :: nil) ++ x); constructor; auto.
    - unfold magicwand_l.
      intros x Hx y Hy; subst.
      inversion Hy; subst.
      enough (sg (a ++ ineg A :: nil) ⊆ cl(⟦N⟧)) as Hi by (apply Hi; reflexivity).
      assert (IHN := @Okada_var_1 atN).
      apply cl_monotone in IHN; auto.
      etransitivity; [ | apply IHN ].
      intros x Hx; subst.
      unfold cl; simpl; unfold ldual, rdual, ctx_orth.
      intros [[si1 si2] C] H; list_simpl.
      apply neg_map_rule; auto.
      specialize H with (N :: nil); apply H; auto.
(* TODO simplify ???
      unfold magicwand_l.
      intros x Hx y Hy; subst.
      inversion Hy; subst; simpl.
      apply neg_ilr.
      apply IHA02; auto.
*)
    - intros x Hx; constructor.
      assert (IHN := @Okada_var_2 atN).
      apply ILLcl_closed in IHN; [ | apply ILLdc_closed ].
      apply IHN, Hx.
      change (A :: x) with ((A :: nil) ++ x); constructor; auto.
    - apply top_greatest.
    - apply glb_in.
      + apply cl_monotone in IHA11; auto.
        etransitivity; [ | apply IHA11 ].
        intros x Hx; subst.
        unfold cl; simpl; unfold ldual, rdual, ctx_orth.
        intros [[si1 si2] C] H; simpl.
        apply with_ilr1.
        specialize H with (A1 :: nil); apply H; auto.
      + apply cl_monotone in IHA21; auto.
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
      + enough (sg (!A :: nil) ⊆ cl(⟦A⟧)) as Hoc by (apply Hoc; reflexivity).
        apply cl_monotone in IHA01; auto.
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

  End Okada_Lemma.

  Notation "⟬߭ Γ ⟭" := (list_form_presem PSILL (ILLval P) Γ) (at level 49).

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
    PMval := ILLval (cutupd_ipfrag P false);
    PMgax := @ILLgax (cutupd_ipfrag P false) P_gax_at_l P_gax_at_r P_gax_cut }.

  Theorem ill_cut_elimination Γ A : Γ ⊢ A [P] -> Γ ⊢ A [cutupd_ipfrag P false].
  Proof.
    intros pi.
    apply (ill_soundness PMILL_cfat) in pi; auto.
    assert (gax_noN_l (cutupd_ipfrag P false)) as HgaxN_cf by assumption.
    assert (HO := snd (Okada_formula HgaxN_cf A)).
    apply (@cl_closed _ _ _ CL_cfat) in HO; [ | apply dc_closed ].
    apply HO, pi, Okada_ctx; auto.
  Qed.

End cut_admissibility.

(*
Check ill_cut_elimination.
Print Assumptions ill_cut_elimination.
*)

