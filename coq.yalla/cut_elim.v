(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Import EqNotations.
Require Import List_more List_Type_more Permutation_Type_more genperm_Type.

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

  Definition gax_noN_l P := forall a, List_Type.In_Type N (fst (projT2 (ipgax P) a)) -> False.
  Definition gax_at_l P := forall a, Forall_Type iatomic (fst (projT2 (ipgax P) a)).
  Definition gax_at_r P := forall a, iatomic (snd (projT2 (ipgax P) a)).
  Definition gax_cut P := forall a b l1 l2,
                            fst (projT2 (ipgax P) b) = l1 ++ snd (projT2 (ipgax P) a) :: l2 -> 
                          { c | l1 ++ fst (projT2 (ipgax P) a) ++ l2 = fst (projT2 (ipgax P) c)
                                /\ snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) }.

Section CutElim_At.

  Variable P : ipfrag.
  Hypothesis P_gax_noN_l : gax_noN_l P.
  Hypothesis P_gax_cut : gax_cut P.

  Theorem cut_at : forall X l0 l1 l2 A,
    ill P l0 (ivar X) -> ill P (l1 ++ ivar X :: l2) A -> ill P (l1 ++ l0 ++ l2) A.
  Proof.
  intros X l0 l1 l2 Y pi1.
  remember (ivar X) as A.
  revert HeqA l1 l2; induction pi1; intros HeqA l1' l2' pi2; inversion HeqA; subst;
    list_simpl; try rewrite app_assoc;
    try (constructor; auto; list_simpl ; rewrite ? app_comm_cons ; rewrite (app_assoc l1); auto; fail).
  + assumption.
  + rewrite <- app_assoc; apply (ex_ir _ (l1' ++ l1 ++ l2')); auto.
    apply PEperm_Type_app_head ; apply PEperm_Type_app_tail; assumption.
  + apply ex_oc_ir with lw; auto.
    list_simpl ; rewrite (app_assoc l1) ; rewrite (app_assoc _ l2) ; rewrite <- (app_assoc l1); auto.
  + apply gen_pam_rule; auto.
  + rewrite <- app_assoc; apply neg_map_rule; auto.
  + apply cut_ir with A; auto.
    list_simpl; rewrite app_comm_cons ; rewrite (app_assoc l1); auto.
  + list_simpl.
    rewrite HeqA in pi2.
    remember (l1' ++ £ X :: l2') as l0.
    revert l1' l2' Heql0 HeqA; clear - P_gax_noN_l P_gax_cut pi2;
      induction pi2; intros l1' l2' Heql0 HeqA; subst;
      try (constructor; apply IHpi2; auto; fail).
    * destruct l1'; inversion Heql0; subst.
      - rewrite <- HeqA; list_simpl; apply gax_ir.
      - destruct l1'; inversion H1.
    * case_eq (ipperm P); intros HP; rewrite HP in p; simpl in p; auto.
      assert (p' := p).
      apply Permutation_Type_vs_elt_inv in p'.
      destruct p' as [[l1'' l2''] Heq]; simpl in Heq.
      rewrite Heq in p.
      apply Permutation_Type_app_inv in p.
      apply IHpi2 in Heq; auto.
      apply ex_ir with (l1'' ++ fst (projT2 (ipgax P) a) ++ l2''); auto.
      rewrite HP; apply Permutation_Type_app_middle; auto.
    * trichot_Type_elt_app_exec Heql0; subst.
      - rewrite 2 app_assoc; apply ex_oc_ir with lw; auto.
        list_simpl; apply IHpi2; list_simpl; auto.
      - destruct Heql2 as [Heql2 _]; decomp_map_Type Heql2; inversion Heql2.
      - list_simpl; apply ex_oc_ir with lw; auto.
        rewrite 2 app_assoc; apply IHpi2; list_simpl; auto.
    * destruct l1'; inversion Heql0.
    * trichot_Type_elt_elt_exec Heql0.
      - list_simpl; apply one_ilr; rewrite app_assoc; apply IHpi2; list_simpl; auto.
      - inversion Heql2.
      - rewrite 2 app_assoc; apply one_ilr; list_simpl; apply IHpi2; list_simpl; auto.
    * dichot_Type_elt_app_exec Heql0; subst.
      - rewrite 2 app_assoc; apply tens_irr; list_simpl; auto.
      - list_simpl; apply tens_irr; auto.
    * trichot_Type_elt_elt_exec Heql0.
      - list_simpl; apply tens_ilr; rewrite 2 app_comm_cons; rewrite app_assoc; apply IHpi2; list_simpl; auto.
      - inversion Heql2.
      - rewrite 2 app_assoc; apply tens_ilr; list_simpl; apply IHpi2; list_simpl; auto.
    * apply lpam_irr; list_simpl; apply IHpi2; list_simpl; auto.
    * trichot_Type_elt_elt_exec Heql0.
      - dichot_Type_elt_app_exec Heql2; subst.
        ++ list_simpl; rewrite 2 app_assoc; apply lpam_ilr; list_simpl; auto.
        ++ list_simpl; apply lpam_ilr; auto.
           rewrite app_comm_cons; rewrite app_assoc; apply IHpi2_2; list_simpl; auto.
      - inversion Heql2.
      - rewrite 2 app_assoc; apply lpam_ilr; auto.
        list_simpl; apply IHpi2_2; list_simpl; auto.
    * apply gen_irr; rewrite <- 2 app_assoc; apply IHpi2; list_simpl; auto.
    * destruct l1'; inversion Heql0; subst.
      list_simpl; apply gen_ilr ; apply IHpi2; auto.
    * apply lmap_irr; rewrite app_comm_cons; apply IHpi2; auto.
    * rewrite app_assoc in Heql0; trichot_Type_elt_elt_exec Heql0.
      - list_simpl; apply lmap_ilr; auto.
        rewrite app_comm_cons; rewrite app_assoc; apply IHpi2_2; list_simpl; auto.
      - inversion Heql2.
      - dichot_Type_elt_app_exec Heql1; subst.
        ++ list_simpl; rewrite 2 app_assoc; apply lmap_ilr; auto.
           list_simpl; apply IHpi2_2; list_simpl; auto.
        ++ list_simpl; rewrite (app_assoc l4); rewrite (app_assoc _ l); apply lmap_ilr; auto.
           list_simpl; apply IHpi2_1; list_simpl; auto.
    * apply neg_irr; rewrite app_comm_cons; apply IHpi2; auto.
    * trichot_Type_elt_elt_exec Heql0.
      - destruct l0; inversion Heql2.
      - inversion Heql2.
      - rewrite 2 app_assoc; apply neg_ilr; list_simpl; apply IHpi2; list_simpl; auto.
    * apply with_irr; [ apply IHpi2_1 | apply IHpi2_2 ]; auto.
    * trichot_Type_elt_elt_exec Heql0.
      - list_simpl; apply with_ilr1; rewrite app_comm_cons; rewrite app_assoc; apply IHpi2; list_simpl; auto.
      - inversion Heql2.
      - rewrite 2 app_assoc; apply with_ilr1; list_simpl; apply IHpi2; list_simpl; auto.
    * trichot_Type_elt_elt_exec Heql0.
      - list_simpl; apply with_ilr2; rewrite app_comm_cons; rewrite app_assoc; apply IHpi2; list_simpl; auto.
      - inversion Heql2.
      - rewrite 2 app_assoc; apply with_ilr2; list_simpl; apply IHpi2; list_simpl; auto.
    * trichot_Type_elt_elt_exec Heql0.
      - list_simpl; apply zero_ilr; rewrite app_assoc; apply IHpi2; list_simpl; auto.
      - inversion Heql2.
      - rewrite 2 app_assoc; apply zero_ilr; list_simpl; apply IHpi2; list_simpl; auto.
    * trichot_Type_elt_elt_exec Heql0.
      - list_simpl; apply plus_ilr; rewrite app_comm_cons; rewrite app_assoc;
          [ apply IHpi2_1 | apply IHpi2_2 ]; list_simpl; auto.
      - inversion Heql2.
      - rewrite 2 app_assoc; apply plus_ilr; list_simpl;
          [ apply IHpi2_1 | apply IHpi2_2 ]; list_simpl; auto.
    * symmetry in Heql0; decomp_map_Type Heql0; inversion Heql0.
    * trichot_Type_elt_elt_exec Heql0.
      - list_simpl; apply de_ilr; rewrite app_comm_cons; rewrite app_assoc; apply IHpi2; list_simpl; auto.
      - inversion Heql2.
      - rewrite 2 app_assoc; apply de_ilr; list_simpl; apply IHpi2; list_simpl; auto.
    * trichot_Type_elt_elt_exec Heql0.
      - list_simpl; apply wk_ilr; rewrite app_assoc; apply IHpi2; list_simpl; auto.
      - inversion Heql2.
      - rewrite 2 app_assoc; apply wk_ilr; list_simpl; apply IHpi2; list_simpl; auto.
    * trichot_Type_elt_elt_exec Heql0.
      - list_simpl; apply co_ilr; rewrite 2 app_comm_cons; rewrite app_assoc; apply IHpi2; list_simpl; auto.
      - inversion Heql2.
      - rewrite 2 app_assoc; apply co_ilr; list_simpl; apply IHpi2; list_simpl; auto.
    * apply cut_ir with (ivar X); auto.
      - rewrite <- HeqA; apply gax_ir.
      - rewrite <- Heql0; apply cut_ir with A; auto.
    * rewrite <- HeqA in Heql0.
      destruct (P_gax_cut a a0 l1' l2') as [c [H1 H2]]; auto.
      rewrite H1, H2.
      apply gax_ir.
  Qed.

End CutElim_At.


Section Okada.

  Variable P : ipfrag.

  Instance PSILL : PhaseSpace (ipperm P) :=
    PS_ctx (ill P) (ipperm P) (@P_perm P) (@P_weak P) (@P_cntr P).
  Instance CLILL : ClosureOp := PSCL.

  Hint Resolve (@composes_monotone _ PSCompose).

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

  Let ltimes := fold_right (fun x y => tensor (Composes PSCompose) x y) (unit PSunit).
  Let lcompose := fold_right (fun x y => Composes PSCompose x y) (sg PSunit).
  Fact ILLgax : forall a, list_Form_sem PSILL ILLval (fst (projT2 (ipgax P) a))
                    ⊆ Form_sem PSILL ILLval (snd (projT2 (ipgax P) a)).
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
    replace (list_Form_sem PSILL ILLval (map ivar l))
       with (ltimes (map ILLval l))
      by (clear; induction l; auto; simpl; rewrite IHl; auto).
    apply subset_trans with (cl (lcompose (map ILLval l))).
    { clear; induction l; try reflexivity.
      revert IHl; simpl.
      remember (ltimes (map (fun x Γ => ill P Γ (£ x)) l)) as L1; clear HeqL1.
      remember (lcompose (map (fun x Γ => ill P Γ (£ x)) l)) as L2; clear HeqL2.
      remember (fun Γ : list iformula => ill P Γ (£ a)) as L0; clear HeqL0.
      intros IH.
      apply (fst (@cl_prop _ (CL_ctx (ill P)) _ _)).
      apply composes_congruent_l_1; auto.
      unfold cl_stability_r; apply cl_ctx_stable_r.
      apply P_perm. }
    apply cl_closed; [ apply ILLvdc_closed | ].
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
      rewrite <- app_assoc in X0.
      apply ex_ir with (l0 ++ a0 ++ b); auto.
      apply PEperm_Type_app_head; auto.
  Qed.

  Instance PMILL : PhaseModel P := {
    PMPS := PSILL;
    PMval := ILLval;
    PMval_closed := ILLvdc_closed;
    PMgax := ILLgax
  }.

  Infix "∘" := (Composes PSCompose) (at level 50, no associativity).
  Infix "⊸" := (Magicwand_l PSCompose) (at level 51, right associativity).
  Infix "⟜" := (Magicwand_r PSCompose) (at level 52, left associativity).
  Notation v := PMval.
  Notation Hv := PMval_closed.
  Notation "'⟦' A '⟧'" := (Form_sem PSILL ILLval A) (at level 49).

  Let cl_sem_closed A : cl (⟦A⟧) ⊆ ⟦A⟧.
  Proof. apply (@closed_Form_sem _ PMILL); auto. Qed.

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

    Let rule_zero_l : cl (fun _ => False) (0::∅).
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

  Notation "'⟬߭' Γ '⟭'" := (list_Form_sem PSILL ILLval Γ) (at level 49).

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

