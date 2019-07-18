Require Import Psatz.
Require Import List_more List_Type_more Permutation_Type genperm_Type wf_nat_more.

Require Import closure_operators cphase_sem.

Require Import ll_def.

Notation "X '⊆' Y" := (subset X Y) (at level 75, format "X  ⊆  Y", no associativity).
Notation "X '≃' Y" := (eqset X Y) (at level 75, format "X  ≃  Y", no associativity).
Notation "A '∩' B" := (fun z => A z * B z : Type)%type (at level 50, format "A  ∩  B", left associativity).
Notation "A '∪' B" := (fun z => A z + B z : Type)%type (at level 50, format "A  ∪  B", left associativity).

Definition gax_at P := forall a, Forall atomic (projT2 (pgax P) a).
Definition gax_cut P := forall a b x l1 l2 l3 l4,
  projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
  { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }.

Lemma ex_app P : forall l1 l2, ll P (l1 ++ l2) -> ll P (l2 ++ l1).
Proof. intros l1 l2 pi; eapply ex_r ; [ apply pi | apply PCperm_Type_app_comm ]. Qed.

Section CutElim_At.

  Variable P : pfrag.
  Hypothesis P_gax_cut : gax_cut P.

  Theorem cut_at : forall X l1 l2 l3 l4,
    ll P (l1 ++ var X :: l2) -> ll P (l3 ++ covar X :: l4) -> ll P (l1 ++ l4 ++ l3 ++ l2).
  Proof.
  enough (forall s A l0 l1 l2 (pi1: ll P (A :: l0)) (pi2 : ll P (l1 ++ dual A :: l2)),
         s = psize pi1 + psize pi2 -> { X & A = var X } + { X & A = covar X } -> ll P (l1 ++ l0 ++ l2))
    as Hat.
  { intros X l1 l2 l3 l4 pi1 pi2.
    eapply ex_r; [ | apply PCperm_Type_app_comm ].
    rewrite app_assoc; rewrite <- 2 app_assoc.
    eapply ex_r; [ | apply PCperm_Type_app_comm ].
    rewrite <- app_assoc.
    apply (ex_r _ _ ((var X :: l2) ++ l1)) in pi1 ; [ | apply PCperm_Type_app_comm ].
    rewrite <- app_comm_cons in pi1.
    refine (Hat (psize pi1 + psize pi2) (var X) (l2 ++ l1) l3 l4 pi1 pi2 _ _).
    - reflexivity.
    - left; eexists; reflexivity. }
  induction s as [s IHsize0] using lt_wf_rect; intros A l0 l1 l2 pi1 pi2 Heqs Hat; subst.
  remember (l1 ++ dual A :: l2) as l; destruct_ll pi2 f X l Hl Hr HP a; simpl in IHsize0.
  - destruct l1; inversion Heql; subst.
    + apply codual in H0; simpl; subst.
      eapply ex_r; [ | apply PCperm_Type_app_comm ].
      apply pi1.
    + destruct l1; inversion H1; [ | destruct l1; inversion H2 ]; subst.
      apply codual in H0; simpl; subst.
      list_simpl; apply pi1.
  - apply PCperm_Type_vs_elt_inv in HP.
    destruct HP as [(l1',l2') Heq HP']; subst.
    apply (ex_r _ (l1' ++ l0 ++ l2')).
    + refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
    + etransitivity; [ apply PCperm_Type_app_comm | ].
      etransitivity; [ | apply PCperm_Type_app_comm ].
      list_simpl; symmetry.
      apply PEperm_PCperm_Type.
      apply PEperm_Type_app_head; assumption.
  - trichot_Type_elt_app_exec Heql; subst.
    + rewrite 2 app_assoc.
      eapply ex_wn_r; [ | apply HP ].
      revert Hl IHsize0; list_simpl; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
    + destruct Heql1 as [H _].
      decomp_map_Type H.
      destruct A; inversion H3; destruct Hat as [[? Heq] | [? Heq]]; inversion Heq.
    + list_simpl.
      eapply ex_wn_r; [ | apply HP ].
      revert Hl IHsize0; rewrite 2 app_assoc; intros Hl IHsize0.
      rewrite 2 app_assoc.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
  - destruct l1; inversion Heql.
  - dichot_Type_elt_app_exec Heql; subst.
    + rewrite 2 app_assoc.
      apply mix2_r; auto.
      list_simpl.
      refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); try lia.
    + list_simpl.
      apply mix2_r; auto.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
  - destruct l1; inversion Heql; [ | destruct l1; inversion H1 ].
    destruct A; inversion H0.
    destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  - destruct l1; inversion Heql; subst.
    + destruct A; inversion H0.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
    + simpl; apply bot_r.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
  - destruct l1; inversion Heql; subst.
    + destruct A; inversion H0.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
    + dichot_Type_elt_app_exec H1; subst.
      * list_simpl; rewrite 2 app_assoc.
        apply tens_r; auto.
        list_simpl; rewrite app_comm_cons.
        revert Hr IHsize0; rewrite app_comm_cons; intros Hr IHsize0.
        refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); try lia.
      * list_simpl.
        apply tens_r; auto.
        list_simpl; rewrite app_comm_cons.
        revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
        refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
  - destruct l1; inversion Heql; subst.
    + destruct A; inversion H0.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
    + simpl; apply parr_r.
      revert Hl IHsize0; rewrite 2 app_comm_cons; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
  - destruct l1; inversion Heql; subst.
    + destruct A; inversion H0.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
    + apply top_r.
  - destruct l1; inversion Heql; subst.
    + destruct A; inversion H0.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
    + simpl; apply plus_r1.
      revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
  - destruct l1; inversion Heql; subst.
    + destruct A; inversion H0.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
    + simpl; apply plus_r2.
      revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
  - destruct l1; inversion Heql; subst.
    + destruct A; inversion H0.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
    + simpl; apply with_r.
      * revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
        refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
      * revert Hr IHsize0; rewrite app_comm_cons; intros Hr IHsize0.
        refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); try lia.
  - destruct l1; inversion Heql; subst.
    + destruct A; inversion H0.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
    + symmetry in H1; decomp_map_Type H1.
      destruct A; inversion H1.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
  -  destruct l1; inversion Heql; subst.
    + destruct A; inversion H0.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
    + simpl; apply de_r.
      revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
  - destruct l1; inversion Heql; subst.
    + destruct A; inversion H0.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
    + simpl; apply wk_r.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
  - destruct l1; inversion Heql; subst.
    + destruct A; inversion H0.
      destruct Hat as [[X Heq] | [X Heq]]; discriminate Heq.
    + simpl; apply co_r.
      revert Hl IHsize0; rewrite 2 app_comm_cons; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
  - dichot_Type_elt_app_exec Heql; subst.
    + rewrite 2 app_assoc.
      eapply (cut_r _ A0); auto.
      list_simpl; rewrite app_comm_cons.
      revert Hr IHsize0; rewrite app_comm_cons; intros Hr IHsize0.
      refine (IHsize0 (psize pi1 + psize Hr) _ _ _ _ _ pi1 Hr _ Hat); try lia.
    + list_simpl.
      eapply (cut_r _ A0); auto.
      list_simpl; rewrite app_comm_cons.
      revert Hl IHsize0; rewrite app_comm_cons; intros Hl IHsize0.
      refine (IHsize0 (psize pi1 + psize Hl) _ _ _ _ _ pi1 Hl _ Hat); try lia.
    Unshelve. all: auto.
  - clear IHsize0.
    remember (A :: l0) as l.
    rewrite <- (app_nil_l l2) ; rewrite <- (app_nil_l (A :: l0)) in Heql0.
    remember nil as l3 ; clear Heql3.
    revert l3 l0 Heql0 ; induction pi1 ; intros l4 l5 Heq ; subst.
    + destruct l4 ; inversion Heq ; subst.
      * simpl in Heql; list_simpl ; rewrite <- Heql ; apply (gax_r _ a).
      * destruct l4 ; inversion H1 ; subst.
        -- simpl in Heql; list_simpl ; rewrite <- Heql ; apply (gax_r _ a).
        -- destruct l4 ; inversion H2.
    + apply PCperm_Type_vs_elt_inv in p.
      destruct p as [[l4' l5'] Heq p] ; simpl in Heq ; simpl in p ; subst.
      assert (PEperm_Type (pperm P) (l1 ++ l5' ++ l4' ++ l2) (l1 ++ l5 ++ l4 ++ l2)) as HP'.
      { apply PEperm_Type_app_head.
        rewrite 2 app_assoc ; apply PEperm_Type_app_tail.
        symmetry; assumption. }
      apply PEperm_PCperm_Type in HP'.
      apply (ex_r _ (l1 ++ l5' ++ l4' ++ l2))...
      apply IHpi1; try reflexivity.
      apply PEperm_PCperm_Type.
      symmetry.
      apply PEperm_Type_app_head.
      rewrite 2 (app_assoc _ _ l2).
      apply PEperm_Type_app_tail; assumption.
    + symmetry in Heq ; trichot_Type_elt_app_exec Heq ; subst.
      * list_simpl ; rewrite app_assoc.
        eapply ex_wn_r; try eassumption.
        list_simpl.
        rewrite (app_assoc l) ; rewrite (app_assoc _ l3) ; rewrite <- (app_assoc l).
        apply IHpi1 ; list_simpl; reflexivity.
      * destruct Heq1 as [Heq1 Heq2] ; decomp_map_Type Heq1.
        exfalso ; destruct A ; inversion Heq1 ; subst ; destruct Hat as [[? Heq] | [? Heq]]; discriminate Heq.
      * list_simpl ; rewrite 2 app_assoc.
        eapply ex_wn_r; try eassumption.
        list_simpl ; rewrite (app_assoc l0) ; rewrite (app_assoc _ l6).
        apply IHpi1 ; list_simpl; reflexivity.
    + destruct l4 ; inversion Heq.
    + dichot_Type_elt_app_exec Heq ; subst.
      * list_simpl.
        eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
        apply mix2_r; auto.
        eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
        apply IHpi1_2 ; list_simpl; reflexivity.
      * eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
        apply mix2_r; auto.
        eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
        apply IHpi1_1 ; list_simpl; reflexivity.
    + exfalso ; destruct l4 ; inversion Heq.
      * destruct A ; inversion H0 ; subst ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'.
      * destruct l4 ; inversion H1.
    + destruct l4 ; inversion Heq ; subst ;
        try (exfalso ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'; fail).
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply bot_r.
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply IHpi1 ; list_simpl; reflexivity.
    + destruct l4 ; inversion Heq ; subst ;
        try (exfalso ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'; fail).
      dichot_Type_elt_app_exec H1 ; subst.
      * list_simpl.
        eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
        rewrite app_comm_cons ; eapply ex_r ; [ | symmetry ; apply PCperm_Type_app_rot ] ; list_simpl.
        rewrite 3 app_assoc ; apply tens_r; try assumption.
        list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
        rewrite app_comm_cons ; apply IHpi1_2 ; list_simpl; reflexivity.
      * eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
        apply tens_r; try assumption.
        list_simpl ; rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
        rewrite app_comm_cons ; apply IHpi1_1 ; list_simpl; reflexivity.
    + destruct l4 ; inversion Heq ; subst ;
        try (exfalso ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'; fail).
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply parr_r.
      rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      rewrite 2 app_comm_cons ; apply IHpi1 ; list_simpl; reflexivity.
    + destruct l4 ; inversion Heq ; subst ;
        try (exfalso ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'; fail).
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply top_r...
    + destruct l4 ; inversion Heq ; subst ;
        try (exfalso ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'; fail).
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply plus_r1...
      rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; apply IHpi1 ; list_simpl; reflexivity.
    + destruct l4 ; inversion Heq ; subst ;
        try (exfalso ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'; fail).
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply plus_r2.
      rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; apply IHpi1 ; list_simpl; reflexivity.
    + destruct l4 ; inversion Heq ; subst ;
        try (exfalso ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'; fail).
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply with_r.
      * rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
        rewrite app_comm_cons ; apply IHpi1_1 ; list_simpl; reflexivity.
      * rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
        rewrite app_comm_cons ; apply IHpi1_2 ; list_simpl; reflexivity.
    + destruct l4 ; inversion Heq ; subst ;
        try (exfalso ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'; fail).
      exfalso ; symmetry in H1 ; decomp_map_Type H1 ; destruct A ; inversion H1 ; subst ;
        destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'.
    + destruct l4 ; inversion Heq ; subst ;
        try (exfalso ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'; fail).
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply de_r.
      rewrite app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      rewrite app_comm_cons ; apply IHpi1 ; list_simpl; reflexivity.
    + destruct l4 ; inversion Heq ; subst ;
        try (exfalso ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'; fail).
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply wk_r.
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply IHpi1 ; list_simpl; reflexivity.
    + destruct l4 ; inversion Heq ; subst ;
        try (exfalso ; destruct Hat as [[? Heq'] | [? Heq']]; discriminate Heq'; fail).
      eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      apply co_r.
      rewrite 2 app_comm_cons ; eapply ex_r ; [ | apply PCperm_Type_app_rot ] ; list_simpl.
      rewrite 2 app_comm_cons ; apply IHpi1 ; list_simpl; reflexivity.
    + dichot_Type_elt_app_exec Heq; subst.
      * apply (ex_r _ (l0 ++ l4 ++ l2 ++ l1 ++ l)).
        -- eapply (cut_r _ (dual A0)); try rewrite bidual; auto.
           apply (ex_r _ ((l2 ++ l1) ++ l ++ A0 :: l4)).
           ++ eapply (cut_r _ (dual A)); try rewrite bidual.
              ** eapply ex_r; [ apply pi1_2 | ].
                 rewrite 2 app_comm_cons; apply PCperm_Type_app_comm.
              ** eapply ex_r; [ apply (gax_r _ a) | ].
                 rewrite Heql.
                 rewrite app_comm_cons; apply PCperm_Type_app_comm.
           ++ rewrite app_comm_cons.
              etransitivity; [ | apply PCperm_Type_app_comm ]; list_simpl; reflexivity.
        -- rewrite 2 app_assoc.
           etransitivity; [ apply PCperm_Type_app_comm | ]; list_simpl; reflexivity.
      * apply (ex_r _ (l3 ++ l6 ++ l2 ++ l1 ++ l5)).
        -- eapply (cut_r _ A0); auto.
           apply (ex_r _ ((l2 ++ l1) ++ l5 ++ dual A0 :: l6)).
           ++ eapply (cut_r _ (dual A)); try rewrite bidual.
              ** eapply ex_r; [ apply pi1_1 | ].
                 rewrite 2 app_comm_cons; apply PCperm_Type_app_comm.
              ** eapply ex_r; [ apply (gax_r _ a) | ].
                 rewrite Heql.
                 rewrite app_comm_cons; apply PCperm_Type_app_comm.
           ++ rewrite app_comm_cons.
              etransitivity; [ | apply PCperm_Type_app_comm ]; list_simpl; reflexivity.
        -- rewrite 2 app_assoc.
           etransitivity; [ apply PCperm_Type_app_comm | ]; list_simpl; reflexivity.
      Unshelve. all: auto.
    + destruct (P_gax_cut _ _ _ _ _ _ _ Heql Heq) as [x Hcut].
      apply (ex_r _ (l4 ++ l2 ++ l1 ++ l5)).
      * rewrite <- Hcut ; apply (gax_r _ x).
      * rewrite app_assoc.
        rewrite (app_assoc _ _ (l4 ++ _)).
        apply PCperm_Type_app_comm.
  Qed.

End CutElim_At.

Global Instance CPS_ctx P : CPhaseSpace (pperm P) (pmix0 P) (pmix2 P).
Proof.
split with (list formula) (@app formula) (@nil formula) (ll P)
           (fun Γ => { Δ | Γ = map wn Δ }) (ex_app P).
- apply monoid_associative_pole_l; intros; list_simpl; reflexivity.
- apply monoid_associative_pole_r; intros; list_simpl; reflexivity.
- apply monoid_associative_pole_ll; intros; list_simpl; reflexivity.
- apply monoid_associative_pole_lr; intros; list_simpl; reflexivity.
- apply monoid_neutral_pole_1; intros; list_simpl; reflexivity.
- apply monoid_neutral_pole_2; intros; list_simpl; reflexivity.
- apply monoid_neutral_pole_l_1; intros; list_simpl; reflexivity.
- apply monoid_neutral_pole_l_2; intros; list_simpl; reflexivity.
- apply monoid_neutral_pole_r_1; intros; list_simpl; reflexivity.
- apply monoid_neutral_pole_r_2; intros; list_simpl; reflexivity.
- simpl; red; red; intros y Hy; red in Hy; simpl.
  specialize Hy with nil; red in Hy.
  rewrite app_nil_r in Hy; apply Hy.
  exists nil; reflexivity.
- red; intros x Hx; inversion Hx.
  inversion H; inversion H0; subst.
  exists (x1 ++ x2); list_simpl; reflexivity.
- intros x Hx; inversion Hx; subst; split.
  + intros y Hy; red; red in Hy; red in Hy.
    apply wk_list_r.
    specialize Hy with nil; rewrite app_nil_r in Hy.
    apply Hy; reflexivity.
  + intros y Hy; red; red in Hy; red in Hy.
    apply co_list_r.
    specialize Hy with (map wn x0 ++ map wn x0).
    eapply ex_r; [ apply Hy | ].
    * constructor; reflexivity.
    * rewrite (app_assoc _ _ y).
      apply PCperm_Type_app_comm.
- intros HP x y z H; red; red in H.
  eapply ex_r; [ apply H | ].
  rewrite HP; simpl.
  apply Permutation_Type_app_tail.
  apply Permutation_Type_app_comm.
- apply mix0_r.
- intros Hmix2 l H; inversion H.
  apply mix2_r; assumption.
Defined.

Section Okada.

  Context { P : pfrag }.

  Hypothesis P_gax_at : gax_at P.
  Hypothesis P_gax_cut : gax_cut P.

  Notation "↓" := (fun A Γ => ll P (A::Γ)).

  Notation LLval := (fun x => ↓(var x)).

  Instance CPSLL : CPhaseSpace (pperm P) (pmix0 P) (pmix2 P) := CPS_ctx P.

  Infix "∘" := (MComposes CPSCompose) (at level 50, no associativity).
  Notation dual := (ldual (R CPSCompose CPSPole)).
  Notation "'⟦' A '⟧'" := (@Form_sem (pperm P) (pmix0 P) (pmix2 P) _ LLval A) (at level 49).
  Notation "⟬߭  ll ⟭" := (@list_Form_presem (pperm P) (pmix0 P) (pmix2 P) _ LLval ll) (at level 49).

  Hint Resolve (@CPSfact_pole _ _ _ CPSLL) (@CPScommute _ _ _ CPSLL)
               CPSassociative_l CPSassociative_r
               CPSneutral_1 CPSneutral_2
               CPSneutral_l_1 CPSneutral_l_2 CPSneutral_r_1 CPSneutral_r_2.

  Fact LLgax : forall a, ⟬߭  projT2 (pgax P) a ⟭ ⊆ CPSPole.
  Proof.
  intros a; red in P_gax_at; specialize P_gax_at with a.
  assert (pi := gax_r _ a).
  remember (projT2 (pgax P) a) as l; clear Heql a.
  enough (forall l, Forall atomic l -> forall l0, ll P (l0 ++ l) -> sg l0 ∘ ⟬߭ l ⟭  ⊆ CPSPole) as IH.
  { specialize IH with l nil.
    etransitivity; [ | apply CPSfact_pole ].
    apply subset_cl.
    etransitivity; [ apply (@neutral_l_1_g _ _ CPSUnit _ CPScommute) | ]; auto.
    apply cl_subset.
    etransitivity; [ apply stability_r | ]; auto.
    apply cl_subset.
    etransitivity; [ | apply cl_increase ].
    etransitivity; [ | apply IH ]; auto.
    apply MComposes_monotone; try reflexivity. }
  clear pi P_gax_at.
  induction l0; intros HF l1 pi; intros x Hx; inversion Hx; rewrite_all <- H.
  - inversion X.
    apply pi.
  - inversion X; simpl.
    eapply ex_r; [ | apply PCperm_Type_app_comm ]; rewrite <- app_assoc.
    apply X0.
    destruct a; try (exfalso; inversion HF; inversion H4; fail); subst; simpl.
    + change (var a :: y0 ++ x0) with ((var a :: nil) ++ y0 ++ x0).
      rewrite app_assoc; eapply ex_r; [ | apply PCperm_Type_app_comm ]; rewrite app_assoc.
      specialize IHl0 with (x0 ++ var a :: nil).
      apply IHl0.
      * clear - HF; inversion HF; assumption.
      * list_simpl; assumption.
      * constructor; auto.
    + intros y Hy; red.
      rewrite <- app_assoc.
      eapply ex_r; [ | apply PCperm_Type_app_comm ].
      specialize IHl0 with (x0 ++ y).
      apply IHl0.
      * clear - HF; inversion HF; assumption.
      * eapply ex_r; [ | apply PCperm_Type_app_comm ].
        rewrite <- (app_nil_l _).
        rewrite <- (app_nil_l _) in Hy.
        eapply cut_at; eassumption.
      * constructor; auto.
  Qed.

  Instance PMLL : CPhaseModel P.
  Proof. split with CPSLL LLval.
  intros X l H; simpl in H; red in H; red in H.
  eapply ex_r ; [ apply (H (var X :: nil)) | ].
  - intros l' pi; assumption.
  - etransitivity; [ apply PCperm_Type_app_comm | ]; reflexivity.
  - apply LLgax.
  Defined.


  Lemma Okada A : ⟦A⟧ ⊆ ↓A.
  Proof.
  induction A; intros l H; simpl in H; auto; try (red in H; red in H).
  - specialize H with (covar a :: nil).
    change (covar a :: l) with ((covar a :: nil) ++ l).
    eapply ex_r; [ apply H | apply PCperm_Type_app_comm ].
    eapply ex_r; [ apply ax_r | apply PCperm_Type_swap ].
  - specialize H with (one :: nil).
    change (one :: l) with ((one :: nil) ++ l).
    eapply ex_r; [ apply H | apply PCperm_Type_app_comm ].
    intros x Hx; inversion Hx.
    apply one_r.
  - apply bot_r; assumption.
  - specialize H with (tens A1 A2 :: nil).
    change (tens A1 A2 :: l) with ((tens A1 A2 :: nil) ++ l).
    eapply ex_r; [ apply H | apply PCperm_Type_app_comm ].
    intros x Hx; inversion Hx.
    red; list_simpl; apply tens_r; auto.
  - apply parr_r.
    specialize H with ((A1 :: nil) ++ A2 :: nil).
    change (A1 :: A2 :: l) with (((A1 :: nil) ++ A2 :: nil) ++ l).
    eapply ex_r; [ apply H | apply PCperm_Type_app_comm ].
    constructor; auto.
  - specialize H with (zero :: nil).
    change (zero :: l) with ((zero :: nil) ++ l).
    eapply ex_r; [ apply H | apply PCperm_Type_app_comm ].
    intros x Hx; inversion Hx.
  - apply top_r.
  - specialize H with (aplus A1 A2 :: nil).
    change (aplus A1 A2 :: l) with ((aplus A1 A2 :: nil) ++ l).
    eapply ex_r; [ apply H | apply PCperm_Type_app_comm ].
    intros x Hx; inversion Hx.
    + red; apply plus_r1; auto.
    + red; apply plus_r2; auto.
  - apply with_r; [ apply IHA1 | apply IHA2 ]; apply H.
  - specialize H with (oc A :: nil).
    change (oc A :: l) with ((oc A :: nil) ++ l).
    eapply ex_r; [ apply H | apply PCperm_Type_app_comm ].
    intros x Hx; inversion Hx.
    inversion H0; subst.
    apply oc_r; auto.
  - specialize H with (wn A :: nil).
    change (wn A :: l) with ((wn A :: nil) ++ l).
    eapply ex_r; [ apply H | apply PCperm_Type_app_comm ].
    split.
    + exists (A :: nil); reflexivity.
    + intros x Hx; red; apply de_r; auto.
  Qed.

  Lemma Okada_ctx l : ⟬߭  l ⟭ l.
  Proof.
  induction l.
  - rewrite list_Form_presem_nil; reflexivity.
  - rewrite list_Form_presem_cons.
    change (a :: l) with ((a :: nil) ++ l).
    constructor; auto.
    apply Okada.
  Qed.

End Okada.

Section Cut_Elim.

  Context { P : pfrag }.
  Hypothesis P_gax_at : gax_at P.
  Hypothesis P_gax_cut : gax_cut P.

  Notation "↓" := (fun A Γ => ll (cutupd_pfrag P false) (A::Γ)).
  Notation LLval_cf := (fun x => ↓(var x)).

  Instance CPSLL_cf : CPhaseSpace (pperm P) (pmix0 P) (pmix2 P) := CPS_ctx (cutupd_pfrag P false).

  Instance PMLL_cf : CPhaseModel P.
  Proof. split with CPSLL_cf LLval_cf.
  intros X l H; simpl in H; red in H; red in H.
  eapply ex_r ; [ apply (H (var X :: nil)) | ].
  - intros l' pi; assumption.
  - etransitivity; [ apply PCperm_Type_app_comm | ]; reflexivity.
  - apply (@LLgax (cutupd_pfrag P false) P_gax_at P_gax_cut).
  Defined.

  Theorem ll_cut_elimination Γ : ll P Γ -> ll (cutupd_pfrag P false) Γ.
  Proof.
    intros pi.
    apply (ll_soundness PMLL_cf) in pi; auto.
    simpl in pi; apply pi.
    apply (@Okada_ctx (cutupd_pfrag P false)).
  Qed.

End Cut_Elim.

