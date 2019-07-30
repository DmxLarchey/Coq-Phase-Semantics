Require Import Lia.
Require Import List_more List_Type_more genperm_Type Wf_nat_more.

Require Export ll_def.

Theorem cut_at {P} :
  (forall a b x l1 l2 l3 l4,
    projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
    { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }) ->
forall X l1 l2 l3 l4,
    ll P (l1 ++ var X :: l2) -> ll P (l3 ++ covar X :: l4) -> ll P (l1 ++ l4 ++ l3 ++ l2).
Proof.
  intros P_gax_cut.
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

