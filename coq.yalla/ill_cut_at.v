Require Import List_more List_Type_more Permutation_Type_more genperm_Type.

Require Export ill_def.

Theorem cut_at {P} :
  (forall a, List_Type.In_Type N (fst (projT2 (ipgax P) a)) -> False) ->
  (forall a b l1 l2, fst (projT2 (ipgax P) b) = l1 ++ snd (projT2 (ipgax P) a) :: l2 -> 
                        { c | l1 ++ fst (projT2 (ipgax P) a) ++ l2 = fst (projT2 (ipgax P) c)
                              /\ snd (projT2 (ipgax P) b) = snd (projT2 (ipgax P) c) }) ->
  forall X l0 l1 l2 A,
    ill P l0 (ivar X) -> ill P (l1 ++ ivar X :: l2) A -> ill P (l1 ++ l0 ++ l2) A.
Proof.
  intros P_gax_noN_l P_gax_cut X l0 l1 l2 Y pi1.
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
    remember (l1' ++ ivar X :: l2') as l0.
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

