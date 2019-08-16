Require Import List_more List_Type Permutation_Type genperm_Type.

Require Import closure_operators cphase_sem.

Require Import ll_cut_at.

Infix "⊆" := subset (at level 75, no associativity).

Definition gax_at P := forall a, Forall_Type atomic (projT2 (pgax P) a).
Definition gax_cut P := forall a b x l1 l2 l3 l4,
  projT2 (pgax P) a = (l1 ++ dual x :: l2) -> projT2 (pgax P) b = (l3 ++ x :: l4) ->
  { c | projT2 (pgax P) c = l3 ++ l2 ++ l1 ++ l4 }.

Lemma ex_app P : forall l1 l2, ll P (l1 ++ l2) -> ll P (l2 ++ l1).
Proof. intros l1 l2 pi; eapply ex_r ; [ apply pi | apply PCperm_Type_app_comm ]. Defined.


Global Instance CPS_ctx P : CPhaseSpace (pperm P) (pmix P).
Proof.
split with (list formula) (@app formula) (@nil formula) (ll P)
           (fun Γ => { Δ | Γ = map wn Δ }) (ex_app P).
- apply m_pl_neutrality_1; intros l; list_simpl; reflexivity.
- apply m_pl_neutrality_2; intros l; list_simpl; reflexivity.
- apply m_pl_rel_associativity_ll; intros l1 l2 l3; list_simpl; reflexivity.
- apply m_pl_rel_associativity_lr; intros l1 l2 l3; list_simpl; reflexivity.
- simpl; red; red; intros y Hy; red in Hy; simpl.
  specialize Hy with nil; red in Hy.
  rewrite app_nil_r in Hy; apply Hy.
  exists nil; reflexivity.
- red; intros x Hx; inversion Hx.
  inversion H; inversion H0; subst.
  exists (x0 ++ x1); list_simpl; reflexivity.
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
- intros n Hmix l H.
  assert ({ L : _ & length L = n & prod (l = concat L)
                                        (Forall_Type (ll P) L)}) as [L Hlen [Heq HF]]; subst.
  { clear Hmix; revert l H; induction n; simpl; intros l H.
    - subst.
      exists nil; try split; try reflexivity.
      constructor.
    - inversion H; subst.
      destruct (IHn _ X0) as [L1 Hlen [Heq HF]]; subst.
      exists (a :: L1); try split; try reflexivity.
      constructor; assumption. }
  apply mix_r ; [ apply Hmix | assumption ].
Defined.

Section Okada.

  Context { P : pfrag }.
  Hypothesis P_gax_at : gax_at P.
  Hypothesis P_gax_cut : gax_cut P.

  Notation "↓" := (fun A Γ => ll P (A::Γ)).
  Notation LLval := (fun x => ↓(var x)).

  Instance CPSLL : CPhaseSpace (pperm P) (pmix P) := CPS_ctx P.

  Infix "∘" := (composes CPScompose) (at level 50, no associativity).
  Notation dual := (ldual (R CPScompose CPSPole)).
  Notation "⟦ A ⟧" := (@form_presem (pperm P) (pmix P) _ LLval A) (at level 49).
  Notation "⟬߭  l ⟭" := (@list_form_presem (pperm P) (pmix P) _ LLval l) (at level 49).

  Hint Resolve (@CPSpole_closed _ _ CPSLL) (@CPScommute _ _ CPSLL)
               CPSassociative_l CPSassociative_r
               CPSneutral_1 CPSneutral_2
               (@mstable_l _ _ _ _ CPScommute CPSassociative_l CPSassociative_r CPSneutral_1 CPSneutral_2)
               (@mstable_r _ _ _ _ CPScommute CPSassociative_l CPSassociative_r CPSneutral_1 CPSneutral_2)
               (@mneutral_l_1 _ _ _ _ CPScommute CPSassociative_l CPSneutral_1 CPSneutral_2)
               (@mneutral_l_2 _ _ _ _ CPScommute CPSassociative_r CPSneutral_1 CPSneutral_2)
               (@mneutral_r_1 _ _ _ _ CPScommute CPSassociative_r CPSneutral_1 CPSneutral_2)
               (@mneutral_r_2 _ _ _ _ CPScommute CPSassociative_l CPSneutral_1 CPSneutral_2).

  Fact LLgax : forall a, ⟬߭  projT2 (pgax P) a ⟭ ⊆ CPSPole.
  Proof.
  intros a; red in P_gax_at; specialize P_gax_at with a.
  assert (pi := gax_r _ a).
  remember (projT2 (pgax P) a) as l; clear Heql a.
  enough (forall l, Forall_Type atomic l -> forall l0, ll P (l0 ++ l) -> sg l0 ∘ ⟬߭ l ⟭  ⊆ CPSPole) as IH.
  { specialize IH with l nil.
    etransitivity; [ | apply CPSpole_closed ].
    apply subset_bidual.
    etransitivity; [ apply mneutral_l_1 | ]; auto.
    apply bidual_subset.
    etransitivity; [ eapply mstable_r | ]; auto.
    apply bidual_subset.
    etransitivity; [ apply IH | apply bidual_increase ]; auto. }
  clear pi P_gax_at.
  induction l0; intros HF l1 pi; intros x Hx; inversion Hx; rewrite_all <- H.
  - inversion X.
    apply pi.
  - rewrite list_form_presem_cons in X.
    inversion X; simpl.
    rewrite app_assoc.
    inversion HF; subst.
    apply (IHl0 H5 (a0 ++ a1)); [ | constructor; try reflexivity; auto ]; list_simpl.
    destruct a; try (exfalso; inversion HF; inversion H4; fail); subst; simpl; simpl in X0.
    + change a1 with (nil ++ a1); rewrite <- app_assoc.
      apply (cut_at P_gax_cut _ _ _ _ _ pi).
      assert (dual (dual (sg (var a :: nil))) ⊆ dual (sg (covar a :: nil))) as H
        by (apply lmonot; intros z Hz y Hy; subst; apply ax_r).
      apply H; auto.
      revert X0; apply lmonot.
      intros z Hz; unfold dual in Hz; specialize Hz with (var a :: nil).
      change (var a :: z) with ((var a :: nil) ++ z); apply ex_app.
      apply Hz; reflexivity.
    + apply ex_app; list_simpl.
      rewrite <- (app_nil_r a0).
      apply (cut_at P_gax_cut a); [ | apply pi ].
      apply ex_app; auto.
  Unshelve. all:auto.
  Qed.

  Instance PMLL : CPhaseModel P.
  Proof. split with CPSLL LLval; apply LLgax. Defined.

  Lemma Okada A : ⟦A⟧ ⊆ ↓A.
  Proof.
  induction A; intros l H; simpl in H; auto; try (red in H; red in H).
  - specialize H with (covar a :: nil).
    change (covar a :: l) with ((covar a :: nil) ++ l).
    apply ex_app; apply H.
    eapply ex_r; [ apply ax_r | apply PCperm_Type_swap ].
  - specialize H with (one :: nil).
    change (one :: l) with ((one :: nil) ++ l).
    apply ex_app; apply H.
    intros x Hx; inversion Hx.
    apply one_r.
  - apply bot_r; assumption.
  - specialize H with (tens A1 A2 :: nil).
    change (tens A1 A2 :: l) with ((tens A1 A2 :: nil) ++ l).
    apply ex_app; apply H.
    intros x Hx; inversion Hx.
    red; list_simpl; apply tens_r; auto.
  - apply parr_r.
    specialize H with ((A1 :: nil) ++ A2 :: nil).
    change (A1 :: A2 :: l) with (((A1 :: nil) ++ A2 :: nil) ++ l).
    apply ex_app; apply H.
    constructor; auto.
  - specialize H with (zero :: nil).
    change (zero :: l) with ((zero :: nil) ++ l).
    apply ex_app; apply H.
    intros x Hx; inversion Hx.
  - apply top_r.
  - specialize H with (aplus A1 A2 :: nil).
    change (aplus A1 A2 :: l) with ((aplus A1 A2 :: nil) ++ l).
    apply ex_app; apply H.
    intros x Hx; inversion Hx; red; [ apply plus_r1 | apply plus_r2 ]; auto.
  - destruct H as [H1 H2] ; apply with_r.
(* TODO simplify? *)
    + apply (@cl_monotone _ _ (CL PMLL)) in IHA1.
      apply IHA1 in H1.
      change (A1 :: l) with ((A1 :: nil) ++ l).
      assert (@cl _ _ (CL PMLL) (dual (sg (A1 :: nil))) l).
      { intros x Hx; apply H1; revert Hx.
        apply lmonot.
        intros z Hz y Heq; subst.
        apply ex_app; assumption. }
      apply dual_is_closed in X.
      unfold dual in X.
      specialize X with (A1 :: nil).
      unfold R in X.
      assert (Y := X eq_refl); unfold CPSPole in Y; simpl in Y.
      apply ex_app; assumption.
    + apply (@cl_monotone _ _ (CL PMLL)) in IHA2.
      apply IHA2 in H2.
      change (A2 :: l) with ((A2 :: nil) ++ l).
      assert (@cl _ _ (CL PMLL) (dual (sg (A2 :: nil))) l).
      { intros x Hx; apply H2; revert Hx.
        apply lmonot.
        intros z Hz y Heq; subst.
        apply ex_app; assumption. }
      apply dual_is_closed in X.
      unfold dual,R in X; specialize X with (A2 :: nil).
      assert (Y := X eq_refl); unfold CPSPole in Y; simpl in Y.
      apply ex_app; assumption.
  - specialize H with (oc A :: nil).
    change (oc A :: l) with ((oc A :: nil) ++ l).
    apply ex_app; apply H.
    intros x Hx; inversion Hx.
    inversion H0; subst.
    apply oc_r; auto.
(* TODO simplify? *)
    apply (@cl_monotone _ _ (CL PMLL)) in IHA.
    apply IHA in X.
    change (A :: ⁇ x0) with ((A :: nil) ++ ⁇ x0).
    assert (@cl _ _ (CL PMLL) (dual (sg (A :: nil))) (⁇ x0)).
    { intros z Hz; apply X; revert Hz.
      apply lmonot.
      intros t Ht y Heq; subst.
      apply ex_app; assumption. }
    apply dual_is_closed in X0.
    unfold dual, R in X0; specialize X0 with (A :: nil).
    assert (Y := X0 eq_refl); unfold CPSPole in Y; simpl in Y.
    apply ex_app; assumption.
  - specialize H with (wn A :: nil).
    change (wn A :: l) with ((wn A :: nil) ++ l).
    apply ex_app; apply H.
    split.
    + exists (A :: nil); reflexivity.
    + intros x Hx; red; apply de_r; auto.
  Qed.

  Lemma Okada_ctx l : dual (dual (⟬߭  l ⟭))  l.
  Proof.
  induction l.
  - apply bidual_increase.
    rewrite list_form_presem_nil; reflexivity.
  - rewrite list_form_presem_cons.
    change (a :: l) with ((a :: nil) ++ l).
    eapply mstable; auto.
    constructor; auto.
    apply form_sem_dual.
    apply Okada.
  Unshelve. all: auto.
  Qed.

End Okada.

Section Cut_Elim.

  Context { P : pfrag }.
  Hypothesis P_gax_at : gax_at P.
  Hypothesis P_gax_cut : gax_cut P.

  Notation "↓" := (fun A Γ => ll (cutupd_pfrag P false) (A::Γ)).
  Notation LLval_cf := (fun x => ↓(var x)).

  Instance CPSLL_cf : CPhaseSpace (pperm P) (pmix P) := CPS_ctx (cutupd_pfrag P false).

  Instance PMLL_cf : CPhaseModel P.
  Proof. split with CPSLL_cf LLval_cf; apply (@LLgax (cutupd_pfrag P false) P_gax_at P_gax_cut). Defined.

  Theorem ll_cut_elimination Γ : ll P Γ -> ll (cutupd_pfrag P false) Γ.
  Proof.
  intros pi.
  apply (ll_soundness PMLL_cf) in pi; auto.
  simpl in pi.
  do 2 eapply lmonot in pi.
  assert (HH := @pole_closed _ _ _ CPSPole CPScommute CPSneutral_1 CPSneutral_2 Γ); apply HH.
  apply pi.
  apply (@Okada_ctx (cutupd_pfrag P false)); assumption.
  Qed.

End Cut_Elim.

