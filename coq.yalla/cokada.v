Require Import List_more List_Type Permutation_Type genperm_Type.

Require Import closure_operators cphase_sem.

Require Import ll_cut_at.

Notation "X '⊆' Y" := (subset X Y) (at level 75, format "X  ⊆  Y", no associativity).

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
- intros n Hmix l H.
  assert ({ L : _ & length L = n & prod (l = concat L)
                                        (Forall_Type (ll P) L)}) as [L Hlen [Heq HF]]; subst.
  { clear Hmix; revert l H; induction n; simpl; intros l H.
    - subst.
      exists nil; try split; try reflexivity.
      constructor.
    - inversion H; subst.
      destruct (IHn _ X0) as [L1 Hlen [Heq HF]]; subst.
      exists (x :: L1); try split; try reflexivity.
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

  Infix "∘" := (MComposes CPSCompose) (at level 50, no associativity).
  Notation dual := (ldual (R CPSCompose CPSPole)).
  Notation "'⟦' A '⟧'" := (@Form_sem (pperm P) (pmix P) _ LLval A) (at level 49).
  Notation "⟬߭  ll ⟭" := (@list_Form_presem (pperm P) (pmix P) _ LLval ll) (at level 49).

  Hint Resolve (@CPSfact_pole _ _ CPSLL) (@CPScommute _ _ CPSLL)
               CPSassociative_l CPSassociative_r
               CPSneutral_1 CPSneutral_2
               CPSneutral_l_1 CPSneutral_l_2 CPSneutral_r_1 CPSneutral_r_2.

  Fact LLgax : forall a, ⟬߭  projT2 (pgax P) a ⟭ ⊆ CPSPole.
  Proof.
  intros a; red in P_gax_at; specialize P_gax_at with a.
  assert (pi := gax_r _ a).
  remember (projT2 (pgax P) a) as l; clear Heql a.
  enough (forall l, Forall_Type atomic l -> forall l0, ll P (l0 ++ l) -> sg l0 ∘ ⟬߭ l ⟭  ⊆ CPSPole) as IH.
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

  Instance CPSLL_cf : CPhaseSpace (pperm P) (pmix P) := CPS_ctx (cutupd_pfrag P false).

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

