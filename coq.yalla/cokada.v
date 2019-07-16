Require Import List_more Permutation_Type genperm_Type.

Require Import closure_operators cphase_sem.

Require Import ll_def.

Notation "X '⊆' Y" := (subset X Y) (at level 75, format "X  ⊆  Y", no associativity).
Notation "X '≃' Y" := (eqset X Y) (at level 75, format "X  ≃  Y", no associativity).
Notation "A '∩' B" := (fun z => A z * B z : Type)%type (at level 50, format "A  ∩  B", left associativity).
Notation "A '∪' B" := (fun z => A z + B z : Type)%type (at level 50, format "A  ∪  B", left associativity).

Lemma ex_app P : forall l1 l2, ll P (l1 ++ l2) -> ll P (l2 ++ l1).
Proof. intros l1 l2 pi; eapply ex_r ; [ apply pi | apply PCperm_Type_app_comm ]. Qed.

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
  Hypothesis Pgax : projT1 (pgax P) -> False.

  Notation "↓" := (fun A Γ => ll P (A::Γ)).

  Notation LLval := (fun x => ↓(var x)).

  Instance CPSLL : CPhaseSpace (pperm P) (pmix0 P) (pmix2 P) := CPS_ctx P.

  Instance PMLL : CPhaseModel P.
  Proof. split with CPSLL LLval.
  intros X l H; simpl in H; red in H; red in H.
  eapply ex_r ; [ apply (H (var X :: nil)) | ].
  - intros l' pi; assumption.
  - etransitivity; [ apply PCperm_Type_app_comm | ]; reflexivity.
  Defined.

  Notation dual := (ldual (R CPSCompose CPSPole)).
  Notation "'⟦' A '⟧'" := (@Form_sem (pperm P) (pmix0 P) (pmix2 P) _ LLval A) (at level 49).
  Notation "⟬߭  ll ⟭" := (@list_Form_presem (pperm P) (pmix0 P) (pmix2 P) _ LLval ll) (at level 49).

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
  Hypothesis Pgax : projT1 (pgax P) -> False.

  Notation "↓" := (fun A Γ => ll (cutupd_pfrag P false) (A::Γ)).
  Notation LLval_cf := (fun x => ↓(var x)).

  Instance CPSLL_cf : CPhaseSpace (pperm P) (pmix0 P) (pmix2 P) := CPS_ctx (cutupd_pfrag P false).

  Instance PMLL_cf : CPhaseModel P.
  Proof. split with CPSLL_cf LLval_cf.
  intros X l H; simpl in H; red in H; red in H.
  eapply ex_r ; [ apply (H (var X :: nil)) | ].
  - intros l' pi; assumption.
  - etransitivity; [ apply PCperm_Type_app_comm | ]; reflexivity.
  Defined.

  Theorem ll_cut_elimination Γ : ll P Γ -> ll (cutupd_pfrag P false) Γ.
  Proof.
    intros pi.
    apply (ll_soundness PMLL_cf) in pi; auto.
    simpl in pi; apply pi.
    apply (@Okada_ctx (cutupd_pfrag P false)).
  Qed.

End Cut_Elim.

