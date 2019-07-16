Require Import List_more Permutation_Type genperm_Type.

Require Import cphase_sem.

Require Import ll_def.

Lemma ex_app P : forall l1 l2, ll P (l1 ++ l2) -> ll P (l2 ++ l1).
Proof. intros l1 l2 pi; eapply ex_r ; [ apply pi | apply PCperm_Type_app_comm ]. Qed.

Instance CPS_ctx P : CPhaseSpace (pperm P) (pmix0 P) (pmix2 P).
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

