(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Utf8_core.

Require Import List_more Permutation_Type genperm_Type.

Require Import utils_tac orthogonality phase_sem.

Require Import iformulas.

Set Implicit Arguments.

  Notation "X ≡ Y" := ((X->Y)*(Y->X))%type (at level 80, format "X  ≡  Y", no associativity).
  Infix "⊆" := subset (at level 75, no associativity).
  Notation "A ∩ B" := (fun z => A z * B z : Type)%type (at level 50, format "A  ∩  B", left associativity).
  Notation "A ∪ B" := (fun z => A z + B z : Type)%type (at level 50, format "A  ∪  B", left associativity).
  Notation sg := (@eq _).


Section Rules.

  Variable prov_pred : list iformula -> iformula -> Type.
  Variable perm_bool : bool.

  Notation "Γ ⊨ A" := (prov_pred Γ A) (at level 70, no associativity).
  Notation " x '~~' y " := (PEperm_Type perm_bool x y) (at level 70).
  Hint Resolve PEperm_Type_refl Permutation_Type_app_comm.

  Hypothesis P_perm : forall Γ Δ A, Γ ~~ Δ -> Γ ⊨ A -> Δ ⊨ A.



  Implicit Types (X Y : list iformula -> Type).

  Notation ctx_compose := (@app iformula).
  Notation ctx_unit := (@nil iformula).
  Notation adj_l := (fun ϴ H => match H with (Γ,Δ,A) => (Γ, ϴ ++ Δ, A) end).
  Notation adj_r := (fun ϴ H => match H with (Γ,Δ,A) => (Γ ++ ϴ, Δ, A) end).

  Notation ctx_hole := (list iformula * list iformula * iformula)%type.
  Infix "∘" := (composes ctx_compose) (at level 50, no associativity).

  Definition ctx_orth : list iformula -> ctx_hole -> Type :=
    fun ϴ H => match H with (Γ,Δ,A) => Γ ++ ϴ ++ Δ ⊨ A end.

  Instance CL_ctx : ClosureOp := (@lclosure _ _ ctx_orth).
  Notation cl_ctx := (@cl _ _ CL_ctx).

  Lemma rel_associative_l_l : rel_associativity_l_l ctx_orth ctx_compose adj_l.
  Proof.
  intros X Y [[X1 Y1] A]; unfold ctx_orth; intros H.
  rewrite <- app_assoc; auto.
  Qed.

  Lemma rel_associative_l_r : rel_associativity_l_r ctx_orth ctx_compose adj_l.
  Proof.
  intros X Y [[X1 Y1] A]; unfold ctx_orth; intros H.
  rewrite <- app_assoc in H; auto.
  Qed.

  Lemma rel_associative_r_l : rel_associativity_r_l ctx_orth ctx_compose adj_r.
  Proof.
  intros X Y [[X1 Y1] A]; unfold ctx_orth; intros H.
  rewrite <- app_assoc; rewrite <- app_assoc in H; auto.
  Qed.

  Lemma rel_associative_r_r : rel_associativity_r_r ctx_orth ctx_compose adj_r.
  Proof.
  intros X Y [[X1 Y1] A]; unfold ctx_orth; intros H.
  rewrite <- app_assoc; rewrite <- app_assoc in H; auto.
  Qed.

  Fact cl_comm : perm_bool = true -> @cl_commutativity _ _ CL_ctx (composes ctx_compose).
  Proof.
  intros Hb Γ Δ ga H.
  inversion H; subst.
  unfold cl_ctx; simpl; unfold ldual, rdual, ctx_orth.
  intros [[ga de] A] H1.
  specialize H1 with (b ++ a).
  eapply P_perm; [ | apply H1; constructor; assumption ].
  apply Permutation_Type_app_head.
  apply Permutation_Type_app_tail.
  apply Permutation_Type_app_swap.
  Qed.

  Notation J := (fun Γ => cl_ctx (sg ∅) Γ * cl_ctx (sg Γ ∘ sg Γ) Γ)%type.
  Notation K := (fun Γ => { Δ | Γ = ‼Δ }).

  Local Fact sub_monoid_1 : cl_ctx K ∅.
  Proof. intros [[ga de] A] H; change de with (nil ++ de); apply H; exists ∅; auto. Qed.

  Local Fact sub_monoid_2 : K ∘ K ⊆ K.
  Proof.
  intros ga H.
  inversion H.
  destruct H0 as [de1 Heq1]; subst.
  destruct H1 as [de2 Heq2]; subst.
  exists (de1 ++ de2).
  unfold ill_lbang.
  rewrite map_app; reflexivity.
  Qed.

    Hypothesis P_weak : ∀ ϴ Γ Δ A, ϴ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A.
    Hypothesis P_cntr : ∀ ϴ Γ Δ A, ϴ++‼Γ++‼Γ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A.

  Local Fact sub_J_1 : K ⊆ J.
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

  Instance PS_ctx : PhaseSpace perm_bool :=
  { Web := list iformula;
    PSCL := CL_ctx;
    PScompose := (@app iformula);
    PSunit := nil;
    PSExp := K;
    PScl_stable_l := stable_l rel_associative_l_l rel_associative_l_r;
    PScl_stable_r := stable_r rel_associative_r_l rel_associative_r_r;
    PScl_associative_l := associative_l (m_rel_associativity_ll _ (@app_assoc _));
    PScl_associative_r := associative_r (m_rel_associativity_lr _ (@app_assoc _));
    PScl_neutral_l_1 := neutral_l_1 (m_rel_neutrality_l_1 _ (@app_nil_l _));
    PScl_neutral_l_2 := neutral_l_2 (m_rel_neutrality_l_2 _ (@app_nil_l _));
    PScl_neutral_r_1 := neutral_r_1 (m_rel_neutrality_r_1 _ (@app_nil_r _));
    PScl_neutral_r_2 := neutral_r_2 (m_rel_neutrality_r_2 _ (@app_nil_r _));
    PSsub_monoid_1 := sub_monoid_1;
    PSsub_monoid_2 := sub_monoid_2;
    PSsub_J := sub_J_1;
    PScl_commute := cl_comm
  }.


  Notation "↓" := (fun A Γ => Γ ⊨ A).

  Fact dc_closed A : cl (↓A) ⊆ ↓A.
  Proof.
  intros ga Hga; red in Hga.
  simpl in Hga; unfold ldual, rdual, ctx_orth in Hga.
  replace ga with (nil++ga++nil) by (list_simpl; reflexivity).
  specialize Hga with (nil,nil,A).
  apply Hga.
  intro; rewrite <- app_nil_end; auto.
  Qed.

  Infix "⊸" := (magicwand_l ctx_compose) (at level 51, right associativity).
  Infix "⟜" := (magicwand_r ctx_compose) (at level 53, left associativity).


End Rules.

