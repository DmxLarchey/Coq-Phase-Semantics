(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(*   Adapted by Olivier Laurent [**]                          *)
(*                                                            *)
(*                              [**] Affiliation LIP -- CNRS  *)


Require Import List_more List_Type Permutation_Type genperm_Type.

Require Export closure_operators.

Require Import ill_def.

Import SetNotations.

Notation " x '~[' b ']' y " := (PEperm_Type b x y) (at level 70, format "x  ~[ b ]  y").

Notation "£" := ivar.
Notation "⟙" := (itop).
Notation "0" := (izero).
Notation 𝝐 := (ione).
Infix "﹠" := (iwith) (at level 50).
Infix "⊗" := (itens) (at level 50).
Infix "⊕" := (iplus) (at level 50).
Infix "-o" := (ilmap) (at level 51, right associativity).
Notation "x o- y" := (ilpam y x) (at level 52, left associativity).
Notation "! x" := (ioc x) (at level 53).




Set Implicit Arguments.

Section PhaseSpaces.

  Class MPhaseSpace (b : bool) := {
    Web : Type;
    PScompose : Web -> Web -> Web;
    PSunit : Web;
    PS_associative : m_associativity PScompose;
    PS_neutral_l : m_neutrality_l PScompose PSunit;
    PS_neutral_r : m_neutrality_r PScompose PSunit;
    PSCL : @ClosureOp _ (@subset Web);
    PScl_stable_l : @cl_stability_l _ _ PSCL (composes PScompose);
    PScl_stable_r : @cl_stability_r _ _ PSCL (composes PScompose);
    PSExp : Web -> Type;
    PSsub_monoid_1 : @pwr_str_sub_monoid_hyp_1 _ PSunit PSExp;
    PSsub_monoid_2 : @sub_monoid_hyp_2 _ subset (composes PScompose) PSExp;
    PSsub_J : @pwr_sub_J_hyp _ PSCL PScompose PSunit PSExp;
    PSsub_monoid_distr : @sub_monoid_distr_hyp _ subset (composes PScompose) glb PSExp;
    PScl_commute : b = true -> @cl_commutativity _ _ PSCL (composes PScompose) }.

  Infix "∘" := (composes PScompose) (at level 50, no associativity).
  Infix "⊸" := (magicwand_l PScompose) (at level 51, right associativity).
  Infix "⟜" := (magicwand_r PScompose) (at level 52, left associativity).
  Notation "♯ x" := (glb PSExp x) (at level 40, no associativity).
  Notation "❗ " := (@bang _ _ PSCL glb PSExp) (at level 40, no associativity).


  Section MonadicInterpretation.

    Variable perm_bool : bool.
    Variable PS : MPhaseSpace perm_bool.

    Definition list_compose l := fold_right (composes PScompose) (sg PSunit) l.

    Fact list_compose_nil : list_compose nil = sg PSunit.
    Proof. auto. Qed.

    Fact list_compose_cons f l : list_compose (f :: l) = f ∘ list_compose l.
    Proof. auto. Qed.

    Notation "l ⊧  x" := (list_compose l ⊆ x) (at level 70, no associativity).
    Notation "□" := (@cl _ _ PSCL).

    Hint Resolve (@subset_refl Web) (@subset_preorder Web).
    Hint Resolve (@composes_monotone _ PScompose).
    Hint Resolve (@cl_idempotent _ _ PSCL).
    Hint Resolve (@PScl_stable_l _ PS) (@PScl_stable_r _ PS)
                 (@PS_associative _ PS) (@PS_neutral_l _ PS) (@PS_neutral_r _ PS)
                 (@PSsub_monoid_1 _ PS) (@PSsub_monoid_2 _ PS) (@PSsub_J _ PS).
    Hint Resolve  magicwand_l_adj_l magicwand_l_adj_r magicwand_r_adj_l magicwand_r_adj_r.


    Fact list_compose_app l1 l2 : list_compose (l1 ++ l2) ≃ list_compose l1 ∘ list_compose l2.
    Proof.
    induction l1 as [ | f l IHl ]; simpl; split.
    - apply (m_pwr_neutrality_l (@PS_neutral_l _ PS)).
    - apply (m_pwr_neutrality_l (@PS_neutral_l _ PS)).
    - etransitivity; [ | apply (m_pwr_associativity (@PS_associative _ PS)) ].
      destruct IHl; apply composes_monotone; auto.
    - etransitivity; [ apply (m_pwr_associativity (@PS_associative _ PS)) | ].
      destruct IHl; apply composes_monotone; auto.
    Qed.

    Fact list_compose_monot_app l1 l2 m1 m2 x :
      m1 ⊧ list_compose m2 -> l1 ++ m2 ++ l2 ⊧ x -> l1 ++ m1 ++ l2 ⊧ x.
    Proof.
    intros Hi H.
    etransitivity; [ | apply H ].
    etransitivity; [ | apply list_compose_app ].
    etransitivity; [ apply list_compose_app | ].
    apply composes_monotone; auto.
    etransitivity; [ | apply list_compose_app ].
    etransitivity; [ apply list_compose_app | ].
    apply composes_monotone; auto.
    Qed.

    Fact list_compose_monot_cons l1 x y l2 z :
      x ⊆ y -> l1 ++ y :: l2 ⊧ z -> l1 ++ x :: l2 ⊧ z.
    Proof.
    change (y :: l2) with ((y :: nil) ++ l2).
    change (x :: l2) with ((x :: nil) ++ l2).
    intros Hi.
    apply list_compose_monot_app; simpl.
    apply composes_monotone; auto.
    Qed.

    Notation lcap := (@fold_right (Web -> Type) _ glb top).

    Hint Resolve glb_in glb_out_l glb_out_r top_greatest
                 (m_pwr_cl_neutrality_l_2 (@PS_neutral_l _ PS)) (m_pwr_cl_neutrality_r_2 (@PS_neutral_r _ PS)).

    Fact list_compose_bang l : □ (list_compose (map (fun x => ❗(□x)) l)) ≃ ❗ (lcap (map □ l)).
    Proof.
    eapply lcompose_store; eauto.
    - apply sub_monoid_hyp_1_str, str_sub_monoid_1, PSsub_monoid_1; auto.
    - apply (@sub_J_1 _ _ PScompose PSunit), PSsub_J.
    - apply (@sub_J_2 _ _ PScompose PSunit), PSsub_J.
    Qed.

    Lemma sem_monad_r l x : l ⊧  x -> l ⊧ □x.
    Proof. intros H; etransitivity; [ apply H | apply cl_increase ]. Qed.

    Lemma sem_monad_l l1 l2 x y : l1 ++ x :: l2 ⊧ □y -> l1 ++ □x :: l2 ⊧ □y.
    Proof.
    intros H.
    apply cl_le in H; auto.
    transitivity (list_compose l1  ∘ □ (list_compose (x :: l2))).
    - etransitivity; [ apply list_compose_app | ].
      apply composes_monotone; auto; simpl.
      apply PScl_stable_l.
    - etransitivity; [ | apply H ].
    etransitivity; [ apply PScl_stable_r | ].
    apply cl_monotone.
    etransitivity; [ | apply list_compose_app ]; auto.
    Qed.

    Lemma sem_monad_list_l l1 l2 l x :
      l1 ++ l ++ l2 ⊧ □x -> list_compose l1 ∘ (□(list_compose l) ∘ list_compose l2) ⊆ □x.
    Proof.
    intros H.
    assert (list_compose l1 ∘ (list_compose l ∘ list_compose l2) ⊆ □ x) as H'.
    { etransitivity; [ | apply H ].
      etransitivity; [ | apply list_compose_app ].
      apply composes_monotone; auto.
      apply list_compose_app. }
    apply cl_le in H'; auto.
    etransitivity; [ | apply H' ].
    etransitivity; [ | apply PScl_stable_r ].
    apply composes_monotone; auto.
    Qed.

    Fact sem_ax x : x :: nil ⊧ x.
    Proof. apply (m_pwr_neutrality_r (@PS_neutral_r _ PS)). Qed.

    Fact sem_cut Γ ϴ Δ x y : Γ ⊧ x -> Δ ++ x :: ϴ ⊧ y -> Δ ++ Γ ++ ϴ ⊧ y.
    Proof.
    intros H1 H2.
    change (x :: ϴ) with ((x :: nil) ++ ϴ) in H2.
    apply list_compose_monot_app with (x :: nil); auto; simpl.
    etransitivity; [ apply H1 | ]; auto.
    apply (m_pwr_neutrality_r (@PS_neutral_r _ PS)).
    Qed.

    Fact sem_swap (HPerm: perm_bool = true) Γ Δ x y z : Γ ++ x :: y :: Δ ⊧ □z -> Γ ++ y :: x :: Δ ⊧ □z.
    Proof.
    intros H.
    change (x::y::Δ) with ((x::y::nil)++Δ) in H.
    change (y::x::Δ) with ((y::x::nil)++Δ).
    apply sem_monad_list_l in H.
    etransitivity; [ | apply H ].
    etransitivity; [ apply list_compose_app | ].
    apply composes_monotone; auto.
    etransitivity; [ apply list_compose_app | ].
    apply composes_monotone; auto; simpl.
    etransitivity; [ apply (m_pwr_associativity (@PS_associative _ PS)) | ].
    etransitivity; [ | apply cl_monotone, (m_pwr_associativity (@PS_associative _ PS)) ].
    etransitivity; [ | apply PScl_stable_l ].
    apply composes_monotone; auto.
    apply PScl_commute; auto.
    Qed.

    Fact sem_perm Γ Δ x : perm_bool = true -> Permutation_Type Γ Δ -> Γ ⊧ □x -> Δ ⊧ □x.
    Proof.
    intros Hb HP; revert x; induction HP as [ | a Ga De H1 IH1 | | ] ; intros c; auto.
      + intros H; simpl; apply magicwand_l_adj_r; auto.
        etransitivity; [ | apply (@cl_magicwand_l_1 _ _ _ _ (composes PScompose)) ]; auto.
        apply IH1.
        etransitivity; [ | apply cl_increase ]; auto.
      + apply sem_swap with (Γ := nil) ; assumption.
    Qed.

(* TODO Universe inconsistency in log_cut_elim: even just the statement creates inconsistency
    Fact sem_perm_0 b Γ Δ x : perm_bool = b -> Γ ~[b] Δ -> Γ ⊧ □x -> Δ ⊧ □x.
    Proof.
    destruct b; intros Hbool HP; revert x.
    - induction HP as [ | a Ga De H1 IH1 | | ] ; intros c; auto.
      + intros H; simpl; apply magicwand_l_adj_r; auto.
        etransitivity; [ | apply (@cl_magicwand_l_1 _ _ _ _ (composes PScompose)) ]; auto.
        apply IH1.
        etransitivity; [ | apply cl_increase ]; auto.
      + apply sem_swap with (Γ := nil) ; assumption.
    - simpl in HP; rewrite HP; tauto.
    Qed.

    Fact sem_perm Γ Δ x : Γ ~[perm_bool] Δ -> Γ ⊧ □x -> Δ ⊧ □x.
    Proof. intros HP; apply sem_perm_0 with perm_bool; auto. Qed.
*)

    Fact sem_tens_l Γ Δ x y z : Γ ++ x :: y :: Δ ⊧ z -> Γ ++ x ∘ y :: Δ ⊧ z.
    Proof.
    change (x::y::Δ) with ((x::y::nil)++Δ).
    change (x ∘ y :: Δ) with ((x ∘ y :: nil) ++ Δ).
    intros H; apply list_compose_monot_app with (x :: y :: nil); simpl; auto.
    apply (m_pwr_associativity (@PS_associative _ PS)).
    Qed.

    Fact sem_tens_r Γ Δ x y : Γ ⊧ x -> Δ ⊧ y -> Γ ++ Δ ⊧ x ∘ y.
    Proof.
    intros H1 H2.
    etransitivity; [ apply list_compose_app | ].
    apply composes_monotone; auto.
    Qed.

    Fact sem_one_l_0 Γ Δ x : Γ ++ Δ ⊧ x -> Γ ++ (sg PSunit :: nil) ++ Δ ⊧ x.
    Proof.
    intros H.
    change Δ with (nil ++ Δ) in H.
    apply list_compose_monot_app with nil; auto.
    apply sem_ax.
    Qed.

    Fact sem_one_l Γ Δ x : Γ ++ Δ ⊧ x -> Γ ++ sg PSunit :: Δ ⊧ x.
    Proof. intros H; apply sem_one_l_0; auto. Qed.

    Fact sem_one_r : nil ⊧ sg PSunit.
    Proof. reflexivity. Qed.

    Fact sem_limp_l Γ ϴ Δ x y z : Γ ⊧ x -> ϴ ++ y :: Δ ⊧ z -> ϴ ++ Γ ++ x ⊸ y :: Δ ⊧ z.
    Proof.
    intros H1 H2.
    change (y :: Δ) with ((y :: nil) ++ Δ) in H2.
    replace (Γ ++ x ⊸ y :: Δ) with ((Γ ++ x ⊸ y :: nil) ++ Δ) by (list_simpl; reflexivity).
    apply list_compose_monot_app with (y :: nil); auto.
    etransitivity; [ apply list_compose_app | ].
    apply magicwand_l_adj_r; auto.
    etransitivity; [ apply sem_ax | ].
    apply (@magicwand_l_monotone _ _ _ (composes PScompose)); auto.
    apply (m_pwr_neutrality_r (@PS_neutral_r _ PS)).
    Qed.

    Fact sem_limp_r Γ x y : x :: Γ ⊧ y -> Γ ⊧ x ⊸ y.
    Proof. auto. Qed.

    Fact sem_rimp_l Γ ϴ Δ x y z : Γ ⊧ x -> ϴ ++ y :: Δ ⊧ z -> ϴ ++ y ⟜ x :: Γ ++ Δ ⊧ z.
    Proof.
    intros H1 H2.
    change (y :: Δ) with ((y :: nil) ++ Δ) in H2.
    replace (y ⟜ x :: Γ ++ Δ) with ((y ⟜ x :: Γ) ++ Δ) by (list_simpl; reflexivity).
    apply list_compose_monot_app with (y :: nil); auto; simpl.
    apply magicwand_r_adj_r; auto.
    apply (@magicwand_r_monotone _ _ _ (composes PScompose)); auto.
    apply (m_pwr_neutrality_r (@PS_neutral_r _ PS)).
    Qed.

    Fact sem_rimp_r Γ x y : Γ ++ x :: nil ⊧ y -> Γ ⊧ y ⟜ x.
    Proof.
    intros H.
    apply magicwand_r_adj_l.
    etransitivity; [ | apply H ].
    etransitivity; [ | apply list_compose_app ].
    apply composes_monotone; auto.
    apply (m_pwr_neutrality_r (@PS_neutral_r _ PS)).
    Qed.

    Fact sem_with_l1 Γ Δ x y z : Γ ++ x :: Δ ⊧ z -> Γ ++ x ∩ y :: Δ ⊧ z.
    Proof. intros H; apply list_compose_monot_cons with x; auto; intros ?; tauto. Qed.

    Fact sem_with_l2 Γ Δ x y z : Γ ++ y :: Δ ⊧ z -> Γ ++ x ∩ y :: Δ ⊧ z.
    Proof. intros H; apply list_compose_monot_cons with y; auto; intros ?; tauto. Qed.

    Fact sem_with_r Γ x y : Γ ⊧ x -> Γ ⊧ y -> Γ ⊧ x ∩ y.
    Proof. intros H1 H2; split; auto. Qed.

    Fact sem_plus_l Γ Δ x y z : Γ ++ x :: Δ ⊧ z -> Γ ++ y :: Δ ⊧ z -> Γ ++ x ∪ y :: Δ ⊧ z.
    Proof.
    intros H1 H2.
    etransitivity; [ apply list_compose_app | ].
    apply magicwand_l_adj_r; auto; simpl.
    apply magicwand_r_adj_r; auto.
    assert (x ⊆ list_compose Γ ⊸ z ⟜ list_compose Δ) as H1'.
    { apply magicwand_r_adj_l, magicwand_l_adj_l; auto; simpl.
      rewrite <- list_compose_cons.
      etransitivity; [ apply list_compose_app | ]; auto. }
    assert (y ⊆ list_compose Γ ⊸ z ⟜ list_compose Δ) as H2'.
    { apply magicwand_r_adj_l, magicwand_l_adj_l; auto; simpl.
      rewrite <- list_compose_cons.
      etransitivity; [ apply list_compose_app | ]; auto. }
    intros a [Ha | Ha]; auto.
    Qed.

    Fact sem_plus_r1 Γ x y : Γ ⊧ x -> Γ ⊧ x ∪ y.
    Proof. intros H; (etransitivity; [ apply H | ]); intros ?; auto. Qed.
    Fact sem_plus_r2 Γ x y : Γ ⊧ y -> Γ ⊧ x ∪ y.
    Proof. intros H; (etransitivity; [ apply H | ]); intros ?; auto. Qed.

    Fact sem_top_r Γ : Γ ⊧ top.
    Proof. apply top_greatest. Qed.

    Fact sem_zero_l Γ Δ x : Γ ++ ∅ :: Δ ⊧ x.
    Proof.
    etransitivity; [ apply list_compose_app | ].
    apply magicwand_l_adj_r; auto.
    apply magicwand_r_adj_r; auto.
    intros z HF; inversion HF.
    Qed.

(* TODO try to remove some □: in the rules or in the definition of ❗ *)
    Fact sem_bang_l Γ Δ x y : Γ ++ □x :: Δ ⊧ y -> Γ ++ ❗(□x) :: Δ ⊧ y.
    Proof.
    intros H.
    apply list_compose_monot_cons with (□x); auto.
    apply store_dec; auto.
    Qed.

    Fact sem_weak Γ Δ x y : Γ ++ □(sg PSunit) :: Δ ⊧ y -> Γ ++ ❗x :: Δ ⊧ y.
    Proof.
    intros H.
    apply list_compose_monot_cons with (□(sg PSunit)); auto.
    apply store_inc_unit; auto.
    apply (@sub_J_1 _ _ PScompose PSunit), PSsub_J.
    Qed.

    Fact sem_cntr Γ Δ x y : Γ ++ ❗x :: ❗x :: Δ ⊧ □y -> Γ ++ ❗x :: Δ ⊧ □y.
    Proof.
    intros H.
    change (❗x::❗x::Δ) with ((❗x::❗x::nil)++Δ) in H.
    change (❗x::Δ) with ((❗x::nil)++Δ).
    apply sem_monad_list_l in H.
    etransitivity; [ | apply H ].
    etransitivity; [ apply list_compose_app | ].
    apply composes_monotone; auto.
    etransitivity; [ apply list_compose_app | ].
    apply composes_monotone; auto; simpl.
    transitivity (❗x); [ apply (m_pwr_neutrality_r (@PS_neutral_r _ PS)) | ].
    etransitivity; [ |    apply cl_monotone, (m_pwr_associativity (@PS_associative _ PS)) ].
    etransitivity ; [ | apply cl_monotone, (m_pwr_neutrality_r (@PS_neutral_r _ PS)) ].
    eapply store_compose_idem; eauto.
    apply (@sub_J_2 _ _ PScompose PSunit), PSsub_J.
    Qed.

    Fact sem_bang_r Γ x : map (fun z => ❗(□z)) Γ ⊧ □x -> map (fun z => ❗(□z)) Γ ⊧ ❗(□x).
    Proof.
    intros H.
    apply le_cl; auto.
    etransitivity; [ apply list_compose_bang | ].
    etransitivity; [ | apply store_der ]; auto.
    etransitivity; [ apply list_compose_bang | ].
    apply cl_closed; auto.
    Qed.

    Fact sem_oc_swap Γ Δ x y z : Γ ++ ❗(□x) :: ❗(□y) :: Δ ⊧ □z -> Γ ++ ❗(□y) :: ❗(□x) :: Δ ⊧ □z.
    Proof.
    intros H.
    change (❗(□x)::❗(□y)::Δ) with ((❗(□x)::❗(□y)::nil)++Δ) in H.
    change (❗(□y)::❗(□x)::Δ) with ((❗(□y)::❗(□x)::nil)++Δ).
    apply sem_monad_list_l in H.
    etransitivity; [ | apply H ].
    etransitivity; [ apply list_compose_app | ].
    apply composes_monotone; auto.
    etransitivity; [ apply list_compose_app | ].
    apply composes_monotone; auto; simpl.
    etransitivity; [ apply (m_pwr_associativity (@PS_associative _ PS)) | ].
    etransitivity; [ | apply cl_monotone, (m_pwr_associativity (@PS_associative _ PS)) ].
    etransitivity; [ | apply PScl_stable_l ].
    apply composes_monotone; auto.
    etransitivity; [ | apply (@store_comp_2 _ _ _ PSCL) ]; auto;
      [ | apply (@sub_J_2 _ _ PScompose PSunit), PSsub_J ].
    transitivity (❗(glb (□y) (□x))).
    - etransitivity; [ | eapply (@store_comp _ _ _ PSCL (composes PScompose) _ _ _ (sg PSunit)) ]; auto.
      + etransitivity; [ | apply cl_increase ]; auto.
      + apply (@sub_J_1 _ _ PScompose PSunit), PSsub_J.
      + apply (@sub_J_2 _ _ PScompose PSunit), PSsub_J.
    - apply store_monotone; auto.
    Unshelve. all: auto.
    Qed.

    Fact sem_oc_perm Γ Δ ϴ ϴ' x : Permutation_Type ϴ ϴ' ->
      Γ ++ map (fun z => ❗(□z)) ϴ ++ Δ ⊧ □x -> Γ ++ map (fun z => ❗(□z)) ϴ' ++ Δ ⊧ □x.
    Proof.
    intros HP; revert Γ Δ; induction HP as [ | a Ga De H1 IH1 | | ] ; intros Γ Δ H; auto.
    - simpl.
      change ((❗) (□ a) :: map (fun z : Web -> Type => (❗) (□ z)) De ++ Δ)
        with (((❗) (□ a) :: nil) ++ map (fun z : Web -> Type => (❗) (□ z)) De ++ Δ).
      rewrite app_assoc.
      apply IH1; list_simpl; auto.
    - apply sem_oc_swap; auto.
    Qed.

  End MonadicInterpretation.


  (* Interpretation of Linear Logic *)

  Section FormulaInterpretation.

    Variable perm_bool : bool.
    Variable PS : MPhaseSpace perm_bool.
    Variable v : IAtom -> Web -> Type.
    Notation "□" := (@cl _ _ PSCL).

    Reserved Notation "⟦ A ⟧" (at level 49).
    Fixpoint form_presem f :=
      match f with
      | 0     => ∅
      | ⟙             => top
      | 𝝐              => sg PSunit
      | £ x    => v x
      | a -o b => ⟦a⟧ ⊸ □(⟦b⟧)
      | ineg a => ⟦a⟧ ⊸ □(v atN)
      | b o- a => □(⟦b⟧) ⟜ ⟦a⟧
      | igen a => □(v atN) ⟜ ⟦a⟧
      | a ⊗ b  => ⟦a⟧ ∘ ⟦b⟧
      | a ⊕ b  => ⟦a⟧ ∪ ⟦b⟧
      | a ﹠ b  => □(⟦a⟧) ∩ □(⟦b⟧)
      | !a     => ❗(□(⟦a⟧))
      end
    where "⟦ a ⟧" := (form_presem a).

    Definition list_form_presem l := list_compose PS (map form_presem l).

  End FormulaInterpretation.

  Class MPhaseModel (P : ipfrag) := {
    PMPS : MPhaseSpace (ipperm P);
    PMval : IAtom -> Web -> Type;
    PMgax : forall a, list_form_presem PMPS PMval (fst (projT2 (ipgax P) a))
                    ⊆ @cl _ _ PSCL (form_presem PMPS PMval (snd (projT2 (ipgax P) a))) }.

  Context { P : ipfrag }.
  Variable PM : MPhaseModel P.

  Infix "∘" := (composes PScompose) (at level 50, no associativity).
  Notation "l ⊧  x" := (@list_compose _ PMPS l ⊆ x) (at level 70, no associativity).
  Notation "□" := (@cl _ _ PSCL).
  Notation Int := (@form_presem _ PMPS PMval).
  Notation "l ⊢ x" := (ill P l x) (at level 70, no associativity).

  Hint Resolve  magicwand_l_adj_l magicwand_l_adj_r magicwand_r_adj_l magicwand_r_adj_r.
  Hint Resolve (@sem_monad_l _ PMPS).
  Hint Resolve (@sem_one_r _ PMPS) (@sem_one_l _ PMPS) (@sem_tens_r _ PMPS) (@sem_tens_l _ PMPS)
               (@sem_rimp_r _ PMPS) (@sem_rimp_l _ PMPS) (@sem_limp_r _ PMPS) (@sem_limp_l _ PMPS)
               (@sem_with_r _ PMPS) (@sem_with_l1 _ PMPS) (@sem_with_l2 _ PMPS)
               (@sem_plus_l _ PMPS) (@sem_zero_l _ PMPS)
               (@sem_bang_r _ PMPS) (@sem_bang_l _ PMPS) (@sem_weak _ PMPS) (@sem_cntr _ PMPS).

  Lemma int_ioc_list l : map Int (map ioc l) = map (fun z => ❗(□z)) (map Int l).
  Proof. induction l; auto; simpl; rewrite IHl; auto. Qed.

  Theorem ill_soundness Γ a : Γ ⊢ a -> map Int Γ ⊧ □(Int a).
  Proof.
  intros pi; induction pi;
    (try rewrite ? map_app);
    (try rewrite ? map_app in IHpi); (try rewrite ? map_app in IHpi1); (try rewrite ? map_app in IHpi2);
    (try rewrite int_ioc_list); (try rewrite int_ioc_list in IHpi);
    (try now (apply (@sem_monad_r _ PMPS); simpl; auto));
    (try now (simpl; auto)).
  - apply (@sem_monad_r _ PMPS), sem_ax.
  - assert ({ipperm P = true} + {ipperm P = false}) as Hbool
      by (clear; destruct (ipperm P); [ left | right ]; reflexivity).
    destruct Hbool as [Hbool | Hbool]; intros; rewrite Hbool in p.
    + apply sem_perm with (map Int l1); auto.
      apply Permutation_Type_map; assumption.
    + rewrite <- p; auto.
(* TODO cf Universe inconsistency in sem_perm_0
 eapply (@sem_perm _ PMPS); try eassumption.
    apply PEperm_Type_map; assumption.
*)
  - apply sem_oc_perm with (map Int lw); auto.
    apply Permutation_Type_map; assumption.
  - transitivity (□ (□(Int A) ∘ □(Int B))); auto.
    + apply (@sem_monad_r _ PMPS); auto.
(* TODO use rules *)
    + apply cl_le; [ apply subset_preorder | ]; simpl.
      apply cl_stable; [ apply subset_preorder | apply PScl_stable_l | apply PScl_stable_r ].
  - simpl; apply list_compose_monot_cons with (□ (Int B) ⟜ □ (Int A)); auto.
    + eapply (@magicwand_r_eq_1 _ _ subset_preorder PSCL (composes PScompose) _ _ (magicwand_r PScompose)); auto.
    + rewrite map_app; auto.
  - rewrite <- (app_nil_l (map _ _)) ; apply list_compose_monot_cons with (□ (PMval atN) ⟜ □ (Int A)).
    + eapply (@magicwand_r_eq_1 _ _ subset_preorder PSCL (composes PScompose) _ _ (magicwand_r PScompose)); auto.
    + rewrite <- (app_nil_r _); rewrite <- ? app_assoc.
      apply sem_rimp_l, sem_monad_l, (@sem_monad_r _ PMPS); list_simpl; auto.
      apply (m_pwr_neutrality_r (@PS_neutral_r _ PMPS)).
  - simpl; rewrite app_assoc; apply list_compose_monot_cons with (□ (Int A) ⊸ □ (Int B)); list_simpl; auto.
    eapply (@magicwand_l_eq_1 _ _ subset_preorder PSCL (composes PScompose) _ _ (magicwand_l PScompose)); auto.
  - apply list_compose_monot_cons with (□ (Int A) ⊸ □ (PMval atN)); list_simpl.
    + eapply (@magicwand_l_eq_1 _ _ subset_preorder PSCL (composes PScompose) _ _ (magicwand_l PScompose)); auto.
    + rewrite <- (app_nil_l _); apply sem_limp_l, sem_monad_l; auto.
      apply sem_monad_r, (m_pwr_neutrality_r (@PS_neutral_r _ PMPS)).
  - etransitivity; [ apply IHpi | apply cl_monotone ]; intros z Hz; simpl; auto.
  - etransitivity; [ apply IHpi | apply cl_monotone ]; intros z Hz; simpl; auto.
  - apply sem_cut with (□ (Int A)); auto.
  - apply PMgax.
  Unshelve. all: try apply PScl_stable_l; try apply PScl_stable_r.
  Qed.

End PhaseSpaces.

