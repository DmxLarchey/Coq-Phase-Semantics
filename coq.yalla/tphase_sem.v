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


Require Import List_Type Permutation_Type genperm_Type.

Require Export closure_operators.

Require Import tl_def.

Import SetNotations.


Notation " x '~[' b ']' y " := (PEperm_Type b x y) (at level 70, format "x  ~[ b ]  y").

Notation "0" := tzero.
Notation 𝝐 := tone.
Infix "⊗" := ttens (at level 50).
Infix "⊕" := tplus (at level 50).
Notation "¬" := tneg.
Notation "! x" := (toc x) (at level 53).
Definition tl_lbang := map toc.
Notation "‼ x" := (tl_lbang x) (at level 53).
Notation "£" := tvar.


Set Implicit Arguments.

Section Phase_Spaces.

  Class PhaseSpace (b : bool) := {
    Web : Type;
    PScompose : Web -> Web -> Web;
    PSunit : Web;
    PSCL : @ClosureOp _ (@subset Web);
    PSExp : Web -> Type;
    PScl_stable_l : @cl_stability_l _ _ PSCL (composes PScompose);
    PScl_stable_r : @cl_stability_r _ _ PSCL (composes PScompose);
    PScl_associative_l : @cl_associativity_l _ _ PSCL (composes PScompose);
    PScl_associative_r : @cl_associativity_r _ _ PSCL (composes PScompose);
    PScl_neutral_l_1 : @cl_neutrality_l_1 _ _ PSCL (composes PScompose) (sg PSunit);
    PScl_neutral_l_2 : @cl_neutrality_l_2 _ _ PSCL (composes PScompose) (sg PSunit);
    PScl_neutral_r_1 : @cl_neutrality_r_1 _ _ PSCL (composes PScompose) (sg PSunit);
    PScl_neutral_r_2 : @cl_neutrality_r_2 _ _ PSCL (composes PScompose) (sg PSunit);
    PSsub_monoid_1 : @pwr_sub_monoid_hyp_1 _ PSCL PSunit PSExp;
    PSsub_monoid_2 : pwr_sub_monoid_hyp_2 PScompose PSExp;
    PSsub_J : @pwr_sub_J_hyp _ PSCL PScompose PSunit PSExp;
    PScl_commute : b = true -> @cl_commutativity _ _ PSCL (composes PScompose)
  }.

  (* Interpretation of Tensor Logic *)

  Infix "∘" := (composes PScompose) (at level 50, no associativity).
  Infix "⊛" := (tensor (composes PScompose)) (at level 59).
  Notation "❗ A" := (bang glb PSExp A) (at level 40, no associativity).
  Infix "⊸" := (magicwand_l PScompose) (at level 51, right associativity).

  Section Formula_Interpretation.

    Reserved Notation "⟦ A ⟧" (at level 49).
    Variable perm_bool : bool.
    Variable PS : PhaseSpace perm_bool.
    Variable v : TAtom -> Web -> Type.
    Variable pole : Web -> Type.
    Instance CL0 : ClosureOp := PSCL.

    Fixpoint form_presem f :=
      match f with
      | 0     => zero
      | 𝝐              => sg PSunit
      | £ x    => v x
      | ¬ a => ⟦a⟧ ⊸ cl pole
      | a ⊗ b  => ⟦a⟧ ∘ ⟦b⟧
      | a ⊕ b  => ⟦a⟧ ∪ ⟦b⟧
      | !a     => ❗cl(⟦a⟧)
      end
    where "⟦ a ⟧" := (form_presem a).

    Definition list_form_presem l := fold_right (composes PScompose) (sg PSunit) (map form_presem l).
    Notation "⟬߭  l ⟭" := (list_form_presem l) (at level 49).

    Fact list_form_presem_nil : ⟬߭nil⟭ = sg PSunit.
    Proof. auto. Qed.

    Fact list_form_presem_cons f l : ⟬߭f :: l⟭  = ⟦f⟧ ∘ ⟬߭l⟭.
    Proof. auto. Qed.

  End Formula_Interpretation.

  Class PhaseModel (P : tpfrag) := {
    PMPS : PhaseSpace (tpperm P);
    PMval : TAtom -> Web -> Type;
    PMpole : Web -> Type;
    PMgax : forall a, match (snd (projT2 (tpgax P) a)) with 
                      | Some A => list_form_presem PMPS PMval PMpole (fst (projT2 (tpgax P) a))
                                  ⊆ @cl _ _ PSCL (form_presem PMPS PMval PMpole A)
                      | None   => list_form_presem PMPS PMval PMpole (fst (projT2 (tpgax P) a))
                                  ⊆ @cl _ _ PSCL PMpole
                      end }.

  Context { P : tpfrag }.
  Variable PM : PhaseModel P.
  Instance PS : PhaseSpace (tpperm P) := PMPS.
  Instance CL : ClosureOp := PSCL.

  Hint Resolve (@cl_idempotent _ _ CL).
  Hint Resolve (@PScl_stable_l _ PS) (@PScl_stable_r _ PS)
               (@PScl_associative_l _ PS) (@PScl_associative_r _ PS)
               (@PScl_neutral_l_1 _ PS) (@PScl_neutral_l_2 _ PS)
               (@PScl_neutral_r_1 _ PS) (@PScl_neutral_r_2 _ PS)
               (@PSsub_monoid_1 _ PS) (@PSsub_monoid_2 _ PS) (@PSsub_J _ PS).
  Hint Resolve (@composes_monotone _ PScompose).
  Hint Resolve (@subset_preorder Web).
  Hint Resolve  magicwand_l_adj_l magicwand_l_adj_r.

  Infix "∘" := (composes PScompose) (at level 50, no associativity).

  Notation closed := (fun x => cl x ⊆ x).
  Notation v := PMval.
  Notation PMform_presem := (form_presem PMPS PMval PMpole).
  Notation PMlist_form_presem := (list_form_presem PMPS PMval PMpole).
  Notation "⟦ A ⟧" := (PMform_presem A) (at level 49).
  Notation "⟬߭  l ⟭" := (PMlist_form_presem l) (at level 49).

  Fact list_form_presem_app_1 l m : cl (⟬߭  l ++ m ⟭) ⊆ cl (⟬߭  l ⟭ ∘ ⟬߭  m ⟭).
  Proof.
  induction l as [ | f l IHl ]; simpl app; auto.
  - etransitivity; [ apply PScl_neutral_l_1 | ]; auto.
    apply cl_le; auto.
  - rewrite 2 list_form_presem_cons.
    etransitivity; [ | eapply cl_le; try apply PScl_associative_l ]; auto.
    transitivity (cl (⟦ f ⟧ ∘ cl (⟬߭  l ⟭ ∘ ⟬߭  m ⟭))).
    + apply cl_le; auto; etransitivity; [ | apply cl_increase ].
      apply composes_monotone; try reflexivity.
      apply le_cl; auto; assumption.
    + apply cl_le; auto.
  Qed.

  Fact list_form_presem_app_closed_1 l m X : closed X -> ⟬߭  l ⟭ ∘ ⟬߭  m ⟭ ⊆ X -> ⟬߭  l ++ m ⟭ ⊆ X.
  Proof.
  intros HF Hc.
  etransitivity; [ | apply HF].
  apply le_cl; auto.
  etransitivity; [ apply list_form_presem_app_1 | ].
  apply cl_le; auto.
  etransitivity; [ eassumption | apply cl_increase ].
  Qed.

  Fact list_form_presem_app_2 l m : cl (⟬߭  l ⟭ ∘ ⟬߭  m ⟭) ⊆ cl (⟬߭  l ++ m ⟭).
  Proof.
  induction l as [ | f l IHl ]; simpl app; auto.
  - apply cl_le; try apply neutral_l_2_g; auto.
  - rewrite 2 list_form_presem_cons.
    etransitivity; [ eapply cl_le; try apply PScl_associative_r | ]; auto.
    transitivity (cl (⟦ f ⟧ ∘ cl (⟬߭  l ⟭ ∘ ⟬߭  m ⟭))).
    + apply cl_le; auto; etransitivity; [ | apply cl_increase ].
      apply composes_monotone; try reflexivity.
      apply cl_increase.
    + apply cl_le; auto.
      etransitivity; [ | apply PScl_stable_r ]; auto.
      apply composes_monotone; try reflexivity; assumption.
  Qed.

  Fact list_form_presem_app_closed_2 l m X : closed X -> ⟬߭  l ++ m ⟭ ⊆ X -> ⟬߭  l ⟭ ∘ ⟬߭  m ⟭ ⊆ X.
  Proof.
  intros HF Hc.
  etransitivity; [ | apply HF].
  apply le_cl; auto.
  etransitivity; [ apply list_form_presem_app_2 | ].
  apply cl_le; auto.
  etransitivity; [ eassumption | apply cl_increase ].
  Qed.

  Fact list_form_presem_app_app_closed_1 l m n X : closed X -> ⟬߭  l ⟭ ∘ (⟬߭  m ⟭ ∘ ⟬߭  n ⟭) ⊆ X -> ⟬߭  l ++ m ++ n ⟭ ⊆ X.
  Proof.
  intros HF Hc.
  apply list_form_presem_app_closed_1; auto.
  transitivity (⟬߭ l ⟭ ∘ cl (⟬߭ m ⟭ ∘ ⟬߭  n ⟭)).
  - apply composes_monotone; try reflexivity.
    apply le_cl; auto; apply list_form_presem_app_1.
  - eapply cl_closed in Hc; auto; [ | apply HF ].
    etransitivity; [ | apply Hc ].
    etransitivity; [ | apply PScl_stable_r ].
    apply composes_monotone; try reflexivity.
  Qed.

  Fact list_form_presem_app_app_closed_2 l m n X : closed X -> ⟬߭  l ++ m ++ n ⟭ ⊆ X -> ⟬߭  l ⟭ ∘ (⟬߭  m ⟭ ∘ ⟬߭  n ⟭) ⊆ X.
  Proof.
  intros HF Hc.
  transitivity (⟬߭ l ⟭ ∘ cl (⟬߭ m ++ n ⟭)).
  - apply composes_monotone; try reflexivity.
    apply le_cl; auto; apply list_form_presem_app_2.
  - etransitivity; [ apply PScl_stable_r | ].
    apply cl_closed; auto.
    apply list_form_presem_app_closed_2; auto.
  Qed.

  Fact list_form_presem_mono_app_closed l m1 m2 n X : closed X -> ⟬߭m1⟭ ⊆ ⟬߭m2⟭  ->
     ⟬߭l ++ m2 ++ n⟭ ⊆ X -> ⟬߭l ++ m1 ++ n⟭ ⊆ X.
  Proof.
  intros Hc Hi H.
  apply list_form_presem_app_app_closed_1; auto.
  apply list_form_presem_app_app_closed_2 in H; auto.
  etransitivity; [ | apply H ].
  apply composes_monotone; try reflexivity.
  apply composes_monotone; try reflexivity; auto.
  Qed.

  Fact list_form_presem_mono_cons_closed l a b m X : closed X -> ⟦a⟧ ⊆ cl(⟦b⟧) ->
     ⟬߭l ++ b :: m⟭ ⊆ X -> ⟬߭l ++ a :: m⟭ ⊆ X.
  Proof.
  intros Hc Hi H.
  apply list_form_presem_app_closed_1; auto.
  rewrite list_form_presem_cons.
  apply list_form_presem_app_closed_2 in H; auto.
  rewrite list_form_presem_cons in H.
  transitivity (⟬߭ l ⟭ ∘ (cl(⟦ b ⟧) ∘ ⟬߭ m ⟭)).
  - apply composes_monotone; try reflexivity.
    apply composes_monotone; try reflexivity; auto.
  - transitivity (⟬߭ l ⟭ ∘ cl (⟦ b ⟧ ∘ ⟬߭ m ⟭)).
    + apply composes_monotone; try reflexivity.
      apply PScl_stable_l.
    + etransitivity; [ apply PScl_stable_r | ].
      apply cl_closed; auto.
  Qed.

  Notation lcap := (@fold_right (Web -> Type) _ glb top).

  Hint Resolve glb_in glb_out_l glb_out_r top_greatest.

  Fact list_form_presem_bang_1 l : cl (⟬߭‼l⟭) ⊆ ❗ (lcap (map (fun x => cl (⟦ x ⟧)) l)).
  Proof.
  induction l.
  - simpl; rewrite list_form_presem_nil.
    apply store_unit_1; auto.
    apply sub_monoid_1, PSsub_monoid_1.
  - simpl; rewrite list_form_presem_cons.
    apply cl_le; auto.
    transitivity (⟦ ! a ⟧ ∘ cl (❗ lcap (map (fun x => cl (⟦ x ⟧)) l))).
    + apply composes_monotone; try reflexivity.
      etransitivity; [ | etransitivity; [apply IHl | ] ]; auto; apply cl_increase.
    + etransitivity; [ apply PScl_stable_r | ]; simpl.
      etransitivity;
        [ refine (fst (@store_comp _ _ _ _ (composes PScompose) _ _ _ (sg PSunit) _ _ _ _ _ _ _ _ _ _ _ _ _ _))
        | ]; auto.
      * apply sub_monoid_2, PSsub_monoid_2.
      * apply (@sub_J_1 _ _ PScompose PSunit), PSsub_J.
      * apply (@sub_J_2 _ _ PScompose PSunit), PSsub_J.
      * apply lmglb_closed; auto.
        clear IHl; induction l; simpl; auto.
      * reflexivity.
  Qed.

  Fact list_form_presem_bang_2 l : ❗ (lcap (map (fun x => cl (⟦ x ⟧)) l)) ⊆ cl (⟬߭‼l⟭).
  Proof.
  induction l.
  - simpl; rewrite list_form_presem_nil.
    eapply store_unit_2; eauto.
    apply (@sub_J_1 _ _ PScompose PSunit), PSsub_J.
  - simpl; rewrite list_form_presem_cons.
    transitivity (cl (⟦ ! a ⟧ ∘ ❗ lcap (map (fun x => cl (⟦ x ⟧)) l))).
    + simpl.
      etransitivity; [ | refine (@store_comp_2 _ _ _ _ (composes PScompose) _ _ _ _ _ _ _ _ _) ]; auto.
      * clear IHl; induction l; simpl; auto; apply store_monotone; auto.
      * apply (@sub_J_2 _ _ PScompose PSunit), PSsub_J.
    + apply cl_le; auto.
      etransitivity; [ | apply PScl_stable_r ].
      apply composes_monotone; try reflexivity; auto.
  Qed.



  (* All the rules of the ILL sequent calculus (including cut) are closed
     under relational phase semantics, hence we deduce the following
     soundness theorem *)

  Section soundness.

    Fact tl_ax_sound a : ⟬߭a :: nil⟭  ⊆ cl (⟦a⟧).
    Proof. apply PScl_neutral_r_2. Qed.

    Fact tl_cut_sound Γ ϴ Δ a X : ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭Δ ++ a :: ϴ⟭ ⊆ cl X -> ⟬߭Δ ++ Γ ++ ϴ⟭ ⊆ cl X.
    Proof.
    intros H1 H2.
    apply list_form_presem_app_app_closed_1; auto.
    apply list_form_presem_app_closed_2 in H2; auto.
    rewrite list_form_presem_cons in H2.
    apply cl_le in H2; auto.
    etransitivity; [ | apply H2 ].
    etransitivity; [ | apply PScl_stable_r ].
    apply composes_monotone; try reflexivity.
    etransitivity; [ | apply PScl_stable_l ].
    apply composes_monotone; try reflexivity; assumption.
    Qed.

    Fact tl_nc_swap_sound Γ Δ a b X : ⟬߭Γ++!a::!b::Δ⟭ ⊆ cl X -> ⟬߭Γ++!b::!a::Δ⟭ ⊆ cl X.
    Proof.
    intros H.
    change (!a::!b::Δ) with ((!a::!b::nil)++Δ) in H.
    change (!b::!a::Δ) with (map toc (b::a::nil)++Δ).
    apply list_form_presem_app_app_closed_1; auto.
    apply list_form_presem_app_app_closed_2 in H; auto.
    transitivity (⟬߭ Γ ⟭ ∘ (cl (⟬߭ !a :: !b :: nil ⟭) ∘ ⟬߭ Δ ⟭)).
    - apply composes_monotone; try reflexivity.
      apply composes_monotone; try reflexivity.
      etransitivity; [ apply cl_increase | ].
      etransitivity; [ apply list_form_presem_bang_1 | ].
      transitivity (❗ lcap (map (fun x => cl (⟦ x ⟧)) (a :: b :: nil))).
      + apply store_monotone; auto.
        simpl; apply glb_in; auto.
        transitivity (glb (cl (⟦ a ⟧)) top); auto.
      + etransitivity; [ apply list_form_presem_bang_2 | ]; reflexivity.
    - transitivity (cl (⟬߭ Γ ⟭ ∘ (⟬߭ !a :: !b :: nil ⟭ ∘ ⟬߭ Δ ⟭)));
        [ transitivity (⟬߭ Γ ⟭ ∘ cl (⟬߭ !a :: !b :: nil ⟭ ∘ ⟬߭ Δ ⟭)) | ]; auto.
      + apply composes_monotone; try reflexivity; auto.
      + apply cl_closed; auto.
    Qed.

    Fact tl_co_oc_perm_sound l1 l2 lw lw' X : Permutation_Type lw lw' ->
             ⟬߭ l1 ++ map toc lw ++ l2 ⟭ ⊆ cl X -> ⟬߭ l1 ++ map toc lw' ++ l2 ⟭ ⊆ cl X.
    Proof.
      intros HP; revert l1 l2; induction HP; intros l1 l2; auto.
      + replace (l1 ++ map toc (x :: l) ++ l2) with ((l1 ++ toc x :: nil) ++ map toc l ++ l2)
          by (simpl; rewrite <- ? app_assoc; rewrite <- app_comm_cons; reflexivity).
        replace (l1 ++ map toc (x :: l') ++ l2) with ((l1 ++ toc x :: nil) ++ map toc l' ++ l2)
          by (simpl; rewrite <- ? app_assoc; rewrite <- app_comm_cons; reflexivity).
        auto.
      + apply tl_nc_swap_sound.
    Qed.

    Fact tl_co_swap_sound (HPerm: tpperm P = true) Γ Δ a b X :
      ⟬߭Γ ++ a :: b :: Δ⟭ ⊆ cl X -> ⟬߭Γ ++ b :: a :: Δ⟭ ⊆ cl X.
    Proof.
    intros H.
    change (a::b::Δ) with ((a::b::nil)++Δ) in H.
    change (b::a::Δ) with ((b::a::nil)++Δ).
    apply list_form_presem_app_app_closed_1; auto.
    apply list_form_presem_app_app_closed_2 in H; auto.
    transitivity (⟬߭ Γ ⟭ ∘ (cl (⟬߭ a :: b :: nil ⟭) ∘ ⟬߭ Δ ⟭)).
    - apply composes_monotone; try reflexivity.
      apply composes_monotone; try reflexivity.
      transitivity (⟦ b ⟧ ∘ cl (⟦ a ⟧)); [ | transitivity (cl (⟦ a ⟧ ∘ ⟦ b ⟧))].
      + apply composes_monotone; try reflexivity.
        apply PScl_neutral_r_2.
      + etransitivity; [ apply PScl_stable_r | ].
        apply cl_le; auto.
        apply PScl_commute; auto.
      + apply cl_le; auto.
        etransitivity; [ | apply PScl_stable_r ].
        apply composes_monotone; try reflexivity; auto.
    - transitivity (cl (⟬߭ Γ ⟭ ∘ (⟬߭ a :: b :: nil ⟭ ∘ ⟬߭ Δ ⟭)));
        [ transitivity (⟬߭ Γ ⟭ ∘ cl (⟬߭ a :: b :: nil ⟭ ∘ ⟬߭ Δ ⟭)) | ]; auto.
      + apply composes_monotone; try reflexivity; auto.
      + apply cl_closed; auto.
    Qed.

    Fact tl_perm_sound Γ Δ X : Γ ~[tpperm P] Δ -> ⟬߭Γ⟭ ⊆ cl X -> ⟬߭Δ⟭ ⊆ cl X.
    Proof.
    assert ({tpperm P = true} + {tpperm P = false}) as Hbool
      by (clear; destruct (tpperm P); [ left | right ]; reflexivity).
    destruct Hbool as [Hbool | Hbool]; intros.
    - rewrite Hbool in X0.
      revert X0 X X1.
      induction 1 as [ | a Ga De H1 IH1 | | ] ; intros c; auto.
      + rewrite ? list_form_presem_cons.
        intros H; apply magicwand_l_adj_r; auto.
        etransitivity; [ | apply (@cl_magicwand_l_1 _ _ _ _ (composes PScompose)) ]; auto.
        apply IH1 with (X := ⟦ a ⟧ ⊸ cl c); simpl.
        etransitivity; [ | apply cl_increase ]; auto.
      + apply tl_co_swap_sound with (Γ := nil) ; assumption.
    - rewrite Hbool in X0; simpl in X0; subst; assumption.
    Qed.

    Fact tl_unit_l_sound Γ Δ X : ⟬߭Γ ++ Δ⟭ ⊆ cl X -> ⟬߭Γ ++ 𝝐 :: Δ⟭ ⊆ cl X.
    Proof.
    intros H.
    apply list_form_presem_app_closed_1; auto.
    rewrite list_form_presem_cons; simpl; unfold one.
    transitivity (⟬߭ Γ ⟭ ∘ (cl (sg PSunit ∘ ⟬߭ Δ ⟭))).
    - apply composes_monotone; try reflexivity; auto.
      apply cl_increase.
    - etransitivity; [ apply PScl_stable_r | ].
      apply cl_closed; auto.
      transitivity (⟬߭ Γ ⟭ ∘ cl (⟬߭ Δ ⟭)).
      + apply composes_monotone; try reflexivity.
        apply PScl_neutral_l_2.
      + etransitivity; [ apply PScl_stable_r | ].
        apply cl_closed; auto.
        apply list_form_presem_app_closed_2; auto.
    Qed.

    Fact tl_unit_r_sound : ⟬߭nil⟭ ⊆ cl(⟦𝝐⟧).
    Proof. apply cl_increase. Qed.

    Fact tl_neg_l_sound Γ a : ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭Γ ++ ¬ a :: nil⟭ ⊆ cl PMpole.
    Proof.
    intros H.
    apply list_form_presem_app_closed_1; auto.
    rewrite list_form_presem_cons.
    transitivity (cl(⟬߭ Γ ⟭ ∘ ⟦ ¬ a ⟧)).
    - etransitivity; [ | apply PScl_stable_r ].
      apply composes_monotone; try reflexivity.
      apply PScl_neutral_r_2.
    - apply cl_closed; auto.
      apply magicwand_r_adj_r; auto.
      etransitivity; [ apply H | ].
      apply magicwand_r_adj_l.
      etransitivity; [ apply PScl_stable_l | ].
      apply cl_le; auto.
      apply magicwand_l_adj_r; reflexivity.
    Qed.

    Fact tl_neg_r_sound Γ a : ⟬߭a :: Γ⟭ ⊆ cl PMpole -> ⟬߭Γ⟭ ⊆ cl(⟦¬ a⟧).
    Proof. intro; etransitivity; [ apply magicwand_l_adj_l | apply cl_increase ]; auto. Qed.

    Fact tl_bang_l_sound Γ Δ a X : ⟬߭Γ++a::Δ⟭ ⊆ cl X -> ⟬߭Γ++!a::Δ⟭ ⊆ cl X.
    Proof.
    intros H.
    apply list_form_presem_mono_cons_closed with a; auto.
    apply store_dec; auto.
    Qed.

    Fact tl_bang_r_sound Γ a : ⟬߭‼Γ⟭ ⊆ cl(⟦ a ⟧) -> ⟬߭‼Γ⟭ ⊆ cl(❗cl(⟦a⟧)).
    Proof.
    intros H.
    apply le_cl; auto.
    etransitivity; [ apply list_form_presem_bang_1 | ].
    etransitivity; [ | apply cl_increase ].
    apply store_der; auto.
    etransitivity; [ apply list_form_presem_bang_2 | ].
    apply cl_closed; auto.
    Qed.

    Fact tl_weak_sound Γ Δ a X : ⟬߭Γ ++ Δ⟭ ⊆ cl X -> ⟬߭Γ ++ !a :: Δ⟭ ⊆ cl X.
    Proof.
    intros H.
    apply list_form_presem_mono_cons_closed with tone; auto.
    - simpl; apply (@store_inc_unit); auto.
      apply (@sub_J_1 _ _ PScompose PSunit), PSsub_J.
    - apply tl_unit_l_sound; assumption.
    Qed.

    Fact tl_cntr_sound Γ Δ a X : ⟬߭Γ ++ !a :: !a :: Δ⟭ ⊆ cl X -> ⟬߭Γ ++ !a :: Δ⟭ ⊆ cl X.
    Proof.
    intros H.
    change (!a::!a::Δ) with ((!a::!a::nil)++Δ) in H.
    apply list_form_presem_mono_cons_closed with ((!a) ⊗ (!a)); auto.
    - eapply store_compose_idem; eauto.
      apply (@sub_J_2 _ _ PScompose PSunit), PSsub_J.
    - apply list_form_presem_app_closed_1; auto.
      rewrite list_form_presem_cons; simpl.
      simpl in H.
      apply list_form_presem_app_closed_2 in H; auto.
      rewrite 2 list_form_presem_cons in H.
      transitivity (⟬߭ Γ ⟭ ∘ cl (⟦ ! a ⟧ ∘ (⟦ ! a ⟧ ∘ ⟬߭ Δ ⟭))).
      + apply composes_monotone; try reflexivity.
        apply PScl_associative_r.
      + etransitivity; [ apply PScl_stable_r | ].
        apply cl_closed; auto.
    Qed.

    Fact tl_tensor_l_sound Γ Δ a b X : ⟬߭Γ ++ a :: b :: Δ⟭ ⊆ cl X -> ⟬߭Γ ++ a ⊗ b :: Δ⟭ ⊆ cl X.
    Proof.
    intros H.
    change (a::b::Δ) with ((a::b::nil)++Δ) in H.
    - apply list_form_presem_app_closed_1; auto.
      rewrite list_form_presem_cons; simpl.
      simpl in H.
      apply list_form_presem_app_closed_2 in H; auto.
      rewrite 2 list_form_presem_cons in H.
      transitivity (⟬߭ Γ ⟭ ∘ cl (⟦ a ⟧ ∘ (⟦ b ⟧ ∘ ⟬߭ Δ ⟭))).
      + apply composes_monotone; try reflexivity.
        apply PScl_associative_r.
      + etransitivity; [ apply PScl_stable_r | ].
        apply cl_closed; auto.
    Qed.

    Fact tl_tensor_r_sound Γ Δ a b : ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭Δ⟭ ⊆ cl(⟦b⟧) -> ⟬߭Γ ++ Δ⟭ ⊆ cl(⟦a⟧ ∘ ⟦b⟧).
    Proof.
    intros H1 H2.
    apply list_form_presem_app_closed_1; [ apply tensor_closed | ].
    etransitivity; [ eapply composes_monotone; eassumption | ].
    apply cl_stable; auto.
    Qed.

    Fact tl_plus_l_sound Γ Δ a b X :
       ⟬߭Γ ++ a :: Δ⟭ ⊆ cl X -> ⟬߭Γ ++ b :: Δ⟭ ⊆ cl X -> ⟬߭Γ ++ a ⊕ b :: Δ⟭ ⊆ cl X.
    Proof.
    intros H1 H2.
    apply list_form_presem_app_closed_2 in H1; auto.
    rewrite list_form_presem_cons in H1.
    apply list_form_presem_app_closed_2 in H2; auto.
    rewrite list_form_presem_cons in H2.
    transitivity (cl ((⟬߭Γ⟭ ⊛(⟦a⟧⊛⟬߭Δ⟭)) ∪ (⟬߭Γ⟭ ⊛(⟦b⟧⊛⟬߭Δ⟭)))).
    - apply list_form_presem_app_closed_1; [ apply cl_closed | ]; auto; try reflexivity.
      rewrite list_form_presem_cons.
      eapply subset_trans; [ | apply tensor_lub_distrib_r ]; auto.
      etransitivity; [ | apply cl_increase ].
      apply composes_monotone; try reflexivity.
      etransitivity; [ | apply tensor_lub_distrib_l]; auto.
      etransitivity; [ | apply cl_increase ].
      apply composes_monotone; try reflexivity.
      apply cl_increase.
    - apply lub_out; auto.
      + eapply cl_closed in H1; auto.
        etransitivity; [ | apply H1 ].
        apply cl_le; auto.
        etransitivity; [ | apply PScl_stable_r ]; reflexivity.
      + eapply cl_closed in H2; auto.
        etransitivity; [ | apply H2 ].
        apply cl_le; auto.
        etransitivity; [ | apply PScl_stable_r ]; reflexivity.
    Qed.

    Fact tl_plus_r1_sound Γ a b : ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭Γ⟭ ⊆ cl(⟦a ⊕ b⟧).
    Proof. intros H; (etransitivity; [ apply H | ]); apply cl_monotone; left; assumption. Qed.
    Fact tl_plus_r2_sound Γ a b : ⟬߭Γ⟭ ⊆ cl(⟦b⟧) -> ⟬߭Γ⟭ ⊆ cl(⟦a ⊕ b⟧).
    Proof. intros H; (etransitivity; [ apply H | ]); apply cl_monotone; right; assumption. Qed.

    Fact tl_zero_l_sound Γ Δ X : ⟬߭Γ ++ 0 :: Δ⟭ ⊆ cl X.
    Proof.
    apply list_form_presem_app_closed_1; auto.
    rewrite list_form_presem_cons; simpl.
    etransitivity; [ | apply zero_least ]; auto.
    etransitivity; [ | apply tensor_zero_distrib_r with (compose := PScompose) (A := ⟬߭Γ⟭)]; auto.
    etransitivity; [ | apply cl_increase ].
    apply composes_monotone; try reflexivity.
    etransitivity; [ | apply tensor_zero_distrib_l with (compose := PScompose) (A := ⟬߭Δ⟭)]; auto.
    etransitivity; [ | apply cl_increase ]; reflexivity.
    Qed.

    Hint Resolve tl_ax_sound
                 tl_neg_r_sound tl_neg_l_sound
                 tl_bang_l_sound tl_bang_r_sound tl_weak_sound tl_cntr_sound
                 tl_tensor_l_sound tl_tensor_r_sound
                 tl_plus_l_sound tl_plus_r1_sound tl_plus_r2_sound
                 tl_zero_l_sound tl_unit_l_sound tl_unit_r_sound.

    Notation option_presem := (fun A =>
    match A with
    | None => PMpole
    | Some B => ⟦B⟧
    end).

    Theorem tl_soundness Γ A : tl P Γ A -> ⟬߭Γ⟭  ⊆ cl(option_presem A).
    Proof.
    induction 1; try auto ; try now (simpl; auto).
    - revert p IHX; apply tl_perm_sound.
    - apply tl_co_oc_perm_sound with (lw := lw); auto.
    - apply tl_cut_sound with A; auto.
    - assert (H := PMgax a); destruct (snd (projT2 (tpgax P) a)); auto.
    Qed.

  End soundness.

End Phase_Spaces.

