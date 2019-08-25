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

Require Import ill_def.

Import SetNotations.


Notation " x '~[' b ']' y " := (PEperm_Type b x y) (at level 70, format "x  ~[ b ]  y").

Notation "⟙" := (itop).
Notation "0" := (izero).
Notation 𝝐 := (ione).
Infix "&" := (iwith) (at level 50, only parsing).
Infix "﹠" := (iwith) (at level 50).
Infix "⊗" := (itens) (at level 50).
Infix "⊕" := (iplus) (at level 50).
Infix "-o" := (ilmap) (at level 51, right associativity).
Notation "x o- y" := (ilpam y x) (at level 52, left associativity).
Notation "! x" := (ioc x) (at level 53).
Definition ill_lbang := map ioc.
Notation "‼ x" := (ill_lbang x) (at level 53).
Notation "£" := ivar.




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
    PSsub_monoid_2 : @sub_monoid_hyp_2 _ subset (composes PScompose) PSExp;
    PSsub_J : @pwr_sub_J_hyp _ PSCL PScompose PSunit PSExp;
    PScl_commute : b = true -> @cl_commutativity _ _ PSCL (composes PScompose) }.

  (* Interpretation of Linear Logic *)

  Infix "∘" := (composes PScompose) (at level 50, no associativity).
  Infix "⊸" := (magicwand_l PScompose) (at level 51, right associativity).
  Infix "⟜" := (magicwand_r PScompose) (at level 52, left associativity).
  Infix "⊛" := (tensor (composes PScompose)) (at level 59).
  Infix "⊓" := glb (at level 50, no associativity).
  Infix "⊔" := lub (at level 50, no associativity).
  Notation "❗ A" := (bang glb PSExp A) (at level 40, no associativity).

  Section Formula_Interpretation.

    Variable perm_bool : bool.
    Variable PS : PhaseSpace perm_bool.
    Variable v : IAtom -> Web -> Type.
    Instance CL0 : ClosureOp := PSCL.

    Reserved Notation "⟦ A ⟧" (at level 49).
    Fixpoint form_presem f :=
      match f with
      | 0     => zero
      | ⟙             => top
      | 𝝐              => sg PSunit
      | £ x    => v x
      | a -o b => ⟦a⟧ ⊸ cl(⟦b⟧)
      | ineg a => ⟦a⟧ ⊸ cl(v atN)
      | b o- a => cl(⟦b⟧) ⟜ ⟦a⟧
      | igen a => cl(v atN) ⟜ ⟦a⟧
      | a ⊗ b  => ⟦a⟧ ∘ ⟦b⟧
      | a ⊕ b  => ⟦a⟧ ∪ ⟦b⟧
      | a & b  => cl(⟦a⟧) ∩ cl(⟦b⟧)
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

  Class PhaseModel (P : ipfrag) := {
    PMPS : PhaseSpace (ipperm P);
    PMval : IAtom -> Web -> Type;
    PMgax : forall a, list_form_presem PMPS PMval (fst (projT2 (ipgax P) a))
                    ⊆ @cl _ _ PSCL (form_presem PMPS PMval (snd (projT2 (ipgax P) a))) }.

  Context { P : ipfrag }.
  Variable PM : PhaseModel P.
  Instance PS : PhaseSpace (ipperm P) := PMPS.
  Instance CL : ClosureOp := PSCL.

  Hint Resolve (@cl_idempotent _ _ CL).
  Hint Resolve (@PScl_stable_l _ PS) (@PScl_stable_r _ PS)
               (@PScl_associative_l _ PS) (@PScl_associative_r _ PS)
               (@PScl_neutral_l_1 _ PS) (@PScl_neutral_l_2 _ PS)
               (@PScl_neutral_r_1 _ PS) (@PScl_neutral_r_2 _ PS)
               (@PSsub_monoid_1 _ PS) (@PSsub_monoid_2 _ PS) (@PSsub_J _ PS).
  Hint Resolve (@composes_monotone _ PScompose).
  Hint Resolve (@subset_preorder Web).
  Hint Resolve  magicwand_l_adj_l magicwand_l_adj_r magicwand_r_adj_l magicwand_r_adj_r.

  Infix "∘" := (composes PScompose) (at level 50, no associativity).

  Notation closed := (fun x => cl x ⊆ x).
  Notation v := PMval.
  Notation PMform_presem := (form_presem PMPS PMval).
  Notation PMlist_form_presem := (list_form_presem PMPS PMval).
  Notation "⟦ A ⟧" := (PMform_presem A) (at level 49).
  Notation "⟬߭ l ⟭" := (PMlist_form_presem l) (at level 49).

  Fact list_form_presem_app_1 l m : cl (⟬߭ l ++ m ⟭) ⊆ cl (⟬߭  l ⟭ ∘ ⟬߭  m ⟭).
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

  Fact list_form_presem_mono_app_closed l m1 m2 n X : closed X -> ⟬߭m1⟭ ⊆ cl(⟬߭m2⟭)  ->
     ⟬߭l ++ m2 ++ n⟭ ⊆ X -> ⟬߭l ++ m1 ++ n⟭ ⊆ X.
  Proof.
  intros Hc Hi H.
  apply list_form_presem_app_app_closed_1; auto.
  apply list_form_presem_app_app_closed_2 in H; auto.
  transitivity (⟬߭ l ⟭ ∘ cl(⟬߭ m2 ⟭ ∘ ⟬߭ n ⟭)).
  - apply composes_monotone; try reflexivity.
    etransitivity; [ | apply PScl_stable_l ].
    apply composes_monotone; try reflexivity; auto.
  - etransitivity; [ apply PScl_stable_r | ].
    apply cl_closed; auto.
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

    Notation "l ⊢ x" := (ill P l x) (at level 70, no associativity).

    Fact ill_ax_sound a : ⟬߭a :: nil⟭  ⊆ cl (⟦a⟧).
    Proof. apply PScl_neutral_r_2. Qed.

    Fact ill_cut_sound Γ ϴ Δ a b : ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭Δ ++ a :: ϴ⟭ ⊆ cl(⟦b⟧) -> ⟬߭Δ ++ Γ ++ ϴ⟭ ⊆ cl(⟦b⟧).
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

    Fact ill_nc_swap_sound Γ Δ a b c : ⟬߭Γ++!a::!b::Δ⟭ ⊆ cl (⟦c⟧) -> ⟬߭Γ++!b::!a::Δ⟭ ⊆ cl (⟦c⟧).
    Proof.
    intros H.
    change (!a::!b::Δ) with ((!a::!b::nil)++Δ) in H.
    change (!b::!a::Δ) with (map ioc (b::a::nil)++Δ).
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
        transitivity (cl (⟦ a ⟧) ⊓ top); auto.
      + etransitivity; [ apply list_form_presem_bang_2 | ]; reflexivity.
    - transitivity (cl (⟬߭ Γ ⟭ ∘ (⟬߭ !a :: !b :: nil ⟭ ∘ ⟬߭ Δ ⟭)));
        [ transitivity (⟬߭ Γ ⟭ ∘ cl (⟬߭ !a :: !b :: nil ⟭ ∘ ⟬߭ Δ ⟭)) | ]; auto.
      + apply composes_monotone; try reflexivity; auto.
      + apply cl_closed; auto.
    Qed.

    Fact ill_co_oc_perm_sound l1 l2 lw lw' a : Permutation_Type lw lw' ->
             ⟬߭ l1 ++ map ioc lw ++ l2 ⟭ ⊆ cl (⟦ a ⟧) -> ⟬߭ l1 ++ map ioc lw' ++ l2 ⟭ ⊆ cl(⟦ a ⟧).
    Proof.
      intros HP; revert l1 l2; induction HP; intros l1 l2; auto.
      + replace (l1 ++ map ioc (x :: l) ++ l2) with ((l1 ++ ioc x :: nil) ++ map ioc l ++ l2)
          by (simpl; rewrite <- ? app_assoc; rewrite <- app_comm_cons; reflexivity).
        replace (l1 ++ map ioc (x :: l') ++ l2) with ((l1 ++ ioc x :: nil) ++ map ioc l' ++ l2)
          by (simpl; rewrite <- ? app_assoc; rewrite <- app_comm_cons; reflexivity).
        auto.
      + apply ill_nc_swap_sound.
    Qed.

    Fact ill_co_swap_sound (HPerm: ipperm P = true) Γ Δ a b c :
      ⟬߭Γ ++ a :: b :: Δ⟭ ⊆ cl(⟦c⟧) -> ⟬߭Γ ++ b :: a :: Δ⟭ ⊆ cl(⟦c⟧).
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

    Fact ill_perm_sound Γ Δ a : Γ ~[ipperm P] Δ -> ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭Δ⟭ ⊆ cl(⟦a⟧).
    Proof.
    assert ({ipperm P = true} + {ipperm P = false}) as Hbool
      by (clear; destruct (ipperm P); [ left | right ]; reflexivity).
    destruct Hbool as [Hbool | Hbool]; intros.
    - rewrite Hbool in X.
      revert X a X0.
      induction 1 as [ | a Ga De H1 IH1 | | ] ; intros c; auto.
      + rewrite ? list_form_presem_cons.
        intros H; apply magicwand_l_adj_r; auto.
        etransitivity; [ | apply (@cl_magicwand_l_1 _ _ _ _ (composes PScompose)) ]; auto.
        apply IH1 with (a := a -o c); simpl.
        etransitivity; [ | apply cl_increase ]; auto.
      + apply ill_co_swap_sound with (Γ := nil) ; assumption.
    - rewrite Hbool in X; simpl in X; subst; assumption.
    Qed.

    Fact ill_unit_l_sound Γ Δ a : ⟬߭Γ ++ Δ⟭ ⊆ cl(⟦a⟧) -> ⟬߭Γ ++ 𝝐 :: Δ⟭ ⊆ cl(⟦a⟧).
    Proof.
    intros H.
    rewrite <- (app_nil_l Δ) in H.
    change (𝝐 :: Δ) with ((𝝐 :: nil) ++ Δ).
    apply list_form_presem_mono_app_closed with nil; auto; unfold list_form_presem; simpl.
    apply PScl_neutral_l_2.
    Qed.

    Fact ill_unit_r_sound : ⟬߭nil⟭ ⊆ cl(⟦𝝐⟧).
    Proof. apply cl_increase. Qed.

    Fact ill_limp_l_sound Γ ϴ Δ a b c : ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭ϴ ++ b :: Δ⟭ ⊆ cl(⟦c⟧) -> ⟬߭ϴ ++ Γ ++ a -o b :: Δ⟭ ⊆ cl(⟦c⟧).
    Proof.
    intros H1 H2.
    apply list_form_presem_app_app_closed_1; auto.
    rewrite list_form_presem_cons.
    transitivity (⟬߭ ϴ ⟭ ∘ cl((⟬߭ Γ ⟭ ∘ (⟦ a ⟧ ⊸ cl(⟦ b ⟧))) ∘ ⟬߭ Δ ⟭)).
    - apply composes_monotone; try reflexivity.
      apply PScl_associative_l.
    - apply list_form_presem_app_closed_2 in H2; auto.
      eapply cl_closed in H2; auto.
      etransitivity; [ | apply H2 ].
      etransitivity; [ | apply PScl_stable_r ].
      apply composes_monotone; try reflexivity.
      rewrite list_form_presem_cons.
      apply cl_le; auto.
      etransitivity; [ | apply PScl_stable_l ].
      apply composes_monotone; try reflexivity.
      apply magicwand_l_adj_r; auto; try reflexivity.
      etransitivity; [ apply (@cl_magicwand_l_3 _ _ _ _ (composes PScompose)) | ]; auto.
      apply (@magicwand_l_monotone _ _ _ (composes PScompose)); auto; reflexivity.
    Qed.

    Fact ill_neg_l_sound Γ a : ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭Γ ++ ineg a :: nil⟭ ⊆ cl(⟦N⟧).
    Proof.
    intros H.
    replace (⟬߭ Γ ++ ineg a :: nil ⟭) with (⟬߭ nil ++ Γ ++ a -o N :: nil⟭)
      by (unfold list_form_presem; rewrite ? map_app; simpl; reflexivity).
    apply ill_limp_l_sound; auto.
    apply PScl_neutral_r_2.
    Qed.

    Fact ill_rimp_l_sound Γ ϴ Δ a b c : ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭ϴ ++ b :: Δ⟭ ⊆ cl(⟦c⟧) -> ⟬߭ϴ ++ b o- a :: Γ ++ Δ⟭ ⊆ cl(⟦c⟧).
    Proof.
    intros H1 H2.
    rewrite app_comm_cons.
    apply list_form_presem_app_app_closed_1; auto.
    rewrite list_form_presem_cons; simpl.
    apply list_form_presem_app_closed_2 in H2; auto.
    eapply cl_closed in H2; auto.
    etransitivity; [ | apply H2 ].
    etransitivity; [ | apply PScl_stable_r ].
    apply composes_monotone; try reflexivity.
    rewrite list_form_presem_cons.
    etransitivity; [ | apply PScl_stable_l ].
    apply composes_monotone; try reflexivity.
    apply magicwand_r_adj_r; auto; try reflexivity.
    etransitivity; [ apply (@cl_magicwand_r_3 _ _ _ _ (composes PScompose)) | ]; auto.
    apply (@magicwand_r_monotone _ _ _ (composes PScompose)); auto ;reflexivity.
    Qed.

    Fact ill_gen_l_sound Γ a :  ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭igen a :: Γ⟭ ⊆ cl(⟦N⟧).
    Proof.
    intros H.
    replace (⟬߭ igen a :: Γ ⟭) with (⟬߭ nil ++ N o- a :: Γ ++ nil⟭)
      by (unfold list_form_presem; simpl; rewrite app_nil_r; reflexivity).
    apply ill_rimp_l_sound; auto.
    apply PScl_neutral_r_2.
    Qed.

    Fact ill_limp_r_sound Γ a b : ⟬߭a :: Γ⟭ ⊆ cl(⟦b⟧) -> ⟬߭Γ⟭ ⊆ cl(⟦a⟧ ⊸ cl(⟦b⟧)).
    Proof. intro; etransitivity; [ apply magicwand_l_adj_l | apply cl_increase ]; auto. Qed.

    Fact ill_neg_r_sound Γ a : ⟬߭a :: Γ⟭ ⊆ cl(⟦N⟧) -> ⟬߭Γ⟭ ⊆ cl(⟦ineg a⟧).
    Proof. simpl; change (v atN) with (⟦ivar atN⟧); apply ill_limp_r_sound; auto. Qed.

    Fact ill_rimp_r_sound Γ a b : ⟬߭Γ ++ a :: nil⟭ ⊆ cl(⟦b⟧) -> ⟬߭Γ⟭ ⊆ cl(cl(⟦b⟧) ⟜ ⟦a⟧).
    Proof.
    intros H.
    etransitivity; [ | apply cl_increase ].
    apply magicwand_r_adj_l; auto.
    apply list_form_presem_app_closed_2 in H; auto.
    eapply cl_closed in H; auto.
    etransitivity; [ | apply H ].
    etransitivity; [ | apply PScl_stable_r ].
    apply composes_monotone; try reflexivity.
    apply PScl_neutral_r_1.
    Qed.

    Fact ill_gen_r_sound Γ a : ⟬߭Γ ++ a :: nil⟭ ⊆ cl(⟦N⟧) -> ⟬߭Γ⟭ ⊆ cl(⟦igen a⟧).
    Proof. simpl; change (v atN) with (⟦ivar atN⟧); apply ill_rimp_r_sound; auto. Qed.

    Fact ill_with_l1_sound Γ Δ a b c : ⟬߭Γ ++ a :: Δ⟭ ⊆ cl(⟦c⟧) -> ⟬߭Γ ++ a ﹠ b :: Δ⟭ ⊆ cl(⟦c⟧).
    Proof.
    intros H.
    apply list_form_presem_mono_cons_closed with a; auto.
    simpl; red; unfold glb; tauto.
    Qed.

    Fact ill_with_l2_sound Γ Δ a b c : ⟬߭Γ ++ b :: Δ⟭ ⊆ cl(⟦c⟧) -> ⟬߭Γ ++ a ﹠ b :: Δ⟭ ⊆ cl(⟦c⟧).
    Proof.
    intros H.
    apply list_form_presem_mono_cons_closed with b; auto.
    simpl; red; unfold glb; tauto.
    Qed.

    Fact ill_with_r_sound Γ a b : ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭Γ⟭ ⊆ cl(⟦b⟧) -> ⟬߭Γ⟭ ⊆ cl(⟦a﹠b⟧).
    Proof. intros H1 H2; (etransitivity; [ | apply cl_increase ]); split; auto. Qed.

    Fact ill_bang_l_sound Γ Δ a b : ⟬߭Γ++a::Δ⟭ ⊆ cl(⟦b⟧) -> ⟬߭Γ++!a::Δ⟭ ⊆ cl(⟦b⟧).
    Proof.
    intros H.
    apply list_form_presem_mono_cons_closed with a; auto.
    apply store_dec; auto.
    Qed.

    Fact ill_bang_r_sound Γ a : ⟬߭‼Γ⟭ ⊆ cl(⟦ a ⟧) -> ⟬߭‼Γ⟭ ⊆ cl(❗cl(⟦a⟧)).
    Proof.
    intros H.
    apply le_cl; auto.
    etransitivity; [ apply list_form_presem_bang_1 | ].
    etransitivity; [ | apply cl_increase ].
    apply store_der; auto.
    etransitivity; [ apply list_form_presem_bang_2 | ].
    apply cl_closed; auto.
    Qed.

    Fact ill_weak_sound Γ Δ a b : ⟬߭Γ ++ Δ⟭ ⊆ cl(⟦b⟧) -> ⟬߭Γ ++ !a :: Δ⟭ ⊆ cl(⟦b⟧).
    Proof.
    intros H.
    apply list_form_presem_mono_cons_closed with ione; auto.
    - simpl; apply (@store_inc_unit); auto.
      apply (@sub_J_1 _ _ PScompose PSunit), PSsub_J.
    - apply ill_unit_l_sound; assumption.
    Qed.

    Fact ill_cntr_sound Γ Δ a b : ⟬߭Γ ++ !a :: !a :: Δ⟭ ⊆ cl(⟦b⟧) -> ⟬߭Γ ++ !a :: Δ⟭ ⊆ cl(⟦b⟧).
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

    Fact ill_tensor_l_sound Γ Δ a b c : ⟬߭Γ ++ a :: b :: Δ⟭ ⊆ cl(⟦c⟧) -> ⟬߭Γ ++ a ⊗ b :: Δ⟭ ⊆ cl(⟦c⟧).
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

    Fact ill_tensor_r_sound Γ Δ a b : ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭Δ⟭ ⊆ cl(⟦b⟧) -> ⟬߭Γ ++ Δ⟭ ⊆ cl(⟦a⟧ ∘ ⟦b⟧).
    Proof.
    intros H1 H2.
    apply list_form_presem_app_closed_1; [ apply tensor_closed | ].
    etransitivity; [ eapply composes_monotone; eassumption | ].
    apply cl_stable; auto.
    Qed.

    Fact ill_plus_l_sound Γ Δ a b c : ⟬߭Γ ++ a :: Δ⟭ ⊆ cl(⟦c⟧) -> ⟬߭Γ ++ b :: Δ⟭ ⊆ cl(⟦c⟧) ->
       ⟬߭Γ ++ a ⊕ b :: Δ⟭ ⊆ cl(⟦c⟧).
    Proof.
    intros H1 H2.
    apply list_form_presem_app_closed_2 in H1; auto.
    rewrite list_form_presem_cons in H1.
    apply list_form_presem_app_closed_2 in H2; auto.
    rewrite list_form_presem_cons in H2.
    transitivity ((⟬߭Γ⟭ ⊛(⟦a⟧⊛⟬߭Δ⟭)) ⊔ (⟬߭Γ⟭ ⊛(⟦b⟧⊛⟬߭Δ⟭))).
    - apply list_form_presem_app_closed_1; [ apply lub_closed | ].
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

    Fact ill_plus_r1_sound Γ a b : ⟬߭Γ⟭ ⊆ cl(⟦a⟧) -> ⟬߭Γ⟭ ⊆ cl(⟦a ⊕ b⟧).
    Proof. intros H; (etransitivity; [ apply H | ]); apply cl_monotone; left; assumption. Qed.
    Fact ill_plus_r2_sound Γ a b : ⟬߭Γ⟭ ⊆ cl(⟦b⟧) -> ⟬߭Γ⟭ ⊆ cl(⟦a ⊕ b⟧).
    Proof. intros H; (etransitivity; [ apply H | ]); apply cl_monotone; right; assumption. Qed.

    Fact ill_zero_l_sound Γ Δ a : ⟬߭Γ ++ 0 :: Δ⟭ ⊆ cl(⟦a⟧).
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

    Fact ill_top_r_sound Γ : ⟬߭Γ⟭ ⊆ cl(⟦⟙⟧).
    Proof. etransitivity; [ | apply cl_increase ]; apply top_greatest. Qed.

    Hint Resolve ill_ax_sound
                 ill_limp_l_sound ill_limp_r_sound ill_rimp_l_sound ill_rimp_r_sound
                 ill_gen_r_sound ill_gen_l_sound ill_neg_r_sound ill_neg_l_sound
                 ill_with_l1_sound ill_with_l2_sound ill_with_r_sound
                 ill_bang_l_sound ill_bang_r_sound ill_weak_sound ill_cntr_sound
                 ill_tensor_l_sound ill_tensor_r_sound
                 ill_plus_l_sound ill_plus_r1_sound ill_plus_r2_sound
                 ill_zero_l_sound ill_top_r_sound 
                 ill_unit_l_sound ill_unit_r_sound.

    Theorem ill_soundness Γ a : Γ ⊢ a -> ⟬߭Γ⟭  ⊆ cl(⟦a⟧).
    Proof.
    induction 1; try auto ; try now (simpl; auto).
    - revert p IHX; apply ill_perm_sound.
    - apply ill_co_oc_perm_sound with (lw := lw); auto.
    - apply ill_cut_sound with A; auto.
    - apply PMgax.
    Qed.

  End soundness.

End Phase_Spaces.

