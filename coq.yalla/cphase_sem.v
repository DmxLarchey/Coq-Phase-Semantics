Require Import List List_Type Permutation_Type_more.

Require Import closure_operators.
Require Export orthogonality.

Require Import ll_def.

Import SetNotations.
Notation "⁇ l" := (map wn l) (at level 53).


Set Implicit Arguments.

Section PhaseSpaces.

  Fixpoint mcomposes {M} n c e x : M -> Type :=
    match n with
    | 0    => sg e
    | S k  => composes c x (mcomposes k c e x)
    end.

  Definition cps_orth {M} comp (P : M -> Type) := fun (x y : M) => P (comp x y).

  Class CPhaseSpace (bp : bool) (bm : nat -> bool) := {
    CWeb : Type;
    CPScompose : CWeb -> CWeb -> CWeb;
    CPSunit : CWeb;
    CPSPole : CWeb -> Type;
    CPSExp : CWeb -> Type;
    CPScommute : rel_commutativity (cps_orth CPScompose CPSPole);
    CPSneutral_1 : pl_neutrality_1 CPScompose CPSunit CPSPole;
    CPSneutral_2 : pl_neutrality_2 CPScompose CPSunit CPSPole;
    CPSassociative_l : rel_associativity_ll (cps_orth CPScompose CPSPole) CPScompose;
    CPSassociative_r : rel_associativity_lr (cps_orth CPScompose CPSPole) CPScompose;
    CPSsub_monoid_1 : @pwr_sub_monoid_hyp_1 _ (bidualCL CPScommute) CPSunit CPSExp;
    CPSsub_monoid_2 : pwr_sub_monoid_hyp_2 CPScompose CPSExp;
    CPSsub_J : @pwr_sub_J_hyp _ (bidualCL CPScommute) CPScompose CPSunit CPSExp;
    CPSfcommute : bp = true -> pl_fcommutativity CPScompose CPSPole;
    CPSmix : forall n, bm n = true -> mcomposes n CPScompose CPSunit CPSPole ⊆ CPSPole }.

  Notation CPSorth := (cps_orth CPScompose CPSPole).
  Notation dual := (@ldual _ _ CPSorth).
  Notation bidual := (fun X => dual (dual X)).
  Notation tridual := (fun X => dual (dual (dual X))).

  Infix "⊓" := glb (at level 50, no associativity).
  Infix "⊔" := lub (at level 50, no associativity).

  Infix "⅋" := (par CPScompose CPSPole) (at level 59).
  Notation "❗ A" := (bang glb CPSExp A) (at level 40, no associativity).
  Notation "❓ A" := (whynot CPScompose CPSPole CPSExp A) (at level 40, no associativity).

  Section Formula_Interpretation.

    Variable perm_bool : bool.
    Variable mix_bool : nat -> bool.
    Variable PS : CPhaseSpace perm_bool mix_bool.
    Variable v : Atom -> CWeb -> Type.
(*
    Variable cov : Atom -> CWeb -> Type.
*)
    Instance CLPS : ClosureOp := bidualCL CPScommute.

    Infix "∘" := (composes CPScompose) (at level 50, no associativity).
    Notation closed := (fun X => dual (dual X) ⊆ X).

    Hint Resolve subset_preorder glb_in glb_out_l glb_out_r.
    Hint Resolve (@dual_is_closed _ _ CPScommute)
                 (@cl_increase _ _ CLPS)
                 CPScommute CPSassociative_l CPSassociative_r CPSneutral_1 CPSneutral_2.

    Lemma CPSpole_closed : cl CPSPole ⊆ CPSPole.
    Proof. eapply pole_closed; auto. Qed.

    Lemma cl_is_bidual X : cl X ≃ dual (dual X).
    Proof. reflexivity. Qed.

    Lemma bidual_idempotent X : dual (dual (dual (dual X))) ⊆ dual (dual X).
    Proof. apply lmonot; apply tridual_eq; apply CPScommute. Qed.

    Lemma bidual_increase X : X ⊆ dual (dual X).
    Proof. apply (@cl_increase _ _ CLPS). Qed.

    Lemma bidual_subset X Y : X ⊆ dual (dual Y) -> dual (dual X) ⊆ dual (dual Y).
    Proof.
    intros Hc.
    etransitivity; [ apply cl_is_bidual | ].
    transitivity (cl Y) ; [ | apply cl_is_bidual ].
    apply cl_le; [ apply subset_preorder | assumption ].
    Qed.

    Lemma bidual_closed X Y : closed Y -> X ⊆ Y -> dual (dual X) ⊆ Y.
    Proof.
    intros Hc H.
    etransitivity; [ apply bidual_subset | apply Hc ].
    etransitivity; [ apply H | apply bidual_increase ].
    Qed.

    Lemma subset_bidual X Y : dual (dual X) ⊆ dual (dual Y) -> X ⊆ dual (dual Y).
    Proof. intros Hc; etransitivity; [ apply bidual_increase | apply Hc ]. Qed.

    Reserved Notation "⟦ A ⟧" (at level 49).
    Fixpoint form_presem f :=
      match f with
      | var x => v x
      | covar x => dual (v x)
      | one => sg CPSunit
      | bot => CPSPole
      | formulas.zero => closure_operators.zero
      | formulas.top => closure_operators.top
      | tens a b => ⟦b⟧ ∘ ⟦a⟧
      | parr a b => ⟦a⟧ ⅋ ⟦b⟧
      | aplus a b => ⟦a⟧ ∪ ⟦b⟧
      | awith a b => cl(⟦a⟧) ∩ cl(⟦b⟧)
      | oc a => ❗cl(⟦a⟧)
      | wn a => ❓⟦a⟧
      end
    where "⟦ a ⟧" := (form_presem a).

    Definition list_form_presem l := fold_right (composes CPScompose) (sg CPSunit)
                                                (map (fun x => form_presem (formulas.dual x)) l).

    Notation "⟬߭  l ⟭" := (@list_form_presem l) (at level 49).

    Fact list_form_presem_nil : list_form_presem nil = (sg CPSunit).
    Proof. auto. Qed.

    Fact list_form_presem_cons f l :
      list_form_presem (f :: l) = composes CPScompose (⟦formulas.dual f⟧) (list_form_presem l).
    Proof. auto. Qed.

    Lemma form_sem_dual A : dual (⟦A⟧) ⊆ bidual (⟦formulas.dual A⟧).
    Proof.
    induction A; simpl.
    - apply bidual_increase.
    - reflexivity.
    - etransitivity; [ | apply bidual_increase ]; auto.
      apply pole_as_bot; auto.
    - apply lmonot.
      apply pole_as_bot; auto.
    - apply subset_bidual; apply lmonot; apply bidual_subset.
      etransitivity; [ | eapply mstable ]; auto.
      apply composes_monotone; (etransitivity; [ apply bidual_increase | apply lmonot]); auto.
    - apply bidual_subset.
      etransitivity; [ | eapply mstable ]; auto.
      apply composes_monotone; assumption.
    - etransitivity; [ | apply bidual_increase ]; auto.
      apply top_greatest.
    - apply lmonot.
      apply top_greatest.
    - etransitivity; [ | apply bidual_increase ]; auto.
      apply glb_in.
      + etransitivity; [ | apply IHA1 ]; apply lmonot; intros ?; auto.
      + etransitivity; [ | apply IHA2 ]; apply lmonot; intros ?; auto.
    - apply lmonot.
      apply glb_in; apply subset_bidual; apply lmonot.
      + etransitivity; [ apply IHA1 | ]; do 2 apply lmonot; intros ?; auto.
      + etransitivity; [ apply IHA2 | ]; do 2 apply lmonot; intros ?; auto.
    - transitivity (dual (dual (❓ (dual (⟦ A ⟧))))); do 3 apply lmonot.
      + intros ? [] ; split; auto.
      + apply glb_in.
        * apply glb_out_l.
        * etransitivity; [ apply glb_out_r | ].
          etransitivity; [ apply bidual_increase | apply lmonot ]; auto.
    - do 2 apply lmonot.
      etransitivity; [ | apply (@store_monotone _ _ _ CLPS) ]; auto.
      etransitivity; [ apply bidual_increase | ].
      apply (@store_monotone _ _ _ CLPS); auto.
      etransitivity; [ apply IHA | ]; auto.
    Unshelve. all: auto.
    Qed.

  End Formula_Interpretation.


  Class CPhaseModel (P : pfrag) := {
    CPMPS : CPhaseSpace (pperm P) (pmix P);
    CPMval : Atom -> CWeb -> Type;
(*
    CPMcoval : Atom -> CWeb -> Type;
    CPMvdual : forall X x y, CPMval X x -> CPMcoval X y -> CPSorth x y;
*)
    CPMgax : forall a, list_form_presem CPMPS CPMval (projT2 (pgax P) a) ⊆ CPSPole
  }.



  Section Soundness.

    Context { P : pfrag }.
    Variable PM : CPhaseModel P.
    Instance PS : CPhaseSpace (pperm P) (pmix P) := CPMPS.
    Instance CL : ClosureOp := bidualCL CPScommute.

    Infix "∘" := (composes CPScompose) (at level 50, no associativity).
    Notation closed := (fun X => cl X ⊆ X).
    Notation "⟦ A ⟧" := (@form_presem (pperm P) (pmix P) _ CPMval A) (at level 49).
    Notation "⟬߭  l ⟭" := (@list_form_presem (pperm P) (pmix P) _ CPMval l) (at level 49).

    Hint Resolve subset_preorder glb_in glb_out_l glb_out_r top_greatest.
    Hint Resolve (@dual_is_closed _ _ CPScommute)
                 (@cl_increase _ _ CL) (@CPSpole_closed _ _ PS)
                 CPScommute CPSassociative_l CPSassociative_r CPSneutral_1 CPSneutral_2.

    Lemma CPSassociative_l_l : rel_associativity_l_l CPSorth CPScompose CPScompose.
    Proof. eapply pl_rel_associative_l_l; auto. Qed.

    Lemma CPSassociative_l_r : rel_associativity_l_r CPSorth CPScompose CPScompose.
    Proof. eapply pl_rel_associative_l_r; auto. Qed.

    Lemma CPSassociative_r_l : rel_associativity_r_l CPSorth CPScompose (fun x y => CPScompose y x).
    Proof. eapply pl_rel_associative_r_l; auto. Qed.

    Lemma CPSassociative_r_r : rel_associativity_r_r CPSorth CPScompose (fun x y => CPScompose y x).
    Proof. eapply pl_rel_associative_r_r; auto. Qed.

    Hint Resolve CPSassociative_l_l CPSassociative_l_r CPSassociative_r_l CPSassociative_r_r
                 (@mstable_l _ _ _ _ CPScommute CPSassociative_l CPSassociative_r CPSneutral_1 CPSneutral_2)
                 (@mstable_r _ _ _ _ CPScommute CPSassociative_l CPSassociative_r CPSneutral_1 CPSneutral_2)
                 (@mneutral_l_1 _ _ _ _ CPScommute CPSassociative_l CPSneutral_1 CPSneutral_2)
                 (@mneutral_l_2 _ _ _ _ CPScommute CPSassociative_r CPSneutral_1 CPSneutral_2)
                 (@mneutral_r_1 _ _ _ _ CPScommute CPSassociative_r CPSneutral_1 CPSneutral_2)
                 (@mneutral_r_2 _ _ _ _ CPScommute CPSassociative_l CPSneutral_1 CPSneutral_2)
                 CPSsub_monoid_1 CPSsub_monoid_2 CPSsub_J.


    Fact list_form_presem_app_1 l m : cl (⟬߭  l ++ m ⟭) ⊆ cl (⟬߭  l ⟭ ∘ ⟬߭  m ⟭).
    Proof.
    induction l as [ | f l IHl ]; simpl app; auto.
    - etransitivity; [ eapply mneutral_l_1 | ]; auto.
      apply cl_le; auto.
    - rewrite 2 list_form_presem_cons.
      etransitivity; [ | eapply cl_le; try apply massociative_l ]; auto.
      transitivity (cl (⟦ formulas.dual f ⟧ ∘ cl (⟬߭  l ⟭ ∘ ⟬߭  m ⟭))).
      + apply bidual_subset; etransitivity; [ | apply bidual_increase ].
        apply composes_monotone; try reflexivity.
        apply subset_bidual; auto.
      + apply bidual_subset.
        etransitivity; [ | eapply mstable_r ]; auto.
        apply composes_monotone; try reflexivity; assumption.
    Unshelve. all: auto.
    Qed.

    Fact list_form_presem_app_fact_1 l m X : closed X -> ⟬߭  l ⟭ ∘ ⟬߭  m ⟭ ⊆ X -> ⟬߭  l ++ m ⟭ ⊆ X.
    Proof.
    intros HF Hc.
    etransitivity; [ | apply HF].
    apply le_cl; [ apply subset_preorder | ].
    etransitivity; [ apply list_form_presem_app_1 | ].
    apply bidual_subset.
    etransitivity; [ eassumption | apply bidual_increase ].
    Qed.

    Fact list_form_presem_app_2 l m : cl (⟬߭  l ⟭ ∘ ⟬߭  m ⟭) ⊆ cl (⟬߭  l ++ m ⟭).
    Proof.
    induction l as [ | f l IHl ]; simpl app; auto.
    - apply bidual_subset; eapply mneutral_l_2; auto.
    - rewrite 2 list_form_presem_cons.
      etransitivity; [ eapply bidual_subset; eapply massociative_r | ]; auto.
      transitivity (cl (⟦ formulas.dual f ⟧ ∘ cl (⟬߭  l ⟭ ∘ ⟬߭  m ⟭))).
      + apply bidual_subset; etransitivity; [ | apply bidual_increase ].
        apply composes_monotone; try reflexivity.
        apply bidual_increase.
      + apply bidual_subset.
        etransitivity; [ | eapply mstable_r ]; auto.
        apply composes_monotone; try reflexivity; assumption.
    Unshelve. all: auto.
    Qed.

    Fact list_form_presem_app_fact_2 l m X : closed X -> ⟬߭  l ++ m ⟭ ⊆ X -> ⟬߭  l ⟭ ∘ ⟬߭  m ⟭ ⊆ X.
    Proof.
    intros HF Hc.
    etransitivity; [ | apply HF].
    apply le_cl; [ apply subset_preorder | ].
    etransitivity; [ apply list_form_presem_app_2 | ].
    apply bidual_subset.
    etransitivity; [ eassumption | apply bidual_increase ].
    Qed.

    Notation lcap := (@fold_right (CWeb -> Type) _ glb closure_operators.top).

    Fact list_form_presem_bang_1 l : cl (⟬߭⁇l⟭) ⊆ ❗ (lcap (map (fun x => cl (⟦ formulas.dual x ⟧)) l)).
    Proof.
    induction l.
    - simpl; rewrite list_form_presem_nil.
      transitivity (@closure_operators.one _ _ CL (sg CPSunit)); [ reflexivity | ].
      apply (@store_unit_1 _ _ _ CL); auto.
      apply sub_monoid_1, CPSsub_monoid_1.
    - simpl; rewrite list_form_presem_cons.
      apply bidual_subset; auto.
      transitivity (⟦ oc (formulas.dual a) ⟧ ∘ cl (❗ lcap (map (fun x => cl (⟦ formulas.dual x ⟧)) l))).
      + apply composes_monotone; try reflexivity.
        etransitivity; [ | etransitivity; [apply IHl | ] ]; auto; apply bidual_increase.
      + etransitivity; [ eapply mstable_r | ]; auto; simpl form_presem.
        etransitivity;
          [ refine (fst (@store_comp _ _ _ CL (composes CPScompose) _ _ _ (sg CPSunit) _ _ _ _ _ _ _ _ _ _ _ _ _ _))
          | ]; auto.
        * apply sub_monoid_2, CPSsub_monoid_2.
        * apply (@sub_J_1 _ _ CPScompose CPSunit), CPSsub_J.
        * apply (@sub_J_2 _ _ CPScompose CPSunit), CPSsub_J.
        * apply lmglb_closed; auto.
          clear IHl; induction l; simpl; auto.
          constructor; auto.
          apply bidual_idempotent.
        * reflexivity.
    Qed.

    Fact list_form_presem_bang_2 l : ❗ (lcap (map (fun x => cl (⟦ formulas.dual x ⟧)) l)) ⊆ cl (⟬߭⁇l⟭).
    Proof.
    induction l.
    - simpl; rewrite list_form_presem_nil.
      apply (@store_unit_2 _ _ _ CL); auto.
      apply (@sub_J_1 _ _ CPScompose CPSunit), CPSsub_J.
    - simpl; rewrite list_form_presem_cons.
      transitivity (cl (⟦ oc (formulas.dual a) ⟧ ∘ ❗ lcap (map (fun x => cl (⟦ formulas.dual x ⟧)) l))).
      + simpl.
        etransitivity; [ | refine (@store_comp_2 _ _ _ CL (composes CPScompose) _ _ _ _ _ _ _ _ _) ]; auto.
        * clear IHl; induction l; simpl; auto;
            intros x Hx; apply mlbidualcl; auto; apply mlbidualcl in Hx; auto.
        * apply (@sub_J_2 _ _ CPScompose CPSunit), CPSsub_J.
      + apply bidual_subset; auto.
        etransitivity; [ | eapply mstable_r ]; auto.
        apply composes_monotone; try reflexivity; auto.
    Unshelve. all: auto.
    Qed.

    Lemma dualsem : forall A, ⟦ formulas.dual A ⟧ ⊆ CPSPole -> cl(⟦A⟧) CPSunit.
    Proof.
    intros A Hd; apply pole_vs_one; auto.
    etransitivity; [ apply form_sem_dual | ].
    apply bidual_closed; auto ; assumption.
    Qed.

    Theorem ll_soundness l : ll P l -> ⟬߭  l ⟭  ⊆ CPSPole.
    Proof.
    induction 1 using ll_nested_ind.
    - etransitivity; [ apply massociative_l | ]; auto.
      apply cl_closed; auto.
      etransitivity; [ apply mneutral_r_2 | ]; auto.
      apply cl_closed; auto.
      apply pole_commute; auto.
      apply compose_adj_r; reflexivity.
    - assert ({ bp & pperm P = bp }) as [bp Heq] by (exists (pperm P); reflexivity).
      rewrite Heq in p; clear - p IHX Heq.
      case_eq bp; intros HP; rewrite HP in p; simpl in p.
      + revert IHX.
        apply (Permutation_Type_morph_transp (fun x => ⟬߭  x ⟭ ⊆ CPSPole)); auto.
        clear l1 l2 p; intros a b l1 l2 Hp.
        apply list_form_presem_app_fact_2 in Hp; auto.
        apply list_form_presem_app_fact_1; auto.
        intros x Hx; inversion Hx; inversion X0; inversion X2.
        apply CPScommute; apply CPSassociative_l; apply CPSassociative_l_l.
        apply CPSfcommute ; [ rewrite Heq, HP; reflexivity | ].
        apply CPSassociative_l_r; apply CPSassociative_r; apply CPScommute.
        apply Hp.
        do 3 (constructor; auto).
      + inversion p; subst.
        apply list_form_presem_app_fact_2 in IHX; auto.
        apply list_form_presem_app_fact_1; auto.
        apply pole_commute; auto; assumption.
    - apply list_form_presem_app_fact_2 in IHX; auto.
      apply pole_commute in IHX; apply compose_adj_l in IHX; auto.
      apply list_form_presem_app_fact_2 in IHX; auto.
      apply compose_adj_r in IHX.
      apply list_form_presem_app_fact_1; auto.
      apply pole_commute; auto; apply compose_adj_r.
      apply list_form_presem_app_fact_1; auto.
      apply compose_adj_l; auto.
      eapply cl_closed in IHX; auto.
      etransitivity; [ | apply IHX ].
      etransitivity; [ | eapply mstable_l ]; auto.
      apply composes_monotone; try reflexivity.
      etransitivity; [ | eapply mstable_l ]; auto.
      apply composes_monotone; try reflexivity.
      apply subset_bidual.
      etransitivity; [ | apply list_form_presem_bang_2 ].
      etransitivity; [ apply list_form_presem_bang_1 | ].
      apply store_monotone; auto.
      symmetry in p.
      intros x.
      apply (@Permutation_Type_morph_transp _ (fun l => lcap (map (fun A => cl (⟦ formulas.dual A ⟧)) l) x)); auto.
      intros A B L1 L2.
      revert A B L2 x.
      induction L1; intros A B L2; simpl.
      + apply glb_in.
        * etransitivity; [ apply glb_out_r | apply glb_out_l ].
        * apply glb_in; [ apply glb_out_l | ].
          etransitivity; [ apply glb_out_r | apply glb_out_r ].
      + apply glb_in; [ apply glb_out_l | ].
        etransitivity; [ apply glb_out_r | intros x; apply IHL1 ].
    - transitivity (cl (mcomposes (length L) CPScompose CPSunit CPSPole)).
      + clear eqpmix.
        revert PL X; induction L; intros PL X; auto.
        etransitivity ; [ apply cl_increase | ].
        etransitivity ; [ apply list_form_presem_app_1 | ].
        apply bidual_subset.
        inversion X; subst.
        etransitivity ; [ apply composes_monotone | ] ; try eassumption.
        * eapply IHL; try eassumption.
        * eapply mstable_r; auto.
      + apply cl_closed; auto.
        apply CPSmix.
        apply eqpmix.
    - rewrite list_form_presem_cons.
      etransitivity; [ apply mneutral_r_2 | ]; auto.
    - rewrite list_form_presem_cons.
      transitivity (⟦ one ⟧ ∘ ⟬߭  l0 ⟭).
      + apply composes_monotone; auto; try reflexivity.
      + assert (sg CPSunit ∘ ⟬߭  l0 ⟭ ⊆ cl CPSPole) as H.
        { etransitivity; [ apply mneutral_l_2 | ]; auto.
          do 2 apply lmonot; assumption. }
        etransitivity; [ | apply CPSpole_closed ].
        apply bidual_subset in H.
        etransitivity; [ | apply H ].
        apply bidual_increase.
    - rewrite app_comm_cons; apply list_form_presem_app_fact_1; auto.
      rewrite_all list_form_presem_cons.
      etransitivity; [ apply massociative_r | apply cl_closed ]; auto.
      apply compose_adj_l in IHX1; apply compose_adj_l in IHX2; auto.
      transitivity (⟦ formulas.dual (tens A B) ⟧ ∘ (bidual(⟬߭ l2 ⟭) ∘ bidual(⟬߭ l1 ⟭)));
        [ do 2 try apply composes_monotone; try reflexivity; try apply bidual_increase | ].
      apply compose_adj_r.
      simpl; apply lmonot.
      apply composes_monotone; apply lmonot; assumption.
    - rewrite_all list_form_presem_cons.
      assert (⟦ formulas.dual A ⟧ ∘ ⟦ formulas.dual B ⟧ ∘ ⟬߭ l0 ⟭ ⊆ CPSPole) as IHX2
        by (etransitivity; [ apply massociative_r | ]; auto; apply bidual_closed; auto ; assumption).
      apply bidual_closed in IHX2; auto.
      etransitivity ; [ apply bidual_increase | apply IHX2 ].
    - rewrite list_form_presem_cons; simpl.
      intros x Hx; inversion Hx; apply X; intros y Hy; inversion Hy.
    - rewrite_all list_form_presem_cons.
      apply bidual_closed in IHX; auto.
      etransitivity ; [ | apply IHX ].
      etransitivity; [ | eapply mstable_l ]; auto.
      apply composes_monotone; try reflexivity.
      apply glb_out_l.
    - rewrite_all list_form_presem_cons.
      apply bidual_closed in IHX; auto.
      etransitivity ; [ | apply IHX ].
      etransitivity; [ | eapply mstable_l ]; auto.
      apply composes_monotone; try reflexivity.
      apply glb_out_r.
    - rewrite_all list_form_presem_cons.
      apply compose_adj_l in IHX1; apply compose_adj_l in IHX2; auto.
      apply compose_adj_r.
      intros x Hx; inversion Hx; auto.
    - rewrite_all list_form_presem_cons.
      apply pole_commute in IHX; auto.
      apply pole_commute; auto.
      apply compose_adj_l in IHX; auto; apply compose_adj_r.
      simpl; unfold whynot.
      apply subset_bidual.
      etransitivity; [ apply list_form_presem_bang_1 | ].
      apply (@store_der _ _ _ CL); auto.
      transitivity (cl (⟬߭ ⁇ l0 ⟭)) ; [ | apply bidual_closed; auto; eapply dual_is_closed ].
      apply list_form_presem_bang_2.
    - rewrite_all list_form_presem_cons.
      apply compose_adj_l in IHX; auto; apply compose_adj_r.
      transitivity (bidual (⟦ formulas.dual A ⟧)) ; [ | apply bidual_closed; auto; eapply dual_is_closed ].
      apply bidual_subset.
      apply glb_out_r.
    - transitivity (cl (⟬߭  l0 ⟭)); [ | apply cl_closed ]; auto.
      transitivity (bidual(sg CPSunit) ∘ ⟬߭  l0 ⟭).
      + apply composes_monotone; try reflexivity.
        etransitivity; [ | apply bidual_idempotent ].
        simpl; do 2 apply lmonot.
        intros x Hx; inversion Hx.
        apply CPSsub_J in X0.
        apply X0.
      + etransitivity; [ eapply mstable_l | ]; auto.
        apply bidual_subset; eapply mneutral_l_2; auto.
    - rewrite_all list_form_presem_cons.
      transitivity (cl ((⟦ oc (formulas.dual A) ⟧ ∘ ⟦ oc (formulas.dual A) ⟧) ∘ ⟬߭  l0 ⟭)).
      + etransitivity; [ | eapply mstable_l ]; auto.
        apply composes_monotone; try reflexivity.
        change (formulas.dual (wn A)) with (oc (formulas.dual A)).
        apply store_compose_idem; auto.
        * apply composes_monotone.
        * apply (@sub_J_2 _ _ CPScompose CPSunit), CPSsub_J.
      + apply bidual_closed in IHX; auto.
        etransitivity ; [ | apply IHX ].
        apply bidual_subset.
        etransitivity ; [ | eapply massociative_r ]; auto.
        apply composes_monotone; try reflexivity.
    - rewrite_all list_form_presem_cons.
      rewrite formulas.bidual in IHX1.
      apply pole_commute in IHX1; apply pole_commute in IHX2; auto.
      apply compose_adj_l in IHX1; apply compose_adj_l in IHX2; auto.
      apply list_form_presem_app_fact_1; auto.
      etransitivity; [ apply composes_monotone; eassumption | ].
      apply pole_commute; auto.
      apply compose_adj_r.
      apply form_sem_dual.
    - apply CPMgax.
    Unshelve. all: auto.
    Qed.

  End Soundness.

End PhaseSpaces.

