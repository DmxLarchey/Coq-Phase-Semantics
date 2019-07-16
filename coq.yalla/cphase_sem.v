Require Import List List_Type Permutation_Type_more.

Require Import closure_operators.
Require Export orthogonality.

Require Import ll_def.

Set Implicit Arguments.

Section Phase_Spaces.

  Notation "X '⊆' Y" := (subset X Y) (at level 75, format "X  ⊆  Y", no associativity).
  Notation "X '≃' Y" := (eqset X Y) (at level 75, format "X  ≃  Y", no associativity).
  Notation "A '∩' B" := (fun z => A z * B z : Type)%type (at level 50, format "A  ∩  B", left associativity).
  Notation "A '∪' B" := (fun z => A z + B z : Type)%type (at level 50, format "A  ∪  B", left associativity).


  Class CPhaseSpace (bp b0 b2 : bool) := {
    CWeb : Type;
    CPSCompose : CWeb -> CWeb -> CWeb;
    CPSUnit : CWeb;
    CPSPole : CWeb -> Type;
    CPSExp : CWeb -> Type;
    CPScommute : pole_commute CPSCompose CPSPole;
    CPSassociative_l : pole_associative_l CPSCompose CPSPole;
    CPSassociative_r : pole_associative_r CPSCompose CPSPole;
    CPSassociative_ll : pole_associative_ll CPSCompose CPSPole;
    CPSassociative_lr : pole_associative_lr CPSCompose CPSPole;
    CPSneutral_1 : pole_neutral_1 CPSCompose CPSUnit CPSPole;
    CPSneutral_2 : pole_neutral_2 CPSCompose CPSUnit CPSPole;
    CPSneutral_l_1 : pole_neutral_l_1 CPSCompose CPSUnit CPSPole;
    CPSneutral_l_2 : pole_neutral_l_2 CPSCompose CPSUnit CPSPole;
    CPSneutral_r_1 : pole_neutral_r_1 CPSCompose CPSUnit CPSPole;
    CPSneutral_r_2 : pole_neutral_r_2 CPSCompose CPSUnit CPSPole;
    CPSsub_monoid_1 : @sub_monoid_hyp_1 _ (bidualCL CPScommute) CPSUnit CPSExp;
    CPSsub_monoid_2 : sub_monoid_hyp_2 (MComposes CPSCompose) CPSExp;
    CPSsub_J : @sub_J_hyp _ (bidualCL CPScommute) (MComposes CPSCompose) CPSUnit CPSExp;
    CPSfcommute : bp = true -> pole_fcommute CPSCompose CPSPole;
    CPSmix0 : b0 = true -> CPSPole CPSUnit;
    CPSmix2 : b2 = true -> MComposes CPSCompose CPSPole CPSPole ⊆ CPSPole
  }.

  Notation dual := (ldual (R CPSCompose CPSPole)).
  Notation bidual := (fun X => dual (dual X)).
  Notation tridual := (fun X => dual (dual (dual X))).

  Notation "x ⊓ y" := (glb x y) (at level 50, no associativity).
  Notation "x ⊔ y" := (lub x y) (at level 50, no associativity).

  Infix "⊛" := (fun X Y => tensor (MComposes CPSCompose) Y X) (at level 59).
  Infix "⅋" := (par CPSCompose CPSPole) (at level 59).
  Notation "❗ A" := (bang CPSExp A) (at level 40, no associativity).
  Notation "❓ A" := (whynot CPSCompose CPSPole CPSExp A) (at level 40, no associativity).

  Section Formula_Interpretation.

    Reserved Notation "'⟦' A '⟧'" (at level 49).
    Variable perm_bool : bool.
    Variable mix0_bool : bool.
    Variable mix2_bool : bool.
    Variable PS : CPhaseSpace perm_bool mix0_bool mix2_bool.
    Variable v : Atom -> CWeb -> Type.

    Instance CL0 : ClosureOp := bidualCL CPScommute.

    Fixpoint Form_sem f :=
      match f with
      | var x => v x
      | covar x => dual (v x)
      | one => unit CPSUnit
      | bot => CPSPole
      | formulas.zero => closure_operators.zero
      | formulas.top => closure_operators.top
      | tens a b => ⟦a⟧ ⊛ ⟦b⟧
      | parr a b => ⟦a⟧ ⅋ ⟦b⟧
      | aplus a b => ⟦a⟧ ⊔ ⟦b⟧
      | awith a b => ⟦a⟧ ⊓ ⟦b⟧
      | oc a => ❗⟦a⟧
      | wn a => ❓⟦a⟧
      end
    where "⟦ a ⟧" := (Form_sem a).

    Definition list_Form_presem ll := fold_right (MComposes CPSCompose) (sg CPSUnit)
                                                           (map (fun x => dual (Form_sem x)) ll).

    Fact list_Form_presem_nil : list_Form_presem nil = (sg CPSUnit).
    Proof. auto. Qed.

    Fact list_Form_presem_cons f ll :
      list_Form_presem (f::ll) = MComposes CPSCompose (dual (⟦f⟧)) (list_Form_presem ll).
    Proof. auto. Qed.

  End Formula_Interpretation.

  Class CPhaseModel (P : pfrag) := {
    CPMPS : CPhaseSpace (pperm P) (pmix0 P) (pmix2 P);
    CPMval : Atom -> CWeb -> Type;
    CPMval_closed : forall x, (@cl _ (bidualCL CPScommute)) (CPMval x) ⊆ CPMval x;
(* TODO
    PMgax : forall a, list_Form_sem PMPS PMval (fst (projT2 (ipgax P) a))
                    ⊆ Form_sem PMPS PMval (snd (projT2 (ipgax P) a))
*)
  }.



  Section Soundness.

    Context { P : pfrag }.
    Variable PM : CPhaseModel P.

    Instance PS : CPhaseSpace (pperm P) (pmix0 P) (pmix2 P) := CPMPS.
    Instance CL : ClosureOp := bidualCL CPScommute.

    Infix "∘" := (MComposes CPSCompose) (at level 50, no associativity).
    Notation "'fact' X" := (cl X ⊆ X) (at level 50).

    Notation "'⟦' A '⟧'" := (@Form_sem (pperm P) (pmix0 P) (pmix2 P) _ CPMval A) (at level 49).
    Notation "⟬߭  ll ⟭" := (@list_Form_presem (pperm P) (pmix0 P) (pmix2 P) _ CPMval ll) (at level 49).

    Hint Resolve (@dual_is_fact _ CPSCompose CPSPole CPScommute)
                 (@cl_increase _ CL)
                 CPScommute CPSassociative_l CPSassociative_r CPSassociative_ll CPSassociative_lr
                 CPSneutral_1 CPSneutral_2 CPSneutral_l_1 CPSneutral_l_2 CPSneutral_r_1 CPSneutral_r_2
                 (@stability_l _ _ _ CPScommute CPSassociative_l CPSassociative_r)
                 (@stability_r _ _ _ CPScommute CPSassociative_l CPSassociative_r)
                 CPSsub_monoid_1 CPSsub_monoid_2 CPSsub_J.

    Lemma CPSfact_pole : cl CPSPole ⊆ CPSPole.
    Proof. eapply fact_pole; auto. Qed.

    Hint Resolve CPSfact_pole.

    Lemma cl_is_bidual X : cl X ≃ dual (dual X).
    Proof. reflexivity. Qed.

    Lemma bidual_increase X : X ⊆ dual (dual X).
    Proof. apply (@cl_increase _ CL). Qed.

    Lemma bidual_subset X Y : X ⊆ dual (dual Y) -> dual (dual X) ⊆ dual (dual Y).
    Proof.
    intros Hc.
    etransitivity; [ apply cl_is_bidual | ].
    transitivity (cl Y) ; [ | apply cl_is_bidual ].
    apply cl_subset; assumption.
    Qed.

    Lemma fact_sem : forall A, fact (⟦A⟧).
    Proof.
    induction A; try apply (@dual_is_fact _ CPSCompose CPSPole CPScommute); auto.
    - apply CPMval_closed.
    - simpl; unfold closure_operators.top; intros x Hx; auto.
    - apply (closed_glb IHA1 IHA2).
    Qed.

    Hint Resolve cl_is_bidual bidual_increase bidual_subset fact_sem.

    Lemma Form_sem_dual A : ⟦formulas.dual A⟧ ≃ dual (⟦A⟧).
    Proof.
    induction A; try reflexivity.
    - split; simpl; auto.
      apply CPMval_closed.
    - etransitivity; [ | apply tridual_eq ]; auto.
      apply pole_as_bot; auto.
    - apply ldual_eq; symmetry ; apply pole_as_bot; auto.
    - transitivity (dual (dual (⟦ formulas.dual (tens A1 A2) ⟧))).
      + split; auto; try apply fact_sem.
      + simpl; apply ldual_eq; symmetry.
        etransitivity; [ apply (@tensor_as_par _ _ _ CPScommute) | ]; auto.
        do 2 apply ldual_eq.
        apply MComposes_compat; apply ldual_eq; symmetry; assumption.
    - simpl; etransitivity; [ apply (@tensor_as_par _ _ _ CPScommute) | ]; auto.
      do 2 apply ldual_eq.
      apply MComposes_compat; (etransitivity; [ | eassumption ]);
        split; auto; apply fact_sem.
    - transitivity (dual (dual (⟦ formulas.dual formulas.zero ⟧))).
      + split; auto; apply fact_sem.
      + simpl.
        do 2 apply ldual_eq.
        split; intros x Hx; [ intros y Hy; contradiction Hy | constructor ].
    - apply ldual_eq.
      split; intros x Hx; [ constructor | intros y Hy; contradiction Hy ].
    - split.
      + transitivity (dual (fun z => ((⟦ A1 ⟧) z + (⟦ A2 ⟧) z)%type)).
        * intros x Hx y Hy; inversion Hx; destruct Hy.
          apply IHA1 in X; apply X; auto.
          apply IHA2 in X0; apply X0; auto.
        * etransitivity; [ apply cl_increase | ].
          do 2 apply lmonot; reflexivity.
      + simpl; apply glb_in; (etransitivity; [ | apply fact_sem ]); do 2 apply lmonot.
        * symmetry in IHA1; etransitivity; [ | apply IHA1 ]; apply lmonot.
          intros H; left; auto.
        * symmetry in IHA2; etransitivity; [ | apply IHA2 ]; apply lmonot.
          intros H; right; auto.
    - simpl; apply ldual_eq.
      split; intros x Hx.
      + constructor; apply fact_sem.
        * assert (dual (⟦ formulas.dual A1 ⟧) ⊆ cl (⟦ A1 ⟧)) as IHA1'
            by (apply ldual_eq; symmetry ; apply IHA1).
          apply IHA1'.
          intros y Hy; apply Hx; left; assumption.
        * assert (dual (⟦ formulas.dual A2 ⟧) ⊆ cl (⟦ A2 ⟧)) as IHA2'
            by (apply ldual_eq; symmetry ; apply IHA2).
          apply IHA2'.
          intros y Hy; apply Hx; right; assumption.
      + inversion Hx; intros y Hy; destruct Hy.
        * apply IHA1 in f; apply CPScommute; apply f; auto.
        * apply IHA2 in f; apply CPScommute; apply f; auto.
    - transitivity (dual (dual (⟦ formulas.dual (oc A) ⟧))).
      + split; auto; apply fact_sem.
      + simpl.
        apply ldual_eq.
        symmetry; etransitivity; [ apply (@bang_as_whynot _ _ _ CPScommute) | ]; auto.
        do 2 apply ldual_eq.
        destruct IHA as [IHA1 IHA2].
        split; intros x [Hx1 Hx2]; split; auto.
        * eapply lmonot in IHA1; apply IHA1; auto.
        * eapply lmonot in IHA2 ; apply IHA2; auto.
    - simpl; etransitivity; [ apply (@bang_as_whynot _ _ _ CPScommute) | ]; auto.
        do 2 apply ldual_eq.
        destruct IHA as [IHA1 IHA2].
        split; intros x [Hx1 Hx2]; split; auto.
        * apply IHA1; apply fact_sem; auto.
        * apply IHA2 in Hx2; intros y Hy.
          apply CPScommute; auto.
    Qed.

    Lemma dualsem : forall A, dual (⟦A⟧) ⊆ CPSPole -> ⟦A⟧ CPSUnit.
    Proof. intros A Hd; apply fact_sem; apply pole_vs_one; auto ; assumption. Qed.

    Fact list_Form_presem_app_1 ll mm : cl (⟬߭  ll++mm ⟭) ⊆ cl (⟬߭  ll ⟭ ∘ ⟬߭  mm ⟭).
    Proof.
    induction ll as [ | f ll IHll ]; simpl app; auto.
    - etransitivity; [ apply neutral_l_1_g | ]; auto.
      apply cl_subset.
      apply stability_r; auto.
    - rewrite 2 list_Form_presem_cons.
      etransitivity; [ | eapply cl_subset; apply associative_1 ]; auto.
      transitivity (cl (dual (⟦ f ⟧) ∘ cl (⟬߭  ll ⟭ ∘ ⟬߭  mm ⟭))).
      + apply cl_subset; etransitivity; [ | apply cl_increase ].
        apply MComposes_monotone; try reflexivity.
        apply subset_cl; assumption.
      + apply cl_subset.
        apply stability_r; auto.
    Qed.

    Fact list_Form_presem_app_pole_1 ll mm X : fact X -> ⟬߭  ll ⟭ ∘ ⟬߭  mm ⟭ ⊆ X -> ⟬߭  ll++mm ⟭ ⊆ X.
    Proof.
    intros HF Hc.
    etransitivity; [ | apply HF].
    apply subset_cl.
    etransitivity; [ apply list_Form_presem_app_1 | ].
    apply cl_subset.
    etransitivity; [ eassumption | apply cl_increase ].
    Qed.

    Fact list_Form_presem_app_2 ll mm : cl (⟬߭  ll ⟭ ∘ ⟬߭  mm ⟭) ⊆ cl (⟬߭  ll++mm ⟭).
    Proof.
    induction ll as [ | f ll IHll ]; simpl app; auto.
    - apply cl_subset; apply neutral_l_2_g; auto.
    - rewrite 2 list_Form_presem_cons.
      etransitivity; [ eapply cl_subset; apply associative_2 | ]; auto.
      transitivity (cl (dual (⟦ f ⟧) ∘ cl (⟬߭  ll ⟭ ∘ ⟬߭  mm ⟭))).
      + apply cl_subset; etransitivity; [ | apply cl_increase ].
        apply MComposes_monotone; try reflexivity.
        apply cl_increase.
      + apply cl_subset.
        etransitivity; [ | apply stability_r ]; auto.
        apply MComposes_monotone; try reflexivity; assumption.
    Qed.

    Fact list_Form_presem_app_pole_2 ll mm X : fact X -> ⟬߭  ll++mm ⟭ ⊆ X -> ⟬߭  ll ⟭ ∘ ⟬߭  mm ⟭ ⊆ X.
    Proof.
    intros HF Hc.
    etransitivity; [ | apply HF].
    apply subset_cl.
    etransitivity; [ apply list_Form_presem_app_2 | ].
    apply cl_subset.
    etransitivity; [ eassumption | apply cl_increase ].
    Qed.

    Fact list_Form_sem_bang ll : cl (⟬߭ ⁇ll ⟭) ≃ ❗ (lcap (map (fun x => (dual (⟦x⟧))) ll)).
    Proof.
    unfold list_Form_presem.
    assert (Forall_Type (fun x => fact x) (map (fun x => (dual (⟦x⟧))) ll)) as Hll
      by (induction ll as [ | y ll IHll ]; constructor; auto).
    eapply eqset_trans
      with (2 := @ltimes_store _ _ _ _ _ _ CPSUnit _ _ _ CPSsub_monoid_1 CPSsub_monoid_2 CPSsub_J _ _).
    rewrite 2 map_map.
    clear Hll.
    induction ll as [ | a ll [IHll1 IHll2] ]; simpl; try reflexivity.
    split.
    - do 2 apply lmonot; apply MComposes_monotone; try reflexivity.
      etransitivity; [ apply cl_increase | apply IHll1 ].
    - apply bidual_subset.
      etransitivity; [ | apply stability_r ]; auto.
      apply MComposes_monotone; auto; reflexivity.
    Unshelve. all: auto.
    + apply neutral_l_2_g; auto.
    + apply neutral_r_2_g; auto.
    Qed.


    Hypothesis Pgax : projT1 (pgax P) -> False.

    Theorem ll_soundness l : ll P l -> ⟬߭  l ⟭  ⊆ CPSPole.
    Proof.
    induction 1.
    - etransitivity; [ apply associative_1 | ]; auto.
      apply cl_closed; auto.
      etransitivity; [ apply neutral_r_2_g | ]; auto.
      apply cl_closed; auto.
      apply diag_pole.
    - assert ({ bp & pperm P = bp }) as [bp Heq] by (exists (pperm P); reflexivity).
      rewrite Heq in p; clear - p IHX Heq.
      case_eq bp; intros HP; rewrite HP in p; simpl in p.
      + revert IHX.
        apply (Permutation_Type_morph_transp (fun x => ⟬߭  x ⟭ ⊆ CPSPole)); auto.
        clear l1 l2 p; intros a b l1 l2 Hp.
        apply list_Form_presem_app_pole_2 in Hp; auto.
        apply list_Form_presem_app_pole_1; auto.
        intros x Hx; inversion Hx; inversion X0; inversion X2.
        apply CPScommute; apply CPSassociative_lr; apply CPSassociative_l.
        apply CPSfcommute ; [ rewrite Heq, HP; reflexivity | ].
        apply CPSassociative_r; apply CPSassociative_ll; apply CPScommute.
        apply Hp.
        do 3 (constructor; auto).
      + inversion p; subst.
        apply list_Form_presem_app_pole_2 in IHX; auto.
        apply list_Form_presem_app_pole_1; auto.
        apply commute_pole; auto; assumption.
    - apply list_Form_presem_app_pole_2 in IHX; auto.
      apply commute_pole in IHX; apply compose_adj_l in IHX; auto.
      apply list_Form_presem_app_pole_2 in IHX; auto.
      apply compose_adj_r in IHX.
      apply list_Form_presem_app_pole_1; auto.
      apply commute_pole; auto; apply compose_adj_r.
      apply list_Form_presem_app_pole_1; auto.
      apply compose_adj_l; auto.
      apply cl_closed in IHX; auto.
      etransitivity; [ | apply IHX ].
      etransitivity; [ | apply stability_l ]; auto.
      apply MComposes_monotone; try reflexivity.
      etransitivity; [ | apply stability_l ]; auto.
      apply MComposes_monotone; try reflexivity.
      apply subset_cl.
      etransitivity; [ | apply list_Form_sem_bang ].
      etransitivity; [ apply list_Form_sem_bang | ].
      apply store_monotone.
      symmetry in p.
      intros x.
      apply (@Permutation_Type_morph_transp _ (fun l => lcap (map (fun A => dual (⟦ A ⟧)) l) x)); auto.
      intros A B L1 L2.
      revert A B L2 x.
      induction L1; intros A B L2; simpl.
      + apply glb_in.
        * etransitivity; [ apply glb_out_r | apply glb_out_l ].
        * apply glb_in; [ apply glb_out_l | ].
          etransitivity; [ apply glb_out_r | apply glb_out_r ].
      + apply glb_in; [ apply glb_out_l | ].
        etransitivity; [ apply glb_out_r | intros x; apply IHL1 ].
    - intros x Hx; rewrite <- Hx.
      apply CPSmix0; assumption.
    - apply list_Form_presem_app_pole_1; auto.
      etransitivity; [ | apply CPSmix2 ]; auto.
      apply MComposes_monotone; assumption.
    - rewrite list_Form_presem_cons.
      etransitivity; [ apply neutral_r_2_g | ]; auto.
      apply cl_closed; auto.
      etransitivity; [ | apply pole_as_bot ]; auto.
      apply lmonot; apply cl_increase.
    - rewrite list_Form_presem_cons.
      transitivity (⟦ one ⟧ ∘ ⟬߭  l ⟭).
      + apply MComposes_monotone; auto; try reflexivity.
        apply lmonot; apply pole_as_bot; simpl; auto.
      + assert (sg CPSUnit ∘ ⟬߭  l ⟭ ⊆ cl CPSPole) as H.
        { etransitivity; [ apply neutral_l_2_g | ]; auto.
          do 2 apply lmonot; assumption. }
        etransitivity; [ | apply CPSfact_pole ].
        apply cl_subset in H.
        etransitivity; [ | apply H ].
        transitivity (cl(sg CPSUnit) ∘ ⟬߭  l ⟭); [ | apply stability_l ]; auto.
        apply MComposes_monotone; reflexivity.
    - apply compose_adj_l in IHX1; apply compose_adj_l in IHX2; auto.
      apply compose_adj_r.
      apply lmonot.
      apply list_Form_presem_app_pole_1; auto.
      etransitivity; [ | apply cl_increase ].
      apply MComposes_monotone; 
        (etransitivity; [ | apply fact_sem ]);
        apply subset_cl; apply lmonot; assumption.
    - rewrite list_Form_presem_cons; rewrite 2 list_Form_presem_cons in IHX.
      transitivity (cl ((dual (⟦ A ⟧) ∘ dual (⟦ B ⟧)) ∘ ⟬߭  l ⟭)).
      + etransitivity; [ | apply stability_l ]; auto.
        apply MComposes_monotone; try reflexivity.
      + apply cl_closed in IHX; auto.
        etransitivity ; [ | apply IHX ].
        apply cl_subset.
        apply associative_2; auto.
    - rewrite list_Form_presem_cons; simpl.
      intros x Hx; inversion Hx; apply X; constructor.
    - rewrite list_Form_presem_cons; rewrite list_Form_presem_cons in IHX.
      etransitivity ; [ | apply IHX ].
      apply MComposes_monotone; try reflexivity.
      apply lmonot.
      etransitivity ; [ | apply cl_increase].
      intros x Hx; left; auto.
    - rewrite list_Form_presem_cons; rewrite list_Form_presem_cons in IHX.
      etransitivity ; [ | apply IHX ].
      apply MComposes_monotone; try reflexivity.
      apply lmonot.
      etransitivity ; [ | apply cl_increase].
      intros x Hx; right; auto.
    - rewrite list_Form_presem_cons in IHX1; rewrite list_Form_presem_cons in IHX2;
        rewrite list_Form_presem_cons.
      apply compose_adj_l in IHX1; apply compose_adj_l in IHX2; auto.
      apply compose_adj_r.
      apply lmonot.
      simpl; apply glb_in; (etransitivity; [ | apply fact_sem ]);
        apply subset_cl; apply lmonot; assumption.
    - rewrite list_Form_presem_cons in IHX; rewrite list_Form_presem_cons.
      apply commute_pole in IHX; auto.
      apply commute_pole; auto.
      apply compose_adj_l in IHX; auto; apply compose_adj_r.
      change (dual (dual (⟦ oc A ⟧))) with (cl (⟦ oc A ⟧)).
      apply subset_cl.
      etransitivity; [ | apply cl_increase ].
      etransitivity; [ apply list_Form_sem_bang | ].
      apply store_der; [ apply fact_sem | ].
      etransitivity; [ | apply fact_sem ].
      change (dual (dual (⟦ A ⟧))) with (cl (⟦ A ⟧)) in IHX.
      apply cl_subset in IHX.
      etransitivity; [ | apply IHX ].
      apply list_Form_sem_bang.
    - rewrite list_Form_presem_cons in IHX; rewrite list_Form_presem_cons.
      apply compose_adj_l in IHX; auto; apply compose_adj_r.
      etransitivity; [ | apply IHX ].
      apply lmonot; etransitivity; [ apply cl_increase | ]; apply lmonot.
      apply glb_out_r.
    - transitivity (cl (⟬߭  l ⟭)); [ | apply cl_closed ]; auto.
      transitivity (unit CPSUnit ∘ ⟬߭  l ⟭).
      + apply MComposes_monotone; try reflexivity.
        etransitivity; [ | apply cl_idempotent ].
        simpl; do 2 apply lmonot.
        intros x Hx; inversion Hx.
        apply CPSsub_J in X0.
        apply J_inc_unit in X0; assumption.
      + etransitivity; [ apply stability_l | ]; auto.
        apply cl_subset; apply neutral_l_2_g; auto.
    - rewrite list_Form_presem_cons; rewrite 2 list_Form_presem_cons in IHX.
      transitivity (cl ((⟦ oc (formulas.dual A) ⟧ ∘ ⟦ oc (formulas.dual A) ⟧) ∘ ⟬߭  l ⟭)).
      + etransitivity; [ | apply stability_l ]; auto.
        apply MComposes_monotone; try reflexivity.
        transitivity (⟦ formulas.dual (wn A) ⟧); [ apply Form_sem_dual | ].
        change (formulas.dual (wn A)) with (oc (formulas.dual A)).
        apply store_compose_idem with CPSUnit; auto.
        * apply MComposes_monotone.
        * apply neutral_l_2_g; auto.
        * apply neutral_r_2_g; auto.
        * apply CPSsub_J.
      + apply cl_closed in IHX; auto.
        etransitivity ; [ | apply IHX ].
        apply cl_subset.
        etransitivity ; [ | apply associative_2 ]; auto.
        apply MComposes_monotone; try reflexivity.
        change (oc (formulas.dual A)) with (formulas.dual (wn A)).
        apply MComposes_monotone; apply Form_sem_dual.
    - rewrite list_Form_presem_cons in IHX1; rewrite list_Form_presem_cons in IHX2.
      apply commute_pole in IHX1; apply commute_pole in IHX2; auto.
      apply compose_adj_l in IHX1; apply compose_adj_l in IHX2; auto.
      apply list_Form_presem_app_pole_1; auto.
      assert (⟬߭  l1 ⟭ ⊆ dual (dual (dual (⟦ A ⟧))))
        by (etransitivity; [ eassumption | ]; do 2 apply lmonot; apply Form_sem_dual).
      etransitivity; [ apply MComposes_monotone; eassumption | ].
      apply commute_pole; auto.
      apply diag_pole.
    - contradiction Pgax.
    Unshelve. all: auto.
    Qed.

  End Soundness.

End Phase_Spaces.

