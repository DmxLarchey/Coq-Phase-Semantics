(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)


Require Import List_Type Permutation_Type genperm_Type.

Require Export closure_operators.

Require Import ill_def.

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
Notation "'!' x" := (ioc x) (at level 52).
Definition ill_lbang := map ioc.
Notation "'!l' x" := (ill_lbang x) (at level 60, only parsing).
Notation "‼ x" := (ill_lbang x) (at level 52).
Notation "£" := ivar.
Notation "∅" := nil (only parsing).




Set Implicit Arguments.

Section Phase_Spaces.

  Notation "X '⊆' Y" := (subset X Y) (at level 75, format "X  ⊆  Y", no associativity).
  Notation "X '≃' Y" := (eqset X Y) (at level 75, format "X  ≃  Y", no associativity).
  Notation "A '∩' B" := (fun z => A z * B z : Type)%type (at level 50, format "A  ∩  B", left associativity).
  Notation "A '∪' B" := (fun z => A z + B z : Type)%type (at level 50, format "A  ∪  B", left associativity).

  Class PhaseSpace (b : bool) := {
    Web : Type;
    PSCL : @ClosureOp Web;
    PSCompose : Web -> Web -> Web -> Type;
    PSunit : Web;
    PSExp : Web -> Type;
    PScl_stable_l : cl_stability_l (Composes PSCompose);
    PScl_stable_r : cl_stability_r (Composes PSCompose);
    PScl_associative_1 : cl_associativity_1 PSCompose;
    PScl_associative_2 : cl_associativity_2 PSCompose;
    PScl_neutral_1 : cl_neutrality_1 PSCompose PSunit;
    PScl_neutral_2 : cl_neutrality_2 PSCompose PSunit;
    PScl_neutral_3 : cl_neutrality_3 PSCompose PSunit;
    PScl_neutral_4 : cl_neutrality_4 PSCompose PSunit;
    PSsub_monoid_1 : sub_monoid_hyp_1 PSunit PSExp;
    PSsub_monoid_2 : sub_monoid_hyp_2 (Composes PSCompose) PSExp;
    PSsub_J : sub_J_hyp (Composes PSCompose) PSunit PSExp;
    PScl_commute : b = true -> cl_commutativity PSCompose
  }.

  (* Interpretation of Linear Logic *)


  Infix "⊸" := (Magicwand_l PSCompose) (at level 51, right associativity).
  Infix "⟜" := (Magicwand_r PSCompose) (at level 52, left associativity).
  Infix "⊛" := (tensor (Composes PSCompose)) (at level 59).
  Notation "x ⊓ y" := (glb x y) (at level 50, no associativity).
  Notation "x ⊔ y" := (lub x y) (at level 50, no associativity).
  Notation "❗ A" := (bang PSExp A) (at level 40, no associativity).

  Section Formula_Interpretation.

    Reserved Notation "'⟦' A '⟧'" (at level 49).
    Variable perm_bool : bool.
    Variable PS : PhaseSpace perm_bool.
    Variable v : IAtom -> Web -> Type.
    Instance CL0 : ClosureOp := PSCL.

    Fixpoint Form_sem f :=
      match f with
      | 0     => zero
      | ⟙             => top
      | 𝝐              => unit PSunit
      | £ x    => v x
      | a -o b => ⟦a⟧ ⊸ ⟦b⟧
      | ineg a => ⟦a⟧ ⊸ v atN
      | b o- a => ⟦b⟧ ⟜ ⟦a⟧
      | igen a => v atN ⟜ ⟦a⟧
      | a ⊗ b  => ⟦a⟧ ⊛ ⟦b⟧
      | a ⊕ b  => ⟦a⟧ ⊔ ⟦b⟧
      | a & b  => ⟦a⟧ ⊓ ⟦b⟧
      | !a     => ❗⟦a⟧
      end
    where "⟦ a ⟧" := (Form_sem a).

    Definition list_Form_sem ll := fold_right (fun x y => x⊛y) (unit PSunit) (map Form_sem ll).

  End Formula_Interpretation.

  Class PhaseModel (P : ipfrag) := {
    PMPS : PhaseSpace (ipperm P);
    PMval : IAtom -> Web -> Type;
    PMval_closed : forall x, (@cl _ PSCL) (PMval x) ⊆ PMval x;
    PMgax : forall a, list_Form_sem PMPS PMval (fst (projT2 (ipgax P) a))
                    ⊆ Form_sem PMPS PMval (snd (projT2 (ipgax P) a))
  }.

  Context { P : ipfrag }.
  Variable PM : PhaseModel P.
  Instance PS : PhaseSpace (ipperm P) := PMPS.
  Instance CL : ClosureOp := PSCL.

  Hint Resolve (@PScl_stable_l (ipperm P) PS) (@PScl_stable_r (ipperm P) PS)
               (@PScl_associative_1 (ipperm P) PS) (@PScl_associative_2 (ipperm P) PS)
               (@PScl_neutral_1 (ipperm P) PS) (@PScl_neutral_2 (ipperm P) PS)
               (@PScl_neutral_3 (ipperm P) PS) (@PScl_neutral_4 (ipperm P) PS)
               (@PSsub_monoid_1 (ipperm P) PS) (@PSsub_monoid_2 (ipperm P) PS) (@PSsub_J (ipperm P) PS).
  Hint Resolve (@composes_monotone _ PSCompose)
               composes_associative_1 composes_associative_2 composes_commute_1
               composes_neutral_l_1 composes_neutral_l_2 composes_neutral_r_1 composes_neutral_r_2.


  Infix "∘" := (Composes PSCompose) (at level 50, no associativity).

  Notation closed := (fun x => cl x ⊆ x).
  Notation v := PMval.
  Notation Hv := PMval_closed.
  Notation PMForm_sem := (Form_sem PMPS PMval).
  Notation PMlist_Form_sem := (list_Form_sem PMPS PMval).
  Notation "'⟦' A '⟧'" := (PMForm_sem A) (at level 49).
  Notation "⟬߭  ll ⟭" := (PMlist_Form_sem ll) (at level 49).

  Fact closed_Form_sem f : cl (⟦f⟧) ⊆ ⟦f⟧.
  Proof.
    induction f; simpl.
    + apply Hv.
    + apply closed_unit.
    + apply closed_times.
    + apply closed_magicwand_r; auto.
    + apply closed_magicwand_r; auto.
      apply Hv.
    + apply closed_magicwand_l; auto.
    + apply closed_magicwand_l; auto.
      apply Hv.
    + apply closed_top.
    + apply closed_glb; auto.
    + apply closed_zero.
    + apply closed_lub; auto.
    + apply closed_store.
  Qed.

  Fact list_Form_sem_nil : ⟬߭nil⟭ = (unit PSunit).
  Proof. auto. Qed.

  Fact list_Form_sem_cons f ll : ⟬߭f::ll⟭  = ⟦f⟧ ⊛ ⟬߭ll⟭.
  Proof. auto. Qed.

  Fact closed_list_Form_sem ll : cl (⟬߭ll⟭) ⊆ ⟬߭ll⟭.
  Proof.
    unfold list_Form_sem; induction ll; simpl.
    + apply closed_unit.
    + apply closed_times.
  Qed.

  Hint Resolve closed_Form_sem closed_list_Form_sem.

  Fact list_Form_sem_app ll mm : ⟬߭ll++mm⟭ ≃ ⟬߭ll⟭ ⊛⟬߭mm⟭.
  Proof.
    induction ll as [ | f ll IHll ]; simpl app; auto.
    + apply eqset_sym, unit_neutral_l; auto.
    + apply (@eqset_trans _ _ (⟦f⟧ ⊛ ⟬߭ ll ++ mm ⟭)); try reflexivity.
      apply (@eqset_trans _ _ (⟦ f ⟧ ⊛ (⟬߭ ll ⟭ ⊛ ⟬߭ mm ⟭))).
      * apply times_congruence; auto.
        apply eqset_refl.
      * apply (@eqset_trans _ _ (⟦ f ⟧ ⊛ ⟬߭ ll ⟭ ⊛ ⟬߭ mm ⟭)).
        apply eqset_sym; apply times_associative; auto.
        apply times_congruence; auto; reflexivity.
  Qed.

  Fact list_Form_sem_congr_l ll mm pp : ⟬߭mm⟭ ≃ ⟬߭pp⟭  -> ⟬߭ll++mm⟭ ≃ ⟬߭ll++pp⟭.
  Proof.
    intros H.
    do 2 apply eqset_trans with (1 := list_Form_sem_app _ _), eqset_sym.
    apply times_congruence; auto; reflexivity.
  Qed.

  Fact list_Form_sem_congr_r ll mm pp : ⟬߭mm⟭ ≃ ⟬߭pp⟭  -> ⟬߭mm++ll⟭ ≃ ⟬߭pp++ll⟭.
  Proof.
    intros H.
    do 2 apply eqset_trans with (1 := list_Form_sem_app _ _), eqset_sym.
    apply times_congruence; auto; reflexivity.
  Qed.

  Fact list_Form_sem_mono_l ll mm pp : ⟬߭mm⟭ ⊆ ⟬߭pp⟭  -> ⟬߭ll++mm⟭ ⊆ ⟬߭ll++pp⟭.
  Proof.
    intros H.
    apply subset_trans with (⟬߭ll⟭ ⊛⟬߭mm⟭); [ apply list_Form_sem_app | ].
    apply subset_trans with (⟬߭ll⟭ ⊛⟬߭pp⟭); [ | apply list_Form_sem_app ].
    apply times_monotone; auto; reflexivity.
  Qed.

  Fact list_Form_sem_mono_r ll mm pp : ⟬߭mm⟭ ⊆ ⟬߭pp⟭  -> ⟬߭mm++ll⟭ ⊆ ⟬߭pp++ll⟭.
  Proof.
    intros H.
    apply subset_trans with (⟬߭mm⟭ ⊛⟬߭ll⟭); [ apply list_Form_sem_app | ].
    apply subset_trans with (⟬߭pp⟭ ⊛⟬߭ll⟭); [ | apply list_Form_sem_app ].
    apply times_monotone; auto; reflexivity.
  Qed.

  Fact list_Form_sem_bang ll : ⟬߭‼ll⟭ ≃ ❗ (lcap (map PMForm_sem ll)).
  Proof.
    unfold list_Form_sem.
    assert (Forall_Type closed (map PMForm_sem ll)) as Hll.
    { induction ll as [ | y ll IHll ].
      + constructor.
      + constructor; auto. }
    eapply eqset_trans with (2 := ltimes_store _ _ _ _ _ _ _ _ _).
    rewrite map_map.
    apply eq_eqset; clear Hll.
    induction ll as [ | a ll IHll ]; simpl; auto.
    rewrite IHll; auto.
    Unshelve. all: auto.
  Qed.

  (* All the rules of the ILL sequent calculus (including cut) are closed
     under relational phase semantics, hence we deduce the following
     soundness theorem *)

  Section soundness.

    Notation "l '⊢' x" := (ill P l x) (at level 70, no associativity).

    Fact ill_ax_sound a : ⟬߭a::nil⟭  ⊆ ⟦a⟧.
    Proof. intro; apply unit_neutral_r; auto. Qed.

    Fact ill_cut_sound Γ ϴ Δ a b : ⟬߭Γ⟭ ⊆ ⟦a⟧ -> ⟬߭Δ++a::ϴ⟭ ⊆ ⟦b⟧ -> ⟬߭Δ++Γ++ϴ⟭ ⊆ ⟦b⟧.
    Proof.
      intros H1 H2.
      apply subset_trans with (2 := H2).
      apply list_Form_sem_mono_l.
      apply subset_trans with (1 := fst (list_Form_sem_app _ _)).
      rewrite list_Form_sem_cons; apply times_monotone; auto; reflexivity.
    Qed.

    Fact ill_nc_swap_sound Γ Δ a b c : ⟬߭Γ++!a::!b::Δ⟭ ⊆ ⟦c⟧ -> ⟬߭Γ++!b::!a::Δ⟭ ⊆ ⟦c⟧.
    Proof.
      intros H x Hx; apply H; revert x Hx.
      apply list_Form_sem_congr_l.
      change (!a::!b::Δ) with (‼(a::b::nil)++Δ).
      change (!b::!a::Δ) with (‼(b::a::nil)++Δ).
      apply list_Form_sem_congr_r.
      do 2 apply eqset_trans with (1 := list_Form_sem_bang _), eqset_sym.
      apply store_congruence.
      simpl; split; red; tauto.
    Qed.

    Fact ill_co_oc_perm_sound l1 l2 lw lw' a : Permutation_Type lw lw' ->
             ⟬߭ l1 ++ map ioc lw ++ l2 ⟭ ⊆ ⟦ a ⟧ -> ⟬߭ l1 ++ map ioc lw' ++ l2 ⟭ ⊆ ⟦ a ⟧.
    Proof.
      intros HP; revert l1 l2; induction HP; intros l1 l2; auto.
      + replace (l1 ++ map ioc (x :: l) ++ l2) with ((l1 ++ ioc x :: nil) ++ map ioc l ++ l2)
          by (simpl; rewrite <- ? app_assoc; rewrite <- app_comm_cons; reflexivity).
        replace (l1 ++ map ioc (x :: l') ++ l2) with ((l1 ++ ioc x :: nil) ++ map ioc l' ++ l2)
          by (simpl; rewrite <- ? app_assoc; rewrite <- app_comm_cons; reflexivity).
        auto.
      + apply ill_nc_swap_sound.
    Qed.

    Fact ill_co_swap_sound (HPerm: ipperm P = true) Γ Δ a b c : ⟬߭Γ++a::b::Δ⟭ ⊆ ⟦c⟧ -> ⟬߭Γ++b::a::Δ⟭ ⊆ ⟦c⟧.
    Proof.
      intros H x Hx; apply H; revert x Hx.
      apply list_Form_sem_congr_l.
      change (a::b::Δ) with ((a::b::nil)++Δ).
      change (b::a::Δ) with ((b::a::nil)++Δ).
      apply list_Form_sem_congr_r.
      repeat rewrite list_Form_sem_cons.
      repeat rewrite list_Form_sem_nil.
      eapply eqset_trans.
      apply times_commute; apply composes_commute_1 ; apply PScl_commute; auto.
      apply times_congruence; auto.
      + apply unit_neutral_r; auto.
      + apply eqset_sym, unit_neutral_r; auto.
    Qed.

    Fact ill_perm_sound Γ Δ a : Γ ~[ipperm P] Δ -> ⟬߭Γ⟭ ⊆ ⟦a⟧ -> ⟬߭Δ⟭ ⊆ ⟦a⟧.
    Proof.
      assert ({ipperm P = true} + {ipperm P = false}) as Hbool
        by (clear; destruct (ipperm P); [ left | right ]; reflexivity).
      destruct Hbool as [Hbool | Hbool]; intros.
      * rewrite Hbool in X.
        revert X a X0.
        induction 1 as [ | a Ga De H1 IH1 | | ] ; intros c; auto.
        + repeat rewrite list_Form_sem_cons.
          intros H; apply adjunction_l_2; auto.
          apply IH1 with (a := a -o c); simpl. 
          apply adjunction_l_1; auto.
        + apply ill_co_swap_sound with (Γ := nil) ; assumption.
      * rewrite Hbool in X; simpl in X; subst; assumption.
    Qed.

    Fact ill_limp_l_sound Γ ϴ Δ a b c :  ⟬߭Γ⟭ ⊆ ⟦a⟧ -> ⟬߭ϴ++b::Δ⟭ ⊆ ⟦c⟧ -> ⟬߭ϴ++Γ++a -o b::Δ⟭ ⊆ ⟦c⟧.
    Proof.
      intros H1 H2 x Hx; apply H2; revert x Hx.
      apply list_Form_sem_mono_l.
      change (b::Δ) with ((b::nil)++Δ).
      replace (Γ++a -o b::Δ) with ((Γ++a -o b::nil)++Δ).
      2: rewrite app_ass; auto.
      apply list_Form_sem_mono_r.
      apply subset_trans with (1 := fst (list_Form_sem_app _ _)).
      apply subset_trans with (⟬߭Γ⟭ ⊛ (⟦ a ⟧ ⊸ ⟦ b ⟧)).
      * apply times_congruence; auto; try reflexivity.
        rewrite list_Form_sem_cons, list_Form_sem_nil. 
        apply eqset_sym, unit_neutral_r; auto.
        apply closed_magicwand_l; auto.
      * apply subset_trans with (⟦b⟧).
        apply adjunction_l; auto; try reflexivity.
        apply magicwand_l_monotone; auto; reflexivity.
        rewrite list_Form_sem_cons, list_Form_sem_nil.
        apply unit_neutral_r; auto.
    Qed.

    Fact ill_neg_l_sound Γ a :  ⟬߭Γ⟭ ⊆ ⟦a⟧ -> ⟬߭Γ++ineg a::nil⟭ ⊆ ⟦N⟧.
    Proof.
      intros H.
      replace (⟬߭ Γ ++ ineg a :: nil ⟭) with (⟬߭ nil ++ Γ ++ a -o N :: nil⟭)
        by (unfold list_Form_sem; rewrite ? map_app; simpl; reflexivity).
      apply ill_limp_l_sound; auto.
      unfold list_Form_sem; simpl; apply unit_neutral_r_1; auto.
      apply Hv.
    Qed.

    Fact ill_rimp_l_sound Γ ϴ Δ a b c :  ⟬߭Γ⟭ ⊆ ⟦a⟧ -> ⟬߭ϴ++b::Δ⟭ ⊆ ⟦c⟧ -> ⟬߭ϴ++b o- a::Γ++Δ⟭ ⊆ ⟦c⟧.
    Proof.
      intros H1 H2 x Hx; apply H2; revert x Hx.
      apply list_Form_sem_mono_l.
      change (b::Δ) with ((b::nil)++Δ).
      change (b o- a::Γ++Δ) with ((b o- a::Γ)++Δ).
      apply list_Form_sem_mono_r.
      do 2 rewrite list_Form_sem_cons.
      rewrite list_Form_sem_nil.
      apply subset_trans with (⟦ b ⟧).
      2: apply unit_neutral_r; auto.
      apply adjunction_r; auto.
      apply magicwand_r_monotone; auto; reflexivity.
    Qed.

    Fact ill_gen_l_sound Γ a :  ⟬߭Γ⟭ ⊆ ⟦a⟧ -> ⟬߭igen a::Γ⟭ ⊆ ⟦N⟧.
    Proof.
      intros H.
      replace (⟬߭ igen a :: Γ ⟭) with (⟬߭ nil ++ N o- a :: Γ ++ nil⟭)
        by (unfold list_Form_sem; simpl; rewrite app_nil_r; reflexivity).
      apply ill_rimp_l_sound; auto.
      unfold list_Form_sem; simpl; apply unit_neutral_r_1; auto.
      apply Hv.
    Qed.

    Fact ill_limp_r_sound Γ a b : ⟬߭a::Γ⟭ ⊆ ⟦b⟧ -> ⟬߭Γ⟭ ⊆ ⟦a⟧ ⊸ ⟦b⟧.
    Proof. intro; apply adjunction_l; auto. Qed.

    Fact ill_neg_r_sound Γ a : ⟬߭a::Γ⟭ ⊆ ⟦N⟧ -> ⟬߭Γ⟭ ⊆ ⟦ineg a⟧.
    Proof.
      simpl; change (v atN) with (⟦ivar atN⟧).
      apply ill_limp_r_sound; auto.
    Qed.

    Fact ill_rimp_r_sound Γ a b : ⟬߭Γ++a::nil⟭ ⊆ ⟦b⟧ -> ⟬߭Γ⟭ ⊆ ⟦b⟧ ⟜ ⟦a⟧.
    Proof.
      intros H.
      apply adjunction_r; auto.
      apply subset_trans with (2 := H).
      apply subset_trans with (2 := snd (list_Form_sem_app _ _)).
      apply times_monotone; auto; try reflexivity.
      rewrite list_Form_sem_cons, list_Form_sem_nil.
      apply unit_neutral_r; auto.
    Qed.

    Fact ill_gen_r_sound Γ a : ⟬߭Γ++a::nil⟭ ⊆ ⟦N⟧ -> ⟬߭Γ⟭ ⊆ ⟦igen a⟧.
    Proof.
      simpl; change (v atN) with (⟦ivar atN⟧).
      apply ill_rimp_r_sound; auto.
    Qed.

    Fact ill_with_l1_sound Γ Δ a b c : ⟬߭Γ++a::Δ⟭ ⊆ ⟦c⟧ -> ⟬߭Γ++a ﹠ b::Δ⟭ ⊆ ⟦c⟧.
    Proof.
      intros H.
      apply subset_trans with (2 := H).
      apply list_Form_sem_mono_l, times_monotone; auto; try reflexivity.
      simpl; red; unfold glb; tauto.
    Qed.

    Fact ill_with_l2_sound Γ Δ a b c : ⟬߭Γ++b::Δ⟭ ⊆ ⟦c⟧ -> ⟬߭Γ++a ﹠ b::Δ⟭ ⊆ ⟦c⟧.
    Proof.
      intros H.
      apply subset_trans with (2 := H).
      apply list_Form_sem_mono_l, times_monotone; auto; try reflexivity.
      simpl; red; unfold glb; tauto.
    Qed.

    Fact ill_with_r_sound Γ a b : ⟬߭Γ⟭ ⊆ ⟦a⟧ -> ⟬߭Γ⟭ ⊆ ⟦b⟧ -> ⟬߭Γ⟭ ⊆ ⟦a﹠b⟧.
    Proof. intros; simpl; red; unfold glb; auto. Qed.

    Fact ill_bang_l_sound Γ Δ a b : ⟬߭Γ++a::Δ⟭ ⊆ ⟦b⟧ -> ⟬߭Γ++!a::Δ⟭ ⊆ ⟦b⟧.
    Proof.
      intros H.
      apply subset_trans with (2 := H).
      apply list_Form_sem_mono_l, times_monotone; auto; try reflexivity.
      apply store_dec; auto.
    Qed.

    Fact ill_bang_r_sound Γ a : ⟬߭‼Γ⟭ ⊆ ⟦ a ⟧ -> ⟬߭‼Γ⟭ ⊆ ❗⟦a⟧.
    Proof.
      intros H x Hx.
      apply list_Form_sem_bang in Hx; revert x Hx.
      apply store_der; auto.
      intros x Hx; apply H, list_Form_sem_bang; auto.
    Qed.

    Fact ill_weak_sound Γ Δ a b : ⟬߭Γ++Δ⟭ ⊆ ⟦b⟧ -> ⟬߭Γ++!a::Δ⟭ ⊆ ⟦b⟧.
    Proof.
      intros H.
      apply subset_trans with (2 := H), list_Form_sem_mono_l.
      apply subset_trans with (unit PSunit ⊛ ⟬߭Δ⟭).
      * apply times_monotone; simpl; auto; try reflexivity.
        apply (@store_inc_unit _ _ (Composes PSCompose)); auto.
      * apply unit_neutral_l; auto.
    Qed.

    Fact ill_cntr_sound Γ Δ a b : ⟬߭Γ++!a::!a::Δ⟭ ⊆ ⟦b⟧ -> ⟬߭Γ++!a::Δ⟭ ⊆ ⟦b⟧.
    Proof.
      intros H.
      apply subset_trans with (2 := H), list_Form_sem_mono_l.
      change (!a::Δ) with (‼(a::nil)++Δ) at 1.
      change (!a::!a::Δ) with (‼(a::a::nil)++Δ).
      apply list_Form_sem_mono_r.
      apply subset_trans with (1 := fst (list_Form_sem_bang _)).
      apply subset_trans with (2 := snd (list_Form_sem_bang _)).
      apply store_monotone; simpl; red; tauto.
    Qed.

    Fact ill_times_l_sound Γ Δ a b c : ⟬߭Γ++a::b::Δ⟭ ⊆ ⟦c⟧ -> ⟬߭Γ++a⊗b::Δ⟭ ⊆ ⟦c⟧.
    Proof.
      intros H.
      apply subset_trans with (2 := H), list_Form_sem_mono_l.
      do 3 rewrite list_Form_sem_cons.
      apply times_associative; auto.
    Qed.

    Fact ill_times_r_sound Γ Δ a b : ⟬߭Γ⟭ ⊆ ⟦a⟧ -> ⟬߭Δ⟭ ⊆ ⟦b⟧ -> ⟬߭Γ++Δ⟭ ⊆ ⟦a⟧⊛⟦b⟧.
    Proof. 
      intros ? ?.
      apply subset_trans with (1 := fst (list_Form_sem_app _ _)).
      apply times_monotone; auto.
    Qed.

    Fact ill_plus_l_sound Γ Δ a b c : ⟬߭Γ++a::Δ⟭ ⊆ ⟦c⟧ -> ⟬߭Γ++b::Δ⟭ ⊆ ⟦c⟧ -> ⟬߭Γ++a⊕b::Δ⟭ ⊆ ⟦c⟧.
    Proof.
      intros H1 H2.
      apply subset_trans with ((⟬߭Γ⟭ ⊛(⟦a⟧⊛⟬߭Δ⟭)) ⊔ (⟬߭Γ⟭ ⊛(⟦b⟧⊛⟬߭Δ⟭))).
      2: { apply lub_out; auto.
           * apply subset_trans with (2 := H1).
             apply subset_trans with (2 := snd (list_Form_sem_app _ _)).
             apply times_monotone; auto; reflexivity.
           * apply subset_trans with (2 := H2).
             apply subset_trans with (2 := snd (list_Form_sem_app _ _)).
             apply times_monotone; auto; reflexivity. }
      apply subset_trans with (1 := fst (list_Form_sem_app _ _)).
      rewrite list_Form_sem_cons.
      eapply subset_trans; [ | apply times_lub_distrib_r ]; auto.
      apply times_monotone; auto; try reflexivity.
      apply times_lub_distrib_l; auto.
    Qed.

    Fact ill_plus_r1_sound Γ a b : ⟬߭Γ⟭ ⊆ ⟦a⟧ -> ⟬߭Γ⟭ ⊆ ⟦a⊕b⟧.
    Proof. intros ? ? ?; simpl; apply cl_increase; auto. Qed.

    Fact ill_plus_r2_sound Γ a b : ⟬߭Γ⟭ ⊆ ⟦b⟧ -> ⟬߭Γ⟭ ⊆ ⟦a⊕b⟧.
    Proof. intros ? ? ?; simpl; apply cl_increase; auto. Qed.

    Fact ill_zero_l_sound Γ Δ a : ⟬߭Γ++0::Δ⟭ ⊆ ⟦a⟧.
    Proof.
      intros x Hx.
      apply list_Form_sem_app in Hx.
      rewrite list_Form_sem_cons in Hx.
      apply zero_least; auto.
      apply times_zero_distrib_r with (Compose := PSCompose) (A := ⟬߭Γ⟭); auto.
      revert x Hx; apply times_monotone; auto; try reflexivity.
      apply times_zero_distrib_l; auto.
    Qed.

    Fact ill_top_r_sound Γ : ⟬߭Γ⟭ ⊆ ⟦⟙⟧.
    Proof. simpl; red; unfold top; auto. Qed.

    Fact ill_unit_l_sound Γ Δ a : ⟬߭Γ++Δ⟭ ⊆ ⟦a⟧ -> ⟬߭Γ++𝝐::Δ⟭ ⊆ ⟦a⟧.
    Proof.
      intros H.
      apply subset_trans with (2 := H), list_Form_sem_mono_l.
      apply unit_neutral_l; auto.
    Qed.

    Fact ill_unit_r_sound : ⟬߭nil⟭ ⊆ ⟦𝝐⟧.
    Proof. simpl; red; auto. Qed.

    Notation "l '⊢' x" := (ill P l x) (at level 70, no associativity).

    Hint Resolve ill_ax_sound
                 ill_limp_l_sound ill_limp_r_sound ill_rimp_l_sound ill_rimp_r_sound
                 ill_gen_r_sound ill_gen_l_sound ill_neg_r_sound ill_neg_l_sound
                 ill_with_l1_sound ill_with_l2_sound ill_with_r_sound
                 ill_bang_l_sound ill_bang_r_sound ill_weak_sound ill_cntr_sound
                 ill_times_l_sound ill_times_r_sound
                 ill_plus_l_sound ill_plus_r1_sound ill_plus_r2_sound
                 ill_zero_l_sound ill_top_r_sound 
                 ill_unit_l_sound ill_unit_r_sound.

    Theorem ill_soundness Γ a : Γ ⊢ a -> ⟬߭Γ⟭  ⊆ ⟦a⟧.
    Proof.
      induction 1; try auto ; try now (simpl; auto).
      + revert p IHX; apply ill_perm_sound.
      + apply ill_co_oc_perm_sound with (lw := lw); auto.
      + apply ill_cut_sound with A; auto.
      + apply PMgax.
    Qed.

  End soundness.

End Phase_Spaces.



