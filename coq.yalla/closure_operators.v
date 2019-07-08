(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import CRelationClasses CMorphisms.
Require Import List_Type.

Require Import utils_tac.

Set Implicit Arguments.

(* Notations for subset or subrel set theoretic operators *)

Section Subset.

  Context { M : Type }.

  Implicit Types A B : M -> Type.

  Definition subset A B := forall x, A x -> B x.
  Notation "X '⊆' Y" := (subset X Y) (at level 75, format "X  ⊆  Y", no associativity).

  Global Instance subset_refl : Reflexive subset := fun X a P => P.
  Global Instance subset_trans : Transitive subset := fun X Y Z P Q a H => Q a (P a H).
  Global Instance subset_preorder : PreOrder subset :=
    { PreOrder_Reflexive := subset_refl; PreOrder_Transitive := subset_trans }.

  Hint Resolve subset_refl subset_trans.

  Definition eqset A B := ((subset A B) * (subset B A))%type.
  Notation "X '≃' Y" := (eqset X Y) (at level 75, format "X  ≃  Y", no associativity).

  Global Instance eqset_refl : Reflexive eqset := fun X => (subset_refl X, subset_refl X).
  Global Instance eqset_sym : Symmetric eqset :=
    fun _ _ H => match H with (H1, H2) => (H2, H1) end.
  Global Instance eqset_trans : Transitive eqset :=
    fun _ _ _ P Q =>
    match P, Q with (P1,P2), (Q1,Q2) => (subset_trans P1 Q1, subset_trans Q2 P2) end.
  Global Instance eqset_equiv : Equivalence eqset :=
    { Equivalence_Reflexive := eqset_refl;
      Equivalence_Symmetric := eqset_sym;
      Equivalence_Transitive := eqset_trans }.

  Hint Resolve eqset_refl eqset_trans.
  Hint Immediate eqset_sym.

  Global Instance eq_eqset : Proper (eq ==> eqset) id.
  Proof. split; subst; apply eqset_refl. Qed.

  (* intersection and union *)

  Notation "A '∩' B" := (fun z => A z * B z : Type)%type (at level 50, format "A  ∩  B", left associativity).
  Notation "A '∪' B" := (fun z => A z + B z : Type)%type (at level 50, format "A  ∪  B", left associativity).



  (* equivalence at Type *)

  Notation "X '≡' Y" := ((X->Y)*(Y->X))%type (at level 80, format "X  ≡  Y", no associativity).

  (** ⊆ ≃ ∩ ∪ ≡ *)

  (* singleton *)

  Notation sg := (@eq _).

  Fact sg_subset A x : A x ≡ sg x ⊆ A.
  Proof.
    split.
    + intros ? ? []; trivial.
    + intros H; apply H; reflexivity. 
  Qed.


  (* Closure operators *)

  Section Closure_Operator.

    Class ClosureOp := {
      cl          : (M -> Type) -> (M -> Type);
      cl_increase : forall A, A ⊆ cl A;
      cl_monotone : forall A B, A ⊆ B -> cl A ⊆ cl B;
      cl_idempotent : forall A, cl (cl A) ⊆ cl A
    }.

    Context { CL : ClosureOp }.

    Proposition cl_prop A B : A ⊆ cl B ≡ cl A ⊆ cl B.
    Proof.
      split; intros H x Hx.
      apply cl_idempotent; revert Hx; apply cl_monotone; try assumption.
      apply H, cl_increase; assumption.
    Qed.

    Definition cl_subset { A B } := fst (cl_prop A B).
    Definition subset_cl { A B } := snd (cl_prop A B). 

    Fact cl_eqset A B : A ≃ B -> cl A ≃ cl B.
    Proof. intros []; split; apply cl_monotone; assumption. Qed.

    Notation closed := (fun x => cl x ⊆ x).

    Fact cl_closed A B : closed B -> A ⊆ B -> cl A ⊆ B.
    Proof.
      intros H1 H2.
      apply subset_trans with (2 := H1), cl_subset, 
            subset_trans with (1 := H2), cl_increase.
    Qed.

    (* Intersection and Union *)

    Definition glb A B := A ∩ B.
    Definition lub A B := cl (A ∪ B).
    Notation "x ⊓ y" := (glb x y) (at level 50, no associativity).
    Notation "x ⊔ y" := (lub x y) (at level 50, no associativity).

    Proposition closed_glb A B : closed A -> closed B -> closed (A ⊓ B).
    Proof.
      unfold glb; simpl; intros HA HB x Hx; split; 
        [ apply HA | apply HB ]; revert x Hx; 
        apply cl_monotone; red; tauto. 
    Qed.

    Proposition lub_out A B C : closed C -> A ⊆ C -> B ⊆ C -> A ⊔ B ⊆ C.
    Proof. 
      simpl.
      intros H1 H2 H3.
      apply subset_trans with (2 := H1), cl_monotone.
      intros ? [ ]; auto.
    Qed.

    Proposition glb_in A B C : C ⊆ A -> C ⊆ B -> C ⊆ A ⊓ B.
    Proof. simpl; split; auto. Qed.

    Proposition closed_lub A B : closed (A ⊔ B).
    Proof. simpl; apply cl_idempotent. Qed.

    Proposition glb_out_l A B  : A ⊓ B ⊆ A.
    Proof. unfold glb; simpl; red; tauto. Qed.

    Proposition glb_out_r A B  : A ⊓ B ⊆ B.
    Proof. unfold glb; simpl; red; tauto. Qed.

    Proposition lub_in_l A B   : A ⊆ A ⊔ B.
    Proof. apply subset_trans with (2 := cl_increase _); red; tauto. Qed.

    Proposition lub_in_r A B   : B ⊆ A ⊔ B.
    Proof. apply subset_trans with (2 := cl_increase _); red; tauto. Qed.

    Proposition glb_comm A B : A ⊓ B ≃ B ⊓ A.
    Proof. unfold glb; split; apply glb_in; red; tauto. Qed.

    Definition top := (fun _ : M => True).
    Definition zero := (cl (fun _ => False)).

    Proposition closed_top     : closed top.         Proof. unfold top; simpl; intros; red; auto. Qed. 
    Proposition closed_zero    : closed zero.        Proof. simpl; apply cl_idempotent. Qed.
    Proposition top_greatest A : A ⊆ top.            Proof. unfold top; simpl; red; tauto. Qed.

    Hint Resolve closed_glb closed_top.

    Fact closed_mglb ll : Forall_Type closed ll -> closed (fold_right (fun x y => x ∩ y) top ll).
    Proof. induction 1; simpl. apply closed_top. apply closed_glb; auto. Qed.

    Hint Resolve closed_mglb.

    Proposition zero_least A : closed A -> zero ⊆ A.
    Proof. intro H; apply subset_trans with (2 := H), cl_monotone; red; tauto. Qed.

  End Closure_Operator.

  Hint Resolve cl_increase cl_monotone cl_idempotent.
  Hint Resolve cl_subset cl_eqset.
  Hint Resolve closed_top closed_glb closed_mglb.

  Notation "x ⊓ y" := (glb x y) (at level 50, no associativity).
  Notation "x ⊔ y" := (lub x y) (at level 50, no associativity).
  Notation closed := (fun x => cl x ⊆ x).



  (* ⊆ ≃ ∩ ∪ ∘ ⊓ ⊔ *)



  (* Relational/non-deterministic phase structure *)

  Section Relational_Phase.

    Context { CL : ClosureOp }.

    (* this is a relational/non-deterministic monoid *)
    Variable Compose : M -> M -> M -> Type.

    (* Composition lifted to predicates *)
    Inductive Composes (A B : M -> Type) : M -> Type :=
      In_composes : forall a b c, A a -> B b -> Compose a b c -> Composes A B c.

    Infix "∘" := Composes (at level 50, no associativity).

    Global Instance composes_monotone : Proper (subset ==> subset ==> subset) Composes.
    Proof.
      intros X1 Y1 H1 X2 Y2 H2 x [a b c Ha Hb Hc].
      apply (In_composes _ _ (H1 _ Ha) (H2 _ Hb) Hc).
    Qed.

    Hint Resolve composes_monotone.


    (* Stability *)
    (** Stability is the important axiom in phase semantics *)

    Definition cl_stability   := forall A B, cl A ∘ cl B ⊆ cl (A ∘ B).
    Definition cl_stability_l := forall A B, cl A ∘    B ⊆ cl (A ∘ B).
    Definition cl_stability_r := forall A B,    A ∘ cl B ⊆ cl (A ∘ B).

    Proposition cl_stable_imp_stable_l : cl_stability -> cl_stability_l.
    Proof.
      intros H ? ? x Hx.
      apply H; revert x Hx.
      apply composes_monotone; auto.
    Qed.

    Proposition cl_stable_imp_stable_r : cl_stability -> cl_stability_r.
    Proof.
      intros H ? ? x Hx.
      apply H; revert x Hx.
      apply composes_monotone; auto.
    Qed.

    Proposition cl_stable_lr_imp_stable : cl_stability_l -> cl_stability_r -> cl_stability.
    Proof.
      intros H1 H2 A B x Hx.
      apply cl_idempotent.
      generalize (H1 _ _ _ Hx).
      apply cl_monotone, H2.
    Qed.

    Hint Resolve cl_stable_imp_stable_l cl_stable_imp_stable_r cl_stable_lr_imp_stable.

    Hypothesis cl_stable_l : cl_stability_l.
    Hypothesis cl_stable_r : cl_stability_r.

    Proposition cl_stable : cl_stability.
    Proof. auto. Qed.

    Hint Resolve cl_stable.

    Proposition cl_equiv_2 X Y : cl (cl X ∘ Y) ≃ cl (X ∘ Y).
    Proof.
      split.
      apply cl_subset; auto.
      apply cl_monotone, composes_monotone; auto.
    Qed.

    Proposition cl_equiv_3 X Y : cl (X ∘ cl Y) ≃ cl (X ∘ Y).
    Proof.
      split.
      apply cl_subset; auto.
      apply cl_monotone, composes_monotone; auto.
    Qed.

    Proposition cl_equiv_4 X Y : cl (cl X ∘ cl Y) ≃ cl (X ∘ Y).
    Proof. 
      split.
      apply cl_subset; auto.
      apply cl_monotone, composes_monotone; auto.
    Qed.

    Hint Immediate cl_equiv_2 cl_equiv_3 cl_equiv_4.


    (* Congruence *)

    Proposition composes_congruent_l_1 A B C : A ⊆ cl B -> C ∘ A ⊆ cl (C ∘ B).
    Proof.
      intros ?.
      apply (@subset_trans _ (cl (C ∘ cl B))) ; auto.
      apply subset_cl, cl_monotone, composes_monotone; auto.
    Qed.

    Hint Resolve composes_congruent_l_1.

    Proposition composes_congruent_l A B C : cl A ≃ cl B -> cl (C ∘ A) ≃ cl (C ∘ B).
    Proof.
      intros [H1 H2].
      generalize (subset_cl H1) (subset_cl H2); intros H3 H4.
      split; apply cl_subset;
      apply subset_trans with (2 := @cl_stable_r _ _), composes_monotone; auto.
    Qed.

    Proposition composes_congruent_r_1 A B C : A ⊆ cl B -> A ∘ C ⊆ cl (B ∘ C).
    Proof.
      intros ?.
      apply (@subset_trans _ (cl (cl B ∘ C))); auto.
      apply subset_cl, cl_monotone, composes_monotone; auto.
    Qed.

    Hint Resolve composes_congruent_r_1.

    Proposition composes_congruent_r A B C : cl A ≃ cl B -> cl (A ∘ C) ≃ cl (B ∘ C).
    Proof.
      intros [H1 H2].
      generalize (subset_cl H1) (subset_cl H2); intros H3 H4.
      split; apply cl_subset;
      apply subset_trans with (2 := @cl_stable_l _ _), composes_monotone; auto.
    Qed.

    Hint Resolve composes_congruent_l composes_congruent_r.

    Proposition composes_congruent A B C D : cl A ≃ cl B -> cl C ≃ cl D ->
      cl (A ∘ C) ≃ cl (B ∘ D).
    Proof. intros; apply eqset_trans with (cl (B ∘ C)); auto. Qed.


    (* Adjunct *)

    Definition Magicwand_l A B k := A ∘ sg k ⊆ B.
    Infix "⊸" := Magicwand_l (at level 51, right associativity).

    Proposition magicwand_l_spec A B C : B ∘ A ⊆ C ≡ A ⊆ B ⊸ C.
    Proof.
      split; intros H x Hx.
      intros y Hy; apply H; revert Hy; apply composes_monotone; auto.
      apply sg_subset; auto.
      destruct Hx as [ a b x Ha Hb Hx ].
      apply (H _ Hb).
      constructor 1 with a b; auto.
    Qed.

    Definition magicwand_l_adj_1 A B C := fst (magicwand_l_spec A B C).
    Definition magicwand_l_adj_2 A B C := snd (magicwand_l_spec A B C).

    Global Instance magicwand_l_monotone : Proper (subset --> subset ==> subset) Magicwand_l.
    Proof.
      intros ? ? ? ? ? HB.
      apply magicwand_l_adj_1, subset_trans with (2 := HB).
      intros _ [? ? ? Ha Hb Hc]; apply Hb, In_composes with (3 := Hc); auto.
    Qed.

    Hint Resolve magicwand_l_monotone.

    Proposition cl_magicwand_l_1 X Y : cl (X ⊸ cl Y) ⊆ X ⊸ cl Y.
    Proof.
      apply magicwand_l_adj_1. 
      apply (@subset_trans _ (cl (X ∘ (X ⊸ cl Y)))); auto.
      apply cl_subset; apply magicwand_l_spec; auto.
    Qed.

    Proposition cl_magicwand_l_2 X Y : cl X ⊸ Y ⊆ X ⊸ Y.
    Proof. apply magicwand_l_monotone; red; auto. Qed.

    Hint Immediate cl_magicwand_l_1 cl_magicwand_l_2.

    Proposition cl_magicwand_l_3 X Y : X ⊸ cl Y ⊆ cl X ⊸ cl Y.
    Proof.
      intros c Hc y.
      apply (@subset_trans _ (cl (X ∘ sg c))); auto.
    Qed.

    Hint Immediate cl_magicwand_l_3.

    Proposition closed_magicwand_l X Y : closed Y -> closed (X ⊸ Y).
    Proof.
      simpl; intros ?.
      apply (@subset_trans _ (cl (X ⊸ cl Y))); auto.
      + apply cl_monotone, magicwand_l_monotone; auto; red; auto.
      + apply (@subset_trans _ (X ⊸ cl Y)); auto.
        apply magicwand_l_monotone; red; auto.
    Qed.

    Hint Resolve closed_magicwand_l.

    Proposition magicwand_l_eq_1 X Y : X ⊸ cl Y ≃ cl X ⊸ cl Y.
    Proof. split; auto. Qed.

    Proposition magicwand_l_eq_2 X Y : cl (X ⊸ cl Y) ≃ X ⊸ cl Y.
    Proof. split; auto. Qed.

    Hint Resolve magicwand_l_eq_1 magicwand_l_eq_2.

    Proposition magicwand_l_eq_3 X Y : cl (X ⊸ cl Y) ≃ cl X ⊸ cl Y.
    Proof. apply eqset_trans with (X ⊸ cl Y); auto. Qed.

    Hint Resolve magicwand_l_eq_3.

    Definition Magicwand_r B A k := sg k ∘ A ⊆ B.
    Infix "⟜" := Magicwand_r (at level 52, left associativity).

    Proposition magicwand_r_spec A B C : A ∘ B ⊆ C ≡ A ⊆ C ⟜ B.
    Proof.
      split; intros H x Hx.
      intros y Hy; apply H; revert Hy; apply composes_monotone; auto.
      apply sg_subset; auto.
      destruct Hx as [ a b x Ha Hb Hx ].
      apply (H _ Ha).
      constructor 1 with a b; auto.
    Qed.

    Definition magicwand_r_adj_1 A B C := fst (magicwand_r_spec A B C).
    Definition magicwand_r_adj_2 A B C := snd (magicwand_r_spec A B C).

    Global Instance magicwand_r_monotone : Proper (subset ==> subset --> subset) Magicwand_r.
    Proof.
      intros ? ? HB ? ? HA.
      apply magicwand_r_adj_1, subset_trans with (2 := HB).
      intros _ [? ? ? Ha Hb Hc]; apply Ha, In_composes with (3 := Hc); auto.
    Qed.

    Hint Resolve magicwand_r_monotone.

    Proposition cl_magicwand_r_1 X Y : cl (cl Y ⟜ X) ⊆ cl Y ⟜ cl X.
    Proof. 
      apply magicwand_r_adj_1.
      apply (@subset_trans _ (cl ((cl Y ⟜ X) ∘ X))); auto.
      apply cl_subset; apply magicwand_r_spec; auto.
    Qed.

    Proposition cl_magicwand_r_2 X Y : Y ⟜ cl X ⊆ Y ⟜ X.
    Proof. apply magicwand_r_monotone; red; auto. Qed.

    Hint Immediate cl_magicwand_r_1 cl_magicwand_r_2.

    Proposition cl_magicwand_r_3 X Y : cl Y ⟜ X ⊆ cl Y ⟜ cl X.
    Proof. intros c ? ?; apply (@subset_trans _ (cl (sg c ∘ X))); auto. Qed.

    Hint Immediate cl_magicwand_r_3.

    Proposition closed_magicwand_r X Y : closed Y -> closed (Y ⟜ X).
    Proof.
      simpl; intros ?.
      apply (@subset_trans _ (cl (cl Y ⟜ X))); auto.
      + apply cl_monotone, magicwand_r_monotone; auto; red; auto.
      + apply (@subset_trans _ (cl Y ⟜ X)); auto.
        apply subset_trans with (1 := @cl_magicwand_r_1 _ _); auto.
        apply magicwand_r_monotone; red; auto.
    Qed.

    Hint Resolve closed_magicwand_r.

    Proposition magicwand_r_eq_1 X Y : cl Y ⟜ X ≃ cl Y ⟜ cl X.
    Proof. split; auto. Qed.

    Proposition magicwand_r_eq_2 X Y : cl (cl Y ⟜ X) ≃ cl Y ⟜ X.
    Proof. split; auto. Qed.

    Hint Resolve magicwand_r_eq_1 magicwand_r_eq_2.

    Proposition magicwand_r_eq_3 X Y : cl (cl Y ⟜ X) ≃ cl Y ⟜ cl X.
    Proof. apply eqset_trans with (cl Y ⟜ X); auto. Qed.

    Hint Resolve magicwand_r_eq_3.


    (* Associativity *)

    Definition cl_associativity_1 := (forall a b c, sg a ∘ (sg b ∘ sg c) ⊆ cl ((sg a ∘ sg b) ∘ sg c)).
    Definition cl_associativity_2 := (forall a b c, (sg a ∘ sg b) ∘ sg c ⊆ cl (sg a ∘ (sg b ∘ sg c))).

    Hypothesis cl_associative_1 : cl_associativity_1.
    Hypothesis cl_associative_2 : cl_associativity_2.

    Proposition composes_associative_1 A B C : A ∘ (B ∘ C) ⊆ cl ((A ∘ B) ∘ C).
    Proof.
      intros _ [a _ k Ha [b c y Hb Hc Hy] Hk].
      generalize (@cl_associative_1 a b c k); intros H.
      spec all in H.
      apply In_composes with (3 := Hk); auto.
      apply In_composes with (3 := Hy); auto.
      revert H.
      apply cl_monotone.
      repeat apply composes_monotone; apply sg_subset; auto.
    Qed.

    Hint Immediate composes_associative_1.

    Proposition composes_associative_2 A B C : (A ∘ B) ∘ C ⊆ cl (A ∘ (B ∘ C)).
    Proof.
      intros _ [_ c k [a b y Ha Hb Hy] Hc Hk].
      generalize (@cl_associative_2 a b c k); intros H.
      spec all in H.
      apply In_composes with (3 := Hk); auto.
      apply In_composes with (3 := Hy); auto.
      revert H.
      apply cl_monotone.
      repeat apply composes_monotone; apply sg_subset; auto.
    Qed.

    Hint Immediate composes_associative_2.

    Proposition composes_associative A B C : cl (A ∘ (B ∘ C)) ≃ cl ((A ∘ B) ∘ C).
    Proof. split; auto; apply cl_inc; auto. Qed.

    Hint Immediate composes_associative.


    (* Unit *)

    Variable e : M.

    Definition cl_neutrality_1  := (forall a, cl (sg e ∘ sg a) a).
    Definition cl_neutrality_2  := (forall a, sg e ∘ sg a ⊆ cl (sg a)).
    Definition cl_neutrality_3  := (forall a, cl (sg a ∘ sg e) a).
    Definition cl_neutrality_4  := (forall a, sg a ∘ sg e ⊆ cl (sg a)).

    Hypothesis cl_neutral_1 : cl_neutrality_1.
    Hypothesis cl_neutral_2 : cl_neutrality_2.
    Hypothesis cl_neutral_3 : cl_neutrality_3.
    Hypothesis cl_neutral_4 : cl_neutrality_4.

    Proposition composes_neutral_l_1 A : A ⊆ cl (sg e ∘ A).
    Proof.
      intros a Ha.
      generalize (cl_neutral_1 a).
      apply cl_monotone, composes_monotone; auto.
      apply sg_subset; auto.
    Qed.

    Proposition composes_neutral_l_2 A : sg e ∘ A ⊆ cl A.
    Proof.
      intros _ [y a x [] Ha Hx].
      generalize (@cl_neutral_2 a x); intros H.
      spec all in H.
      constructor 1 with e a; auto.
      revert H; apply cl_monotone, sg_subset; auto.
    Qed.

    Hint Resolve composes_neutral_l_1 composes_neutral_l_2.

    Proposition composes_neutral_l A : cl (sg e ∘ A) ≃ cl A.
    Proof. split; apply cl_subset; auto. Qed.

    Proposition composes_neutral_r_1 A : A ⊆ cl (A ∘ sg e).
    Proof.
      intros a Ha.
      generalize (cl_neutral_3 a).
      apply cl_monotone, composes_monotone; auto.
      apply sg_subset; auto.
    Qed.

    Proposition composes_neutral_r_2 A : A ∘ sg e ⊆ cl A.
    Proof.
      intros _ [a y x Ha [] Hx].
      generalize (@cl_neutral_4 a x); intros H.
      spec all in H.
      constructor 1 with a e; auto.
      revert H; apply cl_monotone, sg_subset; auto.
    Qed.

    Hint Resolve composes_neutral_r_1 composes_neutral_r_2.

    Proposition composes_neutral_r A : cl (A ∘ sg e) ≃ cl A.
    Proof. split; apply cl_subset; auto. Qed.

    Definition unit := (cl (sg e)).

    Proposition closed_unit : closed unit.
    Proof. simpl; apply cl_idempotent. Qed.


    (* Tensor *)
    Definition tensor x y := (cl (x ∘ y)).
    Infix "⊛" := tensor (at level 59).

    Proposition closed_times A B : closed (A⊛B).
    Proof. simpl; apply cl_idempotent. Qed.

    Global Instance times_monotone : Proper (subset ==> subset ==> subset) tensor.
    Proof. simpl; intros ? ? ? ? ? ?; apply cl_monotone, composes_monotone; auto. Qed.

    Proposition unit_neutral_l_1 A : closed A -> unit ⊛ A ⊆ A.
    Proof.
      intros H; apply subset_trans with (2 := H).
      apply cl_subset.
      apply subset_trans with (1 := @cl_stable_l _ _).
      apply cl_subset; auto.
    Qed.

    Proposition unit_neutral_l_2 A : A ⊆ unit ⊛ A.
    Proof.
      unfold unit; intros a Ha; simpl.
      generalize (composes_neutral_l_1 _ _ Ha).
      apply cl_monotone, composes_monotone; auto.
    Qed.

    Proposition unit_neutral_l A : closed A -> unit ⊛ A ≃ A.
    Proof.
      intros H; split. 
      revert H; apply unit_neutral_l_1.
      apply unit_neutral_l_2.
    Qed.

    Proposition unit_neutral_r_1 A : closed A -> A ⊛ unit ⊆ A.
    Proof.
      intros H; apply subset_trans with (2 := H).
      apply cl_subset.
      apply subset_trans with (1 := @cl_stable_r _ _).
      apply cl_subset; auto.
    Qed.

    Proposition unit_neutral_r_2 A : A ⊆ A ⊛ unit.
    Proof.
      unfold unit; intros a Ha; simpl.
      generalize (composes_neutral_r_1 _ _ Ha).
      apply cl_monotone, composes_monotone; auto.
    Qed.

    Proposition unit_neutral_r A : closed A -> A ⊛ unit ≃ A.
    Proof.
      intros H; split. 
      revert H; apply unit_neutral_r_1.
      apply unit_neutral_r_2.
    Qed.

    Hint Resolve unit_neutral_l unit_neutral_r. 

    Proposition times_associative A B C : (A⊛B)⊛C ≃ A⊛(B⊛C).
    Proof.
      apply eqset_sym, eqset_trans with (1 := cl_equiv_3 _ _ ).
      apply eqset_sym, eqset_trans with (1 := cl_equiv_2 _ _ ).
      apply eqset_sym, composes_associative.
    Qed.

    Proposition times_associative_1 A B C : (A⊛B)⊛C ⊆ A⊛(B⊛C).     Proof. apply times_associative. Qed.
    Proposition times_associative_2 A B C : A⊛(B⊛C) ⊆ (A⊛B)⊛C.     Proof. apply times_associative. Qed.

    Hint Resolve times_associative_1 times_associative_2.

    Global Instance times_congruence : Proper (eqset ==> eqset ==> eqset) tensor.
    Proof. intros ? ? ? ? ? ?; apply composes_congruent; auto. Qed.

    (* Adjunction properties *)
    Proposition adjunction_l_1 A B C : closed C -> B ⊛ A ⊆ C -> A ⊆ B ⊸ C.
    Proof. unfold tensor; intros ? H; apply magicwand_l_adj_1, subset_trans with (2 := H); auto. Qed.

    Proposition adjunction_l_2 A B C : closed C -> A ⊆ B ⊸ C -> B ⊛ A ⊆ C.
    Proof. intros H ?; apply subset_trans with (2 := H), cl_monotone, magicwand_l_adj_2; auto. Qed.

    Hint Resolve times_congruence adjunction_l_1 (* adjunction_2 *).

    Proposition adjunction_l A B C : closed C -> (B ⊛ A ⊆ C ≡ A ⊆ B ⊸ C).
    Proof. split; [ apply adjunction_l_1 | apply adjunction_l_2 ]; auto. Qed.

    Proposition adjunction_r_1 A B C : closed C -> A ⊛ B ⊆ C -> A ⊆ C ⟜ B.
    Proof. unfold tensor; intros ? H; apply magicwand_r_adj_1, subset_trans with (2 := H); auto. Qed.

    Proposition adjunction_r_2 A B C : closed C -> A ⊆ C ⟜ B -> A ⊛ B ⊆ C.
    Proof. intros H ?; apply subset_trans with (2 := H), cl_monotone, magicwand_r_adj_2; auto. Qed.

    Hint Resolve adjunction_r_1 (* adjunction_2 *).

    Proposition adjunction_r A B C : closed C -> (A ⊛ B ⊆ C ≡ A ⊆ C ⟜ B).
    Proof. split; [ apply adjunction_r_1 | apply adjunction_r_2 ]; auto. Qed.


  (* ⊆ ≃ ∩ ∪ ∘ ⊓ ⊔ *)

    (* Distributivity properties *)
    Proposition times_zero_distrib_l A : zero ⊛ A ⊆ zero.
    Proof.
      unfold zero; apply adjunction_r_2; auto.
      apply zero_least; auto.
    Qed.

    Proposition times_zero_distrib_r A : A ⊛ zero ⊆ zero.
    Proof.
      unfold zero; apply adjunction_l_2; auto.
      apply zero_least; auto.
    Qed.

    Hint Immediate times_zero_distrib_l times_zero_distrib_r.

    Proposition times_lub_distrib_l A B C : (A ⊔ B) ⊛ C ⊆ (A ⊛ C) ⊔ (B ⊛ C).
    Proof.
      unfold lub; apply adjunction_r, lub_out; auto;
      apply adjunction_r; auto; intros ? ?; apply cl_increase; auto. 
    Qed.

    Proposition times_lub_distrib_r A B C : C ⊛ (A ⊔ B) ⊆ (C ⊛ A) ⊔ (C ⊛ B).
    Proof.
      unfold lub; apply adjunction_l, lub_out; auto;
      apply adjunction_l; auto; intros ? ?; apply cl_increase; auto. 
    Qed.


    (* Exponentials *)
    (* J := { x | x ∈ unit /\ x ∈ x ⊛ x } with unit = cl e and x ⊛ x = cl (x∘x) *)

    Let J x := (cl (sg e) x * (cl (sg x ∘ sg x)) x)%type.

    Let In_J : forall x, cl (sg e) x -> (cl (sg x ∘ sg x)) x -> J x.
    Proof. split; auto. Qed.

    Let J_inv x : J x -> unit x * cl (sg x ∘ sg x) x.
    Proof. auto. Qed.

    Proposition J_inc_unit : J ⊆ unit.
    Proof. induction 1; trivial. Qed.

    Variable K : M -> Type.

    Definition sub_monoid_hyp_1 := ((cl K) e).
    Definition sub_monoid_hyp_2 := (K ∘ K ⊆ K).
    Definition sub_J_hyp := (K ⊆ J).

    Hypothesis sub_monoid_1 : sub_monoid_hyp_1.
    Hypothesis sub_monoid_2 : sub_monoid_hyp_2.
    Hypothesis sub_J : sub_J_hyp.

    Proposition K_inc_unit : K ⊆ unit.
    Proof. apply subset_trans with J; trivial; apply J_inc_unit. Qed.

    Proposition K_compose A B : (K ∩ A) ∘ (K ∩ B) ⊆ K ∩ (A ∘ B).
    Proof.
      intros x Hx.
      induction Hx as [ a b c [ ] [ ] Hc ]; split.
      + apply sub_monoid_2; constructor 1 with a b; auto.
      + constructor 1 with a b; auto.
    Qed.

    Definition bang A := cl (K∩A).

    Notation "❗ A" := (bang A) (at level 40, no associativity).

    Fact store_inc_unit A : ❗ A ⊆ unit.
    Proof.
      apply subset_trans with (cl K).
      + apply cl_monotone; red; tauto.
      + apply cl_subset, K_inc_unit.
    Qed.

    Hint Resolve store_inc_unit.

    Proposition closed_store A : closed (❗A).
    Proof. simpl; apply cl_idempotent. Qed.

    Proposition store_dec A : closed A -> ❗A ⊆ A.
    Proof.
      intros HA; simpl.
      apply subset_trans with (cl A); trivial.
      apply cl_monotone.
      apply glb_out_r.
    Qed.

    Global Instance store_monotone : Proper (subset ==> subset) bang.
    Proof. intros ? ? ?; apply cl_monotone; intros ? []; split; auto. Qed.

    Hint Resolve store_monotone.

    Global Instance store_congruence : Proper (eqset ==> eqset) bang.
    Proof. intros ? ? [? ?]; split; auto. Qed.

    Proposition store_der A B : closed B -> ❗A ⊆ B -> ❗A ⊆ ❗B.
    Proof.
      unfold bang.
      intros H1 H2; apply cl_monotone; intros x []; split; auto.
      apply H2, cl_increase; auto.
    Qed.

    Proposition store_unit_1 : unit ⊆ ❗top.
    Proof.
      unfold top; apply cl_subset.
      intros ? []; apply cl_monotone with K; auto; red; auto.
    Qed.

    Hint Resolve J_inc_unit.

    Proposition store_unit_2 : ❗top ⊆ unit.
    Proof.
      apply cl_subset; trivial.
      apply subset_trans with J; auto.
      intros ? []; auto.
    Qed.

    Hint Resolve store_unit_1 store_unit_2.

    Proposition store_unit : unit ≃ ❗top.
    Proof. split; auto. Qed.

    Hint Resolve store_unit.

    Proposition store_comp A B : closed A -> closed B -> ❗A ⊛ ❗B ≃ ❗(A ⊓ B).
    Proof.
      intros HA HB; split.
      + apply subset_trans with (cl ((K ⊓ A) ∘ (K ⊓ B))).
        * apply cl_subset; trivial; apply cl_stable.
        * apply cl_monotone.
          intros x [ a b c [ H1 H2 ] [ H3 H4 ] Hc ].
          assert (H5 : unit a). { apply K_inc_unit; auto. }
          assert (H6 : unit b). { apply K_inc_unit; auto. }
          split; [ | split ].
          - apply sub_monoid_2; constructor 1 with a b; auto.
          - apply unit_neutral_r_1; auto; apply cl_increase.
            constructor 1 with a b; auto.
          - apply unit_neutral_l_1; auto; apply cl_increase.
            constructor 1 with a b; auto.
      + apply cl_subset; trivial.
        intros x (H1 & H2 & H3).
        apply cl_monotone with (sg x ∘ sg x).
        2: { apply sub_J in H1; destruct H1; trivial. }
        intros d [ a b ? ? Hab ]; subst a b; constructor 1 with x x; auto;
          apply cl_increase; auto.
    Qed.

    Let ltimes := fold_right (fun x y => x ⊛ y) unit.
    Definition lcap := fold_right (fun x y => x∩y) top.

    Proposition ltimes_store ll : Forall_Type closed ll ->
      ltimes (map bang ll) ≃ ❗(lcap ll).
    Proof.
      unfold ltimes, lcap.
      induction 1; simpl; auto.
      apply eqset_trans with (❗ x ⊛ ❗(fold_right (fun x y => x ∩ y) top l)).
      * apply times_congruence; auto.
      * apply store_comp; auto.
    Qed.

    Proposition store_compose_idem A : closed A -> ❗A ⊆ ❗A⊛❗A.
    Proof.
      intros HA.
      apply subset_trans with (❗(A∩A)).
      + apply store_der. 
        * apply closed_glb; trivial.
        * apply subset_trans with A.
          - apply store_dec; trivial.
          - red; tauto.
     + apply (snd (store_comp HA HA)).
    Qed.


    (* Commutativity *)

    Definition cl_commutativity := (forall a b, sg a ∘ sg b ⊆ cl (sg b ∘ sg a)).

    Hypothesis cl_commute : cl_commutativity.

    Proposition composes_commute_1 A B : A ∘ B ⊆ cl (B ∘ A).
    Proof.
      intros _ [ a b c Ha Hb Hc ].
      apply cl_monotone with (sg b ∘ sg a).
      apply composes_monotone; apply sg_subset; auto.
      apply cl_commute.
      constructor 1 with (3 := Hc); auto.
    Qed.

    Hint Resolve composes_commute_1.

    Proposition composes_commute A B : cl (A∘B) ≃ cl (B∘A).
    Proof. split; intros x Hx; apply cl_idempotent; revert Hx; apply cl_monotone; auto. Qed.

    Hint Resolve composes_commute.

    Proposition cl_stable_l_imp_stable_r : cl_stability_l -> cl_stability_r.
    Proof.
      intros Hl A B x Hx.
      apply cl_idempotent.
      apply cl_monotone with (cl B ∘ A).
      apply subset_trans with (2 := fst (composes_commute _ _)); auto.
      apply composes_commute_1; auto.
    Qed.

    Proposition cl_stable_r_imp_stable_l : cl_stability_r -> cl_stability_l.
    Proof.
      intros Hl A B.
      apply subset_trans with (2 := fst (composes_commute _ _)); auto.
      apply subset_trans with (1 := @composes_commute_1 _ _); auto.
    Qed.

    Proposition cl_stable_l_imp_stable : cl_stability_l -> cl_stability.
    Proof. auto. Qed.

    Proposition cl_associative_1_imp_2 : cl_associativity_1 -> cl_associativity_2.
    Proof.
      intros H1 a b c.
      apply subset_trans with (2 := fst (composes_commute _ _)).
      apply subset_trans with (cl ((sg c ∘ sg b) ∘ sg a)).
      + apply subset_trans with (2 := cl_subset (H1 _ _ _)).
        apply subset_trans with (2 := fst (composes_commute _ _)).
        apply subset_cl, composes_congruent; auto.
      + apply composes_congruent; auto.
    Qed.

    Proposition cl_neutrality_1_imp_3 : cl_neutrality_1 -> cl_neutrality_3.
    Proof. intros H x; generalize (H x); apply composes_commute. Qed.

    Proposition cl_neutrality_2_imp_4 : cl_neutrality_2 -> cl_neutrality_4.
    Proof.
      intros H x y Hxy.
      specialize (H x).
      apply cl_idempotent.
      apply cl_monotone in H.
      apply H.
      revert Hxy; apply cl_commute.
    Qed.

    Proposition times_commute_1 A B : A⊛B ⊆ B⊛A.
    Proof. simpl; apply cl_subset; auto. Qed.

    Hint Resolve times_commute_1.

    Proposition times_commute A B : A⊛B ≃ B⊛A.
    Proof. split; auto. Qed.

  End Relational_Phase.

End Subset.

