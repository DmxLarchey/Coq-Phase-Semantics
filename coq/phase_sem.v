(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Permutation.

Require Import utils ill_form ill_rules.

Set Implicit Arguments.

Section Relational_phase_semantics.

  (** We define a sound relational phase sematics for ILL 
      based on stable closures *)

  Variable M : Type.

  Implicit Types A B C : M -> Prop.

  Variable cl : (M -> Prop) -> (M -> Prop).

  Hypothesis cl_increase   : forall A, A ⊆ cl A.
  Hypothesis cl_monotone   : forall A B, A ⊆ B -> cl A ⊆ cl B.
  Hypothesis cl_idempotent : forall A, cl (cl A) ⊆ cl A.
  
  Proposition cl_prop A B : A ⊆ cl B <-> cl A ⊆ cl B.
  Proof.
    split; intros H x Hx.
    apply cl_idempotent; revert Hx; apply cl_monotone; auto.
    apply H, cl_increase; auto.
  Qed.
  
  Definition cl_inc A B := proj1 (cl_prop A B).
  Definition inc_cl A B := proj2 (cl_prop A B). 
  
  Fact cl_eq1 A B : A ≃ B -> cl A ≃ cl B.
  Proof. intros []; split; apply cl_monotone; auto. Qed.

  Hint Resolve cl_inc cl_eq1.

  Notation closed := (fun x : M -> Prop => cl x ⊆ x).
  
  Fact cl_closed A B : closed B -> A ⊆ B -> cl A ⊆ B.
  Proof.
    intros H1 H2.
    apply inc1_trans with (2 := H1), cl_inc, 
          inc1_trans with (1 := H2), cl_increase.
  Qed.

  Fact cap_closed A B : closed A -> closed B -> closed (A ∩ B).
  Proof.
    intros HA HB x Hx; split; [ apply HA | apply HB ]; revert Hx; apply cl_monotone; tauto.
  Qed.

  Hint Resolve cap_closed.

  (* this is a relational/non-deterministic monoid *)

  Variable Compose : M -> M -> M -> Prop.

  (* Composition lifted to predicates *)

  Inductive Composes (A B : M -> Prop) : M -> Prop :=
    In_composes : forall a b c, A a -> B b -> Compose a b c -> Composes A B c.

  (* ⊆ ≃ ∩ ∪ ∘ *)

  Infix "∘" := Composes (at level 50, no associativity).

  Proposition composes_monotone A A' B B' : A ⊆ A' -> B ⊆ B' ->  A ∘ B ⊆ A' ∘ B'.
  Proof. intros ? ? _ [ ? ? ? ? ? H ]; apply In_composes with (3 := H); auto. Qed.

  Hint Resolve composes_monotone.

  Variable e : M.

  (* Stability is the important axiom in phase semantics *)

  Definition cl_stability   := forall A B, cl A ∘ cl B ⊆ cl (A ∘ B).
  Notation cl_stability_l  := (forall A B, cl A ∘    B ⊆ cl (A ∘ B)).
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
  
  Notation sg := (@eq _).

  Notation cl_neutrality_1  := (forall a, cl (sg e ∘ sg a) a).
  Notation cl_neutrality_2  := (forall a, sg e ∘ sg a ⊆ cl (sg a)).
  Notation cl_commutativity := (forall a b, sg a ∘ sg b ⊆ cl (sg b ∘ sg a)).
  Notation cl_associativity := (forall a b c, sg a ∘ (sg b ∘ sg c) ⊆ cl ((sg a ∘ sg b) ∘ sg c)).

  Hypothesis cl_commute : cl_commutativity.

  Proposition composes_commute_1 A B : A ∘ B ⊆ cl (B ∘ A).
  Proof.
    intros _ [ a b c Ha Hb Hc ].
    apply cl_monotone with (sg b ∘ sg a).
    apply composes_monotone; apply sg_inc1; auto.
    apply cl_commute.
    constructor 1 with (3 := Hc); auto.
  Qed.

  Hint Resolve composes_commute_1.

  (* ⊆ ≃ ∩ ∪ ∘ *)

  Proposition composes_commute A B : cl (A∘B) ≃ cl (B∘A).
  Proof. 
    split; intros x Hx; apply cl_idempotent; revert Hx; apply cl_monotone; auto. 
  Qed. 

  Proposition cl_stable_l_imp_r : cl_stability_l -> cl_stability_r.
  Proof.
    intros Hl A B x Hx.
    apply cl_idempotent.
    apply cl_monotone with (cl B ∘ A).
    apply inc1_trans with (cl ((cl B) ∘ A)); auto.
    rewrite <- cl_prop; auto.
    generalize (@composes_commute_1 B A); intros H.
    rewrite cl_prop in H; auto.
    apply composes_commute_1; auto.
  Qed.
  
  Proposition cl_stable_r_imp_l : cl_stability_r -> cl_stability_l.
  Proof.
    intros Hl A B.
    generalize (@composes_commute_1 B A); intros H.
    rewrite cl_prop in H; auto.
    apply inc1_trans with (B := cl (B ∘ cl A)),
          inc1_trans with (2 := H); auto.
    rewrite <- cl_prop; apply Hl.
  Qed.

  Hint Resolve cl_stable_l_imp_r cl_stable_r_imp_l.
  
  Proposition cl_stable_l_imp_stable : cl_stability_l -> cl_stability.    Proof. auto. Qed. 
  Proposition cl_stable_r_imp_stable : cl_stability_r -> cl_stability.    Proof. auto. Qed.

  Hypothesis cl_stable_l : cl_stability_l.
  
  Proposition cl_stable_r : cl_stability_r.                               Proof. auto. Qed.
  Proposition cl_stable : cl_stability.                                   Proof. auto. Qed.

  Hint Resolve cl_stable_r cl_stable.

  Hypothesis cl_neutral_1 : cl_neutrality_1.
  Hypothesis cl_neutral_2 : cl_neutrality_2.
  Hypothesis cl_associative : cl_associativity.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ *)

  Definition Magicwand A B k := sg k ∘ A ⊆ B.
  Infix "⊸" := Magicwand (at level 51, right associativity).

  Proposition magicwand_spec A B C : A ∘ B ⊆ C <-> A ⊆ B ⊸ C.
  Proof.
    split; intros H x Hx.
    intros y Hy; apply H; revert Hy; apply composes_monotone; auto.
    apply sg_inc1; auto.
    destruct Hx as [ a b x Ha Hb Hx ].
    apply (H _ Ha).
    constructor 1 with a b; auto.
  Qed.

  Definition magicwand_adj_1 A B C := proj1 (magicwand_spec A B C).
  Definition magicwand_adj_2 A B C := proj2 (magicwand_spec A B C).

(*  Hint Resolve magicwand_adj_1 magicwand_adj_2. *)

  Proposition magicwand_monotone A A' B B' : A ⊆ A' -> B ⊆ B' -> A' ⊸ B ⊆ A ⊸ B'.
  Proof.
    intros ? HB; apply magicwand_adj_1, inc1_trans with (2 := HB).
    intros _ [? ? ? Ha ? Hc]; apply Ha, In_composes with (3 := Hc); auto.
  Qed.

  Hint Resolve magicwand_monotone.

  Proposition cl_magicwand_1 X Y : cl (X ⊸ cl Y) ⊆ X ⊸ cl Y.
  Proof. 
    apply magicwand_adj_1, 
          inc1_trans with (B := cl ((X ⊸ cl Y) ∘ X)); auto.
    rewrite <- cl_prop; apply magicwand_spec; auto. 
  Qed.

  Proposition cl_magicwand_2 X Y : cl X ⊸ Y ⊆ X ⊸ Y.
  Proof. apply magicwand_monotone; auto. Qed.
 
  Hint Immediate cl_magicwand_1 cl_magicwand_2.

  Proposition cl_magicwand_3 X Y : X ⊸ cl Y ⊆ cl X ⊸ cl Y.
  Proof.
    intros c Hc y.
    apply inc1_trans with (B := cl (sg c ∘ X)); auto.
    rewrite <- cl_prop.
    intros ? [ a b d [] Hb ].
    intros; apply Hc. 
    constructor 1 with c b; auto.
  Qed.

  Hint Immediate cl_magicwand_3.

  Proposition closed_magicwand X Y : closed Y -> closed (X ⊸ Y).
  Proof. 
    simpl; intros ?.
    apply inc1_trans with (B := cl (X ⊸ cl Y)); auto.
    apply cl_monotone, magicwand_monotone; auto.
    apply inc1_trans with (B := X ⊸ cl Y); auto.
    apply magicwand_monotone; auto.
  Qed.

  Hint Resolve closed_magicwand.

  Proposition magicwand_eq_1 X Y : X ⊸ cl Y ≃ cl X ⊸ cl Y.
  Proof. split; auto. Qed.

  Proposition magicwand_eq_2 X Y : cl (X ⊸ cl Y) ≃ X ⊸ cl Y.
  Proof. split; auto. Qed.

  Proposition magicwand_eq_3 X Y : cl (X ⊸ cl Y) ≃ cl X ⊸ cl Y.
  Proof.
    split; auto.
    apply inc1_trans with (B := X ⊸ cl Y); auto.
  Qed.

  Hint Resolve magicwand_eq_1 magicwand_eq_2 magicwand_eq_3.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ *)

  Proposition cl_equiv_2 X Y : cl (cl X ∘ Y) ≃ cl (X ∘ Y).
  Proof. 
    split.
    rewrite <- cl_prop; auto.
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Proposition cl_equiv_3 X Y : cl (X ∘ cl Y) ≃ cl (X ∘ Y).
  Proof.
    split.
    rewrite <- cl_prop; auto.
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Proposition cl_equiv_4 X Y : cl (cl X ∘ cl Y) ≃ cl (X ∘ Y).
  Proof. 
    split.
    rewrite <- cl_prop; auto.
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Hint Immediate cl_equiv_2 cl_equiv_3 cl_equiv_4.

  Proposition composes_associative_1 A B C : A ∘ (B ∘ C) ⊆ cl ((A ∘ B) ∘ C).
  Proof.
    intros _ [a _ k Ha [b c y Hb Hc Hy] Hk].
    generalize (@cl_associative a b c k); intros H.
    spec all in H.
    apply In_composes with (3 := Hk); auto.
    apply In_composes with (3 := Hy); auto.
    revert H.
    apply cl_monotone.
    repeat apply composes_monotone; apply sg_inc1; auto.
  Qed.

  Hint Immediate composes_associative_1.

  Proposition composes_associative A B C : cl (A ∘ (B ∘ C)) ≃ cl ((A ∘ B) ∘ C).
  Proof.
    split; auto.
    rewrite <- cl_prop; auto.
    rewrite <- cl_prop; auto.
    apply inc1_trans with (1 := @composes_commute_1 _ _).
    rewrite <- cl_prop.
    apply inc1_trans with (B := C ∘ cl (A ∘ B)); auto.
    apply composes_monotone; auto.
    apply inc1_trans with (B := C ∘ cl (B ∘ A)); auto.
    apply composes_monotone; auto.
    apply composes_commute.
    apply inc1_trans with (1 := @cl_stable_r _ _).
    rewrite <- cl_prop.
    apply inc1_trans with (1 := @composes_associative_1 _ _ _).
    rewrite <- cl_prop.
    apply inc1_trans with (1 := @composes_commute_1 _ _). 
    rewrite <- cl_prop.
    apply inc1_trans with (B := A ∘ cl (C ∘ B)); auto.
    apply composes_monotone; auto.
    apply inc1_trans with (B := A ∘ cl (B ∘ C)); auto.
    apply composes_monotone; auto.
    apply composes_commute.
  Qed.

  Hint Immediate composes_associative.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ *)

  Proposition composes_congruent_1 A B C : A ⊆ cl B -> C ∘ A ⊆ cl (C ∘ B).
  Proof.
    intros ?.
    apply inc1_trans with (B := cl (C ∘ cl B)); auto.
    apply cl_prop, cl_monotone, composes_monotone; auto.
    apply cl_equiv_3.
  Qed.

  Hint Resolve composes_congruent_1.

  Proposition composes_congruent A B C : cl A ≃ cl B -> cl (C ∘ A) ≃ cl (C ∘ B).
  Proof. 
    intros [H1 H2].
    rewrite <- cl_prop in H1.
    rewrite <- cl_prop in H2.
    split; rewrite <- cl_prop;
    apply inc1_trans with (2 := @cl_stable_r _ _), composes_monotone; auto.
  Qed.

  Proposition composes_assoc_special A A' B B' : cl((A∘A') ∘ (B∘B')) ≃ cl ((A∘B) ∘ (A'∘B')).
  Proof.
    do 2 apply eq1_sym, eq1_trans with (2 := composes_associative _ _ _).
    apply composes_congruent.
    apply eq1_sym, eq1_trans with (1 := composes_commute _ _).
    apply eq1_sym, eq1_trans with (2 := composes_associative _ _ _).
    apply composes_congruent, composes_commute.
  Qed.

  Definition composes_assoc_special_1 A A' B B' := proj1 (composes_assoc_special A A' B B').
  
  Proposition composes_neutral_1 A : A ⊆ cl (sg e ∘ A).
  Proof.
    intros a Ha.
    generalize (cl_neutral_1 a).
    apply cl_monotone, composes_monotone; auto.
    apply sg_inc1; auto.
  Qed.

  Proposition composes_neutral_2 A : sg e ∘ A ⊆ cl A.
  Proof.
    intros _ [y a x [] Ha Hx].
    generalize (@cl_neutral_2 a x); intros H.
    spec all in H.
    constructor 1 with e a; auto.
    revert H; apply cl_monotone, sg_inc1; auto.
  Qed.
  
  Hint Resolve composes_neutral_1 composes_neutral_2.

  Proposition composes_neutral A : cl (sg e ∘ A) ≃ cl A.
  Proof. split; rewrite <- cl_prop; auto. Qed.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)

  Notation "x 'glb' y " := (x ∩ y) (at level 50, no associativity).
  Notation "x 'lub' y" := (cl (x ∪ y)) (at level 50, no associativity).

  Proposition closed_glb A B : closed A -> closed B -> closed (A glb B).
  Proof. 
    simpl; intros HA HB x Hx; split; 
      [ apply HA | apply HB ]; revert x Hx; 
      apply cl_monotone; tauto. 
  Qed.

  Proposition lub_out A B C : closed C -> A ⊆ C -> B ⊆ C -> A lub B ⊆ C.
  Proof. 
    simpl.
    intros H1 H2 H3.
    apply inc1_trans with (2 := H1), cl_monotone.
    intros ? [ ]; auto.
  Qed.

  Proposition glb_in A B C : C ⊆ A -> C ⊆ B -> C ⊆ A glb B.
  Proof. simpl; split; auto. Qed. 

  Proposition closed_lub A B : closed (A lub B).        Proof. simpl; apply cl_idempotent. Qed.
  Proposition glb_out_l A B  : A glb B ⊆ A .            Proof. simpl; tauto. Qed.
  Proposition glb_out_r A B  : A glb B ⊆ B.             Proof. simpl; tauto. Qed.
  Proposition lub_in_l A B   : A ⊆ A lub B.             Proof. apply inc1_trans with (2 := cl_increase _); tauto. Qed.
  Proposition lub_in_r A B   : B ⊆ A lub B.             Proof. apply inc1_trans with (2 := cl_increase _); tauto. Qed.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)

  Notation "x ⊛ y " := (cl (x ∘ y)) (at level 59).

  Proposition closed_times A B : closed (A⊛B).
  Proof. simpl; apply cl_idempotent. Qed.

  Proposition times_monotone A A' B B' : A ⊆ A' -> B ⊆ B' -> A⊛B ⊆ A'⊛B'.
  Proof. simpl; intros ? ?; apply cl_monotone, composes_monotone; auto. Qed.

  Notation top := (fun _ : M => True).
  Notation bot := (cl (fun _ => False)).
  Notation unit := (cl (sg e)). 

  Proposition closed_top     : closed top.         Proof. simpl; intros; auto. Qed. 
  Proposition closed_bot     : closed bot.         Proof. simpl; apply cl_idempotent. Qed.
  Proposition closed_unit    : closed unit.        Proof. simpl; apply cl_idempotent. Qed.
  Proposition top_greatest A : A ⊆ top.            Proof. simpl; tauto. Qed.

  Hint Resolve closed_glb closed_top.

  Fact closed_mglb ll : Forall closed ll -> closed (fold_right (fun x y => x ∩ y) top ll). 
  Proof. induction 1; simpl; auto. Qed.

  Hint Resolve closed_mglb.

  Proposition bot_least A : closed A -> bot ⊆ A.
  Proof. intro H; apply inc1_trans with (2 := H), cl_monotone; tauto. Qed.

  Proposition unit_neutral_1 A : closed A -> unit ⊛ A ⊆ A.
  Proof. 
    intros H; apply inc1_trans with (2 := H).
    rewrite <- cl_prop.
    apply inc1_trans with (1 := @cl_stable_l _ _).
    rewrite <- cl_prop.
    apply composes_neutral_2.
  Qed.

  Proposition unit_neutral_2 A : A ⊆ unit ⊛ A.
  Proof. 
    intros a Ha; simpl.
    generalize (composes_neutral_1 _ _ Ha).
    apply cl_monotone, composes_monotone; auto.
  Qed.
  
(*  Hint Resolve unit_neutral_1 unit_neutral_2. *)

  Proposition unit_neutral A : closed A -> unit ⊛ A ≃ A.
  Proof. 
    intros H; split. 
    revert H; apply unit_neutral_1.
    apply unit_neutral_2.
  Qed.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)

  Proposition times_commute_1 A B : A⊛B ⊆ B⊛A.
  Proof. simpl; apply cl_inc, composes_commute_1. Qed.

  Hint Resolve unit_neutral times_commute_1.
 
  Proposition times_commute A B : A⊛B ≃ B⊛A.
  Proof. split; auto. Qed.

  Proposition unit_neutral' A : closed A -> A ⊛ unit ≃ A.
  Proof. intros ?; apply eq1_trans with (1 := times_commute _ _); auto. Qed.

  Proposition times_associative A B C : (A⊛B)⊛C ≃ A⊛(B⊛C).
  Proof.
    apply eq1_sym, eq1_trans with (1 := cl_equiv_3 _ _ ).
    apply eq1_sym, eq1_trans with (1 := cl_equiv_2 _ _ ).
    apply eq1_sym, composes_associative.
  Qed.

  Proposition times_associative_1 A B C : (A⊛B)⊛C ⊆ A⊛(B⊛C).     Proof. apply times_associative. Qed.
  Proposition times_associative_2 A B C : A⊛(B⊛C) ⊆ (A⊛B)⊛C.     Proof. apply times_associative. Qed.

  Hint Resolve times_associative_1 times_associative_2.

  Proposition times_congruence A A' B B' : A ≃ A' -> B ≃ B' -> A⊛B ≃ A'⊛B'.
  Proof. 
    intros H1 H2.
    apply eq1_trans with (A ⊛ B').
    apply composes_congruent; auto.
    do 2 apply eq1_sym, eq1_trans with (1 := times_commute _ _).
    apply composes_congruent; auto.
  Qed.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)
 
  Proposition adjunction_1 A B C : closed C -> A ⊛ B ⊆ C -> A ⊆ B ⊸ C.
  Proof. intros ? H; apply magicwand_adj_1, inc1_trans with (2 := H); auto. Qed.

  Proposition adjunction_2 A B C : closed C -> A ⊆ B ⊸ C -> A ⊛ B ⊆ C.
  Proof. intros H ?; apply inc1_trans with (2 := H), cl_monotone, magicwand_adj_2; auto. Qed.

  Hint Resolve times_congruence adjunction_1 (* adjunction_2 *).
 
  Proposition adjunction A B C : closed C -> (A ⊛ B ⊆ C <-> A ⊆ B ⊸ C).
  Proof.
    split; [ apply adjunction_1 | apply  adjunction_2 ]; auto.
  Qed.

  Proposition times_bot_distrib_l A : bot ⊛ A ⊆ bot.
  Proof.
    apply adjunction_2; auto.
    apply bot_least; auto.
  Qed.

  Proposition times_bot_distrib_r A : A ⊛ bot ⊆ bot.
  Proof. apply inc1_trans with (1 := @times_commute_1 _ _), times_bot_distrib_l. Qed.
 
  Hint Immediate times_bot_distrib_l times_bot_distrib_r.

  Proposition times_lub_distrib_l A B C : (A lub B) ⊛ C ⊆ (A ⊛ C) lub (B ⊛ C).
  Proof. 
    apply adjunction, lub_out; auto;
    apply adjunction; auto. 
  Qed.

  Proposition times_lub_distrib_r A B C : C ⊛ (A lub B) ⊆ (C ⊛ A) lub (C ⊛ B).
  Proof. 
    apply inc1_trans with (1 := @times_commute_1 _ _),
          inc1_trans with (1 := @times_lub_distrib_l _ _ _); auto.
    apply lub_out; auto.
  Qed.

(*  Section bang. *)

    (* J := { x | x ∈ unit /\ x ∈ x ⊛ x } with unit = cl e and x ⊛ x = cl (x∘x) *)

    Let J x := cl (sg e) x /\ (cl (sg x ∘ sg x)) x.

    Let In_J : forall x, cl (sg e) x -> (cl (sg x ∘ sg x)) x -> J x.
    Proof. split; auto. Qed.

    Let J_inv x : J x -> unit x /\ cl (sg x ∘ sg x) x.
    Proof. auto. Qed.

    Proposition J_inc_unit : J ⊆ unit.
    Proof. induction 1; trivial. Qed.

    Variable K : M -> Prop.

    Notation sub_monoid_hyp_1 := ((cl K) e).
    Notation sub_monoid_hyp_2 := (K ∘ K ⊆ K).
    Notation sub_J_hyp := (K ⊆ J).

    Hypothesis sub_monoid_1 : sub_monoid_hyp_1.
    Hypothesis sub_monoid_2 : sub_monoid_hyp_2.
    Hypothesis sub_J : sub_J_hyp.

    Proposition K_inc_unit : K ⊆ unit.
    Proof. apply (inc1_trans _ J); trivial; apply J_inc_unit. Qed.

   (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ ❗ *)

    Proposition K_compose A B : (K ∩ A) ∘ (K ∩ B) ⊆ K ∩ (A ∘ B).
    Proof.
      intros x Hx.
      induction Hx as [ a b c [ ] [ ] Hc ]; split.
      + apply sub_monoid_2; constructor 1 with a b; auto.
      + constructor 1 with a b; auto.
    Qed.

    Let bang A := cl (K∩A).

    Notation "❗ A" := (bang A) (at level 40, no associativity).

    Fact store_inc_unit A : ❗ A ⊆ unit.
    Proof. 
      apply inc1_trans with (cl K).
      + apply cl_monotone; tauto.
      + apply cl_inc, K_inc_unit.
    Qed.

    Hint Resolve store_inc_unit.

    Proposition closed_store A : closed (❗A).
    Proof. simpl; apply cl_idempotent. Qed.

    Proposition store_dec A : closed A -> ❗A ⊆ A.
    Proof.
      intros HA; simpl.
      apply inc1_trans with (cl A); trivial.
      apply cl_monotone.
      apply glb_out_r.
    Qed.

    Fact store_monotone A B : A ⊆ B -> ❗A ⊆ ❗B.
    Proof.
      intro; apply cl_monotone.
      intros ? []; split; auto.
    Qed.

    Proposition store_der A B : closed B -> ❗A ⊆ B -> ❗A ⊆ ❗B.
    Proof.
      unfold bang.
      intros ? ?; apply cl_monotone; intros x []; split; auto.
    Qed.
 
    Proposition store_unit_1 : unit ⊆ ❗top.
    Proof.
      apply cl_inc.
      intros ? []; apply cl_monotone with K; auto.
    Qed.

    Hint Resolve J_inc_unit.
 
    Proposition store_unit_2 : ❗top ⊆ unit.
    Proof.
      apply cl_inc; trivial.
      apply inc1_trans with J; auto.
      intros ? []; auto.
    Qed.

    Hint Resolve store_unit_1 store_unit_2.

    Proposition store_unit : unit ≃ ❗top.
    Proof. split; auto. Qed.

    (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ ❗ *)

    Proposition store_comp A B : closed A -> closed B -> ❗A ⊛ ❗B ≃ ❗(A∩B).
    Proof.
      intros HA HB; split.
      + apply inc1_trans with (cl ((K glb A) ∘ (K glb B))).
        * apply cl_inc; trivial; apply cl_stable.
        * apply cl_monotone.
          intros x [ a b c [ H1 H2 ] [ H3 H4 ] Hc ].
          assert (H5 : unit a). { apply K_inc_unit; auto. }
          assert (H6 : unit b). { apply K_inc_unit; auto. }
          split; [ | split ].
          - apply sub_monoid_2; constructor 1 with a b; auto.
          - apply unit_neutral_1; auto; apply times_commute_1, cl_increase.
            constructor 1 with a b; auto.
          - apply unit_neutral_1; auto; apply cl_increase.
            constructor 1 with a b; auto.
      + apply cl_inc; trivial.
        intros x (H1 & H2 & H3).
        apply cl_monotone with (sg x ∘ sg x).
        2: { apply sub_J in H1; destruct H1; trivial. }
        intros d [ a b ? ? Hab ]; subst a b; constructor 1 with x x; auto; 
          apply cl_increase; auto.
    Qed.

    Let ltimes := fold_right (fun x y => x ⊛ y) unit.
    Let lcap := fold_right (fun x y => x∩y) top.

    Proposition ltimes_store ll : 
           Forall closed ll 
        -> ltimes (map bang  ll)
         ≃ ❗(lcap ll).
    Proof.
      unfold ltimes, lcap.
      induction 1 as [ | A ll H1 H2 IH2 ]; auto.
      + simpl; auto.
      + simpl.
        apply eq1_trans with (❗A ⊛ ❗(fold_right (fun x y => x ∩ y) top ll)).
        * apply times_congruence; auto.
        * apply eq1_trans with (❗(A ∩ fold_right (fun x y => x ∩ y) top ll)); auto.
          apply store_comp; auto.
    Qed.

    Proposition store_compose_idem A : closed A -> ❗A ⊆ ❗A⊛❗A.
    Proof.
      intros HA.
      apply inc1_trans with (❗(A∩A)).
      + apply store_der. 
        * apply closed_glb; trivial.
        * apply inc1_trans with A.
          - apply store_dec; trivial.
          - tauto.
      + apply (proj2 (store_comp HA HA)).
    Qed.

(*  End bang. *)

  Reserved Notation "'⟦' A '⟧'" (at level 49).
  Reserved Notation "'⟬߭' A '⟭'" (at level 49).
  
  Variable (v : ill_vars -> M -> Prop) (Hv : forall x, cl (v x) ⊆ v x).
  
  Fixpoint Form_sem f :=
    match f with
      | ⟘             => bot
      | ⟙             => top
      | 𝝐              => unit
      | £ x    => v x
      | a -o b => ⟦a⟧ ⊸ ⟦b⟧
      | a ⊗ b  => ⟦a⟧ ⊛ ⟦b⟧
      | a ⊕ b  => ⟦a⟧ lub ⟦b⟧
      | a & b  => ⟦a⟧ glb ⟦b⟧
      | !a     => ❗⟦a⟧
    end
  where "⟦ a ⟧" := (Form_sem a).
  
  Fact closed_Form_sem f : cl (⟦f⟧) ⊆ ⟦f⟧.
  Proof. induction f as [ | [] | | [] ]; simpl; unfold bang; auto. Qed.
  
  Definition list_Form_sem ll := fold_right (fun x y => x⊛y) unit (map Form_sem ll).
   
  Notation "⟬߭  ll ⟭" := (list_Form_sem ll).

  Fact list_Form_sem_cons f ll : ⟬߭f::ll⟭  = ⟦f⟧ ⊛ ⟬߭ll⟭.
  Proof. auto. Qed.

  Fact closed_list_Form_sem ll : cl (⟬߭ll⟭) ⊆ ⟬߭ll⟭.
  Proof. unfold list_Form_sem; induction ll; simpl; auto. Qed.
  
  Hint Resolve closed_Form_sem closed_list_Form_sem.
  
  Fact list_Form_sem_app ll mm : ⟬߭ll++mm⟭ ≃ ⟬߭ll⟭ ⊛⟬߭mm⟭.
  Proof.
    induction ll as [ | f ll IHll ]; simpl app; auto.
    + apply eq1_sym, unit_neutral; auto.
    + apply eq1_sym, eq1_trans with (1 := @times_associative _ _ _), eq1_sym.
      apply times_congruence; auto.
  Qed.
  
  Fact list_Form_sem_perm ll mm: ll ~p mm -> ⟬߭ll⟭  ≃ ⟬߭mm⟭ .
  Proof.
    induction 1 as [ | x l m _ IHl | x y l | l m k ]; auto.
    + apply composes_congruent, cl_eq1; auto.
    + simpl; do 2 apply eq1_sym, eq1_trans with (2 := @times_associative _ _ _).
      apply times_congruence; auto.
    + apply eq1_trans with (⟬߭m⟭ ); auto.
  Qed.

  Fact list_Form_sem_bang ll : ⟬߭‼ll⟭ ≃ ❗ (lcap (map Form_sem ll)).
  Proof.
    unfold list_Form_sem.
    assert (Forall closed (map Form_sem ll)) as Hll.
    { apply Forall_map, Forall_forall; auto. } 
    apply eq1_trans with (2 := ltimes_store Hll).
    rewrite map_map.
    apply equal_eq1; clear Hll.
    induction ll as [ | a ll IHll ]; simpl; auto.
    rewrite IHll; auto.
  Qed.

  (* All the rules of the ILL sequent calculus (including cut) are closed
     under relational phase semantics, hence we deduce the following
     soundness theorem *)

  Theorem ill_Form_sem_sound Γ a : Γ ⊢ a -> ⟬߭Γ⟭  ⊆ ⟦a⟧.
  Proof.
    induction 1 as [ a 
                   | Ga De a H1 H2 IH2
                   | Ga De a b c H1 IH1 H2 IH2
                   | Ga a b H1 IH1
                   | Ga a b c H1 IH1
                   | Ga a b c H1 IH1
                   | Ga a b H1 IH1 H2 IH2
                   | Ga a b H1 IH1 
                   | Ga a H1 IH1
                   | Ga a b H1 IH1
                   | Ga a b H1 IH1

                   | Ga De a b H1 IH1 H2 IH2
                   | Ga a b c H1 IH1
                   | Ga De a b H1 IH1 H2 IH2
                   | Ga a b c H1 IH1 H2 IH2
                   | Ga a b H1 IH1
                   | Ga a b H1 IH1
                   | Ga a
                   | Ga
                   | Ga a H1 IH1
                   |
                   ]; simpl in *; auto.
      (* axiom *)
    + intro; apply unit_neutral'; auto.

      (* permutation *)
    + intros x Hx; apply IH2; revert Hx; apply list_Form_sem_perm; auto.

      (* -o left *)
    + intros x Hx.
      apply IH2.
      revert x Hx.
      apply inc1_trans with (((⟦ a ⟧ ⊸ ⟦ b ⟧) ⊛ ⟬߭Ga⟭)⊛ ⟬߭De⟭).
      * apply inc1_trans with (2 := @times_associative_2 _ _ _).
        apply times_monotone; auto.
        apply list_Form_sem_app.
      * apply times_monotone; auto.
        apply adjunction; auto.
        apply magicwand_monotone; auto.
    + apply adjunction; auto.
      rewrite list_Form_sem_cons in IH1.
      intros; apply IH1; auto.

      (* plus *)
    + apply inc1_trans with (2 := IH1), times_monotone; simpl; tauto.
    + apply inc1_trans with (2 := IH1), times_monotone; simpl; tauto.

      (* bang *)
    + apply inc1_trans with (2 := IH1), times_monotone; auto.
      apply cl_closed; auto; tauto.
    + intros x Hx.
      apply list_Form_sem_bang in Hx; revert x Hx.
      apply store_der; auto.
      intros x Hx; apply IH1, list_Form_sem_bang; auto.
    + intros x Hx; apply IH1.
      apply unit_neutral_1; auto.
      revert x Hx; apply times_monotone; auto.
      apply store_inc_unit.
    + intros x Hx; apply IH1.
      apply times_associative_1.
      revert x Hx; apply times_monotone; auto.
      simpl; intros x Hx; apply store_comp; auto.
      revert x Hx; apply store_monotone; tauto.

      (* cut rule *)
    + intros x Hx.
      apply list_Form_sem_app in Hx.
      apply IH2.
      revert x Hx; apply times_monotone; auto.

      (* times *)
    + intros x Hx; simpl.
      apply IH1.
      revert Hx; do 3 rewrite list_Form_sem_cons; simpl; auto.
    + intros x Hx; apply list_Form_sem_app in Hx.
      revert x Hx; apply times_monotone; auto.

      (* plus *)
    + intros x Hx.
      apply times_lub_distrib_l in Hx.
      revert Hx; apply cl_closed; auto.
      intros ? []; auto.
  
    + (* bot *)
      intros x Hx.
      apply times_bot_distrib_l in Hx.
      revert x Hx; apply bot_least; auto.

      (* unit *)
    + intros x Hx.
      rewrite list_Form_sem_cons in Hx; simpl in Hx.
      apply unit_neutral_1 in Hx; auto.
  Qed.
   
End Relational_phase_semantics.

Local Infix "∘" := (@Composes _ _) (at level 50, no associativity).

Check ill_Form_sem_sound.


