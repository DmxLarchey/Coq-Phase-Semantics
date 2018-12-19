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

Local Infix "~p" := (@perm_t _) (at level 70).

Set Implicit Arguments.

Section Relational_phase_semantics.

  (** We define a sound relational phase sematics for ILL 
      based on stable closures *)

  Variable M : Type.

  Implicit Types A B C : M -> Type.

  Variable cl : (M -> Type) -> (M -> Type).

  Hypothesis cl_increase   : forall A, A ⊆ cl A.
  Hypothesis cl_monotone   : forall A B, A ⊆ B -> cl A ⊆ cl B.
  Hypothesis cl_idempotent : forall A, cl (cl A) ⊆ cl A.
  
  Proposition cl_prop A B : A ⊆ cl B ≡ cl A ⊆ cl B.
  Proof.
    split; intros H x Hx.
    apply cl_idempotent; revert Hx; apply cl_monotone; auto.
    apply H, cl_increase; auto.
  Qed.
  
  Definition cl_inc A B := fst (cl_prop A B).
  Definition inc_cl A B := snd (cl_prop A B). 
  
  Fact cl_eq1 A B : A ≃ B -> cl A ≃ cl B.
  Proof. intros []; split; apply cl_monotone; auto. Qed.

  Hint Resolve cl_inc cl_eq1.

  Notation closed := (fun x : M -> Type => cl x ⊆ x).
  
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

  Variable Compose : M -> M -> M -> Type.

  (* Composition lifted to predicates *)

  Inductive Composes (A B : M -> Type) : M -> Type :=
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
  Notation cl_neutrality_3  := (forall a, cl (sg a ∘ sg e) a).
  Notation cl_neutrality_4  := (forall a, sg a ∘ sg e ⊆ cl (sg a)).
  Notation cl_associativity_1 := (forall a b c, sg a ∘ (sg b ∘ sg c) ⊆ cl ((sg a ∘ sg b) ∘ sg c)).
  Notation cl_associativity_2 := (forall a b c, (sg a ∘ sg b) ∘ sg c ⊆ cl (sg a ∘ (sg b ∘ sg c))).

  (* ⊆ ≃ ∩ ∪ ∘ *)

  Hypothesis cl_stable_l : cl_stability_l.
  Hypothesis cl_stable_r : cl_stability_r.
  
  Proposition cl_stable : cl_stability.  Proof. auto. Qed.

  Hint Resolve cl_stable.

  Hypothesis cl_neutral_1 : cl_neutrality_1.
  Hypothesis cl_neutral_2 : cl_neutrality_2.
  Hypothesis cl_neutral_3 : cl_neutrality_3.
  Hypothesis cl_neutral_4 : cl_neutrality_4.

  Hypothesis cl_associative_1 : cl_associativity_1.
  Hypothesis cl_associative_2 : cl_associativity_2.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ *)

  Definition Magicwand_l A B k := A ∘ sg k ⊆ B.
  Infix "⊸" := Magicwand_l (at level 51, right associativity).

  Proposition magicwand_l_spec A B C : B ∘ A ⊆ C ≡ A ⊆ B ⊸ C.
  Proof.
    split; intros H x Hx.
    intros y Hy; apply H; revert Hy; apply composes_monotone; auto.
    apply sg_inc1; auto.
    destruct Hx as [ a b x Ha Hb Hx ].
    apply (H _ Hb).
    constructor 1 with a b; auto.
  Qed.

  Definition magicwand_l_adj_1 A B C := fst (magicwand_l_spec A B C).
  Definition magicwand_l_adj_2 A B C := snd (magicwand_l_spec A B C).

  Proposition magicwand_l_monotone A A' B B' : A ⊆ A' -> B ⊆ B' -> A' ⊸ B ⊆ A ⊸ B'.
  Proof.
    intros ? HB; apply magicwand_l_adj_1, inc1_trans with (2 := HB).
    intros _ [? ? ? Ha Hb Hc]; apply Hb, In_composes with (3 := Hc); auto.
  Qed.

  Hint Resolve magicwand_l_monotone.

  Proposition cl_magicwand_l_1 X Y : cl (X ⊸ cl Y) ⊆ X ⊸ cl Y.
  Proof. 
    apply magicwand_l_adj_1. 
    apply inc1_trans with (B := cl (X ∘ (X ⊸ cl Y))); auto.
    apply cl_inc; apply magicwand_l_spec; auto. 
  Qed.

  Proposition cl_magicwand_l_2 X Y : cl X ⊸ Y ⊆ X ⊸ Y.
  Proof. apply magicwand_l_monotone; auto. Qed.
 
  Hint Immediate cl_magicwand_l_1 cl_magicwand_l_2.

  Proposition cl_magicwand_l_3 X Y : X ⊸ cl Y ⊆ cl X ⊸ cl Y.
  Proof.
    intros c Hc y.
    apply inc1_trans with (B := cl (X ∘ sg c)); auto.
    apply cl_inc.
    intros ? [ a b d Hb [] ].
    intros; apply Hc. 
    constructor 1 with a c; auto.
  Qed.

  Hint Immediate cl_magicwand_l_3.

  Proposition closed_magicwand_l X Y : closed Y -> closed (X ⊸ Y).
  Proof. 
    simpl; intros ?.
    apply inc1_trans with (B := cl (X ⊸ cl Y)); auto.
    apply cl_monotone, magicwand_l_monotone; auto.
    apply inc1_trans with (B := X ⊸ cl Y); auto.
    apply magicwand_l_monotone; auto.
  Qed.

  Hint Resolve closed_magicwand_l.

  Proposition magicwand_l_eq_1 X Y : X ⊸ cl Y ≃ cl X ⊸ cl Y.
  Proof. split; auto. Qed.

  Proposition magicwand_l_eq_2 X Y : cl (X ⊸ cl Y) ≃ X ⊸ cl Y.
  Proof. split; auto. Qed.

  Proposition magicwand_l_eq_3 X Y : cl (X ⊸ cl Y) ≃ cl X ⊸ cl Y.
  Proof.
    split; auto.
    apply inc1_trans with (B := X ⊸ cl Y); auto.
  Qed.

  Hint Resolve magicwand_l_eq_1 magicwand_l_eq_2 magicwand_l_eq_3.

  Definition Magicwand_r B A k := sg k ∘ A ⊆ B.
  Infix "⟜" := Magicwand_r (at level 52, left associativity).

  Proposition magicwand_r_spec A B C : A ∘ B ⊆ C ≡ A ⊆ C ⟜ B.
  Proof.
    split; intros H x Hx.
    intros y Hy; apply H; revert Hy; apply composes_monotone; auto.
    apply sg_inc1; auto.
    destruct Hx as [ a b x Ha Hb Hx ].
    apply (H _ Ha).
    constructor 1 with a b; auto.
  Qed.

  Definition magicwand_r_adj_1 A B C := fst (magicwand_r_spec A B C).
  Definition magicwand_r_adj_2 A B C := snd (magicwand_r_spec A B C).

  Proposition magicwand_r_monotone A A' B B' : A ⊆ A' -> B ⊆ B' -> B ⟜ A' ⊆ B' ⟜ A.
  Proof.
    intros ? HB; apply magicwand_r_adj_1, inc1_trans with (2 := HB).
    intros _ [? ? ? Ha Hb Hc]; apply Ha, In_composes with (3 := Hc); auto.
  Qed.

  Hint Resolve magicwand_r_monotone.

  Proposition cl_magicwand_r_1 X Y : cl (cl Y ⟜ X) ⊆ cl Y ⟜ cl X.
  Proof. 
    apply magicwand_r_adj_1. 
    apply inc1_trans with (B := cl ((cl Y ⟜ X) ∘ X)); auto.
    apply cl_inc; apply magicwand_r_spec; auto. 
  Qed.

  Proposition cl_magicwand_r_2 X Y : Y ⟜ cl X ⊆ Y ⟜ X.
  Proof. apply magicwand_r_monotone; auto. Qed.
 
  Hint Immediate cl_magicwand_r_1 cl_magicwand_r_2.

  Proposition cl_magicwand_r_3 X Y : cl Y ⟜ X ⊆ cl Y ⟜ cl X.
  Proof.
    intros c Hc y.
    apply inc1_trans with (B := cl (sg c ∘ X)); auto.
    apply cl_inc.
    intros ? [ a b d [] Hb ].
    intros; apply Hc. 
    constructor 1 with c b; auto.
  Qed.

  Hint Immediate cl_magicwand_r_3.

  Proposition closed_magicwand_r X Y : closed Y -> closed (Y ⟜ X).
  Proof. 
    simpl; intros ?.
    apply inc1_trans with (B := cl (cl Y ⟜ X)); auto.
    apply cl_monotone, magicwand_r_monotone; auto.
    apply inc1_trans with (1 := @cl_magicwand_r_1 _ _); auto.
    apply magicwand_r_monotone; auto.
  Qed.

  Hint Resolve closed_magicwand_r.

  Proposition magicwand_r_eq_1 X Y : cl Y ⟜ X ≃ cl Y ⟜ cl X.
  Proof. split; auto. Qed.

  Proposition magicwand_r_eq_2 X Y : cl (cl Y ⟜ X) ≃ cl Y ⟜ X.
  Proof. split; auto. Qed.

  Proposition magicwand_r_eq_3 X Y : cl (cl Y ⟜ X) ≃ cl Y ⟜ cl X.
  Proof. split; auto. Qed.

  Hint Resolve magicwand_r_eq_1 magicwand_r_eq_2 magicwand_r_eq_3.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ *)

  Proposition cl_equiv_2 X Y : cl (cl X ∘ Y) ≃ cl (X ∘ Y).
  Proof. 
    split.
    apply cl_inc; auto.
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Proposition cl_equiv_3 X Y : cl (X ∘ cl Y) ≃ cl (X ∘ Y).
  Proof.
    split.
    apply cl_inc; auto.
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Proposition cl_equiv_4 X Y : cl (cl X ∘ cl Y) ≃ cl (X ∘ Y).
  Proof. 
    split.
    apply cl_inc; auto.
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Hint Immediate cl_equiv_2 cl_equiv_3 cl_equiv_4.

  Proposition composes_associative_1 A B C : A ∘ (B ∘ C) ⊆ cl ((A ∘ B) ∘ C).
  Proof.
    intros _ [a _ k Ha [b c y Hb Hc Hy] Hk].
    generalize (@cl_associative_1 a b c k); intros H.
    spec all in H.
    apply In_composes with (3 := Hk); auto.
    apply In_composes with (3 := Hy); auto.
    revert H.
    apply cl_monotone.
    repeat apply composes_monotone; apply sg_inc1; auto.
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
    repeat apply composes_monotone; apply sg_inc1; auto.
  Qed.

  Hint Immediate composes_associative_2.

  Proposition composes_associative A B C : cl (A ∘ (B ∘ C)) ≃ cl ((A ∘ B) ∘ C).
  Proof. split; auto; apply cl_inc; auto. Qed.

  Hint Immediate composes_associative.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ *)

  Proposition composes_congruent_l_1 A B C : A ⊆ cl B -> C ∘ A ⊆ cl (C ∘ B).
  Proof.
    intros ?.
    apply inc1_trans with (B := cl (C ∘ cl B)); auto.
    apply inc_cl, cl_monotone, composes_monotone; auto.
    apply cl_equiv_3.
  Qed.

  Hint Resolve composes_congruent_l_1.

  Proposition composes_congruent_l A B C : cl A ≃ cl B -> cl (C ∘ A) ≃ cl (C ∘ B).
  Proof. 
    intros [H1 H2].
    generalize (inc_cl H1) (inc_cl H2); intros H3 H4.
    split; apply cl_inc;
    apply inc1_trans with (2 := @cl_stable_r _ _), composes_monotone; auto.
  Qed.

  Proposition composes_congruent_r_1 A B C : A ⊆ cl B -> A ∘ C ⊆ cl (B ∘ C).
  Proof.
    intros ?.
    apply inc1_trans with (B := cl (cl B ∘ C)); auto.
    apply inc_cl, cl_monotone, composes_monotone; auto.
    apply cl_equiv_2.
  Qed.

  Hint Resolve composes_congruent_r_1.

  Proposition composes_congruent_r A B C : cl A ≃ cl B -> cl (A ∘ C) ≃ cl (B ∘ C).
  Proof. 
    intros [H1 H2].
    generalize (inc_cl H1) (inc_cl H2); intros H3 H4.
    split; apply cl_inc;
    apply inc1_trans with (2 := @cl_stable_l _ _), composes_monotone; auto.
  Qed.

  Hint Resolve composes_congruent_l composes_congruent_r. 

  Proposition composes_congruent A B C D : 
               cl A ≃ cl B 
            -> cl C ≃ cl D
            -> cl (A ∘ C) ≃ cl (B ∘ D).
  Proof. intros; apply eq1_trans with (cl (B ∘ C)); auto. Qed.
 
(*

  Proposition composes_assoc_special A A' B B' : cl((A∘A') ∘ (B∘B')) ≃ cl ((A∘B) ∘ (A'∘B')).
  Proof.
    do 2 apply eq1_sym, eq1_trans with (2 := composes_associative _ _ _).
    apply composes_congruent.
    apply eq1_sym, eq1_trans with (1 := composes_commute _ _).
    apply eq1_sym, eq1_trans with (2 := composes_associative _ _ _).
    apply composes_congruent, composes_commute.
  Qed.

  Definition composes_assoc_special_1 A A' B B' := fst (composes_assoc_special A A' B B').

*)
  
  Proposition composes_neutral_l_1 A : A ⊆ cl (sg e ∘ A).
  Proof.
    intros a Ha.
    generalize (cl_neutral_1 a).
    apply cl_monotone, composes_monotone; auto.
    apply sg_inc1; auto.
  Qed.

  Proposition composes_neutral_l_2 A : sg e ∘ A ⊆ cl A.
  Proof.
    intros _ [y a x [] Ha Hx].
    generalize (@cl_neutral_2 a x); intros H.
    spec all in H.
    constructor 1 with e a; auto.
    revert H; apply cl_monotone, sg_inc1; auto.
  Qed.
  
  Hint Resolve composes_neutral_l_1 composes_neutral_l_2.

  Proposition composes_neutral_l A : cl (sg e ∘ A) ≃ cl A.
  Proof. split; apply cl_inc; auto. Qed.

  Proposition composes_neutral_r_1 A : A ⊆ cl (A ∘ sg e).
  Proof.
    intros a Ha.
    generalize (cl_neutral_3 a).
    apply cl_monotone, composes_monotone; auto.
    apply sg_inc1; auto.
  Qed.

  Proposition composes_neutral_r_2 A : A ∘ sg e ⊆ cl A.
  Proof.
    intros _ [a y x Ha [] Hx].
    generalize (@cl_neutral_4 a x); intros H.
    spec all in H.
    constructor 1 with a e; auto.
    revert H; apply cl_monotone, sg_inc1; auto.
  Qed.
  
  Hint Resolve composes_neutral_r_1 composes_neutral_r_2.

  Proposition composes_neutral_r A : cl (A ∘ sg e) ≃ cl A.
  Proof. split; apply cl_inc; auto. Qed.

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

  Proposition glb_comm A B : A glb B ≃ B glb A.
  Proof. split; apply glb_in; tauto. Qed.

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

  Fact closed_mglb ll : (forall x, In_t x ll -> closed x) -> closed (fold_right (fun x y => x ∩ y) top ll). 
  Proof.
    revert ll; apply Forall_type_rect; simpl; auto.
  Qed.

  Hint Resolve closed_mglb.

  Proposition bot_least A : closed A -> bot ⊆ A.
  Proof. intro H; apply inc1_trans with (2 := H), cl_monotone; tauto. Qed.

  Proposition unit_neutral_l_1 A : closed A -> unit ⊛ A ⊆ A.
  Proof. 
    intros H; apply inc1_trans with (2 := H).
    apply cl_inc.
    apply inc1_trans with (1 := @cl_stable_l _ _).
    apply cl_inc; auto.
  Qed.

  Proposition unit_neutral_l_2 A : A ⊆ unit ⊛ A.
  Proof. 
    intros a Ha; simpl.
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
    intros H; apply inc1_trans with (2 := H).
    apply cl_inc.
    apply inc1_trans with (1 := @cl_stable_r _ _).
    apply cl_inc; auto.
  Qed.

  Proposition unit_neutral_r_2 A : A ⊆ A ⊛ unit.
  Proof. 
    intros a Ha; simpl.
    generalize (composes_neutral_r_1 _ _ Ha).
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Proposition unit_neutral_r A : closed A -> A ⊛ unit ≃ A.
  Proof. 
    intros H; split. 
    revert H; apply unit_neutral_r_1.
    apply unit_neutral_r_2.
  Qed.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)

  Hint Resolve unit_neutral_l unit_neutral_r. 

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
  Proof. intros; apply composes_congruent; auto. Qed.

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ *)
 
  Proposition adjunction_l_1 A B C : closed C -> B ⊛ A ⊆ C -> A ⊆ B ⊸ C.
  Proof. intros ? H; apply magicwand_l_adj_1, inc1_trans with (2 := H); auto. Qed.

  Proposition adjunction_l_2 A B C : closed C -> A ⊆ B ⊸ C -> B ⊛ A ⊆ C.
  Proof. intros H ?; apply inc1_trans with (2 := H), cl_monotone, magicwand_l_adj_2; auto. Qed.

  Hint Resolve times_congruence adjunction_l_1 (* adjunction_2 *).
 
  Proposition adjunction_l A B C : closed C -> (B ⊛ A ⊆ C ≡ A ⊆ B ⊸ C).
  Proof.
    split; [ apply adjunction_l_1 | apply adjunction_l_2 ]; auto.
  Qed.

  Proposition adjunction_r_1 A B C : closed C -> A ⊛ B ⊆ C -> A ⊆ C ⟜ B.
  Proof. intros ? H; apply magicwand_r_adj_1, inc1_trans with (2 := H); auto. Qed.

  Proposition adjunction_r_2 A B C : closed C -> A ⊆ C ⟜ B -> A ⊛ B ⊆ C.
  Proof. intros H ?; apply inc1_trans with (2 := H), cl_monotone, magicwand_r_adj_2; auto. Qed.

  Hint Resolve adjunction_r_1 (* adjunction_2 *).
 
  Proposition adjunction_r A B C : closed C -> (A ⊛ B ⊆ C ≡ A ⊆ C ⟜ B).
  Proof.
    split; [ apply adjunction_r_1 | apply adjunction_r_2 ]; auto.
  Qed.

  Proposition times_bot_distrib_l A : bot ⊛ A ⊆ bot.
  Proof.
    apply adjunction_r_2; auto.
    apply bot_least; auto.
  Qed.

  Proposition times_bot_distrib_r A : A ⊛ bot ⊆ bot.
  Proof.
    apply adjunction_l_2; auto.
    apply bot_least; auto.
  Qed.

  Hint Immediate times_bot_distrib_l times_bot_distrib_r.

  Proposition times_lub_distrib_l A B C : (A lub B) ⊛ C ⊆ (A ⊛ C) lub (B ⊛ C).
  Proof. 
    apply adjunction_r, lub_out; auto;
    apply adjunction_r; auto. 
  Qed.

  Proposition times_lub_distrib_r A B C : C ⊛ (A lub B) ⊆ (C ⊛ A) lub (C ⊛ B).
  Proof.
    apply adjunction_l, lub_out; auto;
    apply adjunction_l; auto. 
  Qed.

  (* J := { x | x ∈ unit /\ x ∈ x ⊛ x } with unit = cl e and x ⊛ x = cl (x∘x) *)

  Let J x := (cl (sg e) x * (cl (sg x ∘ sg x)) x)%type.

  Let In_J : forall x, cl (sg e) x -> (cl (sg x ∘ sg x)) x -> J x.
  Proof. split; auto. Qed.

  Let J_inv x : J x -> unit x * cl (sg x ∘ sg x) x.
  Proof. auto. Qed.

  Proposition J_inc_unit : J ⊆ unit.
  Proof. induction 1; trivial. Qed.

  Variable K : M -> Type.

  Notation sub_monoid_hyp_1 := ((cl K) e).
  Notation sub_monoid_hyp_2 := (K ∘ K ⊆ K).
  Notation sub_J_hyp := (K ⊆ J).

  Hypothesis sub_monoid_1 : sub_monoid_hyp_1.
  Hypothesis sub_monoid_2 : sub_monoid_hyp_2.
  Hypothesis sub_J : sub_J_hyp.

  Proposition K_inc_unit : K ⊆ unit.
  Proof. apply (inc1_trans _ J); trivial; apply J_inc_unit. Qed.

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

  Hint Resolve store_monotone.

  Fact store_congruence A B : A ≃ B -> ❗A ≃ ❗B.
  Proof. intros []; split; eauto. Qed.

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
        - apply unit_neutral_r_1; auto; apply cl_increase.
          constructor 1 with a b; auto.
        - apply unit_neutral_l_1; auto; apply cl_increase.
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
           (forall x, In_t x ll -> closed x) 
        -> ltimes (map bang  ll)
         ≃ ❗(lcap ll).
  Proof.
    unfold ltimes, lcap.
    revert ll.
    apply Forall_type_rect; simpl; auto.
    intros A ll H1 H2 IH2.
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
    + apply (snd (store_comp HA HA)).
  Qed.

  Reserved Notation "'⟦' A '⟧'" (at level 49).
  Reserved Notation "'⟬߭' A '⟭'" (at level 49).
  
  Variable (v : ill_vars -> M -> Type) (Hv : forall x, cl (v x) ⊆ v x).
  
  Fixpoint Form_sem f :=
    match f with
      | ⟘             => bot
      | ⟙             => top
      | 𝝐              => unit
      | £ x    => v x
      | a -o b => ⟦a⟧ ⊸ ⟦b⟧
      | b o- a => ⟦b⟧ ⟜ ⟦a⟧
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

  Fact list_Form_sem_nil : ⟬߭nil⟭ = unit.
  Proof. auto. Qed.

  Fact list_Form_sem_cons f ll : ⟬߭f::ll⟭  = ⟦f⟧ ⊛ ⟬߭ll⟭.
  Proof. auto. Qed.

  Fact closed_list_Form_sem ll : cl (⟬߭ll⟭) ⊆ ⟬߭ll⟭.
  Proof. unfold list_Form_sem; induction ll; simpl; auto. Qed.
  
  Hint Resolve closed_Form_sem closed_list_Form_sem.
  
  Fact list_Form_sem_app ll mm : ⟬߭ll++mm⟭ ≃ ⟬߭ll⟭ ⊛⟬߭mm⟭.
  Proof.
    induction ll as [ | f ll IHll ]; simpl app; auto.
    + apply eq1_sym, unit_neutral_l; auto.
    + apply eq1_sym, eq1_trans with (1 := @times_associative _ _ _), eq1_sym.
      apply times_congruence; auto.
  Qed.

  Fact list_Form_sem_congr_l ll mm pp : ⟬߭mm⟭ ≃ ⟬߭pp⟭  -> ⟬߭ll++mm⟭ ≃ ⟬߭ll++pp⟭.
  Proof.
    intros H.
    do 2 apply eq1_trans with (1 := list_Form_sem_app _ _), eq1_sym.
    apply times_congruence; auto.
  Qed.

  Fact list_Form_sem_congr_r ll mm pp : ⟬߭mm⟭ ≃ ⟬߭pp⟭  -> ⟬߭mm++ll⟭ ≃ ⟬߭pp++ll⟭.
  Proof.
    intros H.
    do 2 apply eq1_trans with (1 := list_Form_sem_app _ _), eq1_sym.
    apply times_congruence; auto.
  Qed.

  Fact list_Form_sem_mono_l ll mm pp : ⟬߭mm⟭ ⊆ ⟬߭pp⟭  -> ⟬߭ll++mm⟭ ⊆ ⟬߭ll++pp⟭.
  Proof.
    intros H.
    apply inc1_trans with (⟬߭ll⟭ ⊛⟬߭mm⟭); [ apply list_Form_sem_app | ].
    apply inc1_trans with (⟬߭ll⟭ ⊛⟬߭pp⟭); [ | apply list_Form_sem_app ].
    apply times_monotone; auto.
  Qed.

  Fact list_Form_sem_mono_r ll mm pp : ⟬߭mm⟭ ⊆ ⟬߭pp⟭  -> ⟬߭mm++ll⟭ ⊆ ⟬߭pp++ll⟭.
  Proof.
    intros H.
    apply inc1_trans with (⟬߭mm⟭ ⊛⟬߭ll⟭); [ apply list_Form_sem_app | ].
    apply inc1_trans with (⟬߭pp⟭ ⊛⟬߭ll⟭); [ | apply list_Form_sem_app ].
    apply times_monotone; auto.
  Qed.

  Fact list_Form_sem_bang ll : ⟬߭‼ll⟭ ≃ ❗ (lcap (map Form_sem ll)).
  Proof.
    unfold list_Form_sem.
    assert (forall x, In_t x (map Form_sem ll) -> closed x) as Hll.
    { induction ll as [ | y ll IHll ].
      + intros _ [].
      + intros x [ ? | Hx ]; subst; auto.
        apply IHll; auto. } 
    apply eq1_trans with (2 := ltimes_store _ Hll).
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
                   | Ga De a b c H1 IH1
                   | Ga De Th a b c H1 IH1 H2 IH2             (* -o left *)
                   | Ga a b H1 IH1
                   | Ga De Th a b c H1 IH1 H2 IH2             (* o- left*)
                   | Ga a b H1 IH1
                   | Ga De a b c H1 IH1                       (* & left1 *)
                   | Ga De a b c H1 IH1
                   | Ga a b H1 IH1 H2 IH2
                   | Ga De a b H1 IH1                         (* ! left *) 
                   | Ga a H1 IH1                              (* ! right *)
                   | Ga De a b H1 IH1                         (* weak *)
                   | Ga De a b H1 IH1                         (* cntr *)

                   | Ga De Th a b H1 IH1 H2 IH2               (* cut *)

                   | Ga De a b c H1 IH1                       (* times left *)
                   | Ga De a b H1 IH1 H2 IH2
                   | Ga De a b c H1 IH1 H2 IH2                (* plus left *)
                   | Ga a b H1 IH1
                   | Ga a b H1 IH1
                   | Ga De a                                  (* bot *)
                   | Ga                                       (* top *)
                   | Ga De a H1 IH1                           (* unit *)
                   |
                   ]; simpl in *; auto.
      (* axiom *)
    + intro; apply unit_neutral_r; auto.

      (* permutation *)
    + intros x Hx; apply IH1; revert x Hx.
      apply list_Form_sem_congr_l.
      change (!a::!b::De) with (‼(a::b::nil)++De).
      change (!b::!a::De) with (‼(b::a::nil)++De).
      apply list_Form_sem_congr_r.
      do 2 apply eq1_trans with (1 := list_Form_sem_bang _), eq1_sym.
      apply store_congruence.
      simpl; tauto.

      (* -o left *)
    + intros x Hx; apply IH2; revert x Hx.
      apply list_Form_sem_mono_l.
      change (b::De) with ((b::nil)++De).
      replace (Ga++a -o b::De) with ((Ga++a -o b::nil)++De).
      2: rewrite app_ass; auto.
      apply list_Form_sem_mono_r.
      apply inc1_trans with (1 := fst (list_Form_sem_app _ _)).
      apply inc1_trans with (⟬߭Ga⟭ ⊛ (⟦ a ⟧ ⊸ ⟦ b ⟧)).
      * apply times_congruence; auto.
        rewrite list_Form_sem_cons, list_Form_sem_nil. 
        apply eq1_sym, unit_neutral_r; auto.
      * apply inc1_trans with (⟦b⟧).
        apply adjunction_l; auto.
        apply magicwand_l_monotone; auto.
        rewrite list_Form_sem_cons, list_Form_sem_nil. 
        apply unit_neutral_r; auto.

    + apply adjunction_l; auto.
 
        (* o- left *)
    + intros x Hx; apply IH2; revert x Hx.
      apply list_Form_sem_mono_l.
      change (b::De) with ((b::nil)++De).
      change (b o- a::Ga++De) with ((b o- a::Ga)++De).
      apply list_Form_sem_mono_r.
      do 2 rewrite list_Form_sem_cons.
      rewrite list_Form_sem_nil.
      apply inc1_trans with (⟦ b ⟧).
      2: apply unit_neutral_r; auto.
      apply adjunction_r; auto.
      apply magicwand_r_monotone; auto.
  
    + apply adjunction_r; auto.
      apply inc1_trans with (2 := IH1).
      apply inc1_trans with (2 := snd (list_Form_sem_app _ _)).
      apply times_monotone; auto.
      rewrite list_Form_sem_cons, list_Form_sem_nil.
      apply unit_neutral_r; auto.

      (* plus *)
    + apply inc1_trans with (2 := IH1).
      apply list_Form_sem_mono_l, times_monotone; auto.
      simpl; tauto.
    + apply inc1_trans with (2 := IH1).
      apply list_Form_sem_mono_l, times_monotone; auto.
      simpl; tauto.

      (* bang *)
    + apply inc1_trans with (2 := IH1), list_Form_sem_mono_l, times_monotone; auto.
      apply cl_closed; auto; tauto.
    + intros x Hx.
      apply list_Form_sem_bang in Hx; revert x Hx.
      apply store_der; auto.
      intros x Hx; apply IH1, list_Form_sem_bang; auto.
    + apply inc1_trans with (2 := IH1), list_Form_sem_mono_l.
      apply inc1_trans with (unit ⊛ ⟬߭ De ⟭).
      * apply times_monotone; simpl; auto.
        apply store_inc_unit.
      * apply unit_neutral_l; auto.
    + apply inc1_trans with (2 := IH1), list_Form_sem_mono_l.
      change (!a::De) with (‼(a::nil)++De) at 1.
      change (!a::!a::De) with (‼(a::a::nil)++De).
      apply list_Form_sem_mono_r.
      apply inc1_trans with (1 := fst (list_Form_sem_bang _)).
      apply inc1_trans with (2 := snd (list_Form_sem_bang _)).
      apply store_monotone; simpl; tauto.

      (* cut rule *)
    + apply inc1_trans with (2 := IH2).
      apply list_Form_sem_mono_l.
      apply inc1_trans with (1 := fst (list_Form_sem_app _ _)).
      rewrite list_Form_sem_cons; apply times_monotone; auto.

      (* times *)
    + apply inc1_trans with (2 := IH1), list_Form_sem_mono_l.
      do 3 rewrite list_Form_sem_cons.
      apply times_associative.
    + apply inc1_trans with (1 := fst (list_Form_sem_app _ _)).
      apply times_monotone; auto.

      (* plus *)
    + (* distrib ... *)
      apply inc1_trans with ((⟬߭Ga⟭ ⊛(⟦a⟧⊛⟬߭De⟭))lub (⟬߭Ga⟭ ⊛(⟦b⟧⊛⟬߭De⟭))).
      2: { apply lub_out; auto.
           * apply inc1_trans with (2 := IH1).
             apply inc1_trans with (2 := snd (list_Form_sem_app _ _)).
             apply times_monotone; auto.
           * apply inc1_trans with (2 := IH2).
             apply inc1_trans with (2 := snd (list_Form_sem_app _ _)).
             apply times_monotone; auto. }
      apply inc1_trans with (1 := fst (list_Form_sem_app _ _)).
      rewrite list_Form_sem_cons.
      apply inc1_trans with (2 := @times_lub_distrib_r _ _ _).
      apply times_monotone; auto.
      apply times_lub_distrib_l.

    + (* bot *)
      intros x Hx.
      apply list_Form_sem_app in Hx.
      rewrite list_Form_sem_cons in Hx.
      apply bot_least; auto.
      apply times_bot_distrib_r with (A := ⟬߭Ga⟭) .
      revert x Hx; apply times_monotone; auto.
      apply times_bot_distrib_l.

      (* unit *)
    + apply inc1_trans with (2 := IH1), list_Form_sem_mono_l.
      apply unit_neutral_l; auto.
  Qed.
   
End Relational_phase_semantics.

Local Infix "∘" := (@Composes _ _) (at level 50, no associativity).

Check ill_Form_sem_sound.


