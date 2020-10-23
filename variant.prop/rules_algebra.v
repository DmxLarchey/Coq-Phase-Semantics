(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Permutation.

Require Import utils ill_form phase_sem.

Set Implicit Arguments.

Section Rules.

  Variable (P : list ill_form -> ill_form -> Prop).

  Notation "Γ ⊨ A" := (P Γ A) (at level 70, no associativity).

  Implicit Types (X Y : list ill_form -> Prop).

  Definition cl_ctx X Δ := forall Γ A, (forall ϴ, X ϴ -> ϴ++Γ ⊨ A) 
                                     ->                  Δ++Γ ⊨ A.

  Definition comp_ctx (Γ Δ ϴ : list ill_form) := Γ++Δ ~p ϴ.

  Notation cl := cl_ctx.
  Notation comp := comp_ctx.

  Infix "∘" := (Composes comp_ctx) (at level 50, no associativity).

  Notation J := (fun Γ => cl (sg ∅) Γ /\ cl (sg Γ ∘ sg Γ) Γ).
  Notation K := (fun Γ => ∃ Δ, Γ = ‼Δ).

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ ⟦ ⟧ ⟬߭ ⟭  ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ Γ Δ ϴ ⊨ *)
  
  Fact cl_ctx_increase X : X ⊆ cl X.
  Proof. intros ? ? ? ?; auto. Qed.
  
  Fact cl_ctx_mono X Y : X ⊆ Y -> cl X ⊆ cl Y.
  Proof.
    intros H1 de Hde ga x HY.
    apply Hde.
    intros; apply HY, H1; auto.
  Qed.
  
  Fact cl_ctx_idem X : cl (cl X) ⊆ cl X.
  Proof.
    intros de Hde ga x HX.
    apply Hde.
    intros th Hth.
    apply Hth, HX.
  Qed.

  Hint Resolve cl_ctx_increase cl_ctx_mono cl_ctx_idem.

  Hypothesis P_perm : forall Γ Δ A, Γ ~p Δ -> Γ ⊨ A -> Δ ⊨ A. 

  Local Fact cl_comm Γ Δ : sg Γ ∘ sg Δ ⊆ cl (sg Δ ∘ sg Γ).
  Proof.
    intros _ [ ga de th ? ? Hth ]; subst Γ Δ.
    intros rho x H; apply H.
    constructor 1 with de ga; auto.
    revert Hth; unfold comp.
    apply perm_trans, Permutation_app_comm.
  Qed.
  
  Local Fact cl_neutral_1 : forall Γ, cl (sg ∅ ∘ sg Γ) Γ.
  Proof.
    intros ga th x H.
    apply H.
    constructor 1 with nil ga; auto.
    red; simpl; auto.
  Qed.

  Local Fact cl_neutral_2 : forall Γ, sg ∅ ∘ sg Γ ⊆ cl (sg Γ).
  Proof.
    intros ga ? [ de th ka ? ? H1 ] rho x G; subst th de.
    cbv in H1.
    generalize (G _ eq_refl).
    apply P_perm, Permutation_app; auto.
  Qed.

  Fact cl_ctx_stable_l : forall X Y, cl X ∘ Y ⊆ cl (X ∘ Y).
  Proof.
    intros X Y _ [ ga de th H1 H2 H3 ] rho x HXY.
    red in H1; red in H3.
    apply P_perm with (ga++(de++rho)).
    1: rewrite <- app_ass; apply Permutation_app; auto.
    apply H1.
    intros ka Hka.
    rewrite <- app_ass.
    apply HXY.
    constructor 1 with ka de; auto.
    red; auto.
  Qed.
  
  Local Fact cl_assoc : forall Γ Δ ϴ, sg Γ ∘ (sg Δ ∘ sg ϴ) ⊆ cl ((sg Γ ∘ sg Δ) ∘ sg ϴ).
  Proof.
    intros ga de th _ [ ga' rho ka H2 H3 H4 ].
    destruct H3 as [ de' th' to ]; subst ga' de' th'.
    intros u x Hu.
    specialize (Hu ((ga++de)++th)).
    spec all in Hu.
    constructor 1 with (ga++de) th; auto.
    constructor 1 with ga de; auto.
    red; auto.
    red; auto.
    revert Hu.
    apply P_perm, Permutation_app; auto.
    rewrite app_ass.
    apply Permutation_trans with (2 := H4).
    apply Permutation_app; auto.
  Qed.

  Local Fact sub_monoid_1 : cl K ∅.
  Proof.
    intros ga A H.
    apply H; exists ∅; auto.
  Qed.

  Local Fact sub_monoid_2 : K ∘ K ⊆ K.
  Proof.
    intros _ [ a b c [ga Ha] [de Hb] H ]; subst a b.
    red in H; simpl in H.
    unfold ill_lbang in H.
    rewrite <- map_app in H.
    apply Permutation_map_inv in H.
    destruct H as (th & H1 & H2); subst c.
    exists th; auto.
  Qed.

  Section sub_J_cs.

    Hypothesis P_weak : ∀ Γ Δ A, Δ ⊨ A -> ‼Γ++Δ ⊨ A.
    Hypothesis P_cntr : ∀ Γ Δ A, ‼Γ++‼Γ++Δ ⊨ A -> ‼Γ++Δ ⊨ A.

    Local Fact sub_J_1 : K ⊆ J.
    Proof.
      intros x (de & Hde); subst x.
      constructor; red.
      + intros ga A H.
        specialize (H _ eq_refl); simpl in H.
        apply P_weak; auto.
      + intros ga A H.
        specialize (H (‼de++‼de)).
        spec all in H.
        { constructor 1 with (‼de) (‼de); auto; red; auto. }
        rewrite app_ass in H.
        apply P_cntr; auto.
    Qed.

    Definition rules_sound := ill_Form_sem_sound _ cl_ctx_increase 
                                                   cl_ctx_mono 
                                                   cl_ctx_idem 
                                                   cl_comm 
                                                   cl_ctx_stable_l 
                                                   cl_neutral_1 
                                                   cl_neutral_2 
                                                   cl_assoc
                                                   sub_monoid_1 
                                                   sub_monoid_2 
                                                   sub_J_1.

  End sub_J_cs.

  Section sub_J_cn.
    
    Hypothesis K_inc_J : K ⊆ J.

    Let J_banged Γ : J (‼Γ).
    Proof. apply K_inc_J; exists Γ; auto. Qed.
    
    Let weak Γ : cl (sg nil) (‼Γ).
    Proof. apply J_banged. Qed.

    Let cntr Γ : cl (sg (‼Γ) ∘ sg (‼Γ)) (‼Γ).
    Proof. apply J_banged. Qed.

    Local Fact sub_J_2 Γ Δ A : Δ ⊨ A -> ‼Γ++Δ ⊨ A.
    Proof.
      intros H; apply weak; intros _ []; apply H.
    Qed.

    Local Fact sub_J_3 Γ Δ A : ‼Γ++‼Γ++Δ ⊨ A -> ‼Γ++Δ ⊨ A.
    Proof.
      intros H; apply cntr.
      intros _ [ x y th [] [] H1 ].
      revert H; apply P_perm.
      rewrite <- app_ass; apply Permutation_app; auto.
    Qed.

  End sub_J_cn.

  Fact sub_J_eq : K ⊆ J <-> (∀ Γ Δ A, Δ ⊨ A -> ‼Γ++Δ ⊨ A)
                         /\ (∀ Γ Δ A, ‼Γ++‼Γ++Δ ⊨ A -> ‼Γ++Δ ⊨ A).
  Proof.
    split.
    + split.
      * apply sub_J_2; auto.
      * apply sub_J_3; auto.
    + intros; apply sub_J_1; tauto.
  Qed.

  Notation "↓" := (fun A Γ => Γ ⊨ A).

  Fact dc_closed A : cl (↓A) ⊆ ↓A.
  Proof.
    intros ga Hga; red in Hga.
    rewrite (app_nil_end ga); apply Hga.
    intro; rewrite <- app_nil_end; auto.
  Qed.
  
  Notation sg := (@eq _).
  Infix "⊸" := (Magicwand comp) (at level 51, right associativity).

  Section equivalences.

    (* We show that each rule has an algebraic counterpart *)

    (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ ⟦ ⟧ ⟬߭ ⟭  ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ Γ Δ ϴ ⊨ *)

    Fact rule_ax_eq A : ↓A (A::∅) 
                    <-> A::∅ ⊨ A.
    Proof. split; auto. Qed. 

    Fact rule_limp_l_eq A B : (↓A ⊸ cl (sg (B::∅))) (A -o B::∅)
                          <-> ∀ Γ Δ C, Γ ⊨ A -> B::Δ ⊨ C -> A -o B::Γ++Δ ⊨ C.
    Proof.
      split.
      + intros H Ga De C H1 H2.
        specialize (H (A -o B::Ga)).
        spec all in H.
        constructor 1 with (A -o B :: nil) Ga; auto; red; simpl; auto.
        change (A -o B :: Ga ++ De) with ((A -o B :: Ga) ++ De).
        apply H; intros _ []; auto.
      + intros H0 th Hth de C H.
        destruct Hth as [ rho ga th H1 H2 H3 ].
        subst rho; red in H3; simpl in H3.
        apply P_perm with (A -o B::ga++de).
        { apply Permutation_app with (1 := H3); auto. }
        apply H0; auto.
        apply H with (ϴ := _::∅); auto.
    Qed.
   
    Fact rule_limp_r_eq A B : sg (A::∅) ⊸ ↓B ⊆ ↓(A -o B)
                          <-> ∀ Γ, A::Γ ⊨ B -> Γ ⊨ A -o B.
    Proof.
      split.
      + intros H Ga H1.
        apply H.
        intros _ [ ? ? De [] [] H2 ].
        apply P_perm with (1 := H2).
        apply P_perm with (2 := H1).
        apply Permutation_app_comm with (l := _::nil).
      + intros H th Hth.
        apply H, Hth.
        constructor 1 with th (A :: nil); auto.
        apply Permutation_app_comm.
    Qed.

    Fact rule_times_l_eq A B : cl (sg (A::B::nil)) (A⊗B::nil)
                           <-> ∀ Γ C, A::B::Γ ⊨ C -> A ⊗ B::Γ ⊨ C.
    Proof.
      split.
      + intros H Ga C H1.
        apply H; intros _ []; auto.
      + intros H0 ? ? H; apply H0, H with (1 := eq_refl). 
    Qed.

    Fact rule_times_r_eq A B : ↓A ∘ ↓B ⊆ ↓(A⊗B)
                           <-> ∀ Γ Δ, Γ ⊨ A -> Δ ⊨ B -> Γ++Δ ⊨ A ⊗ B.
    Proof.
      split.
      + intros H Ga De H1 H2.
        apply H.
        constructor 1 with Ga De; auto; red; auto.
      + intros H _ [ Ga Gb Gc HGa HGb HGc ].
        apply P_perm with (1 := HGc).
        apply H; auto.
    Qed.

    Fact rule_with_l1_eq A B : cl (sg (A::∅)) (A&B::∅)
                           <-> ∀ Γ C, A::Γ ⊨ C -> A﹠B::Γ ⊨ C.
    Proof.
      split.
      + intros H Ga C H1.
        apply H; intros _ []; auto.
      + intros H0 ? ? H; apply H0, H with (1 := eq_refl). 
    Qed.

    Fact rule_with_l2_eq A B : cl (sg (B::∅)) (A&B::∅)
                           <-> ∀ Γ C, B::Γ ⊨ C -> A﹠B::Γ ⊨ C.
    Proof. 
      split.
      + intros H Ga C H1.
        apply H; intros _ []; auto.
      + intros H0 ? ? H; apply H0, H with (1 := eq_refl). 
    Qed.

    Fact rule_with_r_eq A B : ↓A ∩ ↓B ⊆ ↓(A & B)
                          <-> ∀ Γ, Γ ⊨ A -> Γ ⊨ B -> Γ ⊨ A﹠B.
    Proof.
      split.
      + intros H Ga H1 H2.
        apply H; auto.
      + intros H ? []; apply H; auto. 
    Qed.

    Fact rule_plus_l_eq A B : cl (sg (A::∅) ∪ sg (B::∅)) (A⊕B::∅)
                          <-> ∀ Γ C, A::Γ ⊨ C -> B::Γ ⊨ C -> A⊕B::Γ ⊨ C.
    Proof.
      split.
      + intros H Ga C H1 H2.
        apply H; intros _ [ [] | [] ]; auto.
      + intros H0 ? ? H; apply H0; apply H with (ϴ := _::∅); auto. 
    Qed.

    Fact rule_plus_r1_eq A B : ↓A ⊆ ↓(A⊕B)
                           <-> ∀ Γ, Γ ⊨ A -> Γ ⊨ A⊕B.
    Proof.
      split.
      + intros H ? ?; apply H; auto.
      + intros H0 ?; apply H0. 
    Qed.

    Fact rule_plus_r2_eq A B : ↓B ⊆ ↓(A⊕B)
                           <-> ∀ Γ, Γ ⊨ B -> Γ ⊨ A⊕B.
    Proof.
      split.
      + intros H ? ?; apply H; auto.
      + intros H0 ?; apply H0. 
    Qed.

    Fact rule_bang_l_eq A : cl (sg (A::∅)) (!A::∅)
                        <-> ∀ Γ B, A::Γ ⊨ B -> !A::Γ ⊨ B.
    Proof.
      split.
      + intros H Ga B H1; apply H; intros _ []; auto.
      + intros H0 ? ? H; apply H0, H with (1 := eq_refl). 
    Qed.

    Fact rule_bang_r_eq A : K ∩ ↓A ⊆ ↓(!A)
                        <-> ∀ Γ, ‼ Γ ⊨ A -> ‼ Γ ⊨ !A.
    Proof.
      split.
      + intros H Ga H1.
        apply H; split; auto.
        exists Ga; auto.
      + intros H0 Ga [ (De & H1) H2 ]; subst.
        apply H0; auto.
    Qed.

    Fact rule_unit_l_eq : cl (sg ∅) (𝝐::nil)
                      <-> ∀ Γ A, Γ ⊨ A -> 𝝐 :: Γ ⊨ A.
    Proof. 
      split.
      + intros H Ga A H1; apply H; intros _ []; auto. 
      + intros H0 ? ? H; apply H0, H with (1 := eq_refl). 
    Qed.

    Fact rule_unit_r_eq : sg ∅ ⊆ ↓𝝐  <-> ∅ ⊨ 𝝐.
    Proof.
      split.
      + intros H; apply H; auto.
      + intros H x []; apply H. 
    Qed.

    Fact rule_bot_l_eq : cl (fun _ => False) (⟘::∅)
                     <-> ∀ Γ A, ⟘ :: Γ ⊨ A.
    Proof. 
      split.
      + intros H Ga A; apply H; tauto.
      + intros H0 ? ? _; apply H0. 
    Qed.

    Fact rule_top_r_eq : (fun _ => True) ⊆ ↓⟙ <-> ∀ Γ, Γ ⊨ ⟙.
    Proof. 
      split.
      + intros H Ga; apply H; auto.
      + intros H ? _; apply H.
    Qed.

  End equivalences.

End Rules.
