(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Permutation.

Require Import utils ill_form ill_rules phase_sem.

Set Implicit Arguments.

Local Infix "~!" := perm_bang_t.

Section Rules.

  Variable (P : list ill_form -> ill_form -> Type).

  Notation "Γ ⊨ A" := (P Γ A) (at level 70, no associativity).

  Implicit Types (X Y : list ill_form -> Type).

  Definition cl_ctx X Ω := forall Γ Δ A, (forall ϴ, X ϴ -> Γ++ϴ++Δ ⊨ A) 
                                       ->                  Γ++Ω++Δ ⊨ A.

  Definition comp_ctx (Γ Δ ϴ : list ill_form) := Γ++Δ ~! ϴ.

  Notation cl := cl_ctx.
  Notation comp := comp_ctx.

  Infix "∘" := (Composes comp_ctx) (at level 50, no associativity).

  Notation J := (fun Γ => cl (sg ∅) Γ * cl (sg Γ ∘ sg Γ) Γ)%type.
  Notation K := (fun Γ => { Δ | Γ = ‼Δ }).

  (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ ⟦ ⟧ ⟬߭ ⟭  ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ Γ Δ ϴ ⊨ *)
  
  Fact cl_ctx_increase X : X ⊆ cl X.
  Proof. intros ? ? ? ?; auto. Qed.
  
  Fact cl_ctx_mono X Y : X ⊆ Y -> cl X ⊆ cl Y.
  Proof.
    intros H1 om Hom ga de x HY.
    apply Hom.
    intros; apply HY, H1; auto.
  Qed.
  
  Fact cl_ctx_idem X : cl (cl X) ⊆ cl X.
  Proof.
    intros om Hom ga de x HX.
    apply Hom.
    intros th Hth.
    apply Hth, HX.
  Qed.

  Hint Resolve cl_ctx_increase cl_ctx_mono cl_ctx_idem.

  Hypothesis P_perm : forall Γ Δ A, Γ ~! Δ -> Γ ⊨ A -> Δ ⊨ A. 

  Hint Resolve perm_bang_t_refl.

(*
  Local Fact cl_comm Γ Δ : sg Γ ∘ sg Δ ⊆ cl (sg Δ ∘ sg Γ).
  Proof.
    intros _ [ ga de th ? ? Hth ]; subst Γ Δ.
    intros rho x H; apply H.
    constructor 1 with de ga; auto.
    revert Hth; unfold comp.
    apply perm_t_trans; auto. 
  Qed.
*)
  
  Local Fact cl_neutral_1 : forall Γ, cl (sg ∅ ∘ sg Γ) Γ.
  Proof.
    intros ga de th x H.
    apply H.
    constructor 1 with nil ga; auto.
    red; simpl; auto.
  Qed.

  Local Fact cl_neutral_3 : forall Γ, cl (sg Γ ∘ sg ∅) Γ.
  Proof.
    intros ga de th x H.
    apply H.
    constructor 1 with ga nil; auto.
    red; simpl; rewrite <- app_nil_end; auto. 
  Qed.

  Local Fact cl_neutral_2 : forall Γ, sg ∅ ∘ sg Γ ⊆ cl (sg Γ).
  Proof.
    intros ga ? [ de th ka ? ? H1 ] rho om x G; subst th de.
    cbv in H1.
    generalize (G _ eq_refl).
    apply P_perm.
    do 2 (apply perm_bang_t_app; auto).
  Qed.

  Local Fact cl_neutral_4 : forall Γ, sg Γ ∘ sg ∅ ⊆ cl (sg Γ).
  Proof.
    intros ga ? [ de th ka ? ? H1 ] rho om x G; subst th de.
    red in H1; rewrite <- app_nil_end in H1.
    generalize (G _ eq_refl).
    apply P_perm.
    do 2 (apply perm_bang_t_app; auto).
  Qed.

  Fact cl_ctx_stable_l : forall X Y, cl X ∘ Y ⊆ cl (X ∘ Y).
  Proof.
    intros X Y _ [ ga de th H1 H2 H3 ] rho om x HXY.
    red in H1; red in H3.
    apply P_perm with (rho++ga++de++om).
    1: { apply perm_bang_t_app; auto.
         rewrite <- app_ass. 
         apply perm_bang_t_app; auto. }
    apply H1.
    intros ka Hka.
    replace (rho ++ ka ++ de ++ om)
    with    (rho ++ (ka ++ de) ++ om) by solve list eq.
    apply HXY.
    constructor 1 with ka de; auto.
    red; auto.
  Qed.

  Fact cl_ctx_stable_r : forall X Y, X ∘ cl Y ⊆ cl (X ∘ Y).
  Proof.
    intros X Y _ [ ga de th H1 H2 H3 ] rho om x HXY.
    red in H2; red in H3.
    apply P_perm with ((rho++ga)++de++om).
    1: { rewrite app_ass.
         apply perm_bang_t_app; auto.
         rewrite <- app_ass. 
         apply perm_bang_t_app; auto. }
    apply H2.
    intros ka Hka.
    replace ((rho ++ ga) ++ ka ++ om)
    with    (rho ++ (ga ++ ka) ++ om) by solve list eq.
    apply HXY.
    constructor 1 with ga ka; auto.
    red; auto.
  Qed.
  
  Local Fact cl_assoc_1 : forall Γ Δ ϴ, sg Γ ∘ (sg Δ ∘ sg ϴ) ⊆ cl ((sg Γ ∘ sg Δ) ∘ sg ϴ).
  Proof.
    intros ga de th _ [ ga' rho ka H2 H3 H4 ].
    destruct H3 as [ de' th' to ? ? H3 ]; subst ga' de' th'.
    red in H3, H4.
    intros u x v Hu.
    specialize (Hu ((ga++de)++th)).
    spec all in Hu.
    constructor 1 with (ga++de) th; auto.
    constructor 1 with ga de; auto.
    red; auto.
    red; auto.
    revert Hu.
    apply P_perm, perm_bang_t_app; auto.
    apply perm_bang_t_app; auto.
    rewrite app_ass.
    apply perm_bang_t_trans with (2 := H4).
    apply perm_bang_t_app; auto.
  Qed.

  Local Fact cl_assoc_2 : forall Γ Δ ϴ, (sg Γ ∘ sg Δ) ∘ sg ϴ ⊆ cl (sg Γ ∘ (sg Δ ∘ sg ϴ)).
  Proof.
    intros ga de th _ [ ga' rho ka H2 H3 H4 ].
    destruct H2 as [ de' th' to ? ? H2 ]. subst rho de' th'.
    red in H2, H4.
    intros u x v Hu.
    specialize (Hu (ga++de++th)).
    spec all in Hu.
    constructor 1 with (ga) (de++th); auto.
    constructor 1 with de th; auto.
    red; auto.
    red; auto.
    revert Hu.
    apply P_perm, perm_bang_t_app; auto.
    apply perm_bang_t_app; auto.
    apply perm_bang_t_trans with (2 := H4).
    rewrite <- app_ass.
    apply perm_bang_t_app; auto.
  Qed.

  Local Fact sub_monoid_1 : cl K ∅.
  Proof.
    intros ga de A H.
    apply H; exists ∅; auto.
  Qed.

  Local Fact sub_monoid_2 : K ∘ K ⊆ K.
  Proof.
    intros _ [ a b c [ga Ha] [de Hb] H ]; subst a b.
    red in H; simpl in H.
    unfold ill_lbang in H.
    rewrite <- map_app in H.
    revert H; apply perm_t_map_inv_t.
  Qed.

  Section sub_J_cs.

    Hypothesis P_weak : ∀ ϴ Γ Δ A, ϴ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A.
    Hypothesis P_cntr : ∀ ϴ Γ Δ A, ϴ++‼Γ++‼Γ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A.

    Local Fact sub_J_1 : K ⊆ J.
    Proof.
      intros x (de & Hde); subst x.
      constructor; red.
      + intros ga th A H.
        specialize (H _ eq_refl); simpl in H.
        apply P_weak; auto.
      + intros ga th A H.
        specialize (H (‼de++‼de)).
        spec all in H.
        { constructor 1 with (‼de) (‼de); auto; red; auto. }
        rewrite app_ass in H.
        apply P_cntr; auto.
    Qed.

    Definition rules_sound := ill_Form_sem_sound   cl_ctx_increase 
                                                   cl_ctx_mono 
                                                   cl_ctx_idem 
                                                   cl_ctx_stable_l 
                                                   cl_ctx_stable_r
                                                   cl_neutral_1 
                                                   cl_neutral_2 
                                                   cl_neutral_3 
                                                   cl_neutral_4 
                                                   cl_assoc_1
                                                   cl_assoc_2
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

    Local Fact sub_J_2 ϴ Γ Δ A : ϴ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A.
    Proof.
      intros H; apply weak; intros _ []; apply H.
    Qed.

    Local Fact sub_J_3 ϴ Γ Δ A : ϴ++‼Γ++‼Γ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A.
    Proof.
      intros H; apply cntr.
      intros _ [ x y th [] [] H1 ].
      revert H; apply P_perm.
      apply perm_bang_t_app; auto.
      rewrite <- app_ass.
      apply perm_bang_t_app; auto.
    Qed.

  End sub_J_cn.

  Fact sub_J_eq : K ⊆ J ≡ (∀ ϴ Γ Δ A, ϴ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A)
                         * (∀ ϴ Γ Δ A, ϴ++‼Γ++‼Γ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A).
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
    replace ga with (nil++ga++nil) by solve list eq.
    apply Hga.
    intro; rewrite <- app_nil_end; auto.
  Qed.
  
  Notation sg := (@eq _).
  Infix "⊸" := (Magicwand_l comp) (at level 51, right associativity).
  Infix "⟜" := (Magicwand_r comp) (at level 52, left associativity).

  Section equivalences.

    (* We show that each rule has an algebraic counterpart *)

    (* ⊆ ≃ ∩ ∪ ∘ ⊸ ⊛ ⟦ ⟧ ⟬߭ ⟭  ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ Γ Δ ϴ ⊨ *)

    Fact rule_ax_eq A : ↓A (A::∅) 
                    ≡ A::∅ ⊨ A.
    Proof. split; auto. Qed. 

    Fact rule_limp_l_eq A B : (↓A ⊸ cl (sg (B::∅))) (A -o B::∅)
                          ≡ ∀ ϴ Γ Δ C, Γ ⊨ A -> ϴ++B::Δ ⊨ C -> ϴ++Γ++A -o B::Δ ⊨ C.
    Proof.
      split.
      + intros H Ga De Th C H1 H2.
        specialize (H (De++A -o B::nil)).
        spec all in H.
        constructor 1 with De (A -o B :: nil); auto; red; simpl; auto.
        replace (Ga++De++A -o B::Th) with (Ga++(De++A -o B::nil)++Th) by solve list eq.
        apply H; intros _ []; auto.
      + intros H0 th Hth de om C H.
        destruct Hth as [ rho ga th H1 H2 H3 ].
        subst ga; red in H3; simpl in H3.
        apply P_perm with (de++(rho++A -o B::nil)++om).
        { do 2 (apply perm_bang_t_app; auto). }
        rewrite app_ass; simpl; apply H0; auto.
        apply H with (ϴ := _::∅); auto.
    Qed.
   
    Fact rule_limp_r_eq A B : sg (A::∅) ⊸ ↓B ⊆ ↓(A -o B)
                          ≡ ∀ Γ, A::Γ ⊨ B -> Γ ⊨ A -o B.
    Proof.
      split.
      + intros H Ga H1.
        apply H.
        intros _ [ ? ? De [] [] H2 ].
        apply P_perm with (1 := H2).
        apply P_perm with (2 := H1); auto.
      + intros H th Hth.
        apply H, Hth.
        constructor 1 with (A :: nil) th; auto.
        red; auto.
    Qed.

    Fact rule_rimp_l_eq A B : (cl (sg (B::∅)) ⟜ ↓A) (B o- A::∅)
                          ≡ ∀ ϴ Γ Δ C, Γ ⊨ A -> ϴ++B::Δ ⊨ C -> ϴ++B o- A::Γ++Δ ⊨ C.
    Proof.
      split.
      + intros H Ga De Th C H1 H2.
        specialize (H (B o- A::De)).
        spec all in H.
        constructor 1 with (B o- A::nil) De; auto; red; simpl; auto.
        replace (Ga++B o- A::De++Th) with (Ga++(B o- A::De)++Th) by solve list eq.
        apply H; intros _ []; auto.
      + intros H0 th Hth de om C H.
        destruct Hth as [ rho ga th H1 H2 H3 ].
        subst rho; red in H3; simpl in H3.
        apply P_perm with (de++(B o- A::ga)++om).
        { do 2 (apply perm_bang_t_app; auto). }
        simpl; apply H0; auto.
        apply H with (ϴ := _::∅); auto.
    Qed.
   
    Fact rule_rimp_r_eq A B : ↓B ⟜ sg (A::∅) ⊆ ↓(B o- A)
                          ≡ ∀ Γ, Γ++A::nil ⊨ B -> Γ ⊨ B o- A.
    Proof.
      split.
      + intros H Ga H1.
        apply H.
        intros _ [ ? ? De [] [] H2 ].
        apply P_perm with (1 := H2).
        apply P_perm with (2 := H1); auto.
      + intros H th Hth.
        apply H, Hth.
        constructor 1 with th (A :: nil); auto.
        red; auto.
    Qed.

    Fact rule_times_l_eq A B : cl (sg (A::B::nil)) (A⊗B::nil)
                           ≡ ∀ ϴ Γ C, ϴ++A::B::Γ ⊨ C -> ϴ++A ⊗ B::Γ ⊨ C.
    Proof.
      split.
      + intros H Th Ga C H1.
        apply H; intros _ []; auto.
      + intros H0 ? ? ? H; apply H0, H with (1 := eq_refl). 
    Qed.

    Fact rule_times_r_eq A B : ↓A ∘ ↓B ⊆ ↓(A⊗B)
                           ≡ ∀ Γ Δ, Γ ⊨ A -> Δ ⊨ B -> Γ++Δ ⊨ A ⊗ B.
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
                           ≡ ∀ ϴ Γ C, ϴ++A::Γ ⊨ C -> ϴ++A﹠B::Γ ⊨ C.
    Proof.
      split.
      + intros H Th Ga C H1; apply H; intros _ []; auto.
      + intros H0 ? ? ? H; apply H0, H with (1 := eq_refl). 
    Qed.

    Fact rule_with_l2_eq A B : cl (sg (B::∅)) (A&B::∅)
                           ≡ ∀ ϴ Γ C, ϴ++B::Γ ⊨ C -> ϴ++A﹠B::Γ ⊨ C.
    Proof. 
      split.
      + intros H The Ga C H1; apply H; intros _ []; auto.
      + intros H0 ? ? ? H; apply H0, H with (1 := eq_refl). 
    Qed.

    Fact rule_with_r_eq A B : ↓A ∩ ↓B ⊆ ↓(A & B)
                          ≡ ∀ Γ, Γ ⊨ A -> Γ ⊨ B -> Γ ⊨ A﹠B.
    Proof.
      split.
      + intros H Ga H1 H2; apply H; auto.
      + intros H ? []; apply H; auto. 
    Qed.

    Fact rule_plus_l_eq A B : cl (sg (A::∅) ∪ sg (B::∅)) (A⊕B::∅)
                          ≡ ∀ ϴ Γ C, ϴ++A::Γ ⊨ C -> ϴ++B::Γ ⊨ C -> ϴ++A⊕B::Γ ⊨ C.
    Proof.
      split.
      + intros H Th Ga C H1 H2.
        apply H; intros _ [ [] | [] ]; auto.
      + intros H0 ? ? ? H; apply H0; apply H with (ϴ := _::∅); auto. 
    Qed.

    Fact rule_plus_r1_eq A B : ↓A ⊆ ↓(A⊕B)
                           ≡ ∀ Γ, Γ ⊨ A -> Γ ⊨ A⊕B.
    Proof.
      split.
      + intros H ? ?; apply H; auto.
      + intros H0 ?; apply H0. 
    Qed.

    Fact rule_plus_r2_eq A B : ↓B ⊆ ↓(A⊕B)
                           ≡ ∀ Γ, Γ ⊨ B -> Γ ⊨ A⊕B.
    Proof.
      split.
      + intros H ? ?; apply H; auto.
      + intros H0 ?; apply H0. 
    Qed.

    Fact rule_bang_l_eq A : cl (sg (A::∅)) (!A::∅)
                        ≡ ∀ ϴ Γ B, ϴ++A::Γ ⊨ B -> ϴ++!A::Γ ⊨ B.
    Proof.
      split.
      + intros H Th Ga B H1; apply H; intros _ []; auto.
      + intros H0 ? ? ? H; apply H0, H with (1 := eq_refl). 
    Qed.

    Fact rule_bang_r_eq A : K ∩ ↓A ⊆ ↓(!A)
                        ≡   ∀ Γ, ‼ Γ ⊨ A -> ‼ Γ ⊨ !A.
    Proof.
      split.
      + intros H Ga H1.
        apply H; split; auto.
        exists Ga; auto.
      + intros H0 Ga [ (De & H1) H2 ]; subst.
        apply H0; auto.
    Qed.

    Fact rule_unit_l_eq : cl (sg ∅) (𝝐::nil)
                      ≡ ∀ ϴ Γ A, ϴ++Γ ⊨ A -> ϴ++𝝐 :: Γ ⊨ A.
    Proof. 
      split.
      + intros H Th Ga A H1; apply H; intros _ []; auto. 
      + intros H0 ? ? ? H; apply H0, H with (1 := eq_refl). 
    Qed.

    Fact rule_unit_r_eq : sg ∅ ⊆ ↓𝝐  ≡ ∅ ⊨ 𝝐.
    Proof.
      split.
      + intros H; apply H; auto.
      + intros H x []; apply H. 
    Qed.

    Fact rule_bot_l_eq : cl (fun _ => False) (⟘::∅)
                     ≡ ∀ ϴ Γ A, ϴ++⟘ :: Γ ⊨ A.
    Proof. 
      split.
      + intros H Th Ga A; apply H; tauto.
      + intros H0 ? ? ? _; apply H0. 
    Qed.

    Fact rule_top_r_eq : (fun _ => True) ⊆ ↓⟙ ≡ ∀ Γ, Γ ⊨ ⟙.
    Proof. 
      split.
      + intros H Ga; apply H; auto.
      + intros H ? _; apply H.
    Qed.

  End equivalences.

End Rules.
