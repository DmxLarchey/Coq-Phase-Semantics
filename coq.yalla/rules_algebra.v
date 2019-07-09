(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Utf8_core.

Require Import List_more Permutation_Type genperm_Type.

Require Import utils_tac phase_sem.

Require Import iformulas.

Set Implicit Arguments.

  Notation "X '≡' Y" := ((X->Y)*(Y->X))%type (at level 80, format "X  ≡  Y", no associativity).
  Notation "X '⊆' Y" := (subset X Y) (at level 75, format "X  ⊆  Y", no associativity).
  Notation "A '∩' B" := (fun z => A z * B z : Type)%type (at level 50, format "A  ∩  B", left associativity).
  Notation "A '∪' B" := (fun z => A z + B z : Type)%type (at level 50, format "A  ∪  B", left associativity).
  Notation sg := (@eq _).


Section Rules.

  Variable prov_pred : list iformula -> iformula -> Type.
  Variable perm_bool : bool.

  Notation "Γ ⊨ A" := (prov_pred Γ A) (at level 70, no associativity).
  Notation " x '~~' y " := (PEperm_Type perm_bool x y) (at level 70).
  Hint Resolve PEperm_Type_refl Permutation_Type_app_comm.

  Hypothesis P_perm : forall Γ Δ A, Γ ~~ Δ -> Γ ⊨ A -> Δ ⊨ A.



  Implicit Types (X Y : list iformula -> Type).

  Definition cl_ctx X Ω := forall Γ Δ A, (forall ϴ, X ϴ -> Γ++ϴ++Δ ⊨ A)
                                       ->                  Γ++Ω++Δ ⊨ A.

  Definition comp_ctx (Γ Δ ϴ : list iformula) := Γ++Δ ~~ ϴ.

  Notation cl := cl_ctx.
  Notation comp := comp_ctx.

  Infix "∘" := (Composes comp_ctx) (at level 50, no associativity).

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

  Instance CL_ctx : @ClosureOp (list iformula) :=
    { cl := cl_ctx;
      cl_increase := cl_ctx_increase;
      cl_monotone := cl_ctx_mono;
      cl_idempotent := cl_ctx_idem }.

  Fact cl_comm : perm_bool = true -> forall Γ Δ, sg Γ ∘ sg Δ ⊆ cl (sg Δ ∘ sg Γ).
  Proof.
    intros E ? ? _ [ ga de th ? ? Hth ]; subst Γ Δ.
    intros rho del x H.
    apply H.
    constructor 1 with de ga; auto.
    revert Hth; unfold comp.
    etransitivity; eauto.
    rewrite E; simpl; auto.
  Qed.

  Local Fact cl_neutral_1 : forall Γ, cl (sg ∅ ∘ sg Γ) Γ.
  Proof.
    intros ga de th x H.
    apply H.
    constructor 1 with nil ga; auto.
    red; simpl; reflexivity.
  Qed.

  Local Fact cl_neutral_3 : forall Γ, cl (sg Γ ∘ sg ∅) Γ.
  Proof.
    intros ga de th x H.
    apply H.
    constructor 1 with ga nil; auto.
    red; simpl; rewrite <- app_nil_end; reflexivity.
  Qed.

  Local Fact cl_neutral_2 : forall Γ, sg ∅ ∘ sg Γ ⊆ cl (sg Γ).
  Proof.
    intros ga ? [ de th ka ? ? H1 ] rho om x G; subst th de.
    generalize (G _ eq_refl).
    apply P_perm.
    do 2 (apply PEperm_Type_app; try reflexivity); auto.
  Qed.

  Local Fact cl_neutral_4 : forall Γ, sg Γ ∘ sg ∅ ⊆ cl (sg Γ).
  Proof.
    intros ga ? [ de th ka ? ? H1 ] rho om x G; subst th de.
    red in H1; rewrite <- app_nil_end in H1.
    generalize (G _ eq_refl).
    apply P_perm.
    do 2 (apply PEperm_Type_app; try reflexivity); auto.
  Qed.

  Fact cl_ctx_stable_l : forall X Y, cl X ∘ Y ⊆ cl (X ∘ Y).
  Proof.
    intros X Y _ [ ga de th H1 H2 H3 ] rho om x HXY.
    red in H1; red in H3.
    apply P_perm with (rho++ga++de++om).
    { apply PEperm_Type_app; try reflexivity.
      rewrite <- app_ass.
      apply PEperm_Type_app; try reflexivity; auto. }
    apply H1.
    intros ka Hka.
    replace (rho ++ ka ++ de ++ om)
    with    (rho ++ (ka ++ de) ++ om) by (list_simpl; reflexivity).
    apply HXY.
    constructor 1 with ka de; auto.
    red ; reflexivity.
  Qed.

  Fact cl_ctx_stable_r : forall X Y, X ∘ cl Y ⊆ cl (X ∘ Y).
  Proof.
    intros X Y _ [ ga de th H1 H2 H3 ] rho om x HXY.
    red in H2; red in H3.
    apply P_perm with ((rho++ga)++de++om).
    { rewrite app_ass.
      apply PEperm_Type_app; try reflexivity.
      rewrite <- app_ass.
      apply PEperm_Type_app; try reflexivity; auto. }
    apply H2.
    intros ka Hka.
    replace ((rho ++ ga) ++ ka ++ om)
    with    (rho ++ (ga ++ ka) ++ om) by (list_simpl; reflexivity).
    apply HXY.
    constructor 1 with ga ka; auto.
    red; reflexivity.
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
    + constructor 1 with ga de; auto.
      red; reflexivity.
    + red; reflexivity.
    + revert Hu.
      apply P_perm, PEperm_Type_app; try reflexivity.
      apply PEperm_Type_app; try reflexivity.
      rewrite app_ass.
      etransitivity; try eassumption.
      apply PEperm_Type_app; try reflexivity; auto.
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
    + constructor 1 with de th; auto.
      red; reflexivity.
    + red; reflexivity.
    + revert Hu.
      apply P_perm, PEperm_Type_app; try reflexivity.
      apply PEperm_Type_app; try reflexivity.
      etransitivity; try eassumption.
      rewrite <- app_ass.
      apply PEperm_Type_app; try reflexivity; auto.
  Qed.

  Local Fact cl_commut : perm_bool = true -> forall Γ Δ, sg Γ ∘ sg Δ ⊆ cl (sg Δ ∘ sg Γ).
  Proof.
    intros Hperm ga de th HC.
    destruct HC as [ga' de' th' HC1 HC2 HC] ; subst.
    unfold cl; intros Ga De A H.
    unfold comp in HC; rewrite Hperm in HC; simpl in HC.
    apply P_perm with (Ga ++ (ga'++de') ++ De); simpl.
    { apply Permutation_Type_app; auto.
      apply Permutation_Type_app; auto. }
    apply H.
    unfold comp; econstructor; try reflexivity.
    rewrite Hperm; apply Permutation_Type_app_comm.
  Qed.

  Notation J := (fun Γ => cl (sg ∅) Γ * cl (sg Γ ∘ sg Γ) Γ)%type.
  Notation K := (fun Γ => { Δ | Γ = ‼Δ }).

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
    symmetry in H; apply PEperm_Type_map_inv in H.
    destruct H as [l Heq _].
    exists l; auto.
  Qed.

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
      intros H.
      apply weak.
      intros _ []; apply H.
    Qed.

    Local Fact sub_J_3 ϴ Γ Δ A : ϴ++‼Γ++‼Γ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A.
    Proof.
      intros H.
      apply cntr.
      intros _ [ x y th [] [] H1 ].
      simpl; revert H; apply P_perm.
      rewrite <- (app_ass _ _ Δ).
      apply PEperm_Type_app; try reflexivity.
      apply PEperm_Type_app; try reflexivity; auto.
    Qed.

  End sub_J_cn.

  Fact sub_J_eq : K ⊆ J ≡ (∀ ϴ Γ Δ A, ϴ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A)
                         * (∀ ϴ Γ Δ A, ϴ++‼Γ++‼Γ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A).
  Proof.
    split.
    + split.
      * apply sub_J_2; auto.
      * apply sub_J_3; auto.
    + intros [Hweak Hcntr].
      intros x (de & Hde); subst x.
      constructor; red.
      * intros ga th A H.
        specialize (H _ eq_refl); simpl in H.
        apply Hweak; auto.
      * intros ga th A H.
        specialize (H (‼de++‼de)).
        spec all in H.
        { constructor 1 with (‼de) (‼de); auto; red; reflexivity. }
        rewrite app_ass in H.
        apply Hcntr; auto.
  Qed.

  Section Rules_Soundness.

    Hypothesis P_weak : ∀ ϴ Γ Δ A, ϴ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A.
    Hypothesis P_cntr : ∀ ϴ Γ Δ A, ϴ++‼Γ++‼Γ++Δ ⊨ A -> ϴ++‼Γ++Δ ⊨ A.

    Local Fact sub_J_1 : K ⊆ J.
    Proof. apply sub_J_eq; auto. Qed.

    Instance PS_ctx : PhaseSpace perm_bool :=
    { Web := list iformula;
      PSCL := CL_ctx;
      PSCompose := comp_ctx;
      PSunit := nil;
      PSExp := K;
      PScl_stable_l := cl_ctx_stable_l;
      PScl_stable_r := cl_ctx_stable_r;
      PScl_associative_1 := cl_assoc_1;
      PScl_associative_2 := cl_assoc_2;
      PScl_neutral_1 := cl_neutral_1;
      PScl_neutral_2 := cl_neutral_2;
      PScl_neutral_3 := cl_neutral_3;
      PScl_neutral_4 := cl_neutral_4;
      PSsub_monoid_1 := sub_monoid_1;
      PSsub_monoid_2 := sub_monoid_2;
      PSsub_J := sub_J_1;
      PScl_commute := cl_commut
    }.

  End Rules_Soundness.

  Notation "↓" := (fun A Γ => Γ ⊨ A).

  Fact dc_closed A : cl (↓A) ⊆ ↓A.
  Proof.
    intros ga Hga; red in Hga.
    replace ga with (nil++ga++nil) by (list_simpl; reflexivity).
    apply Hga.
    intro; rewrite <- app_nil_end; auto.
  Qed.

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
        constructor 1 with De (A -o B :: nil); auto; red; reflexivity.
        replace (Ga++De++A -o B::Th) with (Ga++(De++A -o B::nil)++Th) by (list_simpl; reflexivity).
        apply H; intros _ []; auto.
      + intros H0 th Hth de om C H.
        destruct Hth as [ rho ga th H1 H2 H3 ].
        subst ga; red in H3; simpl in H3.
        apply P_perm with (de++(rho++A -o B::nil)++om).
        { do 2 (apply PEperm_Type_app; try reflexivity); auto. }
        rewrite app_ass; simpl; apply H0; auto.
        apply H with (ϴ := _::∅); auto.
    Qed.

    Fact rule_neg_l_eq A : (↓A ⊸ cl (sg (N::∅))) (ineg A::∅)
                          ≡ ∀ ϴ Γ Δ C, Γ ⊨ A -> ϴ++N::Δ ⊨ C -> ϴ++Γ++ineg A::Δ ⊨ C.
    Proof.
      split.
      + intros H Ga De Th C H1 H2.
        specialize (H (De++ineg A::nil)).
        spec all in H.
        constructor 1 with De (ineg A :: nil); auto; red; reflexivity.
        replace (Ga++De++ineg A::Th) with (Ga++(De++ineg A::nil)++Th) by (list_simpl; reflexivity).
        apply H; intros _ []; auto.
      + intros H0 th Hth de om C H.
        destruct Hth as [ rho ga th H1 H2 H3 ].
        subst ga; red in H3; simpl in H3.
        apply P_perm with (de++(rho++ineg A::nil)++om).
        { do 2 (apply PEperm_Type_app; try reflexivity); auto. }
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
        apply P_perm with (2 := H1); reflexivity.
      + intros H th Hth.
        apply H, Hth.
        constructor 1 with (A :: nil) th; auto.
        red; reflexivity.
    Qed.

    Fact rule_neg_r_eq A : sg (A::∅) ⊸ ↓N ⊆ ↓(ineg A)
                          ≡ ∀ Γ, A::Γ ⊨ N -> Γ ⊨ ineg A.
    Proof.
      split.
      + intros H Ga H1.
        apply H.
        intros _ [ ? ? De [] [] H2 ].
        apply P_perm with (1 := H2).
        apply P_perm with (2 := H1); reflexivity.
      + intros H th Hth.
        apply H, Hth.
        constructor 1 with (A :: nil) th; auto.
        red; reflexivity.
    Qed.

    Fact rule_rimp_l_eq A B : (cl (sg (B::∅)) ⟜ ↓A) (B o- A::∅)
                          ≡ ∀ ϴ Γ Δ C, Γ ⊨ A -> ϴ++B::Δ ⊨ C -> ϴ++B o- A::Γ++Δ ⊨ C.
    Proof.
      split.
      + intros H Ga De Th C H1 H2.
        specialize (H (B o- A::De)).
        spec all in H.
        constructor 1 with (B o- A::nil) De; auto; red; reflexivity.
        change (Ga++B o- A::De++Th) with (Ga++(B o- A::De)++Th).
        apply H ; intros _ []; auto.
      + intros H0 th Hth de om C H.
        destruct Hth as [ rho ga th H1 H2 H3 ].
        subst rho; red in H3; simpl in H3.
        apply P_perm with (de++(B o- A::ga)++om).
        { do 2 (apply PEperm_Type_app; try reflexivity); auto. }
        simpl; apply H0; auto.
        apply H with (ϴ := _::∅); auto.
    Qed.

    Fact rule_gen_l_eq A : (cl (sg (N::∅)) ⟜ ↓A) (igen A::∅)
                          ≡ ∀ ϴ Γ Δ C, Γ ⊨ A -> ϴ++N::Δ ⊨ C -> ϴ++igen A::Γ++Δ ⊨ C.
    Proof.
      split.
      + intros H Ga De Th C H1 H2.
        specialize (H (igen A::De)).
        spec all in H.
        constructor 1 with (igen A::nil) De; auto; red; reflexivity.
        change (Ga++igen A::De++Th) with (Ga++(igen A::De)++Th).
        apply H ; intros _ []; auto.
      + intros H0 th Hth de om C H.
        destruct Hth as [ rho ga th H1 H2 H3 ].
        subst rho; red in H3; simpl in H3.
        apply P_perm with (de++(igen A::ga)++om).
        { do 2 (apply PEperm_Type_app; try reflexivity); auto. }
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
        apply P_perm with (2 := H1); reflexivity.
      + intros H th Hth.
        apply H, Hth.
        constructor 1 with th (A :: nil); auto.
        red; reflexivity.
    Qed.

    Fact rule_gen_r_eq A : ↓N ⟜ sg (A::∅) ⊆ ↓(igen A)
                          ≡ ∀ Γ, Γ++A::nil ⊨ N -> Γ ⊨ igen A.
    Proof.
      split.
      + intros H Ga H1.
        apply H.
        intros _ [ ? ? De [] [] H2 ].
        apply P_perm with (1 := H2).
        apply P_perm with (2 := H1); reflexivity.
      + intros H th Hth.
        apply H, Hth.
        constructor 1 with th (A :: nil); auto.
        red; reflexivity.
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
        constructor 1 with Ga De; auto; red; reflexivity.
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

    Fact rule_zero_l_eq : cl (fun _ => False) (0::∅)
                     ≡ ∀ ϴ Γ A, ϴ++ 0 :: Γ ⊨ A.
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


