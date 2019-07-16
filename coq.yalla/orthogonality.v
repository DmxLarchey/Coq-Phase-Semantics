Require Import List CRelationClasses CMorphisms.
Require Import List_Type Permutation_Type_more.
Require Import ll_def.
Require Import closure_operators.

Notation "⁇ x" := (map wn x) (at level 52).

Notation "X '⊆' Y" := (subset X Y) (at level 75, format "X  ⊆  Y", no associativity).
Notation "X '≃' Y" := (eqset X Y) (at level 75, format "X  ≃  Y", no associativity).
Notation sg := (@eq _).
Notation "A '∩' B" := (fun z => A z * B z : Type)%type (at level 50, format "A  ∩  B", left associativity).
Notation "A '∪' B" := (fun z => A z + B z : Type)%type (at level 50, format "A  ∪  B", left associativity).

Set Implicit Arguments.

Section Set_Orthogonality.

  Context {A B : Type}.

  Variable R : A -> B -> Type.

  Definition rdual X := fun y => forall x, X x -> R x y.
  Definition ldual Y := fun x => forall y, Y y -> R x y.

  Notation lbidual := (fun X => ldual (rdual X)).
  Notation rbidual := (fun Y => rdual (ldual Y)).
  Notation rtridual := (fun X => rdual (ldual (rdual X))).
  Notation ltridual := (fun Y => ldual (rdual (ldual Y))).

  Notation lfact := (fun X => lbidual X ⊆ X).
  Notation rfact := (fun Y => rbidual Y ⊆ Y).

  Lemma rmonot X1 X2 : X1 ⊆ X2 -> rdual X2 ⊆ rdual X1.
  Proof. intros Hsub x Hx x' Hx'; auto. Qed.

  Lemma lmonot Y1 Y2 : Y1 ⊆ Y2 -> ldual Y2 ⊆ ldual Y1.
  Proof. intros Hsub y Hy y' Hy'; auto. Qed.

  Hint Resolve rmonot lmonot.

  Lemma rdual_eq X1 X2 : X1 ≃ X2 -> rdual X1 ≃ rdual X2.
  Proof. intros [Hsub1 Hsub2]; split; auto. Qed.

  Lemma ldual_eq Y1 Y2 : Y1 ≃ Y2 -> ldual Y1 ≃ ldual Y2.
  Proof. intros [Hsub1 Hsub2]; split; auto. Qed.

  Lemma lbimonot X : X ⊆ lbidual X.
  Proof. intros x Hx x' Hx'; auto. Qed.

  Lemma rbimonot Y : Y ⊆ rbidual Y.
  Proof. intros y Hy y' Hy'; auto. Qed.

  Hint Resolve rdual_eq ldual_eq lbimonot rbimonot.

  Lemma lbidual_eq X1 X2 : X1 ≃ X2 -> lbidual X1 ≃ lbidual X2.
  Proof. intros [Hsub1 Hsub2]; split; auto. Qed.

  Lemma rbidual_eq Y1 Y2 : Y1 ≃ Y2 -> rbidual Y1 ≃ rbidual Y2.
  Proof. intros [Hsub1 Hsub2]; split; auto. Qed.

  Lemma rtridual_eq X : rdual X ≃ rtridual X.
  Proof. split; auto. Qed.

  Lemma ltridual_eq Y : ldual Y ≃ ltridual Y.
  Proof. split; auto. Qed.

  Hint Resolve lbidual_eq rbidual_eq rtridual_eq ltridual_eq.

  Lemma ldual_eq_is_lfact X : forall Y, X ≃ ldual Y -> lfact X.
  Proof.
  intros Y [Heql Heqr]; auto.
  apply subset_trans with (ldual Y); auto.
  apply lmonot.
  apply subset_trans with (rbidual Y); auto.
  Qed.

  Lemma ldual_is_lfact : forall Y, lfact (ldual Y).
  Proof. intros Y; apply ldual_eq_is_lfact with Y; reflexivity. Qed.

  Lemma lfact_is_ldual X : lfact X -> { Y & X ≃ ldual Y }.
  Proof. intros Heq; exists (rdual X); split; auto. Qed.

  Lemma rdual_eq_is_rfact Y : forall X, Y ≃ rdual X -> rfact Y.
  Proof.
  intros X [Heql Heqr]; auto.
  apply subset_trans with (rdual X); auto.
  apply rmonot.
  apply subset_trans with (lbidual X); auto.
  Qed.

  Lemma rdual_is_lfact : forall X, rfact (rdual X).
  Proof. intros X; apply rdual_eq_is_rfact with X; reflexivity. Qed.

  Lemma rfact_is_rdual Y : rfact Y -> { X & Y ≃ rdual X }.
  Proof. intros Heq; exists (ldual Y); split; auto. Qed.

  Instance lclosure : @ClosureOp A.
  Proof. split with lbidual; auto. Defined.

  Instance rclosure : @ClosureOp B.
  Proof. split with rbidual; auto. Defined.

End Set_Orthogonality.


Section Monoid_Orthogonality.

  Context {M : Type}.

  Variable Compose : M -> M -> M.
  Variable Unit : M.

  (* Composition lifted to predicates *)
  Inductive MComposes (X Y : M -> Type) : M -> Type :=
    In_composes : forall x y, X x -> Y y -> MComposes X Y (Compose x y).
  Infix "∘" := MComposes (at level 50, no associativity).

  Global Instance MComposes_monotone : Proper (subset ==> subset ==> subset) MComposes.
  Proof. intros X1 Y1 H1 X2 Y2 H2 x [a b Ha Hb]; constructor; auto. Qed.

  Global Instance MComposes_compat : Proper (eqset ==> eqset ==> eqset) MComposes.
  Proof. intros X1 Y1 [H1 H2] X2 Y2 [H3 H4]; split; apply MComposes_monotone; auto. Qed.

  Variable Pole : M -> Type.

  Definition R := fun x y => Pole (Compose x y).

  Definition pole_commute := forall x y, R x y -> R y x.
  Definition pole_fcommute := forall x y z, R (Compose x y) z -> R (Compose y x) z.
  Definition pole_associative_l := forall x y z, R x (Compose y z) -> R (Compose x y) z.
  Definition pole_associative_r := forall x y z, R (Compose x y) z -> R x (Compose y z).
  Definition pole_associative_ll := forall x y z t,
    R (Compose x (Compose y z)) t -> R (Compose (Compose x y) z) t.
  Definition pole_associative_lr := forall x y z t,
    R (Compose (Compose x y) z) t -> R (Compose x (Compose y z)) t.
  Definition pole_neutral_1 := forall x, Pole (Compose Unit x) -> Pole x.
  Definition pole_neutral_2 := forall x, Pole x -> Pole (Compose Unit x).
  Definition pole_neutral_l_1 := forall x z, R (Compose Unit x) z -> R x z.
  Definition pole_neutral_l_2 := forall x z, R x z -> R (Compose Unit x) z.
  Definition pole_neutral_r_1 := forall x z, R (Compose x Unit) z -> R x z.
  Definition pole_neutral_r_2 := forall x z, R x z -> R (Compose x Unit) z.

  Lemma monoid_commute_pole : (forall x y, Compose x y = Compose y x) -> pole_commute.
  Proof.
  intros Hc x y HR.
  unfold R; rewrite Hc; assumption.
  Qed.

  Lemma monoid_associative_pole_l :
    (forall x y z, Compose x (Compose y z) = Compose (Compose x y) z) -> pole_associative_l.
  Proof.
  intros Ha x y z HR.
  unfold R; rewrite <- Ha; assumption.
  Qed.

  Lemma monoid_associative_pole_r :
    (forall x y z, Compose x (Compose y z) = Compose (Compose x y) z) -> pole_associative_r.
  Proof.
  intros Ha x y z HR.
  unfold R; rewrite Ha; assumption.
  Qed.

  Lemma monoid_associative_pole_ll :
    (forall x y z, Compose x (Compose y z) = Compose (Compose x y) z) -> pole_associative_ll.
  Proof.
  intros Ha x y z t HR.
  unfold R in HR; rewrite <- ? Ha in HR.
  unfold R; rewrite <- ? Ha; try assumption.
  Qed.

  Lemma monoid_associative_pole_lr :
    (forall x y z, Compose x (Compose y z) = Compose (Compose x y) z) -> pole_associative_lr.
  Proof.
  intros Ha x y z t HR.
  unfold R in HR; rewrite <- ? Ha in HR.
  unfold R; rewrite <- ? Ha; try assumption.
  Qed.

  Lemma monoid_neutral_pole_1 : (forall x, Compose Unit x = x) -> pole_neutral_1.
  Proof.
  intros Hn x HP.
  rewrite Hn in HP; assumption.
  Qed.

  Lemma monoid_neutral_pole_2 : (forall x, Compose Unit x = x) -> pole_neutral_2.
  Proof.
  intros Hn x HP.
  rewrite Hn; assumption.
  Qed.

  Lemma monoid_neutral_pole_l_1 : (forall x, Compose Unit x = x) -> pole_neutral_l_1.
  Proof.
  intros Hn x y HR.
  unfold R; rewrite <- (Hn x) ; assumption.
  Qed.

  Lemma monoid_neutral_pole_l_2 : (forall x, Compose Unit x = x) -> pole_neutral_l_2.
  Proof.
  intros Hn x y HR.
  unfold R; rewrite (Hn x) ; assumption.
  Qed.

  Lemma monoid_neutral_pole_r_1 : (forall x, Compose x Unit = x) -> pole_neutral_r_1.
  Proof.
  intros Hn x y HR.
  unfold R; rewrite <- (Hn x) ; assumption.
  Qed.

  Lemma monoid_neutral_pole_r_2 : (forall x, Compose x Unit = x) -> pole_neutral_r_2.
  Proof.
  intros Hn x y HR.
  unfold R; rewrite (Hn x) ; assumption.
  Qed.

  Hypothesis commute : pole_commute.
  Hypothesis associative_l : pole_associative_l.
  Hypothesis associative_r : pole_associative_r.
  Hypothesis associative_ll : pole_associative_ll.
  Hypothesis associative_lr : pole_associative_lr.
  Hypothesis neutral_1 : pole_neutral_1.
  Hypothesis neutral_2 : pole_neutral_2.
  Hypothesis neutral_l_1 : pole_neutral_l_1.
  Hypothesis neutral_l_2 : pole_neutral_l_2.
  Hypothesis neutral_r_1 : pole_neutral_r_1.
  Hypothesis neutral_r_2 : pole_neutral_r_2.

  Lemma lrdual X : ldual R X ≃ rdual R X.
  Proof. split; intros x Hx x' Hx'; apply commute; apply Hx; assumption. Qed.

  Notation dual := (ldual R).
  Notation bidual := (fun X => dual (dual X)).
  Notation tridual := (fun X => dual (dual (dual X))).

  Lemma bimonot X : X ⊆ bidual X.
  Proof. intros x Hx x' Hx'; auto. Qed.

  Hint Resolve lmonot bimonot.

  Lemma tridual_eq X : dual X ≃ tridual X.
  Proof. split; auto. Qed.

  Hint Resolve tridual_eq.

  Instance bidualCL : @ClosureOp M.
  Proof. split with bidual; auto. Defined.

  Notation "'fact' X" := (cl X ⊆ X) (at level 50).

  Lemma dual_eq_is_fact X : forall Y, X ≃ dual Y -> fact X.
  Proof.
  intros Y [Heql Heqr]; auto.
  apply subset_trans with (dual Y); auto.
  apply lmonot.
  apply subset_trans with (bidual Y); auto.
  Qed.

  Lemma dual_is_fact : forall X, fact (dual X).
  Proof. intros X; apply dual_eq_is_fact with X; reflexivity. Qed.

  Lemma stability_l : cl_stability_l MComposes.
  Proof.
  intros X Y _ [x y Hx Hy].
  intros a Ha.
  apply associative_l; apply commute.
  revert x Hx; apply (tridual_eq X) ; intros x Hx.
  apply commute; apply associative_r; apply commute.
  apply Ha.
  constructor; assumption.
  Qed.

  Lemma stability_r : cl_stability_r MComposes.
  Proof.
  intros X Y _ [x y Hx Hy].
  intros a Ha.
  apply commute; apply associative_r.
  revert y Hy; apply (tridual_eq Y); intros y Hy.
  apply associative_l.
  apply Ha.
  constructor; assumption.
  Qed.

  Lemma associative_1 : associative_1_g MComposes.
  Proof.
  intros A B C x Hx y Hy.
  inversion Hx; subst.
  inversion X0; subst.
  apply associative_lr; apply commute.
  apply Hy.
  constructor; auto.
  constructor; auto.
  Qed.

  Lemma associative_2 : associative_2_g MComposes.
  Proof.
  intros A B C x Hx y Hy.
  inversion Hx; subst.
  inversion X; subst.
  apply associative_ll; apply commute.
  apply Hy.
  constructor; auto.
  constructor; auto.
  Qed.

  Lemma neutral_l_1_g : neutrality_l_1_g MComposes Unit.
  Proof.
  intros A x Hx y Hy.
  apply neutral_l_1; apply commute.
  apply Hy.
  constructor; auto.
  Qed.

  Lemma neutral_l_2_g : neutrality_l_2_g MComposes Unit.
  Proof.
  intros A x Hx y Hy.
  inversion Hx; subst.
  rewrite <- H.
  apply neutral_l_2; auto.
  Qed.

  Lemma neutral_r_1_g : neutrality_r_1_g MComposes Unit.
  Proof.
  intros A x Hx y Hy.
  apply neutral_r_1; apply commute.
  apply Hy.
  constructor; auto.
  Qed.

  Lemma neutral_r_2_g : neutrality_r_2_g MComposes Unit.
  Proof.
  intros A x Hx y Hy.
  inversion Hx; subst.
  rewrite <- H.
  apply neutral_r_2; auto.
  Qed.

  Lemma commute_pole X Y : X ∘ Y ⊆ Pole -> Y ∘ X ⊆ Pole.
  Proof.
  intros Hp z Hz; inversion Hz.
  apply commute; apply Hp; constructor; assumption.
  Qed.

  Lemma compose_adj_l X Y : X ∘ Y ⊆ Pole -> X ⊆ dual Y.
  Proof.
  intros Hp x Hx y Hy.
  apply commute_pole in Hp.
  apply commute.
  apply Hp.
  constructor; assumption.
  Qed.

  Lemma compose_adj_r X Y : X ⊆ dual Y -> X ∘ Y ⊆ Pole.
  Proof.
  intros Hd x Hx; inversion Hx.
  apply Hd in X0.
  apply X0; assumption.
  Qed.

  Lemma pole_as_bot : Pole ≃ dual (sg Unit).
  Proof.
  split.
  - intros x Hx y Hy.
    rewrite <- Hy.
    apply commute; apply neutral_2; auto.
  - intros x Hx.
    apply neutral_1; apply commute; auto.
  Qed.

  Lemma fact_pole : fact Pole.
  Proof.
  apply (dual_eq_is_fact pole_as_bot).
  Qed.

  Lemma diag_pole X : (dual X) ∘ X ⊆ Pole.
  Proof. apply compose_adj_r; reflexivity. Qed.

  Lemma pole_vs_one : forall X, X ⊆ Pole -> dual X Unit.
  Proof.
  intros X Hd x Hx.
  apply neutral_2.
  apply Hd; assumption.
  Qed.

  Lemma pole_vs_one_2 : forall X, dual X Unit -> X ⊆ Pole.
  Proof.
  intros X Hu x Hx.
  apply cl_increase in Hu.
  apply neutral_1.
  apply Hu.
  apply cl_increase in Hx; assumption.
  Qed.

  Infix "⊛" := (fun X Y => tensor MComposes Y X) (at level 59).

  Lemma times_commute_pole X Y : X ⊛ Y ⊆ Pole -> Y ⊛ X ⊆ Pole.
  Proof.
  intros Hp.
  apply cl_closed; [ apply fact_pole | ].
  apply commute_pole.
  etransitivity; [ | apply fact_pole ].
  apply subset_cl.
  etransitivity; [ eassumption | apply cl_increase ].
  Qed.

  Definition par X Y := (dual (dual X ∘ dual Y)).
  Infix "⅋" := par (at level 59).

  Lemma tensor_as_par X Y : X ⊛ Y ≃ dual (dual Y ⅋ dual X).
  Proof.
  split.
  - apply lmonot; apply lmonot.
    apply MComposes_monotone; apply bimonot.
  - apply lmonot.
    apply subset_trans with (tridual (Y ∘ X)).
    + apply bimonot. 
    + apply lmonot.
      refine (@cl_stable _ _ MComposes _ _ Y X); [ apply stability_l | apply stability_r ].
  Qed.

  Notation "x ⊓ y" := (glb x y) (at level 50, no associativity).
  Notation "x ⊔ y" := (lub x y) (at level 50, no associativity).

  Variable K : M -> Type.
  Hypothesis sub_monoid_1 : sub_monoid_hyp_1 Unit K.
  Hypothesis sub_monoid_2 : sub_monoid_hyp_2 MComposes K.
  Hypothesis sub_J : sub_J_hyp MComposes Unit K.

  Notation "❗ A" := (bang K A) (at level 40, no associativity).

  Definition whynot X := dual (K ∩ (dual X)).
  Notation "❓ A" := (whynot A) (at level 40, no associativity).

  Lemma bang_as_whynot X : fact X -> ❗X ≃ dual (❓ dual X).
  Proof.
  split.
  - apply lmonot ; apply lmonot.
    split; destruct X1; auto.
    apply cl_increase in x0; assumption.
  - apply lmonot; apply rmonot; split; destruct X1; auto.
  Qed.

End Monoid_Orthogonality.










