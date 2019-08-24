Require Import List CRelationClasses CMorphisms.
Require Import List_Type Permutation_Type_more.
Require Import ll_def.
Require Import closure_operators.

Import SetNotations.

Set Implicit Arguments.



Section SetOrthogonality.

  Context {A B : Type}.

  Variable R : A -> B -> Type.

  Definition rdual X := fun y => forall x, X x -> R x y.
  Definition ldual Y := fun x => forall y, Y y -> R x y.

  Notation lbidual := (fun X => ldual (rdual X)).
  Notation rbidual := (fun Y => rdual (ldual Y)).
  Notation rtridual := (fun X => rdual (ldual (rdual X))).
  Notation ltridual := (fun Y => ldual (rdual (ldual Y))).

  Notation lclosed := (fun X => lbidual X ⊆ X).
  Notation rclosed := (fun Y => rbidual Y ⊆ Y).

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

  Lemma ldual_eq_is_lclosed X : forall Y, X ≃ ldual Y -> lclosed X.
  Proof.
  intros Y [Heql Heqr]; auto.
  transitivity (ldual Y); auto.
  apply lmonot.
  transitivity (rbidual Y); auto.
  Qed.

  Lemma ldual_is_lclosed : forall Y, lclosed (ldual Y).
  Proof. intros Y; apply ldual_eq_is_lclosed with Y; reflexivity. Qed.

  Lemma lclosed_is_ldual X : lclosed X -> { Y & X ≃ ldual Y }.
  Proof. intros Heq; exists (rdual X); split; auto. Qed.

  Lemma rdual_eq_is_rclosed Y : forall X, Y ≃ rdual X -> rclosed Y.
  Proof.
  intros X [Heql Heqr]; auto.
  transitivity (rdual X); auto.
  apply rmonot.
  transitivity (lbidual X); auto.
  Qed.

  Lemma rdual_is_lclosed : forall X, rclosed (rdual X).
  Proof. intros X; apply rdual_eq_is_rclosed with X; reflexivity. Qed.

  Lemma rclosed_is_rdual Y : rclosed Y -> { X & Y ≃ rdual X }.
  Proof. intros Heq; exists (ldual Y); split; auto. Qed.

  Instance lclosure : @ClosureOp _ (@subset A).
  Proof. split with lbidual; auto. Defined.

  Instance rclosure : @ClosureOp _ (@subset B).
  Proof. split with rbidual; auto. Defined.

End SetOrthogonality.




Section MonicSetOrthogonality.

  Context {A : Type}.

  Variable R : crelation A.

  Notation dual := (ldual R).
  Notation bidual := (fun X => dual (dual X)).
  Notation tridual := (fun X => dual (dual (dual X))).
  Notation lbidual := (fun X => ldual R (rdual R X)).

  Definition rel_commutativity := forall x y, R x y -> R y x.
  Hypothesis rel_commute : rel_commutativity.

  Lemma lrdual X : ldual R X ≃ rdual R X.
  Proof. split; intros x Hx x' Hx'; apply rel_commute; apply Hx; assumption. Qed.

  Lemma bilbidual X : bidual X ≃ lbidual X.
  Proof. apply ldual_eq; apply lrdual. Qed.

  Lemma bimonot X : X ⊆ bidual X.
  Proof. intros x Hx x' Hx'; auto. Qed.

  Hint Resolve lmonot bimonot.

  Lemma tridual_eq X : dual X ≃ tridual X.
  Proof. split; auto. Qed.

  Hint Resolve tridual_eq.

  Instance bidualCL : @ClosureOp _ (@subset A).
  Proof. split with bidual; auto. Defined.

  Notation closed := (fun X => cl X ⊆ X).

  Lemma dual_eq_is_closed X : forall Y, X ≃ dual Y -> closed X.
  Proof.
  intros Y [Heql Heqr]; auto.
  transitivity (dual Y); auto.
  apply lmonot.
  transitivity (bidual Y); auto.
  Qed.

  Lemma dual_is_closed : forall X, closed (dual X).
  Proof. intros X; apply dual_eq_is_closed with X; reflexivity. Qed.

End MonicSetOrthogonality.




Section MagmaOrthogonality.
  Context {A B : Type}.

  Variable R : A -> B -> Type.
  Variable compose : A -> A -> A.
  Variable unit : A.

  Infix "•" := compose (at level 45, no associativity).
  Notation "𝟏" := unit.
  Infix "∘" := (composes compose) (at level 50, no associativity).
  Notation lbidual := (fun X => @ldual _ _ R (@rdual _ _ R X)).

  Hint Resolve lmonot rmonot lbimonot.

  Instance lbidualCL : ClosureOp := (@lclosure _ _ R).

  Notation closed := (fun X => cl X ⊆ X).
  Infix "⊛" := (fun x y => tensor compose y x) (at level 59).

  Variable adj_compose_l : A -> B -> B.
  Variable adj_compose_r : A -> B -> B.
(* TODO notations black lolypop *)

  Definition rel_associativity_l_l := forall x y z, R x (adj_compose_l y z) -> R (x • y) z.
  Definition rel_associativity_l_r := forall x y z, R (x • y) z -> R x (adj_compose_l y z).
  Definition rel_associativity_r_l := forall x y z, R y (adj_compose_r x z) -> R (x • y) z.
  Definition rel_associativity_r_r := forall x y z, R (x • y) z -> R y (adj_compose_r x z).
  Definition rel_associativity_ll := forall x y z t, R ((x • y) • z) t -> R (x • (y • z)) t.
  Definition rel_associativity_lr := forall x y z t, R (x • (y • z)) t -> R ((x • y) • z) t.
  Definition rel_neutrality_l_1 := forall x z, R (𝟏 • x) z -> R x z.
  Definition rel_neutrality_l_2 := forall x z, R x z -> R (𝟏 • x) z.
  Definition rel_neutrality_r_1 := forall x z, R (x • 𝟏) z -> R x z.
  Definition rel_neutrality_r_2 := forall x z, R x z -> R (x • 𝟏) z.

  Lemma m_rel_associativity_ll : m_associativity compose -> rel_associativity_ll.
  Proof. intros Ha x y z t HR; rewrite Ha; assumption. Qed.

  Lemma m_rel_associativity_lr : m_associativity compose -> rel_associativity_lr.
  Proof. intros Ha x y z t HR; rewrite <- Ha; assumption. Qed.

  Lemma m_rel_neutrality_l_1 : m_neutrality_l compose unit -> rel_neutrality_l_1.
  Proof. intros Hn x y HR; rewrite <- (Hn x) ; assumption. Qed.

  Lemma m_rel_neutrality_l_2 : m_neutrality_l compose unit -> rel_neutrality_l_2.
  Proof. intros Hn x y HR; rewrite (Hn x) ; assumption. Qed.

  Lemma m_rel_neutrality_r_1 : m_neutrality_r compose unit -> rel_neutrality_r_1.
  Proof. intros Hn x y HR; rewrite <- (Hn x) ; assumption. Qed.

  Lemma m_rel_neutrality_r_2 : m_neutrality_r compose unit -> rel_neutrality_r_2.
  Proof. intros Hn x y HR; rewrite (Hn x) ; assumption. Qed.

  Hypothesis rel_associative_l_l : rel_associativity_l_l.
  Hypothesis rel_associative_l_r : rel_associativity_l_r.
  Hypothesis rel_associative_r_l : rel_associativity_r_l.
  Hypothesis rel_associative_r_r : rel_associativity_r_r.
  Hypothesis rel_associative_ll : rel_associativity_ll.
  Hypothesis rel_associative_lr : rel_associativity_lr.
  Hypothesis rel_neutral_l_1 : rel_neutrality_l_1.
  Hypothesis rel_neutral_l_2 : rel_neutrality_l_2.
  Hypothesis rel_neutral_r_1 : rel_neutrality_r_1.
  Hypothesis rel_neutral_r_2 : rel_neutrality_r_2.

  Lemma stable_l : cl_stability_l (composes compose).
  Proof.
  intros X Y _ [x y Hx Hy].
  intros a Ha.
  apply rel_associative_l_l.
  revert x Hx; apply (rtridual_eq _ X) ; intros x Hx.
  apply rel_associative_l_r.
  apply Ha.
  constructor; assumption.
  Qed.

  Lemma stable_r : cl_stability_r (composes compose).
  Proof.
  intros X Y _ [x y Hx Hy].
  intros a Ha.
  apply rel_associative_r_l.
  revert y Hy; apply (rtridual_eq _ Y); intros y Hy.
  apply rel_associative_r_r.
  apply Ha.
  constructor; assumption.
  Qed.

  Lemma stable : cl_stability (composes compose).
  Proof. apply cl_stable; [ apply subset_preorder | apply stable_l | apply stable_r ]. Qed.

  Lemma associative_l : cl_associativity_l (composes compose).
  Proof.
  intros X Y Z x Hx y Hy.
  inversion Hx; subst.
  inversion X1; subst.
  apply rel_associative_ll.
  apply Hy.
  constructor; auto.
  constructor; auto.
  Qed.

  Lemma associative_r : cl_associativity_r (composes compose).
  Proof.
  intros X Y Z x Hx y Hy.
  inversion Hx; subst.
  inversion X0; subst.
  apply rel_associative_lr.
  apply Hy.
  constructor; auto.
  constructor; auto.
  Qed.

  Lemma neutral_l_1 : cl_neutrality_l_1 (composes compose) (sg unit).
  Proof.
  intros X x Hx y Hy.
  apply rel_neutral_l_1.
  apply Hy.
  constructor; auto.
  Qed.

  Lemma neutral_l_2 : cl_neutrality_l_2 (composes compose) (sg unit).
  Proof.
  clear rel_neutral_l_1 rel_neutral_r_1 rel_neutral_r_2.
  intros X x Hx y Hy.
  inversion Hx; subst.
  rewrite <- H.
  apply rel_neutral_l_2; auto.
  Qed.

  Lemma neutral_r_1 : cl_neutrality_r_1 (composes compose) (sg unit).
  Proof.
  intros X x Hx y Hy.
  apply rel_neutral_r_1.
  apply Hy.
  constructor; auto.
  Qed.

  Lemma neutral_r_2 : cl_neutrality_r_2 (composes compose) (sg unit).
  Proof.
  clear rel_neutral_l_1 rel_neutral_l_2 rel_neutral_r_1.
  intros X x Hx y Hy.
  inversion Hx; subst.
  rewrite <- H.
  apply rel_neutral_r_2; auto.
  Qed.

End MagmaOrthogonality.




Section MonicMagmaOrthogonality.

  Context {M : Type}.

  Variable compose : M -> M -> M.
  Variable unit : M.

  Variable Pole : M -> Type.
  Definition R := fun x y => Pole (compose x y).

  Infix "∘" := (composes compose) (at level 50, no associativity).

  Notation dual := (ldual R).
  Notation bidual := (fun X => dual (dual X)).
  Notation tridual := (fun X => dual (dual (dual X))).

  Hint Resolve (@subset_preorder M).

  Definition pl_fcommutativity := forall x y z, R (compose x y) z -> R (compose y x) z.
  Definition pl_neutrality_1 := forall x, Pole (compose unit x) -> Pole x.
  Definition pl_neutrality_2 := forall x, Pole x -> Pole (compose unit x).

  Lemma m_pl_rel_associativity_ll : m_associativity compose -> rel_associativity_ll R compose.
  Proof. intros Ha x y z t; unfold R; rewrite <- ? Ha; intros H; assumption. Qed.

  Lemma m_pl_rel_associativity_lr : m_associativity compose -> rel_associativity_lr R compose.
  Proof. intros Ha x y z t; unfold R; rewrite ? Ha; intros H; assumption. Qed.

  Lemma m_pl_commutativity : m_commutativity compose -> rel_commutativity R.
  Proof. intros Hc x y HR; unfold R; rewrite Hc; assumption. Qed.

  Lemma m_pl_neutrality_1 : m_neutrality_l compose unit -> pl_neutrality_1.
  Proof. intros Hn x HP; rewrite Hn in HP; assumption. Qed.

  Lemma m_pl_neutrality_2 : m_neutrality_l compose unit -> pl_neutrality_2.
  Proof. intros Hn x HP; rewrite Hn; assumption. Qed.

  Hypothesis rel_commute : rel_commutativity R.
  Hypothesis rel_associative_l : rel_associativity_ll R compose.
  Hypothesis rel_associative_r : rel_associativity_lr R compose.
  Hypothesis pl_neutral_1 : pl_neutrality_1.
  Hypothesis pl_neutral_2 : pl_neutrality_2.

  Lemma pl_rel_associative_l_l : rel_associativity_l_l R compose compose.
  Proof.
  intros x y z; unfold R; intros H.
  apply pl_neutral_1.
  apply rel_commute.
  apply rel_associative_r.
  apply rel_commute.
  apply pl_neutral_2; assumption.
  Qed.

  Lemma pl_rel_associative_l_r : rel_associativity_l_r R compose compose.
  Proof.
  intros x y z; unfold R; intros H.
  apply pl_neutral_1.
  apply rel_commute.
  apply rel_associative_l.
  apply rel_commute.
  apply pl_neutral_2; assumption.
  Qed.

  Lemma pl_rel_associative_r_l : rel_associativity_r_l R compose (fun x y => compose y x).
  Proof.
  intros x y z; unfold R; intros H.
  apply rel_commute.
  apply pl_neutral_1.
  apply rel_commute.
  apply rel_associative_l.
  apply rel_commute.
  apply pl_neutral_2.
  apply rel_commute ; assumption.
  Qed.

  Lemma pl_rel_associative_r_r : rel_associativity_r_r R compose (fun x y => compose y x).
  Proof.
  intros x y z; unfold R; intros H.
  apply rel_commute.
  apply pl_neutral_1.
  apply rel_commute.
  apply rel_associative_r.
  apply rel_commute.
  apply pl_neutral_2.
  apply rel_commute ; assumption.
  Qed.

  Lemma pl_rel_neutrality_l_1 : rel_neutrality_l_1 R compose unit.
  Proof.
  intros x y H.
  apply pl_rel_associative_l_r, rel_commute in H.
  apply pl_neutral_1, rel_commute ; assumption.
  Qed.

  Lemma pl_rel_neutrality_l_2 : rel_neutrality_l_2 R compose unit.
  Proof. intros x y H; apply pl_rel_associative_l_l, pl_neutral_2; assumption. Qed.

  Lemma pl_rel_neutrality_r_1 : rel_neutrality_r_1 R compose unit.
  Proof. intros x y H; apply pl_rel_associative_r_r, pl_neutral_1, rel_commute in H; assumption. Qed.

  Lemma pl_rel_neutrality_r_2 : rel_neutrality_r_2 R compose unit.
  Proof. intros x y H; apply pl_rel_associative_r_l, pl_neutral_2, rel_commute; assumption. Qed.

  Instance mbidualCL : @ClosureOp _ (@subset M) := bidualCL rel_commute.

  Lemma mlbidualcl X : cl X ≃ @cl _ _ (lbidualCL R) X.
  Proof. unfold cl, mbidualCL, bidualCL, lbidualCL, lclosure; apply ldual_eq, lrdual; assumption. Qed.

  Notation closed := (fun X => cl X ⊆ X).

  Hint Resolve rel_commute
               pl_rel_associative_l_l pl_rel_associative_l_r pl_rel_associative_r_l pl_rel_associative_r_r
               pl_rel_neutrality_l_1 pl_rel_neutrality_l_2 pl_rel_neutrality_r_1 pl_rel_neutrality_r_2.

  Lemma pole_commute X Y : X ∘ Y ⊆ Pole -> Y ∘ X ⊆ Pole.
  Proof. intros Hp z Hz; inversion Hz; apply rel_commute; apply Hp; constructor; assumption. Qed.

  Lemma compose_adj_l X Y : X ∘ Y ⊆ Pole -> X ⊆ dual Y.
  Proof.
  intros Hp x Hx y Hy.
  apply pole_commute in Hp.
  apply rel_commute.
  apply Hp.
  constructor; assumption.
  Qed.

  Lemma compose_adj_r X Y : X ⊆ dual Y -> X ∘ Y ⊆ Pole.
  Proof. intros Hd x Hx; inversion Hx; apply Hd in X0; apply X0; assumption. Qed.


  Lemma mstable_l : cl_stability_l (composes compose).
  Proof.
  intros X Y _ [x y Hx Hy].
  apply mlbidualcl in Hx; apply mlbidualcl.
  apply (@stable_l _ _ _ _ compose) ; auto.
  constructor; assumption.
  Qed.

  Lemma mstable_r : cl_stability_r (composes compose).
  Proof.
  intros X Y _ [x y Hx Hy].
  apply mlbidualcl in Hy; apply mlbidualcl.
  apply (@stable_r _ _ _ _ (fun x y => compose y x)) ; auto.
  constructor; assumption.
  Qed.

  Lemma mstable : cl_stability (composes compose).
  Proof. apply cl_stable; [ apply subset_preorder | apply mstable_l | apply mstable_r ]. Qed.

  Lemma massociative_l : cl_associativity_l (composes compose).
  Proof. intros X Y Z x Hx; apply mlbidualcl, associative_l; auto. Qed.

  Lemma massociative_r : cl_associativity_r (composes compose).
  Proof.
  intros X Y Z x Hx.
  apply mlbidualcl.
  apply associative_r; auto.
  Qed.

  Lemma mneutral_l_1 : cl_neutrality_l_1 (composes compose) (sg unit).
  Proof. intros X x Hx; apply mlbidualcl; apply neutral_l_1; auto. Qed.

  Lemma mneutral_l_2 : cl_neutrality_l_2 (composes compose) (sg unit).
  Proof. intros X x Hx; apply mlbidualcl; apply (@neutral_l_2 _ _ R) in Hx; auto. Qed.

  Lemma mneutral_r_1 : cl_neutrality_r_1 (composes compose) (sg unit).
  Proof. intros X x Hx; apply mlbidualcl; apply neutral_r_1; auto. Qed.

  Lemma mneutral_r_2 : cl_neutrality_r_2 (composes compose) (sg unit).
  Proof. intros X x Hx; apply mlbidualcl; apply (@neutral_r_2 _ _ R) in Hx; auto. Qed.


  Lemma pole_as_bot : Pole ≃ dual (sg unit).
  Proof.
  split; intros x Hx.
  - intros y Hy; rewrite <- Hy.
    apply rel_commute; apply pl_neutral_2; auto.
  - apply pl_neutral_1; apply rel_commute; auto.
  Qed.

  Lemma pole_closed : closed Pole.
  Proof. apply (dual_eq_is_closed pole_as_bot). Qed.

(*
  Lemma diag_pole X : (dual X) ∘ X ⊆ Pole.
  Proof. apply compose_adj_r; reflexivity. Qed.
*)

  Lemma pole_vs_one : forall X, X ⊆ Pole -> dual X unit.
  Proof. intros X Hd x Hx; apply pl_neutral_2; apply Hd; assumption. Qed.

  Lemma pole_vs_one_2 : forall X, dual X unit -> X ⊆ Pole.
  Proof.
  intros X Hu x Hx.
  apply pole_as_bot.
  intros y Hy; subst.
  apply rel_commute.
  apply Hu; assumption.
  Qed.

  Infix "⊛" := (fun X Y => tensor (composes compose) Y X) (at level 59).

  Lemma tensor_commute_pole X Y : X ⊛ Y ⊆ Pole -> Y ⊛ X ⊆ Pole.
  Proof.
  intros Hp.
  apply cl_closed; [ | apply pole_closed | ]; auto.
  apply pole_commute.
  etransitivity; [ | apply pole_closed ].
  apply le_cl; auto.
  etransitivity; [ eassumption | apply cl_increase ].
  Qed.

  Definition par X Y := (dual (dual X ∘ dual Y)).
  Infix "⅋" := par (at level 59).

  Lemma tensor_as_par X Y : X ⊛ Y ≃ dual (dual Y ⅋ dual X).
  Proof.
  split.
  - apply lmonot; apply lmonot.
    apply composes_monotone; apply bimonot; auto.
  - apply lmonot.
    transitivity (tridual (Y ∘ X)).
    + apply bimonot; auto.
    + apply lmonot.
      transitivity (dual (rdual R Y) ∘ dual (rdual R X));
        [ | transitivity (dual (rdual R (Y ∘ X))) ];
        try apply composes_monotone; try (apply lmonot);
        try (apply lrdual; auto; fail);
        try (refine (fst (lrdual _ _)); auto; fail).
      refine (@cl_stable _ _ _ (lbidualCL R) (composes compose)_ _ Y X);
        [ apply (@stable_l _ _ _ _ compose) | apply (@stable_r _ _ _ _ (fun x y => compose y x)) ]; auto.
  Qed.

  Infix "⊓" := glb (at level 50, no associativity).
  Infix "⊔" := lub (at level 50, no associativity).

  Variable K : M -> Type.
  Hypothesis sub_monoid_1 : pwr_sub_monoid_hyp_1 unit K.
  Hypothesis sub_monoid_2 : pwr_sub_monoid_hyp_2 compose K.
  Hypothesis sub_J : pwr_sub_J_hyp compose unit K.

  Notation "❗ A" := (bang glb K A) (at level 40, no associativity).

  Definition whynot X := dual (K ⊓ (dual X)).
  Notation "❓ A" := (whynot A) (at level 40, no associativity).

  Lemma bang_as_whynot X : closed X -> ❗X ≃ dual (❓ dual X).
  Proof.
  split.
  - apply lmonot ; apply lmonot.
    split; destruct X1; auto.
    apply (@cl_increase _ _ mbidualCL) in x0; assumption.
  - apply lmonot; apply rmonot; split; destruct X1; auto.
  Qed.

End MonicMagmaOrthogonality.

