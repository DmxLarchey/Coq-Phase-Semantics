Require Import List_more List_Type_more Permutation_Type_more.

Lemma app_cons_to_app_cons_app {T : Type} : forall l1 l2 (x : T),
  l1 ++ x :: l2 = (l1 ++ x :: nil) ++ l2.
Proof. intros; rewrite <- app_assoc; reflexivity. Qed.

Lemma app_cons_cons_to_app_cons_cons_app {T : Type} : forall l1 l2 (x y : T),
  l1 ++ x :: y :: l2 = (l1 ++ x :: y :: nil) ++ l2.
Proof. intros; rewrite <- app_assoc; reflexivity. Qed.


Require Import ill_def.
Notation "Γ ⊢ A [ P ]" := (ill P Γ A) (at level 71).
Notation ν := ivar.
Notation "1" := ione.
Infix "⊗" := itens (at level 50).
Infix "⊸" := ilmap (at level 50).
Notation "B ⟜ A" := (ilpam A B) (at level 50).
Infix "﹠" := iwith (at level 50).
Infix "⊕" := iplus (at level 50).
Notation 𝖳 := itop.
Notation "0" := izero.
Notation "!" := ioc.


Require Import orthogonality log_phase_sem log_cut_elim.

Import SetNotations. (* ⊆ ≃ ∩ ∪ ∅ *)
Notation "﹛ x ﹜" := (sg x).


Section Rules.

  Context { Atom Formula : Type }.
  Variable Proof : list Formula -> Formula -> Type.
  Variable ACon : Atom -> Formula.
  Variable NCon : Formula.
  Variable UCon : Formula -> Formula.
  Variable UCon2 : Formula -> Formula.
  Variable BCon : Formula -> Formula -> Formula.
  Variable Ret : Formula.

  Notation "Γ ⊢ A" := (Proof Γ A) (at level 70).
  Notation µ := ACon.
  Notation "☨" := NCon.
  Notation "☡" := UCon.
  Notation "⚡" := UCon2.
  Infix "☮" := BCon (at level 50).


  Definition def_rule_mul_axiom A B :=
    A :: nil ⊢ B.

  Definition def_rule_add_axiom Γ F :=
    Γ ⊢ F.

  Definition def_rule_mul_cut Γ Δ Σ C A :=
    Γ ⊢ A  ->  Δ ++ A :: Σ ⊢ C  ->
    Δ ++ Γ ++ Σ ⊢ C.

  Definition def_rule_exchange Γ Δ C :=
    Γ ⊢ C  ->  Permutation_Type Γ Δ  ->
    Δ ⊢ C.

  Definition def_rule_swap Γ Δ C A B :=
    Γ ++ A :: B :: Δ ⊢ C  ->
    Γ ++ B :: A :: Δ ⊢ C.

  Definition def_rule_wk_left Γ Δ C F :=
    Γ ++ Δ ⊢ C  ->
    Γ ++ F :: Δ ⊢ C.

  Definition def_rule_mul_un_left Γ Δ C A B F :=
    Γ ++ A :: B :: Δ ⊢ C  ->
    Γ ++ F :: Δ ⊢ C.

  Definition def_rule_mul_nul_right F :=
    nil ⊢ F.

  Definition def_rule_mul_bin_right Γ Δ A B F :=
    Γ ⊢ A  ->  Δ ⊢ B  ->
    Γ ++ Δ ⊢ F.

  Definition def_rule_add_nul_left Γ Δ C F :=
    Γ ++ F :: Δ ⊢ C.

  Definition def_rule_add_un_left Γ Δ C A F :=
    Γ ++ A :: Δ ⊢ C  ->
    Γ ++ F :: Δ ⊢ C.

  Definition def_rule_add_bin_left Γ Δ C A B F :=
    Γ ++ A :: Δ ⊢ C  ->  Γ ++ B :: Δ ⊢ C  ->
    Γ ++ F :: Δ ⊢ C.

  Definition def_rule_add_un_right Γ A F :=
    Γ ⊢ A  ->
    Γ ⊢ F.

  Definition def_rule_add_bin_right Γ A B F :=
    Γ ⊢ A  ->  Γ ⊢ B  ->
    Γ ⊢ F.

  Definition def_rule_mul_right_imp_left Γ Δ Σ C A B F :=
    Γ ⊢ A  ->  Δ ++ B :: Σ ⊢ C  ->
    Δ ++ Γ ++ F :: Σ ⊢ C.

  Definition def_rule_mul_left_imp_left Γ Δ Σ C A B F :=
    Γ ⊢ A  ->  Δ ++ B :: Σ ⊢ C  ->
    Δ ++ F :: Γ ++ Σ ⊢ C.

  Definition def_rule_mul_right_imp_right Γ A B F :=
    A :: Γ ⊢ B  ->
    Γ ⊢ F.

  Definition def_rule_mul_left_imp_right Γ A B F :=
    Γ ++ A :: nil ⊢ B  ->
    Γ ⊢ F.

  Definition rule_axiom := (forall A, def_rule_mul_axiom A A).
  Definition rule_cut := (forall Γ Δ Σ C A, def_rule_mul_cut Γ Δ Σ C A).
  Definition rule_axiom_atomic := (forall X, def_rule_mul_axiom (µ X) (µ X)).
  Definition rule_one_left := (forall Γ Δ C, def_rule_wk_left Γ Δ C ☨).
  Definition rule_one_right := (def_rule_mul_nul_right ☨).
  Definition rule_zero_left := (forall Γ Δ C, def_rule_add_nul_left Γ Δ C ☨).
  Definition rule_top_right := (forall Γ, def_rule_add_axiom Γ ☨).
  Definition rule_tensor_left := (forall Γ Δ C A B, def_rule_mul_un_left Γ Δ C A B (A ☮ B)).
  Definition rule_tensor_right := (forall Γ Δ A B, def_rule_mul_bin_right Γ Δ A B (A ☮ B)).
  Definition rule_right_implication_left := (forall Γ Δ Σ C A B, def_rule_mul_right_imp_left Γ Δ Σ C A B (A ☮ B)).
  Definition rule_right_implication_right := (forall Γ A B, def_rule_mul_right_imp_right Γ A B (A ☮ B)).
  Definition rule_left_implication_left := (forall Γ Δ Σ C A B, def_rule_mul_left_imp_left Γ Δ Σ C A B (A ☮ B)).
  Definition rule_left_implication_right := (forall Γ A B, def_rule_mul_left_imp_right Γ A B (A ☮ B)).
  Definition rule_right_negation_left := (forall Γ Δ Σ C A, def_rule_mul_right_imp_left Γ Δ Σ C A Ret (☡ A)).
  Definition rule_right_negation_right := (forall Γ A, def_rule_mul_right_imp_right Γ A Ret (☡ A)).
  Definition rule_left_negation_left := (forall Γ Δ Σ C A, def_rule_mul_left_imp_left Γ Δ Σ C A Ret (☡ A)).
  Definition rule_left_negation_right := (forall Γ A, def_rule_mul_left_imp_right Γ A Ret (☡ A)).
  Definition rule_with_left_1 := (forall Γ Δ C A B, def_rule_add_un_left Γ Δ C A (A ☮ B)).
  Definition rule_with_left_2 := (forall Γ Δ C B A, def_rule_add_un_left Γ Δ C B (A ☮ B)).
  Definition rule_with_right := (forall Γ A B, def_rule_add_bin_right Γ A B (A ☮ B)).
  Definition rule_plus_left := (forall Γ Δ C A B, def_rule_add_bin_left Γ Δ C A B (A ☮ B)).
  Definition rule_plus_right_1 := (forall Γ A B, def_rule_add_un_right Γ A (A ☮ B)).
  Definition rule_plus_right_2 := (forall Γ B A, def_rule_add_un_right Γ B (A ☮ B)).
  Definition rule_dereliction_left := (forall Γ Δ C A, def_rule_add_un_left Γ Δ C A (☡ A)).
  Definition rule_promotion_left := (forall Γ Δ C A, def_rule_add_un_left Γ Δ (☡ C) A (☡ A)).
  Definition rule_dereliction_right := (forall Γ A, def_rule_add_un_right Γ A (☡ A)).
  Definition rule_promotion_right := (forall Γ A, def_rule_add_un_right (map ☡ Γ) A (☡ A)).
  Definition rule_weakening_modal := (forall Γ Δ C A, def_rule_wk_left Γ Δ C (☡ A)).
  Definition rule_contraction_modal := (forall Γ Δ C A, def_rule_mul_un_left Γ Δ C (☡ A) (☡ A) (☡ A)).
  Definition rule_exchange := (forall Γ Δ C, def_rule_exchange Γ Δ C).
  Definition rule_swap := (forall Γ Δ C A B, def_rule_swap Γ Δ C A B).
  Definition rule_swap_modal := (forall Γ Δ C A B, def_rule_swap Γ Δ C (☡ A) (☡ B)).
  Definition rule_gax a := def_rule_add_axiom (fst a) (snd a).

 (* Left rules with constraint on right-hand side *)

  Definition rule_axiom_monad := (forall A, def_rule_mul_axiom A (⚡ A)).
  Definition rule_axiom_atomic_monad := (forall X, def_rule_mul_axiom (µ X) (⚡ (µ X))).
  Definition rule_one_left_monad := (forall Γ Δ C, def_rule_wk_left Γ Δ (⚡ C) ☨).
  Definition rule_zero_left_monad := (forall Γ Δ C, def_rule_add_nul_left Γ Δ (⚡ C) ☨).
  Definition rule_tensor_left_monad := (forall Γ Δ C A B, def_rule_mul_un_left Γ Δ (⚡ C) A B (A ☮ B)).
  Definition rule_right_implication_left_monad :=
    (forall Γ Δ Σ C A B, def_rule_mul_right_imp_left Γ Δ Σ (⚡ C) A B (A ☮ B)).
  Definition rule_left_implication_left_monad :=
   (forall Γ Δ Σ C A B, def_rule_mul_left_imp_left Γ Δ Σ (⚡ C) A B (A ☮ B)).
  Definition rule_right_negation_left_monad :=
    (forall Γ Δ Σ C A, def_rule_mul_right_imp_left Γ Δ Σ (⚡ C) A Ret (☡ A)).
  Definition rule_left_negation_left_monad :=
   (forall Γ Δ Σ C A, def_rule_mul_left_imp_left Γ Δ Σ (⚡ C) A Ret (☡ A)).
  Definition rule_with_left_1_monad := (forall Γ Δ C A B, def_rule_add_un_left Γ Δ (⚡ C) A (A ☮ B)).
  Definition rule_with_left_2_monad := (forall Γ Δ C B A, def_rule_add_un_left Γ Δ (⚡ C) B (A ☮ B)).
  Definition rule_plus_left_monad := (forall Γ Δ C A B, def_rule_add_bin_left Γ Δ (⚡ C) A B (A ☮ B)).
  Definition rule_dereliction_left_monad := (forall Γ Δ C A, def_rule_add_un_left Γ Δ (⚡ C) A (☡ A)).
  Definition rule_weakening_modal_monad := (forall Γ Δ C A, def_rule_wk_left Γ Δ (⚡ C) (☡ A)).
  Definition rule_contraction_modal_monad := (forall Γ Δ C A, def_rule_mul_un_left Γ Δ (⚡ C) (☡ A) (☡ A) (☡ A)).
  Definition rule_exchange_monad := (forall Γ Δ C, def_rule_exchange Γ Δ (⚡ C)).
  Definition rule_swap_monad := (forall Γ Δ C A B, def_rule_swap Γ Δ (⚡ C) A B).
  Definition rule_swap_modal_monad := (forall Γ Δ C A B, def_rule_swap Γ Δ (⚡ C) (☡ A) (☡ B)).

End Rules.


Section PhILL.

  Inductive phformula : Set :=
  | phvar  : IAtom -> phformula
  | phone  : phformula
  | phtens : phformula -> phformula -> phformula
  | phmap  : phformula -> phformula -> phformula
  | phpam  : phformula -> phformula -> phformula
  | phneg  : phformula -> phformula
  | phgen  : phformula -> phformula
  | phtop  : phformula
  | phwith : phformula -> phformula -> phformula
  | phzero : phformula
  | phplus : phformula -> phformula -> phformula
  | phoc   : phformula -> phformula
  | phcl   : phformula -> phformula.

  Notation µ := phvar.
  Notation I := phone.
  Infix "⊙" := phtens (at level 50).
  Infix "⇾" := phmap (at level 51).
  Notation "B ⇽ A" := (phpam A B) (at level 52).
  Infix "⩚" := phwith (at level 50).
  Infix "☩" := phplus (at level 50).
  Notation ᴛ := phtop.
  Notation "𝟢" := phzero.
  Notation "♯" := phoc.
  Notation "◻" := phcl (at level 55).

  Reserved Notation "‹ A ›".
  Fixpoint ill2ph A :=
  match A with
  | ν X => µ X
  | 1 => I
  | A ⊗ B => ◻‹A› ⊙ ◻‹B›
  | A ⊸ B => ◻‹A› ⇾ ◻‹B›
  | igen A => phgen (◻‹A›)
  | B ⟜ A => ◻‹B› ⇽ ◻‹A›
  | ineg A => phneg (◻‹A›)
  | A ﹠ B => ◻‹A› ⩚ ◻‹B›
  | 𝖳 => ᴛ
  | A ⊕ B => ◻‹A› ☩ ◻‹B›
  | 0 => 𝟢
  | !A => ♯(◻‹A›)
  end
  where "‹ A ›" := (ill2ph A).
  Notation "« Γ »" := (map ill2ph Γ).

  Lemma ill2ph_list_oc Γ : « map ! Γ » = map ♯ (map (◻) « Γ »).
  Proof. induction Γ; simpl; [ | rewrite IHΓ ]; reflexivity. Qed.

  Reserved Notation "⌞ A ⌟".
  Fixpoint ph2ill A :=
  match A with
  | µ X => ν X
  | I => 1
  | A ⊙ B => ⌞A⌟ ⊗ ⌞B⌟
  | A ⇾ B => ⌞A⌟ ⊸ ⌞B⌟
  | B ⇽ A => ⌞B⌟ ⟜ ⌞A⌟
  | phgen A => igen ⌞A⌟
  | phneg A => ineg ⌞A⌟
  | A ⩚ B => ⌞A⌟ ﹠ ⌞B⌟
  | ᴛ => 𝖳
  | A ☩ B => ⌞A⌟ ⊕ ⌞B⌟
  | 𝟢 => 0
  | ♯A => !⌞A⌟
  | ◻A => ⌞A⌟
  end
  where "⌞ A ⌟" := (ph2ill A).
  Notation "⌊ Γ ⌋" := (map ph2ill Γ).

  Lemma ph2ill_list_oc Γ : ⌊map ♯ Γ⌋ = map ! ⌊Γ⌋.
  Proof. induction Γ; simpl; [ | rewrite IHΓ ]; reflexivity. Qed.

  Lemma ill2ill A : ⌞‹A›⌟ = A.
  Proof. induction A; simpl; (try rewrite IHA); (try rewrite IHA1); (try rewrite IHA2); reflexivity. Qed.

  Lemma ill2ill_list Γ : ⌊«Γ»⌋ = Γ.
  Proof. induction Γ; [ | simpl; rewrite ill2ill, IHΓ ]; reflexivity. Qed.


  Section PhILLProofs.

    Variable P : ipfrag.

    Definition ill2phgax a :=
    match projT2 (ipgax P) a with
    | (Γ,A) => («Γ»,‹A›)
    end.

    Inductive PhILL : list phformula -> phformula -> Type :=
    | phax : rule_axiom_atomic_monad PhILL phvar phcl
    | phcut { Hcut : ipcut P = true } : rule_cut PhILL
    | phex { Hperm : ipperm P = true } : rule_swap_monad PhILL phcl
    | phex_oc : rule_swap_modal_monad PhILL phoc phcl
    | phtensl : rule_tensor_left_monad PhILL phcl phtens
    | phtensr : rule_tensor_right PhILL phtens
    | phonel : rule_one_left_monad PhILL phone phcl
    | phoner : rule_one_right PhILL phone
    | phmapl : rule_right_implication_left_monad PhILL phcl phmap
    | phmapr : rule_right_implication_right PhILL phmap
    | phpaml : rule_left_implication_left_monad PhILL phcl phpam
    | phpamr : rule_left_implication_right PhILL phpam
    | phnegl : rule_right_negation_left_monad PhILL phneg phcl (µ atN)
    | phnegr : rule_right_negation_right PhILL phneg (◻(µ atN))
    | phgenl : rule_left_negation_left_monad PhILL phgen phcl (µ atN)
    | phgenr : rule_left_negation_right PhILL phgen (◻(µ atN))
    | phwithl1 : rule_with_left_1_monad PhILL phcl phwith
    | phwithl2 : rule_with_left_2_monad PhILL phcl phwith
    | phwithr : rule_with_right PhILL phwith
    | phtopr : rule_top_right PhILL phtop
    | phplusl : rule_plus_left_monad PhILL phcl phplus
    | phplusr1 : rule_plus_right_1 PhILL phplus
    | phplusr2 : rule_plus_right_2 PhILL phplus
    | phzerol : rule_zero_left_monad PhILL phzero phcl
    | phocl : rule_dereliction_left_monad PhILL phoc phcl
    | phocr : rule_promotion_right PhILL phoc
    | phwk : rule_weakening_modal_monad PhILL phoc phcl
    | phco : rule_contraction_modal_monad PhILL phoc phcl
    | phcll : rule_promotion_left PhILL phcl
    | phclr : rule_dereliction_right PhILL phcl
    | phgax : forall a, rule_gax PhILL (ill2phgax a).
    Notation "Γ ⊦ A" := (PhILL Γ A) (at level 70).

    Proposition ill2ph_translation Γ A : Γ ⊢ A [ P ] -> « Γ » ⊦ ◻‹A›.
    Proof.
    intros pi; induction pi; list_simpl; 
     (try list_simpl in IHpi); (try list_simpl in IHpi1); (try list_simpl in IHpi2);
      try (now apply phclr; constructor; assumption);
      try (now constructor; (try apply phcll);
                            (try (rewrite app_cons_to_app_cons_app; apply phcll)); list_simpl; assumption).
    - case_eq (ipperm P); intros HP; rewrite_all HP; simpl in p.
      + revert p IHpi.
        apply (Permutation_Type_morph_transp (fun l => «l» ⊦ ◻‹A›)).
        intros ? ? ? ? H; list_simpl; list_simpl in H; apply (@phex HP); assumption.
      + subst; assumption.
    - revert p IHpi.
      apply (Permutation_Type_morph_transp (fun l => «l1» ++ «map ! l» ++ «l2» ⊦ ◻‹A›)).
      intros ? ? ? ?; list_simpl; rewrite 2 (app_assoc « l1 »).
      apply phex_oc.
    - apply phclr; constructor.
      rewrite <- (app_nil_l _); apply phcll; assumption.
    - apply phclr; constructor.
      rewrite <- (app_nil_l _); apply phcll; assumption.
    - rewrite <- (app_nil_r _), <- app_comm_cons, <- (app_nil_l _).
      apply phgenl; [ assumption | apply phax ].
    - apply phclr; constructor.
      rewrite <- (app_nil_l _); apply phcll; assumption.
    - apply phclr; constructor.
      rewrite <- (app_nil_l _); apply phcll; assumption.
    - rewrite <- (app_nil_l _).
      apply phnegl; [ assumption | apply phax ].
    - rewrite ill2ph_list_oc.
      apply phclr, phocr.
      rewrite <- ill2ph_list_oc; assumption.
    - apply (@phcut f) with (◻‹A›), phcll; assumption.
    - apply phclr.
      assert (Hgax := phgax a); do 2 red in Hgax; unfold ill2phgax in Hgax.
      destruct (projT2 (ipgax P) a); apply Hgax.
    Qed.

    Hypothesis P_gax_noN_l : gax_noN_l (cutrm_ipfrag P).

    (* not used *)
    Proposition ph2ill_translation Γ A : Γ ⊦ A -> ⌊Γ⌋ ⊢ ⌞A⌟ [ P ].
    Proof.
    intros pi; induction pi; list_simpl; 
      (try list_simpl in IHpi); (try list_simpl in IHpi1); (try list_simpl in IHpi2);
      try (now constructor; assumption); try assumption.
    - apply cut_ir with (⌞A⌟); assumption.
    - eapply ex_ir; [ apply IHpi | ].
      rewrite Hperm; simpl; apply Permutation_Type_app_head, Permutation_Type_swap.
    - change (!⌞B⌟ :: !⌞A⌟ :: ⌊Δ⌋) with (map ! (⌞B⌟ :: ⌞A⌟ :: nil) ++ ⌊Δ⌋).
      change (!⌞A⌟ :: !⌞B⌟ :: ⌊Δ⌋) with (map ! (⌞A⌟ :: ⌞B⌟ :: nil) ++ ⌊Δ⌋) in IHpi.
      eapply ex_oc_ir; [ apply IHpi | ].
      apply Permutation_Type_swap.
    - apply neg_map_rule; assumption.
    - apply gen_pam_rule; assumption.
    - rewrite ph2ill_list_oc; constructor; rewrite <- ph2ill_list_oc; assumption.
    - unfold ill2phgax.
      remember (projT2 (ipgax P) a) as b; destruct b; simpl.
      rewrite ill2ill_list, ill2ill.
      replace l with (fst (projT2 (ipgax P) a)) by (rewrite <- Heqb; reflexivity).
      replace i with (snd (projT2 (ipgax P) a)) by (rewrite <- Heqb; reflexivity).
      apply gax_ir.
    Qed.

  End PhILLProofs.


  Section PhaseSemantics.

    Variable perm_bool : bool.
    Variable PS : MPhaseSpace perm_bool.
    Variable v : IAtom -> Web -> Type.

    Infix "∘" := (composes PScompose) (at level 51, right associativity).
    Notation ε := (sg PSunit).
    Infix "⇀" := (magicwand_l PScompose) (at level 52, right associativity).
    Infix "↼" := (magicwand_r PScompose) (at level 53, left associativity).
    Notation "#" := (glb PSExp).
    Notation "❗ " := (@bang _ _ PSCL glb PSExp).
    Notation "□" := (@cl _ _ PSCL).

    Reserved Notation "⟦ A ⟧".
    Fixpoint pssem f :=
    match f with
    | µ X => v X
    | A ⊙ B => ⟦A⟧ ∘ ⟦B⟧
    | I => ε
    | A ⇾ B => ⟦A⟧ ⇀ □⟦B⟧
    | B ⇽ A => □⟦B⟧ ↼ ⟦A⟧
    | phneg A => ⟦A⟧ ⇀ □(v atN)
    | phgen A => □(v atN) ↼ ⟦A⟧
    | A ⩚ B => □⟦A⟧ ∩ □⟦B⟧
    | ᴛ => top
    | A ☩ B => ⟦A⟧ ∪ ⟦B⟧
    | 𝟢 => ∅
    | ♯A => #(□⟦A⟧)
    | ◻A => □⟦A⟧
    end
    where "⟦ a ⟧" := (pssem a).

    Notation "⦇ l ⦈" := (list_compose PS (map pssem l)).
    Notation sem_jdgt := (fun l x => list_compose PS l ⊆ x).
    Notation "l ⊧  x" := (list_compose PS (map pssem l) ⊆ pssem x) (at level 70).

    Fact pssem_cut : rule_cut sem_jdgt.
    Proof. intros ? ? ? ? ? ? ?; eapply sem_cut; eassumption. Qed.

    Fact pssem_tens_l : rule_tensor_left sem_jdgt (composes PScompose).
    Proof. intros ? ? ? ? ? ?; apply sem_tens_l; assumption. Qed.

    Fact pssem_tens_r : rule_tensor_right sem_jdgt (composes PScompose).
    Proof. intros ? ? ? ? ? ?; apply sem_tens_r; assumption. Qed.

    Fact pssem_one_l : rule_one_left sem_jdgt (sg PSunit).
    Proof. intros ? ? ? ?; apply sem_one_l; assumption. Qed.

    Fact pssem_one_r : rule_one_right sem_jdgt (sg PSunit).
    Proof. apply sem_one_r. Qed.

    Fact pssem_map_l : rule_right_implication_left sem_jdgt (magicwand_l PScompose).
    Proof. intros ? ? ? ? ? ? ? ?; apply sem_limp_l; assumption. Qed.

    Fact pssem_map_r : rule_right_implication_right sem_jdgt (magicwand_l PScompose).
    Proof. intros ? ? ? ?; apply sem_limp_r; assumption. Qed.

    Fact pssem_pam_l : rule_left_implication_left sem_jdgt (fun x y => magicwand_r PScompose y x).
    Proof. intros ? ? ? ? ? ? ? ?; apply sem_rimp_l; assumption. Qed.

    Fact pssem_pam_r : rule_left_implication_right sem_jdgt (fun x y => magicwand_r PScompose y x).
    Proof. intros ? ? ? ?; apply sem_rimp_r; assumption. Qed.

    Fact pssem_with_l1 : rule_with_left_1 sem_jdgt glb.
    Proof. intros ? ? ? ? ? ?; apply sem_with_l1; assumption. Qed.

    Fact pssem_with_l2 : rule_with_left_2 sem_jdgt glb.
    Proof. intros ? ? ? ? ? ?; apply sem_with_l2; assumption. Qed.

    Fact pssem_with_r : rule_with_right sem_jdgt glb.
    Proof. intros ? ? ? ? ?; apply sem_with_r; assumption. Qed.

    Fact pssem_plus_l : rule_plus_left sem_jdgt (fun x y => x ∪ y).
    Proof. intros ? ? ? ? ? ?; apply sem_plus_l; assumption. Qed.

    Fact pssem_plus_r1 : rule_plus_right_1 sem_jdgt (fun x y => x ∪ y).
    Proof. intros ? ? ? ?; apply sem_plus_r1; assumption. Qed.

    Fact pssem_plus_r2 : rule_plus_right_2 sem_jdgt (fun x y => x ∪ y).
    Proof. intros ? ? ? ?; apply sem_plus_r2; assumption. Qed.

    Fact pssem_zero_l : rule_zero_left sem_jdgt ∅.
    Proof. intros ? ? ? ?; apply sem_zero_l; assumption. Qed.

    Fact pssem_oc_l : rule_dereliction_left sem_jdgt (glb PSExp).
    Proof. intros ? ? ? ? ?; apply sem_prebang_l; assumption. Qed.

    Fact pssem_oc_r : rule_promotion_right sem_jdgt (glb PSExp).
    Proof. intros ? ? ?; apply sem_prebang_r; assumption. Qed.

    Fact pssem_wk_l : rule_weakening_modal_monad sem_jdgt (glb PSExp) (□).
    Proof. intros ? ? ? ? ?; apply sem_prebang_weak; assumption. Qed.

    Fact pssem_co_l : rule_contraction_modal_monad sem_jdgt (glb PSExp) (□).
    Proof. intros ? ? ? ? ?; apply sem_prebang_cntr; assumption. Qed.

  End PhaseSemantics.


  Section SyntacticModel.

    Variable P : ipfrag.
    Notation "Γ ⊦ A" := (PhILL P Γ A) (at level 70).

    Notation ctx_compose := (@app iformula).
    Notation ctx_unit := (@nil iformula).
    Notation ctx_adj_l := (fun ϴ H => match H with (Γ,Δ,A) => (Γ, ϴ ++ Δ, A) end).
    Notation ctx_adj_r := (fun ϴ H => match H with (Γ,Δ,A) => (Γ ++ ϴ, Δ, A) end).
    Notation ctx_hole := (list iformula * list iformula * iformula)%type.
    Notation ctx_PS := (PS_ctx (cutrm_ipfrag P)).
    Notation ctx_CL := (@PSCL _ ctx_PS).

    Infix "∘" := (composes ctx_compose) (at level 51, right associativity).
    Notation ε := (sg ctx_unit).
    Infix "⇀" := (magicwand_l ctx_compose) (at level 52, right associativity).
    Infix "↼" := (magicwand_r ctx_compose) (at level 53, left associativity).
    Notation "#" := (glb (@PSExp _ ctx_PS)).
    Notation "□" := (@cl _ _ ctx_CL).

    Notation closed := (fun x => □x ⊆ x).
    Infix "⟂" := (ctx_orth (cutrm_ipfrag P)) (at level 70).

    Notation "⦇ l ⦈" := (list_compose ctx_PS (map pssem l)).
    Notation sem_jdgt := (fun l x => list_compose ctx_PS l ⊆ x).
    Notation "l ⊧  x" := (list_compose ctx_PS l ⊆ x) (at level 70).
    Notation "↓" := (fun A Γ => Γ ⊢ A [cutrm_ipfrag P]).

    Lemma dc_map_sg A B : ﹛A ⊸ B::nil﹜ ⊆ ↓A ⇀ □﹛B::nil﹜.
    Proof.
    apply sg_subset.
    intros x Hx [[Γ Δ] C] H; inversion Hx; subst.
    red; rewrite <- app_assoc; apply lmap_ilr; [ assumption | ].
    change (B :: Δ) with ((B :: nil) ++ Δ).
    apply H; reflexivity.
    Qed.

    Lemma sg_map_dc A B : ﹛A::nil﹜ ⇀ ↓B ⊆ ↓(A ⊸ B).
    Proof. intros Γ H; apply lmap_irr, H; change (A :: Γ) with ((A :: nil) ++ Γ); constructor; reflexivity. Qed.

    Lemma dc_pam_sg A B : ﹛B ⟜ A::nil﹜ ⊆ □﹛B::nil﹜ ↼ ↓A.
    Proof.
    apply sg_subset.
    intros x Hx [[Γ Δ] C] H; inversion Hx; subst.
    apply lpam_ilr; [ assumption | ].
    change (B :: Δ) with ((B :: nil) ++ Δ).
    apply H; reflexivity.
    Qed.

    Lemma sg_pam_dc A B : ↓B ↼ ﹛A::nil﹜ ⊆ ↓(B ⟜ A).
    Proof. intros Γ H; apply lpam_irr, H; change (A :: Γ) with ((A :: nil) ++ Γ); constructor; reflexivity. Qed.

    Hypothesis P_gax_noN_l : gax_noN_l (cutrm_ipfrag P).

    Lemma dc_neg_sg A : ﹛ineg A::nil﹜ ⊆ ↓A ⇀ □﹛N::nil﹜.
    Proof.
    apply sg_subset.
    intros x Hx [[Γ Δ] C] H; inversion Hx; subst.
    red; rewrite <- app_assoc; apply neg_map_rule; [ assumption | assumption | ].
    change (N :: Δ) with ((N :: nil) ++ Δ).
    apply H; reflexivity.
    Qed.

    Lemma sg_neg_dc A : ﹛A::nil﹜ ⇀ ↓N ⊆ ↓(ineg A).
    Proof. intros Γ H; apply neg_irr, H; change (A :: Γ) with ((A :: nil) ++ Γ); constructor; reflexivity. Qed.

    Lemma dc_gen_sg A : ﹛igen A::nil﹜ ⊆ □﹛N::nil﹜ ↼ ↓A.
    Proof.
    apply sg_subset.
    intros x Hx [[Γ Δ] C] H; inversion Hx; subst.
    apply gen_pam_rule; [ assumption | assumption | ].
    change (N :: Δ) with ((N :: nil) ++ Δ).
    apply H; reflexivity.
    Qed.

    Lemma sg_gen_dc A : ↓N ↼ ﹛A::nil﹜ ⊆ ↓(igen A).
    Proof. intros Γ H; apply gen_irr, H; change (A :: Γ) with ((A :: nil) ++ Γ); constructor; reflexivity. Qed.


    Lemma sg_sem_l Σ Σ' : (forall Γ Δ C, Γ ++ Σ ++ Δ ⊢ C [cutrm_ipfrag P] -> Γ ++ Σ' ++ Δ ⊢ C [cutrm_ipfrag P]) ->
      forall Γ Δ C, Γ ++ ﹛Σ﹜ :: Δ ⊧ □C -> Γ ++ ﹛Σ'﹜ :: Δ ⊧ □C.
    Proof.
    intros Hrule Γ Δ C; apply list_compose_monot_sg_mnd; clear - Hrule.
    unfold cl; simpl; unfold ldual, rdual.
    intros [[Γ Δ] C] H; apply Hrule, H; reflexivity.
    Qed.

    Lemma sg_sem_l_bin Σ1 Σ2 Σ' :
     (forall Γ Δ C, Γ ++ Σ1 ++ Δ ⊢ C [cutrm_ipfrag P] -> Γ ++ Σ2 ++ Δ ⊢ C [cutrm_ipfrag P] ->
                    Γ ++ Σ' ++ Δ ⊢ C [cutrm_ipfrag P]) ->
      forall Γ Δ C, Γ ++ ﹛Σ1﹜ :: Δ ⊧ □C -> Γ ++ ﹛Σ2﹜ :: Δ ⊧ □C -> Γ ++ ﹛Σ'﹜ :: Δ ⊧ □C.
    Proof.
    intros Hrule Γ Δ C pi1 pi2.
    apply list_compose_monot_sg_mnd with (﹛Σ1﹜ ∪ ﹛Σ2﹜).
    - clear - Hrule; unfold cl; simpl; unfold ldual, rdual.
      intros [[Γ Δ] C] H; apply Hrule; apply H; [left|right]; reflexivity.
    - apply pssem_plus_l; assumption.
    Qed.

    Lemma sg_sem_l_nul Σ' : (forall Γ Δ C, Γ ++ Σ' ++ Δ ⊢ C [cutrm_ipfrag P]) -> forall Γ Δ C, Γ ++ ﹛Σ'﹜ :: Δ ⊧ □C.
    Proof.
    intros Hrule Γ Δ C.
    eapply list_compose_monot_sg_mnd; [ | apply pssem_zero_l ].
    clear - Hrule; unfold cl; simpl; unfold ldual, rdual.
    intros [[Γ Δ] C] H; apply Hrule.
    Qed.

    Lemma sg_sem_cons_cons_l Σ1 Σ2 Σ' :
     (forall Γ Δ C, Γ ++ Σ1 ++ Σ2 ++ Δ ⊢ C [cutrm_ipfrag P] -> Γ ++ Σ' ++ Δ ⊢ C [cutrm_ipfrag P]) ->
      forall Γ Δ C, Γ ++ ﹛Σ1﹜ :: ﹛Σ2﹜ :: Δ ⊧ □C -> Γ ++ ﹛Σ'﹜ :: Δ ⊧ □C.
    Proof.
    intros Hrule Γ Δ C pi; apply sg_sem_l with (Σ1 ++ Σ2).
    - intros; apply Hrule; rewrite <- app_assoc in X; assumption.
    - rewrite app_cons_cons_to_app_cons_cons_app, <- app_assoc in pi.
      rewrite app_cons_to_app_cons_app, <- app_assoc.
      eapply list_compose_monot_app; try eassumption.
      etransitivity; [ | apply (m_pwr_associativity (@PS_associative _ (PS_ctx P))) ].
      apply composes_monotone; try reflexivity.
      apply sg_subset; constructor; reflexivity.
    Qed.

    Fact sg_tens_l Γ Δ C A B : def_rule_mul_un_left sem_jdgt Γ Δ (□C) ﹛A::nil﹜ ﹛B::nil﹜ ﹛A ⊗ B::nil﹜.
    Proof. intros pi; apply sg_sem_cons_cons_l with (A::nil) (B::nil); [ apply tens_ilr | assumption ]. Qed.

    Fact sg_one_l Γ Δ C : def_rule_wk_left sem_jdgt Γ Δ (□C) ﹛1::nil﹜.
    Proof. intros pi; apply sg_sem_l with nil; [ apply one_ilr | ]; apply pssem_one_l; assumption. Qed.

    Fact sg_map_l Γ Δ Σ C A B : def_rule_mul_right_imp_left sem_jdgt Γ Δ Σ (□C) (↓A) ﹛B::nil﹜ ﹛A ⊸ B::nil﹜.
    Proof.
    intros pi1 pi2.
    rewrite app_assoc.
    apply list_compose_monot_cons with (↓A ⇀ □﹛B::nil﹜); [ apply dc_map_sg | ].
    rewrite <- app_assoc.
    apply (@sem_limp_l _ (PS_ctx (cutrm_ipfrag P))); [ | apply sem_monad_l ]; assumption.
    Qed.

    Fact sg_pam_l Γ Δ Σ C A B : def_rule_mul_left_imp_left sem_jdgt Γ Δ Σ (□C) (↓A) ﹛B::nil﹜ ﹛B ⟜ A::nil﹜.
    Proof.
    intros pi1 pi2.
    apply list_compose_monot_cons with (□﹛B::nil﹜ ↼ ↓A); [ apply dc_pam_sg | ].
    apply (@sem_rimp_l _ (PS_ctx (cutrm_ipfrag P))); [ | apply sem_monad_l ]; assumption.
    Qed.

    Fact sg_neg_l Γ Δ Σ C A : def_rule_mul_right_imp_left sem_jdgt Γ Δ Σ (□C) (↓A) ﹛N::nil﹜ ﹛ineg A::nil﹜.
    Proof.
    intros pi1 pi2.
    rewrite app_assoc.
    apply list_compose_monot_cons with (↓A ⇀ □﹛N::nil﹜); [ apply dc_neg_sg | ].
    rewrite <- app_assoc.
    apply (@sem_limp_l _ (PS_ctx (cutrm_ipfrag P))); [ | apply sem_monad_l ]; assumption.
    Qed.

    Fact sg_gen_l Γ Δ Σ C A : def_rule_mul_left_imp_left sem_jdgt Γ Δ Σ (□C) (↓A) ﹛N::nil﹜ ﹛igen A::nil﹜.
    Proof.
    intros pi1 pi2.
    apply list_compose_monot_cons with (□﹛N::nil﹜ ↼ ↓A); [ apply dc_gen_sg | ].
    apply (@sem_rimp_l _ (PS_ctx (cutrm_ipfrag P))); [ | apply sem_monad_l ]; assumption.
    Qed.

    Fact sg_with_l1 Γ Δ C A B : def_rule_add_un_left sem_jdgt Γ Δ (□C) ﹛A::nil﹜ ﹛A ﹠ B::nil﹜.
    Proof. intros pi; apply sg_sem_l with (A :: nil); [ apply with_ilr1 | ]; assumption. Qed.

    Fact sg_with_l2 Γ Δ C A B : def_rule_add_un_left sem_jdgt Γ Δ (□C) ﹛A::nil﹜ ﹛B ﹠ A::nil﹜.
    Proof. intros pi; apply sg_sem_l with (A :: nil); [ apply with_ilr2 | ]; assumption. Qed.

    Fact sg_plus_l Γ Δ C A B : def_rule_add_bin_left sem_jdgt Γ Δ (□C) ﹛A::nil﹜ ﹛B::nil﹜ ﹛A ⊕ B::nil﹜.
    Proof. intros pi; apply sg_sem_l_bin with (A::nil) ; [ apply plus_ilr | assumption ]. Qed.

    Fact sg_zero_l Γ Δ C : def_rule_add_nul_left sem_jdgt Γ Δ (□C) ﹛0::nil﹜.
    Proof. intros pi; apply sg_sem_l_nul; apply zero_ilr. Qed.

    Fact sg_oc_l Γ Δ C A : def_rule_add_un_left sem_jdgt Γ Δ (□C) ﹛A::nil﹜ ﹛!A::nil﹜.
    Proof. intros pi; apply sg_sem_l with (A :: nil); [ apply de_ilr | ]; assumption. Qed.

    Fact sg_wk_l Γ Δ C A : def_rule_wk_left sem_jdgt Γ Δ (□C) ﹛!A::nil﹜.
    Proof. intros pi; apply sg_sem_l with nil; [ apply wk_ilr | ]; apply pssem_one_l; assumption. Qed.

    Fact sg_co_l Γ Δ C A : def_rule_mul_un_left sem_jdgt Γ Δ (□C) ﹛!A::nil﹜ ﹛!A::nil﹜ ﹛!A::nil﹜.
    Proof. intros pi; apply sg_sem_cons_cons_l with (!A::nil) (!A::nil); [ apply co_ilr | assumption ]. Qed.


(* for some appropriate f (see below)
    Lemma ctx_sem_r (f : forall T, list T -> list T -> list T) c :
      (forall Γ Δ A B, Γ ⊢ A [P] -> Δ ⊢ B [P] -> f _ Γ Δ ⊢ c A B [P]) ->
      forall Γ Δ A B, Γ ⊧ ↓A -> Δ ⊧ ↓B -> f _ Γ Δ ⊧ ↓(c A B).
*)
    Lemma ctx_sem_mul_bin_r c : (forall Γ Δ A B, def_rule_mul_bin_right (ill (cutrm_ipfrag P)) Γ Δ A B (c A B)) ->
      forall Γ Δ A B, def_rule_mul_bin_right (sem_jdgt) Γ Δ (↓A) (↓B) (↓(c A B)).
    Proof.
    intros Hrule Γ Δ A B H1 H2 l H.
    apply list_compose_app in H; inversion H as [Γ' Δ' H1' H2' Heq].
    apply Hrule; auto.
    Qed.

    Lemma ctx_sem_add_bin_r c : (forall Γ A B, def_rule_add_bin_right (ill (cutrm_ipfrag P)) Γ A B (c A B)) ->
      forall Γ A B, def_rule_add_bin_right (sem_jdgt) Γ (↓A) (↓B) (↓(c A B)).
    Proof. intros Hrule Γ A B H1 H2 l H; apply Hrule; auto. Qed.

    Fact ctx_tens_r Γ Δ A B : def_rule_mul_bin_right sem_jdgt Γ Δ (↓A) (↓B) (↓(A ⊗ B)).
    Proof. red; apply ctx_sem_mul_bin_r; intros; red; apply tens_irr. Qed.

    Fact ctx_map_r Γ A B : def_rule_mul_right_imp_right sem_jdgt Γ ﹛A::nil﹜ (↓B) (↓(A ⊸ B)).
    Proof. intros pi; (etransitivity; [ | apply sg_map_dc ]); apply pssem_map_r; assumption. Qed.

    Fact ctx_pam_r Γ A B : def_rule_mul_left_imp_right sem_jdgt Γ ﹛A::nil﹜ (↓B) (↓(B ⟜ A)).
    Proof. intros pi; (etransitivity; [ | apply sg_pam_dc ]); apply pssem_pam_r; assumption. Qed.

    Fact ctx_neg_r Γ A : def_rule_mul_right_imp_right sem_jdgt Γ ﹛A::nil﹜ (↓N) (↓(ineg A)).
    Proof. intros pi; (etransitivity; [ | apply sg_neg_dc ]); apply pssem_map_r; assumption. Qed.

    Fact ctx_gen_r Γ A : def_rule_mul_left_imp_right sem_jdgt Γ ﹛A::nil﹜ (↓N) (↓(igen A)).
    Proof. intros pi; (etransitivity; [ | apply sg_gen_dc ]); apply pssem_pam_r; assumption. Qed.

    Fact ctx_with_r Γ A B : def_rule_add_bin_right sem_jdgt Γ (↓A) (↓B) (↓(A ﹠ B)).
    Proof. red; apply ctx_sem_add_bin_r; intros; red; apply with_irr. Qed.

    Fact ctx_plus_r1 Γ A B : def_rule_add_un_right sem_jdgt Γ (↓A) (↓(A ⊕ B)).
    Proof. intros ? ? ?; apply plus_irr1; auto. Qed.

    Fact ctx_plus_r2 Γ A B : def_rule_add_un_right sem_jdgt Γ (↓A) (↓(B ⊕ A)).
    Proof. intros ? ? ?; apply plus_irr2; auto. Qed.

    Fact ctx_oc_r Γ A : def_rule_add_un_right sem_jdgt (map # Γ) (↓A) (↓(!A)).
    Proof.
    intros pi Δ H.
    assert ({ Δ' & Δ = map ! Δ' }) as [Δ' Heq]; subst.
    { revert Δ H; clear; induction Γ; intros Δ H; inversion H; subst.
      - exists nil; reflexivity.
      - apply IHΓ in X0; destruct X0 as [Δ0 Heq]; subst.
        destruct X as [[Δ1 Heq] _]; subst.
        exists (Δ1 ++ Δ0); list_simpl; reflexivity. }
    apply oc_irr, pi; assumption.
    Qed.

    Definition at_ctx :=
      (fun X Γ => ﹛ivar X::nil﹜ Γ
                + {a | Γ = fst (projT2 (ipgax (cutrm_ipfrag P)) a)
                    /\ ivar X = snd (projT2 (ipgax (cutrm_ipfrag P)) a) })%type.

    Lemma sg_at_ctx X : ﹛ivar X::nil﹜ ⊆ at_ctx X.
    Proof. apply sg_subset; left; reflexivity. Qed.

    Lemma at_ctx_ctx X : at_ctx X ⊆ ↓(ivar X).
    Proof. intros Γ [Heq | [a [Heq1 Heq2]]]; subst; [ apply ax_ir | rewrite Heq2; apply gax_ir ]. Qed.

    Definition left_sem b :=
    match b with
    | false => fun A => pssem _ ctx_PS at_ctx A
    | true => fun A => ﹛⌞A⌟::nil﹜
    end.

    Lemma left_sem_oc b A : { B & left_sem b (♯A) ≃ # B }.
    Proof.
    exists (left_sem b (♯ A)).
    destruct b; simpl.
    + split; [ | apply glb_out_r ].
      intros x Hx; subst; split; [ exists (⌞A⌟ :: nil) | ]; reflexivity.
    + split; [ | apply glb_out_r ].
      apply glb_in; [ apply glb_out_l | reflexivity ].
    Qed.

    Definition right_sem b :=
    match b with
    | false => fun A => pssem _ ctx_PS at_ctx A
    | true => fun A => ↓⌞A⌟
    end.

    Lemma closed_right_sem b C : closed (right_sem b (◻C)).
    Proof. destruct b; simpl; [ apply dc_closed | apply (@cl_idempotent _ _ ctx_CL) ]. Qed.

    Hypothesis P_gax_at_l : gax_at_l (cutrm_ipfrag P).
    Hypothesis P_gax_at_r : gax_at_r (cutrm_ipfrag P).
    Hypothesis P_gax_cut : gax_cut (cutrm_ipfrag P).

    Lemma atlist_from_gax : forall a, { l | fst (projT2 (ipgax (cutrm_ipfrag P)) a) = map ivar l }.
    Proof.
    intros a.
    red in P_gax_at_l; specialize P_gax_at_l with a.
    revert P_gax_at_l ; remember (fst (projT2 (ipgax (cutrm_ipfrag P)) a)) as L; clear.
    induction L; intros Hat.
    - exists nil; reflexivity.
    - inversion Hat; inversion H1; subst.
      destruct (IHL H2) as [l Heq]; subst.
      exists (x0 :: l); reflexivity.
    Qed.

    Fact ILLgax a Γ A :
      map snd Γ = fst (ill2phgax (cutrm_ipfrag P) a) -> snd A = snd (ill2phgax (cutrm_ipfrag P) a) ->
      map (fun x => left_sem (fst x) (snd x)) Γ ⊧ right_sem (fst A) (snd A).
    Proof.
    intros HeqΓ HeqA.
    destruct (atlist_from_gax a) as [l Heq].
    unfold ill2phgax in HeqΓ, HeqA.
    red in P_gax_at_r; specialize P_gax_at_r with a.
    remember (projT2 (ipgax (cutrm_ipfrag P)) a) as b.
    destruct b; simpl in P_gax_at_l, P_gax_at_r, HeqΓ, HeqA, Heq.
    destruct i; inversion P_gax_at_r; subst; rewrite HeqA.
    enough (map (fun x => left_sem (fst x) (snd x)) Γ ⊧ at_ctx i) as Hr
      by (destruct (fst A); simpl; [ etransitivity; [ apply Hr | apply at_ctx_ctx ] | assumption ]).
    intros Δ HΔ; right.
    replace (ν i) with (snd (projT2 (ipgax (cutrm_ipfrag P)) a)) by (rewrite <- Heqb; reflexivity).
    enough (forall l0 Γ a l1 l2, map ivar l1 ++ map ivar l0 = fst (projT2 (ipgax (cutrm_ipfrag P)) a) ->
              map snd Γ = map phvar l0 ->
              list_compose ctx_PS (map (fun x => left_sem (fst x) (snd x)) Γ) l2 ->
              { c | map ivar l1 ++ l2 = fst (projT2 (ipgax (cutrm_ipfrag P)) c)
                 /\ snd (projT2 (ipgax (cutrm_ipfrag P)) a) = snd (projT2 (ipgax (cutrm_ipfrag P)) c) }) as HI.
    { specialize HI with l Γ a nil Δ; list_simpl in HI.
      replace (map ν l) with (fst (projT2 (ipgax (cutrm_ipfrag P)) a)) in HI by (rewrite <- Heqb; reflexivity).
      assert (map snd Γ = map µ l) as Heq.
      { clear - HeqΓ; revert l HeqΓ; induction Γ; intros l Heq; destruct l; inversion Heq; [ reflexivity | ].
        simpl; rewrite IHΓ with l; [ rewrite H0; reflexivity | assumption ]. }
      now apply HI in Heq. }
    clear - P_gax_at_l P_gax_cut; induction l0; intros Γ a' l1 l2 Heq1 Heq2 Hsem;
      destruct Γ; inversion Heq2; inversion Hsem; subst.
    - exists a'; split; [ | reflexivity ]; assumption.
    - assert (at_ctx a a0) as [Ha | Ha]
        by (rewrite H0 in X; simpl in X; destruct (fst p); [ apply sg_at_ctx | ]; apply X); subst.
      + apply IHl0 with (a:=a') (l1 := l1 ++ a :: nil) in X0; list_simpl; auto.
        list_simpl in X0; destruct X0 as [c [Heq1' Heq2']].
        exists c; auto.
      + destruct Ha as [c [Heq1' Heq2']]; subst.
        red in P_gax_cut.
        specialize P_gax_cut with c a' (map ivar l1) (map ivar l0).
        rewrite <- Heq2' in P_gax_cut.
        symmetry in Heq1; apply P_gax_cut in Heq1.
        destruct Heq1 as [d [Heq3 Heq4]].
        destruct (atlist_from_gax c) as [l' Heq'].
        rewrite_all Heq'.
        apply IHl0 with (a := d) (l1 := l1 ++ l') in X0; list_simpl; auto.
        list_simpl in X0; destruct X0 as [e [Heq5 Heq6]].
        exists e; split; auto.
        etransitivity; eassumption.
    Qed.

    Theorem sg_ctx_sem Γ A : map snd Γ ⊦ snd A ->
      map (fun x => left_sem (fst x) (snd x)) Γ ⊧ right_sem (fst A) (snd A).
    Proof.
    intros pi;
      remember (map snd Γ) as Γ0;
      remember (snd A) as A0; revert A Γ HeqΓ0 HeqA0;
      induction pi; intros A' Γ' Heq0 HeqA0; subst;
      (try decomp_map_Type Heq0; try simpl in Heq0; subst; list_simpl).
    - destruct l0; inversion Heq3; simpl.
      simpl in Heq2; rewrite <- Heq2.
      etransitivity; [ | apply closed_right_sem ].
      etransitivity; [ apply (@m_pwr_cl_neutrality_r_2 _ ctx_CL _ _ PS_neutral_r) |].
      apply cl_monotone.
      destruct (fst x); destruct (fst A'); simpl; clear.
      + apply sg_subset, ax_ir.
      + etransitivity; [ | apply (@cl_increase _ _ ctx_CL) ].
        apply sg_at_ctx.
      + apply at_ctx_ctx.
      + apply (@cl_increase _ _ ctx_CL).
    - apply (pssem_cut _ ctx_PS _ _ _ _ (left_sem false A)).
      + change (left_sem false A) with (right_sem false A).
        apply (IHpi1 (false,A) l2); reflexivity.
      + specialize IHpi2 with A' (l0 ++ (false,A) :: l3); list_simpl in IHpi2.
        apply IHpi2; reflexivity.
    - etransitivity; [ | apply closed_right_sem ].
      apply (@sem_swap _ ctx_PS), (@sem_monad_r _ ctx_PS); [ assumption | ].
      specialize IHpi with A' (l0 ++ x0 :: x :: l3); list_simpl in IHpi.
      now apply IHpi.
    - etransitivity; [ | apply closed_right_sem ].
      destruct (left_sem_oc (fst x0) A) as [A0 HeqA].
      destruct (left_sem_oc (fst x) B) as [B0 HeqB].
      transitivity (list_compose (PS_ctx P) (map (fun x1 => left_sem (fst x1) (snd x1)) l0 ++ #B0 :: #A0 ::
                                             map (fun x1 => left_sem (fst x1) (snd x1)) l3)).
      { etransitivity; [ apply (@list_compose_app _ (PS_ctx P)) | ].
        etransitivity; [ | apply (@list_compose_app _ (PS_ctx P)) ].
        apply composes_monotone; [ reflexivity | ].
        apply composes_monotone; [ rewrite Heq0 in HeqB; apply HeqB | ].
        apply composes_monotone; [ simpl in Heq3; rewrite Heq3 in HeqA; apply HeqA | reflexivity ]. }
      apply (@sem_prebang_swap _ ctx_PS), (@sem_monad_r _ ctx_PS).
      specialize IHpi with A' (l0 ++ (fst x0,♯A) :: (fst x,♯B) :: l3); list_simpl in IHpi.
      transitivity (list_compose (PS_ctx P) (map (fun x1 => left_sem (fst x1) (snd x1)) l0 ++
                                             left_sem (fst x0) (♯A) :: left_sem (fst x) (♯B) ::
                                             map (fun x1 => left_sem (fst x1) (snd x1)) l3)).
      { etransitivity; [ apply (@list_compose_app _ (PS_ctx P)) | ].
        etransitivity; [ | apply (@list_compose_app _ (PS_ctx P)) ].
        apply composes_monotone; [ reflexivity | ].
        apply composes_monotone; [ apply HeqA | ].
        apply composes_monotone; [ apply HeqB | reflexivity ]. }
      now apply IHpi.
    - rewrite <- Heq0; destruct (fst x); simpl.
      + etransitivity; [ | apply closed_right_sem ].
        apply sg_tens_l, (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ (true,A) :: (true,B) :: l2); list_simpl in IHpi.
        now apply IHpi.
      + apply (pssem_tens_l _ ctx_PS).
        specialize IHpi with A' (l0 ++ (false,A) :: (false,B) :: l2); list_simpl in IHpi.
        now apply IHpi.
    - destruct (fst A'); simpl.
      + apply ctx_tens_r.
        * apply (IHpi1 (true,A) l0); reflexivity.
        * apply (IHpi2 (true,B) l1); reflexivity.
      + apply (pssem_tens_r _ ctx_PS).
        * apply (IHpi1 (false,A) l0); reflexivity.
        * apply (IHpi2 (false,B) l1); reflexivity.
    - rewrite <- Heq0; destruct (fst x); simpl.
      + etransitivity; [ | apply closed_right_sem ].
        apply sg_one_l, (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ l2); list_simpl in IHpi.
        now apply IHpi.
      + apply (pssem_one_l _ ctx_PS).
        specialize IHpi with A' (l0 ++ l2); list_simpl in IHpi.
        now apply IHpi.
    - destruct Γ'; inversion Heq0; subst; destruct (fst A'); simpl; [ | reflexivity ].
      apply sg_subset, one_irr.
    - simpl in Heq3; rewrite <- Heq3; destruct (fst x); simpl; (etransitivity; [ | apply closed_right_sem ]).
      + apply sg_map_l.
        * apply (IHpi1 (true,A) l2); reflexivity.
        * apply (@sem_monad_r _ ctx_PS).
          specialize IHpi2 with A' (l0 ++ (true,B) :: l4); list_simpl in IHpi2.
          now apply IHpi2.
      + apply (pssem_map_l _ ctx_PS).
        * apply (IHpi1 (false,A) l2); reflexivity.
        * apply (@sem_monad_l _ ctx_PS), (@sem_monad_r _ ctx_PS).
          specialize IHpi2 with A' (l0 ++ (false,B) :: l4); list_simpl in IHpi2.
          now apply IHpi2.
    - destruct (fst A'); simpl.
      + apply ctx_map_r, (IHpi (true,B) ((true,A) :: Γ')); reflexivity.
      + apply (pssem_map_r _ ctx_PS), (@sem_monad_r _ ctx_PS),
              (IHpi (false,B) ((false,A) :: Γ')); reflexivity.
    - rewrite <- Heq0; destruct (fst x); simpl; (etransitivity; [ | apply closed_right_sem ]).
      + apply sg_pam_l.
        * apply (IHpi1 (true,A) l3); reflexivity.
        * apply (@sem_monad_r _ ctx_PS).
          specialize IHpi2 with A' (l0 ++ (true,B) :: l4); list_simpl in IHpi2.
          now apply IHpi2.
      + apply (pssem_pam_l _ ctx_PS).
        * apply (IHpi1 (false,A) l3); reflexivity.
        * apply (@sem_monad_l _ ctx_PS), (@sem_monad_r _ ctx_PS).
          specialize IHpi2 with A' (l0 ++ (false,B) :: l4); list_simpl in IHpi2.
          now apply IHpi2.
    - destruct (fst A'); simpl.
      + apply ctx_pam_r.
        specialize IHpi with (true,B) (Γ' ++ (true,A) :: nil); list_simpl in IHpi.
        now apply IHpi.
      + apply (pssem_pam_r _ ctx_PS), (@sem_monad_r _ ctx_PS).
        specialize IHpi with (false,B) (Γ' ++ (false,A) :: nil); list_simpl in IHpi.
        now apply IHpi.
    - simpl in Heq3; rewrite <- Heq3; destruct (fst x); simpl; (etransitivity; [ | apply closed_right_sem ]).
      + apply sg_neg_l.
        * apply (IHpi1 (true,A) l2); reflexivity.
        * apply (@sem_monad_r _ ctx_PS).
          specialize IHpi2 with A' (l0 ++ (true,µ atN) :: l4); list_simpl in IHpi2.
          now apply IHpi2.
      + apply (pssem_map_l _ ctx_PS).
        * apply (IHpi1 (false,A) l2); reflexivity.
        * apply (@sem_monad_l _ ctx_PS), (@sem_monad_r _ ctx_PS).
          specialize IHpi2 with A' (l0 ++ (false,µ atN) :: l4); list_simpl in IHpi2.
          now apply IHpi2.
    - destruct (fst A'); simpl.
      + apply ctx_neg_r, (IHpi (true,◻(µ atN)) ((true,A) :: Γ')); reflexivity.
      + apply (pssem_map_r _ ctx_PS), (IHpi (false,◻(µ atN)) ((false,A) :: Γ')); reflexivity.
    - rewrite <- Heq0; destruct (fst x); simpl; (etransitivity; [ | apply closed_right_sem ]).
      + apply sg_gen_l.
        * apply (IHpi1 (true,A) l3); reflexivity.
        * apply (@sem_monad_r _ ctx_PS).
          specialize IHpi2 with A' (l0 ++ (true,µ atN) :: l4); list_simpl in IHpi2.
          now apply IHpi2.
      + apply (pssem_pam_l _ ctx_PS).
        * apply (IHpi1 (false,A) l3); reflexivity.
        * apply (@sem_monad_l _ ctx_PS), (@sem_monad_r _ ctx_PS).
          specialize IHpi2 with A' (l0 ++ (false,µ atN) :: l4); list_simpl in IHpi2.
          now apply IHpi2.
    - destruct (fst A'); simpl.
      + apply ctx_gen_r.
        specialize IHpi with (true,◻(µ atN)) (Γ' ++ (true,A) :: nil); list_simpl in IHpi.
        now apply IHpi.
      + apply (pssem_pam_r _ ctx_PS).
        specialize IHpi with (false,◻(µ atN)) (Γ' ++ (false,A) :: nil); list_simpl in IHpi.
        now apply IHpi.
   - etransitivity; [ | apply closed_right_sem ].
      rewrite <- Heq0; destruct (fst x); simpl.
      + apply sg_with_l1, (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ (true,A) :: l2); list_simpl in IHpi.
        now apply IHpi.
      + apply (@pssem_with_l1 _ ctx_PS), (@sem_monad_l _ ctx_PS), (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ (false,A) :: l2); list_simpl in IHpi.
        now apply IHpi.
    - etransitivity; [ | apply closed_right_sem ].
      rewrite <- Heq0; destruct (fst x); simpl.
      + apply sg_with_l2, (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ (true,B) :: l2); list_simpl in IHpi.
        now apply IHpi.
      + apply (@pssem_with_l2 _ ctx_PS), (@sem_monad_l _ ctx_PS), (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ (false,B) :: l2); list_simpl in IHpi.
        now apply IHpi.
    - destruct (fst A'); simpl.
      + apply ctx_with_r.
        * apply (IHpi1 (true,A) Γ'); reflexivity.
        * apply (IHpi2 (true,B) Γ'); reflexivity.
      + apply (pssem_with_r _ ctx_PS).
        * apply (@sem_monad_r _ ctx_PS), (IHpi1 (false,A) Γ'); reflexivity.
        * apply (@sem_monad_r _ ctx_PS), (IHpi2 (false,B) Γ'); reflexivity.
    - destruct (fst A'); simpl.
      + intros ? ?; apply top_irr.
      + intros ? ?; constructor.
    - rewrite <- Heq0; destruct (fst x); simpl.
      + etransitivity; [ | apply closed_right_sem ].
        apply sg_plus_l; apply (@sem_monad_r _ ctx_PS).
        * specialize IHpi1 with A' (l0 ++ (true,A) :: l2); list_simpl in IHpi1.
          now apply IHpi1.
        * specialize IHpi2 with A' (l0 ++ (true,B) :: l2); list_simpl in IHpi2.
          now apply IHpi2.
      + apply (pssem_plus_l _ ctx_PS).
        * specialize IHpi1 with A' (l0 ++ (false,A) :: l2); list_simpl in IHpi1.
          now apply IHpi1.
        * specialize IHpi2 with A' (l0 ++ (false,B) :: l2); list_simpl in IHpi2.
          now apply IHpi2.
    - destruct (fst A'); simpl.
      + apply ctx_plus_r1, (IHpi (true,A) Γ'); reflexivity.
      + apply (pssem_plus_r1 _ ctx_PS), (IHpi (false,A) Γ'); reflexivity.
    - destruct (fst A'); simpl.
      + apply ctx_plus_r2, (IHpi (true,B) Γ'); reflexivity.
      + apply (pssem_plus_r2 _ ctx_PS), (IHpi (false,B) Γ'); reflexivity.
    - rewrite <- Heq0; destruct (fst x); simpl.
      + etransitivity; [ | apply closed_right_sem ].
        apply sg_zero_l.
      + apply (pssem_zero_l _ ctx_PS).
    - rewrite <- Heq0; destruct (fst x); simpl; (etransitivity; [ | apply closed_right_sem ]).
      + apply sg_oc_l, (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ (true,A) :: l2); list_simpl in IHpi.
        now apply IHpi.
      + apply (pssem_oc_l _ ctx_PS), (@sem_monad_l _ ctx_PS), (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ (false,A) :: l2); list_simpl in IHpi.
        now apply IHpi.
    - assert ({ Δ & list_compose ctx_PS (map (fun x => left_sem (fst x) (snd x)) Γ')
                  ≃ list_compose ctx_PS (map # Δ) }) as [Δ Hoc].
      { clear - Heq0; revert Γ Heq0; induction Γ'; intros Γ H.
        - exists nil; reflexivity.
        - destruct Γ; inversion H; subst.
          apply IHΓ' in H2; destruct H2 as [Δ0 Heq].
          destruct (left_sem_oc (fst a) p) as [b Heqb].
          exists (b :: Δ0).
          simpl; rewrite <- H1; apply composes_compat; assumption. }
      etransitivity; [ apply Hoc | ].
      destruct (fst A'); simpl.
      + apply ctx_oc_r.
        etransitivity; [ apply Hoc | ].
        now apply (IHpi (true,A) Γ').
      + apply (@pssem_oc_r _ ctx_PS).
        etransitivity; [ apply Hoc | ].
        now apply (@sem_monad_r _ ctx_PS), (IHpi (false,A) Γ').
    - rewrite <- Heq0; destruct (fst x); simpl; (etransitivity; [ | apply closed_right_sem ]).
      + apply sg_wk_l, (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ l2); list_simpl in IHpi.
        now apply IHpi.
      + apply (pssem_wk_l _ ctx_PS), (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ l2); list_simpl in IHpi.
        now apply IHpi.
    - rewrite <- Heq0; destruct (fst x); simpl; (etransitivity; [ | apply closed_right_sem ]).
      + apply sg_co_l, (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ (true,♯A) :: (true,♯A) :: l2); list_simpl in IHpi.
        now apply IHpi.
      + apply (pssem_co_l _ ctx_PS), (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ (false,♯A) :: (false,♯A) :: l2); list_simpl in IHpi.
        now apply IHpi.
    - rewrite <- Heq0; destruct (fst x); simpl.
      + specialize IHpi with A' (l0 ++ (true,A) :: l2); list_simpl in IHpi.
        now apply IHpi.
      + etransitivity; [ | apply closed_right_sem ].
        apply (@sem_monad_l _ ctx_PS), (@sem_monad_r _ ctx_PS).
        specialize IHpi with A' (l0 ++ (false,A) :: l2); list_simpl in IHpi.
        now apply IHpi.
    - destruct (fst A'); simpl.
      + apply (IHpi (true,A) Γ'); reflexivity.
      + apply (@sem_monad_r _ ctx_PS), (IHpi (false,A) Γ'); reflexivity.
    - rewrite HeqA0; apply ILLgax with a; symmetry; assumption.
    Qed.

  End SyntacticModel.

  Notation ctx_CL := (fun P => @PSCL _ (PS_ctx (cutrm_ipfrag P))).

  Theorem cut_elimination P Γ A : gax_noN_l P -> gax_at_l P -> gax_at_r P -> gax_cut P ->
    Γ ⊢ A [P] -> Γ ⊢ A [cutrm_ipfrag P].
  Proof.
  intros P_gax_noN_l P_gax_at_l P_gax_at_r P_gax_cut pi.
  apply ill2ph_translation in pi.
  change (◻‹A›) with (snd (true,◻‹A›)) in pi.
  replace («Γ») with (map snd (map (fun x => (true,x)) «Γ»)) in pi
    by (rewrite map_map, map_ext with (g := id); [ apply map_id | intros; reflexivity ]).
  apply sg_ctx_sem in pi; try assumption.
  rewrite map_map in pi; simpl in pi; rewrite ill2ill in pi.
  apply pi; clear pi.
  induction Γ; simpl; [ reflexivity | ].
  change (a :: Γ) with ((a :: nil) ++ Γ).
  constructor; [ | assumption ].
  rewrite ill2ill; reflexivity.
  Qed.

End PhILL.

