(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(*   Adapted by Olivier Laurent [**]                          *)
(*                                                            *)
(*                              [**] Affiliation LIP -- CNRS  *)


Require Import List_Type Permutation_Type genperm_Type.

Require Export closure_operators log_phase_sem.

Require Import tl_def.

Import SetNotations. (* ⊆ ≃ ∩ ∪ ∅ *)


Set Implicit Arguments.

Section TPhaseModels.

  (* Interpretation of Tensor Logic *)

  Infix "∘" := (composes PScompose) (at level 51, right associativity).
  Infix "⊸" := (magicwand_l PScompose) (at level 52, right associativity).
  Notation "♯ x" := (glb PSExp x) (at level 40, no associativity).
  Notation "❗ " := (@bang _ _ PSCL glb PSExp) (at level 40, no associativity).
  Notation "□" := (@cl _ _ PSCL).

  Notation "£" := tvar.
  Notation "0" := tzero.
  Notation 𝝐 := tone.
  Infix "⊗" := ttens (at level 50).
  Infix "⊕" := tplus (at level 50).
  Notation "¬" := tneg.
  Notation "! x" := (toc x) (at level 54).
  Definition tl_lbang := map toc.
  Notation "‼ x" := (tl_lbang x) (at level 54).

  Section Formula_Interpretation.

    Variable perm_bool : bool.
    Variable PS : MPhaseSpace perm_bool.
    Variable v : option TAtom -> Web -> Type.

    Reserved Notation "⟦ A ⟧" (at level 49).
    Fixpoint tform_presem f :=
      match f with
      | 0   => ∅
      | 𝝐         => sg PSunit
      | £ x => v (Some x)
      | ¬ a => ⟦a⟧ ⊸ □(v None)
      | a ⊗ b  => ⟦a⟧ ∘ ⟦b⟧
      | a ⊕ b  => ⟦a⟧ ∪ ⟦b⟧
      | !a     => ♯□(⟦a⟧)
      end
    where "⟦ a ⟧" := (tform_presem a).

    Definition list_tform_presem l := fold_right (composes PScompose) (sg PSunit) (map tform_presem l).

  End Formula_Interpretation.

  Class TPhaseModel (P : tpfrag) := {
    PMPS : MPhaseSpace (tpperm P);
    PMval : option TAtom -> Web -> Type;
    PMgax : forall a, match (snd (projT2 (tpgax P) a)) with 
                      | Some A => list_tform_presem PMPS PMval (fst (projT2 (tpgax P) a))
                                  ⊆ @cl _ _ PSCL (tform_presem PMPS PMval A)
                      | None   => list_tform_presem PMPS PMval (fst (projT2 (tpgax P) a))
                                  ⊆ @cl _ _ PSCL (PMval None)
                      end }.

  Context { P : tpfrag }.
  Variable PM : TPhaseModel P.

  Notation "l ⊧  x" := (@list_compose _ PMPS l ⊆ x) (at level 70, no associativity).
  Notation "□" := (@cl _ _ PSCL).
  Notation Int := (@tform_presem _ PMPS PMval).
  Notation "l ⊢ x" := (tl P l x) (at level 70, no associativity).

  Hint Resolve  magicwand_l_adj_l magicwand_l_adj_r.
  Hint Resolve (@sem_monad_l _ PMPS).
  Hint Resolve (@sem_ax _ PMPS)
               (@sem_one_r _ PMPS) (@sem_one_l _ PMPS) (@sem_tens_r _ PMPS) (@sem_tens_l _ PMPS)
               (@sem_rimp_r _ PMPS) (@sem_rimp_l _ PMPS) (@sem_limp_r _ PMPS) (@sem_limp_l _ PMPS)
               (@sem_with_r _ PMPS) (@sem_with_l1 _ PMPS) (@sem_with_l2 _ PMPS)
               (@sem_plus_l _ PMPS) (@sem_zero_l _ PMPS)
               (@sem_prebang_r _ PMPS) (@sem_prebang_l _ PMPS)
               (@sem_prebang_weak _ PMPS) (@sem_prebang_cntr _ PMPS).

  Notation option_apply := (fun (A B : Type) (f:A->B) dflt x =>
  match x with
  | None => dflt
  | Some v => f v
  end).

  Lemma int_toc_list l : map Int (map toc l) = map (fun z => ♯(□z)) (map Int l).
  Proof. induction l; auto; simpl; rewrite IHl; auto. Qed.

  Theorem tl_soundness Γ a : Γ ⊢ a -> map Int Γ ⊧ □(option_apply _ _ Int (PMval None) a).
  Proof.
  intros pi; induction pi;
    (try rewrite ? map_app);
    (try rewrite ? map_app in IHpi); (try rewrite ? map_app in IHpi1); (try rewrite ? map_app in IHpi2);
    (try rewrite int_toc_list); (try rewrite int_toc_list in IHpi);
    (try now (apply (@sem_monad_r _ PMPS); simpl; auto));
    (try now (simpl; auto)).
  - apply sem_monad_r, sem_ax.
  - assert ({tpperm P = true} + {tpperm P = false}) as Hbool
      by (clear; destruct (tpperm P); [ left | right ]; reflexivity).
    destruct Hbool as [Hbool | Hbool]; intros; rewrite Hbool in p.
    + apply sem_perm with (map Int l1); auto.
      apply Permutation_Type_map; assumption.
    + rewrite <- p; auto.
  - rewrite map_map; rewrite map_map in IHpi; simpl.
    replace (map (fun x => ♯□(Int x)) lw')
       with (map (fun t => ♯t) (map (fun x => (□(Int x))) lw'))
      by (rewrite map_map; reflexivity).
    apply sem_prebang_perm with (map (fun x => (□(Int x))) lw); [ | rewrite ? map_map]; auto.
    apply Permutation_Type_map; assumption.
  - rewrite <- (app_nil_r _); rewrite <- (app_nil_l _).
    apply sem_cut with (□ (□(Int A) ∘ □(Int B))); simpl Int.
    + apply sem_monad_r; auto.
    + apply sem_monad_l, sem_tens_l, sem_monad_l; rewrite app_nil_l.
      change (Int A :: □ (Int B) :: nil) with ((Int A :: nil) ++ □ (Int B) :: nil).
      apply sem_monad_l, sem_monad_r, sem_tens_r; auto.
  - simpl; rewrite <- (app_nil_r _); rewrite <- app_assoc.
    apply sem_cut with (□(Int A) ⊸ □(PMval None)); auto.
    + apply sem_limp_r.
      rewrite <- (app_nil_l _); apply sem_monad_l.
      change (Int A :: Int A ⊸ □(PMval None) :: nil)
        with ((Int A :: nil) ++ Int A ⊸ □(PMval None) :: nil).
      apply sem_limp_l; try rewrite app_nil_l; auto.
    + rewrite <- (app_nil_l _); apply sem_limp_l; try rewrite app_nil_l; auto.
  - rewrite <- (app_nil_r _); rewrite <- (app_nil_l _).
    apply sem_cut with (□(Int A)); auto.
    apply sem_monad_l, sem_monad_r, sem_plus_r1; rewrite app_nil_l; auto.
  - rewrite <- (app_nil_r _); rewrite <- (app_nil_l _).
    apply sem_cut with (□(Int A)); auto.
    apply sem_monad_l, sem_monad_r, sem_plus_r2; rewrite app_nil_l; auto.
  - rewrite map_map in IHpi; rewrite map_map; rewrite <- map_map; simpl.
    apply sem_monad_r, sem_prebang_r; rewrite map_map; auto.
  - apply sem_cut with (□ (Int A)); auto.
  - assert (H := PMgax a); destruct (snd (projT2 (tpgax P) a)); auto.
  Qed.

End TPhaseModels.

