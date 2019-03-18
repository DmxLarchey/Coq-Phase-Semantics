(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Omega.

Require Import utils.

Set Implicit Arguments.

(** * Intuionistic Linear Logic *)

Definition ill_vars := nat.

Inductive ill_conn := ll_with | ll_limp | ll_rimp | ll_times | ll_plus.
Inductive ill_cst := ll_one | ll_bot | ll_top.

Inductive ill_form : Set :=
  | ill_var  : ill_vars -> ill_form
  | ill_zero : ill_cst  -> ill_form
  | ill_bang : ill_form -> ill_form
  | ill_bin  : ill_conn -> ill_form -> ill_form -> ill_form.

Fact ill_form_eq_dec (f g : ill_form) : { f = g } + { f <> g }.
Proof. 
  decide equality.
  + apply eq_nat_dec.
  + decide equality.
  + decide equality.
Qed.

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ *)

Notation "⟙" := (ill_zero ll_top).
Notation "⟘" := (ill_zero ll_bot).
Notation 𝝐 := (ill_zero ll_one).

Infix "&" := (ill_bin ll_with) (at level 50, only parsing).
Infix "﹠" := (ill_bin ll_with) (at level 50).

Infix "⊗" := (ill_bin ll_times) (at level 50).
Infix "⊕" := (ill_bin ll_plus) (at level 50).

Infix "-o" := (ill_bin ll_limp) (at level 51, right associativity).
Infix "o-" := (ill_bin ll_rimp) (at level 52, left associativity).

Notation "'!' x" := (ill_bang x) (at level 52).

Definition ill_lbang := map (fun x => !x).

Notation "'!l' x" := (ill_lbang x) (at level 60, only parsing).

Notation "‼ x" := (ill_lbang x) (at level 52).

Notation "£" := ill_var.

Notation "∅" := nil (only parsing).

Infix "~!" := (perm_bang_t ill_bang) (at level 70).
Infix "~p" := (@perm_t _) (at level 70).

Hint Resolve perm_bang_t_refl perm_bang_t_cons.

Fact illnc_perm_t_map_inv_t l m : ‼ l ~! m -> { l' | m = ‼ l' }.
Proof. 
  apply perm_bang_t_map_inv_t.
  inversion 1; trivial.
Qed.