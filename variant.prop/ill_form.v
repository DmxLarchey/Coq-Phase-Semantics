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

Inductive ill_conn := ll_with | ll_limp | ll_times | ll_plus.
Inductive ill_cst := ll_one | ll_bot | ll_top.

Inductive ill_form : Set :=
  | ill_var  : ill_vars -> ill_form
  | ill_zero : ill_cst  -> ill_form
  | ill_bang : ill_form -> ill_form
  | ill_bin  : ill_conn -> ill_form -> ill_form -> ill_form.

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ *)

Notation "⟙" := (ill_zero ll_top).
Notation "⟘" := (ill_zero ll_bot).
Notation 𝝐 := (ill_zero ll_one).

Infix "&" := (ill_bin ll_with) (at level 50, only parsing).
Infix "﹠" := (ill_bin ll_with) (at level 50).

Infix "⊗" := (ill_bin ll_times) (at level 50).
Infix "⊕" := (ill_bin ll_plus) (at level 50).

Infix "-o" := (ill_bin ll_limp) (at level 51, right associativity).

Notation "'!' x" := (ill_bang x) (at level 52).

Definition ill_lbang := map (fun x => !x).

Notation "'!l' Γ" := (ill_lbang Γ) (at level 52, only parsing).
Notation "‼ Γ" := (ill_lbang Γ) (at level 52).

Notation "£" := ill_var.

Notation "∅" := nil (only parsing).