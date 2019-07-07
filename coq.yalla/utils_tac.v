(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Set Implicit Arguments.

Ltac spec H U :=
  match goal with [ G : ?h -> _ |- _ ] => 
    match G with H => assert h as U; [ idtac | specialize (H U) ] end end.

(* and do it as much as you can *)

Ltac spec_all_rec H U :=
  try match goal with [ G : ?h -> _ |- _ ] => 
    match G with H => assert h as U; [ idtac | specialize (H U); clear U; spec_all_rec H U ] end end.

Tactic Notation "spec" "all" "in" hyp(H) := let U := fresh in spec_all_rec H U.
