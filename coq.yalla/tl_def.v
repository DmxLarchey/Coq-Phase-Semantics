(* tl example file for yalla library *)

(** * Example of a concrete use of the yalla library: tensor logic *)

Require Import CMorphisms.
Require Import Bool_more.
Require Import List_more.
Require Import Permutation_Type.
Require Import genperm_Type.

Require Import basic_misc.
Require yalla_ax.


(** ** 1. define formulas *)

Definition TAtom := yalla_ax.TAtom.

(** Tensor formulas *)
Inductive tformula : Set :=
| tvar : TAtom -> tformula
| tone : tformula
| ttens : tformula -> tformula -> tformula
| tneg : tformula -> tformula
| tzero : tformula
| tplus : tformula -> tformula -> tformula
| toc : tformula -> tformula.

Inductive tatomic : tformula -> Type :=
| tatomic_var : forall x, tatomic (tvar x).

Inductive tsubform : tformula -> tformula -> Type :=
| tsub_id : forall A, tsubform A A
| tsub_tens_l : forall A B C, tsubform A B -> tsubform A (ttens B C)
| tsub_tens_r : forall A B C, tsubform A B -> tsubform A (ttens C B)
| tsub_neg_l  : forall A B, tsubform A B -> tsubform A (tneg B)
| tsub_neg_r  : forall A B, tsubform A B -> tsubform A (tneg B)
| tsub_plus_l : forall A B C, tsubform A B -> tsubform A (tplus B C)
| tsub_plus_r : forall A B C, tsubform A B -> tsubform A (tplus C B)
| tsub_oc : forall A B, tsubform A B -> tsubform A (toc B).

Lemma tsub_trans : forall A B C, tsubform A B -> tsubform B C -> tsubform A C.
Proof with try assumption.
intros A B C Hl Hr ; revert A Hl ; induction Hr ; intros A' Hl ;
  try (constructor ; apply IHHr)...
Qed.

Instance tsub_po : PreOrder tsubform.
Proof.
split.
- intros l.
  apply tsub_id.
- intros l1 l2 l3.
  apply tsub_trans.
Qed.



(** ** 3. define proofs *)

Definition NoTAxioms := (existT (fun x => x -> list tformula * option tformula) _ Empty_fun).

Record tpfrag := mk_tpfrag {
  tpcut : bool ;
  tpgax : { tptypgax : Type & tptypgax -> list tformula * option tformula } ;
  tpperm : bool }.

Definition le_tpfrag P Q :=
  prod 
     (Bool.leb (tpcut P) (tpcut Q))
  (prod
     (forall a, { b | projT2 (tpgax P) a = projT2 (tpgax Q) b })
     (Bool.leb (tpperm P) (tpperm Q))).

Lemma le_tpfrag_trans : forall P Q R,
  le_tpfrag P Q -> le_tpfrag Q R -> le_tpfrag P R.
Proof.
intros P Q R H1 H2.
destruct H1 as (Hc1 & Ha1 & Hp1).
destruct H2 as (Hc2 & Ha2 & Hp2).
split ; [ | split ] ; try (eapply leb_trans ; eassumption).
intros a.
destruct (Ha1 a) as [b Heq].
destruct (Ha2 b) as [c Heq2].
exists c ; etransitivity ; eassumption.
Qed.

Definition cutupd_tpfrag P b := mk_tpfrag b (tpgax P) (tpperm P).

Definition axupd_tpfrag P G := mk_tpfrag (tpcut P) G (tpperm P).

Definition cutrm_tpfrag P := cutupd_tpfrag P false.

Inductive tl P : list tformula -> option tformula -> Type :=
| ax_tr : forall X, tl P (tvar X :: nil) (Some (tvar X))
| ex_tr : forall l1 l2 A, tl P l1 A -> PEperm_Type (tpperm P) l1 l2 ->
                          tl P l2 A
| ex_oc_tr : forall l1 lw lw' l2 A, tl P (l1 ++ map toc lw ++ l2) A ->
               Permutation_Type lw lw' -> tl P (l1 ++ map toc lw' ++ l2) A
| one_trr : tl P nil (Some tone)
| one_tlr : forall l1 l2 A, tl P (l1 ++ l2) A ->
                            tl P (l1 ++ tone :: l2) A
| tens_trr : forall A B l1 l2,
                    tl P l1 (Some A) -> tl P l2 (Some B) ->
                    tl P (l1 ++ l2) (Some (ttens A B))
| tens_tlr : forall A B l1 l2 C,
                    tl P (l1 ++ A :: B :: l2) C ->
                    tl P (l1 ++ ttens A B :: l2) C
| neg_trr : forall A l,
                    tl P (A :: l) None ->
                    tl P l (Some (tneg A))
| neg_tlr : forall A l, tl P l (Some A) ->
                        tl P (l ++ tneg A :: nil) None
| zero_tlr : forall l1 l2 C, tl P (l1 ++ tzero :: l2) C
| plus_trr1 : forall A B l, tl P l (Some A) ->
                            tl P l (Some (tplus A B))
| plus_trr2 : forall A B l, tl P l (Some A) ->
                            tl P l (Some (tplus B A))
| plus_tlr : forall A B l1 l2 C,
                        tl P (l1 ++ A :: l2) C ->
                        tl P (l1 ++ B :: l2) C ->
                        tl P (l1 ++ tplus A B :: l2) C
| oc_trr : forall A l, tl P (map toc l) (Some A) ->
                       tl P (map toc l) (Some (toc A))
| de_tlr : forall A l1 l2 C,
                        tl P (l1 ++ A :: l2) C ->
                        tl P (l1 ++ toc A :: l2) C
| wk_tlr : forall A l1 l2 C,
                        tl P (l1 ++ l2) C ->
                        tl P (l1 ++ toc A :: l2) C
| co_tlr : forall A l1 l2 C,
              tl P (l1 ++ toc A :: toc A :: l2) C -> tl P (l1 ++ toc A :: l2) C
| cut_tr {f : tpcut P = true} : forall A l0 l1 l2 C,
                               tl P l0 (Some A) -> tl P (l1 ++ A :: l2) C ->
                               tl P (l1 ++ l0 ++ l2) C
| gax_tr : forall a,
           tl P (fst (projT2 (tpgax P) a)) (snd (projT2 (tpgax P) a)).

Instance tl_perm {P} {Pi} :
  Proper ((PEperm_Type (tpperm P)) ==> Basics.arrow) (fun l => tl P l Pi).
Proof.
intros l1 l2 HP pi.
eapply ex_tr ; eassumption.
Qed.

Lemma stronger_tpfrag P Q : le_tpfrag P Q -> forall l A, tl P l A -> tl Q l A.
Proof with try reflexivity ; try eassumption.
intros Hle l A H.
induction H ; try (constructor ; try assumption ; fail).
- apply (ex_tr _ l1)...
  destruct Hle as (_ & _ & Hp).
  hyps_PEperm_Type_unfold ; unfold PEperm_Type.
  destruct (tpperm P) ; destruct (tpperm Q) ;
    simpl in Hp ; try inversion Hp ; subst...
- eapply ex_oc_tr ; [ apply IHtl | ]...
- destruct Hle as [Hcut _].
  rewrite f in Hcut.
  eapply (@cut_tr _ Hcut)...
- destruct Hle as (_ & Hgax & _).
  destruct (Hgax a) as [b Heq].
  rewrite Heq.
  apply gax_tr.
Qed.

