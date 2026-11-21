(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec2.

Module RefInffastGen.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInffast_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInffast_run.RefInffast17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInffast_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
End RefInffastGen.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefInffastGen.

Module RefItable1.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.


Definition SV0 (s2v s5v s1v s3v : Z) : list (Z * nat * Z) :=
  [(184, 8%nat, s2v); (160, 8%nat, s5v); (192, 8%nat, s1v); (176, 8%nat, s3v)].

Definition slots_in (SV : list (Z * nat * Z)) : Prop :=
  forall e, In e SV -> let '(o, w, _) := e in 0 <= o /\ o + Z.of_nat w <= 208.

End Walk.
End RefItable1.

Module RefItable2.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

Local Ltac sidew :=
  lazymatch goal with
  | |- @ex _ _ => fail
  | |- _ => rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia
  end.

End Walk.
End RefItable2.

Module RefItable3.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

End Walk.
End RefItable3.

Module RefItable4.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

Local Notation SV0 := RefItable1.SV0.
Local Notation slots_in := RefItable1.slots_in.

Fixpoint spills_ok (SV : list (Z * nat * Z)) (l : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | (o, _) :: l' => (112 <=? o) && (o + 8 <=? 208) && fslots_miss SV o 8 && spills_ok SV l'
  end.

Definition SV1 (s0v s4v s6v s7v s8v : Z) (l : list (Z * nat * Z)) : list (Z * nat * Z) :=
  (136, 8%nat, s8v) :: (144, 8%nat, s7v) :: (152, 8%nat, s6v) :: (168, 8%nat, s4v) :: (200, 8%nat, s0v) :: l.
Definition SV2 (s9v s10v : Z) (l : list (Z * nat * Z)) : list (Z * nat * Z) :=
  (120, 8%nat, s10v) :: (128, 8%nat, s9v) :: l.

Lemma SV1_in : forall a b c d e p q r s, slots_in (SV1 a b c d e (SV0 p q r s)).
Proof.
  intros. unfold SV1, RefItable1.SV0, RefItable1.slots_in. intros x Hx.
  repeat (destruct Hx as [<-|Hx]; [cbn; lia|]). destruct Hx.
Qed.
Lemma SV2_in : forall u v a b c d e p q r s, slots_in (SV2 u v (SV1 a b c d e (SV0 p q r s))).
Proof.
  intros. unfold SV2, SV1, RefItable1.SV0, RefItable1.slots_in. intros x Hx.
  repeat (destruct Hx as [<-|Hx]; [cbn; lia|]). destruct Hx.
Qed.


Definition spillsB (v0 v4 v6 v7 v8 : Z) : list (Z * Z) :=
  [(136, v8); (144, v7); (152, v6); (168, v4); (200, v0)].
End Walk.
End RefItable4.

Module RefItable5.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

Local Notation SV0 := RefItable1.SV0.
Local Notation slots_in := RefItable1.slots_in.
Local Notation SV1 := (@RefItable4.SV1).
Local Notation SV2 := (@RefItable4.SV2).

Lemma ty_code_range : forall t, 0 <= ty_code t < 3.
Proof. intros t; destruct t; cbn; lia. Qed.
Lemma ty_code_codes : forall t, codetype_eqb t CODES = true -> ty_code t = 0.
Proof. intros t; destruct t; cbn; intros; first [reflexivity | discriminate]. Qed.
Lemma ty_code_ncodes : forall t, codetype_eqb t CODES = false -> ty_code t <> 0.
Proof. intros t; destruct t; cbn; intros; first [lia | discriminate]. Qed.


Lemma left_rec_16 : forall cnt n l, left_rec cnt n 16 l = Some l.
Proof. intros cnt n l. destruct n; reflexivity. Qed.
End Walk.
End RefItable5.

Module RefItable6.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

Local Notation SV0 := RefItable1.SV0.
Local Notation slots_in := RefItable1.slots_in.

Definition offs_fun (o : arr) (i : Z) : Z := arr_get o (i + 1).

Lemma offs_fun_range : forall cnt j, 0 <= offs_fun (itm_offs cnt) j < 65536.
Proof. intros. unfold offs_fun. apply itm_offs_range. Qed.

Lemma itm_root_minmax : forall b mx mn, itm_root b mx mn = Z.max mn (Z.min b mx).
Proof. intros. unfold itm_root. destruct (Z.ltb_spec mx b); [destruct (Z.ltb_spec mx mn) | destruct (Z.ltb_spec b mn)]; lia. Qed.


Lemma psum_0 : forall cnt, psum cnt 0 = 0. Proof. reflexivity. Qed.
Local Ltac zofnat :=
  change (Z.of_nat 14) with 14; change (Z.of_nat 13) with 13; change (Z.of_nat 12) with 12; change (Z.of_nat 11) with 11;
  change (Z.of_nat 10) with 10; change (Z.of_nat 9) with 9; change (Z.of_nat 8) with 8; change (Z.of_nat 7) with 7;
  change (Z.of_nat 6) with 6; change (Z.of_nat 5) with 5; change (Z.of_nat 4) with 4; change (Z.of_nat 3) with 3;
  change (Z.of_nat 2) with 2; change (Z.of_nat 1) with 1.
Local Ltac psimp := cbn [psum]; zofnat; lia.
End Walk.
End RefItable6.

Module RefItable7.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

Local Notation SV0 := RefItable1.SV0.
Local Notation slots_in := RefItable1.slots_in.
Local Notation offs_fun := RefItable6.offs_fun.


Definition ext_addr (t : codetype) (WP : Z) : Z := match t with CODES => WP | LENS => 0x2e9b0 | DISTS => 0x2e930 end.
Definition base_addr (t : codetype) (WP : Z) : Z := match t with CODES => WP | LENS => 0x2e9f0 | DISTS => 0x2e970 end.
Definition isLENS (t : codetype) : Z := match t with LENS => 1 | _ => 0 end.
Definition isDISTS (t : codetype) : Z := match t with DISTS => 1 | _ => 0 end.

Definition SV3 (bp tp tbt isl isd s11v : Z) (l : list (Z * nat * Z)) : list (Z * nat * Z) :=
  (40, 8%nat, bp) :: (32, 8%nat, tp) :: (8, 8%nat, tbt) :: (24, 8%nat, isl) :: (16, 8%nat, isd) :: (112, 8%nat, s11v) :: l.
End Walk.
End RefItable7.

Module RefItable8.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma zx_shl32_shr31 : forall d, 0 <= d < 2 ^ 31 -> (szwrap 32 d * 2 ^ 32) mod 2 ^ 64 / 2 ^ 31 = 2 * d.
Proof.
  intros d Hd. rewrite szwrap32_small by lia.
  rewrite Z.mod_small by (split; [nia|]; change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); nia).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma zx_shl32_shr30 : forall d, 0 <= d < 2 ^ 31 -> (szwrap 32 d * 2 ^ 32) mod 2 ^ 64 / 2 ^ 30 = 4 * d.
Proof.
  intros d Hd. rewrite szwrap32_small by lia.
  rewrite Z.mod_small by (split; [nia|]; change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); nia).
  change (2 ^ 32) with (4 * 2 ^ 30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma zx_shl32_shr30' : forall d, 0 <= d < 2 ^ 31 -> (d * 2 ^ 32) mod 2 ^ 64 / 2 ^ 30 = 4 * d.
Proof.
  intros d Hd. rewrite Z.mod_small by (split; [nia|]; change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); nia).
  change (2 ^ 32) with (4 * 2 ^ 30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma zx_shl32_shr31' : forall d, 0 <= d < 2 ^ 31 -> (d * 2 ^ 32) mod 2 ^ 64 / 2 ^ 31 = 2 * d.
Proof.
  intros d Hd. rewrite Z.mod_small by (split; [nia|]; change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); nia).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma u16_lext : tab_u16 lext_a 31 = true. Proof. vm_compute. reflexivity. Qed.
Lemma u16_lbase : tab_u16 lbase_a 31 = true. Proof. vm_compute. reflexivity. Qed.
Lemma u16_dext : tab_u16 dext_a 32 = true. Proof. vm_compute. reflexivity. Qed.
Lemma u16_dbase : tab_u16 dbase_a 32 = true. Proof. vm_compute. reflexivity. Qed.

Definition here_opv (t : codetype) (work : arr) (w : Z) : Z :=
  if w + 1 <? it_match t then 0
  else if it_match t <=? w then it_extra t work (w - it_match t) else 96.
Definition here_val (t : codetype) (work : arr) (w : Z) : Z :=
  if w + 1 <? it_match t then w
  else if it_match t <=? w then it_base t work (w - it_match t) else 0.

Lemma code_pack_wrap8_op : forall a b c, code_pack (wrap8 a) b c = code_pack a b c.
Proof. intros. unfold code_pack. rewrite !wrap8_mod, Z.mod_mod by lia. reflexivity. Qed.
Lemma code_pack_wrap8_bits : forall a b c, code_pack a (wrap8 b) c = code_pack a b c.
Proof. intros. unfold code_pack. rewrite !wrap8_mod, Z.mod_mod by lia. reflexivity. Qed.

Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

Local Notation SV0 := RefItable1.SV0.
Local Notation slots_in := RefItable1.slots_in.
Local Notation ext_addr := RefItable7.ext_addr.
Local Notation base_addr := RefItable7.base_addr.
End Walk.
End RefItable8.

Module RefItable9.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma zext16_dec : forall d, -1 <= d < 65536 -> (szwrap 32 d * 2 ^ 48) mod 2 ^ 64 / 2 ^ 48 = d mod 65536.
Proof.
  intros d Hd. rewrite szwrap32_small by lia.
  change (2 ^ 64) with (65536 * 2 ^ 48). rewrite Z.mul_mod_distr_r by lia.
  rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma shl32p_shr31 : forall d, (d * 2 ^ 32 + 4294967296) / 2 ^ 31 = 2 * (d + 1).
Proof.
  intros d. replace (d * 2 ^ 32 + 4294967296) with ((2 * (d + 1)) * 2 ^ 31) by lia.
  rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma shl32p_shr31' : forall d, 0 <= d -> d + 1 < 2 ^ 31 -> (d * 2 ^ 32 + 4294967296) mod 2 ^ 64 / 2 ^ 31 = 2 * (d + 1).
Proof.
  intros d H0 H1. rewrite Z.mod_small by (split; [nia|]; change (2 ^ 64) with (2 ^ 31 * 2 ^ 33); nia).
  apply shl32p_shr31.
Qed.

Definition newhuff (huff inc : Z) : Z := if negb (inc =? 0) then Z.land huff (inc - 1) + inc else 0.

Lemma land_pow2_range : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= a /\ Z.land a b <= b.
Proof.
  intros a b Ha Hb. pose proof (land_upper a b Ha) as H1. pose proof (land_upper b a Hb) as H2.
  rewrite (Z.land_comm b a) in H2. lia.
Qed.


Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

Local Notation SV0 := RefItable1.SV0.
Local Notation slots_in := RefItable1.slots_in.
Local Notation ext_addr := RefItable7.ext_addr.
Local Notation base_addr := RefItable7.base_addr.


Definition lowreg (l : Z) : Z := if l =? 4294967295 then -1 else l.

End Walk.
End RefItable9.

Module RefItable10.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable8.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma shl32c_shr31 : forall d c k, c = k * 4294967296 -> (d * 2 ^ 32 + c) / 2 ^ 31 = 2 * (d + k).
Proof.
  intros d c k ->. replace (d * 2 ^ 32 + k * 4294967296) with ((2 * (d + k)) * 2 ^ 31) by lia.
  rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma shl32c_shr31' : forall d c k, c = k * 4294967296 -> 0 <= d + k < 2 ^ 31 ->
  (d * 2 ^ 32 + c) mod 2 ^ 64 / 2 ^ 31 = 2 * (d + k).
Proof.
  intros d c k Hc Hb. rewrite Z.mod_small by (subst c; split; [nia|]; change (2 ^ 64) with (2 ^ 31 * 2 ^ 33); nia).
  apply shl32c_shr31. exact Hc.
Qed.

Ltac norm_shl32 :=
  repeat match goal with
  | |- context [(?d * 2 ^ 32 + ?c) mod 2 ^ 64 / 2 ^ 31] =>
      let k := eval vm_compute in (c / 4294967296) in
      rewrite (shl32c_shr31' d c k eq_refl) by lia
  | |- context [(?d * 2 ^ 32 + ?c) / 2 ^ 31] =>
      let k := eval vm_compute in (c / 4294967296) in
      rewrite (shl32c_shr31 d c k eq_refl)
  end.

Lemma curr_rec_fuel_le : forall count drop max n n' curr lft,
  0 <= curr -> 0 <= drop -> curr + drop <= max -> max <= 15 ->
  max - (curr + drop) <= Z.of_nat n -> max - (curr + drop) <= Z.of_nat n' ->
  curr_rec count drop max n curr lft = curr_rec count drop max n' curr lft.
Proof.
  intros count drop max n. revert max.
  induction n as [|n IH]; intros max n' curr lft H0 H1 H2 H3 Hn Hn'.
  - destruct n' as [|n']; [reflexivity|]. cbn [curr_rec]. unfold curr_step.
    rewrite !wrap32_id by lia. replace (curr + drop <? max) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - destruct n' as [|n'].
    + cbn [curr_rec]. unfold curr_step. rewrite !wrap32_id by lia.
      replace (curr + drop <? max) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    + cbn [curr_rec]. unfold curr_step. rewrite !wrap32_id by lia.
      destruct (Z.ltb_spec (curr + drop) max); [|reflexivity].
      destruct (_ <=? 0); [reflexivity|]. cbn [fst snd]. apply IH; lia.
Qed.

Lemma curr_step_small : forall cnt drop mx curr lft,
  0 <= curr <= 15 -> 0 <= drop <= 15 ->
  curr_step cnt drop mx (curr, lft) =
  (if curr + drop <? mx then
     if lft - arr_get cnt (curr + drop) <=? 0 then (false, (curr, lft - arr_get cnt (curr + drop)))
     else (true, (curr + 1, Z.shiftl (lft - arr_get cnt (curr + drop)) 1))
   else (false, (curr, lft))).
Proof. intros. unfold curr_step. rewrite !wrap32_id by lia. reflexivity. Qed.


Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

End Walk.
End RefItable10.

Module RefItable11.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastMem.ItableMem2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable8.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition SAVB (s0v s4v s6v s7v s8v s9v s10v s11v : Z) : list (Z * nat * Z) :=
  [(200, 8%nat, s0v); (168, 8%nat, s4v); (152, 8%nat, s6v); (144, 8%nat, s7v); (136, 8%nat, s8v);
   (128, 8%nat, s9v); (120, 8%nat, s10v); (112, 8%nat, s11v)].
Definition SAVA (s1v s2v s3v s5v : Z) : list (Z * nat * Z) :=
  [(192, 8%nat, s1v); (184, 8%nat, s2v); (176, 8%nat, s3v); (160, 8%nat, s5v)].


Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

Local Notation SV0 := RefItable1.SV0.
Local Notation slots_in := RefItable1.slots_in.
Local Notation ext_addr := RefItable7.ext_addr.
Local Notation base_addr := RefItable7.base_addr.
Local Notation isLENS := RefItable7.isLENS.
Local Notation isDISTS := RefItable7.isDISTS.

Lemma szwrap64_div4_mod16 : forall x, (szwrap 64 x / 2 ^ 2) mod 2 ^ 16 = (x / 2 ^ 2) mod 2 ^ 16.
Proof.
  intros x. unfold szwrap. change (2 ^ (64 - 1)) with 9223372036854775808.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 2) with 4. change (2 ^ 16) with 65536.
  Z.to_euclidean_division_equations. lia.
Qed.

End Walk.
End RefItable11.

Module RefItable12.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastMem.ItableMem2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable8.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable10.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable11.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma it_step_eq : forall x st,
  it_step x st =
  let ty := x_ty x in
  let w := arr_get (t_work st) (t_sym st) in
  let here := code_pack (RefItable8.here_opv ty (t_work st) w) (wrap8 (t_len st - t_drop st)) (RefItable8.here_val ty (t_work st) w) in
  let fill := shl32 1 (t_curr st) in
  let tbl := it_fill here (shl32 1 (t_len st - t_drop st)) (t_huff st) (t_drop st) (t_next st) fill (t_tbl st) in
  let huff := RefItable9.newhuff (t_huff st) (it_incr_back (t_huff st) (t_len st)) in
  let sym := wrap32 (t_sym st + 1) in
  let c := wrap16 (arr_get (t_count st) (t_len st) - 1) in
  let count := arr_set (t_count st) (t_len st) c in
  let len := if (c =? 0) && negb (t_len st =? x_max x)
             then arr_get (x_lens x) (x_lens_ofs x + arr_get (t_work st) sym) else t_len st in
  let st1 := mkItSt huff sym len (t_next st) (t_curr st) (t_drop st) (t_low st) (t_used st) fill count tbl (t_work st) in
  if (c =? 0) && (t_len st =? x_max x) then ItBreak st1
  else if (x_root x <? len) && negb (Z.land huff (x_mask x) =? t_low st) then
    let drop := if t_drop st =? 0 then x_root x else t_drop st in
    let next := t_next st + fill in
    let curr := it_subtable_curr count len drop (x_max x) in
    let used := wrap32 (t_used st + Z.shiftl 1 curr) in
    let st2 := mkItSt huff sym len next curr drop (t_low st) used fill count tbl (t_work st) in
    if it_not_enough ty used then ItFail st2
    else ItCont (mkItSt huff sym len next curr drop (Z.land huff (x_mask x)) used fill count
                        (arr_set tbl (x_table x + Z.land huff (x_mask x)) (code_pack curr (x_root x) (next - x_table x)))
                        (t_work st))
  else ItCont st1.
Proof.
  intros x st. unfold it_step, RefItable8.here_opv, RefItable8.here_val, RefItable9.newhuff. cbv zeta.
  destruct (arr_get (t_work st) (t_sym st) + 1 <? it_match (x_ty x));
    [| destruct (it_match (x_ty x) <=? arr_get (t_work st) (t_sym st))]; rewrite ?RefItable8.code_pack_wrap8_op; reflexivity.
Qed.

Lemma shl32_pow2 : forall k, 0 <= k <= 15 -> shl32 1 k = 2 ^ k.
Proof. intros k Hk. pose proof (itm_used_pow2 k Hk) as H. unfold itm_used in H. exact H. Qed.


Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

Local Notation SV0 := RefItable1.SV0.
Local Notation slots_in := RefItable1.slots_in.
Local Notation ext_addr := RefItable7.ext_addr.
Local Notation base_addr := RefItable7.base_addr.
Local Notation isLENS := RefItable7.isLENS.
Local Notation isDISTS := RefItable7.isDISTS.
Local Notation lowreg := RefItable9.lowreg.

Local Ltac fr1 H1 := rewrite (H1 _ eq_refl).
Local Ltac by_frames5 H5 H4 H3 H2 H1 Q := rewrite (H5 _ eq_refl), (H4 _ eq_refl), (H3 _ eq_refl), (H2 _ eq_refl), (H1 _ eq_refl); exact Q.

End Walk.
End RefItable12.

Module RefItable_run.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ItableModel3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ItableModel3.ItableModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DSLayout.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DSLayout.ItableRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastMem.ItableMem2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable8.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable10.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable11.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable12.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma it_step_work : forall x st,
  match it_step x st with ItCont s | ItBreak s | ItFail s => t_work s end = t_work st.
Proof.
  intros x st. rewrite RefItable12.it_step_eq. cbv zeta.
  destruct (_ && (t_len st =? x_max x)); [reflexivity|].
  destruct ((x_root x <? _) && _); [|reflexivity].
  destruct (it_not_enough _ _); reflexivity.
Qed.

Lemma it_left_check_split : forall cnt,
  it_left_check cnt = if 2 - arr_get cnt 1 <? 0 then None else left_rec cnt 15 2 (2 - arr_get cnt 1).
Proof.
  intros cnt. rewrite it_left_check_rec, left_rec_S. unfold MAXBITS. cbn [Z.leb].
  change (Z.shiftl 1 1) with 2. reflexivity.
Qed.


Section Walk.

Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

Local Notation SV0 := RefItable1.SV0.
Local Notation slots_in := RefItable1.slots_in.
Local Notation ext_addr := RefItable7.ext_addr.
Local Notation base_addr := RefItable7.base_addr.
Local Notation isLENS := RefItable7.isLENS.
Local Notation isDISTS := RefItable7.isDISTS.
Local Notation lowreg := RefItable9.lowreg.

End Walk.
End RefItable_run.

Module RefItableGen.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCalleeSpec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCalleeSpec.ItableCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItable_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

End RefItableGen.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefItableGen.

Module RefInflateSafeFCw.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCalleeSpec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeFC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem inflate_fast_congr_proof : inflate_fast_congr_stmt.
Proof. exact inflate_fast_congr. Qed.
End RefInflateSafeFCw.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateArms.RefInflateSafeFCw.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeFR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_TERM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_TERM.RefInflateA_BAD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_TERM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_TERM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_TERM.RefInflateA_LIT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_TERM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_TERM.RefInflateA_TYPE.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_CHECK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CHECK.RefInflateA_LENGTH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DICT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_CHECK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST.RefInflateA_COPY.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_STORED.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_NAME.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_FLAGS.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_FLAGS.RefInflateA_HDR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_FLAGS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_HEAD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST.RefInflateA_LENEXT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_DIST.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_DIST.RefInflateA_MATCH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LEN.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_CODELENS11.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_TABLE.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_CODELENS11.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateA_CODELENS11.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma codelens_body_leave_okb : forall s c r (b : bool) s1 c1 r1,
  codelens_body (mkW s c r) = ARun b (mkW s1 c1 r1) -> leave_okb s1 = leave_okb s.
Proof.
  intros s c r b s1 c1 r1 H. rewrite codelens_body_eq in H.
  change (DECODE1 (is_lencode s) (is_lenbits s)) with (DECODE_k 8 (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits) in H.
  destruct (DECODE_k 8 (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits (mkW s c r)) as [here [s0 c0 r0] | w | rc w] eqn:HD; [| discriminate H | discriminate H].
  destruct (DECODE_k_run' _ _ _ _ _ _ _ _ _ _ _ HD) as [-> ->].
  destruct (code_val here <? 16); [injection H as _ <- _ _; reflexivity|].
  unfold NEEDBITS in H.
  destruct (NEEDBITS_k 8 (code_bits here + cl_nb (code_val here)) (mkW s c r0)) as [[] [s2 c2 r2] | w | rc w] eqn:HN; [| discriminate H | discriminate H].
  destruct (NEEDBITS_k_run' _ _ _ _ _ _ _ _ HN) as [-> ->].
  unfold cl_after, cl_bad in H.
  destruct ((code_val here =? 16) && (is_have s =? 0)); [injection H as _ <- _ _; reflexivity|].
  cbv zeta in H. destruct (is_nlen s + is_ndist s <? _); injection H as _ <- _ _; [reflexivity|].
  unfold cl_rep. destruct (lrep _ _ _ _ _) as [[l h] cp]. reflexivity.
Qed.
Lemma codelens_while_leave_okb : forall k s c r (u : unit) s1 c1 r1,
  codelens_while k (mkW s c r) = ARun u (mkW s1 c1 r1) -> leave_okb s1 = leave_okb s.
Proof.
  induction k as [|k IH]; intros s c r u s1 c1 r1 H; destruct u.
  - rewrite codelens_while_O in H. injection H as <- _ _. reflexivity.
  - rewrite codelens_while_S in H. destruct (is_have s <? is_nlen s + is_ndist s); [| injection H as <- _ _; reflexivity].
    destruct (codelens_body (mkW s c r)) as [[|] [s' c' r'] | w | rc w] eqn:HB; [| | discriminate H | discriminate H].
    + rewrite (IH _ _ _ _ _ _ _ H). exact (codelens_body_leave_okb _ _ _ _ _ _ _ HB).
    + injection H as <- _ _. exact (codelens_body_leave_okb _ _ _ _ _ _ _ HB).
Qed.

Section Arms.

  Definition codelens_chain (flush : Z) (w : iw) : bool :=
    codelens_okb w && match codelens_next flush w with Some w2 => len__chain w2 | None => true end.
  Definition lenlens_chain (flush : Z) (w : iw) : bool :=
    lenlens_okb w && match lenlens_next w with Some w2 => codelens_chain flush w2 | None => true end.
  Definition table_chain (flush : Z) (w : iw) : bool :=
    match table_next w with Some w2 => lenlens_chain flush w2 | None => true end.

  Definition okL (flush : Z) (w : iw) : bool :=
    let s := w_s w in let m := is_mode s in
    if (m =? DICT) || (m =? MEM) || (m =? SYNC) then true
    else leave_okb s &&
      (if m =? DISTEXT then distext_chain w
       else if m =? DIST then dist_chain w
       else if m =? LENEXT then lenext_chain w
       else if m =? MATCH then match_okb s
       else if m =? LEN then len_chain w
       else if m =? LEN_ then len__chain w
       else if m =? TABLE then table_chain flush w
       else if m =? LENLENS then lenlens_chain flush w
       else if m =? CODELENS then codelens_chain flush w
       else true).
  Local Ltac xe_leaf := split; [assumption | repeat (split; [first [assumption | reflexivity] |]); first [assumption | reflexivity]].
  Local Ltac okL_at H Hm := unfold okL in H; cbn [w_s w_c w_r] in H; rewrite Hm in H; cbn -[leave_okb distext_chain dist_chain lenext_chain match_okb len_chain len__chain table_chain lenlens_chain codelens_chain iset_mode] in H.
  Local Ltac ok_leave := intros flush w Hm H; okL_at H Hm; first [exact H | apply andb_prop in H; exact (proj1 H)].
  Local Ltac ok_both := intros flush w Hm H; okL_at H Hm; apply andb_prop in H; exact H.

  Lemma okL_plain : forall flush s c r m,
    is_mode s = m ->
    In m [HEAD; FLAGS; TIME; OS; EXLEN; EXTRA; NAME; COMMENT; HCRC; DICTID; TYPE; TYPEDO; STORED; COPY_; COPY; LIT; CHECK; LENGTH; DONE; BAD] ->
    okL flush (mkW s c r) = leave_okb s.
  Proof.
    intros flush s c r m Hm Hin. unfold okL. cbn [w_s w_c w_r]. rewrite Hm. cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn -[leave_okb]; apply Bool.andb_true_r|]). destruct Hin.
  Qed.
  Local Ltac inm := cbn; repeat (first [left; reflexivity | right]).

  Lemma okL_type1 : forall flush s c' r', okL flush (mkW (iset_mode (iset_check s 1) TYPE) c' r') = true.
  Proof.
    intros. rewrite (okL_plain flush (iset_mode (iset_check s 1) TYPE) c' r' TYPE eq_refl ltac:(inm)).
    unfold leave_okb. cbn [is_wrap is_flags is_check iset_mode iset_check]. rewrite Bool.orb_true_iff. right. reflexivity.
  Qed.

  Lemma okL_carry : forall flush s c r s' c' r' m m',
    is_mode s = m -> okL flush (mkW s c r) = true ->
    In m [HEAD; FLAGS; TIME; OS; EXLEN; EXTRA; NAME; COMMENT; HCRC; DICTID; TYPE; TYPEDO; STORED; COPY_; COPY; LIT; CHECK; LENGTH; DONE; BAD] ->
    is_mode s' = m' ->
    In m' [HEAD; FLAGS; TIME; OS; EXLEN; EXTRA; NAME; COMMENT; HCRC; DICTID; TYPE; TYPEDO; STORED; COPY_; COPY; LIT; CHECK; LENGTH; DONE; BAD] ->
    is_wrap s' = is_wrap s -> is_flags s' = is_flags s -> is_check s' = is_check s ->
    okL flush (mkW s' c' r') = true.
  Proof.
    intros flush s c r s' c' r' m m' Hm H Hin Hm' Hin' E1 E2 E3.
    rewrite (okL_plain flush s c r m Hm Hin) in H. rewrite (okL_plain flush s' c' r' m' Hm' Hin').
    unfold leave_okb in *. rewrite E1, E2, E3. exact H.
  Qed.
  Lemma hcrc_on_flags : forall s, hcrc_on s = true -> (is_flags s =? 0) = false.
  Proof.
    intros s H. unfold hcrc_on in H. apply andb_prop in H. destruct H as [H _].
    apply Z.eqb_neq. intros E. rewrite E in H. discriminate H.
  Qed.
  Lemma flags_deflated_nz : forall f, Z.land f 255 = Z_DEFLATED -> (f =? 0) = false.
  Proof. intros f H. apply Z.eqb_neq. intros E. rewrite E in H. cbv in H. discriminate H. Qed.
  Lemma okL_hcrc : forall flush s s' c' r' m', hcrc_on s = true -> is_mode s' = m' ->
    In m' [HEAD; FLAGS; TIME; OS; EXLEN; EXTRA; NAME; COMMENT; HCRC; DICTID; TYPE; TYPEDO; STORED; COPY_; COPY; LIT; CHECK; LENGTH; DONE; BAD] ->
    is_flags s' = is_flags s -> okL flush (mkW s' c' r') = true.
  Proof.
    intros flush s s' c' r' m' Hon Hm' Hin' E2. rewrite (okL_plain flush s' c' r' m' Hm' Hin').
    unfold leave_okb. rewrite E2, (hcrc_on_flags s Hon). cbn [negb]. rewrite Bool.orb_true_r. reflexivity.
  Qed.
  Local Ltac carry m m' := intros; eapply (okL_carry _ _ _ _ _ _ _ m m'); [eassumption | eassumption | inm | reflexivity | inm | reflexivity | reflexivity | reflexivity].
  Local Ltac hcarry m' := intros; eapply (okL_hcrc _ _ _ _ _ m'); [eassumption | reflexivity | inm | reflexivity].

  Lemma leave_okb_same : forall s s', is_wrap s' = is_wrap s -> is_flags s' = is_flags s -> is_check s' = is_check s ->
    leave_okb s' = leave_okb s.
  Proof. intros s s' E1 E2 E3. unfold leave_okb. rewrite E1, E2, E3. reflexivity. Qed.
  Local Ltac okL_goal m := unfold okL; cbn [w_s w_c w_r]; rewrite m; cbn -[leave_okb distext_chain dist_chain lenext_chain match_okb len_chain len__chain table_chain lenlens_chain codelens_chain iset_mode].

  Lemma distext_next_facts : forall w w2, distext_next w = Some w2 ->
    is_mode (w_s w2) = MATCH /\ leave_okb (w_s w2) = leave_okb (w_s w).
  Proof.
    intros [s c r] w2 H. unfold distext_next in H. cbn [w_s w_c w_r] in H.
    destruct (is_extra s =? 0); [injection H as <-; split; reflexivity|].
    destruct (NEEDBITS (is_extra s) (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1]; try discriminate H.
    injection H as <-. split; reflexivity.
  Qed.
  Lemma dist_next_facts : forall w w2, dist_next w = Some w2 ->
    is_mode (w_s w2) = DISTEXT /\ leave_okb (w_s w2) = leave_okb (w_s w).
  Proof.
    intros [s c r] w2 H. unfold dist_next in H. cbn [w_s w_c w_r] in H.
    destruct (DECODE1 (is_distcode s) (is_distbits s) (mkW s c r)) as [last [s1 c1 r1] | w1 | rc w1]; try discriminate H.
    assert (TL : forall h rt sb, dist_tailnext s c h rt sb = Some w2 -> is_mode (w_s w2) = DISTEXT /\ leave_okb (w_s w2) = leave_okb s).
    { intros h rt sb X. unfold dist_tailnext in X. destruct (negb (Z.land (code_op h) 64 =? 0)); [discriminate X|]. injection X as <-. split; reflexivity. }
    destruct (dist_two (code_op last)); [| exact (TL _ _ _ H)].
    destruct (DECODE2 (is_distcode s) last (mkW s c r1)) as [here [s2 c2 r2] | w1 | rc w1]; try discriminate H. exact (TL _ _ _ H).
  Qed.
  Lemma lenext_next_facts : forall w w2, lenext_next w = Some w2 ->
    is_mode (w_s w2) = DIST /\ leave_okb (w_s w2) = leave_okb (w_s w).
  Proof.
    intros [s c r] w2 H. unfold lenext_next in H. cbn [w_s w_c w_r] in H.
    destruct (is_extra s =? 0); [injection H as <-; split; reflexivity|].
    destruct (NEEDBITS (is_extra s) (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1]; try discriminate H.
    injection H as <-. split; reflexivity.
  Qed.
  Lemma len_next_facts : forall w w2, len_next w = Some w2 ->
    is_mode (w_s w2) = LENEXT /\ leave_okb (w_s w2) = leave_okb (w_s w).
  Proof.
    intros [s c r] w2 H. unfold len_next in H. cbn [w_s w_c w_r] in H.
    destruct ((6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)); [discriminate H|].  (* 1.4 (zl14infl-r2): the fast path also needs bits < 8 *)
    assert (TL : forall h rt sb, is_wrap sb = is_wrap s -> is_flags sb = is_flags s -> is_check sb = is_check s ->
              len_tailnext c h rt sb = Some w2 -> is_mode (w_s w2) = LENEXT /\ leave_okb (w_s w2) = leave_okb s).
    { intros h rt sb E1 E2 E3 X. unfold len_tailnext in X. cbv zeta in X.
      destruct ((code_op h =? 0) || negb (Z.land (code_op h) 32 =? 0) || negb (Z.land (code_op h) 64 =? 0)); [discriminate X|].
      injection X as <-. split; [reflexivity|]. cbn [w_s]. apply leave_okb_same; cbn; assumption. }
    destruct (DECODE1 (is_lencode s) (is_lenbits s) (mkW (iset_back s 0) c r)) as [last [s1 c1 r1] | w1 | rc w1]; try discriminate H.
    destruct (len_two (code_op last)); [| exact (TL last r1 (iset_back s 0) eq_refl eq_refl eq_refl H)].
    destruct (DECODE2 (is_lencode s) last (mkW (iset_back s 0) c r1)) as [here [s2 c2 r2] | w1 | rc w1]; try discriminate H.
    exact (TL here (ddrop r2 (code_bits last)) (addback (iset_back s 0) (code_bits last)) eq_refl eq_refl eq_refl H).
  Qed.
  Lemma table_next_facts : forall w w2, table_next w = Some w2 ->
    is_mode (w_s w2) = LENLENS /\ (leave_okb (w_s w) = true -> leave_okb (w_s w2) = true).
  Proof.
    intros [s c r] w2 H. unfold table_next in H.
    destruct (NEEDBITS 14 (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1] eqn:HN; try discriminate H.
    destruct (_ || _); [discriminate H|]. injection H as <-.
    destruct (NEEDBITS_k_run 8 _ s c r s1 c1 r1 HN) as [-> ->]. split; [reflexivity | intros X; exact X].
  Qed.
  Lemma lenlens_next_facts : forall w w2, lenlens_next w = Some w2 ->
    is_mode (w_s w2) = CODELENS /\ (leave_okb (w_s w) = true -> leave_okb (w_s w2) = true).
  Proof.
    intros [s c r] w2 H. unfold lenlens_next in H.
    destruct (lenlens_while1 19 (mkW s c r)) as [[] [s1 c1 r1] | w1 | rc w1] eqn:HW; try discriminate H.
    cbv zeta in H.
    destruct (inflate_table CODES (is_lens (ll2 19 s1)) 0 19 (is_codes (ll2 19 s1)) 0 7 (is_work (ll2 19 s1))) as [[[[ret tbl] nxt] lb] wk].
    destruct (ret =? 0); [| discriminate H].
    apply (f_equal (fun o => match o with Some x => x | None => w2 end)) in H. cbn beta iota in H. subst w2. cbn [w_s].
    split; [reflexivity|]. intros Hl.
    rewrite (leave_okb_same (ll2 19 s1) (ll_s2 (ll_tab (ll2 19 s1) tbl nxt lb wk)) eq_refl eq_refl eq_refl).
    rewrite (ll2_leave_okb 19 s1). rewrite (lenlens_while1_leave_okb 19 s c r s1 c1 r1 HW). exact Hl.
  Qed.
  Lemma codelens_next_facts : forall flush w w2, codelens_next flush w = Some w2 ->
    is_mode (w_s w2) = LEN_ /\ (leave_okb (w_s w) = true -> leave_okb (w_s w2) = true).
  Proof.
    intros flush [s c r] w2 H. rewrite codelens_next_eq in H.
    destruct (codelens_while 321 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1] eqn:HW; try discriminate H.
    destruct (is_mode s1 =? BAD); [discriminate H|]. unfold cl_post_next in H.
    destruct (arr_get (is_lens s1) 256 =? 0); [discriminate H|].
    destruct (inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as [[[[ret tbl] nxt] lb] wk].
    destruct (negb (ret =? 0)); [discriminate H|]. cbv zeta in H.
    destruct (inflate_table DISTS _ _ _ _ _ 6 _) as [[[[ret2 tbl2] nxt2] db] wk2].
    destruct (negb (ret2 =? 0)); [discriminate H|]. destruct (flush =? Z_TREES); [discriminate H|].
    apply (f_equal (fun o => match o with Some x => x | None => w2 end)) in H. cbn beta iota in H. subst w2. cbn [w_s].
    split; [reflexivity|]. intros Hl. rewrite leave_okb_tab2. rewrite (codelens_while_leave_okb 321 s c r u s1 c1 r1 HW). exact Hl.
  Qed.
End Arms.
