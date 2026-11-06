(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep F_malloc_free.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocTree.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocKit_B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling}.
Definition fm_facts (st : mstate) (g : aptr) : Prop :=
  forall head, c_free_meta_head (ctx st) = Some head ->
    head <> g /\ meta_slot st head /\
    exists pv, m_prev (get_meta_rec st head) = Some pv /\ pv <> g /\ meta_slot st pv.

Lemma meta_word_meta0 : meta_word meta0 = 0. Proof. reflexivity. Qed.
End WithCeiling0.
