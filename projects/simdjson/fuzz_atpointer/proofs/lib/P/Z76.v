(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocP Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun Zpb Z3o Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Layout Exit Zfr Zq5 Sj_kit Sj_new Zq6 Zpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z9l Z9m Zb0 Z9n Z9o Z44 Z46 Z3u Z3r Z5m Z72.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

  Theorem atp_level : rmalloc_stmt -> rfree_stmt -> forall E, aenv_ok E -> forall d, atp_elem_stmt E d.
  Proof.
    intros HM HF E OK d. induction d as [|d IH].
    - apply (atp_elem E OK 0%nat); intros d' Ed; discriminate Ed.
    - apply (atp_elem E OK (S d)); intros d' Ed; injection Ed as <-.
      + exact (atp_obj E OK d IH HM HF).
      + exact (atp_arr E OK d IH).
  Qed.

  Theorem atp_obj_level : rmalloc_stmt -> rfree_stmt -> forall E, aenv_ok E -> forall d, atp_obj_stmt E d.
  Proof. intros HM HF E OK d. exact (atp_obj E OK d (atp_level HM HF E OK d) HM HF). Qed.

  Theorem atp_arr_level : rmalloc_stmt -> rfree_stmt -> forall E, aenv_ok E -> forall d, atp_arr_stmt E d.
  Proof. intros HM HF E OK d. exact (atp_arr E OK d (atp_level HM HF E OK d)). Qed.

  Theorem atp_root : rmalloc_stmt -> rfree_stmt -> forall E, aenv_ok E -> atp_root_stmt E.
  Proof.
    intros HM HF E OK.
    exact (atp_root_cps E OK (atp_obj_level HM HF E OK (Nat.pred TAPE_MAX_DEPTH)) (atp_arr_level HM HF E OK (Nat.pred TAPE_MAX_DEPTH))).
  Qed.

End WithCeiling0.
