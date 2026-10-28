(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_frame_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Lemma zd_iserror_proofA : zd_iserror_stmtA.
Proof.
  intros until c. intros Hc ->. unfold APZD_ISERROR.
  zstep. zstep. zstep. rewrite zd_is_error_sltiu.
  apply evtF_done. reflexivity.
Qed.

Lemma zd_errcode_proofA : zd_errcode_stmtA.
Proof.
  intros until c. intros Hc ->. unfold APZD_ERRCODE.
  zstep. zstep. zstep. zstep. zstep.
  apply evtF_done. unfold zd_errcode_postA. eexists.
  replace (Z.land ((Z.b2z (c <? 18446744073709551497) + -1) mod 18446744073709551616) (bv_swrap 32 (0 - c) mod 18446744073709551616))
    with (zd_error_code c); [reflexivity|].
  unfold zd_error_code. rewrite zd_is_error_lit. change (2^64) with 18446744073709551616 in *.
  destruct (Z.ltb_spec c 18446744073709551497); destruct (Z.ltb_spec 18446744073709551496 c); try lia; cbn [Z.b2z].
  - reflexivity.
  - sw32 (18446744073709551616 - c).
    change ((1 + -1) mod 18446744073709551616) with 0. change ((0 + -1) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.mod_small by lia. rewrite Z.land_comm, Z.land_ones by lia. change (2^64) with 18446744073709551616.
    rewrite Z.mod_small by lia. reflexivity.
Qed.
End CANSEC1.
