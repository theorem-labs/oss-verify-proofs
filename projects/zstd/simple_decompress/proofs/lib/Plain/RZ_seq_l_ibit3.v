(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase RZ_seq_l_ibit RZ_seq_l_ibit2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_bitinit : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> seql_ranges P -> ai_i1 P OEND LLO LEND LOCV -> ai_i0 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST RG0 CONT.
  destruct (Z_le_gt_dec 8 (zlen (y_sq P))) as [H8|H8]; [exact (seql_bitinit_a P OEND LLO LEND LOCV ST RG0 (or_introl H8) CONT)|].
  destruct (Z_le_gt_dec (zlen (y_sq P)) 3) as [H3|H3]; [exact (seql_bitinit_a P OEND LLO LEND LOCV ST RG0 (or_intror H3) CONT)|].
  apply (seql_bitinit_b P OEND LLO LEND LOCV ST RG0); [lia | exact CONT].
Qed.
