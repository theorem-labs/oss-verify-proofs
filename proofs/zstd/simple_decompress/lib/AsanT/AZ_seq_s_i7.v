(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_ibase AZ_seq_s_iat AZ_seq_s_ikit AZ_seq_s_xat AZ_seq_s_a1_at.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].

Section CANSEC1. Context {rc : runConstT}.

Lemma sqs_i7_ok : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> LOCV = 2 ->
  a1_head P OEND LLO LEND LOCV (v_nbSeq P) -> ai_I7 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST HLOCV CONT.
  unfold ai_I7. unfold a1_head in CONT.
  intros m1 jseq jpad c0 c8 c208 c216 p0 p1 p2 cw bc ptr sLL sOF sML x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x24 x25 x26 x28 x29 x30 INV HBC BOK HS1 HS2 HS3.
  assert (HDO : v_DST P <= OEND) by (destruct P; exact (st4 _ _ _ _ _ ST)).
  assert (HLL : LLO <= LEND) by (destruct P; exact (st8 _ _ _ _ _ ST)).
      (* [comment removed for export] *)
  apply (CONT m1 c0 c8 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LLO (v_DST P) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x24 x25 x26 x28 x29 x30).
  - eapply sqs_iinv_linv. exact INV.
  - unfold sqs_lfacts. split; [lia|]. split; [lia|]. split; [exact HS1|]. split; [exact HS2|]. split; [exact HS3|]. split; [lia | exact BOK].
Qed.

End CANSEC1.
