(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdWalkKit ZdCellKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_hft_initds_c1 AZ_hft_initds_c2 AZ_hft_initds_c3 AZ_hft_initds_c4 AZ_hft_initds_c5.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Notation FSE_INITDS_STACK_A := 16 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Theorem fse_initds_proofA : fse_initds_stmtA.
Proof.
  apply fse_initds_of_cases. intros K. unfold fse_initds_atA. intros until junk.
  intros KC MI STK LO0 LOS SPR STC BDC FOK BC2 SRCB SRCL DTC TLR A1 A2 A3 R1 R2 R3 R4 R5 R6 R7 R8 D1 D2 D3 D4 D5 OF1 OF2 OF3 OF4
         ART AST AROC AST16 ABD40 ADT4 ASRC APS APB.
  pose proof FOK as [BCR BOK].
  assert (CASES : 65 <= bc + tl \/ (bc + tl <= 64 /\ ptr = SRC) \/ (bc + tl <= 64 /\ 8 <= n /\ SRC + 8 <= ptr <= SRC + n - 8) \/
                  (bc + tl <= 64 /\ 8 <= n /\ SRC + 1 <= ptr <= SRC + 7 /\ ptr <= SRC + n - 8 /\ (bc + tl) / 8 <= ptr - SRC) \/
                  (bc + tl <= 64 /\ 8 <= n /\ SRC + 1 <= ptr <= SRC + 7 /\ ptr <= SRC + n - 8 /\ ptr - SRC < (bc + tl) / 8)).
  { clear - BOK BCR TLR. destruct (Z_le_gt_dec (bc + tl) 64) as [Bq|Bq]; [|left; lia]. destruct (BOK ltac:(lia)) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec (SRC + 8) ptr); [right; right; left; lia|]. destruct (Z.eq_dec ptr SRC); [right; left; lia|].
    destruct (Z_le_gt_dec ((bc + tl) / 8) (ptr - SRC)); [right; right; right; left; lia | right; right; right; right; lia]. }
  destruct CASES as [C|[C|[C|[C|C]]]].
  - eapply (fse_initds_c1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C); eassumption.
  - eapply (fse_initds_c2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C); eassumption.
  - eapply (fse_initds_c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C); eassumption.
  - eapply (fse_initds_c4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C); eassumption.
  - eapply (fse_initds_c5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C); eassumption.
Qed.
End CANSEC2.
