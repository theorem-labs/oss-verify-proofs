(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_kx AZ_globals AZ_globalsR AZ_huf_iface AZ_seq_bit_iface.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].
Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.

Theorem zd_reload_int_proofA : zd_reload_int_stmtA.
Proof.
  unfold zd_reload_int_stmtA, APZD_RELOADI. intros until sqb.
  intros HBD SQB R1 R2 R3 R4 A1 DJ RB RPT RPT2 STK LOS SPB OS1 OS2 APB AROB AROQ ART AST MI.
  remember (Z.of_nat (length sqb)) as n eqn:En.
  unfold sbd_cells in HBD.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct AROB as (UB & RGB & RGBS). destruct AROQ as (UQ & RGQ & RGQS).
  assert (BDB : BD + 40 <= 0x7fff8000 \/ 0x10007fff8000 <= BD) by (unfold app_blk, KLOW, KHIGH, KEND in APB; clear - APB; lia).
  assert (MU : munch [(BD, BD + 40); (SPV - 16, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
    by (exists (bc / 8), (bc mod 8), (ptr - SEQ); clear - RB RPT RPT2; lia).
  destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
  assert (EDIV : (8 * q + r) / 8 = q /\ (8 * q + r) mod 8 = r) by (clear - Q1 Q2; split; [symmetry; apply (Z.div_unique (8 * q + r) 8 q r); lia | symmetry; apply (Z.mod_unique (8 * q + r) 8 q r); lia]).
  destruct EDIV as (ED & EM).
  assert (RG : 4096 <= BD < 2^47 /\ 4096 <= SEQ < 2^47 /\ 4096 <= SEQ + n < 2^47 /\ 16 <= n < 2^47) by lia.
  carve_frame 16%nat STK.
  clear APB.
  kx_autoFLAx [KAUnp BD 40; KAUnp SEQ n; KAApp BD 40; KAApp (SPV - 16) 16] (@nil Z) 150%nat
    [KZRange BD 4096 (2^47 - 40); KZRange SEQ 4096 (2^47); KZRange (SEQ + n) 4096 (2^47); KZRange n 16 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64;
     KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZRange SPV 4112 (2^47); KZAlign BD 8; KZWr BD 40; KZWr (SPV - 16) 16;
     KZDisj BD 40 SEQ n; KZDisj (SPV - 16) 16 BD 40; KZDisj (SPV - 16) 16 SEQ n]
    [(SEQ, n); (SPV - 16, 16); (BD, 40)] [(BD, 40); (SPV - 16, 16)].
  all: try kx_cell_lit; try kx_z; try kx_acc RI; try kx_acc RGQ; try kx_acc RGB.
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 616656) _ _ _ _) => kx_trap_fast | _ => idtac end.
  all: kx_mem.
  all: zstep.
  all: kx_abs.
  all: release_frame FR STK SPV.
  all: kx_mkR_fold.
  all: (apply evtF_done; unfold zd_reload_int_postA, sbd_cells; repeat (lazymatch goal with |- ex _ => eexists end);
        split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
        rewrite ED, EM; replace (SEQ + d - q) with (SEQ + (-1 * q + d)) by lia;
        match goal with H : rw_cells _ _ ?B (C8 _ :: C4 _ :: _) |- rw_cells _ _ ?B2 _ => constr_eq B B2; exact H end).
Qed.
End CANSEC1.
