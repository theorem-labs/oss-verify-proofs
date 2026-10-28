(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_fa_iface AF_huf_z4d_iface AF_huf_z4e.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Theorem dec_4x2_proofA : forall (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop),
  z4d_stmtA -> fast_args_stmtA -> dec4_int_stmtA AI rng_fs x2_tabA AHUF_DX2_4X.
Proof.
  intros AI rng_fs SLOWD FAP.
  intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m st LB DST dcap S DT mtl flags pdt src lo rstk
    AH NFK ABL MTL HDT TAB DSTF DC SRC BYS NSM S16 SIN DJ1 DJ2 DJ3 STK LOA LOS RCL RLO RHI RRL SPT SP16 MI TPA FL HINV
    WSK WIM WIS WFS RRS E0 E1 E2 E3 E4 E5.
  subst a0 a1 a2 a3 a4 a5.
  destruct TAB as (tl & cells & HDR & LCE & TOK & TLM & CBS).
  assert (TL1 : 1 <= tl) by (destruct TOK as (TB & _); lia).
  assert (LCB : zlen (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells)) = 4 * 2^tl).
  { rewrite length_firstn, x2_bytes'_length.
    pose proof (Z.pow_le_mono_r 2 tl mtl ltac:(lia) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)).
    lia. }
  assert (SB : exists SBL SBH, 0 < zlen src -> exists p, In (HB p SBL (SBH - SBL)) LB /\ SBL <= S /\ S + zlen src <= SBH).
  { destruct (Z_lt_dec 0 (zlen src)) as [NP | NP].
    - destruct (SIN NP) as (p & A & k & IN & H1 & H2). exists A, (A + k). intros _. exists p.
      replace (A + k - A) with k by lia. auto.
    - exists 0, 0. intros C. lia. }
  destruct SB as (SBL & SBH & SRCB).
  assert (DJ3' : KXGoM.apart DST dcap DT (DTABLE_BYTES mtl)) by (unfold KXGoM.apart; lia).
  eapply (z4_entry AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m DST dcap S DT mtl tl lo
            src cells (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells)) pdt SBL SBH rstk);
    first [ eassumption | reflexivity | lia ].
Qed.
End CANSEC1.
