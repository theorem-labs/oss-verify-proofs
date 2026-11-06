(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface LeptC_deser2_defs D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

Section DESER1_DEFS.
Variable RT : rt_sig.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (QF : config -> Prop) (fr : Z).

Definition deser_cut1_stmt_0 (dp n : Z) : Prop :=
  forall (S : rts RT) (mc : mem) (nc w h d psz : Z)
         (j0 j1 f0 f1 f2 : list byte) (c24 c48 vx px : word)
         (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r19 r26 r28 r29 r30 r31 : word) F' fc',
    ART RT S mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -192) ->
    rw_cells asegs mc (usp + -192)
      [CB 16 j0; C8 (Z_to_bv 64 (dp + 4 * nc)); C8 c24; C8 (Z_to_bv 64 psz); C8 (Z_to_bv 64 nc); C8 c48; C8 (Z_to_bv 64 nc);
       CB 16 j1; C8 (Z_to_bv 64 fr);
       C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mc fr [CB 32 f0; C4 vx; CB 44 f1; C8 px; CB 32 f2] ->
    rw_cells asegs mc (fr / 8 + 2147450880) deser_fshadow ->
    LIBH mc -> io_ssp mc -> agree_on (deser_PF RT Σ usp) m mc ->
    rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_credit RT Σ - 42 <= rt_credit RT S ->
    rt_live RT S = rt_live RT Σ ->
    0 <= nc <= 256 -> 1 <= w <= 1000000 -> 1 <= h <= 1000000 -> - 2^31 <= d < 2^31 ->
    psz = 4 * (((w * d + 31) / 32) * h) -> 0 < psz <= 0x4000000 -> psz = n - 28 - 4 * nc ->
    cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))
                                    r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 (Z_to_bv 64 dp) (Z_to_bv 64 w) (Z_to_bv 64 h) (Z_to_bv 64 fr)
                                    (Z_to_bv 64 d) (Z_to_bv 64 (fr / 8 + 2147450880)) r26 (Z_to_bv 64 2147450880) r28 r29 r30 r31 F' fc' 0x94788 mc))) QF.
(* [comment removed for export] *)
Definition deser_cut1_stmt_16 (dp n : Z) : Prop :=
  forall (S : rts RT) (mc : mem) (nc w h d psz : Z)
         (j0 j1 jp f0 f1 f2 : list byte) (c24 c48 vx px : word)
         (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r19 r26 r28 r29 r30 r31 : word) F' fc',
    ART RT S mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -208) ->
    rw_cells asegs mc (usp + -208)
      [CB 16 j0; C8 (Z_to_bv 64 (dp + 4 * nc)); C8 c24; C8 (Z_to_bv 64 psz); C8 (Z_to_bv 64 nc); C8 c48; C8 (Z_to_bv 64 nc);
       CB 16 j1; C8 (Z_to_bv 64 fr); CB 16 jp;
       C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mc fr [CB 32 f0; C4 vx; CB 44 f1; C8 px; CB 32 f2] ->
    rw_cells asegs mc (fr / 8 + 2147450880) deser_fshadow ->
    LIBH mc -> io_ssp mc -> agree_on (deser_PF RT Σ usp) m mc ->
    rt_frames RT S = (fr, 1%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_credit RT Σ - 42 <= rt_credit RT S ->
    rt_live RT S = rt_live RT Σ ->
    0 <= nc <= 256 -> 1 <= w <= 1000000 -> 1 <= h <= 1000000 -> - 2^31 <= d < 2^31 ->
    psz = 4 * (((w * d + 31) / 32) * h) -> 0 < psz <= 0x4000000 -> psz = n - 28 - 4 * nc ->
    cps asegs (ASTA RT S PMc (eq (entry_st r1 (Z_to_bv 64 (usp + -208)) gp (Z_to_bv 64 TP_A) r5 r6 r7 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -208))
                                    r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 fr) r19 (Z_to_bv 64 dp) (Z_to_bv 64 w) (Z_to_bv 64 h) (Z_to_bv 64 fr)
                                    (Z_to_bv 64 d) (Z_to_bv 64 (fr / 8 + 2147450880)) r26 (Z_to_bv 64 2147450880) r28 r29 r30 r31 F' fc' 0x94788 mc))) QF.
End DESER1_DEFS.
