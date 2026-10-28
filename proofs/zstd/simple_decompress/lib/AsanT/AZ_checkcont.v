(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_frame_iface AZ_dframe_iface AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.

Lemma zd_checkcont_proofA : zd_checkcont_stmtA.
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DCTX DST dsize expd lo.
  intros H1 D0 D1 DST0 DS0 ST LOS SPV47 SEPD DPOS D8 ARD ART AST MI -> -> ->.
  destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct (ARD ltac:(lia)) as (ABD & UD & RD & RDS). clear ARD.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (DA : DCTX + 29888 + 32 <= 0x7fff7000 \/ 0x10007fff8000 <= DCTX + 29888) by (unfold ablk, AIMG_HI, KLS in ABD; lia).
  unfold dctx_h1 in H1.
  assert (DAL : 0x625000 <= DCTX + 29888) by (unfold ablk, AIMG_HI, KLS in ABD; lia).
  assert (MU : munch [(DCTX + 29888, DCTX + 29920); (SPV - 16, SPV)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  unfold APZD_CHECKCONT.

  Time kx_autoFLAx [KAUnp (DCTX + 29888) 32; KAApp (DCTX + 29888) 40; KAApp (SPV - 16) 16] [] 80%nat
    [KZRange SPV 4096 (2^47); KZRange DCTX (0x625000 - 29888) (2^47); KZRange DST 0 (2^64 - 1); KZRange dsize 0 (2^64 - 1);
     KZAlign DCTX 8;
     KZWr (DCTX + 29888) 40; KZWr (SPV - 16) 16; KZDisj (DCTX + 29888) 40 (SPV - 16) 16]
    [(SPV - 16, 16); (DCTX + 29888, 40)] [(SPV - 16, 16); (DCTX + 29888, 32)].
  all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
  all: kx_mem.
  all: zstep.
  all: lazymatch goal with FRc : rw_cells _ ?mc (?S + -16) [_; C8 _], STc : stk _ ?mc ?l (?S + -16) |- _ => release_frame FRc STc S end.
  all: lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] =>
         apply evtF_done; unfold zd_checkcont_postA; do 15 eexists; exists mc end.
  all: split; [reflexivity|].
  all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
  all: unfold dctx_h1; change (bv_unsigned wz0) with 0 in *.
  all: destruct (Z.eqb_spec DST 0); destruct (Z.eqb_spec dsize 0); cbn [orb]; try lia; exact H1.
Qed.
End CANSEC1.
