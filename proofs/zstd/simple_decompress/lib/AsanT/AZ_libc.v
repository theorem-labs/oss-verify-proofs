(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_libc_iface AF_fse_rd_mem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

Lemma zd_memsetZ_proofA : zd_memsetZ_stmtA.
Proof.
  unfold zd_memsetZ_stmtA.
  intros RNG A n c SPz ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo junk.
  intros DST Hn Hc ST LO SPR SEP APP (UA & RA & _) (RLO2 & RHI2 & H2a & H2b & H2c & H2d & H2e & H2f & WR2 & RSH2)
    (GOT & RIC & SHB & INI & LAY & REAL) (KLO & RSTK & RI) MI -> -> ->.
  pose proof (proj1 ST) as SP0.
  eapply evtF_mono.
  { eapply (amemset_specZ A n c SPz RNG ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 c) (Z_to_bv 64 n)
              a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo junk RLO2 RHI2);
      first [eassumption | reflexivity | lia | (repeat split; lia)]. }
  intros ms' PO. unfold amemsetZ_post in PO. unfold zd_memsetZ_postA. exact PO.
Qed.

Lemma zd_memcpyZ_proofA : zd_memcpyZ_stmtA.
Proof.
  unfold zd_memcpyZ_stmtA.
  intros RNG A S n SPz ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo src junk.
  intros SS LEN DST SEP1 Hn ST LO SPR SEP2 SEP3 APPS (US & RS & _) (RLO1 & RHI1 & H1a & H1b & H1c & H1d & H1e & H1f & WR1 & RSH1)
    APPD (UD & RD & _) (RLO2 & RHI2 & H2a & H2b & H2c & H2d & H2e & H2f & WR2 & RSH2)
    (GOT & RIC & SHB & INI & LAY & REAL) (KLO & RSTK & RI) MI -> -> ->.
  pose proof (proj1 ST) as SP0.
  eapply evtF_mono.
  { eapply (amemcpy_specZ A S n SPz RNG ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 S) (Z_to_bv 64 n)
              a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo src junk RLO1 RHI1 RLO2 RHI2);
      first [eassumption | reflexivity | lia | (repeat split; lia)]. }
  intros ms' PO. unfold amemcpyZ_post in PO. unfold zd_memcpyZ_postA. exact PO.
Qed.
End CANSEC1.
