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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_libc_iface I_asan_memmove.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

Lemma zd_memmoveZ_proofA : zd_memmoveZ_stmtA.
Proof.
  unfold zd_memmoveZ_stmtA.
  intros RNG D S n SPz ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  intros SD SS Hn ST LO SPR SEPS SEPD APPS (US & RS & _) (RLO1 & RHI1 & H1a & H1b & H1c & H1d & H1e & H1f & WR1 & RSH1)
    APPD (UD & RD & _) (RLO2 & RHI2 & H2a & H2b & H2c & H2d & H2e & H2f & WR2 & RSH2)
    (GOT & RIC & SHB & INI & LAY & REAL) (KLO & RSTK & RI) MI -> -> ->.
  pose proof (proj1 ST) as SP0.
  assert (ESP : bv_unsigned (Z_to_bv 64 SPz) = SPz) by (apply unsigned_lit; lia).
  assert (AKS : 0 <= S /\ S + n + 8 <= KEND) by (destruct APPS as (_ & [(? & ?)|(? & ?)]); unfold KLOW, KHIGH, KEND in *; lia).
  assert (AKD : 0 <= D /\ D + n + 8 <= KEND) by (destruct APPD as (_ & [(? & ?)|(? & ?)]); unfold KLOW, KHIGH, KEND in *; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; unfold KEND in *; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; unfold KEND in *; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).

  eapply evtF_mono.
  { eapply (asan_memmove_spec RNG ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)
              a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo RLO1 RHI1 RLO2 RHI2);
      rewrite ?ED, ?ES, ?En, ?ESP; first [eassumption | lia | (repeat split; lia)]. }
  intros ms' PO. unfold asan_memmove_post in PO. rewrite ED, En, ESP in PO.
  unfold zd_memmoveZ_postA. exact PO.
Qed.
End CANSEC1.
