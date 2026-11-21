(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathCrc CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkA Require Import CrcAGlue CrcAMirror.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkB Require Import CkBImg CkBTables CkBShadow CkBIface CkBKit CrcBGlue CrcBMirror
  CrcB_zkit CrcB_ztail CrcB_zloop8 CrcB_zlast CrcB_zentry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem crc32_z_proofA : crc32_z_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         Fr fc m lo c A bs MI ST LOS KLO GOT SHB CKSH E0 Hc E1 A1 ALO E2 BUF RI RISH RSTK.
  subst a0 a1 a2. unfold CK_CRC32Z_STACK in *. unfold ACK_CRC32Z.
  assert (TAIL : crcz_tail_stmt RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc m lo A bs)
    by (eapply crcz_tail; eassumption).
  assert (LAST : crcz_last_stmt RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc m lo A bs)
    by (eapply crcz_last; eassumption).
  eapply crcz_main; eassumption.
Qed.

Theorem crc32_z_null_proofA : crc32_z_null_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         Fr fc m lo MI ST LOS KLO E1 RSTK.
  subst a1. unfold CK_CRC32Z_STACK in *. unfold ACK_CRC32Z.
  pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 144%nat ST.
  do 14 zstep.
  zstep. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  zstep. zstep.
  do 15 zstep.
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

Theorem crc32_proofA : crc32_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         Fr fc m lo c A v bs MI ST LOS KLO GOT SHB CKSH E0 Hc E1 A1 ALO E2 Hv Hvl BUF RI RISH RSTK.
  subst a2. unfold ACK_CRC32.
  zstep. zstep. zstep.
  lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => idtac end.
  setreg 12 (Z_to_bv 64 (Z.of_nat (length bs))) ltac:(f_equal; rewrite <- Hvl; first [reflexivity | (rewrite Z.land_ones by lia; reflexivity) | (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; reflexivity)]).
  eapply crc32_z_proofA; try eassumption. reflexivity.
Qed.

Theorem crc32_null_proofA : crc32_null_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         Fr fc m lo MI ST LOS KLO E1 RSTK.
  unfold ACK_CRC32.
  zstep. zstep. zstep.
  eapply crc32_z_null_proofA; eassumption.
Qed.
