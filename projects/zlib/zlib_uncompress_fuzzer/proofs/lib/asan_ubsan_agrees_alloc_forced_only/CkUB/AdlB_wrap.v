(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkUB Require Import CkBImg CkBTables CkBShadow CkBIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Wrap.
Hypothesis ADLZ : adler32_z_stmtA.
Hypothesis ADLZ0 : adler32_z_null_stmtA.

Lemma adler32_proofA : adler32_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         FR fc m lo adler A v bs MI ST LOS KLO GOT SHB A0 AR A1 A1R ALO A2 VR VL BUF RI RSTK.
  subst a0 a1 a2. unfold ACK_ADLER32.
  zstep. zstep. zstep.
  eapply ADLZ; try eassumption; try reflexivity.
  f_equal. rewrite <- VL. reflexivity.
Qed.

Lemma adler32_null_proofA : adler32_null_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         FR fc m lo MI ST LOS KLO GOT SHB A1 A2 RI RSTK.
  subst a1 a2. unfold ACK_ADLER32.
  zstep. zstep. zstep.
  eapply ADLZ0; try eassumption; reflexivity.
Qed.
End Wrap.
