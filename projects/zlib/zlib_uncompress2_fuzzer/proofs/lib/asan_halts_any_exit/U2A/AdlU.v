(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AObj AdlUIface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.CkU Require CkAImg CkAShadow CkAIface AdlA_wrap AdlA_z.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

Theorem adler32_U : adler32_stmtU.
Proof.
  pose proof (AdlA_wrap.adler32_proofA AdlA_z.adler32_z_proofA) as H. unfold CkAIface.adler32_stmtA in H.
  unfold adler32_stmtU. intros until bs. intros MI ST LOS KH GOT SHB A0 AR A1 A1R AL A2 VR VM BUF BR UNP RA RSH RI RSTK.
  eapply evtF_mono.
  - eapply (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m lo adler A v bs);
      try eassumption.
    unfold CkAShadow.ck_buf. split; [exact BUF|]. split; [exact BR|]. split; [exact UNP|]. split; [exact RA| exact RSH].
  - cbv beta. unfold CkAIface.ck_postA, adl_postU. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & ST').
    eexists _, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'| exact ST'].
Qed.

Theorem adler32_null_U : adler32_null_stmtU.
Proof.
  pose proof (AdlA_wrap.adler32_null_proofA AdlA_z.adler32_z_null_proofA) as H. unfold CkAIface.adler32_null_stmtA in H.
  unfold adler32_null_stmtU. intros until lo. intros MI ST LOS KH GOT SHB A1 A2 RI RSTK.
  eapply evtF_mono.
  - eapply (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m lo); try eassumption.
  - cbv beta. unfold CkAIface.ck_postA. intros ms' X. exact X.
Qed.
End CANSEC1.
