(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, with its module paths and module names changed; 59 of its 76 lines of code are new or changed and 305 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the token runs of the DIG
   block of ent_build's case 0 from 0x8140c to 0x81504 (pod.h:238-245: the digits of v into r, the reverse copy into
   ch and its NUL) for v = 0 .. 15, one engine run per value (lib/A/RtPgEnt0DigK.v rt7d_T_stmt, rt7d_T_tac).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps RtPgW7bBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSeg RtPgEnt0Def RtPgEnt0DigK.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

Lemma rt7d_T_0 : rt7d_T_stmt B 0.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_1 : rt7d_T_stmt B 1.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_2 : rt7d_T_stmt B 2.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_3 : rt7d_T_stmt B 3.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_4 : rt7d_T_stmt B 4.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_5 : rt7d_T_stmt B 5.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_6 : rt7d_T_stmt B 6.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_7 : rt7d_T_stmt B 7.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_8 : rt7d_T_stmt B 8.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_9 : rt7d_T_stmt B 9.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_10 : rt7d_T_stmt B 10.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_11 : rt7d_T_stmt B 11.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_12 : rt7d_T_stmt B 12.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_13 : rt7d_T_stmt B 13.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_14 : rt7d_T_stmt B 14.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_15 : rt7d_T_stmt B 15.
Proof. rt7d_T_tac. Qed.

End d.
End b.

Print Assumptions rt7d_T_0.
Print Assumptions rt7d_T_1.
Print Assumptions rt7d_T_2.
Print Assumptions rt7d_T_3.
Print Assumptions rt7d_T_4.
Print Assumptions rt7d_T_5.
Print Assumptions rt7d_T_6.
Print Assumptions rt7d_T_7.
Print Assumptions rt7d_T_8.
Print Assumptions rt7d_T_9.
Print Assumptions rt7d_T_10.
Print Assumptions rt7d_T_11.
Print Assumptions rt7d_T_12.
Print Assumptions rt7d_T_13.
Print Assumptions rt7d_T_14.
Print Assumptions rt7d_T_15.
