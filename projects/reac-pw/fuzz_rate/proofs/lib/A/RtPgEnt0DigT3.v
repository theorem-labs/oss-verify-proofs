(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, with its module paths and module names changed; 59 of its 76 lines of code are new or changed and 305 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the token runs of the DIG
   block of ent_build's case 0 from 0x8140c to 0x81504 (pod.h:238-245: the digits of v into r, the reverse copy into
   ch and its NUL) for v = 48 .. 63, one engine run per value (lib/A/RtPgEnt0DigK.v rt7d_T_stmt, rt7d_T_tac).
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

Lemma rt7d_T_48 : rt7d_T_stmt B 48.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_49 : rt7d_T_stmt B 49.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_50 : rt7d_T_stmt B 50.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_51 : rt7d_T_stmt B 51.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_52 : rt7d_T_stmt B 52.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_53 : rt7d_T_stmt B 53.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_54 : rt7d_T_stmt B 54.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_55 : rt7d_T_stmt B 55.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_56 : rt7d_T_stmt B 56.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_57 : rt7d_T_stmt B 57.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_58 : rt7d_T_stmt B 58.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_59 : rt7d_T_stmt B 59.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_60 : rt7d_T_stmt B 60.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_61 : rt7d_T_stmt B 61.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_62 : rt7d_T_stmt B 62.
Proof. rt7d_T_tac. Qed.
Lemma rt7d_T_63 : rt7d_T_stmt B 63.
Proof. rt7d_T_tac. Qed.

End d.
End b.

Print Assumptions rt7d_T_48.
Print Assumptions rt7d_T_49.
Print Assumptions rt7d_T_50.
Print Assumptions rt7d_T_51.
Print Assumptions rt7d_T_52.
Print Assumptions rt7d_T_53.
Print Assumptions rt7d_T_54.
Print Assumptions rt7d_T_55.
Print Assumptions rt7d_T_56.
Print Assumptions rt7d_T_57.
Print Assumptions rt7d_T_58.
Print Assumptions rt7d_T_59.
Print Assumptions rt7d_T_60.
Print Assumptions rt7d_T_61.
Print Assumptions rt7d_T_62.
Print Assumptions rt7d_T_63.
