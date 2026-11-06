(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module paths and module names changed; 59 of its 78 lines of code are new or changed and 307 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0DigT2.v at 21da95a5fcd3; image B's token run 0x81540 .. 0x81608 (lib/AU/RtPgEnt0DigKB.v rt7bd_T_stmt, rt7bd_T_tac) in place of image A's; names rt7d_ -> rt7bd_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the token runs of the DIG
   block of ent_build's case 0 from 0x81540 to 0x81608 (pod.h:238-245: the digits of v into r, the reverse copy into
   ch and its NUL, with the two UBSan trap tests 0x81540 and 0x815f8) for v = 32 .. 47, one engine run per value
   (lib/AU/RtPgEnt0DigKB.v rt7bd_T_stmt, rt7bd_T_tac). Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgStepsB RtPgSegB RtPgEnt0DefB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgEnt0DigKB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

Lemma rt7bd_T_32 : rt7bd_T_stmt B 32.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_33 : rt7bd_T_stmt B 33.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_34 : rt7bd_T_stmt B 34.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_35 : rt7bd_T_stmt B 35.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_36 : rt7bd_T_stmt B 36.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_37 : rt7bd_T_stmt B 37.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_38 : rt7bd_T_stmt B 38.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_39 : rt7bd_T_stmt B 39.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_40 : rt7bd_T_stmt B 40.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_41 : rt7bd_T_stmt B 41.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_42 : rt7bd_T_stmt B 42.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_43 : rt7bd_T_stmt B 43.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_44 : rt7bd_T_stmt B 44.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_45 : rt7bd_T_stmt B 45.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_46 : rt7bd_T_stmt B 46.
Proof. rt7bd_T_tac. Qed.
Lemma rt7bd_T_47 : rt7bd_T_stmt B 47.
Proof. rt7bd_T_tac. Qed.

End d.
End b.

Print Assumptions rt7bd_T_32.
Print Assumptions rt7bd_T_33.
Print Assumptions rt7bd_T_34.
Print Assumptions rt7bd_T_35.
Print Assumptions rt7bd_T_36.
Print Assumptions rt7bd_T_37.
Print Assumptions rt7bd_T_38.
Print Assumptions rt7bd_T_39.
Print Assumptions rt7bd_T_40.
Print Assumptions rt7bd_T_41.
Print Assumptions rt7bd_T_42.
Print Assumptions rt7bd_T_43.
Print Assumptions rt7bd_T_44.
Print Assumptions rt7bd_T_45.
Print Assumptions rt7bd_T_46.
Print Assumptions rt7bd_T_47.
