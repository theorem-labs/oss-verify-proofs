(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, with its module paths and module names changed; 54 of its 77 lines of code are new or changed and 217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0DigT0.v at 21da95a5fcd3; image B's token run 0x81540 .. 0x81608 (lib/AU/RtPgEnt0DigKB.v rt7bd_T_stmt, rt7bd_T_tac) in place of image A's; names rt7d_ -> rt7bd_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0DigT0B.v at cc5ce244897b for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role; role B's token run 0x80cfc .. 0x80dc4 (lib/AU/RPgEnt0DigK.v r7bd_T_stmt, r7bd_T_tac); names rt7bd_ -> r7bd_. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the token runs of the DIG
   block of ent_build's case 0 from 0x80cfc to 0x80dc4 (pod.h:238-245: the digits of v into r, the reverse copy into
   ch and its NUL, with the two UBSan trap tests 0x80cfc and 0x80db4) for v = 0 .. 15, one engine run per value
   (lib/AU/RPgEnt0DigK.v r7bd_T_stmt, r7bd_T_tac). Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgMem RPgSteps RPgSeg RPgEnt0Def.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgEnt0DigK.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
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

Lemma r7bd_T_0 : r7bd_T_stmt B 0.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_1 : r7bd_T_stmt B 1.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_2 : r7bd_T_stmt B 2.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_3 : r7bd_T_stmt B 3.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_4 : r7bd_T_stmt B 4.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_5 : r7bd_T_stmt B 5.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_6 : r7bd_T_stmt B 6.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_7 : r7bd_T_stmt B 7.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_8 : r7bd_T_stmt B 8.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_9 : r7bd_T_stmt B 9.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_10 : r7bd_T_stmt B 10.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_11 : r7bd_T_stmt B 11.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_12 : r7bd_T_stmt B 12.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_13 : r7bd_T_stmt B 13.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_14 : r7bd_T_stmt B 14.
Proof. r7bd_T_tac. Qed.
Lemma r7bd_T_15 : r7bd_T_stmt B 15.
Proof. r7bd_T_tac. Qed.

End d.
End b.

Print Assumptions r7bd_T_0.
Print Assumptions r7bd_T_1.
Print Assumptions r7bd_T_2.
Print Assumptions r7bd_T_3.
Print Assumptions r7bd_T_4.
Print Assumptions r7bd_T_5.
Print Assumptions r7bd_T_6.
Print Assumptions r7bd_T_7.
Print Assumptions r7bd_T_8.
Print Assumptions r7bd_T_9.
Print Assumptions r7bd_T_10.
Print Assumptions r7bd_T_11.
Print Assumptions r7bd_T_12.
Print Assumptions r7bd_T_13.
Print Assumptions r7bd_T_14.
Print Assumptions r7bd_T_15.
