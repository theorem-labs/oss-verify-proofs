(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5v YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac regvE HS AGx EEo X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1 :=
lazymatch goal with |- getr _ ?r = _ =>
let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q;
lazymatch goal with
| |- alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (bv_unsigned (ew ?Ex ?n) + ?c)) (Z_to_bv 64 3)) (ew _ 38) = _ =>
unfold w64; apply (shq_word Ex n 38 c _ SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia
| |- context [alu64] => idtac "REGVE-ALU" r; fail
| |- _ =>
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| idtac "REGVE-FAIL" r; fail ]
end end.
Lemma tcgif_vals_set_frames : forall hw s fr,
tcgif_vals hw (set_frames s fr) = frame_ptr (nth 0 fr None) :: frame_ptr (nth 1 fr None) :: frame_ptr (nth 2 fr None) :: skipn 3 (tcgif_vals hw s).
Proof. intros. reflexivity. Qed.
