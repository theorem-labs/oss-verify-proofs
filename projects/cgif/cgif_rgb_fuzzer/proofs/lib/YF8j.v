(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0h YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3v YF3w YF8g YF8i YF3i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition REG0U2 {imgk : img} : smem := replAt 35 headc0 REG0R.
Definition SS0U2 {imgk : img} : sstate := mkSS (0x3670c + D_150) REGS0R REG0U2 None FR.


Definition RU_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36768 + D_150) SS0U2))).
Lemma RU_1_35 {imgk : img} : nth_error (ss_mem RU_1) 35 = Some headc0. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition RU_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (ss_pc RU_1) (ss_regs RU_1) (replAt 35 headcnt (ss_mem RU_1) ++ TBLS0) (ss_resv RU_1) (ss_facts RU_1)))).
Lemma RU_2_eq {imgk : img} : RU_2 = mkSS (ss_pc RU_1) (ss_regs RU_1) (replAt 35 headcnt (ss_mem RU_1) ++ TBLS0) (ss_resv RU_1) (ss_facts RU_1).
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition RU_3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36804 + D_150) RU_2))).
Lemma RU_3_split {imgk : img} : ss_mem RU_3 = firstn 37 (ss_mem RU_3) ++ TBLSF. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.

Lemma RU_3_ext {imgk : img} : map ext3 (dropAt 35 (firstn 37 (ss_mem RU_3))) = map ext3 (dropAt 35 REG0R). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition RU_4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (ss_pc RU_3) (ss_regs RU_3) (replAt 35 headcJ (firstn 37 (ss_mem RU_3))) (ss_resv RU_3) (ss_facts RU_3)))).
Lemma RU_4_eq {imgk : img} : RU_4 = mkSS (ss_pc RU_3) (ss_regs RU_3) (replAt 35 headcJ (firstn 37 (ss_mem RU_3))) (ss_resv RU_3) (ss_facts RU_3).
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma RU_4_mem {imgk : img} : ss_mem RU_4 = insAt 35 headcJ (dropAt 35 (firstn 37 (ss_mem RU_3))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition RU_5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x3672c + D_150) RU_4))).
Lemma RU_J {imgk : img} : noconds (forget RU_5 hJ0 CLOB_INIT) = RJ2. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma RU_1_ext {imgk : img} : map ext3 (dropAt 35 (ss_mem RU_1)) = map ext3 (dropAt 35 REG0R). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma RU_1_len {imgk : img} : length (ss_mem RU_1) = 37%nat. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.

Lemma RU_3_35' {imgk : img} : nth_error (ss_mem RU_3) 35 = Some headcnt. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma RU_3_len {imgk : img} : length (firstn 37 (ss_mem RU_3)) = 37%nat. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.



