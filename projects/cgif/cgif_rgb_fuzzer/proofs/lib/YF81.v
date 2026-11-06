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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3v YF3w YF8g YF7x YF7z YF3i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition REG0U3 {imgk : img} : smem := replAt 35 headc0 REG0R3.
Definition SS0U3 {imgk : img} : sstate := mkSS (0x3670c + D_150) REGS0R REG0U3 None FR3.


Definition R3_U1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36768 + D_150) SS0U3))).
Lemma R3_U1_35 {imgk : img} : nth_error (ss_mem R3_U1) 35 = Some headc0. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition R3_U2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (ss_pc R3_U1) (ss_regs R3_U1) (replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0) (ss_resv R3_U1) (ss_facts R3_U1)))).
Lemma R3_U2_eq {imgk : img} : R3_U2 = mkSS (ss_pc R3_U1) (ss_regs R3_U1) (replAt 35 headcnt (ss_mem R3_U1) ++ TBLS0) (ss_resv R3_U1) (ss_facts R3_U1).
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition R3_U3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36804 + D_150) R3_U2))).
Lemma R3_U3_split {imgk : img} : ss_mem R3_U3 = firstn 41 (ss_mem R3_U3) ++ TBLSF. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.

Lemma R3_U3_ext {imgk : img} : map ext3 (dropAt 35 (firstn 41 (ss_mem R3_U3))) = map ext3 (dropAt 35 REG0R3). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition R3_U4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (ss_pc R3_U3) (ss_regs R3_U3) (replAt 35 headcJ (firstn 41 (ss_mem R3_U3))) (ss_resv R3_U3) (ss_facts R3_U3)))).
Lemma R3_U4_eq {imgk : img} : R3_U4 = mkSS (ss_pc R3_U3) (ss_regs R3_U3) (replAt 35 headcJ (firstn 41 (ss_mem R3_U3))) (ss_resv R3_U3) (ss_facts R3_U3).
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma R3_U4_mem {imgk : img} : ss_mem R3_U4 = insAt 35 headcJ (dropAt 35 (firstn 41 (ss_mem R3_U3))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition R3_U5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x3672c + D_150) R3_U4))).
Lemma R3_UJ {imgk : img} : noconds (forget R3_U5 hJ0 CLOB_INIT) = R3_J. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma R3_U1_ext {imgk : img} : map ext3 (dropAt 35 (ss_mem R3_U1)) = map ext3 (dropAt 35 REG0R3). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma R3_U1_len {imgk : img} : length (ss_mem R3_U1) = 41%nat. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.

Lemma R3_U3_35' {imgk : img} : nth_error (ss_mem R3_U3) 35 = Some headcnt. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma R3_U3_len {imgk : img} : length (firstn 41 (ss_mem R3_U3)) = 41%nat. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.



