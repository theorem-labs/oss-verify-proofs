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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3v YF3w YF8g YF7x.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition runtoC {imgk : img} (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfxsegs tfxtbl_rtC FUEL pc ss).
Definition setpc (ss : sstate) (pc : Z) : sstate := mkSS pc (ss_regs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition ENOMEM_RET : Z := 18446744073709551604.
Definition EEXIST_RET : Z := 18446744073709551599.
Definition A_RESTORE_SPIN {imgk : img} : Z := (0x6ed08 + D_2c4).
Definition hJ0 : nat := aHAV3.
Definition CLOB_INIT : list (bv 5) := [5; 6; 7; 13; 15; 16; 17; 28; 29; 30]%bv.
Definition R3_J {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget (runto (0x3672c + D_150) SS0R3) hJ0 CLOB_INIT)))).
Definition R3_10 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36730 + D_150) R3_J))).
Definition R3_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin R3_10 9%bv (SOff rN 0)))).
Definition R3_A0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x3688c + D_150) R3_1))).
Definition R3_A {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin R3_A0 8%bv (SOff rRG 0)) 20%bv (SOff rFA 0)))).
Definition R3_B {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36960 + D_150) R3_A))).
Definition R3_P0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36b4c + D_150) (arm BC_LTU true (SOff rNF 0) (SOff rN 0) R3_B)))).
Definition R3_P {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin R3_P0 14%bv (SOff rNEED 0)))).
Definition pin3 (ss : sstate) : sstate := pin (pin (pin ss 21%bv (SOff rCSZ 0)) 19%bv (SOff rTOT 0)) 18%bv (SOff rRB 0).
Definition R3_Q31a {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36d68 + D_150) (arm BC_EQ true (SOff rCL 0) (SLit 31) R3_P)))).
Definition R3_Q31 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin3 R3_Q31a))).
Definition R3_Pn31 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36b54 + D_150) (arm BC_EQ false (SOff rCL 0) (SLit 31) R3_P)))).
Definition R3_Q16a {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36b70 + D_150) (arm BC_LTU false (SLit 16) (SOff rCL 0) R3_Pn31)))).
Definition R3_Q16 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin3 R3_Q16a))).
Definition R3_Qmida {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36bb0 + D_150) (arm BC_LTU true (SLit 16) (SOff rCL 0) R3_Pn31)))).
Definition R3_Qmid {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin3 R3_Qmida))).
Definition hJ1 : nat := 106.
Definition CLOB_J1 : list (bv 5) := [15; 16]%bv.
Definition R3_M {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget (runto (0x36bb4 + D_150) (arm BC_LTU true (SOff rMU 0) (SOff rTOT 0) R3_Q31)) hJ1 CLOB_J1)))).
Definition R3_Ke {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget (runto (0x36c88 + D_150) (arm BC_LTU false (SOff rMU 0) (SOff rTOT 0) R3_Q31)) hJ1 CLOB_J1)))).
Lemma R3_M_16 {imgk : img} : noconds (forget (runto (0x36bb4 + D_150) (arm BC_LTU true (SOff rMU 0) (SOff rTOT 0) R3_Q16)) hJ1 CLOB_J1) = R3_M.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma R3_M_mid {imgk : img} : noconds (forget (runto (0x36bb4 + D_150) (arm BC_GEU false (SOff rMU 0) (SOff rTOT 0) R3_Qmid)) hJ1 CLOB_J1) = R3_M.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma R3_Ke_16 {imgk : img} : noconds (forget (runto (0x36c88 + D_150) (arm BC_LTU false (SOff rMU 0) (SOff rTOT 0) R3_Q16)) hJ1 CLOB_J1) = R3_Ke.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma R3_Ke_mid {imgk : img} : noconds (forget (runto (0x36c88 + D_150) (arm BC_GEU true (SOff rMU 0) (SOff rTOT 0) R3_Qmid)) hJ1 CLOB_J1) = R3_Ke.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition hJ2 : nat := 108.
Definition R3_M2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget (runto (0x36bb8 + D_150) (arm BC_EQ false (SOff rMU 0) (SLit 0) R3_M)) hJ2 [11]%bv)))).
Definition R3_M2z {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36bb8 + D_150) (arm BC_EQ true (SOff rMU 0) (SLit 0) R3_M)))).
Lemma R3_M2_z {imgk : img} : noconds (forget (pin R3_M2z 20%bv (SOff rMU 0)) hJ2 [11]%bv) = R3_M2.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition R3_M3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36bd4 + D_150) R3_M2) 19%bv (SLit 262144)))).
Definition R3_M4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36be8 + D_150) R3_M3))).
Definition R3_M5a {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x6ebd4 + D_2c4) (arm BC_GEU false (SOff rMU 262144) (SLit 3758096385) R3_M4)))).
Definition R3_M5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin R3_M5a 11%bv (SOff rADR 0)) 20%bv (SOff rADR 0)))).
Definition R3_NU {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_M5))).
Definition R3_NUr {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NU 10%bv (SLit ENOMEM_RET)) (0x64c8c + D_2c4)))).
Definition R3_NUg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NU 10%bv (SOff rADR 0)) (0x64c8c + D_2c4)))).
Definition R3_NR {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_NUr))).
Definition R3_NRe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NR 10%bv (SLit ENOMEM_RET)) (0x64c8c + D_2c4)))).
Definition R3_NRx {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NR 10%bv (SLit EEXIST_RET)) (0x64c8c + D_2c4)))).
Definition R3_NRg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (setpc (pin R3_NR 10%bv (SOff rADR 0)) (0x64c8c + D_2c4)))).
Definition R3_SPe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC A_RESTORE_SPIN R3_NRe))).
Definition R3_SPx {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC A_RESTORE_SPIN R3_NRx))).
Definition R3_F1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_NRg))).
Definition R3_FRET {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto 0x7ffffff0 R3_F1))).
Definition R3_G1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC 0x7ffffff0 R3_NUg))).
Definition R3_G2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto 0x7ffffff0 R3_G1))).
Definition R3_MSU {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin R3_G2 10%bv (SOff rSHA 0)) 12%bv (SLit 32768)))).
Definition hMSU : nat := 109.
Definition CLOB_MS : list (bv 5) := [11; 12; 13; 14; 15; 16]%bv.
Definition R3_G3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch R3_MSU (ss_mem R3_MSU) hMSU CLOB_MS (0x36c50 + D_150)))).
Definition R3_Kg {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36c88 + D_150) R3_G3))).

