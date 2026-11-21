(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFk8.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFk8.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB1q AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhy_w AFhz_w AFkp_w AFk6_w.
Import ListNotations. Open Scope Z_scope.
Definition runtoC (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL pc ss).
Definition setpc (ss : sstate) (pc : Z) : sstate := mkSS pc (ss_regs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition ENOMEM_RET : Z := 18446744073709551604.
Definition hJ0 : nat := aHAV3.
Definition CLOB_INIT : list (bv 5) := [5; 6; 7; 13; 15; 16; 17; 28; 29; 30]%bv.
Definition R3_J : sstate := Eval vm_compute in noconds (forget (runto 0x36800 SS0R3) hJ0 CLOB_INIT).
Definition R3_10 : sstate := Eval vm_compute in runto 0x36804 R3_J.
Definition R3_1 : sstate := Eval vm_compute in pin R3_10 9%bv (SOff rN 0).
Definition R3_A0 : sstate := Eval vm_compute in runto 0x36960 R3_1.
Definition R3_A : sstate := Eval vm_compute in pin (pin R3_A0 8%bv (SOff rRG 0)) 20%bv (SOff rFA 0).
Definition R3_B : sstate := Eval vm_compute in runto 0x36a34 R3_A.
Definition R3_P0 : sstate := Eval vm_compute in runto 0x36c20 (arm BC_LTU true (SOff rNF 0) (SOff rN 0) R3_B).
Definition R3_P : sstate := Eval vm_compute in pin R3_P0 14%bv (SOff rNEED 0).
Definition pin3 (ss : sstate) : sstate := pin (pin (pin ss 21%bv (SOff rCSZ 0)) 19%bv (SOff rTOT 0)) 18%bv (SOff rRB 0).
Definition R3_Q31a : sstate := Eval vm_compute in runto 0x36e3c (arm BC_EQ true (SOff rCL 0) (SLit 31) R3_P).
Definition R3_Q31 : sstate := Eval vm_compute in pin3 R3_Q31a.
Definition R3_Pn31 : sstate := Eval vm_compute in runto 0x36c28 (arm BC_EQ false (SOff rCL 0) (SLit 31) R3_P).
Definition R3_Q16a : sstate := Eval vm_compute in runto 0x36c44 (arm BC_LTU false (SLit 16) (SOff rCL 0) R3_Pn31).
Definition R3_Q16 : sstate := Eval vm_compute in pin3 R3_Q16a.
Definition R3_Qmida : sstate := Eval vm_compute in runto 0x36c84 (arm BC_LTU true (SLit 16) (SOff rCL 0) R3_Pn31).
Definition R3_Qmid : sstate := Eval vm_compute in pin3 R3_Qmida.
Definition hJ1 : nat := 106.
Definition CLOB_J1 : list (bv 5) := [15; 16]%bv.
Definition R3_M : sstate := Eval vm_compute in noconds (forget (runto 0x36c88 (arm BC_LTU true (SOff rMU 0) (SOff rTOT 0) R3_Q31)) hJ1 CLOB_J1).
Definition R3_Ke : sstate := Eval vm_compute in noconds (forget (runto 0x36d5c (arm BC_LTU false (SOff rMU 0) (SOff rTOT 0) R3_Q31)) hJ1 CLOB_J1).
Lemma R3_M_16 : noconds (forget (runto 0x36c88 (arm BC_LTU true (SOff rMU 0) (SOff rTOT 0) R3_Q16)) hJ1 CLOB_J1) = R3_M.
Proof. vm_compute. reflexivity. Qed.
Lemma R3_M_mid : noconds (forget (runto 0x36c88 (arm BC_GEU false (SOff rMU 0) (SOff rTOT 0) R3_Qmid)) hJ1 CLOB_J1) = R3_M.
Proof. vm_compute. reflexivity. Qed.
Lemma R3_Ke_16 : noconds (forget (runto 0x36d5c (arm BC_LTU false (SOff rMU 0) (SOff rTOT 0) R3_Q16)) hJ1 CLOB_J1) = R3_Ke.
Proof. vm_compute. reflexivity. Qed.
Lemma R3_Ke_mid : noconds (forget (runto 0x36d5c (arm BC_GEU true (SOff rMU 0) (SOff rTOT 0) R3_Qmid)) hJ1 CLOB_J1) = R3_Ke.
Proof. vm_compute. reflexivity. Qed.
Definition hJ2 : nat := 108.
Definition R3_M2 : sstate := Eval vm_compute in noconds (forget (runto 0x36c8c (arm BC_EQ false (SOff rMU 0) (SLit 0) R3_M)) hJ2 [11]%bv).
Definition R3_M2z : sstate := Eval vm_compute in runto 0x36c8c (arm BC_EQ true (SOff rMU 0) (SLit 0) R3_M).
Lemma R3_M2_z : noconds (forget (pin R3_M2z 20%bv (SOff rMU 0)) hJ2 [11]%bv) = R3_M2.
Proof. vm_compute. reflexivity. Qed.
Definition R3_M3 : sstate := Eval vm_compute in pin (runto 0x36ca8 R3_M2) 19%bv (SLit 262144).
Definition R3_M4 : sstate := Eval vm_compute in runto 0x36cbc R3_M3.
Definition R3_M5a : sstate := Eval vm_compute in runto 0x6e334 (arm BC_GEU false (SOff rMU 262144) (SLit 3758096385) R3_M4).
Definition R3_M5 : sstate := Eval vm_compute in pin (pin R3_M5a 11%bv (SOff rADR 0)) 20%bv (SOff rADR 0).
Definition R3_NU : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_M5.
Definition R3_NUr : sstate := Eval vm_compute in setpc (pin R3_NU 10%bv (SLit ENOMEM_RET)) 0x643ec.
Definition R3_NUg : sstate := Eval vm_compute in setpc (pin R3_NU 10%bv (SOff rADR 0)) 0x643ec.
Definition R3_NR : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NUr.
Definition R3_NRg : sstate := Eval vm_compute in setpc (pin R3_NR 10%bv (SOff rADR 0)) 0x643ec.
Definition R3_F1 : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NRg.
Definition R3_FRET : sstate := Eval vm_compute in runto 0x7ffffff0 R3_F1.
Definition R3_G1 : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NUg.
Definition R3_G2 : sstate := Eval vm_compute in runto 0x7ffffff0 R3_G1.
Definition R3_MSU : sstate := Eval vm_compute in pin (pin R3_G2 10%bv (SOff rSHA 0)) 12%bv (SLit 32768).
Definition hMSU : nat := 109.
Definition CLOB_MS : list (bv 5) := [11; 12; 13; 14; 15; 16]%bv.
Definition R3_G3 : sstate := Eval vm_compute in ss_after_stretch R3_MSU (ss_mem R3_MSU) hMSU CLOB_MS 0x36d24.
Definition R3_Kg : sstate := Eval vm_compute in runto 0x36d5c R3_G3.
