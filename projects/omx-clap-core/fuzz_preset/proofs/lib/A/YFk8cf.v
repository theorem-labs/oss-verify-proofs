(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YFk8cf.v (commit eb934de95d13, blob a3f862021602) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 53 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (3 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFhy AFhz YFkpcf YFk6cf.
Import ListNotations. Open Scope Z_scope.
Definition runtoC (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL pc ss).
Definition setpc (ss : sstate) (pc : Z) : sstate := mkSS pc (ss_regs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition ENOMEM_RET : Z := 18446744073709551604.
Definition EEXIST_RET : Z := 18446744073709551599.
Definition A_RESTORE_SPIN : Z := 0x6f33c.
Definition hJ0 : nat := aHAV3.
Definition CLOB_INIT : list (bv 5) := [5; 6; 7; 13; 15; 16; 17; 28; 29; 30]%bv.
Definition R3_J : sstate := Eval vm_compute in noconds (forget (runto 0x373c8 SS0R3) hJ0 CLOB_INIT).
Definition R3_10 : sstate := Eval vm_compute in runto 0x373cc R3_J.
Definition R3_1 : sstate := Eval vm_compute in pin R3_10 9%bv (SOff rN 0).
Definition R3_A0 : sstate := Eval vm_compute in runto 0x37528 R3_1.
Definition R3_A : sstate := Eval vm_compute in pin (pin R3_A0 8%bv (SOff rRG 0)) 20%bv (SOff rFA 0).
Definition R3_B : sstate := Eval vm_compute in runto 0x375fc R3_A.
Definition R3_P0 : sstate := Eval vm_compute in runto 0x377e8 (arm BC_LTU true (SOff rNF 0) (SOff rN 0) R3_B).
Definition R3_P : sstate := Eval vm_compute in pin R3_P0 14%bv (SOff rNEED 0).
Definition pin3 (ss : sstate) : sstate := pin (pin (pin ss 21%bv (SOff rCSZ 0)) 19%bv (SOff rTOT 0)) 18%bv (SOff rRB 0).
Definition R3_Q31a : sstate := Eval vm_compute in runto 0x37a04 (arm BC_EQ true (SOff rCL 0) (SLit 31) R3_P).
Definition R3_Q31 : sstate := Eval vm_compute in pin3 R3_Q31a.
Definition R3_Pn31 : sstate := Eval vm_compute in runto 0x377f0 (arm BC_EQ false (SOff rCL 0) (SLit 31) R3_P).
Definition R3_Q16a : sstate := Eval vm_compute in runto 0x3780c (arm BC_LTU false (SLit 16) (SOff rCL 0) R3_Pn31).
Definition R3_Q16 : sstate := Eval vm_compute in pin3 R3_Q16a.
Definition R3_Qmida : sstate := Eval vm_compute in runto 0x3784c (arm BC_LTU true (SLit 16) (SOff rCL 0) R3_Pn31).
Definition R3_Qmid : sstate := Eval vm_compute in pin3 R3_Qmida.
Definition hJ1 : nat := 106.
Definition CLOB_J1 : list (bv 5) := [15; 16]%bv.
Definition R3_M : sstate := Eval vm_compute in noconds (forget (runto 0x37850 (arm BC_LTU true (SOff rMU 0) (SOff rTOT 0) R3_Q31)) hJ1 CLOB_J1).
Definition R3_Ke : sstate := Eval vm_compute in noconds (forget (runto 0x37924 (arm BC_LTU false (SOff rMU 0) (SOff rTOT 0) R3_Q31)) hJ1 CLOB_J1).
Lemma R3_M_16 : noconds (forget (runto 0x37850 (arm BC_LTU true (SOff rMU 0) (SOff rTOT 0) R3_Q16)) hJ1 CLOB_J1) = R3_M.
Proof. vm_compute. reflexivity. Qed.
Lemma R3_M_mid : noconds (forget (runto 0x37850 (arm BC_GEU false (SOff rMU 0) (SOff rTOT 0) R3_Qmid)) hJ1 CLOB_J1) = R3_M.
Proof. vm_compute. reflexivity. Qed.
Lemma R3_Ke_16 : noconds (forget (runto 0x37924 (arm BC_LTU false (SOff rMU 0) (SOff rTOT 0) R3_Q16)) hJ1 CLOB_J1) = R3_Ke.
Proof. vm_compute. reflexivity. Qed.
Lemma R3_Ke_mid : noconds (forget (runto 0x37924 (arm BC_GEU true (SOff rMU 0) (SOff rTOT 0) R3_Qmid)) hJ1 CLOB_J1) = R3_Ke.
Proof. vm_compute. reflexivity. Qed.
Definition hJ2 : nat := 108.
Definition R3_M2 : sstate := Eval vm_compute in noconds (forget (runto 0x37854 (arm BC_EQ false (SOff rMU 0) (SLit 0) R3_M)) hJ2 [11]%bv).
Definition R3_M2z : sstate := Eval vm_compute in runto 0x37854 (arm BC_EQ true (SOff rMU 0) (SLit 0) R3_M).
Lemma R3_M2_z : noconds (forget (pin R3_M2z 20%bv (SOff rMU 0)) hJ2 [11]%bv) = R3_M2.
Proof. vm_compute. reflexivity. Qed.
Definition R3_M3 : sstate := Eval vm_compute in pin (runto 0x37870 R3_M2) 19%bv (SLit 262144).
Definition R3_M4 : sstate := Eval vm_compute in runto 0x37884 R3_M3.
Definition R3_M5a : sstate := Eval vm_compute in runto 0x6f208 (arm BC_GEU false (SOff rMU 262144) (SLit 3758096385) R3_M4).
Definition R3_M5 : sstate := Eval vm_compute in pin (pin R3_M5a 11%bv (SOff rADR 0)) 20%bv (SOff rADR 0).
Definition R3_NU : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_M5.
Definition R3_NUr : sstate := Eval vm_compute in setpc (pin R3_NU 10%bv (SLit ENOMEM_RET)) 0x652c0.
Definition R3_NUg : sstate := Eval vm_compute in setpc (pin R3_NU 10%bv (SOff rADR 0)) 0x652c0.
Definition R3_NR : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NUr.
Definition R3_NRe : sstate := Eval vm_compute in setpc (pin R3_NR 10%bv (SLit ENOMEM_RET)) 0x652c0.
Definition R3_NRx : sstate := Eval vm_compute in setpc (pin R3_NR 10%bv (SLit EEXIST_RET)) 0x652c0.
Definition R3_NRg : sstate := Eval vm_compute in setpc (pin R3_NR 10%bv (SOff rADR 0)) 0x652c0.
Definition R3_SPe : sstate := Eval vm_compute in runtoC A_RESTORE_SPIN R3_NRe.
Definition R3_SPx : sstate := Eval vm_compute in runtoC A_RESTORE_SPIN R3_NRx.
Definition R3_F1 : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NRg.
Definition R3_FRET : sstate := Eval vm_compute in runto 0x7ffffff0 R3_F1.
Definition R3_G1 : sstate := Eval vm_compute in runtoC 0x7ffffff0 R3_NUg.
Definition R3_G2 : sstate := Eval vm_compute in runto 0x7ffffff0 R3_G1.
Definition R3_MSU : sstate := Eval vm_compute in pin (pin R3_G2 10%bv (SOff rSHA 0)) 12%bv (SLit 32768).
Definition hMSU : nat := 109.
Definition CLOB_MS : list (bv 5) := [11; 12; 13; 14; 15; 16]%bv.
Definition R3_G3 : sstate := Eval vm_compute in ss_after_stretch R3_MSU (ss_mem R3_MSU) hMSU CLOB_MS 0x378ec.
Definition R3_Kg : sstate := Eval vm_compute in runto 0x37924 R3_G3.
Lemma seg3a_stops :
ss_pc R3_10 = 0x373cc /\ sr_get (ss_regs R3_10) 9%bv = SAluw ALU_SRL (SOff rMAX 0) (SLit 1) /\
ss_pc R3_A0 = 0x37528 /\
sr_get (ss_regs R3_A0) 8%bv = SAlu ALU_ADD (SOff rSB 137438953472) (SAlu ALU_SLL (SOff rCL 0) (SLit 7)) /\
sr_get (ss_regs R3_A0) 20%bv = SAlu ALU_ADD (SOff rSB 3758096384) (SAlu ALU_SLL (SOff rCL 0) (SLit 32)) /\
ss_pc R3_B = 0x375fc /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 R3_A) = RS_stopped (SR_branch BC_LTU (SOff rNF 0) (SOff rN 0)) /\
ss_pc R3_P0 = 0x377e8 /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 (arm BC_LTU true (SOff rNF 0) (SOff rN 0) R3_B)) = RS_stopped (SR_branch BC_EQ (SOff rCL 0) (SLit 31)) /\
sr_get (ss_regs R3_P0) 14%bv = SAlu ALU_ADD (SOff rN 0) (SMd M_MUL (SOff rNF 0) (SLit (-1))) /\
ss_pc R3_Q31a = 0x37a04 /\ sr_get (ss_regs R3_Q31a) 21%bv = SLit 64 /\
sr_get (ss_regs R3_Q31a) 19%bv = SAlu ALU_ADD (SOff rAU 0) (SAlu ALU_SLL (SOff rNEED 0) (SLit 6)) /\
sr_get (ss_regs R3_Q31a) 18%bv = SAlu ALU_ADD (SOff rSB 0) (SAlu ALU_SLL (SOff rCL 0) (SLit 32)) /\
ss_pc R3_Pn31 = 0x377f0 /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 (arm BC_EQ false (SOff rCL 0) (SLit 31) R3_P)) = RS_stopped (SR_branch BC_LTU (SLit 16) (SOff rCL 0)) /\
ss_pc R3_Q16a = 0x3780c /\ sr_get (ss_regs R3_Q16a) 21%bv = SAlu ALU_SLL (SOff rCL 0) (SLit 5) /\
ss_pc R3_Qmida = 0x3784c /\
ss_pc R3_M = 0x37850 /\ ss_pc R3_Ke = 0x37924 /\ ss_pc R3_M2 = 0x37854 /\ ss_pc R3_M2z = 0x37854 /\
ss_pc R3_M3 = 0x37870 /\ ss_pc R3_M4 = 0x37884 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 R3_M3) = RS_stopped (SR_branch BC_GEU (SOff rMU 262144) (SLit 3758096385)) /\
ss_pc R3_M5a = 0x6f208 /\ sr_get (ss_regs R3_M5a) 11%bv = SAlu ALU_ADD (SOff rRB 0) (SOff rMU 0) /\ sr_get (ss_regs R3_M5a) 20%bv = SAlu ALU_ADD (SOff rRB 0) (SOff rMU 0) /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 (arm BC_GEU false (SOff rMU 262144) (SLit 3758096385) R3_M4)) = RS_stopped SR_fetch /\
ss_pc R3_NU = 0x652bc /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL 0x7ffffff0 R3_M5) = RS_ecall /\
sr_get (ss_regs R3_NU) 10%bv = SOff rADR 0 /\ sr_get (ss_regs R3_NU) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NU) 12%bv = SLit 3 /\
sr_get (ss_regs R3_NU) 13%bv = SLit 50 /\ sr_get (ss_regs R3_NU) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NU) 15%bv = SLit 0 /\
sr_get (ss_regs R3_NU) 17%bv = SLit 222 /\
ss_pc R3_NR = 0x652bc /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL 0x7ffffff0 R3_NUr) = RS_ecall /\
sr_get (ss_regs R3_NR) 10%bv = SOff rADR 0 /\ sr_get (ss_regs R3_NR) 11%bv = SLit 262144 /\ sr_get (ss_regs R3_NR) 12%bv = SLit 0 /\
sr_get (ss_regs R3_NR) 13%bv = SLit 0x104022 /\ sr_get (ss_regs R3_NR) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs R3_NR) 15%bv = SLit 0 /\
sr_get (ss_regs R3_NR) 17%bv = SLit 222 /\
ss_pc R3_SPe = 0x6f33c /\ ss_pc R3_SPx = 0x6f33c /\
ss_pc R3_F1 = 0x378d0 /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL 0x7ffffff0 R3_NRg) = RS_stopped SR_fetch /\
ss_pc R3_FRET = 0x37400 /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 R3_F1) = RS_stopped (SR_jalr (SOff 1 0)) /\
sr_get (ss_regs R3_FRET) 10%bv = SLit 0 /\ sr_get (ss_regs R3_FRET) 1%bv = SOff 1 0 /\ sr_get (ss_regs R3_FRET) 2%bv = SOff 2 0 /\
ss_pc R3_G1 = 0x378d0 /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL 0x7ffffff0 R3_NUg) = RS_stopped SR_fetch /\
ss_pc R3_G2 = 0x9b6b8 /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 R3_G1) = RS_stopped SR_fetch /\
sr_get (ss_regs R3_G2) 10%bv = SAlu ALU_ADD (SOff rSHB 0) (SAlu ALU_SRL (SOff rADR 0) (SLit 3)) /\
sr_get (ss_regs R3_G2) 11%bv = SLit 250 /\
sr_get (ss_regs R3_G2) 12%bv = SAlu ALU_ADD (SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SOff rADR 262136) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff rADR 0) (SLit 3))) (SLit 0) /\
sr_get (ss_regs R3_G2) 1%bv = SLit 0x378ec /\
ss_pc R3_Kg = 0x37924.
Proof. vm_compute. repeat split; reflexivity. Qed.
