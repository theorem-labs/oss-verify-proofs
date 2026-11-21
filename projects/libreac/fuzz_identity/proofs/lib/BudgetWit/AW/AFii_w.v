(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFii.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFii.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w AFhy_w AFhz_w AFi0_w AFi4_w AFi9_w AFid_w AFie_w AFif_w AFig_w AFih_w.
Import ListNotations. Open Scope Z_scope.
Definition aCAN : nat := 182.
Definition sB1 : nat := 183.
Definition sB2 : nat := 189.
Definition kJB : nat := 195.
Definition R_got : YP09.region := lit8 0x9d038 0x5f7f90.
Definition R_can : YP09.region := atom8 0x5f7f90 aCAN.
Definition R_pgsz : YP09.region := lit8 0x5f8210 4096.
Definition R_sct : YP09.region :=
YP09.mkRegion None 0x21d48 (0x21d48 + 2) 0 0 [YP09.mkChunk 0x21d48 (CVal 2 (SLit 0xff04))].
Definition R_scj : YP09.region := lit4 0x21ce4 0x686e4.
Definition R_g1 : YP09.region := lit8 0x9c3f0 1.
Definition R_g3 : YP09.region := lit8 0x9c3f8 0x136adc.
Definition R_g2 : YP09.region := lit4 0x136adc 0.
Definition R_f1 : YP09.region := lit1 0x136bdc 1.
Definition R_f2 : YP09.region := lit1 0x136bc3 1.
Definition BREG : smem := [R_got; R_can; R_pgsz; R_sct; R_scj; R_g1; R_g3; R_g2; R_f1; R_f2].
Lemma can_bytes : exists bs, YP09.img_bytes tfibsegs 0x5f7f90 8 = Some bs.
Proof. eexists. vm_compute. reflexivity. Qed.
Definition SHBT : sv := SOff aSM 768.
Definition SHET : sv := SOff aPBS 0.
Definition PGBT : sv := SAlu ALU_AND (SOff aSM 4863) (SLit 18446744073709547520).
Definition PGET : sv := SAlu ALU_AND (SOff aPBS 0) (SLit 18446744073709547520).
Definition B_0 : sstate := arm BC_LTU false USH_LEN (SLit 18446744073709551615) T_R.
Definition B_R : sstate := fold_right addreg B_0 BREG.
Definition B_A0 : sstate := Eval vm_compute in runtoD 0x53d50 B_R.
Definition SHB_X : sv := Eval vm_compute in sr_get (ss_regs B_A0) 10%bv.
Definition SHE_X : sv := Eval vm_compute in sr_get (ss_regs B_A0) 20%bv.
Definition PGB_X : sv := Eval vm_compute in sr_get (ss_regs B_A0) 9%bv.
Definition PGE_X : sv := Eval vm_compute in sr_get (ss_regs B_A0) 18%bv.
Definition B_A : sstate := Eval vm_compute in pin (pin (pin (pin B_A0 10%bv SHBT) 20%bv SHET) 9%bv PGBT) 18%bv PGET.
Definition B_B0 : sstate := Eval vm_compute in runtoD 0x53d54 (arm BC_GEU false PGBT PGET B_A).
Definition B_M1 : sstate := Eval vm_compute in runtoD 0x94a18 (arm BC_EQ false PGBT SHBT B_B0).
Definition B_C : sstate := Eval vm_compute in ss_after_stretch B_M1 (ss_mem B_M1) sB1 CLOB_MS 0x53d68.
Definition B_Ct : sstate := Eval vm_compute in runtoD 0x53d80 (arm BC_EQ true SHET PGET B_C).
Definition B_M2 : sstate := Eval vm_compute in runtoD 0x94a18 (arm BC_EQ false SHET PGET B_C).
Definition B_Cf : sstate := Eval vm_compute in ss_after_stretch B_M2 (ss_mem B_M2) sB2 CLOB_MS 0x53d80.
Definition CLOBB : list (bv 5) := [1; 10; 11; 12; 13; 14; 15; 16]%bv.
Definition joinB (ss : sstate) : sstate := noconds (forget ss kJB CLOBB).
Definition B_D : sstate := Eval vm_compute in joinB B_Ct.
Definition B_E0 : sstate := Eval vm_compute in runtoD 0x6c128 B_D.
Definition REM1 : sv := Eval vm_compute in sr_get (ss_regs B_E0) 13%bv.
Definition B_E : sstate := Eval vm_compute in arm BC_NE false REM1 (SLit 0) B_E0.
Definition B_F0 : sstate := Eval vm_compute in runtoD 0x6c138 B_E.
Definition REM2 : sv := Eval vm_compute in sr_get (ss_regs B_F0) 13%bv.
Definition B_F : sstate := Eval vm_compute in arm BC_NE false REM2 (SLit 0) B_F0.
Definition S_K : sstate := Eval vm_compute in runtoD 0x7ffffff0 B_F.
Definition KA0 : sv := Eval vm_compute in sr_get (ss_regs S_K) 10%bv.
Definition KA1 : sv := Eval vm_compute in sr_get (ss_regs S_K) 11%bv.
Definition K_G0 : sstate := resume S_K KA0 (ss_mem S_K) (ss_facts S_K).
Definition B_Q : sstate := Eval vm_compute in runtoD 0x320b4 K_G0.
