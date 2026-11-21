(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFi2.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFi2.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhy_w AFi1_w AFhz_w AFi0_w.
Import ListNotations. Open Scope Z_scope.
Definition KS_U : sstate := Eval vm_compute in runto 0x5a600 SS0K.
Definition rs_Uk : smem := match ss_mem KS_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 47) | [] => [] end.
Definition KS_1 : sstate := Eval vm_compute in addreg R_bst (addreg R_scr1 (ss_after_call KS_U rs_Uk hU1 0x52ea4)).
Definition KS_A : sstate := Eval vm_compute in runto 0x31da8 KS_1.
Definition KS_Ab : sstate := Eval vm_compute in runto 0x31dd4 (arm BC_LTU true (SLit 8) (SOff 10 0) KS_A).
Definition KS_B : sstate := Eval vm_compute in noconds (pin (pin KS_Ab 10%bv (SOff aR8 0)) 11%bv (SLit 0)).
Definition KS_B1 : sstate := Eval vm_compute in runto 0x31df0 KS_B.
Definition KS_B2 : sstate := Eval vm_compute in pin KS_B1 9%bv (SOff aNP 0).
Definition KS_C0 : sstate := Eval vm_compute in runto 0x360b8 KS_B2.
Definition KS_C : sstate := Eval vm_compute in arm BC_GEU true (SAlu ALU_XOR (SOff aR8 16) (SLit (-1))) (SLit 8) KS_C0.
Definition KS_E0 : sstate := Eval vm_compute in runto 0x36224 KS_C.
Definition KS_E : sstate := Eval vm_compute in noconds (pin KS_E0 8%bv (SOff aCL 0)).
Definition KS_F0 : sstate := Eval vm_compute in runto 0x3623c KS_E.
Definition KS_F : sstate := Eval vm_compute in pin KS_F0 9%bv (SOff aP 0).
Definition KS_JN : sstate := Eval vm_compute in noconds (forget (runto 0x36244 KS_F) hJN CLOBJ).
Definition KS_G0 : sstate := Eval vm_compute in runto 0x36264 KS_JN.
Definition KS_G : sstate := Eval vm_compute in pin KS_G0 14%bv (SOff aPV (-16)).
Definition KS_H0 : sstate := Eval vm_compute in runto 0x31e9c KS_G.
Definition KS_H : sstate := Eval vm_compute in pin KS_H0 10%bv (SOff aK 0).
Definition KS_J0 : sstate := Eval vm_compute in runto 0x31ec0 KS_H.
Definition KS_J : sstate := Eval vm_compute in
arm BC_LTU false (SAlu ALU_ADD (SOff aR8 16) (SOff aK 0)) (SAlu ALU_ADD (SOff aK 16) (SOff aNP 0)) KS_J0.
Definition KS_K0 : sstate := Eval vm_compute in runto 0x31ee8 KS_J.
Definition KS_K : sstate := Eval vm_compute in arm BC_NE false (SAlu ALU_SRL (SOff 10 0) (SLit 48)) (SLit 0) KS_K0.
Definition KS_PD : sstate := Eval vm_compute in runto 0x7272c KS_K.
Definition hJ : nat := 139.
Definition rs_Dk : smem := match ss_mem KS_PD with r0 :: r1 :: rest => r0 :: trim_lo r1 (-2272) :: rest | l => l end.
Definition KS_2 : sstate := Eval vm_compute in addreg R_scr2 (ss_after_call KS_PD rs_Dk hD1 0x31fa8).
Definition KS_M0 : sstate := Eval vm_compute in runto 0x31fd0 KS_2.
Definition KS_M : sstate := Eval vm_compute in pin KS_M0 10%bv (SOff aSK 0).
Definition KS_N0 : sstate := Eval vm_compute in runto 0x320a0 KS_M.
Definition KS_N : sstate := Eval vm_compute in pin KS_N0 22%bv (SOff aN8D 0).
Definition KS_Nz : sstate := Eval vm_compute in runto 0x320b4 (arm BC_EQ true (SOff aN8D 0) (SLit 0) KS_N).
Definition CLOB_J : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28]%bv.
Definition clr0 (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (R_scr2 :: tl (ss_mem ss)) (ss_resv ss) (ss_facts ss).
Definition KS_Q : sstate := Eval vm_compute in noconds (forget (clr0 KS_Nz) hJ CLOB_J).
Definition KS_Qe : sstate := Eval vm_compute in arm BC_EQ true (SOff aNP 0) (SOff aN8D 0) KS_Q.
Definition KS_Qo : sstate := Eval vm_compute in arm BC_EQ false (SOff aNP 0) (SOff aN8D 0) KS_Q.
Definition KS_P0 : sstate := Eval vm_compute in runto 0x32144 KS_Qo.
Definition KS_Po : sstate := Eval vm_compute in addreg R_pb (pin KS_P0 10%bv (SOff aPB 0)).
Definition kst_T (ss : sstate) : sstate := pin (runto 0x32294 ss) 10%bv (SOff aSSLOT 0).
Definition KS_Te : sstate := Eval vm_compute in kst_T KS_Qe.
Definition KS_To : sstate := Eval vm_compute in kst_T KS_Po.
Definition SSLOT_term : sv := SAlu ALU_ADD (SOff aT 2912) (SAlu ALU_SLL (SAlu ALU_SRL (SOff aR8 47) (SLit 5)) (SLit 3)).
