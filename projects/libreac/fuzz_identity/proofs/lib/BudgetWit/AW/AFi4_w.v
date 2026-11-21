(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFi4.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFi4.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w AFhy_w AFhz_w AFi1_w AFi2_w AFhm_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YFen.
Import ListNotations. Open Scope Z_scope.
Definition bare (r : YP09.region) : YP09.region := YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 [].
Definition MTAIL0 : smem :=
[ bare (nth 38 REG0 R_bst); nth 39 REG0 R_bst; bare (nth 40 REG0 R_bst); bare (nth 41 REG0 R_bst);
YP09.mkRegion (Some aP) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 0))] ] ++ map bare (skipn 43 REG0).
Definition MREG0 : smem := Eval vm_compute in firstn 38 REG0 ++ MTAIL0.
Lemma MREG0_skel : map ext3 MREG0 = map ext3 REG0. Proof. vm_compute. reflexivity. Qed.
Definition MS0 : sstate := mkSS 0x52bac (sr_set sr_atoms 4%bv (SLit TFIB_TP)) MREG0 None FG.
Definition MS_U : sstate := Eval vm_compute in runto 0x5a600 MS0.
Definition mrs_U : smem := match ss_mem MS_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 48) | [] => [] end.
Definition MS_1 : sstate := Eval vm_compute in addreg R_bst (addreg R_scr1 (ss_after_call MS_U mrs_U hU1 0x52ea4)).
Definition MS_A : sstate := Eval vm_compute in runto 0x31d00 MS_1.
Definition MS_A1 : sstate := Eval vm_compute in runto 0x31d6c (arm BC_GEU false (SOff 10 0) (SLit 97) MS_A).
Definition MS_L : sstate := Eval vm_compute in noconds (pin MS_A1 19%bv (SOff aKL 0)).
Definition MS_B0 : sstate := Eval vm_compute in runto 0x31dd4 MS_L.
Definition MS_B : sstate := Eval vm_compute in pin (pin MS_B0 10%bv (SOff aR8 0)) 11%bv (SLit 0).
Definition MS_B1 : sstate := Eval vm_compute in runto 0x31de8 MS_B.
Definition MS_B2 : sstate := Eval vm_compute in pin MS_B1 20%bv (SOff aRZ 0).
Definition MS_B3 : sstate := Eval vm_compute in runto 0x31df8 MS_B2.
Definition MS_B4 : sstate := Eval vm_compute in pin MS_B3 19%bv (SOff aND 0).
Definition MS_C0 : sstate := Eval vm_compute in runto 0x360b8 MS_B4.
Definition MS_C : sstate := Eval vm_compute in arm BC_GEU true (SAlu ALU_XOR (SOff aND 0) (SLit (-1))) (SLit 8) MS_C0.
Definition MS_D : sstate := Eval vm_compute in runto 0x36114 MS_C.
Definition MS_Dlo : sstate := Eval vm_compute in runto 0x36224 (arm BC_LTU false (SLit 512) (SOff aND 0) MS_D).
Definition MS_E : sstate := Eval vm_compute in noconds (pin (forget MS_Dlo hCL CLOB_CL) 8%bv (SOff aCL 0)).
Definition MS_F0 : sstate := Eval vm_compute in runto 0x3623c MS_E.
Definition MS_F : sstate := Eval vm_compute in pin MS_F0 9%bv (SOff aP 0).
Definition MS_CALL : sstate := Eval vm_compute in runto 0x367e0 MS_F.
Definition hRF : nat := 87.
Definition H518 : sstate := Eval vm_compute in runto 0x36244 SS_F.
Definition MS_AC : sstate := Eval vm_compute in ss_after_call MS_CALL (ss_mem MS_CALL) hRF 0x36340.
Definition MS_AFTER : sstate := Eval vm_compute in
mkSS 0x36340 (sr_set (ss_regs MS_AC) 10%bv (SLit 1)) (firstn 3 (ss_mem MS_AC) ++ skipn 3 (ss_mem H518)) None (ss_facts MS_AC).
Definition DUMMY : list nat := [37; 41; 42; 44; 45; 46; 48; 49; 50; 51; 53; 54; 59; 60; 61]%nat.
Definition PND (n : nat) : bool := negb (natin DUMMY n).
Definition R3bst : YP09.region := Eval vm_compute in nth 0 (ss_mem MS_CALL) R_bst.
Definition R3scr : YP09.region := Eval vm_compute in nth 1 (ss_mem MS_CALL) R_bst.
Definition R3top : YP09.region := Eval vm_compute in nth 2 (ss_mem MS_CALL) R_bst.
Definition RS3 : smem := Eval vm_compute in [R3bst; trim_lo R3scr (-2320); R3top].
Definition SS3 : sstate := Eval vm_compute in ss_after_call MS_CALL RS3 hRF 0x36340.
Lemma SS3_eq : SS3 = ss_after_call MS_CALL RS3 hRF 0x36340. Proof. vm_compute. reflexivity. Qed.
Lemma MS_CALL_mem3 : exists rest, ss_mem MS_CALL = R3bst :: R3scr :: R3top :: rest. Proof. eexists. vm_compute. reflexivity. Qed.
Lemma MS_AFTER_eq3 : MS_AFTER = mkSS 0x36340 (sr_set (ss_regs SS3) 10%bv (SLit 1)) ([R3bst; R3scr; R3top] ++ tl REG0) None (ss_facts SS3).
Proof. vm_compute. reflexivity. Qed.
Lemma SS3_atoms : regs_atoms_in PND (ss_regs SS3) = true /\ mem_atoms_in PND (ss_mem SS3) = true /\ conds_atoms_in PND (ss_facts SS3) = true /\
ss_resv SS3 = None /\ f_atoms (ss_facts SS3) = f_atoms FG.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma MS_CALL_facts : ss_atoms_lt hRF MS_CALL = true /\ regions_wf RS3 = true /\ no_cdata RS3 = true /\ mem_atoms_lt hRF RS3 = true /\
sr_get (ss_regs MS_CALL) 1%bv = SLit 0x36340 /\ ss_resv MS_CALL = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma tlREG0_facts : mem_atoms_lt 64 (tl REG0) = true /\ regions_wf (tl REG0) = true /\ forallb (fun p => Nat.ltb (fst p) 64) (f_atoms FG) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition oomR : YP09.region := YP09.mkRegion None TFIB_OOM (TFIB_OOM + 1) TFIB_OOM (TFIB_OOM + 1) [].
Definition errR : YP09.region := YP09.mkRegion None TFIB_ERRNO (TFIB_ERRNO + 4) TFIB_ERRNO (TFIB_ERRNO + 4) [].
Definition NREGS : smem := [lit1 (TFIB_OOM + 1) 1; oomR; errR].
Definition MS_N0 : sstate := Eval vm_compute in mkSS 0x36340 (sr_set (ss_regs SS3) 10%bv (SLit 0)) ([R3bst; R3scr; R3top] ++ NREGS) None (ss_facts SS3).
Lemma MS_N0_eq : MS_N0 = mkSS 0x36340 (sr_set (ss_regs SS3) 10%bv (SLit 0)) ([R3bst; R3scr; R3top] ++ NREGS) None (ss_facts SS3).
Proof. vm_compute. reflexivity. Qed.
Definition MKTAIL0 : smem :=
[ bare (nth 38 REG0K R_bst); nth 39 REG0K R_bst; bare (nth 40 REG0K R_bst); bare (nth 41 REG0K R_bst);
YP09.mkRegion (Some aP) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 0))] ] ++ map bare (skipn 43 REG0K).
Definition MKREG0 : smem := Eval vm_compute in firstn 38 REG0K ++ MKTAIL0.
Lemma MKREG0_skel : map ext3 MKREG0 = map ext3 REG0K. Proof. vm_compute. reflexivity. Qed.
Definition MK0 : sstate := mkSS 0x52bac (sr_set sr_atoms 4%bv (SLit TFIB_TP)) MKREG0 None FK.
Definition MK_U : sstate := Eval vm_compute in runto 0x5a600 MK0.
Definition mkrs_U : smem := match ss_mem MK_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 47) | [] => [] end.
Definition MK_1 : sstate := Eval vm_compute in addreg R_bst (addreg R_scr1 (ss_after_call MK_U mkrs_U hU1 0x52ea4)).
Definition MK_A : sstate := Eval vm_compute in runto 0x31da8 MK_1.
Definition MK_Ab : sstate := Eval vm_compute in runto 0x31dd4 (arm BC_LTU true (SLit 8) (SOff 10 0) MK_A).
Definition MK_B : sstate := Eval vm_compute in noconds (pin (pin MK_Ab 10%bv (SOff aR8 0)) 11%bv (SLit 0)).
Definition MK_B1 : sstate := Eval vm_compute in runto 0x31df0 MK_B.
Definition MK_B2 : sstate := Eval vm_compute in pin MK_B1 9%bv (SOff aNP 0).
Definition MK_C0 : sstate := Eval vm_compute in runto 0x360b8 MK_B2.
Definition MK_C : sstate := Eval vm_compute in arm BC_GEU true (SAlu ALU_XOR (SOff aR8 16) (SLit (-1))) (SLit 8) MK_C0.
Definition MK_E0 : sstate := Eval vm_compute in runto 0x36224 MK_C.
Definition MK_E : sstate := Eval vm_compute in noconds (pin MK_E0 8%bv (SOff aCL 0)).
Definition MK_F0 : sstate := Eval vm_compute in runto 0x3623c MK_E.
Definition MK_F : sstate := Eval vm_compute in pin MK_F0 9%bv (SOff aP 0).
Definition MK_CALL : sstate := Eval vm_compute in runto 0x367e0 MK_F.
Definition hRFk : nat := 80.
Definition K518 : sstate := Eval vm_compute in runto 0x36244 KS_F.
Definition MK_AC : sstate := Eval vm_compute in ss_after_call MK_CALL (ss_mem MK_CALL) hRFk 0x36340.
Definition MK_AFTER : sstate := Eval vm_compute in
mkSS 0x36340 (sr_set (ss_regs MK_AC) 10%bv (SLit 1)) (firstn 3 (ss_mem MK_AC) ++ skipn 3 (ss_mem K518)) None (ss_facts MK_AC).
Definition K3bst : YP09.region := Eval vm_compute in nth 0 (ss_mem MK_CALL) R_bst.
Definition K3scr : YP09.region := Eval vm_compute in nth 1 (ss_mem MK_CALL) R_bst.
Definition K3top : YP09.region := Eval vm_compute in nth 2 (ss_mem MK_CALL) R_bst.
Definition RSK3 : smem := Eval vm_compute in [K3bst; trim_lo K3scr (-2320); K3top].
Definition SSK3 : sstate := Eval vm_compute in ss_after_call MK_CALL RSK3 hRFk 0x36340.
Lemma SSK3_eq : SSK3 = ss_after_call MK_CALL RSK3 hRFk 0x36340. Proof. vm_compute. reflexivity. Qed.
Lemma MK_CALL_mem3 : exists rest, ss_mem MK_CALL = K3bst :: K3scr :: K3top :: rest. Proof. eexists. vm_compute. reflexivity. Qed.
Lemma MK_AFTER_eq3 : MK_AFTER = mkSS 0x36340 (sr_set (ss_regs SSK3) 10%bv (SLit 1)) ([K3bst; K3scr; K3top] ++ tl REG0K) None (ss_facts SSK3).
Proof. vm_compute. reflexivity. Qed.
Lemma SSK3_atoms : regs_atoms_in PND (ss_regs SSK3) = true /\ mem_atoms_in PND (ss_mem SSK3) = true /\ conds_atoms_in PND (ss_facts SSK3) = true /\
ss_resv SSK3 = None /\ f_atoms (ss_facts SSK3) = f_atoms FK.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma MK_CALL_facts : ss_atoms_lt hRFk MK_CALL = true /\ regions_wf RSK3 = true /\ no_cdata RSK3 = true /\ mem_atoms_lt hRFk RSK3 = true /\
sr_get (ss_regs MK_CALL) 1%bv = SLit 0x36340 /\ ss_resv MK_CALL = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma tlREG0K_facts : mem_atoms_lt 64 (tl REG0K) = true /\ regions_wf (tl REG0K) = true /\ forallb (fun p => Nat.ltb (fst p) 64) (f_atoms FK) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition MK_N0 : sstate := Eval vm_compute in mkSS 0x36340 (sr_set (ss_regs SSK3) 10%bv (SLit 0)) ([K3bst; K3scr; K3top] ++ NREGS) None (ss_facts SSK3).
Lemma MK_N0_eq : MK_N0 = mkSS 0x36340 (sr_set (ss_regs SSK3) 10%bv (SLit 0)) ([K3bst; K3scr; K3top] ++ NREGS) None (ss_facts SSK3).
Proof. vm_compute. reflexivity. Qed.
