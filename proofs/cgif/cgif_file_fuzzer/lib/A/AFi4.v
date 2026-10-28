(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0f YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0m AF0x AFl0 AFhy AFhz AFi1 AFi2 AFhm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFen.
Import ListNotations. Open Scope Z_scope.
Definition bare (r : YP09.region) : YP09.region := YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 [].
Definition MTAIL0 : smem :=
[ bare (nth 38 REG0 R_bst); nth 39 REG0 R_bst; bare (nth 40 REG0 R_bst); bare (nth 41 REG0 R_bst);
YP09.mkRegion (Some aP) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 0))] ] ++ map bare (skipn 43 REG0).
Definition MREG0 : smem := Eval vm_compute in firstn 38 REG0 ++ MTAIL0.
Lemma MREG0_eq : MREG0 = firstn 38 REG0 ++ MTAIL0. Proof. vm_compute. reflexivity. Qed.
Lemma MREG0_len : length MREG0 = 48%nat. Proof. reflexivity. Qed.
Lemma MREG0_skel : map ext3 MREG0 = map ext3 REG0. Proof. vm_compute. reflexivity. Qed.
Definition MS0 : sstate := mkSS 0x52930 (sr_set sr_atoms 4%bv (SLit TFIB_TP)) MREG0 None FG.
Definition MS_U : sstate := Eval vm_compute in runto 0x5a384 MS0.
Definition mrs_U : smem := match ss_mem MS_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 48) | [] => [] end.
Definition MS_1 : sstate := Eval vm_compute in addreg R_bst (addreg R_scr1 (ss_after_call MS_U mrs_U hU1 0x52c28)).
Definition MS_A : sstate := Eval vm_compute in runto 0x31624 MS_1.
Definition MS_A1 : sstate := Eval vm_compute in runto 0x31690 (arm BC_GEU false (SOff 10 0) (SLit 97) MS_A).
Definition MS_A2' : sstate := Eval vm_compute in runto 0x31634 (arm BC_GEU true (SOff 10 0) (SLit 97) MS_A).
Definition MS_A2 : sstate := Eval vm_compute in runto 0x31690 (arm BC_GEU false (SOff 10 0) (SLit 449) MS_A2').
Definition MS_A3' : sstate := Eval vm_compute in runto 0x31648 (arm BC_GEU true (SOff 10 0) (SLit 449) MS_A2').
Definition MS_A3 : sstate := Eval vm_compute in runto 0x31690 (arm BC_GEU false (SOff 10 0) (SLit 3969) MS_A3').
Definition MS_A4' : sstate := Eval vm_compute in runto 0x3165c (arm BC_GEU true (SOff 10 0) (SLit 3969) MS_A3').
Definition MS_A4 : sstate := Eval vm_compute in runto 0x31690 (arm BC_GEU false (SOff 10 0) (SLit 16129) MS_A4').
Definition MS_A5' : sstate := Eval vm_compute in runto 0x31670 (arm BC_GEU true (SOff 10 0) (SLit 16129) MS_A4').
Definition MS_A5 : sstate := Eval vm_compute in runto 0x31690 (arm BC_GEU false (SOff 10 0) (SLit 32257) MS_A5').
Definition MS_A6' : sstate := Eval vm_compute in runto 0x31684 (arm BC_GEU true (SOff 10 0) (SLit 32257) MS_A5').
Definition MS_A6 : sstate := Eval vm_compute in runto 0x31690 MS_A6'.
Definition MS_L : sstate := Eval vm_compute in noconds (pin MS_A1 19%bv (SOff aKL 0)).
Lemma MS_L_2 : noconds (pin MS_A2 19%bv (SOff aKL 0)) = MS_L. Proof. vm_compute. reflexivity. Qed.
Lemma MS_L_3 : noconds (pin MS_A3 19%bv (SOff aKL 0)) = MS_L. Proof. vm_compute. reflexivity. Qed.
Lemma MS_L_4 : noconds (pin MS_A4 19%bv (SOff aKL 0)) = MS_L. Proof. vm_compute. reflexivity. Qed.
Lemma MS_L_5 : noconds (pin MS_A5 19%bv (SOff aKL 0)) = MS_L. Proof. vm_compute. reflexivity. Qed.
Lemma MS_L_6 : noconds (pin MS_A6 19%bv (SOff aKL 0)) = MS_L. Proof. vm_compute. reflexivity. Qed.
Definition MS_B0 : sstate := Eval vm_compute in runto 0x316f8 MS_L.
Definition MS_B : sstate := Eval vm_compute in pin (pin MS_B0 10%bv (SOff aR8 0)) 11%bv (SLit 0).
Definition MS_B1 : sstate := Eval vm_compute in runto 0x3170c MS_B.
Definition MS_B2 : sstate := Eval vm_compute in pin MS_B1 20%bv (SOff aRZ 0).
Definition MS_B3 : sstate := Eval vm_compute in runto 0x3171c MS_B2.
Definition MS_B4 : sstate := Eval vm_compute in pin MS_B3 19%bv (SOff aND 0).
Definition MS_C0 : sstate := Eval vm_compute in runto 0x359dc MS_B4.
Definition MS_C : sstate := Eval vm_compute in arm BC_GEU true (SAlu ALU_XOR (SOff aND 0) (SLit (-1))) (SLit 8) MS_C0.
Definition MS_D : sstate := Eval vm_compute in runto 0x35a38 MS_C.
Definition MS_Dlo : sstate := Eval vm_compute in runto 0x35b48 (arm BC_LTU false (SLit 512) (SOff aND 0) MS_D).
Definition MS_Dhi : sstate := Eval vm_compute in runto 0x35b48 (arm BC_LTU true (SLit 512) (SOff aND 0) MS_D).
Definition MS_E : sstate := Eval vm_compute in noconds (pin (forget MS_Dlo hCL CLOB_CL) 8%bv (SOff aCL 0)).
Lemma MS_E_hi : noconds (pin (forget MS_Dhi hCL CLOB_CL) 8%bv (SOff aCL 0)) = MS_E. Proof. vm_compute. reflexivity. Qed.
Definition MS_F0 : sstate := Eval vm_compute in runto 0x35b60 MS_E.
Definition MS_F : sstate := Eval vm_compute in pin MS_F0 9%bv (SOff aP 0).
Lemma MS_F_agrees : ss_regs MS_F = ss_regs SS_F /\ ss_facts MS_F = ss_facts SS_F /\ firstn 40 (ss_mem MS_F) = firstn 40 (ss_mem SS_F) /\
skipn 40 (ss_mem MS_F) = MTAIL0 /\ ss_pc MS_F = ss_pc SS_F.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma MS_D_CL : sr_get (ss_regs MS_Dlo) 8%bv = CL_lo /\ sr_get (ss_regs MS_Dhi) 8%bv = CL_hi. Proof. vm_compute. split; reflexivity. Qed.
Definition MS_CALL : sstate := Eval vm_compute in runto 0x36104 MS_F.
Lemma MS_CALL_mem : ss_mem MS_CALL = ss_mem MS_F. Proof. vm_compute. reflexivity. Qed.
Lemma miss_stops :
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 MS_1) = RS_stopped (SR_branch BC_GEU (SOff 10 0) (SLit 97)) /\
ss_pc MS_B0 = 0x316f8 /\ ss_pc MS_B1 = 0x3170c /\ ss_pc MS_B3 = 0x3171c /\ ss_pc MS_C0 = 0x359dc /\ ss_pc MS_D = 0x35a38 /\
ss_pc MS_Dlo = 0x35b48 /\ ss_pc MS_Dhi = 0x35b48 /\ ss_pc MS_F0 = 0x35b60 /\ ss_pc MS_CALL = 0x36104 /\
sr_get (ss_regs MS_CALL) 1%bv = SLit 0x35c64 /\ sr_get (ss_regs MS_CALL) 2%bv = SOff 2 (-2320) /\
sr_get (ss_regs MS_CALL) 10%bv = SOff aT 208 /\ sr_get (ss_regs MS_CALL) 11%bv = SOff aP 0 /\
sr_get (ss_regs MS_CALL) 12%bv = SLit 0xa2998 /\ sr_get (ss_regs MS_CALL) 13%bv = SOff aCL 0 /\
sr_get (ss_regs MS_CALL) 3%bv = SOff 3 0 /\ sr_get (ss_regs MS_CALL) 4%bv = SLit TFIB_TP.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition hRF : nat := 87.
Definition H518 : sstate := Eval vm_compute in runto 0x35b68 SS_F.
Definition MS_AC : sstate := Eval vm_compute in ss_after_call MS_CALL (ss_mem MS_CALL) hRF 0x35c64.
Definition MS_AFTER : sstate := Eval vm_compute in
mkSS 0x35c64 (sr_set (ss_regs MS_AC) 10%bv (SLit 1)) (firstn 3 (ss_mem MS_AC) ++ skipn 3 (ss_mem H518)) None (ss_facts MS_AC).
Lemma MS_AFTER_eq : MS_AFTER = mkSS 0x35c64 (sr_set (ss_regs MS_AC) 10%bv (SLit 1)) (firstn 3 (ss_mem MS_AC) ++ skipn 3 (ss_mem H518)) None (ss_facts MS_AC).
Proof. vm_compute. reflexivity. Qed.
Lemma H518_tail : skipn 3 (ss_mem H518) = tl REG0. Proof. vm_compute. reflexivity. Qed.
Lemma MS_AC_head : firstn 3 (ss_mem MS_AC) = firstn 3 (ss_mem MS_CALL). Proof. vm_compute. reflexivity. Qed.
Lemma MS_JOIN : noconds (forget (runto 0x35b68 MS_AFTER) hJN CLOBJ) = SS_JN. Proof. vm_compute. reflexivity. Qed.
Definition DUMMY : list nat := [37; 41; 42; 44; 45; 46; 48; 49; 50; 51; 53; 54; 59; 60; 61]%nat.
Definition PND (n : nat) : bool := negb (natin DUMMY n).
Definition R3bst : YP09.region := Eval vm_compute in nth 0 (ss_mem MS_CALL) R_bst.
Definition R3scr : YP09.region := Eval vm_compute in nth 1 (ss_mem MS_CALL) R_bst.
Definition R3top : YP09.region := Eval vm_compute in nth 2 (ss_mem MS_CALL) R_bst.
Definition RS3 : smem := Eval vm_compute in [R3bst; trim_lo R3scr (-2320); R3top].
Definition SS3 : sstate := Eval vm_compute in ss_after_call MS_CALL RS3 hRF 0x35c64.
Lemma SS3_eq : SS3 = ss_after_call MS_CALL RS3 hRF 0x35c64. Proof. vm_compute. reflexivity. Qed.
Lemma MS_CALL_mem3 : exists rest, ss_mem MS_CALL = R3bst :: R3scr :: R3top :: rest. Proof. eexists. vm_compute. reflexivity. Qed.
Lemma MS_AFTER_eq3 : MS_AFTER = mkSS 0x35c64 (sr_set (ss_regs SS3) 10%bv (SLit 1)) ([R3bst; R3scr; R3top] ++ tl REG0) None (ss_facts SS3).
Proof. vm_compute. reflexivity. Qed.
Lemma SS3_atoms : regs_atoms_in PND (ss_regs SS3) = true /\ mem_atoms_in PND (ss_mem SS3) = true /\ conds_atoms_in PND (ss_facts SS3) = true /\
ss_resv SS3 = None /\ f_atoms (ss_facts SS3) = f_atoms FG.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma MS_CALL_facts : ss_atoms_lt hRF MS_CALL = true /\ regions_wf RS3 = true /\ no_cdata RS3 = true /\ mem_atoms_lt hRF RS3 = true /\
sr_get (ss_regs MS_CALL) 1%bv = SLit 0x35c64 /\ ss_resv MS_CALL = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma tlREG0_facts : mem_atoms_lt 64 (tl REG0) = true /\ regions_wf (tl REG0) = true /\ forallb (fun p => Nat.ltb (fst p) 64) (f_atoms FG) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition oomR : YP09.region := YP09.mkRegion None TFIB_OOM (TFIB_OOM + 1) TFIB_OOM (TFIB_OOM + 1) [].
Definition errR : YP09.region := YP09.mkRegion None TFIB_ERRNO (TFIB_ERRNO + 4) TFIB_ERRNO (TFIB_ERRNO + 4) [].
Definition NREGS : smem := [lit1 (TFIB_OOM + 1) 1; oomR; errR].
Definition MS_N0 : sstate := Eval vm_compute in mkSS 0x35c64 (sr_set (ss_regs SS3) 10%bv (SLit 0)) ([R3bst; R3scr; R3top] ++ NREGS) None (ss_facts SS3).
Lemma MS_N0_eq : MS_N0 = mkSS 0x35c64 (sr_set (ss_regs SS3) 10%bv (SLit 0)) ([R3bst; R3scr; R3top] ++ NREGS) None (ss_facts SS3).
Proof. vm_compute. reflexivity. Qed.
Definition MS_NR : sstate := Eval vm_compute in runto 0x52c5c MS_N0.
Definition MKTAIL0 : smem :=
[ bare (nth 38 REG0K R_bst); nth 39 REG0K R_bst; bare (nth 40 REG0K R_bst); bare (nth 41 REG0K R_bst);
YP09.mkRegion (Some aP) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 0))] ] ++ map bare (skipn 43 REG0K).
Definition MKREG0 : smem := Eval vm_compute in firstn 38 REG0K ++ MKTAIL0.
Lemma MKREG0_eq : MKREG0 = firstn 38 REG0K ++ MKTAIL0. Proof. vm_compute. reflexivity. Qed.
Lemma MKREG0_len : length MKREG0 = 47%nat. Proof. reflexivity. Qed.
Lemma MKREG0_skel : map ext3 MKREG0 = map ext3 REG0K. Proof. vm_compute. reflexivity. Qed.
Definition MK0 : sstate := mkSS 0x52930 (sr_set sr_atoms 4%bv (SLit TFIB_TP)) MKREG0 None FK.
Definition MK_U : sstate := Eval vm_compute in runto 0x5a384 MK0.
Definition mkrs_U : smem := match ss_mem MK_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 47) | [] => [] end.
Definition MK_1 : sstate := Eval vm_compute in addreg R_bst (addreg R_scr1 (ss_after_call MK_U mkrs_U hU1 0x52c28)).
Definition MK_A : sstate := Eval vm_compute in runto 0x316cc MK_1.
Definition MK_Ab : sstate := Eval vm_compute in runto 0x316f8 (arm BC_LTU true (SLit 8) (SOff 10 0) MK_A).
Definition MK_As : sstate := Eval vm_compute in runto 0x316f8 (arm BC_LTU false (SLit 8) (SOff 10 0) MK_A).
Definition MK_B : sstate := Eval vm_compute in noconds (pin (pin MK_Ab 10%bv (SOff aR8 0)) 11%bv (SLit 0)).
Lemma MK_B_s : noconds (pin (pin MK_As 10%bv (SOff aR8 0)) 11%bv (SLit 0)) = MK_B. Proof. vm_compute. reflexivity. Qed.
Definition MK_B1 : sstate := Eval vm_compute in runto 0x31714 MK_B.
Definition MK_B2 : sstate := Eval vm_compute in pin MK_B1 9%bv (SOff aNP 0).
Definition MK_C0 : sstate := Eval vm_compute in runto 0x359dc MK_B2.
Definition MK_C : sstate := Eval vm_compute in arm BC_GEU true (SAlu ALU_XOR (SOff aR8 16) (SLit (-1))) (SLit 8) MK_C0.
Definition MK_E0 : sstate := Eval vm_compute in runto 0x35b48 MK_C.
Definition MK_E : sstate := Eval vm_compute in noconds (pin MK_E0 8%bv (SOff aCL 0)).
Definition MK_F0 : sstate := Eval vm_compute in runto 0x35b60 MK_E.
Definition MK_F : sstate := Eval vm_compute in pin MK_F0 9%bv (SOff aP 0).
Lemma MK_F_agrees : ss_regs MK_F = ss_regs KS_F /\ ss_facts MK_F = ss_facts KS_F /\ firstn 40 (ss_mem MK_F) = firstn 40 (ss_mem KS_F) /\
skipn 40 (ss_mem MK_F) = MKTAIL0 /\ ss_pc MK_F = ss_pc KS_F.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition MK_CALL : sstate := Eval vm_compute in runto 0x36104 MK_F.
Lemma MK_CALL_mem : ss_mem MK_CALL = ss_mem MK_F. Proof. vm_compute. reflexivity. Qed.
Lemma missk_stops :
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 MK_1) = RS_stopped (SR_branch BC_LTU (SLit 8) (SOff 10 0)) /\
ss_pc MK_A = 0x316cc /\ ss_pc MK_Ab = 0x316f8 /\ ss_pc MK_As = 0x316f8 /\ ss_pc MK_B1 = 0x31714 /\ ss_pc MK_C0 = 0x359dc /\
ss_pc MK_E0 = 0x35b48 /\ ss_pc MK_F0 = 0x35b60 /\ ss_pc MK_CALL = 0x36104 /\
sr_get (ss_regs MK_Ab) 10%bv = SAlu ALU_ADD (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) (SLit 0) /\
sr_get (ss_regs MK_Ab) 11%bv = SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) (SLit 0)) (SLit 7) /\
sr_get (ss_regs MK_As) 10%bv = SLit 8 /\ sr_get (ss_regs MK_As) 11%bv = SLit 0 /\
sr_get (ss_regs MK_B1) 9%bv = SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SOff 10 0) (SLit 1)) /\
sr_get (ss_regs MK_E0) 8%bv = SAlu ALU_SRL (SOff aR8 47) (SLit 5) /\
sr_get (ss_regs MK_F0) 9%bv = SAlu ALU_ADD (SOff aT 208) (SMd M_MUL (SOff aCL 0) (SLit 80)) /\
sr_get (ss_regs MK_CALL) 1%bv = SLit 0x35c64 /\ sr_get (ss_regs MK_CALL) 2%bv = SOff 2 (-2320) /\
sr_get (ss_regs MK_CALL) 10%bv = SOff aT 208 /\ sr_get (ss_regs MK_CALL) 11%bv = SOff aP 0 /\
sr_get (ss_regs MK_CALL) 12%bv = SLit 0xa2998 /\ sr_get (ss_regs MK_CALL) 13%bv = SOff aCL 0 /\
sr_get (ss_regs MK_CALL) 3%bv = SOff 3 0 /\ sr_get (ss_regs MK_CALL) 4%bv = SLit TFIB_TP.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition hRFk : nat := 80.
Definition K518 : sstate := Eval vm_compute in runto 0x35b68 KS_F.
Definition MK_AC : sstate := Eval vm_compute in ss_after_call MK_CALL (ss_mem MK_CALL) hRFk 0x35c64.
Definition MK_AFTER : sstate := Eval vm_compute in
mkSS 0x35c64 (sr_set (ss_regs MK_AC) 10%bv (SLit 1)) (firstn 3 (ss_mem MK_AC) ++ skipn 3 (ss_mem K518)) None (ss_facts MK_AC).
Lemma MK_AFTER_eq : MK_AFTER = mkSS 0x35c64 (sr_set (ss_regs MK_AC) 10%bv (SLit 1)) (firstn 3 (ss_mem MK_AC) ++ skipn 3 (ss_mem K518)) None (ss_facts MK_AC).
Proof. vm_compute. reflexivity. Qed.
Lemma K518_tail : skipn 3 (ss_mem K518) = tl REG0K. Proof. vm_compute. reflexivity. Qed.
Lemma MK_AC_head : firstn 3 (ss_mem MK_AC) = firstn 3 (ss_mem MK_CALL). Proof. vm_compute. reflexivity. Qed.
Lemma MK_JOIN : noconds (forget (runto 0x35b68 MK_AFTER) hJN CLOBJ) = KS_JN. Proof. vm_compute. reflexivity. Qed.
Definition K3bst : YP09.region := Eval vm_compute in nth 0 (ss_mem MK_CALL) R_bst.
Definition K3scr : YP09.region := Eval vm_compute in nth 1 (ss_mem MK_CALL) R_bst.
Definition K3top : YP09.region := Eval vm_compute in nth 2 (ss_mem MK_CALL) R_bst.
Definition RSK3 : smem := Eval vm_compute in [K3bst; trim_lo K3scr (-2320); K3top].
Definition SSK3 : sstate := Eval vm_compute in ss_after_call MK_CALL RSK3 hRFk 0x35c64.
Lemma SSK3_eq : SSK3 = ss_after_call MK_CALL RSK3 hRFk 0x35c64. Proof. vm_compute. reflexivity. Qed.
Lemma MK_CALL_mem3 : exists rest, ss_mem MK_CALL = K3bst :: K3scr :: K3top :: rest. Proof. eexists. vm_compute. reflexivity. Qed.
Lemma MK_AFTER_eq3 : MK_AFTER = mkSS 0x35c64 (sr_set (ss_regs SSK3) 10%bv (SLit 1)) ([K3bst; K3scr; K3top] ++ tl REG0K) None (ss_facts SSK3).
Proof. vm_compute. reflexivity. Qed.
Lemma SSK3_atoms : regs_atoms_in PND (ss_regs SSK3) = true /\ mem_atoms_in PND (ss_mem SSK3) = true /\ conds_atoms_in PND (ss_facts SSK3) = true /\
ss_resv SSK3 = None /\ f_atoms (ss_facts SSK3) = f_atoms FK.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma MK_CALL_facts : ss_atoms_lt hRFk MK_CALL = true /\ regions_wf RSK3 = true /\ no_cdata RSK3 = true /\ mem_atoms_lt hRFk RSK3 = true /\
sr_get (ss_regs MK_CALL) 1%bv = SLit 0x35c64 /\ ss_resv MK_CALL = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma tlREG0K_facts : mem_atoms_lt 64 (tl REG0K) = true /\ regions_wf (tl REG0K) = true /\ forallb (fun p => Nat.ltb (fst p) 64) (f_atoms FK) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition MK_N0 : sstate := Eval vm_compute in mkSS 0x35c64 (sr_set (ss_regs SSK3) 10%bv (SLit 0)) ([K3bst; K3scr; K3top] ++ NREGS) None (ss_facts SSK3).
Lemma MK_N0_eq : MK_N0 = mkSS 0x35c64 (sr_set (ss_regs SSK3) 10%bv (SLit 0)) ([K3bst; K3scr; K3top] ++ NREGS) None (ss_facts SSK3).
Proof. vm_compute. reflexivity. Qed.
Definition MK_NR : sstate := Eval vm_compute in runto 0x52c5c MK_N0.
