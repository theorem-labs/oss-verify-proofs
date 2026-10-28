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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0m AF0x AFl0 AFhy AFhz AFi0 AFi4 AFi9 AFid AFie AFif AFig AFih.
Import ListNotations. Open Scope Z_scope.
Definition aCAN : nat := 182.
Definition sB1 : nat := 183.
Definition sB2 : nat := 189.
Definition kJB : nat := 195.
Definition R_got : YP09.region := lit8 0x9ec38 0x5f8fd0.
Definition R_can : YP09.region := atom8 0x5f8fd0 aCAN.
Definition R_pgsz : YP09.region := lit8 0x5f9250 4096.
Definition R_sct : YP09.region :=
YP09.mkRegion None 0x214ac (0x214ac + 2) 0 0 [YP09.mkChunk 0x214ac (CVal 2 (SLit 0xff04))].
Definition R_scj : YP09.region := lit4 0x21448 0x6b788.
Definition R_g1 : YP09.region := lit8 0x9dfd8 1.
Definition R_g3 : YP09.region := lit8 0x9dfe0 0x137b1c.
Definition R_g2 : YP09.region := lit4 0x137b1c 0.
Definition R_f1 : YP09.region := lit1 0x137c1c 1.
Definition R_f2 : YP09.region := lit1 0x137c03 1.
Definition BREG : smem := [R_got; R_can; R_pgsz; R_sct; R_scj; R_g1; R_g3; R_g2; R_f1; R_f2].
Lemma can_bytes : exists bs, YP09.img_bytes tfibsegs 0x5f8fd0 8 = Some bs.
Proof. eexists. vm_compute. reflexivity. Qed.
Definition SHBT : sv := SOff aSM 768.
Definition SHET : sv := SOff aPBS 0.
Definition PGBT : sv := SAlu ALU_AND (SOff aSM 4863) (SLit 18446744073709547520).
Definition PGET : sv := SAlu ALU_AND (SOff aPBS 0) (SLit 18446744073709547520).
Definition B_0 : sstate := arm BC_LTU false USH_LEN (SLit 18446744073709551615) T_R.
Definition B_R : sstate := fold_right addreg B_0 BREG.
Definition B_A0 : sstate := Eval vm_compute in runtoD 0x53ad4 B_R.
Definition SHB_X : sv := Eval vm_compute in sr_get (ss_regs B_A0) 10%bv.
Definition SHE_X : sv := Eval vm_compute in sr_get (ss_regs B_A0) 20%bv.
Definition PGB_X : sv := Eval vm_compute in sr_get (ss_regs B_A0) 9%bv.
Definition PGE_X : sv := Eval vm_compute in sr_get (ss_regs B_A0) 18%bv.
Definition B_A : sstate := Eval vm_compute in pin (pin (pin (pin B_A0 10%bv SHBT) 20%bv SHET) 9%bv PGBT) 18%bv PGET.
Definition B_B0 : sstate := Eval vm_compute in runtoD 0x53ad8 (arm BC_GEU false PGBT PGET B_A).
Definition B_M1 : sstate := Eval vm_compute in runtoD 0x97698 (arm BC_EQ false PGBT SHBT B_B0).
Definition B_C : sstate := Eval vm_compute in ss_after_stretch B_M1 (ss_mem B_M1) sB1 CLOB_MS 0x53aec.
Definition B_Ct : sstate := Eval vm_compute in runtoD 0x53b04 (arm BC_EQ true SHET PGET B_C).
Definition B_M2 : sstate := Eval vm_compute in runtoD 0x97698 (arm BC_EQ false SHET PGET B_C).
Definition B_Cf : sstate := Eval vm_compute in ss_after_stretch B_M2 (ss_mem B_M2) sB2 CLOB_MS 0x53b04.
Definition CLOBB : list (bv 5) := [1; 10; 11; 12; 13; 14; 15; 16]%bv.
Definition joinB (ss : sstate) : sstate := noconds (forget ss kJB CLOBB).
Definition B_D : sstate := Eval vm_compute in joinB B_Ct.
Lemma B_Df : joinB B_Cf = B_D. Proof. vm_compute. reflexivity. Qed.
Definition B_E0 : sstate := Eval vm_compute in runtoD 0x6beac B_D.
Definition REM1 : sv := Eval vm_compute in sr_get (ss_regs B_E0) 13%bv.
Definition B_E : sstate := Eval vm_compute in arm BC_NE false REM1 (SLit 0) B_E0.
Definition B_F0 : sstate := Eval vm_compute in runtoD 0x6bebc B_E.
Definition REM2 : sv := Eval vm_compute in sr_get (ss_regs B_F0) 13%bv.
Definition B_F : sstate := Eval vm_compute in arm BC_NE false REM2 (SLit 0) B_F0.
Definition S_K : sstate := Eval vm_compute in runtoD 0x7ffffff0 B_F.
Definition KA0 : sv := Eval vm_compute in sr_get (ss_regs S_K) 10%bv.
Definition KA1 : sv := Eval vm_compute in sr_get (ss_regs S_K) 11%bv.
Definition K_R0 : sstate := resume S_K (SLit ENOMEM_RETv) (ss_mem S_K) (ss_facts S_K).
Definition K_SPIN : sstate := Eval vm_compute in runtoD 0x6deec K_R0.
Definition K_G0 : sstate := resume S_K KA0 (ss_mem S_K) (ss_facts S_K).
Definition B_Q : sstate := Eval vm_compute in runtoD 0x319d8 K_G0.
Definition joinQ (ss : sstate) : sstate := joinQ0 (mkSS (ss_pc ss) (ss_regs ss) (skipn 10 (ss_mem ss)) (ss_resv ss) (ss_facts ss)).
Lemma B_Q_join : joinQ B_Q = U_QJ. Proof. vm_compute. reflexivity. Qed.
Lemma segS6_stops :
ss_pc B_A0 = 0x53ad4 /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtD FUEL 0x7ffffff0 B_A) = RS_stopped (SR_branch BC_GEU PGBT PGET) /\
ss_pc B_B0 = 0x53ad8 /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtD FUEL 0x7ffffff0 B_B0) = RS_stopped (SR_branch BC_EQ PGBT SHBT) /\
ss_pc B_M1 = 0x97698 /\ map (sr_get (ss_regs B_M1)) [1; 10; 11; 12]%bv = [SLit 0x53aec; SHBT; SLit 0; SAlu ALU_SUB PGBT SHBT] /\
ss_pc B_C = 0x53aec /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtD FUEL 0x7ffffff0 B_C) = RS_stopped (SR_branch BC_EQ SHET PGET) /\
ss_pc B_Ct = 0x53b04 /\
ss_pc B_M2 = 0x97698 /\ map (sr_get (ss_regs B_M2)) [1; 10; 11; 12]%bv = [SLit 0x53b04; SAlu ALU_ADD PGET (SLit 0); SLit 0; SAlu ALU_SUB SHET PGET] /\
ss_pc B_E0 = 0x6beac /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtD FUEL 0x7ffffff0 B_E0) = RS_stopped (SR_branch BC_NE REM1 (SLit 0)) /\
ss_pc B_F0 = 0x6bebc /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtD FUEL 0x7ffffff0 B_F0) = RS_stopped (SR_branch BC_NE REM2 (SLit 0)) /\
ss_pc S_K = 0x6416c /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtD FUEL 0x7ffffff0 B_F) = RS_ecall /\ ss_resv S_K = None /\
map (sr_get (ss_regs S_K)) [12; 13; 14; 15; 17]%bv = [SLit 3; SLit 0x4032; SLit 18446744073709551615; SLit 0; SLit 222] /\
ss_pc K_SPIN = 0x6deec /\ ss_pc B_Q = 0x319d8.
Proof. vm_compute. repeat split; reflexivity. Qed.
