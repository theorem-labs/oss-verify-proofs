(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YK05 YA0i YA0l YA0m YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0h YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition runto {imgk : img} (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfxsegs tfxtbl_rtA FUEL pc ss).
Definition pin (ss : sstate) (r : bv 5) (e : sv) : sstate := mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition forget (ss : sstate) (k : nat) (clob : list (bv 5)) : sstate := ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss).
Definition addreg (r : YQ0b.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition noconds (ss : sstate) : sstate := YQ04.prune ss [] [].
Definition arm (c : branch_cond) (taken : bool) (a b : sv) (ss : sstate) : sstate := add_cond ss (mkAC (if taken then c else neg_bc c) a b).
Definition hU1 : nat := 64.
Definition hCL : nat := 80.
Definition hJN : nat := 103.
Definition hD1 : nat := 117.
Definition SS_U {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5aea0 + D_2c4) SS0))).
Definition R_scr1 : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [].
Definition R_bst : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) (- 2128) (- 2112) 0 0 [YQ0b.mkChunk (- 2128) (CVal 8 (SOff 2 (- 2112))); YQ0b.mkChunk (- 2120) (CVal 8 (SOff aLEN 0))].
Definition rs_U {imgk : img} : smem := match ss_mem SS_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 48) | [] => [] end.
Definition SS_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_bst (addreg R_scr1 (ss_after_call SS_U rs_U hU1 (0x53400 + D_2c4)))))).
Definition SS_A {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a20 + D_150) SS_1))).
Definition SS_A1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) (arm BC_GEU false (SOff 10 0) (SLit 97) SS_A)))).
Definition SS_A2' {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a30 + D_150) (arm BC_GEU true (SOff 10 0) (SLit 97) SS_A)))).
Definition SS_A2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) (arm BC_GEU false (SOff 10 0) (SLit 449) SS_A2')))).
Definition SS_A3' {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a44 + D_150) (arm BC_GEU true (SOff 10 0) (SLit 449) SS_A2')))).
Definition SS_A3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) (arm BC_GEU false (SOff 10 0) (SLit 3969) SS_A3')))).
Definition SS_A4' {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a58 + D_150) (arm BC_GEU true (SOff 10 0) (SLit 3969) SS_A3')))).
Definition SS_A4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) (arm BC_GEU false (SOff 10 0) (SLit 16129) SS_A4')))).
Definition SS_A5' {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a6c + D_150) (arm BC_GEU true (SOff 10 0) (SLit 16129) SS_A4')))).
Definition SS_A5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) (arm BC_GEU false (SOff 10 0) (SLit 32257) SS_A5')))).
Definition SS_A6' {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a80 + D_150) (arm BC_GEU true (SOff 10 0) (SLit 32257) SS_A5')))).
Definition SS_A6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) SS_A6'))).
Definition SS_L {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (pin SS_A1 19%bv (SOff aKL 0))))).





Definition SS_B0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31af4 + D_150) SS_L))).
Definition SS_B {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin SS_B0 10%bv (SOff aR8 0)) 11%bv (SLit 0)))).
Definition SS_B1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31b08 + D_150) SS_B))).
Definition SS_B2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin SS_B1 20%bv (SOff aRZ 0)))).
Definition SS_B3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31b18 + D_150) SS_B2))).
Definition SS_B4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin SS_B3 19%bv (SOff aND 0)))).
Definition SS_C0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x35fe4 + D_150) SS_B4))).
Definition SS_C {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_GEU true (SAlu ALU_XOR (SOff aND 0) (SLit (-1))) (SLit 8) SS_C0))).
Definition SS_D {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36040 + D_150) SS_C))).
Definition SS_Dlo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36150 + D_150) (arm BC_LTU false (SLit 512) (SOff aND 0) SS_D)))).
Definition SS_Dhi {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36150 + D_150) (arm BC_LTU true (SLit 512) (SOff aND 0) SS_D)))).
Definition CL_lo : sv := ltac:(img_eval_free (fun imgk : img => (sr_get (ss_regs SS_Dlo) 8%bv))).
Definition CL_hi : sv := ltac:(img_eval_free (fun imgk : img => (sr_get (ss_regs SS_Dhi) 8%bv))).
Definition CLOB_CL : list (bv 5) := [5; 6; 12; 14; 15; 16; 17]%bv.
Definition SS_E {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (pin (forget SS_Dlo hCL CLOB_CL) 8%bv (SOff aCL 0))))).

Definition SS_F0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36168 + D_150) SS_E))).
Definition SS_F {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin SS_F0 9%bv (SOff aP 0)))).
Definition CLOBJ : list (bv 5) := [1; 5; 6; 7; 14; 15; 16; 17; 19; 20; 28; 29; 30; 31]%bv.
Definition SS_JN {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget (runto (0x36170 + D_150) SS_F) hJN CLOBJ)))).
Definition SS_G0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36190 + D_150) SS_JN))).
Definition SS_G {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin SS_G0 14%bv (SOff aPV (-16))))).
Definition SS_H0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31bbc + D_150) SS_G))).
Definition SS_H {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin SS_H0 10%bv (SOff aK 0)))).
Definition SS_I0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31bc8 + D_150) SS_H))).
Definition SS_I {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin SS_I0 20%bv (SOff aU 0)))).
Definition SS_J0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31be0 + D_150) SS_I))).
Definition SS_J {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_LTU false (SAlu ALU_ADD (SOff aK 0) (SOff aND 0)) (SAlu ALU_ADD (SOff 10 0) (SOff aU 0)) SS_J0))).
Definition SS_K0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31c08 + D_150) SS_J))).
Definition SS_K {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_NE false (SAlu ALU_SRL (SOff 10 0) (SLit 48)) (SLit 0) SS_K0))).
Definition SS_PD {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x72fcc + D_2c4) SS_K))).
Lemma seg1_stops {imgk : img} :
snd (sym_run_toN_sh tfxsegs tfxtbl_rtA FUEL 0x7ffffff0 SS_1) = RS_stopped (SR_branch BC_GEU (SOff 10 0) (SLit 97)) /\
ss_pc SS_B0 = (0x31af4 + D_150) /\ ss_pc SS_B1 = (0x31b08 + D_150) /\ ss_pc SS_B3 = (0x31b18 + D_150) /\ ss_pc SS_C0 = (0x35fe4 + D_150) /\ ss_pc SS_D = (0x36040 + D_150) /\
ss_pc SS_Dlo = (0x36150 + D_150) /\ ss_pc SS_Dhi = (0x36150 + D_150) /\ ss_pc SS_F0 = (0x36168 + D_150) /\ ss_pc SS_JN = (0x36170 + D_150) /\ ss_pc SS_G0 = (0x36190 + D_150) /\ ss_pc SS_H0 = (0x31bbc + D_150) /\
ss_pc SS_I0 = (0x31bc8 + D_150) /\ ss_pc SS_J0 = (0x31be0 + D_150) /\ ss_pc SS_K0 = (0x31c08 + D_150) /\ ss_pc SS_PD = (0x72fcc + D_2c4) /\
sr_get (ss_regs SS_B0) 10%bv = SAlu ALU_ADD (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) (SLit 0) /\
sr_get (ss_regs SS_B1) 20%bv = SAluw ALU_SLL (SLit 16) (SOff aKL 0) /\
sr_get (ss_regs SS_B3) 19%bv = SAlu ALU_ADD (SOff aR8 0) (SOff aRZ 0) /\
CL_lo = SAlu ALU_SRL (SOff aND 31) (SLit 5) /\ svpure CL_hi = true /\ sv_only aND CL_hi = true /\
sr_get (ss_regs SS_I0) 20%bv = SAlu ALU_ADD (SOff aK 0) (SOff aRZ 0) /\
sr_get (ss_regs SS_PD) 1%bv = SLit (0x31cc8 + D_150) /\ sr_get (ss_regs SS_PD) 10%bv = SOff 2 (-2112) /\ sr_get (ss_regs SS_PD) 11%bv = SOff aLEN 0.
Proof. img_case; vm_compute. all: repeat split; img_refl. Qed.
