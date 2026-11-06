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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF3v YF3w YF3y YF3z YF3i YF0h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition bare (r : YQ0b.region) : YQ0b.region := YQ0b.mkRegion (YQ0b.r_base r) (YQ0b.r_lo r) (YQ0b.r_hi r) 0 0 [].
Definition MTAIL0 {imgk : img} : smem :=
[ bare (nth 38 REG0 R_bst); nth 39 REG0 R_bst; bare (nth 40 REG0 R_bst); bare (nth 41 REG0 R_bst);
YQ0b.mkRegion (Some aP) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SLit 0))] ] ++ map bare (skipn 43 REG0).
Definition MREG0 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (firstn 38 REG0 ++ MTAIL0))).


Lemma MREG0_skel {imgk : img} : map ext3 MREG0 = map ext3 REG0. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition MS0 {imgk : img} : sstate := mkSS (0x53104 + D_2c4) (sr_set sr_atoms 4%bv (SLit TFX_TP)) MREG0 None FG.
Definition MS_U {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5aea0 + D_2c4) MS0))).
Definition mrs_U {imgk : img} : smem := match ss_mem MS_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 48) | [] => [] end.
Definition MS_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_bst (addreg R_scr1 (ss_after_call MS_U mrs_U hU1 (0x53400 + D_2c4)))))).
Definition MS_A {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a20 + D_150) MS_1))).
Definition MS_A1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) (arm BC_GEU false (SOff 10 0) (SLit 97) MS_A)))).
Definition MS_A2' {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a30 + D_150) (arm BC_GEU true (SOff 10 0) (SLit 97) MS_A)))).
Definition MS_A2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) (arm BC_GEU false (SOff 10 0) (SLit 449) MS_A2')))).
Definition MS_A3' {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a44 + D_150) (arm BC_GEU true (SOff 10 0) (SLit 449) MS_A2')))).
Definition MS_A3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) (arm BC_GEU false (SOff 10 0) (SLit 3969) MS_A3')))).
Definition MS_A4' {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a58 + D_150) (arm BC_GEU true (SOff 10 0) (SLit 3969) MS_A3')))).
Definition MS_A4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) (arm BC_GEU false (SOff 10 0) (SLit 16129) MS_A4')))).
Definition MS_A5' {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a6c + D_150) (arm BC_GEU true (SOff 10 0) (SLit 16129) MS_A4')))).
Definition MS_A5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) (arm BC_GEU false (SOff 10 0) (SLit 32257) MS_A5')))).
Definition MS_A6' {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a80 + D_150) (arm BC_GEU true (SOff 10 0) (SLit 32257) MS_A5')))).
Definition MS_A6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31a8c + D_150) MS_A6'))).
Definition MS_L {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (pin MS_A1 19%bv (SOff aKL 0))))).





Definition MS_B0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31af4 + D_150) MS_L))).
Definition MS_B {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin MS_B0 10%bv (SOff aR8 0)) 11%bv (SLit 0)))).
Definition MS_B1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31b08 + D_150) MS_B))).
Definition MS_B2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin MS_B1 20%bv (SOff aRZ 0)))).
Definition MS_B3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31b18 + D_150) MS_B2))).
Definition MS_B4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin MS_B3 19%bv (SOff aND 0)))).
Definition MS_C0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x35fe4 + D_150) MS_B4))).
Definition MS_C {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_GEU true (SAlu ALU_XOR (SOff aND 0) (SLit (-1))) (SLit 8) MS_C0))).
Definition MS_D {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36040 + D_150) MS_C))).
Definition MS_Dlo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36150 + D_150) (arm BC_LTU false (SLit 512) (SOff aND 0) MS_D)))).
Definition MS_Dhi {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36150 + D_150) (arm BC_LTU true (SLit 512) (SOff aND 0) MS_D)))).
Definition MS_E {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (pin (forget MS_Dlo hCL CLOB_CL) 8%bv (SOff aCL 0))))).

Definition MS_F0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36168 + D_150) MS_E))).
Definition MS_F {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin MS_F0 9%bv (SOff aP 0)))).


Definition MS_CALL {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x3670c + D_150) MS_F))).


Definition hRF : nat := 87.
Definition H518 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36170 + D_150) SS_F))).
Definition MS_AC {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_call MS_CALL (ss_mem MS_CALL) hRF (0x3626c + D_150)))).
Definition MS_AFTER {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (0x3626c + D_150) (sr_set (ss_regs MS_AC) 10%bv (SLit 1)) (firstn 3 (ss_mem MS_AC) ++ skipn 3 (ss_mem H518)) None (ss_facts MS_AC)))).




Definition DUMMY : list nat := [37; 41; 42; 44; 45; 46; 48; 49; 50; 51; 53; 54; 59; 60; 61]%nat.
Definition PND (n : nat) : bool := negb (natin DUMMY n).
Definition R3bst {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (nth 0 (ss_mem MS_CALL) R_bst))).
Definition R3scr {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (nth 1 (ss_mem MS_CALL) R_bst))).
Definition R3top {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (nth 2 (ss_mem MS_CALL) R_bst))).
Definition RS3 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => ([R3bst; trim_lo R3scr (-2320); R3top]))).
Definition SS3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_call MS_CALL RS3 hRF (0x3626c + D_150)))).
Lemma SS3_eq {imgk : img} : SS3 = ss_after_call MS_CALL RS3 hRF (0x3626c + D_150). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma MS_CALL_mem3 {imgk : img} : exists rest, ss_mem MS_CALL = R3bst :: R3scr :: R3top :: rest. Proof. img_eexists_vm. Qed.
Lemma MS_AFTER_eq3 {imgk : img} : MS_AFTER = mkSS (0x3626c + D_150) (sr_set (ss_regs SS3) 10%bv (SLit 1)) ([R3bst; R3scr; R3top] ++ tl REG0) None (ss_facts SS3).
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma SS3_atoms {imgk : img} : regs_atoms_in PND (ss_regs SS3) = true /\ mem_atoms_in PND (ss_mem SS3) = true /\ conds_atoms_in PND (ss_facts SS3) = true /\
ss_resv SS3 = None /\ f_atoms (ss_facts SS3) = f_atoms FG.
Proof. img_case; vm_compute. all: repeat split; img_refl. Qed.
Lemma MS_CALL_facts {imgk : img} : ss_atoms_lt hRF MS_CALL = true /\ regions_wf RS3 = true /\ no_cdata RS3 = true /\ mem_atoms_lt hRF RS3 = true /\
sr_get (ss_regs MS_CALL) 1%bv = SLit (0x3626c + D_150) /\ ss_resv MS_CALL = None.
Proof. img_case; vm_compute. all: repeat split; img_refl. Qed.
Lemma tlREG0_facts {imgk : img} : mem_atoms_lt 64 (tl REG0) = true /\ regions_wf (tl REG0) = true /\ forallb (fun p => Nat.ltb (fst p) 64) (f_atoms FG) = true.
Proof. img_case; vm_compute. all: repeat split; img_refl. Qed.
Definition oomR {imgk : img} : YQ0b.region := YQ0b.mkRegion None TFX_OOM (TFX_OOM + 1) TFX_OOM (TFX_OOM + 1) [].
Definition errR {imgk : img} : YQ0b.region := YQ0b.mkRegion None TFX_ERRNO (TFX_ERRNO + 4) TFX_ERRNO (TFX_ERRNO + 4) [].
Definition NREGS {imgk : img} : smem := [lit1 (TFX_OOM + 1) 1; oomR; errR].
Definition MS_N0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (0x3626c + D_150) (sr_set (ss_regs SS3) 10%bv (SLit 0)) ([R3bst; R3scr; R3top] ++ NREGS) None (ss_facts SS3)))).
Lemma MS_N0_eq {imgk : img} : MS_N0 = mkSS (0x3626c + D_150) (sr_set (ss_regs SS3) 10%bv (SLit 0)) ([R3bst; R3scr; R3top] ++ NREGS) None (ss_facts SS3).
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition MS_NR {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x53434 + D_2c4) MS_N0))).
Definition MKTAIL0 {imgk : img} : smem :=
[ bare (nth 38 REG0K R_bst); nth 39 REG0K R_bst; bare (nth 40 REG0K R_bst); bare (nth 41 REG0K R_bst);
YQ0b.mkRegion (Some aP) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SLit 0))] ] ++ map bare (skipn 43 REG0K).
Definition MKREG0 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (firstn 38 REG0K ++ MKTAIL0))).


Lemma MKREG0_skel {imgk : img} : map ext3 MKREG0 = map ext3 REG0K. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition MK0 {imgk : img} : sstate := mkSS (0x53104 + D_2c4) (sr_set sr_atoms 4%bv (SLit TFX_TP)) MKREG0 None FK.
Definition MK_U {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5aea0 + D_2c4) MK0))).
Definition mkrs_U {imgk : img} : smem := match ss_mem MK_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 47) | [] => [] end.
Definition MK_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_bst (addreg R_scr1 (ss_after_call MK_U mkrs_U hU1 (0x53400 + D_2c4)))))).
Definition MK_A {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31ac8 + D_150) MK_1))).
Definition MK_Ab {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31af4 + D_150) (arm BC_LTU true (SLit 8) (SOff 10 0) MK_A)))).
Definition MK_As {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31af4 + D_150) (arm BC_LTU false (SLit 8) (SOff 10 0) MK_A)))).
Definition MK_B {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (pin (pin MK_Ab 10%bv (SOff aR8 0)) 11%bv (SLit 0))))).

Definition MK_B1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31b10 + D_150) MK_B))).
Definition MK_B2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin MK_B1 9%bv (SOff aNP 0)))).
Definition MK_C0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x35fe4 + D_150) MK_B2))).
Definition MK_C {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_GEU true (SAlu ALU_XOR (SOff aR8 16) (SLit (-1))) (SLit 8) MK_C0))).
Definition MK_E0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36150 + D_150) MK_C))).
Definition MK_E {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (pin MK_E0 8%bv (SOff aCL 0))))).
Definition MK_F0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36168 + D_150) MK_E))).
Definition MK_F {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin MK_F0 9%bv (SOff aP 0)))).

Definition MK_CALL {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x3670c + D_150) MK_F))).


Definition hRFk : nat := 80.
Definition K518 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36170 + D_150) KS_F))).
Definition MK_AC {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_call MK_CALL (ss_mem MK_CALL) hRFk (0x3626c + D_150)))).
Definition MK_AFTER {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (0x3626c + D_150) (sr_set (ss_regs MK_AC) 10%bv (SLit 1)) (firstn 3 (ss_mem MK_AC) ++ skipn 3 (ss_mem K518)) None (ss_facts MK_AC)))).




Definition K3bst {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (nth 0 (ss_mem MK_CALL) R_bst))).
Definition K3scr {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (nth 1 (ss_mem MK_CALL) R_bst))).
Definition K3top {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (nth 2 (ss_mem MK_CALL) R_bst))).
Definition RSK3 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => ([K3bst; trim_lo K3scr (-2320); K3top]))).
Definition SSK3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_call MK_CALL RSK3 hRFk (0x3626c + D_150)))).
Lemma SSK3_eq {imgk : img} : SSK3 = ss_after_call MK_CALL RSK3 hRFk (0x3626c + D_150). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma MK_CALL_mem3 {imgk : img} : exists rest, ss_mem MK_CALL = K3bst :: K3scr :: K3top :: rest. Proof. img_eexists_vm. Qed.
Lemma MK_AFTER_eq3 {imgk : img} : MK_AFTER = mkSS (0x3626c + D_150) (sr_set (ss_regs SSK3) 10%bv (SLit 1)) ([K3bst; K3scr; K3top] ++ tl REG0K) None (ss_facts SSK3).
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma SSK3_atoms {imgk : img} : regs_atoms_in PND (ss_regs SSK3) = true /\ mem_atoms_in PND (ss_mem SSK3) = true /\ conds_atoms_in PND (ss_facts SSK3) = true /\
ss_resv SSK3 = None /\ f_atoms (ss_facts SSK3) = f_atoms FK.
Proof. img_case; vm_compute. all: repeat split; img_refl. Qed.
Lemma MK_CALL_facts {imgk : img} : ss_atoms_lt hRFk MK_CALL = true /\ regions_wf RSK3 = true /\ no_cdata RSK3 = true /\ mem_atoms_lt hRFk RSK3 = true /\
sr_get (ss_regs MK_CALL) 1%bv = SLit (0x3626c + D_150) /\ ss_resv MK_CALL = None.
Proof. img_case; vm_compute. all: repeat split; img_refl. Qed.
Lemma tlREG0K_facts {imgk : img} : mem_atoms_lt 64 (tl REG0K) = true /\ regions_wf (tl REG0K) = true /\ forallb (fun p => Nat.ltb (fst p) 64) (f_atoms FK) = true.
Proof. img_case; vm_compute. all: repeat split; img_refl. Qed.
Definition MK_N0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (0x3626c + D_150) (sr_set (ss_regs SSK3) 10%bv (SLit 0)) ([K3bst; K3scr; K3top] ++ NREGS) None (ss_facts SSK3)))).
Lemma MK_N0_eq {imgk : img} : MK_N0 = mkSS (0x3626c + D_150) (sr_set (ss_regs SSK3) 10%bv (SLit 0)) ([K3bst; K3scr; K3top] ++ NREGS) None (ss_facts SSK3).
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition MK_NR {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x53434 + D_2c4) MK_N0))).
