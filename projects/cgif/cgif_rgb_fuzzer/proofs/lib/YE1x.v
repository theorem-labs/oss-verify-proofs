(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8v YE1o YE1p YE07 YE1n YE09 YE1s YE1r YE06 YF8r YE04 YE0v YE1q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition FMT_usage {imgk : img} : Z := (0x158ff + D_20).
Definition lit_usage1 : list Z := [117; 115; 97; 103; 101; 58; 32].
Definition lit_usage2 : list Z := [32; 73; 78; 80; 85; 84; 10].
Definition INT_MAX : Z := 2147483647.
Definition vu0 {imgk : img} : sstate := ss_vf FMT_usage (SOff 32 0).
Definition vu_st1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu0)))).
Definition vu_af1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 34 vu_st1 RA_FX OSP_FX (-352) lit_usage1))).
Definition vu_st2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu_af1)))).
Definition vu_af2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 50 vu_st2 RA_FX OSP_FX (-345) []))).
Definition vu_st3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu_af2)))).
Definition vu_af3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 66 vu_st3 RA_SN OSP_SN 0 []))).
Definition vu_r01 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem vu_st1)))).
Definition vu_rest1 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem vu_st1)))).
Definition vu_r02 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem vu_st2)))).
Definition vu_rest2 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem vu_st2)))).
Definition vu_r03 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem vu_st3)))).
Definition vu_rest3 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem vu_st3)))).
Lemma vu_run1 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu0 = (vu_st1, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu_run2 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu_af1 = (vu_st2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu_run3 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu_af2 = (vu_st3, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition vu1_af3f {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_add_fact vu_af3 70 (mkAF 0 66 0)))).
Definition vu1_st4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af3f)))).
Definition vu1_af4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (set_regs_pc vu1_st4 [((12%bv : bv 5), SLit 0)] (0x984a0 + D_10ec)))).
Definition vu1_st5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af4)))).
Definition vu1_af5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 82 vu1_st5 RA_FX OSP_FX (-345) []))).
Definition vu1_st6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af5)))).
Definition vu1_r05 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem vu1_st5)))).
Definition vu1_rest5 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem vu1_st5)))).
Definition vu1_r06 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem vu1_st6)))).
Definition vu1_rest6 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem vu1_st6)))).
Lemma vu1_run4 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af3f = (vu1_st4, RS_stopped (SR_addr (SAlu ALU_ADD (SOff 32 0) (SOff 70 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu1_run5 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af4 = (vu1_st5, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu1_run6 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af5 = (vu1_st6, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition vu1_af6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt_n 98 vu1_st6 RA_FX OSP_FX (-345) (-272)))).
Definition vu1_st7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af6)))).
Lemma vu1_run7 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af6 = (vu1_st7, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition vu1_st7c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond vu1_st7 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7))))).
Definition vu1_st8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu1_st7c)))).
Definition vu1_r08 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem vu1_st8)))).
Definition vu1_rest8 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem vu1_st8)))).
Definition vu1_af8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt_n 114 vu1_st8 RA_FX OSP_FX (-345) (-272)))).
Definition vu1_st9 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af8)))).
Definition vu1_st9c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond vu1_st9 (mkAC BC_NE (SAlu ALU_ADD (SOff 2 (-338)) (SOff 70 0)) (SOff 2 (-352)))))).
Definition vu1_st10 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu1_st9c)))).
Definition vu1_af10 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (wl_after vu1_st10 0 (-480) 130))).
Definition vu1_st11 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af10)))).
Lemma vu1_run8 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu1_st7c = (vu1_st8, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu1_run9 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af8 = (vu1_st9, RS_stopped (SR_branch BC_EQ (SAlu ALU_ADD (SOff 2 (-338)) (SOff 70 0)) (SOff 2 (-352)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu1_run10 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu1_st9c = (vu1_st10, RS_ecall). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu1_run11 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu1_af10 = (vu1_st11, RS_stopped (SR_jalr (SOff 1 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition vu2_af3f {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_add_fact vu_af3 70 (mkAF 67 73 0)))).
Definition vu2_st4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu2_af3f)))).
Definition vu2_af4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (set_regs_pc vu2_st4 [((12%bv : bv 5), SLit 0)] (0x984a0 + D_10ec)))).
Definition vu2_st5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu2_af4)))).
Definition vu2_af5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 82 vu2_st5 RA_FX OSP_FX (-345) []))).
Definition vu2_st6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu2_af5)))).
Definition vu2_r05 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem vu2_st5)))).
Definition vu2_rest5 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem vu2_st5)))).
Definition vu2_r06 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem vu2_st6)))).
Definition vu2_rest6 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem vu2_st6)))).
Lemma vu2_run4 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu2_af3f = (vu2_st4, RS_stopped (SR_addr (SAlu ALU_ADD (SOff 32 0) (SOff 70 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu2_run5 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu2_af4 = (vu2_st5, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu2_run6 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu2_af5 = (vu2_st6, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition vu2_af6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt_n 98 vu2_st6 RA_FX OSP_FX (-345) (-272)))).
Definition vu2_st7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu2_af6)))).
Lemma vu2_run7 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu2_af6 = (vu2_st7, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition vu2_st7c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond vu2_st7 (mkAC BC_LTU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7))))).
Definition vu2_st8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu2_st7c)))).
Definition vu2_st8c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond vu2_st8 (mkAC BC_NE (SAlu ALU_ADD (SOff 2 (-345)) (SOff 70 0)) (SOff 2 (-352)))))).
Definition vu2_st9 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu2_st8c)))).
Definition vu2_af9 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (wl_after vu2_st9 0 (-1024) 114))).
Definition vu2_st10 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu2_af9)))).
Definition vu2_st10r {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (resume vu2_st10 (SLit 0) (ss_mem vu2_st10) (ss_facts vu2_st10)))).
Definition vu2_st11 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu2_st10r)))).
Lemma vu2_run8 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu2_st7c = (vu2_st8, RS_stopped (SR_branch BC_EQ (SAlu ALU_ADD (SOff 2 (-345)) (SOff 70 0)) (SOff 2 (-352)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu2_run9 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu2_st8c = (vu2_st9, RS_ecall). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu2_run10 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu2_af9 = (vu2_st10, RS_ecall). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu2_run11 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu2_st10r = (vu2_st11, RS_stopped (SR_jalr (SOff 1 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition vu3_af3f {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_add_fact vu_af3 70 (mkAF 74 33554425 0)))).
Definition vu3_st4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu3_af3f)))).
Definition vu3_af4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (set_regs_pc vu3_st4 [((12%bv : bv 5), SLit 0)] (0x984a0 + D_10ec)))).
Definition vu3_st5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu3_af4)))).
Definition vu3_af5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 82 vu3_st5 RA_FX OSP_FX (-345) []))).
Definition vu3_st6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu3_af5)))).
Definition vu3_r05 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem vu3_st5)))).
Definition vu3_rest5 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem vu3_st5)))).
Definition vu3_r06 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem vu3_st6)))).
Definition vu3_rest6 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem vu3_st6)))).
Lemma vu3_run4 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu3_af3f = (vu3_st4, RS_stopped (SR_addr (SAlu ALU_ADD (SOff 32 0) (SOff 70 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu3_run5 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu3_af4 = (vu3_st5, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu3_run6 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu3_af5 = (vu3_st6, RS_ecall). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition vu3_af6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (wl_after vu3_st6 0 (-1024) 98))).
Definition vu3_st7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu3_af6)))).
Definition vu3_r07 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem vu3_st7)))).
Definition vu3_rest7 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem vu3_st7)))).
Definition vu3_af7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 109 vu3_st7 RA_FX OSP_FX (-352) lit_usage2))).
Definition vu3_wx {imgk : img} := ltac:(img_eval_last (fun imgk : img => ((wx_step tfxmusl_tbl 125 vu3_af7)))).
Definition vu3_st8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (match vu3_wx with Some (s1, _, _, _) => s1 | None => vu3_af7 end))).
Definition vu3_af8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (match vu3_wx with Some (_, s2, _, _) => s2 | None => vu3_af7 end))).
Definition vu3_st9 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL vu3_af8)))).
Lemma vu3_wx_eq {imgk : img} : wx_step tfxmusl_tbl 125 vu3_af7 = Some (vu3_st8, vu3_af8, lit_usage2, 2). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu3_run7 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu3_af6 = (vu3_st7, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma vu3_run9 {imgk : img} : sym_runN tfxsegs tfxmusl_tbl FUEL vu3_af8 = (vu3_st9, RS_stopped (SR_jalr (SOff 1 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Section S. Context {imgk : img}.
Variable B : asyms.
Hypothesis TL : TfxSyms B.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfxsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ASTRNLEN : astrnlen_realizesM B (pc_wrap_strnlen (as_code B)).
Let HBcode := ts_code B TL.
Lemma lit_usage1_range : Forall (fun z => 0 <= z < 256) lit_usage1. Proof. img_apply Forall_range_of_forallb. img_case; vm_compute. all: img_refl. Qed.
Lemma lit_usage2_range : Forall (fun z => 0 <= z < 256) lit_usage2. Proof. img_apply Forall_range_of_forallb. img_case; vm_compute. all: img_refl. Qed.
Theorem tfx_vfprintf_usage_A1 : forall ly S (W : world tfxsegs) regs mem md ch ap s (str : list byte) L cval T,
ecall_pre tfxsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_usage -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfxsegs (mrestrict (w_H W) mem) ap 8 s ->
L = Z.of_nat (length str) -> 0 <= L -> L <= 66 ->
1 <= s -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= spZ regs - VF_STK \/ spZ regs <= s) ->
(s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) -> amem_range s (L + 1) ->
vf_tail W mem s L -> mconsts_view W mem ->
vf_str W mem s str ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF s (L + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) s (L + 1) ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF FMT_usage 17 ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) FMT_usage 17 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfxsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfxsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 (L + 14) ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vf_file a -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfxsegs (w_H W) (w_A W) md' ->
srealizes tfxsegs (cfg_at tfxsegs (raZ regs) regs' mem' md') T) ->
srealizes tfxsegs (cfg_at tfxsegs A_vfprintf regs mem md)
(t_emit (map (WriteEv ch) (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2)) T).
Proof.
intros ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HL HLlo HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
assert (HFF : F_STDERR = (681808 + D_10f0)) by img_refl. assert (HFS : FILE_SZ = 232) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (img_try (rewrite KHI; img_lia)).
assert (Hsp47 : sp0 <= 2 ^ 47) by img_lia.
assert (HLlen : length str = Z.to_nat L) by img_lia.
unfold cfg_at. img_change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vf_entry W regs mem FMT_usage (SOff 32 0) ap s cval Hsp44 Hsp47 Hal16
ltac:(img_try (intros a Ha; img_apply Hpres; img_exact Ha)) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg ltac:(img_lia)
HFP Hgot Hcan Hcv Hro ltac:(img_try (cbn [sv_denot]; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl))) as HS0.
img_change (ss_vf FMT_usage (SOff 32 0)) with vu0 in HS0.
remember (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (img_try (intros i r Hi; (subst E0; cbv beta); img_exact (ew_Ereg_nat regs _ i r Hi))).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); img_refl)).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (img_try (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); img_exact Hgp)).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (img_try (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); img_exact Htp)).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (img_try (rewrite (EE 12%nat (12%bv : bv 5) eq_refl), Ha2; img_apply unsigned_lit_small; img_lia)).
assert (A32_0 : bv_unsigned (ew E0 32) = s) by (img_try (rewrite HE0, (ew_Ereg_extra regs _ 0); cbn [nth]; img_apply unsigned_lit_small; img_lia)).
assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E0) by (img_try (rewrite HE0; split; [img_try (intros i Hi; img_refl) | img_refl])).
clear HE0 EE.
pose proof (VI_init B ly S W sp0 mem md HAR Hpres) as VI0.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E0 vu0 vu_st1 _ _ _ HS0 vu_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VI1 : VI B ly S W sp0 mem md (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms1) mat1 VI0) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin); tauto.
- img_apply (vf_band_present W E0 vu_st1 ms1 sp0 HS1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VI0 HF1 HFr1.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms1) _ FMT_usage 17 (88319 + D_20) 7 VI1 Hstk Hra_f Hhull_f
ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (rewrite KHI; unfold FMT_usage; img_lia))) as [SRA1' SHU1'].
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E0 vu_st1 ms1 _ ly S sp0 vu_r01 vu_rest1 34 RA_FX OSP_FX (-352) (SLit (88319 + D_20)) ((88319 + D_20)) 7 lit_usage1
HS1 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_refl) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold OSP_FX; cbn; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (left; unfold kLowMemEnd; cbn; img_lia))
(vf_rest_ok E0 sp0 ap vu_rest1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_0 Hap1 Hap2)
(vf_rest_w E0 vu_rest1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI1) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI1))) SRA1' SHU1') HAI1).
intros W1' c1' _ HAI1' (-> & ms1' & mat1' & -> & HS1' & HAR1' & HP1' & Hfr1' & Hpm1'). cbn [cfg_model] in HAI1'.
rewrite wvb_wvb in HAI1', HAR1' |- *.
img_change (vf_after_icpt 34 vu_st1 RA_FX OSP_FX (-352) lit_usage1) with vu_af1 in HS1'.
assert (VI1' : VI B ly S W sp0 mem md (ms_mem ms1') (with_vm_backing (m_vm_lazy md) mat1' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms1) _ (ms_mem ms1') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-352) <= a < sp0 + (-352) + 7))).
- img_exact VI1.
- img_exact HAR1'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat1' mat1 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr1'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm1'. }
remember (havoc E0 34 (map (getr (ms_regs ms1')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 34)%nat -> ew E1 j = ew E0 j) by (img_try (intros j Hj; rewrite HE1; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact Usp0)).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G3_0)).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G4_0)).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G12_0)).
assert (A32_1 : bv_unsigned (ew E1 32) = s) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A32_0)).
assert (HAE1 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E1)
by (img_try (rewrite HE1; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE0)])).
clear HE1 HS1 VI1 SRA1' SHU1'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E1 vu_af1 vu_st2 _ _ _ HS1' vu_run2) HAI1').
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1'.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VI2 : VI B ly S W sp0 mem md (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms2) mat2 VI1') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin); tauto.
- img_apply (vf_band_present W E1 vu_st2 ms2 sp0 HS2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 ltac:(img_lia)). }
clear VI1' HF2 HFr2.
assert (SRA2' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms2)) SHADOW_OFF (88326 + D_20) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms2)) (88326 + D_20) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E1 vu_st2 ms2 _ ly S sp0 vu_r02 vu_rest2 50 RA_FX OSP_FX (-345) (SLit (88326 + D_20)) ((88326 + D_20)) 0 (@nil Z)
HS2 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_refl) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold OSP_FX; cbn; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (left; unfold kLowMemEnd; cbn; img_lia))
(vf_rest_ok E1 sp0 ap vu_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_1 Hap1 Hap2)
(vf_rest_w E1 vu_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI2) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI2))) SRA2' SHU2') HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
img_change (vf_after_icpt 50 vu_st2 RA_FX OSP_FX (-345) (@nil Z)) with vu_af2 in HS2'.
assert (VI2' : VI B ly S W sp0 mem md (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- img_exact VI2.
- img_exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr2'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm2'. }
remember (havoc E1 50 (map (getr (ms_regs ms2')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 50)%nat -> ew E2 j = ew E1 j) by (img_try (intros j Hj; rewrite HE2; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact Usp1)).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G3_1)).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G4_1)).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G12_1)).
assert (A32_2 : bv_unsigned (ew E2 32) = s) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A32_1)).
assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E2)
by (img_try (rewrite HE2; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE1)])).
clear HE2 HS2 VI2 SRA2' SHU2'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E2 vu_af2 vu_st3 _ _ _ HS2' vu_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VI3 : VI B ly S W sp0 mem md (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms3) mat3 VI2') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin); tauto.
- img_apply (vf_band_present W E2 vu_st3 ms3 sp0 HS3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 ltac:(img_lia)). }
clear VI2' HF3 HFr3.
assert (STR3 : vf_str W (ms_mem ms3) s str).
{ img_apply (vf_str_xfer W mem); [img_try (img_exact HSTR)|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI3)))); [img_lia | img_try (unfold vf_band; img_lia) | img_try (unfold vf_file; img_lia)]. }
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms3) _ s (L + 1) s (L + 1) VI3 Hstk Hra_s Hhull_s
ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (rewrite KHI; img_lia))) as [SRA3' SHU3'].
pose proof (vf_tail_xfer W mem (ms_mem ms3) sp0 s L Hstail (proj1 (proj2 (proj2 (proj2 VI3)))) Hal16 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) Hsband Hsfile) as TAIL3.
pose proof (mconsts_view_xfer W mem (ms_mem ms3) sp0 Hromv (proj1 (proj2 (proj2 (proj2 VI3)))) Hsp44) as ROM3.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_strnlen B ASTRNLEN W E2 vu_st3 ms3 _ ly S sp0 vu_r03 vu_rest3 66 RA_SN OSP_SN (SOff 32 0) s INT_MAX L
HS3 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(img_try (cbn [sv_denot]; rewrite Z.add_0_r, <- A32_2, Z_to_bv_bv_unsigned; img_refl)) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_SN; img_lia)) ltac:(img_try (unfold OSP_SN; img_lia)) ltac:(img_try (unfold RA_SN; img_lia)) ltac:(img_refl)
ltac:(img_try (unfold INT_MAX; img_lia)) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (unfold INT_MAX; img_lia)) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (unfold OSP_SN; img_lia))
(vf_rest_ok E2 sp0 ap vu_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_2 Hap1 Hap2)
(vf_rest_w E2 vu_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VI3)))
ltac:(img_try (rewrite HL; img_apply (vf_str_first_byte W _ s str INT_MAX STR3); unfold INT_MAX; img_lia))
ltac:(img_try (intros a Ha; img_apply (vf_str_readable W _ s str STR3); img_lia))
Hams SRA3' (SHU3' ltac:(img_lia)) TAIL3 ROM3) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & HL3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
img_change (vf_after_icpt 66 vu_st3 RA_SN OSP_SN 0 []) with vu_af3 in HS3'.
assert (VI3' : VI B ly S W sp0 mem md (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms3) _ (ms_mem ms3') _
(fun a => sp0 + OSP_SN - 2 * ESTACK <= a < sp0 + OSP_SN)).
- img_exact VI3.
- img_exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_SN in *. img_lia.
- intros a Hr Hna. img_apply Hfr3'; [img_try (img_exact Hr) | img_try (img_exact Hna)].
- img_exact Hpm3'. }
remember (havoc E2 66 (map (getr (ms_regs ms3')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 66)%nat -> ew E3 j = ew E2 j) by (img_try (intros j Hj; rewrite HE3; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact Usp2)).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G3_2)).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G4_2)).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G12_2)).
assert (A32_3 : bv_unsigned (ew E3 32) = s) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A32_2)).
assert (HAE3 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E3)
by (img_try (rewrite HE3; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE2)])).
assert (A70_3 : bv_unsigned (ew E3 70) = L).
{ rewrite HE3, (ew_havoc_new E2 66 _ 4 (w64 0)) by (img_try (cbn; img_lia)). unfold CLOB. cbn [nth map]. rewrite HL3'. img_apply unsigned_lit_small. img_lia. }
clear HE3 HS3 VI3 SRA3' SHU3' STR3.
pose proof (st_ok_add_fact E3 vu_af3 _ 70 0 66 HS3' eq_refl ltac:(img_try (rewrite A70_3; img_lia))) as HS3f.
img_change (vf_add_fact vu_af3 70 (mkAF 0 66 0)) with vu1_af3f in HS3f. clear HS3'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E3 vu1_af3f vu1_st4 _ _ _ HS3f vu1_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3f.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VI4 : VI B ly S W sp0 mem md (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms4) mat4 VI3') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF4. intros Hin. destruct (vf_windows_sound E3 vu1_af3f sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr4. intros Hin. destruct (vf_windows_sound E3 vu1_af3f sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- img_apply (vf_band_present W E3 vu1_st4 ms4 sp0 HS4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 ltac:(img_lia)). }
clear VI3' HF4 HFr4.
assert (STR4 : vf_str W (ms_mem ms4) s str).
{ img_apply (vf_str_xfer W mem); [img_try (img_exact HSTR)|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI4)))); [img_lia | img_try (unfold vf_band; img_lia) | img_try (unfold vf_file; img_lia)]. }
assert (R11_4 : getr (ms_regs ms4) 11 = Z_to_bv 64 (s + L)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E3 _ _ 11 HS4).
match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite denot_lit_U, U_add_off_atom by (img_try (rewrite ?A32_3, ?A70_3; unfold M64; img_lia)). rewrite A32_3, A70_3. f_equal. img_lia. }
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_lbu_nul W E3 vu1_st4 ms4 _ 82 (s + L) HS4 eq_refl eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) R11_4 ltac:(img_lia)
ltac:(img_try (rewrite HL; img_exact (proj1 (proj2 STR4))))) HAI4).
intros W4l c4l _ HAI4l (-> & ms4l & mat4l & -> & HS4l & Hmm4l). cbn [cfg_model] in HAI4l. rewrite ?wvb_wvb in HAI4l |- *.
img_change (set_regs_pc vu1_st4 [((12%bv : bv 5), SLit 0)] (0x984a0 + D_10ec)) with vu1_af4 in HS4l.
assert (VI4l : VI B ly S W sp0 mem md (ms_mem ms4l) (with_vm_backing (m_vm_lazy md) mat4l md)).
{ rewrite Hmm4l. pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms4) mat4l VI4) as VR.
rewrite ?wvb_wvb in VR. img_apply VR; [img_try (intros; img_refl) | img_try (intros; img_refl) | img_try (img_exact (proj1 (proj2 (proj2 VI4))))]. }
clear VI4 HS4 STR4 R11_4.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E3 vu1_af4 vu1_st5 _ _ _ HS4l vu1_run5) HAI4l).
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4l.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VI5 : VI B ly S W sp0 mem md (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms5) mat5 VI4l) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF5. intros Hin. destruct (vf_windows_sound E3 vu1_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr5. intros Hin. destruct (vf_windows_sound E3 vu1_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- img_apply (vf_band_present W E3 vu1_st5 ms5 sp0 HS5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 ltac:(img_lia)). }
clear VI4l HF5 HFr5.
assert (SRA5' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms5)) SHADOW_OFF (68452 + D_20) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU5' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms5)) (68452 + D_20) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E3 vu1_st5 ms5 _ ly S sp0 vu1_r05 vu1_rest5 82 RA_FX OSP_FX (-345) (SLit (68452 + D_20)) ((68452 + D_20)) 0 (@nil Z)
HS5 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp3 G3_3 G4_3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_refl) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold OSP_FX; cbn; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (left; unfold kLowMemEnd; cbn; img_lia))
(vf_rest_ok E3 sp0 ap vu1_rest5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_3 Hap1 Hap2)
(vf_rest_w E3 vu1_rest5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI5) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI5))) SRA5' SHU5') HAI5).
intros W5' c5' _ HAI5' (-> & ms5' & mat5' & -> & HS5' & HAR5' & HP5' & Hfr5' & Hpm5'). cbn [cfg_model] in HAI5'.
rewrite wvb_wvb in HAI5', HAR5' |- *.
img_change (vf_after_icpt 82 vu1_st5 RA_FX OSP_FX (-345) (@nil Z)) with vu1_af5 in HS5'.
assert (VI5' : VI B ly S W sp0 mem md (ms_mem ms5') (with_vm_backing (m_vm_lazy md) mat5' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms5) _ (ms_mem ms5') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- img_exact VI5.
- img_exact HAR5'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat5' mat5 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr5'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm5'. }
remember (havoc E3 82 (map (getr (ms_regs ms5')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 82)%nat -> ew E5 j = ew E3 j) by (img_try (intros j Hj; rewrite HE5; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact Usp3)).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G3_3)).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G4_3)).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G12_3)).
assert (A32_5 : bv_unsigned (ew E5 32) = s) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact A32_3)).
assert (A70_5 : bv_unsigned (ew E5 70) = L) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact A70_3)).
assert (HAE5 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E5)
by (img_try (rewrite HE5; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE3)])).
clear HE5 HS5 VI5 SRA5' SHU5'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E5 vu1_af5 vu1_st6 _ _ _ HS5' vu1_run6) HAI5').
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5'.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VI6 : VI B ly S W sp0 mem md (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms6) mat6 VI5') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF6. intros Hin. destruct (vf_windows_sound E5 vu1_af5 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr6. intros Hin. destruct (vf_windows_sound E5 vu1_af5 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin); tauto.
- img_apply (vf_band_present W E5 vu1_st6 ms6 sp0 HS6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 ltac:(img_lia)). }
clear VI5' HF6 HFr6.
assert (STR6 : vf_str W (ms_mem ms6) s str).
{ img_apply (vf_str_xfer W mem); [img_try (img_exact HSTR)|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI6)))); [img_lia | img_try (unfold vf_band; img_lia) | img_try (unfold vf_file; img_lia)]. }
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms6) _ s (L + 1) s L VI6 Hstk Hra_s Hhull_s
ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (rewrite KHI; img_lia))) as [SRA6' SHU6'].
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_sym B LAWS AMEMCPY W E5 vu1_st6 ms6 _ ly S sp0 vu1_r06 vu1_rest6 98 RA_FX OSP_FX (-345) (-272)
(SOff 2 (-345)) (SOff 32 0) (SOff 70 0) (-345) (s) (L)
HS6 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp5 G3_5 G4_5 eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_try (cbn; img_lia))
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(img_try (cbn [sv_denot]; rewrite Usp5; img_refl)) eq_refl ltac:(img_try (cbn [sv_denot]; rewrite Z.add_0_r, A32_5; img_refl)) eq_refl ltac:(img_try (cbn [sv_denot]; rewrite Z.add_0_r, A70_5; img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_lia) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_lia) ltac:(img_try (destruct Hams as [Hams'|[Hams' Hams'']]; [img_try (left; img_lia) | img_try (right; img_lia)]))
(vf_rest_ok E5 sp0 ap vu1_rest6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_5 Hap1 Hap2)
(vf_rest_w E5 vu1_rest6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI6) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI6)))
ltac:(img_try (intros a Ha; img_apply (vf_str_readable W _ s str STR6); img_lia)) SRA6' SHU6') HAI6).
intros W6' c6' _ HAI6' (-> & ms6' & mat6' & -> & HS6' & HAR6' & HP6' & Heff6' & Hfr6' & Hpm6'). cbn [cfg_model] in HAI6'.
rewrite wvb_wvb in HAI6', HAR6' |- *.
img_change (vf_after_icpt_n 98 vu1_st6 RA_FX OSP_FX (-345) (-272)) with vu1_af6 in HS6'.
assert (VI6' : VI B ly S W sp0 mem md (ms_mem ms6') (with_vm_backing (m_vm_lazy md) mat6' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms6) _ (ms_mem ms6') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + (L)))).
- img_exact VI6.
- img_exact HAR6'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat6' mat6 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr6'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm6'. }
assert (STRBUF6' : forall i, (i < length str)%nat -> aview tfxsegs (w_H W) (ms_mem ms6') (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite (Heff6' (Z.of_nat i)) by img_lia. img_apply (proj1 STR6). img_exact Hi. }
remember (havoc E5 98 (map (getr (ms_regs ms6')) CLOB)) as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 98)%nat -> ew E6 j = ew E5 j) by (img_try (intros j Hj; rewrite HE6; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact Usp5)).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G3_5)).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G4_5)).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G12_5)).
assert (A32_6 : bv_unsigned (ew E6 32) = s) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact A32_5)).
assert (A70_6 : bv_unsigned (ew E6 70) = L) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact A70_5)).
assert (HAE6 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E6)
by (img_try (rewrite HE6; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE5)])).
clear HE6 HS6 VI6 SRA6' SHU6' Heff6'.
clear STR6.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E6 vu1_af6 vu1_st7 _ _ _ HS6' vu1_run7) HAI6').
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7. clear HS6'.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VI7 : VI B ly S W sp0 mem md (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms7) mat7 VI6') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF7. intros Hin. destruct (vf_windows_sound_n E6 vu1_af6 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr7. intros Hin. destruct (vf_windows_sound_n E6 vu1_af6 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms6') (ms_mem ms7) sp0 (-345) (proj1 (proj2 (proj2 VI6')))
(vf_band_present_n W E6 vu1_st7 ms7 sp0 (-345) HS7 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 ltac:(img_lia))).
intros a Ha. img_apply HF7. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E6 vu1_af6 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
assert (STRBUF7 : forall i, (i < length str)%nat -> aview tfxsegs (w_H W) (ms_mem ms7) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF6' i Hi). img_apply aview_eq_of. img_apply HFr7. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E6 vu1_af6 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear VI6' HF7 HFr7 STRBUF6'.
pose proof (st_ok_add_cond tfxsegs E6 vu1_st7 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7) HS7 ltac:(img_try (rewrite branch_geu_U, U_neg_off, U_SLit by (rewrite A70_6; unfold M64; img_lia); rewrite A70_6; img_change (zcanon 7) with 7; img_apply Bool.negb_true_iff; img_apply Z.ltb_ge; img_lia))) as HS7c.
img_change (YQ09.add_cond vu1_st7 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7))) with vu1_st7c in HS7c. clear HS7.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E6 vu1_st7c vu1_st8 _ _ _ HS7c vu1_run8) HAI7).
intros W8 c8 _ HAI8 (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [cfg_model] in HAI8. clear HS7c.
rewrite ?wvb_wvb in HAI8 |- *.
assert (VI8 : VI B ly S W sp0 mem md (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms8) mat8 VI7) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF8. intros Hin. destruct (vf_windows_sound_n E6 vu1_st7c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr8. intros Hin. destruct (vf_windows_sound_n E6 vu1_st7c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms7) (ms_mem ms8) sp0 (-345) (proj1 (proj2 (proj2 VI7)))
(vf_band_present_n W E6 vu1_st8 ms8 sp0 (-345) HS8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 ltac:(img_lia))).
intros a Ha. img_apply HF8. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E6 vu1_st7c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
assert (STRBUF8 : forall i, (i < length str)%nat -> aview tfxsegs (w_H W) (ms_mem ms8) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF7 i Hi). img_apply aview_eq_of. img_apply HFr8. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E6 vu1_st7c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear VI7 HF8 HFr8 STRBUF7.
pose proof HS8 as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & Hmem8 & _). cbn [restrict ms_mem] in Hmem8.
assert (LIT2AV8 : forall i, (i < 7)%nat -> aview tfxsegs (w_H W) (ms_mem ms8) ((88328 + D_20) + Z.of_nat i) = Some (nth i lit_usage2 0)).
{ intros i Hi. img_apply (lit_buf_aview W E6 (ms_mem ms8) (ss_mem vu1_st8) (SLit (88328 + D_20)) (88328 + D_20) 7 lit_usage2 Hmem8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) eq_refl lit_usage2_range i Hi). }
clear Hmem8.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms8) _ FMT_usage 17 (88328 + D_20) 7 VI8 Hstk Hra_f Hhull_f
ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (rewrite KHI; unfold FMT_usage; img_lia))) as [SRA8' SHU8'].
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_sym B LAWS AMEMCPY W E6 vu1_st8 ms8 _ ly S sp0 vu1_r08 vu1_rest8 114 RA_FX OSP_FX (-345) (-272)
(SAlu ALU_ADD (SOff 2 (-345)) (SOff 70 0)) (SLit (88328 + D_20)) (SLit 7) (-345 + L) ((88328 + D_20)) (7)
HS8 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp6 G3_6 G4_6 eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_try (cbn; img_lia))
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(img_try (rewrite denot_lit_U, U_add_off_atom by (rewrite ?Usp6, ?A70_6; unfold M64; img_lia); rewrite Usp6, A70_6; f_equal; img_lia)) eq_refl ltac:(img_refl) eq_refl ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_lia) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_lia) ltac:(img_try (left; unfold kLowMemEnd; cbn; img_lia))
(vf_rest_ok E6 sp0 ap vu1_rest8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_6 Hap1 Hap2)
(vf_rest_w E6 vu1_rest8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI8) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI8)))
ltac:(img_try (intros a Ha; replace a with ((88328 + D_20) + Z.of_nat (Z.to_nat (a - (88328 + D_20)))) by img_lia; rewrite (LIT2AV8 (Z.to_nat (a - (88328 + D_20))) ltac:(img_lia)); discriminate)) SRA8' SHU8') HAI8).
intros W8' c8' _ HAI8' (-> & ms8' & mat8' & -> & HS8' & HAR8' & HP8' & Heff8' & Hfr8' & Hpm8'). cbn [cfg_model] in HAI8'.
rewrite wvb_wvb in HAI8', HAR8' |- *.
img_change (vf_after_icpt_n 114 vu1_st8 RA_FX OSP_FX (-345) (-272)) with vu1_af8 in HS8'.
assert (VI8' : VI B ly S W sp0 mem md (ms_mem ms8') (with_vm_backing (m_vm_lazy md) mat8' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms8) _ (ms_mem ms8') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345 + L) <= a < sp0 + (-345 + L) + (7)))).
- img_exact VI8.
- img_exact HAR8'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat8' mat8 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr8'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm8'. }
assert (STRBUF8' : forall i, (i < length str)%nat -> aview tfxsegs (w_H W) (ms_mem ms8') (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF8 i Hi). img_apply Hfr8'; [img_lia | img_try (unfold OSP_FX; img_lia) | img_lia]. }
assert (LIT2BUF8' : forall i, (i < 7)%nat -> aview tfxsegs (w_H W) (ms_mem ms8') (sp0 + (-345 + L) + Z.of_nat i) = Some (nth i lit_usage2 0)).
{ intros i Hi. rewrite (Heff8' (Z.of_nat i)) by img_lia. img_apply LIT2AV8. img_exact Hi. }
remember (havoc E6 114 (map (getr (ms_regs ms8')) CLOB)) as E7 eqn:HE7.
assert (OLD7 : forall j, (j < 114)%nat -> ew E7 j = ew E6 j) by (img_try (intros j Hj; rewrite HE7; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp7 : bv_unsigned (ew E7 2) = sp0) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact Usp6)).
assert (G3_7 : ew E7 3 = w64 (as_gp B)) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G3_6)).
assert (G4_7 : ew E7 4 = w64 (as_tp B)) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G4_6)).
assert (G12_7 : bv_unsigned (ew E7 12) = ap) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G12_6)).
assert (A32_7 : bv_unsigned (ew E7 32) = s) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact A32_6)).
assert (A70_7 : bv_unsigned (ew E7 70) = L) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact A70_6)).
assert (HAE7 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E7)
by (img_try (rewrite HE7; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE6)])).
clear HE7 HS8 VI8 SRA8' SHU8' Heff8' STRBUF8.
clear LIT2AV8.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E7 vu1_af8 vu1_st9 _ _ _ HS8' vu1_run9) HAI8').
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9. clear HS8'.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VI9 : VI B ly S W sp0 mem md (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms9) mat9 VI8') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF9. intros Hin. destruct (vf_windows_sound_n E7 vu1_af8 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr9. intros Hin. destruct (vf_windows_sound_n E7 vu1_af8 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms8') (ms_mem ms9) sp0 (-345) (proj1 (proj2 (proj2 VI8')))
(vf_band_present_n W E7 vu1_st9 ms9 sp0 (-345) HS9 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 ltac:(img_lia))).
intros a Ha. img_apply HF9. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_af8 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
assert (STRBUF9 : forall i, (i < length str)%nat -> aview tfxsegs (w_H W) (ms_mem ms9) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF8' i Hi). img_apply aview_eq_of. img_apply HFr9. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_af8 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
assert (LIT2BUF9 : forall i, (i < 7)%nat -> aview tfxsegs (w_H W) (ms_mem ms9) (sp0 + (-345 + L) + Z.of_nat i) = Some (nth i lit_usage2 0)).
{ intros i Hi. rewrite <- (LIT2BUF8' i Hi). img_apply aview_eq_of. img_apply HFr9. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_af8 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear VI8' HF9 HFr9 STRBUF8' LIT2BUF8'.
pose proof (st_ok_add_cond_neg tfxsegs E7 vu1_st9 _ BC_EQ (SAlu ALU_ADD (SOff 2 (-338)) (SOff 70 0)) (SOff 2 (-352)) HS9 ltac:(img_try (rewrite branch_eq_U, U_add_off_atom, U_off by (rewrite ?Usp7, ?A70_7; unfold M64; img_lia); rewrite Usp7, A70_7; img_apply Z.eqb_neq; img_lia))) as HS9c.
img_change (YQ09.add_cond vu1_st9 (mkAC (neg_bc BC_EQ) (SAlu ALU_ADD (SOff 2 (-338)) (SOff 70 0)) (SOff 2 (-352)))) with vu1_st9c in HS9c. clear HS9.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E7 vu1_st9c vu1_st10 _ _ _ HS9c vu1_run10) HAI9).
intros W10 c10 _ HAI10 (-> & ms10 & mat10 & -> & HS10 & HF10 & HFr10). cbn [cfg_model] in HAI10. clear HS9c.
rewrite ?wvb_wvb in HAI10 |- *.
assert (VI10 : VI B ly S W sp0 mem md (ms_mem ms10) (with_vm_backing (m_vm_lazy md) mat10 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms10) mat10 VI9) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF10. intros Hin. destruct (vf_windows_sound_n E7 vu1_st9c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr10. intros Hin. destruct (vf_windows_sound_n E7 vu1_st9c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms9) (ms_mem ms10) sp0 (-345) (proj1 (proj2 (proj2 VI9)))
(vf_band_present_n_ecall W E7 vu1_st10 ms10 sp0 (-345) HS10 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 ltac:(img_lia))).
intros a Ha. img_apply HF10. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_st9c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
assert (STRBUF10 : forall i, (i < length str)%nat -> aview tfxsegs (w_H W) (ms_mem ms10) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF9 i Hi). img_apply aview_eq_of. img_apply HFr10. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_st9c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
assert (LIT2BUF10 : forall i, (i < 7)%nat -> aview tfxsegs (w_H W) (ms_mem ms10) (sp0 + (-345 + L) + Z.of_nat i) = Some (nth i lit_usage2 0)).
{ intros i Hi. rewrite <- (LIT2BUF9 i Hi). img_apply aview_eq_of. img_apply HFr10. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_st9c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear VI9 HF10 HFr10 STRBUF9 LIT2BUF9.
replace (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2) with ((map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2) ++ []) by img_apply app_nil_r.
pose proof HS10 as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & Hregs10 & Hmem10 & HG10). cbn [restrict ms_mem] in Hmem10.
pose proof (lit_buf_sound tfxsegs E7 (mrestrict (w_H W) (ms_mem ms10)) (ss_mem vu1_st10) (SLit (F_STDERR + 120)) 4 [2; 0; 0; 0] Hmem10
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as Hfdrd. cbn [sv_denot] in Hfdrd.
assert (LIT1AV10 : forall i, (i < 7)%nat -> aview tfxsegs (w_H W) (ms_mem ms10) (sp0 + (-352) + Z.of_nat i) = Some (nth i lit_usage1 0)).
{ intros i Hi. img_apply (lit_buf_aview W E7 (ms_mem ms10) (ss_mem vu1_st10) (SOff 2 (-352)) (sp0 + (-352)) 7 lit_usage1 Hmem10 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try (cbn [sv_denot]; rewrite Usp7; img_refl)) lit_usage1_range i Hi). }
eapply (srz_sym_stdio_writev2 W E7 vu1_st10 ms10 _ (Z_to_bv 64 2) ch 0 2 (-480) F_STDERR _ (SOff 2 (-352)) (SOff 70 14) (SLit 0) (SLit 0)
((map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2)) ([]) (map (Z_to_bv 8) [2; 0; 0; 0]) 130 T HAI10 HS10 eq_refl eq_refl eq_refl).
- img_refl.
- eapply fdchan_sbm; [img_try (img_exact Hch) | img_try (img_apply with_vm_backing_same)].
- img_refl.
- img_case; vm_compute. all: img_refl.
- match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite iovcnt_val, U_add_off_atom, U_off by (img_try (rewrite ?Usp7, ?A70_7; unfold M64; img_lia)). rewrite (proj2 (Z.eqb_neq _ _)) by img_lia. img_refl.
- match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite iovcnt_val', U_add_off_atom, U_off by (img_try (rewrite ?Usp7, ?A70_7; unfold M64; img_lia)). rewrite (proj2 (Z.eqb_neq _ _)) by img_lia. img_refl.
- img_refl.
- img_refl.
- img_refl.
- match goal with |- U _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite U_SLit, !U_off by (img_try (rewrite A70_7; unfold M64; img_lia)). img_change (zcanon 0) with 0. img_lia.
- match goal with |- U _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end. rewrite U_SLit. img_refl.
- img_refl.
- img_refl.
- cbn. img_lia. - cbn. img_lia. - cbn. img_lia. - cbn. img_lia.
- img_case; vm_compute. all: img_refl.
-
rewrite word_to_nat_U, U_off by (img_try (rewrite A70_7; unfold M64; img_lia)). cbn [sv_denot]. rewrite Usp7, A70_7.
replace (Z.to_nat (L + 14)) with (length lit_usage1 + length str + length lit_usage2)%nat by (img_try (rewrite HLlen; cbn; img_lia)).
img_apply (rdn_cat3 (w_H W) (ms_mem ms10) (sp0 + (-352)) lit_usage1 str lit_usage2 lit_usage1_range lit_usage2_range LIT1AV10).
+ intros i Hi. replace (sp0 + (-352) + Z.of_nat (length lit_usage1) + Z.of_nat i) with (sp0 + (-345) + Z.of_nat i) by (img_try (cbn; img_lia)). img_apply STRBUF10. img_exact Hi.
+ intros i Hi. replace (sp0 + (-352) + Z.of_nat (length lit_usage1) + Z.of_nat (length str) + Z.of_nat i) with (sp0 + (-345 + L) + Z.of_nat i) by (img_try (rewrite HLlen; cbn; img_lia)).
img_apply LIT2BUF10. cbn in Hi. img_exact Hi.
-   img_refl.
- rewrite U_SLit, U_off by (img_try (rewrite A70_7; unfold M64; img_lia)). rewrite A70_7. img_change (zcanon 0) with 0. img_lia.
- rewrite !U_off by (img_try (rewrite ?Usp7, ?A70_7; unfold M64; img_lia)). rewrite Usp7, A70_7. img_lia.
- rewrite !U_off by (img_try (rewrite ?Usp7, ?A70_7; unfold M64; img_lia)). rewrite Usp7, A70_7. img_lia.
- rewrite !U_SLit. img_change (zcanon 0) with 0. img_lia.
- rewrite !U_SLit. img_change (zcanon 0) with 0. rewrite Usp7. img_lia.
- img_exact Hfdrd.
- img_case; vm_compute. all: img_refl.
- unfold F_STDERR. img_lia.
- unfold F_STDERR. img_lia.
- rewrite Usp7. unfold F_STDERR. img_lia.
- rewrite Usp7. img_lia.
- rewrite Usp7. img_lia.
- img_case; vm_compute. all: img_refl.
-
intros ms10' ws10' mat10' HS10' HF10' HFr10' HAI10'. rewrite ?wvb_wvb in HAI10' |- *.
img_change (wl_after vu1_st10 0 (-480) 130) with vu1_af10 in HS10'.
remember (havoc E7 130 ws10') as E8 eqn:HE8.
assert (OLD8 : forall j, (j < 130)%nat -> ew E8 j = ew E7 j) by (img_try (intros j Hj; rewrite HE8; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp8 : bv_unsigned (ew E8 2) = sp0) by (img_try (rewrite OLD8 by ((img_case; cbv); img_lia); img_exact Usp7)).
assert (G3_8 : ew E8 3 = w64 (as_gp B)) by (img_try (rewrite OLD8 by ((img_case; cbv); img_lia); img_exact G3_7)).
assert (G4_8 : ew E8 4 = w64 (as_tp B)) by (img_try (rewrite OLD8 by ((img_case; cbv); img_lia); img_exact G4_7)).
assert (G12_8 : bv_unsigned (ew E8 12) = ap) by (img_try (rewrite OLD8 by ((img_case; cbv); img_lia); img_exact G12_7)).
assert (A32_8 : bv_unsigned (ew E8 32) = s) by (img_try (rewrite OLD8 by ((img_case; cbv); img_lia); img_exact A32_7)).
assert (A70_8 : bv_unsigned (ew E8 70) = L) by (img_try (rewrite OLD8 by ((img_case; cbv); img_lia); img_exact A70_7)).
assert (HAE8 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E8)
by (img_try (rewrite HE8; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE7)])).
assert (VI10' : VI B ly S W sp0 mem md (ms_mem ms10') (with_vm_backing (m_vm_lazy md) mat10' md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms10') mat10' VI10) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF10'. intros Hin. destruct (vf_windows_sound_n E7 vu1_st10 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr10'. intros Hin. destruct (vf_windows_sound_n E7 vu1_st10 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms10) (ms_mem ms10') sp0 (-345) (proj1 (proj2 (proj2 VI10)))
(vf_band_present_n W E8 vu1_af10 ms10' sp0 (-345) HS10' ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp8 ltac:(img_lia))).
intros a Ha. img_apply HF10'. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_st10 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear HE8 HS10 VI10 Hfdrd Hregs10 Hmem10 HG10 HF10' HFr10'.
clear STRBUF10 LIT2BUF10 LIT1AV10.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E8 vu1_af10 vu1_st11 _ _ _ HS10' vu1_run11) HAI10').
intros W11 c11 _ HAI11 (-> & ms11 & mat11 & -> & HS11 & HF11 & HFr11). cbn [cfg_model] in HAI11. clear HS10'.
rewrite ?wvb_wvb in HAI11 |- *.
assert (VI11 : VI B ly S W sp0 mem md (ms_mem ms11) (with_vm_backing (m_vm_lazy md) mat11 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms11) mat11 VI10') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF11. intros Hin. destruct (vf_windows_sound_n E8 vu1_af10 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp8 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr11. intros Hin. destruct (vf_windows_sound_n E8 vu1_af10 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp8 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms10') (ms_mem ms11) sp0 (-345) (proj1 (proj2 (proj2 VI10')))
(vf_band_present_n W E8 vu1_st11 ms11 sp0 (-345) HS11 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp8 ltac:(img_lia))).
intros a Ha. img_apply HF11. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E8 vu1_af10 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp8 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear VI10' HF11 HFr11.
eapply (SRr_srealizes tfxsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms11) (v_jalr (getr (ms_regs ms11) 1) 0) (ms_mem ms11) (seg_rom tfxsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | img_try (img_exact HAI11) | ].
{ eapply (SRr_ret_at tfxsegs tfxmusl_tbl tfxmusl_tbl_ok Hwx W E8); [img_try (img_exact HS11) | img_refl | img_try ((try img_inst; img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb. split; [img_refl|]. exists mat'. img_refl. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VI11 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS11 (1%bv : bv 5) Q1.
rewrite OLD8, OLD7, OLD6, OLD5, OLD3, OLD2, OLD1 in Q1 by (img_try ((img_case; cbv); img_lia)). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfxsegs (w_H W) E8 _ _ 10 HS11) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := img_ev constr:(v) in img_change v with v' in Q10 end.
rewrite denot_lit_U, !U_SAlu, !U_SLit in Q10. cbn [zalu_raw] in Q10. img_change (zcanon 0) with 0 in Q10.
rewrite !Z.lor_0_l, U_off in Q10 by (img_try (rewrite A70_8; unfold M64; img_lia)). rewrite A70_8, !(zcanon_id (L + 14)) in Q10 by (img_try (unfold M64; img_lia)).
replace (v_jalr (getr (ms_regs ms11) 1) 0) with (w64 (raZ regs))
by (img_try (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra)).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat9 md) (with_vm_backing (m_vm_lazy md) matR md))
by (img_try (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat9 md); img_apply with_vm_backing_same)).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
img_apply (HK (ms_regs ms11) (ms_mem ms11) (with_vm_backing (m_vm_lazy md) matR md)).
* img_apply (al_frame _ _ LAWS ly S W (ms_mem ms11) _ (ms_mem ms11) _ HAR9); [img_try (intros; img_refl) | img_try (intros a Hv; img_exact Hv) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_exact (YE0v.hs_kept_refl _ _))].
* img_exact (aregs_preserved_of_st_ok _ E8 _ _ regs [Z_to_bv 64 s; Z_to_bv 64 cval] HS11 HAE8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
* img_apply with_vm_backing_same.
* rewrite Q10. img_refl.
* destruct HS11 as (_ & _ & _ & _ & _ & _ & _ & Hmem9 & _).
unfold stderr_after_vfprintf, file_is, stderr_fields_after_vf.
repeat img_apply Forall_cons; try img_apply Forall_nil;
(eapply (val_mem_of_lit E8 (mrestrict (w_H W) (ms_mem ms11)) (ss_mem vu1_st11) _ _ _ Hmem9); (try img_inst; img_case; vm_compute); img_refl).
* img_exact Hfr9.
* img_exact Hpm9.
* img_exact HAIR.
Qed.
Theorem tfx_vfprintf_usage_A2 : forall ly S (W : world tfxsegs) regs mem md ch ap s (str : list byte) L cval T,
ecall_pre tfxsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_usage -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfxsegs (mrestrict (w_H W) mem) ap 8 s ->
L = Z.of_nat (length str) -> 67 <= L -> L <= 73 ->
1 <= s -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= spZ regs - VF_STK \/ spZ regs <= s) ->
(s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) -> amem_range s (L + 1) ->
vf_tail W mem s L -> mconsts_view W mem ->
vf_str W mem s str ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF s (L + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) s (L + 1) ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF FMT_usage 17 ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) FMT_usage 17 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfxsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfxsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 (L + 14) ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vf_file a -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfxsegs (w_H W) (w_A W) md' ->
srealizes tfxsegs (cfg_at tfxsegs (raZ regs) regs' mem' md') T) ->
srealizes tfxsegs (cfg_at tfxsegs A_vfprintf regs mem md)
(t_emit (map (WriteEv ch) (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2)) T).
Proof.
intros ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HL HLlo HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
assert (HFF : F_STDERR = (681808 + D_10f0)) by img_refl. assert (HFS : FILE_SZ = 232) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (img_try (rewrite KHI; img_lia)).
assert (Hsp47 : sp0 <= 2 ^ 47) by img_lia.
assert (HLlen : length str = Z.to_nat L) by img_lia.
unfold cfg_at. img_change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vf_entry W regs mem FMT_usage (SOff 32 0) ap s cval Hsp44 Hsp47 Hal16
ltac:(img_try (intros a Ha; img_apply Hpres; img_exact Ha)) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg ltac:(img_lia)
HFP Hgot Hcan Hcv Hro ltac:(img_try (cbn [sv_denot]; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl))) as HS0.
img_change (ss_vf FMT_usage (SOff 32 0)) with vu0 in HS0.
remember (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (img_try (intros i r Hi; (subst E0; cbv beta); img_exact (ew_Ereg_nat regs _ i r Hi))).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); img_refl)).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (img_try (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); img_exact Hgp)).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (img_try (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); img_exact Htp)).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (img_try (rewrite (EE 12%nat (12%bv : bv 5) eq_refl), Ha2; img_apply unsigned_lit_small; img_lia)).
assert (A32_0 : bv_unsigned (ew E0 32) = s) by (img_try (rewrite HE0, (ew_Ereg_extra regs _ 0); cbn [nth]; img_apply unsigned_lit_small; img_lia)).
assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E0) by (img_try (rewrite HE0; split; [img_try (intros i Hi; img_refl) | img_refl])).
clear HE0 EE.
pose proof (VI_init B ly S W sp0 mem md HAR Hpres) as VI0.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E0 vu0 vu_st1 _ _ _ HS0 vu_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VI1 : VI B ly S W sp0 mem md (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms1) mat1 VI0) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin); tauto.
- img_apply (vf_band_present W E0 vu_st1 ms1 sp0 HS1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VI0 HF1 HFr1.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms1) _ FMT_usage 17 (88319 + D_20) 7 VI1 Hstk Hra_f Hhull_f
ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (rewrite KHI; unfold FMT_usage; img_lia))) as [SRA1' SHU1'].
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E0 vu_st1 ms1 _ ly S sp0 vu_r01 vu_rest1 34 RA_FX OSP_FX (-352) (SLit (88319 + D_20)) ((88319 + D_20)) 7 lit_usage1
HS1 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_refl) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold OSP_FX; cbn; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (left; unfold kLowMemEnd; cbn; img_lia))
(vf_rest_ok E0 sp0 ap vu_rest1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_0 Hap1 Hap2)
(vf_rest_w E0 vu_rest1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI1) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI1))) SRA1' SHU1') HAI1).
intros W1' c1' _ HAI1' (-> & ms1' & mat1' & -> & HS1' & HAR1' & HP1' & Hfr1' & Hpm1'). cbn [cfg_model] in HAI1'.
rewrite wvb_wvb in HAI1', HAR1' |- *.
img_change (vf_after_icpt 34 vu_st1 RA_FX OSP_FX (-352) lit_usage1) with vu_af1 in HS1'.
assert (VI1' : VI B ly S W sp0 mem md (ms_mem ms1') (with_vm_backing (m_vm_lazy md) mat1' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms1) _ (ms_mem ms1') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-352) <= a < sp0 + (-352) + 7))).
- img_exact VI1.
- img_exact HAR1'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat1' mat1 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr1'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm1'. }
remember (havoc E0 34 (map (getr (ms_regs ms1')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 34)%nat -> ew E1 j = ew E0 j) by (img_try (intros j Hj; rewrite HE1; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact Usp0)).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G3_0)).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G4_0)).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G12_0)).
assert (A32_1 : bv_unsigned (ew E1 32) = s) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A32_0)).
assert (HAE1 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E1)
by (img_try (rewrite HE1; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE0)])).
clear HE1 HS1 VI1 SRA1' SHU1'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E1 vu_af1 vu_st2 _ _ _ HS1' vu_run2) HAI1').
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1'.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VI2 : VI B ly S W sp0 mem md (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms2) mat2 VI1') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin); tauto.
- img_apply (vf_band_present W E1 vu_st2 ms2 sp0 HS2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 ltac:(img_lia)). }
clear VI1' HF2 HFr2.
assert (SRA2' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms2)) SHADOW_OFF (88326 + D_20) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms2)) (88326 + D_20) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E1 vu_st2 ms2 _ ly S sp0 vu_r02 vu_rest2 50 RA_FX OSP_FX (-345) (SLit (88326 + D_20)) ((88326 + D_20)) 0 (@nil Z)
HS2 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_refl) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold OSP_FX; cbn; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (left; unfold kLowMemEnd; cbn; img_lia))
(vf_rest_ok E1 sp0 ap vu_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_1 Hap1 Hap2)
(vf_rest_w E1 vu_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI2) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI2))) SRA2' SHU2') HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
img_change (vf_after_icpt 50 vu_st2 RA_FX OSP_FX (-345) (@nil Z)) with vu_af2 in HS2'.
assert (VI2' : VI B ly S W sp0 mem md (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- img_exact VI2.
- img_exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr2'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm2'. }
remember (havoc E1 50 (map (getr (ms_regs ms2')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 50)%nat -> ew E2 j = ew E1 j) by (img_try (intros j Hj; rewrite HE2; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact Usp1)).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G3_1)).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G4_1)).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G12_1)).
assert (A32_2 : bv_unsigned (ew E2 32) = s) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A32_1)).
assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E2)
by (img_try (rewrite HE2; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE1)])).
clear HE2 HS2 VI2 SRA2' SHU2'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E2 vu_af2 vu_st3 _ _ _ HS2' vu_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VI3 : VI B ly S W sp0 mem md (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms3) mat3 VI2') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin); tauto.
- img_apply (vf_band_present W E2 vu_st3 ms3 sp0 HS3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 ltac:(img_lia)). }
clear VI2' HF3 HFr3.
assert (STR3 : vf_str W (ms_mem ms3) s str).
{ img_apply (vf_str_xfer W mem); [img_try (img_exact HSTR)|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI3)))); [img_lia | img_try (unfold vf_band; img_lia) | img_try (unfold vf_file; img_lia)]. }
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms3) _ s (L + 1) s (L + 1) VI3 Hstk Hra_s Hhull_s
ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (rewrite KHI; img_lia))) as [SRA3' SHU3'].
pose proof (vf_tail_xfer W mem (ms_mem ms3) sp0 s L Hstail (proj1 (proj2 (proj2 (proj2 VI3)))) Hal16 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) Hsband Hsfile) as TAIL3.
pose proof (mconsts_view_xfer W mem (ms_mem ms3) sp0 Hromv (proj1 (proj2 (proj2 (proj2 VI3)))) Hsp44) as ROM3.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_strnlen B ASTRNLEN W E2 vu_st3 ms3 _ ly S sp0 vu_r03 vu_rest3 66 RA_SN OSP_SN (SOff 32 0) s INT_MAX L
HS3 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(img_try (cbn [sv_denot]; rewrite Z.add_0_r, <- A32_2, Z_to_bv_bv_unsigned; img_refl)) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_SN; img_lia)) ltac:(img_try (unfold OSP_SN; img_lia)) ltac:(img_try (unfold RA_SN; img_lia)) ltac:(img_refl)
ltac:(img_try (unfold INT_MAX; img_lia)) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (unfold INT_MAX; img_lia)) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (unfold OSP_SN; img_lia))
(vf_rest_ok E2 sp0 ap vu_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_2 Hap1 Hap2)
(vf_rest_w E2 vu_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VI3)))
ltac:(img_try (rewrite HL; img_apply (vf_str_first_byte W _ s str INT_MAX STR3); unfold INT_MAX; img_lia))
ltac:(img_try (intros a Ha; img_apply (vf_str_readable W _ s str STR3); img_lia))
Hams SRA3' (SHU3' ltac:(img_lia)) TAIL3 ROM3) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & HL3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
img_change (vf_after_icpt 66 vu_st3 RA_SN OSP_SN 0 []) with vu_af3 in HS3'.
assert (VI3' : VI B ly S W sp0 mem md (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms3) _ (ms_mem ms3') _
(fun a => sp0 + OSP_SN - 2 * ESTACK <= a < sp0 + OSP_SN)).
- img_exact VI3.
- img_exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_SN in *. img_lia.
- intros a Hr Hna. img_apply Hfr3'; [img_try (img_exact Hr) | img_try (img_exact Hna)].
- img_exact Hpm3'. }
remember (havoc E2 66 (map (getr (ms_regs ms3')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 66)%nat -> ew E3 j = ew E2 j) by (img_try (intros j Hj; rewrite HE3; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact Usp2)).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G3_2)).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G4_2)).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G12_2)).
assert (A32_3 : bv_unsigned (ew E3 32) = s) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A32_2)).
assert (HAE3 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E3)
by (img_try (rewrite HE3; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE2)])).
assert (A70_3 : bv_unsigned (ew E3 70) = L).
{ rewrite HE3, (ew_havoc_new E2 66 _ 4 (w64 0)) by (img_try (cbn; img_lia)). unfold CLOB. cbn [nth map]. rewrite HL3'. img_apply unsigned_lit_small. img_lia. }
clear HE3 HS3 VI3 SRA3' SHU3' STR3.
pose proof (st_ok_add_fact E3 vu_af3 _ 70 67 73 HS3' eq_refl ltac:(img_try (rewrite A70_3; img_lia))) as HS3f.
img_change (vf_add_fact vu_af3 70 (mkAF 67 73 0)) with vu2_af3f in HS3f. clear HS3'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E3 vu2_af3f vu2_st4 _ _ _ HS3f vu2_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3f.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VI4 : VI B ly S W sp0 mem md (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms4) mat4 VI3') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF4. intros Hin. destruct (vf_windows_sound E3 vu2_af3f sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr4. intros Hin. destruct (vf_windows_sound E3 vu2_af3f sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- img_apply (vf_band_present W E3 vu2_st4 ms4 sp0 HS4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 ltac:(img_lia)). }
clear VI3' HF4 HFr4.
assert (STR4 : vf_str W (ms_mem ms4) s str).
{ img_apply (vf_str_xfer W mem); [img_try (img_exact HSTR)|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI4)))); [img_lia | img_try (unfold vf_band; img_lia) | img_try (unfold vf_file; img_lia)]. }
assert (R11_4 : getr (ms_regs ms4) 11 = Z_to_bv 64 (s + L)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E3 _ _ 11 HS4).
match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite denot_lit_U, U_add_off_atom by (img_try (rewrite ?A32_3, ?A70_3; unfold M64; img_lia)). rewrite A32_3, A70_3. f_equal. img_lia. }
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_lbu_nul W E3 vu2_st4 ms4 _ 82 (s + L) HS4 eq_refl eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) R11_4 ltac:(img_lia)
ltac:(img_try (rewrite HL; img_exact (proj1 (proj2 STR4))))) HAI4).
intros W4l c4l _ HAI4l (-> & ms4l & mat4l & -> & HS4l & Hmm4l). cbn [cfg_model] in HAI4l. rewrite ?wvb_wvb in HAI4l |- *.
img_change (set_regs_pc vu2_st4 [((12%bv : bv 5), SLit 0)] (0x984a0 + D_10ec)) with vu2_af4 in HS4l.
assert (VI4l : VI B ly S W sp0 mem md (ms_mem ms4l) (with_vm_backing (m_vm_lazy md) mat4l md)).
{ rewrite Hmm4l. pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms4) mat4l VI4) as VR.
rewrite ?wvb_wvb in VR. img_apply VR; [img_try (intros; img_refl) | img_try (intros; img_refl) | img_try (img_exact (proj1 (proj2 (proj2 VI4))))]. }
clear VI4 HS4 STR4 R11_4.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E3 vu2_af4 vu2_st5 _ _ _ HS4l vu2_run5) HAI4l).
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4l.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VI5 : VI B ly S W sp0 mem md (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms5) mat5 VI4l) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF5. intros Hin. destruct (vf_windows_sound E3 vu2_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr5. intros Hin. destruct (vf_windows_sound E3 vu2_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- img_apply (vf_band_present W E3 vu2_st5 ms5 sp0 HS5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 ltac:(img_lia)). }
clear VI4l HF5 HFr5.
assert (SRA5' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms5)) SHADOW_OFF (68452 + D_20) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU5' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms5)) (68452 + D_20) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E3 vu2_st5 ms5 _ ly S sp0 vu2_r05 vu2_rest5 82 RA_FX OSP_FX (-345) (SLit (68452 + D_20)) ((68452 + D_20)) 0 (@nil Z)
HS5 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp3 G3_3 G4_3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_refl) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold OSP_FX; cbn; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (left; unfold kLowMemEnd; cbn; img_lia))
(vf_rest_ok E3 sp0 ap vu2_rest5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_3 Hap1 Hap2)
(vf_rest_w E3 vu2_rest5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI5) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI5))) SRA5' SHU5') HAI5).
intros W5' c5' _ HAI5' (-> & ms5' & mat5' & -> & HS5' & HAR5' & HP5' & Hfr5' & Hpm5'). cbn [cfg_model] in HAI5'.
rewrite wvb_wvb in HAI5', HAR5' |- *.
img_change (vf_after_icpt 82 vu2_st5 RA_FX OSP_FX (-345) (@nil Z)) with vu2_af5 in HS5'.
assert (VI5' : VI B ly S W sp0 mem md (ms_mem ms5') (with_vm_backing (m_vm_lazy md) mat5' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms5) _ (ms_mem ms5') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- img_exact VI5.
- img_exact HAR5'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat5' mat5 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr5'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm5'. }
remember (havoc E3 82 (map (getr (ms_regs ms5')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 82)%nat -> ew E5 j = ew E3 j) by (img_try (intros j Hj; rewrite HE5; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact Usp3)).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G3_3)).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G4_3)).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G12_3)).
assert (A32_5 : bv_unsigned (ew E5 32) = s) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact A32_3)).
assert (A70_5 : bv_unsigned (ew E5 70) = L) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact A70_3)).
assert (HAE5 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E5)
by (img_try (rewrite HE5; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE3)])).
clear HE5 HS5 VI5 SRA5' SHU5'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E5 vu2_af5 vu2_st6 _ _ _ HS5' vu2_run6) HAI5').
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5'.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VI6 : VI B ly S W sp0 mem md (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms6) mat6 VI5') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF6. intros Hin. destruct (vf_windows_sound E5 vu2_af5 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr6. intros Hin. destruct (vf_windows_sound E5 vu2_af5 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin); tauto.
- img_apply (vf_band_present W E5 vu2_st6 ms6 sp0 HS6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 ltac:(img_lia)). }
clear VI5' HF6 HFr6.
assert (STR6 : vf_str W (ms_mem ms6) s str).
{ img_apply (vf_str_xfer W mem); [img_try (img_exact HSTR)|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI6)))); [img_lia | img_try (unfold vf_band; img_lia) | img_try (unfold vf_file; img_lia)]. }
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms6) _ s (L + 1) s L VI6 Hstk Hra_s Hhull_s
ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (rewrite KHI; img_lia))) as [SRA6' SHU6'].
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy_sym B LAWS AMEMCPY W E5 vu2_st6 ms6 _ ly S sp0 vu2_r06 vu2_rest6 98 RA_FX OSP_FX (-345) (-272)
(SOff 2 (-345)) (SOff 32 0) (SOff 70 0) (-345) (s) (L)
HS6 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp5 G3_5 G4_5 eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_try (cbn; img_lia))
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(img_try (cbn [sv_denot]; rewrite Usp5; img_refl)) eq_refl ltac:(img_try (cbn [sv_denot]; rewrite Z.add_0_r, A32_5; img_refl)) eq_refl ltac:(img_try (cbn [sv_denot]; rewrite Z.add_0_r, A70_5; img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_lia)
ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_lia) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_lia) ltac:(img_try (destruct Hams as [Hams'|[Hams' Hams'']]; [img_try (left; img_lia) | img_try (right; img_lia)]))
(vf_rest_ok E5 sp0 ap vu2_rest6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_5 Hap1 Hap2)
(vf_rest_w E5 vu2_rest6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI6) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI6)))
ltac:(img_try (intros a Ha; img_apply (vf_str_readable W _ s str STR6); img_lia)) SRA6' SHU6') HAI6).
intros W6' c6' _ HAI6' (-> & ms6' & mat6' & -> & HS6' & HAR6' & HP6' & Heff6' & Hfr6' & Hpm6'). cbn [cfg_model] in HAI6'.
rewrite wvb_wvb in HAI6', HAR6' |- *.
img_change (vf_after_icpt_n 98 vu2_st6 RA_FX OSP_FX (-345) (-272)) with vu2_af6 in HS6'.
assert (VI6' : VI B ly S W sp0 mem md (ms_mem ms6') (with_vm_backing (m_vm_lazy md) mat6' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms6) _ (ms_mem ms6') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + (L)))).
- img_exact VI6.
- img_exact HAR6'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat6' mat6 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr6'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm6'. }
assert (STRBUF6' : forall i, (i < length str)%nat -> aview tfxsegs (w_H W) (ms_mem ms6') (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite (Heff6' (Z.of_nat i)) by img_lia. img_apply (proj1 STR6). img_exact Hi. }
remember (havoc E5 98 (map (getr (ms_regs ms6')) CLOB)) as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 98)%nat -> ew E6 j = ew E5 j) by (img_try (intros j Hj; rewrite HE6; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact Usp5)).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G3_5)).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G4_5)).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G12_5)).
assert (A32_6 : bv_unsigned (ew E6 32) = s) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact A32_5)).
assert (A70_6 : bv_unsigned (ew E6 70) = L) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact A70_5)).
assert (HAE6 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E6)
by (img_try (rewrite HE6; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE5)])).
clear HE6 HS6 VI6 SRA6' SHU6' Heff6'.
clear STR6.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E6 vu2_af6 vu2_st7 _ _ _ HS6' vu2_run7) HAI6').
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7. clear HS6'.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VI7 : VI B ly S W sp0 mem md (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms7) mat7 VI6') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF7. intros Hin. destruct (vf_windows_sound_n E6 vu2_af6 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr7. intros Hin. destruct (vf_windows_sound_n E6 vu2_af6 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms6') (ms_mem ms7) sp0 (-345) (proj1 (proj2 (proj2 VI6')))
(vf_band_present_n W E6 vu2_st7 ms7 sp0 (-345) HS7 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 ltac:(img_lia))).
intros a Ha. img_apply HF7. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_af6 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
assert (STRBUF7 : forall i, (i < length str)%nat -> aview tfxsegs (w_H W) (ms_mem ms7) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF6' i Hi). img_apply aview_eq_of. img_apply HFr7. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_af6 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear VI6' HF7 HFr7 STRBUF6'.
pose proof (st_ok_add_cond_neg tfxsegs E6 vu2_st7 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7) HS7 ltac:(img_try (rewrite branch_geu_U, U_neg_off, U_SLit by (rewrite A70_6; unfold M64; img_lia); rewrite A70_6; img_change (zcanon 7) with 7; img_apply Bool.negb_false_iff; img_apply Z.ltb_lt; img_lia))) as HS7c.
img_change (YQ09.add_cond vu2_st7 (mkAC (neg_bc BC_GEU) (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7))) with vu2_st7c in HS7c. clear HS7.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E6 vu2_st7c vu2_st8 _ _ _ HS7c vu2_run8) HAI7).
intros W8 c8 _ HAI8 (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [cfg_model] in HAI8. clear HS7c.
rewrite ?wvb_wvb in HAI8 |- *.
assert (VI8 : VI B ly S W sp0 mem md (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms8) mat8 VI7) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF8. intros Hin. destruct (vf_windows_sound_n E6 vu2_st7c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr8. intros Hin. destruct (vf_windows_sound_n E6 vu2_st7c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms7) (ms_mem ms8) sp0 (-345) (proj1 (proj2 (proj2 VI7)))
(vf_band_present_n W E6 vu2_st8 ms8 sp0 (-345) HS8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 ltac:(img_lia))).
intros a Ha. img_apply HF8. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_st7c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
assert (STRBUF8 : forall i, (i < length str)%nat -> aview tfxsegs (w_H W) (ms_mem ms8) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF7 i Hi). img_apply aview_eq_of. img_apply HFr8. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_st7c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear VI7 HF8 HFr8 STRBUF7.
pose proof (st_ok_add_cond_neg tfxsegs E6 vu2_st8 _ BC_EQ (SAlu ALU_ADD (SOff 2 (-345)) (SOff 70 0)) (SOff 2 (-352)) HS8 ltac:(img_try (rewrite branch_eq_U, U_add_off_atom, U_off by (rewrite ?Usp6, ?A70_6; unfold M64; img_lia); rewrite Usp6, A70_6; img_apply Z.eqb_neq; img_lia))) as HS8c.
img_change (YQ09.add_cond vu2_st8 (mkAC (neg_bc BC_EQ) (SAlu ALU_ADD (SOff 2 (-345)) (SOff 70 0)) (SOff 2 (-352)))) with vu2_st8c in HS8c. clear HS8.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E6 vu2_st8c vu2_st9 _ _ _ HS8c vu2_run9) HAI8).
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9. clear HS8c.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VI9 : VI B ly S W sp0 mem md (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms9) mat9 VI8) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF9. intros Hin. destruct (vf_windows_sound_n E6 vu2_st8c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr9. intros Hin. destruct (vf_windows_sound_n E6 vu2_st8c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms8) (ms_mem ms9) sp0 (-345) (proj1 (proj2 (proj2 VI8)))
(vf_band_present_n_ecall W E6 vu2_st9 ms9 sp0 (-345) HS9 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 ltac:(img_lia))).
intros a Ha. img_apply HF9. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_st8c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
assert (STRBUF9 : forall i, (i < length str)%nat -> aview tfxsegs (w_H W) (ms_mem ms9) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF8 i Hi). img_apply aview_eq_of. img_apply HFr9. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_st8c sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear VI8 HF9 HFr9 STRBUF8.
rewrite (app_assoc (map (Z_to_bv 8) lit_usage1) str (map (Z_to_bv 8) lit_usage2)).
pose proof HS9 as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & Hregs9 & Hmem9 & HG9). cbn [restrict ms_mem] in Hmem9.
pose proof (lit_buf_sound tfxsegs E6 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem vu2_st9) (SLit (F_STDERR + 120)) 4 [2; 0; 0; 0] Hmem9
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as Hfdrd. cbn [sv_denot] in Hfdrd.
assert (LIT1AV9 : forall i, (i < 7)%nat -> aview tfxsegs (w_H W) (ms_mem ms9) (sp0 + (-352) + Z.of_nat i) = Some (nth i lit_usage1 0)).
{ intros i Hi. img_apply (lit_buf_aview W E6 (ms_mem ms9) (ss_mem vu2_st9) (SOff 2 (-352)) (sp0 + (-352)) 7 lit_usage1 Hmem9 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try (cbn [sv_denot]; rewrite Usp6; img_refl)) lit_usage1_range i Hi). }
pose proof (lit_buf_sound tfxsegs E6 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem vu2_st9) (SLit (88328 + D_20)) 7 lit_usage2 Hmem9
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as Hl2rd.
eapply (srz_sym_stdio_writev2 W E6 vu2_st9 ms9 _ (Z_to_bv 64 2) ch 0 2 (-1024) F_STDERR _ (SOff 2 (-352)) (SOff 70 7) (SLit (88328 + D_20)) (SLit 7)
((map (Z_to_bv 8) lit_usage1 ++ str)) (map (Z_to_bv 8) lit_usage2) (map (Z_to_bv 8) [2; 0; 0; 0]) 114 T HAI9 HS9 eq_refl eq_refl eq_refl).
- img_refl.
- eapply fdchan_sbm; [img_try (img_exact Hch) | img_try (img_apply with_vm_backing_same)].
- img_refl.
- img_case; vm_compute. all: img_refl.
- match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite iovcnt_val, U_add_off_atom, U_off by (img_try (rewrite ?Usp6, ?A70_6; unfold M64; img_lia)). rewrite (proj2 (Z.eqb_neq _ _)) by img_lia. img_refl.
- match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite iovcnt_val', U_add_off_atom, U_off by (img_try (rewrite ?Usp6, ?A70_6; unfold M64; img_lia)). rewrite (proj2 (Z.eqb_neq _ _)) by img_lia. img_refl.
- img_refl.
- img_refl.
- img_refl.
- match goal with |- U _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite U_SLit, !U_off by (img_try (rewrite A70_6; unfold M64; img_lia)). rewrite A70_6. img_change (zcanon 7) with 7. img_lia.
- match goal with |- U _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end. rewrite U_SLit. img_refl.
- img_refl.
- img_refl.
- cbn. img_lia. - cbn. img_lia. - cbn. img_lia. - cbn. img_lia.
- img_case; vm_compute. all: img_refl.
-
rewrite word_to_nat_U, U_off by (img_try (rewrite A70_6; unfold M64; img_lia)). cbn [sv_denot]. rewrite Usp6, A70_6.
replace (Z.to_nat (L + 7)) with (length lit_usage1 + length str + @length Z [])%nat by (img_try (rewrite HLlen; cbn; img_lia)).
replace (map (Z_to_bv 8) lit_usage1 ++ str) with (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) []) by (img_try (cbn [map]; rewrite app_nil_r; img_refl)).
img_apply (rdn_cat3 (w_H W) (ms_mem ms9) (sp0 + (-352)) lit_usage1 str [] lit_usage1_range ltac:(img_try (constructor)) LIT1AV9).
+ intros i Hi. replace (sp0 + (-352) + Z.of_nat (length lit_usage1) + Z.of_nat i) with (sp0 + (-345) + Z.of_nat i) by (img_try (cbn; img_lia)). img_apply STRBUF9. img_exact Hi.
+ intros i Hi. cbn in Hi. img_lia.
-   img_change (word_to_nat (sv_denot E6 (SLit 7))) with 7%nat. img_exact Hl2rd.
- rewrite U_SLit, U_off by (img_try (rewrite A70_6; unfold M64; img_lia)). rewrite A70_6. img_change (zcanon 7) with 7. img_lia.
- rewrite !U_off by (img_try (rewrite ?Usp6, ?A70_6; unfold M64; img_lia)). rewrite Usp6, A70_6. img_lia.
- rewrite !U_off by (img_try (rewrite ?Usp6, ?A70_6; unfold M64; img_lia)). rewrite Usp6, A70_6. img_lia.
- rewrite !U_SLit. img_change (zcanon (88328 + D_20)) with (88328 + D_20). img_change (zcanon 7) with 7. img_lia.
- rewrite !U_SLit. img_change (zcanon (88328 + D_20)) with (88328 + D_20). img_change (zcanon 7) with 7. rewrite Usp6. img_lia.
- img_exact Hfdrd.
- img_case; vm_compute. all: img_refl.
- unfold F_STDERR. img_lia.
- unfold F_STDERR. img_lia.
- rewrite Usp6. unfold F_STDERR. img_lia.
- rewrite Usp6. img_lia.
- rewrite Usp6. img_lia.
- img_case; vm_compute. all: img_refl.
-
intros ms9' ws9' mat9' HS9' HF9' HFr9' HAI9'. rewrite ?wvb_wvb in HAI9' |- *.
img_change (wl_after vu2_st9 0 (-1024) 114) with vu2_af9 in HS9'.
remember (havoc E6 114 ws9') as E7 eqn:HE7.
assert (OLD7 : forall j, (j < 114)%nat -> ew E7 j = ew E6 j) by (img_try (intros j Hj; rewrite HE7; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp7 : bv_unsigned (ew E7 2) = sp0) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact Usp6)).
assert (G3_7 : ew E7 3 = w64 (as_gp B)) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G3_6)).
assert (G4_7 : ew E7 4 = w64 (as_tp B)) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G4_6)).
assert (G12_7 : bv_unsigned (ew E7 12) = ap) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G12_6)).
assert (A32_7 : bv_unsigned (ew E7 32) = s) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact A32_6)).
assert (A70_7 : bv_unsigned (ew E7 70) = L) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact A70_6)).
assert (HAE7 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E7)
by (img_try (rewrite HE7; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE6)])).
assert (VI9' : VI B ly S W sp0 mem md (ms_mem ms9') (with_vm_backing (m_vm_lazy md) mat9' md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms9') mat9' VI9) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF9'. intros Hin. destruct (vf_windows_sound_n E6 vu2_st9 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr9'. intros Hin. destruct (vf_windows_sound_n E6 vu2_st9 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms9) (ms_mem ms9') sp0 (-345) (proj1 (proj2 (proj2 VI9)))
(vf_band_present_n W E7 vu2_af9 ms9' sp0 (-345) HS9' ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 ltac:(img_lia))).
intros a Ha. img_apply HF9'. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_st9 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear HE7 HS9 VI9 Hfdrd Hregs9 Hmem9 HG9 HF9' HFr9'.
clear STRBUF9 LIT1AV9 Hl2rd.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E7 vu2_af9 vu2_st10 _ _ _ HS9' vu2_run10) HAI9').
intros W10 c10 _ HAI10 (-> & ms10 & mat10 & -> & HS10 & HF10 & HFr10). cbn [cfg_model] in HAI10. clear HS9'.
rewrite ?wvb_wvb in HAI10 |- *.
assert (VI10 : VI B ly S W sp0 mem md (ms_mem ms10) (with_vm_backing (m_vm_lazy md) mat10 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms10) mat10 VI9') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF10. intros Hin. destruct (vf_windows_sound_n E7 vu2_af9 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr10. intros Hin. destruct (vf_windows_sound_n E7 vu2_af9 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms9') (ms_mem ms10) sp0 (-345) (proj1 (proj2 (proj2 VI9')))
(vf_band_present_n_ecall W E7 vu2_st10 ms10 sp0 (-345) HS10 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 ltac:(img_lia))).
intros a Ha. img_apply HF10. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E7 vu2_af9 sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear VI9' HF10 HFr10.
eapply (srz_sym_writev_empty W E7 vu2_st10 ms10 _ (Z_to_bv 64 2) ch 0 2 _ (Some 2%nat) (-456) (SLit 0) (SLit 0) T HAI10 HS10 eq_refl eq_refl).
+ img_refl.
+ eapply fdchan_sbm; [img_try (img_exact Hch) | img_try (img_apply with_vm_backing_same)].
+ img_refl.
+ match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite iovcnt_val. rewrite Z.eqb_refl. img_refl.
+ match goal with |- U _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite U_off by (img_try (rewrite Usp7; unfold M64; img_lia)). cbn [base_val]. img_refl.
+ img_case; vm_compute. all: img_refl.
+ rewrite U_SLit. img_refl.
+ img_refl.
+ img_refl.
+ cbn. img_lia.
+ cbn. img_lia.
+ cbn [base_val]. rewrite Usp7. img_lia.
+ cbn [base_val]. rewrite Usp7. img_lia.
+ cbn [base_val]. rewrite Usp7. img_lia.
+ match goal with |- U _ ?x <= _ => let x' := img_ev constr:(x) in img_change x with x' end;
first [ rewrite U_off by (img_try (rewrite Usp7; unfold M64; img_lia)); cbn [base_val]; rewrite Usp7; img_lia | rewrite U_SLit; (try img_inst; img_case; vm_compute); discriminate | rewrite U_SLit; cbn; img_lia ].
+ intros ms10r mat10r HS10r Hmm10r HAI10r. rewrite ?wvb_wvb in HAI10r |- *.
img_change (resume vu2_st10 (SLit 0) (ss_mem vu2_st10) (ss_facts vu2_st10)) with vu2_st10r in HS10r.
assert (VI10r : VI B ly S W sp0 mem md (ms_mem ms10r) (with_vm_backing (m_vm_lazy md) mat10r md)).
{ rewrite Hmm10r. pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms10) mat10r VI10) as VR.
rewrite ?wvb_wvb in VR. img_apply VR; [img_try (intros; img_refl) | img_try (intros; img_refl) | img_try (img_exact (proj1 (proj2 (proj2 VI10))))]. }
clear VI10 HS10.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E7 vu2_st10r vu2_st11 _ _ _ HS10r vu2_run11) HAI10r).
intros W11 c11 _ HAI11 (-> & ms11 & mat11 & -> & HS11 & HF11 & HFr11). cbn [cfg_model] in HAI11. clear HS10r.
rewrite ?wvb_wvb in HAI11 |- *.
assert (VI11 : VI B ly S W sp0 mem md (ms_mem ms11) (with_vm_backing (m_vm_lazy md) mat11 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms11) mat11 VI10r) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF11. intros Hin. destruct (vf_windows_sound_n E7 vu2_st10r sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- intros x Hx1 Hx2. img_apply HFr11. intros Hin. destruct (vf_windows_sound_n E7 vu2_st10r sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_try (img_apply Hx1; unfold vf_band; img_lia) | img_try (tauto)].
- apply (vf_band_present_gap W (ms_mem ms10r) (ms_mem ms11) sp0 (-345) (proj1 (proj2 (proj2 VI10r)))
(vf_band_present_n W E7 vu2_st11 ms11 sp0 (-345) HS11 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 ltac:(img_lia))).
intros a Ha. img_apply HF11. rewrite unsigned_lit_small by img_lia. intros Hin.
destruct (vf_windows_sound_n E7 vu2_st10r sp0 (-345) _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin) as [Hw|Hw]; [img_lia | img_try (unfold vf_file in Hw; img_lia)]. }
clear VI10r HF11 HFr11.
eapply (SRr_srealizes tfxsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms11) (v_jalr (getr (ms_regs ms11) 1) 0) (ms_mem ms11) (seg_rom tfxsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | img_try (img_exact HAI11) | ].
{ eapply (SRr_ret_at tfxsegs tfxmusl_tbl tfxmusl_tbl_ok Hwx W E7); [img_try (img_exact HS11) | img_refl | img_try ((try img_inst; img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb. split; [img_refl|]. exists mat'. img_refl. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VI11 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS11 (1%bv : bv 5) Q1.
rewrite OLD7, OLD6, OLD5, OLD3, OLD2, OLD1 in Q1 by (img_try ((img_case; cbv); img_lia)). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfxsegs (w_H W) E7 _ _ 10 HS11) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := img_ev constr:(v) in img_change v with v' in Q10 end.
rewrite denot_lit_U, !U_SAlu, !U_SLit in Q10. cbn [zalu_raw] in Q10. img_change (zcanon 0) with 0 in Q10.
rewrite !Z.lor_0_l, U_off in Q10 by (img_try (rewrite A70_7; unfold M64; img_lia)). rewrite A70_7, !(zcanon_id (L + 14)) in Q10 by (img_try (unfold M64; img_lia)).
replace (v_jalr (getr (ms_regs ms11) 1) 0) with (w64 (raZ regs))
by (img_try (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra)).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat9 md) (with_vm_backing (m_vm_lazy md) matR md))
by (img_try (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat9 md); img_apply with_vm_backing_same)).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
img_apply (HK (ms_regs ms11) (ms_mem ms11) (with_vm_backing (m_vm_lazy md) matR md)).
* img_apply (al_frame _ _ LAWS ly S W (ms_mem ms11) _ (ms_mem ms11) _ HAR9); [img_try (intros; img_refl) | img_try (intros a Hv; img_exact Hv) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_exact (YE0v.hs_kept_refl _ _))].
* img_exact (aregs_preserved_of_st_ok _ E7 _ _ regs [Z_to_bv 64 s; Z_to_bv 64 cval] HS11 HAE7 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
* img_apply with_vm_backing_same.
* rewrite Q10. img_refl.
* destruct HS11 as (_ & _ & _ & _ & _ & _ & _ & Hmem9 & _).
unfold stderr_after_vfprintf, file_is, stderr_fields_after_vf.
repeat img_apply Forall_cons; try img_apply Forall_nil;
(eapply (val_mem_of_lit E7 (mrestrict (w_H W) (ms_mem ms11)) (ss_mem vu2_st11) _ _ _ Hmem9); (try img_inst; img_case; vm_compute); img_refl).
* img_exact Hfr9.
* img_exact Hpm9.
* img_exact HAIR.
Qed.
Theorem tfx_vfprintf_usage_A3 : forall ly S (W : world tfxsegs) regs mem md ch ap s (str : list byte) L cval T,
ecall_pre tfxsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_usage -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfxsegs (mrestrict (w_H W) mem) ap 8 s ->
L = Z.of_nat (length str) -> 74 <= L -> L <= 33554425 ->
1 <= s -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= spZ regs - VF_STK \/ spZ regs <= s) ->
(s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) -> amem_range s (L + 1) ->
vf_tail W mem s L -> mconsts_view W mem ->
vf_str W mem s str ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF s (L + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) s (L + 1) ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF FMT_usage 17 ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) FMT_usage 17 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfxsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfxsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 (L + 14) ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vf_file a -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfxsegs (w_H W) (w_A W) md' ->
srealizes tfxsegs (cfg_at tfxsegs (raZ regs) regs' mem' md') T) ->
srealizes tfxsegs (cfg_at tfxsegs A_vfprintf regs mem md)
(t_emit (map (WriteEv ch) (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2)) T).
Proof.
intros ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HL HLlo HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
assert (HFF : F_STDERR = (681808 + D_10f0)) by img_refl. assert (HFS : FILE_SZ = 232) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (img_try (rewrite KHI; img_lia)).
assert (Hsp47 : sp0 <= 2 ^ 47) by img_lia.
assert (HLlen : length str = Z.to_nat L) by img_lia.
unfold cfg_at. img_change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vf_entry W regs mem FMT_usage (SOff 32 0) ap s cval Hsp44 Hsp47 Hal16
ltac:(img_try (intros a Ha; img_apply Hpres; img_exact Ha)) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg ltac:(img_lia)
HFP Hgot Hcan Hcv Hro ltac:(img_try (cbn [sv_denot]; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl))) as HS0.
img_change (ss_vf FMT_usage (SOff 32 0)) with vu0 in HS0.
remember (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (img_try (intros i r Hi; (subst E0; cbv beta); img_exact (ew_Ereg_nat regs _ i r Hi))).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); img_refl)).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (img_try (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); img_exact Hgp)).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (img_try (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); img_exact Htp)).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (img_try (rewrite (EE 12%nat (12%bv : bv 5) eq_refl), Ha2; img_apply unsigned_lit_small; img_lia)).
assert (A32_0 : bv_unsigned (ew E0 32) = s) by (img_try (rewrite HE0, (ew_Ereg_extra regs _ 0); cbn [nth]; img_apply unsigned_lit_small; img_lia)).
assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E0) by (img_try (rewrite HE0; split; [img_try (intros i Hi; img_refl) | img_refl])).
clear HE0 EE.
pose proof (VI_init B ly S W sp0 mem md HAR Hpres) as VI0.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E0 vu0 vu_st1 _ _ _ HS0 vu_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VI1 : VI B ly S W sp0 mem md (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms1) mat1 VI0) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin); tauto.
- img_apply (vf_band_present W E0 vu_st1 ms1 sp0 HS1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VI0 HF1 HFr1.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms1) _ FMT_usage 17 (88319 + D_20) 7 VI1 Hstk Hra_f Hhull_f
ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (rewrite KHI; unfold FMT_usage; img_lia))) as [SRA1' SHU1'].
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E0 vu_st1 ms1 _ ly S sp0 vu_r01 vu_rest1 34 RA_FX OSP_FX (-352) (SLit (88319 + D_20)) ((88319 + D_20)) 7 lit_usage1
HS1 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_refl) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold OSP_FX; cbn; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (left; unfold kLowMemEnd; cbn; img_lia))
(vf_rest_ok E0 sp0 ap vu_rest1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_0 Hap1 Hap2)
(vf_rest_w E0 vu_rest1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI1) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI1))) SRA1' SHU1') HAI1).
intros W1' c1' _ HAI1' (-> & ms1' & mat1' & -> & HS1' & HAR1' & HP1' & Hfr1' & Hpm1'). cbn [cfg_model] in HAI1'.
rewrite wvb_wvb in HAI1', HAR1' |- *.
img_change (vf_after_icpt 34 vu_st1 RA_FX OSP_FX (-352) lit_usage1) with vu_af1 in HS1'.
assert (VI1' : VI B ly S W sp0 mem md (ms_mem ms1') (with_vm_backing (m_vm_lazy md) mat1' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms1) _ (ms_mem ms1') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-352) <= a < sp0 + (-352) + 7))).
- img_exact VI1.
- img_exact HAR1'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat1' mat1 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr1'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm1'. }
remember (havoc E0 34 (map (getr (ms_regs ms1')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 34)%nat -> ew E1 j = ew E0 j) by (img_try (intros j Hj; rewrite HE1; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact Usp0)).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G3_0)).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G4_0)).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G12_0)).
assert (A32_1 : bv_unsigned (ew E1 32) = s) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A32_0)).
assert (HAE1 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E1)
by (img_try (rewrite HE1; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE0)])).
clear HE1 HS1 VI1 SRA1' SHU1'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E1 vu_af1 vu_st2 _ _ _ HS1' vu_run2) HAI1').
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1'.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VI2 : VI B ly S W sp0 mem md (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms2) mat2 VI1') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin); tauto.
- img_apply (vf_band_present W E1 vu_st2 ms2 sp0 HS2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 ltac:(img_lia)). }
clear VI1' HF2 HFr2.
assert (SRA2' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms2)) SHADOW_OFF (88326 + D_20) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms2)) (88326 + D_20) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E1 vu_st2 ms2 _ ly S sp0 vu_r02 vu_rest2 50 RA_FX OSP_FX (-345) (SLit (88326 + D_20)) ((88326 + D_20)) 0 (@nil Z)
HS2 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_refl) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold OSP_FX; cbn; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (left; unfold kLowMemEnd; cbn; img_lia))
(vf_rest_ok E1 sp0 ap vu_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_1 Hap1 Hap2)
(vf_rest_w E1 vu_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI2) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI2))) SRA2' SHU2') HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
img_change (vf_after_icpt 50 vu_st2 RA_FX OSP_FX (-345) (@nil Z)) with vu_af2 in HS2'.
assert (VI2' : VI B ly S W sp0 mem md (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- img_exact VI2.
- img_exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr2'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm2'. }
remember (havoc E1 50 (map (getr (ms_regs ms2')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 50)%nat -> ew E2 j = ew E1 j) by (img_try (intros j Hj; rewrite HE2; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact Usp1)).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G3_1)).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G4_1)).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G12_1)).
assert (A32_2 : bv_unsigned (ew E2 32) = s) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A32_1)).
assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E2)
by (img_try (rewrite HE2; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE1)])).
clear HE2 HS2 VI2 SRA2' SHU2'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E2 vu_af2 vu_st3 _ _ _ HS2' vu_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VI3 : VI B ly S W sp0 mem md (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms3) mat3 VI2') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin); tauto.
- img_apply (vf_band_present W E2 vu_st3 ms3 sp0 HS3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 ltac:(img_lia)). }
clear VI2' HF3 HFr3.
assert (STR3 : vf_str W (ms_mem ms3) s str).
{ img_apply (vf_str_xfer W mem); [img_try (img_exact HSTR)|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI3)))); [img_lia | img_try (unfold vf_band; img_lia) | img_try (unfold vf_file; img_lia)]. }
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms3) _ s (L + 1) s (L + 1) VI3 Hstk Hra_s Hhull_s
ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (rewrite KHI; img_lia))) as [SRA3' SHU3'].
pose proof (vf_tail_xfer W mem (ms_mem ms3) sp0 s L Hstail (proj1 (proj2 (proj2 (proj2 VI3)))) Hal16 ltac:(img_lia) ltac:(img_lia) ltac:(img_lia) Hsband Hsfile) as TAIL3.
pose proof (mconsts_view_xfer W mem (ms_mem ms3) sp0 Hromv (proj1 (proj2 (proj2 (proj2 VI3)))) Hsp44) as ROM3.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_strnlen B ASTRNLEN W E2 vu_st3 ms3 _ ly S sp0 vu_r03 vu_rest3 66 RA_SN OSP_SN (SOff 32 0) s INT_MAX L
HS3 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(img_try (cbn [sv_denot]; rewrite Z.add_0_r, <- A32_2, Z_to_bv_bv_unsigned; img_refl)) ltac:(img_refl)
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_SN; img_lia)) ltac:(img_try (unfold OSP_SN; img_lia)) ltac:(img_try (unfold RA_SN; img_lia)) ltac:(img_refl)
ltac:(img_try (unfold INT_MAX; img_lia)) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (unfold INT_MAX; img_lia)) ltac:(img_lia) ltac:(img_lia) ltac:(img_try (unfold OSP_SN; img_lia))
(vf_rest_ok E2 sp0 ap vu_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_2 Hap1 Hap2)
(vf_rest_w E2 vu_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VI3)))
ltac:(img_try (rewrite HL; img_apply (vf_str_first_byte W _ s str INT_MAX STR3); unfold INT_MAX; img_lia))
ltac:(img_try (intros a Ha; img_apply (vf_str_readable W _ s str STR3); img_lia))
Hams SRA3' (SHU3' ltac:(img_lia)) TAIL3 ROM3) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & HL3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
img_change (vf_after_icpt 66 vu_st3 RA_SN OSP_SN 0 []) with vu_af3 in HS3'.
assert (VI3' : VI B ly S W sp0 mem md (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms3) _ (ms_mem ms3') _
(fun a => sp0 + OSP_SN - 2 * ESTACK <= a < sp0 + OSP_SN)).
- img_exact VI3.
- img_exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_SN in *. img_lia.
- intros a Hr Hna. img_apply Hfr3'; [img_try (img_exact Hr) | img_try (img_exact Hna)].
- img_exact Hpm3'. }
remember (havoc E2 66 (map (getr (ms_regs ms3')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 66)%nat -> ew E3 j = ew E2 j) by (img_try (intros j Hj; rewrite HE3; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact Usp2)).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G3_2)).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G4_2)).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G12_2)).
assert (A32_3 : bv_unsigned (ew E3 32) = s) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A32_2)).
assert (HAE3 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E3)
by (img_try (rewrite HE3; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE2)])).
assert (A70_3 : bv_unsigned (ew E3 70) = L).
{ rewrite HE3, (ew_havoc_new E2 66 _ 4 (w64 0)) by (img_try (cbn; img_lia)). unfold CLOB. cbn [nth map]. rewrite HL3'. img_apply unsigned_lit_small. img_lia. }
clear HE3 HS3 VI3 SRA3' SHU3' STR3.
pose proof (st_ok_add_fact E3 vu_af3 _ 70 74 33554425 HS3' eq_refl ltac:(img_try (rewrite A70_3; img_lia))) as HS3f.
img_change (vf_add_fact vu_af3 70 (mkAF 74 33554425 0)) with vu3_af3f in HS3f. clear HS3'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E3 vu3_af3f vu3_st4 _ _ _ HS3f vu3_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3f.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VI4 : VI B ly S W sp0 mem md (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms4) mat4 VI3') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF4. intros Hin. destruct (vf_windows_sound E3 vu3_af3f sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr4. intros Hin. destruct (vf_windows_sound E3 vu3_af3f sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- img_apply (vf_band_present W E3 vu3_st4 ms4 sp0 HS4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 ltac:(img_lia)). }
clear VI3' HF4 HFr4.
assert (STR4 : vf_str W (ms_mem ms4) s str).
{ img_apply (vf_str_xfer W mem); [img_try (img_exact HSTR)|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI4)))); [img_lia | img_try (unfold vf_band; img_lia) | img_try (unfold vf_file; img_lia)]. }
assert (R11_4 : getr (ms_regs ms4) 11 = Z_to_bv 64 (s + L)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E3 _ _ 11 HS4).
match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite denot_lit_U, U_add_off_atom by (img_try (rewrite ?A32_3, ?A70_3; unfold M64; img_lia)). rewrite A32_3, A70_3. f_equal. img_lia. }
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_lbu_nul W E3 vu3_st4 ms4 _ 82 (s + L) HS4 eq_refl eq_refl ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) R11_4 ltac:(img_lia)
ltac:(img_try (rewrite HL; img_exact (proj1 (proj2 STR4))))) HAI4).
intros W4l c4l _ HAI4l (-> & ms4l & mat4l & -> & HS4l & Hmm4l). cbn [cfg_model] in HAI4l. rewrite ?wvb_wvb in HAI4l |- *.
img_change (set_regs_pc vu3_st4 [((12%bv : bv 5), SLit 0)] (0x984a0 + D_10ec)) with vu3_af4 in HS4l.
assert (VI4l : VI B ly S W sp0 mem md (ms_mem ms4l) (with_vm_backing (m_vm_lazy md) mat4l md)).
{ rewrite Hmm4l. pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms4) mat4l VI4) as VR.
rewrite ?wvb_wvb in VR. img_apply VR; [img_try (intros; img_refl) | img_try (intros; img_refl) | img_try (img_exact (proj1 (proj2 (proj2 VI4))))]. }
clear VI4 HS4 STR4 R11_4.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E3 vu3_af4 vu3_st5 _ _ _ HS4l vu3_run5) HAI4l).
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4l.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VI5 : VI B ly S W sp0 mem md (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms5) mat5 VI4l) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF5. intros Hin. destruct (vf_windows_sound E3 vu3_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr5. intros Hin. destruct (vf_windows_sound E3 vu3_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin); tauto.
- img_apply (vf_band_present W E3 vu3_st5 ms5 sp0 HS5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 ltac:(img_lia)). }
clear VI4l HF5 HFr5.
assert (SRA5' : range_addressable (aview tfxsegs (w_H W) (ms_mem ms5)) SHADOW_OFF (68452 + D_20) 0) by (img_try (intros y Hy; img_lia)).
assert (SHU5' : 0 < 0 -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms5)) (68452 + D_20) 0) by (img_try (intros H0; img_lia)).
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E3 vu3_st5 ms5 _ ly S sp0 vu3_r05 vu3_rest5 82 RA_FX OSP_FX (-345) (SLit (68452 + D_20)) ((68452 + D_20)) 0 (@nil Z)
HS5 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp3 G3_3 G4_3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_refl) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold OSP_FX; cbn; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (left; unfold kLowMemEnd; cbn; img_lia))
(vf_rest_ok E3 sp0 ap vu3_rest5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_3 Hap1 Hap2)
(vf_rest_w E3 vu3_rest5 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI5) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI5))) SRA5' SHU5') HAI5).
intros W5' c5' _ HAI5' (-> & ms5' & mat5' & -> & HS5' & HAR5' & HP5' & Hfr5' & Hpm5'). cbn [cfg_model] in HAI5'.
rewrite wvb_wvb in HAI5', HAR5' |- *.
img_change (vf_after_icpt 82 vu3_st5 RA_FX OSP_FX (-345) (@nil Z)) with vu3_af5 in HS5'.
assert (VI5' : VI B ly S W sp0 mem md (ms_mem ms5') (with_vm_backing (m_vm_lazy md) mat5' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms5) _ (ms_mem ms5') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- img_exact VI5.
- img_exact HAR5'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat5' mat5 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr5'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm5'. }
remember (havoc E3 82 (map (getr (ms_regs ms5')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 82)%nat -> ew E5 j = ew E3 j) by (img_try (intros j Hj; rewrite HE5; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact Usp3)).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G3_3)).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G4_3)).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact G12_3)).
assert (A32_5 : bv_unsigned (ew E5 32) = s) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact A32_3)).
assert (A70_5 : bv_unsigned (ew E5 70) = L) by (img_try (rewrite OLD5 by ((img_case; cbv); img_lia); img_exact A70_3)).
assert (HAE5 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E5)
by (img_try (rewrite HE5; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE3)])).
clear HE5 HS5 VI5 SRA5' SHU5'.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E5 vu3_af5 vu3_st6 _ _ _ HS5' vu3_run6) HAI5').
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5'.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VI6 : VI B ly S W sp0 mem md (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms6) mat6 VI5') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF6. intros Hin. destruct (vf_windows_sound E5 vu3_af5 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr6. intros Hin. destruct (vf_windows_sound E5 vu3_af5 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin); tauto.
- img_apply (vf_band_present_ecall W E5 vu3_st6 ms6 sp0 HS6 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 ltac:(img_lia)). }
clear VI5' HF6 HFr6.
eapply (srz_conseq tfxsegs); [ | img_try (rewrite (app_assoc (map (Z_to_bv 8) lit_usage1) str (map (Z_to_bv 8) lit_usage2)), (map_app (WriteEv ch)); img_apply t_emit_app) ].
assert (STR6 : vf_str W (ms_mem ms6) s str).
{ img_apply (vf_str_xfer W mem); [img_try (img_exact HSTR)|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI6)))); [img_lia | img_try (unfold vf_band; img_lia) | img_try (unfold vf_file; img_lia)]. }
pose proof HS6 as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & Hregs6 & Hmem6 & HG6). cbn [restrict ms_mem] in Hmem6.
pose proof (lit_buf_sound tfxsegs E5 (mrestrict (w_H W) (ms_mem ms6)) (ss_mem vu3_st6) (SLit (F_STDERR + 120)) 4 [2; 0; 0; 0] Hmem6
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as Hfdrd. cbn [sv_denot] in Hfdrd.
pose proof (lit_buf_sound tfxsegs E5 (mrestrict (w_H W) (ms_mem ms6)) (ss_mem vu3_st6) (SOff 2 (-352)) 7 lit_usage1 Hmem6
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as Hbuf6.
eapply (srz_sym_stdio_writev2 W E5 vu3_st6 ms6 _ (Z_to_bv 64 2) ch 0 2 (-1024) F_STDERR _ (SOff 2 (-352)) (SLit 7) (SOff 32 0) (SOff 70 0)
(map (Z_to_bv 8) lit_usage1) (str) (map (Z_to_bv 8) [2; 0; 0; 0]) 98 _ HAI6 HS6 eq_refl eq_refl eq_refl).
- img_refl.
- eapply fdchan_sbm; [img_try (img_exact Hch) | img_try (img_apply with_vm_backing_same)].
- img_refl.
- img_case; vm_compute. all: img_refl.
- match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite iovcnt_val, !U_off by (img_try (rewrite Usp5; unfold M64; img_lia)). rewrite (proj2 (Z.eqb_neq _ _)) by img_lia. img_refl.
- match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite iovcnt_val', !U_off by (img_try (rewrite Usp5; unfold M64; img_lia)). rewrite (proj2 (Z.eqb_neq _ _)) by img_lia. img_refl.
- img_refl.
- img_refl.
- img_refl.
- match goal with |- U _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite U_SLit, !U_off by (img_try (rewrite A70_5; unfold M64; img_lia)). rewrite A70_5. img_change (zcanon 7) with 7. img_lia.
- match goal with |- U _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end. rewrite U_SLit. img_refl.
- img_refl.
- img_refl.
- cbn. img_lia. - cbn. img_lia. - cbn. img_lia. - cbn. img_lia.
- img_case; vm_compute. all: img_refl.
-   img_change (word_to_nat (sv_denot E5 (SLit 7))) with 7%nat. img_exact Hbuf6.
-   rewrite word_to_nat_U, (U_atom E5 70 L) by (img_try (first [rewrite <- A70_5, Z_to_bv_bv_unsigned; img_refl | img_lia])).
cbn [sv_denot]. rewrite Z.add_0_r, A32_5, <- HLlen. img_exact (vf_str_rdn W _ s str STR6).
- rewrite U_SLit, (U_atom E5 70 L) by (img_try (first [rewrite <- A70_5, Z_to_bv_bv_unsigned; img_refl | img_lia])). img_change (zcanon 7) with 7. img_lia.
- rewrite U_SLit, U_off by (img_try (rewrite Usp5; unfold M64; img_lia)). rewrite Usp5. img_change (zcanon 7) with 7. img_lia.
- rewrite U_SLit, U_off by (img_try (rewrite Usp5; unfold M64; img_lia)). rewrite Usp5. img_change (zcanon 7) with 7. img_lia.
- rewrite (U_atom E5 70 L) by (img_try (first [rewrite <- A70_5, Z_to_bv_bv_unsigned; img_refl | img_lia])).
rewrite (U_atom E5 32 s) by (img_try (first [rewrite <- A32_5, Z_to_bv_bv_unsigned; img_refl | img_lia])). img_lia.
- rewrite (U_atom E5 70 L) by (img_try (first [rewrite <- A70_5, Z_to_bv_bv_unsigned; img_refl | img_lia])).
rewrite (U_atom E5 32 s) by (img_try (first [rewrite <- A32_5, Z_to_bv_bv_unsigned; img_refl | img_lia])). rewrite Usp5. img_lia.
- img_exact Hfdrd.
- img_case; vm_compute. all: img_refl.
- unfold F_STDERR. img_lia.
- unfold F_STDERR. img_lia.
- rewrite Usp5. unfold F_STDERR. img_lia.
- rewrite Usp5. img_lia.
- rewrite Usp5. img_lia.
- img_case; vm_compute. all: img_refl.
-
intros ms6' ws6' mat6' HS6' HF6' HFr6' HAI6'. rewrite ?wvb_wvb in HAI6' |- *.
img_change (wl_after vu3_st6 0 (-1024) 98) with vu3_af6 in HS6'.
remember (havoc E5 98 ws6') as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 98)%nat -> ew E6 j = ew E5 j) by (img_try (intros j Hj; rewrite HE6; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact Usp5)).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G3_5)).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G4_5)).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact G12_5)).
assert (A32_6 : bv_unsigned (ew E6 32) = s) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact A32_5)).
assert (A70_6 : bv_unsigned (ew E6 70) = L) by (img_try (rewrite OLD6 by ((img_case; cbv); img_lia); img_exact A70_5)).
assert (HAE6 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E6)
by (img_try (rewrite HE6; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE5)])).
assert (VI6' : VI B ly S W sp0 mem md (ms_mem ms6') (with_vm_backing (m_vm_lazy md) mat6' md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms6') mat6' VI6) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF6'. intros Hin. destruct (vf_windows_sound E5 vu3_st6 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr6'. intros Hin. destruct (vf_windows_sound E5 vu3_st6 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp5 Hin); tauto.
- img_apply (vf_band_present W E6 vu3_af6 ms6' sp0 HS6' ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 ltac:(img_lia)). }
clear HE6 HS6 VI6 Hfdrd Hregs6 Hmem6 HG6 HF6' HFr6'.
clear STR6 Hbuf6.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E6 vu3_af6 vu3_st7 _ _ _ HS6' vu3_run7) HAI6').
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7. clear HS6'.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VI7 : VI B ly S W sp0 mem md (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms7) mat7 VI6') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF7. intros Hin. destruct (vf_windows_sound E6 vu3_af6 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr7. intros Hin. destruct (vf_windows_sound E6 vu3_af6 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 Hin); tauto.
- img_apply (vf_band_present W E6 vu3_st7 ms7 sp0 HS7 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp6 ltac:(img_lia)). }
clear VI6' HF7 HFr7.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms7) _ FMT_usage 17 (88328 + D_20) 7 VI7 Hstk Hra_f Hhull_f
ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (unfold FMT_usage; img_lia)) ltac:(img_try (rewrite KHI; unfold FMT_usage; img_lia))) as [SRA7' SHU7'].
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E6 vu3_st7 ms7 _ ly S sp0 vu3_r07 vu3_rest7 109 RA_FX OSP_FX (-352) (SLit (88328 + D_20)) ((88328 + D_20)) 7 lit_usage2
HS7 ltac:(img_try (rewrite HBcode; img_refl)) eq_refl Usp6 G3_6 G4_6 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(img_refl) eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (unfold OSP_FX; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold RA_FX; img_lia)) ltac:(img_refl)
ltac:(img_lia) ltac:(img_try (cbn; img_lia)) ltac:(img_try (unfold OSP_FX; cbn; img_lia)) ltac:(img_try (cbn; img_lia)) ltac:(img_try (left; unfold kLowMemEnd; cbn; img_lia))
(vf_rest_ok E6 sp0 ap vu3_rest7 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) G12_6 Hap1 Hap2)
(vf_rest_w E6 vu3_rest7 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VI7) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI7))) SRA7' SHU7') HAI7).
intros W7' c7' _ HAI7' (-> & ms7' & mat7' & -> & HS7' & HAR7' & HP7' & Hfr7' & Hpm7'). cbn [cfg_model] in HAI7'.
rewrite wvb_wvb in HAI7', HAR7' |- *.
img_change (vf_after_icpt 109 vu3_st7 RA_FX OSP_FX (-352) lit_usage2) with vu3_af7 in HS7'.
assert (VI7' : VI B ly S W sp0 mem md (ms_mem ms7') (with_vm_backing (m_vm_lazy md) mat7' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms7) _ (ms_mem ms7') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-352) <= a < sp0 + (-352) + 7))).
- img_exact VI7.
- img_exact HAR7'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat7' mat7 md). img_apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. img_lia.
- intros a Hr Hna. img_apply Hfr7'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; img_exact H')].
- img_exact Hpm7'. }
remember (havoc E6 109 (map (getr (ms_regs ms7')) CLOB)) as E7 eqn:HE7.
assert (OLD7 : forall j, (j < 109)%nat -> ew E7 j = ew E6 j) by (img_try (intros j Hj; rewrite HE7; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp7 : bv_unsigned (ew E7 2) = sp0) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact Usp6)).
assert (G3_7 : ew E7 3 = w64 (as_gp B)) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G3_6)).
assert (G4_7 : ew E7 4 = w64 (as_tp B)) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G4_6)).
assert (G12_7 : bv_unsigned (ew E7 12) = ap) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact G12_6)).
assert (A32_7 : bv_unsigned (ew E7 32) = s) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact A32_6)).
assert (A70_7 : bv_unsigned (ew E7 70) = L) by (img_try (rewrite OLD7 by ((img_case; cbv); img_lia); img_exact A70_6)).
assert (HAE7 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E7)
by (img_try (rewrite HE7; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE6)])).
clear HE7 HS7 VI7 SRA7' SHU7'.
eapply (srz_stdio_writev_by_run tfxmusl_tbl W E7 vu3_af7 ms7' _ ch 125 vu3_st8 vu3_af8 lit_usage2 2 T tfxmusl_tbl_ok HS7' HAI7' vu3_wx_eq).
{ eapply fdchan_sbm; [img_try (img_exact Hch) | img_try (img_apply with_vm_backing_same)]. }
intros ms8 ws8 mat8 HS8 HF8 HFr8 _ _ HAI8. rewrite ?wvb_wvb in HAI8 |- *.
assert (VI8 : VI B ly S W sp0 mem md (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms8) mat8 VI7') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF8. intros Hin. destruct (vf_windows_sound E7 vu3_af7 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr8. intros Hin. destruct (vf_windows_sound E7 vu3_af7 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp7 Hin); tauto.
- img_apply (vf_band_present W (havoc E7 125 ws8) vu3_af8 ms8 sp0 HS8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))); [|img_lia].
rewrite ew_havoc_old by (img_try ((img_case; cbv); img_lia)). img_exact Usp7. }
remember (havoc E7 125 ws8) as E8 eqn:HE8.
assert (OLD8 : forall j, (j < 125)%nat -> ew E8 j = ew E7 j) by (img_try (intros j Hj; rewrite HE8; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp8 : bv_unsigned (ew E8 2) = sp0) by (img_try (rewrite OLD8 by ((img_case; cbv); img_lia); img_exact Usp7)).
assert (A70_8 : bv_unsigned (ew E8 70) = L) by (img_try (rewrite OLD8 by ((img_case; cbv); img_lia); img_exact A70_7)).
assert (HAE8 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E8)
by (img_try (rewrite HE8; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (img_exact HAE7)])).
clear HE8 HS7' VI7' HF8 HFr8.
eapply (SRr_srealizes tfxsegs W _ _ _ (vf_phase W E8 vu3_af8 vu3_st9 _ _ _ HS8 vu3_run9) HAI8).
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9. clear HS8.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VI9 : VI B ly S W sp0 mem md (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(img_lia) _ _ (ms_mem ms9) mat9 VI8) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF9. intros Hin. destruct (vf_windows_sound E8 vu3_af8 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp8 Hin); tauto.
- intros x Hx1 Hx2. img_apply HFr9. intros Hin. destruct (vf_windows_sound E8 vu3_af8 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp8 Hin); tauto.
- img_apply (vf_band_present W E8 vu3_st9 ms9 sp0 HS9 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp8 ltac:(img_lia)). }
clear VI8 HF9 HFr9.
eapply (SRr_srealizes tfxsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms9) (v_jalr (getr (ms_regs ms9) 1) 0) (ms_mem ms9) (seg_rom tfxsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | img_try (img_exact HAI9) | ].
{ eapply (SRr_ret_at tfxsegs tfxmusl_tbl tfxmusl_tbl_ok Hwx W E8); [img_try (img_exact HS9) | img_refl | img_try ((try img_inst; img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb. split; [img_refl|]. exists mat'. img_refl. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VI9 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS9 (1%bv : bv 5) Q1.
rewrite OLD8, OLD7, OLD6, OLD5, OLD3, OLD2, OLD1 in Q1 by (img_try ((img_case; cbv); img_lia)). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfxsegs (w_H W) E8 _ _ 10 HS9) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := img_ev constr:(v) in img_change v with v' in Q10 end.
rewrite denot_lit_U, !U_SAlu, !U_SLit in Q10. cbn [zalu_raw] in Q10. img_change (zcanon 0) with 0 in Q10.
rewrite !Z.lor_0_l, U_off in Q10 by (img_try (rewrite A70_8; unfold M64; img_lia)). rewrite A70_8, !(zcanon_id (L + 14)) in Q10 by (img_try (unfold M64; img_lia)).
replace (v_jalr (getr (ms_regs ms9) 1) 0) with (w64 (raZ regs))
by (img_try (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra)).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat9 md) (with_vm_backing (m_vm_lazy md) matR md))
by (img_try (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat9 md); img_apply with_vm_backing_same)).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
img_apply (HK (ms_regs ms9) (ms_mem ms9) (with_vm_backing (m_vm_lazy md) matR md)).
* img_apply (al_frame _ _ LAWS ly S W (ms_mem ms9) _ (ms_mem ms9) _ HAR9); [img_try (intros; img_refl) | img_try (intros a Hv; img_exact Hv) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_apply MF) | img_try (img_exact (YE0v.hs_kept_refl _ _))].
* img_exact (aregs_preserved_of_st_ok _ E8 _ _ regs [Z_to_bv 64 s; Z_to_bv 64 cval] HS9 HAE8 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
* img_apply with_vm_backing_same.
* rewrite Q10. img_refl.
* destruct HS9 as (_ & _ & _ & _ & _ & _ & _ & Hmem9 & _).
unfold stderr_after_vfprintf, file_is, stderr_fields_after_vf.
repeat img_apply Forall_cons; try img_apply Forall_nil;
(eapply (val_mem_of_lit E8 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem vu3_st9) _ _ _ Hmem9); (try img_inst; img_case; vm_compute); img_refl).
* img_exact Hfr9.
* img_exact Hpm9.
* img_exact HAIR.
Qed.
Theorem tfx_vfprintf_usage : forall ly S (W : world tfxsegs) regs mem md ch ap s (str : list byte) L cval T,
ecall_pre tfxsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_usage -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfxsegs (mrestrict (w_H W) mem) ap 8 s ->
L = Z.of_nat (length str) -> L <= 33554425 ->
1 <= s -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= spZ regs - VF_STK \/ spZ regs <= s) ->
(s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) -> amem_range s (L + 1) ->
vf_tail W mem s L -> mconsts_view W mem ->
vf_str W mem s str ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF s (L + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) s (L + 1) ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF FMT_usage 17 ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) FMT_usage 17 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfxsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfxsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 (L + 14) ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vf_file a -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfxsegs (w_H W) (w_A W) md' ->
srealizes tfxsegs (cfg_at tfxsegs (raZ regs) regs' mem' md') T) ->
srealizes tfxsegs (cfg_at tfxsegs A_vfprintf regs mem md)
(t_emit (map (WriteEv ch) (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2)) T).
Proof.
intros ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HL HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK.
destruct (Z_lt_le_dec 66 L) as [H1|H1];
[| img_try (img_exact (tfx_vfprintf_usage_A1 ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg HL ltac:(img_lia) H1 Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK))].
destruct (Z_lt_le_dec 73 L) as [H2|H2];
[| img_try (img_exact (tfx_vfprintf_usage_A2 ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg HL ltac:(img_lia) H2 Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK))].
img_exact (tfx_vfprintf_usage_A3 ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg HL ltac:(img_lia) HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK).
Qed.
End S.
End b.
