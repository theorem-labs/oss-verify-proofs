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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3v YF3y YF3w YF3x.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition KS_U {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5aea0 + D_2c4) SS0K))).
Definition rs_Uk {imgk : img} : smem := match ss_mem KS_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 47) | [] => [] end.
Definition KS_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_bst (addreg R_scr1 (ss_after_call KS_U rs_Uk hU1 (0x53400 + D_2c4)))))).
Definition KS_A {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31ac8 + D_150) KS_1))).
Definition KS_Ab {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31af4 + D_150) (arm BC_LTU true (SLit 8) (SOff 10 0) KS_A)))).
Definition KS_As {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31af4 + D_150) (arm BC_LTU false (SLit 8) (SOff 10 0) KS_A)))).
Definition KS_B {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (pin (pin KS_Ab 10%bv (SOff aR8 0)) 11%bv (SLit 0))))).

Definition KS_B1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31b10 + D_150) KS_B))).
Definition KS_B2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin KS_B1 9%bv (SOff aNP 0)))).
Definition KS_C0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x35fe4 + D_150) KS_B2))).
Definition KS_C {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_GEU true (SAlu ALU_XOR (SOff aR8 16) (SLit (-1))) (SLit 8) KS_C0))).
Definition KS_E0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36150 + D_150) KS_C))).
Definition KS_E {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (pin KS_E0 8%bv (SOff aCL 0))))).
Definition KS_F0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36168 + D_150) KS_E))).
Definition KS_F {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin KS_F0 9%bv (SOff aP 0)))).
Definition KS_JN {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget (runto (0x36170 + D_150) KS_F) hJN CLOBJ)))).
Definition KS_G0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36190 + D_150) KS_JN))).
Definition KS_G {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin KS_G0 14%bv (SOff aPV (-16))))).
Definition KS_H0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31bbc + D_150) KS_G))).
Definition KS_H {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin KS_H0 10%bv (SOff aK 0)))).
Definition KS_J0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31be0 + D_150) KS_H))).
Definition KS_J {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_LTU false (SAlu ALU_ADD (SOff aR8 16) (SOff aK 0)) (SAlu ALU_ADD (SOff aK 16) (SOff aNP 0)) KS_J0))).
Definition KS_K0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31c08 + D_150) KS_J))).
Definition KS_K {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_NE false (SAlu ALU_SRL (SOff 10 0) (SLit 48)) (SLit 0) KS_K0))).
Definition KS_PD {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x72fcc + D_2c4) KS_K))).

Definition hJ : nat := 139.
Definition hMS2k : nat := 152.
Definition rs_Dk {imgk : img} : smem := match ss_mem KS_PD with r0 :: r1 :: rest => r0 :: trim_lo r1 (-2272) :: rest | l => l end.
Definition KS_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_scr2 (ss_after_call KS_PD rs_Dk hD1 (0x31cc8 + D_150))))).
Definition KS_M0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31cf0 + D_150) KS_2))).
Definition KS_M {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin KS_M0 10%bv (SOff aSK 0)))).
Definition KS_N0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31dc0 + D_150) KS_M))).
Definition KS_N {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin KS_N0 22%bv (SOff aN8D 0)))).
Definition KS_Nz {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31dd4 + D_150) (arm BC_EQ true (SOff aN8D 0) (SLit 0) KS_N)))).
Definition KS_Nn {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_EQ false (SOff aN8D 0) (SLit 0) KS_N))).
Definition KS_O0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x545a4 + D_2c4) KS_Nn))).
Definition KS_O {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin KS_O0 8%bv (SOff aCNT8 0)) 10%bv (SOff aSK 2)))).
Definition KS_MS1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) KS_O))).
Definition KS_Q1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch KS_MS1 (ss_mem KS_MS1) hMS1 CLOB_MS (0x31dd4 + D_150)))).
Definition CLOB_J : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28]%bv.
Definition clr0 (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (R_scr2 :: tl (ss_mem ss)) (ss_resv ss) (ss_facts ss).
Definition KS_Q {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget (clr0 KS_Nz) hJ CLOB_J)))).

Definition KS_Qe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_EQ true (SOff aNP 0) (SOff aN8D 0) KS_Q))).
Definition KS_Qo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_EQ false (SOff aNP 0) (SOff aN8D 0) KS_Q))).
Definition KS_P0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31e64 + D_150) KS_Qo))).
Definition KS_Po {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_pb (pin KS_P0 10%bv (SOff aPB 0))))).
Definition kst_T {imgk : img} (ss : sstate) : sstate := pin (runto (0x31fb4 + D_150) ss) 10%bv (SOff aSSLOT 0).
Definition kst_X {imgk : img} (ss : sstate) : sstate := let m := runto (0x9b894 + D_10ec) ss in ss_after_stretch m (ss_mem m) hMS2k CLOB_MS (0x31ffc + D_150).
Definition KS_Te {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (kst_T KS_Qe))).
Definition KS_Xe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (kst_X KS_Te))).
Definition KS_RETe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_RET KS_Xe))).
Definition KS_To {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (kst_T KS_Po))).
Definition KS_Xo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (kst_X KS_To))).
Definition KS_RETo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_RET KS_Xo))).
Definition SSLOT_term : sv := SAlu ALU_ADD (SOff aT 2912) (SAlu ALU_SLL (SAlu ALU_SRL (SOff aR8 47) (SLit 5)) (SLit 3)).

