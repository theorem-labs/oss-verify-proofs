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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF3v YF3w YF3x YF41 YF47 YF4b YF4c YF4d YF4e YF4f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition aCAN : nat := 182.
Definition sB1 : nat := 183.
Definition sB2 : nat := 189.
Definition kJB : nat := 195.
Definition R_got {imgk : img} : YQ0b.region := lit8 (0xa2e10 + D_10f0) (0x5fd190 + D_10c0).
Definition R_can {imgk : img} : YQ0b.region := atom8 (0x5fd190 + D_10c0) aCAN.
Definition R_pgsz {imgk : img} : YQ0b.region := lit8 (0x5fd410 + D_10c0) 4096.
Definition R_sct : YQ0b.region :=
YQ0b.mkRegion None 0x2150c (0x2150c + 2) 0 0 [YQ0b.mkChunk 0x2150c (CVal 2 (SLit 0xff04))].
Definition R_scj {imgk : img} : YQ0b.region := lit4 0x214a8 (0x6f924 + D_104c).
Definition R_g1 {imgk : img} : YQ0b.region := lit8 (0xa21a0 + D_10f0) 1.
Definition R_g3 {imgk : img} : YQ0b.region := lit8 (0xa21a8 + D_10f0) (0x13bcdc + D_10c0).
Definition R_g2 {imgk : img} : YQ0b.region := lit4 (0x13bcdc + D_10c0) 0.
Definition R_f1 {imgk : img} : YQ0b.region := lit1 (0x13bddc + D_10c0) 1.
Definition R_f2 {imgk : img} : YQ0b.region := lit1 (0x13bdc3 + D_10c0) 1.
Definition BREG {imgk : img} : smem := [R_got; R_can; R_pgsz; R_sct; R_scj; R_g1; R_g3; R_g2; R_f1; R_f2].
Lemma can_bytes {imgk : img} : exists bs, YQ0b.img_bytes tfxsegs (0x5fd190 + D_10c0) 8 = Some bs.
Proof. img_eexists_vm. Qed.
Definition SHBT : sv := SOff aSM 768.
Definition SHET : sv := SOff aPBS 0.
Definition PGBT : sv := SAlu ALU_AND (SOff aSM 4863) (SLit 18446744073709547520).
Definition PGET : sv := SAlu ALU_AND (SOff aPBS 0) (SLit 18446744073709547520).
Definition B_0 {imgk : img} : sstate := arm BC_LTU false USH_LEN (SLit 18446744073709551615) T_R.
Definition B_R {imgk : img} : sstate := fold_right addreg B_0 BREG.
Definition B_A0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x545f0 + D_2c4) B_R))).
Definition SHB_X {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs B_A0) 10%bv))).
Definition SHE_X {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs B_A0) 20%bv))).
Definition PGB_X {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs B_A0) 9%bv))).
Definition PGE_X {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs B_A0) 18%bv))).
Definition B_A {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin (pin (pin B_A0 10%bv SHBT) 20%bv SHET) 9%bv PGBT) 18%bv PGET))).
Definition B_B0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x545f4 + D_2c4) (arm BC_GEU false PGBT PGET B_A)))).
Definition B_M1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x9b894 + D_10ec) (arm BC_EQ false PGBT SHBT B_B0)))).
Definition B_C {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch B_M1 (ss_mem B_M1) sB1 CLOB_MS (0x54608 + D_2c4)))).
Definition B_Ct {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x54620 + D_2c4) (arm BC_EQ true SHET PGET B_C)))).
Definition B_M2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x9b894 + D_10ec) (arm BC_EQ false SHET PGET B_C)))).
Definition B_Cf {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch B_M2 (ss_mem B_M2) sB2 CLOB_MS (0x54620 + D_2c4)))).
Definition CLOBB : list (bv 5) := [1; 10; 11; 12; 13; 14; 15; 16]%bv.
Definition joinB (ss : sstate) : sstate := noconds (forget ss kJB CLOBB).
Definition B_D {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (joinB B_Ct))).

Definition B_E0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x6c9c8 + D_2c4) B_D))).
Definition REM1 {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs B_E0) 13%bv))).
Definition B_E {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_NE false REM1 (SLit 0) B_E0))).
Definition B_F0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x6c9d8 + D_2c4) B_E))).
Definition REM2 {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs B_F0) 13%bv))).
Definition B_F {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_NE false REM2 (SLit 0) B_F0))).
Definition S_K {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD 0x7ffffff0 B_F))).
Definition KA0 {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs S_K) 10%bv))).
Definition KA1 {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs S_K) 11%bv))).
Definition K_R0 {imgk : img} : sstate := resume S_K (SLit ENOMEM_RETv) (ss_mem S_K) (ss_facts S_K).
Definition K_SPIN {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x6ea08 + D_2c4) K_R0))).
Definition K_G0 {imgk : img} : sstate := resume S_K KA0 (ss_mem S_K) (ss_facts S_K).
Definition B_Q {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoD (0x31dd4 + D_150) K_G0))).
Definition joinQ (ss : sstate) : sstate := joinQ0 (mkSS (ss_pc ss) (ss_regs ss) (skipn 10 (ss_mem ss)) (ss_resv ss) (ss_facts ss)).


