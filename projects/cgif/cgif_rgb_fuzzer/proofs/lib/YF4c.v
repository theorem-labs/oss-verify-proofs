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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF3v YF3w YF3x YF41 YF47 YF4b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition ENOMEM_RETv : Z := 18446744073709551604.
Definition S_R0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (0x64c8c + D_2c4) (sr_set (ss_regs S_N) 10%bv (SLit ENOMEM_RETv)) (ss_mem S_N ++ NREGS) None FS))).

Definition S_R1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC (0x36350 + D_150) S_R0))).
Definition S_RET {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x53434 + D_2c4) S_R1))).
Definition R_map : YQ0b.region := YQ0b.mkRegion (Some aMAP) 0 6144 0 6144 [YQ0b.mkChunk 6129 (CVal 1 (SLit 0))].
Definition S_P0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (0x64c8c + D_2c4) (sr_set (ss_regs S_N) 10%bv (SOff aMAP 0)) (R_map :: ss_mem S_N) None FS2))).

Definition S_P1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC (0x36350 + D_150) S_P0))).
Definition S_L1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54344 + D_2c4) S_P1))).
Definition S_L1l {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5452c + D_2c4) (armR BC_GEU true 14 10 S_L1)))).
Definition S_L1lo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) (armR BC_GEU true 14 11 S_L1l)))).
Definition S_L1h {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54384 + D_2c4) (armR BC_GEU false 14 10 S_L1)))).
Definition S_L1h2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5452c + D_2c4) (armR BC_LTU true 7 10 S_L1h)))).
Definition S_L1h3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5456c + D_2c4) (armR BC_GEU false 14 11 S_L1h2)))).
Definition S_L1hi {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) (armR BC_GEU false 5 11 S_L1h3)))).
Definition S_M1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (psJ sL1 S_L1lo))).

Definition S_P2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch S_M1 (ss_mem S_M1) sM1 CLOB_MS (0x363a8 + D_150)))).
Definition S_P3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin S_P2 23%bv (SOff aEND 0)))).
Definition S_P4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x363b4 + D_150) S_P3) 11%bv (SOff aTL 0)))).
Definition S_L2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54344 + D_2c4) S_P4))).
Definition S_L2l {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5452c + D_2c4) (armR BC_GEU true 14 10 S_L2)))).
Definition S_L2lo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) (armR BC_GEU true 14 11 S_L2l)))).
Definition S_L2h {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54384 + D_2c4) (armR BC_GEU false 14 10 S_L2)))).
Definition S_L2h2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5452c + D_2c4) (armR BC_LTU true 7 10 S_L2h)))).
Definition S_L2h3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5456c + D_2c4) (armR BC_GEU false 14 11 S_L2h2)))).
Definition S_L2hi {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) (armR BC_GEU false 5 11 S_L2h3)))).
Definition S_M2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (psJ sL2 S_L2lo))).

Definition S_P5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch S_M2 (ss_mem S_M2) sM2 CLOB_MS (0x363b8 + D_150)))).
Definition S_P6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_LTU false (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (SOff aMAP 0) (runto (0x363f0 + D_150) S_P5)))).
Definition S_P7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_LTU false (SAlu ALU_ADD (SOff aMS 0) (SOff aMAP 0)) (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (runto (0x363f4 + D_150) S_P6)))).
Definition S_P8 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_NE false (SAlu ALU_SRL (SOff aNCH 0) (SLit 20)) (SLit 0) (runto (0x36448 + D_150) S_P7)))).
Definition S_X {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x364f4 + D_150) S_P8))).
Definition R_qs : YQ0b.region := YQ0b.mkRegion (Some aQS) 0 8 0 8 [].
Definition S_Y0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x3650c + D_150) (arm BC_EQ false (SOff aNCH 0) (SOff aRES 0) S_X)))).
Definition S_Y {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_qs (noconds (pin S_Y0 12%bv (SOff aQS 0)))))).
Definition S_Z0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36538 + D_150) S_Y))).
Definition S_Zt {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36540 + D_150) (arm BC_LTU true (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0) S_Z0)))).
Definition S_Zf {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36540 + D_150) (arm BC_LTU false (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0) S_Z0)))).
Definition S_Z {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget S_Zt sMX [12]%bv)))).

Definition S_Z1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36548 + D_150) S_Z) 11%bv (SOff aBSL (-104))))).
Definition S_T0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31be0 + D_150) S_Z1))).

