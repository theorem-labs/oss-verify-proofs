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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF3v YF3w YF47.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition armR (cnd : branch_cond) (tk : bool) (r1 r2 : bv 5) (ss : sstate) : sstate :=
arm cnd tk (sr_get (ss_regs ss) r1) (sr_get (ss_regs ss) r2) ss.
Definition CLOB_L : list (bv 5) := [5; 6; 7; 14; 15; 16; 17; 28]%bv.
Definition psLO1 {imgk : img} (ss : sstate) : sstate := armR BC_GEU true 14 10 (runto (0x54344 + D_2c4) ss).
Definition psLO2 {imgk : img} (ss : sstate) : sstate := armR BC_GEU true 14 11 (runto (0x5452c + D_2c4) (psLO1 ss)).
Definition psLO {imgk : img} (ss : sstate) : sstate := runto (0x54570 + D_2c4) (psLO2 ss).
Definition psHI1 {imgk : img} (ss : sstate) : sstate := armR BC_GEU false 14 10 (runto (0x54344 + D_2c4) ss).
Definition psHI2 {imgk : img} (ss : sstate) : sstate := armR BC_LTU true 7 10 (runto (0x54384 + D_2c4) (psHI1 ss)).
Definition psHI3 {imgk : img} (ss : sstate) : sstate := armR BC_GEU false 14 11 (runto (0x5452c + D_2c4) (psHI2 ss)).
Definition psHI4 {imgk : img} (ss : sstate) : sstate := armR BC_GEU false 5 11 (runto (0x5456c + D_2c4) (psHI3 ss)).
Definition psHI {imgk : img} (ss : sstate) : sstate := runto (0x54570 + D_2c4) (psHI4 ss).
Definition psJ (k : nat) (ss : sstate) : sstate := noconds (forget ss k CLOB_L).
Definition CLOB_Lt : list (bv 5) := [5; 7; 14; 15; 16; 17; 28]%bv.
Definition psJt (k : nat) (ss : sstate) : sstate := noconds (forget ss k CLOB_Lt).
Definition S_U {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5aea0 + D_2c4) S0))).
Definition srs_U {imgk : img} : smem := match ss_mem S_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 57) | [] => [] end.
Definition S_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_bst (addreg R_scr1 (ss_after_call S_U srs_U sU1 (0x53400 + D_2c4)))))).
Definition S_B0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31af4 + D_150) S_1))).
Definition S_B {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin S_B0 10%bv (SOff aR8 0)) 11%bv (SLit 0)))).
Definition S_C0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31b30 + D_150) S_B))).
Definition S_C {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin S_C0 19%bv (SOff aND 0)))).
Definition S_D0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x35fe4 + D_150) S_C))).
Definition S_D {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_GEU true (SAlu ALU_XOR (SOff aND 0) (SLit (-1))) (SLit 8) S_D0))).
Definition S_E0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36310 + D_150) S_D))).
Definition S_E {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_GEU true (SOff aMS 0) (SOff aND 0) (pin S_E0 18%bv (SOff aMS 0))))).
Definition S_G {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x66550 + D_2c4) S_E))).
Definition S_N {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC (0x64c88 + D_2c4) S_G))).

