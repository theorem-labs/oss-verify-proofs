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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3v YF3w YF8g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition hJ0 : nat := aHAV.
Definition CLOB_INIT : list (bv 5) := [5; 6; 7; 13; 15; 16; 17; 28; 29; 30]%bv.
Definition RJ2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget (runto (0x3672c + D_150) SS0R) hJ0 CLOB_INIT)))).
Definition RS_10 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36730 + D_150) RJ2))).
Definition RS_1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin RS_10 9%bv (SOff rN 0)))).
Definition RS_A0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x3688c + D_150) RS_1))).
Definition RS_A {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin RS_A0 8%bv (SOff rRG 0)) 20%bv (SOff rFA 0)))).
Definition RS_B {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36960 + D_150) RS_A))).
Definition RS_B2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_LTU false (SOff rNF 0) (SOff rN 0) RS_B))).
Definition RS_C0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36980 + D_150) RS_B2))).
Definition CLOB_CP : list (bv 5) := [12; 13; 20]%bv.
Definition hCP2 : nat := 74.
Definition RS_C {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch RS_C0 (ss_mem RS_C0) hCP2 CLOB_CP (0x36994 + D_150)))).
Definition RS_RET {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto 0x7ffffff0 RS_C))).

