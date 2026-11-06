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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF3v YF3w YF3x YF41 YF6z YF71 YF72 YF73.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF77.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition sM5 : nat := 182.
Definition kJQ : nat := 203.
Definition sMF : nat := 224.
Definition sL6 : nat := 218.
Definition CLOB_L6 : list (bv 5) := [12; 13; 14; 15; 16; 17]%bv.
Definition CLOBJ : list (bv 5) := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition USH_LEN : sv :=
SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff aMAP 6136) (SOff aN8DS 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aMAP 6144) (SLit 3)).
Definition U_M5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) (arm BC_LTU true USH_LEN (SLit 18446744073709551615) T_R)))).
Definition U_Q {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch U_M5 (ss_mem U_M5) sM5 CLOB_MS (0x31dd4 + D_150)))).
Definition joinQ0 (ss : sstate) : sstate :=
noconds (forget (mkSS (ss_pc ss) (ss_regs ss) (trimscratch (-2336) (ss_mem ss)) (ss_resv ss) (ss_facts ss)) kJQ CLOBJ).
Definition U_QJ {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (joinQ0 U_Q))).
Definition Ue_MF {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) (arm BC_EQ true (SOff 10 0) (SOff aN8DS 0) U_QJ)))).
Definition R_pbS : YQ0b.region := YQ0b.mkRegion (Some aPBS) 0 1 0 1 [].
Definition Uo_L6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31e00 + D_150) (arm BC_EQ false (SOff 10 0) (SOff aN8DS 0) U_QJ)))).
Definition Uo_L6lo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31e64 + D_150) (armR BC_GEU true 12 22 Uo_L6)))).
Definition Uo_L6h {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31e3c + D_150) (armR BC_GEU false 12 22 Uo_L6)))).
Definition Uo_L6h2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31e40 + D_150) (armR BC_LTU false 17 22 Uo_L6h)))).
Definition Uo_L6hi {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31e64 + D_150) (armR BC_GEU false 16 22 Uo_L6h2)))).
Definition Uo_P0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget Uo_L6lo sL6 CLOB_L6)))).

Definition Uo_P {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_pbS (pin Uo_P0 10%bv (SOff aPBS 0))))).
Definition Uo_MF {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) Uo_P))).
Definition st_end {imgk : img} (ss : sstate) : sstate :=
let a := ss_after_stretch ss (ss_mem ss) sMF CLOB_MS (0x31ffc + D_150) in
runto (0x323bc + D_150) (arm BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112) (runto (0x3202c + D_150) (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto (0x32024 + D_150) a)))).
Definition Ue_RET {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_end Ue_MF))).
Definition Uo_RET {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_end Uo_MF))).

