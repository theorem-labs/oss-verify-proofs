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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF3v YF3w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition hMS1 : nat := 133.
Definition hCL2 : nat := 139.
Definition hMS2 : nat := 144.
Definition R_scr2 : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- 2272) (- ASTACK) (- 2272) [].
Definition rs_D {imgk : img} : smem := match ss_mem SS_PD with r0 :: r1 :: rest => r0 :: trim_lo r1 (-2272) :: rest | l => l end.
Definition SS_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_scr2 (ss_after_call SS_PD rs_D hD1 (0x31cc8 + D_150))))).
Definition SS_M0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31cf0 + D_150) SS_2))).
Definition SS_M {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin SS_M0 10%bv (SOff aSK 0)))).
Definition SS_N0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31dc0 + D_150) SS_M))).
Definition SS_N {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin SS_N0 22%bv (SOff aN8D 0)))).
Definition SS_O0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x545a4 + D_2c4) SS_N))).
Definition SS_O {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin SS_O0 8%bv (SOff aCNT8 0)) 10%bv (SOff aSU 0)))).
Definition SS_MS1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) SS_O))).
Definition CLOB_MS : list (bv 5) := [11; 12; 13; 14; 15; 16]%bv.
Definition SS_Q {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch SS_MS1 (ss_mem SS_MS1) hMS1 CLOB_MS (0x31dd4 + D_150)))).
Definition SS_Qe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_EQ true (SOff 10 0) (SOff aN8D 0) SS_Q))).
Definition SS_Qo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_EQ false (SOff 10 0) (SOff aN8D 0) SS_Q))).
Definition R_pb : YQ0b.region := YQ0b.mkRegion (Some aPB) 0 1 0 1 [YQ0b.mkChunk 0 (CVal 1 (SLit 250))].
Definition SS_P0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31e64 + D_150) SS_Qo))).
Definition SS_Po {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_pb (pin SS_P0 10%bv (SOff aPB 0))))).
Definition CLOB_CL2 : list (bv 5) := [12; 13; 14; 15; 16]%bv.
Definition st_R {imgk : img} (ss : sstate) : sstate := runto (0x31ec0 + D_150) ss.
Definition st_S {imgk : img} (lo : bool) (ss : sstate) : sstate := noconds (pin (forget (runto (0x31fac + D_150) (arm BC_LTU (negb lo) (SLit 512) (SOff aND 0) ss)) hCL2 CLOB_CL2) 11%bv (SOff aCL 0)).
Definition st_T {imgk : img} (ss : sstate) : sstate := pin (runto (0x31fb4 + D_150) ss) 10%bv (SOff aSSLOT 0).
Definition st_V {imgk : img} (ss : sstate) : sstate := runto (0x31fdc + D_150) ss.
Definition st_W {imgk : img} (small : bool) (ss : sstate) : sstate := noconds (pin (runto (0x31fe4 + D_150) (arm BC_LTU small (SOff 10 0) (SLit 4096) ss)) 12%bv (SOff aFIL 0)).
Definition st_X {imgk : img} (ss : sstate) : sstate := let m := runto (0x9b894 + D_10ec) ss in ss_after_stretch m (ss_mem m) hMS2 CLOB_MS (0x31ffc + D_150).
Definition st_Y {imgk : img} (ss : sstate) : sstate := arm BC_EQ false (SOff aU (-16)) (SOff aK 0) (runto (0x32024 + D_150) ss).
Definition st_Z {imgk : img} (ss : sstate) : sstate := arm BC_LTU false (SOff aU (-16)) (SOff aK 16) (runto (0x3202c + D_150) ss).
Definition st_RET {imgk : img} (ss : sstate) : sstate := runto (0x53434 + D_2c4) ss.
Definition SS_Re {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_R SS_Qe))).
Definition SS_Se {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_S true SS_Re))).
Definition SS_Te {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_T SS_Se))).
Definition SS_Ve {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_V SS_Te))).
Definition SS_We {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_W true SS_Ve))).
Definition SS_Xe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_X SS_We))).
Definition SS_Ye {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_Y SS_Xe))).
Definition SS_Ze {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_Z SS_Ye))).
Definition SS_RETe {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_RET SS_Ze))).
Definition SS_Ro {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_R SS_Po))).
Definition SS_So {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_S true SS_Ro))).
Definition SS_To {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_T SS_So))).
Definition SS_Vo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_V SS_To))).
Definition SS_Wo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_W true SS_Vo))).
Definition SS_Xo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_X SS_Wo))).
Definition SS_Yo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_Y SS_Xo))).
Definition SS_Zo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_Z SS_Yo))).
Definition SS_RETo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (st_RET SS_Zo))).




Definition CL2_lo {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs (runto (0x31fac + D_150) (arm BC_LTU false (SLit 512) (SOff aND 0) SS_Re))) 11%bv))).
Definition CL2_hi {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => (sr_get (ss_regs (runto (0x31fac + D_150) (arm BC_LTU true (SLit 512) (SOff aND 0) SS_Re))) 11%bv))).

