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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF3v YF3w YF3x YF41 YF47 YF4b YF4c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition S_V0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x6ed20 + D_2c4) (arm BC_EQ true (SOff aNCH 0) (SOff aRES 0) S_X)))).
Definition S_V {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC (0x64c88 + D_2c4) S_V0))).
Definition S_V2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runtoC (0x366f0 + D_150) (mkSS (0x64c8c + D_2c4) (ss_regs S_V) (ss_mem S_V) None (ss_facts S_V))))).
Definition S_V3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x3650c + D_150) S_V2))).
Definition RES2T : sv := SAlu ALU_ADD (SOff aRES 0) (SAlu ALU_SLL (SAlu ALU_XOR (SAlu ALU_SLTU (SOff aNCH 0) (SOff aRES 0)) (SLit 1)) (SLit 14)).
Definition dropchunks (lo : Z) (m : smem) : smem :=
map (fun r => if (match YQ0b.r_base r with None => Z.eqb (YQ0b.r_lo r) lo | Some _ => false end)
then YQ0b.mkRegion (YQ0b.r_base r) (YQ0b.r_lo r) (YQ0b.r_hi r) (YQ0b.r_wlo r) (YQ0b.r_whi r) [] else r) m.
Definition setchunks (lo : Z) (cs : list YQ0b.chunk) (m : smem) : smem :=
map (fun r => if (match YQ0b.r_base r with None => Z.eqb (YQ0b.r_lo r) lo | Some _ => false end)
then YQ0b.mkRegion (YQ0b.r_base r) (YQ0b.r_lo r) (YQ0b.r_hi r) (YQ0b.r_wlo r) (YQ0b.r_whi r) cs else r) m.
Definition trimscratch (cut : Z) (m : smem) : smem :=
map (fun r => match YQ0b.r_base r with
| Some 2%nat => if Z.ltb (YQ0b.r_lo r) cut
then YQ0b.mkRegion (YQ0b.r_base r) (YQ0b.r_lo r) (YQ0b.r_hi r) (YQ0b.r_wlo r) (YQ0b.r_whi r)
(List.filter (fun c => Z.leb cut (YQ0b.c_off c)) (YQ0b.r_chunks r))
else r
| _ => r end) m.
Definition sJY : nat := 124.
Definition joinY {imgk : img} (ss : sstate) : sstate :=
let ss1 := mkSS (ss_pc ss) (sr_set (ss_regs ss) 12%bv (SOff aQS 0))
(trimscratch (-2416) (setchunks (TFX_INST + o_sec_reserved) [YQ0b.mkChunk (TFX_INST + o_sec_reserved) (CVal 8 RES2T)] (ss_mem ss))) (ss_resv ss) (ss_facts ss) in
addreg R_qs (noconds (forget ss1 sJY [1; 15; 17; 20]%bv)).
Definition S_YJ {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (joinY S_Y0))).
Lemma S_VY_join {imgk : img} : joinY S_V3 = S_YJ. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition S_ZJ0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36538 + D_150) S_YJ))).
Definition S_ZJt {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36540 + D_150) (arm BC_LTU true (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0) S_ZJ0)))).
Definition S_ZJf {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x36540 + D_150) (arm BC_LTU false (SAlu ALU_ADD (SOff aMS 0) (SOff aI2 0)) (SOff aI3 0) S_ZJ0)))).
Definition S_ZJ {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget S_ZJt sMX [12]%bv)))).

Definition S_ZJ1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x36548 + D_150) S_ZJ) 11%bv (SOff aBSL (-104))))).
Definition MUTCH {imgk : img} : list YQ0b.chunk :=
[YQ0b.mkChunk (TFX_INST + o_sec_mutex) (CVal 1 (SLit 1)); YQ0b.mkChunk (TFX_INST + o_sec_mutex + 1) (CVal 1 (SLit 0));
YQ0b.mkChunk (TFX_INST + o_sec_mutex + 2) (CVal 2 (SLit 0))].
Definition S_ZJ1s {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (mkSS (ss_pc S_ZJ1) (ss_regs S_ZJ1) (setchunks (TFX_INST + o_sec_mutex) MUTCH (ss_mem S_ZJ1)) (ss_resv S_ZJ1) (ss_facts S_ZJ1)))).
Definition S_TJ0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31be0 + D_150) S_ZJ1s))).
Definition T_J {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_LTU false (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (SAlu ALU_ADD (SOff 10 6144) (SOff aMAP 0)) S_TJ0))).
Definition T_K {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (arm BC_NE false (SAlu ALU_SRL (SOff 10 0) (SLit 48)) (SLit 0) (runto (0x31c08 + D_150) T_J)))).
Definition T_PD {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x72fcc + D_2c4) T_K))).
Definition trs_D {imgk : img} : smem := match ss_mem T_PD with rq :: rm :: rb :: r1 :: rest => rq :: rm :: rb :: trim_lo r1 (-2272) :: rest | l => l end.
Definition T_2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (addreg R_scr2 (ss_after_call T_PD trs_D sD1 (0x31cc8 + D_150))))).
Definition T_M0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31cfc + D_150) T_2))).
Definition T_Ma {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31d34 + D_150) (arm BC_LTU true (SOff aMAP 4096) (SOff aSB 0) T_M0)))).
Definition T_Mb {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x31d34 + D_150) (arm BC_GEU true (SOff aMAP 4096) (SOff aSB 137438953472) (runto (0x31d0c + D_150) (arm BC_LTU false (SOff aMAP 4096) (SOff aSB 0) T_M0)))))).
Definition T_N {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (noconds (forget T_Ma sGA [11]%bv)))).

Definition T_L3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54344 + D_2c4) T_N))).
Definition T_L3l {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5452c + D_2c4) (armR BC_GEU true 14 10 T_L3)))).
Definition T_L3lo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) (armR BC_GEU true 14 11 T_L3l)))).
Definition T_L3h {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54384 + D_2c4) (armR BC_GEU false 14 10 T_L3)))).
Definition T_L3h2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5452c + D_2c4) (armR BC_LTU true 7 10 T_L3h)))).
Definition T_L3h3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5456c + D_2c4) (armR BC_GEU false 14 11 T_L3h2)))).
Definition T_L3hi {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) (armR BC_GEU false 5 11 T_L3h3)))).
Definition T_M3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (psJ sL3 T_L3lo))).

Definition T_P3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch T_M3 (ss_mem T_M3) sM3 CLOB_MS (0x31da0 + D_150)))).
Definition T_P4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (pin T_P3 22%bv (SOff aUE 0)) 8%bv (SOff aMS (-4096))))).
Definition T_P5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x31db0 + D_150) T_P4) 11%bv (SOff aRL 0)))).
Definition T_L4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54344 + D_2c4) T_P5))).
Definition T_L4l {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5452c + D_2c4) (armR BC_GEU true 14 10 T_L4)))).
Definition T_L4lo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) (armR BC_GEU true 14 11 T_L4l)))).
Definition T_L4h {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54384 + D_2c4) (armR BC_GEU false 14 10 T_L4)))).
Definition T_L4h2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5452c + D_2c4) (armR BC_LTU true 7 10 T_L4h)))).
Definition T_L4h3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5456c + D_2c4) (armR BC_GEU false 14 11 T_L4h2)))).
Definition T_L4hi {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x9b894 + D_10ec) (armR BC_GEU false 5 11 T_L4h3)))).
Definition T_M4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (psJ sL4 T_L4lo))).

Definition T_P6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (ss_after_stretch T_M4 (ss_mem T_M4) sM4 CLOB_MS (0x31db4 + D_150)))).
Definition T_P7 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (pin (runto (0x31dc0 + D_150) T_P6) 22%bv (SOff aN8DS 0)))).
Definition T_L5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54344 + D_2c4) T_P7))).
Definition T_L5l {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5452c + D_2c4) (armR BC_GEU true 14 10 T_L5)))).
Definition T_L5lo {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54594 + D_2c4) (armR BC_GEU true 14 11 T_L5l)))).
Definition T_L5h {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54384 + D_2c4) (armR BC_GEU false 14 10 T_L5)))).
Definition T_L5h2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5452c + D_2c4) (armR BC_LTU true 7 10 T_L5h)))).
Definition T_L5h3a {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54568 + D_2c4) (armR BC_GEU false 14 11 T_L5h2)))).
Definition T_L5h3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x5456c + D_2c4) (armR BC_LTU false 6 11 T_L5h3a)))).
Definition T_L5hi {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (runto (0x54594 + D_2c4) (armR BC_GEU false 5 11 T_L5h3)))).
Definition T_R {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (psJt sL5 T_L5lo))).


