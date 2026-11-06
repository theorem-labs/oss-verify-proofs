(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF2d YF1q YF2h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition SS_L1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((xrun_to (0x5e984 + D_2c4) YF2h.SS0)))).
Definition SS_A {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((xrun_to (0x5aea0 + D_2c4) (xpin 12 (SOff 37%nat 0) (xrun_to (0x53154 + D_2c4) (xpin 11 (SLit 0) (xrun
(xpin 10 (SLit TFX_IAL_LO) (xadd R_IM (xadd R_SCR (xafter 54 (-2128) (0x53140 + D_2c4) SS_L1)))))))))))).
Definition SS_B {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((let s0 := xadd R_OBJ (xadd R_SCR (xafterU 70 (0x532a0 + D_2c4) SS_A)) in
let s1 := xrun s0 in
let s2 := xpin 17 (SLit 2) (xpin 16 (SLit 3) (xpin 14 (SLit 2) (xpin 15 (SLit 255) s1))) in
let s3 := xrun s2 in
let s4 := xrun (xpin 11 (SLit 1) s3) in
xrun_to (0x72fcc + D_2c4) (xpin 11 (SLit 3) s4))))).
Goal forall imgk : img, ss_pc SS_A = (0x5aea0 + D_2c4) /\ ss_pc SS_B = (0x72fcc + D_2c4). Proof. intros imgk. split; img_refl. Qed.
Definition xafterD (k : nat) (retpc : Z) (ss : sstate) : sstate :=
ss_after_call ss (match ss_mem ss with robj :: rscr :: rest => robj :: trim_lo rscr (-2176) :: rest | _ => [] end) k retpc.
Definition R_SCR2 : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- ASTACK) (- 2176) (- ASTACK) (- 2176) [].
Definition xtake {imgk : img} (ss : sstate) : sstate :=
match sym_step_sh tfxsegs tfxtbl_rtF ss with SStop (SR_branch c a b) => add_cond ss (mkAC c a b) | _ => ss end.
Definition xfall {imgk : img} (ss : sstate) : sstate :=
match sym_step_sh tfxsegs tfxtbl_rtF ss with SStop (SR_branch c a b) => add_cond ss (mkAC (neg_bc c) a b) | _ => ss end.
Definition SS_P {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((xrun (xpin 15 (SOff 39%nat 0) (xrun_to (0x35c28 + D_150) (xadd R_SCR2 (xafterD 86 (0x35b08 + D_150) SS_B)))))))).
Definition SS_ML {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((xpin 12 (SOff 43%nat 0) (xpin 10 (SOff 41%nat 0)
(xrun (xtake (xrun (xpin 15 (SLit 0) (xpin 11 (SOff 42%nat 0) (xrun (xtake SS_P)))))))))))).
Definition F_R {imgk : img} : facts := ltac:(img_eval_last (fun imgk : img => ((ss_facts (ss_after_stretch SS_P (ss_mem SS_P) 102 [11; 12; 13; 14; 15; 16]%bv (0x35db4 + D_150)))))).
Definition SS_R {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((set_facts (xpin 28 (SOff 111%nat 0) (xpin 17 (SOff 110%nat 0) (xpin 7 (SOff 109%nat 0) (xpin 5 (SOff 108%nat 0)
(ss_after_stretch SS_ML (ss_mem SS_ML) 102 [11; 12; 13; 14; 15; 16]%bv (0x35db4 + D_150)))))) F_R)))).
Definition SS_E {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => ((xrun_to (0x35dd8 + D_150) SS_R)))).
Goal forall imgk : img, ss_pc SS_P = (0x54344 + D_2c4) /\ ss_pc SS_ML = (0x9b894 + D_10ec) /\ ss_pc SS_R = (0x35db4 + D_150) /\ ss_pc SS_E = (0x35dd8 + D_150). Proof. intros imgk. repeat split; img_refl. Qed.
Goal forall imgk : img, facts_leb F_R (ss_facts (ss_after_stretch SS_ML (ss_mem SS_ML) 102 [11; 12; 13; 14; 15; 16]%bv (0x35db4 + D_150))) = true. Proof. intros imgk. img_case; vm_compute. all: img_refl. Qed.
