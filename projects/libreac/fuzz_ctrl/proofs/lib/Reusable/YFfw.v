(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFfw.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_ctrl's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YFeq YFgi YFfv YFgm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition SS_L1 : sstate := Eval vm_compute in (xrun_to 0x5e9f0 YFgm.SS0).
Definition SS_A : sstate := Eval vm_compute in
(xrun_to 0x5af0c (xpin 12 (SOff 37%nat 0) (xrun_to 0x53504 (xpin 11 (SLit 0) (xrun
(xpin 10 (SLit TFIB_IAL_LO) (xadd R_IM (xadd R_SCR (xafter 54 (-2128) 0x534f0 SS_L1))))))))).
Definition SS_B : sstate := Eval vm_compute in
(let s0 := xadd R_OBJ (xadd R_SCR (xafterU 70 0x53650 SS_A)) in
let s1 := xrun s0 in
let s2 := xpin 17 (SLit 2) (xpin 16 (SLit 3) (xpin 14 (SLit 2) (xpin 15 (SLit 255) s1))) in
let s3 := xrun s2 in
let s4 := xrun (xpin 11 (SLit 1) s3) in
xrun_to 0x73038 (xpin 11 (SLit 3) s4)).
Goal ss_pc SS_A = 0x5af0c /\ ss_pc SS_B = 0x73038. Proof. split; reflexivity. Qed.
Definition xafterD (k : nat) (retpc : Z) (ss : sstate) : sstate :=
ss_after_call ss (match ss_mem ss with robj :: rscr :: rest => robj :: trim_lo rscr (-2176) :: rest | _ => [] end) k retpc.
Definition R_SCR2 : YP09.region := YP09.mkRegion (Some 2%nat) (- ASTACK) (- 2176) (- ASTACK) (- 2176) [].
Definition xtake (ss : sstate) : sstate :=
match sym_step_sh tfibsegs tfibtbl_rtF ss with SStop (SR_branch c a b) => add_cond ss (mkAC c a b) | _ => ss end.
Definition xfall (ss : sstate) : sstate :=
match sym_step_sh tfibsegs tfibtbl_rtF ss with SStop (SR_branch c a b) => add_cond ss (mkAC (neg_bc c) a b) | _ => ss end.
Definition SS_P : sstate := Eval vm_compute in
(xrun (xpin 15 (SOff 39%nat 0) (xrun_to 0x36470 (xadd R_SCR2 (xafterD 86 0x36350 SS_B))))).
Definition SS_ML : sstate := Eval vm_compute in
(xpin 12 (SOff 43%nat 0) (xpin 10 (SOff 41%nat 0)
(xrun (xtake (xrun (xpin 15 (SLit 0) (xpin 11 (SOff 42%nat 0) (xrun (xtake SS_P))))))))).
Definition F_R : facts := Eval vm_compute in (ss_facts (ss_after_stretch SS_P (ss_mem SS_P) 102 [11; 12; 13; 14; 15; 16]%bv 0x365fc)).
Definition SS_R : sstate := Eval vm_compute in
(set_facts (xpin 28 (SOff 111%nat 0) (xpin 17 (SOff 110%nat 0) (xpin 7 (SOff 109%nat 0) (xpin 5 (SOff 108%nat 0)
(ss_after_stretch SS_ML (ss_mem SS_ML) 102 [11; 12; 13; 14; 15; 16]%bv 0x365fc))))) F_R).
Definition SS_E : sstate := Eval vm_compute in (xrun_to 0x36620 SS_R).
Goal ss_pc SS_P = 0x543b0 /\ ss_pc SS_ML = 0x98e34 /\ ss_pc SS_R = 0x365fc /\ ss_pc SS_E = 0x36620. Proof. repeat split; reflexivity. Qed.
Goal facts_leb F_R (ss_facts (ss_after_stretch SS_ML (ss_mem SS_ML) 102 [11; 12; 13; 14; 15; 16]%bv 0x365fc)) = true. Proof. vm_compute. reflexivity. Qed.
