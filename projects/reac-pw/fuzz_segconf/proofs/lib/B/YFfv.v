(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFfv.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AFfv.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AFfv.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YFeq YFgi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition xrun_to (stop : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfibsegs tfibtbl_rtF FUEL stop ss).
Definition xrun (ss : sstate) : sstate := fst (sym_runN_sh tfibsegs tfibtbl_rtF FUEL ss).
Definition xpin (r : bv 5) (e : sv) (ss : sstate) : sstate := mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition xadd (r : YP09.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition xafter (k : nat) (stklo retpc : Z) (ss : sstate) : sstate :=
ss_after_call ss (match ss_mem ss with r0 :: rest => trim_lo r0 stklo :: rest | [] => [] end) k retpc.
Definition R_SCR : YP09.region := YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [].
Definition R_IM : YP09.region := YP09.mkRegion (Some 37%nat) 8 16 0 0 [YP09.mkChunk 8 (CZero 8)].
Definition SS_L1 : sstate := Eval vm_compute in (xrun_to 0x62684 SS0).
Definition SS_A : sstate := Eval vm_compute in
(xrun_to 0x5eba0 (xpin 12 (SOff 37%nat 0) (xrun_to 0x56d10 (xpin 11 (SLit 0) (xrun
(xpin 10 (SLit TFIB_IAL_LO) (xadd R_IM (xadd R_SCR (xafter 54 (-2128) 0x56cfc SS_L1))))))))).
Definition xafterU (k : nat) (retpc : Z) (ss : sstate) : sstate :=
ss_after_call ss (match ss_mem ss with rim :: _ :: rfr :: rest => rim :: trim_lo rfr (-64) :: rest | _ => [] end) k retpc.
Definition R_OBJ : YP09.region := YP09.mkRegion (Some 2%nat) (- 2128) (- 64) 0 0
[YP09.mkChunk (- 2128) (CVal 8 (SOff 2 (- 2112))); YP09.mkChunk (- 2120) (CVal 8 (SOff 36%nat 0))].
Definition SS_B : sstate := Eval vm_compute in
(let s0 := xadd R_OBJ (xadd R_SCR (xafterU 70 0x56e5c SS_A)) in
let s1 := xrun s0 in
let s2 := xpin 17 (SLit 2) (xpin 16 (SLit 3) (xpin 14 (SLit 2) (xpin 15 (SLit 255) s1))) in
let s3 := xrun s2 in
let s4 := xrun (xpin 11 (SLit 1) s3) in
xrun_to 0x76de0 (xpin 11 (SLit 3) s4)).
