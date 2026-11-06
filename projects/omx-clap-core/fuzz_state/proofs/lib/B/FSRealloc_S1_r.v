(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fuzz_state image B, realloc segment S1 (a Theorem Labs lane, 2026-10-29).
   The symbolic states of the walk (SS_L1R .. SS_ER) and its regions R_SCRR / R_IMR / R_OBJR.  The B twin of
   lib/A/FSRealloc_S1_r.v (a working branch ce07ca45bca; port of cgif_rgb_fuzzer lib/YF6r.v).
   Every B address literal is the A file's at fs-addr-map.tsv's B column (internal path), each checked by
   capstone (RV64, no compressed instructions) over the pinned fuzz_state.asan-ubsan (sha256 5ac5ce0954f87e2d...):
   same instruction word at the A and the B address.
   Stops: internal_allocator 0x5e964 [0x5e8f4] (0x53524 `jal 0xb440`, return pc 0x53528), the AsanInited probe's
   `ld a3, 8(a2)` 0x5353c [0x534cc], UnwindImpl 0x5ae80 [0x5ae10] (0x53678 `jal 0x7808`, return pc 0x5367c [0x5360c]),
   Allocate's entry 0x31f64 [0x31ef4] (Reallocate 0x32a00 `jal -0xa9c`). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10-29: the image-B twin of lib/A/FSRealloc_S1_r.v (a working branch ce07ca45bca): image B's modules (lib/B/Yxxx for lib/A/Axxx) and fuzz_state.asan-ubsan's addresses (a Theorem Labs lane's realloc-thin/fs-addr-map.tsv, capstone-checked). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFeq FSRealloc_S1_tbl FSRealloc_S1_u.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.
Definition xrun_to (stop : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfibsegs tfibtbl_rr FUEL stop ss).
Definition xrun (ss : sstate) : sstate := fst (sym_runN_sh tfibsegs tfibtbl_rr FUEL ss).
Definition xpin (r : bv 5) (e : sv) (ss : sstate) : sstate := mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition xadd (r : YP09.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition xafter (k : nat) (stklo retpc : Z) (ss : sstate) : sstate :=
ss_after_call ss (match ss_mem ss with r0 :: rest => trim_lo r0 stklo :: rest | [] => [] end) k retpc.
Definition xafterU (k : nat) (retpc : Z) (ss : sstate) : sstate :=
ss_after_call ss (match ss_mem ss with rim :: _ :: rfr :: rest => rim :: trim_lo rfr (-64) :: rest | _ => [] end) k retpc.
Definition IFRAMER : Z := 2144.
Definition R_SCRR : YP09.region := YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAMER) (- ASTACK) (- IFRAMER) [].
Definition R_IMR : YP09.region := YP09.mkRegion (Some 37%nat) 8 16 0 0 [YP09.mkChunk 8 (CZero 8)].
Definition R_OBJR : YP09.region := YP09.mkRegion (Some 2%nat) (- 2136) (- 64) 0 0
[YP09.mkChunk (- 2136) (CVal 8 (SOff 2 (- 2120))); YP09.mkChunk (- 2128) (CVal 8 (SOff 36%nat 0))].
Definition SS_L1R : sstate := Eval vm_compute in (xrun_to 0x5e964 FSRealloc_S1_u.SS0).
Definition SS_P1R : sstate := Eval vm_compute in (xrun (xpin 10 (SLit TFIB_IAL_LO) (xadd R_IMR (xadd R_SCRR (xafter 54 (-2144) 0x53528 SS_L1R))))).
Definition SS_P2R : sstate := Eval vm_compute in (xrun_to 0x5353c (xpin 11 (SLit 0) SS_P1R)).
Definition SS_AR : sstate := Eval vm_compute in (xrun_to 0x5ae80 (xpin 12 (SOff 37%nat 0) SS_P2R)).
Definition SS_ER : sstate := Eval vm_compute in (xrun_to 0x31f64 (xadd R_OBJR (xadd R_SCRR (xafterU 70 0x5367c SS_AR)))).
Goal ss_pc SS_L1R = 0x5e964 /\ ss_pc SS_P2R = 0x5353c /\ ss_pc SS_AR = 0x5ae80 /\ ss_pc SS_ER = 0x31f64. Proof. repeat split; reflexivity. Qed.
