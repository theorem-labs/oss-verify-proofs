(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: relocated from proofs/omx-clap-core/fuzz_state/lib/A/FSRealloc_S1_r.v (hub ddc081c1a03, blob 85a1ffc06e6a) to omx-clap-core/fuzz_preset's asan image A by a Theorem Labs lane's internal file alreloc.py (frozen-c4338d099cfb8025), every image numeral moved by symbol + offset; record, the internal file A5.md. *)
(* fuzz_state image A, realloc segment S1 (RtS1, 2026-10-29).
   The symbolic states of the walk (SS_L1R .. SS_ER) and its regions R_SCRR / R_IMR / R_OBJR.
   Port of cgif_rgb_fuzzer lib/YF6r.v (released donor of the realloc prefix; hub checkout 102d6008296,
   byte-equal to h-state-a5/realloc-thin/donor/), translated by h-state-a5/realloc-thin/s1/translate_rgb_to_fs.py:
   module names mapped to fs's (the map checked on cgif_rgb YF2w / YF2i / YF1y against fs's A/AFh1 / AFgn / AFg3),
   img_* tactics to plain ones, (addr + D_xxx) to fs.asan addresses (the internal file fs-addr-map.tsv; 0x53b7c = return pc
   of 0x53b78 `jal 0xb440` (-> 0x5efb8), disassembled).
   Changed: SS_ER runs to Allocate's entry 0x325b8 (through Reallocate's `jal -0xa9c` 0x33054) instead of 0x33054 *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFeq FSRealloc_S1_tbl FSRealloc_S1_u.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
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
Definition SS_L1R : sstate := Eval vm_compute in (xrun_to 0x5efb8 FSRealloc_S1_u.SS0).
Definition SS_P1R : sstate := Eval vm_compute in (xrun (xpin 10 (SLit TFIB_IAL_LO) (xadd R_IMR (xadd R_SCRR (xafter 54 (-2144) 0x53b7c SS_L1R))))).
Definition SS_P2R : sstate := Eval vm_compute in (xrun_to 0x53b90 (xpin 11 (SLit 0) SS_P1R)).
Definition SS_AR : sstate := Eval vm_compute in (xrun_to 0x5b4d4 (xpin 12 (SOff 37%nat 0) SS_P2R)).
Definition SS_ER : sstate := Eval vm_compute in (xrun_to 0x325b8 (xadd R_OBJR (xadd R_SCRR (xafterU 70 0x53cd0 SS_AR)))).
Goal ss_pc SS_L1R = 0x5efb8 /\ ss_pc SS_P2R = 0x53b90 /\ ss_pc SS_AR = 0x5b4d4 /\ ss_pc SS_ER = 0x325b8. Proof. repeat split; reflexivity. Qed.
