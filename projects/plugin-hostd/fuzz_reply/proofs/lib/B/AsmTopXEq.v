(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane): copied from lib/A/AsmTopXEq.v (a working branch dac32c4fd94) for fuzz_reply.asan-ubsan (image B): the module paths changed and the WFX / TOPX aliases are written out. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane): image B's (fuzz_reply.asan-ubsan) twin of lib/A/AsmTopXEq.v
   (a working branch dac32c4fd94). Rule 24: no function is proved here (instance discharge); the
   function's reuse search is lib/B/RT_asan_stack_malloc_0.v's header:
   RULE 24: `proof-index __asan_stack_malloc_0 0x3d1c0`: 0 released lemmas for either key; no released FUNCTION proof found. Second-agent
   check: CONFIRM (the 25 unreleased hits are all statements or symbols; in the lemma index over 17316 refs, no lib/B class-0 walk declaration, and every stack_malloc0_contract / tfib_stack_malloc_at / asm0 / ASM0 declaration is lib/A). REUSE = this port of the image-A walk of the same function.
   Changes from A's text: module paths lib.A -> lib.B (AB1v AD2l -> YB1v YD2l; W_* and AsmTopX -> their lib/B files);
   the row is stated with the qualified names W_frame_x / W_LLVMFuzzerTestOneInput_top_x (A's WFX / TOPX aliases
   dropped), the consumer's fixed text. No numeral.
   Theorem Labs, 2026-10-30 (a Theorem Labs lane), the class-1 port: ASM1_topx, B top_x's Hypothesis ASM1 text
   (W_LLVMFuzzerTestOneInput_top_x.v's Hypothesis ASM1), from AsmTopX's asm1_pres_ARX; ASM0_topx's text is unchanged. Its function's
   reuse search is lib/B/RT_asan_stack_malloc_1_x.v's header (RULE 24: proves function __asan_stack_malloc_1,
   image B entry 0x3d334; `proof-index __asan_stack_malloc_1 0x3d334`: 0 released lemmas for both keys;
   second-agent check: CONFIRM, lib/B class-1 walk declarations: 0).

   The row ASM0 (TOPX-HYPS.md (sha256 47b88854dcb3; internal record) table) AT B top_x's OWN relation:
   W_LLVMFuzzerTestOneInput_top_x.ARX (lib/B/W_LLVMFuzzerTestOneInput_top_x.v's Definition ARX) is AsmTopX.ARX_asm by
   reflexivity (segs = pa_segs PB_fr = tfibsegs, lib/B/Rt/Bcmp.v:44), so the row is AsmTopX's theorem by conversion. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YG00 YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_frame_x W_LLVMFuzzerTestOneInput_top_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AsmTopX.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* top_x's relation IS ARX_asm *)
Lemma ARX_asm_topx : W_LLVMFuzzerTestOneInput_top_x.ARX = ARX_asm.
Proof. reflexivity. Qed.

(* ASM0 at top_x's own segs and relation: the consumer's text (B top_x's ASM rows, Hypothesis ASM1's shape at class 0) *)
Theorem ASM0_topx : W_frame_x.astack_malloc_pres_x (@pa_segs _ fr_prog_listing PB_fr) TfibB W_LLVMFuzzerTestOneInput_top_x.ARX 0.
Proof. exact asm0_pres_ARX. Qed.

(* ASM1 at top_x's own segs and relation: B top_x's Hypothesis ASM1 (W_LLVMFuzzerTestOneInput_top_x.v), verbatim *)
Theorem ASM1_topx : W_frame_x.astack_malloc_pres_x (@pa_segs _ fr_prog_listing PB_fr) TfibB W_LLVMFuzzerTestOneInput_top_x.ARX 1.
Proof. exact asm1_pres_ARX. Qed.

End e.

(* The lane's Print Assumptions (toolchain/allowed-axioms.txt). *)
Check ASM0_topx.
Print Assumptions ASM0_topx.
Check ASM1_topx.
Print Assumptions ASM1_topx.
