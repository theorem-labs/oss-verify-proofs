(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/CLrefill0.v (cold/c-asan-realloc-c5 ced28ed2383, file sha256 fa358ad428e7) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* The refill callee's contract with a RAW frame (statement only; lib/AU/MnRefillRB.v:399 proves its _em form, tfib_refill_okR_em).  The released
   YFl1.tfib_refill_spec frames the memory through [aview] only (YG0d.acall_post), which hides the bytes of hidden
   pages; an ARX-style relation reads those raw bytes.  [refill_leafR] keeps the released [refill_leaf] as its first
   conjunct and adds: outside the bytes owned before or after the call and outside the callee's stack window
   [spZ regs - RSTACK, spZ regs), the raw memory at the return equals the memory at the call. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP09 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Section d.
Variable B : asyms.
Definition refill_leafR (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (c : Z)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
refill_leaf B ly S W regs mem md c r W' c' /\
exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
   ~ (spZ regs - RSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x).
Definition tfib_refill_specR : Prop :=
forall ly S W regs mem md c,
refill_pre B ly S W regs mem md c ->
amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs mem md) (refill_leafR ly S W regs mem md c).
End d.
End b.
