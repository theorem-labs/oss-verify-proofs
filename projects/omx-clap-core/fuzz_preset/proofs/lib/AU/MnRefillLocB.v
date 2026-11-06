(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillLoc.v (a working branch 29b7505aa27, file sha256 d444e2c90fc1) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at 74f20580f552) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve resolve-B102.txt (sha256 5cd2316e3413; internal record) (0 lines name this file); 0 numerals changed. *)
(* Theorem Labs, 2026-10-29 (a Theorem Labs lane, hand H1 of task MEMNORM; lead a Theorem Labs lane, integrator ReallocPrimary).
   rule 24: no function proved (kind: run invariant twin - the refill callee's leaf with the memnorm keep, and the
   its composition).

   - [refill_leafR_em]: CLrefill0.refill_leafR (CLrefill0.v:26-33) plus `MemnormT.memnorm_keep tfibsegs mem mem'` inside
     the same existential as the raw frame; [refill_leafR_em_R] drops the keep; [tfib_refill_specR_em] is
     CLrefill0.tfib_refill_specR over it (the Enqueue miss arm's premise shape, CLenqcgif.v:213).
   Keeps compose by a Theorem Labs lane's MemnormLoc.memnorm_keep_trans.
   It holds no image constant (the location facts at cgif's numbers are MnRefillLoccgif.v), so a consumer instance
   (preset's) relocates it by module path only.
   Every existing statement is unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP09 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CLrefill0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT YAkMemnorm.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The leaf.                                                                                                        *)
Section d.
Variable B : asyms.
Definition refill_leafR_em (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (c : Z)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
refill_leaf B ly S W regs mem md c r W' c' /\
exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
   ~ (spZ regs - RSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
MemnormT.memnorm_keep tfibsegs mem mem'.
Lemma refill_leafR_em_R : forall ly S W regs mem md c r W' c',
  refill_leafR_em ly S W regs mem md c r W' c' -> refill_leafR B ly S W regs mem md c r W' c'.
Proof.
intros ly S W regs mem md c r W' c' [L (regs' & mem' & md' & Ec & RAW & _)].
split; [exact L|]. exists regs', mem', md'. split; [exact Ec | exact RAW].
Qed.
Definition tfib_refill_specR_em : Prop :=
forall ly S W regs mem md c,
refill_pre B ly S W regs mem md c ->
amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs mem md) (refill_leafR_em ly S W regs mem md c).
Lemma tfib_refill_specR_of_em : tfib_refill_specR_em -> tfib_refill_specR B.
Proof.
intros H ly S W regs mem md c P. eapply amreal_mono; [| exact (H ly S W regs mem md c P)].
intros r W' c' HL. exact (refill_leafR_em_R ly S W regs mem md c r W' c' HL).
Qed.
End d.

End b.
