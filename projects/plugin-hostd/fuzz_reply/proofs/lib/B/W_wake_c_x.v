(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (G-BRA): the ARx-GENERIC twin of lib/B/W_wake_c.v (the contract of image B's
   wake, 0x82484, 101 instructions), in the form of lib/B/W_contract_x.v's twins: afn_pre_x / ajournal_gx_x over a
   Section relation ARx (its third argument the head set Hp) and the program statics PST; Hp after S, Hp' after S'.
   Hand-written (W_wake_c.v has no lib/A twin: image A inlines wake).  Proves no function (kind: statement text); the
   walk that proves wk_spec_x is lib/B/W_wake_x.v pb_wake_x.

   Every premise and conjunct of W_wake_c.v's wk_spec / wk_post is kept.  wk_post_x adds ONE conjunct, the SEAT fact
   `exists f, S' = set_fs f S`: wake's only allocator-state changes are its class-0 fake frame's stack_malloc (a set_fs,
   W_frame_x.v Section fsp's SMALLOC) and its release stack_free_state (a set_fs, Reusable/YG01.v:577), and set_fs over
   set_fs is set_fs (Reusable/YG00.v:200).  A caller carries any invariant that ignores the fake stack (the room
   round's rp_RM, its law rp_RPF) across the call with it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_wake_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable RG : rep_globals.

(* W_wake_c.v wk_post, over ARx, plus the seat fact *)
Definition wk_post_x (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
: world SEGS -> config -> Prop :=
fun W' c' => exists regs' ly' S' Hp' mem' md' k,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_x SEGS B PST ARx [] 0 [] WK_STK (spZ regs) [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
aregs_preserved regs regs' /\
ablocks B ly' S' = ablocks B ly S /\
(forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
awake_at RG W' mem' /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W') mem' (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)) /\
(exists f, S' = set_fs f S).

(* W_wake_c.v wk_spec, over ARx *)
Definition wk_spec_x (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch,
afn_pre_x SEGS B ARx WK_STK ly S Hp W regs mem md ch ->
count_cid 0 (frames S) < fs_frames 0 ->
awake_at RG W mem ->
rom_view SEGS W mem ->
SRr SEGS W (cfg_at SEGS pc regs mem md) (wk_post_x regs ly S Hp W mem md).
End c.
End b.
End a.
