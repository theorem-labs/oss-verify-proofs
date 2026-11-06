(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contract of fuzz_reply.asan-ubsan's wake (0x82484, 101 instructions), which
   image B calls where image A inlines it: relay_remove TAIL-CALLS it (0x843e8 `j wake`) and relay_add calls it (the
   kit's RA_STK counts it).  Hand-written (no lib/A twin exists for mkbkit to generate).  Proves no function (kind:
   statement text); the walk that proves wk_spec is pb_wake.

   wake () is relay.c's wake: `char b = 0; if (g_wake[1] >= 0) write (g_wake[1], &b, 1);`.  On image B the byte b lives
   at F + 32 of a class-0 ASan fake frame F (__asan_stack_malloc_0 (64) at 0x824d0, taken because the
   detect_stack_use_after_return cell is 1), or of the real stack when the allocator returns 0; g_wake is read at
   0x82574 (`lw a0, 4(a0)`, a0 = &g_wake, A_OBJ 8 of lib/B/W_listing.v); with awake_at (g_wake[1] = -1) the write
   0x82584 is not reached; the frame is released (retired magic 0x45e0360e, shadow 0xf5, flag cleared at 0x825c8) and
   wake returns.  The trap at 0x82614 (`beq &g_wake, -4`) is refuted by the placement of g_wake.

   The post: a journal at G = [] (wake writes no global and no block; its fake frame is taken and released inside, so
   own = []), the callee-saved registers, the live blocks, the presence of every present IMAGE byte, g_wake[1] still -1,
   and errno's view (which the journal's image clause leaves out).  Frame 64 bytes, the stack allocator's scratch below it: WK_STK = 64 + ASTACK (the kit's RA_STK term). *)
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
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* wake's frame (its entry AF_fr_wake = 0x140, B 0x82484, is the listing's, lib/B/W_listing.v) *)
Definition WK_FRAME : Z := 64.
Definition WK_STK : Z := WK_FRAME + ASTACK.

Section c.
Variable B : asyms.
Variable RG : rep_globals.

Definition wk_post (regs : bvmap 5 word) ly S (W : world SEGS) (mem : word -> option byte) (md : Model)
: world SEGS -> config -> Prop :=
fun W' c' => exists regs' ly' S' mem' md' k,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
@ajournal_gx _ SK SEGS B [] 0 [] WK_STK (spZ regs) [] ly S W mem md [] ly' S' W' mem' md' k /\
aregs_preserved regs regs' /\
ablocks B ly' S' = ablocks B ly S /\
(* presence of IMAGE bytes (a Theorem Labs lane, proving pb_wake: __asan_stack_malloc_0's contract ASMP keeps presence only for
   in_img bytes, the new frame and its scratch; no AR law keeps allocator-owned non-image bytes below the ceiling);
   this still gives apres_kept, which is all rr_post / ra_post ask *)
(forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
awake_at RG W' mem' /\
(* errno keeps its view: the journal's image clause excludes errno (YCbq.v:363), and wake neither reaches the write
   nor calls anything that sets it (the stack allocator's frame clause keeps it); found by BRrTail: rr_post's aout_at
   reads errno after the tail call *)
(forall i, 0 <= i < 4 -> aview SEGS (w_H W') mem' (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)) /\
(* the SEAT fact (KF-COUNT, image B only: B's relay_remove tail-calls wake, so its meter step across wake needs the
   set_fs form the new MO_FR consumes; A inlines wake): wake's only allocator-state changes are its class-0 fake
   frame's stack_malloc (a set_fs, lib/B/W_frame.v aj_stack_malloc_pres_at_raw's last conjunct) and its release
   stack_free_state (a set_fs, Reusable/YG01.v stack_free_state); W_wake_c_x.v's wk_post_x states the same conjunct *)
(exists f, S' = set_fs f S).

Definition wk_spec (pc : Z) : Prop :=
forall W ly S regs mem md ch,
afn_pre SEGS B WK_STK ly S W regs mem md ch ->
count_cid 0 (frames S) < fs_frames 0 ->
awake_at RG W mem ->
rom_view SEGS W mem ->
SRr SEGS W (cfg_at SEGS pc regs mem md) (wk_post regs ly S W mem md).
End c.
End b.
End a.
