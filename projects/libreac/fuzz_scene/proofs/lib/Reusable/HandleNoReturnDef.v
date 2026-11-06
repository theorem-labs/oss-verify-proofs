(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of the ASan runtime entry __asan_handle_no_return, in the form of the
   callee contracts of proofs/cgif/cgif_file_fuzzer/lib/YG0d.v (astack_malloc_realizes, aintrin_realizes) over the
   asan-state definitions of that proof as libreac/fuzz_scene holds them. Its effect follows the released walk
   proofs/jsoncons/fuzz_bigint/lib/As0HandleNoReturn.v hnr_run (code equal modulo PC-relative fields): the shadow of the
   stack from one page below the entry sp - 64 up to the thread's stack top becomes 0, and the fake stack's needs_gc_
   byte becomes 1. The contract is target-independent: every address comes from the layout or the registers. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

(* The low end of the range __asan_handle_no_return unpoisons: its local sits at entry sp - 64 (frame 80, local at
   sp + 16), and UnpoisonDefaultStack takes ((&local - page) & ~(page - 1)), page = 4096. *)
Definition hnr_bottom (regs : bvmap 5 word) : Z := (spZ regs - 4160) - (spZ regs - 4160) mod 4096.

(* The fake stack's needs_gc_ byte: offset 96 of the FakeStack object (stack_size_log_ 8 bytes, then
   hint_position_[11] 88 bytes); the asan state's fs_cells (YG0n.v) pin it to 0, and FakeStack::HandleNoReturn sets
   it to 1. *)
Definition hnr_gc_addr (ly : alayout) : Z := ly_F ly + 96.

(* AR, except that the needs_gc_ byte holds 1: the memory with that byte put back to 0 satisfies AR. *)
Definition AR_gc1 (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model) : Prop :=
  exists mem0, AR segs B ly S W mem0 md /\
    mem (w64 (hnr_gc_addr ly)) = Some (Z_to_bv 8 1) /\
    (forall a, 0 <= a < 2 ^ 64 -> a <> hnr_gc_addr ly -> mem (w64 a) = mem0 (w64 a)).

(* Premises beyond ecall_pre:
   - the unpoisoned range starts inside the stack;
   - its shadow is shorter than clear_shadow_mmap_threshold (64 KiB of shadow, i.e. less than 2^19 bytes of stack), so
     FastPoisonShadow clears it with REAL(memset) and does not remap the shadow pages (no mmap, so the model only
     changes by materialisation); this also excludes UnpoisonStack's kMaxExpectedCleanupSize warning path (2^26). *)
Definition ahnr_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md,
  ecall_pre segs B ly S W regs mem md ->
  ly_stk_lo ly <= hnr_bottom regs ->
  ly_top ly - hnr_bottom regs < 2 ^ 19 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       aregs_preserved regs regs' /\ same_but_materialized md md' /\
       AR_gc1 ly S W mem' md' /\
       zero_shadow (aview segs (w_H W) mem') SHADOW_OFF (hnr_bottom regs) (ly_top ly - hnr_bottom regs) /\
       (forall a, 0 <= a < 2 ^ 64 ->
          ~ (shadow_addr (hnr_bottom regs) <= a < shadow_addr (hnr_bottom regs) + (ly_top ly - hnr_bottom regs + 7) / 8) ->
          a <> hnr_gc_addr ly -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End c.
End b.
