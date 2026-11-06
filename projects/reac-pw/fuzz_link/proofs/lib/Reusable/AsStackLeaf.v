(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene, shared by both images (lib/Reusable). STATEMENTS ONLY.

   The two callee summaries the class-8 stack walks consume: __asan::PoisonShadow and the __asan::MemToShadow copy
   that __asan_stack_malloc_8 and __asan_stack_free_8 call. They are stated in the shape of the contracts in
   lib/Reusable/AsStackSz.v (cgif_rgb_fuzzer lib/YG0e.v:17-61) and in the form the class-8 walk consumes them at
   its call points (cgif_rgb_fuzzer's class-7 walk runs both inline instead: lib/YF9c.v:356-392, lib/YF3h.v:30).
   Owner of the proofs: a Theorem Labs lane. Consumers (Section hypotheses): the class-8 stack-malloc walk (segments C, D) and
   the stack-free walk (a Theorem Labs lane). The entry pcs are parameters; each image's addresses live in its Tbl files
   (lib/A/Rt/... and lib/AU/Rt/...), not here.

   NO IMAGE VALUE APPEARS IN THIS FILE a Theorem Labs lane: both entry pcs are
   parameters, and each image's addresses live in its own table, lib/A/Rt/StackMalloc8Tbl.v and
   lib/AU/Rt/StackMalloc8Tbl.v (PC_POISON_SHADOW, PC_MEM_TO_SHADOW), measured there. The measurement record,
   with every address, the disassembly it comes from and the relocation finding it guards against ("the
   460-byte trap"), is (internal path) and PORT.md.

   What the summaries need from AR, and why AR is the only state premise (MEASURED, from the disassembly):
   - PoisonShadow reads start-up constant cells: the shadow-offset cell, kHighMemEnd, kMidMemBeg / kMidMemEnd,
     can_poison_memory, clear_shadow_mmap_threshold and the REAL(memset) pointer. MemToShadow reads the shadow
     offset and the same kHighMemEnd / kMidMem* cells. They are start-up facts, so they come from AR's
     constant-cell list; a Theorem Labs lane's review (CLASS8-REVIEW.md) makes keeping exactly these cells in the
     relocated list a CONDITION of the port. While that list is not trustworthy on the dry-run tree, a Theorem Labs lane states
     them as named Section hypotheses of ITS proof, which is why they do not appear in these statements.
   - the value premise 0 <= v < 256 with v <> 0 reaches the can_poison_memory test; v = 0 (the stack-malloc call)
     skips it. Both values end at the same tail jump into musl memset, so both return to the ra that is live at
     the entry.
   - clear_shadow_mmap_threshold keeps the walk out of the ReleaseMemoryPagesToOS path, the only path on which
     PoisonShadow writes a global of its own. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.

(* The stack PoisonShadow and its callee own below the caller's sp. MEASURED: PoisonShadow's own frame is 64 bytes
   and it reaches musl memset by a tail jump with its frame already released, so 256 bytes is a window with slack.
   Both call sites can give it: the stack-malloc entry calls PoisonShadow with its own frame below sp0, the
   stack-free entry jumps to it with sp = sp0, and ecall_pre gives the caller ESTACK = 4096 bytes below sp0. *)
Definition PS_STK : Z := 256.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

(* __asan::PoisonShadow(p, n, v) over the shadow of ONE fake frame.
   a0 = p, a1 = n, a2 = v; it writes `v` into the n/8 shadow bytes of [p, p + n), touches nothing else outside its
   own stack window, keeps AR for the ambient state, keeps the callee-saved registers and returns to the ra that is
   live at `pc`.

   The frame premises (0 <= cid <= 10, 0 <= pos < fs_frames cid, the range inside frame (cid, pos)) are what makes
   "AR kept" true: AR puts NO value on the shadow of a fake frame, live or free (CLASS8-DESIGN.md section 2:
   am_shadow constrains heap chunks and fa_poison_ranges only, am_zshadow the real stack and the static ranges, and
   a live frame's shadow is client while a free frame's shadow is aowned but unconstrained). The statement does NOT
   ask the frame to be live, because the two call sites differ:
     - __asan_stack_malloc_8 CALLS it with v = 0 and the frame LIVE in the post-state S';
     - __asan_stack_free_8 TAIL-JUMPS to it (`j`) with v = 0xf5 and the frame FREE in
       stack_free_state cid pos S.
   This is also the TAIL-ENTRY form: the post returns to `raZ regs`, i.e. to the ra live at `pc`. At free_8's `j`
   that register still holds free_8's caller's ra (free_8 restores ra and sp before the jump),
   so the same statement is what the free_8 walk consumes, with regs = the registers at the jump. *)
Definition poison_shadow_realizes (pc : Z) : Prop :=
forall ly S W regs mem md cid pos p n v,
AR segs B ly S W mem md ->
YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + PS_STK <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - PS_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
getr regs 10 = w64 p -> getr regs 11 = w64 n -> getr regs 12 = w64 v ->
0 <= v < 256 -> 0 < n -> n mod 8 = 0 -> p mod 8 = 0 ->
frame_addr ly cid pos <= p -> p + n <= frame_addr ly cid pos + fs_frame_bytes cid ->
(forall a, shadow_addr p <= a < shadow_addr p + n / 8 -> apresent (w_H W) mem a) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n / 8 -> aview segs (w_H W) mem' (shadow_addr p + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr p <= a < shadow_addr p + n / 8) ->
~ (spZ regs - PS_STK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - PS_STK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* __asan::MemToShadow(p): a0 := SHADOW_OFF + p / 8 = shadow_addr p, and nothing else at all.
   MEASURED: on the path a fake-frame address takes it is a leaf - no store, no sp change, only the constant-cell
   loads; the CHECK path that would build a frame is not reached. __asan_stack_malloc_8 calls it with a0 = the
   frame address and DISCARDS the result (the next instruction overwrites a0); __asan_stack_free_8 calls it the
   same way. The post names the result anyway, so a consumer that needs it has it. *)
Definition mem_to_shadow_realizes (pc : Z) : Prop :=
forall ly S W regs mem md cid pos p,
AR segs B ly S W mem md ->
YK0s.ret_ok (getr regs 1) ->
0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
getr regs 10 = w64 p ->
frame_addr ly cid pos <= p -> p < frame_addr ly cid pos + fs_frame_bytes cid ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (shadow_addr p) /\
(forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End c.
End b.
