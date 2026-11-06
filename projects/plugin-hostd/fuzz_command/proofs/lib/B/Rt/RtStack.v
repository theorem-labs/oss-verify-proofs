(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: only the side-stack contracts of cgif_rgb_fuzzer's lib/YG0e.v (astack_malloc_sz_realizes, astack_free_realizes), restated over the asan-state definitions of the cgif_file_fuzzer proof as plugin-hostd/fuzz_command holds them; module names; and one contract added for the classes that fill the whole frame's shadow (astack_free_cls_realizes). *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Rt/RtStack.v for fuzz_command.asan-ubsan: module paths and the runtime's addresses in that image. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.

(* The side-stack entries of fuzz_command.asan-ubsan, and which contract each one has.

   Measured on the pinned image (projects/plugin-hostd/bin/fuzz_command/fuzz_command.asan-ubsan):

   __asan_stack_malloc_0 0x3f954, _1 0x3fac8, _3 0x3fc58, _4 0x3fe04, _5 0x3ffd0: the shadow fill is a straight-line
     store sequence over the whole frame (class <= 6), so the size in a0 does not change what they write. Their
     contract is cgif_file's own [astack_malloc_realizes segs B cid] (Reusable/YG0d.v:284); this file adds nothing
     for them.
   __asan_stack_malloc_7 0x40290: calls PoisonShadow(ptr, size, 0), so it zeroes size/8 shadow bytes only. Its
     contract is [astack_malloc_sz_realizes], the cgif_rgb form.
   __asan_stack_free_5 0x401dc: stores the 0xf5 word 32 times = the whole frame's 256 shadow bytes; a1 (the size) is
     overwritten before any use. Its contract is [astack_free_cls_realizes].
   __asan_stack_free_7 0x4040c: calls PoisonShadow(ptr, size, 0xf5), so it fills size/8 shadow bytes. Its contract is
     [astack_free_realizes], the cgif_rgb form.
   Both free entries first store 0 to the saved flag word at frame + fs_frame_bytes cid - 8. *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

(* cgif_rgb_fuzzer lib/YG0e.v:17-31. The class-7 side-stack allocation: a0 carries the frame size, and only that
   many shadow bytes are zeroed. *)
Definition astack_malloc_sz_realizes (pc cid : Z) : Prop :=
forall ly S W regs mem md pos S' n,
ecall_pre segs B ly S W regs mem md ->
getr regs 10 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
count_cid cid (frames S) < fs_frames cid ->
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S' W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly cid pos) /\
zero_shadow (aview segs (w_H W) mem') SHADOW_OFF (frame_addr ly cid pos) n /\
rdword (aview segs (w_H W) mem') (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* cgif_rgb_fuzzer lib/YG0e.v:32-46. The class-7 side-stack release: a1 carries the frame size, and only that many
   shadow bytes take the after-return value 0xf5. *)
Definition astack_free_realizes (pc cid : Z) : Prop :=
forall ly S W regs mem md pos n,
ecall_pre segs B ly S W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 (frame_addr ly cid pos) -> getr regs 11 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
rdword (aview segs (w_H W) mem) (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly (stack_free_state cid pos S) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n / 8 -> aview segs (w_H W) mem' (shadow_addr (frame_addr ly cid pos) + i) = Some 0xf5) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + n / 8) ->
a <> flag_addr ly cid pos -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* The release entry of a class that fills the whole frame's shadow (class <= 6, here class 5 at 0x401dc). The size
   in a1 is read by nothing, so the contract does not constrain it and the conclusion covers fs_frame_bytes cid / 8
   shadow bytes. Everything else is [astack_free_realizes] above. *)
Definition astack_free_cls_realizes (pc cid : Z) : Prop :=
forall ly S W regs mem md pos n,
ecall_pre segs B ly S W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 (frame_addr ly cid pos) -> getr regs 11 = w64 n ->
rdword (aview segs (w_H W) mem) (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly (stack_free_state cid pos S) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < fs_frame_bytes cid / 8 ->
aview segs (w_H W) mem' (shadow_addr (frame_addr ly cid pos) + i) = Some 0xf5) /\
(forall a, 0 <= a < 2 ^ 64 ->
~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
a <> flag_addr ly cid pos -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).

End c.
End b.
