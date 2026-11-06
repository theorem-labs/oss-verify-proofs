(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_rgb_fuzzer/lib/YG0e.v (its Definition astack_malloc_sz_realizes, lines 17-33),
   with its module paths changed to fuzz_scene's relocated cgif framework (lib/Reusable/YG0d.v and its imports). Not named YG0e:
   cgif_file's own lib/Reusable/YG0e.v is a different file with the same name. *)

(*   The size-dependent stack-malloc contract. The shared stack-free contract (astack_free_realizes) is
   lib/Reusable/StackFreeDef.v (libreac/fuzz_grant c3bfa00452c) and the set-shadow contract (aset_shadow_realizes) is
   a Theorem Labs lane's SetShadowDef.v (identical to cgif_rgb YG0e.v:48); Require those directly. Generic in the class id and the entry pc; it
   holds no fuzz_scene address. The pc / cid arguments are explicit on purpose: the code record (Tfib_code, pc_stack_malloc)
   maps only classes 1 and 2, so do not "fix" this by editing that record. fuzz_scene's instance (class 8, entry
   __asan_stack_malloc_8) lives in a separate file.

   Statement only. It type-checks over the relocated framework (a Theorem Labs lane's output), which this tree carries (lib/Reusable/YG0d.v and the other modules Required below). *)
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
End c.
End b.
