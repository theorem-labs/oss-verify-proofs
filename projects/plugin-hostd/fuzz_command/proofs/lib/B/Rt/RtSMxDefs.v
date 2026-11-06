(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: only the side-stack contracts of cgif_rgb_fuzzer's lib/YG0e.v (astack_malloc_sz_realizes, astack_free_realizes), restated over the asan-state definitions of the cgif_file_fuzzer proof as plugin-hostd/fuzz_command holds them; module names; and one contract added for the classes that fill the whole frame's shadow (astack_free_cls_realizes). *)
(* Modified by Theorem Labs, 2026-10: only astack_malloc_sz_realizes of lib/A/Rt/RtStack.v:39, restated over a relation ARx with the poisoned-head set Hp in the way lib/Reusable/FCiface.v restates astack_malloc_realizes (AR -> ARx ly S Hp, Hp quantified, ecall_pre -> ecall_pre_x), and the lemma that gives back RtStack.v's form for cgif's AR. *)
(* Modified by Theorem Labs, 2026-10: moved from this harness's lib/A/Rt/RtSMxDefs.v to plugin-hostd/fuzz_command's ASan+UBSan image (fuzz_command.asan-ubsan): module paths lib/A to lib/B; it names no address; the proof text is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtStack.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

(* RtStack.v:39-55: a0 carries the frame size, and only that many shadow bytes are zeroed. *)
Definition astack_malloc_sz_realizes_x (pc cid : Z) : Prop :=
forall ly S Hp W regs mem md pos S' n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 n -> 8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
count_cid cid (frames S) < fs_frames cid ->
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S' Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly cid pos) /\
zero_shadow (aview segs (w_H W) mem') SHADOW_OFF (frame_addr ly cid pos) n /\
rdword (aview segs (w_H W) mem') (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
End b.

(* For cgif's own AR (Hp ignored) the _x contract is RtStack.v's contract. *)
Section c.
Variable segs : list Segment.
Variable B : asyms.
Lemma astack_malloc_sz_realizes_of_x : forall pc cid,
astack_malloc_sz_realizes_x segs B (AR_nohp segs B) pc cid -> astack_malloc_sz_realizes segs B pc cid.
Proof. intros pc cid H ly S W regs mem md pos S' n HPRE. exact (H ly S [] W regs mem md pos S' n HPRE). Qed.
End c.
End a.
