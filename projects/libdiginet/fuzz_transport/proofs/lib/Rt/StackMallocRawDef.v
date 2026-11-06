(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan fake-stack vocabulary of the cgif walks at fuzz_reply's symbol type wsym:
   proofs/cgif/cgif_file_fuzzer/lib/YC44.v (fake-frame and shadow regions, the plain pi runs over the journal and the
   flag store that ends a fake frame), lib/YC1h.v (atoms above A_LIM, after-call with high atoms), lib/YC45.v (the
   plain pi run that stops at a call) and the generic lemmas of lib/A/AC8j.v.  Only the symbol type, the module paths
   and PALibF's two stack_malloc fields (fuzz_reply calls classes 0 and 1) change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_frame.v, with its module paths changed; 18 of its 42 lines of code are new or changed and 1156 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from libreac/fuzz_ctrl for libdiginet/fuzz_transport by this unit's provenance/evidence/class1/run.sh (image-free: module paths only). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Let code := as_code B.
Definition astack_malloc_realizes_raw (cid : Z) : Prop :=
forall ly S W regs mem md pos S',
ecall_pre segs B ly S W regs mem md ->
count_cid cid (frames S) < fs_frames cid ->
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
SRr segs W (cfg_at segs (pc_stack_malloc code cid) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S' W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly cid pos) /\
zero_shadow (aview segs (w_H W) mem') SHADOW_OFF (frame_addr ly cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem') (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall x : word, w_H W x = true -> ~ aowned B ly S' (bv_unsigned x) -> mem' x = mem x) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
Lemma astack_malloc_realizes_raw_view : forall cid, astack_malloc_realizes_raw cid -> astack_malloc_realizes segs B cid.
Proof.
intros cid R ly S W regs mem md pos S' H1 H2 H3.
eapply SRr_mono; [exact (R ly S W regs mem md pos S' H1 H2 H3)|].
intros W' c' _ (EW & regs' & mem' & md' & EC & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _ & P9).
split; [exact EW|]. exists regs', mem', md'.
exact (conj EC (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 P9))))))))).
Qed.
End c.
End b.
