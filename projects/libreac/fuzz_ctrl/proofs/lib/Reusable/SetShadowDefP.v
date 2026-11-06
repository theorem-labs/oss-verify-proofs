(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10, for libreac/fuzz_ctrl (images A and B; image-neutral, so in lib/Reusable): the
   contract of the shadow-fill entries (__asan_set_shadow_XX) of Reusable/SetShadowDef.v with ONE more post clause,
   presence preservation: every address present before the call is present after it. The image-B stages need it
   (a Theorem Labs lane, 2026-10-29 07:48Z: ajournal_after_write / ajournal_exec and B.ProgWorld.ctl_post_set_shadow). It is
   ADDITIVE: aset_shadow_realizes (a Theorem Labs lane's shared text) is unchanged, and aset_shadow_realizesP_weaken gives it
   back, so no consumer of the old contract rebuilds. The clause does not follow from the old post: aview reads the
   segment image where memory holds no byte, so `aview mem' a = aview mem a` does not give `mem' a = Some _`. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import SetShadowDef.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Definition aset_shadow_realizesP (pc v : Z) : Prop :=
forall ly S W regs mem md cid pos q n,
ecall_pre segs B ly S W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 q -> getr regs 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr ly cid pos) <= q -> q + n <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Lemma aset_shadow_realizesP_weaken : forall pc v, aset_shadow_realizesP pc v -> aset_shadow_realizes segs B pc v.
Proof.
intros pc v HP ly S W regs mem md cid pos q n H1 H2 H3 H4 H5 H6 H7.
eapply SRr_mono; [exact (HP ly S W regs mem md cid pos q n H1 H2 H3 H4 H5 H6 H7)|].
cbv beta. intros W' c' _ (E & regs' & mem' & md' & C & A1 & A2 & A3 & A4 & A5 & A6 & _).
split; [exact E|]. exists regs', mem', md'. tauto.
Qed.
End c.
End b.
