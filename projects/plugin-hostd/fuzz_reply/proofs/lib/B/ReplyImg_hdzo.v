(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-hdzo-B of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record), for a Theorem Labs lane's cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row; a closed computation at reply's image B, fuzz_reply.asan-ubsan).
   Reuse search: proof-index hdzo_B HDZO HDZO_cgif (2026-10-30 04:4xZ, exit 0): HDZO only as the layer's
   Hypothesis (YGcfInstHit / HitCore / HitPost / Miss / MissW on unreleased cold/* branches), no discharge at any unit.

   HDZO is the cf layer's Hypothesis of YGcfInstHit.v:142-143 (commit d2e17f315ba, Section b):
     forall ly' a, ag_dzone ly' a ->
       Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/
       (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
   Every name in it is already in reply's tree, so hdzo_B below states it verbatim at reply's instance (the image
   class ImgBase.AImg at image B's AImg_reply, B/AGif2reply.v; ImgBaseAG.AGImg at B/AGif0reply.v's AGImg_reply,
   whose ag_dzone is AGis.DZONE), for a B with the image's symbol facts (im_syms = TfibSyms). A consumer closes the
   layer's HDZO with `exact (hdzo_B B TS)` once the layer is on reply. No Definition of the layer is copied here.
   The proof is cgif's HDZO_cgif (YGcfInstHitcgif.v:65 @ cc4fb1f2a13, AGif5.v:913-917's own_Dg script) at this image:
   AGis.DZONE's image part [0x178508, 0x5c8c90) (B/AGis.v) lies in the fifth region of Tfib_owned_static (B/YF0m.v,
   ts_owned), checked by vm_compute on the table's entry; its NB and SB parts are the statement's two other arms. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ImgBaseAG AGis AGif0reply.
Open Scope Z_scope.

(* HDZO at image B (YGcfInstHit.v:142-143 @ d2e17f315ba). *)
Lemma hdzo_B : forall B, @im_syms AImg_reply B ->
  forall ly' a, @ImgBaseAG.ag_dzone AImg_reply AGif0reply.AGImg_reply ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/
  (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Proof.
intros B TS ly a Hd. change (TfibSyms B) in TS.
change (AGis.DZONE ly a) in Hd. unfold AGis.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]].
- left. rewrite (ts_owned B TS). apply Exists_exists.
  (* the table's fifth region, by Rocq term: its bounds against DZONE's image part by vm_compute *)
  set (r := nth 4 Tfib_owned_static (0, 0)).
  assert (Hin : In r Tfib_owned_static) by (apply nth_In, Nat.ltb_lt; vm_compute; reflexivity).
  assert (Hb : ((fst r <=? 0x178508) && (0x5c8c90 <=? fst r + snd r))%bool = true) by (vm_compute; reflexivity).
  apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1, Hb2.
  exists r. split; [exact Hin|]. unfold in_zr. lia.
- right; left; exact Hd.
- right; right; exact Hd.
Qed.
