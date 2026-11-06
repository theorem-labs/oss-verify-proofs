(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, row img-hdzo-A of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record); merger ReallocPrimary.CfW).
   rule 24: no function proved (kind: image rows; a closed computation at reply's image A, fuzz_reply.asan).
   Reuse search: the row's own cgif discharge, YGcfInstHitcgif.v:65 HDZO_cgif (a working branch cc4fb1f2a13), and
   a Theorem Labs lane's reply A rows (ReplyImgRowsA.v, a working branch c61d83c6f0cc): no HDZO discharge at reply.

   HDZO is the cf layer's YGcfInstHit.v:142-143 (commit d2e17f315ba):
     forall ly' a, ag_dzone ly' a ->
       Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/
       (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
   [ag_dzone] is a field of the cf layer's interface class AGImg, which reply does not carry yet. At cgif the field is
   AGis.DZONE (AGis.v:230-231): the image part [TFIB_STORE, end of Tfib_owned_static's fifth region) = [0x178148,
   0x5c88d0), then the depot's nodes block and store block. So this file states HDZO with [ag_dzone] UNFOLDED:
   - [hdzo_A_any]: for ANY image part [lo, hi) inside Tfib_owned_static's fifth region (0xa5910, 0x5c8710 - 0xa5910),
     A/AF0m.v:823, so the row closes whatever image part reply's AGImg instance chooses there;
   - [hdzo_A]: the instance cgif's DZONE has at reply A's symbols, image part [TFIB_STORE = 0x177f88, 0x5c8710)
     (A/AF0m.v:18), i.e. [DZONE_A] below = AGis.DZONE's text with reply's numbers.
   A consumer closes the layer's row with `exact` (or `exact (hdzo_A_any lo hi _ _)`) once the layer is on reply. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
Import ListNotations.
Open Scope Z_scope.

(* The fifth region of Tfib_owned_static (A/AF0m.v:823): every address in [0xa5910, 0x5c8710) is owned. *)
Lemma owned5_A : forall B, @im_syms AImg_reply B -> forall a, 0xa5910 <= a < 0x5c8710 ->
  Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha. change (TfibSyms B) in TS. rewrite (ts_owned B TS).
apply Exists_exists. exists (0xa5910, 0x5c8710 - 0xa5910). split.
- apply (nth_error_In Tfib_owned_static 4). reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

(* HDZO at image A for any image part [lo, hi) inside the fifth owned region. *)
Lemma hdzo_A_any : forall lo hi, 0xa5910 <= lo -> hi <= 0x5c8710 ->
  forall B, @im_syms AImg_reply B -> forall ly' a,
  ((lo <= a < hi) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize)) ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/
  (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Proof.
intros lo hi Hlo Hhi B TS ly a [Hd|[Hd|Hd]].
- left. apply (owned5_A B TS a). lia.
- right; left; exact Hd.
- right; right; exact Hd.
Qed.

(* AGis.DZONE's text (cgif AGis.v:230-231) with reply A's numbers: the image part starts at TFIB_STORE (0x177f88,
   A/AF0m.v:18; cgif 0x178148 = its TFIB_STORE) and ends where Tfib_owned_static's fifth region ends (0x5c8710;
   cgif 0x5c88d0). *)
Definition DZONE_A (ly : alayout) (a : Z) : Prop :=
  (TFIB_STORE <= a < 0x5c8710) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).

(* HDZO at image A, with ag_dzone := DZONE_A. *)
Theorem hdzo_A : forall B, @im_syms AImg_reply B -> forall ly' a, DZONE_A ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/
  (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Proof.
intros B TS ly a Hd. unfold DZONE_A, TFIB_STORE in Hd.
exact (hdzo_A_any 0x177f88 0x5c8710 ltac:(lia) ltac:(lia) B TS ly a Hd).
Qed.
