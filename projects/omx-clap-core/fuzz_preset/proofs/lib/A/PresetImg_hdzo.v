(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_hdzo.v (commit eb934de95d13, blob 2caae5af874c) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 11 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
Import ListNotations.
Open Scope Z_scope.

Lemma owned5_A : forall B, @im_syms AImg_A B -> forall a, 0xaa710 <= a < 0x5cd510 ->
  Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha. change (TfibSyms B) in TS. rewrite (ts_owned B TS).
apply Exists_exists. exists (0xaa710, 0x5cd510 - 0xaa710). split.
- apply (nth_error_In Tfib_owned_static 3). reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma hdzo_A_any : forall lo hi, 0xaa710 <= lo -> hi <= 0x5cd510 ->
  forall B, @im_syms AImg_A B -> forall ly' a,
  ((lo <= a < hi) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize)) ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/
  (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Proof.
intros lo hi Hlo Hhi B TS ly a [Hd|[Hd|Hd]].
- left. apply (owned5_A B TS a). lia.
- right; left; exact Hd.
- right; right; exact Hd.
Qed.

Definition DZONE_A (ly : alayout) (a : Z) : Prop :=
  (TFIB_STORE <= a < 0x5cd510) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).

Theorem hdzo_A : forall B, @im_syms AImg_A B -> forall ly' a, DZONE_A ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/
  (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Proof.
intros B TS ly a Hd. unfold DZONE_A, TFIB_STORE in Hd.
exact (hdzo_A_any 0x17cd88 0x5cd510 ltac:(lia) ltac:(lia) B TS ly a Hd).
Qed.
