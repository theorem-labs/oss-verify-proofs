(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_fvzones.v (commit eb934de95d13, blob a0d805f87bef) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 6 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGgi.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma owned_big_img : forall B, TfibSyms B ->
  forall a, 0xaa710 <= a < 0x5cd510 -> Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha. rewrite (ts_owned B TS).
apply Exists_exists. exists (0xaa710, 0x5cd510 - 0xaa710). split.
- apply (nth_error_In Tfib_owned_static 3). reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma fv_ial_img : forall B, TfibSyms B -> forall (W : world im_segs) (m : word -> option byte),
  @dg_ial_post AImg_A DImg_A W m <->
  (let m' := mrestrict (w_H W) m in
   val_mem im_segs m' (as_ialloc_flag B) 1 1 /\ val_mem im_segs m' (as_ialloc_flag B + 1) 1 0 /\
   val_mem im_segs m' (as_ialloc_w B) 8 4096 /\ val_mem im_segs m' (as_ialloc_w B + 8) 8 (as_ialloc_w B + 16) /\
   (forall a, as_ialloc_lo B <= a < as_ialloc_w B \/ as_ialloc_w B + 16 <= a < as_ialloc_hi B ->
      mbyte im_segs m' a = Some (Z_to_bv 8 0))).
Proof.
intros B TS W m. cbn [dg_ial_post DImg_A]. unfold DGgi.IAL_POST.
rewrite (ts_ial_flag B TS), (ts_ial_w B TS), (ts_ial_lo B TS), (ts_ial_hi B TS). reflexivity.
Qed.

Lemma fv_zone3_img : forall ly x sz, @im_img_cover AImg_A ly -> 0 <= sz -> in_app x sz ->
  zdisjoint (x, sz) (ly_img ly) -> @dg_zone3 AImg_A DImg_A x sz.
Proof. intros ly x sz IC Hsz Ha D. exact (zone3_intro ly x sz IC Hsz Ha D). Qed.

Lemma dzone_owned_img : forall B, TfibSyms B -> forall ly a, @dg_dzone AImg_A DImg_A ly a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
  (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros B TS ly a Ha. cbn [dg_dzone DImg_A] in Ha. unfold DGgi.DZONE in Ha.
destruct Ha as [H|[H|H]]; [left; apply (owned_big_img B TS); lia | right; left; exact H | right; right; exact H].
Qed.

Lemma izone_owned_img : forall B, TfibSyms B -> forall a, @dg_izone AImg_A DImg_A a ->
  (as_ialloc_lo B <= a < as_ialloc_hi B) \/ Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha. cbn [dg_izone DImg_A] in Ha. unfold DGgi.IZONE in Ha.
rewrite (ts_ial_lo B TS), (ts_ial_hi B TS).
destruct Ha as [H|H]; [left; exact H | right; apply (owned_big_img B TS); unfold TFIB_IAL_FLAG in H; lia].
Qed.
End rows.
