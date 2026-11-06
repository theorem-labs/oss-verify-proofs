(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_hdzx.v (commit eb934de95d13, blob 0a18b16addd7) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 3 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA PresetImg_hdzo.
Import ListNotations.
Open Scope Z_scope.

Lemma hdzx_pairwise_nth {X : Type} (R : X -> X -> Prop) : forall l i j x y, pairwise R l ->
  nth_error l i = Some x -> nth_error l j = Some y -> (i < j)%nat -> R x y.
Proof.
induction l as [|h t IH]; intros i j x y P Hi Hj Lt; [destruct i; discriminate|].
cbn [pairwise] in P. destruct P as [F P]. destruct i as [|i].
- cbn in Hi. injection Hi as <-. destruct j as [|j]; [lia|]. cbn in Hj.
  exact (proj1 (Forall_forall _ _) F y (nth_error_In _ _ Hj)).
- destruct j as [|j]; [lia|]. cbn in Hi, Hj. exact (IH i j x y P Hi Hj ltac:(lia)).
Qed.

Section rows. Context {rc : YM05.RunCeil}.

Lemma hdzx_blocks_off_img_A : forall ly, layout_ok ly -> img_cover ly -> forall a,
  ((ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize)) ->
  a < TFIB_IMG_LO \/ TFIB_IMG_END <= a.
Proof.
intros ly LY [I1 I2] a Ha.
pose proof (hdzx_pairwise_nth zdisjoint _ 4 9 _ _ (lo_disj _ LY) eq_refl eq_refl ltac:(lia)) as D4.
pose proof (hdzx_pairwise_nth zdisjoint _ 5 9 _ _ (lo_disj _ LY) eq_refl eq_refl ltac:(lia)) as D5.
unfold zdisjoint in D4, D5. cbn [fst snd] in D4, D5. lia.
Qed.

Lemma hdzx_A_any : forall lo hi, 0x13a948 + 2 <= lo ->
  forall B, @im_syms AImg_A B -> forall ly' a, layout_ok ly' -> @im_img_cover AImg_A ly' ->
  ((lo <= a < hi) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize)) ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
  ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros lo hi Hlo B TS ly a LY IMG Hd. change (TfibSyms B) in TS. change (img_cover ly) in IMG.
rewrite (ts_inst B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
unfold TFIB_INST, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG.
destruct Hd as [Hd|Hb].
- split; [|split]; intros Ha; lia.
- pose proof (hdzx_blocks_off_img_A ly LY IMG a Hb) as Off. unfold TFIB_IMG_LO, TFIB_IMG_END in Off.
  split; [|split]; intros Ha; lia.
Qed.

Theorem hdzx_A : forall B, @im_syms AImg_A B -> forall ly' a, layout_ok ly' -> @im_img_cover AImg_A ly' ->
  DZONE_A ly' a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
  ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros B TS ly a LY IMG Hd. unfold DZONE_A, TFIB_STORE in Hd.
exact (hdzx_A_any 0x17cd88 0x5cd510 ltac:(lia) B TS ly a LY IMG Hd).
Qed.

End rows.
