(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyPfApartA.v (commit eb934de95d13, blob d87ecdbbdc8a) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x CfImgA AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGgi PresetRelroGeoA PresetImg_pfrows.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance CfImg_A.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Local Lemma pairwise_nth_pf {X} (R : X -> X -> Prop) : forall (l : list X) i j x y,
  pairwise R l -> nth_error l i = Some x -> nth_error l j = Some y -> (i < j)%nat -> R x y.
Proof.
induction l as [|h t IH]; intros [|i] [|j] x y P Hi Hj Hij; cbn in *; try discriminate; try lia.
- injection Hi as <-. destruct P as [F _]. apply nth_error_In in Hj. exact (proj1 (Forall_forall _ _) F _ Hj).
- destruct P as [_ P]. eapply IH; eauto. lia.
Qed.

Lemma pf_apart_preset_A : forall a,
  (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) ->
  ~ dg_izone a /\
  (forall ly, (layout_ok ly /\ ly_tsd ly = as_tsd TfibB /\
                 Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static TfibB ++ as_zero_shadow TfibB)) /\
              im_img_cover ly /\ asyms_ok TfibB ->
              ~ dg_dzone ly a).
Proof.
intros a Ha. split.
- cbn [dg_izone DImg_A]. unfold DGgi.IZONE.
  destruct (PresetRelroGeoA.pf_ial_apart_preset_A TfibB TfibB_syms a Ha) as [I1 I2].
  rewrite (ts_ial_lo _ TfibB_syms), (ts_ial_hi _ TfibB_syms) in I1. rewrite (ts_ial_flag _ TfibB_syms) in I2.
  intros [Hz|Hz]; [exact (I1 Hz) | exact (I2 Hz)].
- intros ly ((LO & _ & SI) & _ & _) Hd.
  cbn [dg_dzone DImg_A] in Hd.
  change (DGgi.DZONE ly a) with ((PresetRelroGeoA.dzone_static_lo <= a < PresetRelroGeoA.dzone_static_hi) \/
    (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize)) in Hd.
  destruct Hd as [Hs|Hd]; [exact (PresetRelroGeoA.pf_dzone_static_preset_A a Ha Hs)|].
  destruct (PresetImg_pfrows.pf_cells_static_preset_A TfibB TfibB_syms a Ha) as [OS _].
  apply Exists_exists in OS as (r & Hr & Hin).
  pose proof (proj1 (Forall_forall _ _) SI r ltac:(apply in_or_app; left; exact Hr)) as [Z1 Z2].
  pose proof (pairwise_nth_pf zdisjoint _ 4 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DN.
  pose proof (pairwise_nth_pf zdisjoint _ 5 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DS.
  unfold zdisjoint, in_zr in *. cbn [fst snd] in DN, DS. lia.
Qed.

End a.
