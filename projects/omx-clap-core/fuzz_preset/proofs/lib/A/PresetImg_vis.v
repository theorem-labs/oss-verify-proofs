(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_vis.v (commit eb934de95d13, blob 446a1c41268a) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB13 AFff.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
Import ListNotations.
Open Scope Z_scope.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma preset_win_view : forall (H : word -> bool) (mem : word -> option byte) a,
  0xa1000 <= a < 0x600000 -> aview im_segs H mem a <> None.
Proof.
intros H mem a Ha. change im_segs with tfibsegs. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)); [discriminate|].
pose proof (tfib_rw_rom a Ha) as R.
destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [discriminate|contradiction].
Qed.

Variable B : asyms.
Hypothesis TB : TfibSyms B.

Lemma comb_vis_A : forall (H : word -> bool) (mem : word -> option byte) a,
  as_inst B + o_comb_stats <= a < as_inst B + o_comb_stats + 40 -> aview im_segs H mem a <> None.
Proof.
intros H mem a Ha. rewrite (ts_inst B TB) in Ha. unfold TFIB_INST, o_comb_stats in Ha.
apply preset_win_view. lia.
Qed.

Lemma errno_vis_A : forall (H : word -> bool) (mem : word -> option byte) a,
  as_errno B <= a < as_errno B + 4 -> aview im_segs H mem a <> None.
Proof.
intros H mem a Ha. rewrite (ts_errno B TB) in Ha. unfold TFIB_ERRNO in Ha.
apply preset_win_view. lia.
Qed.

Lemma dep_unhid_A : forall (W : world im_segs) a,
  (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) ->
  w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Ha. rewrite (ts_depot B TB), (ts_store B TB) in Ha. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in Ha.
apply (rw_unhidden W a). lia.
Qed.

End v.
