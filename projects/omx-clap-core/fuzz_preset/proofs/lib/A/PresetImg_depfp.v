(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_depfp.v (commit eb934de95d13, blob 8284fb45619e) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

Lemma footprint_DZONE_preset : forall ly a, CLdepot.depot_footprint B ly a ->
  (TFIB_STORE <= a < TFIB_DEPOT + d_map1 + 8 * 32768) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
  (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros ly a FP. unfold CLdepot.depot_footprint in FP. rewrite (ts_depot B TS), (ts_store B TS) in FP.
unfold TFIB_DEPOT, TFIB_STORE, d_map1 in *. lia.
Qed.

Theorem dep_fp_a_A : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  CLdepot.depot_footprint B ly a -> ag_dzone ly a.
Proof.
intros ly a _ _ _ FP. destruct (footprint_DZONE_preset ly a FP) as [X|[X|X]]; [left | right; left | right; right].
- unfold TFIB_DEPOT, TFIB_STORE, d_map1 in X. lia.
- exact X.
- exact X.
Qed.

Theorem dep_fp_d_A : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  CLdepot.depot_footprint B ly a -> dg_dzone ly a.
Proof.
intros ly a _ _ _ FP. destruct (footprint_DZONE_preset ly a FP) as [X|[X|X]]; [left | right; left | right; right].
- unfold TFIB_DEPOT, TFIB_STORE, d_map1 in X. lia.
- exact X.
- exact X.
Qed.
End a.
