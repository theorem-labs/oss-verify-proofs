(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_hcw.v (commit eb934de95d13, blob 03472a099d9d) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); const_cells_zone is AGix's, whose CZONE is AGImgA.CZONE (A/AGix.v imports AGImgA), so the unfold names it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetImg_depkeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGix AGImgA.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem hcw_A : forall B, @im_syms AImg_A B ->
  forall ly' c j cl', layout_ok ly' -> @im_img_cover AImg_A ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
Proof.
intros B TS ly c j cl LY IMG HT Hc Hj Hcl Hw. change (TfibSyms B) in TS. change (img_cover ly) in IMG.
assert (HT' : ly_tsd ly = TFIB_TSD) by (rewrite HT; exact (ts_tsd B TS)).
pose proof (AGix.const_cells_zone B ly TS LY IMG HT' c j Hc Hj) as CZ.
set (a := aeval B ly (c_at c) + j) in *. clearbody a.
destruct IMG as [I1 I2].
pose proof (lo_disj ly LY) as HD.
pose proof (AGis.pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl) as DTI.
pose proof (AGis.pairwise_ij _ _ 2 3 _ _ HD eq_refl eq_refl) as DTC.
pose proof (AGis.pairwise_ij _ _ 2 4 _ _ HD eq_refl eq_refl) as DTD.
pose proof (AGis.Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as AT.
unfold zdisjoint in DTI, DTC, DTD. cbn beta in AT. cbn [fst snd] in DTI, DTC, DTD, AT.
unfold ImgBaseAG.WINT, ImgBaseAG.Pv, ImgBaseAG.SSLOTv in Hw. unfold AGImgA.CZONE in CZ.
clear - CZ Hw Hcl DTI DTC DTD AT I1 I2.
unfold in_app, TFIB_TSD, TFIB_IMG_LO, TFIB_IMG_END, kThreadObjSize, t_cache, t_stats, t_unwinding,
  kLowShadowBeg, kHighMemBeg in *.
lia.
Qed.

End d.
