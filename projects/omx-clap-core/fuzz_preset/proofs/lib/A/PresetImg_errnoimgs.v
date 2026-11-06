(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_errnoimgs.v (commit eb934de95d13, blob 694d424cdbb7) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgSA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ErrnoApartpreset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma errno_apart_dzone_s_A :
forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly -> ims_dzone ly a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B ly a TS LY IMG Hd. destruct Hd as [Hd|[Hd|Hd]].
- rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia.
- exact (errno_apart_owned errno_in_img_preset B ly (ly_NB ly, kNodesBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; left; reflexivity) Hd).
- exact (errno_apart_owned errno_in_img_preset B ly (ly_SB ly, kStoreBlockSize) a TS LY IMG
    ltac:(unfold owned_extents; right; right; right; right; right; left; reflexivity) Hd).
Qed.

Lemma errno_apart_shadow_s_A :
forall B a, im_syms B -> ImgBaseAGS.SHBv <= a -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros B a TS Ha. change (0x7fff8000 <= a) in Ha. rewrite (ts_errno B TS). unfold TFIB_ERRNO. lia. Qed.

Lemma errno_apart_zone3_s_A :
forall B x sz a, im_syms B -> ims_zone3 x sz -> x <= a < x + sz -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B x sz a TS Hz Ha. pose proof (zone3_off_img x sz a Hz Ha) as O. rewrite (ts_errno B TS).
unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TFIB_ERRNO in *. lia.
Qed.

End a.
