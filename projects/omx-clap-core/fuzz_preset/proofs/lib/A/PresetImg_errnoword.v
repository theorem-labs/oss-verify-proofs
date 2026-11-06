(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_errnoword.v (commit eb934de95d13, blob 6422255d1d26) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l.
Local Open Scope Z_scope.

Lemma errno_word_cf_A : forall B, @im_syms AImg_A B -> 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
Proof.
intros B TS. change (TfibSyms B) in TS. rewrite (ts_errno B TS).
replace (2 ^ 64) with 18446744073709551616 by reflexivity.
unfold TFIB_ERRNO. lia.
Qed.

Lemma errno_word_cf_A_TfibB : 0 <= as_errno AD2l.TfibB /\ as_errno AD2l.TfibB + 4 <= 2 ^ 64.
Proof. exact (errno_word_cf_A AD2l.TfibB AD2l.TfibB_syms). Qed.
