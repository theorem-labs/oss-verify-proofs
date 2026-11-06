(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_herr.v (commit 4d286b2e618d, file sha256 3cb7243d7a3c) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, row img-herr-B of a Theorem Labs lane's reply image rows, for the cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row; a closed fact of the symbol table at reply's image B,
   fuzz_reply.asan-ubsan, pin 10ffb5f9202a).

   HERR: the cf layer's unit premise `Hypothesis HERR : as_errno B = im_errno.` (YGcfInstMiss.v:242, commit
   1ad1106e381), stated here at reply's image instance: the image class ImgBase.AImg at AImg_cgif (B/AGif2cgif.v:24),
   for every B with the image's symbol facts (im_syms = TfibSyms, B/AGif2cgif.v:28).  Both names are reply's own
   (as_errno: Reusable/YG0f.v:165; im_errno: B/ImgBase.v:32), so the text is the layer's verbatim; a consumer closes
   HERR with `exact (herr_B B TS)` (the name is the A twin herr_A's, lib/A/PresetImg_herr.v, lane W 7cb9ea48d19).
   Discharge (cgif's pattern, AGif2cgif.v:26 + YF0m.v:297): im_errno := TFIB_ERRNO at AImg_cgif (B/AGif2cgif.v:26),
   and the symbol table's errno field is TFIB_ERRNO (TfibSyms's ts_errno, B/YF0m.v:863; TFIB_ERRNO, B/YF0m.v:21). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
Local Open Scope Z_scope.

(* HERR at image B: errno of the symbol table is the image class's errno cell. *)
Lemma herr_B : forall B, @im_syms AImg_cgif B -> as_errno B = @im_errno AImg_cgif.
Proof.
intros B TS. change (TfibSyms B) in TS.
rewrite (ts_errno B TS). reflexivity.
Qed.
