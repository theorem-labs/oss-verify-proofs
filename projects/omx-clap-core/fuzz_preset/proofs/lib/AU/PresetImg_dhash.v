(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_dhash.v (commit 4d286b2e618d, file sha256 e190f8477080) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2l.
Open Scope Z_scope.

(* dhash_img at reply B (the internal file REPLY-IMG-ROWS.md row img-dhash-B; the internal file CF-UNIT-HYPS.md:45). The cf layer takes the
   depot hash field as the witness-only premise `forall t, as_dhash B t = <unit dhash> t` of depot_spec_a / depot_spec_d
   (cgif: YGcfInstF1Wcgif.v:131 / :135, with B := its instance). At reply B the instance is TfibB (lib/B/YD2l.v:15),
   whose field is `as_dhash := tfib_dhash` (lib/B/YD2l.v:33): the image-free hash of lib/Reusable/YF0p.v:14. So the
   premise holds by computation, with no image data and no start-up fact. Stem `dhash_img`, as the A twin's
   (a prior worker, row img-dhash-A: lib/A/PresetImg_dhash.v dhash_img_A), so lane W's A -> B relocation maps it by name. *)
Lemma dhash_img_B : forall t : list Z, as_dhash TfibB t = tfib_dhash t.
Proof. reflexivity. Qed.
