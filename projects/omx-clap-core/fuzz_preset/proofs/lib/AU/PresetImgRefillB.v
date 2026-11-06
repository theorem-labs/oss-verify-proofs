(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImgRefillB.v (commit 4d286b2e618d, file sha256 a753fdcb56a9) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 1 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 0 list indices re-picked, and 3 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* The two image rows of reply B that the relocated cf refill cites in place of cgif's YGcfImgcgif.cf_errbuf_obj_cgif /
   relro_seg_cgif (the third, cf_exh_off, is PresetImgRowsB.exh_off_B): the errbuf object of CfImg_B (B/CfImgB.v:33,
   __asan::error_message_buffer at 0xaaf68 in image B), and the RELRO row [cf_relro_lo, cf_relro_hi) = [0xa2240, 0xa4000)
   of CfImg_B (image B's PT_GNU_RELRO) inside one segment of reply B's tfibsegs. Image B's twin of lib/A/ReplyImgRefillA.v.
   EVENT-FREE.  rule 24: no function proved (kind: image facts, proved by computation on reply B's segment table). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
Import ListNotations.
Open Scope Z_scope.

Lemma cf_errbuf_obj_B : @cf_errbuf_obj CfImg_B = 0xaaf68.
Proof. reflexivity. Qed.

(* relro_seg_B_b: preset states this fact as the segment test inside CfAroPresetB.relro_seg_preset_AU. *)

(* relro_seg_B: preset states this fact as CfAroPresetB.relro_seg_preset_AU. *)
