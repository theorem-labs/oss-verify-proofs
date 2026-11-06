(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyQBBytes.v (commit 4d286b2e618d, file sha256 6da2375323ae) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10 (a prior worker): the free interface's quarantine byte premise
   YGcfInstFreeQ.QB_BYTES (YGcfInstFreeQ.v:44) at lane F2b's drain-entry premise QB := YGcfInstDrainR.QB_cf kQuarantineMax
   (YGcfInstDrainR.v:262), over image B's modules.  rule 24: proves no function (kind: statement text; a model fact).

   QB_BYTES QB says: for every allocator state X with QB X, qc_bytes (st_qthread X) + qc_bytes (st_qglobal X) <= 2 ^ 31
   (the two quarantine caches together hold at most 2 ^ 31 bytes; DMiface.qview's qv_bytes).  QB_cf NMAXD X is a
   conjunction whose FIRST conjunct is that bound, so the proof is its first projection.  It reads no numeral of the
   image and holds for every NMAXD; kQuarantineMax (lib/Reusable/YG00.v:30) is only the argument the consumer names.
   lib/B's YGcfInstFreeQ.v and YGcfInstDrainR.v differ from lib/A's only in their Require lines (lib.A -> lib.B).

   Relocated from cgif's YGcfInstFreeImgcgif.QB_BYTES_qbcf (branch 807fff6eccda,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstFreeImgcgif.v:243), at NMAXD := kQuarantineMax.  The definitions of
   QB_BYTES and QB_cf are textually the same in that tree and in this one. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YG00 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstFreeQ YGcfInstDrainR.

Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Theorem qb_bytes_preset_B : YGcfInstFreeQ.QB_BYTES (YGcfInstDrainR.QB_cf kQuarantineMax).
Proof. intros X H. exact (proj1 H). Qed.

End q.
