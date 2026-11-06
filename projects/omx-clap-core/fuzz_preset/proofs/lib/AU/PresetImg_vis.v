(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_vis.v (commit 4d286b2e618d, file sha256 d131049a9b6d) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 2 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 4 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply; row img-vis-B of
   a notes file, the internal file CF-UNIT-HYPS.md line 59).
   rule 24: no function proved (kind: image rows; closed computations at reply's image B, fuzz_reply.asan-ubsan).

   The cf layer states these three rows as Section hypotheses of YGcfInstSec.v (commit 4c2fd365d8e) over its own
   context; reply does not carry those layer files.  So each Lemma below states the hypothesis's text VERBATIM at
   reply's instance (the image class ImgBase.AImg at image B's AImg_cgif, B/AGif2cgif.v), with the image's symbol
   facts TfibSyms (B/YF0m.v:857), and a consumer closes the layer's hypothesis with `exact` once the layer is on reply.
   No Definition of the layer is copied; o_comb_stats and d_map1 are reply's own (Reusable/YG0f.v:207 / :225), the
   same numerals as the layer's (cgif YG0f.v:206 / :224).
   - COMB_VIS (YGcfInstSec.v:359-360): the combined allocator's 40 stats bytes [TFIB_INST + 688, + 728) =
     [0xa3288, 0xa8370) lie in the image's rw window [0xa2000, 0x601000), whose bytes every view reads
     [cgif: rw_view; here YB13.tfib_rw_rom, as YFim.v:468 aview_rw_some].
   - ERRNO_VIS (YGcfInstSec.v:736-737): errno's 4 bytes [TFIB_ERRNO, + 4) = [0x5d994c, 0x5d9950) lie in the same window.
   - DEP_UNHID (YGcfInstSec.v:380-382): the depot's map [TFIB_DEPOT, + d_map1 + 8 * 32768) = [0x188518, 0x5c8528)
     and the store's 64 bytes [0x17d5c8, 0x178548) lie in the rw window, which no world hides [YFff.rw_unhidden]. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFff.
Open Scope Z_scope.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* Every view reads a byte of the image's rw window: the restricted memory either holds it or falls back to the
   image's own byte, which tfib_rw_rom gives (the proof of YFim.v:468 aview_rw_some, stated at im_segs). *)
Lemma vis_rw_window : forall (H : word -> bool) (mem : word -> option byte) a, 0xa2000 <= a < 0x601000 ->
  aview (@im_segs AImg_cgif) H mem a <> None.
Proof.
intros H mem a Ha. change (@im_segs AImg_cgif) with tfibsegs.
unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)); cbn; [discriminate|].
pose proof (YB13.tfib_rw_rom a Ha) as X.
destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [cbn; discriminate | exfalso; exact (X eq_refl)].
Qed.

(* COMB_VIS at image B (YGcfInstSec.v:359-360). *)
Lemma comb_vis_B : forall B, @im_syms AImg_cgif B ->
  forall (H : word -> bool) (mem : word -> option byte) a,
  as_inst B + o_comb_stats <= a < as_inst B + o_comb_stats + 40 -> aview (@im_segs AImg_cgif) H mem a <> None.
Proof.
intros B TS H mem a Ha. change (TfibSyms B) in TS. rewrite (ts_inst B TS) in Ha.
apply vis_rw_window. unfold TFIB_INST, o_comb_stats in Ha. lia.
Qed.

(* ERRNO_VIS at image B (YGcfInstSec.v:736-737). *)
Lemma errno_vis_B : forall B, @im_syms AImg_cgif B ->
  forall (H : word -> bool) (mem : word -> option byte) a, as_errno B <= a < as_errno B + 4 ->
  aview (@im_segs AImg_cgif) H mem a <> None.
Proof.
intros B TS H mem a Ha. change (TfibSyms B) in TS. rewrite (ts_errno B TS) in Ha.
apply vis_rw_window. unfold TFIB_ERRNO in Ha. lia.
Qed.

(* DEP_UNHID at image B (YGcfInstSec.v:380-382). *)
Lemma dep_unhid_B : forall B, @im_syms AImg_cgif B ->
  forall (W : world (@im_segs AImg_cgif)) a,
  (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) ->
  w_H W (Z_to_bv 64 a) = false.
Proof.
intros B TS W a Ha. change (TfibSyms B) in TS. rewrite (ts_depot B TS), (ts_store B TS) in Ha.
change (@im_segs AImg_cgif) with tfibsegs in W.
apply YFff.rw_unhidden. unfold TFIB_DEPOT, TFIB_STORE, d_map1 in Ha.
replace (2 ^ 20) with 1048576 in Ha by reflexivity. lia.
Qed.

End rows.
