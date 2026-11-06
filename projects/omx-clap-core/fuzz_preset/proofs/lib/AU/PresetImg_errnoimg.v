(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_errnoimg.v (commit 4d286b2e618d, file sha256 baa2ac4e1115) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply; row img-errnoimg-B of
   a Theorem Labs lane's internal file REPLY-IMG-ROWS.md).
   rule 24: no function proved (kind: image row; a closed fact of reply's image B, fuzz_reply.asan-ubsan, pin
   10ffb5f9202a).  Reuse search: proof-index errno_img_cf / ErrnoImgCf (2026-10-30 04:5xZ): no released or
   unreleased discharge at any unit; the Record itself only in the cf layer (cgif_file, fuzz_preset).

   ErrnoImgCf is the cf layer's Record of ErrnoApart.v's nine image facts (b6891182536,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstErrno.v:62-72); cgif discharges it as YGcfInstF1Wcgif.v:52
   errno_img_cf_cgif, one field per lemma of ErrnoApartcgif.v.  Reply has not taken the layer file yet, so the Lemma
   below states the Record's nine fields UNFOLDED, as a conjunction in the Record's field order (ei_in_img, ei_unhidden,
   ei_dzone_ag, ei_shadow_ag, ei_inst_ag, ei_dzone_d, ei_izone, ei_zone3_d, ei_inst_d), at reply's image-B instances:
   ImgBase.AImg at AImg_cgif (B/AGif2cgif.v:24), ImgBaseAG.AGImg at AGImg_cgif (B/AGif0cgif.v:116) and
   ImgBaseDG.DImg at DImg_cgif (B/DGif0cgif.v:30).  Once the layer is on reply a consumer closes the Record with
   `destruct errno_img_cf_B as (? & ? & ? & ? & ? & ? & ? & ? & ?); constructor; assumption`.  No Definition of the
   layer is copied here.  The nine facts are B/ErrnoApartcgif.v's lemmas (relocated from cgif's ErrnoApartcgif.v);
   this file only packages them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require ErrnoApartcgif.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* = YGcfInstErrno.ErrnoImgCf (cf layer, YGcfInstErrno.v:62-72) at IM := AImg_cgif, AG := AGImg_cgif,
   DI := DImg_cgif, its nine fields in order. *)
Lemma errno_img_cf_B :
  errno_in_img (IM := AImg_cgif) /\
  errno_unhidden (IM := AImg_cgif) /\
  errno_apart_dzone_ag (IM := AImg_cgif) (AG := AGImg_cgif) /\
  errno_apart_shadow_ag (IM := AImg_cgif) (AG := AGImg_cgif) /\
  errno_apart_inst_ag (IM := AImg_cgif) (AG := AGImg_cgif) /\
  errno_apart_dzone_d (IM := AImg_cgif) (DI := DImg_cgif) /\
  errno_apart_izone (IM := AImg_cgif) (DI := DImg_cgif) /\
  errno_apart_zone3_d (IM := AImg_cgif) (DI := DImg_cgif) /\
  errno_apart_inst_d (IM := AImg_cgif) (DI := DImg_cgif).
Proof.
split; [exact ErrnoApartcgif.errno_in_img_cgif|].
split; [exact ErrnoApartcgif.errno_unhidden_cgif|].
split; [exact ErrnoApartcgif.errno_apart_dzone_ag_cgif|].
split; [exact ErrnoApartcgif.errno_apart_shadow_ag_cgif|].
split; [exact ErrnoApartcgif.errno_apart_inst_ag_cgif|].
split; [exact ErrnoApartcgif.errno_apart_dzone_d_cgif|].
split; [exact ErrnoApartcgif.errno_apart_izone_cgif|].
split; [exact ErrnoApartcgif.errno_apart_zone3_d_cgif|].
exact ErrnoApartcgif.errno_apart_inst_d_cgif.
Qed.

End a.
