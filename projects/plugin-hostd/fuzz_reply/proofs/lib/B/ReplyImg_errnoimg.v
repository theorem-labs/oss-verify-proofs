(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply; row img-errnoimg-B of
   a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record)).
   rule 24: no function proved (kind: image row; a closed fact of reply's image B, fuzz_reply.asan-ubsan, pin
   10ffb5f9202a).  Reuse search: proof-index errno_img_cf / ErrnoImgCf (2026-10-30 04:5xZ): no released or
   unreleased discharge at any unit; the Record itself only in the cf layer (cgif_file, fuzz_preset).

   ErrnoImgCf is the cf layer's Record of ErrnoApart.v's nine image facts (a working branch b6891182536,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstErrno.v:62-72); cgif discharges it as YGcfInstF1Wcgif.v:52
   errno_img_cf_cgif, one field per lemma of ErrnoApartcgif.v.  Reply has not taken the layer file yet, so the Lemma
   below states the Record's nine fields UNFOLDED, as a conjunction in the Record's field order (ei_in_img, ei_unhidden,
   ei_dzone_ag, ei_shadow_ag, ei_inst_ag, ei_dzone_d, ei_izone, ei_zone3_d, ei_inst_d), at reply's image-B instances:
   ImgBase.AImg at AImg_reply (B/AGif2reply.v:24), ImgBaseAG.AGImg at AGImg_reply (B/AGif0reply.v:117) and
   ImgBaseDG.DImg at DImg_reply (B/DGif0reply.v:31).  Once the layer is on reply a consumer closes the Record with
   `destruct errno_img_cf_B as (? & ? & ? & ? & ? & ? & ? & ? & ?); constructor; assumption`.  No Definition of the
   layer is copied here.  The nine facts are B/ErrnoApartreply.v's lemmas (relocated from cgif's ErrnoApartcgif.v);
   this file only packages them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply AGif0reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ErrnoApart.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoApartreply.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* = YGcfInstErrno.ErrnoImgCf (cf layer, YGcfInstErrno.v:62-72) at IM := AImg_reply, AG := AGImg_reply,
   DI := DImg_reply, its nine fields in order. *)
Lemma errno_img_cf_B :
  errno_in_img (IM := AImg_reply) /\
  errno_unhidden (IM := AImg_reply) /\
  errno_apart_dzone_ag (IM := AImg_reply) (AG := AGImg_reply) /\
  errno_apart_shadow_ag (IM := AImg_reply) (AG := AGImg_reply) /\
  errno_apart_inst_ag (IM := AImg_reply) (AG := AGImg_reply) /\
  errno_apart_dzone_d (IM := AImg_reply) (DI := DImg_reply) /\
  errno_apart_izone (IM := AImg_reply) (DI := DImg_reply) /\
  errno_apart_zone3_d (IM := AImg_reply) (DI := DImg_reply) /\
  errno_apart_inst_d (IM := AImg_reply) (DI := DImg_reply).
Proof.
split; [exact ErrnoApartreply.errno_in_img_reply|].
split; [exact ErrnoApartreply.errno_unhidden_reply|].
split; [exact ErrnoApartreply.errno_apart_dzone_ag_reply|].
split; [exact ErrnoApartreply.errno_apart_shadow_ag_reply|].
split; [exact ErrnoApartreply.errno_apart_inst_ag_reply|].
split; [exact ErrnoApartreply.errno_apart_dzone_d_reply|].
split; [exact ErrnoApartreply.errno_apart_izone_reply|].
split; [exact ErrnoApartreply.errno_apart_zone3_d_reply|].
exact ErrnoApartreply.errno_apart_inst_d_reply.
Qed.

End a.
