(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImgRowsB.v (commit 4d286b2e618d, file sha256 c4a12e44f9d2) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 6 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 1 list indices re-picked, and 38 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image rows; closed computations at reply's image B, fuzz_reply.asan-ubsan, pin
   10ffb5f9202a).  Reuse search: proof-index errb_obj_owned_t IMG_SAPART IMG_JUNK (2026-10-30 03:5xZ): only the
   layer's Definitions, no discharge at any unit.

   The cf layer states these rows as Definitions over its own Section context; reply has not taken those layer files
   yet.  So each Lemma below states the layer Definition's body VERBATIM at reply's instance (the image class
   ImgBase.AImg at image B's AImg_cgif, B/AGif2cgif.v:24; the image constants CfImg_B, B/CfImgB.v), and a consumer
   closes the layer's row with `exact` once the layer is on reply.  No Definition of the layer is copied here.
   - EXH_OFF: EXH_OFF_t, the cf layer's YGcfErrbSep.v:35 (commit ee95275bccbf): cf_exh_off = 68.
   - IMG_SAPART: the cf layer's YGcfInstRcSec.v:124-130 (commit 79f3c704722), sdeal_inst unfolded.
   - IMG_JUNK: YGcfInstRcSec.v:135-137 (commit 6233fefec18d), segment containment: every junk byte lies in a segment
     of im_segs; at this image the junk range of ts_junk, [0xa2000, 0x601000), is tiled exactly by the image's segments
     2 and 3, [0xa2000, 0xa4000) and [0xa4000, 0x601000) (the proof image's AsanUbsan.v).
   - ERRB_OWN: errb_obj_owned_t, the cf layer's YGcfInstBase.v:87-88 (commit 688e15b2663f), at a B with the image's
     symbol facts: the 56 bytes of the error buffer object [0xaaf68, 0xaafa0) (error_message_buffer, error_report_callback,
     error_message_buf_mutex, error_message_buffer_placeholder in the unstripped twin) lie in the owned region
     (0xaaf50, 0x5cdd50 - 0xaaf50), B/YF0m.v:820.
   - ERRB_SEP: ERRB_SEP_t, YGcfErrbSep.v:25-28 (commit ee95275bccbf), at a B with the image's symbol facts: the error
     buffer object [0xaaf68, 0xaafa0) lies above the instance object [0xa8098, 0xa8ec8), below the out-of-memory byte
     0x12d960 and errno 0x5d994c, below the depot's static zone [0x17d5c8, 0x5cdd50), and apart from the nodes and store
     blocks, which layout_ok keeps apart from the image window (lo_disj) that im_img_cover makes cover the image. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseAGS. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif0cgif AGif4cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGis AGjm.
Open Scope Z_scope.

(* EXH_OFF at image B (EXH_OFF_t): CfImg_B's cf_exh_off is 68 (B/CfImgB.v:35). *)
Lemma exh_off_B : @cf_exh_off CfImg_B = 68.
Proof. reflexivity. Qed.

(* IMG_SAPART at image B (YGcfInstRcSec.v:124-130, sdeal_inst unfolded): the four allocator-word ranges of the instance
   (TFIB_INST 0xa8098 + 120 .. + 720, all below 0xa32a8) lie below the internal allocator's area (TFIB_IAL_LO 0xac900),
   the flag (0x1360c8), the store (0x17d5c8) and the depot (0x188518), B/YF0m.v:16-19. *)
(* img_sapart_B: preset states this fact as DMrcSecCf.img_sapart_preset. *)

(* ERRB_OWN at image B (errb_obj_owned_t, YGcfInstBase.v:87-88): cf_errbuf_obj is 0xaaf68 (B/CfImgB.v:33), and
   [0xaaf68, 0xaafa0) lies in the fifth region of Tfib_owned_static, (0xaaf50, 0x5cdd50 - 0xaaf50) (B/YF0m.v:820). *)
Lemma errb_obj_owned_B : forall B, @im_syms AImg_cgif B ->
  forall a, @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 -> Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha. change (TfibSyms B) in TS. rewrite (ts_owned B TS).
unfold CfImg_B in Ha. cbn [cf_errbuf_obj] in Ha.
apply Exists_exists. exists (0xaaf50, 0x5cdd50 - 0xaaf50). split.
- apply (nth_error_In Tfib_owned_static 3). reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* IMG_JUNK at image B (YGcfInstRcSec.v:135-137, commit 6233fefec18d): each junk range of TfibSyms lies in
   [0xa2000, 0x601000) (ts_junk, B/YF0m.v:874), which the image's segments 2 = [0xa2000, 0xa4000) and 3 = [0xa4000, 0x601000)
   (seg_size 0x55d000) tile. *)
(* img_junk_B: preset states this fact as DMrcSecCf.img_junk_preset. *)

(* ERRB_SEP at image B (ERRB_SEP_t, YGcfErrbSep.v:25-28, commit ee95275bccbf): cf_errbuf_obj is 0xaaf68 (B/CfImgB.v:33); the
   instance, the out-of-memory byte and errno are 0xa8098 / 0x12d960 / 0x5d994c (B/YF0m.v:16-21); ims_dzone and ag_dzone are reply's DZONE
   (B/AGif4cgif.v:29, B/AGif0cgif.v:119), whose static part is [0x17d5c8, 0x5cdd50); its nodes and store blocks are owned extents that
   lo_disj (YG0f.v:321) keeps apart from ly_img, which im_img_cover (img_cover) makes cover [TFIB_IMG_LO, TFIB_IMG_END). *)
Lemma errb_sep_B : forall B, @im_syms AImg_cgif B -> forall ly a, layout_ok ly -> @im_img_cover AImg_cgif ly -> ly_tsd ly = as_tsd B ->
  @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\
  ~ ims_dzone ly a /\ ~ ag_dzone ly a.
Proof.
intros B TS ly a LY IC _ Ha. change (TfibSyms B) in TS. change (img_cover ly) in IC.
unfold CfImg_B in Ha. cbn [cf_errbuf_obj] in Ha.
rewrite (ts_inst B TS), (ts_oom B TS), (ts_errno B TS).
change (ims_dzone ly a) with (AGjm.DZONE ly a). change (ag_dzone ly a) with (AGis.DZONE ly a).
pose proof (lo_disj ly LY) as D. unfold static_extents, owned_extents in D. cbn [pairwise app] in D.
destruct D as (_ & _ & _ & _ & DNB & DSB & _). rewrite Forall_forall in DNB, DSB.
specialize (DNB (ly_img ly) ltac:(cbn; intuition)). specialize (DSB (ly_img ly) ltac:(cbn; intuition)).
unfold zdisjoint, AGjm.DZONE, AGis.DZONE, img_cover, TFIB_IMG_LO, TFIB_IMG_END, TFIB_INST, TFIB_OOM, TFIB_ERRNO in *.
cbn [fst snd] in *. repeat split; lia.
Qed.

End rows.
