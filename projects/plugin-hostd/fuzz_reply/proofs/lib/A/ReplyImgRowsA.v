(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image rows; closed computations at reply's image A, fuzz_reply.asan, pin
   42c58610e125).  Reuse search: proof-index errb_obj_owned_t IMG_SAPART IMG_JUNK (2026-10-30 03:5xZ): only the
   layer's Definitions, no discharge at any unit.

   The cf layer states these rows as Definitions over its own Section context; reply has not taken those layer files
   yet.  So each Lemma below states the layer Definition's body VERBATIM at reply's instance (the image class
   ImgBase.AImg at AImg_reply, A/AGif2reply.v:23; the image constants CfImg_A, A/CfImgA.v), and a consumer closes the
   layer's row with `exact` once the layer is on reply.  No Definition of the layer is copied here.
   - EXH_OFF: EXH_OFF_t, the cf layer's YGcfErrbSep.v:35 (commit ee95275bccbf): cf_exh_off = 68.
   - IMG_SAPART: the cf layer's YGcfInstRcSec.v:124-130 (commit 79f3c704722), sdeal_inst unfolded.
   - IMG_JUNK: YGcfInstRcSec.v:135-137 (commit 6233fefec18d), segment containment: every junk byte lies in a segment
     of im_segs; at this image the junk range of ts_junk, [0x9d000, 0x5fb000), is tiled exactly by the image's segments
     2 and 3, [0x9d000, 0x9f000) and [0x9f000, 0x5fb000) (the proof image's Asan.v).
   - ERRB_OWN: errb_obj_owned_t, the cf layer's YGcfInstBase.v:87-88 (commit 688e15b2663f), at a B with the image's
     symbol facts: the 56 bytes of the error buffer object [0xa5928, 0xa5960) (error_message_buffer, error_report_callback,
     error_message_buf_mutex, error_message_buffer_placeholder in the unstripped twin) lie in the owned region
     (0xa5910, 0x5c8710 - 0xa5910), A/AF0m.v:823.
   - ERRB_SEP: ERRB_SEP_t, YGcfErrbSep.v:25-28 (commit ee95275bccbf), at a B with the image's symbol facts: the error
     buffer object [0xa5928, 0xa5960) lies above the instance object [0xa2a58, 0xa3888), below the out-of-memory byte
     0x128320 and errno 0x5d93cc, below the depot's static zone [0x177f88, 0x5c8710), and apart from the nodes and store
     blocks, which layout_ok keeps apart from the image window (lo_disj) that im_img_cover makes cover the image. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG ImgBaseAGS AGif0reply AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGis AGjm.
Open Scope Z_scope.

(* EXH_OFF at image A (EXH_OFF_t): CfImg_A's cf_exh_off is 68 (A/CfImgA.v:36). *)
Lemma exh_off_A : @cf_exh_off CfImg_A = 68.
Proof. reflexivity. Qed.

(* IMG_SAPART at image A (YGcfInstRcSec.v:124-130, sdeal_inst unfolded): the four allocator-word ranges of the instance
   (TFIB_INST 0xa2a58 + 120 .. + 720, all below 0xa2d28) lie below the internal allocator's area (TFIB_IAL_LO 0xa72c0),
   the flag (0x135b48), the store (0x177f88) and the depot (0x187f98), A/AF0m.v:17-20. *)
Lemma img_sapart_A : forall B, @im_syms AImg_reply B -> forall a,
  ((as_inst B + 680 <= a < as_inst B + 684) \/ (as_inst B + 120 <= a < as_inst B + 129) \/
   (as_inst B + 144 <= a < as_inst B + 160) \/ (as_inst B + 704 <= a < as_inst B + 720)) ->
  ~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\
  ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof.
intros B TS a Ha. change (TfibSyms B) in TS.
rewrite (ts_inst B TS) in Ha.
rewrite (ts_depot B TS), (ts_store B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
replace (2 ^ 20) with 1048576 by reflexivity.
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
Qed.

(* ERRB_OWN at image A (errb_obj_owned_t, YGcfInstBase.v:87-88): cf_errbuf_obj is 0xa5928 (A/CfImgA.v:34), and
   [0xa5928, 0xa5960) lies in the fifth region of Tfib_owned_static, (0xa5910, 0x5c8710 - 0xa5910) (A/AF0m.v:823). *)
Lemma errb_obj_owned_A : forall B, @im_syms AImg_reply B ->
  forall a, @cf_errbuf_obj CfImg_A <= a < @cf_errbuf_obj CfImg_A + 56 -> Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS a Ha. change (TfibSyms B) in TS. rewrite (ts_owned B TS).
unfold CfImg_A in Ha. cbn [cf_errbuf_obj] in Ha.
apply Exists_exists. exists (0xa5910, 0x5c8710 - 0xa5910). split.
- apply (nth_error_In Tfib_owned_static 4). reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

Section rows. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* IMG_JUNK at image A (YGcfInstRcSec.v:135-137, commit 6233fefec18d): each junk range of TfibSyms lies in
   [0x9d000, 0x5fb000) (ts_junk, A/AF0m.v:875), which the image's segments 2 = [0x9d000, 0x9f000) and 3 = [0x9f000, 0x5fb000)
   (seg_size 0x55c000) tile. *)
Lemma img_junk_A : forall B ly r0, @im_syms AImg_reply B -> layout_ok ly -> In r0 (as_junk B ly) ->
  forall j, 0 <= j < snd r0 ->
  exists sg, In sg (@im_segs AImg_reply) /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
intros B ly r0 TS _ Hr j Hj. change (TfibSyms B) in TS.
destruct (ts_junk B TS ly r0 Hr) as (z & Ez & Hlo & Hhi). rewrite Ez. cbn [aeval].
destruct (Z.lt_ge_cases (z + j) 0x9f000) as [Hl | Hg].
- exists Asan.Asan_segment_002. split; [change (In Asan.Asan_segment_002 tfibsegs); do 2 right; left; reflexivity|].
  change (Z.of_N (seg_base Asan.Asan_segment_002)) with 0x9d000. change (Z.of_N (seg_size Asan.Asan_segment_002)) with 0x2000. lia.
- exists Asan.Asan_segment_003. split; [change (In Asan.Asan_segment_003 tfibsegs); do 3 right; left; reflexivity|].
  change (Z.of_N (seg_base Asan.Asan_segment_003)) with 0x9f000. change (Z.of_N (seg_size Asan.Asan_segment_003)) with 0x55c000. lia.
Qed.

(* ERRB_SEP at image A (ERRB_SEP_t, YGcfErrbSep.v:25-28, commit ee95275bccbf): cf_errbuf_obj is 0xa5928 (A/CfImgA.v:31); the
   instance, the out-of-memory byte and errno are 0xa2a58 / 0x128320 / 0x5d93cc (A/AF0m.v:17-22); ims_dzone and ag_dzone are reply's DZONE
   (A/AGif4reply.v:29, A/AGif0reply.v:119), whose static part is [0x177f88, 0x5c8710); its nodes and store blocks are owned extents that
   lo_disj (YG0f.v:324) keeps apart from ly_img, which im_img_cover (img_cover) makes cover [TFIB_IMG_LO, TFIB_IMG_END). *)
Lemma errb_sep_A : forall B, @im_syms AImg_reply B -> forall ly a, layout_ok ly -> @im_img_cover AImg_reply ly -> ly_tsd ly = as_tsd B ->
  @cf_errbuf_obj CfImg_A <= a < @cf_errbuf_obj CfImg_A + 56 ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\
  ~ ims_dzone ly a /\ ~ ag_dzone ly a.
Proof.
intros B TS ly a LY IC _ Ha. change (TfibSyms B) in TS. change (img_cover ly) in IC.
unfold CfImg_A in Ha. cbn [cf_errbuf_obj] in Ha.
rewrite (ts_inst B TS), (ts_oom B TS), (ts_errno B TS).
change (ims_dzone ly a) with (AGjm.DZONE ly a). change (ag_dzone ly a) with (AGis.DZONE ly a).
pose proof (lo_disj ly LY) as D. unfold static_extents, owned_extents in D. cbn [pairwise app] in D.
destruct D as (_ & _ & _ & _ & DNB & DSB & _). rewrite Forall_forall in DNB, DSB.
specialize (DNB (ly_img ly) ltac:(cbn; intuition)). specialize (DSB (ly_img ly) ltac:(cbn; intuition)).
unfold zdisjoint, AGjm.DZONE, AGis.DZONE, img_cover, TFIB_IMG_LO, TFIB_IMG_END, TFIB_INST, TFIB_OOM, TFIB_ERRNO in *.
cbn [fst snd] in *. repeat split; lia.
Qed.

End rows.
