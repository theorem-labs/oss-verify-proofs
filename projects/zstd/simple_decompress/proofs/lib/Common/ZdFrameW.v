(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma zd_is_error_lit : forall r, zd_is_error r = (18446744073709551496 <? r).
Proof. reflexivity. Qed.
Lemma zd_is_error_sltiu : forall c, Z.lxor (Z.b2z (c <? 18446744073709551497)) 1 = Z.b2z (zd_is_error c).
Proof.
  intros c. rewrite zd_is_error_lit.
  destruct (Z.ltb_spec c 18446744073709551497); destruct (Z.ltb_spec 18446744073709551496 c); cbn; try reflexivity; lia.
Qed.
Lemma ZERR_lit : forall c, ZERR c = 18446744073709551616 - c.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma le64_bytes : forall l i,
  le64 l i = Znth i l + 256 * Znth (i + 1) l + 65536 * Znth (i + 2) l + 16777216 * Znth (i + 3) l
             + 4294967296 * (Znth (i + 4) l + 256 * Znth (i + 5) l + 65536 * Znth (i + 6) l + 16777216 * Znth (i + 7) l).
Proof.
  intros l i. unfold le64, le32.
  replace (i + 4 + 1) with (i + 5) by lia. replace (i + 4 + 2) with (i + 6) by lia. replace (i + 4 + 3) with (i + 7) by lia.
  change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216. change (2^32) with 4294967296. reflexivity.
Qed.
Lemma le32_bytes : forall l i, le32 l i = Znth i l + 256 * Znth (i + 1) l + 65536 * Znth (i + 2) l + 16777216 * Znth (i + 3) l.
Proof. reflexivity. Qed.
Lemma le24_bytes : forall l i, le24 l i = Znth i l + 256 * Znth (i + 1) l + 65536 * Znth (i + 2) l.
Proof. reflexivity. Qed.
Lemma le16_bytes : forall l i, le16 l i = Znth i l + 256 * Znth (i + 1) l.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fhd_singleSegment_range : forall fhd, 0 <= fhd_singleSegment fhd < 2.
Proof. intros. unfold fhd_singleSegment. Z.div_mod_to_equations. lia. Qed.
Lemma fhd_reserved_range : forall fhd, 0 <= fhd_reserved fhd < 2.
Proof. intros. unfold fhd_reserved. Z.div_mod_to_equations. lia. Qed.
Lemma fhd_dictIDSizeCode_range : forall fhd, 0 <= fhd_dictIDSizeCode fhd < 4.
Proof. intros. unfold fhd_dictIDSizeCode. Z.div_mod_to_equations. lia. Qed.
Lemma fhd_fcsID_range : forall fhd, 0 <= fhd < 256 -> 0 <= fhd_fcsID fhd < 4.
Proof. intros. unfold fhd_fcsID. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition fhd_rp1 (fhd : Z) : Z := 5 + (if fhd_singleSegment fhd =? 0 then 1 else 0).
Definition fhd_extra (fhd : Z) : Z := if (fhd_singleSegment fhd =? 1) && (fhd_fcsID fhd =? 0) then 1 else 0.
Lemma fhd_rp1_range : forall fhd, 5 <= fhd_rp1 fhd <= 6.
Proof. intros. unfold fhd_rp1. destruct (fhd_singleSegment fhd =? 0); lia. Qed.
Lemma fhd_extra_range : forall fhd, 0 <= fhd_extra fhd <= 1.
Proof. intros. unfold fhd_extra. destruct ((fhd_singleSegment fhd =? 1) && (fhd_fcsID fhd =? 0)); lia. Qed.
Lemma fhd_header_size_split : forall fhd,
  fhd_header_size fhd = fhd_rp1 fhd + did_fieldSize (fhd_dictIDSizeCode fhd) + fcs_fieldSize (fhd_fcsID fhd) + fhd_extra fhd.
Proof. intros. unfold fhd_header_size, fhd_rp1, fhd_extra, ZD_FRAMEHEADERSIZE_PREFIX. lia. Qed.

(* [comment removed for export] *)
Lemma wl_windowLog_ok_iff : forall wl, 0 <= wl -> (ZD_WINDOWLOG_MAX <? wl_windowLog wl) = (175 <? wl).
Proof.
  intros wl Hw. unfold wl_windowLog, ZD_WINDOWLOG_MAX, ZD_WINDOWLOG_ABSOLUTEMIN.
  destruct (Z.ltb_spec 31 (wl / 8 + 10)); destruct (Z.ltb_spec 175 wl); try reflexivity; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma gfh_ret_pos : forall src off size v, 5 <= size ->
  get_frame_header src off size = FH_ret v -> 0 < v < 18446744073709551616.
Proof.
  intros src off size v H5 E. apply get_frame_header_ret in E.
  pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX ltac:(unfold ZD_FRAMEHEADERSIZE_PREFIX; lia)) as R.
  unfold ZD_FRAMEHEADERSIZE_PREFIX, ZD_SKIPPABLEHEADERSIZE, ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX, ZERR,
         ZE_prefix_unknown, ZE_frameParameter_unsupported, ZE_frameParameter_windowTooLarge in *.
  change (2^64) with 18446744073709551616 in *.
  destruct E as [-> | [-> | [[-> _] | [-> | [-> | ->]]]]]; lia.
Qed.
Lemma gfh_ok_of_ret0 : forall src off size, 5 <= size -> fh_retval (get_frame_header src off size) = 0 ->
  exists h, get_frame_header src off size = FH_ok h.
Proof.
  intros src off size H5 E. destruct (get_frame_header src off size) as [h|v] eqn:G; [eexists; reflexivity|].
  cbn in E. pose proof (gfh_ret_pos src off size v H5 G). lia.
Qed.
