(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zd_is_error_ZERR c : 0 < c < ZE_maxCode -> zd_is_error (ZERR c) = true.
Proof. unfold zd_is_error, ZERR, ZE_maxCode. intros. apply Z.ltb_lt. lia. Qed.

Lemma zd_is_error_false_iff r : zd_is_error r = false <-> r <= 2^64 - 120.
Proof. unfold zd_is_error, ZE_maxCode. rewrite Z.ltb_ge. reflexivity. Qed.

Lemma zd_is_error_true_iff r : zd_is_error r = true <-> 2^64 - 120 < r.
Proof. unfold zd_is_error, ZE_maxCode. rewrite Z.ltb_lt. reflexivity. Qed.

Lemma zd_error_code_ZERR c : 0 < c < ZE_maxCode -> zd_error_code (ZERR c) = c.
Proof. intros H. unfold zd_error_code. rewrite zd_is_error_ZERR by exact H. unfold ZERR. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Bytes.
  Variable src : list Z.
  Hypothesis SRC : all_bytes src.

  Lemma le16_range p : 0 <= le16 src p < 2^16.
  Proof. unfold le16. pose proof (SRC p). pose proof (SRC (p + 1)). lia. Qed.

  Lemma le24_range p : 0 <= le24 src p < 2^24.
  Proof. unfold le24. pose proof (SRC p). pose proof (SRC (p + 1)). pose proof (SRC (p + 2)). lia. Qed.

  Lemma le32_range p : 0 <= le32 src p < 2^32.
  Proof.
    unfold le32. pose proof (SRC p). pose proof (SRC (p + 1)). pose proof (SRC (p + 2)). pose proof (SRC (p + 3)). lia.
  Qed.

  Lemma le64_range p : 0 <= le64 src p < 2^64.
  Proof. unfold le64. pose proof (le32_range p). pose proof (le32_range (p + 4)). lia. Qed.
End Bytes.

(* [comment removed for export] *)
Lemma land_mask_F0 magic : 0 <= magic < 2^32 -> Z.land magic 4294967280 = 16 * (magic / 16).
Proof.
  intros H.
  assert (E : Z.land magic 4294967280 = Z.ldiff magic (Z.ones 4)).
  { apply Z.bits_inj'. intros n Hn.
    change 4294967280 with (Z.ldiff (Z.ones 32) (Z.ones 4)).
    rewrite Z.land_spec, !Z.ldiff_spec.
    destruct (Z.ltb_spec n 32) as [L|L].
    - rewrite (Z.ones_spec_low 32 n) by lia. rewrite Bool.andb_true_l. reflexivity.
    - assert (T : Z.testbit magic n = false).
      { destruct (Z.eq_dec magic 0) as [->|NZ]; [apply Z.bits_0|].
        apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32; [|exact L].
        apply Z.log2_lt_pow2; lia. }
      rewrite T. reflexivity. }
  rewrite E, Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^4) with 16. lia.
Qed.

Lemma is_skippable_magic_land magic : 0 <= magic < 2^32 ->
  is_skippable_magic magic = (Z.land magic 4294967280 =? ZD_MAGIC_SKIPPABLE_START).
Proof.
  intros H. rewrite land_mask_F0 by exact H. unfold is_skippable_magic, ZD_MAGIC_SKIPPABLE_START.
  destruct (Z.eqb_spec (magic / 16) 25481893), (Z.eqb_spec (16 * (magic / 16)) 407710288); lia.
Qed.

Lemma is_skippable_magic_range magic :
  is_skippable_magic magic = true <-> ZD_MAGIC_SKIPPABLE_START <= magic < ZD_MAGIC_SKIPPABLE_START + 16.
Proof.
  unfold is_skippable_magic, ZD_MAGIC_SKIPPABLE_START. rewrite Z.eqb_eq.
  pose proof (Z.div_mod magic 16 ltac:(lia)). pose proof (Z.mod_pos_bound magic 16 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma did_fieldSize_range c : 0 <= did_fieldSize c <= 4.
Proof. unfold did_fieldSize. destruct (c =? 0), (c =? 1), (c =? 2); lia. Qed.

Lemma fcs_fieldSize_range c : 0 <= fcs_fieldSize c <= 8.
Proof. unfold fcs_fieldSize. destruct (c =? 0), (c =? 1), (c =? 2); lia. Qed.

Lemma fhd_header_size_range fhd : ZD_FRAMEHEADERSIZE_MIN <= fhd_header_size fhd <= ZD_FRAMEHEADERSIZE_MAX.
Proof.
  unfold fhd_header_size, ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX, ZD_FRAMEHEADERSIZE_PREFIX.
  pose proof (did_fieldSize_range (fhd_dictIDSizeCode fhd)).
  pose proof (Z.mod_pos_bound (fhd / 32) 2 ltac:(lia)) as SS. fold (fhd_singleSegment fhd) in SS.
  unfold fcs_fieldSize.
  destruct (Z.eqb_spec (fhd_singleSegment fhd) 0), (Z.eqb_spec (fhd_singleSegment fhd) 1),
           (Z.eqb_spec (fhd_fcsID fhd) 0), (Z.eqb_spec (fhd_fcsID fhd) 1), (Z.eqb_spec (fhd_fcsID fhd) 2);
    cbn [andb]; lia.
Qed.

Lemma frame_header_size_ge5 src off size : ZD_FRAMEHEADERSIZE_PREFIX <= size ->
  frame_header_size src off size = fhd_header_size (Znth (off + 4) src).
Proof. intros H. unfold frame_header_size. destruct (Z.ltb_spec size ZD_FRAMEHEADERSIZE_PREFIX); [lia|reflexivity]. Qed.

Lemma frame_header_size_range src off size : ZD_FRAMEHEADERSIZE_PREFIX <= size ->
  ZD_FRAMEHEADERSIZE_MIN <= frame_header_size src off size <= ZD_FRAMEHEADERSIZE_MAX.
Proof. intros H. rewrite frame_header_size_ge5 by exact H. apply fhd_header_size_range. Qed.

Lemma wl_windowSize_range wl : 0 <= wl -> wl_windowLog wl <= ZD_WINDOWLOG_MAX ->
  2^10 <= wl_windowSize wl < 2^32.
Proof.
  unfold wl_windowSize, wl_windowLog, ZD_WINDOWLOG_MAX, ZD_WINDOWLOG_ABSOLUTEMIN. intros H0 H.
  pose proof (Z.mod_pos_bound wl 8 ltac:(lia)) as M.
  assert (Q : 0 <= wl / 8) by (apply Z.div_pos; lia).
  set (L := wl / 8 + 10) in *.
  assert (P1 : 2^10 <= 2^L) by (apply Z.pow_le_mono_r; lia).
  assert (P2 : 2^L <= 2^31) by (apply Z.pow_le_mono_r; lia).
  assert (D : 0 <= 2^L / 8 <= 2^L / 8) by (split; [apply Z.div_pos; lia|lia]).
  assert (D8 : 8 * (2^L / 8) <= 2^L) by (apply Z.mul_div_le; lia).
  change (2^31) with 2147483648 in P2. change (2^32) with 4294967296. change (2^10) with 1024 in *.
  nia.
Qed.

Section HeaderFacts.
  Variable src : list Z.
  Hypothesis SRC : all_bytes src.

  Lemma fh_read_dictID_range pos code : 0 <= fh_read_dictID src pos code < 2^32.
  Proof.
    unfold fh_read_dictID. pose proof (SRC pos). pose proof (le16_range src SRC pos). pose proof (le32_range src SRC pos).
    destruct (code =? 0), (code =? 1), (code =? 2); lia.
  Qed.

  Lemma fh_read_fcs_range pos fcsID ss : 0 <= fh_read_fcs src pos fcsID ss < 2^64.
  Proof.
    unfold fh_read_fcs, ZD_CONTENTSIZE_UNKNOWN. pose proof (SRC pos). pose proof (le16_range src SRC pos).
    pose proof (le32_range src SRC pos). pose proof (le64_range src SRC pos).
    destruct (fcsID =? 0), (ss =? 0), (fcsID =? 1), (fcsID =? 2); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma get_frame_header_ok off size h : get_frame_header src off size = FH_ok h ->
    (fh_type h = 0 \/ fh_type h = 1) /\
    ZD_FRAMEHEADERSIZE_PREFIX <= size /\ fh_hsize h <= size /\
    0 <= fh_fcs h < 2^64 /\ 0 <= fh_window h < 2^64 /\ 0 <= fh_bsmax h <= ZD_BLOCKSIZE_MAX /\
    0 <= fh_dictID h < 2^32 /\ 0 <= fh_checksum h <= 1 /\
    (fh_type h = 0 -> le32 src off = ZD_MAGICNUMBER /\ fh_hsize h = frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX /\
                      ZD_FRAMEHEADERSIZE_MIN <= fh_hsize h <= ZD_FRAMEHEADERSIZE_MAX /\ fh_bsmax h = Z.min (fh_window h) ZD_BLOCKSIZE_MAX) /\
    (fh_type h = 1 -> is_skippable_magic (le32 src off) = true /\ fh_hsize h = ZD_SKIPPABLEHEADERSIZE /\
                      fh_fcs h = le32 src (off + 4) /\ fh_dictID h = le32 src off - ZD_MAGIC_SKIPPABLE_START /\ fh_dictID h < 16).
  Proof.
    unfold get_frame_header.
    destruct (Z.ltb_spec size ZD_FRAMEHEADERSIZE_PREFIX) as [L|L].
    { destruct (size =? 0); [discriminate|].
      destruct (_ =? ZD_MAGICNUMBER); [discriminate|]. destruct (is_skippable_magic _); discriminate. }
    destruct (Z.eqb_spec (le32 src off) ZD_MAGICNUMBER) as [M|M].
    - unfold get_frame_header_zstd.
      pose proof (frame_header_size_range src off size L) as R.
      rewrite (frame_header_size_ge5 src off size L) in *.
      rewrite (frame_header_size_ge5 src off ZD_FRAMEHEADERSIZE_PREFIX) by lia.
      destruct (Z.ltb_spec size (fhd_header_size (Znth (off + 4) src))) as [L2|L2]; [discriminate|].
      destruct (negb _); [discriminate|].
      set (fhd := Znth (off + 4) src) in *. set (wl := Znth (off + 5) src) in *.
      destruct (Z.eqb_spec (fhd_singleSegment fhd) 0) as [SS|SS]; cbn [andb].
      + destruct (Z.ltb_spec ZD_WINDOWLOG_MAX (wl_windowLog wl)) as [W|W]; [discriminate|].
        intros E. injection E as <-. cbn [fh_type fh_hsize fh_fcs fh_window fh_bsmax fh_dictID fh_checksum].
        pose proof (wl_windowSize_range wl ltac:(apply SRC) W) as WR.
        pose proof (fh_read_fcs_range (off + 5 + 1 + did_fieldSize (fhd_dictIDSizeCode fhd)) (fhd_fcsID fhd) (fhd_singleSegment fhd)).
        pose proof (fh_read_dictID_range (off + 5 + 1) (fhd_dictIDSizeCode fhd)).
        pose proof (Z.mod_pos_bound (fhd / 4) 2 ltac:(lia)). unfold fhd_checksumFlag.
        unfold ZD_BLOCKSIZE_MAX in *.
        repeat split; try lia; try (intros; discriminate); try (left; reflexivity).
      + intros E. injection E as <-. cbn [fh_type fh_hsize fh_fcs fh_window fh_bsmax fh_dictID fh_checksum].
        pose proof (fh_read_fcs_range (off + 5 + 0 + did_fieldSize (fhd_dictIDSizeCode fhd)) (fhd_fcsID fhd) (fhd_singleSegment fhd)).
        pose proof (fh_read_dictID_range (off + 5 + 0) (fhd_dictIDSizeCode fhd)).
        pose proof (Z.mod_pos_bound (fhd / 4) 2 ltac:(lia)). unfold fhd_checksumFlag.
        unfold ZD_BLOCKSIZE_MAX in *.
        repeat split; try lia; try (intros; discriminate); try (left; reflexivity).
    - destruct (is_skippable_magic (le32 src off)) eqn:SK; [|discriminate].
      destruct (Z.ltb_spec size ZD_SKIPPABLEHEADERSIZE) as [L2|L2]; [discriminate|].
      intros E. injection E as <-. cbn [fh_type fh_hsize fh_fcs fh_window fh_bsmax fh_dictID fh_checksum].
      pose proof (le32_range src SRC (off + 4)). apply is_skippable_magic_range in SK.
      unfold ZD_BLOCKSIZE_MAX, ZD_SKIPPABLEHEADERSIZE, ZD_MAGIC_SKIPPABLE_START in *.
      repeat split; try lia; try (intros; discriminate); try (right; reflexivity).
  Qed.

  (* [comment removed for export] *)
  Lemma get_frame_header_ret off size v : get_frame_header src off size = FH_ret v ->
    v = ZD_FRAMEHEADERSIZE_PREFIX \/ v = ZD_SKIPPABLEHEADERSIZE \/
    (v = frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX /\ size < v) \/
    v = ZERR ZE_prefix_unknown \/ v = ZERR ZE_frameParameter_unsupported \/ v = ZERR ZE_frameParameter_windowTooLarge.
  Proof.
    unfold get_frame_header.
    destruct (Z.ltb_spec size ZD_FRAMEHEADERSIZE_PREFIX) as [L|L].
    { destruct (size =? 0); [intros E; injection E as <-; auto|].
      destruct (_ =? ZD_MAGICNUMBER); [intros E; injection E as <-; auto|].
      destruct (is_skippable_magic _); intros E; injection E as <-; auto. }
    destruct (Z.eqb_spec (le32 src off) ZD_MAGICNUMBER) as [M|M].
    - unfold get_frame_header_zstd. rewrite (frame_header_size_ge5 src off size L).
      rewrite (frame_header_size_ge5 src off ZD_FRAMEHEADERSIZE_PREFIX) by lia.
      destruct (Z.ltb_spec size (fhd_header_size (Znth (off + 4) src))) as [L2|L2].
      { intros E; injection E as <-. right. right. left. split; [reflexivity|exact L2]. }
      destruct (negb _); [intros E; injection E as <-; auto 10|].
      destruct (_ && _); [intros E; injection E as <-; auto 10|discriminate].
    - destruct (is_skippable_magic (le32 src off)); [|intros E; injection E as <-; auto 10].
      destruct (Z.ltb_spec size ZD_SKIPPABLEHEADERSIZE); [intros E; injection E as <-; auto|discriminate].
  Qed.

  (* [comment removed for export] *)
  Lemma get_frame_header_mono off hsz size h :
    get_frame_header src off hsz = FH_ok h -> hsz <= size -> get_frame_header src off size = FH_ok h.
  Proof.
    intros G LE. pose proof (get_frame_header_ok off hsz h G) as (_ & L5 & _).
    revert G. unfold get_frame_header.
    destruct (Z.ltb_spec hsz ZD_FRAMEHEADERSIZE_PREFIX); [lia|].
    destruct (Z.ltb_spec size ZD_FRAMEHEADERSIZE_PREFIX); [lia|].
    destruct (Z.eqb_spec (le32 src off) ZD_MAGICNUMBER) as [M|M].
    - unfold get_frame_header_zstd. rewrite !frame_header_size_ge5 by lia.
      destruct (Z.ltb_spec hsz (fhd_header_size (Znth (off + 4) src))); [discriminate|].
      destruct (Z.ltb_spec size (fhd_header_size (Znth (off + 4) src))); [lia|]. auto.
    - destruct (is_skippable_magic (le32 src off)); [|discriminate].
      destruct (Z.ltb_spec hsz ZD_SKIPPABLEHEADERSIZE); [discriminate|].
      destruct (Z.ltb_spec size ZD_SKIPPABLEHEADERSIZE); [lia|]. auto.
  Qed.
End HeaderFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section BlockFacts.
  Variable src : list Z.
  Hypothesis SRC : all_bytes src.

  (* [comment removed for export] *)
  Lemma skippable_wrap_iff s : 0 <= s < 2^32 -> ((s + ZD_SKIPPABLEHEADERSIZE) mod 2^32 <? s) = (2^32 - 9 <? s).
  Proof.
    intros H. unfold ZD_SKIPPABLEHEADERSIZE.
    destruct (Z.ltb_spec (2^32 - 9) s) as [L|L].
    - apply Z.ltb_lt. replace ((s + 8) mod 2^32) with (s + 8 - 2^32); [lia|].
      apply Z.mod_unique with 1; lia.
    - apply Z.ltb_ge. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma read_skippable_frame_size_ok off size : zd_is_error (read_skippable_frame_size src off size) = false ->
    size < 2^64 - 120 ->
    read_skippable_frame_size src off size = ZD_SKIPPABLEHEADERSIZE + le32 src (off + 4) /\
    ZD_SKIPPABLEHEADERSIZE <= read_skippable_frame_size src off size <= size.
  Proof.
    unfold read_skippable_frame_size. intros E SZ. revert E.
    destruct (Z.ltb_spec size ZD_SKIPPABLEHEADERSIZE). { rewrite zd_is_error_ZERR by (compute; auto). discriminate. }
    destruct (_ <? le32 src (off + 4)). { rewrite zd_is_error_ZERR by (compute; auto). discriminate. }
    destruct (Z.ltb_spec size (ZD_SKIPPABLEHEADERSIZE + le32 src (off + 4))).
    { rewrite zd_is_error_ZERR by (compute; auto). discriminate. }
    intros _. pose proof (le32_range src SRC (off + 4)). unfold ZD_SKIPPABLEHEADERSIZE in *. lia.
  Qed.

  Lemma cblock_props_range hdr : 0 <= hdr < 2^24 ->
    0 <= bp_type (cblock_props hdr) <= 3 /\ 0 <= bp_last (cblock_props hdr) <= 1 /\ 0 <= bp_orig (cblock_props hdr) < 2^21.
  Proof.
    intros H. unfold cblock_props; cbn [bp_type bp_last bp_orig].
    pose proof (Z.mod_pos_bound (hdr / 2) 4 ltac:(lia)). pose proof (Z.mod_pos_bound hdr 2 ltac:(lia)).
    assert (0 <= hdr / 8 < 2^21) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma get_cblock_size_ok ip size cbs bp : get_cblock_size src ip size = Some (cbs, bp) ->
    ZD_blockHeaderSize <= size /\ bp = cblock_props (le24 src ip) /\
    0 <= bp_type bp <= 3 /\ 0 <= bp_last bp <= 1 /\ 0 <= bp_orig bp < 2^21 /\
    (zd_is_error cbs = false ->
       bp_type bp <> bt_reserved /\ 0 <= cbs < 2^21 /\ (bp_type bp = bt_rle -> cbs = 1) /\ (bp_type bp <> bt_rle -> cbs = bp_orig bp)).
  Proof.
    unfold get_cblock_size. destruct (Z.ltb_spec size ZD_blockHeaderSize); [discriminate|].
    intros E. injection E as <- <-.
    pose proof (cblock_props_range (le24 src ip) (le24_range src SRC ip)) as (T & L & O).
    repeat (split; [first [assumption | reflexivity | lia]|]).
    unfold bt_rle, bt_reserved. cbn [cblock_props bp_type bp_last bp_orig] in *.
    destruct (Z.eqb_spec ((le24 src ip / 2) mod 4) 1) as [R|R].
    - intros _. repeat split; try lia.
    - destruct (Z.eqb_spec ((le24 src ip / 2) mod 4) 3) as [R3|R3].
      + rewrite zd_is_error_ZERR by (compute; auto). discriminate.
      + intros _. repeat split; try lia.
  Qed.
End BlockFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Finder.
  Variable src : list Z.
  Hypothesis SRC : all_bytes src.

  Lemma fsi_blocks_fuel_irrel : forall f1 f2 ip rem nb, rem < Z.of_nat f1 -> rem < Z.of_nat f2 ->
    fsi_blocks_fuel f1 src ip rem nb = fsi_blocks_fuel f2 src ip rem nb.
  Proof.
    assert (Z0 : forall f ip rem nb, rem < 0 -> fsi_blocks_fuel f src ip rem nb = FL_err (ZERR ZE_srcSize_wrong)).
    { intros [|f] ip rem nb H; cbn [fsi_blocks_fuel]; [reflexivity|].
      unfold get_cblock_size. destruct (Z.ltb_spec rem ZD_blockHeaderSize); [reflexivity|].
      unfold ZD_blockHeaderSize in *. lia. }
    induction f1 as [|f1 IH]; intros f2 ip rem nb H1 H2.
    - rewrite !Z0 by (cbn in H1; lia). reflexivity.
    - destruct f2 as [|f2]. { rewrite !Z0 by (cbn in H2; lia). reflexivity. }
      cbn [fsi_blocks_fuel].
      destruct (get_cblock_size src ip rem) as [[cbs bp]|] eqn:G; [|reflexivity].
      destruct (zd_is_error cbs) eqn:E; [reflexivity|].
      destruct (Z.ltb_spec rem (ZD_blockHeaderSize + cbs)); [reflexivity|].
      destruct (bp_last bp =? 0); [|reflexivity].
      pose proof (get_cblock_size_ok src SRC ip rem cbs bp G) as (_ & _ & _ & _ & _ & K).
      specialize (K E). unfold ZD_blockHeaderSize in *. apply IH; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fsi_blocks_eq ip rem nb :
    fsi_blocks src ip rem nb =
    match get_cblock_size src ip rem with
    | None => FL_err (ZERR ZE_srcSize_wrong)
    | Some (cbs, bp) =>
      if zd_is_error cbs then FL_err cbs
      else if rem <? ZD_blockHeaderSize + cbs then FL_err (ZERR ZE_srcSize_wrong)
      else if bp_last bp =? 0
           then fsi_blocks src (ip + (ZD_blockHeaderSize + cbs)) (rem - (ZD_blockHeaderSize + cbs)) (nb + 1)
           else FL_done (ip + (ZD_blockHeaderSize + cbs)) (rem - (ZD_blockHeaderSize + cbs)) (nb + 1)
    end.
  Proof.
    unfold fsi_blocks at 1. cbn [fsi_blocks_fuel].
    destruct (get_cblock_size src ip rem) as [[cbs bp]|] eqn:G; [|reflexivity].
    destruct (zd_is_error cbs) eqn:E; [reflexivity|].
    destruct (Z.ltb_spec rem (ZD_blockHeaderSize + cbs)); [reflexivity|].
    destruct (bp_last bp =? 0); [|reflexivity].
    pose proof (get_cblock_size_ok src SRC ip rem cbs bp G) as (_ & _ & _ & _ & _ & K).
    specialize (K E). unfold fsi_blocks, ZD_blockHeaderSize in *. apply fsi_blocks_fuel_irrel; lia.
  Qed.

  Lemma FL_done_inj a b c a' b' c' : FL_done a b c = FL_done a' b' c' -> a = a' /\ b = b' /\ c = c'.
  Proof. intros E. injection E. auto. Qed.

  (* [comment removed for export] *)
  Lemma fsi_blocks_done : forall f ip rem nb ip' rem' nb',
    fsi_blocks_fuel f src ip rem nb = FL_done ip' rem' nb' ->
    ip + ZD_blockHeaderSize <= ip' /\ 0 <= rem' /\ ip' + rem' = ip + rem /\ nb + 1 <= nb' /\ nb' - nb <= (rem - rem') / 3.
  Proof.
    induction f as [|f IH]; intros ip rem nb ip' rem' nb'; cbn [fsi_blocks_fuel]; [discriminate|].
    destruct (get_cblock_size src ip rem) as [[cbs bp]|] eqn:G; [|discriminate].
    destruct (zd_is_error cbs) eqn:E; [discriminate|].
    destruct (Z.ltb_spec rem (ZD_blockHeaderSize + cbs)); [discriminate|].
    pose proof (get_cblock_size_ok src SRC ip rem cbs bp G) as (_ & _ & _ & _ & _ & K). specialize (K E).
    unfold ZD_blockHeaderSize in *.
    destruct (bp_last bp =? 0).
    - intros R. apply IH in R. destruct R as (R1 & R2 & R3 & R4 & R5).
      repeat split; try lia.
      assert (nb' - (nb + 1) + 1 <= (rem - rem') / 3); [|lia].
      replace (rem - rem') with ((rem - (3 + cbs) - rem') + cbs + 1 * 3) by lia.
      rewrite Z.div_add by lia.
      assert ((rem - (3 + cbs) - rem') / 3 <= (rem - (3 + cbs) - rem' + cbs) / 3) by (apply Z.div_le_mono; lia). lia.
    - intros R. apply FL_done_inj in R. destruct R as (<- & <- & <-). repeat split; try lia.
      replace (rem - (rem - (3 + cbs))) with (cbs + 1 * 3) by lia. rewrite Z.div_add by lia.
      assert (0 <= cbs / 3) by (apply Z.div_pos; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma find_frame_compressed_size_ok off size : size < 2^64 - 120 ->
    zd_is_error (find_frame_compressed_size src off size) = false ->
    ZD_SKIPPABLEHEADERSIZE <= find_frame_compressed_size src off size <= size.
  Proof.
    intros SZ. unfold find_frame_compressed_size, find_frame_size_info.
    destruct (_ && _).
    { cbn [fsi_csize]. intros E. apply (read_skippable_frame_size_ok src SRC off size E SZ). }
    destruct (get_frame_header src off size) as [h|v] eqn:G.
    2:{ destruct (zd_is_error v) eqn:E; cbn [fsi_csize]; [congruence|].
        rewrite zd_is_error_ZERR by (compute; auto). discriminate. }
    pose proof (get_frame_header_ok src SRC off size h G) as (T & L5 & HS & _ & _ & _ & _ & CK & F0 & F1).
    destruct (fsi_blocks src (off + fh_hsize h) (size - fh_hsize h) 0) as [v|ip rem nb] eqn:B; cbn [fsi_csize].
    { intros E. exfalso. revert B. unfold fsi_blocks. generalize (S (Z.to_nat (size - fh_hsize h))).
      intros f. revert E. generalize (off + fh_hsize h), (size - fh_hsize h), 0. clear - SRC.
      induction f as [|f IH]; intros ip rem nb E; cbn [fsi_blocks_fuel].
      - intros B. injection B as <-. rewrite zd_is_error_ZERR in E by (compute; auto). discriminate.
      - destruct (get_cblock_size src ip rem) as [[cbs bp]|].
        2:{ intros B. injection B as <-. rewrite zd_is_error_ZERR in E by (compute; auto). discriminate. }
        destruct (zd_is_error cbs) eqn:E2. { intros B. injection B as <-. congruence. }
        destruct (_ <? _). { intros B. injection B as <-. rewrite zd_is_error_ZERR in E by (compute; auto). discriminate. }
        destruct (_ =? 0); [apply IH; exact E|discriminate]. }
    apply fsi_blocks_done in B. destruct B as (B1 & B2 & B3 & B4 & _).
    assert (HS6 : ZD_FRAMEHEADERSIZE_MIN <= fh_hsize h).
    { destruct T as [T|T]; [apply F0 in T; lia|apply F1 in T; unfold ZD_FRAMEHEADERSIZE_MIN, ZD_SKIPPABLEHEADERSIZE in *; lia]. }
    unfold ZD_FRAMEHEADERSIZE_MIN, ZD_SKIPPABLEHEADERSIZE, ZD_blockHeaderSize in *.
    destruct (Z.eqb_spec (fh_checksum h) 0); cbn [negb andb].
    - cbn [fsi_csize]. intros _. lia.
    - destruct (Z.ltb_spec rem 4); cbn [fsi_csize].
      + rewrite zd_is_error_ZERR by (compute; auto). discriminate.
      + intros _. lia.
  Qed.
End Finder.

Section FinderLoop.
  Variable src : list Z.
  Hypothesis SRC : all_bytes src.

  Lemma find_dsize_fuel_irrel : forall f1 f2 off size total, size < 2^64 - 120 ->
    size < Z.of_nat f1 -> size < Z.of_nat f2 ->
    find_dsize_fuel f1 src off size total = find_dsize_fuel f2 src off size total.
  Proof.
    assert (Z0 : forall f off size total, size < 0 -> find_dsize_fuel f src off size total = ZD_CONTENTSIZE_ERROR).
    { intros [|f] off size total H; cbn [find_dsize_fuel]; [reflexivity|].
      destruct (Z.ltb_spec size ZD_FRAMEHEADERSIZE_PREFIX); [|unfold ZD_FRAMEHEADERSIZE_PREFIX in *; lia].
      destruct (Z.eqb_spec size 0); [lia|reflexivity]. }
    induction f1 as [|f1 IH]; intros f2 off size total SZ H1 H2.
    - rewrite !Z0 by (cbn in H1; lia). reflexivity.
    - destruct f2 as [|f2]. { rewrite !Z0 by (cbn in H2; lia). reflexivity. }
      cbn [find_dsize_fuel].
      destruct (size <? ZD_FRAMEHEADERSIZE_PREFIX); [reflexivity|].
      destruct (is_skippable_magic (le32 src off)).
      + destruct (zd_is_error (read_skippable_frame_size src off size)) eqn:E; [reflexivity|].
        pose proof (read_skippable_frame_size_ok src SRC off size E SZ) as (_ & K).
        unfold ZD_SKIPPABLEHEADERSIZE in *. apply IH; lia.
      + destruct (_ <=? get_frame_content_size src off size); [reflexivity|].
        destruct (_ <=? _); [reflexivity|].
        destruct (zd_is_error (find_frame_compressed_size src off size)) eqn:E; [reflexivity|].
        pose proof (find_frame_compressed_size_ok src SRC off size SZ E) as K.
        unfold ZD_SKIPPABLEHEADERSIZE in *. apply IH; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma find_dsize_eq off size total : size < 2^64 - 120 ->
    find_dsize src off size total =
    if size <? ZD_FRAMEHEADERSIZE_PREFIX then (if size =? 0 then total else ZD_CONTENTSIZE_ERROR)
    else if is_skippable_magic (le32 src off) then
      let sk := read_skippable_frame_size src off size in
      if zd_is_error sk then ZD_CONTENTSIZE_ERROR else find_dsize src (off + sk) (size - sk) total
    else
      let fcs := get_frame_content_size src off size in
      if ZD_CONTENTSIZE_ERROR <=? fcs then fcs
      else if 2^64 <=? total + fcs then ZD_CONTENTSIZE_ERROR
      else
        let fsz := find_frame_compressed_size src off size in
        if zd_is_error fsz then ZD_CONTENTSIZE_ERROR else find_dsize src (off + fsz) (size - fsz) (total + fcs).
  Proof.
    intros SZ. unfold find_dsize at 1. cbn [find_dsize_fuel].
    destruct (size <? ZD_FRAMEHEADERSIZE_PREFIX); [reflexivity|].
    destruct (is_skippable_magic (le32 src off)); cbv zeta.
    - destruct (zd_is_error (read_skippable_frame_size src off size)) eqn:E; [reflexivity|].
      pose proof (read_skippable_frame_size_ok src SRC off size E SZ) as (_ & K).
      unfold find_dsize, ZD_SKIPPABLEHEADERSIZE in *. apply find_dsize_fuel_irrel; lia.
    - destruct (_ <=? get_frame_content_size src off size); [reflexivity|].
      destruct (_ <=? _); [reflexivity|].
      destruct (zd_is_error (find_frame_compressed_size src off size)) eqn:E; [reflexivity|].
      pose proof (find_frame_compressed_size_ok src SRC off size SZ E) as K.
      unfold find_dsize, ZD_SKIPPABLEHEADERSIZE in *. apply find_dsize_fuel_irrel; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u64_add_overflow_iff total fcs : 0 <= total < 2^64 -> 0 <= fcs < 2^64 ->
    ((total + fcs) mod 2^64 <? total) = (2^64 <=? total + fcs).
  Proof.
    intros H1 H2. destruct (Z.leb_spec (2^64) (total + fcs)) as [L|L].
    - apply Z.ltb_lt. replace ((total + fcs) mod 2^64) with (total + fcs - 2^64); [lia|].
      apply Z.mod_unique with 1; lia.
    - apply Z.ltb_ge. rewrite Z.mod_small by lia. lia.
  Qed.
End FinderLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Decoder.
  Variable src : list Z.
  Hypothesis SRC : all_bytes src.

  Lemma block_result_range room cbs bp v ip rem :
    get_cblock_size src ip rem = Some (cbs, bp) -> zd_is_error cbs = false ->
    block_result room cbs bp v -> 0 <= v <= room.
  Proof.
    intros G E B. pose proof (get_cblock_size_ok src SRC ip rem cbs bp G) as (_ & _ & _ & _ & O & K). specialize (K E).
    unfold block_result in B. destruct (bp_type bp =? bt_raw); [lia|]. destruct (bp_type bp =? bt_rle); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dblocks_fsi cap : forall ip rem o ip' rem' o', dblocks src cap ip rem o ip' rem' o' ->
    (0 <= o -> o <= o' <= cap) /\
    (forall nb, exists nb', fsi_blocks src ip rem nb = FL_done ip' rem' nb').
  Proof.
    induction 1 as [ip rem o cbs bp v G E L B LAST | ip rem o cbs bp v ip' rem' o' G E L B LAST D IH].
    - pose proof (block_result_range _ _ _ _ _ _ G E B) as R. split; [lia|].
      intros nb. exists (nb + 1). rewrite (fsi_blocks_eq src SRC). rewrite G, E.
      destruct (Z.ltb_spec rem (ZD_blockHeaderSize + cbs)); [lia|].
      destruct (Z.eqb_spec (bp_last bp) 0); [contradiction|].
      f_equal; lia.
    - pose proof (block_result_range _ _ _ _ _ _ G E B) as R. destruct IH as (IH1 & IH2). split; [lia|].
      intros nb. destruct (IH2 (nb + 1)) as (nb' & IH3). exists nb'.
      rewrite (fsi_blocks_eq src SRC). rewrite G, E.
      destruct (Z.ltb_spec rem (ZD_blockHeaderSize + cbs)); [lia|].
      destruct (Z.eqb_spec (bp_last bp) 0); [|contradiction].
      rewrite <- IH3. f_equal; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dframe_finder cap off size r off' size' :
    0 <= cap -> size < 2^64 - 120 ->
    is_skippable_magic (le32 src off) = false ->
    dframe src cap off size r off' size' ->
    0 <= r <= cap /\
    (get_frame_content_size src off size = ZD_CONTENTSIZE_UNKNOWN \/ get_frame_content_size src off size = r) /\
    zd_is_error (find_frame_compressed_size src off size) = false /\
    off' = off + find_frame_compressed_size src off size /\
    size' = size - find_frame_compressed_size src off size.
  Proof.
    intros CAP SZ NSK (S9 & S3 & h & ip' & rem' & G & D & FCS & CK).
    set (hsz := frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX) in *.
    pose proof (get_frame_header_ok src SRC off hsz h G) as (T & _ & _ & _ & _ & _ & _ & _ & F0 & F1).
    assert (T0 : fh_type h = 0). { destruct T as [T|T]; [exact T|]. apply F1 in T. destruct T as (T & _). congruence. }
    destruct (F0 T0) as (_ & HS & _ & _). fold hsz in HS.
    assert (G' : get_frame_header src off size = FH_ok h).
    { apply (get_frame_header_mono src SRC off hsz size h G). unfold ZD_blockHeaderSize in *. lia. }
    apply dblocks_fsi in D. destruct D as (D1 & D2). specialize (D1 ltac:(lia)). destruct (D2 0) as (nb' & D3).
    split; [lia|].
    assert (FC : get_frame_content_size src off size = fh_fcs h).
    { unfold get_frame_content_size. rewrite G', T0. reflexivity. }
    split.
    { rewrite FC. destruct (Z.eq_dec (fh_fcs h) ZD_CONTENTSIZE_UNKNOWN) as [U|U]; [left; exact U|right]. symmetry. auto. }
    assert (FS : find_frame_size_info src off size =
                 if negb (fh_checksum h =? 0) && (rem' <? 4) then FSI_err (ZERR ZE_srcSize_wrong)
                 else FSI nb' ((if fh_checksum h =? 0 then ip' else ip' + 4) - off)
                          (if fh_fcs h =? ZD_CONTENTSIZE_UNKNOWN then nb' * fh_bsmax h else fh_fcs h)).
    { unfold find_frame_size_info. rewrite NSK, Bool.andb_false_r, G', HS, D3. reflexivity. }
    pose proof (fsi_blocks_done src SRC _ _ _ _ _ _ _ D3) as (B1 & B2 & B3 & _).
    unfold find_frame_compressed_size. rewrite FS.
    destruct (Z.eqb_spec (fh_checksum h) 0) as [C0|C0]; cbn [negb andb fsi_csize].
    - destruct CK as (-> & ->). rewrite zd_is_error_false_iff. unfold ZD_blockHeaderSize in *. lia.
    - destruct CK as (R4 & -> & ->). destruct (Z.ltb_spec rem' 4); [lia|]. cbn [fsi_csize].
      rewrite zd_is_error_false_iff. unfold ZD_blockHeaderSize in *. lia.
  Qed.

  Lemma dmulti_finder : forall off size cap tot r, dmulti src off size cap tot r ->
    size < 2^64 - 120 -> 0 <= tot -> 0 <= cap -> tot + cap < ZD_CONTENTSIZE_ERROR ->
    find_dsize src off size tot <> ZD_CONTENTSIZE_ERROR /\
    (find_dsize src off size tot = ZD_CONTENTSIZE_UNKNOWN \/ find_dsize src off size tot = r) /\
    tot <= r <= tot + cap.
  Proof.
    induction 1 as [off cap tot | off size cap tot r S5 SK E D IH | off size cap tot r fr off' size' S5 SK F D IH];
      intros SZ T0 C0 TC.
    - rewrite (find_dsize_eq src SRC) by exact SZ. cbn. unfold ZD_CONTENTSIZE_ERROR in *. repeat split; auto; lia.
    - rewrite (find_dsize_eq src SRC) by exact SZ.
      destruct (Z.ltb_spec size ZD_FRAMEHEADERSIZE_PREFIX); [lia|]. rewrite SK. cbv zeta. rewrite E.
      pose proof (read_skippable_frame_size_ok src SRC off size E SZ) as (_ & K).
      unfold ZD_SKIPPABLEHEADERSIZE in *. apply IH; lia.
    - rewrite (find_dsize_eq src SRC) by exact SZ.
      destruct (Z.ltb_spec size ZD_FRAMEHEADERSIZE_PREFIX); [lia|]. rewrite SK. cbv zeta.
      pose proof (dframe_finder cap off size fr off' size' C0 SZ SK F) as (R & FC & NE & -> & ->).
      pose proof (find_frame_compressed_size_ok src SRC off size SZ NE) as K. unfold ZD_SKIPPABLEHEADERSIZE in K.
      specialize (IH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). destruct IH as (IH1 & IH2 & IH3).
      destruct FC as [FC|FC]; rewrite FC.
      + unfold ZD_CONTENTSIZE_UNKNOWN, ZD_CONTENTSIZE_ERROR in *.
        destruct (Z.leb_spec (2^64 - 2) (2^64 - 1)); [|lia]. repeat split; auto; lia.
      + unfold ZD_CONTENTSIZE_ERROR in *.
        destruct (Z.leb_spec (2^64 - 2) fr); [lia|]. destruct (Z.leb_spec (2^64) (tot + fr)); [lia|].
        rewrite NE. repeat split; auto; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem decompress_ok_finder size cap r :
    size < 2^64 - 120 -> 0 <= cap < ZD_CONTENTSIZE_ERROR ->
    decompress_ok src size cap r ->
    find_decompressed_size src size <> ZD_CONTENTSIZE_ERROR /\
    (find_decompressed_size src size = ZD_CONTENTSIZE_UNKNOWN \/ find_decompressed_size src size = r) /\
    0 <= r <= cap.
  Proof.
    intros SZ C D. unfold decompress_ok in D. unfold find_decompressed_size.
    pose proof (dmulti_finder 0 size cap 0 r D SZ ltac:(lia) ltac:(lia) ltac:(lia)) as (A & B & R).
    repeat split; auto; lia.
  Qed.
End Decoder.
