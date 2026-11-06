(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record lit_hdr : Type := mkLH { lh_type : Z; lh_size : Z; lh_lit : Z; lh_csize : Z; lh_single : Z }.

Definition lit_encType (b0 : Z) : Z := b0 mod 4.           (* [comment removed for export] *)
Definition lit_lhlCode (b0 : Z) : Z := (b0 / 4) mod 4.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lit_hdr_compressed (ty lhl lhc b4 : Z) : lit_hdr :=
  if lhl <? 2 then mkLH ty 3 ((lhc / 16) mod 1024) ((lhc / 16384) mod 1024) (if lhl =? 0 then 1 else 0)
  else if lhl =? 2 then mkLH ty 4 ((lhc / 16) mod 16384) (lhc / 262144) 0
  else mkLH ty 5 ((lhc / 16) mod 262144) (lhc / 4194304 + b4 * 1024) 0.

(* [comment removed for export] *)
Definition lit_hdr_simple (ty lhl : Z) (src : list Z) (ip srcSize : Z) : option lit_hdr :=
  if (lhl =? 0) || (lhl =? 2) then Some (mkLH ty 1 (Znth ip src / 8) 0 0)
  else if lhl =? 1 then
    if (ty =? set_rle) && (srcSize <? 3) then None else Some (mkLH ty 2 (le16 src ip / 16) 0 0)
  else
    if srcSize <? (if ty =? set_rle then 4 else 3) then None else Some (mkLH ty 3 (le24 src ip / 16) 0 0).

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive lit_base : Type := LB_dst | LB_extra | LB_src.

(* [comment removed for export] *)
Record lit_place : Type := mkLP { lp_loc : Z; lp_base : lit_base; lp_buf : Z; lp_end : Z }.

(* [comment removed for export] *)
Definition alloc_lit_buffer (bsmax cap litSize ews : Z) (splitImmediately : bool) : lit_place :=
  if bsmax + WILDCOPY_OVERLENGTH + litSize + WILDCOPY_OVERLENGTH <? cap then
    mkLP ZSTD_in_dst LB_dst (bsmax + WILDCOPY_OVERLENGTH) (bsmax + WILDCOPY_OVERLENGTH + litSize)
  else if litSize <=? ZSTD_LITBUFFEREXTRASIZE then
    mkLP ZSTD_not_in_dst LB_extra 0 litSize
  else if splitImmediately then
    mkLP ZSTD_split LB_dst (ews - litSize + ZSTD_LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH) (ews - WILDCOPY_OVERLENGTH)
  else
    mkLP ZSTD_split LB_dst (ews - litSize) ews.

(* [comment removed for export] *)
Definition split_fixup (p : lit_place) : lit_place :=
  if lp_loc p =? ZSTD_split
  then mkLP ZSTD_split LB_dst (lp_buf p + ZSTD_LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH) (lp_end p - WILDCOPY_OVERLENGTH)
  else p.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive lit_action : Type :=
| LA_huf (h : lit_hdr) (p : lit_place)     (* [comment removed for export] *)
| LA_raw_copy (h : lit_hdr) (p : lit_place) (* [comment removed for export] *)
| LA_raw_ref (h : lit_hdr)                 (* [comment removed for export] *)
| LA_rle (h : lit_hdr) (p : lit_place)     (* [comment removed for export] *)
| LA_err (code : Z).                       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition decode_literals (src : list Z) (ip srcSize : Z) (litEntropy bsmax : Z) (dstNull : bool) (cap : Z) : lit_action :=
  if srcSize <? MIN_CBLOCK_SIZE then LA_err ZE_corruption_detected
  else
    let b0 := Znth ip src in
    let ty := lit_encType b0 in
    let lhl := lit_lhlCode b0 in
    let ews := Z.min bsmax cap in
    let common (h : lit_hdr) (k : unit -> lit_action) : lit_action :=
      if (0 <? lh_lit h) && dstNull then LA_err ZE_dstSize_tooSmall
      else if bsmax <? lh_lit h then LA_err ZE_corruption_detected
      else k tt in
    if (ty =? set_compressed) || (ty =? set_repeat) then
      if (ty =? set_repeat) && (litEntropy =? 0) then LA_err ZE_dictionary_corrupted
      else if srcSize <? 5 then LA_err ZE_corruption_detected
      else
        let h := lit_hdr_compressed ty lhl (le32 src ip) (Znth (ip + 4) src) in
        common h (fun _ =>
          if (lh_single h =? 0) && (lh_lit h <? MIN_LITERALS_FOR_4_STREAMS) then LA_err ZE_literals_headerWrong
          else if srcSize <? lh_csize h + lh_size h then LA_err ZE_corruption_detected
          else if ews <? lh_lit h then LA_err ZE_dstSize_tooSmall
          else LA_huf h (alloc_lit_buffer bsmax cap (lh_lit h) ews false))
    else
      match lit_hdr_simple ty lhl src ip srcSize with
      | None => LA_err ZE_corruption_detected
      | Some h =>
        common h (fun _ =>
          if ews <? lh_lit h then LA_err ZE_dstSize_tooSmall
          else
            let p := alloc_lit_buffer bsmax cap (lh_lit h) ews true in
            if ty =? set_rle then LA_rle h p
            else if srcSize <? lh_size h + lh_lit h + WILDCOPY_OVERLENGTH then
              (if srcSize <? lh_lit h + lh_size h then LA_err ZE_corruption_detected else LA_raw_copy h p)
            else LA_raw_ref h)
      end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Facts.
  Variable src : list Z.
  Hypothesis SRC : all_bytes src.

  Lemma lit_hdr_compressed_range ty lhl ip : 0 <= lhl <= 3 ->
    let h := lit_hdr_compressed ty lhl (le32 src ip) (Znth (ip + 4) src) in
    3 <= lh_size h <= 5 /\ 0 <= lh_lit h < 2^18 /\ 0 <= lh_csize h < 2^18 /\ 0 <= lh_single h <= 1 /\ lh_type h = ty.
  Proof.
    intros L. unfold lit_hdr_compressed.
    assert (R : 0 <= le32 src ip < 2^32).
    { unfold le32. pose proof (SRC ip). pose proof (SRC (ip + 1)). pose proof (SRC (ip + 2)). pose proof (SRC (ip + 3)). lia. }
    pose proof (SRC (ip + 4)) as B4. set (lhc := le32 src ip) in *.
    assert (Q1 : 0 <= lhc / 16) by (apply Z.div_pos; lia).
    destruct (Z.ltb_spec lhl 2); [|destruct (Z.eqb_spec lhl 2)]; cbn [lh_size lh_lit lh_csize lh_single lh_type].
    - pose proof (Z.mod_pos_bound (lhc / 16) 1024 ltac:(lia)). pose proof (Z.mod_pos_bound (lhc / 16384) 1024 ltac:(lia)).
      destruct (lhl =? 0); lia.
    - pose proof (Z.mod_pos_bound (lhc / 16) 16384 ltac:(lia)).
      assert (0 <= lhc / 262144 < 2^14) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]). lia.
    - pose proof (Z.mod_pos_bound (lhc / 16) 262144 ltac:(lia)).
      assert (0 <= lhc / 4194304 < 2^10) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]). lia.
  Qed.

  Lemma lit_hdr_simple_range ty lhl ip srcSize h : lit_hdr_simple ty lhl src ip srcSize = Some h ->
    1 <= lh_size h <= 3 /\ 0 <= lh_lit h < 2^20 /\ lh_csize h = 0 /\ lh_single h = 0 /\ lh_type h = ty /\
    (ty = set_rle -> lh_size h + 1 <= Z.max srcSize MIN_CBLOCK_SIZE) /\
    (ty <> set_rle -> lh_size h <= Z.max srcSize MIN_CBLOCK_SIZE).
  Proof.
    unfold lit_hdr_simple, set_rle, MIN_CBLOCK_SIZE.
    pose proof (SRC ip) as B0.
    assert (R16 : 0 <= le16 src ip < 2^16) by (unfold le16; pose proof (SRC (ip + 1)); lia).
    assert (R24 : 0 <= le24 src ip < 2^24) by (unfold le24; pose proof (SRC (ip + 1)); pose proof (SRC (ip + 2)); lia).
    destruct ((lhl =? 0) || (lhl =? 2)).
    { intros E. injection E as <-. cbn [lh_size lh_lit lh_csize lh_single lh_type].
      assert (0 <= Znth ip src / 8 < 32) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]). lia. }
    destruct (lhl =? 1).
    { destruct (Z.eqb_spec ty 1); destruct (Z.ltb_spec srcSize 3); cbn [andb]; try discriminate;
        intros E; injection E as <-; cbn [lh_size lh_lit lh_csize lh_single lh_type];
        assert (0 <= le16 src ip / 16 < 2^12) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]); lia. }
    destruct (Z.eqb_spec ty 1); [destruct (Z.ltb_spec srcSize 4)|destruct (Z.ltb_spec srcSize 3)]; try discriminate;
      intros E; injection E as <-; cbn [lh_size lh_lit lh_csize lh_single lh_type];
      assert (0 <= le24 src ip / 16 < 2^20) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]); lia.
  Qed.
End Facts.

(* [comment removed for export] *)
Lemma alloc_lit_buffer_regions bsmax cap litSize ews imm :
  0 <= litSize <= ews -> ews = Z.min bsmax cap -> 0 <= bsmax <= ZSTD_BLOCKSIZE_MAX ->
  let p := alloc_lit_buffer bsmax cap litSize ews imm in
  match lp_base p with
  | LB_dst =>
      (lp_loc p = ZSTD_in_dst /\ lp_buf p = bsmax + WILDCOPY_OVERLENGTH /\ lp_end p = lp_buf p + litSize /\
         lp_end p + WILDCOPY_OVERLENGTH < cap) \/
      (lp_loc p = ZSTD_split /\ ZSTD_LITBUFFEREXTRASIZE < litSize /\ 0 <= lp_buf p /\
         (if imm then lp_end p = lp_buf p + litSize - ZSTD_LITBUFFEREXTRASIZE /\ lp_end p + WILDCOPY_OVERLENGTH = ews
          else lp_end p = lp_buf p + litSize /\ lp_end p = ews) /\ ews <= cap)
  | LB_extra => lp_loc p = ZSTD_not_in_dst /\ lp_buf p = 0 /\ lp_end p = litSize /\ litSize <= ZSTD_LITBUFFEREXTRASIZE
  | LB_src => False
  end.
Proof.
  intros HL HE HB p. subst p. unfold alloc_lit_buffer, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX in *.
  destruct (Z.ltb_spec (bsmax + 32 + litSize + 32) cap); cbn [lp_base lp_loc lp_buf lp_end].
  { left. repeat split; lia. }
  destruct (Z.leb_spec litSize 65536); cbn [lp_base lp_loc lp_buf lp_end].
  { repeat split; lia. }
  destruct imm; cbn [lp_base lp_loc lp_buf lp_end]; right; repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma split_fixup_shape bsmax cap litSize ews :
  0 <= litSize <= ews -> ews = Z.min bsmax cap ->
  lp_loc (alloc_lit_buffer bsmax cap litSize ews false) = ZSTD_split ->
  split_fixup (alloc_lit_buffer bsmax cap litSize ews false) = alloc_lit_buffer bsmax cap litSize ews true.
Proof.
  intros HL HE. unfold alloc_lit_buffer, split_fixup, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE, ZSTD_split, ZSTD_in_dst, ZSTD_not_in_dst.
  destruct (Z.ltb_spec (bsmax + 32 + litSize + 32) cap); cbn [lp_loc]; [discriminate|].
  destruct (Z.leb_spec litSize 65536); cbn [lp_loc lp_buf lp_end]; [discriminate|].
  intros _. cbn. f_equal; lia.
Qed.
