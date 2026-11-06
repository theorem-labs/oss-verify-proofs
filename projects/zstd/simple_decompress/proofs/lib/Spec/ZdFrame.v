(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ZE_GENERIC : Z := 1.
Definition ZE_prefix_unknown : Z := 10.
Definition ZE_frameParameter_unsupported : Z := 14.
Definition ZE_frameParameter_windowTooLarge : Z := 16.
Definition ZE_corruption_detected : Z := 20.
Definition ZE_checksum_wrong : Z := 22.
Definition ZE_literals_headerWrong : Z := 24.
Definition ZE_dictionary_corrupted : Z := 30.
Definition ZE_tableLog_tooLarge : Z := 44.
Definition ZE_maxSymbolValue_tooLarge : Z := 46.
Definition ZE_maxSymbolValue_tooSmall : Z := 48.
Definition ZE_dstSize_tooSmall : Z := 70.
Definition ZE_srcSize_wrong : Z := 72.
Definition ZE_dstBuffer_null : Z := 74.
Definition ZE_maxCode : Z := 120.

(* [comment removed for export] *)
Definition ZERR (code : Z) : Z := 2^64 - code.
(* [comment removed for export] *)
Definition zd_is_error (r : Z) : bool := 2^64 - ZE_maxCode <? r.
(* [comment removed for export] *)
Definition zd_error_code (r : Z) : Z := if zd_is_error r then 2^64 - r else 0.

Definition ZD_CONTENTSIZE_UNKNOWN : Z := 2^64 - 1.
Definition ZD_CONTENTSIZE_ERROR : Z := 2^64 - 2.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ZD_MAGICNUMBER : Z := 4247762216.            (* [comment removed for export] *)
Definition ZD_MAGIC_SKIPPABLE_START : Z := 407710288.   (* [comment removed for export] *)
Definition ZD_FRAMEIDSIZE : Z := 4.
Definition ZD_SKIPPABLEHEADERSIZE : Z := 8.
Definition ZD_FRAMEHEADERSIZE_PREFIX : Z := 5.          (* [comment removed for export] *)
Definition ZD_FRAMEHEADERSIZE_MIN : Z := 6.
Definition ZD_FRAMEHEADERSIZE_MAX : Z := 18.
Definition ZD_blockHeaderSize : Z := 3.
Definition ZD_WINDOWLOG_ABSOLUTEMIN : Z := 10.
Definition ZD_WINDOWLOG_MAX : Z := 31.
Definition ZD_BLOCKSIZE_MAX : Z := 131072.              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bt_raw : Z := 0.
Definition bt_rle : Z := 1.
Definition bt_compressed : Z := 2.
Definition bt_reserved : Z := 3.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition le16 (b : list Z) (p : Z) : Z := Znth p b + 2^8 * Znth (p + 1) b.
Definition le24 (b : list Z) (p : Z) : Z := Znth p b + 2^8 * Znth (p + 1) b + 2^16 * Znth (p + 2) b.
Definition le32 (b : list Z) (p : Z) : Z :=
  Znth p b + 2^8 * Znth (p + 1) b + 2^16 * Znth (p + 2) b + 2^24 * Znth (p + 3) b.
Definition le64 (b : list Z) (p : Z) : Z := le32 b p + 2^32 * le32 b (p + 4).

(* [comment removed for export] *)
Definition is_skippable_magic (magic : Z) : bool := magic / 16 =? 25481893.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition did_fieldSize (c : Z) : Z := if c =? 0 then 0 else if c =? 1 then 1 else if c =? 2 then 2 else 4.
Definition fcs_fieldSize (c : Z) : Z := if c =? 0 then 0 else if c =? 1 then 2 else if c =? 2 then 4 else 8.

(* [comment removed for export] *)
Definition fhd_dictIDSizeCode (fhd : Z) : Z := fhd mod 4.          (* [comment removed for export] *)
Definition fhd_checksumFlag (fhd : Z) : Z := (fhd / 4) mod 2.      (* [comment removed for export] *)
Definition fhd_reserved (fhd : Z) : Z := (fhd / 8) mod 2.          (* [comment removed for export] *)
Definition fhd_singleSegment (fhd : Z) : Z := (fhd / 32) mod 2.    (* [comment removed for export] *)
Definition fhd_fcsID (fhd : Z) : Z := fhd / 64.                    (* [comment removed for export] *)

Definition fhd_header_size (fhd : Z) : Z :=
  ZD_FRAMEHEADERSIZE_PREFIX
  + (if fhd_singleSegment fhd =? 0 then 1 else 0)
  + did_fieldSize (fhd_dictIDSizeCode fhd) + fcs_fieldSize (fhd_fcsID fhd)
  + (if (fhd_singleSegment fhd =? 1) && (fhd_fcsID fhd =? 0) then 1 else 0).

(* [comment removed for export] *)
Definition frame_header_size (src : list Z) (off size : Z) : Z :=
  if size <? ZD_FRAMEHEADERSIZE_PREFIX then ZERR ZE_srcSize_wrong
  else fhd_header_size (Znth (off + 4) src).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record frame_header : Type := mkFH {
  fh_fcs : Z;        (* [comment removed for export] *)
  fh_window : Z;     (* [comment removed for export] *)
  fh_bsmax : Z;      (* [comment removed for export] *)
  fh_type : Z;       (* [comment removed for export] *)
  fh_hsize : Z;      (* [comment removed for export] *)
  fh_dictID : Z;     (* [comment removed for export] *)
  fh_checksum : Z    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Inductive fh_result : Type := FH_ok (h : frame_header) | FH_ret (v : Z).
Definition fh_retval (r : fh_result) : Z := match r with FH_ok _ => 0 | FH_ret v => v end.

(* [comment removed for export] *)
Definition hbyte (magic : Z) (src : list Z) (off n i : Z) : Z :=
  if i <? n then Znth (off + i) src else (magic / 2^(8 * i)) mod 256.
Definition hbuf32 (magic : Z) (src : list Z) (off n : Z) : Z :=
  hbyte magic src off n 0 + 2^8 * hbyte magic src off n 1 + 2^16 * hbyte magic src off n 2
  + 2^24 * hbyte magic src off n 3.

(* [comment removed for export] *)
Definition wl_windowLog (wlByte : Z) : Z := wlByte / 8 + ZD_WINDOWLOG_ABSOLUTEMIN.
Definition wl_windowSize (wlByte : Z) : Z :=
  2^(wl_windowLog wlByte) + (2^(wl_windowLog wlByte) / 8) * (wlByte mod 8).

(* [comment removed for export] *)
Definition fh_read_dictID (src : list Z) (pos code : Z) : Z :=
  if code =? 0 then 0 else if code =? 1 then Znth pos src else if code =? 2 then le16 src pos else le32 src pos.
(* [comment removed for export] *)
Definition fh_read_fcs (src : list Z) (pos fcsID singleSegment : Z) : Z :=
  if fcsID =? 0 then (if singleSegment =? 0 then ZD_CONTENTSIZE_UNKNOWN else Znth pos src)
  else if fcsID =? 1 then le16 src pos + 256
  else if fcsID =? 2 then le32 src pos
  else le64 src pos.

(* [comment removed for export] *)
Definition get_frame_header_zstd (src : list Z) (off size : Z) : fh_result :=
  let fhsize := frame_header_size src off size in
  if size <? fhsize then FH_ret fhsize
  else
    let fhd := Znth (off + 4) src in
    let ss := fhd_singleSegment fhd in
    if negb (fhd_reserved fhd =? 0) then FH_ret (ZERR ZE_frameParameter_unsupported)
    else
      let wlByte := Znth (off + 5) src in
      if (ss =? 0) && (ZD_WINDOWLOG_MAX <? wl_windowLog wlByte) then FH_ret (ZERR ZE_frameParameter_windowTooLarge)
      else
        let pos1 := off + 5 + (if ss =? 0 then 1 else 0) in
        let dcode := fhd_dictIDSizeCode fhd in
        let dictID := fh_read_dictID src pos1 dcode in
        let pos2 := pos1 + did_fieldSize dcode in
        let fcs := fh_read_fcs src pos2 (fhd_fcsID fhd) ss in
        let windowSize := if ss =? 0 then wl_windowSize wlByte else fcs in
        FH_ok (mkFH fcs windowSize (Z.min windowSize ZD_BLOCKSIZE_MAX) 0 fhsize dictID (fhd_checksumFlag fhd)).

Definition get_frame_header (src : list Z) (off size : Z) : fh_result :=
  if size <? ZD_FRAMEHEADERSIZE_PREFIX then
    (* [comment removed for export] *)
    if size =? 0 then FH_ret ZD_FRAMEHEADERSIZE_PREFIX
    else
      let n := Z.min 4 size in
      if hbuf32 ZD_MAGICNUMBER src off n =? ZD_MAGICNUMBER then FH_ret ZD_FRAMEHEADERSIZE_PREFIX
      else if is_skippable_magic (hbuf32 ZD_MAGIC_SKIPPABLE_START src off n) then FH_ret ZD_FRAMEHEADERSIZE_PREFIX
      else FH_ret (ZERR ZE_prefix_unknown)
  else
    let magic := le32 src off in
    if magic =? ZD_MAGICNUMBER then get_frame_header_zstd src off size
    else if is_skippable_magic magic then
      if size <? ZD_SKIPPABLEHEADERSIZE then FH_ret ZD_SKIPPABLEHEADERSIZE
      else FH_ok (mkFH (le32 src (off + 4)) 0 0 1 ZD_SKIPPABLEHEADERSIZE (magic - ZD_MAGIC_SKIPPABLE_START) 0)
    else FH_ret (ZERR ZE_prefix_unknown).

(* [comment removed for export] *)
Definition get_frame_content_size (src : list Z) (off size : Z) : Z :=
  match get_frame_header src off size with
  | FH_ret _ => ZD_CONTENTSIZE_ERROR
  | FH_ok h => if fh_type h =? 1 then 0 else fh_fcs h
  end.

(* [comment removed for export] *)
Definition decode_frame_header (src : list Z) (off headerSize : Z) : Z :=
  match get_frame_header src off headerSize with
  | FH_ret v => if zd_is_error v then v else ZERR ZE_srcSize_wrong
  | FH_ok _ => 0
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition read_skippable_frame_size (src : list Z) (off size : Z) : Z :=
  if size <? ZD_SKIPPABLEHEADERSIZE then ZERR ZE_srcSize_wrong
  else
    let sizeU32 := le32 src (off + 4) in
    if (sizeU32 + ZD_SKIPPABLEHEADERSIZE) mod 2^32 <? sizeU32 then ZERR ZE_frameParameter_unsupported
    else
      let skippableSize := ZD_SKIPPABLEHEADERSIZE + sizeU32 in
      if size <? skippableSize then ZERR ZE_srcSize_wrong else skippableSize.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record block_props : Type := mkBP { bp_type : Z; bp_last : Z; bp_orig : Z }.

Definition cblock_props (hdr : Z) : block_props := mkBP ((hdr / 2) mod 4) (hdr mod 2) (hdr / 8).

(* [comment removed for export] *)
Definition get_cblock_size (src : list Z) (ip size : Z) : option (Z * block_props) :=
  if size <? ZD_blockHeaderSize then None
  else
    let bp := cblock_props (le24 src ip) in
    Some (if bp_type bp =? bt_rle then 1
          else if bp_type bp =? bt_reserved then ZERR ZE_corruption_detected
          else bp_orig bp, bp).

Definition cblock_ret (r : option (Z * block_props)) : Z :=
  match r with None => ZERR ZE_srcSize_wrong | Some (v, _) => v end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive fsi_result : Type := FSI_err (v : Z) | FSI (nbBlocks compressedSize decompressedBound : Z).
Definition fsi_csize (r : fsi_result) : Z := match r with FSI_err v => v | FSI _ c _ => c end.
Definition fsi_bound (r : fsi_result) : Z := match r with FSI_err _ => ZD_CONTENTSIZE_ERROR | FSI _ _ b => b end.

(* [comment removed for export] *)
Inductive fsi_loop_result : Type := FL_err (v : Z) | FL_done (ip rem nb : Z).

Fixpoint fsi_blocks_fuel (fuel : nat) (src : list Z) (ip rem nb : Z) : fsi_loop_result :=
  match fuel with
  | O => FL_err (ZERR ZE_srcSize_wrong)     (* [comment removed for export] *)
  | S f =>
    match get_cblock_size src ip rem with
    | None => FL_err (ZERR ZE_srcSize_wrong)
    | Some (cbs, bp) =>
      if zd_is_error cbs then FL_err cbs
      else if rem <? ZD_blockHeaderSize + cbs then FL_err (ZERR ZE_srcSize_wrong)
      else
        let ip' := ip + (ZD_blockHeaderSize + cbs) in
        let rem' := rem - (ZD_blockHeaderSize + cbs) in
        if bp_last bp =? 0 then fsi_blocks_fuel f src ip' rem' (nb + 1)
        else FL_done ip' rem' (nb + 1)
    end
  end.

Definition fsi_blocks (src : list Z) (ip rem nb : Z) : fsi_loop_result :=
  fsi_blocks_fuel (S (Z.to_nat rem)) src ip rem nb.

Definition find_frame_size_info (src : list Z) (off size : Z) : fsi_result :=
  if (ZD_SKIPPABLEHEADERSIZE <=? size) && is_skippable_magic (le32 src off) then
    FSI 0 (read_skippable_frame_size src off size) 0
  else
    match get_frame_header src off size with
    | FH_ret v => if zd_is_error v then FSI_err v else FSI_err (ZERR ZE_srcSize_wrong)
    | FH_ok h =>
      match fsi_blocks src (off + fh_hsize h) (size - fh_hsize h) 0 with
      | FL_err v => FSI_err v
      | FL_done ip rem nb =>
        if negb (fh_checksum h =? 0) && (rem <? 4) then FSI_err (ZERR ZE_srcSize_wrong)
        else
          let ip' := if fh_checksum h =? 0 then ip else ip + 4 in
          FSI nb (ip' - off)
              (if fh_fcs h =? ZD_CONTENTSIZE_UNKNOWN then nb * fh_bsmax h else fh_fcs h)
      end
    end.

Definition find_frame_compressed_size (src : list Z) (off size : Z) : Z :=
  fsi_csize (find_frame_size_info src off size).

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint find_dsize_fuel (fuel : nat) (src : list Z) (off size total : Z) : Z :=
  match fuel with
  | O => ZD_CONTENTSIZE_ERROR          (* [comment removed for export] *)
  | S f =>
    if size <? ZD_FRAMEHEADERSIZE_PREFIX then (if size =? 0 then total else ZD_CONTENTSIZE_ERROR)
    else if is_skippable_magic (le32 src off) then
      let sk := read_skippable_frame_size src off size in
      if zd_is_error sk then ZD_CONTENTSIZE_ERROR
      else find_dsize_fuel f src (off + sk) (size - sk) total
    else
      let fcs := get_frame_content_size src off size in
      if ZD_CONTENTSIZE_ERROR <=? fcs then fcs
      else if 2^64 <=? total + fcs then ZD_CONTENTSIZE_ERROR        (* [comment removed for export] *)
      else
        let fsz := find_frame_compressed_size src off size in
        if zd_is_error fsz then ZD_CONTENTSIZE_ERROR
        else find_dsize_fuel f src (off + fsz) (size - fsz) (total + fcs)
  end.

Definition find_dsize (src : list Z) (off size total : Z) : Z :=
  find_dsize_fuel (S (Z.to_nat size)) src off size total.

(* [comment removed for export] *)
Definition find_decompressed_size (src : list Z) (size : Z) : Z := find_dsize src 0 size 0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition block_result (room cbs : Z) (bp : block_props) (v : Z) : Prop :=
  if bp_type bp =? bt_raw then v = cbs /\ cbs <= room
  else if bp_type bp =? bt_rle then v = bp_orig bp /\ bp_orig bp <= room
  else 0 <= v <= room.

(* [comment removed for export] *)
Inductive dblocks (src : list Z) (cap : Z) : Z -> Z -> Z -> Z -> Z -> Z -> Prop :=
| DB_last : forall ip rem o cbs bp v,
    get_cblock_size src ip rem = Some (cbs, bp) -> zd_is_error cbs = false ->
    cbs <= rem - ZD_blockHeaderSize ->
    block_result (cap - o) cbs bp v ->
    bp_last bp <> 0 ->
    dblocks src cap ip rem o (ip + ZD_blockHeaderSize + cbs) (rem - ZD_blockHeaderSize - cbs) (o + v)
| DB_more : forall ip rem o cbs bp v ip' rem' o',
    get_cblock_size src ip rem = Some (cbs, bp) -> zd_is_error cbs = false ->
    cbs <= rem - ZD_blockHeaderSize ->
    block_result (cap - o) cbs bp v ->
    bp_last bp = 0 ->
    dblocks src cap (ip + ZD_blockHeaderSize + cbs) (rem - ZD_blockHeaderSize - cbs) (o + v) ip' rem' o' ->
    dblocks src cap ip rem o ip' rem' o'.

(* [comment removed for export] *)
Definition dframe (src : list Z) (cap off size r off' size' : Z) : Prop :=
  ZD_FRAMEHEADERSIZE_MIN + ZD_blockHeaderSize <= size /\
  let hsz := frame_header_size src off ZD_FRAMEHEADERSIZE_PREFIX in
  hsz + ZD_blockHeaderSize <= size /\
  exists h ip' rem',
    get_frame_header src off hsz = FH_ok h /\
    dblocks src cap (off + hsz) (size - hsz) 0 ip' rem' r /\
    (fh_fcs h <> ZD_CONTENTSIZE_UNKNOWN -> r = fh_fcs h) /\
    (if fh_checksum h =? 0 then off' = ip' /\ size' = rem'
     else 4 <= rem' /\ off' = ip' + 4 /\ size' = rem' - 4).

(* [comment removed for export] *)
Inductive dmulti (src : list Z) : Z -> Z -> Z -> Z -> Z -> Prop :=
| DM_end : forall off cap tot,
    dmulti src off 0 cap tot tot
| DM_skip : forall off size cap tot r,
    ZD_FRAMEHEADERSIZE_PREFIX <= size ->
    is_skippable_magic (le32 src off) = true ->
    zd_is_error (read_skippable_frame_size src off size) = false ->
    dmulti src (off + read_skippable_frame_size src off size) (size - read_skippable_frame_size src off size) cap tot r ->
    dmulti src off size cap tot r
| DM_frame : forall off size cap tot r fr off' size',
    ZD_FRAMEHEADERSIZE_PREFIX <= size ->
    is_skippable_magic (le32 src off) = false ->
    dframe src cap off size fr off' size' ->
    dmulti src off' size' (cap - fr) (tot + fr) r ->
    dmulti src off size cap tot r.

(* [comment removed for export] *)
Definition decompress_ok (src : list Z) (size cap r : Z) : Prop := dmulti src 0 size cap 0 r.
