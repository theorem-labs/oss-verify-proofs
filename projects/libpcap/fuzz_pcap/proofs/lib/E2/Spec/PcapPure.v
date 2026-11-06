(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import String.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Fmt PcapPrelim PcapTypes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition linktype_to_dlt (lt : Z) : Z :=
  if lt =? 100 then 11
  else if lt =? 101 then 12
  else if lt =? 102 then 15
  else if lt =? 103 then 16
  else if lt =? 106 then 19
  else lt.

Definition DLT_EN10MB : Z := 1.
Definition DLT_LINUX_SLL : Z := 113.
Definition DLT_PFLOG : Z := 117.
Definition DLT_USB_LINUX : Z := 189.
Definition DLT_USB_LINUX_MMAPPED : Z := 220.
Definition DLT_DBUS : Z := 231.
Definition DLT_NFLOG : Z := 239.
Definition DLT_USBPCAP : Z := 249.
Definition DLT_LINUX_SLL2 : Z := 276.
Definition DLT_EBHSCR : Z := 279.
Definition MAXIMUM_SNAPLEN : Z := 262144.

(* [comment removed for export] *)
Definition max_snaplen_for_dlt (dlt : Z) : Z :=
  if dlt =? DLT_DBUS then 134217728          (* [comment removed for export] *)
  else if dlt =? DLT_EBHSCR then 8388608     (* [comment removed for export] *)
  else if dlt =? DLT_USBPCAP then 1048576    (* [comment removed for export] *)
  else MAXIMUM_SNAPLEN.

(* [comment removed for export] *)
Definition pcapint_adjust_snapshot (linktype snaplen : Z) : Z :=
  if (snaplen =? 0) || (INT_MAX <? snaplen) then max_snaplen_for_dlt linktype else snaplen.

(* [comment removed for export] *)
Definition PCAP_ERRBUF_SIZE : Z := 256.

Module Msg.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
#[local] Abbreviation snp := (snprintf PCAP_ERRBUF_SIZE).
(* [comment removed for export] *)
Definition trunc_file_header (want got : Z) : list Z :=      (* [comment removed for export] *)
  snp "truncated dump file; tried to read %zu file header bytes, only got %zu" [AInt want; AInt got].
Definition unknown_file_format : list Z := snp "unknown file format" [].          (* [comment removed for export] *)
Definition stats_not_avail : list Z := snp "Statistics aren't available from savefiles" [].  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition unsupported_pcap_version (maj min : Z) : list Z :=                     (* [comment removed for export] *)
  snp "unsupported pcap savefile version %u.%u" [AInt maj; AInt min].
Definition reserved_not_zero (v : Z) : list Z :=                                  (* [comment removed for export] *)
  snp "savefile linktype reserved field not zero (0x%08x)" [AInt v].
Definition unknown_tstamp_resolution (prec : Z) : list Z :=                       (* [comment removed for export] *)
  snp "unknown time stamp resolution %u" [AInt prec].
Definition out_of_memory : list Z := snp "out of memory" [].                      (* [comment removed for export] *)
Definition trunc_header (want got : Z) : list Z :=                                (* [comment removed for export] *)
  snp "truncated dump file; tried to read %zu header bytes, only got %zu" [AInt want; AInt got].
Definition invalid_caplen_snaplen (caplen snapshot : Z) : list Z :=               (* [comment removed for export] *)
  snp "invalid packet capture length %u, bigger than snaplen of %d" [AInt caplen; AInt snapshot].
Definition invalid_caplen_maximum (caplen mx : Z) : list Z :=                     (* [comment removed for export] *)
  snp "invalid packet capture length %u, bigger than maximum of %u" [AInt caplen; AInt mx].
Definition trunc_captured_d (want got : Z) : list Z :=                            (* [comment removed for export] *)
  snp "truncated dump file; tried to read %d captured bytes, only got %zu" [AInt want; AInt got].
Definition trunc_captured_u (want got : Z) : list Z :=                            (* [comment removed for export] *)
  snp "truncated dump file; tried to read %u captured bytes, only got %zu" [AInt want; AInt got].
(* [comment removed for export] *)
Definition trunc_pcapng (want got : Z) : list Z :=                                (* [comment removed for export] *)
  snp "truncated pcapng dump file; tried to read %zu bytes, only got %zu" [AInt want; AInt got].
Definition block_length_lt (tl : Z) : list Z :=                                   (* [comment removed for export] *)
  snp "block in pcapng dump file has a length of %u < %zu" [AInt tl; AInt 12].
Definition block_length_not_mult4 (tl : Z) : list Z :=                            (* [comment removed for export] *)
  snp "block in pcapng dump file has a length of %u that is not a multiple of 4" [AInt tl].
Definition block_size_gt_max (tl mx : Z) : list Z :=                              (* [comment removed for export] *)
  snp "pcapng block size %u > maximum %u" [AInt tl; AInt mx].
Definition header_trailer_mismatch (h t : Z) : list Z :=                          (* [comment removed for export] *)
  snp "block total length in header %u and trailer %u don't match" [AInt h; AInt t].
Definition block_too_short (bt : Z) : list Z :=                                   (* [comment removed for export] *)
  snp "block of type %u in pcapng dump file is too short" [AInt bt].
Definition endofopt_len (l : Z) : list Z :=                                       (* [comment removed for export] *)
  snp "Interface Description Block has opt_endofopt option with length %u != 0" [AInt l].
Definition tsresol_len (l : Z) : list Z :=                                        (* [comment removed for export] *)
  snp "Interface Description Block has if_tsresol option with length %u != 1" [AInt l].
Definition tsresol_dup : list Z :=                                                (* [comment removed for export] *)
  snp "Interface Description Block has more than one if_tsresol option" [].
Definition tsresol_bin_high (s : Z) : list Z :=                                   (* [comment removed for export] *)
  snp "Interface Description Block if_tsresol option resolution 2^-%u is too high" [AInt s].
Definition tsresol_dec_high (s : Z) : list Z :=                                   (* [comment removed for export] *)
  snp "Interface Description Block if_tsresol option resolution 10^-%u is too high" [AInt s].
Definition tsoffset_len (l : Z) : list Z :=                                       (* [comment removed for export] *)
  snp "Interface Description Block has if_tsoffset option with length %u != 8" [AInt l].
Definition tsoffset_dup : list Z :=                                               (* [comment removed for export] *)
  snp "Interface Description Block has more than one if_tsoffset option" [].
Definition too_many_interfaces (n : Z) : list Z :=                                (* [comment removed for export] *)
  snp "more than %u interfaces in the file" [AInt n].
Definition oom_interfaces (n : Z) : list Z :=                                     (* [comment removed for export] *)
  snp "out of memory for per-interface information (%u interfaces)" [AInt n].
Definition shb_invalid_length (tl : Z) : list Z :=                                (* [comment removed for export] *)
  snp "Section Header Block in pcapng dump file has invalid length %zu < _%u_ < %u (BT_SHB_INSANE_MAX)"
      [AInt 28; AInt tl; AInt 1048576].
Definition unsupported_pcapng_version (maj min : Z) : list Z :=                   (* [comment removed for export] *)
  snp "unsupported pcapng savefile version %u.%u" [AInt maj; AInt min].
Definition no_idb : list Z :=                                                     (* [comment removed for export] *)
  snp "the capture file has no Interface Description Blocks" [].
Definition packet_before_idb : list Z :=                                         (* [comment removed for export] *)
  snp "the capture file has a packet block before any Interface Description Blocks" [].
Definition iface_type_differs (lt : Z) : list Z :=                                (* [comment removed for export] *)
  snp "an interface has a type %u different from the type of the first interface" [AInt lt].
Definition iface_snaplen_differs (sl : Z) : list Z :=                             (* [comment removed for export] *)
  snp "an interface has a snapshot length %u different from the snapshot length of the first interface" [AInt sl].
Definition sections_byte_order : list Z :=                                        (* [comment removed for export] *)
  snp "the file has sections with different byte orders" [].
Definition bad_byte_order_magic : list Z :=                                       (* [comment removed for export] *)
  snp "the file has a section with a bad byte order magic field" [].
Definition unknown_major (v : Z) : list Z :=                                      (* [comment removed for export] *)
  snp "unknown pcapng savefile major version number %u" [AInt v].
Definition no_idb_for_interface (i : Z) : list Z :=                               (* [comment removed for export] *)
  snp "a packet arrived on interface %u, but there's no Interface Description Block for that interface" [AInt i].
End Msg.

(* [comment removed for export] *)
Definition fmt_errmsg (f : string) (args : list farg) (errnum : Z) : list Z :=
  let m := snprintf PCAP_ERRBUF_SIZE f args in
  let msglen := zlength m in
  if PCAP_ERRBUF_SIZE <? msglen + 3 then m
  else m ++ str ": " ++ snprintf (PCAP_ERRBUF_SIZE - msglen - 2) "%s" [AStr (snd (strerror_r errnum PCAP_ERRBUF_SIZE))].

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition swap_pflog_header (hdr : pkthdr) (d : list Z) : list Z :=
  let caplen := h_caplen hdr in
  let length := h_len hdr in
  if (caplen <? 48) || (length <? 48) then d else
  let pfloghdr_length := get_u8 d 0 in
  if pfloghdr_length <? 48 then d else
  let d := swap_field 4 44 d in                          (* [comment removed for export] *)
  if (caplen <? 52) || (length <? 52) then d else
  if pfloghdr_length <? 52 then d else
  let d := swap_field 4 48 d in                          (* [comment removed for export] *)
  if (caplen <? 56) || (length <? 56) then d else
  if pfloghdr_length <? 56 then d else
  let d := swap_field 4 52 d in                          (* [comment removed for export] *)
  if (caplen <? 60) || (length <? 60) then d else
  if pfloghdr_length <? 60 then d else
  swap_field 4 56 d.                                     (* [comment removed for export] *)

Definition LINUX_SLL_P_CAN : Z := 12.
Definition LINUX_SLL_P_CANFD : Z := 13.
Definition LINUX_SLL_P_CANXL : Z := 14.

(* [comment removed for export] *)
Definition swap_socketcan_header (protocol caplen length base : Z) (d : list Z) : list Z :=
  if (protocol =? LINUX_SLL_P_CAN) || (protocol =? LINUX_SLL_P_CANFD) then
    if (caplen <? 4) || (length <? 4) then d
    else swap_field 4 base d                             (* [comment removed for export] *)
  else if protocol =? LINUX_SLL_P_CANXL then
    if (caplen <? 4) || (length <? 4) then d else
    let d := swap_field 4 base d in                      (* [comment removed for export] *)
    if (caplen <? 8) || (length <? 8) then d else
    let d := swap_field 2 (base + 6) d in                (* [comment removed for export] *)
    if (caplen <? 12) || (length <? 12) then d else
    swap_field 4 (base + 8) d                            (* [comment removed for export] *)
  else d.

(* [comment removed for export] *)
Definition swap_linux_sll_socketcan_header (hdr : pkthdr) (d : list Z) : list Z :=
  let caplen := h_caplen hdr in
  let length := h_len hdr in
  if (caplen <? 16) || (length <? 16) then d
  else swap_socketcan_header (get_be16 d 14) (caplen - 16) (length - 16) 16 d.

(* [comment removed for export] *)
Definition swap_linux_sll2_socketcan_header (hdr : pkthdr) (d : list Z) : list Z :=
  let caplen := h_caplen hdr in
  let length := h_len hdr in
  if (caplen <? 20) || (length <? 20) then d
  else swap_socketcan_header (get_be16 d 0) (caplen - 20) (length - 20) 20 d.

Definition URB_ISOCHRONOUS : Z := 0.
Definition URB_COMPLETE : Z := 67.  (* [comment removed for export] *)
Definition URB_TRANSFER_IN : Z := 128.
Definition USB_MAXDESC : Z := 128.

(* [comment removed for export] *)
Fixpoint swap_usb_isodescs (fuel : nat) (ndesc caplen : Z) (i desc offset : Z) (d : list Z) : list Z :=
  match fuel with
  | O => d
  | S fuel' =>
    if i <? ndesc then
      let offset := offset + 4 in                        (* [comment removed for export] *)
      if caplen <? offset then d else
      let d := swap_field 4 desc d in
      let offset := offset + 4 in                        (* [comment removed for export] *)
      if caplen <? offset then d else
      let d := swap_field 4 (desc + 4) d in
      let offset := offset + 4 in                        (* [comment removed for export] *)
      if caplen <? offset then d else
      let d := swap_field 4 (desc + 8) d in
      let offset := offset + 4 in                        (* [comment removed for export] *)
      swap_usb_isodescs fuel' ndesc caplen (i + 1) (desc + 16) offset d
    else d
  end.

(* [comment removed for export] *)
Definition swap_linux_usb_header (hdr : pkthdr) (d : list Z) (header_len_64_bytes : bool) : list Z :=
  let caplen := h_caplen hdr in
  let offset := 8 in
  if caplen <? offset then d else
  let d := swap_field 8 0 d in                           (* [comment removed for export] *)
  let offset := offset + 4 + 2 in
  if caplen <? offset then d else
  let d := swap_field 2 12 d in                          (* [comment removed for export] *)
  let offset := offset + 2 + 8 in
  if caplen <? offset then d else
  let d := swap_field 8 16 d in                          (* [comment removed for export] *)
  let offset := offset + 4 in
  if caplen <? offset then d else
  let d := swap_field 4 24 d in                          (* [comment removed for export] *)
  let offset := offset + 4 in
  if caplen <? offset then d else
  let d := swap_field 4 28 d in                          (* [comment removed for export] *)
  let offset := offset + 4 in
  if caplen <? offset then d else
  let d := swap_field 4 32 d in                          (* [comment removed for export] *)
  let offset := offset + 4 in
  if caplen <? offset then d else
  let d := swap_field 4 36 d in                          (* [comment removed for export] *)
  let iso := get_u8 d 9 =? URB_ISOCHRONOUS in            (* [comment removed for export] *)
  let k (offset : Z) (d : list Z) :=
    if header_len_64_bytes then
      let offset := offset + 4 in
      if caplen <? offset then d else
      let d := swap_field 4 48 d in                      (* [comment removed for export] *)
      let offset := offset + 4 in
      if caplen <? offset then d else
      let d := swap_field 4 52 d in                      (* [comment removed for export] *)
      let offset := offset + 4 in
      if caplen <? offset then d else
      let d := swap_field 4 56 d in                      (* [comment removed for export] *)
      let offset := offset + 4 in
      if caplen <? offset then d else
      let d := swap_field 4 60 d in                      (* [comment removed for export] *)
      if get_u8 d 9 =? URB_ISOCHRONOUS then
        swap_usb_isodescs (Z.to_nat (caplen / 16 + 2)) (get_le32 d 60) caplen 0 64 offset d
      else d
    else d in
  if iso then
    let offset := offset + 4 in
    if caplen <? offset then d else
    let d := swap_field 4 40 d in                        (* [comment removed for export] *)
    let offset := offset + 4 in
    if caplen <? offset then d else
    let d := swap_field 4 44 d in                        (* [comment removed for export] *)
    k offset d
  else k (offset + 8) d.

(* [comment removed for export] *)
Fixpoint swap_nflog_tlvs (fuel : nat) (caplen length p : Z) (d : list Z) : list Z :=
  match fuel with
  | O => d
  | S fuel' =>
    if caplen <? 4 then d else
    let d := swap_field 2 (p + 2) d in                   (* [comment removed for export] *)
    let d := swap_field 2 p d in                         (* [comment removed for export] *)
    let size := get_le16 d p in
    let size := if size mod 4 =? 0 then size else size + (4 - size mod 4) in
    if size <? 4 then d else
    if (caplen <? size) || (length <? size) then d else
    swap_nflog_tlvs fuel' (caplen - size) (length - size) (p + size) d
  end.

(* [comment removed for export] *)
Definition swap_nflog_header (hdr : pkthdr) (d : list Z) : list Z :=
  let caplen := h_caplen hdr in
  let length := h_len hdr in
  if (caplen <? 4) || (length <? 4) then d else
  if negb (get_u8 d 1 =? 0) then d else                  (* [comment removed for export] *)
  swap_nflog_tlvs (Z.to_nat (caplen / 4 + 1)) (caplen - 4) (length - 4) 4 d.

(* [comment removed for export] *)
Definition swap_pseudo_headers (linktype : Z) (hdr : pkthdr) (d : list Z) : list Z :=
  if linktype =? DLT_PFLOG then swap_pflog_header hdr d
  else if linktype =? DLT_LINUX_SLL then swap_linux_sll_socketcan_header hdr d
  else if linktype =? DLT_LINUX_SLL2 then swap_linux_sll2_socketcan_header hdr d
  else if linktype =? DLT_USB_LINUX then swap_linux_usb_header hdr d false
  else if linktype =? DLT_USB_LINUX_MMAPPED then swap_linux_usb_header hdr d true
  else if linktype =? DLT_NFLOG then swap_nflog_header hdr d
  else d.

(* [comment removed for export] *)
Definition u_int_sum (a b : Z) : Z := if b <=? UINT_MAX - a then a + b else UINT_MAX.
(* [comment removed for export] *)
Definition iso_pseudo_header_len (ndesc : Z) : Z := u32 (64 + ndesc * 16).

(* [comment removed for export] *)
Fixpoint iso_data_len_loop (fuel : nat) (ndesc : Z) (desc bytes_left pre : Z) (d : list Z) : Z :=
  match fuel with
  | O => pre
  | S fuel' =>
    if (desc <? ndesc) && (16 <=? bytes_left) then
      let dlen := get_le32 d (64 + 16 * desc + 8) in
      let pre := if negb (dlen =? 0) then
                   let desc_end := u_int_sum (get_le32 d (64 + 16 * desc + 4)) dlen in
                   if pre <? desc_end then desc_end else pre
                 else pre in
      iso_data_len_loop fuel' ndesc (desc + 1) (bytes_left - 16) pre d
    else pre
  end.
Definition incoming_isochronous_transfer_completed_len (hdr : pkthdr) (d : list Z) : Z :=
  let ndesc := get_le32 d 60 in
  let pre := iso_data_len_loop (Z.to_nat (ndesc + 1)) ndesc 0 (h_caplen hdr - 64) 0 d in
  u_int_sum (iso_pseudo_header_len ndesc) pre.

(* [comment removed for export] *)
Definition fixup_usb_mmapped_len (hdr : pkthdr) (d : list Z) : pkthdr :=
  let caplen := h_caplen hdr in
  if caplen <? 64 then hdr else
  let ndesc := get_le32 d 60 in
  if USB_MAXDESC <? ndesc then hdr else
  let data_flag := get_u8 d 15 in
  let transfer_type := get_u8 d 9 in
  let event_type := get_u8 d 8 in
  let endpoint_number := get_u8 d 10 in
  let urb_len := get_le32 d 32 in
  if (data_flag =? 0) && (transfer_type =? URB_ISOCHRONOUS) && (event_type =? URB_COMPLETE)
     && negb (Z.land endpoint_number URB_TRANSFER_IN =? 0)
     && (h_len hdr =? u32 (iso_pseudo_header_len ndesc + urb_len))
  then
    if caplen <? iso_pseudo_header_len ndesc then hdr else
    let len := incoming_isochronous_transfer_completed_len hdr d in
    let hdr := if caplen <=? len then mkHdr (h_sec hdr) (h_usec hdr) caplen len else hdr in
    if h_len hdr <? h_caplen hdr then mkHdr (h_sec hdr) (h_usec hdr) (h_caplen hdr) (h_caplen hdr) else hdr
  else hdr.

(* [comment removed for export] *)
Definition pcapint_post_process (linktype : Z) (swapped : bool) (hdr : pkthdr) (d : list Z)
  : pkthdr * list Z :=
  let d := if swapped then swap_pseudo_headers linktype hdr d else d in
  let hdr := if linktype =? DLT_USB_LINUX_MMAPPED then fixup_usb_mmapped_len hdr d else hdr in
  (hdr, d).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition get_from_block_data (c : cursor) (chunk_size : Z) : (list Z) + (Z * cursor) :=
  if cur_remaining c <? chunk_size then inl (Msg.block_too_short (cur_block_type c))
  else inr (cur_off c, mkCursor (cur_off c + chunk_size) (cur_remaining c - chunk_size) (cur_block_type c)).

(* [comment removed for export] *)
Definition get_opthdr_from_block_data (swapped : bool) (c : cursor) (buf : list Z)
  : (list Z) + (Z * Z * cursor * list Z) :=
  match get_from_block_data c 4 with
  | inl m => inl m
  | inr (off, c') =>
    let buf := if swapped then swap_field 2 (off + 2) (swap_field 2 off buf) else buf in
    inr (get_le16 buf off, get_le16 buf (off + 2), c', buf)
  end.

(* [comment removed for export] *)
Definition get_optvalue_from_block_data (c : cursor) (option_length : Z) : (list Z) + (Z * cursor) :=
  get_from_block_data c (((option_length + 3) / 4) * 4).

Definition OPT_ENDOFOPT : Z := 0.
Definition IF_TSRESOL : Z := 9.
Definition IF_TSOFFSET : Z := 14.

(* [comment removed for export] *)
Record idbopts := mkIdbOpts { io_tsresol : Z ; io_tsoffset : Z ; io_is_binary : bool ;
                              io_saw_tsresol : bool ; io_saw_tsoffset : bool }.

(* [comment removed for export] *)
Fixpoint process_idb_options_loop (fuel : nat) (swapped : bool) (st : idbopts) (c : cursor) (buf : list Z)
  : list Z * ((list Z) + (idbopts * cursor)) :=
  match fuel with
  | O => (buf, inr (st, c))
  | S fuel' =>
    if cur_remaining c =? 0 then (buf, inr (st, c)) else
    match get_opthdr_from_block_data swapped c buf with
    | inl m => (buf, inl m)
    | inr (code, olen, c, buf) =>
      match get_optvalue_from_block_data c olen with
      | inl m => (buf, inl m)
      | inr (voff, c) =>
        if code =? OPT_ENDOFOPT then
          if negb (olen =? 0) then (buf, inl (Msg.endofopt_len olen))
          else (buf, inr (st, c))                                  (* [comment removed for export] *)
        else if code =? IF_TSRESOL then
          if negb (olen =? 1) then (buf, inl (Msg.tsresol_len olen)) else
          if io_saw_tsresol st then (buf, inl Msg.tsresol_dup) else
          let tsresol_opt := get_u8 buf voff in
          if negb (Z.land tsresol_opt 128 =? 0) then
            let tsresol_shift := Z.land tsresol_opt 127 in
            if 63 <? tsresol_shift then (buf, inl (Msg.tsresol_bin_high tsresol_shift))
            else process_idb_options_loop fuel' swapped
                   (mkIdbOpts (2 ^ tsresol_shift) (io_tsoffset st) true true (io_saw_tsoffset st)) c buf
          else
            if 19 <? tsresol_opt then (buf, inl (Msg.tsresol_dec_high tsresol_opt))
            else process_idb_options_loop fuel' swapped
                   (mkIdbOpts (10 ^ tsresol_opt) (io_tsoffset st) false true (io_saw_tsoffset st)) c buf
        else if code =? IF_TSOFFSET then
          if negb (olen =? 8) then (buf, inl (Msg.tsoffset_len olen)) else
          if io_saw_tsoffset st then (buf, inl Msg.tsoffset_dup) else
          let raw := get_le64 buf voff in
          let tsoffset := if swapped then s64 (bswap64 raw) else s64 raw in
          process_idb_options_loop fuel' swapped
            (mkIdbOpts (io_tsresol st) tsoffset (io_is_binary st) (io_saw_tsresol st) true) c buf
        else process_idb_options_loop fuel' swapped st c buf
      end
    end
  end.

(* [comment removed for export] *)
Definition process_idb_options (swapped : bool) (c : cursor) (buf : list Z)
  : list Z * ((list Z) + (idbopts * cursor)) :=
  process_idb_options_loop (Z.to_nat (cur_remaining c / 4 + 1)) swapped
    (mkIdbOpts 1000000 0 false false false) c buf.

(* [comment removed for export] *)
Example linktype_to_dlt_ex : map linktype_to_dlt [0; 10; 11; 99; 100; 101; 102; 103; 104; 105; 106; 107; 276]
                             = [0; 10; 11; 99; 11; 12; 15; 16; 104; 105; 19; 107; 276].
Proof. vm_compute. reflexivity. Qed.
Example adjust_ex : map (pcapint_adjust_snapshot 231) [0; 1; 2147483647; 2147483648]
                    = [134217728; 1; 2147483647; 134217728].
Proof. vm_compute. reflexivity. Qed.
Local Open Scope string_scope.
Example fmt_errmsg_ex1 : fmt_errmsg "malloc" [] 12 = str "malloc: Out of memory".
Proof. vm_compute. reflexivity. Qed.
Example fmt_errmsg_ex2 :
  fmt_errmsg "%s" [AStr (str "libpcap_fuzz_pcap.000000")] 2 = str "libpcap_fuzz_pcap.000000: No such file or directory".
Proof. vm_compute. reflexivity. Qed.
Example msg_shb_ex : Msg.shb_invalid_length 8 =
  str "Section Header Block in pcapng dump file has invalid length 28 < _8_ < 1048576 (BT_SHB_INSANE_MAX)".
Proof. vm_compute. reflexivity. Qed.
Example msg_reserved_ex : Msg.reserved_not_zero 67043328 = str "savefile linktype reserved field not zero (0x03ff0000)".
Proof. vm_compute. reflexivity. Qed.
Example msg_snaplen_neg_ex : Msg.invalid_caplen_snaplen 4294967295 5 =
  str "invalid packet capture length 4294967295, bigger than snaplen of 5".
Proof. vm_compute. reflexivity. Qed.
