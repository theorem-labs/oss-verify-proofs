(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import Strings.String.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy.
Import ListNotations.
Import X1bt.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition SIZEOF_SPEEX_HEADER : Z := 80.
Definition SPEEX_NB_MODES : Z := 3.
Definition SPEEX_MAGIC : list Z := str_bytes "Speex   ".
Definition MSG_HEADER_TOO_SMALL : list Z := str_bytes "Speex header too small".
Definition MSG_INVALID_MODE_HEADER : list Z := str_bytes "Invalid mode specified in Speex header".

Record spx_header : Type := mkSpxHeader {
hd_speex_version_id : Z;
hd_header_size : Z;
hd_rate : Z;
hd_mode : Z;
hd_mode_bitstream_version : Z;
hd_nb_channels : Z;
hd_bitrate : Z;
hd_frame_size : Z;
hd_vbr : Z;
hd_frames_per_packet : Z;
hd_extra_headers : Z;
hd_reserved1 : Z;
hd_reserved2 : Z }.

Definition s32_at (l : list Z) (off : Z) : Z := s32 (le32_at l off).

Definition header_of_bytes (pkt : list Z) : spx_header :=
mkSpxHeader (s32_at pkt 28) (s32_at pkt 32) (s32_at pkt 36) (s32_at pkt 40) (s32_at pkt 44)
(s32_at pkt 48) (s32_at pkt 52) (s32_at pkt 56) (s32_at pkt 60) (s32_at pkt 64)
(s32_at pkt 68) (s32_at pkt 72) (s32_at pkt 76).

Definition clamp_channels (c : Z) : Z := if 2 <? c then 2 else if c <? 1 then 1 else c.

Definition set_nb_channels (h : spx_header) (c : Z) : spx_header :=
mkSpxHeader (hd_speex_version_id h) (hd_header_size h) (hd_rate h) (hd_mode h) (hd_mode_bitstream_version h)
c (hd_bitrate h) (hd_frame_size h) (hd_vbr h) (hd_frames_per_packet h)
(hd_extra_headers h) (hd_reserved1 h) (hd_reserved2 h).

Definition le32_bytes (v : Z) : list Z :=
let u := u32 v in [u mod 256; (u / 2^8) mod 256; (u / 2^16) mod 256; (u / 2^24) mod 256].

Definition header_block_bytes (pkt : list Z) (h : spx_header) : list Z :=
ztake 48 pkt ++ le32_bytes (hd_nb_channels h) ++ zslice 52 28 pkt.

Section SpxHeader.
Context {St ptr : Type}.
Variable lib_calloc : Z -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Variable spx_notify : list Z -> M St unit.

Definition speex_packet_to_header (pkt : list Z) (size : Z) : M St (option (ptr * spx_header)) :=
if size <? SIZEOF_SPEEX_HEADER then
spx_notify MSG_HEADER_TOO_SMALL ;;; mret None
else if negb (list_eqb (ztake 8 pkt) SPEEX_MAGIC) then mret None
else
r <- lib_calloc SIZEOF_SPEEX_HEADER 1 ;;
match r with
| None => munr
| Some blk =>
let h := header_of_bytes pkt in
if (SPEEX_NB_MODES <=? hd_mode h) || (hd_mode h <? 0) then
spx_notify MSG_INVALID_MODE_HEADER ;;; lib_free blk ;;; mret None
else
mret (Some (blk, set_nb_channels h (clamp_channels (hd_nb_channels h))))
end.

End SpxHeader.

Lemma SPEEX_MAGIC_eq : SPEEX_MAGIC = [83; 112; 101; 101; 120; 32; 32; 32].
Proof. reflexivity. Qed.
