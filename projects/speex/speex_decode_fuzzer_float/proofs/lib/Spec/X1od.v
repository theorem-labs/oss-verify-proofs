(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import Strings.String.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1nw X1qz X1nt X1rg X1rh X1re.
Import ListNotations.
Import X1bt.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition INT64_MAX : Z := 9223372036854775807.
Definition INT_MAX : Z := 2147483647.
Definition INT_MIN : Z := -2147483648.
Definition MAX_FUZZ_SIZE : Z := 4096.
Definition CHUNK : Z := 200.
Definition SPEEX_STR : list Z := str_bytes "Speex".

Section Records.
Variable ptr : Type.
Record hstate : Type := mkH {
h_oy : sync_st ptr;
h_os : stream_st ptr;
h_bits : bits_st ptr;
h_st : option (dec_state ptr);
h_stream_init : Z;
h_packet_count : Z;
h_last_granule : Z;
h_skip_samples : Z;
h_nframes : Z;
h_eos : Z;
h_channels : Z;
h_rate : Z;
h_extra_headers : Z;
h_speex_serialno : Z;
h_frame_size : Z;
h_granule_frame_size : Z;
h_bytes_remaining : Z }.
End Records.
Arguments mkH {ptr}.
Arguments h_oy {ptr}. Arguments h_os {ptr}. Arguments h_bits {ptr}. Arguments h_st {ptr}. Arguments h_stream_init {ptr}.
Arguments h_packet_count {ptr}. Arguments h_last_granule {ptr}. Arguments h_skip_samples {ptr}. Arguments h_nframes {ptr}.
Arguments h_eos {ptr}. Arguments h_channels {ptr}. Arguments h_rate {ptr}. Arguments h_extra_headers {ptr}.
Arguments h_speex_serialno {ptr}. Arguments h_frame_size {ptr}. Arguments h_granule_frame_size {ptr}.
Arguments h_bytes_remaining {ptr}.

Section Setters.
Context {ptr : Type}.
Implicit Types h : hstate ptr.
Definition set_ogg h oy os : hstate ptr :=
mkH oy os (h_bits h) (h_st h) (h_stream_init h) (h_packet_count h) (h_last_granule h) (h_skip_samples h)
(h_nframes h) (h_eos h) (h_channels h) (h_rate h) (h_extra_headers h) (h_speex_serialno h)
(h_frame_size h) (h_granule_frame_size h) (h_bytes_remaining h).
Definition set_bits_st h b st (eos : Z) : hstate ptr :=
mkH (h_oy h) (h_os h) b st (h_stream_init h) (h_packet_count h) (h_last_granule h) (h_skip_samples h)
(h_nframes h) eos (h_channels h) (h_rate h) (h_extra_headers h) (h_speex_serialno h)
(h_frame_size h) (h_granule_frame_size h) (h_bytes_remaining h).
Definition set_stream_init h os : hstate ptr :=
mkH (h_oy h) os (h_bits h) (h_st h) 1 (h_packet_count h) (h_last_granule h) (h_skip_samples h)
(h_nframes h) (h_eos h) (h_channels h) (h_rate h) (h_extra_headers h) (h_speex_serialno h)
(h_frame_size h) (h_granule_frame_size h) (h_bytes_remaining h).
Definition set_granule h (last_granule skip : Z) : hstate ptr :=
mkH (h_oy h) (h_os h) (h_bits h) (h_st h) (h_stream_init h) (h_packet_count h) last_granule skip
(h_nframes h) (h_eos h) (h_channels h) (h_rate h) (h_extra_headers h) (h_speex_serialno h)
(h_frame_size h) (h_granule_frame_size h) (h_bytes_remaining h).
Definition set_serialno h (sser : Z) : hstate ptr :=
mkH (h_oy h) (h_os h) (h_bits h) (h_st h) (h_stream_init h) (h_packet_count h) (h_last_granule h) (h_skip_samples h)
(h_nframes h) (h_eos h) (h_channels h) (h_rate h) (h_extra_headers h) sser
(h_frame_size h) (h_granule_frame_size h) (h_bytes_remaining h).
Definition incr_packet_count h : hstate ptr :=
mkH (h_oy h) (h_os h) (h_bits h) (h_st h) (h_stream_init h) (h_packet_count h + 1) (h_last_granule h) (h_skip_samples h)
(h_nframes h) (h_eos h) (h_channels h) (h_rate h) (h_extra_headers h) (h_speex_serialno h)
(h_frame_size h) (h_granule_frame_size h) (h_bytes_remaining h).
Definition set_bytes_remaining h oy (br : Z) : hstate ptr :=
mkH oy (h_os h) (h_bits h) (h_st h) (h_stream_init h) (h_packet_count h) (h_last_granule h) (h_skip_samples h)
(h_nframes h) (h_eos h) (h_channels h) (h_rate h) (h_extra_headers h) (h_speex_serialno h)
(h_frame_size h) (h_granule_frame_size h) br.

Definition set_header h st (nframes channels rate extra frame_size : Z) : hstate ptr :=
mkH (h_oy h) (h_os h) (h_bits h) (Some st) (h_stream_init h) (h_packet_count h) (h_last_granule h) (h_skip_samples h)
(if nframes =? 0 then 1 else nframes) (h_eos h) channels rate extra (h_speex_serialno h)
frame_size frame_size (h_bytes_remaining h).
End Setters.

Inductive outcome {ptr : Type} : Type := Cont (h : hstate ptr) | Returned.
Arguments outcome ptr : clear implicits.

Section Harness.
Context {St ptr : Type}.
Variable lib_malloc : Z -> M St (option ptr).
Variable lib_calloc : Z -> Z -> M St (option ptr).
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Variable spx_notify : list Z -> M St unit.
Variable spx_warning : list Z -> M St unit.

Variable bits_unpack_unsigned : bits_st ptr -> Z -> M St (Z * bits_st ptr).
Variable bits_peek : bits_st ptr -> M St (Z * bits_st ptr).
Variable bits_advance : bits_st ptr -> Z -> M St (bits_st ptr).
Variable bits_remaining : bits_st ptr -> M St Z.

Definition h_decoder_init (m : spx_mode) : M St (option (dec_state ptr)) :=
speex_decoder_init lib_calloc lib_free m.
Definition h_decoder_destroy (d : dec_state ptr) : M St unit := speex_decoder_destroy lib_free d.
Definition h_decode (d : dec_state ptr) (b : bits_st ptr) : M St (Z * dec_state ptr * bits_st ptr) :=
speex_decode spx_notify bits_unpack_unsigned bits_peek bits_advance bits_remaining d b 0.

Implicit Types h : hstate ptr.

Definition cleanup h : M St unit :=
(match h_st h with Some d => h_decoder_destroy d | None => mret tt end) ;;;
speex_bits_destroy lib_free (h_bits h) ;;;
(if negb (h_stream_init h =? 0) then os' <- ogg_stream_clear lib_free (h_os h) ;; mret tt else mret tt) ;;;
oy' <- ogg_sync_clear lib_free (h_oy h) ;; mret tt.

Definition process_header h (pdata : list Z) (bytes : Z) : M St (option (hstate ptr)) :=
r <- speex_packet_to_header lib_calloc lib_free spx_notify pdata bytes ;;
match r with
| None => mret None
| Some (blk, hd) =>
if (SPEEX_NB_MODES <=? hd_mode hd) || (hd_mode hd <? 0) then lib_free blk ;;; mret None else
let modeID := hd_mode hd in
match speex_lib_get_mode modeID with
| None => munr
| Some mode =>
if 1 <? hd_speex_version_id hd then lib_free blk ;;; mret None else
if mode_bitstream_version mode <? hd_mode_bitstream_version hd then lib_free blk ;;; mret None else
if hd_mode_bitstream_version hd <? mode_bitstream_version mode then lib_free blk ;;; mret None else
ost <- h_decoder_init mode ;;
match ost with
| None => lib_free blk ;;; mret None
| Some st =>
let '(_, st) := speex_decoder_ctl st (CtlSetEnh 1) in
let '(frame_size, st) := speex_decoder_ctl st CtlGetFrameSize in
if (frame_size <? 0) || (2 * 320 <? frame_size) then h_decoder_destroy st ;;; lib_free blk ;;; mret None else
let rate := if h_rate h =? 0 then hd_rate hd else h_rate h in
let '(_, st) := speex_decoder_ctl st (CtlSetSamplingRate rate) in
if (hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd)
then h_decoder_destroy st ;;; lib_free blk ;;; mret None else
let nframes := hd_frames_per_packet hd in
let channels := if h_channels h =? -1 then hd_nb_channels hd else h_channels h in
let '(channels, st) := (if negb (channels =? 1)
then let '(_, st) := speex_decoder_ctl st CtlSetHandlerStereo in (2, st)
else (channels, st)) in
if INT_MAX - 1 <? hd_extra_headers hd then h_decoder_destroy st ;;; lib_free blk ;;; mret None else
let extra := hd_extra_headers hd in
lib_free blk ;;;

let '(lookahead, st) := speex_decoder_ctl st CtlGetLookahead in
mret (Some (set_header h st nframes channels rate extra frame_size))
end end
end.

Fixpoint decode_loop (n : nat) (st : dec_state ptr) (b : bits_st ptr) : M St (dec_state ptr * bits_st ptr) :=
match n with
| O => mret (st, b)
| S n' =>
' (ret, st, b) <- h_decode st b ;;
if (ret =? -1) || (ret =? -2) then mret (st, b)
else rem <- bits_remaining b ;;
if rem <? 0 then mret (st, b)
else decode_loop n' st b
end.

Fixpoint packet_loop (fuel : nat) h (packet_no : Z) : M St (outcome ptr) :=
match fuel with
| O => munr
| S fuel' =>
if negb (h_eos h =? 0) then mret (Cont h) else
match ogg_stream_packetout (h_os h) with
| None => munr
| Some ((r, oop), os) =>
let h := set_ogg h (h_oy h) os in
if negb (r =? 1) then mret (Cont h) else
match oop with
| None => munr
| Some op =>
let pdata := packet_data os op in
let sser := if (5 <=? pk_bytes op) && list_eqb (ztake 5 pdata) SPEEX_STR
then os_serialno os else h_speex_serialno h in
let h := set_serialno h sser in
if (sser =? -1) || negb (os_serialno os =? sser) then mret (Cont h) else
ro <- (if h_packet_count h =? 0 then
ph <- process_header h pdata (pk_bytes op) ;;
match ph with
| None => cleanup h ;;; mret None
| Some h => mret (Some (h, packet_no))
end
else if h_packet_count h <=? 1 + h_extra_headers h then mret (Some (h, packet_no))
else
let packet_no := packet_no + 1 in
let eos := if negb (pk_e_o_s op =? 0) && (os_serialno os =? h_speex_serialno h) then 1 else h_eos h in
b <- speex_bits_read_from lib_realloc spx_notify spx_warning (h_bits h) pdata (pk_bytes op) ;;
match h_st h with
| None => munr
| Some st =>
' (st, b) <- decode_loop (Z.to_nat (h_nframes h)) st b ;;
mret (Some (set_bits_st h b (Some st) eos, packet_no))
end) ;;
match ro with
| None => mret Returned
| Some (h, packet_no) => packet_loop fuel' (incr_packet_count h) packet_no
end
end
end
end.
Definition packet_fuel (os : stream_st ptr) : nat := S (Z.to_nat (os_lacing_fill os - os_lacing_returned os)).

Definition granule_step h (hdr : list Z) : option Z :=
let page_granule := ogg_page_granulepos hdr in
let page_nb_packets := ogg_page_packets hdr in
if (0 <? page_granule) && negb (h_frame_size h =? 0) &&
((0 <? h_last_granule h) || (page_granule <? INT64_MAX + h_last_granule h)) then
let a := page_nb_packets * h_granule_frame_size h * h_nframes h in
let b := page_granule - h_last_granule h in
if (a <? b) || (Z.quot INT64_MAX 640 - a <? - b) || (Z.quot INT64_MAX 640 <? a - b) then None
else
let skip := s32 (Z.quot (h_frame_size h * (a - b)) (h_granule_frame_size h)) in
if skip =? INT_MIN then None
else Some (if negb (ogg_page_eos hdr =? 0) then - skip else skip)
else if page_granule <? -1 then None
else Some 0.

Fixpoint page_loop (fuel : nat) h : M St (outcome ptr) :=
match fuel with
| O => munr
| S fuel' =>
match ogg_sync_pageout (h_oy h) with
| None => munr
| Some ((r, oog), oy) =>
let h := set_ogg h oy (h_os h) in
if negb (r =? 1) then mret (Cont h) else
match oog with
| None => munr
| Some og =>
let hdr := page_header oy og in
let body := page_body oy og in
let serial := ogg_page_serialno hdr in
h <- (if h_stream_init h =? 0 then
' (r, os) <- ogg_stream_init lib_malloc lib_free serial ;;
mret (set_stream_init h os)
else mret h) ;;
let h := (if negb (serial =? os_serialno (h_os h)) then
let '(r, os) := ogg_stream_reset_serialno (h_os h) serial in set_ogg h (h_oy h) os
else h) in
' (r, os) <- ogg_stream_pagein lib_realloc lib_free (h_os h) hdr body ;;
let h := set_ogg h (h_oy h) os in
match granule_step h hdr with
| None => cleanup h ;;; mret Returned
| Some skip =>
let h := set_granule h (ogg_page_granulepos hdr) skip in
o <- packet_loop (packet_fuel (h_os h)) h 0 ;;
match o with
| Returned => mret Returned
| Cont h => page_loop fuel' h
end
end
end
end
end.
Definition page_fuel (oy : sync_st ptr) : nat := S (Z.to_nat (sy_fill oy - sy_returned oy)).

Fixpoint chunk_loop (fuel : nat) (payload : list Z) h : M St (outcome ptr) :=
match fuel with
| O => munr
| S fuel' =>
let nb_read := if CHUNK <? h_bytes_remaining h then CHUNK else h_bytes_remaining h in
' (data, oy) <- ogg_sync_buffer lib_malloc lib_realloc lib_free (h_oy h) nb_read ;;
let h := set_ogg h oy (h_os h) in
match data, (0 <? nb_read) with
| None, true => munr
| _, _ =>
let oy := match data with Some (_, off) => sync_write oy off (ztake nb_read payload) | None => oy end in
let '(r, oy) := ogg_sync_wrote oy nb_read in
let h := set_bytes_remaining h oy (h_bytes_remaining h - nb_read) in
o <- page_loop (page_fuel (h_oy h)) h ;;
match o with
| Returned => mret Returned
| Cont h => if h_bytes_remaining h <=? 0 then mret (Cont h) else chunk_loop fuel' payload h
end
end
end.
Definition chunk_fuel (fuzz_size : Z) : nat := S (Z.to_nat fuzz_size).

Definition LLVMFuzzerTestOneInput (payload : list Z) : M St Z :=
let fuzz_size := zlength payload in
if MAX_FUZZ_SIZE <? fuzz_size then mret 0 else
let oy := ogg_sync_init in
ob <- speex_bits_init lib_calloc ;;
match ob with
| None => munr
| Some bits =>
let h := mkH oy stream_zero bits None 0 0 0 0 2 0 (-1) 0 0 (-1) 0 0 fuzz_size in
o <- chunk_loop (chunk_fuel fuzz_size) payload h ;;
match o with
| Returned => mret 0
| Cont h => cleanup h ;;; mret 0
end
end.

End Harness.
