(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1nw X1qz X1nt X1rg X1rh X1re X1od.
Import ListNotations.

Section PMap.
Context {ptr ptr' : Type}.
Variable f : ptr -> ptr'.

Definition pm_sync (sy : sync_st ptr) : sync_st ptr' :=
mkSync (option_map f (sy_data sy)) (sy_buf sy) (sy_storage sy) (sy_fill sy) (sy_returned sy)
(sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy).

Definition pm_stream (os : stream_st ptr) : stream_st ptr' :=
mkStream (option_map f (os_body_data os)) (os_body os) (os_body_storage os) (os_body_fill os) (os_body_returned os)
(option_map f (os_lacing_vals os)) (os_lacing os) (option_map f (os_granule_vals os)) (os_granules os)
(os_lacing_storage os) (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os)
(os_header_fill os) (os_e_o_s os) (os_b_o_s os) (os_serialno os) (os_pageno os) (os_packetno os) (os_granulepos os).

Definition pm_bits (b : bits_st ptr) : bits_st ptr' :=
mkBits (f (sb_chars b)) (sb_data b) (sb_nbBits b) (sb_charPtr b) (sb_bitPtr b) (sb_owner b) (sb_overflow b) (sb_buf_size b).

Definition pm_nb (st : nb_state ptr) : nb_state ptr' :=
mkNB (f (nb_blk st)) (nb_first st) (nb_count_lost st) (nb_sampling_rate st) (nb_innov_save st) (nb_pitch_gain_buf_idx st)
(nb_encode_submode st) (nb_submodeID st) (nb_lpc_enh_enabled st) (nb_stereo_cb st) (nb_voc_offset st) (nb_dtx_enabled st)
(nb_isWideband st) (nb_highpass_enabled st).

Definition pm_sbd (st : sbd_state ptr) : sbd_state ptr' :=
mkSBD (f (sbd_blk st)) (sbd_mode st) (sbd_full_frame_size st) (sbd_frame_size st) (sbd_subframeSize st) (sbd_nbSubframes st)
(sbd_lpcSize st) (sbd_first st) (sbd_sampling_rate st) (sbd_lpc_enh_enabled st)
(f (sbd_g0_mem st)) (f (sbd_g1_mem st)) (f (sbd_excBuf st)) (f (sbd_old_qlsp st)) (f (sbd_interp_qlpc st))
(f (sbd_mem_sp st)) (f (sbd_pi_gain st)) (f (sbd_exc_rms st))
(sbd_innov_save st) (sbd_encode_submode st) (sbd_submodeID st).

Fixpoint pm_dec (d : dec_state ptr) : dec_state ptr' :=
match d with
| DecNB n => DecNB (pm_nb n)
| DecSB s low => DecSB (pm_sbd s) (pm_dec low)
end.

Definition pm_h (h : hstate ptr) : hstate ptr' :=
mkH (pm_sync (h_oy h)) (pm_stream (h_os h)) (pm_bits (h_bits h)) (option_map pm_dec (h_st h))
(h_stream_init h) (h_packet_count h) (h_last_granule h) (h_skip_samples h) (h_nframes h) (h_eos h) (h_channels h)
(h_rate h) (h_extra_headers h) (h_speex_serialno h) (h_frame_size h) (h_granule_frame_size h) (h_bytes_remaining h).

Definition pm_outcome (o : outcome ptr) : outcome ptr' :=
match o with Cont h => Cont (pm_h h) | Returned => Returned end.

End PMap.

Definition er {ptr : Type} : ptr -> unit := fun _ => tt.
Abbreviation er_opt := (option_map er).
Abbreviation er_sync := (pm_sync er).
Abbreviation er_stream := (pm_stream er).
Abbreviation er_bits := (pm_bits er).
Abbreviation er_nb := (pm_nb er).
Abbreviation er_sbd := (pm_sbd er).
Abbreviation er_dec := (pm_dec er).
Abbreviation er_h := (pm_h er).
Abbreviation er_outcome := (pm_outcome er).
