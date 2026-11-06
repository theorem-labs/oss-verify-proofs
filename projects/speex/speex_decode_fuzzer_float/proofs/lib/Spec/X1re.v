(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import Strings.String.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1nt X1rh.
Import ListNotations.
Import X1bt.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition MSG_INVALID_MODE : list Z := str_bytes "Invalid mode encountered. The stream is corrupted.".
Definition MSG_MORE_THAN_TWO_WB : list Z := str_bytes "More than two wideband layers found. The stream is corrupted.".

Section Records.
Variable ptr : Type.
Record nb_state : Type := mkNB {
nb_blk : ptr;
nb_first : Z;
nb_count_lost : Z;
nb_sampling_rate : Z;
nb_innov_save : option Z;
nb_pitch_gain_buf_idx : Z;
nb_encode_submode : Z;
nb_submodeID : Z;
nb_lpc_enh_enabled : Z;
nb_stereo_cb : bool;
nb_voc_offset : Z;
nb_dtx_enabled : Z;
nb_isWideband : Z;
nb_highpass_enabled : Z }.

Record sbd_state : Type := mkSBD {
sbd_blk : ptr;
sbd_mode : spx_mode;
sbd_full_frame_size : Z;
sbd_frame_size : Z;
sbd_subframeSize : Z;
sbd_nbSubframes : Z;
sbd_lpcSize : Z;
sbd_first : Z;
sbd_sampling_rate : Z;
sbd_lpc_enh_enabled : Z;
sbd_g0_mem : ptr;
sbd_g1_mem : ptr;
sbd_excBuf : ptr;
sbd_old_qlsp : ptr;
sbd_interp_qlpc : ptr;
sbd_mem_sp : ptr;
sbd_pi_gain : ptr;
sbd_exc_rms : ptr;
sbd_innov_save : option Z;
sbd_encode_submode : Z;
sbd_submodeID : Z }.

Inductive dec_state : Type :=
| DecNB (n : nb_state)
| DecSB (s : sbd_state) (low : dec_state).
End Records.
Arguments mkNB {ptr}. Arguments mkSBD {ptr}. Arguments DecNB {ptr}. Arguments DecSB {ptr}.
Arguments nb_blk {ptr}. Arguments nb_first {ptr}. Arguments nb_count_lost {ptr}. Arguments nb_sampling_rate {ptr}.
Arguments nb_innov_save {ptr}. Arguments nb_pitch_gain_buf_idx {ptr}. Arguments nb_encode_submode {ptr}.
Arguments nb_submodeID {ptr}. Arguments nb_lpc_enh_enabled {ptr}. Arguments nb_stereo_cb {ptr}.
Arguments nb_voc_offset {ptr}. Arguments nb_dtx_enabled {ptr}. Arguments nb_isWideband {ptr}. Arguments nb_highpass_enabled {ptr}.
Arguments sbd_blk {ptr}. Arguments sbd_mode {ptr}. Arguments sbd_full_frame_size {ptr}. Arguments sbd_frame_size {ptr}.
Arguments sbd_subframeSize {ptr}. Arguments sbd_nbSubframes {ptr}. Arguments sbd_lpcSize {ptr}. Arguments sbd_first {ptr}.
Arguments sbd_sampling_rate {ptr}. Arguments sbd_lpc_enh_enabled {ptr}. Arguments sbd_g0_mem {ptr}. Arguments sbd_g1_mem {ptr}.
Arguments sbd_excBuf {ptr}. Arguments sbd_old_qlsp {ptr}. Arguments sbd_interp_qlpc {ptr}. Arguments sbd_mem_sp {ptr}.
Arguments sbd_pi_gain {ptr}. Arguments sbd_exc_rms {ptr}. Arguments sbd_innov_save {ptr}. Arguments sbd_encode_submode {ptr}.
Arguments sbd_submodeID {ptr}.

Section Setters.
Context {ptr : Type}.
Definition set_nb_first (st : nb_state ptr) (v : Z) : nb_state ptr :=
mkNB (nb_blk st) v (nb_count_lost st) (nb_sampling_rate st) (nb_innov_save st) (nb_pitch_gain_buf_idx st) (nb_encode_submode st) (nb_submodeID st) (nb_lpc_enh_enabled st) (nb_stereo_cb st) (nb_voc_offset st) (nb_dtx_enabled st) (nb_isWideband st) (nb_highpass_enabled st).
Definition set_nb_count_lost (st : nb_state ptr) (v : Z) : nb_state ptr :=
mkNB (nb_blk st) (nb_first st) v (nb_sampling_rate st) (nb_innov_save st) (nb_pitch_gain_buf_idx st) (nb_encode_submode st) (nb_submodeID st) (nb_lpc_enh_enabled st) (nb_stereo_cb st) (nb_voc_offset st) (nb_dtx_enabled st) (nb_isWideband st) (nb_highpass_enabled st).
Definition set_nb_sampling_rate (st : nb_state ptr) (v : Z) : nb_state ptr :=
mkNB (nb_blk st) (nb_first st) (nb_count_lost st) v (nb_innov_save st) (nb_pitch_gain_buf_idx st) (nb_encode_submode st) (nb_submodeID st) (nb_lpc_enh_enabled st) (nb_stereo_cb st) (nb_voc_offset st) (nb_dtx_enabled st) (nb_isWideband st) (nb_highpass_enabled st).
Definition set_nb_innov_save (st : nb_state ptr) (v : option Z) : nb_state ptr :=
mkNB (nb_blk st) (nb_first st) (nb_count_lost st) (nb_sampling_rate st) v (nb_pitch_gain_buf_idx st) (nb_encode_submode st) (nb_submodeID st) (nb_lpc_enh_enabled st) (nb_stereo_cb st) (nb_voc_offset st) (nb_dtx_enabled st) (nb_isWideband st) (nb_highpass_enabled st).
Definition set_nb_pitch_gain_buf_idx (st : nb_state ptr) (v : Z) : nb_state ptr :=
mkNB (nb_blk st) (nb_first st) (nb_count_lost st) (nb_sampling_rate st) (nb_innov_save st) v (nb_encode_submode st) (nb_submodeID st) (nb_lpc_enh_enabled st) (nb_stereo_cb st) (nb_voc_offset st) (nb_dtx_enabled st) (nb_isWideband st) (nb_highpass_enabled st).
Definition set_nb_submodeID (st : nb_state ptr) (v : Z) : nb_state ptr :=
mkNB (nb_blk st) (nb_first st) (nb_count_lost st) (nb_sampling_rate st) (nb_innov_save st) (nb_pitch_gain_buf_idx st) (nb_encode_submode st) v (nb_lpc_enh_enabled st) (nb_stereo_cb st) (nb_voc_offset st) (nb_dtx_enabled st) (nb_isWideband st) (nb_highpass_enabled st).
Definition set_nb_lpc_enh_enabled (st : nb_state ptr) (v : Z) : nb_state ptr :=
mkNB (nb_blk st) (nb_first st) (nb_count_lost st) (nb_sampling_rate st) (nb_innov_save st) (nb_pitch_gain_buf_idx st) (nb_encode_submode st) (nb_submodeID st) v (nb_stereo_cb st) (nb_voc_offset st) (nb_dtx_enabled st) (nb_isWideband st) (nb_highpass_enabled st).
Definition set_nb_stereo_cb (st : nb_state ptr) (v : bool) : nb_state ptr :=
mkNB (nb_blk st) (nb_first st) (nb_count_lost st) (nb_sampling_rate st) (nb_innov_save st) (nb_pitch_gain_buf_idx st) (nb_encode_submode st) (nb_submodeID st) (nb_lpc_enh_enabled st) v (nb_voc_offset st) (nb_dtx_enabled st) (nb_isWideband st) (nb_highpass_enabled st).
Definition set_nb_voc_offset (st : nb_state ptr) (v : Z) : nb_state ptr :=
mkNB (nb_blk st) (nb_first st) (nb_count_lost st) (nb_sampling_rate st) (nb_innov_save st) (nb_pitch_gain_buf_idx st) (nb_encode_submode st) (nb_submodeID st) (nb_lpc_enh_enabled st) (nb_stereo_cb st) v (nb_dtx_enabled st) (nb_isWideband st) (nb_highpass_enabled st).
Definition set_nb_dtx_enabled (st : nb_state ptr) (v : Z) : nb_state ptr :=
mkNB (nb_blk st) (nb_first st) (nb_count_lost st) (nb_sampling_rate st) (nb_innov_save st) (nb_pitch_gain_buf_idx st) (nb_encode_submode st) (nb_submodeID st) (nb_lpc_enh_enabled st) (nb_stereo_cb st) (nb_voc_offset st) v (nb_isWideband st) (nb_highpass_enabled st).
Definition set_nb_isWideband (st : nb_state ptr) (v : Z) : nb_state ptr :=
mkNB (nb_blk st) (nb_first st) (nb_count_lost st) (nb_sampling_rate st) (nb_innov_save st) (nb_pitch_gain_buf_idx st) (nb_encode_submode st) (nb_submodeID st) (nb_lpc_enh_enabled st) (nb_stereo_cb st) (nb_voc_offset st) (nb_dtx_enabled st) v (nb_highpass_enabled st).

Definition set_sbd_first (st : sbd_state ptr) (v : Z) : sbd_state ptr :=
mkSBD (sbd_blk st) (sbd_mode st) (sbd_full_frame_size st) (sbd_frame_size st) (sbd_subframeSize st) (sbd_nbSubframes st) (sbd_lpcSize st) v (sbd_sampling_rate st) (sbd_lpc_enh_enabled st) (sbd_g0_mem st) (sbd_g1_mem st) (sbd_excBuf st) (sbd_old_qlsp st) (sbd_interp_qlpc st) (sbd_mem_sp st) (sbd_pi_gain st) (sbd_exc_rms st) (sbd_innov_save st) (sbd_encode_submode st) (sbd_submodeID st).
Definition set_sbd_sampling_rate (st : sbd_state ptr) (v : Z) : sbd_state ptr :=
mkSBD (sbd_blk st) (sbd_mode st) (sbd_full_frame_size st) (sbd_frame_size st) (sbd_subframeSize st) (sbd_nbSubframes st) (sbd_lpcSize st) (sbd_first st) v (sbd_lpc_enh_enabled st) (sbd_g0_mem st) (sbd_g1_mem st) (sbd_excBuf st) (sbd_old_qlsp st) (sbd_interp_qlpc st) (sbd_mem_sp st) (sbd_pi_gain st) (sbd_exc_rms st) (sbd_innov_save st) (sbd_encode_submode st) (sbd_submodeID st).
Definition set_sbd_lpc_enh_enabled (st : sbd_state ptr) (v : Z) : sbd_state ptr :=
mkSBD (sbd_blk st) (sbd_mode st) (sbd_full_frame_size st) (sbd_frame_size st) (sbd_subframeSize st) (sbd_nbSubframes st) (sbd_lpcSize st) (sbd_first st) (sbd_sampling_rate st) v (sbd_g0_mem st) (sbd_g1_mem st) (sbd_excBuf st) (sbd_old_qlsp st) (sbd_interp_qlpc st) (sbd_mem_sp st) (sbd_pi_gain st) (sbd_exc_rms st) (sbd_innov_save st) (sbd_encode_submode st) (sbd_submodeID st).
Definition set_sbd_innov_save (st : sbd_state ptr) (v : option Z) : sbd_state ptr :=
mkSBD (sbd_blk st) (sbd_mode st) (sbd_full_frame_size st) (sbd_frame_size st) (sbd_subframeSize st) (sbd_nbSubframes st) (sbd_lpcSize st) (sbd_first st) (sbd_sampling_rate st) (sbd_lpc_enh_enabled st) (sbd_g0_mem st) (sbd_g1_mem st) (sbd_excBuf st) (sbd_old_qlsp st) (sbd_interp_qlpc st) (sbd_mem_sp st) (sbd_pi_gain st) (sbd_exc_rms st) v (sbd_encode_submode st) (sbd_submodeID st).
Definition set_sbd_submodeID (st : sbd_state ptr) (v : Z) : sbd_state ptr :=
mkSBD (sbd_blk st) (sbd_mode st) (sbd_full_frame_size st) (sbd_frame_size st) (sbd_subframeSize st) (sbd_nbSubframes st) (sbd_lpcSize st) (sbd_first st) (sbd_sampling_rate st) (sbd_lpc_enh_enabled st) (sbd_g0_mem st) (sbd_g1_mem st) (sbd_excBuf st) (sbd_old_qlsp st) (sbd_interp_qlpc st) (sbd_mem_sp st) (sbd_pi_gain st) (sbd_exc_rms st) (sbd_innov_save st) (sbd_encode_submode st) v.

End Setters.

Definition dec_mode {ptr} (d : dec_state ptr) : spx_mode :=
match d with DecNB _ => ModeNB | DecSB s _ => sbd_mode s end.

Inductive ctl_req : Type :=
| CtlSetEnh (v : Z)
| CtlGetFrameSize
| CtlSetHandlerStereo
| CtlSetSamplingRate (v : Z)
| CtlGetSamplingRate
| CtlGetLookahead
| CtlGetPiGain
| CtlGetExc
| CtlGetDtxStatus
| CtlSetInnovationSave (off : Z)
| CtlSetWideband (v : Z).

Definition ctl_req_code (r : ctl_req) : Z :=
match r with
| CtlSetEnh _ => 0 | CtlGetFrameSize => 3 | CtlSetHandlerStereo => 20 | CtlSetSamplingRate _ => 24
| CtlGetSamplingRate => 25 | CtlGetLookahead => 39 | CtlGetPiGain => 100 | CtlGetExc => 101
| CtlGetDtxStatus => 103 | CtlSetInnovationSave _ => 104 | CtlSetWideband _ => 105
end.

Section Ctl.
Context {ptr : Type}.

Definition nb_decoder_ctl (st : nb_state ptr) (r : ctl_req) : Z * nb_state ptr :=
match r with
| CtlSetEnh v => (0, set_nb_lpc_enh_enabled st v)
| CtlGetFrameSize => (NB_FRAME_SIZE, st)
| CtlSetHandlerStereo => (0, set_nb_stereo_cb st true)
| CtlSetSamplingRate v => (0, set_nb_sampling_rate st v)
| CtlGetSamplingRate => (nb_sampling_rate st, st)
| CtlGetLookahead => (NB_SUBFRAME_SIZE, st)
| CtlGetPiGain => (0, st)
| CtlGetExc => (0, st)
| CtlGetDtxStatus => (nb_dtx_enabled st, st)
| CtlSetInnovationSave off => (0, set_nb_innov_save st (Some off))
| CtlSetWideband v => (0, set_nb_isWideband st v)
end.

Definition c_shr1 (v : Z) : Z := Z.shiftr v 1.

Fixpoint speex_decoder_ctl (d : dec_state ptr) (r : ctl_req) : Z * dec_state ptr :=
match d with
| DecNB st => let '(v, st') := nb_decoder_ctl st r in (v, DecNB st')
| DecSB st low =>
match r with
| CtlSetEnh v =>
let '(_, low') := speex_decoder_ctl low r in (0, DecSB (set_sbd_lpc_enh_enabled st v) low')
| CtlGetFrameSize => (sbd_full_frame_size st, d)
| CtlSetHandlerStereo =>
let '(_, low') := speex_decoder_ctl low r in (0, DecSB st low')
| CtlSetSamplingRate v =>
let '(_, low') := speex_decoder_ctl low (CtlSetSamplingRate (c_shr1 v)) in
(0, DecSB (set_sbd_sampling_rate st v) low')
| CtlGetSamplingRate => (sbd_sampling_rate st, d)
| CtlGetLookahead =>
let '(v, low') := speex_decoder_ctl low r in (2 * v, DecSB st low')
| CtlGetPiGain => (0, d)
| CtlGetExc => (0, d)
| CtlGetDtxStatus =>
let '(v, low') := speex_decoder_ctl low r in (v, DecSB st low')
| CtlSetInnovationSave off => (0, DecSB (set_sbd_innov_save st (Some off)) low)
| CtlSetWideband v =>
let '(_, low') := speex_decoder_ctl low r in (0, DecSB st low')
end
end.
End Ctl.

Section SpxDecode.
Context {St ptr : Type}.
Variable lib_calloc : Z -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Variable spx_notify : list Z -> M St unit.
Variable bits_unpack_unsigned : bits_st ptr -> Z -> M St (Z * bits_st ptr).
Variable bits_peek : bits_st ptr -> M St (Z * bits_st ptr).
Variable bits_advance : bits_st ptr -> Z -> M St (bits_st ptr).
Variable bits_remaining : bits_st ptr -> M St Z.

Definition speex_default_user_handler (b : bits_st ptr) : M St (Z * bits_st ptr) :=
' (req_size, b) <- bits_unpack_unsigned b 4 ;;
b <- bits_advance b (5 + 8 * req_size) ;;
mret (0, b).

Definition speex_std_stereo_request_handler (b : bits_st ptr) : M St (Z * bits_st ptr) :=
' (sign, b) <- bits_unpack_unsigned b 1 ;;
' (dexp, b) <- bits_unpack_unsigned b 5 ;;
' (tmp, b) <- bits_unpack_unsigned b 2 ;;
mret (0, b).

Definition inband_skip_bits (id : Z) : Z :=
if id <? 2 then 1 else if id <? 8 then 4 else if id <? 10 then 8
else if id <? 12 then 16 else if id <? 14 then 32 else 64.

Definition speex_inband_handler (b : bits_st ptr) (stereo_cb : bool) : M St (Z * bits_st ptr) :=
' (id, b) <- bits_unpack_unsigned b 4 ;;
if stereo_cb && (id =? SPEEX_INBAND_STEREO) then speex_std_stereo_request_handler b
else b <- bits_advance b (inband_skip_bits id) ;; mret (0, b).

Definition lsp_unquant_lbr (b : bits_st ptr) : M St (bits_st ptr) :=
' (id1, b) <- bits_unpack_unsigned b 6 ;;
' (id2, b) <- bits_unpack_unsigned b 6 ;;
' (id3, b) <- bits_unpack_unsigned b 6 ;;
mret b.

Definition lsp_unquant_nb (b : bits_st ptr) : M St (bits_st ptr) :=
' (id1, b) <- bits_unpack_unsigned b 6 ;;
' (id2, b) <- bits_unpack_unsigned b 6 ;;
' (id3, b) <- bits_unpack_unsigned b 6 ;;
' (id4, b) <- bits_unpack_unsigned b 6 ;;
' (id5, b) <- bits_unpack_unsigned b 6 ;;
mret b.

Definition lsp_unquant_high (b : bits_st ptr) : M St (bits_st ptr) :=
' (id1, b) <- bits_unpack_unsigned b 6 ;;
' (id2, b) <- bits_unpack_unsigned b 6 ;;
mret b.

Definition lsp_unquant (k : lsp_kind) (b : bits_st ptr) : M St (bits_st ptr) :=
match k with
| LspUnquantLbr => lsp_unquant_lbr b
| LspUnquantNb => lsp_unquant_nb b
| LspUnquantHigh => lsp_unquant_high b
end.

Definition pitch_unquant_3tap (par : ltp_params) (start : Z) (b : bits_st ptr) : M St (Z * bits_st ptr) :=
' (p, b) <- bits_unpack_unsigned b (ltp_pitch_bits par) ;;
let pitch := p + start in
' (gain_index, b) <- bits_unpack_unsigned b (ltp_gain_bits par) ;;
mret (pitch, b).

Definition forced_pitch_unquant (start : Z) (b : bits_st ptr) : M St (Z * bits_st ptr) :=
mret (start, b).

Definition ltp_unquant (k : ltp_kind) (start : Z) (b : bits_st ptr) : M St (Z * bits_st ptr) :=
match k with
| LtpForcedPitchUnquant => forced_pitch_unquant start b
| LtpPitchUnquant3tap par => pitch_unquant_3tap par start b
end.

Fixpoint split_cb_read (n : nat) (have_sign shape_bits : Z) (b : bits_st ptr) : M St (bits_st ptr) :=
match n with
| O => mret b
| S n' =>
b <- (if negb (have_sign =? 0) then ' (s, b) <- bits_unpack_unsigned b 1 ;; mret b else mret b) ;;
' (ind, b) <- bits_unpack_unsigned b shape_bits ;;
split_cb_read n' have_sign shape_bits b
end.

Definition split_cb_shape_sign_unquant (par : split_cb_params) (b : bits_st ptr) : M St (bits_st ptr) :=
split_cb_read (Z.to_nat (scb_nb_subvect par)) (scb_have_sign par) (scb_shape_bits par) b.

Definition noise_codebook_unquant (b : bits_st ptr) : M St (bits_st ptr) := mret b.

Definition innovation_unquant (k : innov_kind) (b : bits_st ptr) : M St (bits_st ptr) :=
match k with
| InnovNoiseCodebookUnquant => noise_codebook_unquant b
| InnovSplitCbShapeSignUnquant par => split_cb_shape_sign_unquant par b
end.

Definition nb_init_state (blk : ptr) : (nb_state ptr) :=
mkNB blk 1   0   8000   None   0
1   NB_DEFAULT_SUBMODE   1   false
0   0   0   1  .

Definition nb_decoder_init : M St (option (nb_state ptr)) :=
r <- lib_calloc SIZEOF_DECSTATE 1 ;;
match r with
| None => mret None
| Some blk => mret (Some (nb_init_state blk))
end.

Definition nb_decoder_destroy (st : (nb_state ptr)) : M St unit := lib_free (nb_blk st).

Definition free_opt (o : option ptr) : M St unit :=
match o with Some p => lib_free p | None => mret tt end.

Fixpoint speex_decoder_destroy (d : (dec_state ptr)) : M St unit :=
match d with
| DecNB st => nb_decoder_destroy st
| DecSB st low =>
speex_decoder_destroy low ;;;
lib_free (sbd_g0_mem st) ;;; lib_free (sbd_g1_mem st) ;;; lib_free (sbd_excBuf st) ;;; lib_free (sbd_old_qlsp st) ;;;
lib_free (sbd_interp_qlpc st) ;;; lib_free (sbd_pi_gain st) ;;; lib_free (sbd_exc_rms st) ;;; lib_free (sbd_mem_sp st) ;;;
lib_free (sbd_blk st)
end.

Definition sb_decoder_init (m : spx_mode) (low_init : M St (option (dec_state ptr))) : M St (option (dec_state ptr)) :=
let _ := lib_free in
r <- lib_calloc SIZEOF_SBDECSTATE 1 ;;
match r with
| None => mret None
| Some blk =>
ol <- low_init ;;
match ol with
| None => munr
| Some low =>
let frame_size := sbm_frameSize m in
let subframeSize := sbm_subframeSize m in
let nbSubframes := Z.quot frame_size subframeSize in
let lpcSize := sbm_lpcSize m in
let '(low_rate, low) := speex_decoder_ctl low CtlGetSamplingRate in
let sampling_rate := low_rate * 2 in
let '(_, low) := speex_decoder_ctl low (CtlSetWideband 1) in
g0 <- lib_calloc (QMF_ORDER * 4) 1 ;;
g1 <- lib_calloc (QMF_ORDER * 4) 1 ;;
ex <- lib_calloc (subframeSize * 4) 1 ;;
oq <- lib_calloc (lpcSize * 4) 1 ;;
iq <- lib_calloc (lpcSize * 4) 1 ;;
pg <- lib_calloc (nbSubframes * 4) 1 ;;
er <- lib_calloc (nbSubframes * 4) 1 ;;
ms <- lib_calloc (2 * lpcSize * 4) 1 ;;
match g0, g1, ex, oq, iq, pg, er, ms with
| Some g0, Some g1, Some ex, Some oq, Some iq, Some pg, Some er, Some ms =>
mret (Some (DecSB (mkSBD blk m (2 * frame_size) frame_size subframeSize nbSubframes lpcSize
1   sampling_rate 0
g0 g1 ex oq iq ms pg er None   1
(sbm_defaultSubmode m)) low))
| _, _, _, _, _, _, _, _ =>

munr
end
end
end.

Definition nb_decoder_init_d : M St (option (dec_state ptr)) :=
r <- nb_decoder_init ;; mret (option_map DecNB r).
Definition speex_decoder_init (m : spx_mode) : M St (option (dec_state ptr)) :=
match m with
| ModeNB => nb_decoder_init_d
| ModeWB => sb_decoder_init ModeWB nb_decoder_init_d
| ModeUWB => sb_decoder_init ModeUWB (sb_decoder_init ModeWB nb_decoder_init_d)
end.

Inductive nb_search_res : Type :=
| NbReturn (r : Z) (b : bits_st ptr)
| NbMode (m : Z) (b : bits_st ptr).

Definition nb_skip_wb_layer (b : bits_st ptr) : M St (bits_st ptr) :=
' (submode, b) <- bits_unpack_unsigned b SB_SUBMODE_BITS ;;
bits_advance b (znth wb_skip_table submode - (SB_SUBMODE_BITS + 1)).

Fixpoint nb_mode_search (fuel : nat) (st : (nb_state ptr)) (b : bits_st ptr) : M St nb_search_res :=
match fuel with
| O => munr
| S fuel' =>
rem <- bits_remaining b ;;
if rem <? 5 then mret (NbReturn (-1) b) else
' (wideband, b) <- bits_unpack_unsigned b 1 ;;
wb <- (if negb (wideband =? 0) then
b <- nb_skip_wb_layer b ;;
rem <- bits_remaining b ;;
if rem <? 5 then mret (inr (NbReturn (-1) b)) else
' (wideband, b) <- bits_unpack_unsigned b 1 ;;
if negb (wideband =? 0) then
b <- nb_skip_wb_layer b ;;
' (wideband, b) <- bits_unpack_unsigned b 1 ;;
if negb (wideband =? 0) then
spx_notify MSG_MORE_THAN_TWO_WB ;;; mret (inr (NbReturn (-2) b))
else mret (inl b)
else mret (inl b)
else mret (inl b)) ;;
match wb with
| inr res => mret res
| inl b =>
rem <- bits_remaining b ;;
if rem <? 4 then mret (NbReturn (-1) b) else
' (m, b) <- bits_unpack_unsigned b 4 ;;
if m =? 15 then mret (NbReturn (-1) b)
else if m =? 14 then
' (ret, b) <- speex_inband_handler b (nb_stereo_cb st) ;;
if negb (ret =? 0) then mret (NbReturn ret b) else nb_mode_search fuel' st b
else if m =? 13 then
' (ret, b) <- speex_default_user_handler b ;;
if negb (ret =? 0) then mret (NbReturn ret b) else nb_mode_search fuel' st b
else if 8 <? m then
spx_notify MSG_INVALID_MODE ;;; mret (NbReturn (-2) b)
else mret (NbMode m b)
end
end.

Definition nb_search_fuel (b : bits_st ptr) : nat := S (S (Z.to_nat (sb_nbBits b))).

Fixpoint voc_loop (fuel : nat) (v ol_pitch : Z) : option Z :=
match fuel with
| O => None
| S fuel' => if v <? NB_SUBFRAME_SIZE then voc_loop fuel' (v + ol_pitch) ol_pitch else Some v
end.
Definition VOC_FUEL : nat := 64%nat.

Definition nb_pit_min (sm : submode) (ol_pitch : Z) : Z :=
if negb (sm_lbr_pitch sm =? -1) then
let margin := sm_lbr_pitch sm in
if negb (margin =? 0) then
(let pit_min := ol_pitch - margin + 1 in if pit_min <? NB_PITCH_START then NB_PITCH_START else pit_min)
else ol_pitch
else NB_PITCH_START.
Definition nb_pit_max (sm : submode) (ol_pitch : Z) : Z :=
if negb (sm_lbr_pitch sm =? -1) then
let margin := sm_lbr_pitch sm in
if negb (margin =? 0) then
(let pit_max := ol_pitch + margin in if NB_PITCH_END <? pit_max then NB_PITCH_END else pit_max)
else ol_pitch
else NB_PITCH_END.

Definition nb_decode_subframe (sm : submode) (ol_pitch : Z) (sub : Z) (st : (nb_state ptr)) (b : bits_st ptr)
: M St ((nb_state ptr) * bits_st ptr) :=
let pit_min := nb_pit_min sm ol_pitch in
' (pitch, b) <- (match sm_ltp_unquant sm with
| Some k => ltp_unquant k pit_min b
| None => munr
end) ;;
b <- (if sm_have_subframe_gain sm =? 3 then ' (q_energy, b) <- bits_unpack_unsigned b 3 ;; mret b
else if sm_have_subframe_gain sm =? 1 then ' (q_energy, b) <- bits_unpack_unsigned b 1 ;; mret b
else mret b) ;;
b <- (match sm_innovation_unquant sm with
| Some k => innovation_unquant k b
| None => munr
end) ;;
b <- (if negb (sm_double_codebook sm =? 0) then
match sm_innovation_unquant sm with
| Some k => innovation_unquant k b
| None => munr
end
else mret b) ;;
st <- (if nb_submodeID st =? 1 then
match voc_loop VOC_FUEL (nb_voc_offset st) ol_pitch with
| Some v => mret (set_nb_voc_offset st (v - NB_SUBFRAME_SIZE))
| None => munr
end
else mret st) ;;
mret (st, b).

Fixpoint nb_decode_subframes (n : nat) (sub : Z) (sm : submode) (ol_pitch : Z) (st : (nb_state ptr)) (b : bits_st ptr)
: M St ((nb_state ptr) * bits_st ptr) :=
match n with
| O => mret (st, b)
| S n' =>
' (st, b) <- nb_decode_subframe sm ol_pitch sub st b ;;
nb_decode_subframes n' (sub + 1) sm ol_pitch st b
end.

Definition nb_decode (st : (nb_state ptr)) (b : bits_st ptr) : M St (Z * (nb_state ptr) * bits_st ptr) :=
sr <- (if negb (nb_encode_submode st =? 0) then nb_mode_search (nb_search_fuel b) st b
else mret (NbMode (nb_submodeID st) b)) ;;
match sr with
| NbReturn r b => mret (r, st, b)
| NbMode m b =>
let st := set_nb_submodeID st m in
match submode_at nb_submodes (nb_submodeID st) with
| None =>

mret (0, set_nb_count_lost (set_nb_first st 1) 0, b)
| Some sm =>
b <- lsp_unquant (sm_lsp_unquant sm) b ;;
' (ol_pitch, b) <- (if negb (sm_lbr_pitch sm =? -1) then
' (p, b) <- bits_unpack_unsigned b 7 ;; mret (NB_PITCH_START + p, b)
else mret (0, b)) ;;
b <- (if negb (sm_forced_pitch_gain sm =? 0) then
' (quant, b) <- bits_unpack_unsigned b 4 ;; mret b
else mret b) ;;
' (qe, b) <- bits_unpack_unsigned b 5 ;;
' (st, b) <- (if nb_submodeID st =? 1 then
' (extra, b) <- bits_unpack_unsigned b 4 ;;
mret (set_nb_dtx_enabled st (if extra =? 15 then 1 else 0), b)
else mret (st, b)) ;;
let st := if 1 <? nb_submodeID st then set_nb_dtx_enabled st 0 else st in
' (st, b) <- nb_decode_subframes 4%nat 0 sm ol_pitch st b ;;

let idx := nb_pitch_gain_buf_idx st + 1 in
let st := set_nb_pitch_gain_buf_idx (set_nb_count_lost (set_nb_first st 0) 0)
(if 2 <? idx then 0 else idx) in
mret (0, st, b)
end
end.

Definition sb_decode_subframe (sm : submode) (b : bits_st ptr) : M St (bits_st ptr) :=
match sm_innovation_unquant sm with
| None => ' (quant, b) <- bits_unpack_unsigned b 5 ;; mret b
| Some k =>
' (qgc, b) <- bits_unpack_unsigned b 4 ;;
b <- innovation_unquant k b ;;
if negb (sm_double_codebook sm =? 0) then innovation_unquant k b else mret b
end.

Fixpoint sb_decode_subframes (n : nat) (sm : submode) (b : bits_st ptr) : M St (bits_st ptr) :=
match n with
| O => mret b
| S n' => b <- sb_decode_subframe sm b ;; sb_decode_subframes n' sm b
end.

Definition sb_decode (st : (sbd_state ptr)) (low : (dec_state ptr))
(low_decode : (dec_state ptr) -> bits_st ptr -> Z -> M St (Z * (dec_state ptr) * bits_st ptr))
(b : bits_st ptr) (out : Z) : M St (Z * ((sbd_state ptr) * (dec_state ptr)) * bits_st ptr) :=
let '(_, low) := speex_decoder_ctl low (CtlSetInnovationSave (out + sbd_frame_size st)) in
' (ret, low, b) <- low_decode low b out ;;
let '(dtx, low) := speex_decoder_ctl low CtlGetDtxStatus in
if negb (ret =? 0) then mret (ret, (st, low), b) else
sr <- (if negb (sbd_encode_submode st =? 0) then
rem <- bits_remaining b ;;
' (wideband, b) <- (if 0 <? rem then bits_peek b else mret (0, b)) ;;
' (st, b) <- (if negb (wideband =? 0) then
' (wideband, b) <- bits_unpack_unsigned b 1 ;;
' (id, b) <- bits_unpack_unsigned b SB_SUBMODE_BITS ;;
mret (set_sbd_submodeID st id, b)
else mret (set_sbd_submodeID st 0, b)) ;;
if negb (sbd_submodeID st =? 0) &&
match submode_at (sbm_submodes (sbd_mode st)) (sbd_submodeID st) with None => true | Some _ => false end
then spx_notify MSG_INVALID_MODE ;;; mret (inr (st, b))
else mret (inl (st, b))
else mret (inl (st, b))) ;;
match sr with
| inr (st, b) => mret (-2, (st, low), b)
| inl (st, b) =>
match submode_at (sbm_submodes (sbd_mode st)) (sbd_submodeID st) with
| None =>

mret (0, (set_sbd_first st 1, low), b)
| Some sm =>
let '(_, low) := speex_decoder_ctl low CtlGetPiGain in
let '(_, low) := speex_decoder_ctl low CtlGetExc in
b <- lsp_unquant (sm_lsp_unquant sm) b ;;
b <- sb_decode_subframes (Z.to_nat (sbd_nbSubframes st)) sm b ;;
mret (0, (set_sbd_first st 0, low), b)
end
end.

Fixpoint dec_depth (d : dec_state ptr) : nat :=
match d with DecNB _ => 1%nat | DecSB _ low => S (dec_depth low) end.

Fixpoint speex_decode_n (n : nat) (d : dec_state ptr) (b : bits_st ptr) (out : Z) : M St (Z * dec_state ptr * bits_st ptr) :=
match n with
| O => munr
| S n' =>
match d with
| DecNB st => ' (r, st, b) <- nb_decode st b ;; mret (r, DecNB st, b)
| DecSB st low =>
' (r, sl, b) <- sb_decode st low (speex_decode_n n') b out ;;
let '(st', low') := sl in mret (r, DecSB st' low', b)
end
end.
Definition speex_decode (d : dec_state ptr) (b : bits_st ptr) (out : Z) : M St (Z * dec_state ptr * bits_st ptr) :=
speex_decode_n (dec_depth d) d b out.
Definition speex_decode_native := speex_decode.

End SpxDecode.

Section Canonical.
Context {St ptr : Type}.
Definition bits_unpack_unsigned_M (b : bits_st ptr) (n : Z) : M St (Z * bits_st ptr) :=
mret (speex_bits_unpack_unsigned b n).
Definition bits_peek_M (b : bits_st ptr) : M St (Z * bits_st ptr) := mret (speex_bits_peek b).
Definition bits_advance_M (b : bits_st ptr) (n : Z) : M St (bits_st ptr) := mret (speex_bits_advance b n).
Definition bits_remaining_M (b : bits_st ptr) : M St Z := mret (speex_bits_remaining b).
End Canonical.

Lemma nb_submodes_complete : forall i sm,
submode_at nb_submodes i = Some sm -> sm_ltp_unquant sm <> None /\ sm_innovation_unquant sm <> None.
Proof.
intros i sm H. unfold submode_at in H.
destruct (i <? 0); [discriminate|].
destruct (Z.to_nat i) as [|[|[|[|[|[|[|[|[|n]]]]]]]]]; cbn in H; try discriminate;
try (inversion H; subst; cbn; split; discriminate).

do 7 (destruct n as [|n]; [cbn in H; discriminate|]). cbn in H.
destruct n; cbn in H; [discriminate|]. destruct n; discriminate.
Qed.

Lemma speex_decoder_ctl_depth : forall {ptr} (d : dec_state ptr) r,
dec_depth (snd (speex_decoder_ctl d r)) = dec_depth d.
Proof.
induction d as [st|st low IH]; intros r; cbn.
- destruct (nb_decoder_ctl st r); reflexivity.
- assert (G : forall q, dec_depth (snd (speex_decoder_ctl low q)) = dec_depth low) by (intros q; apply IH).
destruct r; cbn; try reflexivity;
match goal with
| |- context [speex_decoder_ctl low ?q] =>
generalize (G q); destruct (speex_decoder_ctl low q) as [v' low']; cbn; intros E; rewrite E; reflexivity
end.
Qed.

Lemma voc_loop_step : forall fuel v ol,
voc_loop (S fuel) v ol = if v <? NB_SUBFRAME_SIZE then voc_loop fuel (v + ol) ol else Some v.
Proof. reflexivity. Qed.

Lemma voc_loop_inv : forall v ol,
0 <= v <= 143 -> 17 <= ol <= 144 ->
exists v', voc_loop VOC_FUEL v ol = Some v' /\ 0 <= v' - NB_SUBFRAME_SIZE <= 143.
Proof.
intros v ol Hv Hol. unfold VOC_FUEL.
rewrite voc_loop_step; unfold NB_SUBFRAME_SIZE. destruct (Z.ltb_spec v 40); [|exists v; split; [reflexivity|lia]].
rewrite voc_loop_step; unfold NB_SUBFRAME_SIZE. destruct (Z.ltb_spec (v + ol) 40); [|exists (v + ol); split; [reflexivity|lia]].
rewrite voc_loop_step; unfold NB_SUBFRAME_SIZE. destruct (Z.ltb_spec (v + ol + ol) 40); [|exists (v + ol + ol); split; [reflexivity|lia]].
rewrite voc_loop_step; unfold NB_SUBFRAME_SIZE. destruct (Z.ltb_spec (v + ol + ol + ol) 40); [lia|].
exists (v + ol + ol + ol); split; [reflexivity|lia].
Qed.

