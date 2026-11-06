(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2.
Import ListNotations.
Open Scope Z_scope.

Definition NB_ORDER : Z := 10.
Definition NB_FRAME_SIZE : Z := 160.
Definition NB_SUBFRAME_SIZE : Z := 40.
Definition NB_NB_SUBFRAMES : Z := 4.
Definition NB_PITCH_START : Z := 17.
Definition NB_PITCH_END : Z := 144.
Definition NB_DEC_BUFFER : Z := 500.
Definition NB_EXC_OFFSET : Z := 334.
Definition NB_SUBMODES : Z := 16.
Definition NB_SUBMODE_BITS : Z := 4.
Definition SB_SUBMODES : Z := 8.
Definition SB_SUBMODE_BITS : Z := 3.
Definition QMF_ORDER : Z := 64.
Definition SPEEX_MAX_CALLBACKS : Z := 16.
Definition SPEEX_INBAND_STEREO : Z := 9.
Definition SPEEX_NB_MODES : Z := 3.

Definition SIZEOF_DECSTATE : Z := 2968.
Definition SIZEOF_SBDECSTATE : Z := 160.

Inductive lsp_kind : Type := LspUnquantLbr | LspUnquantNb | LspUnquantHigh.

Inductive gain_cdbk_id : Type := GainCdbkNb | GainCdbkLbr.
Definition gain_cdbk_size (g : gain_cdbk_id) : Z := match g with GainCdbkNb => 512 | GainCdbkLbr => 128 end.

Record ltp_params : Type := mkLtpParams {
ltp_gain_cdbk : gain_cdbk_id;
ltp_gain_bits : Z;
ltp_pitch_bits : Z }.

Inductive ltp_kind : Type := LtpForcedPitchUnquant | LtpPitchUnquant3tap (p : ltp_params).

Inductive shape_cb_id : Type :=
Exc_5_256_table | Exc_5_64_table | Exc_8_128_table | Exc_10_32_table | Exc_10_16_table | Exc_20_32_table
| Hexc_table | Hexc_10_32_table.
Definition shape_cb_size (t : shape_cb_id) : Z :=
match t with
| Exc_5_256_table => 1280 | Exc_5_64_table => 320 | Exc_8_128_table => 1024 | Exc_10_32_table => 320
| Exc_10_16_table => 160 | Exc_20_32_table => 640 | Hexc_table => 1024 | Hexc_10_32_table => 320
end.

Record split_cb_params : Type := mkSplitCb {
scb_subvect_size : Z;
scb_nb_subvect : Z;
scb_shape_cb : shape_cb_id;
scb_shape_bits : Z;
scb_have_sign : Z }.

Inductive innov_kind : Type := InnovNoiseCodebookUnquant | InnovSplitCbShapeSignUnquant (p : split_cb_params).

Record submode : Type := mkSubmode {
sm_lbr_pitch : Z;
sm_forced_pitch_gain : Z;
sm_have_subframe_gain : Z;
sm_double_codebook : Z;
sm_lsp_unquant : lsp_kind;
sm_ltp_unquant : option ltp_kind;
sm_innovation_unquant : option innov_kind;
sm_comb_gain_pos : bool;
sm_bits_per_frame : Z }.

Definition ltp_params_nb   : ltp_params := mkLtpParams GainCdbkNb 7 7.
Definition ltp_params_vlbr : ltp_params := mkLtpParams GainCdbkLbr 5 0.
Definition ltp_params_lbr  : ltp_params := mkLtpParams GainCdbkLbr 5 7.
Definition ltp_params_med  : ltp_params := mkLtpParams GainCdbkLbr 5 7.

Definition split_cb_nb_vlbr : split_cb_params := mkSplitCb 10 4 Exc_10_16_table 4 0.
Definition split_cb_nb_ulbr : split_cb_params := mkSplitCb 20 2 Exc_20_32_table 5 0.
Definition split_cb_nb_lbr  : split_cb_params := mkSplitCb 10 4 Exc_10_32_table 5 0.
Definition split_cb_nb      : split_cb_params := mkSplitCb 5 8 Exc_5_64_table 6 0.
Definition split_cb_nb_med  : split_cb_params := mkSplitCb 8 5 Exc_8_128_table 7 0.
Definition split_cb_sb      : split_cb_params := mkSplitCb 5 8 Exc_5_256_table 8 0.
Definition split_cb_high    : split_cb_params := mkSplitCb 8 5 Hexc_table 7 1.
Definition split_cb_high_lbr: split_cb_params := mkSplitCb 10 4 Hexc_10_32_table 5 0.

Definition nb_submode1 : submode :=
mkSubmode 0 1 0 0 LspUnquantLbr (Some LtpForcedPitchUnquant) (Some InnovNoiseCodebookUnquant) false 43.
Definition nb_submode8 : submode :=
mkSubmode 0 1 0 0 LspUnquantLbr (Some LtpForcedPitchUnquant) (Some (InnovSplitCbShapeSignUnquant split_cb_nb_ulbr)) true 79.
Definition nb_submode2 : submode :=
mkSubmode 0 0 0 0 LspUnquantLbr (Some (LtpPitchUnquant3tap ltp_params_vlbr)) (Some (InnovSplitCbShapeSignUnquant split_cb_nb_vlbr)) true 119.
Definition nb_submode3 : submode :=
mkSubmode (-1) 0 1 0 LspUnquantLbr (Some (LtpPitchUnquant3tap ltp_params_lbr)) (Some (InnovSplitCbShapeSignUnquant split_cb_nb_lbr)) true 160.
Definition nb_submode4 : submode :=
mkSubmode (-1) 0 1 0 LspUnquantLbr (Some (LtpPitchUnquant3tap ltp_params_med)) (Some (InnovSplitCbShapeSignUnquant split_cb_nb_med)) true 220.
Definition nb_submode5 : submode :=
mkSubmode (-1) 0 3 0 LspUnquantNb (Some (LtpPitchUnquant3tap ltp_params_nb)) (Some (InnovSplitCbShapeSignUnquant split_cb_nb)) true 300.
Definition nb_submode6 : submode :=
mkSubmode (-1) 0 3 0 LspUnquantNb (Some (LtpPitchUnquant3tap ltp_params_nb)) (Some (InnovSplitCbShapeSignUnquant split_cb_sb)) true 364.
Definition nb_submode7 : submode :=
mkSubmode (-1) 0 3 1 LspUnquantNb (Some (LtpPitchUnquant3tap ltp_params_nb)) (Some (InnovSplitCbShapeSignUnquant split_cb_nb)) true 492.

Definition wb_submode1 : submode := mkSubmode 0 0 1 0 LspUnquantHigh None None false 36.
Definition wb_submode2 : submode := mkSubmode 0 0 1 0 LspUnquantHigh None (Some (InnovSplitCbShapeSignUnquant split_cb_high_lbr)) false 112.
Definition wb_submode3 : submode := mkSubmode 0 0 1 0 LspUnquantHigh None (Some (InnovSplitCbShapeSignUnquant split_cb_high)) false 192.
Definition wb_submode4 : submode := mkSubmode 0 0 1 1 LspUnquantHigh None (Some (InnovSplitCbShapeSignUnquant split_cb_high)) false 352.

Definition nb_submodes : list (option submode) :=
[None; Some nb_submode1; Some nb_submode2; Some nb_submode3; Some nb_submode4; Some nb_submode5;
Some nb_submode6; Some nb_submode7; Some nb_submode8; None; None; None; None; None; None; None].
Definition wb_submodes : list (option submode) :=
[None; Some wb_submode1; Some wb_submode2; Some wb_submode3; Some wb_submode4; None; None; None].
Definition uwb_submodes : list (option submode) :=
[None; Some wb_submode1; None; None; None; None; None; None].

Definition submode_at (tbl : list (option submode)) (i : Z) : option submode :=
if i <? 0 then None else nth (Z.to_nat i) tbl None.

Definition NB_DEFAULT_SUBMODE : Z := 5.

Definition wb_skip_table : list Z := [0; 36; 112; 192; 352; 0; 0; 0].

Inductive spx_mode : Type := ModeNB | ModeWB | ModeUWB.

Definition mode_id (m : spx_mode) : Z := match m with ModeNB => 0 | ModeWB => 1 | ModeUWB => 2 end.
Definition mode_bitstream_version (m : spx_mode) : Z := 4.
Definition spx_mode_eqb (a b : spx_mode) : bool := mode_id a =? mode_id b.

Definition speex_lib_get_mode (mode : Z) : option spx_mode :=
if (mode <? 0) || (SPEEX_NB_MODES <=? mode) then None
else if mode =? 0 then Some ModeNB else if mode =? 1 then Some ModeWB else Some ModeUWB.

Definition sbm_nb_mode (m : spx_mode) : spx_mode :=
match m with ModeUWB => ModeWB | _ => ModeNB end.
Definition sbm_frameSize (m : spx_mode) : Z := match m with ModeUWB => 320 | _ => 160 end.
Definition sbm_subframeSize (m : spx_mode) : Z := match m with ModeUWB => 80 | _ => 40 end.
Definition sbm_lpcSize (m : spx_mode) : Z := 8.
Definition sbm_defaultSubmode (m : spx_mode) : Z := match m with ModeUWB => 1 | _ => 3 end.
Definition sbm_submodes (m : spx_mode) : list (option submode) :=
match m with ModeUWB => uwb_submodes | _ => wb_submodes end.

Definition mode_frame_size (m : spx_mode) : Z := match m with ModeNB => 160 | ModeWB => 320 | ModeUWB => 640 end.

Lemma split_cb_tables_exact :
Forall (fun p => shape_cb_size (scb_shape_cb p) = 2 ^ (scb_shape_bits p) * scb_subvect_size p
/\ scb_subvect_size p * scb_nb_subvect p = 40)
[split_cb_nb_vlbr; split_cb_nb_ulbr; split_cb_nb_lbr; split_cb_nb; split_cb_nb_med; split_cb_sb;
split_cb_high; split_cb_high_lbr].
Proof. repeat constructor; cbn; lia. Qed.

Lemma ltp_tables_exact :
Forall (fun p => gain_cdbk_size (ltp_gain_cdbk p) = 4 * 2 ^ (ltp_gain_bits p) /\ 0 <= ltp_pitch_bits p <= 7)
[ltp_params_nb; ltp_params_vlbr; ltp_params_lbr; ltp_params_med].
Proof. repeat constructor; cbn; lia. Qed.

Lemma wb_skip_table_nonneg : Forall (fun x => 0 <= x) wb_skip_table.
Proof. repeat constructor; cbn; lia. Qed.

Lemma nb_submodes_length : zlength nb_submodes = NB_SUBMODES.
Proof. reflexivity. Qed.
Lemma wb_submodes_length : zlength wb_submodes = SB_SUBMODES /\ zlength uwb_submodes = SB_SUBMODES.
Proof. split; reflexivity. Qed.
