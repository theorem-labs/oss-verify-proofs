(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 440 of its 488 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_ctrl_build_asG.v, with its module paths and module names changed; 210 of its 278 lines of code are new or changed and 420 lines of the source are left out. *)
(* fuzz_ctrl image A, ctrl_emit_as (0x849d8): the part of a Theorem Labs lane's cgif-form glue that gives the facts about
   the IMAGE OBJECTS the lifted stretch reads, at the call state (W, memc) of `tctrl_emit_as_spec`:
     f  = VAL (A_OBJ A_FRAMES) + ROW_BYTES * r   row r of CTRL_FRAMES, 24 bytes, 3 <= r <= 9;
     md = VAL (A_OBJ A_CAT) + CAT_BYTES * i      a BOX_CATALOGUE entry, 296 bytes, 0 <= i < 11;
     s  = VAL (A_OBJ A_BOX)                      round_trip.box, 6 bytes, a registered global;
   and the two 32-byte JOIN blocks the catalogue arm copies (reac_box_model_block_c.JOIN_0014 when the row's kind
   is 5, JOIN_0013 when it is 6).

   Each lemma gives one hypothesis of A/Prog/ctrl_emit_asF2.v `Section Emit` (the name in brackets), in the form
   of ctrl's lib.Lib run world (`bytes_at`, `addressable`) or in the visibility form that A/ProgBridge.v
   `rng_of_visible` and A/Prog/GEbase.v `sh_cov_rng` turn into the footprint premises of RNG := RNG_W (w_H W):
     ge_row_bytes [HR]   ge_md_bytes [HM]    ge_sb_bytes [HSb]
     ge_row_addr  [Af]   ge_md_addr  [Amd]   ge_sb_addr  [As]
     ge_row_vis   [RROW] ge_md_vis   [RMD]   ge_sb_vis   [RSB]
     ge_row_shcov [RROWS] ge_md_shcov [RMDS] ge_sb_shcov [RSBS]
     ge_j14_addr  [AJ14] ge_j13_addr [AJ13]  ge_j14_shcov [RJ14S] ge_j13_shcov [RJ13S].
   Their premises are copied from A/Prog/C_ctrl_emit_as.v: the binders of `pb_ctrl_emit_as_stmt` (:183-196) and
   the premises of `tctrl_emit_as_spec` (:129-160) at rlo := RLO, rhi := RHI.

   The two JOIN blocks: the statement has no binder that marks their bytes usable (their shadow bytes zero), so
   ge_j14_addr / ge_j13_addr take that binder themselves, in the form A/Prog/C_reac_box_model_block.v:216-217
   states it (HZS_J13, HZS_J14). Their shadow covers need only img_shadow_vis.

   The step from the core's world to lib.Lib. A byte the world view `aview SEGS (w_H W) memc` reads at an address
   outside the segments is a visible byte of memc (Reusable/YA0o.v mbyte_mrestrict_some: a hidden byte reads the
   segments' rom, which holds nothing there), and every byte it reads is the byte lib.Lib's `mrd rsegs memc`
   reads (`ge_mrd`). So a `garr8` over `mrestrict (w_H W) memc` is a `bytes_at rsegs memc`, a
   `range_addressable` of the world view is an `addressable memc`, and a `shadow_hull_vis` of the world view is a
   visible shadow cover.

   Memory-checking runtime: before each load or store the code loads a shadow byte at (a >> 3) + 0x7fff8000 and
   compares it; with the range addressable the check passes and the error path is not reached.

   Glue closure rule (two Theorem Labs lanes, 2026-10-28 23:38Z): no _F file is Required here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
(* the glue's import mix: GEbase.v Exports the core / PA stack and ctrl's lib.Lib run world *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase.
(* this file's own: the JOIN objects' names (A_JOIN_0013, A_JOIN_0014), their numerals, ctrl's row model (ly_k)
   and ProgBridge's image bounds, the last three qualified *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import C_reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_model_block_c ImgBounds.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).

(* ---------------------------------------------------------------------------------------------------------
   From the core's world view to ctrl's lib.Lib memory, for a range of the image. *)

(* lib.Lib's read of memc is the core's mbyte of memc: both read memc, then the segments' rom. *)
Lemma ge_mrd : forall (m : word -> option byte) x, mrd rsegs m (wa x) = mbyte SEGS m x.
Proof. intros m x. reflexivity. Qed.

(* A byte the world view reads is a visible byte, and lib.Lib reads the same byte. *)
Lemma ge_aview_some : forall (W : world SEGS) (memc : word -> option byte) a,
  aview SEGS (w_H W) memc a <> None ->
  w_H W (Z_to_bv 64 a) = false /\
  exists b, mrd rsegs memc (wa a) = Some b /\ aview SEGS (w_H W) memc a = Some (bv_unsigned b).
Proof.
  intros W memc a Ha. unfold aview in *.
  destruct (mbyte SEGS (mrestrict (w_H W) memc) a) as [b|] eqn:E; [| exfalso; exact (Ha eq_refl)].
  destruct (mbyte_mrestrict_some SEGS (w_H W) memc a b (w_Hoff W) E) as [E' Hv].
  split; [exact Hv|]. exists b. split; [rewrite ge_mrd; exact E' | reflexivity].
Qed.

(* A byte below 128 reads back as the same signed value. *)
Lemma ge_sbyte_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128.
  rewrite Z.mod_small by lia. lia.
Qed.

(* garr8 of the world's memory is lib.Lib's bytes_at. *)
Lemma ge_bytes : forall (W : world SEGS) (memc : word -> option byte) a (bs : list byte),
  IMG_LO <= a -> a + Z.of_nat (length bs) <= IMG_HI ->
  garr8 SEGS (mrestrict (w_H W) memc) a (map bv_unsigned bs) -> bytes_at rsegs memc a bs.
Proof.
  intros W memc a bs Ha Hb HG. unfold IMG_LO, IMG_HI in *.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold bytes_at. rewrite P64. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:Eb; [| apply nth_error_None in Eb; lia].
  assert (Hi' : (i < length (map bv_unsigned bs))%nat) by (rewrite length_map; exact Hi).
  destruct (HG i Hi') as [HV Hr].
  assert (En : nth i (map bv_unsigned bs) 0 = bv_unsigned b).
  { apply nth_error_nth. rewrite nth_error_map, Eb. reflexivity. }
  rewrite En in HV, Hr.
  specialize (HV 0%nat ltac:(lia)).
  replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) in HV by lia.
  destruct (mbyte_mrestrict_some SEGS (w_H W) memc _ _ (w_Hoff W) HV) as [E _].
  rewrite ge_mrd, E. f_equal.
  unfold YG0f.le_byte, YO0f.le_byte.
  change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (2 ^ 8) with 256.
  rewrite Z.shiftr_0_r, (Z.mod_small (bv_unsigned b) 256 Hr), (Z.mod_small (bv_unsigned b) 256 Hr).
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* range_addressable of the world view is lib.Lib's addressable. *)
Lemma ge_addr : forall (W : world SEGS) (memc : word -> option byte) a n,
  IMG_LO <= a -> 0 <= n -> a + n <= IMG_HI ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF a n -> addressable memc a n.
Proof.
  intros W memc a n Ha Hn Hb HR. unfold IMG_LO, IMG_HI in *. unfold addressable.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
  intros i Hi. unfold addr_byte. split; [unfold app_mem, LOWMEM_END; left; lia|].
  destruct (HR (a + i) ltac:(lia)) as (s & Hs & Hok).
  destruct (ge_aview_some W memc (shadow_of_addr SHADOW_OFF (a + i)) ltac:(rewrite Hs; discriminate))
    as (_ & b & Eb & Ev).
  rewrite Ev in Hs. injection Hs as Hs.
  exists b.
  replace (shadow_addr (a + i)) with (shadow_of_addr SHADOW_OFF (a + i))
    by (unfold shadow_of_addr, SHADOW_OFF, shadow_addr, ASAN_K; lia).
  split; [exact Eb|].
  unfold shadow_ok. rewrite ge_sbyte_small by (destruct Hok as [Hok | Hok]; lia).
  destruct Hok as [Hok | Hok]; [left | right]; lia.
Qed.

(* A visible shadow hull of the world view is a visible shadow cover of the hidden set (GEbase.sh_cov_vis). *)
Lemma ge_shcov : forall (W : world SEGS) (memc : word -> option byte) a n,
  IMG_LO <= a -> 0 < n -> a + n <= IMG_HI ->
  shadow_hull_vis (aview SEGS (w_H W) memc) a n -> GEbase.sh_cov_vis (w_H W) a (a + n - 1).
Proof.
  intros W memc a n Ha Hn Hb HV x y Hx Hy. unfold IMG_LO, IMG_HI in *.
  unfold shadow_hull_vis, YG0f.shadow_addr, SHADOW_OFF in HV.
  unfold range_visible, shadow_addr, ASAN_K.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity. rewrite P64.
  assert (D1 : a / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : y / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (D3 : (0x7fff8000 + a / 8) / 8 <= (x / 8 + 0x7fff8000) / 8) by (apply Z.div_le_mono; lia).
  assert (D4 : (y / 8 + 0x7fff8000) / 8 <= (0x7fff8000 + (a + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
  assert (D5 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (D6 : 0 <= (x / 8 + 0x7fff8000) / 8) by (apply Z.div_pos; lia).
  assert (D7 : (a + n - 1) / 8 <= a + n) by (apply Z.div_le_upper_bound; lia).
  assert (D8 : 8 * ((0x7fff8000 + (a + n - 1) / 8) / 8) <= 0x7fff8000 + (a + n - 1) / 8)
    by (apply Z.mul_div_le; lia).
  split; [lia|]. split; [lia|].
  intros s Hs. exact (proj1 (ge_aview_some W memc s (HV s ltac:(lia)))).
Qed.

(* A range of the image is visible in every world (A/ProgBridge.v img_vis_W). *)
Lemma ge_vis : forall (W : world SEGS) a n, IMG_LO <= a -> 0 <= n -> a + n <= IMG_HI ->
  range_visible (w_H W) a n.
Proof.
  intros W a n Ha Hn Hb.
  apply (range_visible_sub (w_H W) ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO));
    [exact (img_vis_W W) | | | ]; unfold IMG_LO, IMG_HI, ImgBounds.IMG_LO, ImgBounds.IMG_HI in *; lia.
Qed.

(* A part of a range marked usable is marked usable. *)
Lemma ge_zs_sub : forall B q n a m, in_zs B q n -> q <= a -> a + m <= q + n -> in_zs B a m.
Proof. intros B q n a m (q0 & m0 & Hin & H1 & H2) Ha Hb. exists q0, m0. split; [exact Hin | lia]. Qed.

(* The numerals of the two JOIN objects (CtrlAddr.v:98-99 = reac_box_model_block_c.v:17-18). *)
Lemma ge_val_j13 : VAL (A_OBJ A_JOIN_0013) = reac_box_model_block_c.JOIN_0013.
Proof. reflexivity. Qed.
Lemma ge_val_j14 : VAL (A_OBJ A_JOIN_0014) = reac_box_model_block_c.JOIN_0014.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------
   The facts at the call, from the statement's binders and premises. *)
Section e.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Variables RLO RHI : Z.

(* ---- [HR] the row's 24 bytes ---- *)
Lemma ge_row_bytes :
  forall (HROWS : forall r, 3 <= r <= 9 -> forall (H : word -> bool) mem,
            arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
            garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (map bv_unsigned (CROW r)))
    (HFR_rng : IMG_LO + 64 <= VAL (A_OBJ A_FRAMES) /\ VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES + 64 <= IMG_HI)
    (W : world SEGS) (memc : word -> option byte) (r : Z),
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  3 <= r <= 9 ->
  bytes_at rsegs memc (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (CROW r).
Proof.
  intros HROWS HFR_rng W memc r HRO Hr.
  apply (ge_bytes W memc _ _);
    [| change (length (CROW r)) with 24%nat | exact (HROWS r Hr (w_H W) memc HRO)];
    unfold ROW_BYTES in *; lia.
Qed.

(* ---- [HM] the catalogue entry's 296 bytes ---- *)
Lemma ge_md_bytes :
  forall (HCAT_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI)
    (W : world SEGS) (memc : word -> option byte) (md i : Z) (mb : list byte),
  md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->
  garr8 SEGS (mrestrict (w_H W) memc) md (map bv_unsigned mb) -> length mb = 296%nat ->
  bytes_at rsegs memc md mb.
Proof.
  intros HCAT_rng W memc md i mb Hmd Hi HG Hl.
  apply (ge_bytes W memc _ _ ); [| | exact HG]; rewrite ?Hl; unfold CAT_BYTES in *; lia.
Qed.

(* ---- [HSb] round_trip.box's 6 bytes ---- *)
Lemma ge_sb_bytes :
  forall (HBOX_rng : IMG_LO + 64 <= VAL (A_OBJ A_BOX) /\ VAL (A_OBJ A_BOX) + 6 + 64 <= IMG_HI)
    (W : world SEGS) (memc : word -> option byte) (sb : list byte),
  length sb = 6%nat ->
  garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ A_BOX)) (map bv_unsigned sb) ->
  bytes_at rsegs memc (VAL (A_OBJ A_BOX)) sb.
Proof.
  intros HBOX_rng W memc sb Hl HG.
  apply (ge_bytes W memc _ _); [| | exact HG]; rewrite ?Hl; lia.
Qed.

(* ---- [Af] the row is addressable ---- *)
Lemma ge_row_addr :
  forall (HGM : globs_marked SEGS B GLOBS)
    (HFR_glob : In (VAL (A_OBJ A_FRAMES), 11 * ROW_BYTES) GLOBS)
    (HFR_rng : IMG_LO + 64 <= VAL (A_OBJ A_FRAMES) /\ VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES + 64 <= IMG_HI)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (r : Z),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  3 <= r <= 9 ->
  addressable memc (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) 24.
Proof.
  intros HGM HFR_glob HFR_rng STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k r HJ Hr.
  destruct HJ as [HAR _].
  apply (ge_addr W memc); [unfold ROW_BYTES in *; lia | lia | unfold ROW_BYTES in *; lia |].
  apply (ro_usable_glob SEGS B GLOBS lyc Sc W memc mdc (VAL (A_OBJ A_FRAMES)) (11 * ROW_BYTES) _ _
           HGM HFR_glob HAR); unfold ROW_BYTES in *; lia.
Qed.

(* ---- [Amd] the catalogue entry is addressable ---- *)
Lemma ge_md_addr :
  forall (HGM : globs_marked SEGS B GLOBS)
    (HCAT_glob : In (VAL (A_OBJ A_CAT), 11 * CAT_BYTES) GLOBS)
    (HCAT_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (md i : Z),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->
  addressable memc md 296.
Proof.
  intros HGM HCAT_glob HCAT_rng STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k md i HJ Hmd Hi.
  destruct HJ as [HAR _]. subst md.
  apply (ge_addr W memc); [unfold CAT_BYTES in *; lia | lia | unfold CAT_BYTES in *; lia |].
  apply (ro_usable_glob SEGS B GLOBS lyc Sc W memc mdc (VAL (A_OBJ A_CAT)) (11 * CAT_BYTES) _ _
           HGM HCAT_glob HAR); unfold CAT_BYTES in *; lia.
Qed.

(* ---- [As] round_trip.box is addressable: a registered global of 6 bytes ---- *)
Lemma ge_sb_addr :
  forall (HGM : globs_marked SEGS B GLOBS)
    (HBOX_glob : In (VAL (A_OBJ A_BOX), 6) GLOBS)
    (HBOX_rng : IMG_LO + 64 <= VAL (A_OBJ A_BOX) /\ VAL (A_OBJ A_BOX) + 6 + 64 <= IMG_HI)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  addressable memc (VAL (A_OBJ A_BOX)) 6.
Proof.
  intros HGM HBOX_glob HBOX_rng STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ.
  destruct HJ as [HAR _].
  apply (ge_addr W memc); [lia | lia | lia |].
  apply (ro_usable_glob SEGS B GLOBS lyc Sc W memc mdc (VAL (A_OBJ A_BOX)) 6 _ _ HGM HBOX_glob HAR); lia.
Qed.

(* ---- [RROW] [RMD] [RSB] the three objects are visible ---- *)
Lemma ge_row_vis :
  forall (HFR_rng : IMG_LO + 64 <= VAL (A_OBJ A_FRAMES) /\ VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES + 64 <= IMG_HI)
    (W : world SEGS) (r : Z),
  3 <= r <= 9 ->
  range_visible (w_H W) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) 24.
Proof. intros HFR_rng W r Hr. apply ge_vis; unfold ROW_BYTES in *; lia. Qed.

Lemma ge_md_vis :
  forall (HCAT_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI)
    (W : world SEGS) (md i : Z),
  md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->
  range_visible (w_H W) md 296.
Proof. intros HCAT_rng W md i Hmd Hi. apply ge_vis; unfold CAT_BYTES in *; lia. Qed.

Lemma ge_sb_vis :
  forall (HBOX_rng : IMG_LO + 64 <= VAL (A_OBJ A_BOX) /\ VAL (A_OBJ A_BOX) + 6 + 64 <= IMG_HI)
    (W : world SEGS),
  range_visible (w_H W) (VAL (A_OBJ A_BOX)) 6.
Proof. intros HBOX_rng W. apply ge_vis; lia. Qed.

(* ---- [RROWS] [RMDS] [RSBS] the shadow covers of the three objects are visible ---- *)
Lemma ge_row_shcov :
  forall (HIMGSH : img_shadow_vis SEGS B)
    (HFR_rng : IMG_LO + 64 <= VAL (A_OBJ A_FRAMES) /\ VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES + 64 <= IMG_HI)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (r : Z),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  3 <= r <= 9 ->
  GEbase.sh_cov_vis (w_H W) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 23).
Proof.
  intros HIMGSH HFR_rng STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k r HJ Hr.
  destruct HJ as [HAR _].
  replace (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 23) with (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r + 24 - 1)
    by lia.
  apply (ge_shcov W memc); [unfold ROW_BYTES in *; lia | lia | unfold ROW_BYTES in *; lia |].
  apply (ro_hull SEGS B lyc Sc W memc mdc _ _ HIMGSH HAR); unfold ROW_BYTES in *; lia.
Qed.

Lemma ge_md_shcov :
  forall (HIMGSH : img_shadow_vis SEGS B)
    (HCAT_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (md i : Z),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->
  GEbase.sh_cov_vis (w_H W) md (md + 295).
Proof.
  intros HIMGSH HCAT_rng STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k md i HJ Hmd Hi.
  destruct HJ as [HAR _].
  replace (md + 295) with (md + 296 - 1) by lia.
  apply (ge_shcov W memc); [unfold CAT_BYTES in *; lia | lia | unfold CAT_BYTES in *; lia |].
  apply (ro_hull SEGS B lyc Sc W memc mdc _ _ HIMGSH HAR); unfold CAT_BYTES in *; lia.
Qed.

Lemma ge_sb_shcov :
  forall (HIMGSH : img_shadow_vis SEGS B)
    (HBOX_rng : IMG_LO + 64 <= VAL (A_OBJ A_BOX) /\ VAL (A_OBJ A_BOX) + 6 + 64 <= IMG_HI)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  GEbase.sh_cov_vis (w_H W) (VAL (A_OBJ A_BOX)) (VAL (A_OBJ A_BOX) + 5).
Proof.
  intros HIMGSH HBOX_rng STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ.
  destruct HJ as [HAR _].
  replace (VAL (A_OBJ A_BOX) + 5) with (VAL (A_OBJ A_BOX) + 6 - 1) by lia.
  apply (ge_shcov W memc); [lia | lia | lia |].
  apply (ro_hull SEGS B lyc Sc W memc mdc _ _ HIMGSH HAR); lia.
Qed.

(* [AJ14] [AJ13], the JOIN blocks' addressability, are NOT here. Neither lifted stretch of ctrl_emit_as takes
   them (they are ctrl_lay_block's own run's premises, and that call is the cgif cut), and the only route to
   them was an `in_zs` fact over an image object, which a Theorem Labs lane measured to be FALSE under a Theorem Labs lane's
   corrected zero-shadow list (04:49Z): a registered global's last granule carries its size, not 0. The two
   lemmas that used that route are removed rather than left with a premise nothing can supply. Their shadow
   covers below need no such fact. *)

(* ---- [RJ14S] [RJ13S] the JOIN blocks' shadow covers are visible: the image's shadow is mapped ---- *)
Lemma ge_j14_shcov :
  forall (HIMGSH : img_shadow_vis SEGS B)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (r : Z),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  RcLay.ly_k (CROW r) = 5 ->
  GEbase.sh_cov_vis (w_H W) reac_box_model_block_c.JOIN_0014 (reac_box_model_block_c.JOIN_0014 + 31).
Proof.
  intros HIMGSH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k r HJ _.
  destruct HJ as [HAR _].
  replace (reac_box_model_block_c.JOIN_0014 + 31) with (reac_box_model_block_c.JOIN_0014 + 32 - 1) by lia.
  apply (ge_shcov W memc); [| lia | |]; [unfold reac_box_model_block_c.JOIN_0014, IMG_LO; lia
                                      | unfold reac_box_model_block_c.JOIN_0014, IMG_HI; lia |].
  apply (ro_hull SEGS B lyc Sc W memc mdc _ _ HIMGSH HAR);
    unfold reac_box_model_block_c.JOIN_0014, IMG_LO, IMG_HI; lia.
Qed.

Lemma ge_j13_shcov :
  forall (HIMGSH : img_shadow_vis SEGS B)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (r : Z),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  RcLay.ly_k (CROW r) = 6 ->
  GEbase.sh_cov_vis (w_H W) reac_box_model_block_c.JOIN_0013 (reac_box_model_block_c.JOIN_0013 + 31).
Proof.
  intros HIMGSH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k r HJ _.
  destruct HJ as [HAR _].
  replace (reac_box_model_block_c.JOIN_0013 + 31) with (reac_box_model_block_c.JOIN_0013 + 32 - 1) by lia.
  apply (ge_shcov W memc); [| lia | |]; [unfold reac_box_model_block_c.JOIN_0013, IMG_LO; lia
                                      | unfold reac_box_model_block_c.JOIN_0013, IMG_HI; lia |].
  apply (ro_hull SEGS B lyc Sc W memc mdc _ _ HIMGSH HAR);
    unfold reac_box_model_block_c.JOIN_0013, IMG_LO, IMG_HI; lia.
Qed.

End e.
End b.
