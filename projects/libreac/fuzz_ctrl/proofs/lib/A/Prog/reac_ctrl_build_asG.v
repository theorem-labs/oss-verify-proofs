(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 440 of its 488 lines of code are new or changed and 963 lines of the source are left out. *)
(* fuzz_ctrl image A (ASan build): the glue proof of reac_ctrl_build_as (0x848ac, AF 0x39d0) in the cgif
   caller-journal form, `pb_reac_ctrl_build_as` for A/Prog/C_reac_ctrl_build_as.v `pb_reac_ctrl_build_as_stmt`.

   Route (a), one straight line:
   1. The entry configuration is the start state of the lift ProgLift/reac_ctrl_build_as.v
      `reac_ctrl_build_as_SRr_at_hid` (ProgBridge.cfg_at_MS, Reusable/YA0nR.v SRr_xregs_eqv). Its premises come
      from the spec's premises and binders: reac_box_model_upstream_width runs on its CLOSED contract
      reac_box_model_upstream_widthF.reac_box_model_upstream_width_F_holds; asan_cells / shadow_rw / ro_agree at
      the entry are A/ProgWorldCtlRt.v `ctlrt_of_AR` at the journal's AR; the switch table and the catalogue entry
      are addressable as registered globals (CtrlRo.ro_usable_glob over HGM, HSW_glob, HCAT_glob); the window is
      present by the journal; the image shadow is visible by HIMGSH.
   2. The stretch's post has go = true (o > 0, md > 0, kind <= 6), so the state is at ctrl_emit_as (0x849d8) with
      memory mu, where `munch [(sp - 4640, sp)] memc mu`.
   3. The caller's journal at mu: GE_jrnl.ge_jrnl (a Theorem Labs lane 8b1bb6bdd1e, taken by path); the read-only data at mu:
      GE_jrnl.ge_ro_keep. build_as logs no event and takes no side-stack frame, so k and Sc do not change.
   4. TEMIT (tctrl_emit_as_spec) at the jump state. Every premise about the world's memory moves from memc to mu
      because each of those bytes lies below the window (frames and blocks below alloc_ceiling, the image, the
      shadow band). Its post is treac_ctrl_build_as_post up to the regs and memory arguments: the jump registers
      agree with the entry registers on ra, sp, gp, tp, s0-s11, and tcj_kept over mu becomes tcj_kept over memc
      because TEMIT_STK = 4640 covers the window [sp - 4640, sp) the stretch writes.

   Section hypotheses (a Theorem Labs lane 05:3xZ): ProgWorld's AR_states_vis0_shadow and AR_states_owned_ro, and
   `TSYMS : A.AF0m.CtrlTSyms B` (as a Theorem Labs lane's reac_ctrl_classify_box_frame_glue.v), the premises of ctlrt_of_AR.

   Six-module rule: YI04, YI16, YK11, YK1b, YM05, YO09 are named lib.Reusable.<X> (the core's copy). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase GE_jrnl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import C_reac_ctrl_build_as.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcPorts RcLay RcSynth RcBox reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_build_as_c reac_box_model_upstream_widthF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgLift Require reac_ctrl_build_as.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.ProgWorldCtlRt A.AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldRtRo A.ProgWorldOwnedRo.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).
#[local] Notation getr := lib.Reusable.YK11.getr (only parsing).
#[local] Notation LIFT :=
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgLift.reac_ctrl_build_as.reac_ctrl_build_as_SRr_at_hid
  (only parsing).
#[local] Notation LIFT_ON :=
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgLift.reac_ctrl_build_as.reac_ctrl_build_as_SRr_at_hid_on
  (only parsing).
#[local] Notation POST_RO :=
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgLift.reac_ctrl_build_as.reac_ctrl_build_as_stretch_post_ro
  (only parsing).

(* ---------------------------------------------------------------------------------------------------------
   1. The model and the image constants. *)

Lemma bb_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hz.
Qed.

(* the stretch goes on to ctrl_emit_as *)
Lemma bb_go : forall o md kind, 0 < o -> md <> 0 -> 0 <= kind <= 6 ->
  lib.Prog.reac_ctrl_build_as_c.ba_go o md kind = true.
Proof.
  intros o md kind Ho Hmd Hk. unfold lib.Prog.reac_ctrl_build_as_c.ba_go.
  destruct (Z.eqb_spec o 0) as [E|_]; [lia|]. destruct (Z.eqb_spec md 0) as [E|_]; [lia|].
  destruct (Z.leb_spec kind 6) as [_|E]; [reflexivity | lia].
Qed.

(* the row of each kind is one of CTRL_FRAMES' rows 3 .. 9 *)
Lemma bb_row : forall k, 0 <= k <= 6 -> 3 <= lib.Prog.reac_ctrl_build_as_c.ba_row k <= 9.
Proof.
  intros k Hk. assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
  unfold lib.Prog.reac_ctrl_build_as_c.ba_row.
  destruct E as [->|[->|[->|[->|[->|[->| ->]]]]]]; simpl; lia.
Qed.

Lemma bb_wok : forall w, RcPorts.bm_wok w = true -> 2 <= w <= 40.
Proof.
  intros w H. unfold RcPorts.bm_wok in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* reac_box_model_upstream_width's result n is 0 or an even width in [2, 40] *)
Lemma bb_uw : forall md bs, 0 <= RcPorts.bm_uw md bs <= 40.
Proof.
  intros md bs. unfold RcPorts.bm_uw.
  set (wi := RcPorts.bm_in_ch bs). set (wo := RcPorts.bm_out_ch bs).
  destruct (md =? 0); [lia|].
  destruct ((wi <? 0) || (wo <? 0)) eqn:E1; [lia|].
  apply orb_false_iff in E1 as [E1 _]. apply Z.ltb_ge in E1.
  destruct (wi =? 0) eqn:Ew; cbn [negb andb].
  - apply Z.eqb_eq in Ew. rewrite Ew. destruct (negb (wo =? 0) && negb (RcPorts.bm_wok wo)); lia.
  - destruct (RcPorts.bm_wok wi) eqn:Hw; cbn [negb andb]; [|lia].
    apply bb_wok in Hw. destruct (negb (wo =? 0) && negb (RcPorts.bm_wok wo)); lia.
Qed.

Lemma bb_entry_pc : BASE + AF_reac_ctrl_build_as = 0x848ac.
Proof. vm_compute. reflexivity. Qed.

Lemma bb_emit_pc : BASE + AF_ctrl_emit_as = 0x849d8.
Proof. vm_compute. reflexivity. Qed.

Lemma bb_val_sw : VAL (A_OBJ 20) = 0x21980.
Proof. vm_compute. reflexivity. Qed.

Lemma bb_val_box : VAL (A_OBJ 4) = 0x21140.
Proof. vm_compute. reflexivity. Qed.

(* TEMIT's row argument is the stretch's a1 *)
Lemma bb_frames_row : forall r,
  VAL (A_OBJ C_ctrl_lay_block.A_FRAMES) + C_ctrl_lay_block.ROW_BYTES * r = A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * r.
Proof.
  intros r. assert (E : VAL (A_OBJ 21) = 0x9f7e0) by (vm_compute; reflexivity).
  unfold C_ctrl_lay_block.A_FRAMES, C_ctrl_lay_block.ROW_BYTES. rewrite E. reflexivity.
Qed.

Lemma bb_temit_stk : TEMIT_STK = 4640.
Proof. vm_compute. reflexivity. Qed.

(* The lift's register map, written register by register. *)
Lemma bb_mkR_of : forall regs : bvmap 5 word,
  mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. Below the window the stretch's memory is the entry memory (`munch [(lo, hi)]`). *)

Lemma bb_mem_keep : forall (m m' : word -> option byte) lo hi a,
  munch [(lo, hi)] m m' -> 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m m' lo hi a Hmu Ha Hn. apply Hmu. rewrite (bb_u64 a Ha). cbn [outside]. split; [exact Hn | exact I].
Qed.

Lemma bb_view_keep : forall (H : word -> bool) (m m' : word -> option byte) lo hi a,
  munch [(lo, hi)] m m' -> 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros H m m' lo hi a Hmu Ha Hn. apply (aview_eq_of SEGS). unfold mrestrict.
  rewrite (bb_mem_keep m m' lo hi a Hmu Ha Hn). reflexivity.
Qed.

Lemma bb_garr8_keep : forall (H : word -> bool) (m m' : word -> option byte) lo hi base (l : list Z),
  munch [(lo, hi)] m m' -> 0 <= base -> base + Z.of_nat (length l) <= lo -> lo <= 2 ^ 64 ->
  garr8 SEGS (mrestrict H m) base l -> garr8 SEGS (mrestrict H m') base l.
Proof.
  intros H m m' lo hi base l Hmu H0 H1 H2 HG j Hj.
  destruct (HG j Hj) as [HV Hr]. split; [|exact Hr].
  intros kk Hk. rewrite <- (HV kk Hk). assert (kk = 0%nat) by lia. subst kk.
  unfold mbyte, mrestrict.
  rewrite (bb_mem_keep m m' lo hi (base + Z.of_nat j + Z.of_nat 0) Hmu); [reflexivity | lia | lia].
Qed.

Lemma bb_present_keep : forall (H : word -> bool) (m m' : word -> option byte) lo hi a,
  munch [(lo, hi)] m m' -> 0 <= a < lo -> lo <= 2 ^ 64 -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' lo hi a Hmu Ha Hlo [Hh [b Hb]]. split; [exact Hh|]. exists b.
  rewrite (bb_mem_keep m m' lo hi a Hmu ltac:(lia) ltac:(lia)). exact Hb.
Qed.

Lemma bb_ra_keep : forall (H : word -> bool) (m m' : word -> option byte) lo hi p n,
  munch [(lo, hi)] m m' -> 0x7fff7f800000 <= lo -> lo <= 2 ^ 64 -> 0 <= p -> p + n <= 2 ^ 47 ->
  range_addressable (aview SEGS H m) SHADOW_OFF p n -> range_addressable (aview SEGS H m') SHADOW_OFF p n.
Proof.
  intros H m m' lo hi p n Hmu Hlo Hlo' Hp Hn HR x Hx.
  rewrite (bb_view_keep H m m' lo hi); [exact (HR x Hx) | exact Hmu | |];
    unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia.
Qed.

Lemma bb_hull_keep : forall (H : word -> bool) (m m' : word -> option byte) lo hi p n,
  munch [(lo, hi)] m m' -> 0x7fff7f800000 <= lo -> lo <= 2 ^ 64 -> 0 <= p -> p + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis (aview SEGS H m) p n -> shadow_hull_vis (aview SEGS H m') p n.
Proof.
  intros H m m' lo hi p n Hmu Hlo Hlo' Hp Hn Hn0 HV s Hs.
  rewrite (bb_view_keep H m m' lo hi); [exact (HV s Hs) | exact Hmu | |];
    unfold YG0f.shadow_addr, SHADOW_OFF in Hs; Z.div_mod_to_equations; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   3. Image ranges: from the world's view to ctrl's lib.Lib forms. *)

Lemma bb_aview_some : forall (W : world SEGS) (memc : word -> option byte) a,
  aview SEGS (w_H W) memc a <> None ->
  w_H W (Z_to_bv 64 a) = false /\
  exists b, lib.Lib.Mem.mrd rsegs memc (lib.Lib.Mem.wa a) = Some b /\ aview SEGS (w_H W) memc a = Some (bv_unsigned b).
Proof.
  intros W memc a Ha. unfold aview in *.
  destruct (mbyte SEGS (mrestrict (w_H W) memc) a) as [b|] eqn:E; [| exfalso; exact (Ha eq_refl)].
  destruct (mbyte_mrestrict_some SEGS (w_H W) memc a b (w_Hoff W) E) as [E' Hv].
  split; [exact Hv|]. exists b. split; [exact E' | reflexivity].
Qed.

Lemma bb_sbyte_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma bb_bytes_img : forall (W : world SEGS) (memc : word -> option byte) a (bs : list byte),
  CtrlRo.IMG_LO <= a -> a + Z.of_nat (length bs) <= CtrlRo.IMG_HI ->
  garr8 SEGS (mrestrict (w_H W) memc) a (map bv_unsigned bs) -> lib.Lib.Mem.bytes_at rsegs memc a bs.
Proof.
  intros W memc a bs Ha Hb HG. unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in *.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold lib.Lib.Mem.bytes_at. rewrite P64. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:Eb; [| apply nth_error_None in Eb; lia].
  assert (Hi' : (i < length (map bv_unsigned bs))%nat) by (rewrite length_map; exact Hi).
  destruct (HG i Hi') as [HV Hr].
  assert (En : nth i (map bv_unsigned bs) 0 = bv_unsigned b).
  { apply nth_error_nth. rewrite nth_error_map, Eb. reflexivity. }
  rewrite En in HV, Hr.
  specialize (HV 0%nat ltac:(lia)).
  replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) in HV by lia.
  destruct (mbyte_mrestrict_some SEGS (w_H W) memc _ _ (w_Hoff W) HV) as [E _].
  change (lib.Lib.Mem.mrd rsegs memc (lib.Lib.Mem.wa (a + Z.of_nat i))) with (mbyte SEGS memc (a + Z.of_nat i)).
  rewrite E. f_equal.
  unfold YG0f.le_byte, lib.Reusable.YO0f.le_byte.
  change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (2 ^ 8) with 256.
  rewrite Z.shiftr_0_r, (Z.mod_small (bv_unsigned b) 256 Hr), (Z.mod_small (bv_unsigned b) 256 Hr).
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma bb_addr_img : forall (W : world SEGS) (memc : word -> option byte) a n,
  CtrlRo.IMG_LO <= a -> 0 <= n -> a + n <= CtrlRo.IMG_HI ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF a n -> addressable memc a n.
Proof.
  intros W memc a n Ha Hn Hb HR. unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in *. unfold addressable.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
  intros i Hi. unfold addr_byte. split; [unfold app_mem, LOWMEM_END; left; lia|].
  destruct (HR (a + i) ltac:(lia)) as (s & Hs & Hok).
  destruct (bb_aview_some W memc (shadow_of_addr SHADOW_OFF (a + i)) ltac:(rewrite Hs; discriminate))
    as (_ & b & Eb & Ev).
  rewrite Ev in Hs. injection Hs as Hs.
  exists b.
  replace (AsanRT.shadow_addr (a + i)) with (shadow_of_addr SHADOW_OFF (a + i))
    by (unfold shadow_of_addr, SHADOW_OFF, AsanRT.shadow_addr, ASAN_K; lia).
  split; [exact Eb|].
  unfold shadow_ok. unfold saddr_ok in Hok. rewrite bb_sbyte_small by (destruct Hok as [Hok | Hok]; lia).
  destruct Hok as [Hok | Hok]; [left | right]; lia.
Qed.

(* the image's shadow [0x7fffa000, 0x7fffa000 + 0xbdc00) is visible: img_shadow_vis at the journal's AR *)
Lemma bb_imgsh_vis : forall B ly S (W : world SEGS) memc md,
  img_shadow_vis SEGS B -> AR SEGS B ly S W memc md -> range_visible (w_H W) 0x7fffa000 0xbdc00.
Proof.
  intros B ly S W memc md HIS HAR. unfold range_visible.
  split; [lia|]. split; [lia|]. intros a Ha.
  pose proof (HIS ly S W memc md (8 * (a - 0x7fff8000)) HAR ltac:(unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI; lia)) as Hv.
  match type of Hv with aview _ _ _ ?t <> None =>
    assert (Et : t = a) by (unfold YG0f.shadow_addr, SHADOW_OFF; rewrite Z.mul_comm, Z.div_mul by lia; lia);
    rewrite Et in Hv end.
  exact (proj1 (bb_aview_some W memc a Hv)).
Qed.

(* a non-empty range of image bytes lies in low memory *)
Lemma bb_img_range : forall base len, 0 < len -> (forall x, base <= x < base + len -> lib.Reusable.YG0d.in_img SEGS x) ->
  0 <= base /\ base + len <= 0x7fff8000.
Proof.
  intros base len Hl HI.
  pose proof (ctrl_segs_low base (HI base ltac:(lia))) as L1.
  pose proof (ctrl_segs_low (base + len - 1) (HI (base + len - 1) ltac:(lia))) as L2.
  unfold kLowMemEnd in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   4. The caller's journal: the window, the journal step, the read-only data, tcj_kept. *)

Lemma bb_win : forall B STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k sp,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= sp - 4640 -> sp <= sp0 ->
  range_visible (w_H W) (sp - 4640) 4640 /\ stk rsegs memc (sp - 4640) sp /\
  0x7fff7f800000 <= lib.Reusable.YM05.alloc_ceiling <= sp - 4640 /\ sp <= 2 ^ 47.
Proof.
  intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k sp HJ Hlo Hhi.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & HK & _).
  destruct HK as (_ & _ & HC & HL & HH & H47 & _).
  pose proof asan_consts as (C1 & _).
  split; [|split; [|split; lia]].
  - split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (HP a ltac:(lia))).
  - split; [lia|]. split; [lia|]. intros a Ha. destruct (HP a ltac:(lia)) as [_ [b Hb]]. unfold lib.Lib.Mem.wa. split.
    + unfold wview. rewrite Hb. discriminate.
    + exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

(* The journal across the stretch, which writes only [lo, hi), a part of the caller's window. *)
Lemma bb_jrnl : forall B (LAWS : AR_laws SEGS B) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (mdc' : Model) (m' : word -> option byte) lo hi,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  munch [(lo, hi)] memc m' -> wmono rsegs memc m' ->
  (forall x : word, w_H W x = true -> m' x = memc x) ->
  same_but_materialized mdc mdc' ->
  sp0 - STK <= lo -> hi <= sp0 ->
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m' mdc' k.
Proof.
  intros B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mdc' m' lo hi HJ MU WM HID SAME Hlo Hhi.
  apply (ge_jrnl B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mdc' [(lo, hi)] m' LAWS HJ MU WM HID SAME).
  intros a _ Ho. cbn [outside] in Ho. unfold awr_byte. left.
  destruct (Z.le_gt_cases lo a) as [H1|H1]; [destruct (Z.lt_ge_cases a hi) as [H2|H2]|].
  - lia.
  - exfalso. apply Ho. split; [lia | exact I].
  - exfalso. apply Ho. split; [lia | exact I].
Qed.

Lemma bb_ro : forall B (H : word -> bool) rlo rhi (m m' : word -> option byte) lo hi,
  (forall a, rlo <= a < rhi -> lib.Reusable.YG0d.in_img SEGS a) ->
  arodata_okS SEGS B rlo rhi (aview SEGS H m) -> munch [(lo, hi)] m m' -> 0x7fff8000 <= lo ->
  arodata_okS SEGS B rlo rhi (aview SEGS H m').
Proof.
  intros B H rlo rhi m m' lo hi Hrel Hro MU Hlo.
  apply (ge_ro_keep B H rlo rhi m m' [(lo, hi)] Hrel Hro MU).
  intros a Hi. pose proof (ctrl_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
  cbn [outside]. split; [lia | exact I].
Qed.

(* ctrl_emit_as's tcj_kept over the jump memory mu is the same over the entry memory memc: the two differ only in
   the window [sp - 4640, sp), which tcj_kept excludes (TEMIT_STK = 4640), and every block, frame, frame shadow
   and image byte lies below it. *)
Lemma bb_tcj : forall B (LAWS : AR_laws SEGS B) lyc Sc (W W2 : world SEGS) memc mdc mu mem2 sp (E : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc ->
  lib.Reusable.YM05.alloc_ceiling <= sp - 4640 -> sp <= 2 ^ 47 ->
  munch [(sp - 4640, sp)] memc mu ->
  tcj_kept (PI := PI_ctrl) B TEMIT_STK lyc Sc W mu W2 mem2 sp E ->
  tcj_kept (PI := PI_ctrl) B TEMIT_STK lyc Sc W memc W2 mem2 sp E.
Proof.
  intros B LAWS lyc Sc W W2 memc mdc mu mem2 sp E HAR Hlo Hhi MU HK.
  unfold tcj_kept in *. rewrite bb_temit_stk in *.
  repeat match goal with |- context [@pa_segs ?g ?L ?P] => change (@pa_segs g L P) with SEGS end.
  repeat match goal with Hx : context [@pa_segs ?g ?L ?P] |- _ => change (@pa_segs g L P) with SEGS in Hx end.
  destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof asan_consts as (C1 & _).
  assert (VK : forall a, 0 <= a < sp - 4640 -> aview SEGS (w_H W) mu a = aview SEGS (w_H W) memc a)
    by (intros a Ha; apply (bb_view_keep _ memc mu (sp - 4640) sp); [exact MU | lia | lia]).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw HE. rewrite (K1 a Ha Hw HE).
    apply (bb_view_keep _ memc mu (sp - 4640) sp); [exact MU | lia | exact Hw].
  - intros b m i Hin Hi HE. rewrite (K2 b m i Hin Hi HE).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & Hb0 & Hb1 & _).
    apply VK. lia.
  - intros a Hai Ho He. rewrite (K3 a Hai Ho He).
    pose proof (ctrl_segs_low a Hai) as Hl. unfold kLowMemEnd in Hl. apply VK. lia.
  - intros cid pos a Hin Ha HE. rewrite (K4 cid pos a Hin Ha HE).
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F0 & F1 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Fn.
    apply VK.
    destruct Ha as [Ha|Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
    + lia.
    + unfold YG0f.shadow_addr, SHADOW_OFF in Ha. Z.div_mod_to_equations. lia.
  - intros a Ha Hw Hp. apply K5; [exact Ha | exact Hw |].
    destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b.
    rewrite (bb_mem_keep memc mu (sp - 4640) sp a MU ltac:(lia) Hw). exact Hb.
  - exact K6.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   5. The glue. *)
(* ---- route (C) (a Theorem Labs lane 09:20Z) and a Theorem Labs lane's AR lemmas (10:14Z): the glue with TSYMS as its ONLY Section
   hypothesis. asan_cells from ProgWorldCtlRt.asan_cells_of_AR (CtrlTSyms + AR), ro_agree from
   ProgWorldRtRo.ro_agree_of_AR with ProgWorldOwnedRo.AR_states_owned_ro_of_AR, and the lift's _hid_on twin (no
   shadow_rw premise): AR_states_vis0_shadow and AR_states_owned_ro are not needed. ---- *)
Section m_on.
Variable B : asyms.
(* ProgWorld.v:95 and :139, ProgWorld's text; and the runtime symbol bundle (a Theorem Labs lane 05:3xZ, as a Theorem Labs lane's
   reac_ctrl_classify_box_frame_glue.v:1099). The three are the premises of ProgWorldCtlRt.ctlrt_of_AR beyond
   AR_laws, which give asan_cells / shadow_rw / ro_agree at the entry memory. *)
Hypothesis TSYMS : A.AF0m.CtrlTSyms B.

Theorem pb_reac_ctrl_build_as_on : forall GLOBS RLO RHI, pb_reac_ctrl_build_as_stmt (SK := SK) B GLOBS RLO RHI.
Proof.
  intros GLOBS RLO RHI. unfold pb_reac_ctrl_build_as_stmt.
  intros TL LAWS ML RELRO_IMG TEMIT HIMGSH HGM HSW_glob HSW_al HSW_e HCAT_glob HCAT_al HSW_rng HCAT_rng.
  unfold treac_ctrl_build_as_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o md d c16 kind ns i mb nb db sb
    HJ HRO Hra Hra4 Hgp Htp H10 Ho H11 Hmd Hi H12 Hk H13 H14 H15 Hc16 H17 Hns
    Hsp16 Hslo Hshi Hc1 Hc0 Ho' Ho8 Ho47 Hoam Honi Hotw Hofo Hofr Hdfr Hohull
    Hdb HdG Hdsrc Hdni Hod Hds Hd8 Hsb HsG HmG Hmb HNB.
  pose proof HJ as [HAR _].
  unfold TBUILD_STK in Hslo, Hds.
  match type of Hshi with ?x <= _ => assert (ESP : x = bv_unsigned (getr regs 2)) by reflexivity end.
  assert (EK : A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K = 4640) by reflexivity.
  destruct (bb_win B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) HJ Hslo Hshi)
    as (VWIN & STK0 & HLO & H47).
  (* asan_cells, shadow_rw and ro_agree at the entry memory *)
  pose proof (A.ProgWorldCtlRt.asan_cells_of_AR B TSYMS lyc Sc W memc mdc HAR) as RAC.
  pose proof (A.ProgWorldRtRo.ro_agree_of_AR B TSYMS (A.ProgWorldOwnedRo.AR_states_owned_ro_of_AR B TSYMS)
                RLO RHI lyc Sc W memc mdc HAR
                (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO (Z.le_refl _) (Z.le_refl _))) as RRO.
  (* the catalogue entry lies in the image *)
  assert (HmdR : CtrlRo.IMG_LO + 64 <= md /\ md + 296 + 64 <= CtrlRo.IMG_HI)
    by (rewrite Hmd; unfold CAT_BYTES in *; lia).
  assert (HmdN : 0x10000 + 64 <= md /\ md + 296 + 64 <= 0x5fe000) by (unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in HmdR; lia).
  assert (Hmd0 : md <> 0) by lia.
  (* o and d lie in class >= 2 frames of the caller, below the window *)
  pose proof Hofr as (co & po & Ino & _ & _ & Hfo2).
  pose proof Hdfr as (cd & pd & Ind & _ & Hfd1 & Hfd2).
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc co po HAR Ino) as (Fo0 & Fo1 & _).
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cd pd HAR Ind) as (Fd0 & Fd1 & _).
  pose proof Hdsrc as (_ & _ & _ & _ & Hd0 & _).
  assert (HoLo : o + 1492 <= spZ regs - 4640) by lia.
  assert (HdLo : d + 6 <= spZ regs - 4640) by lia.
  (* ---- the entry state is the lift's start state ---- *)
  rewrite (cfg_at_MS SEGS (BASE + AF_reac_ctrl_build_as) regs memc mdc).
  apply (SRr_xregs_eqv SEGS W (mkR_of regs) regs); [| exact (xregs_eqv_sym _ _ (mkR_of_eqv regs))].
  rewrite bb_entry_pc, bb_mkR_of.
  apply (LIFT_ON ctrl_wx reac_box_model_upstream_widthF.reac_box_model_upstream_width_F_holds W mdc
           (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
           (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
           (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
           (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
           (getr regs 29) (getr regs 30) (getr regs 31) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr memc
           o md kind d (bv_unsigned (getr regs 14)) ns mb db sb).
  - (* a0 *) rewrite H10. apply bb_u64. lia.
  - (* a1 *) rewrite H11. apply bb_u64. lia.
  - (* a2 *) rewrite H12. apply bb_u64. lia.
  - (* a3 *) rewrite H13. apply bb_u64. lia.
  - (* a4 *) reflexivity.
  - (* a7 *) exact H17.
  - (* the window is the caller's stack *) exact STK0.
  - exact Hdb.
  - exact Hsb.
  - (* the catalogue entry *)
    intros _. split; [|split; [|split; [exact Hmb | split]]].
    + rewrite Hmd. unfold CAT_BYTES. clear - HCAT_al. Z.div_mod_to_equations. lia.
    + lia.
    + apply (bb_bytes_img W memc md mb); [lia | rewrite Hmb; lia | exact HmG].
    + unfold RcLay.ly_dj. right. lia.
  - exact RRO.
  - exact RAC.
  - unfold AsanRT.HIGHMEM_BEG. lia.
  - (* the switch table: a registered global *)
    replace A.Prog.reac_ctrl_build_as_c.BA_SW with (VAL (A_OBJ A_SW))
      by (unfold A_SW; rewrite bb_val_sw; reflexivity).
    apply (bb_addr_img W memc); [unfold SW_BYTES in HSW_rng; lia | lia | unfold SW_BYTES in HSW_rng; lia |].
    apply (ro_usable_glob SEGS B GLOBS lyc Sc W memc mdc (VAL (A_OBJ A_SW)) SW_BYTES _ _ HGM HSW_glob HAR);
      unfold SW_BYTES; lia.
  - (* the catalogue entry: a registered global *)
    intros _. apply (bb_addr_img W memc); [lia | lia | lia |].
    apply (ro_usable_glob SEGS B GLOBS lyc Sc W memc mdc (VAL (A_OBJ A_CAT)) (11 * CAT_BYTES) _ _ HGM HCAT_glob HAR);
      rewrite Hmd; unfold CAT_BYTES; lia.
  - exact (bb_imgsh_vis B lyc Sc W memc mdc HIMGSH HAR).
  - exact VWIN.
  - intros _. split.
    + apply (range_visible_sub (w_H W) ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO));
        [exact (img_vis_W W) | | |];
        unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI, CtrlRo.IMG_LO, CtrlRo.IMG_HI in *; lia.
    + apply (range_visible_sub (w_H W) 0x7fffa000 0xbdc00); [exact (bb_imgsh_vis B lyc Sc W memc mdc HIMGSH HAR) | | |];
        unfold AsanRT.shadow_addr, ASAN_K, CtrlRo.IMG_LO, CtrlRo.IMG_HI in *; Z.div_mod_to_equations; lia.
  - (* ---- the continuation: the stretch ends at the tail jump ---- *)
    intros ms' model' PO HID SAME.
    unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgLift.reac_ctrl_build_as.reac_ctrl_build_as_stretch_post_ro
      in PO.
    cbv zeta in PO.
    destruct PO as [[_ (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a6' & a7' & t3' & t4' & t5' & t6' & mu &
                     Ems & E0 & E1 & E2 & E3 & E4 & E6 & E7 & E9 & MU & WM & ROmu & STmu)] | [HG _]];
      [| rewrite (bb_go o md kind Ho Hmd0 Hk) in HG; discriminate HG].
    subst ms' a0' a1' a2' a3' a4' a6' a7' t4'.
    (* the caller's journal and read-only data at the jump memory *)
    assert (J' : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mu model' k).
    { apply (bb_jrnl B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k model' mu
               (bv_unsigned (getr regs 2) - A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K)
               (bv_unsigned (getr regs 2)) HJ MU WM HID SAME); lia. }
    assert (HROmu : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mu)).
    { apply (bb_ro B (w_H W) RLO RHI memc mu _ _ RELRO_IMG HRO MU). lia. }
    (* the jump state is the core's configuration at ctrl_emit_as *)
    match goal with |- SRr _ ?w (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) ?md') ?Q =>
      set (R' := R); change (SRr SEGS w (cfg_at SEGS 0x849d8 R' mu md') Q) end.
    rewrite <- bb_emit_pc.
    eapply (SRr_mono SEGS).
    { apply (TEMIT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mu model' k R' o md d c16
               (RcPorts.bm_uw md (firstn 8 (skipn 16 mb))) (lib.Prog.reac_ctrl_build_as_c.ba_row kind) i ns
               mb nb db sb).
      - exact J'.
      - exact HROmu.
      - exact Hra.
      - exact Hra4.
      - exact Hgp.
      - exact Htp.
      - reflexivity.
      - change (getr R' 11) with
          (Z_to_bv 64 (A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * lib.Prog.reac_ctrl_build_as_c.ba_row kind)).
        unfold w64. f_equal; symmetry; apply bb_frames_row.
      - exact (bb_row kind Hk).
      - reflexivity.
      - exact Hmd.
      - exact Hi.
      - reflexivity.
      - change (getr R' 14) with (Z_to_bv 64 (bv_unsigned (getr regs 14))). rewrite lib.Lib.MState.Z_to_bv_bv_unsigned.
        exact H14.
      - exact H15.
      - exact Hc16.
      - reflexivity.
      - pose proof (bb_uw md (firstn 8 (skipn 16 mb))). lia.
      - reflexivity.
      - reflexivity.
      - exact Hns.
      - exact Hsp16.
      - rewrite bb_temit_stk. exact Hslo.
      - exact Hshi.
      - exact Hc1.
      - exact Hc0.
      - exact Ho'.
      - exact Ho8.
      - exact Ho47.
      - exact Hoam.
      - exact Honi.
      - (* the output buffer is still present at mu *)
        intros a Ha. destruct (Hotw a Ha) as (A1 & A2 & A3 & A4).
        split; [exact A1|]. split; [|split; [exact A3 | exact A4]].
        apply (bb_present_keep _ memc mu _ _ a MU); [lia | lia | exact A2].
      - destruct Hofo as (F1 & F2 & F3). split; [exact F1|]. split; [exact F2|].
        apply (bb_ra_keep _ memc mu _ _ o 1492 MU); [lia | lia | lia | lia | exact F3].
      - exact Hofr.
      - exact Hdfr.
      - exact Hohull.
      - exact Hdb.
      - apply (bb_garr8_keep _ memc mu _ _ d (map bv_unsigned db) MU); [lia | rewrite length_map, Hdb; lia | lia | exact HdG].
      - destruct Hdsrc as (T1 & T2 & T3 & T4).
        split; [|split; [|split; [|exact T4]]].
        + intros a Ha. destruct (T1 a Ha) as [V N]. split; [|exact N].
          rewrite (bb_view_keep _ memc mu _ _ a MU); [exact V | lia | lia].
        + apply (bb_ra_keep _ memc mu _ _ d 6 MU); [lia | lia | lia | lia | exact T2].
        + apply (bb_hull_keep _ memc mu _ _ d 6 MU); [lia | lia | lia | lia | lia | exact T3].
      - exact Hdni.
      - exact Hod.
      - rewrite bb_temit_stk. exact Hds.
      - exact Hd8.
      - exact Hsb.
      - apply (bb_garr8_keep _ memc mu _ _ (VAL (A_OBJ 4)) (map bv_unsigned sb) MU);
          [rewrite bb_val_box; lia | rewrite bb_val_box, length_map, Hsb; lia | lia | exact HsG].
      - apply (bb_garr8_keep _ memc mu _ _ md (map bv_unsigned mb) MU);
          [lia | rewrite length_map, Hmb; lia | lia | exact HmG].
      - exact Hmb.
      - (* the name bytes: read-only image bytes *)
        intros Hbb Hh Hr. destruct (HNB Hbb Hh Hr) as (N1 & N2 & N3 & N4).
        split; [exact N1|]. split; [|exact (conj N3 N4)].
        destruct nb as [|b0 nb'].
        + cbn [map]. apply garr8_nil.
        + assert (NI : forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length (b0 :: nb')) ->
                         lib.Reusable.YG0d.in_img SEGS x).
          { intros x Hx. destruct (proj1 (N4 x Hx)) as [(s & Hs & _ & Hsr) | Hg];
              [exists s; split; [exact Hs | exact Hsr] | exact (RELRO_IMG x Hg)]. }
          destruct (bb_img_range (RcSynth.rname mb) (Z.of_nat (length (b0 :: nb'))) ltac:(cbn [length]; lia) NI)
            as [R0 R1].
          apply (bb_garr8_keep _ memc mu _ _ _ _ MU); [lia | rewrite length_map; lia | lia | exact N2]. }
    (* ---- TEMIT's post is build_as's post ---- *)
    intros W2 c2 Hle Hpost.
    unfold tctrl_emit_as_post in Hpost. cbv zeta in Hpost.
    destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & J2 & Hpr & Hfr & Hbl & Ha0 & HE & Hkept).
    unfold treac_ctrl_build_as_post, tctrl_emit_as_post. cbv zeta.
    exists ly2, S2, regs2, mem2, md2.
    split; [exact Ec2|]. split; [exact J2|].
    split.
    { apply (aregs_preserved_trans regs R' regs2); [|exact Hpr].
      intros r Hr. unfold acallee_saved in Hr.
      destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity..|].
      assert (E : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
        by lia.
      destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
    split; [exact Hfr|]. split; [exact Hbl|]. split; [exact Ha0|]. split; [exact HE|].
    apply (bb_tcj B LAWS lyc Sc W W2 memc mdc mu mem2 (spZ regs) _ HAR); [lia | lia | exact MU | exact Hkept].
Qed.

End m_on.

Section m.
Variable B : asyms.
(* ProgWorld.v:95 and :139, ProgWorld's text; and the runtime symbol bundle (a Theorem Labs lane 05:3xZ, as a Theorem Labs lane's
   reac_ctrl_classify_box_frame_glue.v:1099). The three are the premises of ProgWorldCtlRt.ctlrt_of_AR beyond
   AR_laws, which give asan_cells / shadow_rw / ro_agree at the entry memory. *)
Hypothesis AR_states_vis0_shadow : A.ProgWorld.AR_states_vis0_shadow B.
Hypothesis AR_states_owned_ro : A.ProgWorld.AR_states_owned_ro B.
Hypothesis TSYMS : A.AF0m.CtrlTSyms B.

(* The old statement (Section hypotheses unchanged), from the _on theorem. *)
Theorem pb_reac_ctrl_build_as : forall GLOBS RLO RHI, pb_reac_ctrl_build_as_stmt (SK := SK) B GLOBS RLO RHI.
Proof using AR_states_vis0_shadow AR_states_owned_ro TSYMS.
  exact (pb_reac_ctrl_build_as_on B TSYMS).
Qed.

End m.

End b.
