(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane). *)
(* fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the proof-internal library of the cgif-form glue of
   reac_ctrl_build_as (lib/B/Prog/C_reac_ctrl_build_as.v).
   1. The statements the glue takes:
      - the program-world facts are the REAL lemmas of lib/B/ProgWorld.v (ajournal_of_fsteps) and
        lib/B/ProgWorldCtlRtC.v (ctl_rt_C_of_AR, no AR_states_vis0_shadow), Required by C_reac_ctrl_build_as.v;
        no twin here;
      - the image-object facts: lib/B/Prog/CtrlRo.v's in_zs / img_shadow_vis (the PA layer's own definitions).
      The lifted stretch is a Theorem Labs lane's own reac_ctrl_build_asF.reac_ctrl_build_as_stretch_F_on (route (C), no
      shadow_rw premise; a working branch 26e8a9dd8b0; Required qualified, glue brief (a working note, not in this delivery)).
   2. Lemmas (Qed): the world -> ctrl lib.Lib conversions at a cut, the transport of world facts across a lifted
      stretch that writes only the stack window, the call-kept algebra, the image bytes, and the lift of the stretch.
   Glue closure rule: the _F files are Required qualified; frame-route names (AsanRT, Frame, ExecF) only inside
   Qed lemmas or inside the bodies of the named statements of item 1. The six (fifteen on image B) modules that
   exist both in lib/Reusable and lib/{A,B}/Reusable are named qualified (a Theorem Labs lane 04:03Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require AsanRT MemNorm MemNormF MemNormTr ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK0s YK14 YI00 YI04 YI16 YM05 YK1b YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
  YG0v YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d YCbq YE01 YK04R YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0o.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YF0m APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcPorts RcBox RcSynth RcLay RcFin RcEmit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c reac_ctrl_build_as.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_build_as_c ctrl_emit_as_c reac_ctrl_build_asF.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
#[local] Notation ygetr := lib.Reusable.YK11.getr.
#[local] Notation yseg_rom := lib.Reusable.YK11.seg_rom.
#[local] Notation garr8 := lib.Reusable.YI00.garr8.
(* image B's numerals (lib/B/Prog/reac_ctrl_build_as_c.v:14-21, ctrl_emit_as_c.v:11): entry, _F window, switch
   table, CTRL_FRAMES, ctrl_emit_as's entry; written as numerals so that the glue's arithmetic sees them *)
#[local] Notation BREAC := 0x8528c.
#[local] Notation BK := 4640.
#[local] Notation BA_SW := 0x21980.
#[local] Notation BA_FR := 0xa0600.
#[local] Notation BEMIT := 0x853c4.
#[local] Notation ba_go := Prog.reac_ctrl_build_as_c.ba_go.
#[local] Notation ba_row := Prog.reac_ctrl_build_as_c.ba_row.
(* names whose families exist as a core copy and an image-B copy in this file's closure (ctrlgate DUP), pinned to the
   constant `About` names in this file's context (measured 07:0xZ).  MemNorm is image B's lib/B/MemNorm.v, the copy
   lib/B/MemNormF.v:15 and lib/B/MemNormTr.v:26 Import and the statements fed here use (a Theorem Labs lane 07:58Z). *)
#[local] Notation rsegs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Img0.rsegs.
#[local] Notation MS := lib.Lib.MState.MS.
#[local] Notation ret_pc := lib.Lib.MState.ret_pc.
#[local] Notation bytes_at := lib.Lib.Mem.bytes_at.
#[local] Notation mrd := lib.Lib.Mem.mrd.
#[local] Notation wa := lib.Lib.Mem.wa.
#[local] Notation in_img := lib.Reusable.YG0d.in_img.
#[local] Notation frames := lib.Reusable.YG01.frames.
Module MemNorm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
#[local] Notation yfp_regs := (@lib.Reusable.YK11.fp_regs fx).
#[local] Notation yfp_csr := (@lib.Reusable.YK11.fp_csr fx).
#[local] Notation alloc_ceiling := (@lib.Reusable.YM05.alloc_ceiling rc).
(* the image-object facts of B's PA layer (lib/B/Prog/CtrlRo.v) *)
#[local] Notation in_zs := B.Prog.CtrlRo.in_zs.
#[local] Notation img_shadow_vis := (B.Prog.CtrlRo.img_shadow_vis SEGS).

(* =========================================================================================================
   2. Lemmas
   ========================================================================================================= *)

Lemma bl_u64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma bl_wx : wx_segs_nowrap SEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* ---- the world view and ctrl's lib.Lib memory ---- *)

Lemma bl_aview_some : forall (W : world SEGS) (m : word -> option byte) a v,
  aview SEGS (w_H W) m a = Some v ->
  w_H W (Z_to_bv 64 a) = false /\ exists b, mrd rsegs m (Z_to_bv 64 a) = Some b /\ v = bv_unsigned b.
Proof.
  intros W m a v H. unfold aview in H.
  destruct (lib.Reusable.YP09.mbyte SEGS (mrestrict (w_H W) m) a) as [b|] eqn:E; [|discriminate H].
  cbn [option_map] in H. injection H as <-.
  destruct (YA0o.mbyte_mrestrict_some SEGS (w_H W) m a b (w_Hoff W) E) as [E' Hv].
  split; [exact Hv|]. exists b. split; [exact E' | reflexivity].
Qed.

Lemma bl_vis_of_aview : forall (W : world SEGS) (m : word -> option byte) a,
  aview SEGS (w_H W) m a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W m a H. destruct (aview SEGS (w_H W) m a) as [v|] eqn:E; [|exfalso; exact (H eq_refl)].
  exact (proj1 (bl_aview_some W m a v E)).
Qed.

Lemma bl_sbyte_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. change (256 / 2) with 128.
  rewrite Z.mod_small by lia. lia.
Qed.

(* garr8 of the world's memory is lib.Lib's bytes_at, and its bytes are visible. *)
Lemma bl_bytes_of_garr8 : forall (W : world SEGS) (m : word -> option byte) a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W) m) a (map bv_unsigned bs) ->
  bytes_at rsegs m a bs /\ (forall i, 0 <= i < Z.of_nat (length bs) -> w_H W (Z_to_bv 64 (a + i)) = false).
Proof.
  intros W m a bs Ha Hb HG.
  assert (K : forall i, (i < length bs)%nat ->
            mrd rsegs m (wa (a + Z.of_nat i)) = nth_error bs i /\ w_H W (Z_to_bv 64 (a + Z.of_nat i)) = false).
  { intros i Hi.
    destruct (nth_error bs i) as [b|] eqn:Eb; [| apply nth_error_None in Eb; lia].
    assert (Hi' : (i < length (map bv_unsigned bs))%nat) by (rewrite length_map; exact Hi).
    destruct (HG i Hi') as [HV Hr].
    assert (En : nth i (map bv_unsigned bs) 0 = bv_unsigned b).
    { apply nth_error_nth. rewrite nth_error_map, Eb. reflexivity. }
    rewrite En in HV, Hr.
    specialize (HV 0%nat ltac:(lia)).
    replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) in HV by lia.
    rewrite lib.Reusable.YI04.le_byte_small in HV by (cbn; lia).
    change (8 * Z.of_nat 0) with 0 in HV. rewrite Z.shiftr_0_r in HV.
    replace (Z_to_bv 8 (bv_unsigned b)) with b in HV
      by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range).
    destruct (YA0o.mbyte_mrestrict_some SEGS (w_H W) m _ _ (w_Hoff W) HV) as [E Hv].
    split; [exact E | exact Hv]. }
  split.
  - split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (K i Hi)).
  - intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. apply K. lia.
Qed.

(* range_addressable of the world view is lib.Lib's addressable, on application memory. *)
Lemma bl_addr_of_ra : forall (W : world SEGS) (m : word -> option byte) a n,
  0 <= a -> 0 <= n -> a + n <= AsanRT.APPMEM_END -> (forall i, 0 <= i < n -> AsanRT.app_mem (a + i)) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n -> AsanRT.addressable m a n.
Proof.
  intros W m a n Ha Hn Hb Happ HR. unfold AsanRT.addressable.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. unfold AsanRT.addr_byte. split; [exact (Happ i Hi)|].
  destruct (HR (a + i) ltac:(lia)) as (s & Hs & Hok).
  destruct (bl_aview_some W m _ _ Hs) as (_ & b & Eb & ->).
  exists b.
  replace (AsanRT.shadow_addr (a + i)) with (shadow_of_addr SHADOW_OFF (a + i))
    by (unfold shadow_of_addr, SHADOW_OFF, AsanRT.shadow_addr, AsanRT.ASAN_K; lia).
  split; [exact Eb|].
  unfold AsanRT.shadow_ok. unfold saddr_ok in Hok.
  rewrite bl_sbyte_small by (destruct Hok as [Hok | Hok]; lia).
  destruct Hok as [Hok | Hok]; [left | right]; lia.
Qed.

Lemma bl_app_of_in_app : forall a n, in_app a n -> forall i, 0 <= i < n -> AsanRT.app_mem (a + i).
Proof.
  intros a n [H0 H] i Hi. pose proof ASAN_CEIL_range as [CR _].
  unfold AsanRT.app_mem, AsanRT.LOWMEM_END, AsanRT.HIGHMEM_BEG, AsanRT.APPMEM_END.
  unfold kLowShadowBeg, kHighMemBeg in H. lia.
Qed.

(* the zero-shadow ranges the runtime keeps (lib/A/Prog/CtrlRo.v ro_usable, B twin) *)
Lemma bl_zs_ra : forall B, AR_laws SEGS B -> forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> in_zs B a n -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
  intros B LAWS ly S W mem md a n HAR (q & m & Hin & H1 & H2).
  pose proof (am_syms _ _ _ _ (proj1 HAR)) as HS.
  pose proof (proj1 (Forall_forall _ _) (aso_zshadow B HS) (q, m) Hin) as H. cbn [fst snd] in H.
  destruct H as (Hq0 & Hm0 & Hq8 & Hm8 & Hhi).
  pose proof (al_zshadow _ _ LAWS ly S W mem md (q, m) HAR (or_intror Hin)) as Hz.
  apply (range_addressable_sub (aview SEGS (w_H W) mem) SHADOW_OFF q m a n); [| exact H1 | exact H2].
  exact (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF q m Hq8 Hm8 Hz).
Qed.

(* ---- visibility: the footprint ranges of RNG_W (w_H W) ---- *)

Lemma bl_vis_present : forall (W : world SEGS) (m : word -> option byte) lo len,
  0 <= lo -> lo + len <= 2 ^ 64 -> (forall a, lo <= a < lo + len -> apresent (w_H W) m a) ->
  ProgBridge.range_visible (w_H W) lo len.
Proof.
  intros W m lo len H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros a Ha. exact (proj1 (H a Ha)).
Qed.

Lemma bl_img_vis : forall (W : world SEGS), ProgBridge.range_visible (w_H W) 0x10000 0x5ee000.
Proof.
  intros W. pose proof (ProgBridge.img_vis_W W) as H.
  unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI in H. exact H.
Qed.

Lemma bl_img_sub_vis : forall (W : world SEGS) lo len,
  0x10000 <= lo -> 0 <= len -> lo + len <= 0x5fe000 -> ProgBridge.range_visible (w_H W) lo len.
Proof.
  intros W lo len H1 H2 H3. apply (ProgBridge.range_visible_sub _ 0x10000 0x5ee000); [exact (bl_img_vis W) | lia..].
Qed.

Lemma bl_imgsh_vis : forall B (W : world SEGS) ly S mem md,
  img_shadow_vis B -> AR SEGS B ly S W mem md -> ProgBridge.range_visible (w_H W) 0x7fffa000 0xbdc00.
Proof.
  intros B W ly S mem md HV HAR. split; [lia|]. split; [lia|]. intros s Hs.
  set (x := 8 * (s - SHADOW_OFF)).
  assert (Hx : shadow_addr x = s).
  { unfold shadow_addr, x, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
  assert (Hxr : CtrlRo.IMG_LO <= x < CtrlRo.IMG_HI) by (unfold x, SHADOW_OFF, CtrlRo.IMG_LO, CtrlRo.IMG_HI; lia).
  pose proof (HV ly S W mem md x HAR Hxr) as H. rewrite Hx in H.
  exact (bl_vis_of_aview W mem s H).
Qed.

Lemma bl_hull_vis : forall (W : world SEGS) (m : word -> option byte) x n,
  0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_hull_vis (aview SEGS (w_H W) m) x n ->
  ProgBridge.range_visible (w_H W) (AsanRT.shadow_addr x / 8 * 8)
    (AsanRT.shadow_addr (x + n - 1) / 8 * 8 + 8 - AsanRT.shadow_addr x / 8 * 8).
Proof.
  intros W m x n Hx Hn Hxn HH.
  assert (E1 : forall y, AsanRT.shadow_addr y = shadow_addr y)
    by (intros y; unfold AsanRT.shadow_addr, AsanRT.ASAN_K, shadow_addr, SHADOW_OFF; lia).
  rewrite !E1.
  assert (B1 : 0 <= shadow_addr x / 8 * 8).
  { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (2147450880 + x / 8) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (B2 : shadow_addr (x + n - 1) / 8 * 8 + 8 <= 2 ^ 64).
  { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_le_upper_bound (x + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (2147450880 + (x + n - 1) / 8) 8 (2 ^ 42) ltac:(lia) ltac:(lia)). lia. }
  split; [exact B1|]. split; [lia|]. intros s Hs.
  exact (bl_vis_of_aview W m s (HH s ltac:(lia))).
Qed.

(* the window bytes of the caller's journal are present, so the window is a stk window *)
Lemma bl_stk_of_present : forall (W : world SEGS) (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> apresent (w_H W) m a) -> stk rsegs m lo hi.
Proof.
  intros W m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as [_ [b Hb]]. change (wa a) with (Z_to_bv 64 a).
  split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* ---- a stretch that writes only [lo, hi) (raw munch) keeps the world facts outside it ---- *)

Lemma bl_mr_munch : forall lo hi (m m' : word -> option byte) (H : word -> bool) x,
  munch [(lo, hi)] m m' -> ~ (lo <= bv_unsigned x < hi) -> mrestrict H m' x = mrestrict H m x.
Proof.
  intros lo hi m m' H x HM Hx. unfold mrestrict. destruct (H x); [reflexivity|].
  apply HM. cbn [outside]. split; [exact Hx | exact I].
Qed.

Lemma bl_aview_munch : forall lo hi (m m' : word -> option byte) (H : word -> bool) a,
  munch [(lo, hi)] m m' -> 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros lo hi m m' H a HM Ha Hw. apply aview_eq_of.
  apply (bl_mr_munch lo hi m m' H). exact HM. rewrite bl_u64 by exact Ha. exact Hw.
Qed.

Lemma bl_apresent_munch : forall lo hi (m m' : word -> option byte) (H : word -> bool) a,
  munch [(lo, hi)] m m' -> 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> apresent H m a -> apresent H m' a.
Proof.
  intros lo hi m m' H a HM Ha Hw [Hv [b Hb]]. split; [exact Hv|]. exists b.
  rewrite (HM (Z_to_bv 64 a)); [exact Hb|]. cbn [outside]. rewrite bl_u64 by exact Ha. split; [exact Hw | exact I].
Qed.

Lemma bl_garr8_munch : forall lo hi (m m' : word -> option byte) (H : word -> bool) a (l : list Z),
  munch [(lo, hi)] m m' -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (hi <= a \/ a + Z.of_nat (length l) <= lo) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
  intros lo hi m m' H a l HM H0 H1 Hd HG j Hj. destruct (HG j Hj) as [HV Hr]. split; [|exact Hr].
  intros k Hk. specialize (HV k Hk). assert (k = 0%nat) by lia. subst k.
  unfold lib.Reusable.YP09.mbyte in *.
  rewrite (bl_mr_munch lo hi m m' H); [exact HV | exact HM |].
  rewrite bl_u64 by lia. lia.
Qed.

Lemma bl_ra_munch : forall lo hi (m m' : word -> option byte) (H : word -> bool) a n,
  munch [(lo, hi)] m m' -> 0 <= a -> a + n <= 2 ^ 47 -> 2 ^ 45 <= lo ->
  range_addressable (aview SEGS H m) SHADOW_OFF a n -> range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof.
  intros lo hi m m' H a n HM H0 H1 Hlo HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite (bl_aview_munch lo hi m m' H); [exact Hs | exact HM | |];
    unfold shadow_of_addr, SHADOW_OFF; pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia));
    pose proof (Z.div_le_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia.
Qed.

(* ---- the image ---- *)

Lemma bl_in_img : forall a, (0x10000 <= a < 0x31000) \/ (0x9f000 <= a < 0xa2000) -> in_img SEGS a.
Proof.
  intros a Ha. pose proof ProgBridge.rsegs_spans as E.
  destruct Ha as [Ha | Ha].
  - assert (Hin : In (0x10000, 0x21000) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs))
      by (rewrite E; left; reflexivity).
    apply in_map_iff in Hin as (sg & Hsg & Hin). injection Hsg as H1 H2.
    exists sg. split; [exact Hin|]. lia.
  - assert (Hin : In (0x9f000, 0x3000) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs))
      by (rewrite E; right; right; left; reflexivity).
    apply in_map_iff in Hin as (sg & Hsg & Hin). injection Hsg as H1 H2.
    exists sg. split; [exact Hin|]. lia.
Qed.

Lemma bl_img_low : forall a, in_img SEGS a -> 0x10000 <= a < 0x5fe000.
Proof.
  intros a (sg & Hin & Hr). pose proof ProgBridge.rsegs_spans as E.
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                 (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs))
    by (apply in_map_iff; exists sg; split; [reflexivity | exact Hin]).
  rewrite E in H. cbn [In] in H.
  destruct H as [H | [H | [H | [H | []]]]]; injection H as H1 H2; lia.
Qed.

(* ---- the call-kept algebra (YCbq.acall_kept) ---- *)

Lemma bl_frame_sh_low : forall B ly S (W : world SEGS) mem md cid pos a,
  AR_laws SEGS B -> AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  0 <= a < alloc_ceiling.
Proof.
  intros B ly S W mem md cid pos a LAWS HAR Hin Hr.
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn. pose proof ASAN_CEIL_range as [CR _].
  unfold ASAN_CEIL in CR.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  destruct Hr as [Hr | Hr]; [lia|].
  unfold shadow_addr, SHADOW_OFF in Hr.
  pose proof (Z.div_le_upper_bound (frame_addr ly cid pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (fs_frame_bytes cid) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma bl_block_low : forall B ly S (W : world SEGS) mem md b m i,
  AR_laws SEGS B -> AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
  0 <= b + i < alloc_ceiling.
Proof.
  intros B ly S W mem md b m i LAWS HAR Hin Hi.
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4 & Hc & _). lia.
Qed.

(* a stretch that writes only [lo, hi) inside the call window [slo, shi) keeps everything acall_kept keeps *)
Lemma bl_ack_munch : forall B lyc Sc (W : world SEGS) memc mdc mem' lo hi slo shi (E : Z -> Prop),
  AR_laws SEGS B -> AR SEGS B lyc Sc W memc mdc ->
  munch [(lo, hi)] memc mem' -> slo <= lo -> hi <= shi -> alloc_ceiling <= slo ->
  (forall a, slo <= a < shi -> apresent (w_H W) mem' a) ->
  acall_kept SEGS B lyc Sc W memc W mem' slo shi E.
Proof.
  intros B lyc Sc W memc mdc mem' lo hi slo shi E LAWS HAR HM H1 H2 H3 Hpres.
  pose proof ASAN_CEIL_range as [CR0 _]. unfold ASAN_CEIL in CR0.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hs. apply (bl_aview_munch lo hi memc mem'); [exact HM | lia | lia].
  - intros b m i Hb Hi _. pose proof (bl_block_low B lyc Sc W memc mdc b m i LAWS HAR Hb Hi).
    apply (bl_aview_munch lo hi memc mem'); [exact HM | lia | lia].
  - intros a Hi _ _. pose proof (bl_img_low a Hi). pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
    apply (bl_aview_munch lo hi memc mem'); [exact HM | lia | lia].
  - intros cid pos a Hin Hr _. pose proof (bl_frame_sh_low B lyc Sc W memc mdc cid pos a LAWS HAR Hin Hr).
    apply (bl_aview_munch lo hi memc mem'); [exact HM | lia | lia].
  - intros a Ha Hs Hp. apply (bl_apresent_munch lo hi memc mem'); [exact HM | lia | lia | exact Hp].
  - exact Hpres.
Qed.

(* the same, composed with a callee's acall_kept from the stretch's end memory *)
Lemma bl_ack_comp : forall B lyc Sc (W W2 : world SEGS) memc mdc mem1 mem2 lo hi slo shi (E : Z -> Prop),
  AR_laws SEGS B -> AR SEGS B lyc Sc W memc mdc ->
  munch [(lo, hi)] memc mem1 -> slo <= lo -> hi <= shi -> alloc_ceiling <= slo ->
  acall_kept SEGS B lyc Sc W mem1 W2 mem2 slo shi E ->
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi E.
Proof.
  intros B lyc Sc W W2 memc mdc mem1 mem2 lo hi slo shi E LAWS HAR HM H1 H2 H3 (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof ASAN_CEIL_range as [CR0 _]. unfold ASAN_CEIL in CR0.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hs. rewrite (K1 a Ha Hs). apply (bl_aview_munch lo hi memc mem1); [exact HM | lia | lia].
  - intros b m i Hb Hi HE. rewrite (K2 b m i Hb Hi HE).
    pose proof (bl_block_low B lyc Sc W memc mdc b m i LAWS HAR Hb Hi).
    apply (bl_aview_munch lo hi memc mem1); [exact HM | lia | lia].
  - intros a Hi Hn He. rewrite (K3 a Hi Hn He). pose proof (bl_img_low a Hi).
    pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
    apply (bl_aview_munch lo hi memc mem1); [exact HM | lia | lia].
  - intros cid pos a Hin Hr HE. rewrite (K4 cid pos a Hin Hr HE).
    pose proof (bl_frame_sh_low B lyc Sc W memc mdc cid pos a LAWS HAR Hin Hr).
    apply (bl_aview_munch lo hi memc mem1); [exact HM | lia | lia].
  - intros a Ha Hs Hp. apply (K5 a Ha Hs). apply (bl_apresent_munch lo hi memc mem1); [exact HM | lia | lia | exact Hp].
  - exact K6.
Qed.

(* ---- the return address ---- *)
Lemma bl_ret_pc : forall k : word, lib.Reusable.YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H. unfold lib.Reusable.YK0s.ret_ok in H. rewrite <- H at 2.
  unfold ret_pc. apply bv_eq.
  unfold lib.Reusable.YK14.v_jalr, lib.Reusable.YK11.jalr_tgtZ.
  rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 1) with 1%Z. change (Z.lnot 1) with (-2)%Z.
  rewrite Z.add_0_r.
  rewrite <- (bv_wrap_small 64 (bv_unsigned k)) at 1 by apply bv_unsigned_in_range.
  apply lib.Reusable.YK11.Z_land_m2_wrap.
Qed.

(* ---- the lift of a stretch at a cut of the walk (A/Prog/GE_entry.v of a Theorem Labs lane, B twin), with the run itself
   handed to the continuation (ajournal_of_fsteps takes it) ---- *)
(* the run's start state at pc a: the walk's registers named one by one *)
Definition bl_ms0 (regs : bvmap 5 word) (a : Z) (memc : word -> option byte) : machine_state :=
  MS (mkR (ygetr regs 1) (ygetr regs 2) (ygetr regs 3) (ygetr regs 4) (ygetr regs 5) (ygetr regs 6)
          (ygetr regs 7) (ygetr regs 8) (ygetr regs 9) (ygetr regs 10) (ygetr regs 11) (ygetr regs 12)
          (ygetr regs 13) (ygetr regs 14) (ygetr regs 15) (ygetr regs 16) (ygetr regs 17) (ygetr regs 18)
          (ygetr regs 19) (ygetr regs 20) (ygetr regs 21) (ygetr regs 22) (ygetr regs 23) (ygetr regs 24)
          (ygetr regs 25) (ygetr regs 26) (ygetr regs 27) (ygetr regs 28) (ygetr regs 29) (ygetr regs 30)
          (ygetr regs 31))
     yfp_regs (Z_to_bv 64 a) yfp_csr None memc (yseg_rom SEGS).

Lemma bl_entry : forall (W : world SEGS) (a : Z) (regs : bvmap 5 word) (memc : word -> option byte)
    (mdc : Model) (P : machine_state -> Prop) (Q : world SEGS -> config -> Prop),
  ExecF.evtF rsegs (ProgBridge.RNG_W (w_H W)) P (bl_ms0 regs a memc) ->
  (forall (ms' : machine_state) (mdc' : Model), P ms' ->
     fsteps SEGS (ProgBridge.RNG_W (w_H W)) (bl_ms0 regs a memc) ms' ->
     same_but_materialized mdc mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (cfg_at SEGS a regs memc mdc) Q.
Proof.
  intros W a regs memc mdc P Q HE K.
  rewrite (ProgBridge.cfg_at_MS SEGS a regs memc mdc).
  apply (SRr_xregs_eqv SEGS W (Regs6ss.mkR_of regs) regs yfp_regs (Z_to_bv 64 a) yfp_csr None memc
           (yseg_rom SEGS) mdc Q);
    [| exact (Regs6ss.xregs_eqv_sym _ _ (Regs6ss.mkR_of_eqv regs))].
  change (SRr SEGS W (mkCfg (bl_ms0 regs a memc) mdc) Q).
  destruct (ProgBridge.fevt_of_evtF _ P _ HE) as (ms' & Hrun & HP).
  apply (SRr_fevt SEGS bl_wx W _ mdc (ProgBridge.RNG_W (w_H W))
           (fun s => P s /\ fsteps SEGS (ProgBridge.RNG_W (w_H W)) (bl_ms0 regs a memc) s) Q).
  - exists ms'. split; [exact Hrun|]. split; [exact HP | exact Hrun].
  - exact (ProgBridge.fp_avoids_RNG_W (w_H W)).
  - intros s mdc' [HPs Hs] Hsame. exact (K s mdc' HPs Hs Hsame).
Qed.

(* ---- the stretch's post over the REAL memory (ro_agree in place of mem_inv, a Theorem Labs lane's _post_ro form), with
   the walk's registers ---- *)
Definition bl_post (regs : bvmap 5 word) (memc : word -> option byte) (o md b d s ns : Z) (mb : list byte)
    (ms' : machine_state) : Prop :=
  let S := bv_unsigned (ygetr regs 2) in
  let Lo := S - BK in
  let n := RcPorts.bm_uw md (firstn 8 (skipn 16 mb)) in
  (ba_go o md b = true /\
   exists (t0' t1' t2' t3' t5' t6' : word) (mu : word -> option byte),
     ms' = MS (mkR (ygetr regs 1) (ygetr regs 2) (ygetr regs 3) (ygetr regs 4) t0' t1' t2'
                   (ygetr regs 8) (ygetr regs 9) (Z_to_bv 64 o) (Z_to_bv 64 (BA_FR + 24 * ba_row b))
                   (Z_to_bv 64 md) (Z_to_bv 64 d) (Z_to_bv 64 s) (ygetr regs 15) (Z_to_bv 64 n) (Z_to_bv 64 0)
                   (ygetr regs 18) (ygetr regs 19) (ygetr regs 20) (ygetr regs 21) (ygetr regs 22)
                   (ygetr regs 23) (ygetr regs 24) (ygetr regs 25) (ygetr regs 26) (ygetr regs 27)
                   t3' (Z_to_bv 64 ns) t5' t6')
              yfp_regs (Z_to_bv 64 BEMIT) yfp_csr None mu (yseg_rom SEGS)
     /\ munch [(Lo, S)] memc mu /\ wmono rsegs memc mu /\ MemNorm.ro_agree rsegs mu /\ stk rsegs mu Lo S)
  \/
  (ba_go o md b = false /\
   exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     ms' = MS (mkR (ygetr regs 1) (ygetr regs 2) (ygetr regs 3) (ygetr regs 4) t0' t1' t2'
                   (ygetr regs 8) (ygetr regs 9) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                   (ygetr regs 18) (ygetr regs 19) (ygetr regs 20) (ygetr regs 21) (ygetr regs 22)
                   (ygetr regs 23) (ygetr regs 24) (ygetr regs 25) (ygetr regs 26) (ygetr regs 27)
                   t3' t4' t5' t6')
              yfp_regs (ret_pc (ygetr regs 1)) yfp_csr None m' (yseg_rom SEGS)
     /\ munch [(S - 80, S)] memc m' /\ wmono rsegs memc m' /\ MemNorm.ro_agree rsegs m' /\ stk rsegs m' Lo S).

(* The stretch [entry, tail jump | ret 0] as a step of the world walk: reac_ctrl_build_as_stretch_F_on (route (C),
   no shadow_rw premise; a working branch 26e8a9dd8b0) on normalize memc (by decision 27a of decisions.md (a working note, not in this delivery)),
   moved to memc by MemNormF.evtF_normalize_ro, lifted by bl_entry at RNG := RNG_W (w_H W); every footprint
   premise is a visibility fact. *)
Lemma bl_stretch_on : lib.B.Prog.reac_ctrl_build_asF.reac_ctrl_build_as_stretch_F_on ->
  forall (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model)
         (o md b d s ns : Z) (mb db sb : list byte) (Q : world SEGS -> config -> Prop),
  let S := bv_unsigned (ygetr regs 2) in
  let Lo := S - BK in
  ygetr regs 10 = Z_to_bv 64 o -> ygetr regs 11 = Z_to_bv 64 md -> ygetr regs 12 = Z_to_bv 64 b ->
  ygetr regs 13 = Z_to_bv 64 d -> ygetr regs 14 = Z_to_bv 64 s -> ygetr regs 17 = Z_to_bv 64 ns ->
  0 <= o < 2 ^ 64 -> 0 <= md < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= d < 2 ^ 64 -> 0 <= s < 2 ^ 64 ->
  stk rsegs memc Lo S -> 0x5fe000 <= Lo ->
  length db = 6%nat -> length sb = 6%nat ->
  (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ bytes_at rsegs memc md mb /\
              RcLay.ly_dj Lo S md (md + 296)) ->
  MemNorm.ro_agree rsegs memc -> AsanRT.asan_cells memc ->
  0x10007fff8000 <= Lo -> AsanRT.addressable memc BA_SW 56 -> (md <> 0 -> AsanRT.addressable memc md 296) ->
  ProgBridge.range_visible (w_H W) 0x7fffa000 0xbdc00 ->
  ProgBridge.range_visible (w_H W) Lo BK ->
  (md <> 0 -> ProgBridge.range_visible (w_H W) md 296 /\
     ProgBridge.range_visible (w_H W) (AsanRT.shadow_addr md / 8 * 8)
       (AsanRT.shadow_addr (md + 295) / 8 * 8 + 8 - AsanRT.shadow_addr md / 8 * 8)) ->
  (forall (ms' : machine_state) (mdc' : Model), bl_post regs memc o md b d s ns mb ms' ->
     fsteps SEGS (ProgBridge.RNG_W (w_H W)) (bl_ms0 regs BREAC memc) ms' ->
     same_but_materialized mdc mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (cfg_at SEGS BREAC regs memc mdc) Q.
Proof.
  intros STR W regs memc mdc o md b d s ns mb db sb Q S Lo Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 Ro Rmd Rb Rd Rs
    HST HIH Hdb Hsb HM Pro HAC HHM ASW AM VISH VWIN VMD K.
  pose proof (MemNorm.mem_rel_normalize rsegs memc Pro) as REL.
  pose proof (STR (ProgBridge.RNG_W (w_H W))
                (ygetr regs 1) (ygetr regs 2) (ygetr regs 3) (ygetr regs 4) (ygetr regs 5) (ygetr regs 6)
                (ygetr regs 7) (ygetr regs 8) (ygetr regs 9) (ygetr regs 10) (ygetr regs 11) (ygetr regs 12)
                (ygetr regs 13) (ygetr regs 14) (ygetr regs 15) (ygetr regs 16) (ygetr regs 17) (ygetr regs 18)
                (ygetr regs 19) (ygetr regs 20) (ygetr regs 21) (ygetr regs 22) (ygetr regs 23) (ygetr regs 24)
                (ygetr regs 25) (ygetr regs 26) (ygetr regs 27) (ygetr regs 28) (ygetr regs 29) (ygetr regs 30)
                (ygetr regs 31) yfp_regs yfp_csr (MemNorm.normalize rsegs memc) o md b d s ns mb db sb) as HS.
  cbv zeta in HS.
  assert (VIMG := ProgBridge.img_vis_W W).
  assert (VGK : ProgBridge.range_visible (w_H W) AsanRT.GOT_CELL_K 8)
    by (apply bl_img_sub_vis; unfold AsanRT.GOT_CELL_K; lia).
  assert (VCK : ProgBridge.range_visible (w_H W) AsanRT.CELL_K 8)
    by (apply bl_img_sub_vis; unfold AsanRT.CELL_K; lia).
  specialize (HS ltac:(rewrite Ha0; apply bl_u64; exact Ro) ltac:(rewrite Ha1; apply bl_u64; exact Rmd)
                 ltac:(rewrite Ha2; apply bl_u64; exact Rb) ltac:(rewrite Ha3; apply bl_u64; exact Rd)
                 ltac:(rewrite Ha4; apply bl_u64; exact Rs) Ha7
                 (MemNormTr.stk_normalize_ro memc _ _ Pro HIH HST) Hdb Hsb).
  specialize (HS ltac:(intros H0; destruct (HM H0) as (M1 & M2 & M3 & M4 & M5);
                       split; [exact M1|]; split; [exact M2|]; split; [exact M3|];
                       split; [exact (MemNorm.bytes_at_normalize rsegs memc _ _ Pro M4) | exact M5])
                 (MemNorm.mem_inv_normalize rsegs memc)
                 (MemNormTr.asan_cells_normalize memc Pro HAC) HHM
                 (MemNormTr.addressable_normalize memc _ _ Pro ASW)
                 (fun H0 => MemNormTr.addressable_normalize memc _ _ Pro (AM H0))
                 (ProgBridge.rng_of_visible _ _ _ VIMG) (ProgBridge.rng_of_visible _ _ _ VISH)
                 (ProgBridge.rng_of_visible _ _ _ VWIN)
                 (ProgBridge.rng_of_visible _ _ _ VGK) (ProgBridge.rng_of_visible _ _ _ VCK)
                 (fun H0 => conj (ProgBridge.rng_of_visible _ _ _ (proj1 (VMD H0)))
                                 (ProgBridge.rng_of_visible _ _ _ (proj2 (VMD H0))))).
  pose proof (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ memc _ Pro HS) as HN.
  apply (bl_entry W BREAC regs memc mdc _ Q HN).
  intros ms' mdc' HP Hrun Hsame. apply (K ms' mdc'); [| exact Hrun | exact Hsame].
  destruct HP as (s0 & PO & HREL & HROS).
  destruct PO as [[HG (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a6' & a7' & t3' & t4' & t5' & t6' & mu &
                      E & E0 & E1 & E2 & E3 & E4 & E6 & E7 & E8 & E9 & MU & WM & _ & ST)] |
                  [HG (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                      E & MU & WM & _ & ST)]].
  - rewrite E in HREL. destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
    left. split; [exact HG|]. subst a0' a1' a2' a3' a4' a6' a7' t4'.
    exists t0', t1', t2', t3', t5', t6', (ms_mem ms').
    split; [exact Ems|].
    split; [exact (MemNorm.munch_rel rsegs _ memc _ _ _ REL HMR HROS MU)|].
    split; [exact (MemNorm.wmono_rel rsegs memc _ _ _ REL HMR HROS WM)|].
    split; [exact (MemNorm.ro_agree_of_mem_rel rsegs _ _ HMR)|].
    exact (MemNormTr.stk_of_rel _ _ _ _ HMR ST).
  - rewrite E in HREL. destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
    right. split; [exact HG|].
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem ms').
    split; [exact Ems|].
    split; [exact (MemNorm.munch_rel rsegs _ memc _ _ _ REL HMR HROS MU)|].
    split; [exact (MemNorm.wmono_rel rsegs memc _ _ _ REL HMR HROS WM)|].
    split; [exact (MemNorm.ro_agree_of_mem_rel rsegs _ _ HMR)|].
    exact (MemNormTr.stk_of_rel _ _ _ _ HMR ST).
Qed.

(* ---- the image bytes of the CTRL_FRAMES rows 3..9 (computation on image B's segments) ---- *)
Definition bl_rom_is (a : Z) (x : byte) : bool :=
  match yseg_rom SEGS (Z_to_bv 64 a) with Some y => Z.eqb (bv_unsigned y) (bv_unsigned x) | None => false end.

Lemma bl_rows_rom_b : forallb (fun bn => forallb (fun j =>
    bl_rom_is (BA_FR + 24 * ba_row (Z.of_nat bn) + Z.of_nat j)
      (nth j (Prog.reac_ctrl_build_as_c.ba_fr (ba_row (Z.of_nat bn))) (Z_to_bv 8 0))) (seq 0 24)) (seq 0 7) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bl_row_rom : forall b, 0 <= b <= 6 -> forall j, (j < 24)%nat ->
  yseg_rom SEGS (Z_to_bv 64 (BA_FR + 24 * ba_row b + Z.of_nat j)) =
  Some (nth j (Prog.reac_ctrl_build_as_c.ba_fr (ba_row b)) (Z_to_bv 8 0)).
Proof.
  intros b Hb j Hj. pose proof bl_rows_rom_b as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat b) ltac:(apply in_seq; lia)). rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  unfold bl_rom_is in H.
  destruct (yseg_rom SEGS (Z_to_bv 64 (BA_FR + 24 * ba_row b + Z.of_nat j))) as [y|]; [|discriminate H].
  apply Z.eqb_eq in H. f_equal. apply bv_eq. exact H.
Qed.

(* ---- the row model of rows 3..9 (ctrl_emit_as's premises on the row, and its post's block) ---- *)
Lemma bl_row_facts : forall b, 0 <= b <= 6 ->
  let row := Prog.reac_ctrl_build_as_c.ba_fr (ba_row b) in
  length row = 24%nat /\ RcLay.ly_k row = ba_row b /\ 3 <= ba_row b <= 9 /\ RcLay.ly_bb (ba_row b) = b /\
  RcFin.ubat row 20 = (if b <=? 1 then 1 else 0) /\ RcFin.ubat row 21 <= 1 /\ RcFin.ubat row 22 <= 1 /\
  RcFin.ubat row 23 <= 1 /\ RcFin.ubat row 18 = 0 /\ RcFin.ubat row 19 = 0 /\
  RcLay.ly_ao row = 0 /\ RcLay.ly_al row = 0 /\
  nth 0 row (Z_to_bv 8 0) = Z_to_bv 8 205 /\ nth 1 row (Z_to_bv 8 0) = Z_to_bv 8 234.
Proof.
  intros b Hb. cbv zeta.
  destruct (reac_ctrl_build_as.ba_cases b Hb) as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    vm_compute; repeat split; try reflexivity; try (intros Hc; discriminate Hc).
Qed.

Lemma bl_blk : forall b md (mb nb : list byte), 0 <= b <= 6 ->
  let row := Prog.reac_ctrl_build_as_c.ba_fr (ba_row b) in
  RcFin.fin (RcFin.ubat row 20) (RcFin.ubat row 18) (RcFin.ubat row 19)
    (RcLay.ly_lay (RcLay.ly_k row) [] (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k row))) 0 (RcLay.ly_ao row)
       (RcLay.ly_al row) []) = Prog.reac_ctrl_build_as_c.ba_X md mb nb b.
Proof.
  intros b md mb nb Hb. cbv zeta.
  destruct (bl_row_facts b Hb) as (_ & Hk & Hr & Hbb & H20 & _ & _ & _ & H18 & H19 & Hao & Hal & _).
  rewrite Hk, Hbb, H18, H19, Hao, Hal, H20.
  rewrite reac_ctrl_build_as.ba_lay by lia.
  unfold Prog.reac_ctrl_build_as_c.ba_X. destruct (b <=? 1); reflexivity.
Qed.

(* ---- more world facts at the cut ---- *)

(* the read-only view below a written stack window is kept (the read-only span lies in the image: decision 17's
   RELRO_IMG form) *)
Lemma bl_arodata_munch : forall B (H : word -> bool) (m m' : word -> option byte) rlo rhi lo hi,
  munch [(lo, hi)] m m' -> 0x5fe000 <= lo -> (forall a, rlo <= a < rhi -> in_img SEGS a) ->
  arodata_okS SEGS B rlo rhi (aview SEGS H m) -> arodata_okS SEGS B rlo rhi (aview SEGS H m').
Proof.
  intros B H m m' rlo rhi lo hi HM Hlo HRI HA a Ha Hno He.
  assert (Ra : 0x10000 <= a < 0x5fe000).
  { destruct Ha as [(sg & Hin & _ & Hr) | Hr].
    - exact (bl_img_low a (ex_intro _ sg (conj Hin Hr))).
    - exact (bl_img_low a (HRI a Hr)). }
  rewrite (bl_aview_munch lo hi m m' H a HM ltac:(lia) ltac:(lia)). exact (HA a Ha Hno He).
Qed.

(* image bytes that the read-only view gives, as garr8 *)
Lemma bl_garr8_ro : forall B (H : word -> bool) (m : word -> option byte) rlo rhi a (l : list byte),
  arodata_okS SEGS B rlo rhi (aview SEGS H m) ->
  (forall j, (j < length l)%nat ->
     rlo <= a + Z.of_nat j < rhi /\ ~ Exists (in_zr (a + Z.of_nat j)) (as_owned_static B) /\
     ~ (as_errno B <= a + Z.of_nat j < as_errno B + 4) /\
     yseg_rom SEGS (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j l (Z_to_bv 8 0))) ->
  garr8 SEGS (mrestrict H m) a (map (fun x : byte => bv_unsigned x) l).
Proof.
  intros B H m rlo rhi a l HA Hl j Hj. rewrite length_map in Hj.
  destruct (Hl j Hj) as (R1 & R2 & R3 & R4).
  pose proof (HA (a + Z.of_nat j) (or_intror R1) R2 R3) as Hv. rewrite R4 in Hv.
  unfold aview in Hv.
  destruct (lib.Reusable.YP09.mbyte SEGS (mrestrict H m) (a + Z.of_nat j)) as [y|] eqn:Ey; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as Hv.
  assert (Exy : y = nth j l (Z_to_bv 8 0)) by (apply bv_eq; exact Hv).
  pose proof (bv_unsigned_in_range 8 (nth j l (Z_to_bv 8 0))) as Hrg. change (bv_modulus 8) with 256 in Hrg.
  assert (En : nth j (map (fun x : byte => bv_unsigned x) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0))).
  { rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
    rewrite map_nth. reflexivity. }
  rewrite En. split; [|lia].
  intros k Hk. assert (k = 0%nat) by lia. subst k.
  replace (a + Z.of_nat j + Z.of_nat 0) with (a + Z.of_nat j) by lia.
  rewrite Ey, Exy. f_equal.
  rewrite lib.Reusable.YI04.le_byte_small by (cbn; lia).
  change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* a shadow cover is kept below a written stack window *)
Lemma bl_hull_munch : forall lo hi (m m' : word -> option byte) (H : word -> bool) x n,
  munch [(lo, hi)] m m' -> 0 <= x -> x + n <= 2 ^ 47 -> 2 ^ 45 <= lo ->
  shadow_hull_vis (aview SEGS H m) x n -> shadow_hull_vis (aview SEGS H m') x n.
Proof.
  intros lo hi m m' H x n HM H0 H1 Hlo HH s Hs.
  assert (Bs : 0 <= s < 2 ^ 45).
  { unfold shadow_addr, SHADOW_OFF in Hs.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (2147450880 + x / 8) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (x + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.mul_div_le (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)). lia. }
  rewrite (bl_aview_munch lo hi m m' H s HM ltac:(lia) ltac:(lia)). exact (HH s Hs).
Qed.

(* an output range inside a caller frame is apart from a range of image bytes *)
Lemma bl_dj_frame_img : forall B ly S (W : world SEGS) mem md cid pos o len f n,
  AR_laws SEGS B -> AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> 0 < len -> 0 < n ->
  (forall a, o <= a < o + len -> in_zr a (frame_rng ly (cid, pos))) ->
  (forall a, f <= a < f + n -> in_img SEGS a) ->
  RcLay.ly_dj o (o + len) f (f + n).
Proof.
  intros B ly S W mem md cid pos o len f n LAWS HAR Hin Hlen Hn Ho Hf. unfold RcLay.ly_dj.
  destruct (Z_le_gt_dec (o + len) f) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (f + n) o) as [H2|H2]; [right; exact H2|].
  exfalso.
  assert (Ha1 : o <= Z.max o f < o + len) by lia.
  assert (Ha2 : f <= Z.max o f < f + n) by lia.
  pose proof (Ho _ Ha1) as Hz. unfold frame_rng, in_zr in Hz. cbn [fst snd] in Hz.
  destruct (al_client_img _ _ LAWS ly S W mem md (Z.max o f) HAR
              (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Hz)))))) as [_ Hni].
  exact (Hni (Hf _ Ha2)).
Qed.

Lemma bl_go : forall o md b, ba_go o md b = true -> o <> 0 /\ md <> 0 /\ b <= 6.
Proof.
  intros o md b H. unfold Prog.reac_ctrl_build_as_c.ba_go in H.
  apply andb_true_iff in H as [H Hb]. apply andb_true_iff in H as [Ho Hm].
  apply negb_true_iff, Z.eqb_neq in Ho. apply negb_true_iff, Z.eqb_neq in Hm. apply Z.leb_le in Hb.
  auto.
Qed.

(* the callee-saved registers of a state whose x1..x4, x8, x9, x18..x27 are the walk's *)
Lemma bl_aregs : forall (regs : bvmap 5 word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  aregs_preserved regs
    (mkR (ygetr regs 1) (ygetr regs 2) (ygetr regs 3) (ygetr regs 4) t0 t1 t2 (ygetr regs 8) (ygetr regs 9)
         a0 a1 a2 a3 a4 a5 a6 a7 (ygetr regs 18) (ygetr regs 19) (ygetr regs 20) (ygetr regs 21) (ygetr regs 22)
         (ygetr regs 23) (ygetr regs 24) (ygetr regs 25) (ygetr regs 26) (ygetr regs 27) t3 t4 t5 t6).
Proof.
  intros. intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [-> | Hc]; [reflexivity |]). subst r. reflexivity.
Qed.

(* the window case of awr_byte from a one-interval munch *)
Lemma bl_not_outside1 : forall lo hi a, ~ outside [(lo, hi)] a -> lo <= a < hi.
Proof.
  intros lo hi a H. cbn [outside] in H.
  destruct (Z_le_gt_dec lo a) as [H1|H1]; [|exfalso; apply H; split; [lia | exact I]].
  destruct (Z_lt_ge_dec a hi) as [H2|H2]; [lia|exfalso; apply H; split; [lia | exact I]].
Qed.

Lemma bl_awr_window : forall STK sp0 (FP : list (Z * Z)) bl0 blc ly own lo hi,
  sp0 - STK <= lo -> hi <= sp0 ->
  forall a, 0 <= a < 2 ^ 64 -> ~ outside [(lo, hi)] a -> awr_byte STK sp0 FP bl0 blc ly own a.
Proof.
  intros STK sp0 FP bl0 blc ly own lo hi H1 H2 a _ Ha. pose proof (bl_not_outside1 lo hi a Ha). left. lia.
Qed.

(* a range of the image (resp. of application memory) whose world view is addressable is lib.Lib-addressable *)
Lemma bl_addr_img : forall (W : world SEGS) (m : word -> option byte) a n,
  0x10000 <= a -> 0 <= n -> a + n <= 0x5fe000 ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n -> AsanRT.addressable m a n.
Proof.
  intros W m a n H1 H2 H3 HR. apply (bl_addr_of_ra W m a n); [lia | lia | unfold AsanRT.APPMEM_END; lia | | exact HR].
  intros i Hi. unfold AsanRT.app_mem, AsanRT.LOWMEM_END. lia.
Qed.

Lemma bl_addr_app : forall (W : world SEGS) (m : word -> option byte) a n,
  in_app a n -> 0 <= n ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n -> AsanRT.addressable m a n.
Proof.
  intros W m a n HA Hn HR. pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
  pose proof HA as [H0 H].
  apply (bl_addr_of_ra W m a n); [lia | lia | | exact (bl_app_of_in_app a n HA) | exact HR].
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H. unfold AsanRT.APPMEM_END. lia.
Qed.

(* the bytes a garr8 reads are visible *)
Lemma bl_vis_of_garr8 : forall (W : world SEGS) (m : word -> option byte) a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W) m) a (map (fun x : byte => bv_unsigned x) bs) ->
  ProgBridge.range_visible (w_H W) a (Z.of_nat (length bs)).
Proof.
  intros W m a bs H0 H1 HG. destruct (bl_bytes_of_garr8 W m a bs H0 H1 HG) as [_ Hv].
  split; [exact H0|]. split; [exact H1|]. intros x Hx.
  replace x with (a + (x - a)) by lia. apply Hv. lia.
Qed.

(* ctrl_emit_as's result on row (ba_row b) is reac_ctrl_build_as's (lib/Prog/reac_ctrl_build_as.v ba_E_eq,
   ba_len_eq) *)
Lemma bl_R : forall o md b n (mb : list byte), 0 <= b <= 6 -> ba_go o md b = true ->
  let row := Prog.reac_ctrl_build_as_c.ba_fr (ba_row b) in
  (if RcEmit.em_E (RcFin.ubat row 21) (RcFin.ubat row 22) n (RcEmit.em_hid mb)
   then RcEmit.em_len (RcFin.ubat row 21) n else 0) =
  (if ba_go o md b && Prog.reac_ctrl_build_as_c.ba_E n mb b then 52 + 36 * n else 0).
Proof.
  intros o md b n mb Hb HG. cbv zeta.
  rewrite reac_ctrl_build_as.ba_E_eq by exact Hb. rewrite HG. cbn [andb].
  rewrite reac_ctrl_build_as.ba_len_eq by exact Hb. reflexivity.
Qed.

(* ctrl_emit_as's closing facts on row (ba_row b), in reac_ctrl_build_as's terms *)
Lemma bl_closes : forall b md (mb nb : list byte), 0 <= b <= 6 ->
  let row := Prog.reac_ctrl_build_as_c.ba_fr (ba_row b) in
  let lay := RcLay.ly_lay (RcLay.ly_k row) [] (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k row))) 0
               (RcLay.ly_ao row) (RcLay.ly_al row) [] in
  let blk := RcFin.fin (RcFin.ubat row 20) (RcFin.ubat row 18) (RcFin.ubat row 19) lay in
  (RcFin.ubat row 20 = 1 \/ RcFin.ubat row 20 = 2 ->
     RcFin.closes (RcFin.ubat row 20) (RcFin.ubat row 18) (RcFin.ubat row 19) blk /\
     (RcFin.closes (RcFin.ubat row 20) (RcFin.ubat row 18) (RcFin.ubat row 19) lay -> blk = lay)) ->
  (b <= 1 -> RcModel.blocksum (Prog.reac_ctrl_build_as_c.ba_X md mb nb b) = 0) /\
  (RcModel.blocksum (RcLay.ly_Z md mb nb b) = 0 ->
     Prog.reac_ctrl_build_as_c.ba_X md mb nb b = RcLay.ly_Z md mb nb b).
Proof.
  intros b md mb nb Hb. cbv zeta. intros HCL.
  pose proof (bl_blk b md mb nb Hb) as Hblk. cbv zeta in Hblk. rewrite Hblk in HCL.
  destruct (bl_row_facts b Hb) as (_ & Hk & Hr & Hbb & H20 & _ & _ & _ & H18 & H19 & Hao & Hal & _).
  rewrite Hk, Hbb, Hao, Hal in HCL. rewrite reac_ctrl_build_as.ba_lay in HCL by lia.
  rewrite H18, H19 in HCL.
  destruct (Z.leb_spec b 1) as [Hb1 | Hb1].
  - rewrite H20 in HCL. cbv iota in HCL.
    destruct (HCL (or_introl eq_refl)) as [[Hbs _] Himp]. split; [intros _; exact Hbs|].
    intros Hz. apply Himp. split; [exact Hz | intros Hc; discriminate Hc].
  - split; [intros Hc; lia|]. intros _. unfold Prog.reac_ctrl_build_as_c.ba_X.
    rewrite (proj2 (Z.leb_gt b 1) Hb1). reflexivity.
Qed.

(* ---- decision 10's check, by computation over image B's bundle tables (CtrlTSyms: ts_zsh, ts_owned, ts_errno):
   the switch table [0x21980, 0x219b8) lies in a zero-shadow range ((0x21980, 0x38) of Tfib_zero_shadow), and the
   CTRL_FRAMES rows 3..9 [0xa0648, 0xa06f0) in no owned-static range, away from errno ---- *)
Lemma bl_in_of_existsb : forall (l : list (Z * Z)) q m,
  existsb (fun r => (fst r =? q) && (snd r =? m)) l = true -> In (q, m) l.
Proof.
  intros l q m H. apply existsb_exists in H as ([q' m'] & Hin & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.eqb_eq in H1, H2. cbn [fst snd] in H1, H2. subst. exact Hin.
Qed.

Lemma bl_ts_zs_sw : forall B, lib.Reusable.YF0m.CtrlTSyms B -> in_zs B 0x21980 56.
Proof.
  intros B TS. exists 0x21980, 0x38. rewrite (lib.Reusable.YF0m.ts_zsh _ TS).
  split; [apply bl_in_of_existsb; vm_compute; reflexivity | lia].
Qed.

Lemma bl_ts_rows_ro : forall B, lib.Reusable.YF0m.CtrlTSyms B -> forall a, 0xa0648 <= a < 0xa06f0 ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros B TS a Ha. rewrite (lib.Reusable.YF0m.ts_owned _ TS), (lib.Reusable.YF0m.ts_errno _ TS).
  assert (C : forallb (fun r => (fst r + snd r <=? 0xa0648) || (0xa06f0 <=? fst r))
                lib.Reusable.YF0m.Tfib_owned_static = true) by (vm_compute; reflexivity).
  split.
  - intros HE. apply Exists_exists in HE as (r & Hin & Hz).
    rewrite forallb_forall in C. specialize (C r Hin). unfold in_zr in Hz.
    apply orb_true_iff in C as [C | C]; apply Z.leb_le in C; lia.
  - unfold lib.Reusable.YF0m.TFIB_ERRNO. lia.
Qed.

(* The CTRL_FRAMES row ctrl_emit_as reads (rows 3..9 of the global (0xa0600, 264), PT_GNU_RELRO) is a read-only
   registered global range in a Theorem Labs lane's tctrl_lay_block_ro form (C_ctrl_lay_block.v (at head lib/B/Prog/C_ctrl_lay_block.v:89-93; written on a working branch 079649851ae)), over a read-only
   span [rlo, rhi) that contains CTRL_FRAMES [0xa0600, 0xa0708) and the registered-globals list GLOBS, given that
   CTRL_FRAMES is listed in GLOBS. *)
Lemma bl_fr_ro : forall B (GLOBS : list (Z * Z)) (rlo rhi : Z), lib.Reusable.YF0m.CtrlTSyms B ->
  In (0xa0600, 264) GLOBS -> rlo <= 0xa0600 -> 0xa0708 <= rhi ->
  forall b, 0 <= b <= 6 ->
  let q := 0xa0600 + 24 * ba_row b in
  (exists q0 sz, In (q0, sz) GLOBS /\ q0 <= q /\ q + 24 <= q0 + sz) /\
  CtrlRo.IMG_LO + 64 <= q /\ q + 24 + 64 <= CtrlRo.IMG_HI /\
  (forall x, q <= x < q + 24 -> lib.Reusable.APostBase.in_roP SEGS rlo rhi x /\
     ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)).
Proof.
  intros B GLOBS rlo rhi TS Hin Hlo Hhi b Hb. cbv zeta.
  destruct (bl_row_facts b Hb) as (_ & _ & Hr & _).
  unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI.
  split; [exists 0xa0600, 264; split; [exact Hin | lia]|].
  split; [lia|]. split; [lia|].
  intros x Hx. split; [right; lia|]. exact (bl_ts_rows_ro B TS x ltac:(lia)).
Qed.

End b.
