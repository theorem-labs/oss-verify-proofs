(* fuzz_ctrl image A, reac_ctrl_parse: the world facts the cgif-form glue (C_reac_ctrl_parseP.v) feeds to the lifted
   footprint stretches (reac_ctrl_parseF_pre.v at the entry; reac_ctrl_parseF_rpost.v at the return of
   __asan_stack_malloc_1).  Every fact comes from the core's world (AR, ajournal) through a Theorem Labs lane's ProgWorld
   lemmas (taken by path on the glue base) and a Theorem Labs lane's ProgBridge / MemNormTr; the memory a stretch runs on is
   MemNorm.normalize of a world memory.  Written by a Theorem Labs lane (glue lane).  rule 24: proof-index
   reac_ctrl_parse (2026-10-28 21:05Z, exit 0): 12 named files, plain / ubsan builds of other units;
   checker a Theorem Labs lane: CONFIRM. At ossv/recipes c5e779efe8c (2026-10-31), released ASan walks of reac_ctrl_parse exist in fuzz_grant, fuzz_disco and fuzz_scene.
   Twin families: every name of a doubled family is reached through a full-path Module alias below (lib.Reusable, lib.Lib,
   lib.A.MemNorm and friends), never bare. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YK04R YA0n YA0nR YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0n YG0d YG0v YG0s YCbq YP09 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorld ProgWorld_Fs ProgWorldAstack ProgWorldCtlRt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldRt ProgWorldRtRo ProgWorldRtShadow ProgWorldShadow.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldVisWin ProgWorldVisHeap ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgBridge MemNorm MemNormF MemNormTr AF0m AB1v AsanRT Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c RcAsanFP RcAsanFPLib rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_parse_c CtrlBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame ExecF MState Regs6ss.
Import ListNotations.
Local Open Scope Z_scope.

Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module RK04R := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04R.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module R00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module R01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module R0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module R0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module R0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module R0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
Module R0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0s.
Module Rbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module PW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld.
Module PWF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld_Fs.
Module PWA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldAstack.
Module PWC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldCtlRt.
Module PWR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldRt.
Module PWS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldShadow.
Module PWVW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisWin.
Module PWVH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisHeap.
Module PWVF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisFrame.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Module MNT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormTr.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module IB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Local Notation segs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AB1v.tfibsegs (only parsing).
Local Notation rsegs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.rsegs (only parsing).

(* ---------------------------------------------------------------------------------------------------------
   1. Visibility and presence, byte by byte. *)

Lemma pz_rv_of_present : forall (H : word -> bool) (m : word -> option byte) lo len,
  0 <= lo -> lo + len <= 2 ^ 64 -> (forall a, lo <= a < lo + len -> R0n.apresent H m a) -> PB.range_visible H lo len.
Proof. intros H m lo len H0 H1 HP. split; [exact H0|]. split; [exact H1|]. intros a Ha. exact (proj1 (HP a Ha)). Qed.

Lemma pz_rv_sub : forall H lo len lo' len',
  PB.range_visible H lo len -> lo <= lo' -> 0 <= len' -> lo' + len' <= lo + len -> PB.range_visible H lo' len'.
Proof. exact PB.range_visible_sub. Qed.

(* the footprint form: a visible range is a range of RNG_W *)
Lemma pz_rng : forall H lo len, PB.range_visible H lo len -> LE.rng (PB.RNG_W H) lo len.
Proof. exact PB.rng_of_visible. Qed.

Section W.
Context {fx : RK11.FPState} {rc : RM05.RunCeil} {SK : RI16.sink_head}.
Variable B : R0f.asyms.

(* The side stack's bytes are visible (am_areas over (AF 0, kFakeStackSize); ProgWorld_Fs.pw_F_present). *)
Lemma pz_F_vis : forall ly S (W : RA0n.world segs) m md, R0n.AR segs B ly S W m md ->
  PB.range_visible (RA0n.w_H W) (R0f.ly_F ly) R0f.kFakeStackSize.
Proof.
  intros ly S W m md HAR. pose proof HAR as (M & _).
  pose proof (R0n.am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (R0f.lo_app _ LO) _ (PWF.pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (PWF.pw_ext_range _ _ F1) as [F0 F2].
  apply (pz_rv_of_present _ m); [lia | lia |].
  intros a Ha. exact (PWF.pw_F_present B ly S W m md a HAR Ha).
Qed.

(* The shadow of the side stack's frame area is present (am_areas over its last entry, (ASh (AF kFakeFramesOff),
   (kFakeStackSize - kFakeFramesOff) / 8), YG0n.v:139). The proof is pw_F_present's (ProgWorld_Fs.v:266-283) at that
   entry. *)
Lemma pz_Fsh_present : forall ly S (W : RA0n.world segs) m md a, R0n.AR segs B ly S W m md ->
  R0f.shadow_addr (R0f.ly_F ly + R0f.kFakeFramesOff) <= a <
    R0f.shadow_addr (R0f.ly_F ly + R0f.kFakeFramesOff) + (R0f.kFakeStackSize - R0f.kFakeFramesOff) / 8 ->
  R0n.apresent (RA0n.w_H W) m a.
Proof.
  intros ly S W m md a (M & L & _) Ha.
  pose proof (R0n.am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (R0f.lo_app _ LO) _ (PWF.pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (PWF.pw_ext_range _ _ F1) as [F0 F2].
  pose proof (R0f.lo_img _ LO) as (I1 & I2 & I3 & I4).
  pose proof (R0n.am_areas _ _ _ _ M) as AA. unfold R0n.aareas in AA.
  apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA].
  apply Forall_cons_iff in AA as [_ AA]. apply Forall_cons_iff in AA as [_ AA].
  apply Forall_cons_iff in AA as [_ AA]. apply Forall_cons_iff in AA as [_ AA].
  apply Forall_cons_iff in AA as [_ AA]. apply Forall_cons_iff in AA as [ASH _].
  specialize (ASH (a - R0f.shadow_addr (R0f.ly_F ly + R0f.kFakeFramesOff)) ltac:(cbn [snd]; clear -Ha; lia)).
  cbn [fst R0f.aeval] in ASH.
  replace (R0f.shadow_addr (R0f.ly_F ly + R0f.kFakeFramesOff) +
           (a - R0f.shadow_addr (R0f.ly_F ly + R0f.kFakeFramesOff))) with a in ASH by lia.
  assert (HDlo : 0 <= (R0f.ly_F ly + R0f.kFakeFramesOff) / 8)
    by (apply Z.div_pos; [clear -F0; unfold R0f.kFakeFramesOff; lia | lia]).
  assert (HDhi : (R0f.ly_F ly + R0f.kFakeFramesOff) / 8 <= R0f.ly_F ly + R0f.kFakeFramesOff)
    by (apply Z.div_le_upper_bound; [lia | clear -F0; unfold R0f.kFakeFramesOff; lia]).
  assert (HSH : (R0f.kFakeStackSize - R0f.kFakeFramesOff) / 8 = 1441792) by reflexivity.
  assert (HE : R0f.shadow_addr (R0f.ly_F ly + R0f.kFakeFramesOff) =
               R0f.SHADOW_OFF + (R0f.ly_F ly + R0f.kFakeFramesOff) / 8) by reflexivity.
  apply (R0s.aview_present segs ly S md (RA0n.w_H W) m a L).
  - clear -Ha F0 F2 HDlo HDhi HSH HE. rewrite HE, HSH in Ha.
    unfold R0f.SHADOW_OFF, R0f.kFakeFramesOff, R0f.kFakeStackSize in *. lia.
  - unfold R0n.in_zr. rewrite I1. clear -Ha I2 I3 HDlo HE HSH.
    rewrite HE, HSH in Ha. unfold R0f.SHADOW_OFF, R0f.kImgLo, R0f.kImgEnd in *. lia.
  - exact ASH.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The side stack in ctrl's vocabulary (FS = ly_F ly, FS_SIZE = kFakeStackSize): its bytes, and the shadow
   of its frame area, are visible.  These give the Section premises RFLG / RFRM / RFSS / SCFR / SKFR of
   reac_ctrl_parseF.v at RNG := RNG_W (w_H W). *)

Lemma pz_side_vis : forall ly S (W : RA0n.world segs) m md lo len, R0n.AR segs B ly S W m md ->
  R0f.ly_F ly <= lo -> 0 <= len -> lo + len <= R0f.ly_F ly + SMC.FS_SIZE ->
  PB.range_visible (RA0n.w_H W) lo len.
Proof.
  intros ly S W m md lo len HAR H1 H2 H3.
  assert (ESZ : SMC.FS_SIZE = R0f.kFakeStackSize) by reflexivity.
  eapply pz_rv_sub; [exact (pz_F_vis ly S W m md HAR) | lia | lia | rewrite ESZ in H3; lia].
Qed.

(* One shadow byte of the side stack's frame area ([FS + kFakeFramesOff, FS + FS_SIZE)) is visible. *)
Lemma pz_sh1_vis : forall ly S (W : RA0n.world segs) m md x, R0n.AR segs B ly S W m md ->
  R0f.ly_F ly + R0f.kFakeFramesOff <= x < R0f.ly_F ly + SMC.FS_SIZE ->
  PB.range_visible (RA0n.w_H W) (R0f.shadow_addr x) 1.
Proof.
  intros ly S W m md x HAR Hx.
  assert (ESZ : SMC.FS_SIZE = R0f.kFakeStackSize) by reflexivity. rewrite ESZ in Hx.
  pose proof HAR as (M & _).
  pose proof (R0n.am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (R0f.lo_app _ LO) _ (PWF.pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (PWF.pw_ext_range _ _ F1) as [F0 F2].
  assert (HE : forall y, R0f.shadow_addr y = R0f.SHADOW_OFF + y / 8) by reflexivity.
  assert (HIN : R0f.shadow_addr (R0f.ly_F ly + R0f.kFakeFramesOff) <= R0f.shadow_addr x <
                R0f.shadow_addr (R0f.ly_F ly + R0f.kFakeFramesOff) +
                  (R0f.kFakeStackSize - R0f.kFakeFramesOff) / 8).
  { rewrite !HE. pose proof (R0f.lo_F_al _ LO) as FAL. unfold R0f.page_aligned in FAL.
    clear -Hx F0 F2 FAL. unfold R0f.kFakeFramesOff, R0f.kFakeStackSize in *.
    Z.div_mod_to_equations. lia. }
  apply (pz_rv_of_present _ m).
  - rewrite HE. clear -Hx F0 F2.
    assert (0 <= x / 8) by (apply Z.div_pos; [unfold R0f.kFakeFramesOff in *; lia | lia]).
    unfold R0f.SHADOW_OFF. lia.
  - rewrite HE. clear -Hx F0 F2.
    assert (x / 8 <= x) by (apply Z.div_le_upper_bound; [lia | unfold R0f.kFakeFramesOff in *; lia]).
    unfold R0f.SHADOW_OFF, R0f.kFakeStackSize, R0f.kFakeFramesOff in *. lia.
  - intros a Ha. replace a with (R0f.shadow_addr x) by lia.
    exact (pz_Fsh_present ly S W m md (R0f.shadow_addr x) HAR HIN).
Qed.

(* The class-1 flag array and frame area of ctrl's geometry, as ranges of the side stack. *)
Lemma pz_flag_vis : forall ly S (W : RA0n.world segs) m md j n, R0n.AR segs B ly S W m md ->
  SMC.ASAN_GT <= R0f.ly_F ly -> 0 <= j -> 0 <= n -> j + n <= SMC.fs_M 1 ->
  PB.range_visible (RA0n.w_H W) (SMC.fs_flag (R0f.ly_F ly) 1 j) n.
Proof.
  intros ly S W m md j n HAR HGT Hj Hn Hjn.
  unfold SMC.fs_flag. cbn [Z.of_nat Pos.of_succ_nat].
  change (SMC.fs_M 1) with 8192 in Hjn. change (2 ^ 15) with 32768. change (2 ^ (15 - 1)) with 16384.
  eapply pz_side_vis; [exact HAR | lia | lia |]. unfold SMC.FS_SIZE. lia.
Qed.

Lemma pz_frame_vis : forall ly S (W : RA0n.world segs) m md j n, R0n.AR segs B ly S W m md ->
  0 <= j -> 0 <= n -> j * SMC.fs_B 1 + n <= SMC.fs_M 1 * SMC.fs_B 1 ->
  PB.range_visible (RA0n.w_H W) (SMC.fs_frame (R0f.ly_F ly) 1 j) n.
Proof.
  intros ly S W m md j n HAR Hj Hn Hjn.
  unfold SMC.fs_frame. cbn [Z.of_nat Pos.of_succ_nat].
  change (SMC.fs_M 1 * SMC.fs_B 1) with 1048576 in Hjn. change (2 ^ 20) with 1048576.
  eapply pz_side_vis; [exact HAR | | lia |]; unfold SMC.FS_SIZE, SMC.fs_B in *; cbn [Z.of_nat] in *;
    change (2 ^ 1) with 2 in *; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   3. A present window above the image is a stack window of the normalized memory a stretch runs on
   (ProgWorld_Fs.pw_stk_of_present, then MemNormTr.stk_normalize_ro). *)
Lemma pz_win_stk_norm : forall (W : RA0n.world segs) (m : word -> option byte) lo hi,
  MN.ro_agree rsegs m -> IB.IMG_HI <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> R0n.apresent (RA0n.w_H W) m a) ->
  LF.stk rsegs (MN.normalize rsegs m) lo hi.
Proof.
  intros W m lo hi RA Hlo Hhi HP.
  apply MNT.stk_normalize_ro; [exact RA | exact Hlo |].
  apply (PWF.pw_stk_of_present W m lo hi); [unfold IB.IMG_HI in Hlo; lia | exact Hhi | exact HP].
Qed.

End W.
