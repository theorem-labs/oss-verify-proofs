(* lib/A/Prog/C_reac_ctrl_parseVS.v -- fuzz_ctrl image A (asan, libreac v1.9.0): the side-stack facts of
   reac_ctrl_parse's call of __asan_stack_malloc_1 (the class-1 fake frame) and the .str.4 constant cover, at a state the
   core's AR describes: the Section premises RFLG / RFRM / SCFR / SKFR and BC / SKBC of reac_ctrl_parseF.v (SetupF) at
   RNG := ProgBridge.RNG_W (w_H W), for the cgif-form glue (fuzz_ctrl row A-PARSE-VS (a working note, not in this delivery); statements fixed by a Theorem Labs lane).
   Route (C) only: AR's areas and layout (ProgWorld_Fs.pw_F_present, the side stack's frame-area shadow entry of
   YG0n.aareas, YG0f.lo_F_al), AR's const rows (ProgWorldShadow.ctl_gshadow_of_AR at .str.4's shadow row
   z1 (ANum 0x7fffc240) 0x7, ctl_const_vis_of_AR at the rows 0x7fffc240 .. 0x7fffc247 of AF0m.Tfib_const_shadow).
   No VIS0, OWNED_RO, ctlrt_of_AR, shadow_rw_of_AR or rt_of_core.  The side-stack shadow step is the proof of
   lib/A/Prog/C_reac_ctrl_parseW.v pz_Fsh_present, restated here so this file Requires only C_reac_ctrl_parseV.v's
   header.  Header and aliases are C_reac_ctrl_parseV.v's (twin rule: every project module is Required without Import
   and named through a full-path Module alias).
   rule 24: no function proved (proof-index rcpVS_side / rcpVS_bc: 0 hits; two side lemmas for one call site). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Cells Step PropExec MState ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AsanRT MemNorm MemNormTr ProgBridge AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorld ProgWorld_Fs ProgWorldAstack ProgWorldShadow.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldVisWin ProgWorldVisFrame ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldCtlRtC ProgWorldRtC ACtlRtC ACtlK ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgWorldTlsApart ProgWorldTlsOwned ProgWorldBlkApart.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds rng_asan asan_stack_malloc_c RcAsanFP
  RcAsanFPLib asan_stack_malloc_c_on sh_word_on reac_ctrl_parse_c reac_ctrl_parseF bcmp_wrap_c memcmp_c CtrlBase CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YA0n YM05 YI16 YG0f YG0d YCbq YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0n YG0v YE01 YG0a YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YConstIn.
Import ListNotations.
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module AI0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Module MNT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormTr.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgBridge.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.
Module PW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld.
Module PWF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorld_Fs.
Module PWA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldAstack.
Module PWS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldShadow.
Module PWVW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisWin.
Module PWVF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisFrame.
Module PWVH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldVisHeap.
Module PWCC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldCtlRtC.
Module PWRC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldRtC.
Module PWTA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldTlsApart.
Module PWTO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldTlsOwned.
Module PWBA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldBlkApart.
Module ARC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlRtC.
Module AK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlK.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module IB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Module RA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP.
Module FPL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFPLib.
Module SMO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c_on.
Module SWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.
Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parse_c.
Module PF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Module CB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlBase.
Module CR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlRo.
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RG0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RG0a := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0a.
Module RG0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0s.
Module RG0q := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0q.
Module RE01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module RP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Local Notation rsegs := AI0.rsegs (only parsing).

(* A range whose every byte is present in the core's view is a range of RNG_W. *)
Lemma rcpVS_rng_of_present : forall (H : word -> bool) (m : word -> option byte) lo len,
  0 <= lo -> lo + len <= 2 ^ 64 -> (forall a, lo <= a < lo + len -> RG0n.apresent H m a) ->
  LX.rng (PB.RNG_W H) lo len.
Proof.
  intros H m lo len H0 H1 HP. apply PB.rng_of_visible.
  split; [exact H0|]. split; [exact H1|]. intros a Ha. exact (proj1 (HP a Ha)).
Qed.

(* The 8 shadow bytes of .str.4's granule [0x21200, 0x21208) are rows of the const table (AF0m.Tfib_const_shadow). *)
Lemma rcpVS_bc_row : forall ly y, 0x7fffc240 <= y < 0x7fffc248 ->
  exists v, 0 <= v < 256 /\ In (RG0f.z1 (RG0f.ANum y) v) (AF.Tfib_const ly).
Proof.
  intros ly y Hy. unfold AF.Tfib_const.
  assert (Hc : y = 0x7fffc240 \/ y = 0x7fffc241 \/ y = 0x7fffc242 \/ y = 0x7fffc243 \/
               y = 0x7fffc244 \/ y = 0x7fffc245 \/ y = 0x7fffc246 \/ y = 0x7fffc247) by lia.
  destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst y;
    [exists 7 | exists 0xf9 | exists 0xf9 | exists 0xf9 | exists 5 | exists 0xf9 | exists 0xf9 | exists 0xf9];
    (split; [lia | lib.Reusable.YConstIn.in_const_tbl]).
Qed.

(* .str.4's shadow row: z1 (ANum (shadow_addr 0x21200)) 7, shadow_addr 0x21200 = 0x7fffc240. *)
Lemma rcpVS_bc_shrow : forall ly,
  In (RG0f.z1 (RG0f.ANum (RG0f.shadow_addr 0x21200)) 7) (AF.Tfib_const ly).
Proof. intros ly. unfold AF.Tfib_const. lib.Reusable.YConstIn.in_const_tbl. Qed.

Section VS.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.
Hypothesis TS : A.AF0m.CtrlTSyms B.
(* AR_laws of the bundle: the core's own proof (lib/Reusable/YG0q.v AR_laws_ok), no premise. *)
Local Notation LAWS := (RG0q.AR_laws_ok rsegs B).

(* The shadow of the side stack's frame area is present (am_areas over its last entry, (ASh (AF kFakeFramesOff),
   (kFakeStackSize - kFakeFramesOff) / 8)): C_reac_ctrl_parseW.v pz_Fsh_present's proof. *)
Lemma rcpVS_Fsh_present : forall ly S (W : RA0n.world rsegs) m md a, RG0n.AR rsegs B ly S W m md ->
  RG0f.shadow_addr (RG0f.ly_F ly + RG0f.kFakeFramesOff) <= a <
    RG0f.shadow_addr (RG0f.ly_F ly + RG0f.kFakeFramesOff) + (RG0f.kFakeStackSize - RG0f.kFakeFramesOff) / 8 ->
  RG0n.apresent (RA0n.w_H W) m a.
Proof.
  intros ly S W m md a (M & L & _) Ha.
  pose proof (RG0n.am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (RG0f.lo_app _ LO) _ (PWF.pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (PWF.pw_ext_range _ _ F1) as [F0 F2].
  pose proof (RG0f.lo_img _ LO) as (I1 & I2 & I3 & I4).
  pose proof (RG0n.am_areas _ _ _ _ M) as AA. unfold RG0n.aareas in AA.
  apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA].
  apply Forall_cons_iff in AA as [_ AA]. apply Forall_cons_iff in AA as [_ AA].
  apply Forall_cons_iff in AA as [_ AA]. apply Forall_cons_iff in AA as [_ AA].
  apply Forall_cons_iff in AA as [_ AA]. apply Forall_cons_iff in AA as [ASH _].
  specialize (ASH (a - RG0f.shadow_addr (RG0f.ly_F ly + RG0f.kFakeFramesOff)) ltac:(cbn [snd]; clear -Ha; lia)).
  cbn [fst RG0f.aeval] in ASH.
  replace (RG0f.shadow_addr (RG0f.ly_F ly + RG0f.kFakeFramesOff) +
           (a - RG0f.shadow_addr (RG0f.ly_F ly + RG0f.kFakeFramesOff))) with a in ASH by lia.
  assert (HDlo : 0 <= (RG0f.ly_F ly + RG0f.kFakeFramesOff) / 8)
    by (apply Z.div_pos; [clear -F0; unfold RG0f.kFakeFramesOff; lia | lia]).
  assert (HDhi : (RG0f.ly_F ly + RG0f.kFakeFramesOff) / 8 <= RG0f.ly_F ly + RG0f.kFakeFramesOff)
    by (apply Z.div_le_upper_bound; [lia | clear -F0; unfold RG0f.kFakeFramesOff; lia]).
  assert (HSH : (RG0f.kFakeStackSize - RG0f.kFakeFramesOff) / 8 = 1441792) by reflexivity.
  assert (HE : RG0f.shadow_addr (RG0f.ly_F ly + RG0f.kFakeFramesOff) =
               RG0f.SHADOW_OFF + (RG0f.ly_F ly + RG0f.kFakeFramesOff) / 8) by reflexivity.
  apply (RG0s.aview_present rsegs ly S md (RA0n.w_H W) m a L).
  - clear -Ha F0 F2 HDlo HDhi HSH HE. rewrite HE, HSH in Ha.
    unfold RG0f.SHADOW_OFF, RG0f.kFakeFramesOff, RG0f.kFakeStackSize in *. lia.
  - unfold RG0n.in_zr. rewrite I1. clear -Ha I2 I3 HDlo HE HSH.
    rewrite HE, HSH in Ha. unfold RG0f.SHADOW_OFF, RG0f.kImgLo, RG0f.kImgEnd in *. lia.
  - exact ASH.
Qed.

Lemma rcpVS_side : forall ly S (W : RA0n.world rsegs) m md,
  RG0n.AR rsegs B ly S W m md ->
  LX.rng (PB.RNG_W (RA0n.w_H W)) (SMC.fs_flag (RG0f.ly_F ly) 1 0) (SMC.fs_M 1) /\
  LX.rng (PB.RNG_W (RA0n.w_H W)) (SMC.fs_frame (RG0f.ly_F ly) 1 0)
    (SMC.fs_frame (RG0f.ly_F ly) 1 (SMC.fs_M 1) - SMC.fs_frame (RG0f.ly_F ly) 1 0) /\
  PF.shcov (PB.RNG_W (RA0n.w_H W)) (SMC.fs_frame (RG0f.ly_F ly) 1 0)
    (SMC.fs_frame (RG0f.ly_F ly) 1 (SMC.fs_M 1) - SMC.fs_frame (RG0f.ly_F ly) 1 0) /\
  PF.shkov (PB.RNG_W (RA0n.w_H W)) (SMC.fs_frame (RG0f.ly_F ly) 1 0)
    (SMC.fs_frame (RG0f.ly_F ly) 1 (SMC.fs_M 1) - SMC.fs_frame (RG0f.ly_F ly) 1 0).
Proof.
  intros ly S W m md HAR.
  pose proof HAR as (M & _).
  pose proof (RG0n.am_layout _ _ _ _ M) as LO.
  pose proof (proj1 (Forall_forall _ _) (RG0f.lo_app _ LO) _ (PWF.pw_F_in_owned ly)) as F1.
  cbn [fst snd] in F1. destruct (PWF.pw_ext_range _ _ F1) as [F0 F2].
  pose proof (RG0f.lo_F_al _ LO) as FAL. unfold RG0f.page_aligned in FAL.
  (* the side stack's bytes, and the shadow of its frame area, are present *)
  assert (HP : forall a, RG0f.ly_F ly <= a < RG0f.ly_F ly + RG0f.kFakeStackSize ->
                 RG0n.apresent (RA0n.w_H W) m a)
    by (intros a Ha; exact (PWF.pw_F_present B ly S W m md a HAR Ha)).
  assert (HS : forall a, RG0f.shadow_addr (RG0f.ly_F ly + RG0f.kFakeFramesOff) <= a <
                 RG0f.shadow_addr (RG0f.ly_F ly + RG0f.kFakeFramesOff) +
                   (RG0f.kFakeStackSize - RG0f.kFakeFramesOff) / 8 ->
                 RG0n.apresent (RA0n.w_H W) m a)
    by (intros a Ha; exact (rcpVS_Fsh_present ly S W m md a HAR Ha)).
  (* ctrl's class-1 geometry: flags [F + 20480, F + 28672), frames [F + 1085440, F + 2134016) *)
  assert (EFL : SMC.fs_flag (RG0f.ly_F ly) 1 0 = RG0f.ly_F ly + 20480).
  { unfold SMC.fs_flag. cbn [Z.of_nat Pos.of_succ_nat].
    change (2 ^ 15) with 32768. change (2 ^ (15 - 1)) with 16384. lia. }
  assert (EF0 : SMC.fs_frame (RG0f.ly_F ly) 1 0 = RG0f.ly_F ly + 1085440).
  { unfold SMC.fs_frame. cbn [Z.of_nat Pos.of_succ_nat]. change (2 ^ 20) with 1048576. lia. }
  assert (EFM : SMC.fs_frame (RG0f.ly_F ly) 1 (SMC.fs_M 1) = RG0f.ly_F ly + 2134016).
  { unfold SMC.fs_frame, SMC.fs_M, SMC.fs_B. cbn [Z.of_nat Pos.of_succ_nat].
    change (2 ^ 20) with 1048576. change (2 ^ (14 - 1)) with 8192. change (2 ^ 1) with 2. lia. }
  assert (EM : SMC.fs_M 1 = 8192) by reflexivity.
  rewrite EFM, EFL, EF0, EM.
  replace (RG0f.ly_F ly + 2134016 - (RG0f.ly_F ly + 1085440)) with 1048576 by lia.
  assert (HSH : (RG0f.kFakeStackSize - RG0f.kFakeFramesOff) / 8 = 1441792) by reflexivity.
  rewrite HSH in HS.
  unfold RG0f.shadow_addr, RG0f.SHADOW_OFF, RG0f.kFakeFramesOff in HS.
  unfold RG0f.kFakeStackSize in HP, F2.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold PF.shcov, PF.shkov.
  set (F := RG0f.ly_F ly) in *.
  split; [|split; [|split]].
  - (* RFLG *)
    apply (rcpVS_rng_of_present _ m); [lia | lia |]. intros a Ha. apply HP. lia.
  - (* RFRM *)
    apply (rcpVS_rng_of_present _ m); [lia | lia |]. intros a Ha. apply HP. lia.
  - (* SCFR: each shadow byte of the class-1 frame area *)
    intros x Hx. unfold ART.ASAN_K.
    apply (rcpVS_rng_of_present _ m).
    + clear -Hx F0. Z.div_mod_to_equations. lia.
    + clear -Hx F2 P64. Z.div_mod_to_equations. lia.
    + intros a Ha. apply HS. clear -Ha Hx F0 F2 FAL. Z.div_mod_to_equations. lia.
  - (* SKFR: the 8-aligned shadow cover of every sub-range of the class-1 frame area *)
    intros a b Ha Hab Hb. unfold ART.ASAN_K.
    apply (rcpVS_rng_of_present _ m).
    + clear -Ha F0. Z.div_mod_to_equations. lia.
    + clear -Hab Hb F2 P64. Z.div_mod_to_equations. lia.
    + intros y Hy. apply HS. clear -Hy Ha Hab Hb F0 F2 FAL. Z.div_mod_to_equations. lia.
Qed.

Lemma rcpVS_bc : forall ly S (W : RA0n.world rsegs) m md,
  RG0n.AR rsegs B ly S W m md ->
  ART.addressable m PC.REAC_CTRL_PARSE_BC 6 /\ PF.shkov (PB.RNG_W (RA0n.w_H W)) PC.REAC_CTRL_PARSE_BC 6.
Proof.
  intros ly S W m md HAR. unfold PC.REAC_CTRL_PARSE_BC.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  split.
  - (* addressable: .str.4's shadow row z1 (ANum 0x7fffc240) 7 (k = 7 > 6 bytes) *)
    exact (PWS.ctl_gshadow_of_AR B TS LAWS ly S W m md 0x21200 7 0x21200 6 HAR (rcpVS_bc_shrow ly)
             eq_refl ltac:(unfold RG0f.kImgLo; lia) ltac:(unfold RG0f.kImgEnd; lia)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* SKBC: the cover is the one granule [0x7fffc240, 0x7fffc248), each byte a visible const row *)
    unfold PF.shkov. intros a b Ha Hab Hb.
    assert (Ea : (a / 8 + ART.ASAN_K) / 8 * 8 = 0x7fffc240)
      by (clear -Ha Hab Hb; unfold ART.ASAN_K; Z.div_mod_to_equations; lia).
    assert (Eb : (b / 8 + ART.ASAN_K) / 8 * 8 = 0x7fffc240)
      by (clear -Ha Hab Hb; unfold ART.ASAN_K; Z.div_mod_to_equations; lia).
    rewrite Ea, Eb. apply PB.rng_of_visible.
    split; [lia|]. split; [lia|]. intros y Hy.
    destruct (rcpVS_bc_row ly y ltac:(lia)) as (v & Hv & Hin).
    exact (proj1 (PWS.ctl_const_vis_of_AR B TS ly S W m md (RG0f.ANum y) v y HAR Hin eq_refl ltac:(lia) Hv)).
Qed.

End VS.
