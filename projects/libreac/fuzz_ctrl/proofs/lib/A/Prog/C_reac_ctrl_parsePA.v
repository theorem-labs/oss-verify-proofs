(* lib/A/Prog/C_reac_ctrl_parsePA.v -- fuzz_ctrl image A (asan, libreac v1.9.0): two memory facts of the cgif-form glue
   pb_reac_ctrl_parse (lib/A/Prog/C_reac_ctrl_parseP.v), after the re-based stretch reac_ctrl_parseF_rpost.RPostFOn.
     rcpPA_rec      the record: 36 bytes that rw_cells puts at o, inside a live frame, read back through the core's view
                    (the frame bytes are visible: A.ProgWorldVisFrame.frame_vis; at a visible byte the view is ctrl's mrd:
                    C_reac_ctrl_parseV.rcpV_aview_mrd).  Port of a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_parsePf.v (at head lib/B/Prog/C_reac_ctrl_parsePf.v:795-806)
                    (written on a working branch 258208c7d59).
     rcpPA_kept_wr  the write premise of C_reac_ctrl_parseK.rcpK_compose for the stretch's EXACT write set
                    reac_ctrl_parseF_rbody.RBodyFOn.Wf2 fra jj 1 ++ [(ob, ob + 36)]: off the window [S - 8800, S), every
                    written byte is below alloc_ceiling, not an image byte, and inside the record [o, o + 36) if it is a
                    byte of a caller's block, frame or frame shadow.  The new class-1 frame, its shadow and its flag byte
                    are apart from all of these (C_reac_ctrl_parseV.rcpV_frame / rcpV_apart_img / rcpV_apart_block /
                    rcpV_apart_frame at S2, where (1, pos) is live); the record bytes are inside o's frame of Sc
                    (rcpV_in_frame).  Port of a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_parsePf.v (at head lib/B/Prog/C_reac_ctrl_parsePf.v:821-859; written on a working branch 258208c7d59).
   Twin rule: every project module is Required without Import and named through a full-path Module alias.
   rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_parseF_rbody C_reac_ctrl_parseV.
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
Module RB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_parseF_rbody.
Module PV := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parseV.
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

Section PA.
Context {fx : RK11.FPState} {rc : RM05.RunCeil} {SK : RI16.sink_head}.
Variable B : RG0f.asyms.
(* AR_laws of the bundle: the core's own proof (lib/Reusable/YG0q.v AR_laws_ok), no premise. *)
Local Notation LAWS := (RG0q.AR_laws_ok rsegs B).

(* The record: the 36 bytes at o, inside the live frame (co, po) of S, read back through the view at the end memory. *)
Lemma rcpPA_rec : forall ly S (W : RA0n.world rsegs) m md m' co po o (bs : list byte) (d : byte),
  RG0n.AR rsegs B ly S W m md -> In (co, po) (RG01.frames S) ->
  RG0f.frame_addr ly co po <= o -> o + 36 <= RG0f.frame_addr ly co po + RG00.fs_frame_bytes co ->
  LS.rw_cells rsegs m' o [LC.CB 36 bs] -> length bs = 36%nat ->
  forall i, (i < 36)%nat -> RG0n.aview rsegs (RA0n.w_H W) m' (o + Z.of_nat i) = Some (bv_unsigned (nth i bs d)).
Proof.
  intros ly S W m md m' co po o bs d HAR Hin Hlo Hhi Hrw Hlen i Hi.
  destruct (PWVF.frame_vis B LAWS ly S W m md co po o 36 HAR Hin Hlo Hhi) as [(_ & _ & VO) _].
  rewrite (PV.rcpV_aview_mrd (RA0n.w_H W) m' (o + Z.of_nat i) (VO (o + Z.of_nat i) ltac:(lia))).
  destruct Hrw as [[_ (_ & _ & Hb)] _].
  cbn [LC.cells_bytes LC.cbytes] in Hb. rewrite app_nil_r in Hb.
  rewrite (Hb i ltac:(rewrite Hlen; exact Hi)).
  rewrite (nth_error_nth' bs d ltac:(rewrite Hlen; exact Hi)). reflexivity.
Qed.

(* A byte of a frame (cid, pos') or of its shadow, in rcpV_apart_frame's form (A.AsanRT.shadow_addr). *)
Lemma rcpPA_fr_or : forall ly cid pos' a,
  RG0n.in_zr a (RCbq.frame_rng ly (cid, pos')) \/
  RG0n.in_zr a (RG0f.shadow_addr (RG0f.frame_addr ly cid pos'), RG00.fs_frame_bytes cid / 8) ->
  RG0f.frame_addr ly cid pos' <= a < RG0f.frame_addr ly cid pos' + RG00.fs_frame_bytes cid \/
  ART.shadow_addr (RG0f.frame_addr ly cid pos') <= a <
    ART.shadow_addr (RG0f.frame_addr ly cid pos') + RG00.fs_frame_bytes cid / 8.
Proof.
  intros ly cid pos' a H.
  unfold RG0n.in_zr, RCbq.frame_rng, RG0f.shadow_addr, RG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K in *.
  cbn [fst snd] in *. lia.
Qed.

(* The write premise of rcpK_compose for the stretch's exact write set.  The premise on o is the first conjunct of the
   spec's `o <> 0 -> afobj ... lyc Sc W memc o 36`. *)
Lemma rcpPA_kept_wr : forall ly S2 (W : RA0n.world rsegs) mem2 md2 Sc pos jj fra ob o S,
  RG0n.AR rsegs B ly S2 W mem2 md2 ->
  RG01.frames S2 = (1, pos) :: RG01.frames Sc -> ~ In (1, pos) (RG01.frames Sc) ->
  RG0d.ablocks B ly S2 = RG0d.ablocks B ly Sc ->
  fra = RG0f.frame_addr ly 1 pos -> fra = SMC.fs_frame (RG0f.ly_F ly) 1 jj ->
  SMC.fs_flag (RG0f.ly_F ly) 1 jj = RG0f.flag_addr ly 1 pos ->
  ((o = 0 /\ ob = fra + 32) \/ (o <> 0 /\ ob = o)) ->
  (o <> 0 -> exists co po, In (co, po) (RG01.frames Sc) /\ RG0f.frame_addr ly co po <= o /\
     o + 36 <= RG0f.frame_addr ly co po + RG00.fs_frame_bytes co) ->
  RM05.alloc_ceiling <= S - 8800 ->
  forall a, 0 <= a < 2 ^ 64 -> ~ LF.outside (RB.RBodyFOn.Wf2 S (RG0f.ly_F ly) fra jj 1 ++ [(ob, ob + 36)]) a ->
  ~ (S - 8800 <= a < S) ->
  a < RM05.alloc_ceiling /\ ~ RG0d.in_img rsegs a /\
  (forall b m i, In (b, m) (RG0d.ablocks B ly Sc) -> 0 <= i < RG00.req_size m -> a = b + i -> o <= a < o + 36) /\
  (forall cid pos', In (cid, pos') (RG01.frames Sc) ->
     (RG0n.in_zr a (RCbq.frame_rng ly (cid, pos')) \/
      RG0n.in_zr a (RG0f.shadow_addr (RG0f.frame_addr ly cid pos'), RG00.fs_frame_bytes cid / 8)) -> o <= a < o + 36).
Proof.
  intros ly S2 W mem2 md2 Sc pos jj fra ob o S HAR2 HFR Hnin HAB Efa Efs Efl Hob Hof Hceil a Ha Hwr Hw.
  assert (In1 : In (1, pos) (RG01.frames S2)) by (rewrite HFR; left; reflexivity).
  assert (InSc : forall c q, In (c, q) (RG01.frames Sc) -> In (c, q) (RG01.frames S2))
    by (intros c q Hcq; rewrite HFR; right; exact Hcq).
  assert (Ne1 : forall c q, In (c, q) (RG01.frames Sc) -> (c, q) <> (1, pos))
    by (intros c q Hcq E; rewrite E in Hcq; exact (Hnin Hcq)).
  pose proof (PV.rcpV_frame B ly S2 W mem2 md2 pos HAR2 In1) as Hfr. cbv zeta in Hfr.
  destruct Hfr as (_ & Fr2 & _ & FL2 & _ & _ & _ & _ & Sh2).
  (* the new frame, its flag byte and its shadow: below alloc_ceiling, apart from the image, the blocks and the
     other frames (so the last two conjuncts hold vacuously) *)
  assert (NEW : forall x,
            (RG0f.frame_addr ly 1 pos <= x < RG0f.frame_addr ly 1 pos + 128) \/ x = RG0f.flag_addr ly 1 pos \/
            (ART.shadow_addr (RG0f.frame_addr ly 1 pos) <= x < ART.shadow_addr (RG0f.frame_addr ly 1 pos) + 16) ->
            x < RM05.alloc_ceiling /\ ~ RG0d.in_img rsegs x /\
            (forall b m i, In (b, m) (RG0d.ablocks B ly Sc) -> 0 <= i < RG00.req_size m -> x = b + i ->
               o <= x < o + 36) /\
            (forall cid pos', In (cid, pos') (RG01.frames Sc) ->
               (RG0n.in_zr x (RCbq.frame_rng ly (cid, pos')) \/
                RG0n.in_zr x (RG0f.shadow_addr (RG0f.frame_addr ly cid pos'), RG00.fs_frame_bytes cid / 8)) ->
               o <= x < o + 36)).
  { intros x Hx.
    split; [lia|]. split.
    { intros Hi. pose proof (PV.rcpV_apart_img B ly S2 W mem2 md2 pos x HAR2 In1 Hi) as N.
      cbv zeta in N. destruct N as (N1 & N2 & N3). destruct Hx as [X|[X|X]]; contradiction. }
    split.
    { intros b m i Hb Hi Ex. exfalso.
      assert (Hb2 : In (b, m) (RG0d.ablocks B ly S2)) by (rewrite HAB; exact Hb).
      pose proof (PV.rcpV_apart_block B ly S2 W mem2 md2 pos b m x HAR2 In1 Hb2 ltac:(lia)) as N.
      cbv zeta in N. destruct N as (N1 & N2 & N3). destruct Hx as [X|[X|X]]; contradiction. }
    { intros cid pos' Hin Hr. exfalso.
      pose proof (PV.rcpV_apart_frame B ly S2 W mem2 md2 pos cid pos' x HAR2 In1 (InSc _ _ Hin) (Ne1 _ _ Hin)
                    (rcpPA_fr_or ly cid pos' x Hr)) as N.
      cbv zeta in N. destruct N as (N1 & N2 & N3). destruct Hx as [X|[X|X]]; contradiction. } }
  (* the written byte: the flag byte, the frame, its shadow or the record box [ob, ob + 36) (the hint interval of Wf2
     is empty) *)
  unfold RB.RBodyFOn.Wf2 in Hwr. cbn [app LF.outside] in Hwr.
  assert (Hc : (SMC.fs_flag (RG0f.ly_F ly) 1 jj <= a < SMC.fs_flag (RG0f.ly_F ly) 1 jj + 1) \/
               (fra <= a < fra + 128) \/ (ART.shadow_addr fra <= a < ART.shadow_addr fra + 16) \/
               (ob <= a < ob + 36)) by lia.
  rewrite Efl in Hc. subst fra.
  destruct Hc as [Hc|[Hc|[Hc|Hc]]].
  - apply NEW. right; left; lia.
  - apply NEW. left; exact Hc.
  - apply NEW. right; right; exact Hc.
  - destruct Hob as [(Eo & Eob)|(Eo & Eob)].
    + (* o = 0: the box is the frame's [fra + 32, fra + 68) *)
      apply NEW. left. lia.
    + (* o <> 0: the box is the record, inside o's frame of Sc *)
      subst ob. destruct (Hof Eo) as (co & po & Hin & Hlo & Hhi).
      destruct (PV.rcpV_in_frame B ly S2 W mem2 md2 co po o 36 HAR2 (InSc _ _ Hin) ltac:(lia) Hlo Hhi)
        as (Oc & OI & _).
      split; [lia|]. split.
      { intros Hi. pose proof (PV.rcpV_img_lt a Hi). lia. }
      split; [intros; exact Hc | intros; exact Hc].
Qed.
End PA.
