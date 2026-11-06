(* lib/A/ACtlG/KitMem.v -- the SHARED memory helpers of the glue lemmas of fuzz_ctrl image A's walk of
   LLVMFuzzerTestOneInput (lib/A/ACtl.v's stage hypotheses, one glue file per stage in lib/A/ACtlG/).  Written by
   a Theorem Labs lane, its SINGLE WRITER (a Theorem Labs lane, 03:5xZ: one shared file for the nine glue lanes, not a
   piece file).  Every glue file Requires it QUALIFIED (`From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require
   A.ACtlG.KitMem.`) and cites `A.ACtlG.KitMem.kitmem_*`; a lemma it lacks is asked of a Theorem Labs lane, never copied.
   rule 24: no function proved.

   WHAT IS HERE (requests of Theorem Labs lanes: K1-K6, V1-V6 / W1-W5, K2 / K4, (1)-(3), and two others,
   and the writer lane's own)
     lift      kitmem_lift            an _F run (lib/Lib ExecF.evtF over Img0.rsegs) as a prefix of a world walk,
                                      the continuation receiving the run's fsteps (for ProgWorld.ajournal_of_fsteps /
                                      ProgWorld.pws_fsteps_mem) and same_but_materialized
     shell     kitmem_frame_addr_le   frame_addr is the same along layout_le
               kitmem_own6            the owned class-6 frame at an own6 cut: In frames, frame_addr at ly3, the
                                      bounds 4096 <= fr, fr mod 32 = 0, fr + 4096 <= alloc_ceiling <= c_sp - STK
               kitmem_arodataS_journal  the entry's arodata_okS at a cut (FP = [])
               kitmem_input_apart     the input block apart from the owned frame, below alloc_ceiling (a Theorem Labs lane K3)
     presence  kitmem_wview_some, kitmem_mrd_some, kitmem_stk_of_present, kitmem_stk_of_journal,
               kitmem_grows_munch_stk, kitmem_mrd_grow, kitmem_bytes_grow
     writes    kitmem_outside_dec, kitmem_not_outside, kitmem_awr_win, kitmem_awr_frame (ajournal_of_fsteps'
               awr_byte premise)
     munch     kitmem_mrd_munch, kitmem_bytes_munch, kitmem_q64_munch, kitmem_addr_munch, kitmem_spill_q64,
               kitmem_spill_munch,
               kitmem_saved_len, kitmem_frac_munch, kitmem_frac_keep (both by SHAPE: they move FRAC's announced
               trailer conjunct q64 (fr + 4088) too), kitmem_asan_cells_img, kitmem_ro_agree_img,
               kitmem_ctlrt_munch, kitmem_ctlrt_keep
     mrd       kitmem_bytes_at_mrd, kitmem_addressable_mrd, kitmem_rw_cells_mrd (pointwise transports)
     image     kitmem_find_segment_img, kitmem_not_img_hi, kitmem_rom_none_img, kitmem_rom_none_hi, kitmem_ro_img,
               kitmem_in_img
     rng       kitmem_rng_win, kitmem_rng_frame, kitmem_rng_frame_sh, kitmem_rng_heap, kitmem_rng_heap_sh1,
               kitmem_rng_heap_sh_span (RNG_W footprint ranges from visibility, for an _F's rng premises)
   Cited, not restated: a Theorem Labs lane's ProgBridge (fevt_of_evtF, rng_of_visible, range_visible_sub), YA0nR
   (SRr_fsteps), ProgWorldVis{Win,Frame,Heap} (win_vis, frame_vis, heap_vis, heap_sh_vis); the core's YCbq
   (frames_bounds, ajournal, awr_byte, fs_frame_bytes_nonneg), YG0d (AR_laws fields); lib/Lib's Mem / Frame / Step /
   Cells (stk_bytes).  The journal across a lifted run is a Theorem Labs lane's ProgWorld.ajournal_of_fsteps, and the run's
   mem_grows is ProgWorld.pws_fsteps_mem (cite them there; KitMem does not load ProgWorld).  lib/Lib's modules are
   loaded by ABSOLUTE path: lib/A/Bz/Lib and lib/AZ/Lib (not in this delivery) carry modules of the same short names.

   CLOSURE: every Require below is qualified (no Import / Export of a project module); no statement names a
   frame-route identifier.  The six modules that exist both as the core's lib/Reusable/<X> and as ctrl's
   lib/A/Reusable/<X> and that this file names (YK11 YM05 YI16 YK1b) are written FULLY qualified everywhere
   (a Theorem Labs lane 03:4xZ: a partial `Reusable.YK11` resolves to ctrl's copy once A.Contract is loaded).

   BUILD STATE: type-check on 5da74c9c931 (glue base 29ddfc3ea99 merged), closure reaches no stand-in:
   cb build on a build machine, no substitution (log name in the commit).  No Axiom, no
   Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The four twin modules this file names, by ABSOLUTE path: a `From ...lib Require Reusable.YK11` would match ctrl's
   ...lib.A.Reusable.YK11 by suffix (a Theorem Labs lane / porter 04:33Z). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R Reusable.YA0n Reusable.YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YCbq Reusable.YE01 Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.Img0 A.AsanRT A.AsanRTFacts A.ACfn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisWin A.ProgWorldVisFrame A.ProgWorldVisHeap.
(* lib/Lib by ABSOLUTE path too: lib/A/Bz/Lib and lib/AZ/Lib carry modules of the same short names. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list (= A.Img0.rsegs by reflexivity, A.ProgBridge.tfibsegs_rsegs). *)
Local Notation segs := A.AB1v.tfibsegs.
Local Notation rsegs := A.Img0.rsegs.

(* ---------------------------------------------------------------------------------------------------------
   0. The image.  rsegs tiles [IMG_LO, IMG_HI) = [0x10000, 0x5fe000) (ProgBridge.rsegs_spans). *)

(* A found segment contains the address (find_segment's own recursion, as YCbq.find_segment_none reads it). *)
Lemma kitmem_find_segment_img : forall (sg : list Segment) x s,
  find_segment sg x 1 = Some s -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.in_img sg x.
Proof.
  induction sg as [|s0 r IH]; intros x s H; cbn in H; [discriminate H|].
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + 1) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool
    eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    exists s0. split; [left; reflexivity | lia].
  - destruct (IH x s H) as (s1 & Hin & Hr). exists s1. split; [right; exact Hin | exact Hr].
Qed.

(* No image byte at or above IMG_HI. *)
Lemma kitmem_not_img_hi : forall a, A.Prog.ImgBounds.IMG_HI <= a ->
  ~ Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha (sg & Hin & Hr).
  pose proof (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs sg Hin) as H.
  change A.AB1v.tfibsegs with A.Img0.rsegs in H. rewrite A.ProgBridge.rsegs_spans in H.
  unfold A.Prog.ImgBounds.IMG_HI in Ha.
  repeat (destruct H as [H | H]; [injection H as E1 E2; rewrite <- E1, <- E2 in Hr; lia |]).
  destruct H.
Qed.

(* The rom has no byte off the image. *)
Lemma kitmem_rom_none_img : forall a, 0 <= a < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs a ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa a) = None.
Proof.
  intros a Ha Hn. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom, memory_read. try change (Z.of_N 1) with 1.
  destruct (find_segment rsegs (bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. apply Hn. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa_unsigned a Ha) in E. exact (kitmem_find_segment_img rsegs a s E).
Qed.

Lemma kitmem_rom_none_hi : forall a, A.Prog.ImgBounds.IMG_HI <= a < 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa a) = None.
Proof.
  intros a Ha. apply kitmem_rom_none_img; [unfold A.Prog.ImgBounds.IMG_HI in Ha; lia|].
  apply kitmem_not_img_hi. lia.
Qed.

(* A read-only byte is an image byte. *)
Lemma kitmem_ro_img : forall a : word, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr rsegs a = true -> Reusable.YG0d.in_img segs (bv_unsigned a).
Proof.
  intros a H. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  exact (kitmem_find_segment_img rsegs (bv_unsigned a) s E).
Qed.

(* Every byte of [IMG_LO, IMG_HI) is an image byte. *)
Lemma kitmem_in_img : forall a, A.Prog.ImgBounds.IMG_LO <= a < A.Prog.ImgBounds.IMG_HI ->
  Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha. unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI in Ha.
  pose proof A.ProgBridge.rsegs_spans as SP.
  assert (G : forall b z, In (b, z) [(0x10000, 0x20000); (0x30000, 0x6e000); (0x9e000, 0x3000); (0xa1000, 0x55d000)] ->
                b <= a < b + z -> Reusable.YG0d.in_img segs a).
  { intros b z Hbz Hr. rewrite <- SP in Hbz. apply in_map_iff in Hbz as (s & Es & Hs).
    injection Es as Eb Ez. exists s. split; [exact Hs | lia]. }
  destruct (Z_lt_le_dec a 0x30000); [apply (G 0x10000 0x20000); [left; reflexivity | lia]|].
  destruct (Z_lt_le_dec a 0x9e000); [apply (G 0x30000 0x6e000); [right; left; reflexivity | lia]|].
  destruct (Z_lt_le_dec a 0xa1000); [apply (G 0x9e000 0x3000); [right; right; left; reflexivity | lia]|].
  apply (G 0xa1000 0x55d000); [right; right; right; left; reflexivity | lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   1. The lift.  The run is stated over Img0.rsegs, the walk over the core's tfibsegs (the same list); the
   continuation gets the fsteps run itself, which ProgWorld.ajournal_of_fsteps and ProgWorld.pws_fsteps_mem take. *)
Lemma kitmem_lift : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState},
  Reusable.YK04.wx_segs_nowrap segs ->
  forall (W : Reusable.YA0n.world segs) (ms : machine_state) (md : Model) (RNG : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.footprint)
         (P : machine_state -> Prop) (Q : Reusable.YA0n.world segs -> config -> Prop),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF rsegs RNG P ms ->
  Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W) RNG ->
  (forall ms' md', Reusable.YK04R.fsteps segs RNG ms ms' -> P ms' ->
     Reusable.YK04.same_but_materialized md md' -> Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (mkCfg ms md) Q.
Proof.
  intros fx Hwx W ms md RNG P Q HE Hfp Hk.
  destruct (A.ProgBridge.fevt_of_evtF RNG P ms HE) as (ms' & Hrun & HP).
  exact (Reusable.YA0nR.SRr_fsteps segs Hwx W ms ms' md RNG Q Hrun Hfp (fun md' Hs => Hk ms' md' Hrun HP Hs)).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The owned class-6 frame at an own6 cut (A5's G2 as one lemma, plus the window bound). *)
Lemma kitmem_frame_addr_le : forall n ly ly' cid pos,
  Reusable.YG0f.layout_le n ly ly' -> Reusable.YG0f.frame_addr ly' cid pos = Reusable.YG0f.frame_addr ly cid pos.
Proof.
  intros n ly ly' cid pos Hle. destruct Hle as (_ & _ & _ & _ & _ & EF & _).
  unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity.
Qed.

Lemma kitmem_own6 : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
    {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}
    (B : Reusable.YG0f.asyms) (cx : A.ACtlCut.ctlcx) (FP : list (Z * Z)) ly3 S3 W3 mem3 md3 (k fr : Z),
  Reusable.YG0d.AR_laws segs B ->
  Reusable.YCbq.ajournal (SK := SK) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) FP
    (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
    (A.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = A.ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (A.ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (A.ACtlCut.c_ly cx) cid pos) ->
  In (6, A.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3) /\
  Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) = fr /\
  4096 <= fr /\ fr mod 32 = 0 /\
  fr + Reusable.YG00.fs_frame_bytes 6 <= OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling /\
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling <= A.ACtlCut.c_sp cx - A.ACfn.LLVMF_STK.
Proof.
  intros fx rc SK B cx FP ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL.
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hlo & _).
  assert (Hin : In (6, A.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (A.ACtlCut.c_ly cx) 6 (A.ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (E3 : Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; exact (kitmem_frame_addr_le _ _ _ 6 (A.ACtlCut.c_fpos cx) Hly)).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hin)
    as (H4096 & Hc & _).
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR Hin) as (H32 & _).
  rewrite E3 in H4096, Hc, H32.
  split; [exact Hin|]. split; [exact E3|]. split; [exact H4096|]. split; [exact H32|].
  split; [exact Hc | lia].
Qed.

(* a Theorem Labs lane K3: the input block [c_p, c_p + c_n) at an own6 cut lies below alloc_ceiling, apart from the owned class-6
   frame, and in one application-memory band; its byte list has length c_n.  From ctl_base (tfib_lib_pre_x,
   ACfn.v:38-39: n = 0 and p = A_EMPTY, or 0 < n < 2^26 and (p, n) a live block), the body's Permutation of the
   live list, AR_blocks_law and YCbq.sep_block_frame.  The frame's placement above the image is a premise (Kit's
   announced kit_frame6_above_img gives it); it decides only the n = 0 case (A_EMPTY = 0x5daee0 < IMG_HI). *)
Lemma kitmem_input_apart : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
    {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}
    {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}
    (B : Reusable.YG0f.asyms) (MT : Reusable.YC5d.ameter_ops) (XM_LIB : Z -> Z) (RLO RHI : Z)
    (cx : A.ACtlCut.ctlcx) (FP : list (Z * Z)) ly3 S3 W3 mem3 md3 (k : Z),
  Reusable.YG0d.AR_laws segs B ->
  A.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := SK) segs B A.ACfn.LLVMF_STK (A.ACtlCut.c_sp cx) FP
    (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx) (A.ACtlCut.c_W cx) (A.ACtlCut.c_mem cx) (A.ACtlCut.c_md cx)
    (A.ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = A.ACtlCut.own6 cx ->
  Permutation (Reusable.YG0d.ablocks B ly3 S3) (Reusable.YG0d.ablocks B (A.ACtlCut.c_ly cx) (A.ACtlCut.c_S cx)) ->
  A.Prog.ImgBounds.IMG_HI <= Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) ->
  Z.of_nat (length (A.ACtlCut.c_in cx)) = A.ACtlCut.c_n cx /\ 0 <= A.ACtlCut.c_p cx /\
  A.ACtlCut.c_p cx + A.ACtlCut.c_n cx <= OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling /\
  (A.ACtlCut.c_p cx + A.ACtlCut.c_n cx <= Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) \/
   Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx) + Reusable.YG00.fs_frame_bytes 6 <= A.ACtlCut.c_p cx) /\
  (A.ACtlCut.c_p cx + A.ACtlCut.c_n cx <= Reusable.YG0f.kLowShadowBeg \/ Reusable.YG0f.kHighMemBeg <= A.ACtlCut.c_p cx).
Proof.
  intros fx rc LS SK B MT XM_LIB RLO RHI cx FP ly3 S3 W3 mem3 md3 k LAWS HB HJ HF HP Himg.
  destruct HB as (Hpre & _). destruct Hpre as (_ & _ & _ & _ & Hcase & Hlen & _).
  pose proof HJ as (HAR & _).
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  assert (Hinf : In (6, A.ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  split; [symmetry; exact Hlen|].
  unfold A.Prog.ImgBounds.IMG_HI in Himg.
  destruct Hcase as [(E0 & Ep) | (Hn & Hin)].
  - rewrite E0, Ep. unfold A.ACfn.A_EMPTY, Reusable.YG0f.kLowShadowBeg. lia.
  - assert (Hin3 : In (A.ACtlCut.c_p cx, A.ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
      by exact (Permutation_in _ (Permutation_sym HP) Hin).
    destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (_ & H4096 & Hceil & Happ & _).
    pose proof (Reusable.YCbq.req_size_pos (A.ACtlCut.c_n cx) ltac:(lia)) as [_ Hrs].
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (A.ACtlCut.c_fpos cx) HAR Hin3 Hinf)
      as Hsep.
    unfold Reusable.YG0f.zdisjoint in Hsep; cbn [fst snd] in Hsep.
    unfold Reusable.YG0f.in_app in Happ.
    split; [lia|]. split; [lia|]. split; [lia | lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   3. Presence: a window of present bytes is a lib/Lib `stk` window; the journal's stack window is present. *)
Lemma kitmem_wview_some : forall (m : word -> option byte) (x : word) b,
  m x = Some b -> wview rsegs m x <> None.
Proof. intros m x b Hb. unfold wview. rewrite Hb. discriminate. Qed.

Lemma kitmem_mrd_some : forall (m : word -> option byte) (x : word) b,
  m x = Some b -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd rsegs m x = Some b.
Proof. intros m x b Hb. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd. rewrite Hb. reflexivity. Qed.

Lemma kitmem_stk_of_present : forall (H : word -> bool) (mem : word -> option byte) (lo hi : Z),
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> Reusable.YG0n.apresent H mem a) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk rsegs mem lo hi.
Proof.
  intros H mem lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|]. intros a Ha.
  destruct (Hp a Ha) as [_ (b & Hb)]. split.
  - exact (kitmem_wview_some mem _ b Hb).
  - exists b. exact (kitmem_mrd_some mem _ b Hb).
Qed.

Lemma kitmem_not_outside : forall (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) x,
  ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x -> exists lo hi, In (lo, hi) WR /\ lo <= x < hi.
Proof.
  induction WR as [|[lo hi] WR IH]; cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]; intros x H; [exfalso; exact (H I)|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - exists lo, hi. split; [left; reflexivity | lia].
  - assert (H' : ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) by (intros Ho; apply H; split; [lia | exact Ho]).
    destruct (IH x H') as (lo' & hi' & Hin & Hr). exists lo', hi'. split; [right; exact Hin | exact Hr].
  - assert (H' : ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) by (intros Ho; apply H; split; [lia | exact Ho]).
    destruct (IH x H') as (lo' & hi' & Hin & Hr). exists lo', hi'. split; [right; exact Hin | exact Hr].
Qed.

(* `outside` is decidable (ProgWorld.pws_outside_dec's statement; restated here so KitMem does not load ProgWorld). *)
Lemma kitmem_outside_dec : forall (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) x, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x \/ ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]; intros x; [left; exact I|].
  destruct (IH x) as [H|H]; destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi);
    first [left; split; [lia | exact H] | right; intros [H1 H2]; first [lia | exact (H H2)]].
Qed.

(* a Theorem Labs lane: ajournal_exec's mem_grows premise for a run whose writes are one high window it leaves present. *)
Lemma kitmem_grows_munch_stk : forall (H : word -> bool) (m m' : word -> option byte) (lo hi : Z),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch [(lo, hi)] m m' -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk A.Img0.rsegs m' lo hi -> A.Prog.ImgBounds.IMG_HI <= lo ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows
    (Reusable.YK04.mrestrict H m) (Reusable.YK04.mrestrict H m').
Proof.
  intros H m m' lo hi MU (_ & _ & ST) Hlo x Hx. unfold Reusable.YK04.mrestrict in *.
  destruct (H x); [exact Hx|].
  destruct (kitmem_outside_dec [(lo, hi)] (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho). exact Hx.
  - (* decided with Z's comparisons, not tauto: tauto would use Classical_Prop.classic here (a Theorem Labs lane, measured) *)
    destruct (kitmem_not_outside [(lo, hi)] (bv_unsigned x) Ho) as (lo' & hi' & Hin & Hr0).
    destruct Hin as [Ei | []]. injection Ei as <- <-.
    assert (Hr : lo <= bv_unsigned x < hi) by exact Hr0.
    destruct (ST (bv_unsigned x) Hr) as [_ (b & Hb)].
    pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
    unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd in Hb. rewrite (kitmem_rom_none_hi (bv_unsigned x) ltac:(lia)) in Hb.
    unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa in Hb. rewrite Z_to_bv_bv_unsigned in Hb.
    destruct (m' x); [discriminate | discriminate Hb].
Qed.

Lemma kitmem_stk_of_journal : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
    {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}
    (B : Reusable.YG0f.asyms) (STK sp0 : Z) (FP : list (Z * Z)) ly S W mem md own lyc Sc Wc
    (memc : word -> option byte) mdc k (lo hi : Z),
  Reusable.YCbq.ajournal (SK := SK) A.AB1v.tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  sp0 - STK <= lo -> hi <= sp0 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk A.Img0.rsegs memc lo hi.
Proof.
  intros fx rc SK B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k lo hi HJ Hlo Hhi.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  apply (kitmem_stk_of_present (Reusable.YA0n.w_H Wc)); [lia | lia |].
  intros a Ha. apply Hpres. lia.
Qed.

(* a Theorem Labs lane: the read-only data fact of the entry's pre (arodata_okS, ACfn.v:43) at a cut, from the journal's
   image clause (YCbq.v:362-363) with FP = [] (fp_spares by fp_spares_closed, as ACtl.v's ajournal_fp_nil). *)
Lemma kitmem_arodataS_journal : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
    {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}
    (B : Reusable.YG0f.asyms) (RLO RHI STK sp0 : Z) ly S (W : Reusable.YA0n.world A.AB1v.tfibsegs) mem md own
    ly' S' (W' : Reusable.YA0n.world A.AB1v.tfibsegs) mem' md' k,
  (forall a, RLO <= a < RHI -> Reusable.YG0d.in_img A.AB1v.tfibsegs a) ->
  Reusable.YCbq.ajournal (SK := SK) A.AB1v.tfibsegs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  Reusable.YE01.arodata_okS A.AB1v.tfibsegs B RLO RHI (Reusable.YG0n.aview A.AB1v.tfibsegs (Reusable.YA0n.w_H W) mem) ->
  Reusable.YE01.arodata_okS A.AB1v.tfibsegs B RLO RHI (Reusable.YG0n.aview A.AB1v.tfibsegs (Reusable.YA0n.w_H W') mem').
Proof.
  intros fx rc SK B RLO RHI STK sp0 ly S W mem md own ly' S' W' mem' md' k Himg HJ HA a Ha Hno Herr.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  assert (Hi : Reusable.YG0d.in_img A.AB1v.tfibsegs a).
  { destruct Ha as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (Himg a Hr)]. }
  assert (Hsp : Reusable.YCbq.fp_spares (SK := SK) [] a).
  { apply (Reusable.YCbq.fp_spares_closed (SK := SK)). intros Ho. exact (Reusable.YCbq.sink_closed_nil Ho). }
  rewrite (F3 a Hi Hno Herr Hsp). exact (HA a Ha Hno Herr).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   4. The write set of a run (`munch WR m m'`): its bytes, and the awr_byte premise of
   ProgWorld.ajournal_of_fsteps / YCbq.ajournal_exec for a byte of the stack window or of an owned frame. *)
Lemma kitmem_awr_win : forall STK sp0 FP bl0 blc lyc own a,
  sp0 - STK <= a < sp0 -> Reusable.YCbq.awr_byte STK sp0 FP bl0 blc lyc own a.
Proof. intros STK sp0 FP bl0 blc lyc own a Ha. left. exact Ha. Qed.

Lemma kitmem_awr_frame : forall STK sp0 FP bl0 blc lyc own (cid pos fr a : Z),
  fr = Reusable.YG0f.frame_addr lyc cid pos -> In (cid, pos) own ->
  (fr <= a < fr + Reusable.YG00.fs_frame_bytes cid \/
   A.AsanRT.shadow_addr fr <= a < A.AsanRT.shadow_addr fr + Reusable.YG00.fs_frame_bytes cid / 8) ->
  Reusable.YCbq.awr_byte STK sp0 FP bl0 blc lyc own a.
Proof.
  intros STK sp0 FP bl0 blc lyc own cid pos fr a Efr Hin Ha. right; right; right.
  exists cid, pos. split; [exact Hin|]. unfold Reusable.YG0n.in_zr; cbn [fst snd]. rewrite <- Efr.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   5. Facts over bytes the run does not write (munch WR m m': m' = m outside WR). *)
Lemma kitmem_mrd_munch : forall (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (m m' : word -> option byte) (x : Z),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' -> 0 <= x < 2 ^ 64 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd rsegs m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd rsegs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x).
Proof.
  intros WR m m' x MU Hx Ho. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd. rewrite (MU (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x)); [reflexivity|].
  rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa_unsigned by exact Hx. exact Ho.
Qed.

Lemma kitmem_bytes_at_mrd : forall (m m' : word -> option byte) (a : Z) (bs : list byte),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd A.Img0.rsegs m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (a + i)) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd A.Img0.rsegs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (a + i))) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite HE by lia. exact (H i Hi).
Qed.

Lemma kitmem_bytes_munch : forall (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (m m' : word -> option byte) (a : Z) (bs : list byte),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs m a bs -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs m' a bs.
Proof.
  intros WR m m' a bs HB MU HO. pose proof HB as (H0 & H1 & _).
  apply (kitmem_bytes_at_mrd m m' a bs HB). intros i Hi.
  apply (kitmem_mrd_munch WR m m' (a + i) MU); [lia | apply HO; lia].
Qed.

Lemma kitmem_q64_munch : forall (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (m m' : word -> option byte) (a v : Z),
  A.ACtlCutP.q64 m a v -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' ->
  (forall x, a <= x < a + 8 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) -> A.ACtlCutP.q64 m' a v.
Proof.
  intros WR m m' a v H MU HO. unfold A.ACtlCutP.q64 in *. apply (kitmem_bytes_munch WR m m' a _ H MU).
  rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8. intros x Hx. apply HO. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
Qed.

Lemma kitmem_addressable_mrd : forall (m m' : word -> option byte) (p n : Z),
  A.AsanRT.addressable m p n ->
  (forall i, 0 <= i < n -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd A.Img0.rsegs m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + i))) =
                           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd A.Img0.rsegs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (A.AsanRT.shadow_addr (p + i)))) ->
  A.AsanRT.addressable m' p n.
Proof.
  intros m m' p n (H1 & H2 & H3 & H) HE. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite HE by exact Hi. exact Hb.
Qed.

Lemma kitmem_addr_munch : forall (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (m m' : word -> option byte) (p n : Z),
  A.AsanRT.addressable m p n -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' ->
  (forall x, A.AsanRT.in_shadow x -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) -> A.AsanRT.addressable m' p n.
Proof.
  intros WR m m' p n HA MU HS. apply (kitmem_addressable_mrd m m' p n HA). intros i Hi.
  pose proof HA as (_ & _ & _ & H). destruct (H i Hi) as (Ha & _).
  pose proof (A.AsanRTFacts.shadow_of_app (p + i) Ha) as Hs.
  destruct (A.AsanRTFacts.in_shadow_range _ Hs) as [R1 R2].
  apply (kitmem_mrd_munch WR m m' _ MU); [lia | exact (HS _ Hs)].
Qed.

Lemma kitmem_rw_cells_mrd : forall (m m' : word -> option byte) (a : Z) (cs : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.cell),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.rw_cells A.Img0.rsegs m a cs ->
  (forall i, 0 <= i < Z.of_nat (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.cells_size cs) ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd A.Img0.rsegs m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (a + i)) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd A.Img0.rsegs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (a + i)) /\
     m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (a + i)) <> None) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.rw_cells A.Img0.rsegs m' a cs.
Proof.
  intros m m' a cs [[Hwf Hb] (W0 & W1 & Hw)] HE. split; [split; [exact Hwf|]|].
  - apply (kitmem_bytes_at_mrd m m' a _ Hb). intros i Hi. apply HE.
    rewrite <- (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.cells_bytes_length cs Hwf). exact Hi.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. destruct (HE i Hi) as [_ Hn].
    destruct (m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (a + i))) as [b|] eqn:E; [|exfalso; exact (Hn eq_refl)].
    exact (kitmem_wview_some m' _ b E).
Qed.

(* A spill read through register 9: the body's `spill regs m off v` names the q64 at A + off when register 9 holds
   A (the spill's own base is A modulo 2^64, and both sums lie in [0, 2^64)).  two Theorem Labs lanes / R7T / R8 each
   proved it locally (r2g_ / r4g_ / r8g_spill_q64). *)
Lemma kitmem_spill_q64 : forall (regs : bvmap 5 word) (m : word -> option byte) (off v A : Z),
  A.ACtlCutP.spill regs m off v -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  A.ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A1 & HA1 & Hq) HA H0 Hoff Hhi.
  assert (EA : A1 = A).
  { unfold A.ACtlCut.rgv in HA1, HA. rewrite HA in HA1.
    pose proof Hq as (Hq0 & Hq1 & _). rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8 in Hq1.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hq1.
    apply (f_equal bv_unsigned) in HA1. rewrite !Z_to_bv_unsigned in HA1. unfold bv_wrap in HA1.
    change (bv_modulus 64) with (2 ^ 64) in HA1. Z.div_mod_to_equations. lia. }
  subst A1. exact Hq.
Qed.

Lemma kitmem_spill_munch : forall (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (regs regs' : bvmap 5 word) (m m' : word -> option byte)
    (off v A : Z),
  A.ACtlCutP.spill regs m off v -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) -> A.ACtlCutP.spill regs' m' off v.
Proof.
  intros WR regs regs' m m' off v A (A1 & HA1 & Hq) HA H0 Hoff Hhi MU E9 HO.
  assert (EA : A1 = A).
  { unfold A.ACtlCut.rgv in HA1, HA. rewrite HA in HA1.
    pose proof Hq as (Hq0 & Hq1 & _). rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8 in Hq1.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hq1.
    apply (f_equal bv_unsigned) in HA1. rewrite !Z_to_bv_unsigned in HA1. unfold bv_wrap in HA1.
    change (bv_modulus 64) with (2 ^ 64) in HA1. Z.div_mod_to_equations. lia. }
  subst A1. exists A. split; [unfold A.ACtlCut.rgv in *; rewrite E9; exact HA|].
  exact (kitmem_q64_munch WR m m' (A + off) v Hq MU HO).
Qed.

(* the saved registers of FRAC are 13 words *)
Lemma kitmem_saved_len : forall cx, Z.of_nat (length (A.ACtlCutP.saved_bytes cx)) = 104.
Proof.
  intros cx. unfold A.ACtlCutP.saved_bytes. rewrite !List.length_app, !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8. reflexivity.
Qed.

(* FRAC's conjuncts at the new memory, BY SHAPE, not by position (so FRAC's announced last conjunct, the trailer
   word q64 m (fr + 4088) .., a Theorem Labs lane 05:3xZ, moves the same way): a register / arithmetic conjunct is unchanged,
   a q64 / bytes_at conjunct moves by kitmem_q64_munch / kitmem_bytes_munch over a range that one of the lemma's
   premises puts outside the write set. *)
Ltac kitmem_out :=
  match goal with
  | Ho : forall x, _ -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside ?WR x |- OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside ?WR _ => apply Ho; lia
  end.

Ltac kitmem_frac_conj MU :=
  first
  [ assumption
  | lazymatch goal with
    | |- A.ACtlCutP.q64 ?m' ?a ?v =>
        match goal with Hq : A.ACtlCutP.q64 ?m a v |- _ =>
          apply (kitmem_q64_munch _ m m' a v Hq MU); intros ? ?; kitmem_out end
    | |- OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at _ ?m' ?a ?bs =>
        match goal with Hb : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at _ ?m a bs |- _ =>
          apply (kitmem_bytes_munch _ m m' a bs Hb MU); intros ? ?; kitmem_out end
    | |- exists sh, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at _ ?m' ?lo sh /\ length sh = ?n =>
        match goal with Hx : exists sh, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at _ ?m lo sh /\ length sh = n |- _ =>
          let sh := fresh "sh" in let Hb := fresh "Hb" in let Hl := fresh "Hl" in
          destruct Hx as (sh & Hb & Hl); exists sh; split; [|exact Hl];
          apply (kitmem_bytes_munch _ m m' lo sh Hb MU); rewrite Hl;
          try rewrite Z2Nat.id by (unfold A.ACtlCutP.FRAME_SHADOW, A.ACtlCutP.FRAME_BYTES; lia);
          intros ? ?; kitmem_out end
    end ].

Lemma kitmem_frac_munch : forall (B : Reusable.YG0f.asyms) cx (fr sel : Z) (regs : bvmap 5 word)
    (m m' : word -> option byte) (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl),
  A.ACtlCutP.FRAC B cx fr sel regs m -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' ->
  (forall x, Reusable.YG0d.spZ regs <= x -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  (forall x, (fr <= x < fr + 24) \/ (fr + 4088 <= x < fr + 4096) -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  (forall x, A.ACtlCutP.Sfr fr <= x < A.ACtlCutP.Sfr fr + A.ACtlCutP.FRAME_SHADOW -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  A.ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros B cx fr sel regs m m' WR HF MU Hsp Hfr Hsh.
  pose proof (kitmem_saved_len cx) as Hlen.
  destruct HF as (A & sp & HF). exists A, sp.
  repeat match type of HF with _ /\ _ => let H1 := fresh "HF" in destruct HF as [H1 HF] end.
  (* split FRAC's own /\ only (syntactically): `split` would also open the q64 / exists conjuncts *)
  repeat (match goal with |- _ /\ _ => split end); kitmem_frac_conj MU.
Qed.

(* A byte off the image that m holds, m' still holds when the run only grows memory: so its readers stay. *)
Lemma kitmem_mrd_grow : forall (m m' : word -> option byte) (x : Z),
  0 <= x < 2 ^ 64 -> ~ Reusable.YG0d.in_img segs x ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows m m' ->
  (exists b, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd rsegs m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) = Some b) ->
  wview rsegs m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) <> None /\ exists b, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd rsegs m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) = Some b.
Proof.
  intros m m' x Hx Hn G (b & Hb). unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd in Hb.
  rewrite (kitmem_rom_none_img x Hx Hn) in Hb.
  destruct (m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x)) as [b0|] eqn:E; [|discriminate Hb].
  assert (Hm' : m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x) <> None) by (apply G; rewrite E; discriminate).
  destruct (m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa x)) as [b'|] eqn:E'; [|exfalso; exact (Hm' eq_refl)].
  split; [exact (kitmem_wview_some m' _ b' E')|]. exists b'. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd. rewrite E'. reflexivity.
Qed.

(* A byte list m holds off the image, m' holds a list of the same length at, when the run only grows memory. *)
Lemma kitmem_bytes_grow : forall (m m' : word -> option byte) (lo : Z) (sh : list byte),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows m m' -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at rsegs m lo sh ->
  (forall x, lo <= x < lo + Z.of_nat (length sh) -> ~ Reusable.YG0d.in_img segs x) ->
  exists bs, length bs = length sh /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at rsegs m' lo bs.
Proof.
  intros m m' lo sh G (Hs0 & Hs1 & Hsr) Hn.
  assert (Hst : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk rsegs m' lo (lo + Z.of_nat (length sh))).
  { split; [exact Hs0|]. split; [exact Hs1|]. intros a Ha.
    replace a with (lo + Z.of_nat (Z.to_nat (a - lo))) by lia.
    apply (kitmem_mrd_grow m m'); [lia | apply Hn; lia | exact G |].
    rewrite (Hsr (Z.to_nat (a - lo))) by lia.
    destruct (nth_error sh (Z.to_nat (a - lo))) as [b|] eqn:E; [exists b; reflexivity|].
    apply nth_error_None in E. lia. }
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk_bytes rsegs m' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
  exists bs. split; [|exact Hb]. rewrite Hl.
  replace (lo + Z.of_nat (length sh) - lo) with (Z.of_nat (length sh)) by lia. apply Nat2Z.id.
Qed.

(* FRAC across a run that may write inside the frame (not its header / trailer words) and its shadow, and inside the
   spill block (not FRAC's three spill cells): the frame-shadow conjunct is an existential list, rebuilt by growth. *)
Lemma kitmem_frac_keep : forall (B : Reusable.YG0f.asyms) cx (fr sel : Z) (regs : bvmap 5 word)
    (m m' : word -> option byte) (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl),
  A.ACtlCutP.FRAC B cx fr sel regs m -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows m m' -> 0 <= fr ->
  (forall A, A.ACtlCut.rgv regs 9 A -> forall x, (A + 16 <= x < A + 32 \/ A + 304 <= x < A + 312) ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  (forall x, (fr <= x < fr + 8 \/ fr + 16 <= x < fr + 24 \/ fr + 4088 <= x < fr + 4096) -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  (forall x, A.ACtlCut.c_sp cx - 104 <= x < A.ACtlCut.c_sp cx -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  A.ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros B cx fr sel regs m m' WR HF MU G Hfr0 HA Hfr Hsv0.
  pose proof (kitmem_saved_len cx) as Hlen.
  destruct HF as (A & sp & HF). exists A, sp.
  repeat match type of HF with _ /\ _ => let H1 := fresh "HF" in destruct HF as [H1 HF] end.
  match goal with HR9 : A.ACtlCut.rgv regs 9 A |- _ => specialize (HA A HR9) end.
  repeat (match goal with |- _ /\ _ => split end);
    first
    [ lazymatch goal with
      | |- exists sh, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at _ ?m' ?lo sh /\ length sh = ?n =>
          match goal with Hx : exists sh, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at _ ?m lo sh /\ length sh = n |- _ =>
            let sh := fresh "sh" in let Hb := fresh "Hb" in let Hl := fresh "Hl" in
            let bs := fresh "bs" in let Hl' := fresh "Hl" in let Hb' := fresh "Hb" in
            destruct Hx as (sh & Hb & Hl);
            let HNI := fresh "HNI" in
            assert (HNI : forall x, lo <= x < lo + Z.of_nat (length sh) -> ~ Reusable.YG0d.in_img segs x)
              by (intros ? ?; apply kitmem_not_img_hi; rewrite Hl in *;
                  unfold A.ACtlCutP.Sfr, A.ACtlCutP.FRAME_SHADOW, A.ACtlCutP.FRAME_BYTES, A.AsanRT.shadow_addr,
                    A.AsanRT.ASAN_K, A.Prog.ImgBounds.IMG_HI in *; Z.div_mod_to_equations; lia);
            destruct (kitmem_bytes_grow m m' lo sh G Hb HNI) as (bs & Hl' & Hb');
            exists bs; split; [exact Hb' | rewrite Hl'; exact Hl]
          end
      end
    | kitmem_frac_conj MU ].
Qed.

(* Two Theorem Labs lanes: the seven frame-loop bundles of a b5 cut (FLSI, LK, b5_C, b5_K, b5_F17, b5_W240, b5_PF) move
   to a register map that keeps registers 2 9 18 20 21 22 23 24 25 (same memory).  Stated over ACtlCutP's own
   predicates: Seg/F10.v's f10_keep is over SlotInv's, which are not convertible with the transcription (f1_IN /
   b5_C / b5_PH drop conjuncts, SlotInv.v:1826 / :2128 / :2058).  Proof as a Theorem Labs lane's f10g_keep (rc=0 in its F10.v). *)
Lemma kitmem_b5_keep : forall cx j phi fr (regs regs' : bvmap 5 word) (m : word -> option byte),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 2 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 2 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 18 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 18 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 20 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 20 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 21 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 21 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 22 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 22 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 23 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 23 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 24 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 24 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 25 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 25 ->
  A.ACtlCutP.FLSI cx j fr regs m -> A.ACtlCutP.LK cx fr j regs m -> A.ACtlCutP.b5_C cx j phi fr regs m ->
  A.ACtlCutP.b5_K cx j phi fr regs m -> A.ACtlCutP.b5_F17 cx j phi fr regs m -> A.ACtlCutP.b5_W240 cx j regs m ->
  A.ACtlCutP.b5_PF cx j phi fr regs m ->
  A.ACtlCutP.FLSI cx j fr regs' m /\ A.ACtlCutP.LK cx fr j regs' m /\ A.ACtlCutP.b5_C cx j phi fr regs' m /\
  A.ACtlCutP.b5_K cx j phi fr regs' m /\ A.ACtlCutP.b5_F17 cx j phi fr regs' m /\ A.ACtlCutP.b5_W240 cx j regs' m /\
  A.ACtlCutP.b5_PF cx j phi fr regs' m.
Proof.
  intros cx j phi fr regs regs' m E2 E9 E18 E20 E21 E22 E23 E24 E25 H1 H2 H3 H4 H5 H6 H7.
  unfold A.ACtlCutP.FLSI, A.ACtlCutP.FLSH, A.ACtlCutP.PRO, A.ACtlCutP.FLC, A.ACtlCutP.LK, A.ACtlCutP.b5_C,
    A.ACtlCutP.b5_K, A.ACtlCutP.b5_PH, A.ACtlCutP.b5_sp, A.ACtlCutP.b5_F17, A.ACtlCutP.b5_W240, A.ACtlCutP.b5_PF,
    A.ACtlCutP.FSj, A.ACtlCutP.FSb, A.ACtlCutP.spill, A.ACtlCut.rgv, Reusable.YG0d.spZ in *.
  rewrite ?E2, ?E9, ?E18, ?E20, ?E21, ?E22, ?E23, ?E24, ?E25.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 H7)))))).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   6. The carried runtime facts (ACtlCut.ctl_rt) across a run's writes.  The 17 asan cells and every read-only
   byte are image bytes; a write set off the image touches none of them. *)
Lemma kitmem_asan_cells_img : forall (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (m m' : word -> option byte),
  A.AsanRT.asan_cells m -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' ->
  (forall x, ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x -> ~ Reusable.YG0d.in_img segs x) ->
  A.AsanRT.asan_cells m'.
Proof.
  intros WR m m' AC MU HW.
  assert (HO : forall x, A.Prog.ImgBounds.IMG_LO <= x < A.Prog.ImgBounds.IMG_HI -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x).
  { intros x Hx. destruct (kitmem_outside_dec WR x) as [Ho|Ho]; [exact Ho|].
    exfalso. exact (HW x Ho (kitmem_in_img x Hx)). }
  unfold A.AsanRT.asan_cells in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply kitmem_bytes_munch; [eassumption | exact MU | ]);
    intros x Hx; apply HO; rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8, ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le4 in Hx; cbn [length] in Hx;
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
    unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, A.AsanRT.CELL_K, A.AsanRT.UAR, A.AsanRT.INITED,
      A.AsanRT.REPLACE, A.AsanRT.CANPOISON, A.AsanRT.HIEND, A.AsanRT.MIDBEG, A.AsanRT.MIDEND, A.AsanRT.REAL_MEMCPY,
      A.AsanRT.REAL_MEMSET, A.AsanRT.GOT_CELL_K, A.AsanRT.GOT_UAR, A.AsanRT.GOT_REPLACE, A.AsanRT.GOT_HIEND,
      A.AsanRT.GOT_MIDBEG, A.AsanRT.GOT_MIDEND, A.AsanRT.GOT_REAL_MEMSET in *; lia.
Qed.

Lemma kitmem_ro_agree_img : forall (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (m m' : word -> option byte),
  A.ACtlK.ro_agree_at m -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' ->
  (forall x, ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x -> ~ Reusable.YG0d.in_img segs x) ->
  A.ACtlK.ro_agree_at m'.
Proof.
  intros WR m m' RO MU HW a Ha. rewrite <- (RO a Ha). unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd. rewrite (MU a); [reflexivity|].
  destruct (kitmem_outside_dec WR (bv_unsigned a)) as [Ho|Ho]; [exact Ho|].
  exfalso. exact (HW _ Ho (kitmem_ro_img a Ha)).
Qed.

(* a Theorem Labs lane K6: the write set is application memory off the image (so no shadow byte and no image byte). *)
Lemma kitmem_ctlrt_munch : forall (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (m m' : word -> option byte),
  A.ACtlCut.ctl_rt m -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' ->
  (forall x, ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x -> A.AsanRT.app_mem x /\ ~ Reusable.YG0d.in_img A.AB1v.tfibsegs x) ->
  A.ACtlCut.ctl_rt m'.
Proof.
  intros WR m m' (AC & SR & RO) MU HW.
  assert (HW' : forall x, ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x -> ~ Reusable.YG0d.in_img segs x) by (intros x Hx; apply HW, Hx).
  split; [exact (kitmem_asan_cells_img WR m m' AC MU HW')|].
  split; [|exact (kitmem_ro_agree_img WR m m' RO MU HW')].
  unfold A.ACtlK.shadow_rw_at in *. intros a Ha. destruct (SR a Ha) as [Hw (b & Hb)].
  destruct (A.AsanRTFacts.in_shadow_range a Ha) as [R1 R2].
  assert (Ho : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR a).
  { destruct (kitmem_outside_dec WR a) as [Ho|Ho]; [exact Ho|].
    exfalso. exact (A.AsanRTFacts.app_not_shadow a (proj1 (HW a Ho)) Ha). }
  assert (E : m' (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa a) = m (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa a)) by (apply MU; rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa_unsigned by lia; exact Ho).
  split.
  - unfold wview in *. rewrite E. exact Hw.
  - exists b. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd in *. rewrite E. exact Hb.
Qed.

(* The same when the run may also write shadow bytes (frame poisoning, set_shadow, a callee's own checks): the
   run only grows memory (ProgWorld.pws_fsteps_mem), so every shadow byte stays present and readable. *)
Lemma kitmem_ctlrt_keep : forall (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl) (m m' : word -> option byte),
  A.ACtlCut.ctl_rt m -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows m m' ->
  (forall x, ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x -> ~ Reusable.YG0d.in_img A.AB1v.tfibsegs x) ->
  A.ACtlCut.ctl_rt m'.
Proof.
  intros WR m m' (AC & SR & RO) MU G HW.
  split; [exact (kitmem_asan_cells_img WR m m' AC MU HW)|].
  split; [|exact (kitmem_ro_agree_img WR m m' RO MU HW)].
  unfold A.ACtlK.shadow_rw_at in *. intros a Ha. destruct (SR a Ha) as [Hw Hb].
  destruct (A.AsanRTFacts.in_shadow_range a Ha) as [R1 R2].
  apply (kitmem_mrd_grow m m'); [lia | | exact G | exact Hb].
  apply kitmem_not_img_hi. unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END,
    A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG, A.Prog.ImgBounds.IMG_HI in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   7. Footprint ranges of RNG_W (w_H W) at a cut: the _F runs' `ExecF.rng RNG lo len` premises. *)
Lemma kitmem_rng_win : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
    {SK : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.sink_head}
    (B : Reusable.YG0f.asyms) (STK sp0 : Z) (FP : list (Z * Z)) ly S W mem md own lyc Sc Wc
    (memc : word -> option byte) mdc k (lo len : Z),
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  sp0 - STK <= lo -> lo + len <= sp0 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H Wc)) lo len.
Proof.
  intros fx rc SK B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k lo len HJ H1 H2.
  (* ProgWorldVisWin.win_vis's argument, for any sink head (its statement at 1d23ced37fd fixes SK to
     tfib_sink_head through ProgWorld.win_vis_stmt; the window clauses of the journal do not read SK) *)
  apply A.ProgBridge.rng_of_visible.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  change (2 ^ 47) with 140737488355328 in H47.
  unfold A.ProgBridge.range_visible. change (2 ^ 64) with 18446744073709551616.
  split; [lia |]. split; [lia |].
  intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
Qed.

Lemma kitmem_rng_frame : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} (B : Reusable.YG0f.asyms),
  Reusable.YG0d.AR_laws segs B ->
  forall ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 cid pos lo len,
  Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3 -> In (cid, pos) (Reusable.YG01.frames S3) ->
  Reusable.YG0f.frame_addr ly3 cid pos <= lo ->
  lo + len <= Reusable.YG0f.frame_addr ly3 cid pos + Reusable.YG00.fs_frame_bytes cid ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len.
Proof.
  intros fx rc B LAWS ly3 S3 W3 mem3 md3 cid pos lo len HAR Hin H1 H2.
  apply A.ProgBridge.rng_of_visible.
  exact (proj1 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 cid pos lo len HAR Hin H1 H2)).
Qed.

Lemma kitmem_rng_frame_sh : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} (B : Reusable.YG0f.asyms),
  Reusable.YG0d.AR_laws segs B ->
  forall ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 cid pos lo len,
  Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3 -> In (cid, pos) (Reusable.YG01.frames S3) ->
  A.AsanRT.shadow_addr (Reusable.YG0f.frame_addr ly3 cid pos) <= lo ->
  lo + len <= A.AsanRT.shadow_addr (Reusable.YG0f.frame_addr ly3 cid pos) + Reusable.YG00.fs_frame_bytes cid / 8 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len.
Proof.
  intros fx rc B LAWS ly3 S3 W3 mem3 md3 cid pos lo len HAR Hin H1 H2.
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 cid pos HAR Hin) as (_ & Happ & _ & Hsh).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 cid pos HAR Hin) as (H4096 & Hc & _).
  destruct (@Reusable.YG0f.ASAN_CEIL_range rc) as [Hce _]. unfold Reusable.YG0f.ASAN_CEIL in Hce.
  pose proof (Reusable.YCbq.fs_frame_bytes_nonneg cid) as Hfb.
  set (F := Reusable.YG0f.frame_addr ly3 cid pos) in *.
  apply A.ProgBridge.rng_of_visible. unfold A.ProgBridge.range_visible.
  unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in H1, H2.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  split; [Z.div_mod_to_equations; lia|]. split; [rewrite P64; Z.div_mod_to_equations; lia|].
  intros a Ha.
  assert (Hi : 0 <= a - Reusable.YG0f.shadow_addr F < Reusable.YG00.fs_frame_bytes cid / 8)
    by (unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF; lia).
  destruct (Hsh _ Hi) as [[Hv _] _].
  replace (Reusable.YG0f.shadow_addr F + (a - Reusable.YG0f.shadow_addr F)) with a in Hv by ring.
  exact Hv.
Qed.

Lemma kitmem_rng_heap : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} (B : Reusable.YG0f.asyms),
  Reusable.YG0d.AR_laws segs B ->
  forall ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 p n lo len,
  Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3 -> In (p, n) (Reusable.YG0d.ablocks B ly3 S3) ->
  p <= lo -> lo + len <= p + Reusable.YG00.req_size n ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len.
Proof.
  intros fx rc B LAWS ly3 S3 W3 mem3 md3 p n lo len HAR Hin H1 H2.
  apply A.ProgBridge.rng_of_visible.
  exact (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 p n lo len HAR Hin H1 H2).
Qed.

Lemma kitmem_rng_heap_sh_span : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} (B : Reusable.YG0f.asyms),
  Reusable.YG0d.AR_laws segs B ->
  forall ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 p n lo len,
  Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3 -> In (p, n) (Reusable.YG0d.ablocks B ly3 S3) ->
  p <= lo -> 0 < len -> lo + len <= p + Reusable.YG00.req_size n ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (A.AsanRT.shadow_addr lo) (A.AsanRT.shadow_addr (lo + len - 1) - A.AsanRT.shadow_addr lo + 1).
Proof.
  intros fx rc B LAWS ly3 S3 W3 mem3 md3 p n lo len HAR Hin H1 Hlen H2.
  destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 p n lo len HAR Hin H1 H2 ltac:(lia))
    as [E0 | HV]; [lia|].
  apply A.ProgBridge.rng_of_visible.
  apply (A.ProgBridge.range_visible_sub _ _ _ _ _ HV);
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
    Z.div_mod_to_equations; lia.
Qed.

Lemma kitmem_rng_heap_sh1 : forall {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
    {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} (B : Reusable.YG0f.asyms),
  Reusable.YG0d.AR_laws segs B ->
  forall ly3 S3 (W3 : Reusable.YA0n.world segs) mem3 md3 p n a,
  Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3 -> In (p, n) (Reusable.YG0d.ablocks B ly3 S3) ->
  p <= a -> a < p + Reusable.YG00.req_size n ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A.AsanRT.shadow_addr a) 1.
Proof.
  intros fx rc B LAWS ly3 S3 W3 mem3 md3 p n a HAR Hin H1 H2.
  pose proof (kitmem_rng_heap_sh_span B LAWS ly3 S3 W3 mem3 md3 p n a 1 HAR Hin H1 ltac:(lia) ltac:(lia)) as H.
  replace (a + 1 - 1) with a in H by ring. replace (A.AsanRT.shadow_addr a - A.AsanRT.shadow_addr a + 1) with 1 in H
    by ring.
  exact H.
Qed.
