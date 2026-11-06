(* lib/A/ACtlG/F15b.v -- GLUE for stage seg_F15b of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:789).  Written by a Theorem Labs lane (piece W4c); single writer.  rule 24: no function
   proved (stage glue of a walk).  Pattern: glue-pattern.md (a working note, not in this delivery).

   WHAT IT PROVES
     glue_seg_F15b : forall POST (j : nat),
       CF POST (ix_cut C_A821d0_at [Z.of_nat j]) -> CF POST (ix_cut C_A822a0_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A82178_at [Z.of_nat j])
   with ACtl.v's own CF notation, i.e. exactly ACtl.v's Section hypothesis seg_F15b.  Segment F15b (Seg/F15.v:13-32)
   starts at 0x82178 `li a0,1 ; bne s9,a0,822a0`, s9 = fg_ret of the turn's fragment class (0 or 1):
   - s9 <> 1: the branch is taken, exit cut C_A822a0_at (Seg/F15F.f15_evt_c4_F, register-only);
   - s9 = 1 (class FgClose): the four checked tests pass and the loop registers are set, exit cut C_A821d0_at
     (Seg/F15F.f15_evt_34_F, eight 8-byte LOADS: six spill cells [A+80 .. A+280) and the two frame words fr + 272 /
     fr + 304; no store).

   THE PROOF (glue-pattern.md section 3; Seg/F15.v:542-786 is the v1.9 source of record over SlotInv)
   G1  the entry cut C_A82178_at (ACtlCutP.v:2314-2325), its f14_tail and FRAC unfolded.
   G2  bounds from VISIBLE state only: 4096 <= fr (frames_bounds + frame law + layout_le's ly_F); the spill base A
       of FRAC with c_sp cx - 4096 < sp <= A, A + 416 <= c_sp cx < APPMEM_END; the journal's astk_ok
       (alloc_ceiling <= ly_stk_lo (c_ly cx), ly_stk_lo + LLVMF_STK <= c_sp cx) and YCbq.asan_consts
       (0x7fff7f800000 <= alloc_ceiling) put A above HIGHMEM_BEG; the record block (phi, flen) is a live block of
       the journal's AR (the body's Permutation), so the AR block law gives phi + req_size flen <= alloc_ceiling.
       The run's rng premises (34 arm): the six spill cells lie in the journal's stack window
       [c_sp cx - LLVMF_STK, c_sp cx) (KitMem.kitmem_rng_win), the two frame words in the owned class-6 frame
       (KitMem.kitmem_rng_frame, frame_addr ly3 6 pos = fr, fs_frame_bytes 6 = 4096).
   G3  the walk moved from regs3 to the run's canonical start map mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  lift: ProgBridge.fevt_of_evtF / tfibsegs_rsegs, YA0nR.SRr_fevt at kit_RNG0 (c4 arm) or at
       ProgBridge.RNG_W (w_H W3) with fp_avoids_RNG_W (34 arm, a read-only run).
   G5  the exit cut at the run's end map R (registers named by the run's post); journal: ajournal_exec with the
       empty write set (no byte written, the model materialized); frames / frame law / k unchanged, and the cut's
       ctl_rt_C B ly3 S3 mem3 (route (C), a working branch shell 1899bed1aee) carried whole by
       `exact Hrt` (same ly3 S3 mem3 at both exits; the stage reads no shadow byte).
       Body: FRAC through Kit.kit_frac_move; the predicates that read registers move through the v1.9 source's own
       register lemmas (Seg/F13 fsj_regs / ifs2_regs, Seg/F15 lk_regs / flv_regs / f16carry_regs / spill_regs /
       spill_at), applied to a SlotInv ghost whose g_in is c_in cx: those predicates are ACtlCutP's
       transcriptions of SlotInv's, equal up to that field (measured by text), so the lemma's conclusion is the
       ACtlCutP predicate by conversion.  FLSI (whose PRO / f1_IN name the input block differently) moves through
       the local w4c_flsi_move.  Model facts (the class, f_pll, the turn-S j identity) are Seg/F13-F15's.

   SECTION HYPOTHESES: LAWS (the core's AR laws, YCbq.v:207, as ACtl.v:183 states it).  No other.  The _F runs are
   Required (Seg/F15F.v, a Theorem Labs lane's re-run), not assumed.

   CLOSURE: every Require is qualified; no statement names a frame-route identifier (SlotInv / Seg names appear
   only inside proofs, qualified).  The blob list is in the commit message.  SHADOWED NAMES: getr / seg_rom /
   cfg_at are YK11 / Reusable.YG0d-qualified; the six modules present both as the core's lib/Reusable/<X> and
   ctrl's lib/A/Reusable/<X> (YI04 YI16 YK11 YK1b YM05 YO09) are written with their full path
   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.<X> and loaded by an absolute Require.

   BUILD STATE: TYPE-CHECK on a working branch shell 1899bed1aee (cb build, BASE row 23b918fe0c2e, a build machine,
   workspace (internal path)); the build of record is cbrec.sh's, named in the lane's
   report. *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ACtlG.KitMem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.SlotInv Prog.RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F13 A.Prog.Seg.F14 A.Prog.Seg.F15.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F15F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   FLSI moves with register 9 (its spills are read through s1).  Seg/F14.flsi_regs is the v1.9 source's lemma
   over SlotInv's FLSI, whose PRO / f1_IN name the input block through the ghost's g_H / g_n where ACtlCutP's name
   c_p / c_n, so it does not apply by conversion; this is the same proof over ACtlCutP's text. *)
Lemma w4c_spill_move : forall (regs regs' : bvmap 5 word) m off v,
  ACtlCutP.spill regs m off v ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 -> ACtlCutP.spill regs' m off v.
Proof.
  intros regs regs' m off v (A & HA & Hq) E9. exists A. split; [|exact Hq].
  unfold ACtlCut.rgv in *. rewrite E9. exact HA.
Qed.

Lemma w4c_flsi_move : forall cx j fr (regs regs' : bvmap 5 word) m,
  ACtlCutP.FLSI cx j fr regs m ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 -> ACtlCutP.FLSI cx j fr regs' m.
Proof.
  intros cx j fr regs regs' m H E9.
  assert (K : forall off v, ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m off v)
    by (intros off v Hs; exact (w4c_spill_move regs regs' m off v Hs E9)).
  unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC in *.
  destruct H as (((P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pa & Pin & Pn & P184 & P256 & P264 &
    P272 & P32) & S128 & Hstk & S144 & Ha17) & S216 & S224 & S248 & HIN &
    (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Crest)).
  split; [split; [|split; [exact (K _ _ S128)|split; [exact Hstk|split; [exact (K _ _ S144)|exact Ha17]]]]|].
  - exact (conj (K _ _ P40) (conj (K _ _ P120) (conj (K _ _ P136) (conj (K _ _ P160) (conj (K _ _ P168)
      (conj (K _ _ P176) (conj (K _ _ P208) (conj (K _ _ P248) (conj Pa (conj Pin (conj Pn (conj (K _ _ P184)
      (conj (K _ _ P256) (conj (K _ _ P264) (conj (K _ _ P272) (K _ _ P32)))))))))))))))).
  - split; [exact (K _ _ S216)|]. split; [exact (K _ _ S224)|]. split; [exact (K _ _ S248)|].
    split; [exact HIN|].
    split; [exact (K _ _ C256)|]. split; [exact (K _ _ C184)|]. split; [exact (K _ _ C192)|].
    split; [exact (K _ _ C80)|]. split; [exact (K _ _ C88)|]. split; [exact (K _ _ C96)|].
    split; [exact (K _ _ C272)|]. split; [exact (K _ _ C264)|].
    destruct Crest as (Hfa & Hid & C72 & C64 & C56 & C48).
    split; [exact Hfa|]. split; [exact Hid|].
    split; [exact (K _ _ C72)|]. split; [exact (K _ _ C64)|]. split; [exact (K _ _ C56)|]. exact (K _ _ C48).
Qed.

Section GlueF15b.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :284-287), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82178_at := (ACtlCutP.C_A82178_at B).
Local Notation C_A821d0_at := (ACtlCutP.C_A821d0_at B).
Local Notation C_A822a0_at := (ACtlCutP.C_A822a0_at B).

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

Lemma glue_seg_F15b : forall POST (j : nat),
  CF POST (ix_cut C_A821d0_at [Z.of_nat j]) -> CF POST (ix_cut C_A822a0_at [Z.of_nat j]) -> CF POST (ix_cut C_A82178_at [Z.of_nat j]).
Proof.
  intros POST j H34 Hc4 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut (ix_cut, ACtlCut.v:232-234; C_A82178_at, ACtlCutP.v:2314-2325). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82178_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK & HFLV & (A & v & w280 & HT) & HIFS2).
  pose proof HT as HT2. unfold ACtlCutP.f14_tail in HT2.
  destruct HT2 as (T9 & T25 & T10 & TAb & Twb & Tws & Tphifr & Tphisep & Tstk & T184 & T192 & T280 & TbL & TaL &
    TbR & TaR & TB1 & TB2 & TB3 & TB4 & TB5 & Tc256 & TFGM & TCAR).
  (* G2: the frame (frames_bounds, the frame law, layout_le's ly_F). *)
  pose proof HJ as (HAR & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (Hf4096 & _ & _).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efa : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr in *; lia).
  assert (Hfr4096 : 4096 <= fr) by (rewrite <- Efa; exact Hf4096).
  (* G2: the journal's stack window and the allocator ceiling *)
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _).
  destruct Hastk as (_ & _ & Hceil & Hstklo & _).
  unfold A.ACfn.LLVMF_STK in Hstklo.
  pose proof Reusable.YCbq.asan_consts as (Hac & _).
  (* G2: FRAC's spill base and sp *)
  pose proof HFRAC as (A2 & sp & HR2 & Hspm & Hspz & HR4 & HR8 & HR9 & HR3 & HR19 & HR26 & Hfrm & HAm & HAS &
    HspA & HfrA & HA416 & HSsp & HSapp & _).
  unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *.
  assert (EA : A2 = A).
  { assert (E : Z_to_bv 64 A2 = Z_to_bv 64 A) by (unfold ACtlCut.rgv in HR9, T9; rewrite <- HR9; exact T9).
    apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit in E by lia. exact E. }
  subst A2.
  (* G2: model facts of the turn's fragment class (Seg/F13-F15, over a SlotInv ghost with g_in = c_in cx) *)
  pose (gx := A.Prog.SlotInv.Ghost (ACtlCut.c_in cx) 0 0 regs3 mem3 md3 [] []).
  assert (Hfnz : ACtlCutP.fragb fr <> 0) by (unfold ACtlCutP.fragb; lia).
  assert (Hphinz : phi <> 0) by (destruct HHB as (HH & _); exact HH).
  assert (Hrr : 0 <= Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi) <= 1).
  { unfold ACtlCutP.frcl. apply A.Prog.Seg.F14.fg_ret_range; unfold ACtlCutP.fragb in *; lia. }
  assert (Htrf : A.Prog.SlotModel.t_rf (ACtlCut.c_in cx) j = Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi))
    by (exact (A.Prog.Seg.F14.trf_of_frcl gx j fr phi Hfnz Hphinz ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (HFGf : ACtlCutP.frrec cx j fr phi = A.Prog.SlotModel.t_FGf (ACtlCut.c_in cx) j)
    by (exact (A.Prog.Seg.F13.frrec_FGf gx j fr phi Hfnz Hphinz ltac:(lia) ltac:(lia) ltac:(lia))).
  rewrite HFGf in TbR.
  (* G3: the cut's configuration in the run's state form, the walk moved to mkR_of regs3 *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82178_at [Z.of_nat j])) with 0x82178.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) regs3 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82178) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.xregs_eqv_sym _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  destruct (Z.eq_dec (Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi)) 1) as [Hc|Hnc].
  - (* ===== s9 = 1: the class is FgClose; exit cut C_A821d0_at (Seg/F15.v:569-693) ===== *)
    assert (HC : ACtlCutP.frcl cx j fr phi = Prog.RcFrag.FgClose) by (apply A.Prog.Seg.F14.ret1_close; exact Hc).
    assert (HL5 : 1 <= A.Prog.SlotModel.f_pll (A.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
                         (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) <= 51)
      by (exact (A.Prog.Seg.F15.pll_range gx j fr phi HC)).
    pose proof HFLV as (F80 & F88 & F96 & F272 & F264 & Fcond).
    destruct (Fcond ltac:(rewrite Htrf; exact Hc)) as (Hpp & Hpn).
    pose proof HIFS2 as HI2. unfold ACtlCutP.IFS2, ACtlCutP.FSj, ACtlCutP.FSb in HI2.
    destruct HI2 as (_ & _ & _ & S112 & _).
    assert (HAb' : 0 <= A /\ A + 416 <= 2 ^ 64) by lia.
    pose proof (A.Prog.Seg.F15.spill_at regs3 mem3 80 _ A F80 T9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as Q80.
    pose proof (A.Prog.Seg.F15.spill_at regs3 mem3 88 _ A F88 T9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as Q88.
    pose proof (A.Prog.Seg.F15.spill_at regs3 mem3 96 _ A F96 T9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as Q96.
    pose proof (A.Prog.Seg.F15.spill_at regs3 mem3 112 _ A S112 T9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as Q112.
    pose proof (A.Prog.Seg.F15.spill_at regs3 mem3 272 _ A F272 T9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as Q272.
    pose proof (A.Prog.Seg.F15.spill_at regs3 mem3 264 _ A F264 T9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as Q264.
    (* the run's footprint: the spills in the journal's stack window, the two words in the owned frame *)
    assert (Vsp : forall off, 0 <= off -> off + 8 <= 416 ->
              OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng
                (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + off) 8).
    { intros off Ho1 Ho2.
      apply (A.ACtlG.KitMem.kitmem_rng_win B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); unfold A.ACfn.LLVMF_STK; lia. }
    assert (Vfr : forall lo len, fr <= lo -> lo + len <= fr + 4096 ->
              OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng
                (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) lo len).
    { intros lo len Hlo Hhi.
      apply (A.ACtlG.KitMem.kitmem_rng_frame B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) lo len HAR Hin).
      - rewrite Efa. exact Hlo.
      - rewrite Efa. change (Reusable.YG00.fs_frame_bytes 6) with 4096. exact Hhi. }
    (* G4: the run (Seg/F15F.v:140-205) at RNG_W (w_H W3), with its end-map facts *)
    assert (HRUN : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF A.Img0.rsegs (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
      (fun ms' => exists R,
         ms' = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS R OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x821d0) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
                 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 2 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 3 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 4 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 4 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 8 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 8 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 9 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 18 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 18 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 19 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 19 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 20 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 20 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 21 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 21 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 22 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 22 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 23 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 23 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 24 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 24 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 26 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 26 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 10 = Z_to_bv 64 (ACtlCutP.fragb fr + 15) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 15 = Z_to_bv 64 (ACtlCutP.fragb fr + 15) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 11 = Z_to_bv 64 0 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 12 = Z_to_bv 64 (ACtlCutP.fragb fr + 19) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 13 = Z_to_bv 64 (A.Prog.SlotModel.f_pll (A.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
                                                     (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j)) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 14 = Z_to_bv 64 (A.Prog.SlotModel.f_pll (A.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
                                                     (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j) + 5) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 5 = Z_to_bv 64 (A.Prog.SlotModel.fs_n (A.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)))
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82178) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr
         None mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs))).
    { eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF_mono.
      { unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of.
        eapply (A.Prog.Seg.F15F.f15_evt_34_F) with (A := A) (F := ACtlCutP.fragb fr) (Q := fr + 272) (N := fr + 304)
          (L := A.Prog.SlotModel.f_pll (A.Prog.SlotModel.t_FG (ACtlCut.c_in cx) j)
                  (A.Prog.SlotModel.t_g (ACtlCut.c_in cx) j))
          (Nf := A.Prog.SlotModel.fs_n (A.Prog.SlotModel.fst_at (ACtlCut.c_in cx) j)).
        - exact T9.
        - unfold ACtlCut.rgv in T25. rewrite Hc in T25. exact T25.
        - unfold ACtlCutP.fragb; lia.
        - lia.
        - lia.
        - exact HL5.
        - exact Q272.
        - exact Q264.
        - exact Q96.
        - exact Q88.
        - exact Q80.
        - exact Q112.
        - exact Hpp.
        - exact Hpn.
        - apply Vsp; lia.
        - apply Vsp; lia.
        - apply Vsp; lia.
        - apply Vsp; lia.
        - apply Vsp; lia.
        - apply Vsp; lia.
        - apply Vfr; lia.
        - apply Vfr; lia. }
      intros ms' E. cbv beta in E. subst ms'. eexists. split; [reflexivity|].
      repeat (split; [reflexivity|]). reflexivity. }
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
             (POST cx) HFS).
    { exact (A.ProgBridge.fp_avoids_RNG_W _). }
    (* G5: the exit cut C_A821d0_at at the run's end map R *)
    intros ms' md' HQ0 Hsbm.
    destruct HQ0 as (R & Ems & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K26 & K10 & K15 &
      K11 & K12 & K13 & K14 & K5).
    subst ms'.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A821d0_at [Z.of_nat j])) R mem3 md') (POST cx)).
    apply (H34 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
    + eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A821d0_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|].
      rewrite Nat2Z.id.
      assert (HR9' : ACtlCut.rgv R 9 A) by (unfold ACtlCut.rgv in *; rewrite K9; exact T9).
      assert (HCAR' : ACtlCutP.F16CARRY cx j fr phi A R mem3)
        by (exact (A.Prog.Seg.F15.f16carry_regs gx j fr phi A regs3 R mem3 TCAR K9 K18 K20 K22 K23 K24)).
      pose proof HCAR' as HCAR2. unfold ACtlCutP.F16CARRY in HCAR2.
      destruct HCAR2 as (Hfok & HFS' & Hidb & Haid & H144 & HF17).
      exists phi.
      split; [exact HP|].
      split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
      split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact (w4c_flsi_move cx j fr regs3 R mem3 HFLSI K9)|].
      split; [exact (A.Prog.Seg.F15.lk_regs gx fr j regs3 R mem3 HLK K21)|].
      split; [exact (A.Prog.Seg.F15.flv_regs gx fr j regs3 R mem3 HFLV K9)|].
      split; [rewrite Htrf; exact Hc|].
      split; [exact K10|]. split; [exact K15|]. split; [exact K11|]. split; [exact K12|].
      split; [exact K13|]. split; [exact K14|].
      split; [exact TbR|]. split; [exact TaR|].
      split; [exact Hfok|]. split; [exact HFS'|].
      split.
      { rewrite HC in TFGM. cbn [A.Prog.reac_ctrl_identity_fragment_c.fg_mem] in TFGM.
        destruct TFGM as (_ & Hpa2 & _ & _). exact Hpa2. }
      split; [exact Hidb|]. split; [exact Haid|].
      exists A. split; [exact HR9'|].
      split; [exact T192|].
      split.
      { destruct Tc256 as ((_ & Hb256) & _).
        cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.cells_bytes OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.cbytes] in Hb256.
        apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at_app in Hb256. destruct Hb256 as (Hb1 & _). exact Hb1. }
      split; [exact H144|]. split; [exact HF17|].
      split; [exact (A.Prog.Seg.F13.ifs2_regs gx fr j regs3 R mem3 HIFS2 K9)|].
      exact K5.
    + exact Hrt.
  - (* ===== s9 <> 1: the branch is taken; exit cut C_A822a0_at (Seg/F15.v:694-785) ===== *)
    (* G4: the run (Seg/F15F.v:99-117) at the empty footprint, with its end-map facts *)
    assert (HRUN : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF A.Img0.rsegs A.ACtlG.Kit.kit_RNG0
      (fun ms' => exists R,
         ms' = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS R OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x822a0) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
                 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 2 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 3 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 3 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 4 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 4 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 8 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 8 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 9 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 9 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 18 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 18 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 19 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 19 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 20 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 20 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 21 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 21 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 22 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 22 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 23 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 23 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 24 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 24 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R 26 = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 26)
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82178) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr
         None mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom A.Img0.rsegs))).
    { eapply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.evtF_mono.
      { unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of.
        eapply (A.Prog.Seg.F15F.f15_evt_c4_F) with (r := Prog.RcFrag.fg_ret (ACtlCutP.frcl cx j fr phi));
          [exact T25 | exact Hrr | exact Hnc]. }
      intros ms' E. cbv beta in E. subst ms'. eexists. split; [reflexivity|].
      repeat (split; [reflexivity|]). reflexivity. }
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx) HFS).
    { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
    (* G5: the exit cut C_A822a0_at at the run's end map R *)
    intros ms' md' HQ0 Hsbm.
    destruct HQ0 as (R & Ems & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K26).
    subst ms'.
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A822a0_at [Z.of_nat j])) R mem3 md') (POST cx)).
    apply (Hc4 cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
    + eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    + exact HF.
    + exact HL.
    + exact Hk.
    + cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A822a0_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|].
      rewrite Nat2Z.id.
      assert (HR9' : ACtlCut.rgv R 9 A) by (unfold ACtlCut.rgv in *; rewrite K9; exact T9).
      assert (HCAR' : ACtlCutP.F16CARRY cx j fr phi A R mem3)
        by (exact (A.Prog.Seg.F15.f16carry_regs gx j fr phi A regs3 R mem3 TCAR K9 K18 K20 K22 K23 K24)).
      pose proof HCAR' as HC2. unfold ACtlCutP.F16CARRY, ACtlCutP.F17CARRY in HC2.
      destruct HC2 as (_ & _ & _ & _ & _ & C23 & C22 & C24 & C18 & C20 & C232 & C192 & C136 & C120 & C176 & C152 &
        Cw & C50 & C88).
      (* the record block (phi, flen) is live: the AR block law bounds it below alloc_ceiling *)
      assert (Hblk : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
      { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
      destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hblk)
        as (_ & Hp4096 & Hpceil & _).
      assert (Hrq : forall n, 0 <= n -> n <= Reusable.YG00.req_size n)
        by (intros n Hn0; unfold Reusable.YG00.req_size; destruct (n =? 0) eqn:En; [apply Z.eqb_eq in En; lia | lia]).
      assert (Hadd50 : 50 <= ACtlCutP.flen cx j -> A.AsanRT.addressable mem3 phi 50).
      { intros Hl. destruct HHB as (_ & Hadd). rewrite <- (Z.add_0_r phi).
        eapply A.AsanRTFacts.addressable_sub; [exact Hadd | lia | lia | unfold A.ACtlK.a_size; lia]. }
      assert (Hsp2 : Reusable.YG0d.spZ R = Reusable.YG0d.spZ regs3)
        by (unfold Reusable.YG0d.spZ; rewrite K2; reflexivity).
      exists phi.
      split; [exact HP|].
      split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
      split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact (w4c_flsi_move cx j fr regs3 R mem3 HFLSI K9)|].
      split; [exact (A.Prog.Seg.F15.lk_regs gx fr j regs3 R mem3 HLK K21)|].
      split; [exact C23|]. split; [exact C22|].
      split; [intros Hl; destruct (C50 Hl) as (Crb & _ & _ & _); split; [exact (Hadd50 Hl) | exact Crb]|].
      split.
      { exists A. split; [exact HR9'|].
        split; [exact C232|]. split; [exact C192|].
        split; [exact C136|]. split; [exact C120|]. split; [exact C176|].
        split; [intros a Ha; unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END; lia|].
        split; [exact Cw|].
        split; [exact C24|].
        split; [|exact C88].
        intros Hl. destruct (C50 Hl) as (_ & _ & _ & CRI). split; [exact CRI|].
        split.
        - rewrite Hsp2. destruct Tphisep as [Hs|Hs];
            [left; unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K, A.Prog.reac_ctrl_identity_fragment_c.REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia
            | right; exact Hs].
        - left. pose proof (Hrq (ACtlCutP.flen cx j) ltac:(lia)). lia. }
      split; [exact C18|].
      split.
      { intros Hl. destruct (C50 Hl) as (_ & Cg & Cp & _).
        split; [exact Cg|]. split; [exact Cp | exact (A.Prog.Seg.F13.t_phi_len gx j)]. }
      split; [exact C152|].
      split; [exists A; split; [exact HR9' | rewrite <- Tws; exact T280]|].
      split; [|exact C20].
      unfold ACtlCutP.IFS2 in HIFS2. destruct HIFS2 as (HId1 & HFG1 & HFS1).
      assert (Hrf1 : A.Prog.SlotModel.t_rf (ACtlCut.c_in cx) j <> 1) by (rewrite Htrf; exact Hnc).
      assert (EID : A.Prog.SlotModel.t_ID (ACtlCut.c_in cx) (S j) = ACtlCutP.ID1 cx j)
        by (exact (A.Prog.Seg.F13.t_ID_S_skip gx j Hrf1)).
      unfold ACtlCutP.IFS3. split; [|split; [exact HFG1 | exact (A.Prog.Seg.F13.fsj_regs gx fr j regs3 R mem3 HFS1 K9)]].
      unfold ACtlCutP.IDj, ACtlCutP.IDb. rewrite EID. exact HId1.
    + exact Hrt.
Qed.

End GlueF15b.
