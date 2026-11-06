(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4b.v, with its module paths and module names changed; 782 of its 845 lines of code are new or changed and 4089 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F12.v; 451 of its 489 lines of code are new or changed and 807 lines of the source are left out. *)
(* lib/A/ACtlG/F18.v -- GLUE for stage seg_F18 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:806).
   Written by a Theorem Labs lane (piece W4d); single writer.  rule 24: no function proved (stage glue
   of a walk).  Pattern: glue-pattern.md (a working note, not in this delivery); worked example ACtlG/A5.v.

   WHAT IT PROVES
     glue_seg_F18 : forall POST (j : nat),
       CF POST (ix_cut C_A82400_at [Z.of_nat j]) -> CF POST (ix_cut C_A8275c_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A823e8_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F18.  Segment F18 (Seg/F18.v:923-930, the v1.9 source of record) is `ld a0,240(s1); beqz a0,8275c` at
   0x823e8, two arms per turn j:
   - t_8819 = false ([A+240] = 0): the beqz is taken, exit C_A8275c_at.  Run Seg/F18F_on.f18_evt0_F_on (a Theorem Labs lane's
     Seg/F18F.v (not in this delivery) f18_evt0_F moved beside it, statement and proof unchanged; one 8-byte load, only a0 changes, memory
     unchanged).
   - t_8819 = true ([A+240] <> 0): `li a2,6; ld a0,72(s1); mv a1,s7; jal wrapper_bcmp` and the return at 0x82400,
     exit C_A82400_at.  Run Seg/F18F_on.f18_evt_ro_F_on (a Theorem Labs lane's route (C) twin of a Theorem Labs lane's
     Seg/F18F.v (not in this delivery) f18_evt_ro_F (whose later versions differ from the twin's base only in module qualification): `shadow_rw m` narrowed to
     `shadow_rw_on (bcmp_wrap_shadow_R L R 6) m`; its call of wrapper_bcmp is discharged inside by the PROVED
     bcmp_wrap_on.bcmp_wrap_holds_F_on; no split, a Theorem Labs lane's split rule 04:01Z), which writes only the
     wrapper's stack window W = [sp - 4560, sp).

   ROUTE (C) (a working branch 1899bed1aee; recipe L3-recipe.md section 2 (a working note, not in this delivery)): the
   entry carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3, destructed as (Hcells & Hcut & Himgs & Hroag).  The 82400 arm's
   shadow premise, the aligned shadow words of [fr + 186, fr + 192) and [phi, phi + 6), comes from Hcut: the owned
   class-6 frame's shadow ((F) disjunct, glue_f18_frame_sh) and the live record block's shadow-word cover ((L),
   glue_f18_block_sh).  rt_of_core is A.ProgWorldRtC.rt_of_core_C (RT_used_C's destruct shifted by one slot).
   Exits keep the state (ly3, S3): the 8275c arm's memory is unchanged (the entry's ctl_rt_C); the 82400 arm's
   ctl_rt_C by kitmem_asan_cells_img / kitmem_ro_agree_img (W is off the image) and A.ShadowRwOnK.fl_shadow_rw_on
   for both regions (W holds no shadow byte).

   THE PROOF (glue-pattern.md section 3 (a working note, not in this delivery))
   G1  the entry cut C_A823e8_at (ACtlCutP.v:2562-2599): ix_cut's index equation, the body destructed per conjunct;
       FRAC's spill base and sp (FRAC's last conjunct is never named: a Theorem Labs lane's announced fr + 4088 conjunct).
   G2  premises from the body and from VISIBLE state only:
       - t_8819 true gives t_big true, so 50 <= flen (rec_inv0, the record bytes) and s6 = phi + 18;
       - the frame: kitmem_own6 (frames_bounds, the frame law, layout_le, the journal's astk_ok:
         fr + 4096 <= alloc_ceiling <= c_sp cx - LLVMF_STK) and YCbq.frames_bounds' in_app (frame bytes are app
         memory); the record block (phi, flen) and the input block (c_p, c_n) are live blocks of the journal's AR
         (the body's Permutation, the core lib pre's In (p, n) (ablocks ..)), so the AR block law puts them below
         alloc_ceiling; FRAC puts the spill base A above sp and sp above c_sp cx - 4096; so the frame, both blocks
         and every shadow byte lie below W, every spill [A + off) lies above W;
       - footprint RNG := ProgBridge.RNG_W (w_H W3): the spill loads and the wrapper window by
         ProgWorldVisWin.win_vis (the journal's stack window), the image by ProgBridge.img_vis_W, the operand
         fr + 186 and its 8-aligned shadow words by ProgWorldVisFrame.frame_vis, the operand phi and its shadow
         words by ProgWorldVisHeap.heap_vis / heap_sh_vis, rng_bytes by ProgBridge.rng_bytes_RNG_W;
       - the wrapper's stk window premise by kitmem_stk_of_journal; asan_cells / the cut_shadow region / ro_agree
         from the cut's ctl_rt_C; the five wrapper cells REAL_BCMP / REAL_MEMCMP / GOT_CF / CF+254 / CF+255 from
         a Theorem Labs lane's PROVED A.ProgWorldRtC.rt_of_core_C (RT_used_C's asan_cf_cells and REAL_USED slots).
   G3  the walk moved from regs3 to the run's canonical start mkR_of regs3 (YA0nR.SRr_xregs_eqv); the run's explicit
       mkR binders are instantiated by unification with reg_get regs3 r (sp with getr regs3 2), so every register
       the run keeps is, at the end map, convertible to the entry's (a Theorem Labs lane's cheaper route).
   G4  lift: ProgBridge.fevt_of_evtF, YA0nR.SRr_fevt (8275c arm, read-only) / YA0nR.SRr_fevt_hid (82400 arm, writes
       W), fp_avoids by ProgBridge.fp_avoids_RNG_W.
   G5  the exit cut at the run's end map.  8275c arm: memory unchanged, every body conjunct by conversion, FLS
       assembled from the entry's conjuncts, journal by ajournal_exec with the empty write set.  82400 arm:
       journal by YCbq.ajournal_exec with Wr := W (hidden bytes from SRr_fevt_hid, mem_grows from the run's stk
       post, every written byte in the journal's stack window: awr_byte's stack case); ctl_rt_C by
       kitmem_asan_cells_img / kitmem_ro_agree_img and A.ShadowRwOnK.fl_shadow_rw_on; the body across `munch W`:
       FRAC by Kit.kit_frac_move + kitmem_frac_munch,
       HB / addressable by kitmem_addr_munch, bytes / q64 / spills by kitmem_bytes_munch / q64_munch / spill_munch,
       FLSI by the local glue_f18_flsi_keep, rec_inv by SlotInv.rec_inv_of_split + Seg/F18.rec_inv_kept and LT by
       Seg/F18.f18_lt_keep (both by conversion at a SlotInv.Ghost whose g_in is c_in cx: those two bundles are
       ACtlCutP's verbatim transcription), the compare operands at fr + 180 / phi + 6 through their first 6 bytes
       (Seg/F18.ba_first6, memcmp_firstn).
   Instructions this glue steps itself: none (both runs are Seg/F18F_on.v's).

   TRANSCRIPTION DIFFERENCE (recorded, not worked around): ACtlCutP.f1_IN (ACtlCutP.v:658-659) drops SlotInv.f1_IN's
   `(0 < g_n g -> In (g_p g, g_n g) (g_H g))` (SlotInv.v:1826), so ACtlCutP.FLSI is weaker than SlotInv.FLSI and
   Seg/F18.flsi_keep does not apply; glue_f18_flsi_keep below is its proof over ACtlCutP's FLSI (the input block's
   bytes kept by its live-block bound instead of SlotInv's ghost heap).

   SECTION HYPOTHESES (exact text below)
   - LAWS : Reusable.YG0d.AR_laws segs B -- the core's AR law record (YCbq.v:207), as the route (C) walk's ACtl.v:244 states it.
   - TFIB_SYMS : A.AF0m.CtrlTSyms B -- the route (C) walk's ACtl.v:259 hypothesis, the bundle law rt_of_core_C takes.
   Both are the route (C) walk's ACtl.v Section hypotheses with the same name and text; VIS0 / OWNED_RO: none.
   CITED from a Theorem Labs lane's shared KitMem (lib/A/ACtlG/KitMem.v, a working branch 4a56e997c0f, blob
   19bfb2e48a9, merged c8728e5ba73): kitmem_not_img_hi, kitmem_own6, kitmem_grows_munch_stk, kitmem_stk_of_journal,
   kitmem_bytes_munch, kitmem_q64_munch, kitmem_addr_munch, kitmem_spill_munch, kitmem_frac_munch,
   kitmem_asan_cells_img, kitmem_ro_agree_img.
   CITED, NOT HYPOTHESES: A.ProgWorldRtC.rt_of_core_C (lib/A/ProgWorldRtC.v:76, PROVED, a Theorem Labs lane): the five
   wrapper_bcmp runtime cells are not in the cut's ctl_rt_C; this is their one source.  Its am_const rows used here
   (GOT_CF, CF+240..255, REAL_BCMP, REAL_MEMCMP) are the same on the record AF0m (e56483f863b AF0m.v:61-62, :98-99,
   :173).  ShadowRwOn.shadow_rw_on_mono, ShadowRwOnK.fl_shadow_rw_on.
   No _F run is assumed: Seg/F18F_on.v (f18_evt0_F_on, moved from a Theorem Labs lane's Seg/F18F.v (not in this delivery) f18_evt0_F; and
   f18_evt_ro_F_on) is Required.  Seg/F18F.v (not in this delivery) is NOT Required (a Theorem Labs lane 2026-10-29 ~17:00Z): it Requires the frozen
   bcmp_wrap_F.v (not in this delivery), which brings the root lib.MemNormP / lib.MemNorm.  Route (C) leaves, by path from a Theorem Labs lane
   f4423e55886 (the root-free bcmp proof): bcmp_wrap_c.v
   64293314ee8, bcmp_wrap_c_on.v ca2f37ea2b6, bcmp_wrap_on.v 49fcbf2eeed, bcmp_wrap_Fk.v 1fa5b214cf3, A/MemNormP.v
   e45ea6f496f.
   FRAC RE-ESTABLISHED at a new memory: the 82400 exit's FRAC, by Kit.kit_frac_move (registers) and kitmem_frac_munch
   (memory, across W); the announced trailer q64 at fr + 4088 is kept across W the same way (Htrail).

   CLOSURE: every Require is qualified (absolute for the six Reusable twins and for lib/Lib); no statement names a
   frame-route identifier (SlotInv / Seg / F18F_on names appear only inside the proof, qualified, closed by Qed).
   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are written fully qualified.

   BUILD STATE: type-checked with cb build on a build machine (workspace (internal path)) on a working branch 1899bed1aee;
   the build of record is the lane's cbrec run (report).
   No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq Reusable.YK04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP A.AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnK A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisWin A.ProgWorldVisFrame A.ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.rng_asan A.Prog.bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.bcmp_wrap_c_on A.Prog.sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.memcmp_c.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F18 A.Prog.Seg.F18F_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Local lemmas (stage-specific, proved). *)

(* One window [lo, hi): a byte below or above it is outside. *)
Lemma glue_f18_out1 : forall lo hi x, (x < lo \/ hi <= x) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(lo, hi)] x.
Proof.
  intros lo hi x H. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]. split; [lia | exact I].
Qed.

(* The wrapper's shadow-word footprint premise (Seg/F18F.v:103 / :105, n = 6) from the visible 8-aligned shadow
   word cover that ProgWorldVisFrame.frame_vis / ProgWorldVisHeap.heap_sh_vis give (rng_asan.sh_al8_lo / hi). *)
Lemma glue_f18_sh8 : forall (H : word -> bool) (L : Z),
  6 = 0 \/ A.ProgBridge.range_visible H (A.Prog.rng_asan.sh_al8_lo L)
             (A.Prog.rng_asan.sh_al8_hi L 6 - A.Prog.rng_asan.sh_al8_lo L) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng (A.ProgBridge.RNG_W H)
    (8 * (A.AsanRT.shadow_addr L / 8))
    (8 * (A.AsanRT.shadow_addr (L + 6 - 1) / 8) + 8 - 8 * (A.AsanRT.shadow_addr L / 8)).
Proof.
  intros H L [E | HV]; [discriminate E|].
  apply A.ProgBridge.rng_of_visible.
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in HV.
  replace (8 * (A.AsanRT.shadow_addr L / 8)) with (A.AsanRT.shadow_addr L / 8 * 8) by ring.
  replace (8 * (A.AsanRT.shadow_addr (L + 6 - 1) / 8)) with (A.AsanRT.shadow_addr (L + 6 - 1) / 8 * 8) by ring.
  exact HV.
Qed.

(* Route (C) region lemmas: an aligned shadow-word range (A.Prog.sh_word_on) is a cut_shadow byte when its bytes lie
   in the owned class-6 frame ((F) disjunct) or in a live block ((L) disjunct), A.ACtlRtC.v:25-36. *)
Lemma glue_f18_frame_sh : forall (B : Reusable.YG0f.asyms) ly (S : Reusable.YG00.astate) pos fr p n a,
  In (6, pos) (Reusable.YG01.frames S) -> Reusable.YG0f.frame_addr ly 6 pos = fr -> fr mod 32 = 0 ->
  fr + 64 <= p -> p + n + 64 <= fr + 4096 ->
  A.Prog.sh_word_on.sh_word_on p n a -> A.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros B ly S pos fr p n a Hin Efa H32 Hlo Hhi (Hn & Ha).
  left. exists 6, pos. split; [exact Hin|]. rewrite Efa.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096.
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

Lemma glue_f18_block_sh : forall (B : Reusable.YG0f.asyms) ly (S : Reusable.YG00.astate) ph ln p n a,
  In (ph, ln) (Reusable.YG0d.ablocks B ly S) -> ph <= p -> p + n <= ph + Reusable.YG00.req_size ln ->
  A.Prog.sh_word_on.sh_word_on p n a -> A.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros B ly S ph ln p n a Hin Hlo Hhi (Hn & Ha).
  right. left. exists ph, ln. split; [exact Hin|].
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

Section GlueF18.

(* ACtl.v's Section shape, restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
  {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
  {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A823e8_at := (ACtlCutP.C_A823e8_at B).
Local Notation C_A82400_at := (ACtlCutP.C_A82400_at B).
Local Notation C_A8275c_at := (ACtlCutP.C_A8275c_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* FLSI across a write set WR that keeps register 9 and misses the spill cells [A + 32, A + 280), the frame body
   [fr, fr + FRAME_BYTES), every shadow byte and the input block's bytes.  Seg/F18.flsi_keep's proof (F18.v:483-541)
   over ACtlCutP's FLSI, whose f1_IN differs from SlotInv's (header). *)
Lemma glue_f18_flsi_keep : forall (cx : ACtlCut.ctlcx) (j : nat) (fr A : Z) (regs regs' : bvmap 5 word)
    (m m' : word -> option byte) (WR : list OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.ivl),
  ACtlCutP.FLSI cx j fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 288 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch WR m m' ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.wmono A.Img0.rsegs m m' ->
  (forall x, A.AsanRT.in_shadow x -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  (forall x, A + 32 <= x < A + 280 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  (forall x, fr <= x < fr + ACtlCutP.FRAME_BYTES -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside WR x) ->
  ACtlCutP.FLSI cx j fr regs' m'.
Proof.
  intros cx j fr A regs regs' m m' WR H HA HA0 HA1 E9 MU WM HSh HSp HFr HIn.
  assert (K : forall off v, ACtlCutP.spill regs m off v -> 32 <= off <= 272 -> ACtlCutP.spill regs' m' off v).
  { intros off v Hs Hoff.
    apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs regs' m m' off v A Hs HA HA0 ltac:(lia) ltac:(lia) MU E9).
    intros x Hx. apply HSp. lia. }
  assert (KA : forall p n, A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n)
    by (intros p n Ha; exact (A.ACtlG.KitMem.kitmem_addr_munch WR m m' p n Ha MU HSh)).
  unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC, ACtlCutP.f1_IN in *.
  destruct H as (((P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pa & Pin & Pn & P184 & P256 & P264 &
    P272 & P32) & S128 & Hstk & S144 & Ha17) & S216 & S224 & S248 & (HINa & HINb) &
    (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cfa & Cid & C72 & C64 & C56 & C48)).
  assert (Pin' : ACtlCutP.MEM.bytes_at segs m' (ACtlCut.c_p cx) (ACtlCut.c_in cx))
    by exact (A.ACtlG.KitMem.kitmem_bytes_munch WR m m' _ _ Pin MU HIn).
  assert (Hstk' : ACtlCutP.FRM.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES)).
  { apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk_transport segs WR m m' fr
             (fr + ACtlCutP.FRAME_BYTES) Hstk MU WM).
    intros x Hx. left. exact (HFr x Hx). }
  split; [split; [|split; [exact (K _ _ S128 ltac:(lia))|split; [exact Hstk'|
          split; [exact (K _ _ S144 ltac:(lia)) | exact (KA _ _ Ha17)]]]]|].
  { exact (conj (K _ _ P40 ltac:(lia)) (conj (K _ _ P120 ltac:(lia)) (conj (K _ _ P136 ltac:(lia))
      (conj (K _ _ P160 ltac:(lia)) (conj (K _ _ P168 ltac:(lia)) (conj (K _ _ P176 ltac:(lia))
      (conj (K _ _ P208 ltac:(lia)) (conj (K _ _ P248 ltac:(lia)) (conj (KA _ _ Pa) (conj Pin'
      (conj (fun Hn => KA _ _ (Pn Hn)) (conj (K _ _ P184 ltac:(lia)) (conj (K _ _ P256 ltac:(lia))
      (conj (K _ _ P264 ltac:(lia)) (conj (K _ _ P272 ltac:(lia)) (K _ _ P32 ltac:(lia))))))))))))))))). }
  split; [exact (K _ _ S216 ltac:(lia))|]. split; [exact (K _ _ S224 ltac:(lia))|].
  split; [exact (K _ _ S248 ltac:(lia))|].
  split; [exact (conj (KA _ _ HINa) Pin')|].
  exact (conj (K _ _ C256 ltac:(lia)) (conj (K _ _ C184 ltac:(lia)) (conj (K _ _ C192 ltac:(lia))
    (conj (K _ _ C80 ltac:(lia)) (conj (K _ _ C88 ltac:(lia)) (conj (K _ _ C96 ltac:(lia))
    (conj (K _ _ C272 ltac:(lia)) (conj (K _ _ C264 ltac:(lia)) (conj (KA _ _ Cfa) (conj (KA _ _ Cid)
    (conj (K _ _ C72 ltac:(lia)) (conj (K _ _ C64 ltac:(lia)) (conj (K _ _ C56 ltac:(lia))
    (K _ _ C48 ltac:(lia))))))))))))))).
Qed.


(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_F18 : forall POST (j : nat),
  CF POST (ix_cut C_A82400_at [Z.of_nat j]) -> CF POST (ix_cut C_A8275c_at [Z.of_nat j]) -> CF POST (ix_cut C_A823e8_at [Z.of_nat j]).
Proof.
  intros POST j H400 H75c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ix_cut, ACtlCut.v:232-234; C_A823e8_at, ACtlCutP.v:2453-2490). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A823e8_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK &
    (A & w240 & R9 & HA64 & HspA & R23 & R24 & R22 & Hri0 & Q136 & Q120 & Q176 & Q240 & Hw240 & Hw0 & Hw1) &
    R18 & R25 & Hrec & S152 & S280 & HLT).
  (* FRAC's spill base is the body's A, its sp the machine sp (ACtlCutP.v:980-994) *)
  pose proof HFRAC as (Af & spf & FR2 & Fsp16 & FspZ & FR4 & FR8 & FR9 & FR3 & FR19 & FR26 & Ffr32 & FA32 & FAc &
    FspA & FfrA & FA416 & Fsplo & Fapp & _).
  assert (EspZ : bv_unsigned (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2) = spf)
    by exact FspZ.
  assert (Esp0 : 0 <= spf < 2 ^ 64) by (rewrite <- EspZ; apply (bv_unsigned_in_range 64)).
  unfold A.AsanRT.APPMEM_END in Fapp.
  assert (EAf : Af = A).
  { assert (E : Z_to_bv 64 Af = Z_to_bv 64 A) by (unfold ACtlCut.rgv in *; rewrite <- FR9; exact R9).
    apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
    change (bv_modulus 64) with (2 ^ 64) in E. rewrite !Z.mod_small in E by lia. exact E. }
  subst Af.
  (* G3: the cut's configuration in the run's state form, then the walk moved to mkR_of regs3. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A823e8_at [Z.of_nat j])) with 0x823e8.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3)
           regs3 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x823e8)
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.xregs_eqv_sym _ _
                (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of.
  destruct (A.Prog.SlotModel.t_8819 (ACtlCut.c_in cx) j) eqn:E8819.
  2:{
    (* ---- the [A+240] = 0 arm: f18_evt0_F_on, then the exit C_A8275c_at (ACtlCutP.v:2708-2718) ---- *)
    assert (Hw0' : w240 = 0) by (apply Hw0; reflexivity). subst w240.
    eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
              (POST cx)).
    { apply A.ProgBridge.fevt_of_evtF.
      eapply A.Prog.Seg.F18F_on.f18_evt0_F_on with (A := A).
      - exact R9.
      - exact Q240.
      - apply A.ProgBridge.rng_of_visible.
        apply (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ k _ _ HJ); unfold A.ACfn.LLVMF_STK; lia. }
    { apply A.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' Hms' Hsbm. cbv beta in Hms'. subst ms'.
    match goal with |- context [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R _ _ _ _ _ _] =>
      set (R1 := R) end.
    (* ProgBridge.cfg_at_MS read backwards (eq_refl), at the exit cut's pc and the run's end map R1 *)
    change (Reusable.YA0n.SRr segs W3
              (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A8275c_at [Z.of_nat j])) R1 mem3 md') (POST cx)).
    apply (H75c cx [Z.of_nat j] fr k ly3 S3 W3 R1 mem3 md' HB).
    - (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643) *)
      eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity
        | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
        | intros x _; reflexivity | exact Hsbm | intros a Ha; destruct Ha].
    - exact HF.
    - exact HL.
    - exact Hk.
    - (* the exit body: the run keeps every register but a0 and the memory, so each conjunct converts *)
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A8275c_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      exists phi.
      split; [exact HP|]. split; [exact HFRAC|]. split; [exact Hn|]. split; [exact Hj|].
      split; [exact HHB|]. split; [exact HFLSI|].
      split; [exact HLK|].
      split; [|exact HLT].
      unfold ACtlCutP.FLS.
      split; [exact HFLSI|]. split; [exact R18|]. split; [exact R22|]. split; [exact R23|].
      split; [exact R24|]. split; [exact R25|].
      split; [|split; [exact S152 | exact S280]].
      intros HfL. destruct (Hri0 HfL) as (Hp0 & Hp50 & _). destruct (Hrec HfL) as (Hg & Hph & Hlen).
      exact (conj Hp0 (conj Hp50 (conj Hg (conj Hph Hlen)))).
    - exact Hrt. }
  (* ---- the [A+240] <> 0 arm: f18_evt_ro_F (the wrapper_bcmp call inside), then the exit C_A82400_at ---- *)
  destruct (Hw1 eq_refl) as (Hw240nz & HRP & ls & rs & ls2 & rs2 & Q72 & HBL & HLls & HBR & HLrs & Hmm & HADL &
    HADR & Hdj50 & Q64 & HBL2 & HLls2 & HBR2 & HLrs2 & Hmm2 & HADL2 & HADR2).
  assert (Htbig : A.Prog.SlotModel.t_big (ACtlCut.c_in cx) j = true).
  { unfold A.Prog.SlotModel.t_8819 in E8819. apply andb_prop in E8819 as [E1 _].
    apply andb_prop in E1 as [Eb _]. exact Eb. }
  assert (HfL : 50 <= ACtlCutP.flen cx j).
  { unfold A.Prog.SlotModel.t_big in Htbig. apply Z.leb_le in Htbig. exact Htbig. }
  rewrite Htbig in R22.
  destruct (Hri0 HfL) as (Hp0 & Hp50 & _ & _ & Hpap & _).
  destruct (Hrec HfL) as (Hgb & Hphb & Hphl).
  (* G2: the frame (KitMem.kitmem_own6) and its app-memory placement (frames_bounds' in_app) *)
  pose proof HJ as (HAR & _).
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efa & Hfr4096 & Hfr32 & Hfrc & Hc).
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfrc.
  unfold A.ACfn.LLVMF_STK in Hc.
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfapp).
  rewrite Efa in Hfapp. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfapp.
  (* the record block (phi, flen) is a live block of the journal's AR: below alloc_ceiling *)
  assert (Hinphi : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  assert (Ereq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j).
  { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hinphi)
    as (_ & _ & Hphic & _).
  rewrite Ereq in Hphic.
  (* the input block [c_p, c_p + length c_in) lies below alloc_ceiling (the core's lib pre, ACfn.v:38-39) *)
  assert (HinB : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                   x < OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling).
  { pose proof HB as ((_ & _ & _ & _ & Hpn & Hlen & _) & _).
    intros x Hx. rewrite <- Hlen in Hx. destruct Hpn as [(Hn0 & _) | (Hnp & Hinp)]; [lia|].
    assert (Hinp' : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hinp. }
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hinp') as (_ & _ & Hpc & _).
    unfold Reusable.YG00.req_size in Hpc. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  (* route (C): the entry's ctl_rt_C B ly3 S3 mem3 (ACtlRtC.v:44-46) *)
  pose proof Hrt as (Hcells & Hcut & Himgs & Hroag).
  (* the five wrapper_bcmp runtime cells, from rt_of_core_C at the cut (RT_used_C, ProgWorldRtC.v:29-35) *)
  pose proof (A.ProgWorldRtC.rt_of_core_C B MT XM_LIB RLO RHI [] TFIB_SYMS LAWS cx (ACtlCut.own6 cx) k ly3 S3 W3
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.mkst regs3 (Z_to_bv 64 0x823e8) mem3
       (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs)) md3 HB HJ Hrt) as HRT.
  unfold A.ProgWorldRtC.RT_used_C in HRT.
  destruct HRT as (_ & _ & _ & _ & Hcf & _ & _ & Hreal).
  unfold A.AsanRT.asan_cf_cells in Hcf. destruct Hcf as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  rewrite Forall_forall in Hreal.
  assert (HC254 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs mem3
                    (A.Prog.bcmp_wrap_c.CF + 254) [Z_to_bv 8 1]).
  { pose proof (A.Prog.Seg.F18.ba_sub _ _ _ 14 1 HCF240 ltac:(cbn; lia)) as Hs.
    replace (A.AsanRT.RT_CF + 240 + Z.of_nat 14) with (A.Prog.bcmp_wrap_c.CF + 254) in Hs
      by (unfold A.Prog.bcmp_wrap_c.CF, A.AsanRT.RT_CF; lia).
    replace (firstn 1 (skipn 14 (A.AsanRT.cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (HC255 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs mem3
                    (A.Prog.bcmp_wrap_c.CF + 255) [Z_to_bv 8 1]).
  { pose proof (A.Prog.Seg.F18.ba_sub _ _ _ 15 1 HCF240 ltac:(cbn; lia)) as Hs.
    replace (A.AsanRT.RT_CF + 240 + Z.of_nat 15) with (A.Prog.bcmp_wrap_c.CF + 255) in Hs
      by (unfold A.Prog.bcmp_wrap_c.CF, A.AsanRT.RT_CF; lia).
    replace (firstn 1 (skipn 15 (A.AsanRT.cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  assert (HRB : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs mem3
                  A.Prog.bcmp_wrap_c.REAL_BCMP
                  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8
                     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa A.Prog.bcmp_wrap_c.BCMP))).
  { exact (Hreal (0xa17f0, 0x97b0c)
      ltac:(unfold A.AsanRT.RT_REALS; cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(unfold A.ProgWorld.REAL_USED; cbn [In fst]; repeat (first [left; reflexivity | right]))). }
  assert (HRM : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at A.Img0.rsegs mem3
                  A.Prog.bcmp_wrap_c.REAL_MEMCMP
                  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8
                     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa A.Prog.memcmp_c.MEMCMP))).
  { exact (Hreal (0xa17e8, 0x97bdc)
      ltac:(unfold A.AsanRT.RT_REALS; cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(unfold A.ProgWorld.REAL_USED; cbn [In fst]; repeat (first [left; reflexivity | right]))). }
  (* the run's shadow premise (F18F_on: bcmp_wrap_shadow_R L R 6 at L = fr + 186, R = phi), from the cut's region:
     [fr + 186, fr + 192) is in the owned class-6 frame ((F)), [phi, phi + 6) in the live record block ((L)) *)
  assert (HSW : A.ShadowRwOn.shadow_rw_on (A.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R (fr + 186) phi 6) mem3).
  { apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3) _ mem3); [|exact Hcut].
    intros a [Ha | Ha].
    - exact (glue_f18_frame_sh B ly3 S3 (ACtlCut.c_fpos cx) fr (fr + 186) 6 a Hin6 Efa Ffr32
               ltac:(lia) ltac:(lia) Ha).
    - exact (glue_f18_block_sh B ly3 S3 phi (ACtlCutP.flen cx j) phi 6 a Hinphi (Z.le_refl _)
               ltac:(rewrite Ereq; lia) Ha). }
  (* G4: the run f18_evt_ro_F_on (Seg/F18F_on.v) at RNG_W (w_H W3), lifted with SRr_fevt_hid (it writes W) *)
  eapply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
            (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF.
    eapply A.Prog.Seg.F18F_on.f18_evt_ro_F_on with (A := A) (L := fr + 186) (R := phi) (ls := ls) (rs := rs)
      (w240 := w240) (vcmp := 0) (lo := spf - 4560)
      (sp := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2).
    - exact R9.
    - exact R23.
    - lia.
    - lia.
    - exact Q240.
    - exact Hw240nz.
    - exact Hw240.
    - exact Q72.
    - exact HBL.
    - exact HLls.
    - exact HBR.
    - exact HLrs.
    - exact Hmm.
    - exact Hroag.
    - exact HADL.
    - exact HADR.
    - unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia.
    - unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia.
    - apply Hpap. lia.
    - apply Hpap. lia.
    - rewrite EspZ. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. left. lia.
    - rewrite EspZ. rewrite FspZ in Hdj50. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K in *. lia.
    - rewrite EspZ. eapply (A.ACtlG.KitMem.kitmem_stk_of_journal B);
        [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia].
    - rewrite EspZ. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. lia.
    - unfold A.AsanRT.HIGHMEM_BEG. lia.
    - rewrite EspZ. unfold A.AsanRT.APPMEM_END. lia.
    - exact Hcells.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGOTCF.
    - exact HC254.
    - exact HC255.
    - apply A.ProgBridge.rng_of_visible.
      apply (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ k _ _ HJ); unfold A.ACfn.LLVMF_STK; lia.
    - apply A.ProgBridge.rng_of_visible.
      apply (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ k _ _ HJ); unfold A.ACfn.LLVMF_STK; lia.
    - apply A.ProgBridge.rng_bytes_RNG_W.
    - pose proof (A.ProgBridge.img_vis_W W3) as Himg.
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI in Himg.
      exact (A.ProgBridge.rng_of_visible _ _ _ Himg).
    - rewrite EspZ. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K.
      apply A.ProgBridge.rng_of_visible.
      apply (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ k _ _ HJ); unfold A.ACfn.LLVMF_STK; lia.
    - apply A.ProgBridge.rng_of_visible.
      exact (proj1 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 186) 6
                      HAR Hin6 ltac:(rewrite Efa; lia)
                      ltac:(rewrite Efa; change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia))).
    - apply glue_f18_sh8.
      destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 186) 6
                  HAR Hin6 ltac:(rewrite Efa; lia)
                  ltac:(rewrite Efa; change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia)) as [_ Hsh].
      apply Hsh; [lia | rewrite Efa; Z.div_mod_to_equations; lia
                 | rewrite Efa; change (Reusable.YG00.fs_frame_bytes 6) with 4096; Z.div_mod_to_equations; lia].
    - apply A.ProgBridge.rng_of_visible.
      exact (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) phi 6 HAR Hinphi
               (Z.le_refl _) ltac:(rewrite Ereq; lia)).
    - apply glue_f18_sh8.
      exact (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) phi 6 HAR Hinphi
               (Z.le_refl _) ltac:(rewrite Ereq; lia) ltac:(lia)). }
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  (* G5: the continuation at the run's end state *)
  intros ms' md' HQ Hhid Hsbm. cbv beta in HQ.
  destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m' &
    Ems & MU & WM & RO' & ROS & ST').
  subst ms'.
  rewrite EspZ in MU, ST'. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K in MU.
  match goal with |- context [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.MS ?R _ _ _ _ _ _] =>
    set (R1 := R) end.
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82400_at [Z.of_nat j])) R1 m' md') (POST cx)).
  assert (E9 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr R1 9 =
               OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 9) by exact (eq_sym R9).
  assert (EspR : Reusable.YG0d.spZ R1 = spf) by exact EspZ.
  (* every byte the run writes is in W = [spf - 4560, spf) *)
  assert (HOW : forall x, (x < spf - 4560 \/ spf <= x) ->
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(spf - 4560, spf)] x)
    by (intros x Hx; exact (glue_f18_out1 _ _ x Hx)).
  assert (HinW : forall x, ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(spf - 4560, spf)] x ->
                   spf - 4560 <= x < spf).
  { intros x Hx. destruct (Z_lt_le_dec x (spf - 4560)) as [Hl|Hl]; [exfalso; exact (Hx (HOW x (or_introl Hl)))|].
    destruct (Z_lt_le_dec x spf) as [Hh|Hh]; [lia | exfalso; exact (Hx (HOW x (or_intror Hh)))]. }
  assert (HSh : forall x, A.AsanRT.in_shadow x ->
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(spf - 4560, spf)] x).
  { intros x Hx. apply HOW. left.
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in Hx. lia. }
  assert (KA : forall p n, A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable m' p n)
    by (intros p n Ha; exact (A.ACtlG.KitMem.kitmem_addr_munch _ mem3 m' p n Ha MU HSh)).
  assert (Hc1 : 0x10007fff8000 + 32768 <= ACtlCut.c_sp cx) by lia.
  (* FRAC's announced trailer word q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx)) (a Theorem Labs lane 05:5xZ) lies
     in the class-6 frame, outside W: kept across the run like every other frame q64. *)
  assert (Htrail : forall v, ACtlCutP.q64 mem3 (fr + 4088) v -> ACtlCutP.q64 m' (fr + 4088) v)
    by (intros v Hv; exact (A.ACtlG.KitMem.kitmem_q64_munch _ mem3 m' _ _ Hv MU (fun x Hx => HOW x ltac:(lia)))).
  apply (H400 cx [Z.of_nat j] fr k ly3 S3 W3 R1 m' md' HB).
  - (* journal across W (YCbq.ajournal_exec, Wr := W; every written byte is in the journal's stack window) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a : Z => spf - 4560 <= a < spf).
    + exact HJ.
    + intros x Hx. cbv beta in Hx. unfold Reusable.YK04.mrestrict.
      destruct (Reusable.YA0n.w_H W3 x); [reflexivity|].
      apply MU. apply HOW. lia.
    + apply (A.ACtlG.KitMem.kitmem_grows_munch_stk _ mem3 m' (spf - 4560) spf MU ST').
      unfold A.Prog.ImgBounds.IMG_HI. lia.
    + exact Hhid.
    + exact Hsbm.
    + intros a Ha. cbv beta in Ha. unfold Reusable.YCbq.awr_byte. left. unfold A.ACfn.LLVMF_STK. lia.
  - exact HF.
  - exact HL.
  - exact Hk.
  - (* the exit body, C_A82400_at (ACtlCutP.v:2494-2518) *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A82400_at ACtlCutP.ixn ACtlCutP.ixz nth].
    split; [reflexivity|]. rewrite Nat2Z.id.
    exists phi.
    split; [exact HP|].
    split.
    { (* FRAC: its registers move along the run's end map, its memory part lies outside W *)
      apply (A.ACtlG.KitMem.kitmem_frac_munch B cx fr fr R1 mem3 m' _
               (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R1 mem3 HFRAC eq_refl eq_refl eq_refl eq_refl E9
                  eq_refl eq_refl) MU).
      - intros x Hx. apply HOW. right. lia.
      - intros x Hx. apply HOW. left. lia.
      - intros x Hx. apply HOW. left.
        unfold ACtlCutP.Sfr, ACtlCutP.FRAME_SHADOW, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Hx.
        Z.div_mod_to_equations. lia. }
    split; [exact Hn|]. split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz | exact (KA _ _ Hphiad)]. }
    split.
    { apply (glue_f18_flsi_keep cx j fr A regs3 R1 mem3 m' _ HFLSI R9 ltac:(lia) ltac:(lia) E9 MU WM HSh).
      - intros x Hx. apply HOW. right. lia.
      - intros x Hx. apply HOW. left. unfold ACtlCutP.FRAME_BYTES in Hx. lia.
      - intros x Hx. apply HOW. left. pose proof (HinB x Hx). lia. }
    split.
    { destruct HLK as (Hj' & R21 & HOUR). split; [exact Hj'|]. split; [exact R21|].
      unfold ACtlCutP.OURb in *.
      apply (A.ACtlG.KitMem.kitmem_bytes_munch _ mem3 m' _ _ HOUR MU).
      rewrite A.Prog.SlotModel.OUR_length. intros x Hx. apply HOW. left. lia. }
    split.
    { destruct (A.Prog.Seg.F18.ba_first6 mem3 (fr + 180) ls2 HBL2 HLls2) as (HBL2f & HL2f).
      destruct (A.Prog.Seg.F18.ba_first6 mem3 (phi + 6) rs2 HBR2 HLrs2) as (HBR2f & HR2f).
      pose (gx := A.Prog.SlotInv.Ghost (ACtlCut.c_in cx) 0 0 regs3 mem3 md3 [] []).
      exists A, (firstn 6 ls2), (firstn 6 rs2).
      split; [reflexivity|].
      split; [exact HA64|].
      split; [rewrite EspR; lia|].
      split; [reflexivity|].
      split; [exact R24|].
      split; [reflexivity|].
      split; [exact R22|].
      split.
      { exact (A.Prog.Seg.F18.rec_inv_kept gx j fr phi A mem3 m' [(spf - 4560, spf)]
                 (A.Prog.SlotInv.rec_inv_of_split gx j fr phi A mem3 (Hri0 HfL) HRP) MU
                 (fun x Hx => HOW x ltac:(lia)) (fun x Hx => HOW x ltac:(lia))
                 (fun x Hx => HOW x ltac:(unfold A.AsanRT.HIGHMEM_BEG in Hx; lia))
                 (fun x Hx => HOW x ltac:(lia))). }
      split; [exact (A.ACtlG.KitMem.kitmem_q64_munch _ mem3 m' _ _ Q136 MU (fun x Hx => HOW x ltac:(lia)))|].
      split; [exact (A.ACtlG.KitMem.kitmem_q64_munch _ mem3 m' _ _ Q120 MU (fun x Hx => HOW x ltac:(lia)))|].
      split; [exact (A.ACtlG.KitMem.kitmem_q64_munch _ mem3 m' _ _ Q176 MU (fun x Hx => HOW x ltac:(lia)))|].
      split; [exact (A.ACtlG.KitMem.kitmem_q64_munch _ mem3 m' _ _ Q64 MU (fun x Hx => HOW x ltac:(lia)))|].
      split.
      { apply (A.ACtlG.KitMem.kitmem_bytes_munch _ mem3 m' _ _ HBL2f MU).
        rewrite HL2f. intros x Hx. apply HOW. left. lia. }
      split; [rewrite HL2f; lia|].
      split.
      { apply (A.ACtlG.KitMem.kitmem_bytes_munch _ mem3 m' _ _ HBR2f MU).
        rewrite HR2f. intros x Hx. apply HOW. left. lia. }
      split; [rewrite HR2f; lia|].
      split; [rewrite A.Prog.Seg.F18.memcmp_firstn; exact Hmm2|].
      split; [exact (KA _ _ HADL2)|].
      split; [exact (KA _ _ HADR2)|].
      rewrite EspR. rewrite FspZ in Hdj50. exact Hdj50. }
    split; [exact R18|].
    split.
    { exact (A.ACtlG.KitMem.kitmem_spill_munch _ regs3 R1 mem3 m' 152 _ A S152 R9 ltac:(lia) ltac:(lia) ltac:(lia)
               MU E9 (fun x Hx => HOW x ltac:(lia))). }
    split.
    { apply (A.ACtlG.KitMem.kitmem_bytes_munch _ mem3 m' _ _ Hgb MU).
      rewrite A.Prog.Seg.F18.f18_t_g_length. intros x Hx. apply HOW. left. lia. }
    split.
    { apply (A.ACtlG.KitMem.kitmem_bytes_munch _ mem3 m' _ _ Hphb MU).
      intros x Hx. apply HOW. left. lia. }
    split; [exact Hphl|].
    (* LT = IFS (S j) (ACtlCutP.v:724-725, SlotInv.v:1976 verbatim): Seg/F18.f18_lt_keep at the ghost *)
    pose (gx := A.Prog.SlotInv.Ghost (ACtlCut.c_in cx) 0 0 regs3 mem3 md3 [] []).
    refine (A.Prog.Seg.F18.f18_lt_keep gx fr j regs3 R1 mem3 m' [(spf - 4560, spf)] HLT E9 MU _ _ _).
    + cbn [A.AsanRTFacts.all_app]. split; [|exact I].
      unfold A.AsanRTFacts.app_ivl. intros a Ha.
      unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia.
    + intros x Hx. apply HOW. left. lia.
    + intros A' HA' x Hx. apply HOW.
      assert (E : Z_to_bv 64 A' = Z_to_bv 64 A)
        by (unfold A.Prog.SlotInv.rg in HA'; rewrite <- HA'; exact R9).
      apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
      change (bv_modulus 64) with (2 ^ 64) in E. rewrite (Z.mod_small A) in E by lia.
      Z.div_mod_to_equations. lia.
  - (* ctl_rt_C at the same (ly3, S3): W is application memory above the image, so the runtime cells and ro_agree
       are kept (kitmem_asan_cells_img / kitmem_ro_agree_img) and no shadow byte is written (both regions kept by
       A.ShadowRwOnK.fl_shadow_rw_on) *)
    assert (HW' : forall x, ~ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(spf - 4560, spf)] x ->
                    ~ Reusable.YG0d.in_img segs x).
    { intros x Hx. pose proof (HinW x Hx) as Hxw.
      apply A.ACtlG.KitMem.kitmem_not_img_hi. unfold A.Prog.ImgBounds.IMG_HI. lia. }
    split; [exact (A.ACtlG.KitMem.kitmem_asan_cells_img _ mem3 m' Hcells MU HW')|].
    split; [exact (A.ShadowRwOnK.fl_shadow_rw_on _ _ mem3 m' Hcut MU WM HSh)|].
    split; [exact (A.ShadowRwOnK.fl_shadow_rw_on _ _ mem3 m' Himgs MU WM HSh)|].
    exact (A.ACtlG.KitMem.kitmem_ro_agree_img _ mem3 m' Hroag MU HW').
Qed.

End GlueF18.
