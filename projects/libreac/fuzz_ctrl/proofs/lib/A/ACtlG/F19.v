(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths, module names and numbers changed; 927 of its 1102 lines of code are new or changed and 2382 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F18.v; 442 of its 492 lines of code are new or changed and 1052 lines of the source are left out. *)
(* lib/A/ACtlG/F19.v -- GLUE for stage seg_F19 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:809),
   following the glue pattern (glue-pattern.md (a working note, not in this delivery)) and the pilot
   lib/A/ACtlG/A5.v.  Written by a Theorem Labs lane; single writer.  proves no function (kind: segment lemma);
   rule 24: no function proved.

   WHAT IT PROVES
     glue_seg_F19 : forall POST (j : nat),
       CF POST (ix_cut C_A82418_at [Z.of_nat j]) -> CF POST (ix_cut C_A82400_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_F19.  Segment F19 is 0x82400 -> 0x82418 (Seg/F19.v:1-5): ld s4,192(s1) (the spill [A+200] = phi + 18);
   bnez a0 (not taken: a0 = 0); addi a1,s7,6; li a2,6; ld a0,48(s1) (the spill [A+64] = fr + 180);
   jal wrapper_bcmp@0x42970, which returns to 0x82418 with a0 = memcmp_model ls2 rs2 6 = 0.  The call writes only
   the wrapper's stack window W = [sp - 4560, sp).

   THE _F RUN (Required, not assumed): lib/A/Prog/Seg/F19F_on.v f19_evt_ro_F_on (a Theorem Labs lane's route (C) twin of
   a Theorem Labs lane's Seg/F19F.v (not in this delivery) f19_evt_ro_F, whose later versions differ from the twin's base only in module qualification: the same statement with `shadow_rw m` narrowed to
   `shadow_rw_on (bcmp_wrap_shadow_R L (R + 6) 6) m`; the wrapper's bcmp_wrap_contract_F_on is discharged INSIDE it
   by bcmp_wrap_on.bcmp_wrap_holds_F_on, so no callee premise and no split remain: a Theorem Labs lane's split rule, 04:01Z).
   The _ro twin is used because the cut carries ro_agree (ctl_rt_C), not mem_inv.

   ROUTE (C) (a working branch 1899bed1aee; recipe L3-recipe.md section 2 (a working note, not in this delivery)): the
   entry carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3, destructed as (Hcells & Hcut & Himg & Hroag).  The run's one
   shadow premise, the aligned shadow words of [fr + 180, fr + 186) and [phi + 6, phi + 12), comes from Hcut:
   the first range is the owned class-6 frame's shadow, cut_shadow's (F) disjunct (glue_f19_frame_sh), the second
   the live record block (phi, flen)'s shadow-word cover, its (L) disjunct (glue_f19_block_sh).  rt_of_core is
   A.ProgWorldRtC.rt_of_core_C (RT_used_C's destruct shifted by one slot).  The exit's ctl_rt_C keeps the state
   (ly3, S3): asan_cells by fl_asan_cells, both regions by A.ShadowRwOnK.fl_shadow_rw_on across the munch, ro_agree
   from the run.

   THE PROOF
   G1  unfold the entry cut: ix_cut's index equation, then C_A82400_at's conjuncts (ACtlCutP.v:2494-2518).
   G2  the run's premises.  Registers from the body (s1 = A, s7 = phi, a0 = 0).  Memory from the body (the two
       spills, the two compare operands with their addressability and memcmp_model = 0), ctl_rt_C (asan_cells,
       the cut_shadow region, ro_agree) and the five wrapper cells REAL_BCMP / REAL_MEMCMP / GOT_CF / CF+254 /
       CF+255 from a Theorem Labs lane's PROVED A.ProgWorldRtC.rt_of_core_C at the cut (ctl_rt_C does not carry them:
       REAL_BCMP 0xa17f0 / REAL_MEMCMP 0xa17e8 are RT_used's REAL_USED slots, GOT_CF and CF + 254 / CF + 255 are
       asan_cf_cells, the last two cut out of RT_CF + 240 by F18.ba_sub).  Bounds from VISIBLE state only: FRAC
       (sp, A, c_sp), the journal's astk_ok
       (alloc_ceiling + LLVMF_STK <= c_sp) and its stack-window presence (the wrapper's stk premise), the owned
       class-6 frame (frames_bounds at ly3 + the frame law + layout_le's ly_F), the record block (phi, flen) as a
       live block of ablocks (the body's Permutation; AR_blocks_law), rec_inv's app_mem of [phi, phi + 50).
       Footprint RNG := ProgBridge.RNG_W (w_H W3): the two spills and the wrapper window by win_vis, the image
       by img_vis_W, fr + 180 and its shadow words by frame_vis, phi + 6 and its shadow words by heap_vis /
       heap_sh_vis, rng_bytes by rng_bytes_RNG_W.
   G3  cfg_at_MS, then the walk moved from regs3 to the run's canonical map mkR_of regs3 (YA0nR.SRr_xregs_eqv);
       the run's 31 register binders are instantiated with reg_get regs3 r, so every register the run keeps is
       convertible at the end map.
   G4  lift: ProgBridge.fevt_of_evtF, then YA0nR.SRr_fsteps (the continuation keeps the fsteps run, which
       a Theorem Labs lane's PROVED ProgWorld.ajournal_of_fsteps takes).
   G5  the exit cut C_A82418_at at the run's end map R and memory m': journal by ProgWorld.ajournal_of_fsteps with
       WR = [(sp - 4560, sp)] (every written byte is in the journal's stack window [c_sp - LLVMF_STK, c_sp));
       frames / frame law / k bound unchanged; the body: register facts by conversion (kept registers) or from the
       run (s4 = phi + 18, s7 = phi, a0 = 0); memory facts across munch W by the local keep lemmas below (every
       body byte is a spill at A + off >= sp, a frame byte below alloc_ceiling < sp - 4560, a record-block byte
       below alloc_ceiling, the input block below alloc_ceiling, or a shadow byte below HIGHMEM_BEG); ctl_rt_C by
       RcAsanFPLib.fl_asan_cells, A.ShadowRwOnK.fl_shadow_rw_on (both regions) and the run's ro_agree.
   This glue steps NO instruction itself: all six instructions and the wrapper call are inside f19_evt_ro_F_on.

   LOCAL LEMMAS (Qed; a Theorem Labs lane's 04:4xZ rule: ACtlCutP's transcriptions are NOT all convertible with SlotInv's,
   so the frame-route keep lemmas are restated over ACtlCutP's predicates and the core getr):
     f19_flsi_keep    ACtlCutP.FLSI (F18.flsi_keep over ACtlCutP: f1_IN there lacks SlotInv's
                      `(0 < g_n g -> In (g_p g, g_n g) (g_H g))`, and PRO reads c_n cx, not nlen (g_in g))
     f19_lt_keep      ACtlCutP.LT (F18.f18_lt_keep over ACtlCutP)
     f19_rec_inv_keep ACtlCutP.rec_inv (F18.rec_inv_kept over ACtlCutP)
     glue_f19_frame_sh / glue_f19_block_sh  an aligned shadow-word range (sh_word_on) inside the owned class-6
                      frame / inside a live block is a cut_shadow byte ((F) / (L) disjunct, A.ACtlRtC.v:25-36)
   They use the frame-route memory lemmas RcAsanFPLib.fl_bytes / fl_addressable / fl_stk and the model length
   facts F18.f18_t_ID_length / f18_t_FG_length / f18_fsbody_length / f18_t_g_length / bsl_len_le and
   SlotModel.OUR_length, F18.ba_sub, all proof-internal (Qed; a Theorem Labs lane 23:54Z).

   SECTION HYPOTHESES (exact text below; source of each)
   - LAWS : the core's AR laws (YCbq.v:207), as A5.v:153 and ACtl.v:183.
   - TFIB_SYMS : A.AF0m.CtrlTSyms B, ACtl.v:252 verbatim (rt_of_core_C's first premise).
   Both are the route (C) walk's ACtl.v Section hypotheses with the same name and text, so ACtl.v discharges seg_F19 by
   `glue_seg_F19 B MT XM_LIB RLO RHI LAWS TFIB_SYMS` (fx / rc implicit; LS is not used).  VIS0 / OWNED_RO: none.
   CITED, PROVED (not hypotheses): f19_evt_ro_F_on (Seg/F19F_on.v); rt_of_core_C (ProgWorldRtC.v:76, a Theorem Labs lane);
   ajournal_of_fsteps (ProgWorld.v:1091, a Theorem Labs lane); win_vis / frame_vis / heap_vis /
   heap_sh_vis (ProgWorldVis*.v, a Theorem Labs lane); SRr_xregs_eqv / SRr_fsteps (YA0nR.v); fevt_of_evtF, cfg_at_MS,
   tfibsegs_rsegs, RNG_W, fp_avoids_RNG_W, rng_of_visible, rng_bytes_RNG_W, img_vis_W (ProgBridge.v);
   frames_bounds, asan_consts (YCbq.v); al_blocks (YG0d.v); Kit.kit_wx, Kit.kit_frac_move;
   ShadowRwOn.shadow_rw_on_mono, ShadowRwOnK.fl_shadow_rw_on.
   NOT USED: CTLRT_ENTRY, CHAIN_OF_CUT (no allocator call), any callee contract hypothesis (closed inside the _F),
   the AF0m zero-shadow row (no shadow byte here comes from ts_zsh: the frame's shadow is AR_frames_law's, the
   record block's AR_shadow_law's, phi + 14 .. phi + 17's the body's rec_inv).

   FROM THE SHARED MEMORY KIT lib/A/ACtlG/KitMem.v (a working branch 4a56e997c0f, merged
   into the w4d worktree at c8728e5ba73; blob 19bfb2e48a9; Required qualified, never copied): kitmem_spill_munch (a
   spill across the munch) and kitmem_frac_munch (FRAC at the run's memory, by shape).

   FRAC: every FRAC destruct ends in `& _`; FRAC is re-established at the run's memory m' by KitMem.kitmem_frac_munch
   (by shape; its frame premise covers [fr, fr + 24) and [fr + 4088, fr + 4096), so a Theorem Labs lane's announced trailing
   conjunct `q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx))` is carried: those bytes lie in the owned frame,
   below the wrapper window) and at the run's end map by Kit.kit_frac_move.

   CLOSURE: every Require below is qualified (no Import / Export of a project module); the six twin modules
   (YK11 YM05 YO09) and lib/Lib's Mem / MState / Frame / ExecF / Regs6ss are Required by absolute path and named
   by full path (module aliases LMS / LMem / LFr / LEF / LR6); no statement names a frame-route identifier (the
   frame-route names F19F_on / F18 / RcAsanFPLib / SlotModel appear only inside Qed proofs).  Frame-route files
   Required, blobs at a working branch 1899bed1aee: Seg/F19F_on.v (a Theorem Labs lane, new; Requires Seg/F18.v e414ca1bb71 for its
   helper lemmas), RcAsanFPLib.v e1f4a4f0b5a, SlotModel.v d544a5956be and SlotInv.v 689d6853b42 (the route (C) walk's blobs);
   route (C) leaves by path from a Theorem Labs lane f4423e55886 (the root-free bcmp proof): bcmp_wrap_c.v 64293314ee8,
   bcmp_wrap_c_on.v ca2f37ea2b6, bcmp_wrap_on.v 49fcbf2eeed, bcmp_wrap_Fk.v 1fa5b214cf3, A/MemNormP.v e45ea6f496f;
   AsanRT.v b67d26f8ec7 (mcs 30), AsanRTFacts.v 1657e654e8c.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are fully qualified everywhere (checked: no unqualified
   occurrence outside comments).

   BUILD STATE: type-checked with cb build on a build machine (workspace (internal path)) on a working branch 1899bed1aee;
   the build of record is the lane's cbrec run (report).  No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq Reusable.YG00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.AsanRTFacts A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.ACfn A.AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnK A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisWin A.ProgWorldVisFrame A.ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.rng_asan A.Prog.bcmp_wrap_c A.Prog.bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.sh_word_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F19F_on A.Prog.Seg.F18 A.Prog.RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:155 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* lib/Lib's memory modules, by their full paths (lib/A/Bz/Lib and lib/AZ/Lib carry files of the same names). *)
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module FPL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFPLib.
Module F18 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F18.

(* ---------------------------------------------------------------------------------------------------------
   Route (C) region lemmas: an aligned shadow-word range (A.Prog.sh_word_on) is a cut_shadow byte when its bytes lie
   in the owned class-6 frame ((F) disjunct) or in a live block ((L) disjunct), A.ACtlRtC.v:25-36. *)
Lemma glue_f19_frame_sh : forall (B : Reusable.YG0f.asyms) ly (S : Reusable.YG00.astate) pos fr p n a,
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

Lemma glue_f19_block_sh : forall (B : Reusable.YG0f.asyms) ly (S : Reusable.YG00.astate) ph ln p n a,
  In (ph, ln) (Reusable.YG0d.ablocks B ly S) -> ph <= p -> p + n <= ph + Reusable.YG00.req_size ln ->
  A.Prog.sh_word_on.sh_word_on p n a -> A.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros B ly S ph ln p n a Hin Hlo Hhi (Hn & Ha).
  right. left. exists ph, ln. split; [exact Hin|].
  unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   Local keep lemmas: the cut body's memory facts across a run whose writes are a munch W (sources in the header). *)

(* ACtlCutP.FLSI (ACtlCutP.v:677-680) across a munch: its spills at [A + 32, A + 288), the frame body (stk), the
   input block's bytes, and the shadow bytes its addressability reads. *)
Lemma f19_flsi_keep : forall cx j fr (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list LFr.ivl)
    (A : Z),
  A.ACtlCutP.FLSI cx j fr regs m -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 512 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  LFr.munch W m m' -> LFr.wmono A.Img0.rsegs m m' ->
  (forall x, A + 32 <= x < A + 288 -> LFr.outside W x) ->
  (forall x, fr <= x < fr + A.ACtlCutP.FRAME_BYTES -> LFr.outside W x) ->
  (forall x, A.AsanRT.in_shadow x -> LFr.outside W x) ->
  (forall x, A.ACtlCut.c_p cx <= x < A.ACtlCut.c_p cx + Z.of_nat (length (A.ACtlCut.c_in cx)) ->
     LFr.outside W x) ->
  A.ACtlCutP.FLSI cx j fr regs' m'.
Proof.
  intros cx j fr regs regs' m m' W A HFLSI HA9 HA0 HA512 E9 MU WM HWsp HWfr HWsh HWin.
  assert (HSK : forall off v, 32 <= off <= 280 -> A.ACtlCutP.spill regs m off v -> A.ACtlCutP.spill regs' m' off v).
  { intros off v Hoff Hsp. apply (A.ACtlG.KitMem.kitmem_spill_munch W regs regs' m m' off v A Hsp HA9 HA0 ltac:(lia) ltac:(lia) MU E9).
    intros x Hx. apply HWsp. lia. }
  assert (HAD : forall p n, A.AsanRT.addressable m p n -> A.AsanRT.addressable m' p n)
    by (intros p n H; exact (FPL.fl_addressable W m m' p n H MU HWsh)).
  destruct HFLSI as (((Fs40 & Fs120 & Fs136 & Fs160 & Fs168 & Fs176 & Fs208 & Fs248p & Fad & Fpb & Fph &
                       P184 & P256 & P264 & P272 & P32) &
                      Fs128 & Fstk & Fs144 & Fad2691) &
                     Fs216 & Fs224 & Fs248 & (Finad & Finb) &
                     (Cs256 & Cs184 & Cs192 & Cs80 & Cs88 & Cs96 & Cs272 & Cs264 & Cad1 & Cad2 &
                      Cs72 & Cs64 & Cs56 & Cs48)).
  assert (HIN : LMem.bytes_at A.Img0.rsegs m' (A.ACtlCut.c_p cx) (A.ACtlCut.c_in cx))
    by exact (FPL.fl_bytes W m m' _ _ Fpb MU HWin).
  split.
  { split.
    { split; [exact (HSK 40 _ ltac:(lia) Fs40)|].
      split; [exact (HSK 120 _ ltac:(lia) Fs120)|].
      split; [exact (HSK 136 _ ltac:(lia) Fs136)|].
      split; [exact (HSK 160 _ ltac:(lia) Fs160)|].
      split; [exact (HSK 168 _ ltac:(lia) Fs168)|].
      split; [exact (HSK 176 _ ltac:(lia) Fs176)|].
      split; [exact (HSK 208 _ ltac:(lia) Fs208)|].
      split; [exact (HSK 248 _ ltac:(lia) Fs248p)|].
      split; [exact (HAD _ _ Fad)|].
      split; [exact HIN|].
      split; [intros Hn; exact (HAD _ _ (Fph Hn))|].
      split; [exact (HSK 184 _ ltac:(lia) P184)|]. split; [exact (HSK 256 _ ltac:(lia) P256)|].
      split; [exact (HSK 264 _ ltac:(lia) P264)|].
      split; [exact (HSK 272 _ ltac:(lia) P272) | exact (HSK 32 _ ltac:(lia) P32)]. }
    split; [exact (HSK 128 _ ltac:(lia) Fs128)|].
    split; [exact (FPL.fl_stk W m m' fr (fr + A.ACtlCutP.FRAME_BYTES) Fstk MU WM (fun x Hx => or_introl (HWfr x Hx)))|].
    split; [exact (HSK 144 _ ltac:(lia) Fs144) | exact (HAD _ _ Fad2691)]. }
  split; [exact (HSK 216 _ ltac:(lia) Fs216)|].
  split; [exact (HSK 224 _ ltac:(lia) Fs224)|].
  split; [exact (HSK 248 _ ltac:(lia) Fs248)|].
  split; [split; [exact (HAD _ _ Finad) | exact HIN]|].
  split; [exact (HSK 256 _ ltac:(lia) Cs256)|]. split; [exact (HSK 184 _ ltac:(lia) Cs184)|].
  split; [exact (HSK 192 _ ltac:(lia) Cs192)|]. split; [exact (HSK 80 _ ltac:(lia) Cs80)|].
  split; [exact (HSK 88 _ ltac:(lia) Cs88)|]. split; [exact (HSK 96 _ ltac:(lia) Cs96)|].
  split; [exact (HSK 272 _ ltac:(lia) Cs272)|]. split; [exact (HSK 264 _ ltac:(lia) Cs264)|].
  split; [exact (HAD _ _ Cad1)|]. split; [exact (HAD _ _ Cad2)|].
  split; [exact (HSK 72 _ ltac:(lia) Cs72)|]. split; [exact (HSK 64 _ ltac:(lia) Cs64)|].
  split; [exact (HSK 56 _ ltac:(lia) Cs56) | exact (HSK 48 _ ltac:(lia) Cs48)].
Qed.

(* ACtlCutP.LT = IFS cx fr (S j) (ACtlCutP.v:724-725) across a munch: the identity record (fr + 2688, 38 bytes),
   the fragment record (fr + 2768, 72), the first fragment's body (fr + 2880, at most 35) and its shadow, the two
   spills [A + 104] / [A + 112]. *)
Lemma f19_lt_keep : forall cx fr j (regs regs' : bvmap 5 word) (m m' : word -> option byte) (W : list LFr.ivl)
    (A : Z),
  A.ACtlCutP.LT cx fr j regs m -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> A + 512 <= 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs' 9 =
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9 ->
  LFr.munch W m m' ->
  (forall x, fr + 2688 <= x < fr + 2915 -> LFr.outside W x) ->
  (forall x, A + 104 <= x < A + 120 -> LFr.outside W x) ->
  (forall x, A.AsanRT.in_shadow x -> LFr.outside W x) ->
  A.ACtlCutP.LT cx fr j regs' m'.
Proof.
  intros cx fr j regs regs' m m' W A HLT HA9 HA0 HA512 E9 MU Hfrw HAw HWsh.
  destruct HLT as ((Hid & Hidok) & (Hfg & Hfgok) & H104 & H112 & Hbody & Hbad & HFI).
  split.
  { split; [|exact Hidok].
    apply (FPL.fl_bytes W m m' _ _ Hid MU).
    rewrite F18.f18_t_ID_length. intros x Hx. apply Hfrw. lia. }
  split.
  { split; [|exact Hfgok].
    apply (FPL.fl_bytes W m m' _ _ Hfg MU).
    rewrite F18.f18_t_FG_length. intros x Hx. apply Hfrw. lia. }
  split; [apply (A.ACtlG.KitMem.kitmem_spill_munch W regs regs' m m' 104 _ A H104 HA9 HA0 ltac:(lia) ltac:(lia) MU E9);
          intros x Hx; apply HAw; lia|].
  split; [apply (A.ACtlG.KitMem.kitmem_spill_munch W regs regs' m m' 112 _ A H112 HA9 HA0 ltac:(lia) ltac:(lia) MU E9);
          intros x Hx; apply HAw; lia|].
  split.
  { apply (FPL.fl_bytes W m m' _ _ Hbody MU).
    intros x Hx. apply Hfrw.
    pose proof (F18.f18_fsbody_length (A.ACtlCut.c_in cx) (S j)) as HB. lia. }
  split; [exact (FPL.fl_addressable W m m' _ _ Hbad MU HWsh) | exact HFI].
Qed.

(* ACtlCutP.rec_inv (ACtlCutP.v:783-797) across a munch: the record bytes at [phi, phi + 50), the spills
   [A + 200, A + 288), their shadow bytes (low memory, phi being app memory) and the u16 at fr + 196. *)
Lemma f19_rec_inv_keep : forall cx j (fr phi A : Z) (m m' : word -> option byte) (W : list LFr.ivl),
  A.ACtlCutP.rec_inv cx j fr phi A m -> LFr.munch W m m' ->
  (forall x, phi <= x < phi + 50 -> LFr.outside W x) ->
  (forall x, A + 200 <= x < A + 288 -> LFr.outside W x) ->
  (forall x, 0 <= x < A.AsanRT.HIGHMEM_BEG -> LFr.outside W x) ->
  (forall x, fr + 196 <= x < fr + 198 -> LFr.outside W x) ->
  A.ACtlCutP.rec_inv cx j fr phi A m'.
Proof.
  intros cx j fr phi A m m' W (Hp0 & Hp50 & Hfl & Htk & Hpap & H192 & H18 & H34 &
     field16 & v14 & v15 & v16 & v17 & Hkp & H280 & Hf16 & Hb14 & Hb15 & Hb16 & Hb17 &
     Rv14 & Rv15 & Rv16 & Rv17 & Hs14 & Hs15 & Hs16 & Hs17 & Heq1 & Heq2)
    MU OWphi OWspill OWlo OWkp.
  assert (SHlo : forall t, 14 <= t <= 17 -> 0 <= Z.shiftr (phi + t) 3 + A.ACtlK.ASAN_K < A.AsanRT.HIGHMEM_BEG).
  { intros t Ht. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (A.AsanRTFacts.shadow_of_app (phi + t) (Hpap (phi + t) ltac:(lia))) as His.
    unfold A.ACtlK.ASAN_K, A.AsanRT.shadow_addr, A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END,
      A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG, A.AsanRT.ASAN_K in *.
    destruct His as [His|His]; lia. }
  assert (Hq : forall a v, A.ACtlCutP.q64 m a v -> (forall x, a <= x < a + 8 -> LFr.outside W x) ->
                 A.ACtlCutP.q64 m' a v).
  { intros a v H HO. unfold A.ACtlCutP.q64 in *. apply (FPL.fl_bytes W m m' a _ H MU).
    rewrite LMem.length_le8. intros x Hx. apply HO. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia. }
  assert (Hb : forall a v, A.ACtlCutP.b8 m a v -> (forall x, a <= x < a + 1 -> LFr.outside W x) ->
                 A.ACtlCutP.b8 m' a v).
  { intros a v H HO. unfold A.ACtlCutP.b8 in *. apply (FPL.fl_bytes W m m' a _ H MU).
    cbn [length Z.of_nat Pos.of_succ_nat]. exact HO. }
  unfold A.ACtlCutP.rec_inv.
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|]. split; [exact Hpap|].
  split; [apply (Hq _ _ H192); intros x Hx; apply OWspill; lia|].
  split; [apply (FPL.fl_bytes W m m' _ _ H18 MU); intros x Hx; apply OWphi; unfold A.Prog.SlotModel.t_blk in Hx;
          pose proof (F18.bsl_len_le (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j) 18 32) as BL;
          change (Z.to_nat 32) with 32%nat in BL; lia|].
  split; [apply (FPL.fl_bytes W m m' _ _ H34 MU); intros x Hx; apply OWphi;
          pose proof (F18.bsl_len_le (A.Prog.SlotModel.t_g (A.ACtlCut.c_in cx) j) 34 6) as BL;
          change (Z.to_nat 6) with 6%nat in BL; lia|].
  exists field16, v14, v15, v16, v17.
  split; [apply (Hq _ _ Hkp); intros x Hx; apply OWspill; lia|].
  split; [apply (Hq _ _ H280); intros x Hx; apply OWspill; lia|].
  split; [unfold A.ACtlCutP.u16 in *; apply (FPL.fl_bytes W m m' _ _ Hf16 MU); rewrite LMem.length_le2;
          intros x Hx; apply OWkp; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia|].
  split; [apply (Hb _ _ Hb14); intros x Hx; apply OWphi; lia|].
  split; [apply (Hb _ _ Hb15); intros x Hx; apply OWphi; lia|].
  split; [apply (Hb _ _ Hb16); intros x Hx; apply OWphi; lia|].
  split; [apply (Hb _ _ Hb17); intros x Hx; apply OWphi; lia|].
  split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
  split; [apply (Hb _ _ Hs14); intros x Hx; apply OWlo; pose proof (SHlo 14 ltac:(lia)); lia|].
  split; [apply (Hb _ _ Hs15); intros x Hx; apply OWlo; pose proof (SHlo 15 ltac:(lia)); lia|].
  split; [apply (Hb _ _ Hs16); intros x Hx; apply OWlo; pose proof (SHlo 16 ltac:(lia)); lia|].
  split; [apply (Hb _ _ Hs17); intros x Hx; apply OWlo; pose proof (SHlo 17 ltac:(lia)); lia|].
  split; [exact Heq1 | exact Heq2].
Qed.

Section GlueF19.

(* ACtl.v's Section shape (ACtl.v:162-166), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState}
        {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:187, :191-192), verbatim, and this stage's two cuts. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82400_at := (ACtlCutP.C_A82400_at B).
Local Notation C_A82418_at := (ACtlCutP.C_A82418_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis), as A5.v:153 and ACtl.v:183. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
(* The core's symbol record for B (ACtl.v:252, verbatim): rt_of_core_C's first premise. *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_F19 : forall POST (j : nat), CF POST (ix_cut C_A82418_at [Z.of_nat j]) -> CF POST (ix_cut C_A82400_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB0 HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [j] (ix_cut, ACtlCut.v:232-234; C_A82400_at, ACtlCutP.v:2494-2518). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82400_at] in Hb.
  set (jj := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct Hb as (phi & HP & HFRAC & Hn & Hj & HHB & HFLSI & HLK &
    (A & ls2 & rs2 & HA9 & HAb & HspA & R23 & R24 & R10 & R22 & HRI & Q136 & Q120 & Q176 & Q64 &
     HBL & HLls & HBR & HLrs & Hmm & HADL & HADR & Hdj50) &
    R18 & S152 & Hbtg & Hbtphi & Hblen & HLT).
  (* G2: bounds, from visible state only. *)
  pose proof HFRAC as (A1 & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hf32 & HA32 & HAS & HspA1 &
    HfrA & HA416 & HSlo & HSapp & _).
  assert (HspR : 0 <= sp < 2 ^ 64).
  { rewrite <- HspZ. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 2))
      as Hr.
    unfold bv_modulus in Hr. exact Hr. }
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HSapp.
  assert (EA : A1 = A).
  { unfold ACtlCut.rgv in R9, HA9. rewrite HA9 in R9.
    apply (f_equal bv_unsigned) in R9. rewrite !Z_to_bv_unsigned in R9. unfold bv_wrap in R9.
    change (bv_modulus 64) with (2 ^ 64) in R9. rewrite !Z.mod_small in R9 by lia. lia. }
  subst A1.
  (* the journal: AR, the layout's ly_F, the stack window's presence and astk_ok *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hlo & _).
  unfold A.ACfn.LLVMF_STK in Hpres, Hlo.
  pose proof (@Reusable.YCbq.asan_consts rc) as (Hcv & _).
  (* the owned class-6 frame: fr = frame_addr ly3 6 pos, [fr, fr + 4096) below alloc_ceiling and in app memory *)
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  rewrite Efr3 in Hf4096, Hfceil, Hfapp.
  assert (Hfs6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite Hfs6 in Hfceil, Hfapp.
  (* the record block (phi, flen cx jj): a live block, below alloc_ceiling *)
  pose proof HRI as (Hphi0 & Hphi50 & Hfl50 & Htk & Hpapp & H200 & _).
  assert (Hinphi : In (phi, ACtlCutP.flen cx jj) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
  destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx jj) HAR Hinphi)
    as (_ & Hp4096 & Hpceil & _).
  assert (Ereq : Reusable.YG00.req_size (ACtlCutP.flen cx jj) = ACtlCutP.flen cx jj).
  { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx jj) 0); lia. }
  rewrite Ereq in Hpceil.
  (* the wrapper's write window W = [sp - 4560, sp): above alloc_ceiling and the shadow, below the spill base *)
  assert (HOW : forall x, x < sp - 4560 \/ sp <= x -> LFr.outside [(sp - 4560, sp)] x).
  { intros x Hx. cbn [LFr.outside]. split; [lia | exact I]. }
  assert (HWlo : forall x, x < OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling ->
                   LFr.outside [(sp - 4560, sp)] x) by (intros x Hx; apply HOW; left; lia).
  assert (HWsh : forall x, A.AsanRT.in_shadow x -> LFr.outside [(sp - 4560, sp)] x).
  { intros x Hx. apply HWlo. unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END,
      A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG in Hx. lia. }
  assert (HWlow : forall x, 0 <= x < A.AsanRT.HIGHMEM_BEG -> LFr.outside [(sp - 4560, sp)] x).
  { intros x Hx. apply HWlo. unfold A.AsanRT.HIGHMEM_BEG in Hx. lia. }
  (* the input block: empty, or a live block below alloc_ceiling (the core's pre, ACfn.v:38-39) *)
  pose proof HB0 as ((_ & _ & _ & _ & Hpn & Hnlen & _) & _).
  assert (HWin : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) ->
                   LFr.outside [(sp - 4560, sp)] x).
  { intros x Hx. rewrite <- Hnlen in Hx. destruct Hpn as [[Hn0 _] | [Hnpos Hinp]]; [lia|].
    assert (Hinp3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hinp. }
    destruct (Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hinp3) as (_ & _ & Hpc & _).
    unfold Reusable.YG00.req_size in Hpc. destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); [lia|].
    apply HWlo. lia. }
  (* the run's register binders, read through reg_get *)
  assert (Esp : bv_unsigned (Sem.reg_get regs3 2) = sp) by exact HspZ.
  (* route (C): the entry's ctl_rt_C B ly3 S3 mem3 (ACtlRtC.v:44-46) *)
  pose proof Hrt as (Hcells & Hcut & Himg & Hroag).
  (* the five wrapper cells, from a Theorem Labs lane's PROVED rt_of_core_C (ProgWorldRtC.v:76) at the cut *)
  pose proof (A.ProgWorldRtC.rt_of_core_C B MT XM_LIB RLO RHI [] TFIB_SYMS LAWS cx (ACtlCut.own6 cx) k ly3 S3 W3
    (LMS.MS regs3 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82400)
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
       (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs)) md3 HB0 HJ Hrt) as HRT.
  destruct HRT as (_ & _ & _ & _ & HCF & _ & _ & HREAL).
  rewrite Forall_forall in HREAL.
  assert (HRB : LMem.bytes_at A.Img0.rsegs mem3 A.Prog.bcmp_wrap_c.REAL_BCMP
                  (LMem.le8 (LMem.wa A.Prog.bcmp_wrap_c.BCMP))).
  { exact (HREAL (0xa17f0, 0x97b0c) ltac:(cbv [A.AsanRT.RT_REALS]; repeat (apply in_eq || apply in_cons))
             ltac:(cbv [A.ProgWorld.REAL_USED fst]; repeat (apply in_eq || apply in_cons))). }
  assert (HRM : LMem.bytes_at A.Img0.rsegs mem3 A.Prog.bcmp_wrap_c.REAL_MEMCMP
                  (LMem.le8 (LMem.wa OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.MEMCMP))).
  { exact (HREAL (0xa17e8, 0x97bdc) ltac:(cbv [A.AsanRT.RT_REALS]; repeat (apply in_eq || apply in_cons))
             ltac:(cbv [A.ProgWorld.REAL_USED fst]; repeat (apply in_eq || apply in_cons))). }
  destruct HCF as (HGC & _ & _ & _ & _ & _ & HCF240 & _).
  assert (HC254 : LMem.bytes_at A.Img0.rsegs mem3 (A.Prog.bcmp_wrap_c.CF + 254) [Z_to_bv 8 1]).
  { pose proof (F18.ba_sub mem3 (A.AsanRT.RT_CF + 240)
      (A.AsanRT.cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 14 1 HCF240 ltac:(cbn; lia)) as Hs.
    replace (A.AsanRT.RT_CF + 240 + Z.of_nat 14) with (A.Prog.bcmp_wrap_c.CF + 254) in Hs
      by (unfold A.Prog.bcmp_wrap_c.CF, A.AsanRT.RT_CF; lia).
    exact Hs. }
  assert (HC255 : LMem.bytes_at A.Img0.rsegs mem3 (A.Prog.bcmp_wrap_c.CF + 255) [Z_to_bv 8 1]).
  { pose proof (F18.ba_sub mem3 (A.AsanRT.RT_CF + 240)
      (A.AsanRT.cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 15 1 HCF240 ltac:(cbn; lia)) as Hs.
    replace (A.AsanRT.RT_CF + 240 + Z.of_nat 15) with (A.Prog.bcmp_wrap_c.CF + 255) in Hs
      by (unfold A.Prog.bcmp_wrap_c.CF, A.AsanRT.RT_CF; lia).
    exact Hs. }
  (* the wrapper's stack premise: the journal's stack window [c_sp - LLVMF_STK, sp) is present *)
  assert (Hstk : LFr.stk A.Img0.rsegs mem3 (ACtlCut.c_sp cx - 32768) (bv_unsigned (Sem.reg_get regs3 2))).
  { rewrite Esp. split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hpres a ltac:(lia)) as [_ (b & Hb)].
    unfold LMem.wa. split.
    - unfold wview. rewrite Hb. discriminate.
    - exists b. unfold LMem.mrd. rewrite Hb. reflexivity. }
  (* the footprint RNG_W (w_H W3) *)
  set (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (Hwin : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= ACtlCut.c_sp cx ->
                   LEF.rng RNG lo len).
  { intros lo len H1 H2. apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
             (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
             (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k lo len HJ);
      unfold A.ACfn.LLVMF_STK; lia. }
  assert (G200 : LEF.rng RNG (A + 200) 8) by (apply Hwin; lia).
  assert (G64 : LEF.rng RNG (A + 64) 8) by (apply Hwin; lia).
  assert (Gimg : LEF.rng RNG 0x10000 0x5ee000) by exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3)).
  assert (Gstk : LEF.rng RNG (bv_unsigned (Sem.reg_get regs3 2) - A.Prog.bcmp_wrap_c.BCMP_WRAP_K)
                   A.Prog.bcmp_wrap_c.BCMP_WRAP_K).
  { rewrite Esp. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. apply Hwin; lia. }
  destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 180) 6 HAR Hin6
              ltac:(rewrite Efr3; lia) ltac:(rewrite Efr3, Hfs6; lia)) as (HVL & HVLs).
  assert (Hal : fr <= 64 * ((fr + 180) / 64) /\ 64 * ((fr + 180 + 6 - 1) / 64) + 64 <= fr + 4096)
    by (clear - Hf32 Hf4096; Z.div_mod_to_equations; lia).
  destruct (HVLs ltac:(lia) ltac:(rewrite Efr3; lia) ltac:(rewrite Efr3, Hfs6; lia)) as [E0 | HVLs']; [lia|].
  assert (GL : LEF.rng RNG (fr + 180) 6) by exact (A.ProgBridge.rng_of_visible _ _ _ HVL).
  assert (GsL : LEF.rng RNG (8 * (A.AsanRT.shadow_addr (fr + 180) / 8))
                  (8 * (A.AsanRT.shadow_addr (fr + 180 + 6 - 1) / 8) + 8 - 8 * (A.AsanRT.shadow_addr (fr + 180) / 8))).
  { apply A.ProgBridge.rng_of_visible.
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in HVLs'. rewrite !(Z.mul_comm _ 8) in HVLs'.
    exact HVLs'. }
  assert (GR : LEF.rng RNG (phi + 6) 6).
  { apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx jj) (phi + 6) 6 HAR Hinphi);
      rewrite ?Ereq; lia. }
  destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx jj) (phi + 6) 6
              HAR Hinphi ltac:(lia) ltac:(rewrite Ereq; lia) ltac:(lia)) as [E0 | HVR]; [lia|].
  assert (GsR : LEF.rng RNG (8 * (A.AsanRT.shadow_addr (phi + 6) / 8))
                  (8 * (A.AsanRT.shadow_addr (phi + 6 + 6 - 1) / 8) + 8 - 8 * (A.AsanRT.shadow_addr (phi + 6) / 8))).
  { apply A.ProgBridge.rng_of_visible.
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in HVR. rewrite !(Z.mul_comm _ 8) in HVR.
    exact HVR. }
  (* the remaining numeric premises *)
  assert (HaL6 : A.AsanRT.app_mem (fr + 180 + 6)).
  { unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfapp.
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (HaL7 : A.AsanRT.app_mem (fr + 180 + 7)).
  { unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hfapp.
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  assert (HdjL : fr + 180 + 6 <= bv_unsigned (Sem.reg_get regs3 2) - A.Prog.bcmp_wrap_c.BCMP_WRAP_K \/
                 bv_unsigned (Sem.reg_get regs3 2) <= fr + 180).
  { rewrite Esp. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K. left. lia. }
  assert (HdjR : phi + 12 <= bv_unsigned (Sem.reg_get regs3 2) - A.Prog.bcmp_wrap_c.BCMP_WRAP_K \/
                 bv_unsigned (Sem.reg_get regs3 2) <= phi + 6).
  { rewrite Esp. rewrite HspZ in Hdj50. destruct Hdj50 as [Hd|Hd]; [left | right]; lia. }
  (* the run's shadow premise (F19F_on: bcmp_wrap_shadow_R L (R + 6) 6 at L = fr + 180, R = phi), from the cut's
     region: [fr + 180, fr + 186) is in the owned class-6 frame ((F)), [phi + 6, phi + 12) in the live record block
     (phi, flen) ((L)) *)
  assert (HSW : A.ShadowRwOn.shadow_rw_on (A.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R (fr + 180) (phi + 6) 6) mem3).
  { apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3) _ mem3); [|exact Hcut].
    intros a [Ha | Ha].
    - exact (glue_f19_frame_sh B ly3 S3 (ACtlCut.c_fpos cx) fr (fr + 180) 6 a Hin6 Efr3 Hf32
               ltac:(lia) ltac:(lia) Ha).
    - exact (glue_f19_block_sh B ly3 S3 phi (ACtlCutP.flen cx jj) (phi + 6) 6 a Hinphi ltac:(lia)
               ltac:(rewrite Ereq; lia) Ha). }
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82400_at [Z.of_nat j])) with 0x82400.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x82400)
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  unfold LR6.mkR_of.
  (* G4: the run (f19_evt_ro_F_on, binders at reg_get regs3 r) and the lift. *)
  pose proof (A.Prog.Seg.F19F_on.f19_evt_ro_F_on RNG
    (Sem.reg_get regs3 1) (Sem.reg_get regs3 2) (Sem.reg_get regs3 3) (Sem.reg_get regs3 4) (Sem.reg_get regs3 5)
    (Sem.reg_get regs3 6) (Sem.reg_get regs3 7) (Sem.reg_get regs3 8) (Sem.reg_get regs3 9) (Sem.reg_get regs3 10)
    (Sem.reg_get regs3 11) (Sem.reg_get regs3 12) (Sem.reg_get regs3 13) (Sem.reg_get regs3 14)
    (Sem.reg_get regs3 15) (Sem.reg_get regs3 16) (Sem.reg_get regs3 17) (Sem.reg_get regs3 18)
    (Sem.reg_get regs3 19) (Sem.reg_get regs3 20) (Sem.reg_get regs3 21) (Sem.reg_get regs3 22)
    (Sem.reg_get regs3 23) (Sem.reg_get regs3 24) (Sem.reg_get regs3 25) (Sem.reg_get regs3 26)
    (Sem.reg_get regs3 27) (Sem.reg_get regs3 28) (Sem.reg_get regs3 29) (Sem.reg_get regs3 30)
    (Sem.reg_get regs3 31)
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr mem3
    A (fr + 180) phi ls2 rs2 0 (ACtlCut.c_sp cx - 32768)
    HA9 R23 R10 ltac:(lia) ltac:(lia) ltac:(lia) H200 Q64 HBL HLls HBR HLrs Hmm Hroag
    HADL HADR HaL6 HaL7 (Hpapp (phi + 12) ltac:(lia)) (Hpapp (phi + 13) ltac:(lia)) HdjL HdjR Hstk
    ltac:(rewrite Esp; unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K; lia)
    ltac:(unfold A.AsanRT.HIGHMEM_BEG; lia) ltac:(rewrite Esp; unfold A.AsanRT.APPMEM_END; lia)
    Hcells HSW HRB HRM HGC HC254 HC255
    G200 G64 (A.ProgBridge.rng_bytes_RNG_W _) Gimg Gstk GL GsL GR GsR) as HRUN.
  destruct (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as (ms' & Hrun & HQ).
  rewrite <- A.ProgBridge.tfibsegs_rsegs in Hrun.
  apply (Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 _ ms' md3 RNG (POST cx) Hrun
           (A.ProgBridge.fp_avoids_RNG_W _)).
  intros md' Hsame.
  (* G5: the end state, and the exit cut C_A82418_at at its map R and memory m'. *)
  destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m' &
    Ems & MU & WM & RO' & ROS & ST').
  rewrite Esp in MU. unfold A.Prog.bcmp_wrap_c.BCMP_WRAP_K in MU.
  (* the journal across the run: every written byte lies in the journal's stack window *)
  assert (Hwr : forall a, 0 <= a < 2 ^ 64 -> ~ LFr.outside [(sp - 4560, sp)] a ->
    Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
      (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
      (ACtlCut.own6 cx) a).
  { intros a _ Ho. left. unfold A.ACfn.LLVMF_STK.
    destruct (Z_lt_le_dec a (sp - 4560)) as [H1|H1]; [exfalso; exact (Ho (HOW a (or_introl H1)))|].
    destruct (Z_lt_le_dec a sp) as [H2|H2]; [lia | exfalso; exact (Ho (HOW a (or_intror H2)))]. }
  subst ms'.
  match type of Hrun with Reusable.YK04R.fsteps _ _ ?s0 ?s1 =>
    pose proof (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
      (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
      (ACtlCut.own6 cx) ly3 S3 W3 s0 s1 md3 md' k RNG [(sp - 4560, sp)] HJ Hrun
      (A.ProgBridge.fp_avoids_RNG_W _) MU Hsame Hwr) as HJ'
  end.
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (?M ?R _ _ _ _ _ _) _) _ => set (Rx := R) end.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82418_at [Z.of_nat j]))
            Rx m' md') (POST cx)).
  assert (E9 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr Rx 9 =
               OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 9) by exact (eq_sym HA9).
  assert (HA9x : ACtlCut.rgv Rx 9 A) by reflexivity.
  (* the body's bytes across the window *)
  assert (Hblk : forall x, phi <= x < phi + ACtlCutP.flen cx jj -> LFr.outside [(sp - 4560, sp)] x)
    by (intros x Hx; apply HWlo; lia).
  assert (Hq : forall a v, sp <= a -> ACtlCutP.q64 mem3 a v -> ACtlCutP.q64 m' a v).
  { intros a v Ha H. unfold ACtlCutP.q64 in *. apply (FPL.fl_bytes _ mem3 m' a _ H MU).
    rewrite LMem.length_le8. intros x Hx. apply HOW. right. lia. }
  pose proof (f19_rec_inv_keep cx jj fr phi A mem3 m' _ HRI MU
                ltac:(intros x Hx; apply Hblk; lia) ltac:(intros x Hx; apply HOW; right; lia) HWlow
                ltac:(intros x Hx; apply HWlo; lia)) as HRI'.
  destruct HRI' as (Hp0' & Hp50' & Hfl' & Htk' & Hpap' & H200' & H18' & H34' &
    field16 & v14 & v15 & v16 & v17 & Hkp & H280 & Hf16 & Hb14 & Hb15 & Hb16 & Hb17 &
    Rv14 & Rv15 & Rv16 & Rv17 & Hs14 & Hs15 & Hs16 & Hs17 & Heq1 & Heq2).
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 Rx m' md' HB0 HJ' HF HL Hk).
  - (* the exit body, C_A82418_at (ACtlCutP.v:2522-2554), at the same turn *)
    split; [reflexivity|].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82418_at].
    fold jj.
    exists phi.
    split; [exact HP|].
    split.
    { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 Rx m');
        [| reflexivity | reflexivity | reflexivity | reflexivity | exact E9 | reflexivity | reflexivity].
      apply (A.ACtlG.KitMem.kitmem_frac_munch B cx fr fr regs3 mem3 m' _ HFRAC MU).
      - intros x Hx. apply HOW. right. lia.
      - intros x Hx. apply HWlo. lia.
      - intros x Hx. apply HWlow. clear - Hx Hfceil Hcv Hf4096.
        unfold ACtlCutP.Sfr, ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES,
          A.AsanRT.shadow_addr, A.AsanRT.ASAN_K, A.AsanRT.HIGHMEM_BEG in *. Z.div_mod_to_equations. lia. }
    split; [exact Hn|]. split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
      exact (FPL.fl_addressable _ mem3 m' _ _ Hphiad MU HWsh). }
    split.
    { apply (f19_flsi_keep cx jj fr regs3 Rx mem3 m' _ A HFLSI HA9 ltac:(lia) ltac:(lia) E9 MU WM);
        [intros x Hx; apply HOW; right; lia
        | intros x Hx; apply HWlo; unfold ACtlCutP.FRAME_BYTES in Hx; lia | exact HWsh | exact HWin]. }
    split.
    { destruct HLK as (Hj' & R21 & HOUR). split; [exact Hj'|]. split; [exact R21|].
      unfold ACtlCutP.OURb in *. apply (FPL.fl_bytes _ mem3 m' _ _ HOUR MU).
      rewrite A.Prog.SlotModel.OUR_length. intros x Hx. apply HWlo. lia. }
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact R22|]. split; [exact R24|].
    split; [reflexivity|].
    split; [exact Hp0'|]. split; [exact Hp50'|]. split; [exact Hfl'|]. split; [exact Htk'|].
    split; [exact H18'|]. split; [exact H34'|].
    split; [exists A; split; [exact HA9x | exact H280]|].
    split; [exists A; split; [exact HA9x | exact (Hq (A + 136) _ ltac:(lia) Q136)]|].
    split; [exists A; split; [exact HA9x | exact (Hq (A + 120) _ ltac:(lia) Q120)]|].
    split; [exists A; split; [exact HA9x | exact (Hq (A + 176) _ ltac:(lia) Q176)]|].
    split.
    { exists v14, v15, v16, v17, field16.
      split; [exists A; split; [exact HA9x | exact Hkp]|].
      split; [replace (fr + 196) with (fr + 176 + 20) by lia; exact Hf16|].
      split; [exact Hb14|]. split; [exact Hb15|]. split; [exact Hb16|]. split; [exact Hb17|].
      split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
      split; [exact Hs14|]. split; [exact Hs15|]. split; [exact Hs16|]. split; [exact Hs17|].
      split; [exact Heq1 | exact Heq2]. }
    split; [exact R18|].
    split; [exact (A.ACtlG.KitMem.kitmem_spill_munch _ regs3 Rx mem3 m' 152 _ A S152 HA9 ltac:(lia) ltac:(lia) ltac:(lia) MU E9
                     ltac:(intros x Hx; apply HOW; right; lia))|].
    split.
    { apply (FPL.fl_bytes _ mem3 m' _ _ Hbtg MU).
      rewrite F18.f18_t_g_length. intros x Hx. apply Hblk. lia. }
    split.
    { apply (FPL.fl_bytes _ mem3 m' _ _ Hbtphi MU). intros x Hx. apply Hblk. lia. }
    split; [exact Hblen|].
    apply (f19_lt_keep cx fr jj regs3 Rx mem3 m' _ A HLT HA9 ltac:(lia) ltac:(lia) E9 MU);
      [intros x Hx; apply HWlo; lia | intros x Hx; apply HOW; right; lia | exact HWsh].
  - (* ctl_rt_C at the same (ly3, S3): the runtime cells are image bytes, every shadow byte is below the window
       (both regions kept across the munch, A.ShadowRwOnK.fl_shadow_rw_on), ro_agree is the run's *)
    split; [|split; [|split]].
    + apply (FPL.fl_asan_cells _ mem3 m' Hcells MU). intros x Hx. apply HWlo.
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI in Hx. lia.
    + exact (A.ShadowRwOnK.fl_shadow_rw_on _ _ mem3 m' Hcut MU WM HWsh).
    + exact (A.ShadowRwOnK.fl_shadow_rw_on _ _ mem3 m' Himg MU WM HWsh).
    + exact RO'.
Qed.

End GlueF19.
