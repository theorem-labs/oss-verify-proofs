(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F13.v, with its module names changed; 426 of its 465 lines of code are new or changed and 927 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R8.v, with its module names, addresses and numbers changed; 166 of its 338 lines of code are new or changed and 293 lines of the source are left out. *)
(* lib/A/ACtlG/R4.v -- GLUE for stage seg_R4 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:666,
   `Hypothesis seg_R4 : forall POST, CF POST C_A81588 -> CF POST C_A81578`).  Written by a Theorem Labs lane's glue lane
   (piece W0/W1); single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery), the worked example lib/A/ACtlG/A2.v.
   rule 24: no function proved (stage glue of a walk; kind: segment lemma).

   WHAT IT PROVES
     glue_seg_R4 : forall POST, CF POST C_A81588 -> CF POST C_A81578
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R4.  Segment R4 is 0x81578 -> 0x81588 (Seg/R4.v:1-7): li a2,72 ; ld a0,48(s1) ; li a1,0 ; jal checked_memset.
   The spill [A + 48] holds D = fr + 2256, so the call zeroes the 72 fragment-record bytes [D, D + 72) of the owned
   class-6 frame; the callee's stack window is [sp - 2208, sp).

   RULE 24 (released proofs first): proof-index LLVMFuzzerTestOneInput (index v5, built 2026-10-28 20:16:23Z
   from e966c513ee6, ossv/recipes@a8831f7c5c), second-agent check a Theorem Labs lane 21:10Z CONFIRM: the released ASan
   donor is cgif/cgif_file_fuzzer at origin/ossv/recipes c8557374ad2e; its walk lifts no outside-proved run, so this
   glue has no donor counterpart.  Its pieces are the donor's SRr (YA0n) and ajournal (YCbq), a Theorem Labs lane's kit and
   bridge (YA0nR.SRr_xregs_eqv / SRr_fsteps; ProgBridge; ProgWorldVis{Win,Frame}), a Theorem Labs lane's
   ProgWorld.ajournal_of_fsteps, a Theorem Labs lane's footprint run (and its route (C) twin), a Theorem Labs lane's
   asan_memset_holds_F_on, and the shared kits lib/A/ACtlG/Kit.v and lib/A/ACtlG/KitMem.v.

   THE RUN.  A.Prog.Seg.R4F_on.r4_evt_F_on (lib/A/Prog/Seg/R4F_on.v, the route (C) twin of a Theorem Labs lane's mechanical
   v1.9 re-run Seg/R4F.v (not in this delivery) r4_evt_F, which is unchanged), Required, not assumed: R4.r4_evt (Seg/R4.v:193) under a
   footprint RNG, with the callee's route (C) footprint contract asan_memset_contract_F_on as its first premise.  NO
   SPLIT (a Theorem Labs lane's split rule, 04:01Z): that premise is DISCHARGED by a Theorem Labs lane's PROVED
   A.Prog.asan_memsetF_on.asan_memset_holds_F_on A.Prog.memset.memset_holds, and the whole run is lifted once.  The
   run is stated over lib/Lib's MState with explicit F / fc, so it takes the core's fp state CK11.fp_regs /
   CK11.fp_csr directly (as a Theorem Labs lane's R8.v does), and its 31 register binders are the cut map's CK11.getr regs3 1 .. 31.

   THE PROOF, step by step (glue-pattern.md section 3, a run that writes memory)
   G1  unfold the entry cut C_A81578 (ACtlCutP.v:1230-1248): 29 conjuncts; FRAC's pins (sp, s1 = A, the stack
       bounds); ctl_rt_C's asan_cells / cut_shadow / ro_agree (its img_shadow conjunct is not read).
   G2  r4_evt_F_on's premises at spv = sp, D = fr + 2256, lo = c_sp cx - LLVMF_STK (its shadow premise: HSWr):
         registers  sp, s1 = A from FRAC;
         [A + 48]   the spill holds D (spill 48 (fr + 2256)); its 8 bytes are writable: the save area lies in the
                    journal's present stack window [c_sp - LLVMF_STK, c_sp) (KitMem.kitmem_stk_of_journal);
         [D, D + 72) present (AR_frames_law, the owned frame, KitMem.kitmem_own6), hence rw_cells over its bytes
                    (Seg/R4.v's r4_rw_CB / r4_wr_stk); addressable from the body; app memory (frames_bounds'
                    in_app); at or above IMG_HI, hence above RT_HI (local lemma r4g_frame6_above_img, from
                    a Theorem Labs lane's proved ProgWorld_Fs.ctl_frame_above_img);
         window     stk m lo sp from the journal (kitmem_stk_of_journal); lo >= alloc_ceiling >= HIGHMEM_BEG; the
                    frame lies below alloc_ceiling <= c_sp - LLVMF_STK, so below the window;
         rng        at RNG := ProgBridge.RNG_W (w_H W3): [A + 48, + 8) and the window by ProgWorldVisWin.win_vis;
                    the image by ProgBridge.img_vis_W; [D, D + 72) and its 8-aligned shadow word cover by
                    ProgWorldVisFrame.frame_vis (both components; the 64-byte hull lies inside the 4096-byte frame);
                    the window's shadow word cover by ProgWorldVisWin.win_sh_vis; rng_bytes by
                    ProgBridge.rng_bytes_RNG_W.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from the cut's map regs3 to the run's mkR_of regs3.
   G4  ProgBridge.fevt_of_evtF + tfibsegs_rsegs, then YA0nR.SRr_fsteps at RNG (fp_avoids by
       ProgBridge.fp_avoids_RNG_W); its continuation keeps the fsteps run for ajournal_of_fsteps.
   G5  the exit cut C_A81588 (ACtlCutP.v:1252-1271) at the run's end map R and memory m'
       (munch [(D, D + 72); (sp - 2208, sp)] mem3 m'), the same cx, idx, fr, k, ly3, S3, W3, the materialized md':
         journal  ProgWorld.ajournal_of_fsteps; every written byte awr_byte: [D, D + 72) by the owned frame case
                  (KitMem.kitmem_awr_frame), the window by the stack case (KitMem.kitmem_awr_win);
         frames, frame law, k bound   unchanged (own6, kmax 0 on both cuts);
         body     every memory conjunct off the write set: the save area [A, A + 416) lies at or above sp; the frame
                  cells other than [D, D + 72) by Lib.Frame.rw_cells_transport / KitMem.kitmem_bytes_munch; the
                  shadow is not written (the write set is application memory: KitMem.kitmem_addr_munch); the input
                  block is below alloc_ceiling and apart from the frame (KitMem.kitmem_input_apart); FRAC moved by
                  shape (KitMem.kitmem_frac_munch, which carries the announced trailer word) and then across the
                  register map (Kit.kit_frac_move); FGBr from the run's post (the 72 zero bytes = RFG (c_in cx) 0);
                  OUTA from the entry's out[] addressability; registers through the run's kept registers;
         ctl_rt_C A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the exit journal's AR (same ly3 S3, memory m'), with the
                  entry's arodata_okS carried along the journal (KitMem.kitmem_arodataS_journal, RELRO_IMG) and made
                  arodata_okP by ProgWorld.arodata_okP_of_S.

   ROUTE (C) (a Theorem Labs lane truth audit 11:02Z, a Theorem Labs lane 11:10Z; recipe (internal path)
   L3-recipe.md (a working note, not in this delivery)): the cut's runtime conjunct is A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.  The run's shadow premise is the
   route (C) twin's (Seg/R4F_on.v r4_evt_F_on, a Theorem Labs lane): shadow_rw_on (r4_evt_shadow_R D) with
   r4_evt_shadow_R D = sh_word_on D 72, the aligned shadow words of [D, D + 72), the shadow the callee
   __asan_memset reads (asan_memset_cF_on.v).  With D = fr + 2256 that span lies inside the owned frame's shadow
   [shadow_addr fr, shadow_addr fr + 512), cut_shadow's (F) disjunct at (6, c_fpos cx) (local fact HSWr), so it
   comes from ctl_rt_C's cut_shadow conjunct by ShadowRwOn.shadow_rw_on_mono.  The callee's premise is a Theorem Labs lane's
   proved asan_memsetF_on.asan_memset_holds_F_on memset_holds.

   SECTION HYPOTHESES (each is ACtl.v's Section hypothesis of the same name and text; the top supplies it)
   - RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a -- for the exit's arodata_okS.
   - LAWS : Reusable.YG0d.AR_laws segs B -- the core's AR law record, which kitmem_own6, frames_bounds, al_frames,
     frame_vis, win_sh_vis, ajournal_of_fsteps and ctl_rt_C_of_AR take.
   - TFIB_SYMS : A.AF0m.CtrlTSyms B -- the core's symbol record, which ctl_rt_C_of_AR takes.
   The owned frame at or above IMG_HI is a Theorem Labs lane's PROVED, premise-free A.ProgWorld_Fs.ctl_frame_above_img
   (statement ProgWorld.ctl_frame_above_img_stmt, every class), cited by name; the run is Required from
   Seg/R4F_on.v and its callee premise is a Theorem Labs lane's proved theorem.

   READS NO PLANNING-CORE VALUE that differs from the record (ts_zsh / am_const / owned_static / const_shadow /
   TFIB_GP / pc_wrap_* / pc_stack_malloc / AB01): gp passes through FRAC symbolically.
   NOT USED: rt_of_core (the runtime facts the run needs are ctl_rt_C's, from the cut); the frame-route RT
   conjuncts of the premise rows.

   CLOSURE (glue closure rule, a Theorem Labs lane 23:32Z, porter 23:38Z / 23:40Z): every Require is qualified (no Import /
   Export of a project module); no statement here names a frame-route identifier.  The twin modules (YK11 YM05 YO09
   YI16) and lib/Lib are named absolutely and written through the aliases below.  Frame-route files of record in the
   closure come through Seg/R4F_on.v -> Seg/R4.v (SlotInv, SlotModel, AsanRTInv, Contract, FrameAPI, MemNorm, Tac_slot,
   Tac_b5, Tac_fs, RcPro); their blobs are named in the commit.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are fully qualified (through CK11) or Reusable.YG0d-qualified
   everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/R4.v   -- hits only inside comments.

   BUILD STATE (honest): type-check on a working branch shell merged on this branch (cb build); the build of
   record is cbrec's (log and .prov named in the commit).  Print Assumptions glue_seg_R4: lib/A/ACtlG/L3W01Audit.v.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
(* route (C): the cut's runtime conjunct, its producer from AR, the symbol record it takes *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisWin A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.rng_asan A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_memset_c A.Prog.asan_memsetF_on A.Prog.memset.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.sh_word_on A.Prog.Seg.R4 A.Prog.Seg.R4F_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* The twin-safe module names (fully qualified). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module AMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset_c.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module SR4 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R4.
Module SR4FO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R4F_on.

(* The core's segment list, as ACtlCut.v:76 and ACtl.v bind it; ctrl's runs' list (= segs by reflexivity,
   ProgBridge.tfibsegs_rsegs). *)
Local Notation segs := A.AB1v.tfibsegs.
Local Notation rsegs := A.Img0.rsegs.

(* ---------------------------------------------------------------------------------------------------------
   A local fact (proof-internal, no world vocabulary): a spill whose base register 9 holds A reads its word at
   A + off. *)
Lemma r4g_spill_q64 : forall (regs : bvmap 5 word) (m : word -> option byte) (off v A : Z),
  A.ACtlCutP.spill regs m off v -> A.ACtlCut.rgv regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  A.ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A1 & HA1 & Hq) HA H0 Hoff Hhi.
  assert (EA : A1 = A).
  { unfold A.ACtlCut.rgv in HA1, HA. rewrite HA in HA1.
    pose proof Hq as (Hq0 & Hq1 & _). rewrite LMem.length_le8 in Hq1.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hq1.
    apply (f_equal bv_unsigned) in HA1. rewrite !Z_to_bv_unsigned in HA1. unfold bv_wrap in HA1.
    change (bv_modulus 64) with (2 ^ 64) in HA1. Z.div_mod_to_equations. lia. }
  subst A1. exact Hq.
Qed.

Section GlueR4.

(* ACtl.v's Section shape (ACtl.v:170-176), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:219-220, :233-234), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81578 := (ACtlCutP.C_A81578 B).
Local Notation C_A81588 := (ACtlCutP.C_A81588 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* ACtl.v's Section hypotheses this stage reads, same names and texts: the read-only span is image bytes
   (RELRO_IMG, for the exit's arodata_okS), the core's AR laws (LAWS) and symbol record (TFIB_SYMS, for
   ctl_rt_C_of_AR). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* The owned class-6 frame lies above the image: a Theorem Labs lane's proved ProgWorld_Fs.ctl_frame_above_img at class 6. *)
Lemma r4g_frame6_above_img : forall ly S (W : Reusable.YA0n.world segs) mem md pos,
  Reusable.YG0n.AR segs B ly S W mem md -> In (6, pos) (Reusable.YG01.frames S) ->
  A.Prog.ImgBounds.IMG_HI <= Reusable.YG0f.frame_addr ly 6 pos.
Proof. intros ly S W mem md pos HAR Hin. exact (A.ProgWorld_Fs.ctl_frame_above_img B ly S W mem md 6 pos HAR Hin). Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_R4 : forall POST, CF POST C_A81588 -> CF POST C_A81578.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 Hbase HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A81578 (ACtlCutP.v:1230-1248), 29 conjuncts. *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81578] in Hbody.
  destruct Hbody as (HP & HFRAC & Hcn & HCUR & HOUR & HID & S48 & HAD544 & HAD2176 & HAD2256 & S128 & HPRO &
    R21 & S152 & S144 & S192 & RW38 & RW72 & S280 & S240 & RW1 & RW32 & S56 & S88 & S80 & S72 & S200 & S216 & R18).
  pose proof HFRAC as (A & sp & R2 & Hs16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hf32 & HA32 & HAS & HspA & HfrA &
    HA416 & HSlo & HSapp & _).
  destruct Hrt as (HAC & Hcut & _ & HRO).
  (* G2: the numbers *)
  assert (HK : AMC.ASAN_MEMSET_K = 2208) by reflexivity.
  assert (HFB : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (HSTKv : A.ACfn.LLVMF_STK = 32768) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (@CM05.alloc_ceiling_value rc) as [[Hceil0 Hceil1] _].
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HSapp.
  (* the journal: AR, the layout, the stack window's presence and bounds *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hastk as (_ & _ & Hstklo & Hstk0 & Hstkhi & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ely_lo & Ely_hi & _).
  (* the owned frame: its address, bounds, placement, presence *)
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efr6 & Hfr4096 & Hfr32 & Hfrceil & Hceilsp).
  rewrite HFB in Hfrceil. rewrite HSTKv in Hceilsp, Hstk0, Hpres.
  pose proof (r4g_frame6_above_img ly3 S3 W3 mem3 md3 (ACtlCut.c_fpos cx) HAR Hin6) as HGT0.
  pose proof HGT0 as HGT. rewrite Efr6 in HGT. unfold A.Prog.ImgBounds.IMG_HI in HGT.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Happfr).
  rewrite Efr6, HFB in Happfr.
  assert (Happ_fr : forall x, fr <= x < fr + 4096 -> A.AsanRT.app_mem x).
  { intros x Hx. unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
      Reusable.YG0f.ASAN_CEIL in Happfr.
    unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfpres & _).
  rewrite Efr6, HFB in Hfpres.
  (* the input block: below alloc_ceiling, apart from the frame (KitMem K3) *)
  destruct (A.ACtlG.KitMem.kitmem_input_apart B MT XM_LIB RLO RHI cx [] ly3 S3 W3 mem3 md3 k LAWS Hbase HJ HF HP
              HGT0) as (Hlenin & Hp0 & Hpceil & Hpfr & _).
  rewrite Efr6, HFB in Hpfr.
  (* the write set of the run and what lies outside it *)
  set (lo := ACtlCut.c_sp cx - A.ACfn.LLVMF_STK).
  assert (Hlo : lo = ACtlCut.c_sp cx - 32768) by (unfold lo; rewrite HSTKv; reflexivity).
  assert (HHM : A.AsanRT.HIGHMEM_BEG <= lo) by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  set (WR := [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)]).
  assert (Hout : forall x, ~ (fr + 2256 <= x < fr + 2256 + 72) -> ~ (sp - 2208 <= x < sp) ->
            LFrame.outside WR x).
  { intros x H1 H2. cbn [LFrame.outside WR]. split; [exact H1 | split; [exact H2 | exact I]]. }
  assert (Hnapp_out : forall x, ~ A.AsanRT.app_mem x -> LFrame.outside WR x).
  { intros x Hx. apply Hout.
    - intros Hin. exact (Hx (Happ_fr x ltac:(lia))).
    - intros Hin. apply Hx. unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in *. right. lia. }
  assert (Hsh_out : forall x, A.AsanRT.in_shadow x -> LFrame.outside WR x).
  { intros x Hx. apply Hnapp_out. intros Ha. exact (A.AsanRTFacts.app_not_shadow x Ha Hx). }
  assert (HAout : forall x, A <= x < A + 416 -> LFrame.outside WR x) by (intros x Hx; apply Hout; lia).
  assert (Hspout : forall x, sp <= x -> LFrame.outside WR x) by (intros x Hx; apply Hout; lia).
  (* G2: the run's memory premises *)
  pose proof (r4g_spill_q64 regs3 mem3 48 (fr + 2256) A S48 R9 ltac:(lia) ltac:(lia) ltac:(lia)) as Hq48.
  assert (Hst48 : LFrame.stk rsegs mem3 (A + 48) (A + 56))
    by exact (A.ACtlG.KitMem.kitmem_stk_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A + 48) (A + 56) HJ
               ltac:(lia) ltac:(lia)).
  assert (RW48 : LStep.rw_cells rsegs mem3 (A + 48) [LCells.C8 (Z_to_bv 64 (fr + 2256))]).
  { split; [split|].
    - cbn [LCells.cells_wf LCells.cell_wf]. split; exact I.
    - cbn [LCells.cells_bytes LCells.cbytes]. rewrite app_nil_r. exact Hq48.
    - cbn [LCells.cells_size LCells.csize Nat.add].
      replace (Z.of_nat 8) with (A + 56 - (A + 48)) by lia. exact (SR4.r4_wr_stk mem3 _ _ Hst48). }
  assert (Hstk_D : LFrame.stk rsegs mem3 (fr + 2256) (fr + 2256 + 72)).
  { apply (A.ACtlG.KitMem.kitmem_stk_of_present (Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha. exact (proj1 (Hfpres a ltac:(lia))). }
  destruct (LFrame.stk_bytes rsegs mem3 _ _ Hstk_D ltac:(lia)) as (junk & Hjl & Hjb).
  assert (RWd : LStep.rw_cells rsegs mem3 (fr + 2256) [LCells.CB 72 junk]).
  { replace 72%nat with (length junk) by lia. apply SR4.r4_rw_CB; [exact Hjb|].
    replace (Z.of_nat (length junk)) with (fr + 2256 + 72 - (fr + 2256)) by lia.
    exact (SR4.r4_wr_stk mem3 _ _ Hstk_D). }
  assert (HE : A.AsanRT.end_in_app (fr + 2256) 72) by (right; apply Happ_fr; lia).
  assert (HA7 : A.AsanRT.app_mem (fr + 2256 + 7)) by (apply Happ_fr; lia).
  assert (HRTd : fr + 2256 + 72 <= A.AsanRT.RT_LO \/ A.AsanRT.RT_HI <= fr + 2256)
    by (right; unfold A.AsanRT.RT_HI; lia).
  assert (HSEPd : fr + 2256 + 72 <= sp - 2208 \/ sp <= fr + 2256) by (left; lia).
  assert (ST : LFrame.stk rsegs mem3 lo sp)
    by exact (A.ACtlG.KitMem.kitmem_stk_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo sp HJ
               ltac:(unfold lo; lia) ltac:(lia)).
  (* the footprint RNG_W (w_H W3) and its ranges *)
  set (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (Rld : LExecF.rng RNG (A + 48) 8).
  { apply A.ProgBridge.rng_of_visible.
    exact (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A + 48) 8 HJ ltac:(lia) ltac:(lia)). }
  assert (Rimg : LExecF.rng RNG A.Prog.ImgBounds.IMG_LO (A.Prog.ImgBounds.IMG_HI - A.Prog.ImgBounds.IMG_LO))
    by exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3)).
  assert (Rstk : LExecF.rng RNG (sp - AMC.ASAN_MEMSET_K) AMC.ASAN_MEMSET_K).
  { apply A.ProgBridge.rng_of_visible.
    exact (A.ProgWorldVisWin.win_vis B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sp - AMC.ASAN_MEMSET_K) AMC.ASAN_MEMSET_K
             HJ ltac:(lia) ltac:(lia)). }
  pose proof (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 2256) 72
                HAR Hin6) as Hfv.
  rewrite Efr6, HFB in Hfv. destruct (Hfv ltac:(lia) ltac:(lia)) as (Hfv1 & Hfv2).
  assert (RngD : LExecF.rng RNG (fr + 2256) 72) by exact (A.ProgBridge.rng_of_visible _ _ _ Hfv1).
  assert (RngDs : A.Prog.rng_asan.sh_word_rng RNG (fr + 2256) 72).
  { destruct (Hfv2 ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia)) as [E0 | HV];
      [left; exact E0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ HV)]. }
  assert (RngKs : A.Prog.rng_asan.sh_word_rng RNG (sp - AMC.ASAN_MEMSET_K) AMC.ASAN_MEMSET_K).
  { destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3 (sp - AMC.ASAN_MEMSET_K) AMC.ASAN_MEMSET_K
                HAR ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | HV];
      [left; exact E0 | right; exact (A.ProgBridge.rng_of_visible _ _ _ HV)]. }
  (* route (C): the run's shadow premise.  The destination D = fr + 2256's aligned shadow-word span
     [sh_al8_lo D, sh_al8_hi D 72) lies inside the owned frame's shadow [shadow_addr fr, shadow_addr fr + 512), which
     is cut_shadow's (F) disjunct at (6, c_fpos cx); ctl_rt_C's cut_shadow conjunct gives it. *)
  assert (HSWr : A.ShadowRwOn.shadow_rw_on (SR4FO.r4_evt_shadow_R (fr + 2256)) mem3).
  { apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3)); [| exact Hcut].
    intros a Ha. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite Efr6, HFB. change (4096 / 8) with 512.
    unfold SR4FO.r4_evt_shadow_R, A.Prog.sh_word_on.sh_word_on, A.Prog.rng_asan.sh_al8_lo,
      A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
    clear - Ha Hf32. Z.div_mod_to_equations. lia. }
  (* the run in route (C) form (Seg/R4F_on.v), its memset premise discharged by a Theorem Labs lane's proof (no split); its
     shadow premise is the destination's shadow-word span, inside the owned frame's shadow (HSWr) *)
  pose proof (SR4FO.r4_evt_F_on (A.Prog.asan_memsetF_on.asan_memset_holds_F_on A.Prog.memset.memset_holds) RNG
    (CK11.getr regs3 1) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4) (CK11.getr regs3 5)
    (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8) (CK11.getr regs3 9) (CK11.getr regs3 10)
    (CK11.getr regs3 11) (CK11.getr regs3 12) (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15)
    (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20)
    (CK11.getr regs3 21) (CK11.getr regs3 22) (CK11.getr regs3 23) (CK11.getr regs3 24) (CK11.getr regs3 25)
    (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30)
    (CK11.getr regs3 31)
    CK11.fp_regs CK11.fp_csr mem3 sp A (fr + 2256) lo junk
    R2 R9 ltac:(lia) ltac:(lia) ltac:(lia) RW48 RWd HAD2256 HE HA7 HRTd HSEPd ltac:(lia) ltac:(unfold lo; lia)
    ST ltac:(unfold lo; lia) HHM ltac:(unfold A.AsanRT.APPMEM_END; lia)
    HAC HSWr HRO Rld (A.ProgBridge.rng_bytes_RNG_W _) Rimg Rstk RngD RngDs RngKs) as HRUN.
  match type of HRUN with LExecF.evtF _ _ _ ?s => set (ms0 := s) in HRUN end.
  destruct (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as (ms1 & Hrun & HQ).
  rewrite <- A.ProgBridge.tfibsegs_rsegs in Hrun.
  assert (Hfp : Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W3) RNG) by exact (A.ProgBridge.fp_avoids_RNG_W _).
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81578) with 0x81578.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81578) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  (* G4: the lift (YA0nR.SRr_fsteps keeps the run for ajournal_of_fsteps). *)
  change (Reusable.YA0n.SRr segs W3 (mkCfg ms0 md3) (POST cx)).
  apply (Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 ms0 ms1 md3 RNG (POST cx) Hrun Hfp).
  intros md' Hsbm.
  (* G5: the continuation at the run's end state *)
  destruct HQ as (R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K22 & K25 & K26 & K18 & K21 &
    MU & WM & RO' & ST' & AC' & SW' & RW').
  assert (E2 : CK11.getr R 2 = CK11.getr regs3 2) by exact K2.
  assert (E3 : CK11.getr R 3 = CK11.getr regs3 3) by exact K3.
  assert (E4 : CK11.getr R 4 = CK11.getr regs3 4) by exact K4.
  assert (E8 : CK11.getr R 8 = CK11.getr regs3 8) by exact K8.
  assert (E9 : CK11.getr R 9 = CK11.getr regs3 9) by exact K9.
  assert (E18 : CK11.getr R 18 = CK11.getr regs3 18) by exact K18.
  assert (E19 : CK11.getr R 19 = CK11.getr regs3 19) by exact K19.
  assert (E21 : CK11.getr R 21 = CK11.getr regs3 21) by exact K21.
  assert (E22 : CK11.getr R 22 = CK11.getr regs3 22) by exact K22.
  assert (E25 : CK11.getr R 25 = CK11.getr regs3 25) by exact K25.
  assert (E26 : CK11.getr R 26 = CK11.getr regs3 26) by exact K26.
  assert (MU0 : LFrame.munch WR mem3 m') by exact MU.
  (* the journal across the run (ProgWorld.ajournal_of_fsteps) *)
  assert (Hawr : forall a, 0 <= a < 2 ^ 64 -> ~ LFrame.outside WR a ->
            Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
              (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3)
              ly3 (ACtlCut.own6 cx) a).
  { intros a Ha Hno. destruct (SR4.r4_not_out _ _ _ _ a Hno) as [Hx | Hx].
    - apply (A.ACtlG.KitMem.kitmem_awr_frame _ _ _ _ _ _ _ 6 (ACtlCut.c_fpos cx) fr a (eq_sym Efr6));
        [left; reflexivity | left; rewrite HFB; lia].
    - apply A.ACtlG.KitMem.kitmem_awr_win. lia. }
  assert (MU1 : LFrame.munch WR (ms_mem ms0) (ms_mem ms1)) by (rewrite Ems; exact MU0).
  pose proof (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx)
    ly3 S3 W3 ms0 ms1 md3 md' k RNG WR HJ Hrun Hfp MU1 Hsbm Hawr) as HJ'.
  rewrite Ems in HJ'. rewrite Ems.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81588) R m' md') (POST cx)).
  (* the keep facts *)
  assert (KSP : forall off v, 0 <= off -> off + 8 <= 416 -> ACtlCutP.spill regs3 mem3 off v ->
            ACtlCutP.spill R m' off v).
  { intros off v Ho1 Ho2 Hs.
    exact (A.ACtlG.KitMem.kitmem_spill_munch WR regs3 R mem3 m' off v A Hs R9 ltac:(lia) Ho1 ltac:(lia) MU0 E9
             (fun x Hx => HAout x ltac:(lia))). }
  assert (KFR : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
            (a + Z.of_nat (length bs) <= fr + 2256 \/ fr + 2328 <= a) ->
            LMem.bytes_at segs mem3 a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs H1 H2 H3 Hb.
    exact (A.ACtlG.KitMem.kitmem_bytes_munch WR mem3 m' a bs Hb MU0 (fun x Hx => Hout x ltac:(lia) ltac:(lia))). }
  assert (KAD : forall p n, A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable m' p n)
    by (intros p n Hadr; exact (A.ACtlG.KitMem.kitmem_addr_munch WR mem3 m' p n Hadr MU0 Hsh_out)).
  assert (KRW : forall a n bs, fr <= a -> a + Z.of_nat n <= fr + 4096 ->
            (a + Z.of_nat n <= fr + 2256 \/ fr + 2328 <= a) ->
            LStep.rw_cells segs mem3 a [LCells.CB n bs] -> LStep.rw_cells segs m' a [LCells.CB n bs]).
  { intros a n bs H1 H2 H3 Hc. apply (LFrame.rw_cells_transport rsegs WR mem3 m' a _ Hc MU0 WM).
    cbn [LCells.cells_size LCells.csize LFrame.disjoint_from WR]. rewrite Nat.add_0_r.
    split; [lia|]. split; [lia | exact I]. }
  assert (KIN : LMem.bytes_at segs mem3 (ACtlCut.c_p cx) (ACtlCut.c_in cx) ->
            LMem.bytes_at segs m' (ACtlCut.c_p cx) (ACtlCut.c_in cx)).
  { intros Hb. apply (A.ACtlG.KitMem.kitmem_bytes_munch WR mem3 m' _ _ Hb MU0).
    intros x Hx. rewrite Hlenin in Hx. apply Hout; lia. }
  apply (HX cx idx fr k ly3 S3 W3 R m' md' Hbase).
  - (* journal *)
    exact HJ'.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: kmax 0 on both cuts *)
    exact Hk.
  - (* the exit body, C_A81588 (ACtlCutP.v:1252-1271), 30 conjuncts *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81588].
    split; [exact HP|].
    split.
    { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R m'); [| exact E2 | exact E3 | exact E4 | exact E8 |
        exact E9 | exact E19 | exact E26].
      apply (A.ACtlG.KitMem.kitmem_frac_munch B cx fr fr regs3 mem3 m' WR HFRAC MU0).
      - intros x Hx. apply Hspout. rewrite HspZ in Hx. exact Hx.
      - intros x Hx. apply Hout; lia.
      - intros x Hx. apply Hnapp_out.
        unfold ACtlCutP.Sfr, ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES, A.AsanRT.shadow_addr,
          A.AsanRT.ASAN_K in Hx.
        unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
        Z.div_mod_to_equations. lia. }
    split; [exact Hcn|].
    split.
    { destruct HCUR as (Hc0 & Hc22 & Hc25). split; [exact Hc0|].
      split; [unfold ACtlCut.rgv in *; rewrite E22; exact Hc22 | unfold ACtlCut.rgv in *; rewrite E25; exact Hc25]. }
    split; [unfold ACtlCutP.OURb in *; apply KFR; [lia | rewrite SM.OUR_length; lia | right; lia | exact HOUR]|].
    split; [unfold ACtlCutP.OUTA; exact (KAD _ _ HAD544)|].
    split.
    { unfold ACtlCutP.IDBr in *. apply KFR; [lia | | | exact HID];
        change (SM.RID (ACtlCut.c_in cx) 0) with (repeat (Z_to_bv 8 0) 38); rewrite repeat_length; lia. }
    split.
    { unfold ACtlCutP.FGBr. change (SM.RFG (ACtlCut.c_in cx) 0) with (repeat (Z_to_bv 8 0) 72).
      destruct RW' as ((_ & Hbq) & _). cbn [LCells.cells_bytes LCells.cbytes] in Hbq. rewrite app_nil_r in Hbq.
      exact Hbq. }
    split; [exact (KSP 128 _ ltac:(lia) ltac:(lia) S128)|].
    split.
    { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & PA6 & PIN & PINB &
        P184 & P256 & P264 & P272 & P32).
      split; [exact (KSP 40 _ ltac:(lia) ltac:(lia) P40)|].
      split; [exact (KSP 120 _ ltac:(lia) ltac:(lia) P120)|].
      split; [exact (KSP 136 _ ltac:(lia) ltac:(lia) P136)|].
      split; [exact (KSP 160 _ ltac:(lia) ltac:(lia) P160)|].
      split; [exact (KSP 168 _ ltac:(lia) ltac:(lia) P168)|].
      split; [exact (KSP 176 _ ltac:(lia) ltac:(lia) P176)|].
      split; [exact (KSP 208 _ ltac:(lia) ltac:(lia) P208)|].
      split; [exact (KSP 248 _ ltac:(lia) ltac:(lia) P248)|].
      split; [exact (KAD _ _ PA6)|].
      split; [exact (KIN PIN)|].
      split; [intros Hn0; exact (KAD _ _ (PINB Hn0))|].
      split; [exact (KSP 184 _ ltac:(lia) ltac:(lia) P184)|].
      split; [exact (KSP 256 _ ltac:(lia) ltac:(lia) P256)|].
      split; [exact (KSP 264 _ ltac:(lia) ltac:(lia) P264)|].
      split; [exact (KSP 272 _ ltac:(lia) ltac:(lia) P272)|].
      exact (KSP 32 _ ltac:(lia) ltac:(lia) P32). }
    split; [unfold ACtlCut.rgv; rewrite E21; exact R21|].
    split; [exact (KSP 152 _ ltac:(lia) ltac:(lia) S152)|].
    split; [exact (KSP 144 _ ltac:(lia) ltac:(lia) S144)|].
    split; [exact (KSP 192 _ ltac:(lia) ltac:(lia) S192)|].
    split; [destruct RW38 as (idb & Hc); exists idb; apply KRW; [lia | lia | right; lia | exact Hc]|].
    split; [destruct RW72 as (jk & Hc); exists jk; apply KRW; [lia | lia | right; lia | exact Hc]|].
    split; [exact (KSP 280 _ ltac:(lia) ltac:(lia) S280)|].
    split; [exact (KSP 240 _ ltac:(lia) ltac:(lia) S240)|].
    split; [destruct RW1 as (jy & Hc); exists jy; apply KRW; [lia | lia | right; lia | exact Hc]|].
    split; [destruct RW32 as (jk & Hc); exists jk; apply KRW; [lia | lia | right; lia | exact Hc]|].
    split; [exact (KSP 48 _ ltac:(lia) ltac:(lia) S48)|].
    split; [exact (KSP 56 _ ltac:(lia) ltac:(lia) S56)|].
    split; [exact (KSP 88 _ ltac:(lia) ltac:(lia) S88)|].
    split; [exact (KSP 80 _ ltac:(lia) ltac:(lia) S80)|].
    split; [exact (KSP 72 _ ltac:(lia) ltac:(lia) S72)|].
    split; [exact (KSP 200 _ ltac:(lia) ltac:(lia) S200)|].
    split; [exact (KSP 216 _ ltac:(lia) ltac:(lia) S216)|].
    split; [exact (KAD _ _ HAD2256)|].
    split; [exact (KAD _ _ HAD2176)|].
    unfold ACtlCut.rgv; rewrite E18; exact R18.
  - (* ctl_rt_C at the exit (same ly3 S3, memory m'): ctl_rt_C_of_AR at the exit journal's AR, with the entry's
       arodata_okS carried along the journal (KitMem.kitmem_arodataS_journal) *)
    pose proof Hbase as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _) & _).
    pose proof HJ' as (HAR' & _).
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 m' md' HAR'
             (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _
                (A.ACtlG.KitMem.kitmem_arodataS_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ' HROS)
                (Z.le_refl _) (Z.le_refl _))).
Qed.

End GlueR4.
