(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4b.v, with its module paths and module names changed; 782 of its 845 lines of code are new or changed and 4089 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F12.v, with its module paths and module names changed; 495 of its 520 lines of code are new or changed and 820 lines of the source are left out. *)
(* lib/A/ACtlG/F6_e28.v -- GLUE for stage seg_F6_e28 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:759).  Written by a Theorem Labs lane; single writer of this file.
   rule 24: no function proved (kind: segment lemma of a walk).

   WHAT IT PROVES
     glue_seg_F6_e28 : forall POST (j : nat),
       CF POST (ix_cut C_A81f54_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ec0_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. ACtl.v:576's Hypothesis
   seg_F6_e28 character for character.  ACtl.v:575's "glue:" comment names Seg/F6.v seg_F6_e28 :2727, runs
   f6_loop :398 and f6_e28_evt :483; the whole segment 0x81ec0 -> 0x81f54 is ONE footprint run,
   lib/A/Prog/Seg/F6F.v:234-385 f6_e28_evt_F (PROVED there), which contains the loop.  No callee, no split.

   THE ONE WRITE.  f6_e28_evt_F reads the 50-byte record block at phi, its byte-exact shadow span and the
   spill cell [A+240, A+248), and writes EXACTLY ONE 8-byte cell: its post memory is
     write_to_mem m (wa (A + 280)) (le8 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 1 else 0)))
   (F6F.v:252).  So the stage carries the exit cut's whole body, the journal and ctl_rt_C ACROSS that write, with
   the write set WR := [(A + 280, A + 288)] (a Lib.Frame.munch WR, by Lib.Frame.munch_write).

   ROUTE (C) (a working branch shell 1502cba0417): the cut carries A.ACtlRtC.ctl_rt_C B ly3 S3
   mem3 in place of ctl_rt mem3.  This stage reads no shadow byte through it; it CARRIES it to the exit cut at the
   same ly3 S3: asan cells and read-only bytes by KitMem.kitmem_asan_cells_img / kitmem_ro_agree_img, both
   shadow_rw_on regions (cut_shadow B ly3 S3 and img_shadow) by the local e28_srw_on_munch (the write set misses
   every shadow byte).  No VIS0 / OWNED_RO was ever a hypothesis here.

   THE PROOF, step by step
   G1  unfold the entry cut C_A81ec0_at (ACtlCutP.v:2078-2090) through ix_cut and b5_body; the loop index stays
       folded as `ACtlCutP.ixn 0 [Z.of_nat j]` (named jn; the exit cut reads the same term).  FRAC is read by
       position from the FRONT only and kept whole (its coming trailer conjunct is carried by shape, G6).
   G2  the run's premises from the body and from VISIBLE state only:
       - the frame: A.ACtlG.KitMem.kitmem_own6 (4096 <= fr, fr + 4096 <= alloc_ceiling <= c_sp cx - LLVMF_STK);
       - the record block: b5_PH's bytes (50 <= flen) and HB's addressable, cut to 50 by addressable_sub;
         0 <= phi, phi + 50 <= 2 ^ 64 from that addressable;
       - 0 <= A, A + 288 <= 2 ^ 64 from FRAC (sp <= A, A + 416 <= c_sp cx < APPMEM_END);
       - stk over [A+240, A+288) from the JOURNAL (KitMem.kitmem_stk_of_journal) -- ctrl's FRA stk conjunct is
         the one ACtlCutP.v:968 drops as RESTATED;
       - the kind bound 0 <= t_k < 2 ^ 64 from Prog.RcParse.ctrlparse_kind_range;
       - the [A+240] flag cell and its value from b5_sp 240 and Seg/F6.v f6_8819_eq;
       - the four footprint ranges at RNG := A.ProgBridge.RNG_W (w_H W3): KitMem.kitmem_rng_heap and
         kitmem_rng_heap_sh_span on the live block (phi, flen) of the body's Permutation, KitMem.kitmem_rng_win
         for [A+240, A+248) and [A+280, A+288) in the journal's stack window.
       No `_of_F_bounded` corollary exists for f6_e28_evt (segment-F-premises-A.tsv rows 538-541 (a working note, not in this delivery); a Theorem Labs lane
       04:4xZ), so the bounded-corollary rule asks nothing more of this stage.
   G3  the cut's configuration in the run's state form (ProgBridge.cfg_at_MS, eq_refl); the walk is moved from
       the cut's map regs3 to the canonical mkR_of regs3 by Reusable.YA0nR.SRr_xregs_eqv; mkR_of is expanded
       (e28_mkR_expand, reflexivity) and the NINE pinned slots 9 10 11 12 13 18 23 24 26 rewritten to the run's
       start map; every other slot is the run's free binder, instantiated with `getr regs3 r`.
   G4  the lift: KitMem.kitmem_lift (= ProgBridge.fevt_of_evtF + YA0nR.SRr_fsteps) at RNG_W (w_H W3), fp_avoids
       by ProgBridge.fp_avoids_RNG_W; its continuation hands over the fsteps run itself.
   G5  the journal across the write: A.ProgWorld.ajournal_of_fsteps (ProgWorld.v:1079, PROVED) with WR, the
       run's fsteps, same_but_materialized from the lift, and awr_byte's stack-window case (KitMem.kitmem_awr_win:
       by FRAC, A + 288 <= c_sp cx - 128 and c_sp cx - 4096 < sp <= A).  mem_grows of the run:
       A.ProgWorld.pws_fsteps_mem.
   G6  the exit body C_A81f54_at (ACtlCutP.v:2095-2104), rebuilt conjunct by conjunct over KitMem's munch lemmas
       (kitmem_frac_keep -- by SHAPE, so it also carries FRAC's announced trailer q64 (fr + 4088) --,
       kitmem_spill_munch, kitmem_q64_munch, kitmem_bytes_munch, kitmem_addr_munch; ctl_rt_C as above) plus
       lib/Lib's Frame.stk_write for FLSH's frame window; the written cell [A+280] by Lib.Mem.bytes_at_write_same;
       b5_K's three model equations by Seg/F6.v f6_sum / f6_tfill / f6_reply; registers from the run's end map.

   LEMMAS OF THIS FILE THAT RE-ESTABLISH FRAC (for the gate's Batch3 re-check): only glue_seg_F6_e28 itself, at its
   exit body, through A.ACtlG.Kit.kit_frac_move (registers) and A.ACtlG.KitMem.kitmem_frac_keep (memory, by shape;
   its frame premise already covers [fr + 4088, fr + 4096), discharged here from fr + 4096 + 32768 <= c_sp cx).

   MEASURED FINDING (reported to a Theorem Labs lane, 05:0xZ): ACtlCutP's bundles are NOT convertible with SlotInv's at a
   ghost g_in := c_in cx: ACtlCutP.PRO (:549-558) and f1_IN (:741-742) drop SlotInv's `In (g_p g, g_n g) (g_H g)`
   (SlotInv.v:811, :1826) and read the field c_n where SlotInv reads g_n g = nlen (g_in g) (SlotInv.v:122); so
   Seg/F6.v's bundle keep f6_keep (:2176, which also takes FRA, a frame-route predicate) cannot be applied.  The
   leaves ARE convertible, so the body is rebuilt leaf by leaf over KitMem's lemmas; this file states NO keep
   lemma of its own.  The local lemmas are e28_mkR_expand (mkR_of as the explicit map over the CORE's getr) and
   e28_srw_on_munch (route (C), above).

   STAND-IN VALUES (a Theorem Labs lane 05:52Z): none read.  No Tfib_zero_shadow / ts_zsh / am_const / Tfib_const_* /
   Tfib_owned_static / AB01 / port_core_refused literal; the shadow facts come from AR_shadow_law
   (ProgWorldVisHeap.heap_sh_vis via kitmem_rng_heap_sh_span) or are CARRIED unchanged across the write.

   SECTION HYPOTHESES: one, ACtl.v's own LAWS : Reusable.YG0d.AR_laws segs B (ACtl.v:183; YCbq Section a0's
   hypothesis that ajournal_of_fsteps, kitmem_own6 and the kitmem_rng_heap* lemmas take).  The `_F` run is NOT a
   hypothesis: f6_e28_evt_F is Required from lib/A/Prog/Seg/F6F.v (closure rule 1, qualified, never Imported).

   SHADOWED / AMBIGUOUS NAMES.  The six twin modules (lib/Reusable/<X> and lib/A/Reusable/<X>: YI04 YI16 YK11
   YK1b YM05 YO09) and the lib/Lib modules that have lib/A/Bz/Lib twins (Mem MState Frame Regs6ss ExecF) are
   loaded by ABSOLUTE Require lines and named through absolute module aliases (QYK11 QYM05 QYO09 QLMEM QLMS QLFRM
   QLREG); getr / mkst / seg_rom / cfg_at are QYK11.* / Reusable.YG0d.* only.

   CLOSURE: every Require below is qualified (no Import / Export of a project module); the `_F` file
   lib/A/Prog/Seg/F6F.v and its closure (which reaches the frame route) are allowed by glue closure rule 1; no
   STATEMENT of this file names a frame-route identifier.  Measured (Require scan from this file, worktree HEAD
   c5d58e80468): 403 files; no lib/AZ/AsanW, no W6, no SegCF / *_cfw / Cf* file; the lib/AZ files are
   LibA/AcctCore.v 0e06d81d553 (via lib/Lib/ExecF) and Spec/AsanCtrl.v 80ffbfc0a07, Spec/AsanCtrlProps.v
   b4f333a2672, Spec/STree.v 1293d54ecd2.  Frame-route files and their blobs (all the v1.9 blobs of record):
     lib/A/Prog/SlotInv.v 4cf85db229a   lib/A/Prog/Seg/Tac_slot.v de02ff45188   lib/A/Prog/SlotModel.v 04dc7903221
     lib/A/AsanRT.v b67d26f8ec7 (mcs 30)  lib/A/AsanRTInv.v 2a8602e8526     lib/A/AsanRTFacts.v 1657e654e8c
     lib/A/Contract.v fa6fd478d9a      lib/A/FrameAPI.v f6ffefa9bb4         lib/A/MemNorm.v cb518fc0304
     lib/A/MemNormF.v 9e5ea0ff243      lib/A/PContract.v a0c4b1b2aa5        lib/A/AsanLift.v e92b008d733
     lib/A/KindBGlue.v 35e845dad50     lib/A/Prog/RcAsanRT.v 706993599b7    lib/A/Prog/Seg/Tac_fs.v 8bd492a660d
     lib/A/Prog/Seg/Tac_fsfree.v d76d2012bf8   lib/A/Prog/Seg/Tac_b5.v 4a9ebd96689
     lib/A/Prog/Seg/F6.v 5a9c598d249 (F6F's own provenance line)   lib/A/Prog/Seg/F6F.v 61c2fb6fc48

   ROUTE (C) BUILD STATE: type-check rc=0 on a working branch shell 1899bed1aee (cb build, a build machine, log
   of 2026-10-29T13:05:56Z); build of record: a Theorem Labs lane's cbrec record
   over an audit file not in this delivery.  The paragraph below is the pre-route-(C) state.
   BUILD STATE: TYPE-CHECKS (TYPES ONLY, values do not count): rc=0, wb4b.sh on a build machine, logs
   of the 2026-10-29T07:31:05Z build (F6_e28.vo 11.06 s) and
   build-20261029T073248Z.log (12.22 s, with the Print Assumptions below), with the build workspace's
   port_core_refused_<hex> -> literal substitution (workspace only, never committed); this file's closure does
   not reach lib/A/AD2l.v, so no AD2l stand-in was used.  Print Assumptions glue_seg_F6_e28: the Rocq primitives
   (PrimInt63.*, PrimString.*, PrimArray.array) and FunctionalExtensionality.functional_extensionality_dep (the
   lift's, via YK04R.fsteps_restrict), nothing else.  No Axiom, no Parameter, no Admitted, no admit, no Abort. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG0f Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG0n Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
(* route (C): the cut's narrowed runtime conjunct A.ACtlRtC.ctl_rt_C and its region form A.ShadowRwOn.shadow_rw_on *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.Prog.ImgBounds.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F6.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F6F.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* Absolute module aliases: the twin modules this file names. *)
Module QYK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module QYM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module QYO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module QLMEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module QLFRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module QLMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module QLREG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module QSM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module QF6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F6.
Module QF6F := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F6F.
Module QRP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module QRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcModel.
Module QKM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.KitMem.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* mkR_of is the explicit 31-slot map (Seg/F6.v f6_mkR_expand's statement, here over the CORE's YK11.getr, which
   the cut's rgv facts are stated with). *)
Lemma e28_mkR_expand : forall regs : bvmap 5 word,
  QLREG.mkR_of regs =
  QLFRM.mkR (QYK11.getr regs 1) (QYK11.getr regs 2) (QYK11.getr regs 3) (QYK11.getr regs 4)
    (QYK11.getr regs 5) (QYK11.getr regs 6) (QYK11.getr regs 7) (QYK11.getr regs 8)
    (QYK11.getr regs 9) (QYK11.getr regs 10) (QYK11.getr regs 11) (QYK11.getr regs 12)
    (QYK11.getr regs 13) (QYK11.getr regs 14) (QYK11.getr regs 15) (QYK11.getr regs 16)
    (QYK11.getr regs 17) (QYK11.getr regs 18) (QYK11.getr regs 19) (QYK11.getr regs 20)
    (QYK11.getr regs 21) (QYK11.getr regs 22) (QYK11.getr regs 23) (QYK11.getr regs 24)
    (QYK11.getr regs 25) (QYK11.getr regs 26) (QYK11.getr regs 27) (QYK11.getr regs 28)
    (QYK11.getr regs 29) (QYK11.getr regs 30) (QYK11.getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Route (C): a munch whose write set misses every shadow byte keeps shadow_rw_on of any region (the shadow part of
   KitMem.kitmem_ctlrt_munch, stated for A.ShadowRwOn.shadow_rw_on). *)
Lemma e28_srw_on_munch : forall (P : Z -> Prop) (WR : list QLFRM.ivl) (m m' : word -> option byte),
  A.ShadowRwOn.shadow_rw_on P m -> QLFRM.munch WR m m' ->
  (forall x, A.AsanRT.in_shadow x -> QLFRM.outside WR x) ->
  A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P WR m m' SR MU HO a Hp Ha. destruct (SR a Hp Ha) as [Hw (b & Hb)].
  destruct (A.AsanRTFacts.in_shadow_range a Ha) as [R1 R2].
  assert (E : m' (QLMEM.wa a) = m (QLMEM.wa a))
    by (apply MU; rewrite QLMEM.wa_unsigned by lia; exact (HO a Ha)).
  split.
  - unfold wview in *. rewrite E. exact Hw.
  - exists b. unfold QLMEM.mrd in *. rewrite E. exact Hb.
Qed.

Section GlueF6e28.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : QYK11.FPState} {rc : QYM05.RunCeil} {LS : QYO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :271-272), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81ec0_at := (ACtlCutP.C_A81ec0_at B).
Local Notation C_A81f54_at := (ACtlCutP.C_A81f54_at B).

(* The core's AR law record (YCbq.v:207; ACtl.v:183's own Hypothesis). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

Lemma glue_seg_F6_e28 : forall POST (j : nat), CF POST (ix_cut C_A81f54_at [Z.of_nat j]) -> CF POST (ix_cut C_A81ec0_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HBASE HJ HF HL Hk Hbody Hrt.
  assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity.
  (* ---- G1: the entry cut at index [Z.of_nat j] ---- *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81ec0_at ACtlCutP.b5_body] in Hb.
  set (jn := ACtlCutP.ixn 0 [Z.of_nat j]) in *.
  destruct Hb as (HFRAC & phi & HPerm & Hn26 & Hj255 & HHB & HFLSI & HLK & HC & HBODY).
  destruct HBODY as (Hlen50 & R10 & R11 & R12 & R13 & R22 & R24 & R25 & HS240 & HU32 & HIDj & HF17 & HW240 & HPF).
  (* FRAC by position from the FRONT only, kept whole (G6 carries it by shape) *)
  pose proof HFRAC as (A & sp & E2 & Hsp16 & Hspz & E4 & R8 & R9 & E3 & R19 & R26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA416 & Hsp4096 & HSapp & _).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold A.AsanRT.APPMEM_END in HSapp.
  (* ---- G2: the numeric frame of the write site, from visible state only ---- *)
  pose proof HJ as (HAR & _).
  assert (Hsp0 : 0 <= sp).
  { rewrite <- Hspz. unfold Reusable.YG0d.spZ.
    pose proof (bv_unsigned_in_range 64 (QYK11.getr regs3 2)) as Hr. lia. }
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  (* the owned class-6 frame and the journal's stack bound (KitMem.kitmem_own6) *)
  destruct (QKM.kitmem_own6 (SK := A.AE2k.tfib_sink_head) B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efr3 & Hfr4096 & _ & Hfceil & Hceilsp).
  assert (E6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite E6 in Hfceil. unfold A.ACfn.LLVMF_STK in Hceilsp.
  pose proof (proj1 Reusable.YCbq.asan_consts) as [Hac0 Hac1].
  assert (Hfrtop : fr + 4096 + 32768 <= ACtlCut.c_sp cx) by lia.
  assert (HwHIGH : A.AsanRT.HIGHMEM_BEG < A + 280) by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  (* the record block is live, so it ends below alloc_ceiling, far below the spill area *)
  assert (Hinblk : In (phi, ACtlCutP.flen cx jn) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  assert (Hreq : Reusable.YG00.req_size (ACtlCutP.flen cx jn) = ACtlCutP.flen cx jn).
  { unfold Reusable.YG00.req_size. rewrite (proj2 (Z.eqb_neq (ACtlCutP.flen cx jn) 0) ltac:(lia)).
    reflexivity. }
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx jn) HAR Hinblk)
    as (_ & Hp4096 & Hpceil & _).
  rewrite Hreq in Hpceil.
  (* the record block's 50 bytes and their addressability *)
  destruct HHB as (Hphi0 & Haddrblk).
  unfold A.ACtlK.a_size in Haddrblk.
  assert (Haddr50 : A.AsanRT.addressable mem3 phi 50).
  { rewrite <- (Z.add_0_r phi).
    apply (A.AsanRTFacts.addressable_sub mem3 phi (Z.max (ACtlCutP.flen cx jn) 1) 0 50 Haddrblk); lia. }
  assert (Hphib : 0 <= phi /\ phi + 50 <= 2 ^ 64).
  { destruct Haddr50 as (Hq0 & _ & Hq1 & _). unfold A.AsanRT.APPMEM_END in Hq1. lia. }
  destruct HC as (R23 & R18 & HCA & HPH & HFR & HKN & HFGj & HFSj).
  pose proof HPH as (HPHb & HPHd).
  pose proof (HPHb Hlen50) as Hbs.
  (* the kind word *)
  assert (Htk : 0 <= QSM.t_k (ACtlCut.c_in cx) jn < 2 ^ 64).
  { pose proof (QRP.ctrlparse_kind_range (QSM.t_len (ACtlCut.c_in cx) jn)
      (QSM.t_g (ACtlCut.c_in cx) jn)) as HR.
    unfold QSM.t_k. lia. }
  (* the [A+240] flag cell *)
  destruct HS240 as (A240 & H9240 & HA240 & Q240).
  assert (EA240 : A240 = A).
  { apply (QF6.f6_id A240 A HA240 HA64). unfold ACtlCut.rgv in H9240, R9.
    rewrite <- H9240, <- R9. reflexivity. }
  subst A240.
  (* the spill window [A+240, A+288) lies in the journal's present stack window *)
  assert (Hstkw : QLFRM.stk A.Img0.rsegs mem3 (A + 240) (A + 288))
    by (apply (QKM.kitmem_stk_of_journal (SK := A.AE2k.tfib_sink_head) B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                 (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                 (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k (A + 240) (A + 288) HJ);
        unfold A.ACfn.LLVMF_STK; lia).
  (* the four footprint ranges at RNG_W (w_H W3) *)
  set (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  pose proof (QKM.kitmem_rng_heap B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx jn) phi 50 HAR Hinblk
                ltac:(lia) ltac:(rewrite Hreq; lia)) as Rbuf.
  pose proof (QKM.kitmem_rng_heap_sh_span B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx jn) phi 50 HAR Hinblk
                ltac:(lia) ltac:(lia) ltac:(rewrite Hreq; lia)) as Rsh.
  replace (phi + 50 - 1) with (phi + 49) in Rsh by lia.
  pose proof (QKM.kitmem_rng_win (SK := A.AE2k.tfib_sink_head) B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k (A + 240) 8 HJ
                ltac:(unfold A.ACfn.LLVMF_STK; lia) ltac:(lia)) as R240.
  pose proof (QKM.kitmem_rng_win (SK := A.AE2k.tfib_sink_head) B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k (A + 280) 8 HJ
                ltac:(unfold A.ACfn.LLVMF_STK; lia) ltac:(lia)) as R280.
  (* ---- G3: the cut's configuration as the run's start state ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81ec0_at [Z.of_nat j])) with 0x81ec0.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (QLREG.mkR_of regs3) regs3 QYK11.fp_regs
           (Z_to_bv 64 0x81ec0) QYK11.fp_csr None mem3 (QYK11.seg_rom segs) md3 (POST cx));
    [| exact (QLREG.xregs_eqv_sym _ _ (QLREG.mkR_of_eqv regs3))].
  rewrite (e28_mkR_expand regs3).
  unfold ACtlCut.rgv in R9, R10, R11, R12, R13, R18, R23, R24, R26.
  rewrite R9, R10, R11, R12, R13, R18, R23, R24, R26.
  (* ---- G4: the run and its lift ---- *)
  assert (He240 : QSM.b2z (QSM.t_8819 (ACtlCut.c_in cx) jn) =
                  (if QSM.t_k (ACtlCut.c_in cx) jn =? 0 then 0 else 1)).
  { rewrite <- (QF6.f6_8819_eq (ACtlCut.c_in cx) jn). rewrite QLMS.unsigned_lit by lia. reflexivity. }
  pose proof (QF6F.f6_e28_evt_F RNG
                (QYK11.getr regs3 1) (QYK11.getr regs3 2) (QYK11.getr regs3 3) (QYK11.getr regs3 4)
                (QYK11.getr regs3 5) (QYK11.getr regs3 6) (QYK11.getr regs3 7) (QYK11.getr regs3 8)
                (QYK11.getr regs3 14) (QYK11.getr regs3 15) (QYK11.getr regs3 16) (QYK11.getr regs3 17)
                (QYK11.getr regs3 19) (QYK11.getr regs3 20) (QYK11.getr regs3 21) (QYK11.getr regs3 22)
                (QYK11.getr regs3 25) (QYK11.getr regs3 27) (QYK11.getr regs3 28) (QYK11.getr regs3 29)
                (QYK11.getr regs3 30) (QYK11.getr regs3 31)
                QYK11.fp_regs QYK11.fp_csr mem3 phi A (ACtlCutP.flen cx jn)
                (QSM.t_k (ACtlCut.c_in cx) jn) (QSM.b2z (QSM.t_8819 (ACtlCut.c_in cx) jn))
                (QSM.t_g (ACtlCut.c_in cx) jn)
                ltac:(lia) ltac:(lia) (QF6.f6_tg_len (ACtlCut.c_in cx) jn) Hbs Haddr50
                ltac:(lia) ltac:(lia) Hstkw Htk Q240 He240 Rbuf Rsh R240 R280) as HRUN.
  apply (QKM.kitmem_lift A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx) HRUN (A.ProgBridge.fp_avoids_RNG_W _)).
  intros ms1 md' Hrun HPost Hsbm.
  destruct HPost as (y10 & y11 & y12 & y13 & y14 & y15 & Ems). subst ms1.
  (* ---- G5: the write site ---- *)
  set (vw := QLMEM.le8 (Z_to_bv 64
        (if QRM.psum (skipn 18 (QSM.t_g (ACtlCut.c_in cx) jn)) 32 mod 256 =? 0 then 1 else 0))) in *.
  assert (Hvw : Z.of_nat (length vw) = 8) by (unfold vw; rewrite QLMEM.length_le8; reflexivity).
  match goal with
  | |- Reusable.YA0n.SRr _ _ (mkCfg (QLMS.MS ?R _ _ _ _ ?M _) _) _ => set (Rend := R); set (memW := M)
  end.
  set (WR := ([(A + 280, A + 288)] : list QLFRM.ivl)).
  assert (MU : QLFRM.munch WR mem3 memW).
  { apply (QLFRM.munch_write WR mem3 mem3 (A + 280) vw); [apply QLFRM.munch_refl | lia | lia |].
    rewrite Hvw. unfold WR. cbn [QLFRM.inside]. left. lia. }
  (* a range wholly below or wholly above the write is outside it *)
  assert (Hout : forall lo len, lo + len <= A + 280 \/ A + 288 <= lo ->
                   forall x, lo <= x < lo + len -> QLFRM.outside WR x).
  { intros lo len Hd x Hx. unfold WR. cbn [QLFRM.outside]. split; [lia | exact I]. }
  (* every shadow byte is below HIGHMEM_BEG < A + 280 *)
  assert (Hsho : forall x, A.AsanRT.in_shadow x -> QLFRM.outside WR x).
  { intros x Hx. unfold WR. cbn [QLFRM.outside]. split; [|exact I].
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in Hx, HwHIGH. lia. }
  (* the run grows memory (ProgWorld.pws_fsteps_mem) *)
  pose proof (proj1 (A.ProgWorld.pws_fsteps_mem segs (Reusable.YA0n.w_H W3) RNG _ _ Hrun
                       (A.ProgBridge.fp_avoids_RNG_W _))) as Hgrow.
  cbn [ms_mem] in Hgrow.
  (* the kept slots of the run's end map *)
  assert (K2 : QYK11.getr Rend 2 = QYK11.getr regs3 2) by reflexivity.
  assert (K3 : QYK11.getr Rend 3 = QYK11.getr regs3 3) by reflexivity.
  assert (K4 : QYK11.getr Rend 4 = QYK11.getr regs3 4) by reflexivity.
  assert (K8 : QYK11.getr Rend 8 = QYK11.getr regs3 8) by reflexivity.
  assert (K9 : QYK11.getr Rend 9 = QYK11.getr regs3 9) by (unfold Rend; symmetry; exact R9).
  assert (K18 : QYK11.getr Rend 18 = QYK11.getr regs3 18) by (unfold Rend; symmetry; exact R18).
  assert (K19 : QYK11.getr Rend 19 = QYK11.getr regs3 19) by reflexivity.
  assert (K21 : QYK11.getr Rend 21 = QYK11.getr regs3 21) by reflexivity.
  assert (K22 : QYK11.getr Rend 22 = QYK11.getr regs3 22) by reflexivity.
  assert (K23 : QYK11.getr Rend 23 = QYK11.getr regs3 23) by (unfold Rend; symmetry; exact R23).
  assert (K24 : QYK11.getr Rend 24 = QYK11.getr regs3 24) by (unfold Rend; symmetry; exact R24).
  assert (K26 : QYK11.getr Rend 26 = QYK11.getr regs3 26) by (unfold Rend; symmetry; exact R26).
  assert (K20 : QYK11.getr Rend 20 =
    Z_to_bv 64 (if QRM.psum (skipn 18 (QSM.t_g (ACtlCut.c_in cx) jn)) 32 mod 256 =? 0 then 0 else 1))
    by reflexivity.
  assert (K25 : QYK11.getr Rend 25 = Z_to_bv 64 (QF6.f6_s9 (QSM.t_g (ACtlCut.c_in cx) jn))) by reflexivity.
  assert (R9' : ACtlCut.rgv regs3 9 A) by exact R9.
  (* the KitMem munch lemmas at this write, once *)
  assert (KQ : forall a v, ACtlCutP.q64 mem3 a v -> a + 8 <= A + 280 \/ A + 288 <= a ->
                 ACtlCutP.q64 memW a v)
    by (intros a v Hq Hd; exact (QKM.kitmem_q64_munch WR mem3 memW a v Hq MU (Hout a 8 Hd))).
  assert (KB : forall a bs, QLMEM.bytes_at A.Img0.rsegs mem3 a bs ->
                 a + Z.of_nat (length bs) <= A + 280 \/ A + 288 <= a ->
                 QLMEM.bytes_at A.Img0.rsegs memW a bs)
    by (intros a bs Hb Hd; exact (QKM.kitmem_bytes_munch WR mem3 memW a bs Hb MU (Hout a _ Hd))).
  assert (KA : forall p n, A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable memW p n)
    by (intros p n Ha; exact (QKM.kitmem_addr_munch WR mem3 memW p n Ha MU Hsho)).
  assert (KS : forall off v, ACtlCutP.spill regs3 mem3 off v -> 0 <= off -> off + 8 <= 280 ->
                 ACtlCutP.spill Rend memW off v)
    by (intros off v Hs H0 H1;
        exact (QKM.kitmem_spill_munch WR regs3 Rend mem3 memW off v A Hs R9' ltac:(lia) H0 ltac:(lia) MU K9
                 (Hout (A + off) 8 ltac:(lia)))).
  (* a byte address of application memory has its shadow byte below the write *)
  assert (Hshb : forall a, 0 <= a <= 0x800000000000 -> Z.shiftr a 3 + A.ACtlK.ASAN_K + 1 <= A + 280).
  { intros a Ha. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold A.ACtlK.ASAN_K, A.AsanRT.ASAN_K. unfold A.AsanRT.HIGHMEM_BEG in HwHIGH.
    pose proof (Z.div_le_upper_bound a 8 0x100000000000 ltac:(lia) ltac:(lia)). lia. }
  (* the journal across the write, and its stack window still present at memW *)
  assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 memW md' k).
  { match type of Hrun with
    | Reusable.YK04R.fsteps _ _ ?s0 ?s1 =>
        apply (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx
                 A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
                 (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 s0 s1 md3 md' k RNG WR)
    end;
      [exact HJ | exact Hrun | exact (A.ProgBridge.fp_avoids_RNG_W _) | exact MU | exact Hsbm |].
    intros a Ha Ho. apply QKM.kitmem_awr_win. unfold A.ACfn.LLVMF_STK.
    destruct (QKM.kitmem_not_outside WR a Ho) as (lo & hi & Hin & Hr).
    unfold WR in Hin. cbn [In] in Hin. destruct Hin as [E | []]. injection E as <- <-. lia. }
  (* the model facts of the long arm *)
  assert (Hbig : QSM.t_big (ACtlCut.c_in cx) jn = true)
    by (unfold QSM.t_big, ACtlCutP.flen in *; apply Z.leb_le; lia).
  pose proof (QF6.f6_sum (ACtlCut.c_in cx) jn Hbig) as Hsum.
  pose proof (QF6.f6_tfill (ACtlCut.c_in cx) jn Hbig) as Htfill.
  (* back to the exit cut's configuration *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81f54_at [Z.of_nat j])) Rend memW md')
            (POST cx)).
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 Rend memW md' HBASE).
  - (* the journal across the one write *)
    exact HJ'.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: the same kmax formula at the same index *)
    exact Hk.
  - (* ---- G6: the exit body C_A81f54_at ---- *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81f54_at ACtlCutP.b5_body].
    change (ACtlCutP.ixn 0 [Z.of_nat j]) with jn.
    split; [reflexivity|].
    split.
    + (* FRAC: registers by Kit.kit_frac_move, memory by KitMem.kitmem_frac_keep (by shape) *)
      apply (QKM.kitmem_frac_keep B cx fr fr Rend mem3 memW WR
               (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 Rend mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)
               MU Hgrow ltac:(lia)).
      * (* FRAC's spill cells [A+16, A+32) and [A+304, A+312), for every representative of register 9 *)
        intros A' H9' x Hx. unfold WR. cbn [QLFRM.outside]. split; [|exact I].
        unfold ACtlCut.rgv in H9'. rewrite K9, R9 in H9'.
        apply (f_equal (@bv_unsigned 64)) in H9'. rewrite !Z_to_bv_unsigned in H9'.
        unfold bv_wrap in H9'. change (bv_modulus 64) with (2 ^ 64) in H9'. rewrite HP in H9'.
        Z.div_mod_to_equations. lia.
      * (* the frame header words and the fake-frame trailer, inside [fr, fr + 4096), below the write *)
        intros x Hx. apply (Hout fr 4096); lia.
      * (* the saved registers [c_sp cx - 104, c_sp cx), above the write *)
        intros x Hx. apply (Hout (ACtlCut.c_sp cx - 104) 104); lia.
    + exists phi.
      split; [exact HPerm|]. split; [exact Hn26|]. split; [exact Hj255|].
      (* HB *)
      split; [split; [exact Hphi0 | unfold A.ACtlK.a_size; exact (KA _ _ Haddrblk)]|].
      (* FLSI *)
      split.
      * destruct HFLSI as (HFLSH & Sp216 & Sp224 & Sp248 & HIN & HFLC).
        destruct HFLSH as (HPRO & Sp128 & Hstkfr & Sp144 & Haddr2691).
        destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pa2624 & Pin & Pn & P184 &
          P256 & P264 & P272 & P32).
        destruct HFLC as (F256 & F184 & F192 & F80 & F88 & F96 & F272 & F264 & Ffrag & F2688 & F72 & F64 &
          F56 & F48).
        destruct HIN as (HINa & HINb).
        (* the input block ends below the spill area *)
        assert (Hinlen : ACtlCut.c_n cx = Z.of_nat (length (ACtlCut.c_in cx))).
        { pose proof HBASE as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hn & _). exact Hn. }
        assert (Hinbnd : ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) <= A + 280).
        { pose proof HBASE as (HPRE & _).
          pose proof HPRE as (_ & _ & _ & _ & HPn & _).
          destruct HPn as [[Hz Hp] | [Hpos Hinb]].
          - rewrite <- Hinlen, Hz. rewrite Hp. unfold A.ACfn.A_EMPTY. lia.
          - destruct (Reusable.YG0d.al_blocks _ _ LAWS (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
              (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.c_p cx) (ACtlCut.c_n cx)
              (proj1 (proj1 HPRE)) Hinb) as (_ & _ & Hcc & _).
            replace (Reusable.YG00.req_size (ACtlCut.c_n cx)) with (ACtlCut.c_n cx) in Hcc
              by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia).
            rewrite <- Hinlen. lia. }
        unfold ACtlCutP.FLSI, ACtlCutP.FLSH, ACtlCutP.PRO, ACtlCutP.FLC, ACtlCutP.f1_IN.
        repeat match goal with |- _ /\ _ => split end.
        -- exact (KS 40 _ P40 ltac:(lia) ltac:(lia)).
        -- exact (KS 120 _ P120 ltac:(lia) ltac:(lia)).
        -- exact (KS 136 _ P136 ltac:(lia) ltac:(lia)).
        -- exact (KS 160 _ P160 ltac:(lia) ltac:(lia)).
        -- exact (KS 168 _ P168 ltac:(lia) ltac:(lia)).
        -- exact (KS 176 _ P176 ltac:(lia) ltac:(lia)).
        -- exact (KS 208 _ P208 ltac:(lia) ltac:(lia)).
        -- exact (KS 248 _ P248 ltac:(lia) ltac:(lia)).
        -- exact (KA _ _ Pa2624).
        -- exact (KB _ _ Pin ltac:(lia)).
        -- intros Hpos. exact (KA _ _ (Pn Hpos)).
        -- exact (KS 184 _ P184 ltac:(lia) ltac:(lia)).
        -- exact (KS 256 _ P256 ltac:(lia) ltac:(lia)).
        -- exact (KS 264 _ P264 ltac:(lia) ltac:(lia)).
        -- exact (KS 272 _ P272 ltac:(lia) ltac:(lia)).
        -- exact (KS 32 _ P32 ltac:(lia) ltac:(lia)).
        -- exact (KS 128 _ Sp128 ltac:(lia) ltac:(lia)).
        -- exact (QLFRM.stk_write segs mem3 fr (fr + ACtlCutP.FRAME_BYTES) (A + 280) vw Hstkfr
                    ltac:(lia) ltac:(lia)).
        -- exact (KS 144 _ Sp144 ltac:(lia) ltac:(lia)).
        -- exact (KA _ _ Haddr2691).
        -- exact (KS 216 _ Sp216 ltac:(lia) ltac:(lia)).
        -- exact (KS 224 _ Sp224 ltac:(lia) ltac:(lia)).
        -- exact (KS 248 _ Sp248 ltac:(lia) ltac:(lia)).
        -- exact (KA _ _ HINa).
        -- exact (KB _ _ HINb ltac:(lia)).
        -- exact (KS 256 _ F256 ltac:(lia) ltac:(lia)).
        -- exact (KS 184 _ F184 ltac:(lia) ltac:(lia)).
        -- exact (KS 192 _ F192 ltac:(lia) ltac:(lia)).
        -- exact (KS 80 _ F80 ltac:(lia) ltac:(lia)).
        -- exact (KS 88 _ F88 ltac:(lia) ltac:(lia)).
        -- exact (KS 96 _ F96 ltac:(lia) ltac:(lia)).
        -- exact (KS 272 _ F272 ltac:(lia) ltac:(lia)).
        -- exact (KS 264 _ F264 ltac:(lia) ltac:(lia)).
        -- exact (KA _ _ Ffrag).
        -- exact (KA _ _ F2688).
        -- exact (KS 72 _ F72 ltac:(lia) ltac:(lia)).
        -- exact (KS 64 _ F64 ltac:(lia) ltac:(lia)).
        -- exact (KS 56 _ F56 ltac:(lia) ltac:(lia)).
        -- exact (KS 48 _ F48 ltac:(lia) ltac:(lia)).
      * split.
        -- (* LK *)
           destruct HLK as (HLj & HL21 & HOUR).
           split; [exact HLj|]. split; [unfold ACtlCut.rgv in *; rewrite K21; exact HL21|].
           unfold ACtlCutP.OURb in *.
           apply (KB _ _ HOUR). left. rewrite QSM.OUR_length. lia.
        -- split.
           ++ (* b5_C *)
              split; [unfold ACtlCut.rgv in *; rewrite K23; exact R23|].
              split; [unfold ACtlCut.rgv in *; rewrite K18; exact R18|].
              split.
              ** destruct HCA as (Ac & H9c & HAc & HSPILL & Q232).
                 assert (EAc : Ac = A).
                 { apply (QF6.f6_id Ac A HAc HA64). unfold ACtlCut.rgv in H9c.
                   rewrite <- H9c, <- R9. reflexivity. }
                 subst Ac.
                 exists A. split; [unfold ACtlCut.rgv; rewrite K9; exact R9|]. split; [exact HA64|].
                 split.
                 --- destruct HSPILL as (B248 & B256 & B144 & B184 & B192 & B80 & B88 & B96 & B272 & B264).
                     unfold ACtlCutP.b5_SPILL.
                     repeat match goal with |- _ /\ _ => split end;
                       (apply KQ; [eassumption | lia]).
                 --- exact (KQ _ _ Q232 ltac:(lia)).
              ** split.
                 --- (* b5_PH *)
                     split.
                     +++ intros Hl. apply (KB _ _ (HPHb Hl)).
                         left. rewrite (QF6.f6_tg_len (ACtlCut.c_in cx) jn). lia.
                     +++ intros Hl. unfold Reusable.YG0d.spZ. rewrite K2. exact (HPHd Hl).
                 --- split.
                     +++ (* b5_FR *)
                         destruct HFR as (HFRa & HFRb & HFRc & HFRl).
                         split; [exact (KA _ _ HFRa)|].
                         split; [exact (KA _ _ HFRb)|].
                         split; [|exact HFRl].
                         apply (KB _ _ HFRc). left. rewrite HFRl. unfold ACtlCutP.fragb. lia.
                     +++ split.
                         *** (* b5_KN: the kind-name table, an image range below 0x5fe000 *)
                             destruct HKN as (HKNa & HKNb).
                             split; [|exact (KA _ _ HKNb)].
                             apply (KB _ _ HKNa). left.
                             match goal with
                             | |- ?e <= _ =>
                                 assert (Hkn : (e <=? 6283264) = true) by (vm_compute; reflexivity);
                                 apply Z.leb_le in Hkn
                             end.
                             unfold A.AsanRT.HIGHMEM_BEG in HwHIGH. lia.
                         *** split.
                             ---- (* FGj *)
                                  destruct HFGj as (HFGa & HFGb). split; [|exact HFGb].
                                  apply (KB _ _ HFGa). left. rewrite (proj2 (proj2 (proj2 HFR))). lia.
                             ---- (* FSj *)
                                  destruct HFSj as (S104 & S112 & Sbody & Saddr & SFI).
                                  split; [exact (KS 104 _ S104 ltac:(lia) ltac:(lia))|].
                                  split; [exact (KS 112 _ S112 ltac:(lia) ltac:(lia))|].
                                  split.
                                  ++++ apply (KB _ _ Sbody).
                                       left. pose proof (QF6.f6_fs_body_len (ACtlCut.c_in cx) jn). lia.
                                  ++++ split; [exact (KA _ _ Saddr) | exact SFI].
           ++ split.
              ** (* b5_K *)
                 split.
                 --- unfold ACtlCut.rgv. rewrite K20, Hsum.
                     destruct (QRM.psum (skipn 18 (QSM.t_g (ACtlCut.c_in cx) jn)) 32 mod 256 =? 0);
                       reflexivity.
                 --- split; [rewrite Hbig; unfold ACtlCut.rgv in *; rewrite K22; exact R22|].
                     split; [unfold ACtlCut.rgv; rewrite K24; exact R24|].
                     split; [rewrite Htfill; unfold ACtlCut.rgv; exact K25|].
                     split.
                     +++ (* the written cell [A+280] = b2z (t_sum_ok) *)
                         exists A. split; [unfold ACtlCut.rgv; rewrite K9; exact R9|].
                         split; [exact HA64|].
                         rewrite Hsum. unfold ACtlCutP.q64, memW, vw.
                         apply QLMEM.bytes_at_write_same; [lia | rewrite QLMEM.length_le8; lia].
                     +++ split.
                         { unfold ACtlCutP.u32 in *. apply (KB _ _ HU32). left.
                           rewrite QLMEM.length_le4. lia. }
                         apply QF6.f6_reply; [exact Hphi0 | lia].
              ** split.
                 --- (* IDj *)
                     destruct HIDj as (HIDa & HIDb). split; [|exact HIDb].
                     apply (KB _ _ HIDa). left. rewrite (QF6.f6_tID_len (ACtlCut.c_in cx) jn). lia.
                 --- split.
                     +++ (* b5_F17 *)
                         destruct HF17 as (Af & H9f & HAf & Q200).
                         assert (EAf : Af = A).
                         { apply (QF6.f6_id Af A HAf HA64). unfold ACtlCut.rgv in H9f.
                           rewrite <- H9f, <- R9. reflexivity. }
                         subst Af.
                         exists A. split; [unfold ACtlCut.rgv; rewrite K9; exact R9|].
                         split; [exact HA64|].
                         exact (KQ _ _ Q200 ltac:(lia)).
                     +++ split.
                         *** (* b5_W240 *)
                             destruct HW240 as (Aw & H9w & HAw & w240 & Qw & Hwr & Hw1 & Hw0').
                             assert (EAw : Aw = A).
                             { apply (QF6.f6_id Aw A HAw HA64). unfold ACtlCut.rgv in H9w.
                               rewrite <- H9w, <- R9. reflexivity. }
                             subst Aw.
                             exists A. split; [unfold ACtlCut.rgv; rewrite K9; exact R9|].
                             split; [exact HA64|].
                             exists w240. split; [exact (KQ _ _ Qw ltac:(lia))|].
                             split; [exact Hwr|]. split; [exact Hw1 | exact Hw0'].
                         *** (* b5_PF *)
                             destruct HPF as (Ap & H9p & HAp & HPFa & HPFb).
                             assert (EAp : Ap = A).
                             { apply (QF6.f6_id Ap A HAp HA64). unfold ACtlCut.rgv in H9p.
                               rewrite <- H9p, <- R9. reflexivity. }
                             subst Ap.
                             exists A. split; [unfold ACtlCut.rgv; rewrite K9; exact R9|].
                             split; [exact HA64|].
                             split.
                             ---- intros Hl. destruct (HPFa Hl) as ((rb & Hrb & Hrbl) & Hphib').
                                  split.
                                  ++++ exists (firstn 38 rb). split.
                                       **** apply (KB _ _ (QF6.f6_bytes_firstn mem3 phi rb 38 Hrb)).
                                            left. rewrite length_firstn. lia.
                                       **** rewrite length_firstn. lia.
                                  ++++ apply (KB _ _ Hphib').
                                       left. unfold QSM.t_phi, QSM.f_phi. rewrite length_firstn.
                                       unfold ACtlCutP.flen, QSM.t_len in *. lia.
                             ---- intros H8819. destruct (HPFb H8819) as (HR1 & HR2 & HR3).
                                  split.
                                  ++++ destruct HR1 as (f16 & v14 & v15 & v16 & v17 & U16 & B14 & B15 & B16 &
                                         B17 & N14 & N15 & N16 & N17 & SH14 & SH15 & SH16 & SH17 & Ef & Ek).
                                       exists f16, v14, v15, v16, v17.
                                       unfold ACtlCutP.u16, ACtlCutP.b8 in *.
                                       split; [apply (KB _ _ U16); left; rewrite QLMEM.length_le2; lia|].
                                       split; [apply (KB _ _ B14); left; cbn [length]; lia|].
                                       split; [apply (KB _ _ B15); left; cbn [length]; lia|].
                                       split; [apply (KB _ _ B16); left; cbn [length]; lia|].
                                       split; [apply (KB _ _ B17); left; cbn [length]; lia|].
                                       split; [exact N14|]. split; [exact N15|]. split; [exact N16|].
                                       split; [exact N17|].
                                       split; [apply (KB _ _ SH14); left; cbn [length];
                                               pose proof (Hshb (phi + 14) ltac:(lia)); lia|].
                                       split; [apply (KB _ _ SH15); left; cbn [length];
                                               pose proof (Hshb (phi + 15) ltac:(lia)); lia|].
                                       split; [apply (KB _ _ SH16); left; cbn [length];
                                               pose proof (Hshb (phi + 16) ltac:(lia)); lia|].
                                       split; [apply (KB _ _ SH17); left; cbn [length];
                                               pose proof (Hshb (phi + 17) ltac:(lia)); lia|].
                                       split; [exact Ef | exact Ek].
                                  ++++ split.
                                       **** destruct HR2 as (ls & rs & Q72 & Bls & Hls & Brs & Hrs & Hmc & Ha186).
                                            exists (firstn 6 ls), (firstn 6 rs).
                                            split; [exact (KQ _ _ Q72 ltac:(lia))|].
                                            split; [apply (KB _ _ (QF6.f6_bytes_firstn mem3 (fr + 186) ls 6 Bls));
                                                    left; rewrite length_firstn; lia|].
                                            split; [rewrite length_firstn; lia|].
                                            split; [apply (KB _ _ (QF6.f6_bytes_firstn mem3 phi rs 6 Brs));
                                                    left; rewrite length_firstn; lia|].
                                            split; [rewrite length_firstn; lia|].
                                            split; [rewrite QF6.f6_memcmp_firstn; exact Hmc|].
                                            exact (KA _ _ Ha186).
                                       **** destruct HR3 as (ls2 & rs2 & Q64 & Bls2 & Hls2 & Brs2 & Hrs2 & Hmc2 & Ha180).
                                            exists (firstn 6 ls2), (firstn 6 rs2).
                                            split; [exact (KQ _ _ Q64 ltac:(lia))|].
                                            split; [apply (KB _ _ (QF6.f6_bytes_firstn mem3 (fr + 180) ls2 6 Bls2));
                                                    left; rewrite length_firstn; lia|].
                                            split; [rewrite length_firstn; lia|].
                                            split; [apply (KB _ _ (QF6.f6_bytes_firstn mem3 (phi + 6) rs2 6 Brs2));
                                                    left; rewrite length_firstn; lia|].
                                            split; [rewrite length_firstn; lia|].
                                            split; [rewrite QF6.f6_memcmp_firstn; exact Hmc2|].
                                            exact (KA _ _ Ha180).
  - (* ctl_rt_C across the write, at the entry's ly3 S3: the write set is application memory off the image, so the
       asan cells and the read-only bytes (image bytes: KitMem.kitmem_asan_cells_img / kitmem_ro_agree_img) and
       every shadow byte (Hsho) keep their values, and both regions (cut_shadow B ly3 S3, img_shadow) stay *)
    assert (HWI : forall x, ~ QLFRM.outside WR x -> ~ Reusable.YG0d.in_img A.AB1v.tfibsegs x).
    { intros x Hx. destruct (QKM.kitmem_not_outside WR x Hx) as (lo & hi & Hin & Hr).
      unfold WR in Hin. cbn [In] in Hin. destruct Hin as [E | []]. injection E as <- <-.
      apply QKM.kitmem_not_img_hi. unfold A.Prog.ImgBounds.IMG_HI. unfold A.AsanRT.HIGHMEM_BEG in HwHIGH. lia. }
    destruct Hrt as (AC & HCUT & HIMG & RO).
    split; [exact (QKM.kitmem_asan_cells_img WR mem3 memW AC MU HWI)|].
    split; [exact (e28_srw_on_munch _ WR mem3 memW HCUT MU Hsho)|].
    split; [exact (e28_srw_on_munch _ WR mem3 memW HIMG MU Hsho)|].
    exact (QKM.kitmem_ro_agree_img WR mem3 memW RO MU HWI).
Qed.

End GlueF6e28.

Print Assumptions glue_seg_F6_e28.
