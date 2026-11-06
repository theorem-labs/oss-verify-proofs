(* lib/A/ACtlG/F20.v -- GLUE for stage seg_F20 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:810-811).  Written by a Theorem Labs lane; single writer.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F20 : forall POST (j : nat),
       CF POST (ix_cut C_A824b4_at [Z.of_nat j]) -> CF POST (ix_cut C_A82418_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v:621's Section
   hypothesis seg_F20.  Segment F20 is 0x82418 -> 0x824b4: four one-byte instrumented checks on the record bytes
   phi+14..phi+17, the is_8819 field read and compare, the v16 case split, and the ONE LLVMF-level call of
   reac_ctrl_checksum_verify at 0x824b0.

   NO LIFT IS CITED, and no `<f>_SRr_at` and no `_hid` placeholder (a Theorem Labs lane, 04:10Z and 04:43Z): the
   segment's `_F` for the call half SPANS the `jal` and discharges the callee's footprint contract itself with the
   callee's own closed theorem.  The caller obligation at the call site is therefore that contract's premises (the
   record block, the runtime cells, the 16-byte callee window), not a lift's.  ROUTE (C) (a working branch
   1899bed1aee): the call half is A.Prog.Seg.F20Fs.f20_call_evt_F_on, this lane's twin
   of a Theorem Labs lane's Seg/F20F.v f20_call_evt_F WITHOUT its `shadow_rw m` premise (Seg/F20F.v unchanged apart from comment text), cut
   through the narrowed reac_ctrl_checksum_verify_F.reac_ctrl_checksum_verify_F_holds_on.  The cut now carries
   A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.

   THE TWO RUNS
   - head 0x82418 -> 0x824ac: A.Prog.Seg.F20Fs.f20_head_F.  F20's head stretch has NO `_F` of record
     (segment-runs-A.tsv (a working note, not in this delivery) names only sl_run_lib:206, which is not a run lemma, and f20_call_evt:341, the call
     half; F20.v runs the head inline at F20.v:496-545), so this lane wrote lib/A/Prog/Seg/F20Fs.v, a file of its
     own that Requires a Theorem Labs lane's F20F and the sources only and never edits them.  Its pin is the PROVED
     composition F20Fs.f20_of_head_call.  It READS memory and WRITES NONE, so it is lifted with the plain
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.SRr_fevt.
   - call 0x824ac -> 0x824b4: A.Prog.Seg.F20Fs.f20_call_evt_F_on (route (C) twin of F20F.v:45-105).  It writes the
     callee's own 16-byte frame [sp - 16, sp), so it is lifted with OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.SRr_fevt_hid, whose
     continuation hands this file exactly ajournal_exec's hidden-bytes premise.
   Both lifts are at the same footprint A.ProgBridge.RNG_W (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.w_H W3), and each `rng` premise is
   A.ProgBridge.rng_of_visible of a visibility fact (ProgWorldVisHeap / ProgWorldVisFrame / ProgWorldVisWin /
   ProgBridge.img_vis_W).

   THE PROOF, step by step (glue-pattern.md section 3 is the template)
   G1  unfold the entry cut: ix_cut's index equation, then C_A82418_at's conjuncts (ACtlCutP.v:2522-2554).
   G2  the run's premises from the body and from visible state only.  THE ONE GEOMETRIC FACT everything rests
       on: the callee's 16-byte window [sp - 16, sp) lies strictly ABOVE every byte the cut speaks of except the
       spill area [A, A + 416) and the saved registers at [c_sp cx - 104, c_sp cx), which lie at or above sp.
       Proof: frames_bounds gives fr + fs_frame_bytes 6 <= alloc_ceiling (fs_frame_bytes 6 = 4096), the AR block
       law gives phi + flen <= alloc_ceiling, and the journal's astk_ok gives
       alloc_ceiling <= ly_stk_lo (c_ly cx) <= c_sp cx - LLVMF_STK, while FRAC gives c_sp cx - 4096 < sp <= A and
       A + 416 <= c_sp cx.  So fr + 3136 < sp - 16 and phi + 50 < sp - 16, and sp <= A.
   G3  register maps: ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv moves the WALK to the run's canonical map
       (mkR_of regs3), mkR_expand turns that into the 31 slots, and the body's rgv facts pin slots 9, 10, 20,
       22, 23, 24 and 26 to the values the run's start state names.
   G4  two lifts: SRr_fevt over the head (no write), SRr_fevt_hid over the call (the 16-byte window).
   G5  the exit cut C_A824b4_at (ACtlCutP.v:2558-2578), rebuilt conjunct for conjunct across the write:
         journal  ajournal_exec twice -- once with the empty write set for the head's model materialization,
                  once with Wr := [sp - 16, sp), whose awr_byte is the stack-window disjunct (YCbq.v:461);
         frames, frame law, k bound   unchanged (own6 and the same cut_kmax on both cuts);
         body     every memory conjunct through munch (fl_bytes / addressable_kept / stk_transport), every
                  register conjunct from the run's post;
         ctl_rt_C asan_cells_kept, the two shadow regions cut_shadow / img_shadow kept by
                  A.ShadowRwOnK.fl_shadow_rw_on (the window lies above every shadow byte; the state ly3 S3 is the
                  entry cut's), and ro_agree across a write above the image.

   SECTION HYPOTHESES (exact text in the file; why each one)
   - LAWS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.AR_laws segs B.  The core's AR law record, the Section hypothesis of YCbq Section a0
     (YCbq.v:207) that ajournal_exec, frames_bounds and al_blocks take; ACtl.v:183 has it.
   NOTHING ELSE is left open: the image facts come from the shared kit, A.ACtlG.Kit.kit_wx and
   A.ACtlG.Kit.kit_segs_low (Kit.v builds on the glue base 46eb24cd4b3, blob 7e164a09a73; the placeholders this
   file carried on the older base eb89fed7fac are gone).  A.ACtlG.Kit.kit_frac_move is NOT used here: FRAC has
   to move over memory as well as registers, which kit_frac_move does not do, so this file rebuilds FRAC
   conjunct by conjunct instead.
   No Axiom, no Parameter, no unproved step.

   CLOSURE: every Require below is qualified (no Import / Export of a project module); no statement here names a
   frame-route identifier.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are Reusable.YK11 / Reusable.YG0d-qualified everywhere. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.ACfn A.AE2k A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisHeap A.ProgWorldVisFrame A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.rng_asan A.Prog.RcAsanFPLib A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F13 A.Prog.Seg.F20 A.Prog.Seg.F20F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.F20Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.MemNormTr.
Import ListNotations.
Local Open Scope Z_scope.
(* NAME SHADOWING, measured on this base: lib/A/Reusable (and lib/B, lib/U) hold copies of YK11, YK1b, YM05 and
   YO09, and lib/AZ/Lib (not in this delivery) and lib/A/Bz/Lib hold copies of lib/Lib's files.  Requiring a Theorem Labs lane's Seg/F20F.v (which
   Imports lib/A/Reusable) therefore lets a short `Reusable.` or `Lib.` prefix resolve to a ctrl-side copy, whose
   FPState / RunCeil / lib_shape classes are NOT the core's.  Every such name below is written with its full
   OSSVerify.Proofs.libreac.fuzz_ctrl.lib path, as ACtl.v:172 and ACtlG/A5.v do.  Nothing is Imported. *)


(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Local helpers, each closed by Qed.  None of them is a Kit helper. *)

(* The canonical register map in its 31 slots (F20.v:196-202 is the same equation over ctrl's YK11). *)
Lemma mkR_expand : forall regs : bvmap 5 word, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs =
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 1) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 2) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 3)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 4) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 5) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 6)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 7) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 9)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 10) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 11) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 12)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 13) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 14) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 15)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 16) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 17) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 18)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 19) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 20) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 21)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 23) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 24)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 25) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 27)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 28) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 29) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 30)
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* A byte above the image is in no loaded segment, so the rom reads None there and lib/Lib's mrd is the memory
   itself.  (Image A's segments end at 0x5fe000; kLowMemEnd = 0x7fff8000 is a safe cut.) *)
Lemma mrd_some_mem : forall (m : word -> option byte) (x : word) b,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.kLowMemEnd <= bv_unsigned x ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd A.Img0.rsegs m x = Some b -> m x = Some b.
Proof.
  intros m x b Hx H. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd in H.
  destruct (m x) as [b0|] eqn:E; [exact H|].
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom, memory_read in H. cbn [Z.of_N] in H.
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.find_segment1_none_above A.Img0.rsegs OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.kLowMemEnd (bv_unsigned x)
             ltac:(vm_compute; reflexivity) Hx) in H.
  discriminate.
Qed.

(* A byte the memory maps is a writable view (lib/Lib's wview reads the memory first). *)
Lemma wv_some : forall (m : word -> option byte) (x : word) b,
  m x = Some b -> wview A.Img0.rsegs m x <> None.
Proof. intros m x b H. unfold wview. rewrite H. discriminate. Qed.

(* A spill read through s1 = A: its base is A (the analogue of F20.v:226-238 over the cut layer's vocabulary). *)
Lemma spill_q64 : forall (regs : bvmap 5 word) (m : word -> option byte) (Ab off v : Z),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv regs 9 Ab -> 0 <= Ab -> Ab + 416 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 416 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.spill regs m off v -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.q64 m (Ab + off) v.
Proof.
  intros regs m Ab off v H9 HA0 HA Ho0 Ho (A' & H9' & Hq).
  assert (E : A' = Ab).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8 in Hq1. cbn [Z.of_nat] in Hq1.
    unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv in H9, H9'. rewrite H9 in H9'.
    apply (f_equal (bv_unsigned (n := 64))) in H9'.
    rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit Ab) in H9' by lia. rewrite Z_to_bv_unsigned in H9'.
    unfold bv_wrap, bv_modulus in H9'. change (2 ^ Z.of_N 64) with (2 ^ 64) in H9'.
    pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound A' (2 ^ 64) ltac:(lia)). lia. }
  subst A'. exact Hq.
Qed.

(* The byte-exact shadow range of [p, p + n) sits inside the 8-aligned shadow word cover the visibility lemmas
   return (A.Prog.rng_asan.sh_al8_lo / sh_al8_hi).  CANDIDATE FOR Kit: every stage that lifts a run with an
   instrumented access needs it. *)
Lemma sh_byte_vis : forall H p n, 0 <= p -> 0 < n ->
  A.ProgBridge.range_visible H (A.Prog.rng_asan.sh_al8_lo p)
    (A.Prog.rng_asan.sh_al8_hi p n - A.Prog.rng_asan.sh_al8_lo p) ->
  A.ProgBridge.range_visible H (p / 8 + A.AsanRT.ASAN_K) ((p + n - 1) / 8 - p / 8 + 1).
Proof.
  intros H p n Hp Hn HV.
  apply (A.ProgBridge.range_visible_sub H (A.Prog.rng_asan.sh_al8_lo p)
           (A.Prog.rng_asan.sh_al8_hi p n - A.Prog.rng_asan.sh_al8_lo p)); [exact HV | | |];
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
    Z.div_mod_to_equations; lia.
Qed.

Section GlueF20.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil} {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.asyms.
Variable MT : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :224-...), verbatim. *)
Local Notation ix_cut := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.ix_cut.
Local Notation CF POST X :=
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82418_at := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.C_A82418_at B).
Local Notation C_A824b4_at := (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.C_A824b4_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The core's AR law record (YCbq.v:207, Section a0's hypothesis; ACtl.v:183 has the same one). *)
Hypothesis LAWS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.AR_laws segs B.

(* (no kit placeholder: Kit.v builds on this base and is Required qualified above) *)

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_F20 : forall POST (j : nat),
  CF POST (ix_cut C_A824b4_at [Z.of_nat j]) -> CF POST (ix_cut C_A82418_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* ---- G1: the entry cut at index [Z.of_nat j] ---- *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.cut_body OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.C_A82418_at OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HPerm & HFRAC & Hn26 & Hj255 & HHB & HFLSI & HLK & R23 & R20 & R22 & R24 & R10 &
    Hphi0 & Hphi50 & Hflen & Htk & Hblk & Hrec34 & S280 & S136 & S120 & S176 & HIS & R18 & S152 &
    Hgb & Hpb & Hpl & HLT).
  destruct HIS as (v14 & v15 & v16 & v17 & field16 & S248 & Hfield & Hb14 & Hb15 & Hb16 & Hb17 &
    Rv14 & Rv15 & Rv16 & Rv17 & Hsh14 & Hsh15 & Hsh16 & Hsh17 & Heq1 & Heq2).
  destruct Hrt as (HACl & HCUTl & HIMGl & HROl).
  unfold A.ACtlK.asan_cells_at in HACl.
  (* ---- G2: the geometry, from visible state only ---- *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstkok & _).
  destruct Hstkok as (_ & _ & Hceil_lo & Hlo_sp & _).
  unfold A.ACfn.LLVMF_STK in Hlo_sp, Hpres.
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  pose proof (@OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.ASAN_CEIL_range rc) as (Hacr & _).
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.ASAN_CEIL in Hacr.
  assert (Hin6 : In (6, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_fpos cx) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  assert (Efb : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.fs_frame_bytes 6 = 4096) by (vm_compute; reflexivity).
  rewrite Efb in Hfceil.
  assert (Efr : fr = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.frame_addr (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_ly cx) 6 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.frame_addr ly3 6 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_fpos cx) = fr).
  { rewrite Efr. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.frame_addr in *. rewrite EF. reflexivity. }
  rewrite Efr3 in Hf4096, Hfceil.
  (* the live record block *)
  assert (Hinblk : In (phi, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  assert (Ereq : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.req_size (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j) = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j).
  { unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j) 0); [lia | reflexivity]. }
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.al_blocks segs B LAWS ly3 S3 W3 mem3 md3 phi (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j) HAR Hinblk)
    as (_ & Hp4096 & Hpceil & _).
  rewrite Ereq in Hpceil.
  (* FRAC.  Its last conjunct is the class-6 frame's trailer word, `q64 m (fr + 4088) (flag_addr (c_ly cx) 6
     (c_fpos cx))` (a Theorem Labs lane's glue base batch 3); it is Htrail. *)
  pose proof HFRAC as (A & sp & Hr2 & Hspm & Hspz & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm32 & HAm &
    HAS & HspA & HfrA & HA416 & Hsp4096 & HSapp & Hq304 & Hq24 & Hq16 & Hqfr & Hqfr16 & Hshb & Hsaved & Htrail).
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.FRAME_BYTES in HfrA.
  unfold A.AsanRT.APPMEM_END in HSapp.
  (* the input block of the lib pre: it also ends below the allocator ceiling *)
  pose proof HB as (HPRE & _).
  unfold A.ACfn.tfib_lib_pre_x in HPRE.
  destruct HPRE as (HAFN & _ & _ & _ & HBLK & Hnlen & _).
  pose proof HAFN as (HAR0 & _).
  assert (Hcpend : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_p cx + Z.of_nat (length (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx)) <= OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling).
  { destruct HBLK as [(Hn0 & Hp0) | (Hnpos & Hin0)].
    - rewrite <- Hnlen, Hn0, Hp0. unfold A.ACfn.A_EMPTY. lia.
    - destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.al_blocks segs B LAWS (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_ly cx) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_S cx) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_W cx)
                  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_mem cx) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_md cx) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_p cx) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_n cx) HAR0 Hin0)
        as (_ & _ & Hce & _).
      unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.req_size in Hce. destruct (Z.eqb_spec (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_n cx) 0); lia. }
  (* THE geometric facts the whole proof uses *)
  assert (Hspw : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.alloc_ceiling + 28672 <= sp) by lia.
  assert (Hfrw : fr + 3136 + 16 <= sp) by lia.
  assert (Hphiw : phi + 50 + 16 <= sp) by lia.
  assert (Hcpw : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_p cx + Z.of_nat (length (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx)) + 16 <= sp) by lia.
  assert (Hsp0 : 0 <= sp) by lia.
  assert (Hsp64 : sp + 16 <= 2 ^ 64) by lia.
  assert (HA0 : 0 <= A) by lia.
  assert (HA64 : A + 416 <= 2 ^ 64) by lia.
  assert (Hsfr : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.Sfr fr + 392 + 16 <= sp).
  { unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. Z.div_mod_to_equations. lia. }
  (* the record block's addressable bytes *)
  pose proof HHB as (Hphinz & Hadr).
  unfold A.ACtlK.a_size in Hadr. rewrite Z.max_l in Hadr by lia.
  assert (Hadr18 : A.AsanRT.addressable mem3 (phi + 18) 32)
    by (apply (A.AsanRTFacts.addressable_sub mem3 phi (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j) 18 32 Hadr); lia).
  (* the callee's 16-byte window is present at the cut *)
  assert (Hstk16 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk A.Img0.rsegs mem3 (sp - 16) sp).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (Hpres a ltac:(lia)) as (_ & b & Hbm).
    split; [exact (wv_some mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa a) b Hbm)|].
    exists b. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa. rewrite Hbm. reflexivity. }
  (* ---- the footprint and its visibility facts ---- *)
  pose (RNGW := A.ProgBridge.RNG_W (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.w_H W3)).
  assert (Vwin : forall lo len, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_sp cx ->
                   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng RNGW lo len).
  { intros lo len Hl Hh. apply A.ProgBridge.rng_of_visible.
    exact (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_sp cx) [] (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_ly cx) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_S cx)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_W cx) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_mem cx) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_md cx) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.cut_own (ix_cut C_A82418_at
             [Z.of_nat j]) cx) ly3 S3 W3 mem3 md3 k lo len HJ Hl Hh). }
  assert (Vheap : forall lo len, phi <= lo -> lo + len <= phi + OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j ->
                   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng RNGW lo len).
  { intros lo len Hl Hh. apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j) lo len HAR Hinblk Hl).
    rewrite Ereq. exact Hh. }
  assert (Vframe : forall lo len, fr <= lo -> lo + len <= fr + 4096 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng RNGW lo len).
  { intros lo len Hl Hh. apply A.ProgBridge.rng_of_visible.
    refine (proj1 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_fpos cx) lo len
                     HAR Hin6 _ _)); rewrite Efr3, ?Efb; lia. }
  assert (Vimg : forall lo len, A.Prog.ImgBounds.IMG_LO <= lo -> lo + len <= A.Prog.ImgBounds.IMG_HI ->
                   0 <= len -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng RNGW lo len).
  { intros lo len Hl Hh Hlen. apply A.ProgBridge.rng_of_visible.
    exact (A.ProgBridge.range_visible_sub _ _ _ lo len (A.ProgBridge.img_vis_W W3) Hl Hlen ltac:(lia)). }
  assert (Vsh : forall p n, phi <= p -> 0 < n -> p + n <= phi + OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j ->
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng RNGW (p / 8 + A.AsanRT.ASAN_K) ((p + n - 1) / 8 - p / 8 + 1)).
  { intros p n Hl Hn Hh. apply A.ProgBridge.rng_of_visible. apply sh_byte_vis; [lia | lia |].
    destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j) p n
                HAR Hinblk Hl ltac:(rewrite Ereq; lia) ltac:(lia)) as [E0 | HV]; [lia | exact HV]. }
  assert (Vsh1 : forall p, phi <= p -> p + 1 <= phi + OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j ->
                   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.rng RNGW (Z.shiftr p 3 + A.AsanRT.ASAN_K) 1).
  { intros p Hl Hh.
    replace (Z.shiftr p 3) with (p / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    replace 1 with ((p + 1 - 1) / 8 - p / 8 + 1) by lia.
    apply (Vsh p 1); lia. }
  (* ---- G3: the cut's configuration in the run's form, then the walk at the run's register map ---- *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.cut_pc (ix_cut C_A82418_at [Z.of_nat j])) with 0x82418.
  apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of regs3) regs3 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x82418) OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr None mem3 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.xregs_eqv_sym _ _ (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  rewrite mkR_expand.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv in Hr9, R10, R20, R22, R23, R24, Hr26.
  rewrite Hr2, Hr9, R10, R20, R22, R23, R24, Hr26.
  (* ---- G4a: the head run, lifted with SRr_fevt (it writes no memory) ---- *)
  eapply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 RNGW _ (POST cx)).
  { rewrite A.ProgBridge.tfibsegs_rsegs. apply A.ProgBridge.fevt_of_evtF.
    apply (A.Prog.Seg.F20Fs.f20_head_F RNGW
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 1) (Z_to_bv 64 sp) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 3)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 4) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 5) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 6)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 7) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 8)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 11) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 12) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 13)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 14) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 15) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 16)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 17) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 18) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 19)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 21) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 25) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 27)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 28) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 29) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 30)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 31)
             OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr mem3
             phi A fr (A.Prog.SlotModel.t_k (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) j) v14 v15 v16 v17 field16);
      try exact Hphi0; try exact Hphi50; try lia;
      try exact Heq1; try exact Heq2;
      try exact Rv14; try exact Rv15; try exact Rv16; try exact Rv17;
      try exact Hb14; try exact Hb15; try exact Hb16; try exact Hb17;
      try exact Hsh14; try exact Hsh15; try exact Hsh16; try exact Hsh17;
      try exact Htk.
    - (* q64 m (A + 248) (fr + 176) *)
      exact (spill_q64 regs3 mem3 A 248 (fr + 176) Hr9 HA0 HA64 ltac:(lia) ltac:(lia) S248).
    - (* u16 m (fr + 196) field16 *) exact Hfield.
    - (* rng (A + 248) 8 *) apply Vwin; lia.
    - (* rng (fr + 196) 2 *) apply Vframe; lia.
    - apply Vheap; lia.
    - apply Vheap; lia.
    - apply Vheap; lia.
    - apply Vheap; lia.
    - apply Vsh1; lia.
    - apply Vsh1; lia.
    - apply Vsh1; lia.
    - apply Vsh1; lia. }
  { exact (A.ProgBridge.fp_avoids_RNG_W (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.w_H W3)). }
  intros ms1 md1 HQ1 Hsbm1.
  destruct HQ1 as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & Ems1). subst ms1.
  (* ---- G4b: the call run, lifted with SRr_fevt_hid (it writes the callee's 16-byte frame) ---- *)
  eapply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md1 RNGW _ (POST cx)).
  { rewrite A.ProgBridge.tfibsegs_rsegs. apply A.ProgBridge.fevt_of_evtF.
    apply (A.Prog.Seg.F20Fs.f20_call_evt_F_on RNGW
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 1) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 3) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 4)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 5) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 6) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 7)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 8)
             c0 c1 c2 c3 c4 c5 c6 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 17)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 18) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 19) (Z_to_bv 64 (phi + 18))
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 21) (Z_to_bv 64 (phi + 18))
             (Z_to_bv 64 (A.Prog.SlotModel.t_k (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) j)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 25)
             (Z_to_bv 64 A.AsanRT.ASAN_K) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 27) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 28)
             (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 29) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 30) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 31)
             OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_regs OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.fp_csr mem3
             phi A (sp - 16) sp (A.Prog.SlotModel.t_blk (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) j)).
    - (* 0 <= sp < 2 ^ 64 *) lia.
    - (* 0 < phi *) exact Hphi0.
    - (* phi + 50 <= APPMEM_END *) unfold A.AsanRT.APPMEM_END. lia.
    - (* phi + 50 <= sp - 16 *) lia.
    - (* HIGHMEM_BEG <= sp - 16 *) unfold A.AsanRT.HIGHMEM_BEG. lia.
    - (* sp - 16 + 16 <= sp *) lia.
    - (* length blk = 32 *) exact (A.Prog.Seg.F20.t_blk_len (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) j).
    - (* the 32 record bytes *) exact Hblk.
    - (* stk *) exact Hstk16.
    - (* asan_cells *) exact HACl.
    - (* addressable (phi + 18) 32 *) exact Hadr18.
    - (* rng (sp - 16) 16 *) apply Vwin; lia.
    - (* rng GOT_CELL_K 8 *) apply Vimg; unfold A.AsanRT.GOT_CELL_K, A.Prog.ImgBounds.IMG_LO,
                                           A.Prog.ImgBounds.IMG_HI; lia.
    - (* rng CELL_K 8 *) apply Vimg; unfold A.AsanRT.CELL_K, A.Prog.ImgBounds.IMG_LO,
                                      A.Prog.ImgBounds.IMG_HI; lia.
    - (* rng (phi + 18) 32 *) apply Vheap; lia.
    - (* the record's shadow bytes *)
      replace (phi + 49) with (phi + 18 + 32 - 1) by lia. apply (Vsh (phi + 18) 32); lia. }
  { exact (A.ProgBridge.fp_avoids_RNG_W (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.w_H W3)). }
  intros ms2 md2 HQ2 Hhid Hsbm2.
  destruct HQ2 as (ra' & d1 & d2 & d3 & d4 & d5 & d6 & mem' & Ems2 & MU & WM & ST').
  subst ms2.
  cbn [ms_mem] in Hhid.
  (* ---- G5: the exit cut ---- *)
  assert (OW : forall x, x < sp - 16 \/ sp <= x -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(sp - 16, sp)] x).
  { intros x Hx. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]. split; [lia | exact I]. }
  assert (Hallapp : A.AsanRTFacts.all_app [(sp - 16, sp)]).
  { cbn [A.AsanRTFacts.all_app]. split; [|exact I].
    unfold A.AsanRTFacts.app_ivl. intros a Ha. unfold A.AsanRT.app_mem. right.
    unfold A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END. lia. }
  pose proof (A.AsanRTFacts.munch_meta [(sp - 16, sp)] mem3 mem' MU Hallapp) as MK.
  assert (Kb : forall a l, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem3 a l -> a + Z.of_nat (length l) <= sp - 16 ->
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem' a l).
  { intros a l Hl Hle. eapply A.Prog.RcAsanFPLib.fl_bytes;
      [exact Hl | exact MU | intros x Hx; apply OW; left; lia]. }
  assert (Kbh : forall a l, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem3 a l -> sp <= a -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem' a l).
  { intros a l Hl Hle. eapply A.Prog.RcAsanFPLib.fl_bytes;
      [exact Hl | exact MU | intros x Hx; apply OW; right; lia]. }
  assert (Kq : forall off v, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.q64 mem3 (A + off) v -> 0 <= off -> off + 8 <= 416 ->
                 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.q64 mem' (A + off) v).
  { intros off v Hq Ho0 Ho1. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.q64 in *. apply Kbh; [exact Hq | lia]. }
  assert (Ksp : forall off v, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.spill regs3 mem3 off v -> 0 <= off -> off + 8 <= 416 ->
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.spill (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR ra' (Z_to_bv 64 sp) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 3)
                     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 4) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 5) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 6)
                     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 7) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 8) (Z_to_bv 64 A)
                     (Z_to_bv 64 (if OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcModel.blocksum (A.Prog.SlotModel.t_blk (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) j) =? 0
                                  then 0 else -1))
                     d1 d2 d3 d4 d5 d6 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 17)
                     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 18) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 19) (Z_to_bv 64 (phi + 18))
                     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 21) (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 phi)
                     (Z_to_bv 64 (A.Prog.SlotModel.t_k (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) j)) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 25)
                     (Z_to_bv 64 A.AsanRT.ASAN_K) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 27) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 28)
                     (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 29) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 30) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regs3 31))
                   mem' off v).
  { intros off v Hs Ho0 Ho1. exists A. split; [reflexivity|].
    apply Kq; [exact (spill_q64 regs3 mem3 A off v Hr9 HA0 HA64 Ho0 Ho1 Hs) | lia | lia]. }
  change (A.Reusable.YK11.seg_rom A.Img0.rsegs) with (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.seg_rom segs).
  rewrite <- A.ProgBridge.cfg_at_MS.
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 _ mem' md2 HB).
  - (* the journal: the head materializes the model, the call writes [sp - 16, sp) *)
    eapply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => sp - 16 <= a < sp).
    + eapply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [ exact HJ | intros x _; reflexivity | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.mem_grows_refl
        | intros x _; reflexivity | exact Hsbm1 | intros a Ha; destruct Ha ].
    + (* memory equal outside the window *)
      intros x Hx. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.mrestrict.
      destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.w_H W3 x) eqn:EH; [reflexivity|].
      assert (Ho : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(sp - 16, sp)] (bv_unsigned x))
        by (cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]; split; [exact Hx | exact I]).
      rewrite (MU x Ho). reflexivity.
    + (* mem_grows: the window's bytes are present after the write (the callee's stk post) *)
      intros x Hx. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.mrestrict in *.
      destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.w_H W3 x) eqn:EH; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (sp - 16)) as [Hd|Hd].
      { assert (Ho : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(sp - 16, sp)] (bv_unsigned x)) by (apply OW; left; lia).
        rewrite (MU x Ho). exact Hx. }
      destruct (Z_lt_le_dec (bv_unsigned x) sp) as [Hd2|Hd2].
      { destruct ST' as (_ & _ & HST).
        assert (Hinw : sp - 16 <= bv_unsigned x < sp) by lia.
        destruct (HST (bv_unsigned x) Hinw) as (_ & b & Hbm).
        replace (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (bv_unsigned x)) with x in Hbm
          by (unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa; symmetry; apply Z_to_bv_bv_unsigned).
        assert (Hk64 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.kLowMemEnd <= bv_unsigned x)
          by (unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.kLowMemEnd; lia).
        rewrite (mrd_some_mem mem' x b Hk64 Hbm). discriminate. }
      { assert (Ho : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(sp - 16, sp)] (bv_unsigned x)) by (apply OW; right; lia).
        rewrite (MU x Ho). exact Hx. }
    + (* the hidden bytes, from SRr_fevt_hid *)
      exact Hhid.
    + exact Hsbm2.
    + (* every written byte: the stack-window disjunct of awr_byte (YCbq.v:461) *)
      intros a Ha. left. unfold A.ACfn.LLVMF_STK. lia.
  - (* frames: own6 on both cuts *) exact HF.
  - (* the frame law: own6 on both cuts *) exact HL.
  - (* the event bound: the same cut_kmax on both cuts *) exact Hk.
  - (* the exit body, C_A824b4_at (ACtlCutP.v:2558-2578) *)
    cbv beta iota zeta delta [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.ix_cut OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.cut_body OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.C_A824b4_at OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    split; [reflexivity|].
    exists phi.
    split; [exact HPerm|].
    (* FRAC *)
    split.
    { exists A, sp.
      split; [reflexivity|]. split; [exact Hspm|].
      split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.spZ; cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR];
              apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia|].
      split; [exact Hr4|]. split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv; exact Hr8|].
      split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv; reflexivity|].
      split; [exact Hr3|].
      split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv; exact Hr19|].
      split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv; reflexivity|].
      split; [exact Hfrm32|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact HspA|].
      split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.FRAME_BYTES; lia|]. split; [exact HA416|]. split; [exact Hsp4096|].
      split; [unfold A.AsanRT.APPMEM_END; lia|].
      split; [exact (Kq 304 fr Hq304 ltac:(lia) ltac:(lia))|].
      split; [exact (Kq 24 fr Hq24 ltac:(lia) ltac:(lia))|].
      split; [exact (Kq 16 fr Hq16 ltac:(lia) ltac:(lia))|].
      split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.q64 in *; apply Kb; [exact Hqfr|];
              rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8; cbn [Z.of_nat]; lia|].
      split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.q64 in *; apply Kb; [exact Hqfr16|];
              rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8; cbn [Z.of_nat]; lia|].
      split.
      { destruct Hshb as (shb & Hshb1 & Hshb2). exists shb. split; [|exact Hshb2].
        apply Kb; [exact Hshb1|]. rewrite Hshb2.
        unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.FRAME_SHADOW, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.FRAME_BYTES. cbn [Z.to_nat Z.of_nat]. lia. }
      split; [apply Kbh; [exact Hsaved|]; lia|].
      (* the trailer word [fr + 4088, fr + 4096): Hfceil and Hspw put it below the callee window [sp - 16, sp) *)
      unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.q64 in *; apply Kb; [exact Htrail|];
        rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le8; cbn [Z.of_nat]; lia. }
    split; [exact Hn26|]. split; [exact Hj255|].
    (* HB *)
    split.
    { split; [exact Hphinz|].
      unfold A.ACtlK.a_size. rewrite Z.max_l by lia.
      exact (A.AsanRTFacts.addressable_kept mem3 mem' phi (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.flen cx j) Hadr MK). }
    (* FLSI *)
    split.
    { destruct HFLSI as (HFLSH & F216 & F224 & F248 & Hf1 & HFLC).
      destruct HFLSH as (HPRO & F128 & Fstk & F144 & Fid17).
      destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg &
        P184 & P256 & P264 & P272 & P32).
      destruct Hf1 as (Hf1a & Hf1b).
      destruct HFLC as (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cfa & Cid & C72 & C64 & C56 & C48).
      split; [split|].
      - (* PRO *)
        split; [apply Ksp; [exact P40 | lia | lia]|].
        split; [apply Ksp; [exact P120 | lia | lia]|].
        split; [apply Ksp; [exact P136 | lia | lia]|].
        split; [apply Ksp; [exact P160 | lia | lia]|].
        split; [apply Ksp; [exact P168 | lia | lia]|].
        split; [apply Ksp; [exact P176 | lia | lia]|].
        split; [apply Ksp; [exact P208 | lia | lia]|].
        split; [apply Ksp; [exact P248 | lia | lia]|].
        split; [exact (A.AsanRTFacts.addressable_kept mem3 mem' _ _ Pad MK)|].
        split; [apply Kb; [exact Pin | lia]|].
        split; [intros Hn; exact (A.AsanRTFacts.addressable_kept mem3 mem' _ _ (Pg Hn) MK)|].
        split; [apply Ksp; [exact P184 | lia | lia]|].
        split; [apply Ksp; [exact P256 | lia | lia]|].
        split; [apply Ksp; [exact P264 | lia | lia]|].
        split; [apply Ksp; [exact P272 | lia | lia]|].
        apply Ksp; [exact P32 | lia | lia].
      - (* the rest of FLSH *)
        split; [apply Ksp; [exact F128 | lia | lia]|].
        split.
        { apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.stk_transport segs [(sp - 16, sp)] mem3 mem' fr (fr + OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.FRAME_BYTES)
                   Fstk MU WM).
          intros x Hx. left. apply OW. left. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.FRAME_BYTES in *. lia. }
        split; [apply Ksp; [exact F144 | lia | lia]|].
        exact (A.AsanRTFacts.addressable_kept mem3 mem' _ _ Fid17 MK).
      - split; [apply Ksp; [exact F216 | lia | lia]|].
        split; [apply Ksp; [exact F224 | lia | lia]|].
        split; [apply Ksp; [exact F248 | lia | lia]|].
        split.
        { split; [exact (A.AsanRTFacts.addressable_kept mem3 mem' _ _ Hf1a MK)|].
          apply Kb; [exact Hf1b | lia]. }
        (* FLC *)
        split; [apply Ksp; [exact C256 | lia | lia]|].
        split; [apply Ksp; [exact C184 | lia | lia]|].
        split; [apply Ksp; [exact C192 | lia | lia]|].
        split; [apply Ksp; [exact C80 | lia | lia]|].
        split; [apply Ksp; [exact C88 | lia | lia]|].
        split; [apply Ksp; [exact C96 | lia | lia]|].
        split; [apply Ksp; [exact C272 | lia | lia]|].
        split; [apply Ksp; [exact C264 | lia | lia]|].
        split; [exact (A.AsanRTFacts.addressable_kept mem3 mem' _ _ Cfa MK)|].
        split; [exact (A.AsanRTFacts.addressable_kept mem3 mem' _ _ Cid MK)|].
        split; [apply Ksp; [exact C72 | lia | lia]|].
        split; [apply Ksp; [exact C64 | lia | lia]|].
        split; [apply Ksp; [exact C56 | lia | lia]|].
        apply Ksp; [exact C48 | lia | lia]. }
    (* LK *)
    split.
    { destruct HLK as (Lj & L21 & LOUR).
      split; [exact Lj|].
      split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv in *; exact L21|].
      unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.OURb in *. apply Kb; [exact LOUR|].
      rewrite A.Prog.SlotModel.OUR_length. cbn [Z.of_nat]. lia. }
    split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv; reflexivity|].
    split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv; reflexivity|].
    split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv; reflexivity|].
    split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv; reflexivity|].
    split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv; reflexivity|].
    split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hflen|]. split; [exact Htk|].
    split; [apply Kb; [exact Hblk|];
            rewrite (A.Prog.Seg.F20.t_blk_len (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) j); cbn [Z.of_nat]; lia|].
    split; [apply Kb; [exact Hrec34|];
            rewrite (A.Prog.Seg.F20.t_g6_len (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) j); cbn [Z.of_nat]; lia|].
    split; [apply Ksp; [exact S280 | lia | lia]|].
    split; [apply Ksp; [exact S136 | lia | lia]|].
    split; [apply Ksp; [exact S120 | lia | lia]|].
    split; [apply Ksp; [exact S176 | lia | lia]|].
    split; [unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.rgv in *; exact R18|].
    split; [apply Ksp; [exact S152 | lia | lia]|].
    split; [apply Kb; [exact Hgb|];
            rewrite (A.Prog.Seg.F20.t_g_len (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) j); cbn [Z.of_nat]; lia|].
    split; [apply Kb; [exact Hpb | lia]|].
    split; [exact Hpl|].
    (* LT = IFS cx fr (S j) *)
    unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.LT, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.IFS, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.IDj, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.FGj, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.FSj,
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.IDb, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.FGb, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.FSb, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.IDBe, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.FGBe in HLT |- *.
    destruct HLT as ((HI & HIok) & (HG & HGok) & (T104 & T112 & Tbody & Tadr & TFI)).
    split; [split; [|exact HIok]|].
    { apply Kb; [exact HI|].
      rewrite (A.Prog.Seg.F20.t_ID_len (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) (S j)). cbn [Z.of_nat]. lia. }
    split; [split; [|exact HGok]|].
    { apply Kb; [exact HG|].
      rewrite (A.Prog.Seg.F20.t_FG_len (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) (S j)). cbn [Z.of_nat]. lia. }
    split; [apply Ksp; [exact T104 | lia | lia]|].
    split; [apply Ksp; [exact T112 | lia | lia]|].
    split.
    { apply Kb; [exact Tbody|].
      pose proof (A.Prog.Seg.F13.fs_body_len (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.c_in cx) (S j)) as Hbl. lia. }
    split; [exact (A.AsanRTFacts.addressable_kept mem3 mem' _ _ Tadr MK) | exact TFI].
  - (* ctl_rt_C across the write, at the entry cut's state ly3 S3 *)
    assert (HshOut : forall x, A.AsanRT.in_shadow x ->
              OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(sp - 16, sp)] x).
    { intros x Hx. apply OW. left.
      unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
        A.AsanRT.HIGHMEM_BEG in Hx.
      lia. }
    split.
    { apply (A.AsanRTFacts.asan_cells_kept [(sp - 16, sp)] mem3 mem' HACl MU).
      cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.disjoint_from]. split; [|exact I].
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI. lia. }
    split.
    { exact (A.ShadowRwOnK.fl_shadow_rw_on _ _ mem3 mem' HCUTl MU WM HshOut). }
    split.
    { exact (A.ShadowRwOnK.fl_shadow_rw_on _ _ mem3 mem' HIMGl MU WM HshOut). }
    (* ro_agree: the write is above the image, where no address is read-only *)
    intros a Ha.
    assert (Hlow : bv_unsigned a < A.Prog.ImgBounds.IMG_HI).
    { destruct (Z_lt_le_dec (bv_unsigned a) A.Prog.ImgBounds.IMG_HI) as [Hd|Hd]; [exact Hd|].
      exfalso.
      pose proof (A.MemNormTr.ro_addr_above_img (bv_unsigned a)
                    (conj Hd (proj2 (bv_unsigned_in_range 64 a)))) as Hro.
      replace (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa (bv_unsigned a)) with a in Hro
        by (unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.wa; symmetry; apply Z_to_bv_bv_unsigned).
      rewrite Ha in Hro. discriminate. }
    assert (Hoa : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(sp - 16, sp)] (bv_unsigned a))
      by (apply OW; left; unfold A.Prog.ImgBounds.IMG_HI in Hlow; lia).
    unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.mrd. rewrite (MU a Hoa).
    exact (HROl a Ha).
Qed.

End GlueF20.

Print Assumptions glue_seg_F20.
