(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 4006 of its 4152 lines of code are new or changed and 2320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4b.v, with its module paths and module names changed; 782 of its 845 lines of code are new or changed and 4089 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F12.v; 350 of its 378 lines of code are new or changed and 817 lines of the source are left out. *)
(* lib/A/ACtlG/A1.v -- GLUE for stage seg_A1 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   W0 prologue: ENTRY -> A80f54).  Written by a Theorem Labs lane; single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery) (steps G1-G5), the worked example lib/A/ACtlG/A5.v.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_A1 : forall POST, (forall cx p, POST (ACtlCut.cx_set_fpos cx p) = POST cx) ->
                   CF POST C_A80f54 -> CF POST C_A80f88 -> CF POST C_ENTRY
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []) and cut names: character for character the
   statement of ACtl.v's Section hypothesis seg_A1 on a working branch shell (a working branch).  Segment A1
   is 0x80edc -> 0x80f54: the prologue stores (sp -= 416, ra and s0..s11 saved at [S - 104, S), sd zero at the new
   sp), the tail (the GOT loads of UAR / CELL_K, the use-after-return switch, s0 = S, s1 = A = (S - 416) & -32,
   a0 = 3136, s7 / s8 = the entry a0 / a1, s10 = ASAN_K), and `jal __asan_stack_malloc_6` at 0x80f50 (ra = 0x80f54).
   The exit C_A80f88 (the `beqz a2` UAR-off edge) is dead: ctl_rt_C's asan_cells pins UAR = 1 (AsanRT.v:81), and
   the run takes the UAR-on edge; that premise is unused.

   BATCH 4 TEXTS (on a working branch shell; they replaced this file's earlier local stand-ins one for one):
     ACtlCut.cx_set_fpos  the context with only c_fpos replaced (B5.2).
     ACtlCutP.C_ENTRY     its body's last conjunct `regs = c_regs cx` (B5.1): the run's sp, gp, saved registers and
                          a0 / a1 come from the entry registers.
     ACtlCutP.PREFC       `c_sp cx <= ART.APPMEM_END` (B5.4): afn_pre's astk_ok gives sp0 <= ly_stk_hi <=
                          kHighMemEnd, nothing gives the strict bound.  This file needs no strict bound
                          (S <= APPMEM_END is a1_pro_Fs's own premise).
     ACtlCutP.C_A80f54 / C_A80f88  the frame's trailer word `q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx))`
                          as their LAST conjunct (B5.3), BORN at A1's request.
   The cx_set_fpos premise: the model's fake-stack request returns its own frame position pos (fs_probe from the
   class-6 hint), which no entry fact ties to c_fpos cx; the exit is taken at cx_set_fpos cx pos, and the premise
   carries POST back to cx.  ctl_base reads no c_fpos, so ctl_base (cx_set_fpos cx pos) is ctl_base cx by
   conversion.

   ROUTE (C) (a Theorem Labs lane truth audit 11:02Z, a Theorem Labs lane 11:10Z; recipe (internal path)
   L3-recipe.md (a working note, not in this delivery)): the cut's runtime conjunct is A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.  At C_ENTRY the top supplies it
   (ACtl.v's CTLRT_ENTRY Let, A.ACtlTopFacts.ctlrt_C_entry); this stage reads only its asan_cells (the four runtime
   cells of the run), never its shadow conjuncts.  At the exit C_A80f54 the frame request is a world step
   (S3 -> S2), so ctl_rt_C B ly3 S2 mem2 comes from A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the request's AR.  VIS0 and
   OWNED_RO are gone.

   THE PROOF (G1-G5 of glue-pattern.md section 3)
   G1  unfold C_ENTRY: the cut's map is c_regs cx (subst); frames S3 = [], k <= 0.
   G2  premises of the composite run A1Fs.a1_pro_Fs (lib/A/Prog/Seg/A1Fs.v, this lane's narrowed re-run of
       A1F's three stretches, each pinned back to A1F by constr_eq): S = c_sp cx with HIGHMEM_BEG <= S - 1 MiB
       (alloc_ceiling >= CEIL_MIN, astk_ok), S <= APPMEM_END, the present window [S - 32768, S) as `stk`
       (KitMem.kitmem_stk_of_journal), the four runtime cells from ctl_rt_C's asan_cells; footprint RNG_W (w_H W3):
       the 14 stores by KitMem.kitmem_rng_win, the cells by ProgBridge.img_vis_W.
   G3  cfg_at_MS, then the walk moved to mkR_of (c_regs cx) (YA0nR.SRr_xregs_eqv), written as the run's explicit
       31-slot map with slot 2 = Z_to_bv 64 S.
   G4  lift: KitMem.kitmem_lift (its continuation receives the fsteps run); the journal across the run by
       a Theorem Labs lane's PROVED ProgWorld.ajournal_of_fsteps (write set [(S - 416, S)], awr_byte by kitmem_awr_win).
   G5a the fake-stack request at ASAN_STACK_MALLOC_6: the core's YCbq.aj_stack_malloc_at at cid 6 (Section d0:
       LAWS, Kit.kit_segs_low, ACeh.tl_env, YG05.model_laws_ok, YG05.stack_malloc_progress), o = A - S, raw =
       0x80f54, frames S3 = [].  Its post is the only outcome: a0 = frame_addr ly3 6 pos (the class-full arm does
       not arise).
   G5b the exit C_A80f54 at cx' = cx_set_fpos cx pos, fr = frame_addr (c_ly cx) 6 pos: journal and frames from
       the rule's post; registers through aregs_preserved and the run's map; the saved registers kept across the
       request by ProgWorld.ctl_post_acall_kept; the input bytes from the entry's garr8 through the journal's block
       clause and ProgWorldVisHeap.heap_vis; their shadow by ctl_block_shadow_of_AR; ctl_rt_C by
       ProgWorldCtlRtC.ctl_rt_C_of_AR (the request is a world step) with the read-only view kept by
       APostBase.arodata_ok_journalP at the empty relro span [0, 0) (only read-only segment bytes are needed:
       ro_agree_at); the trailer word from the request's post (rdword of the view at frame_addr + fs_frame_bytes 6 - 8
       = fr + 4088 is flag_addr, YCbq.v:1764) as lib/Lib's q64 by the local a1_q64_of_rdword (view = mrd at the
       visible frame bytes, ProgWorldVisFrame.frame_vis, and Seg/A1.v's le8_of_bytes), with flag_addr ly3 =
       flag_addr (c_ly cx) by layout_le's ly_F.

   SECTION HYPOTHESES (exact text below)
   - LAWS, TFIB_SYMS, TFIB_LIB: ACtl.v's own Section hypotheses, same names and texts (the top supplies them).
   NOT HYPOTHESES (cited by name): ASM6 (astack_malloc_realizes segs B 6, the frame request's rule) is a Let bound to
   a Theorem Labs lane's PROVED A.Rt.StackMalloc6.disco_stack_malloc6 fx B LAWS TFIB_SYMS (lib/A/Rt/StackMalloc6.v and the
   files it needs, by path from a working branch 055c2ebca7f), so glue_seg_A1's type has no ASM6 premise;
   PC6 is a1_pc6, from TFIB_LIB's tl_code (the interim AF0l keys class 6 at 0x3da58 = ASAN_STACK_MALLOC_6);
   ctl_rt_C_of_AR (ProgWorldCtlRtC.v) and ctl_block_shadow_of_AR (ProgWorldShadow.v: the input block's shadow at the
   exit).

   CLOSURE: every Require is qualified (absolute paths for the modules that have a lib/A/Reusable twin and for
   lib/Lib); no statement names a frame-route identifier.  The closure gains A1Fs.v / A1F.v's (Seg/A1.v, SlotInv,
   Contract, FrameAPI ...: the v1.9 blobs of record, glue-pattern.md section 12a).

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are written FK11.* (the core's YK11, full path) or
   Reusable.YG0d.cfg_at; ctrl's YK11 appears only as CK11.mkFP (the fx of the _Fs run).

   BUILD STATE (honest): type-check on a working branch shell merged on this branch (cb build); the build of
   record is cbrec's (log and .prov named in the commit).  Print Assumptions glue_seg_A1: lib/A/ACtlG/L3W01Audit.v.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI00.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04R.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE01 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.ACfn A.ACeh A.AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.ProgWorldVisHeap A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlRtC A.ProgWorldCtlRtC A.ProgWorldShadow.
(* a Theorem Labs lane's class-6 stack_malloc theorem (discharges ASM6). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Rt.StackMalloc6.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c A.Prog.Seg.A1Fs.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import ListNotations.
Local Open Scope Z_scope.

(* The six twin modules and lib/Lib, by full path (the core's lib/Reusable vs ctrl's lib/A/Reusable). *)
Module FK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module FM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module FO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module FI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module FI04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Module FG05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG05.
Module APB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LFR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LBy := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Bytes.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   The input bytes at a later state: the entry's garr8 over the restricted entry memory, the journal's block clause
   (the view is kept on the block) and the block's visibility give lib/Lib's bytes_at at the later memory. *)
Lemma a1_bytes_of_garr8 : forall {fx : FK11.FPState} {rc : FM05.RunCeil}
    (W W' : Reusable.YA0n.world segs) (mc m2 : word -> option byte) (p : Z) (pl : list byte),
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI00.garr8 segs
    (Reusable.YK04.mrestrict (Reusable.YA0n.w_H W) mc) p (map (fun b : byte => bv_unsigned b) pl) ->
  A.ProgBridge.range_visible (Reusable.YA0n.w_H W') p (Z.of_nat (length pl)) ->
  (forall i, 0 <= i < Z.of_nat (length pl) ->
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W') m2 (p + i) =
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mc (p + i)) ->
  LMem.bytes_at segs m2 p pl.
Proof.
  intros fx rc W W' mc m2 p pl Hg (H0 & H1 & Hv) Hk.
  split; [exact H0|]. split; [exact H1|].
  intros i Hi.
  destruct (nth_error pl i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  assert (Hj : (i < length (map (fun b : byte => bv_unsigned b) pl))%nat) by (rewrite length_map; exact Hi).
  destruct (Hg i Hj) as [Hval _].
  specialize (Hval 0%nat ltac:(lia)).
  assert (En : nth i (map (fun b : byte => bv_unsigned b) pl) 0 = bv_unsigned b).
  { rewrite (nth_indep _ 0 ((fun b : byte => bv_unsigned b) b)) by (rewrite length_map; exact Hi).
    rewrite map_nth. rewrite (nth_error_nth pl i b Eb). reflexivity. }
  rewrite En in Hval. cbn [Z.of_nat] in Hval. rewrite Z.add_0_r in Hval.
  rewrite (FI04.le_byte_small (bv_unsigned b) 1 0) in Hval
    by (pose proof (bv_unsigned_in_range 8 b) as Rb; change (bv_modulus 8) with 256 in Rb; cbn; lia).
  change (8 * Z.of_nat 0) with 0 in Hval.
  rewrite Z.shiftr_0_r, Z_to_bv_bv_unsigned in Hval.
  specialize (Hk (Z.of_nat i) ltac:(lia)).
  unfold Reusable.YG0n.aview at 2 in Hk. rewrite Hval in Hk. cbn [option_map] in Hk.
  rewrite (A.ProgWorld.aview_vis_mrd W' m2 (p + Z.of_nat i) (Hv (p + Z.of_nat i) ltac:(lia))) in Hk.
  unfold LMem.wa.
  change (LMem.mrd A.Img0.rsegs m2 (Z_to_bv 64 (p + Z.of_nat i)) = Some b).
  destruct (LMem.mrd A.Img0.rsegs m2 (Z_to_bv 64 (p + Z.of_nat i))) as [b'|] eqn:E'; cbn [option_map] in Hk;
    [|discriminate Hk].
  injection Hk as Hk. f_equal. apply bv_eq. exact Hk.
Qed.

(* An 8-byte word the core's view reads at a visible address is lib/Lib's q64 there (the view is mrd at a visible
   byte, ProgWorld.aview_vis_mrd; the byte list is le8 of its little-endian value, Seg/A1.v's le8_of_bytes). *)
Lemma a1_q64_of_rdword : forall {fx : FK11.FPState} {rc : FM05.RunCeil}
    (W : Reusable.YA0n.world segs) (m : word -> option byte) (a v : Z),
  A.ProgBridge.range_visible (Reusable.YA0n.w_H W) a 8 ->
  Reusable.YG0d.rdword (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) a = Some v ->
  A.ACtlCutP.q64 m a v.
Proof.
  intros fx rc W m a v (H0 & H1 & Hv) Hr.
  assert (Rb : forall k z, 0 <= k < 8 -> Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + k) = Some z ->
            exists x : byte, LMem.mrd A.Img0.rsegs m (Z_to_bv 64 (a + k)) = Some x /\ z = bv_unsigned x).
  { intros k z Hk Hz. rewrite (A.ProgWorld.aview_vis_mrd W m (a + k) (Hv (a + k) ltac:(lia))) in Hz.
    destruct (LMem.mrd A.Img0.rsegs m (Z_to_bv 64 (a + k))) as [x|]; cbn [option_map] in Hz; [|discriminate Hz].
    injection Hz as <-. exists x. split; reflexivity. }
  unfold Reusable.YG0d.rdword in Hr.
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m a) as [z0|] eqn:E0; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 1)) as [z1|] eqn:E1; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 2)) as [z2|] eqn:E2; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 3)) as [z3|] eqn:E3; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 4)) as [z4|] eqn:E4; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 5)) as [z5|] eqn:E5; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 6)) as [z6|] eqn:E6; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 7)) as [z7|] eqn:E7; [|discriminate Hr].
  injection Hr as <-.
  rewrite <- (Z.add_0_r a) in E0.
  destruct (Rb 0 z0 ltac:(lia) E0) as (x0 & M0 & ->). destruct (Rb 1 z1 ltac:(lia) E1) as (x1 & M1 & ->).
  destruct (Rb 2 z2 ltac:(lia) E2) as (x2 & M2 & ->). destruct (Rb 3 z3 ltac:(lia) E3) as (x3 & M3 & ->).
  destruct (Rb 4 z4 ltac:(lia) E4) as (x4 & M4 & ->). destruct (Rb 5 z5 ltac:(lia) E5) as (x5 & M5 & ->).
  destruct (Rb 6 z6 ltac:(lia) E6) as (x6 & M6 & ->). destruct (Rb 7 z7 ltac:(lia) E7) as (x7 & M7 & ->).
  unfold A.ACtlCutP.q64.
  lazymatch goal with |- context [LMem.le8 (Z_to_bv 64 ?V)] =>
    assert (EL : LMem.le8 (Z_to_bv 64 V) = [x0; x1; x2; x3; x4; x5; x6; x7]);
    [ rewrite <- (A.Prog.Seg.A1.le8_of_bytes [x0; x1; x2; x3; x4; x5; x6; x7] eq_refl); do 2 f_equal;
      rewrite LBy.bytes_le_to_Z_le_val; cbn [LBy.le_val map]; lia
    | rewrite EL ] end.
  split; [exact H0|]. split; [cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  intros i Hi. unfold LMem.wa.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [exact M0 | exact M1 | exact M2 | exact M3 | exact M4 | exact M5 |
    exact M6 | exact M7 | cbn [length] in Hi; lia].
Qed.

Section GlueA1.

(* ACtl.v's Section shape (ACtl.v:172-176), restricted to what this stage uses. *)
Context {fx : FK11.FPState} {rc : FM05.RunCeil} {LS : FO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block and cut names (ACtl.v section 1), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_ENTRY := (ACtlCutP.C_ENTRY B).
Local Notation C_A80f54 := (ACtlCutP.C_A80f54 B).
Local Notation C_A80f88 := (ACtlCutP.C_A80f88 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis TFIB_LIB : A.ACeh.TfibLib B.
(* The class-6 fake-stack request's realizes fact at B: NOT a hypothesis.  a Theorem Labs lane's PROVED
   A.Rt.StackMalloc6.disco_stack_malloc6 (lib/A/Rt/StackMalloc6.v, taken by path from a working branch
   055c2ebca7f; a Theorem Labs lane signed 14:59Z), at this Section's fx, B, LAWS and TFIB_SYMS. *)
Let ASM6 : Reusable.YG0d.astack_malloc_realizes segs B 6 :=
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Rt.StackMalloc6.disco_stack_malloc6 fx B LAWS TFIB_SYMS.
Lemma a1_pc6 :
  Reusable.YG0f.pc_stack_malloc (Reusable.YG0f.as_code B) 6 = A.Prog.asan_stack_malloc_c.ASAN_STACK_MALLOC_6.
Proof. rewrite (A.ACeh.tl_code B TFIB_LIB). vm_compute. reflexivity. Qed.

(* The read-only segments of the image end below the sink head's overflow word (APostBase's ro_below_ofl at the
   empty relro span). *)
Lemma a1_ro_below : APB.ro_below_ofl (SK := A.AE2k.tfib_sink_head) segs 0 0.
Proof.
  intros a [(s & Hs & Hw & Hr) | Hr]; [| lia].
  assert (HB0 : forallb (fun s => seg_writable s ||
                  (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? @FI16.sk_ofl_head A.AE2k.tfib_sink_head)) segs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HB0. specialize (HB0 s Hs). rewrite Hw in HB0. cbn [orb] in HB0.
  apply Z.leb_le in HB0. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_A1 : forall POST, (forall cx p, POST (ACtlCut.cx_set_fpos cx p) = POST cx) -> CF POST C_A80f54 -> CF POST C_A80f88 -> CF POST C_ENTRY.
Proof.
  intros POST Hinv H54 _ cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut (C_ENTRY): the cut's registers are the entry's *)
  cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_ENTRY] in Hbody.
  destruct Hbody as (Hperm & _ & Ereg). subst regs3.
  change (Reusable.YG01.frames S3 = []) in HF.
  change (k <= 0) in Hk.
  pose proof HB as (HPRE & _).
  pose proof HPRE as (HAFN & Hra & Hp & Hn & Hpn & Hnpl & Hgarr & _ & _ & _ & Hrod & _).
  pose proof HAFN as (_ & _ & _ & Hgp & Htp & _).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & Hk0 & _ & _ & _ & _ & _ & _ & Hstat & _ & _).
  pose proof Hstat as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold A.ACfn.LLVMF_STK in Hslo.
  pose proof (@FM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  pose proof (@FM05.alloc_ceiling_lt rc) as Hclt.
  set (S := ACtlCut.c_sp cx) in *.
  assert (HS1 : A.AsanRT.HIGHMEM_BEG <= S - 1048576) by (unfold A.AsanRT.HIGHMEM_BEG; lia).
  assert (HS2 : S <= A.AsanRT.APPMEM_END) by (unfold A.AsanRT.APPMEM_END; lia).
  set (Ab := (S - 416) / 32 * 32).
  assert (HA : Ab mod 32 = 0 /\ S - 447 <= Ab <= S - 416) by (unfold Ab; split; Z.div_mod_to_equations; lia).
  (* the four runtime cells, from ctl_rt_C's asan_cells (its shadow conjuncts are not read) *)
  pose proof Hrt as (HAC & _ & _ & _).
  unfold A.ACtlK.asan_cells_at, A.AsanRT.asan_cells in HAC.
  destruct HAC as (HK & HG2 & _ & _ & _ & HU & HG1 & _).
  (* G2: the footprint *)
  pose (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (Hvis_img : forall lo len, A.Prog.ImgBounds.IMG_LO <= lo -> lo + len <= A.Prog.ImgBounds.IMG_HI ->
            0 <= len -> LEF.rng RNG lo len).
  { intros lo len H1 H2 H3. apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.img_vis_W W3)); lia. }
  assert (RST : LEF.rng RNG (S - 416) 416).
  { eapply A.ACtlG.KitMem.kitmem_rng_win; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  assert (HST : LFR.stk A.Img0.rsegs mem3 (S - 32768) S).
  { eapply A.ACtlG.KitMem.kitmem_stk_of_journal; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  pose proof (A.Prog.Seg.A1Fs.a1_pro_Fs (fx := CK11.mkFP FK11.fp_regs FK11.fp_csr) RNG
    (FK11.getr (ACtlCut.c_regs cx) 1) (FK11.getr (ACtlCut.c_regs cx) 3) (FK11.getr (ACtlCut.c_regs cx) 4)
    (FK11.getr (ACtlCut.c_regs cx) 5) (FK11.getr (ACtlCut.c_regs cx) 6) (FK11.getr (ACtlCut.c_regs cx) 7)
    (FK11.getr (ACtlCut.c_regs cx) 8) (FK11.getr (ACtlCut.c_regs cx) 9) (FK11.getr (ACtlCut.c_regs cx) 10)
    (FK11.getr (ACtlCut.c_regs cx) 11) (FK11.getr (ACtlCut.c_regs cx) 12) (FK11.getr (ACtlCut.c_regs cx) 13)
    (FK11.getr (ACtlCut.c_regs cx) 14) (FK11.getr (ACtlCut.c_regs cx) 15) (FK11.getr (ACtlCut.c_regs cx) 16)
    (FK11.getr (ACtlCut.c_regs cx) 17) (FK11.getr (ACtlCut.c_regs cx) 18) (FK11.getr (ACtlCut.c_regs cx) 19)
    (FK11.getr (ACtlCut.c_regs cx) 20) (FK11.getr (ACtlCut.c_regs cx) 21) (FK11.getr (ACtlCut.c_regs cx) 22)
    (FK11.getr (ACtlCut.c_regs cx) 23) (FK11.getr (ACtlCut.c_regs cx) 24) (FK11.getr (ACtlCut.c_regs cx) 25)
    (FK11.getr (ACtlCut.c_regs cx) 26) (FK11.getr (ACtlCut.c_regs cx) 27) (FK11.getr (ACtlCut.c_regs cx) 28)
    (FK11.getr (ACtlCut.c_regs cx) 29) (FK11.getr (ACtlCut.c_regs cx) 30) (FK11.getr (ACtlCut.c_regs cx) 31)
    mem3 S (S - 32768) HS1 HS2 ltac:(lia) ltac:(lia) HST HG1 HG2 HU HK RST
    (Hvis_img A.AsanRT.GOT_UAR 8 ltac:(unfold A.Prog.ImgBounds.IMG_LO, A.AsanRT.GOT_UAR; lia)
                  ltac:(unfold A.Prog.ImgBounds.IMG_HI, A.AsanRT.GOT_UAR; lia) ltac:(lia))
    (Hvis_img A.AsanRT.GOT_CELL_K 8 ltac:(unfold A.Prog.ImgBounds.IMG_LO, A.AsanRT.GOT_CELL_K; lia)
                  ltac:(unfold A.Prog.ImgBounds.IMG_HI, A.AsanRT.GOT_CELL_K; lia) ltac:(lia))
    (Hvis_img A.AsanRT.UAR 4 ltac:(unfold A.Prog.ImgBounds.IMG_LO, A.AsanRT.UAR; lia)
                  ltac:(unfold A.Prog.ImgBounds.IMG_HI, A.AsanRT.UAR; lia) ltac:(lia))
    (Hvis_img A.AsanRT.CELL_K 8 ltac:(unfold A.Prog.ImgBounds.IMG_LO, A.AsanRT.CELL_K; lia)
                  ltac:(unfold A.Prog.ImgBounds.IMG_HI, A.AsanRT.CELL_K; lia) ltac:(lia))) as HRUN.
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_ENTRY) with 0x80edc.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of (ACtlCut.c_regs cx)) (ACtlCut.c_regs cx) FK11.fp_regs
           (Z_to_bv 64 0x80edc) FK11.fp_csr None mem3 (FK11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv (ACtlCut.c_regs cx)))].
  change (LR6.mkR_of (ACtlCut.c_regs cx)) with
    (LFR.mkR (FK11.getr (ACtlCut.c_regs cx) 1) (FK11.getr (ACtlCut.c_regs cx) 2) (FK11.getr (ACtlCut.c_regs cx) 3)
    (FK11.getr (ACtlCut.c_regs cx) 4) (FK11.getr (ACtlCut.c_regs cx) 5) (FK11.getr (ACtlCut.c_regs cx) 6)
    (FK11.getr (ACtlCut.c_regs cx) 7) (FK11.getr (ACtlCut.c_regs cx) 8) (FK11.getr (ACtlCut.c_regs cx) 9)
    (FK11.getr (ACtlCut.c_regs cx) 10) (FK11.getr (ACtlCut.c_regs cx) 11) (FK11.getr (ACtlCut.c_regs cx) 12)
    (FK11.getr (ACtlCut.c_regs cx) 13) (FK11.getr (ACtlCut.c_regs cx) 14) (FK11.getr (ACtlCut.c_regs cx) 15)
    (FK11.getr (ACtlCut.c_regs cx) 16) (FK11.getr (ACtlCut.c_regs cx) 17) (FK11.getr (ACtlCut.c_regs cx) 18)
    (FK11.getr (ACtlCut.c_regs cx) 19) (FK11.getr (ACtlCut.c_regs cx) 20) (FK11.getr (ACtlCut.c_regs cx) 21)
    (FK11.getr (ACtlCut.c_regs cx) 22) (FK11.getr (ACtlCut.c_regs cx) 23) (FK11.getr (ACtlCut.c_regs cx) 24)
    (FK11.getr (ACtlCut.c_regs cx) 25) (FK11.getr (ACtlCut.c_regs cx) 26) (FK11.getr (ACtlCut.c_regs cx) 27)
    (FK11.getr (ACtlCut.c_regs cx) 28) (FK11.getr (ACtlCut.c_regs cx) 29) (FK11.getr (ACtlCut.c_regs cx) 30)
    (FK11.getr (ACtlCut.c_regs cx) 31)).
  assert (Esp : FK11.getr (ACtlCut.c_regs cx) 2 = Z_to_bv 64 S).
  { unfold S, ACtlCut.c_sp, Reusable.YG0d.spZ. symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite Esp.
  (* G4: the lift; the continuation receives the run's fsteps *)
  apply (A.ACtlG.KitMem.kitmem_lift (fx := fx) A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx) HRUN);
    [exact (A.ProgBridge.fp_avoids_RNG_W _) |].
  intros ms' md' Hfs HP Hsbm.
  destruct HP as (mem' & a1' & a2' & Ems & MU & _ & _ & HSV). subst ms'.
  (* the journal across the run: the 14 stores lie in the LLVMF window *)
  assert (Hawr : forall a, 0 <= a < 2 ^ 64 -> ~ LFR.outside [(S - 416, S)] a ->
            Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK S [] (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx))
              (Reusable.YG0d.ablocks B ly3 S3) ly3 [] a).
  { intros a _ Hno. destruct (A.ACtlG.KitMem.kitmem_not_outside _ _ Hno) as (lo & hi & Hin & Hr).
    destruct Hin as [Ein | []]. injection Ein as <- <-.
    apply A.ACtlG.KitMem.kitmem_awr_win. unfold A.ACfn.LLVMF_STK. lia. }
  assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK S []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  [] ly3 S3 W3 mem' md' k).
  { lazymatch type of Hfs with Reusable.YK04R.fsteps _ _ ?ms0 ?ms1 =>
      exact (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ ms0 ms1 _ _ _ _
               [(S - 416, S)] HJ Hfs (A.ProgBridge.fp_avoids_RNG_W _) MU Hsbm Hawr) end. }
  pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres' & _ & _ & _).
  (* G5a: the fake-stack request (YCbq.aj_stack_malloc_at at cid 6) *)
  rewrite <- a1_pc6.
  lazymatch goal with |- context [LMS.MS ?R _ _ _ _ mem' _] => set (RT := R) end.
  change (Reusable.YA0n.SRr segs W3
            (mkCfg (FK11.mkst RT (Z_to_bv 64 (Reusable.YG0f.pc_stack_malloc (Reusable.YG0f.as_code B) 6)) mem'
                      (FK11.seg_rom segs)) md') (POST cx)).
  assert (ML : Reusable.YG0d.model_laws (Reusable.YG0f.as_universe B))
    by exact (FG05.model_laws_ok _ (A.AF0m.ts_universe B TFIB_SYMS)).
  assert (SMP : Reusable.YCbq.stack_malloc_progressP B)
    by (intros s cid HW Hc Hn0; exact (FG05.stack_malloc_progress _ s cid HW Hc Hn0)).
  assert (U64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z)
    by (intros z Hz; exact (LMem.wa_unsigned z Hz)).
  assert (R2 : FK11.getr RT 2 = Z_to_bv 64 Ab) by reflexivity.
  assert (Hsp : Reusable.YG0d.spZ RT = S + (Ab - S)).
  { unfold Reusable.YG0d.spZ. rewrite R2. rewrite (U64 Ab) by lia. lia. }
  eapply Reusable.YA0n.SRr_bind.
  { apply (Reusable.YCbq.aj_stack_malloc_at (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low
             (A.ACeh.tl_env B TFIB_LIB) ML SMP 6 ASM6 ltac:(lia) W3 RT mem' A.ACfn.LLVMF_STK S []
             (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) [] ly3 S3
             md' k (Ab - S) (Z_to_bv 64 0x80f54) HJ' Hsp).
    - Z.div_mod_to_equations. lia.
    - lia.
    - unfold Reusable.YG0d.ESTACK, A.ACfn.LLVMF_STK. lia.
    - exact Hgp.
    - exact Htp.
    - reflexivity.
    - vm_compute. reflexivity.
    - rewrite HF. vm_compute. reflexivity. }
  intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HPR & Ha0 & Hab & Hfr2 & _ & _ & _ & _ & Hflag &
    Hkept).
  (* G5b: the exit C_A80f54 at cx_set_fpos cx pos *)
  rewrite <- (Hinv cx pos).
  pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & HF2 & _ & _ & _ & _ & _ & _ & _).
  assert (Efr : Reusable.YG0f.frame_addr ly3 6 pos = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 pos)
    by exact (A.ACtlG.KitMem.kitmem_frame_addr_le _ _ _ 6 pos Hly).
  assert (Hin6 : In (6, pos) (Reusable.YG01.frames S2)) by (rewrite Hfr2; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S2 W3 mem2 md2 6 pos HAR2 Hin6) as (Hf4096 & Hfc & _).
  rewrite Efr in Hf4096, Hfc.
  pose proof (Reusable.YCbq.fs_frame_bytes_nonneg 6) as Hfb6.
  (* the frame's trailer word: the request writes flag_addr at frame + fs_frame_bytes 6 - 8 = fr + 4088 *)
  assert (Efl : Reusable.YG0f.flag_addr ly3 6 pos = Reusable.YG0f.flag_addr (ACtlCut.c_ly cx) 6 pos).
  { pose proof Hly as (_ & _ & _ & _ & _ & EF & _). unfold Reusable.YG0f.flag_addr. rewrite EF. reflexivity. }
  assert (HQfl : A.ACtlCutP.q64 mem2 (Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 pos + 4088)
                   (Reusable.YG0f.flag_addr (ACtlCut.c_ly cx) 6 pos)).
  { assert (Hfb : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
    pose proof (proj1 (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S2 W3 mem2 md2 6 pos
       (Reusable.YG0f.frame_addr ly3 6 pos + 4088) 8 HAR2 Hin6 ltac:(lia) ltac:(rewrite Hfb; lia))) as HVf.
    rewrite Hfb in Hflag.
    replace (Reusable.YG0f.frame_addr ly3 6 pos + 4096 - 8) with (Reusable.YG0f.frame_addr ly3 6 pos + 4088)
      in Hflag by lia.
    rewrite <- Efr, <- Efl. exact (a1_q64_of_rdword W3 mem2 _ _ HVf Hflag). }
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A80f54) regs2 mem2 md2)
            (POST (ACtlCut.cx_set_fpos cx pos))).
  apply (H54 (ACtlCut.cx_set_fpos cx pos) [] (Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 pos) k ly3 S2 W3 regs2
           mem2 md2 HB).
  - (* journal: own6 at the new position *)
    exact HJ2.
  - (* frames *)
    rewrite Hfr2, HF. reflexivity.
  - (* the frame law *)
    intros cid pos' [E | []]. injection E as <- <-. reflexivity.
  - (* the event bound *)
    exact Hk.
  - (* the exit body at cx_set_fpos cx pos: its fields are cx's, its frame position is pos *)
    cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_A80f54].
    assert (Xly : ACtlCut.c_ly (ACtlCut.cx_set_fpos cx pos) = ACtlCut.c_ly cx) by reflexivity.
    assert (XS : ACtlCut.c_S (ACtlCut.cx_set_fpos cx pos) = ACtlCut.c_S cx) by reflexivity.
    assert (Xregs : ACtlCut.c_regs (ACtlCut.cx_set_fpos cx pos) = ACtlCut.c_regs cx) by reflexivity.
    assert (Xp : ACtlCut.c_p (ACtlCut.cx_set_fpos cx pos) = ACtlCut.c_p cx) by reflexivity.
    assert (Xn : ACtlCut.c_n (ACtlCut.cx_set_fpos cx pos) = ACtlCut.c_n cx) by reflexivity.
    assert (Xin : ACtlCut.c_in (ACtlCut.cx_set_fpos cx pos) = ACtlCut.c_in cx) by reflexivity.
    assert (Xfp : ACtlCut.c_fpos (ACtlCut.cx_set_fpos cx pos) = pos) by reflexivity.
    assert (Xsp : ACtlCut.c_sp (ACtlCut.cx_set_fpos cx pos) = S) by reflexivity.
    assert (Xsb : A.ACtlCutP.saved_bytes (ACtlCut.cx_set_fpos cx pos) = A.ACtlCutP.saved_bytes cx) by reflexivity.
    rewrite ?Xly, ?XS, ?Xregs, ?Xp, ?Xn, ?Xin, ?Xfp, ?Xsp.
    (* register facts of the exit map: aregs_preserved from the run's map RT *)
    assert (CS : forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27)) ->
                 Reusable.YG0d.acallee_saved r) by (intros r Hr; exact Hr).
    pose proof (HPR 2 (CS 2 ltac:(lia))) as P2. change (FK11.getr regs2 2 = Z_to_bv 64 Ab) in P2.
    pose proof (HPR 3 (CS 3 ltac:(lia))) as P3.
    change (FK11.getr regs2 3 = FK11.getr (ACtlCut.c_regs cx) 3) in P3.
    pose proof (HPR 4 (CS 4 ltac:(lia))) as P4.
    change (FK11.getr regs2 4 = FK11.getr (ACtlCut.c_regs cx) 4) in P4.
    pose proof (HPR 8 (CS 8 ltac:(lia))) as P8. change (FK11.getr regs2 8 = Z_to_bv 64 S) in P8.
    pose proof (HPR 9 (CS 9 ltac:(lia))) as P9. change (FK11.getr regs2 9 = Z_to_bv 64 Ab) in P9.
    pose proof (HPR 23 (CS 23 ltac:(lia))) as P23.
    change (FK11.getr regs2 23 = FK11.getr (ACtlCut.c_regs cx) 10) in P23.
    pose proof (HPR 24 (CS 24 ltac:(lia))) as P24.
    change (FK11.getr regs2 24 = FK11.getr (ACtlCut.c_regs cx) 11) in P24.
    pose proof (HPR 26 (CS 26 ltac:(lia))) as P26.
    change (FK11.getr regs2 26 = Z_to_bv 64 A.AsanRT.ASAN_K) in P26.
    (* the input block *)
    assert (HnN : ACtlCut.c_n cx <= A.ACtlK.ANMAX)
      by (unfold A.ACtlK.ANMAX; destruct Hpn as [(E0 & _) | (E0 & _)]; lia).
    split; [rewrite Hab; exact Hperm|].
    split.
    { unfold ACtlCutP.PREFC. exists Ab, Ab. rewrite ?Xsp, ?Xregs, ?Xn, ?Xsb.
      split; [exact P2|]. split; [Z.div_mod_to_equations; lia|].
      split; [unfold Reusable.YG0d.spZ; rewrite P2; apply U64; lia|].
      split; [rewrite P4; exact Htp|].
      split; [unfold ACtlCut.rgv; exact P8|]. split; [unfold ACtlCut.rgv; exact P9|].
      split; [exact P3|]. split; [unfold ACtlCut.rgv; exact P26|].
      split; [exact (proj1 HA)|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact HS2|].
      split; [|exact HnN].
      (* the saved registers, kept by the request (outside its window [A - ESTACK, A)) *)
      assert (Era : FK11.getr (ACtlCut.c_regs cx) 1 = Z_to_bv 64 A.ACfn.RA_LLVMF).
      { rewrite <- Hra. unfold Reusable.YG0d.raZ. symmetry. apply Z_to_bv_bv_unsigned. }
      rewrite Era in HSV.
      assert (HSV2 : LMem.bytes_at segs mem' (S - 104) (A.ACtlCutP.saved_bytes cx)) by exact HSV.
      apply (A.ACtlG.KitMem.kitmem_bytes_at_mrd mem' mem2 _ _ HSV2).
      rewrite A.ACtlG.KitMem.kitmem_saved_len. intros i Hi.
      assert (Hx : 0 <= S - 104 + i < 2 ^ 64) by lia.
      apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W3 mem' mem2 (S + (Ab - S) - Reusable.YG0d.ESTACK)
               (S + (Ab - S)) (fun _ => False) Hkept (Reusable.YA0n.wle_refl _ W3)).
      + unfold LMem.wa. exact (proj1 (Hpres' (S - 104 + i) ltac:(unfold A.ACfn.LLVMF_STK; lia))).
      + left. rewrite (LMem.wa_unsigned _ Hx). unfold Reusable.YG0d.ESTACK. split; lia. }
    split; [unfold ACtlCut.a0v, ACtlCut.rgv; rewrite <- Efr; exact Ha0|].
    split; [lia|].
    split; [unfold ACtlCut.rgv; rewrite P23; exact Hp|].
    split; [unfold ACtlCut.rgv; rewrite P24; exact Hn|].
    destruct Hpn as [(En & Ep) | (Hn26 & Hin0)].
    + (* the empty input *)
      assert (Ein : ACtlCut.c_in cx = []).
      { destruct (ACtlCut.c_in cx) as [|b l] eqn:Ec; [reflexivity|].
        try rewrite Ec in Hnpl. cbn [length] in Hnpl. lia. }
      split; [rewrite Ein; apply LMem.bytes_at_nil; rewrite Ep; unfold A.ACfn.A_EMPTY; lia|].
      split; [intros Hn0; lia | exact HQfl].
    + (* a live input block of the entry *)
      assert (Hin2 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S2)).
      { rewrite Hab. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hin0. }
      assert (Hrq : 0 < Reusable.YG00.req_size (ACtlCut.c_n cx) /\
                    ACtlCut.c_n cx <= Reusable.YG00.req_size (ACtlCut.c_n cx))
        by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia).
      split.
      * apply (a1_bytes_of_garr8 (ACtlCut.c_W cx) W3 (ACtlCut.c_mem cx) mem2 _ _ Hgarr).
        -- rewrite <- Hnpl.
           exact (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S2 W3 mem2 md2 (ACtlCut.c_p cx) (ACtlCut.c_n cx)
                    (ACtlCut.c_p cx) (ACtlCut.c_n cx) HAR2 Hin2 (Z.le_refl _) ltac:(lia)).
        -- intros i Hi. rewrite <- Hnpl in Hi.
           apply (HF2 _ _ i Hin0 Hin2); [lia|]. apply FI04.inFP_nil.
      * split; [intros _ | exact HQfl].
        exact (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly3 S2 W3 mem2 md2 (ACtlCut.c_p cx) (ACtlCut.c_n cx)
                 (ACtlCut.c_p cx) (ACtlCut.c_n cx)
                 HAR2 Hin2 (Z.le_refl _) ltac:(lia) ltac:(lia)).
  - (* ctl_rt_C after the request (a world step, S3 -> S2): ctl_rt_C_of_AR at the request's AR and the empty relro
       span *)
    apply (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS 0 0 ly3 S2 W3 mem2 md2 HAR2).
    apply (APB.arodata_ok_journalP (SK := A.AE2k.tfib_sink_head) segs 0 0 ltac:(intros a Ha; lia)
             (RO := a1_ro_below) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2).
    intros a Ha Hno Herr. apply Hrod; [| exact Hno | exact Herr].
    destruct Ha as [Ha | Ha]; [left; exact Ha | lia].
Qed.

End GlueA1.
