(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module names and numbers changed; 1086 of its 1232 lines of code are new or changed and 1651 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R7tail.v; 1150 of its 1202 lines of code are new or changed and 1180 lines of the source are left out. *)
(* lib/A/ACtlG/R7.v -- GLUE for stage seg_R7 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:674).
   Written by a Theorem Labs lane (piece W2a); single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery) (worked example lib/A/ACtlG/A5.v).
   rule 24: no function proved (stage glue of a walk; kind: segment lemma).

   WHAT IT PROVES
     glue_seg_R7 : forall POST (b : nat),
       CF POST (ix_cut C_A81640_at [Z.of_nat b]) -> CF POST (ix_cut C_A815cc_at [Z.of_nat (S b)]) ->
       CF POST C_A81ac0 -> CF POST C_A81b10 -> CF POST (ix_cut C_A815ec_at [Z.of_nat b])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R7 (the six twin modules and lib/Lib written fully qualified, brief ruling 1).

   SOURCE OF RECORD: a Theorem Labs lane's fixed Seg/R7.v ff604ad21972 (the blob this tree had at release c5e779efe8c) (a working branch 553cd287ffb; this
   branch's lib/A/Prog/Seg/R7.v differs in comments only) seg_R7 :1143-1157, and Seg/R7tail.v r7_tail_run :1242; the runs' footprint twins
   are a Theorem Labs lane's Seg/R7F.v (r7_evt_F :51, r7_latch_evt_F :138) and Seg/R7tailF.v (r7_tail_evt_F :81).

   THE PROOF: the case split of seg_R7 on n_b = rnb cx b (the build_as result of turn b, in a0 at the cut):
   - n_b <> 0 (r7_arm_malloc): r7_evt_F to the __wrap_malloc entry 0x5337c (ra = 0x81640; one read [A + 64], visible by
     win_vis; lifted with SRr_fevt at RNG_W), the core's malloc rule AMALLOC4 there through SRr_bind (o := sp - c_sp,
     live bytes by blocks_bytes_bsum + the pre's LIVE_LIB, chain / trace by CHAIN_OF_CUT at (pc_malloc_ra0, 0x81640)),
     its continuation the exit C_A81640_at [b] at k + 1: registers by aregs_preserved, the body's memory by
     ProgWorld.ctl_post_acall_kept on the spill window, the class-6 frame and its shadow, and the input block (the new
     block is apart from each by sep_block_frame / sep_blocks at the post state and Free81920.not_in_entry), HB and the
     input block's addressability by ProgWorldShadow.ctl_block_shadow_of_AR (PROVED), ctl_rt_C by
     ProgWorldCtlRtC.ctl_rt_C_of_AR with APostBase.arodata_ok_journalP.  The three validity branches of n_b to the
     abort block 0x82bf4 are refuted inside the run by its premise n_b = 52 + 36 u, 2 <= u <= 40 (Tac_slot.a_rtn_u).
   - n_b = 0, b <= 5 (r7_arm_latch): r7_latch_evt_F to the next turn's head C_A815cc_at [S b] (r7_rid_skip keeps the
     turn's identity / fragment records).  Register-only run, one read [A + 128] = fr + 544 (visible by
     ProgWorldVisWin.win_vis), lifted with YA0nR.SRr_fevt at ProgBridge.RNG_W (w_H W3); journal by ajournal_exec
     over the empty write set; memory, frames, frame law, k and ctl_rt_C unchanged.
   - n_b = 0, b = 6 (r7_arm_tail, drafted by a Theorem Labs lane): r7_tail_evt_F (0x815ec -> 0x81b10; the 14 frame-shadow
     stores of 0xf8 and __asan_set_shadow_f8, lifted straight: its contract_F by the PROVED
     asan_set_shadowF.asan_set_shadow_f8_holds_F memset.memset_holds) to the exit C_A81b10.  The run takes mem_inv,
     which the cut does not carry, so it runs on MemNorm.normalize mem3 and MemNormF.evtF_normalize_ro brings it back
     (as a Theorem Labs lane's P1_70.v); lifted with YA0nR.SRr_fsteps at RNG_W (w_H W3) (every footprint range visible: win_vis
     for the spills and the callee window, al_frames for the frame bytes and frame shadow, img_vis_W for the
     catalogue row and the image, the row's shadow bytes by AR_zshadow_law at CAT_ZSH); the journal by
     ProgWorld.ajournal_of_fsteps (the only bytes written are the frame shadow [Sfr fr + 68, Sfr fr + 291), awr_byte's
     frame case); the catalogue row's bytes from the entry pre's arodata_okS carried by the journal's image clause
     (RELRO_IMG, RELRO_CAT).  The exit C_A81ac0 is not reached on this arm (the run's row check takes 0x81a7c's
     branch to 0x81ac8), as in r7_tail_run.  Route (C): the two frame-shadow runs the tail writes are writable cells by
     r7t_sh_rw_on from ctl_rt_C's cut_shadow, (F) disjunct of the owned class-6 frame (r7t_frsh_cut); the run's post
     carries any shadow region across it (r7t_srw_keep_on, ShadowRwOnT normalize / of_rel), so the exit's ctl_rt_C at
     the same ly3 S3 keeps cut_shadow and img_shadow, and the frame shadow after the run is read from cut_shadow.

   SECTION HYPOTHESES (exact text below):
   - LAWS, TFIB_SYMS, RELRO_IMG, CHAIN_OF_CUT: ACtl.v's own (ACtl.v:185, :193, :181, :436-456; CHAIN_OF_CUT verbatim
     with lib/Lib's Mem as LMem and the cut-layer names qualified).
   - AMALLOC4 / MO_MALLOC_OK: the core's malloc rule amalloc04_rule (YC5d.v:57), taken as the donor walk takes it
     (A/ACfj.v:99-112; the glue brief (a working note, not in this delivery)), and its meter obligation (the same name as a Theorem Labs lane's F1.v).  ACtl.v has the same
     mo_ok hypothesis MO_MALLOC_OK (ACtl.v:291) and one more, MT_FREE (ACtl.v:287), besides MO_LE (ACtl.v:251): its top fixes MT := YCbp.ameter_triv, whose mo_ok is True.
   - Route (C): VIS0 / OWNED_RO are gone; the malloc exit's ctl_rt_C is ProgWorldCtlRtC.ctl_rt_C_of_AR, which takes
     neither.
   - RELRO_CAT: ACtl.v's own (ACtl.v:205, Batch3), same text: RLO <= SlotModel.CAT /\ SlotModel.CAT + SlotModel.CAT_N
     * SlotModel.CAT_ROW <= RHI.  The pointwise form the tail arm reads (each catalogue byte in [RLO, RHI), outside
     the owned statics and errno) is the local lemma r7t_cat_ro (ts_owned / ts_errno and computation over AF0m's
     concrete lists).
   PROVED here, no longer Section hypotheses: CAT_ZSH (the catalogue is a zero-shadow row of the bundle, In (0x9e800,
   0x9f4b8 - 0x9e800) (as_zero_shadow B)), from TFIB_SYMS ts_zsh and a computed check over the branch's AF0m (interim
   zero-stand-in base 5da74c9c931, lib/A/AF0m.v:2963; the record AF0m e56483f863b has the same row at :2963); and the
   block-shadow fact after the malloc, a Theorem Labs lane's PROVED ProgWorldShadow.ctl_block_shadow_of_AR.

   START-UP TABLE VALUES READ (a Theorem Labs lane 05:52Z check against the record AF0m e56483f863b): TFIB_SYMS.ts_code
   (pc_wrap_malloc = 0x5337c; the same on the record, AF0l.v:10); ts_owned / ts_errno with AF0m's Tfib_owned_static
   and TFIB_ERRNO (r7t_cat_ro: no row meets [0x9e800, 0x9f4b8), errno 0x5db76c; the same on the record); ts_zsh with
   AF0m's Tfib_zero_shadow, ONLY its row (0x9e800, 0x9f4b8 - 0x9e800) (CAT_ZSH; the same row on the record, so the
   ts_zsh CAVEAT of the planning core's coarse row does not apply); ProgWorldCtlRtC.ctl_rt_C_of_AR (a Theorem Labs lane's proof over
   ts_const rows).

   FRAC RE-ESTABLISHED AT A NEW MEMORY: r7m_frac_mem (after the malloc) and the exit FRAC step of r7_arm_tail (after
   the frame-shadow writes); both walk FRAC's conjuncts generically, so the trailer q64 (fr + 4088) (Batch3), a frame
   byte off every write, is kept with no edit (built on Batch3).  The latch arm moves FRAC only along
   registers (Kit.kit_frac_move, the same memory).

   CLOSURE: every project Require is qualified; 491 files, measured from this file's Requires; no lib/AZ/AsanW, no W6
   but lib/A/W6/QSlot.v, no cut-free file; lib/AZ files: LibA/AcctCore (via Lib/ExecF), Spec/AsanCtrl,
   Spec/AsanCtrlProps, Spec/STree.  Frame-route blobs: in the commit message.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at only as Y11.* (the core's lib/Reusable/YK11) / Reusable.YG0d.*.

   BUILD STATE: see the commit message (type-check on the interim no-stand-in base, no workspace substitution). *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.AF0m A.Img0 A.AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.ACtlRtC A.RoAdapt.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R7 A.Prog.Seg.R7F A.Prog.Seg.R7tailF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AsanRTFacts A.Prog.CtrlBase A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.Tac_slot A.Prog.Seg.Tac_rt2_b2 A.Prog.Seg.R7tail.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.KitMem A.ACtlG.Free81920.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldShadow.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisFrame A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.MemNorm A.MemNormF A.MemNormTr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_set_shadow_cF A.Prog.asan_set_shadowF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.memset.
Import ListNotations.
Local Open Scope Z_scope.

Module Y11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module Y1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LR6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module SMo := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module R7T := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R7tail.
Module R7TF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R7tailF.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

Section GlueR7.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : Y11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :233-235, :249, :251), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
(* ACtl.v's local notations (ACtl.v:380, :387-389), verbatim, so that CHAIN_OF_CUT below is ACtl.v's text. *)
Local Notation ctlcx := ACtlCut.ctlcx.
Local Notation c_md := ACtlCut.c_md.
Local Notation c_mem := ACtlCut.c_mem.
Local Notation CB cx := (ACtlCut.ctl_base B MT XM_LIB RLO RHI cx).
Local Notation C_A815cc_at := (ACtlCutP.C_A815cc_at B).
Local Notation C_A815ec_at := (ACtlCutP.C_A815ec_at B).
Local Notation C_A81640_at := (ACtlCutP.C_A81640_at B).
Local Notation C_A81ac0 := (ACtlCutP.C_A81ac0 B).
Local Notation C_A81b10 := (ACtlCutP.C_A81b10 B).

(* The entry cut C_A815ec_at at turn b, unfolded once (ACtlCut.ctl_from's premises at ix_cut [Z.of_nat b], with
   own6 and kmax 2b), under an extra guard G on the context: each arm of the stage proves one guard. *)
Definition R7_ENTRY (POST : ACtlCut.ctlcx -> Reusable.YA0n.world segs -> config -> Prop) (b : nat)
    (G : ACtlCut.ctlcx -> Prop) : Prop :=
  forall (cx : ACtlCut.ctlcx) (fr k : Z) ly3 S3 W3 (regs3 : bvmap 5 word) (mem3 : word -> option byte) md3,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx)
    ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  k <= 2 * Z.of_nat b ->
  ACtlCut.cut_body C_A815ec_at cx [Z.of_nat b] (Reusable.YG0d.ablocks B ly3 S3) fr fr regs3 mem3 ->
  A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
  G cx ->
  Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x815ec regs3 mem3 md3) (POST cx).

(* A spill read off register 9 is the q64 at the base the cut pins in register 9 (the spill's own base agrees with
   it modulo 2 ^ 64, and the q64's byte range is in [0, 2 ^ 64)). *)
Lemma r7g_spill_q64 : forall (regs : bvmap 5 word) (m : word -> option byte) (A off v : Z),
  ACtlCut.rgv regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m A off v HA H0 Hoff Hhi (A1 & HA1 & Hq).
  assert (EA : A1 = A).
  { unfold ACtlCut.rgv in HA1, HA. rewrite HA in HA1.
    pose proof Hq as (Hq0 & Hq1 & _). rewrite LMem.length_le8 in Hq1.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hq1.
    apply (f_equal bv_unsigned) in HA1. rewrite !Z_to_bv_unsigned in HA1. unfold bv_wrap in HA1.
    change (bv_modulus 64) with (2 ^ 64) in HA1. Z.div_mod_to_equations. lia. }
  subst A1. exact Hq.
Qed.

(* The section hypotheses this file takes (sources in the header). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The latch arm, n_b = 0 and b <= 5 (Seg/R7.v seg_R7_latch :1038): r7_latch_evt_F (0x815ec -> 0x8194c -> 0x815cc,
   one access: the 8-byte spill [A + 128] = fr + 544, R7F.v:137) to the next turn's head C_A815cc_at [S b]. *)
Lemma r7_arm_latch : forall POST (b : nat), (b <= 5)%nat -> CF POST (ix_cut C_A815cc_at [Z.of_nat (S b)]) ->
  R7_ENTRY POST b (fun cx => ACtlCutP.rnb cx b = 0).
Proof.
  intros POST b Hb5 HX cx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hb Hrt Hz.
  (* G1: the entry body at [Z.of_nat b] (ACtlCutP.v:1300-1323) *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A815ec_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HP & HFRAC & A & Hcn & Hb6 & Hrnb & Hasz & HA & R9 & R24 & Ha0 & Q64 & S128 & HID & HFG & HRTF &
    R23 & Hour & Hout & Hcur & S112 & HPRO & S104 & S96 & S144 & S192 & Hidb & Hjk72 & S280 & S240 & Hjy & Hjk32 &
    S152 & R21 & Had & HRXS).
  (* G2: the spill base A is FRAC's (both are register 9), so [A, A + 416) is in the stack window *)
  pose proof HFRAC as (Af & sp & Esp & Hsp16 & EspZ & _ & _ & R9f & _ & _ & _ & _ & _ & HAS & HspA & HfrA & HA416 &
    HSsp & HSapp & _).
  unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *.
  assert (Hsp0 : 0 <= sp).
  { rewrite <- EspZ. unfold Reusable.YG0d.spZ. pose proof (bv_unsigned_in_range 64 (Y11.getr regs3 2)) as Rg.
    unfold bv_modulus in Rg. lia. }
  assert (EA : Af = A).
  { unfold ACtlCut.rgv in R9, R9f. rewrite R9 in R9f.
    apply (f_equal bv_unsigned) in R9f. rewrite !Z_to_bv_unsigned in R9f. unfold bv_wrap in R9f.
    change (bv_modulus 64) with (2 ^ 64) in R9f. Z.div_mod_to_equations. lia. }
  subst Af.
  pose proof (r7g_spill_q64 regs3 mem3 A 128 (fr + 544) R9 ltac:(lia) ltac:(lia) ltac:(lia) S128) as Q128.
  assert (V128 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (A + 128) 8).
  { apply (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ W3 mem3 md3 k
             (A + 128) 8 HJ); unfold A.ACfn.LLVMF_STK; lia. }
  (* G3: the cut's configuration in the run's state form, the walk moved to the canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 Y11.fp_regs
           (Z_to_bv 64 0x815ec) Y11.fp_csr None mem3 (Y11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  unfold LR6.mkR_of.
  (* G4: the lift at RNG_W (w_H W3); the run reads only [A + 128] *)
  assert (Hbz : 0 <= Z.of_nat b <= 5) by lia.
  eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3
            (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF.
    apply (A.Prog.Seg.R7F.r7_latch_evt_F _ (Z.of_nat b) Hbz) with (A := A) (V := fr + 544).
    - exact R9.
    - rewrite Hz in Ha0. exact Ha0.
    - exact R23.
    - lia.
    - lia.
    - exact (A.Prog.Seg.R7.r7_q64_ro _ _ _ Q128).
    - exact (A.ProgBridge.rng_of_visible _ _ _ V128). }
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* G5: the end state, 0x815cc, the same memory, the run's explicit end map RT *)
  intros ms' md' HQ Hsbm.
  destruct HQ as (a1' & a2' & ->).
  match goal with |- context [mkCfg (LMS.MS ?R _ _ _ _ _ _) _] => set (RT := R) end.
  assert (K2 : Y11.getr RT 2 = Y11.getr regs3 2) by reflexivity.
  assert (K3 : Y11.getr RT 3 = Y11.getr regs3 3) by reflexivity.
  assert (K4 : Y11.getr RT 4 = Y11.getr regs3 4) by reflexivity.
  assert (K8 : Y11.getr RT 8 = Y11.getr regs3 8) by reflexivity.
  assert (K9 : Y11.getr RT 9 = Y11.getr regs3 9).
  { transitivity (Z_to_bv 64 A); [reflexivity | symmetry; exact R9]. }
  assert (K19 : Y11.getr RT 19 = Y11.getr regs3 19) by reflexivity.
  assert (K21 : Y11.getr RT 21 = Y11.getr regs3 21) by reflexivity.
  assert (K22 : Y11.getr RT 22 = Y11.getr regs3 22) by reflexivity.
  assert (K24 : Y11.getr RT 24 = Y11.getr regs3 24) by reflexivity.
  assert (K25 : Y11.getr RT 25 = Y11.getr regs3 25) by reflexivity.
  assert (K26 : Y11.getr RT 26 = Y11.getr regs3 26) by reflexivity.
  assert (K10 : Y11.getr RT 10 = Z_to_bv 64 (fr + 544)) by reflexivity.
  assert (K23 : Y11.getr RT 23 = Z_to_bv 64 (Z.of_nat b + 1)) by reflexivity.
  change (Reusable.YA0n.SRr segs W3
    (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A815cc_at [Z.of_nat (S b)])) RT mem3 md') (POST cx)).
  assert (Hsp : forall off v, ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill RT mem3 off v).
  { intros off v (Ab & HAb & Hq). exists Ab. split; [|exact Hq]. unfold ACtlCut.rgv in *. rewrite K9. exact HAb. }
  apply (HX cx [Z.of_nat (S b)] fr k ly3 S3 W3 RT mem3 md' HB).
  - (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643, as A5.v) *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply Y1b.mem_grows_refl | intros x _; reflexivity | exact Hsbm
      | intros a Ha; destruct Ha].
  - exact HF.
  - exact HL.
  - (* the event bound: kmax 2 (S b) >= 2 b *)
    cbv beta iota delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A815cc_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id. lia.
  - (* the next turn's head C_A815cc_at [S b] (ACtlCutP.v:1276-1296) *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A815cc_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    split; [reflexivity|].
    split; [exact HP|].
    split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 RT mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
    split; [exact Hcn|].
    split.
    { (* RS at S b: n_b = 0 keeps the turn's identity and fragment records (Seg/R7.v r7_rid_skip :250) *)
      destruct (A.Prog.Seg.R7.r7_rid_skip (ACtlCut.c_in cx) b Hz) as (EID & EFG).
      unfold ACtlCutP.RS, ACtlCutP.RB.
      split; [lia|].
      split; [unfold ACtlCutP.CUR, ACtlCut.rgv in *; rewrite K22, K25; exact Hcur|].
      split; [exact Hour|].
      split; [unfold ACtlCut.rgv; rewrite K23; f_equal; lia|].
      unfold ACtlCutP.IDBr, ACtlCutP.FGBr in *. rewrite EID, EFG. split; [exact HID | exact HFG]. }
    split; [exact Hout|].
    split; [exact (Hsp _ _ S128)|].
    split; [unfold ACtlCutP.PRO, ACtlCutP.spill, ACtlCut.rgv in HPRO |- *; rewrite K9; exact HPRO|].
    split; [exact (Hsp _ _ S104)|]. split; [exact (Hsp _ _ S96)|].
    split; [unfold ACtlCut.a0v, ACtlCut.rgv; exact K10|].
    split; [unfold ACtlCut.rgv in *; rewrite K24; exact R24|].
    split; [exists A; split; [unfold ACtlCut.rgv in *; rewrite K9; exact R9 | exact Q64]|].
    split; [exact (Hsp _ _ S112)|].
    split; [unfold ACtlCut.rgv in *; rewrite K21; exact R21|].
    split; [exact (Hsp _ _ S152)|].
    split; [exact (Hsp _ _ S144)|].
    split; [exact Had|].
    split; [exact (Hsp _ _ S192)|].
    split; [exact Hidb|]. split; [exact Hjk72|].
    split; [exact (Hsp _ _ S280)|]. split; [exact (Hsp _ _ S240)|].
    split; [exact Hjy|]. split; [exact Hjk32|].
    unfold ACtlCutP.RXS, ACtlCutP.spill, ACtlCut.rgv in HRXS |- *. rewrite K9. exact HRXS.
  - (* ctl_rt_C: the state and the memory are the entry cut's *)
    exact Hrt.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The malloc arm's Section hypotheses (sources in the header). *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
Hypothesis CHAIN_OF_CUT : forall (FP : list (Z * Z)) (cx : ctlcx) own ly3 S3 W3 mem3 md3 k (regsT : bvmap 5 word)
    (pc0 ra : Z),
  CB cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regsT 8 = Z_to_bv 64 (ACtlCut.c_sp cx) ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 ra ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104)
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 27) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 26) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 25) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 24) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 23) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 22) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 21) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 20) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 19) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 18) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 9) ++ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 8) ++
     OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.le8 (Z_to_bv 64 A.ACfn.RA_LLVMF)) ->
  ACtlCut.c_sp cx - 4096 < Reusable.YG0d.spZ regsT -> Reusable.YG0d.spZ regsT + 416 <= ACtlCut.c_sp cx ->
  In (pc0, ra) [(Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81640);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x81924);
                (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B), 0x81da4);
                (Reusable.YG0f.pc_free_ra0 (Reusable.YG0f.as_code B), 0x82940)] ->
  exists ch, ACtlCut.ctl_chain ly3 W3 mem3 regsT ch /\ ACtlCut.ctl_trace_in B pc0 regsT ch.
Hypothesis AMALLOC4 : Reusable.YC5d.amalloc04_rule (SK := A.AE2k.tfib_sink_head) segs B MT.
Hypothesis MO_MALLOC_OK : forall (S : Reusable.YG00.astate) (n : Z), Reusable.YC5d.mo_ok MT S (Reusable.YC5d.mo_malloc MT n).

(* ---------------------------------------------------------------------------------------------------------
   The malloc arm's local lemmas. *)

(* Walk a conjunction H and the goal's conjunction of the same shape in lock step, closing each goal conjunct with
   tac applied to the matching conjunct of H.  The record's conjunct count is never named. *)
Ltac r7m_peel H tac :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "Hc" in destruct H as [H1 H]; split; [tac H1 | r7m_peel H tac]
  | _ => tac H
  end.

(* Find the conjunct of H that is the goal (the conjunct count is never named). *)
Ltac r7m_find H :=
  first [ exact H
        | let H1 := fresh "Hq" in let H2 := fresh "Hr" in
          destruct H as [H1 H2]; first [ exact H1 | r7m_find H2 ] ].

(* FRAC's memory conjuncts move to a memory that keeps mrd on the spill window [spZ regs, c_sp cx), on the class-6
   frame [fr, fr + 4096) and on its shadow [Sfr fr, Sfr fr + 512).  The conjuncts are walked generically: a spill
   q64 or the saved registers by the window, a frame q64 (the header words and the announced trailer q64 at
   fr + 4088) by the frame, the frame shadow bytes by the shadow, every register or arithmetic conjunct as is. *)
Lemma r7m_frac_mem : forall cx fr sel (regs : bvmap 5 word) (m m' : word -> option byte),
  ACtlCutP.FRAC B cx fr sel regs m ->
  (forall a, Reusable.YG0d.spZ regs <= a < ACtlCut.c_sp cx ->
     LMem.mrd A.Img0.rsegs m' (LMem.wa a) = LMem.mrd A.Img0.rsegs m (LMem.wa a)) ->
  (forall a, fr <= a < fr + 4096 ->
     LMem.mrd A.Img0.rsegs m' (LMem.wa a) = LMem.mrd A.Img0.rsegs m (LMem.wa a)) ->
  (forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
     LMem.mrd A.Img0.rsegs m' (LMem.wa a) = LMem.mrd A.Img0.rsegs m (LMem.wa a)) ->
  ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros cx fr sel regs m m' HF KS KF KH.
  unfold ACtlCutP.FRAC in HF |- *. destruct HF as (A & sp & HF).
  pose proof HF as (_ & _ & EspZ & _ & _ & _ & _ & _ & _ & _ & _ & HAS & HspA & HfrA & HA416 & HSsp & HSapp & _).
  unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *.
  assert (L8 : forall w : word, length (LMem.le8 w) = 8%nat) by (intros w; reflexivity).
  assert (MSA : forall a bs, sp <= a -> a + Z.of_nat (length bs) <= ACtlCut.c_sp cx ->
            LMem.bytes_at segs m a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs H1 H2 H. apply (A.ACtlG.KitMem.kitmem_bytes_at_mrd m m' a bs H). intros i Hi. apply KS. rewrite EspZ. lia. }
  assert (MF : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
            LMem.bytes_at segs m a bs -> LMem.bytes_at segs m' a bs).
  { intros a bs H1 H2 H. apply (A.ACtlG.KitMem.kitmem_bytes_at_mrd m m' a bs H). intros i Hi. apply KF. lia. }
  assert (MH : forall bs, Z.of_nat (length bs) <= 512 ->
            LMem.bytes_at segs m (ACtlCutP.Sfr fr) bs -> LMem.bytes_at segs m' (ACtlCutP.Sfr fr) bs).
  { intros bs H1 H. apply (A.ACtlG.KitMem.kitmem_bytes_at_mrd m m' _ bs H). intros i Hi. apply KH. lia. }
  exists A, sp.
  unfold ACtlCutP.q64 in *.
  r7m_peel HF ltac:(fun H =>
    first [ exact H
          | apply MSA; [lia | rewrite L8; lia | exact H]
          | apply MF; [lia | rewrite L8; lia | exact H]
          | (let sh := fresh "sh" in let Hsh := fresh "Hsh" in let Hl := fresh "Hl" in
             destruct H as (sh & Hsh & Hl); exists sh; split; [|exact Hl];
             apply MH; [rewrite Hl; change ACtlCutP.FRAME_SHADOW with 392; rewrite Z2Nat.id by lia; lia | exact Hsh])
          | (apply MSA; [lia | unfold ACtlCutP.saved_bytes; rewrite !length_app, !L8; cbn; lia | exact H]) ]).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The malloc arm, n_b <> 0 (Seg/R7.v seg_R7_malloc :571): r7_evt_F (0x815ec -> 0x5337c, R7F.v:51), the core's
   malloc rule at __wrap_malloc, the exit cut C_A81640_at [b] at ra = 0x81640. *)
Lemma r7_arm_malloc : forall POST (b : nat), CF POST (ix_cut C_A81640_at [Z.of_nat b]) ->
  R7_ENTRY POST b (fun cx => ACtlCutP.rnb cx b <> 0).
Proof.
  intros POST b HX cx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hb Hrt Hnz.
  (* G1: the entry body at [Z.of_nat b] (ACtlCutP.v:1300-1323) *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A815ec_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HP & HFRAC & A & Hcn & Hb6 & Hrnb & Hasz & HA & R9 & R24 & Ha0 & Q64 & S128 & HID & HFG & HRTF &
    R23 & Hour & Hout & Hcur & S112 & HPRO & S104 & S96 & S144 & S192 & Hidb & Hjk72 & S280 & S240 & Hjy & Hjk32 &
    S152 & R21 & Had & HRXS).
  (* the turn's request n_b: 52 + 36 u with 2 <= u <= 40, 124 <= n_b <= 1492, |rt_F| = n_b *)
  pose proof (A.Prog.Seg.Tac_slot.a_rtn_u (ACtlCut.c_in cx) (Z.of_nat b) Hnz) as Hu.
  destruct (A.Prog.Seg.Tac_rt2_b2.a_rtn (ACtlCut.c_in cx) (Z.of_nat b) Hnz) as (_ & Hn124 & HLF).
  change (A.Prog.SlotModel.rt_n (ACtlCut.c_in cx) (Z.of_nat b)) with (ACtlCutP.rnb cx b) in Hu, Hn124, HLF.
  (* G2: the shell's facts *)
  pose proof HFRAC as (Af & sp & Esp & Hsp16 & EspZ & E4f & R8f & R9f & E3f & R19f & R26f & Hfr32 & HA32 & HAS &
    HspA & HfrA & HA416 & HSsp & HSapp & _).
  assert (Hsaved : LMem.bytes_at segs mem3 (ACtlCut.c_sp cx - 104) (ACtlCutP.saved_bytes cx)).
  { unfold ACtlCutP.FRAC in HFRAC. destruct HFRAC as (A1 & sp1 & HH). r7m_find HH. }
  unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *.
  assert (Hsp0 : 0 <= sp).
  { rewrite <- EspZ. unfold Reusable.YG0d.spZ. pose proof (bv_unsigned_in_range 64 (Y11.getr regs3 2)) as Rg.
    unfold bv_modulus in Rg. lia. }
  assert (EA : Af = A).
  { unfold ACtlCut.rgv in R9, R9f. rewrite R9 in R9f.
    apply (f_equal bv_unsigned) in R9f. rewrite !Z_to_bv_unsigned in R9f. unfold bv_wrap in R9f.
    change (bv_modulus 64) with (2 ^ 64) in R9f. Z.div_mod_to_equations. lia. }
  subst Af.
  (* the entry pre and the journal *)
  pose proof HB as ((HAFN & Hraz & Hp10 & Hn11 & Hpn & Hlen & Hgarr & Hfr0 & Hnev0 & Hlive0 & Hro & Hsink & Hfd &
    Hfs & Hmeta & Hmo) & Hsp1).
  pose proof HAFN as (HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & Hnev3 & Hk03 & _ & _ & _ & _ & _ & Hpres3 & Hstk3 & _ & _).
  pose proof Hstk3 as (Hc16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof (@CM05.alloc_ceiling_lt rc) as Hceil47.
  (* the class-6 frame (glue-pattern.md G2) *)
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) by (apply HL; left; reflexivity).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  assert (Efr3 : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; lia).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR3 Hin6)
    as (Hf4096 & Hfceil & _).
  rewrite Efr3 in Hf4096, Hfceil. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil.
  (* the reciprocal word [A + 64] is in the stack window *)
  assert (V64 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (A + 64) 8).
  { apply (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ W3 mem3 md3 k
             (A + 64) 8 HJ); unfold A.ACfn.LLVMF_STK; lia. }
  (* G3: the cut's configuration in the run's state form, the walk moved to the canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 Y11.fp_regs
           (Z_to_bv 64 0x815ec) Y11.fp_csr None mem3 (Y11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  unfold LR6.mkR_of.
  (* G4: the lift at RNG_W (w_H W3); the run reads only [A + 64] *)
  eapply (Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3
            (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF.
    apply (A.Prog.Seg.R7F.r7_evt_F _) with (A := A) (n := ACtlCutP.rnb cx b).
    - exact R9.
    - exact R24.
    - exact Ha0.
    - exact (A.Prog.Seg.R7.r7_q64_ro _ _ _ Q64).
    - lia.
    - lia.
    - exact Hu.
    - exact (A.ProgBridge.rng_of_visible _ _ _ V64). }
  { exact (A.ProgBridge.fp_avoids_RNG_W _). }
  (* G5: the run's end state, the malloc entry 0x5337c with ra = 0x81640, the same memory, the end map RT *)
  intros ms' md' HQ Hsbm.
  destruct HQ as (a1' & a2' & ->).
  match goal with |- context [mkCfg (LMS.MS ?R _ _ _ _ _ _) _] => set (RT := R) end.
  (* the journal across the run: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643) *)
  assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
  { eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply Y1b.mem_grows_refl | intros x _; reflexivity | exact Hsbm
      | intros a Ha; destruct Ha]. }
  (* the malloc call's chain and call trace (CHAIN_OF_CUT at (pc_malloc_ra0, 0x81640)) *)
  assert (R8T : Y11.getr RT 8 = Z_to_bv 64 (ACtlCut.c_sp cx)) by exact R8f.
  assert (R1T : Y11.getr RT 1 = Z_to_bv 64 0x81640) by reflexivity.
  assert (HspT : Reusable.YG0d.spZ RT = sp) by exact EspZ.
  destruct (CHAIN_OF_CUT [] cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k RT
              (Reusable.YG0f.pc_malloc_ra0 (Reusable.YG0f.as_code B)) 0x81640 HB HJ' R8T R1T Hsaved
              ltac:(rewrite HspT; lia) ltac:(rewrite HspT; lia) ltac:(left; reflexivity)) as (ch & Hch & Htr).
  (* the live bytes: blocks_bytes is the bsum of the live list, a permutation of the entry's *)
  assert (Hlive3 : Reusable.YG01.blocks_bytes S3 + ACtlCutP.rnb cx b <= Reusable.YG01.LIVE_MAX).
  { rewrite (Reusable.YCbq.blocks_bytes_bsum B ly3 S3), (Reusable.YCbq.bsum_perm _ _ HP),
      <- (Reusable.YCbq.blocks_bytes_bsum B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)).
    unfold A.ACfn.LIVE_LIB in Hlive0. unfold Reusable.YG01.LIVE_MAX in *. lia. }
  (* G9.2: the core's malloc rule at the run's end state *)
  assert (Epc : Reusable.YG0f.pc_wrap_malloc (Reusable.YG0f.as_code B) = 0x5337c)
    by (rewrite (A.AF0m.ts_code _ TFIB_SYMS); reflexivity).
  change (Reusable.YA0n.SRr segs W3 (mkCfg (Y11.mkst RT (Z_to_bv 64 0x5337c) mem3 (Y11.seg_rom segs)) md') (POST cx)).
  rewrite <- Epc.
  refine (Reusable.YA0n.SRr_bind segs W3 _ _ (POST cx)
    (AMALLOC4 W3 RT mem3 A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
       (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 md' k (ACtlCutP.rnb cx b) (sp - ACtlCut.c_sp cx)
       (Z_to_bv 64 0x81640) ch HJ'
       ltac:(reflexivity)
       ltac:(unfold Reusable.YG00.MALLOC_MAX; lia)
       Hlive3
       ltac:(rewrite HspT; lia)
       ltac:(rewrite Zminus_mod, Hsp16, Hc16; reflexivity)
       ltac:(lia)
       ltac:(unfold Reusable.YG0d.ASTACK, A.ACfn.LLVMF_STK; lia)
       ltac:(transitivity (Y11.getr (ACtlCut.c_regs cx) 3); [exact E3f | exact Hgp0])
       E4f R1T
       ltac:(vm_compute; reflexivity)
       ltac:(unfold A.ACfn.EV_LIB in Hnev0; lia)
       Hch Htr
       (MO_MALLOC_OK S3 _)) _).
  (* G9.4: the continuation is the exit cut at ra = 0x81640 *)
  intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & res & Ec2 & HJ2 & HPR & Hres & Hfr2 & Hres4096 & Hbl2 & HK & _).
  subst c2.
  pose proof HJ2 as (HAR2 & Hly2 & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
  assert (Efr2 : Reusable.YG0f.frame_addr ly2 6 (ACtlCut.c_fpos cx) = fr)
    by (rewrite Efr; unfold Reusable.YG0f.frame_addr; lia).
  assert (Hin62 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S2)) by (rewrite Hfr2; exact Hin6).
  (* the new block: live at S2, not live at S3 *)
  assert (Hres2 : In (res, ACtlCutP.rnb cx b) (Reusable.YG0d.ablocks B ly2 S2))
    by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res (ACtlCutP.rnb cx b) HAR2 Hres2)
    as (_ & _ & Hresceil & Hresapp & _ & Hpw2 & Hnr).
  assert (Hnot3 : ~ In (res, ACtlCutP.rnb cx b) (Reusable.YG0d.ablocks B ly3 S3)).
  { refine (A.ACtlG.Free81920.not_in_entry (Reusable.YG0d.ablocks B ly2 S2) (Reusable.YG0d.ablocks B ly3 S3)
             (res, ACtlCutP.rnb cx b) _ Hpw2 (proj1 Hnr)).
    rewrite Hbl2. apply Permutation_refl. }
  assert (Hreq : Reusable.YG00.req_size (ACtlCutP.rnb cx b) = ACtlCutP.rnb cx b)
    by (unfold Reusable.YG00.req_size; destruct (Z.eqb_spec (ACtlCutP.rnb cx b) 0); lia).
  (* the callee-saved registers the exit body reads (aregs_preserved; RT keeps them from regs3) *)
  assert (E2 : Y11.getr regs2 2 = Y11.getr regs3 2) by exact (HPR 2 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E3 : Y11.getr regs2 3 = Y11.getr regs3 3) by exact (HPR 3 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E4 : Y11.getr regs2 4 = Y11.getr regs3 4) by exact (HPR 4 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E8 : Y11.getr regs2 8 = Y11.getr regs3 8) by exact (HPR 8 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E9 : Y11.getr regs2 9 = Y11.getr regs3 9).
  { transitivity (Z_to_bv 64 A); [exact (HPR 9 ltac:(unfold Reusable.YG0d.acallee_saved; lia)) | symmetry; exact R9]. }
  assert (E18 : Y11.getr regs2 18 = Z_to_bv 64 (ACtlCutP.rnb cx b))
    by exact (HPR 18 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E19 : Y11.getr regs2 19 = Y11.getr regs3 19) by exact (HPR 19 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E21 : Y11.getr regs2 21 = Y11.getr regs3 21) by exact (HPR 21 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E22 : Y11.getr regs2 22 = Y11.getr regs3 22) by exact (HPR 22 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E23 : Y11.getr regs2 23 = Y11.getr regs3 23) by exact (HPR 23 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E25 : Y11.getr regs2 25 = Y11.getr regs3 25) by exact (HPR 25 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (E26 : Y11.getr regs2 26 = Y11.getr regs3 26) by exact (HPR 26 ltac:(unfold Reusable.YG0d.acallee_saved; lia)).
  assert (HspZ2 : Reusable.YG0d.spZ regs2 = sp) by (unfold Reusable.YG0d.spZ in EspZ |- *; rewrite E2; exact EspZ).
  (* memory kept across the malloc, on every byte the exit body reads (ProgWorld.ctl_post_acall_kept) *)
  assert (KS : forall x : word, sp <= bv_unsigned x < ACtlCut.c_sp cx ->
            LMem.mrd A.Img0.rsegs mem2 x = LMem.mrd A.Img0.rsegs mem3 x).
  { intros x Hx.
    pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
    apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem3 mem2 _ _ _ HK Hwle x).
    - destruct (Hpres3 (bv_unsigned x) ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (Hh & _).
      rewrite Z_to_bv_bv_unsigned in Hh. exact Hh.
    - left. unfold A.ACfn.LLVMF_STK in Hslo. split; [lia|]. lia. }
  assert (KF : forall a, fr <= a < fr + 4096 ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa a) = LMem.mrd A.Img0.rsegs mem3 (LMem.wa a) /\
            mem2 (LMem.wa a) <> None).
  { intros a Ha.
    destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR3 Hin6)
      as (_ & _ & Hfp3 & _).
    destruct (Hfp3 a ltac:(rewrite Efr3; change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia)) as ((Hh & _) & _).
    split.
    - apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem3 mem2 _ _ _ HK Hwle (LMem.wa a) Hh).
      rewrite LMem.wa_unsigned by lia.
      right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
      + left. unfold Reusable.YG0n.in_zr, Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite Efr3.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
      + intros HE. cbv beta in HE.
        pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 res (ACtlCutP.rnb cx b) 6
          (ACtlCut.c_fpos cx) HAR2 Hres2 Hin62) as Hd.
        unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efr2 in Hd.
        change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hd. lia.
    - destruct (Reusable.YG0d.al_frames _ _ LAWS ly2 S2 W2 mem2 md2 6 (ACtlCut.c_fpos cx) HAR2 Hin62)
        as (_ & _ & Hfp2 & _).
      destruct (Hfp2 a ltac:(rewrite Efr2; change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia))
        as ((_ & bb & Hbb) & _).
      unfold LMem.wa. rewrite Hbb. discriminate. }
  assert (KH : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa a) = LMem.mrd A.Img0.rsegs mem3 (LMem.wa a)).
  { intros a Ha. unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Ha.
    destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR3 Hin6)
      as (_ & _ & _ & Hsh3).
    destruct (Hsh3 (a - (fr / 8 + 0x7fff8000)) ltac:(change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512; lia))
      as ((Hh & _) & _).
    assert (Ea : Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)) +
                   (a - (fr / 8 + 0x7fff8000)) = a).
    { rewrite Efr3. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia. }
    rewrite Ea in Hh.
    apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem3 mem2 _ _ _ HK Hwle (LMem.wa a) Hh).
    rewrite LMem.wa_unsigned by lia.
    right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|]. split.
    - right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr3.
      change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia.
    - intros HE. cbv beta in HE.
      unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hresapp.
      lia. }
  assert (KI1 : forall i, 0 <= i < Z.of_nat (length (ACtlCut.c_in cx)) ->
            LMem.mrd A.Img0.rsegs mem2 (LMem.wa (ACtlCut.c_p cx + i)) =
            LMem.mrd A.Img0.rsegs mem3 (LMem.wa (ACtlCut.c_p cx + i))).
  { intros i Hi. rewrite <- Hlen in Hi.
    destruct Hpn as [(Hn0 & _) | (Hnpos & Hinp)]; [lia|].
    assert (Hinp3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym HP)); exact Hinp).
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 Hinp3)
      as (_ & Hp4096 & Hpceil & _ & Hppres & _ & Hcnr).
    pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) (proj1 Hcnr)) as Hreqc.
    destruct (Hppres (ACtlCut.c_p cx + i) ltac:(lia)) as ((Hh & _) & _).
    apply (A.ProgWorld.ctl_post_acall_kept B ly3 S3 W3 W2 mem3 mem2 _ _ _ HK Hwle _ Hh).
    rewrite LMem.wa_unsigned by lia.
    right. left. exists (ACtlCut.c_p cx), (ACtlCut.c_n cx), i.
    split; [exact Hinp3|]. split; [lia|]. split; [reflexivity|].
    intros HE. cbv beta in HE.
    assert (Hne : (ACtlCut.c_p cx, ACtlCut.c_n cx) <> (res, ACtlCutP.rnb cx b))
      by (intros E; rewrite E in Hinp3; exact (Hnot3 Hinp3)).
    assert (Hinp2 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly2 S2))
      by (rewrite Hbl2; apply in_or_app; left; exact Hinp3).
    pose proof (Reusable.YCbq.sep_blocks segs B LAWS ly2 S2 W2 mem2 md2 _ _ _ _ HAR2 Hinp2 Hres2 Hne) as Hd.
    unfold Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KI2 : 0 < ACtlCut.c_n cx -> A.AsanRT.addressable mem2 (ACtlCut.c_p cx) (ACtlCut.c_n cx)).
  { intros Hnpos'. destruct Hpn as [(Hn0 & _) | (Hnpos & Hinp)]; [lia|].
    assert (Hinp2 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly2 S2)).
    { rewrite Hbl2. apply in_or_app. left. apply (Permutation_in _ (Permutation_sym HP)). exact Hinp. }
    pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as Hreqc.
    exact (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2 (ACtlCut.c_p cx) (ACtlCut.c_n cx) (ACtlCut.c_p cx) (ACtlCut.c_n cx)
             HAR2 Hinp2 ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* the movers, one per kind of fact *)
  assert (L8 : forall w : word, length (LMem.le8 w) = 8%nat) by (intros w; reflexivity).
  assert (MSA : forall a bs, sp <= a -> a + Z.of_nat (length bs) <= ACtlCut.c_sp cx ->
            LMem.bytes_at segs mem3 a bs -> LMem.bytes_at segs mem2 a bs).
  { intros a bs H1 H2 H. apply (A.ACtlG.KitMem.kitmem_bytes_at_mrd mem3 mem2 a bs H). intros i Hi. apply KS.
    rewrite LMem.wa_unsigned by lia. lia. }
  assert (MS : forall off v, 0 <= off -> off + 8 <= 416 ->
            ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill regs2 mem2 off v).
  { intros off v Hoff0 Hoff Hs.
    pose proof (r7g_spill_q64 regs3 mem3 A off v R9 ltac:(lia) Hoff0 ltac:(lia) Hs) as Hq.
    exists A. split; [unfold ACtlCut.rgv; rewrite E9; exact R9|].
    unfold ACtlCutP.q64 in *. apply MSA; [lia | rewrite L8; lia | exact Hq]. }
  assert (MF : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + 4096 ->
            LMem.bytes_at segs mem3 a bs -> LMem.bytes_at segs mem2 a bs).
  { intros a bs H1 H2 H. apply (A.ACtlG.KitMem.kitmem_bytes_at_mrd mem3 mem2 a bs H). intros i Hi.
    exact (proj1 (KF (a + i) ltac:(lia))). }
  assert (MC : forall a k junk, fr <= a -> a + Z.of_nat k <= fr + 4096 ->
            LStep.rw_cells segs mem3 a [LCells.CB k junk] -> LStep.rw_cells segs mem2 a [LCells.CB k junk]).
  { intros a k' junk H1 H2 H. apply (A.ACtlG.KitMem.kitmem_rw_cells_mrd mem3 mem2 a _ H). intros i Hi.
    change (LCells.cells_size [LCells.CB k' junk]) with (k' + 0)%nat in Hi. rewrite Nat.add_0_r in Hi.
    exact (KF (a + i) ltac:(lia)). }
  assert (MA : forall p n, fr <= p -> p + n <= fr + 4096 ->
            A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable mem2 p n).
  { intros p n H1 H2 H. apply (A.ACtlG.KitMem.kitmem_addressable_mrd mem3 mem2 p n H). intros i Hi. apply KH.
    unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr. lia. }
  assert (LOUR : length (A.Prog.SlotModel.OUR (ACtlCut.c_in cx)) = 6%nat)
    by (unfold A.Prog.SlotModel.OUR; rewrite length_map, length_seq; reflexivity).
  (* the exit body's memory facts at mem2 *)
  assert (S64 : ACtlCutP.spill regs3 mem3 64 0xe38f0000) by (exists A; split; [exact R9 | exact Q64]).
  assert (HOUR2 : ACtlCutP.OURb cx fr mem2).
  { unfold ACtlCutP.OURb in Hour |- *. apply MF; [lia | rewrite LOUR; lia | exact Hour]. }
  assert (HOUTA2 : ACtlCutP.OUTA fr mem2).
  { unfold ACtlCutP.OUTA in Hout |- *. apply MA; [lia | lia | exact Hout]. }
  assert (HRTF2 : LMem.bytes_at segs mem2 (fr + 544) (A.Prog.SlotModel.rt_F (ACtlCut.c_in cx) (Z.of_nat b))).
  { apply MF; [lia | rewrite HLF, Z2Nat.id by lia; lia | exact (HRTF Hnz)]. }
  assert (HPRO2 : ACtlCutP.PRO cx fr regs2 mem2).
  { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pinad &
      P184 & P256 & P264 & P272 & P32).
    split; [exact (MS 40 _ ltac:(lia) ltac:(lia) P40)|].
    split; [exact (MS 120 _ ltac:(lia) ltac:(lia) P120)|].
    split; [exact (MS 136 _ ltac:(lia) ltac:(lia) P136)|].
    split; [exact (MS 160 _ ltac:(lia) ltac:(lia) P160)|].
    split; [exact (MS 168 _ ltac:(lia) ltac:(lia) P168)|].
    split; [exact (MS 176 _ ltac:(lia) ltac:(lia) P176)|].
    split; [exact (MS 208 _ ltac:(lia) ltac:(lia) P208)|].
    split; [exact (MS 248 _ ltac:(lia) ltac:(lia) P248)|].
    split; [apply MA; [lia | lia | exact Pad]|].
    split; [exact (A.ACtlG.KitMem.kitmem_bytes_at_mrd mem3 mem2 _ _ Pin KI1)|].
    split; [exact KI2|].
    split; [exact (MS 184 _ ltac:(lia) ltac:(lia) P184)|].
    split; [exact (MS 256 _ ltac:(lia) ltac:(lia) P256)|].
    split; [exact (MS 264 _ ltac:(lia) ltac:(lia) P264)|].
    split; [exact (MS 272 _ ltac:(lia) ltac:(lia) P272)|].
    exact (MS 32 _ ltac:(lia) ltac:(lia) P32). }
  (* the exit cut C_A81640_at [b] (ACtlCutP.v:1327-1349) *)
  change (mkCfg (Y11.mkst regs2 (Z_to_bv 64 0x81640) mem2 (Y11.seg_rom segs)) md2)
    with (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A81640_at [Z.of_nat b])) regs2 mem2 md2).
  apply (HX cx [Z.of_nat b] fr (k + 1) ly2 S2 W2 regs2 mem2 md2 HB HJ2).
  - rewrite Hfr2. exact HF.
  - exact HL.
  - (* the event bound: kmax 2 b + 1 >= k + 1 *)
    cbv beta iota delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A81640_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id. lia.
  - cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A81640_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    split; [reflexivity|].
    exists res.
    split; [rewrite Hbl2; apply Permutation_app_tail; exact HP|].
    split.
    { (* FRAC: the registers by Kit.kit_frac_move, the memory by r7m_frac_mem (generic in FRAC's conjuncts) *)
      apply (r7m_frac_mem cx fr fr regs2 mem3 mem2).
      - exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 regs2 mem3 HFRAC E2 E3 E4 E8 E9 E19 E26).
      - intros a Ha. rewrite HspZ2 in Ha. apply KS. rewrite LMem.wa_unsigned by lia. lia.
      - intros a Ha. exact (proj1 (KF a Ha)).
      - exact KH. }
    split.
    { split; [exact Hcn|]. split; [exact Hb6|]. split; [exact Hnz|].
      split; [exact Hres|].
      split.
      { (* HB: the new block is addressable for its served size a_size n_b = n_b (ctl_block_shadow_of_AR at S2) *)
        split; [lia|].
        replace (A.ACtlK.a_size (ACtlCutP.rnb cx b)) with (ACtlCutP.rnb cx b) by (unfold A.ACtlK.a_size; lia).
        exact (A.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS ly2 S2 W2 mem2 md2 res (ACtlCutP.rnb cx b) res (ACtlCutP.rnb cx b) HAR2 Hres2
                 ltac:(lia) ltac:(lia) ltac:(rewrite Hreq; lia)). }
      split; [exact E18|].
      split; [exact (MS 128 _ ltac:(lia) ltac:(lia) S128)|].
      split.
      { unfold ACtlCutP.OUTA in HOUTA2.
        pose proof (A.AsanRTFacts.addressable_sub mem2 (fr + 544) 1492 0 (ACtlCutP.rnb cx b) HOUTA2
                      ltac:(lia) ltac:(lia) ltac:(lia)) as X.
        rewrite Z.add_0_r in X. exact X. }
      split.
      { exists (A.Prog.SlotModel.rt_F (ACtlCut.c_in cx) (Z.of_nat b)). split; [exact HRTF2|].
        rewrite HLF. apply Z2Nat.id. lia. }
      split; [unfold ACtlCut.rgv in R23 |- *; rewrite E23; exact R23|].
      split; [exact HOUR2|].
      split; [exact HOUTA2|].
      split; [unfold ACtlCutP.CUR, ACtlCut.rgv in Hcur |- *; rewrite E22, E25; exact Hcur|].
      split; [exact (MS 112 _ ltac:(lia) ltac:(lia) S112)|].
      split; [exact HPRO2|].
      split; [exact (MS 104 _ ltac:(lia) ltac:(lia) S104)|].
      split; [exact (MS 96 _ ltac:(lia) ltac:(lia) S96)|].
      split; [exact (MS 64 _ ltac:(lia) ltac:(lia) S64)|].
      split; [exact (MS 144 _ ltac:(lia) ltac:(lia) S144)|].
      split; [exact (MS 192 _ ltac:(lia) ltac:(lia) S192)|].
      split; [destruct Hidb as (idb & H); exists idb; apply MC; [lia | lia | exact H]|].
      split; [destruct Hjk72 as (junk & H); exists junk; apply MC; [lia | lia | exact H]|].
      split; [exact (MS 280 _ ltac:(lia) ltac:(lia) S280)|].
      split; [exact (MS 240 _ ltac:(lia) ltac:(lia) S240)|].
      split; [destruct Hjy as (jy & H); exists jy; apply MC; [lia | lia | exact H]|].
      split; [destruct Hjk32 as (junk & H); exists junk; apply MC; [lia | lia | exact H]|].
      split; [exact (MS 152 _ ltac:(lia) ltac:(lia) S152)|].
      split; [unfold ACtlCut.rgv in R21 |- *; rewrite E21; exact R21|].
      apply MA; [lia | lia | exact Had]. }
    (* X81640: the turn-b records and out[]'s n_b bytes are frame bytes, RXS's spills are in the save area *)
    destruct (A.Prog.Seg.R7tail.r7t_RS_len (ACtlCut.c_in cx) b) as (LID & LFG).
    unfold ACtlCutP.X81640. unfold ACtlCutP.IDBr, ACtlCutP.FGBr in HID, HFG |- *.
    split; [apply MF; [lia | rewrite LID; lia | exact HID]|].
    split; [apply MF; [lia | rewrite LFG; lia | exact HFG]|].
    split; [exact HRTF2|].
    destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & Xad).
    split; [exact (MS 48 _ ltac:(lia) ltac:(lia) X48)|].
    split; [exact (MS 56 _ ltac:(lia) ltac:(lia) X56)|].
    split; [exact (MS 88 _ ltac:(lia) ltac:(lia) X88)|].
    split; [exact (MS 80 _ ltac:(lia) ltac:(lia) X80)|].
    split; [exact (MS 72 _ ltac:(lia) ltac:(lia) X72)|].
    split; [exact (MS 8 _ ltac:(lia) ltac:(lia) X8)|].
    split; [exact (MS 0 _ ltac:(lia) ltac:(lia) X0)|].
    split; [exact (MS 200 _ ltac:(lia) ltac:(lia) X200)|].
    split; [exact (MS 216 _ ltac:(lia) ltac:(lia) X216)|].
    apply MA; [lia | lia | exact Xad].
  - (* ctl_rt_C after the malloc: ctl_rt_C_of_AR at the post's AR and the kept read-only view *)
    assert (HRO0 : A.Prog.CtrlBase.arodata_okP segs 0 0 B
                     (Reusable.YG0n.aview segs (Reusable.YA0n.w_H (ACtlCut.c_W cx)) (ACtlCut.c_mem cx))).
    { intros a Ha Ho He. apply Hro; [|exact Ho | exact He].
      destruct Ha as [Ha | Ha]; [left; exact Ha | lia]. }
    pose proof (Reusable.APostBase.arodata_ok_journalP (SK := A.AE2k.tfib_sink_head) segs 0 0
                  (fun a (Ha : 0 <= a < 0) => False_ind _ (ltac:(lia) : False)) (RO := A.ACtlG.Free81920.ro00_below) B
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HRO0) as HRO2.
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS 0 0 ly2 S2 W2 mem2 md2 HAR2 HRO2).
Qed.


(* ---------------------------------------------------------------------------------------------------------
   The tail arm's Section hypotheses (a Theorem Labs lane).  RELRO_IMG is ACtl.v's own (:226), verbatim. *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
(* RELRO_CAT: ACtl.v's own Section hypothesis (ACtl.v:205, Batch3), same text.  The box catalogue SlotModel.CAT
   [0x9e800, +CAT_N * CAT_ROW) is .data.rel.ro in the RW PT_LOAD [0x9e348, 0xa1000), so ro_agree does not cover it;
   its bytes are read through the entry pre's arodata_okS over [RLO, RHI).  The pointwise form the tail arm reads
   (each catalogue byte in [RLO, RHI), outside the bundle's owned statics and errno) is the local lemma r7t_cat_ro:
   the two exclusions by TFIB_SYMS ts_owned / ts_errno and computation over AF0m's concrete lists (the record AF0m
   e56483f863b's Tfib_owned_static, AF0m.v:2965-2981, has the same rows near the table: (0x9e7d0, 0x30) ends and
   (0x9f4b8, 0x328) starts exactly at its bounds; errno 0x5db76c on both). *)
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.

Lemma r7t_cat_ro : forall a, 0x9e800 <= a < 0x9e800 + 3256 ->
  (RLO <= a < RHI) /\ ~ Exists (Reusable.YG0n.in_zr a) (Reusable.YG0f.as_owned_static B) /\
  ~ (Reusable.YG0f.as_errno B <= a < Reusable.YG0f.as_errno B + 4).
Proof.
  intros a Ha.
  split.
  { destruct RELRO_CAT as [Hlo Hhi].
    unfold A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_N, A.Prog.SlotModel.CAT_ROW in Hlo, Hhi. lia. }
  split.
  { rewrite (A.AF0m.ts_owned B TFIB_SYMS). intros Hex.
    assert (Hc : forallb (fun r => (fst r + snd r <=? 0x9e800) || (0x9e800 + 3256 <=? fst r))
                   A.AF0m.Tfib_owned_static = true) by (vm_compute; reflexivity).
    apply Exists_exists in Hex as (r & Hr & Hz). unfold Reusable.YG0n.in_zr in Hz.
    rewrite forallb_forall in Hc. specialize (Hc r Hr).
    apply Bool.orb_prop in Hc as [Hc | Hc]; apply Z.leb_le in Hc; lia. }
  rewrite (A.AF0m.ts_errno B TFIB_SYMS). unfold A.AF0m.TFIB_ERRNO. lia.
Qed.

(* CAT_ZSH: the catalogue is a zero-shadow row of the bundle.  Proved from TFIB_SYMS ts_zsh and a computed check over
   the branch's AF0m Tfib_zero_shadow (the interim zero-stand-in base 5da74c9c931: the row (0x9e800, 0x9f4b8 - 0x9e800)
   at lib/A/AF0m.v:2963, the same row as the record AF0m e56483f863b's AF0m.v:2963). *)
Lemma CAT_ZSH : In (0x9e800, 0x9f4b8 - 0x9e800) (Reusable.YG0f.as_zero_shadow B).
Proof.
  rewrite (A.AF0m.ts_zsh B TFIB_SYMS).
  assert (H : existsb (fun r => (fst r =? 0x9e800) && (snd r =? 0x9f4b8 - 0x9e800)) A.AF0m.Tfib_zero_shadow = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in H as ([x y] & Hin & He). cbn [fst snd] in He.
  apply Bool.andb_true_iff in He as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst x y. exact Hin.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The tail arm's local lemmas. *)

(* An addressable range stays addressable across a munch whose window avoids its shadow bytes. *)
Lemma r7t_addr_keep : forall (W : list LFrame.ivl) (m m' : word -> option byte) p n,
  A.AsanRT.addressable m p n -> LFrame.munch W m m' ->
  (forall i, 0 <= i < n -> LFrame.outside W (A.AsanRT.shadow_addr (p + i))) ->
  A.AsanRT.addressable m' p n.
Proof.
  intros W m m' p n (H0 & H1 & H2 & H) MU HW.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hrd & Hok).
  split; [exact Happ|]. exists b. split; [|exact Hok].
  assert (Hs : 0 <= A.AsanRT.shadow_addr (p + i) < 2 ^ 64).
  { pose proof (A.AsanRTFacts.in_shadow_range _ (A.AsanRTFacts.shadow_of_app _ Happ)) as R. lia. }
  unfold LMem.mrd in *. rewrite (MU (LMem.wa (A.AsanRT.shadow_addr (p + i)))); [exact Hrd|].
  rewrite LMem.wa_unsigned by exact Hs. exact (HW i Hi).
Qed.

(* A shadow region survives a run that keeps every writable byte writable: a shadow byte lies above the image, where
   a writable byte is a present one (R7tail.r7t_wview_hi). *)
Lemma r7t_srw_keep_on : forall (P : Z -> Prop) (m m' : word -> option byte),
  A.ShadowRwOn.shadow_rw_on P m -> LFrame.wmono A.Img0.rsegs m m' -> A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P m m' H WM a Hp Ha. destruct (H a Hp Ha) as [Hv _].
  pose proof (WM _ Hv) as Hv'. split; [exact Hv'|].
  apply (R7T.r7t_wview_hi m' (LMem.wa a)); [|exact Hv'].
  pose proof (A.AsanRTFacts.in_shadow_range a Ha) as R.
  rewrite LMem.wa_unsigned by lia.
  unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
    A.AsanRT.HIGHMEM_BEG in Ha.
  lia.
Qed.

(* Route (C) twin of R7tail.r7t_sh_rw (Seg/R7tail.v:869), the same proof: a run of shadow bytes in a region the
   memory holds shadow_rw_on, present in m, is a writable cell of the normalized memory. *)
Lemma r7t_sh_rw_on : forall (P : Z -> Prop) m a (bs : list byte) n,
  A.MemNorm.ro_agree A.Img0.rsegs m -> LMem.bytes_at A.Img0.rsegs m a bs -> length bs = n ->
  A.ShadowRwOn.shadow_rw_on P m ->
  (forall i, 0 <= i < Z.of_nat n -> P (a + i) /\ A.AsanRT.in_shadow (a + i)) ->
  LStep.rw_cells A.Img0.rsegs (A.MemNorm.normalize A.Img0.rsegs m) a [LCells.CB n bs].
Proof.
  intros P m a bs n Hro Hb L HSW Hin.
  apply (A.RoAdapt.rel_rw_norm m _ a _ (A.MemNorm.mem_rel_normalize A.Img0.rsegs m Hro)).
  - intros i Hi. cbn [LCells.cells_size LCells.csize] in Hi. apply A.RoAdapt.ro_addr_false_shadow. apply Hin. lia.
  - pose proof (LMem.bytes_at_bound A.Img0.rsegs m a bs Hb) as Hbd. rewrite L in Hbd.
    split.
    + split; [split; [exact L | exact I]|]. cbn [LCells.cells_bytes LCells.cbytes]. rewrite app_nil_r. exact Hb.
    + split; [lia|]. split; [cbn [LCells.cells_size LCells.csize]; lia|].
      intros i Hi. cbn [LCells.cells_size LCells.csize] in Hi.
      destruct (Hin i ltac:(lia)) as [HP Hs]. exact (proj1 (HSW (a + i) HP Hs)).
Qed.

(* n present bytes from a are some n-byte list at a. *)
Lemma r7t_bytes_present : forall (m : word -> option byte) (n : nat) a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> exists b, LMem.mrd A.Img0.rsegs m (LMem.wa x) = Some b) ->
  exists bs, LMem.bytes_at A.Img0.rsegs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros a Ha Hn Hrd.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (Hrd a ltac:(lia)) as (b0 & Hb0).
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply Hrd; lia)) as (bs & Hbs & Hl).
    exists (b0 :: bs). split; [|cbn [length]; rewrite Hl; reflexivity].
    destruct Hbs as (_ & _ & Hbs). split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi.
    + cbn [nth_error]. replace (a + Z.of_nat 0) with a by lia. exact Hb0.
    + cbn [nth_error]. cbn [length] in Hi. rewrite <- (Hbs i ltac:(lia)). f_equal. f_equal. lia.
Qed.

(* The shadow byte of a byte at least 8 below fr + 544, or at or above fr + 2328, is off the frame-shadow bytes
   [Sfr fr + 68, Sfr fr + 291) the tail writes. *)
Lemma r7t_sh_apart : forall fr x, x + 8 <= fr + 544 \/ fr + 2328 <= x ->
  LFrame.outside [(ACtlCutP.Sfr fr + 68, ACtlCutP.Sfr fr + 291)] (A.AsanRT.shadow_addr x).
Proof.
  intros fr x H. cbn [LFrame.outside]. split; [|exact I].
  unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* The class-6 frame's shadow bytes [Sfr fr, Sfr fr + 512) are visible (AR_frames_law, YG0d.v:447-455). *)
Lemma r7t_frsh_vis : forall ly S (W : Reusable.YA0n.world segs) mem md pos fr lo len,
  Reusable.YG0n.AR segs B ly S W mem md -> In (6, pos) (Reusable.YG01.frames S) ->
  fr = Reusable.YG0f.frame_addr ly 6 pos -> ACtlCutP.Sfr fr <= lo -> 0 <= len -> lo + len <= ACtlCutP.Sfr fr + 512 ->
  A.ProgBridge.range_visible (Reusable.YA0n.w_H W) lo len.
Proof.
  intros ly S W mem md pos fr lo len HAR Hin Efr Hlo Hlen Hhi.
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly S W mem md 6 pos HAR Hin) as (_ & Happ & _ & Hsh).
  rewrite <- Efr in Happ, Hsh.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Happ, Hsh.
  pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as (Hce & _).
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ.
  unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Hlo, Hhi.
  assert (Hdiv : 8 * (fr / 8) <= fr < 8 * (fr / 8) + 8).
  { pose proof (Z.div_mod fr 8 ltac:(lia)). pose proof (Z.mod_pos_bound fr 8 ltac:(lia)). lia. }
  split; [lia|]. split; [lia|].
  intros a Ha.
  assert (Hi : 0 <= a - Reusable.YG0f.shadow_addr fr < 4096 / 8).
  { unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. change (4096 / 8) with 512. lia. }
  destruct (Hsh _ Hi) as [[Hv _] _].
  replace (Reusable.YG0f.shadow_addr fr + (a - Reusable.YG0f.shadow_addr fr)) with a in Hv by ring.
  exact Hv.
Qed.

(* Route (C): a byte of the class-6 frame's shadow [Sfr fr, Sfr fr + 512) is in the cut's own shadow, cut_shadow's
   (F) disjunct. *)
Lemma r7t_frsh_cut : forall ly S pos fr x, In (6, pos) (Reusable.YG01.frames S) ->
  fr = Reusable.YG0f.frame_addr ly 6 pos -> ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 ->
  A.ACtlRtC.cut_shadow B ly S x.
Proof.
  intros ly S pos fr x Hin Efr Hx. left. exists 6, pos. split; [exact Hin|]. rewrite <- Efr.
  change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
  unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Hx.
  unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

(* A catalogue byte's shadow byte reads 0 and is visible: the catalogue is a zero-shadow row of the bundle
   (CAT_ZSH), so AR_zshadow_law (YG0d.v:435-438) makes the view read Some 0 there. *)
Lemma r7t_cat_sh : forall ly S (W : Reusable.YA0n.world segs) mem md p,
  Reusable.YG0n.AR segs B ly S W mem md -> 0x9e800 <= p < 0x9f4b8 ->
  LStep.ro_cells A.Img0.rsegs mem (p / 8 + 2147450880) [LCells.C1 (Z_to_bv 8 0)] /\
  A.ProgBridge.range_visible (Reusable.YA0n.w_H W) (p / 8 + 2147450880) 1.
Proof.
  intros ly S W mem md p HAR Hp.
  assert (Hr : In (0x9e800, 0x9f4b8 - 0x9e800) (Reusable.YG0n.zero_shadow_ranges B ly)) by (right; exact CAT_ZSH).
  pose proof (Reusable.YG0d.al_zshadow _ _ LAWS ly S W mem md _ HAR Hr) as Hz.
  unfold Reusable.YG0v.zero_shadow in Hz. cbn [fst snd] in Hz.
  assert (Hi : 0 <= (p / 8 + 2147450880) - Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF 0x9e800 <
               (0x9f4b8 - 0x9e800) / 8).
  { unfold Reusable.YG0v.shadow_of_addr, Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia. }
  pose proof (Hz _ Hi) as Hs.
  replace (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF 0x9e800 +
           (p / 8 + 2147450880 - Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF 0x9e800))
    with (p / 8 + 2147450880) in Hs by ring.
  assert (Hv : Reusable.YA0n.w_H W (Z_to_bv 64 (p / 8 + 2147450880)) = false).
  { apply (A.ProgWorldVisFrame.vis_of_aview _ W mem). rewrite Hs. discriminate. }
  pose proof (A.ProgWorld.mrd_of_aview_some W mem (p / 8 + 2147450880) 0 Hv Hs) as Hm.
  assert (Hs0 : 0 <= p / 8 + 2147450880 < 2 ^ 64) by (Z.div_mod_to_equations; lia).
  split.
  - split; [split; [exact I | exact I]|].
    cbn [LCells.cells_bytes LCells.cbytes app].
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi'. cbn [length] in Hi'. destruct i as [|i]; [|lia].
    cbn [nth_error]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact Hm.
  - split; [lia|]. split; [lia|]. intros a Ha. replace a with (p / 8 + 2147450880) by lia. exact Hv.
Qed.

(* A catalogue byte at a cut reads as the image's ROM byte: the entry's read-only view (the core pre's
   arodata_okS over [RLO, RHI)) is kept by the journal on image bytes, and the byte is visible (an image byte).
   The ONLY reader of RELRO_CAT (through r7t_cat_ro). *)
Lemma r7t_cat_rom : forall cx ly3 S3 W3 mem3 md3 k a,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx)
    ly3 S3 W3 mem3 md3 k ->
  0x9e800 <= a < 0x9e800 + 3256 ->
  LMem.mrd A.Img0.rsegs mem3 (LMem.wa a) = Y11.seg_rom segs (LMem.wa a).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k a HB HJ Ha.
  destruct (r7t_cat_ro a Ha) as (Hr & Ho & He).
  destruct HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
  pose proof (Himg a (RELRO_IMG a Hr) Ho He
                ltac:(apply Reusable.YCbq.fp_spares_closed; intros (r & Hin & _); destruct Hin)) as E0.
  pose proof (Hro a (or_intror Hr) Ho He) as E1.
  rewrite <- E0 in E1.
  assert (Hv : Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { destruct (A.ProgBridge.img_vis_W W3) as (_ & _ & Hvis). apply Hvis.
    unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI. lia. }
  rewrite (A.ProgWorld.aview_vis_mrd W3 mem3 a Hv) in E1.
  revert E1. unfold LMem.wa.
  destruct (LMem.mrd A.Img0.rsegs mem3 (Z_to_bv 64 a)) as [x|];
    destruct (Y11.seg_rom segs (Z_to_bv 64 a)) as [y|]; cbn [option_map]; intros E1;
    [| discriminate E1 | discriminate E1 | reflexivity].
  injection E1 as Exy. f_equal. apply bv_eq. exact Exy.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The tail arm, n_6 = 0 and b = 6 (Seg/R7tail.v r7_tail_run :1242): r7_tail_evt_F (R7tailF.v:79; 0x815ec ->
   0x8194c -> 0x81990 .. 0x81abc -> 0x81ac8, the 14 frame-shadow stores of 0xf8, and __asan_set_shadow_f8 taken
   through its PROVED footprint contract) to the exit C_A81b10.  The run takes mem_inv, which the cut does not carry,
   so it runs on the normalized memory and comes back by MemNormF.evtF_normalize_ro (as P1_70.v's p1_70_ro_F).
   Its write set is the class-6 frame's shadow [Sfr fr + 68, Sfr fr + 291): the journal crosses it by
   ProgWorld.ajournal_of_fsteps (awr_byte's frame case), and every body fact off it is kept. *)
Lemma r7_arm_tail : forall POST, CF POST C_A81b10 ->
  R7_ENTRY POST 6 (fun cx => ACtlCutP.rnb cx 6 = 0).
Proof.
  intros POST HX cx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hb Hrt Hz.
  cbv beta in Hz.
  (* G1: the entry body at [Z.of_nat 6] (ACtlCutP.v:1300-1323) *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A815ec_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HP & HFRAC & A & Hcn & Hb6 & Hrnb & Hasz & HA & R9 & R24 & Ha0 & Q64 & S128 & HID & HFG & HRTF &
    R23 & Hour & Hout & Hcur & S112 & HPRO & S104 & S96 & S144 & S192 & Hidb & Hjk72 & S280 & S240 & Hjy & Hjk32 &
    S152 & R21 & Had & HRXS).
  destruct Hrt as (HAC & Hcut & Himg & HRO).
  (* G2: the shell's facts *)
  pose proof HB as ((_ & _ & _ & _ & Hinb & Hlen & _) & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  destruct Hastk as (_ & _ & Hceil_lo & Hstk_lo & Hstk_hi & Hstk47 & _).
  unfold A.ACfn.LLVMF_STK in Hstk_lo, Hpres.
  pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as (Hce & _). unfold Reusable.YG0f.ASAN_CEIL in Hce.
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  assert (Efr : fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) ltac:(left; reflexivity)).
    unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  rewrite <- Efr in Hf4096, Hfceil, Hfapp.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil, Hfapp.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Hfapp.
  (* FRAC: the spill base is register 9's, the stack geometry *)
  pose proof HFRAC as (Af & sp & _ & _ & _ & _ & _ & R9f & _ & R19 & R26 & _ & _ & HAS & HspA & HfrA & HA416 &
    HSsp & HSapp & _ & _ & _ & _ & _ & Hsh & _).
  unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in HfrA, HSapp.
  assert (EA : Af = A).
  { unfold ACtlCut.rgv in R9, R9f. rewrite R9 in R9f.
    apply (f_equal bv_unsigned) in R9f. rewrite !Z_to_bv_unsigned in R9f. unfold bv_wrap in R9f.
    change (bv_modulus 64) with (2 ^ 64) in R9f. Z.div_mod_to_equations. lia. }
  subst Af.
  (* the frame shadow Sfr fr = fr / 8 + ASAN_K: shadow memory, apart from the frame, below the stack *)
  assert (ESh : ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  assert (Hdiv : 8 * (fr / 8) <= fr < 8 * (fr / 8) + 8).
  { pose proof (Z.div_mod fr 8 ltac:(lia)). pose proof (Z.mod_pos_bound fr 8 ltac:(lia)). lia. }
  assert (HShfr : fr + 4096 <= ACtlCutP.Sfr fr \/ ACtlCutP.Sfr fr + 512 <= fr) by (rewrite ESh; lia).
  assert (HShst : ACtlCutP.Sfr fr + 512 <= CM05.alloc_ceiling) by (rewrite ESh; lia).
  assert (HShmax : ACtlCutP.Sfr fr + 512 <= 0x10007fff8000) by (rewrite ESh; lia).
  assert (HSh0 : 2147450880 <= ACtlCutP.Sfr fr) by (rewrite ESh; lia).
  assert (HSHin : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 -> A.AsanRT.in_shadow x).
  { intros x Hx. rewrite ESh in Hx.
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG.
    lia. }
  (* the model: the turn-6 identity record against the catalogue row (R7tail.r7t_model) *)
  assert (Hz6 : SMo.rt_n (ACtlCut.c_in cx) 6 = 0) by exact Hz.
  destruct (R7T.r7t_model (ACtlCut.c_in cx) Hz6) as (Hlen6 & H02 & H36 & M00 & M22 & M24 & M26 & M56 & Hist).
  assert (Hmr : SMo.mrow (ACtlCut.c_in cx) = 0x9e800 + 296 * SMo.istar (ACtlCut.c_in cx)) by reflexivity.
  assert (Hrow0 : 0x9e800 <= SMo.mrow (ACtlCut.c_in cx)) by lia.
  assert (Hrow1 : SMo.mrow (ACtlCut.c_in cx) + 296 <= 0x9e800 + 3256) by lia.
  (* the catalogue row's bytes (the ROM's, RELRO_CAT through r7t_cat_rom), the record's and row's cells *)
  pose proof (R7T.r7t_bytes_of_img mem3 (SMo.mrow (ACtlCut.c_in cx)) 296 (SMo.rowb (SMo.istar (ACtlCut.c_in cx)))
    (R7T.r7t_row_img _ Hist) ltac:(lia) ltac:(lia)
    (fun i Hi => r7t_cat_rom cx ly3 S3 W3 mem3 md3 k (SMo.mrow (ACtlCut.c_in cx) + Z.of_nat i) HB HJ
                   ltac:(lia))) as NROW.
  destruct (R7T.r7t_idrow_cells mem3 (fr + 2176) (SMo.mrow (ACtlCut.c_in cx)) (SMo.RID (ACtlCut.c_in cx) 6)
              (SMo.rowb (SMo.istar (ACtlCut.c_in cx))) Hlen6 (R7T.row_len _) HID NROW M00 M22 M24 M26) as (CI & CR).
  pose proof (R7T.r7t_c56 mem3 (SMo.mrow (ACtlCut.c_in cx)) (SMo.rowb (SMo.istar (ACtlCut.c_in cx)))
    (R7T.row_len _) NROW M56) as CR56.
  destruct (r7t_cat_sh ly3 S3 W3 mem3 md3 (SMo.mrow (ACtlCut.c_in cx) + 266) HAR ltac:(lia)) as (SC266 & SV266).
  destruct (r7t_cat_sh ly3 S3 W3 mem3 md3 (SMo.mrow (ACtlCut.c_in cx) + 268) HAR ltac:(lia)) as (SC268 & SV268).
  destruct (r7t_cat_sh ly3 S3 W3 mem3 md3 (SMo.mrow (ACtlCut.c_in cx) + 270) HAR ltac:(lia)) as (SC270 & SV270).
  destruct (r7t_cat_sh ly3 S3 W3 mem3 md3 (SMo.mrow (ACtlCut.c_in cx) + 272) HAR ltac:(lia)) as (SC272 & SV272).
  destruct (r7t_cat_sh ly3 S3 W3 mem3 md3 (SMo.mrow (ACtlCut.c_in cx) + 56) HAR ltac:(lia)) as (SC56 & SV56).
  (* the spills the run reads *)
  pose proof (r7g_spill_q64 regs3 mem3 A 112 _ R9 ltac:(lia) ltac:(lia) ltac:(lia) S112) as Q112.
  pose proof (r7g_spill_q64 regs3 mem3 A 128 _ R9 ltac:(lia) ltac:(lia) ltac:(lia) S128) as Q128.
  pose proof (r7g_spill_q64 regs3 mem3 A 144 _ R9 ltac:(lia) ltac:(lia) ltac:(lia) S144) as Q144.
  pose proof (r7g_spill_q64 regs3 mem3 A 152 _ R9 ltac:(lia) ltac:(lia) ltac:(lia) S152) as Q152.
  (* the frame shadow the run writes: two runs of present shadow bytes, writable on the normalized memory *)
  destruct Hsh as (sh & Bsh & Lsh).
  change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat in Lsh.
  pose proof (R7T.r7t_sub mem3 (ACtlCutP.Sfr fr) sh 68 187 Bsh ltac:(lia)) as Bjsh.
  pose proof (R7T.r7t_sub mem3 (ACtlCutP.Sfr fr) sh 272 19 Bsh ltac:(lia)) as Bjfl.
  assert (Ljsh : length (firstn 187 (skipn 68 sh)) = 187%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (Ljfl : length (firstn 19 (skipn 272 sh)) = 19%nat) by (rewrite length_firstn, length_skipn; lia).
  pose proof (r7t_sh_rw_on _ mem3 (ACtlCutP.Sfr fr + 68) (firstn 187 (skipn 68 sh)) 187 HRO Bjsh Ljsh Hcut
    (fun i Hi => conj (r7t_frsh_cut ly3 S3 (ACtlCut.c_fpos cx) fr (ACtlCutP.Sfr fr + 68 + i) Hin6 Efr ltac:(lia))
                      (HSHin (ACtlCutP.Sfr fr + 68 + i) ltac:(lia)))) as RWsh.
  pose proof (r7t_sh_rw_on _ mem3 (ACtlCutP.Sfr fr + 272) (firstn 19 (skipn 272 sh)) 19 HRO Bjfl Ljfl Hcut
    (fun i Hi => conj (r7t_frsh_cut ly3 S3 (ACtlCut.c_fpos cx) fr (ACtlCutP.Sfr fr + 272 + i) Hin6 Efr ltac:(lia))
                      (HSHin (ACtlCutP.Sfr fr + 272 + i) ltac:(lia)))) as RWfl.
  assert (Ra0 : ACtlCut.rgv regs3 10 0) by (rewrite Hz in Ha0; exact Ha0).
  (* footprint: RNG_W (w_H W3) and the visibility of every range the run reads or writes *)
  pose (RNG := A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (VW : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= ACtlCut.c_sp cx -> LEF.rng RNG lo len).
  { intros lo len H1 H2. apply A.ProgBridge.rng_of_visible.
    apply (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] _ _ _ _ _ _ _ _ W3 mem3 md3 k lo len HJ);
      unfold A.ACfn.LLVMF_STK; lia. }
  assert (VID : LEF.rng RNG (fr + 2176) 38).
  { apply A.ProgBridge.rng_of_visible.
    pose proof (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 2176) 38
                  HAR Hin6) as V.
    rewrite <- Efr in V. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in V.
    exact (proj1 (V ltac:(lia) ltac:(lia))). }
  assert (VIMG : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.Prog.ImgBounds.IMG_LO
                   (A.Prog.ImgBounds.IMG_HI - A.Prog.ImgBounds.IMG_LO)) by exact (A.ProgBridge.img_vis_W W3).
  assert (VR266 : LEF.rng RNG (SMo.mrow (ACtlCut.c_in cx) + 266) 8).
  { apply A.ProgBridge.rng_of_visible. apply (A.ProgBridge.range_visible_sub _ _ _ _ _ VIMG);
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia. }
  assert (VR56 : LEF.rng RNG (SMo.mrow (ACtlCut.c_in cx) + 56) 4).
  { apply A.ProgBridge.rng_of_visible. apply (A.ProgBridge.range_visible_sub _ _ _ _ _ VIMG);
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia. }
  assert (VF68 : LEF.rng RNG (ACtlCutP.Sfr fr + 68) 187).
  { apply A.ProgBridge.rng_of_visible.
    exact (r7t_frsh_vis ly3 S3 W3 mem3 md3 (ACtlCut.c_fpos cx) fr (ACtlCutP.Sfr fr + 68) 187 HAR Hin6 Efr
             ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (VF272 : LEF.rng RNG (ACtlCutP.Sfr fr + 272) 19).
  { apply A.ProgBridge.rng_of_visible.
    exact (r7t_frsh_vis ly3 S3 W3 mem3 md3 (ACtlCut.c_fpos cx) fr (ACtlCutP.Sfr fr + 272) 19 HAR Hin6 Efr
             ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (RWIN : forall x : word, LEF.rng RNG (bv_unsigned x - A.Prog.asan_set_shadow_cF.ASAN_SET_SHADOW_K)
                                     A.Prog.asan_set_shadow_cF.ASAN_SET_SHADOW_K).
  { intros x. apply A.ProgBridge.rng_of_visible. unfold A.Prog.asan_set_shadow_cF.ASAN_SET_SHADOW_K.
    pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
    split; [lia|]. split; [lia|]. intros a Ha. lia. }
  pose proof (A.Prog.asan_set_shadowF.asan_set_shadow_f8_holds_F A.Prog.memset.memset_holds) as SSF.
  (* the run, on the cut's memory: r7_tail_evt_F on the normalized memory, brought back by evtF_normalize_ro *)
  assert (HRUN : LEF.evtF A.Img0.rsegs RNG
    (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
       ms' = LMS.MS R Y11.fp_regs (Z_to_bv 64 0x81b10) Y11.fp_csr None m' (Y11.seg_rom A.Img0.rsegs) /\
       Y11.getr R 2 = Y11.getr regs3 2 /\ Y11.getr R 3 = Y11.getr regs3 3 /\ Y11.getr R 4 = Y11.getr regs3 4 /\
       Y11.getr R 8 = Y11.getr regs3 8 /\ Y11.getr R 9 = Y11.getr regs3 9 /\
       Y11.getr R 19 = Y11.getr regs3 19 /\ Y11.getr R 22 = Y11.getr regs3 22 /\
       Y11.getr R 25 = Y11.getr regs3 25 /\ Y11.getr R 26 = Y11.getr regs3 26 /\
       Y11.getr R 27 = Z_to_bv 64 (fr + 2688) /\
       LFrame.munch [(ACtlCutP.Sfr fr + 68, ACtlCutP.Sfr fr + 291)] mem3 m' /\
       LFrame.wmono A.Img0.rsegs mem3 m' /\ A.MemNorm.ro_agree A.Img0.rsegs m' /\
       (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P mem3 -> A.ShadowRwOn.shadow_rw_on P m'))
    (LMS.MS (LR6.mkR_of regs3) Y11.fp_regs (Z_to_bv 64 0x815ec) Y11.fp_csr None mem3
       (Y11.seg_rom A.Img0.rsegs))).
  { unfold LR6.mkR_of.
    pose proof (A.MemNorm.mem_rel_normalize A.Img0.rsegs mem3 HRO) as REL.
    eapply LEF.evtF_mono.
    - eapply (A.MemNormF.evtF_normalize_ro RNG _ _ _ _ _ _ mem3 _ HRO).
      eapply (R7TF.r7_tail_evt_F SSF RNG) with (A := A) (IDa := fr + 2176) (row := SMo.mrow (ACtlCut.c_in cx))
        (S3 := ACtlCutP.Sfr fr) (v128 := Z_to_bv 64 (fr + 544)) (v144 := Z_to_bv 64 (fr + 2688))
        (h2 := nth 2 (SMo.RID (ACtlCut.c_in cx) 6) (Z_to_bv 8 0))
        (h36 := nth 36 (SMo.RID (ACtlCut.c_in cx) 6) (Z_to_bv 8 0))
        (w0 := R7T.r7t_w2 (firstn 2 (skipn 266 (SMo.rowb (SMo.istar (ACtlCut.c_in cx))))))
        (w1 := R7T.r7t_w2 (firstn 2 (skipn 268 (SMo.rowb (SMo.istar (ACtlCut.c_in cx))))))
        (w2 := R7T.r7t_w2 (firstn 2 (skipn 270 (SMo.rowb (SMo.istar (ACtlCut.c_in cx))))))
        (w3 := R7T.r7t_w2 (firstn 2 (skipn 272 (SMo.rowb (SMo.istar (ACtlCut.c_in cx))))))
        (j1 := firstn 19 (skipn 3 (SMo.RID (ACtlCut.c_in cx) 6)))
        (j2 := firstn 8 (skipn 28 (SMo.RID (ACtlCut.c_in cx) 6)))
        (jsh := firstn 187 (skipn 68 sh)) (jfl := firstn 19 (skipn 272 sh)).
      (* registers *)
      + exact R9.
      + exact Ra0.
      + exact R21.
      + exact R26.
      + exact R19.
      + exact R23.
      (* bounds *)
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + lia.
      + intros i Hi. apply HSHin. lia.
      (* memory *)
      + exact (R7T.r7t_ro_norm _ _ _ HRO (R7T.r7t_q64_ro _ _ _ Q112)).
      + exact (R7T.r7t_ro_norm _ _ _ HRO (R7T.r7t_q64_ro _ _ _ Q128)).
      + exact (R7T.r7t_ro_norm _ _ _ HRO (R7T.r7t_q64_ro _ _ _ Q144)).
      + exact (R7T.r7t_ro_norm _ _ _ HRO (R7T.r7t_q64_ro _ _ _ Q152)).
      + exact (R7T.r7t_ro_norm _ _ _ HRO CI).
      + exact H02.
      + exact H36.
      + exact (R7T.r7t_ro_norm _ _ _ HRO CR).
      + exact (R7T.r7t_ro_norm _ _ _ HRO CR56).
      + exact (R7T.r7t_ro_norm _ _ _ HRO SC266).
      + exact (R7T.r7t_ro_norm _ _ _ HRO SC268).
      + exact (R7T.r7t_ro_norm _ _ _ HRO SC270).
      + exact (R7T.r7t_ro_norm _ _ _ HRO SC272).
      + exact (R7T.r7t_ro_norm _ _ _ HRO SC56).
      + exact RWsh.
      + exact RWfl.
      + exact Ljsh.
      + exact Ljfl.
      + exact (A.MemNormTr.asan_cells_normalize mem3 HRO HAC).
      + exact (A.MemNorm.mem_inv_normalize A.Img0.rsegs mem3).
      (* footprint *)
      + apply VW; lia.
      + apply VW; lia.
      + apply VW; lia.
      + apply VW; lia.
      + exact VID.
      + exact VR266.
      + exact VR56.
      + exact (A.ProgBridge.rng_of_visible _ _ _ SV266).
      + exact (A.ProgBridge.rng_of_visible _ _ _ SV268).
      + exact (A.ProgBridge.rng_of_visible _ _ _ SV270).
      + exact (A.ProgBridge.rng_of_visible _ _ _ SV272).
      + exact (A.ProgBridge.rng_of_visible _ _ _ SV56).
      + exact VF272.
      + exact (A.ProgBridge.rng_bytes_RNG_W _).
      + exact (A.ProgBridge.rng_of_visible _ _ _ VIMG).
      + apply RWIN.
      + exact VF68.
    - intros s (s0 & (R & m0' & -> & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K25 & K26 & K27 & MU0 & WM0 & MI0 &
                     RW0) & MR & RS).
      destruct (A.MemNormTr.ms_rel_MS s _ _ _ _ _ _ _ MR) as (Es & Hmem).
      exists R, (ms_mem s).
      split; [exact Es|].
      split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
      split; [exact K19|]. split; [exact K22|]. split; [exact K25|]. split; [exact K26|]. split; [exact K27|].
      split.
      { apply (LFrame.munch_weaken [(ACtlCutP.Sfr fr + 68, ACtlCutP.Sfr fr + 255);
                                    (ACtlCutP.Sfr fr + 272, ACtlCutP.Sfr fr + 291)]).
        - intros x Hx. cbn [LFrame.outside] in Hx |- *. destruct Hx as (Hx & _).
          split; [lia | split; [lia | exact I]].
        - exact (A.MemNorm.munch_rel A.Img0.rsegs _ mem3 _ (ms_mem s) m0' REL Hmem RS MU0). }
      split; [exact (A.MemNorm.wmono_rel A.Img0.rsegs mem3 _ (ms_mem s) m0' REL Hmem RS WM0)|].
      split; [exact (A.MemNorm.ro_agree_same A.Img0.rsegs mem3 (ms_mem s) HRO RS)|].
      intros Pr HPr. exact (A.ShadowRwOnT.shadow_rw_on_of_rel Pr (ms_mem s) m0' Hmem
               (r7t_srw_keep_on Pr _ _ (A.ShadowRwOnT.shadow_rw_on_normalize Pr mem3 HRO HPr) WM0)). }
  (* G3: the cut's configuration in the run's state form, the walk moved to the canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LR6.mkR_of regs3) regs3 Y11.fp_regs
           (Z_to_bv 64 0x815ec) Y11.fp_csr None mem3 (Y11.seg_rom segs) md3 (POST cx));
    [| exact (LR6.xregs_eqv_sym _ _ (LR6.mkR_of_eqv regs3))].
  (* G4: the lift (YA0nR.SRr_fsteps keeps the run for ajournal_of_fsteps) *)
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  destruct HFS as (ms' & Hrun & HQ0).
  apply (Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 _ ms' md3 RNG (POST cx) Hrun
           (A.ProgBridge.fp_avoids_RNG_W _)).
  intros md' Hsbm.
  (* G5: the end state is the exit cut's state at the run's map R and memory m' *)
  destruct HQ0 as (R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K22 & K25 & K26 & K27 & MU & WM & RO' & SW').
  subst ms'.
  (* route (C): the cut's regions after the run (its forall-P post) *)
  pose proof (SW' _ Hcut) as Hcut'. pose proof (SW' _ Himg) as Himg'.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81b10) R m' md') (POST cx)).
  (* memory kept across the run: its write set [Sfr fr + 68, Sfr fr + 291) is frame shadow *)
  assert (Tb : forall a bs, LMem.bytes_at segs mem3 a bs ->
                 (a + Z.of_nat (length bs) <= ACtlCutP.Sfr fr + 68 \/ ACtlCutP.Sfr fr + 291 <= a) ->
                 LMem.bytes_at segs m' a bs).
  { intros a bs H Hd. apply (LFrame.bytes_at_transport segs _ mem3 m' a bs H MU).
    cbn [LFrame.disjoint_from]. split; [exact Hd | exact I]. }
  assert (Tq : forall a v, ACtlCutP.q64 mem3 a v ->
                 (a + 8 <= ACtlCutP.Sfr fr + 68 \/ ACtlCutP.Sfr fr + 291 <= a) -> ACtlCutP.q64 m' a v).
  { intros a v H Hd. unfold ACtlCutP.q64 in *. apply Tb; [exact H|]. rewrite LMem.length_le8. lia. }
  assert (Trw : forall a cs, LStep.rw_cells segs mem3 a cs ->
                  (a + Z.of_nat (LCells.cells_size cs) <= ACtlCutP.Sfr fr + 68 \/ ACtlCutP.Sfr fr + 291 <= a) ->
                  LStep.rw_cells segs m' a cs).
  { intros a cs H Hd. apply (LFrame.rw_cells_transport segs _ mem3 m' a cs H MU WM).
    cbn [LFrame.disjoint_from]. split; [exact Hd | exact I]. }
  assert (Tsp : forall off v, 0 <= off -> off + 8 <= 416 ->
                  ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R m' off v).
  { intros off v H0 H1 S. exists A. split; [unfold ACtlCut.rgv in *; rewrite K9; exact R9|].
    apply Tq; [exact (r7g_spill_q64 regs3 mem3 A off v R9 ltac:(lia) H0 ltac:(lia) S)|]. right. lia. }
  assert (Tad : forall p n, A.AsanRT.addressable mem3 p n ->
                  (forall i, 0 <= i < n -> p + i + 8 <= fr + 544 \/ fr + 2328 <= p + i) ->
                  A.AsanRT.addressable m' p n).
  { intros p n Hpa Hpn. apply (r7t_addr_keep _ mem3 m' p n Hpa MU).
    intros i Hi. exact (r7t_sh_apart fr (p + i) (Hpn i Hi)). }
  (* the frame shadow after the run: present bytes (cut_shadow's (F) disjunct, kept by the run) *)
  assert (FSH' : exists sh', LMem.bytes_at segs m' (ACtlCutP.Sfr fr) sh' /\
                             length sh' = Z.to_nat ACtlCutP.FRAME_SHADOW).
  { change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat.
    apply (r7t_bytes_present m' 392 (ACtlCutP.Sfr fr)); [lia | lia |].
    intros x Hx.
    exact (proj2 (Hcut' x (r7t_frsh_cut ly3 S3 (ACtlCut.c_fpos cx) fr x Hin6 Efr ltac:(lia)) (HSHin x ltac:(lia)))). }
  (* the input block (the lib pre): A_EMPTY, or a live block in application memory apart from the frame *)
  assert (HBLK : (ACtlCut.c_n cx = 0 /\ ACtlCut.c_p cx = A.ACfn.A_EMPTY) \/
                 (0 < ACtlCut.c_n cx /\ 4096 <= ACtlCut.c_p cx /\
                  (ACtlCut.c_p cx + ACtlCut.c_n cx <= 0x7fff7000 \/ 0x10007fff8000 <= ACtlCut.c_p cx) /\
                  (ACtlCut.c_p cx + ACtlCut.c_n cx <= fr \/ fr + 4096 <= ACtlCut.c_p cx))).
  { destruct Hinb as [H0 | (Hn & Hin)]; [left; exact H0 | right].
    assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
      by exact (Permutation_in _ (Permutation_sym HP) Hin).
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (_ & Hp4096 & Hpceil & Hpapp & _).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hin3 Hin6)
      as Hsep.
    pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as Hrs.
    unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite <- Efr in Hsep.
    change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hsep.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hpapp.
    lia. }
  unfold A.ACfn.A_EMPTY in HBLK.
  apply (HX cx [] fr k ly3 S3 W3 R m' md' HB).
  - (* journal: a Theorem Labs lane's ajournal_of_fsteps; the write set is the class-6 frame's shadow (awr_byte's frame
       case) *)
    assert (Hawr : forall a, 0 <= a < 2 ^ 64 ->
              ~ LFrame.outside [(ACtlCutP.Sfr fr + 68, ACtlCutP.Sfr fr + 291)] a ->
              Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
                (ACtlCut.own6 cx) a).
    { intros a _ Hw.
      assert (Ha : ACtlCutP.Sfr fr + 68 <= a < ACtlCutP.Sfr fr + 291).
      { destruct (Z_le_gt_dec (ACtlCutP.Sfr fr + 68) a) as [H1|H1].
        - destruct (Z_lt_ge_dec a (ACtlCutP.Sfr fr + 291)) as [H2|H2]; [lia|].
          exfalso. apply Hw. cbn [LFrame.outside]. split; [lia | exact I].
        - exfalso. apply Hw. cbn [LFrame.outside]. split; [lia | exact I]. }
      unfold Reusable.YCbq.awr_byte. right; right; right.
      exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
      right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr.
      change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESh in Ha. lia. }
    match type of Hrun with Reusable.YK04R.fsteps _ _ ?s0 ?s1 =>
      exact (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
               (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
               (ACtlCut.own6 cx) ly3 S3 W3 s0 s1 md3 md' k RNG _ HJ Hrun (A.ProgBridge.fp_avoids_RNG_W _) MU Hsbm
               Hawr)
    end.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: kmax 14 >= 2 * 6 *)
    cbv beta iota delta [ACtlCut.cut_kmax ACtlCutP.C_A81b10]. lia.
  - (* the exit body C_A81b10 (ACtlCutP.v:1752-1767) *)
    cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_A81b10].
    split; [exact HP|].
    split.
    { (* FRAC: registers through the run's post (kit_frac_move), every memory conjunct off the written frame shadow
         (the frame shadow itself re-read from shadow_rw).  Walked conjunct by conjunct, so a conjunct appended to
         FRAC (a Theorem Labs lane 05:40Z: q64 m (fr + 4088) ..., inside the frame) is kept by the same q64 transport. *)
      pose proof (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26) as HF1.
      unfold ACtlCutP.FRAC in HF1 |- *.
      destruct HF1 as (A2 & sp2 & HF1). exists A2, sp2.
      repeat (lazymatch type of HF1 with
              | _ /\ _ =>
                  let H1 := fresh "F" in let H2 := fresh "F" in
                  destruct HF1 as [H1 H2]; rename H2 into HF1;
                  split; [first [ exact H1 | exact FSH'
                                | lazymatch type of H1 with ACtlCutP.q64 _ _ _ => exact (Tq _ _ H1 ltac:(lia)) end
                                | exact (Tb _ _ H1 ltac:(lia)) ] |]
              end).
      first [ exact HF1 | exact FSH'
            | lazymatch type of HF1 with ACtlCutP.q64 _ _ _ => exact (Tq _ _ HF1 ltac:(lia)) end
            | exact (Tb _ _ HF1 ltac:(lia)) ]. }
    split; [exact Hcn|].
    split.
    { (* OURb: our[]'s 6 frame bytes at fr + 2624 *)
      unfold ACtlCutP.OURb in Hour |- *. apply Tb; [exact Hour|]. rewrite SMo.OUR_length. lia. }
    split.
    { (* CUR at c0 (c_in cx) = 7 (the entry's CUR cx 7 gives 7 <= c_n cx); s6 / s9 kept *)
      destruct Hcur as (Hc7 & C22 & C25).
      assert (E7 : SMo.c0 (ACtlCut.c_in cx) = 7) by (unfold SMo.c0, SMo.nlen; lia).
      unfold ACtlCutP.CUR. rewrite E7. split; [exact Hc7|].
      unfold ACtlCut.rgv in *. split; [rewrite K22; exact C22 | rewrite K25; exact C25]. }
    split.
    { (* PRO: the spills through register 9 (kept) in the save area; our[]'s addressability and the input block
         off the written frame shadow *)
      destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg & P184 & P256 & P264 &
        P272 & P32).
      unfold ACtlCutP.PRO.
      split; [exact (Tsp 40 _ ltac:(lia) ltac:(lia) P40)|].
      split; [exact (Tsp 120 _ ltac:(lia) ltac:(lia) P120)|].
      split; [exact (Tsp 136 _ ltac:(lia) ltac:(lia) P136)|].
      split; [exact (Tsp 160 _ ltac:(lia) ltac:(lia) P160)|].
      split; [exact (Tsp 168 _ ltac:(lia) ltac:(lia) P168)|].
      split; [exact (Tsp 176 _ ltac:(lia) ltac:(lia) P176)|].
      split; [exact (Tsp 208 _ ltac:(lia) ltac:(lia) P208)|].
      split; [exact (Tsp 248 _ ltac:(lia) ltac:(lia) P248)|].
      split; [exact (Tad _ _ Pad ltac:(intros i Hi; right; lia))|].
      split; [apply Tb; [exact Pin|]; rewrite <- Hlen; lia|].
      split; [intros Hn0; exact (Tad _ _ (Pg Hn0) ltac:(intros i Hi; lia))|].
      split; [exact (Tsp 184 _ ltac:(lia) ltac:(lia) P184)|].
      split; [exact (Tsp 256 _ ltac:(lia) ltac:(lia) P256)|].
      split; [exact (Tsp 264 _ ltac:(lia) ltac:(lia) P264)|].
      split; [exact (Tsp 272 _ ltac:(lia) ltac:(lia) P272)|].
      exact (Tsp 32 _ ltac:(lia) ltac:(lia) P32). }
    split; [exact (Tsp 144 _ ltac:(lia) ltac:(lia) S144)|].
    (* push 7 / push 9: s11 = fr + 2688, the cell [A + 192] (a spill in the stack window, present so writable), the
       two frame records, the words [A + 280] / [A + 240] and the code cell / scratch, all off the written shadow *)
    pose proof (r7g_spill_q64 regs3 mem3 A 192 _ R9 ltac:(lia) ltac:(lia) ltac:(lia) S192) as Q192.
    assert (RW192 : LStep.rw_cells segs mem3 (A + 192) [LCells.C8 (Z_to_bv 64 (fr + 2768))]).
    { split.
      - split; [split; [exact I | exact I]|]. cbn [LCells.cells_bytes LCells.cbytes]. rewrite app_nil_r. exact Q192.
      - split; [lia|]. split; [cbn [LCells.cells_size LCells.csize]; lia|].
        intros i Hi. cbn [LCells.cells_size LCells.csize] in Hi.
        destruct (Hpres (A + 192 + i) ltac:(lia)) as (_ & b & Hb).
        unfold wview, LMem.wa. rewrite Hb. discriminate. }
    destruct Hidb as (idb & Hidb). destruct Hjk72 as (junk & Hjk).
    exists A, idb, junk.
    split; [transitivity (Y11.getr regs3 9); [exact K9 | exact R9]|].
    split; [exact K27|].
    split; [exact HA|].
    split; [apply Trw; [exact RW192|]; cbn [LCells.cells_size LCells.csize]; lia|].
    split; [apply Trw; [exact Hidb|]; cbn [LCells.cells_size LCells.csize]; lia|].
    split; [apply Trw; [exact Hjk|]; cbn [LCells.cells_size LCells.csize]; lia|].
    split; [exact (Tq _ _ (r7g_spill_q64 regs3 mem3 A 280 _ R9 ltac:(lia) ltac:(lia) ltac:(lia) S280) ltac:(lia))|].
    split; [exact (Tq _ _ (r7g_spill_q64 regs3 mem3 A 240 _ R9 ltac:(lia) ltac:(lia) ltac:(lia) S240) ltac:(lia))|].
    destruct Hjy as (jy & Hjy'). destruct Hjk32 as (junk2 & Hj2).
    exists jy, junk2.
    split; [apply Trw; [exact Hjy'|]; cbn [LCells.cells_size LCells.csize]; lia|].
    apply Trw; [exact Hj2|]; cbn [LCells.cells_size LCells.csize]; lia.
  - (* ctl_rt_C m': the runtime cells are far from the frame shadow; the run keeps ro_agree and the two regions *)
    split; [exact (A.AsanRTFacts.asan_cells_kept _ mem3 m' HAC MU
                     ltac:(cbn [LFrame.disjoint_from]; unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI;
                           split; [lia | exact I]))|].
    split; [exact Hcut'|]. split; [exact Himg'|].
    exact RO'.
Qed.


(* ---------------------------------------------------------------------------------------------------------
   The stage: the case split of Seg/R7.v seg_R7 (:1143-1157) on n_b = rnb cx b. *)
Lemma glue_seg_R7 : forall POST (b : nat),
  CF POST (ix_cut C_A81640_at [Z.of_nat b]) -> CF POST (ix_cut C_A815cc_at [Z.of_nat (S b)]) -> CF POST C_A81ac0 -> CF POST C_A81b10 ->
  CF POST (ix_cut C_A815ec_at [Z.of_nat b]).
Proof.
  intros POST b H8 H74 _ Hp2 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A815ec_at ACtlCutP.ixn nth] in Hk.
  rewrite Nat2Z.id in Hk.
  change (ACtlCut.cut_pc (ix_cut C_A815ec_at [Z.of_nat b])) with 0x815ec.
  destruct (Z.eq_dec (ACtlCutP.rnb cx b) 0) as [Hz|Hnz].
  - assert (Hb6 : (b <= 6)%nat).
    { pose proof Hb as Hb'.
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A815ec_at ACtlCutP.ixn nth] in Hb'.
      rewrite Nat2Z.id in Hb'. destruct Hb' as (_ & _ & A & _ & Hb6 & _). exact Hb6. }
    destruct (le_lt_dec b 5) as [Hb5|Hb6'].
    + exact (r7_arm_latch POST b Hb5 H74 cx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hb Hrt Hz).
    + assert (Eb : b = 6%nat) by lia. subst b.
      exact (r7_arm_tail POST Hp2 cx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hb Hrt Hz).
  - exact (r7_arm_malloc POST b H8 cx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hb Hrt Hnz).
Qed.

End GlueR7.

Print Assumptions glue_seg_R7.

(* Gate check (a Theorem Labs lane 07:18Z): the Section's classes are the CORE copies of the twin modules (lib/Reusable). *)
Locate CM05.RunCeil.
Locate CO09.lib_shape.
Locate Y11.FPState.
