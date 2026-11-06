(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module names and numbers changed; 1086 of its 1232 lines of code are new or changed and 1651 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R7tail.v; 1150 of its 1202 lines of code are new or changed and 1180 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R7.v, with its module paths and module names changed; 297 of its 372 lines of code are new or changed and 1127 lines of the source are left out. *)
(* lib/A/ACtlG/R2.v -- GLUE for stage seg_R2 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:662,
   `Hypothesis seg_R2 : forall POST, CF POST C_A8152c -> CF POST C_A814f8`).  Written by a Theorem Labs lane's glue lane
   (piece W0/W1); single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery), the worked examples lib/A/ACtlG/A5.v and A2.v.
   rule 24: no function proved (stage glue of a walk; kind: segment lemma).

   WHAT IT PROVES
     glue_seg_R2 : forall POST, CF POST C_A8152c -> CF POST C_A814f8
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_R2.  Segment R2 is 0x814f8 -> 0x8152c (Seg/R2.v:1-8): the two non-taken abort tests (a0 = CAT <> 0, the
   count [s2] = [fr + 2656] = CAT_N = 11 <> 0), the catalogue row s2 = CAT + 296 * ((s7 >> 1) mod 11), and
   meta_fill_00 (__asan_set_shadow_00) over the 186 frame-shadow bytes [Q, Q + 186), Q = Sfr fr + 68 = [A + 152].

   RULE 24 (released proofs first): the released ASan donor cgif/cgif_file_fuzzer (proof-index
   LLVMFuzzerTestOneInput, see A2.v's header) lifts no outside-proved run, so this glue has no donor counterpart.

   THE RUN.  a Theorem Labs lane's mechanical v1.9 re-run A.Prog.Seg.R2F.r2_evt_F (Seg/R2F.v:51-78), Required, not assumed:
   R2.r2_evt (Seg/R2.v:196) under StepF, RNG first, the callee's footprint contract
   asan_set_shadow_cF.asan_set_shadow_00_contract_F as its FIRST premise.  That premise is discharged outright by
   the PROVED closed theorem asan_set_shadowF.asan_set_shadow_00_holds_F memset.memset_holds (no split, a Theorem Labs lane
   04:01Z / 04:28Z).  The run is an explicit-mkR run over lib/Lib's getr / seg_rom; it is instantiated at the
   cut's canonical map mkR_of regs3 (Regs6ss.v:456, the 31 binders := reg_get regs3 i by delta) with
   A := the spill base (FRAC's register 9), c := fr + 2656 (the body's s2 = fr + 2656 and q64 (fr + 2656) CAT_N:
   the count cell is a FRAME cell, so no RELRO_* hypothesis is needed), Q := Sfr fr + 68 (the body's spill
   [A + 152]), md := SM.mode (c_in cx) (the body's s7), junk := bytes 68 .. 253 of FRAC's frame-shadow list.

   THE PROOF, step by step (glue-pattern.md section 3)
   G1  unfold the entry cut C_A814f8 (ACtlCutP.v:1188-1206), 28 conjuncts; FRAC by its first 26 conjuncts (`& _`
       at the end, so FRAC's trailer conjunct is not named); ctl_rt_C's four facts (its img_shadow one unused).
   G2  the owned class-6 frame (KitMem.kitmem_own6, YCbq.frames_bounds): 4096 <= fr, fr mod 32 = 0,
       frame_addr ly3 6 pos = fr, fr + 4096 <= alloc_ceiling <= c_sp cx - LLVMF_STK, in_app fr 4096; with
       ASAN_CEIL_range the written window [Q, Q + 186) is shadow memory, below the spill block and the stack, off
       the frame and off the image.  The run's premises: registers from the body's rgv facts (a0 = CAT, s1 = A,
       s2 = fr + 2656, s7 = mode), md < 256 by R2.r2_mode_rng, the two read cells by R2.r2_ro8 (the spill through
       register 9, local r2g_spill_q64), the written cells by R2.r2_ba_sub + R2.r2_rw_CB over FRAC's frame-shadow
       bytes and ctl_rt_C's cut_shadow (region HFsh), asan_cells / ro_agree from ctl_rt_C.  Footprint at RNG_W (w_H W3):
       rng_bytes_RNG_W; the count cell by KitMem.kitmem_rng_frame (owned frame); the spill by kitmem_rng_win
       (LLVMF stack window); the image by img_vis_W; the callee window of length ASAN_SET_SHADOW_K = 0 directly;
       [Q, Q + 186) by kitmem_rng_frame_sh (the owned frame's shadow).
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from the cut's map regs3 to the run's mkR_of regs3.
   G4  KitMem.kitmem_lift at RNG_W (w_H W3), fp_avoids by ProgBridge.fp_avoids_RNG_W; its continuation gives the
       run's fsteps; mem_grows of the run by ProgWorld.pws_fsteps_mem.
   G5  the exit cut C_A8152c (ACtlCutP.v:1317-1333) at the run's end map R and memory m'
       (munch [(Q, Q + 186)] mem3 m'):
         journal  ProgWorld.ajournal_of_fsteps (PROVED, a Theorem Labs lane), every written byte awr_byte's in_frames
                  case (the owned frame's shadow, KitMem.kitmem_awr_frame);
         frames, frame law, k bound   unchanged (own6 and kmax 0 on both cuts);
         body     FRAC by Kit.kit_frac_move (registers 2 3 4 8 9 19 26 kept) and KitMem.kitmem_frac_keep (by
                  SHAPE; the frame shadow re-read by growth); spills by KitMem.kitmem_spill_munch; OURb and the
                  input bytes by kitmem_bytes_munch; the three frame records by Lib.Frame.rw_cells_transport;
                  PRO's two addressable facts by local r2g_addr_keep (their shadow bytes are off the window: our[]'s
                  is Sfr fr + 328, the input block is apart from the frame by YCbq.sep_block_frame); s2 = mrow, s5,
                  s6, s9 from the run's post; out[]'s first 1488 bytes addressable from the 186 written zeros
                  (R2.r2_addr_z), as ctrl's seg_R2 (Seg/R2.v:584-588);
         ctl_rt_C A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the exit journal's AR (same ly3 S3, memory m'), with the
                  entry's arodata_okS carried along the journal (KitMem.kitmem_arodataS_journal, RELRO_IMG) and made
                  arodata_okP by ProgWorld.arodata_okP_of_S.

   ROUTE (C) (a Theorem Labs lane truth audit 11:02Z, a Theorem Labs lane 11:10Z; recipe (internal path)
   L3-recipe.md (a working note, not in this delivery)): the cut's runtime conjunct is A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.  The stage's one shadow read is the
   write permission of [Sfr fr + 68, Sfr fr + 254) at mem3, inside cut_shadow's (F) disjunct at (6, c_fpos cx)
   (frames S3 = own6 cx, frame_addr ly3 6 (c_fpos cx) = fr; local fact HFsh); it comes from ctl_rt_C's cut_shadow
   conjunct.  asan_cells / ro_agree are ctl_rt_C's first and last conjuncts.

   SECTION HYPOTHESES (each is ACtl.v's Section hypothesis of the same name and text; the top supplies it)
   - RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a -- for the exit's arodata_okS.
   - LAWS : Reusable.YG0d.AR_laws segs B -- the core's AR law record, which kitmem_own6, frames_bounds, al_blocks,
     sep_block_frame, the kitmem_rng_frame* lemmas, ajournal_of_fsteps and ctl_rt_C_of_AR take.
   - TFIB_SYMS : A.AF0m.CtrlTSyms B -- the core's symbol record, which ctl_rt_C_of_AR takes.

   CITED BY NAME (proof-internal): Seg/R2F.r2_evt_F; Seg/R2.v's lib-level lemmas r2_mode_rng, r2_ro8, r2_ba_sub,
   r2_rw_CB, r2_addr_z (Seg/R2.v:22-331, before its frame-route Imports); asan_set_shadowF.asan_set_shadow_00_holds_F,
   memset.memset_holds; ProgBridge (cfg_at_MS, img_vis_W, rng_of_visible, rng_bytes_RNG_W, fp_avoids_RNG_W);
   YA0nR.SRr_xregs_eqv; ProgWorld (ajournal_of_fsteps, pws_fsteps_mem, arodata_okP_of_S); ProgWorldCtlRtC
   (ctl_rt_C_of_AR); YCbq (frames_bounds, sep_block_frame, req_size_pos); YG0d.al_blocks; Kit (kit_wx,
   kit_frac_move); KitMem (kitmem_lift, kitmem_own6, kitmem_rng_win, kitmem_rng_frame, kitmem_rng_frame_sh,
   kitmem_awr_frame, kitmem_not_outside, kitmem_bytes_munch, kitmem_spill_munch, kitmem_frac_keep,
   kitmem_arodataS_journal, kitmem_addressable_mrd, kitmem_mrd_munch); Lib.Frame.rw_cells_transport.
   READS NO STAND-IN VALUE: no ts_gp / TFIB_GP, pc_wrap_*, pc_stack_malloc, ts_zsh / AF0m row, Tfib_owned_static or
   port_core_refused literal; gp passes through FRAC symbolically.

   CLOSURE (glue closure rule, a Theorem Labs lane 23:32Z, porter 23:38Z / 23:40Z): every Require is qualified (no Import /
   Export of a project module); no statement here names a frame-route identifier.  The twin modules (YK11 YK1b YM05
   YO09) are loaded by absolute Require lines and written through the fully qualified aliases CK11 / CK1b / CM05 /
   CO09; lib/Lib's modules through LMState / LRegs / LFrame / LStep / LCells / LMem / LEF.  Measured closure (a
   scan of the Require lines from this file): 470 files; no lib/AZ/AsanW file, no W6 file, no cut-free file
   (SegCF / *_cfw / Cf*; Reusable/R/Cfg.v is the donor's config module, also in A2.v's and KitMem.v's closure);
   lib/AZ only LibA/AcctCore (via Lib/ExecF), Spec/AsanCtrl, Spec/AsanCtrlProps, Spec/STree; AsanRT.v is the v1.9
   one (mcs 30).  Frame-route files of record come through Seg/R2F.v -> Seg/R2.v (SlotInv, Tac_slot, Tac_b5,
   Tac_fs, Tac_fsfree, RcPro, RcAsanFPLib, AsanRTInv, PContract, Contract, FrameAPI, KindBGlue, AsanLift, BzBridge,
   MemNorm, MemNormF); their blobs are named in the commit message.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are fully qualified (CK11 / Reusable.YG0d) everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/R2.v   -- hits only inside comments.

   BUILD STATE (honest): type-check on a working branch shell merged on this branch (cb build); the build of
   record is cbrec's (log and .prov named in the commit).  Print Assumptions glue_seg_R2: lib/A/ACtlG/L3W01Audit.v.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
(* route (C): the cut's runtime conjunct, its producer from AR, the symbol record it takes *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorld A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R2F A.Prog.Seg.R2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_set_shadow_cF A.Prog.asan_set_shadowF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.memset.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* The twin-safe module names (fully qualified). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module LMState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRegs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module SR2 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R2.
Module SR2F := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R2F.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.

(* The core's segment list, as ACtlCut.v:76 and ACtl.v:165 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Local lemmas (none is a Kit / KitMem helper). *)

(* Two values a register pins agree modulo 2 ^ 64. *)
Lemma r2g_rgv_mod : forall (regs : bvmap 5 word) (r : bv 5) (A A' : Z),
  ACtlCut.rgv regs r A -> ACtlCut.rgv regs r A' -> 0 <= A < 2 ^ 64 -> A' mod 2 ^ 64 = A.
Proof.
  intros regs r A A' H H' HA. unfold ACtlCut.rgv in H, H'. rewrite H in H'.
  apply (f_equal bv_unsigned) in H'. rewrite !Z_to_bv_unsigned in H'. unfold bv_wrap in H'.
  change (bv_modulus 64) with (2 ^ 64) in H'. rewrite <- H'. apply Z.mod_small. exact HA.
Qed.

(* A spill read off register 9 is the q64 at the base the cut pins in register 9. *)
Lemma r2g_spill_q64 : forall (regs : bvmap 5 word) (m : word -> option byte) (A off v : Z),
  ACtlCut.rgv regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m A off v HA H0 Hoff Hhi (A1 & HA1 & Hq).
  pose proof (r2g_rgv_mod regs 9 A A1 HA HA1 ltac:(lia)) as EA.
  assert (E : A1 = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite LMem.length_le8 in Hq1.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hq1.
    Z.div_mod_to_equations. lia. }
  subst A1. exact Hq.
Qed.

(* An addressable range stays addressable across a munch that avoids its shadow bytes. *)
Lemma r2g_addr_keep : forall (WR : list LFrame.ivl) (m m' : word -> option byte) p n,
  ART.addressable m p n -> LFrame.munch WR m m' ->
  (forall i, 0 <= i < n -> LFrame.outside WR (ART.shadow_addr (p + i))) -> ART.addressable m' p n.
Proof.
  intros WR m m' p n HA MU HO. apply (A.ACtlG.KitMem.kitmem_addressable_mrd m m' p n HA). intros i Hi.
  pose proof HA as (_ & _ & _ & H). destruct (H i Hi) as (Ha & _).
  pose proof (A.AsanRTFacts.in_shadow_range _ (A.AsanRTFacts.shadow_of_app (p + i) Ha)) as R.
  apply (A.ACtlG.KitMem.kitmem_mrd_munch WR m m' _ MU); [lia | exact (HO i Hi)].
Qed.

(* The shadow byte of a byte at least 8 below fr + 544, or at or above fr + 2032, is off the window
   [Sfr fr + 68, Sfr fr + 254) the fill writes. *)
Lemma r2g_sh_apart : forall fr x, x + 8 <= fr + 544 \/ fr + 2032 <= x ->
  LFrame.outside [(ACtlCutP.Sfr fr + 68, ACtlCutP.Sfr fr + 68 + 186)] (ART.shadow_addr x).
Proof.
  intros fr x H. cbn [LFrame.outside]. split; [|exact I].
  unfold ACtlCutP.Sfr, ART.shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Section GlueR2.

(* ACtl.v's Section shape (ACtl.v:172-176), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:219-220, :231-232), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A814f8 := (ACtlCutP.C_A814f8 B).
Local Notation C_A8152c := (ACtlCutP.C_A8152c B).

(* ACtl.v's Section hypotheses this stage reads, same names and texts: the read-only span is image bytes
   (RELRO_IMG, for the exit's arodata_okS), the core's AR laws (LAWS) and symbol record (TFIB_SYMS, for
   ctl_rt_C_of_AR). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_R2 : forall POST, CF POST C_A8152c -> CF POST C_A814f8.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut C_A814f8 (ACtlCutP.v:1188-1206), 28 conjuncts. *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A814f8] in Hbody.
  destruct Hbody as (HP & HFRAC & Hcn & Ha0 & HOUR & S152 & R18 & Q2656 & R21 & HCUR & S48 & S128 & HPRO & R23 &
    S144 & S192 & Hidb & Hjk72 & S280 & S240 & Hjy & Hjk32 & S56 & S88 & S80 & S72 & S200 & S216).
  pose proof Hrt as (HAC & HSW & _ & HRO).
  pose proof HFRAC as (A & sp & _ & _ & _ & _ & _ & R9 & _ & _ & _ & _ & _ & HAS & HspA & HfrA & HA416 & HSsp & HSapp &
    _ & _ & _ & _ & _ & Hsh & _).
  unfold ACtlCutP.FRAME_BYTES, ART.APPMEM_END in HfrA, HSapp.
  (* G2: the owned class-6 frame. *)
  destruct (A.ACtlG.KitMem.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & Efr3 & Hfr4096 & Hfr32 & Hfceil & Hceil).
  pose proof HJ as (HAR & _).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & _ & Hfapp).
  rewrite Efr3 in Hfapp.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil, Hfapp.
  unfold A.ACfn.LLVMF_STK in Hceil.
  pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as (Hce & _). unfold Reusable.YG0f.ASAN_CEIL in Hce.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Hfapp.
  (* the frame shadow Sfr fr = fr / 8 + ASAN_K: shadow memory, apart from the frame, below the stack *)
  assert (ESh : ACtlCutP.Sfr fr = fr / 8 + 2147450880) by reflexivity.
  assert (Hdiv : 8 * (fr / 8) = fr) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (HSh0 : 2147450880 <= ACtlCutP.Sfr fr) by (rewrite ESh; lia).
  assert (HShmax : ACtlCutP.Sfr fr + 512 <= 0x10007fff8000) by (rewrite ESh; lia).
  assert (HQA : ACtlCutP.Sfr fr + 68 + 186 <= A) by (rewrite ESh; lia).
  assert (HQfr : fr + 4096 <= ACtlCutP.Sfr fr + 68 \/ ACtlCutP.Sfr fr + 68 + 186 <= fr) by (rewrite ESh; lia).
  assert (HSHin : forall x, ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 512 -> ART.in_shadow x).
  { intros x Hx. rewrite ESh in Hx.
    unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG. lia. }
  (* route (C): the frame shadow [Sfr fr, Sfr fr + 512) is cut_shadow's (F) disjunct at the owned class-6 frame
     (frames S3 holds (6, c_fpos cx), frame_addr ly3 6 (c_fpos cx) = fr) *)
  assert (HFsh : forall y, ACtlCutP.Sfr fr <= y < ACtlCutP.Sfr fr + 512 -> A.ACtlRtC.cut_shadow B ly3 S3 y).
  { intros y Hy. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite Efr3. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512. rewrite ESh in Hy.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia. }
  (* the input block (the lib pre): empty, or a live block in an application band apart from the frame *)
  pose proof HB as ((_ & _ & _ & _ & Hinb & Hlen & _) & _).
  assert (HBLK : ACtlCut.c_n cx = 0 \/
                 (0 < ACtlCut.c_n cx /\
                  (ACtlCut.c_p cx + ACtlCut.c_n cx <= 0x7fff7000 \/ 0x10007fff8000 <= ACtlCut.c_p cx) /\
                  (ACtlCut.c_p cx + ACtlCut.c_n cx <= fr \/ fr + 4096 <= ACtlCut.c_p cx))).
  { destruct Hinb as [(H0 & _) | (Hn & Hin)]; [left; exact H0 | right].
    assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3))
      by exact (Permutation_in _ (Permutation_sym HP) Hin).
    destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (_ & Hp4096 & Hpceil & Hpapp & _).
    pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hin3 Hin6)
      as Hsep.
    pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as Hrs.
    unfold Reusable.YG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Efr3 in Hsep.
    change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hsep.
    unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hpapp.
    lia. }
  (* the run's two read cells: the count [fr + 2656] = 11 and the spill [A + 152] = Q *)
  pose proof (SR2.r2_ro8 mem3 (fr + 2656) (Z_to_bv 64 11) Q2656) as RC.
  pose proof (SR2.r2_ro8 mem3 (A + 152) (Z_to_bv 64 (ACtlCutP.Sfr fr + 68))
                (r2g_spill_q64 regs3 mem3 A 152 _ R9 ltac:(lia) ltac:(lia) ltac:(lia) S152)) as RQ.
  (* the 186 frame-shadow bytes the fill writes: present (FRAC) and writable (shadow_rw) *)
  destruct Hsh as (sh & Bsh & Lsh).
  change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat in Lsh.
  pose proof (SR2.r2_ba_sub mem3 (ACtlCutP.Sfr fr) sh 68 186 Bsh ltac:(lia)) as Bx.
  replace (ACtlCutP.Sfr fr + Z.of_nat 68) with (ACtlCutP.Sfr fr + 68) in Bx by lia.
  assert (Lx : length (firstn 186 (skipn 68 sh)) = 186%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (CHQ : LStep.rw_cells A.Img0.rsegs mem3 (ACtlCutP.Sfr fr + 68)
                  [LCells.CB 186 (firstn 186 (skipn 68 sh))]).
  { replace (LCells.CB 186 (firstn 186 (skipn 68 sh)))
      with (LCells.CB (length (firstn 186 (skipn 68 sh))) (firstn 186 (skipn 68 sh))) by (rewrite Lx; reflexivity).
    apply SR2.r2_rw_CB; [exact Bx|]. rewrite Lx. change (Z.of_nat 186) with 186.
    split; [lia|]. split; [lia|]. intros i Hi.
    exact (proj1 (HSW (ACtlCutP.Sfr fr + 68 + i) (HFsh (ACtlCutP.Sfr fr + 68 + i) ltac:(lia))
                      (HSHin (ACtlCutP.Sfr fr + 68 + i) ltac:(lia)))). }
  (* the run, at RNG_W (w_H W3), from the canonical map mkR_of regs3 *)
  assert (HRUN : LEF.evtF A.Img0.rsegs (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
    (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
       ms' = LMState.MS R CK11.fp_regs (Z_to_bv 64 0x8152c) CK11.fp_csr None m' (CK11.seg_rom A.Img0.rsegs) /\
       CK11.getr R 2 = CK11.getr regs3 2 /\ CK11.getr R 3 = CK11.getr regs3 3 /\
       CK11.getr R 4 = CK11.getr regs3 4 /\ CK11.getr R 8 = CK11.getr regs3 8 /\
       CK11.getr R 9 = CK11.getr regs3 9 /\ CK11.getr R 19 = CK11.getr regs3 19 /\
       CK11.getr R 21 = CK11.getr regs3 21 /\ CK11.getr R 22 = CK11.getr regs3 22 /\
       CK11.getr R 25 = CK11.getr regs3 25 /\ CK11.getr R 26 = CK11.getr regs3 26 /\
       CK11.getr R 18 = Z_to_bv 64 (SM.mrow (ACtlCut.c_in cx)) /\
       LFrame.munch [(ACtlCutP.Sfr fr + 68, ACtlCutP.Sfr fr + 68 + 186)] mem3 m' /\
       LFrame.wmono A.Img0.rsegs mem3 m' /\
       LStep.rw_cells A.Img0.rsegs m' (ACtlCutP.Sfr fr + 68) [LCells.CB 186 (repeat (Z_to_bv 8 0) 186)])
    (LMState.MS (LRegs.mkR_of regs3) CK11.fp_regs (Z_to_bv 64 0x814f8) CK11.fp_csr None mem3
       (CK11.seg_rom A.Img0.rsegs))).
  { unfold LRegs.mkR_of.
    eapply LEF.evtF_mono.
    - eapply (SR2F.r2_evt_F (A.Prog.asan_set_shadowF.asan_set_shadow_00_holds_F A.Prog.memset.memset_holds)
                (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)))
        with (A := A) (c := fr + 2656) (Q := ACtlCutP.Sfr fr + 68) (md := SM.mode (ACtlCut.c_in cx))
             (junk := firstn 186 (skipn 68 sh)).
      (* registers *)
      + exact Ha0.
      + exact R9.
      + exact R18.
      + exact R23.
      (* bounds *)
      + exact (SR2.r2_mode_rng _).
      + lia.
      + lia.
      (* memory *)
      + exact RC.
      + exact RQ.
      + intros i Hi. apply HSHin. lia.
      + exact CHQ.
      + exact HAC.
      + exact HRO.
      (* footprint *)
      + exact (A.ProgBridge.rng_bytes_RNG_W _).
      + apply (A.ACtlG.KitMem.kitmem_rng_frame B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 2656) 8
                 HAR Hin6); rewrite Efr3; [lia | change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia].
      + eapply A.ACtlG.KitMem.kitmem_rng_win; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia].
      + exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3)).
      + apply A.ProgBridge.rng_of_visible. unfold A.Prog.asan_set_shadow_cF.ASAN_SET_SHADOW_K.
        match goal with |- context [bv_unsigned ?x] => pose proof (bv_unsigned_in_range 64 x) as Rx end.
        change (bv_modulus 64) with (2 ^ 64) in Rx.
        split; [lia|]. split; [lia|]. intros a Ha. lia.
      + apply (A.ACtlG.KitMem.kitmem_rng_frame_sh B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx)
                 (ACtlCutP.Sfr fr + 68) 186 HAR Hin6); rewrite Efr3;
          [change (ART.shadow_addr fr) with (ACtlCutP.Sfr fr); lia
          | change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512; change (ART.shadow_addr fr) with (ACtlCutP.Sfr fr);
            lia].
    - intros s (R & m' & Es & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K25 & K26 & K18 & MU & WM & _ & RW).
      exists R, m'.
      split; [exact Es|].
      split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
      split; [exact K19|]. split; [exact K21|]. split; [exact K22|]. split; [exact K25|]. split; [exact K26|].
      split; [exact K18|].
      split; [exact MU|]. split; [exact WM | exact RW]. }
  (* G3: the cut's configuration in the run's state form, the walk moved to the run's map mkR_of regs3. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A814f8) with 0x814f8.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x814f8) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
  (* G4: the lift (KitMem.kitmem_lift keeps the run's fsteps for ajournal_of_fsteps / pws_fsteps_mem). *)
  apply (A.ACtlG.KitMem.kitmem_lift A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _
           (POST cx) HRUN (A.ProgBridge.fp_avoids_RNG_W _)).
  intros ms' md' Hrun HQ0 Hsbm.
  pose proof (proj1 (A.ProgWorld.pws_fsteps_mem segs (Reusable.YA0n.w_H W3) _ _ _ Hrun
                       (A.ProgBridge.fp_avoids_RNG_W _))) as Hgrow.
  destruct HQ0 as (R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K25 & K26 & K18 & MU & WM & RW).
  subst ms'. cbn [ms_mem LMState.MS] in Hgrow.
  (* G5: the end state is the exit cut's state at the run's map R and memory m'. *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A8152c) R m' md') (POST cx)).
  set (WR := [(ACtlCutP.Sfr fr + 68, ACtlCutP.Sfr fr + 68 + 186)]) in *.
  (* every written byte is in [Sfr fr + 68, Sfr fr + 254) *)
  assert (HWin : forall a, ~ LFrame.outside WR a -> ACtlCutP.Sfr fr + 68 <= a < ACtlCutP.Sfr fr + 68 + 186).
  { intros a Ha. destruct (A.ACtlG.KitMem.kitmem_not_outside _ _ Ha) as (lo & hi & Hin & Hr).
    destruct Hin as [Ei | []]. injection Ei as <- <-. exact Hr. }
  (* the exit journal: a Theorem Labs lane's ajournal_of_fsteps; the window is the owned frame's shadow *)
  assert (Hawr : forall a, 0 <= a < 2 ^ 64 -> ~ LFrame.outside WR a ->
            Reusable.YCbq.awr_byte A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
              (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
              (ACtlCut.own6 cx) a).
  { intros a _ Hw. pose proof (HWin a Hw) as Ha.
    apply (A.ACtlG.KitMem.kitmem_awr_frame _ _ _ _ _ _ (ACtlCut.own6 cx) 6 (ACtlCut.c_fpos cx) fr a
             (eq_sym Efr3) (or_introl eq_refl)).
    right. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
    change (ART.shadow_addr fr) with (ACtlCutP.Sfr fr). lia. }
  assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { match type of Hrun with Reusable.YK04R.fsteps _ _ ?s0 ?s1 =>
      exact (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
               (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
               (ACtlCut.own6 cx) ly3 S3 W3 s0 s1 md3 md' k _ WR HJ Hrun (A.ProgBridge.fp_avoids_RNG_W _) MU Hsbm
               Hawr)
    end. }
  apply (HX cx idx fr k ly3 S3 W3 R m' md' HB).
  - (* journal *)
    exact HJ'.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: kmax 0 on both cuts *)
    exact Hk.
  - (* the exit body C_A8152c (ACtlCutP.v:1210-1226), 26 conjuncts *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A8152c].
    assert (R9R : ACtlCut.rgv R 9 A) by (unfold ACtlCut.rgv in *; rewrite K9; exact R9).
    split; [exact HP|].
    split.
    { (* FRAC: registers through the run's keeps, memory by shape (the frame shadow re-read by growth) *)
      apply (A.ACtlG.KitMem.kitmem_frac_keep B cx fr fr R mem3 m' WR
               (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26) MU Hgrow ltac:(lia)).
      - intros A' HA' x Hx. cbn [LFrame.outside]. split; [|exact I].
        pose proof (r2g_rgv_mod R 9 A A' R9R HA' ltac:(lia)) as EA'.
        clear - EA' Hx HQA HSh0 HA416 HSapp. Z.div_mod_to_equations. lia.
      - intros x Hx. cbn [LFrame.outside]. split; [lia | exact I].
      - intros x Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
    split; [exact Hcn|].
    split.
    { (* OURb: our[]'s 6 frame bytes at fr + 2624 *)
      unfold ACtlCutP.OURb in HOUR |- *. apply (A.ACtlG.KitMem.kitmem_bytes_munch WR mem3 m' _ _ HOUR MU).
      rewrite SM.OUR_length. intros x Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
    split; [unfold ACtlCut.rgv in *; rewrite K21; exact R21|].
    split.
    { destruct HCUR as (Hc7 & C22 & C25). split; [exact Hc7|].
      unfold ACtlCut.rgv in *. split; [rewrite K22; exact C22 | rewrite K25; exact C25]. }
    split.
    { apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs3 R mem3 m' 48 _ A S48 R9 ltac:(lia) ltac:(lia) ltac:(lia)
               MU K9).
      intros x Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
    split.
    { (* out[]'s first 1488 bytes: the fill wrote Sfr fr + 68 .. 253 = 00 (as Seg/R2.v:584-588) *)
      pose proof RW as ((_ & Hzb) & _). cbn [LCells.cells_bytes LCells.cbytes] in Hzb. rewrite app_nil_r in Hzb.
      apply (SR2.r2_addr_z m' (fr + 544) 186 1488); [reflexivity | lia | clear - Hfr32; Z.div_mod_to_equations; lia
        | unfold ART.APPMEM_END; lia | |].
      - intros i Hi. unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END. lia.
      - replace (ART.shadow_addr (fr + 544)) with (ACtlCutP.Sfr fr + 68)
          by (unfold ACtlCutP.Sfr, ART.shadow_addr; clear - Hdiv; Z.div_mod_to_equations; lia).
        exact Hzb. }
    split.
    { apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs3 R mem3 m' 128 _ A S128 R9 ltac:(lia) ltac:(lia) ltac:(lia)
               MU K9).
      intros x Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
    split.
    { (* PRO: the spills through register 9, our[]'s shadow byte Sfr fr + 328 and the input block's shadow off
         the window, the input bytes in an application band *)
      destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg & P184 & P256 & P264 &
        P272 & P32).
      unfold ACtlCutP.PRO.
      repeat (match goal with |- _ /\ _ => split end);
        try lazymatch goal with
        | |- ACtlCutP.spill _ _ ?off _ =>
            match goal with
            | Hs : ACtlCutP.spill regs3 mem3 off _ |- _ =>
                apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs3 R mem3 m' off _ A Hs R9 ltac:(lia) ltac:(lia)
                         ltac:(lia) MU K9);
                let x := fresh "x" in let Hx := fresh "Hx" in
                intros x Hx; cbn [LFrame.outside]; split; [lia | exact I]
            end
        end.
      - apply (r2g_addr_keep WR mem3 m' _ _ Pad MU). intros i Hi. apply r2g_sh_apart. lia.
      - apply (A.ACtlG.KitMem.kitmem_bytes_munch WR mem3 m' _ _ Pin MU). rewrite <- Hlen.
        intros x Hx. cbn [LFrame.outside]. split; [|exact I].
        destruct HBLK as [H0 | (_ & Hband & _)]; [lia|]. lia.
      - intros Hn0. apply (r2g_addr_keep WR mem3 m' _ _ (Pg Hn0) MU). intros i Hi. apply r2g_sh_apart.
        destruct HBLK as [H0 | (_ & _ & Hsep)]; [lia|]. lia. }
    (* the spills [A + 152], [A + 144], [A + 192] and the frame records: none is written *)
    split.
    { apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs3 R mem3 m' 152 _ A S152 R9 ltac:(lia) ltac:(lia) ltac:(lia)
               MU K9).
      intros x Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
    split.
    { apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs3 R mem3 m' 144 _ A S144 R9 ltac:(lia) ltac:(lia) ltac:(lia)
               MU K9).
      intros x Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
    split.
    { apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs3 R mem3 m' 192 _ A S192 R9 ltac:(lia) ltac:(lia) ltac:(lia)
               MU K9).
      intros x Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
    split.
    { destruct Hidb as (idb & Hidb'). exists idb.
      apply (LFrame.rw_cells_transport segs WR mem3 m' _ _ Hidb' MU WM).
      cbn [LCells.cells_size LCells.csize LFrame.disjoint_from]. split; [lia | exact I]. }
    split.
    { destruct Hjk72 as (jk & Hjk'). exists jk.
      apply (LFrame.rw_cells_transport segs WR mem3 m' _ _ Hjk' MU WM).
      cbn [LCells.cells_size LCells.csize LFrame.disjoint_from]. split; [lia | exact I]. }
    split.
    { apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs3 R mem3 m' 280 _ A S280 R9 ltac:(lia) ltac:(lia) ltac:(lia)
               MU K9).
      intros x Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
    split.
    { apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs3 R mem3 m' 240 _ A S240 R9 ltac:(lia) ltac:(lia) ltac:(lia)
               MU K9).
      intros x Hx. cbn [LFrame.outside]. split; [lia | exact I]. }
    split.
    { destruct Hjy as (jy & Hjy'). exists jy.
      apply (LFrame.rw_cells_transport segs WR mem3 m' _ _ Hjy' MU WM).
      cbn [LCells.cells_size LCells.csize LFrame.disjoint_from]. split; [lia | exact I]. }
    split.
    { destruct Hjk32 as (jk & Hjk'). exists jk.
      apply (LFrame.rw_cells_transport segs WR mem3 m' _ _ Hjk' MU WM).
      cbn [LCells.cells_size LCells.csize LFrame.disjoint_from]. split; [lia | exact I]. }
    (* R1's [A + 56] / [A + 88] / [A + 80] / [A + 72] and A4's [A + 200] / [A + 216] *)
    do 6 (split; [
      lazymatch goal with
      | |- ACtlCutP.spill _ _ ?off _ =>
          match goal with
          | Hs : ACtlCutP.spill regs3 mem3 off _ |- _ =>
              apply (A.ACtlG.KitMem.kitmem_spill_munch WR regs3 R mem3 m' off _ A Hs R9 ltac:(lia) ltac:(lia)
                       ltac:(lia) MU K9);
              let x := fresh "x" in let Hx := fresh "Hx" in
              intros x Hx; cbn [LFrame.outside]; split; [lia | exact I]
          end
      end|]).
    (* s2 = mrow (0x8151c; meta_fill_00 keeps s2) *)
    exact K18.
  - (* ctl_rt_C at the exit (same ly3 S3, memory m'): ctl_rt_C_of_AR at the exit journal's AR, with the entry's
       arodata_okS carried along the journal (KitMem.kitmem_arodataS_journal) *)
    pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _) & _).
    pose proof HJ' as (HAR' & _).
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 m' md' HAR'
             (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _
                (A.ACtlG.KitMem.kitmem_arodataS_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ' HROS)
                (Z.le_refl _) (Z.le_refl _))).
Qed.

End GlueR2.
