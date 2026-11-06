(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module names and numbers changed; 1086 of its 1232 lines of code are new or changed and 1651 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R7tail.v; 1150 of its 1202 lines of code are new or changed and 1180 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R7.v, with its module names changed; 329 of its 397 lines of code are new or changed and 1134 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/P1_70.v, with its module names and addresses changed; 226 of its 260 lines of code are new or changed and 363 lines of the source are left out. *)
(* lib/A/ACtlG/A3.v -- GLUE for stage seg_A3 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:651,
   `Hypothesis seg_A3 : forall POST, CF POST C_A810e4 -> CF POST C_A80f88`).  Written by a Theorem Labs lane's glue lane
   (piece W0/W1); single writer.  The pattern is
   glue-pattern.md (a working note, not in this delivery), the worked examples lib/A/ACtlG/A5.v / A2.v.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_A3 : forall POST, CF POST C_A810e4 -> CF POST C_A80f88
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_A3.  Segment A3 is 0x80f88 -> 0x810e4: the ASan prologue of the class-6 fake frame (87 instructions:
   the spill `sd s6,304(s1)`, the frame header 0x41b58ab3 / 0x11b66 / 0x80edc at fr / fr + 8 / fr + 16, s3 = S(fr),
   the 68 single-byte shadow stores at S(fr) .. S(fr) + 67, s9 = S(fr) + 68) and the call of meta_fill_f8
   (__asan_set_shadow_f8, 0x55008) at 0x810e0 that fills S(fr) + 68 .. S(fr) + 254 with 0xf8.

   RULE 24 (released proofs first): proof-index LLVMFuzzerTestOneInput (index v5, built 2026-10-28 20:16:23Z
   from e966c513ee6, ossv/recipes@a8831f7c5c), second-agent check a Theorem Labs lane 21:10Z CONFIRM: the released ASan
   donor is cgif/cgif_file_fuzzer at origin/ossv/recipes c8557374ad2e; its walk lifts no outside-proved run, so this
   glue has no donor counterpart.  Its pieces are the donor's SRr (YA0n) and ajournal (YCbq), a Theorem Labs lane's kit and
   bridge (Reusable/YA0nR.v SRr_xregs_eqv / SRr_fsteps; A/ProgBridge.v cfg_at_MS, tfibsegs_rsegs, RNG_W,
   rng_of_visible, img_vis_W, rng_bytes_RNG_W, fp_avoids_RNG_W), a Theorem Labs lane's ProgWorld (ajournal_of_fsteps,
   pws_fsteps_mem), a Theorem Labs lane's footprint run, and the shared kits lib/A/ACtlG/Kit.v and lib/A/ACtlG/KitMem.v.

   THE RUN.  a Theorem Labs lane's mechanical v1.9 re-run A.Prog.Seg.A3F.a3_evt_F (Seg/A3F.v:164-183), Required, not
   assumed: A3.a3_evt (Seg/A3.v:217) under StepF, with the callee's footprint contract as its first premise.  That
   premise is discharged OUTRIGHT by the proved closed theorem
   `A.Prog.asan_set_shadowF.asan_set_shadow_f8_holds_F A.Prog.memset.memset_holds` (no split, a Theorem Labs lane's rule).
   Its footprint premises (premise rows segment-F-premises-A.tsv (a working note, not in this delivery), A3)
   at RNG := ProgBridge.RNG_W (w_H W3):
     rng_bytes RNG                       ProgBridge.rng_bytes_RNG_W
     [A + 304, A + 312)  the spill cell  KitMem.kitmem_rng_win (inside the LLVMF stack window, PREFC's A bounds)
     [fr, fr + 24)       the header      KitMem.kitmem_rng_frame (the owned class-6 frame)
     [S3, S3 + 68), [S3 + 68, S3 + 255)  KitMem.kitmem_rng_frame_sh (the frame's shadow), S3 = Sfr fr
     [IMG_LO, IMG_HI)    the image       ProgBridge.img_vis_W + rng_of_visible
     [sp - 0, sp)        callee window   empty (ASAN_SET_SHADOW_K = 0): range_visible of length 0
   The run is stated over ctrl's lib/A/Reusable/YK11 class FPState; its fx is instantiated with
   `A.Reusable.YK11.mkFP CK11.fp_regs CK11.fp_csr` (CK11 = the core's YK11), and its post is then rewritten with
   `change` from ctrl's getr / seg_rom / fp_regs / fp_csr to the core's (same bodies; the projections reduce by iota).

   THE PROOF, step by step (glue-pattern.md section 3)
   G1  unfold the entry cut C_A80f88 (ACtlCutP.v:1105-1117): live list, PREFC (A, sp and their bounds, the saved
       registers, c_n <= ANMAX), s6 = fr, fr mod 32 = 0, s5 = sel (= fr), s7 = p, s8 = n, the input bytes and their
       addressability.  The body's own `exists A, .. fr + FRAME_BYTES <= A` is not PREFC's A and is not used.
   G2  the run's premises: KitMem.kitmem_own6 (fr = frame_addr ly3 6 pos, 4096 <= fr, fr + 4096 <= alloc_ceiling <=
       c_sp - LLVMF_STK), YG0d.al_frames (the frame in one application band, its bytes present), the local lemma
       a3g_frame6_above_img (IMG_HI <= fr, from ProgWorld_Fs.ctl_frame_above_img), ctl_rt_C's cut_shadow (the
       frame's shadow bytes readable, region HFsh);
       the four write regions as lib/A/Tk/UL junk cells (stage-local a3g_junk: lib/Lib stk_carve, then
       CellBridge.rw_cells_lib_ul) over the lib/Lib stk windows KitMem.kitmem_stk_of_journal (spill),
       KitMem.kitmem_stk_of_present (header) and ctl_rt_C's cut_shadow (shadow); the footprint ranges above; the input block
       apart from the write set by KitMem.kitmem_input_apart.
   G3  ProgBridge.cfg_at_MS, then YA0nR.SRr_xregs_eqv from the cut's map regs3 to the run's mkR_of regs3.
   G4  KitMem.kitmem_lift at RNG_W (w_H W3) (fp_avoids by ProgBridge.fp_avoids_RNG_W); its continuation gives the
       run's fsteps, A3.KA (the write set WR = [A+304, A+312) ++ [fr, fr+24) ++ [S3, S3+68) ++ [S3+68, S3+255), the
       written words and bytes, the register post) and same_but_materialized.
   G5  the exit cut C_A810e4 (ACtlCutP.v:1121-1133) at the run's end map R, memory mem' and model md', the same cx,
       idx, fr, k, ly3, S3, W3:
         journal  ProgWorld.ajournal_of_fsteps over WR: the spill byte by KitMem.kitmem_awr_win (LLVMF window), the
                  header and shadow bytes by KitMem.kitmem_awr_frame (the owned class-6 frame and its shadow);
         frames, frame law, k bound   unchanged (own6 and kmax 0 on both cuts);
         body     live list unchanged; FRAHC (header 0x41b58ab3) built BY SHAPE from PREFC's A / sp (registers
                  2 3 4 8 through the run's keeps, 9 19 26 written), fr mod 32 from the entry body, fr + FRAME_BYTES
                  <= A from kitmem_own6 and PREFC's c_sp - 432 <= A, the spill / header / function words from KA,
                  the 392 frame-shadow bytes from the exit's ctl_rt_C at mem' (lib/Lib stk_bytes), the saved registers by
                  KitMem.kitmem_bytes_munch; c_n <= ANMAX from PREFC; s2 = -8, s4 = -14, s6 = fr, s9 = S3 + 68 from
                  the run; s5, s7, s8 through its keeps; the input bytes by kitmem_bytes_munch and their
                  addressability by kitmem_addressable_mrd (input block apart from WR, its shadow apart from the
                  frame's shadow);
         ctl_rt_C A.ProgWorldCtlRtC.ctl_rt_C_of_AR at the exit journal's AR (same ly3 S3, memory mem'), with the
                  entry's arodata_okS carried along the journal (KitMem.kitmem_arodataS_journal, RELRO_IMG) and made
                  arodata_okP by ProgWorld.arodata_okP_of_S.

   ROUTE (C) (a Theorem Labs lane truth audit 11:02Z, a Theorem Labs lane 11:10Z; recipe (internal path)
   L3-recipe.md (a working note, not in this delivery)): the cut's runtime conjunct is A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.  The stage's shadow reads are the
   owned class-6 frame's shadow [Sfr fr, Sfr fr + 255) at mem3 and [Sfr fr, Sfr fr + 392) at mem', both inside
   cut_shadow's (F) disjunct at (6, c_fpos cx) (frames S3 = own6 cx, frame_addr ly3 6 (c_fpos cx) = fr; local fact
   HFsh).  The entry's are read from ctl_rt_C's cut_shadow conjunct at mem3, the exit's from the exit's ctl_rt_C.

   SECTION HYPOTHESES (each is ACtl.v's Section hypothesis of the same name and text; the top supplies it)
   - RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a -- for the exit's arodata_okS.
   - LAWS : Reusable.YG0d.AR_laws segs B -- the core's AR law record, which kitmem_own6, al_frames, the rng lemmas,
     ajournal_of_fsteps and ctl_rt_C_of_AR take.
   - TFIB_SYMS : A.AF0m.CtrlTSyms B -- the core's symbol record, which ctl_rt_C_of_AR takes.
   The owned frame above the image (IMG_HI <= fr: a3_evt_F's premise `0x5fe000 <= fr`, kitmem_input_apart's
   premise) is a Theorem Labs lane's PROVED, premise-free A.ProgWorld_Fs.ctl_frame_above_img, cited by name.

   NOT USED: rt_of_core (the run's runtime premises asan_cells / ro_agree are ctl_rt_C's carried facts); the Seg/*.v
   keep lemmas (the world side is KitMem's).

   CLOSURE (glue closure rule, a Theorem Labs lane 23:32Z, porter 23:38Z / 23:40Z): every Require is qualified (no Import /
   Export of a project module); no statement here names a frame-route identifier.  The twin modules this file names
   (YK11 YK1b YM05 YO09) are loaded by absolute Require lines and written through the fully qualified aliases CK11 /
   CK1b / CM05 / CO09; lib/Lib's modules and lib/A/Tk/UL's through absolute aliases; ctrl's YK11 (the run's)
   through AK11.  Frame-route files of record in the closure (through Seg/A3F.v), blobs at the glue worktree HEAD
   f32c86d5c0b: Seg/A3F.v 0c88255b8c0, Seg/A3.v 0d4714ea12b, SlotInv.v 4cf85db229a, SlotModel.v 04dc7903221,
   Seg/Tac_slot.v de02ff45188, Seg/Tac_fs.v 8bd492a660d, AsanRT.v b67d26f8ec7 (mcs 30), AsanRTInv.v 2a8602e8526,
   Contract.v fa6fd478d9a, FrameAPI.v f6ffefa9bb4, MemNorm.v cb518fc0304, MemNormF.v 9e5ea0ff243; the callee files
   asan_set_shadow_c.v 7153a91e7cc, asan_set_shadow_cF.v 2400425d11d, asan_set_shadowF.v 96806d7fcf8, memset.v
   b36e4a246bb; Tk/UL/CellBridge.v ac265d6399b.

   STAND-IN VALUES: seg_A3 reads no stand-in value (no AF0m row, no rt_of_core, none of ts_gp, pc_wrap_memcmp /
   pc_wrap_bcmp, pc_stack_malloc, ts_zsh, the 0x9fe18 / 0xa2878 rows); ctl_rt_C_of_AR reads CtrlTSyms B, a Section
   hypothesis.

   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at are fully qualified (through CK11 / AK11) or Reusable.YG0d-qualified
   everywhere.  Check:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/A/ACtlG/A3.v   -- hits only inside comments.

   BUILD STATE (honest): type-check on a working branch shell merged on this branch (cb build); the build of
   record is cbrec's (log and .prov named in the commit).  Print Assumptions glue_seg_A3: lib/A/ACtlG/L3W01Audit.v.
   No Axiom, no Parameter, no Admitted, no admit. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Cells.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.CellBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00 Reusable.YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.ACtlK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.ProgBridge A.ProgWorld A.ProgWorld_Fs.
(* route (C): the cut's runtime conjunct, its producer from AR, the symbol record it takes *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AF0m A.ShadowRwOn A.ACtlRtC A.ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.asan_set_shadow_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_set_shadowF A.Prog.memset.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.A3 A.Prog.Seg.A3F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem.
Import ListNotations.
Local Open Scope Z_scope.

(* The twin-safe module names (fully qualified). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module AK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Module LMState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRegs := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module US := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Step.
Module UCl := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Cells.
Module CBr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.CellBridge.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module KM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG.KitMem.
Module SSH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_set_shadow_cF.

(* The core's segment list, as ACtlCut.v:76 and ACtl.v:165 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Stage-local facts (no Section argument). *)

(* A lib/Lib stk window carves to one lib/A/Tk/UL junk cell, the cell form a3_evt_F's write-region premises take
   (lib/Lib's stk_split / stk_carve, then CellBridge.rw_cells_lib_ul). *)
Lemma a3g_junk : forall (m : word -> option byte) lo hi a (n : nat),
  LF.stk A.Img0.rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists bs, US.rw_cells A.Img0.rsegs m a [UCl.CB n bs].
Proof.
  intros m lo hi a n S H1 H2.
  destruct (LF.stk_split A.Img0.rsegs m lo (a + Z.of_nat n) hi S ltac:(lia)) as [S1 _].
  destruct (LF.stk_carve A.Img0.rsegs m lo (a + Z.of_nat n) n S1 ltac:(lia)) as [_ (bs & R)].
  replace (a + Z.of_nat n - Z.of_nat n) with a in R by lia.
  exists bs. exact (CBr.rw_cells_lib_ul A.Img0.rsegs m a _ R).
Qed.

(* The first 512 shadow bytes of a 4096-byte block in one application band are shadow bytes. *)
Lemma a3g_shadow_in : forall fr y, 4096 <= fr ->
  (fr + 4096 <= Reusable.YG0f.kLowShadowBeg \/ (Reusable.YG0f.kHighMemBeg <= fr /\ fr + 4096 <= 0x7fffff800000)) ->
  ART.shadow_addr fr <= y < ART.shadow_addr fr + 512 -> ART.in_shadow y.
Proof.
  intros fr y H0 Hb Hy.
  unfold ART.shadow_addr, ART.ASAN_K, ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG,
    ART.HIGHMEM_BEG, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in *.
  Z.div_mod_to_equations. lia.
Qed.

Section GlueA3.

(* ACtl.v's Section shape (ACtl.v:172-176), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block and cut names (ACtl.v section 1), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A80f88 := (ACtlCutP.C_A80f88 B).
Local Notation C_A810e4 := (ACtlCutP.C_A810e4 B).

(* ACtl.v's Section hypotheses this stage reads, same names and texts: the read-only span is image bytes
   (RELRO_IMG, for the exit's arodata_okS), the core's AR laws (LAWS) and symbol record (TFIB_SYMS, for
   ctl_rt_C_of_AR). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* The owned class-6 frame lies above the image: a Theorem Labs lane's proved ProgWorld_Fs.ctl_frame_above_img at class 6. *)
Lemma a3g_frame6_above_img : forall ly S (W : Reusable.YA0n.world segs) mem md pos,
  Reusable.YG0n.AR segs B ly S W mem md -> In (6, pos) (Reusable.YG01.frames S) ->
  A.Prog.ImgBounds.IMG_HI <= Reusable.YG0f.frame_addr ly 6 pos.
Proof. intros ly S W mem md pos HAR Hin. exact (A.ProgWorld_Fs.ctl_frame_above_img B ly S W mem md 6 pos HAR Hin). Qed.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_A3 : forall POST, CF POST C_A810e4 -> CF POST C_A80f88.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* ===== G1: the entry cut C_A80f88 (ACtlCutP.v:1105-1117) ===== *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A80f88] in Hbody.
  destruct Hbody as (HP & HPREF & A0 & R22 & Hfr32 & R21 & Hfr64 & HA0 & R23 & R24 & Hinb & Hina & Htr).
  clear A0 HA0.
  destruct HPREF as (A & sp & P2 & Psp16 & Pspz & P4 & P8 & P9 & P3 & P26 & PAm & PAS & PA432 & PspA & PA416 &
    PS4096 & PSAPP & PSAVED & PNMAX).
  (* ===== G2: the owned class-6 frame, its band, its place above the image ===== *)
  destruct (KM.kitmem_own6 B cx [] ly3 S3 W3 mem3 md3 k fr LAWS HJ HF HL)
    as (Hin6 & E3 & Hfr4096 & _ & Hceil & Hceil2).
  pose proof HJ as (HAR & _).
  destruct (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (_ & Happ & Hpres & _).
  rewrite E3 in Happ, Hpres.
  pose proof (a3g_frame6_above_img ly3 S3 W3 mem3 md3 (ACtlCut.c_fpos cx) HAR Hin6) as Himg.
  destruct (KM.kitmem_input_apart B MT XM_LIB RLO RHI cx [] ly3 S3 W3 mem3 md3 k LAWS HB HJ HF HP Himg)
    as (Hlen & Hp0 & Hpceil & Hpfr & Hpband).
  rewrite E3 in Himg, Hpfr.
  assert (FB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  assert (FB8 : Reusable.YG00.fs_frame_bytes 6 / 8 = 512) by reflexivity.
  rewrite FB6 in Hceil, Happ, Hpres, Hpfr.
  destruct (@Reusable.YG0f.ASAN_CEIL_range rc) as [HCE _].
  unfold Reusable.YG0f.ASAN_CEIL in HCE.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.ASAN_CEIL in Happ.
  unfold A.Prog.ImgBounds.IMG_HI in Himg.
  unfold A.ACfn.LLVMF_STK in Hceil2.
  unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hpband.
  assert (ESfr : ACtlCutP.Sfr fr = fr / 8 + 0x7fff8000) by reflexivity.
  assert (Hq8 : fr = 8 * (fr / 8)) by (clear - Hfr32; Z.div_mod_to_equations; lia).
  assert (Hband : fr + 4096 <= 0x7fff7000 \/ (0x10007fff8000 <= fr /\ fr + 4096 <= 0x7fffff800000))
    by (unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Happ; lia).
  assert (HSHI : forall y, ACtlCutP.Sfr fr <= y < ACtlCutP.Sfr fr + 512 -> ART.in_shadow y).
  { intros y Hy. apply (a3g_shadow_in fr y); [lia | | exact Hy].
    unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg. lia. }
  (* route (C): ctl_rt_C's four facts; the frame shadow [Sfr fr, Sfr fr + 512) is cut_shadow's (F) disjunct at the
     owned class-6 frame (frames S3 holds (6, c_fpos cx), frame_addr ly3 6 (c_fpos cx) = fr) *)
  destruct Hrt as (Hcells & Hcut & _ & Hroag).
  assert (HFsh : forall y, ACtlCutP.Sfr fr <= y < ACtlCutP.Sfr fr + 512 -> A.ACtlRtC.cut_shadow B ly3 S3 y).
  { intros y Hy. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite E3, FB8. rewrite ESfr in Hy. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. lia. }
  (* the four write regions as lib/Lib stk windows, then as UL junk cells *)
  assert (STK1 : LF.stk A.Img0.rsegs mem3 (A + 304) (A + 312)).
  { eapply KM.kitmem_stk_of_journal; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  assert (STK2 : LF.stk A.Img0.rsegs mem3 fr (fr + 24)).
  { apply (KM.kitmem_stk_of_present (Reusable.YA0n.w_H W3)); [lia | lia |].
    intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  assert (STK3 : LF.stk A.Img0.rsegs mem3 (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 255)).
  { split; [lia|]. split; [lia|]. intros a Ha. exact (Hcut a (HFsh a ltac:(lia)) (HSHI a ltac:(lia))). }
  destruct (a3g_junk mem3 (A + 304) (A + 312) (A + 304) 8 STK1 ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia))
    as (j1 & C1).
  destruct (a3g_junk mem3 fr (fr + 24) fr 24 STK2 ltac:(lia) ltac:(change (Z.of_nat 24) with 24; lia))
    as (j2 & C2).
  destruct (a3g_junk mem3 (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 255) (ACtlCutP.Sfr fr) 68 STK3 ltac:(lia)
              ltac:(change (Z.of_nat 68) with 68; lia)) as (j3 & C3).
  destruct (a3g_junk mem3 (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 255) (ACtlCutP.Sfr fr + 68) 187 STK3 ltac:(lia)
              ltac:(change (Z.of_nat 187) with 187; lia)) as (j4 & C4).
  assert (HIS : forall i, 0 <= i < 187 -> ART.in_shadow (ACtlCutP.Sfr fr + 68 + i))
    by (intros i Hi; apply HSHI; lia).
  (* the footprint ranges at RNG_W (w_H W3) *)
  assert (RW1 : LX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (A + 304) 8).
  { eapply KM.kitmem_rng_win; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia]. }
  assert (RW2 : LX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) fr 24).
  { apply (KM.kitmem_rng_frame B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) fr 24 HAR Hin6);
      rewrite E3; rewrite ?FB6; lia. }
  assert (RW3 : LX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (ACtlCutP.Sfr fr) 68).
  { apply (KM.kitmem_rng_frame_sh B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) _ 68 HAR Hin6);
      rewrite E3; rewrite ?FB8; unfold ACtlCutP.Sfr; lia. }
  assert (RW4 : LX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (ACtlCutP.Sfr fr + 68) 187).
  { apply (KM.kitmem_rng_frame_sh B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) _ 187 HAR Hin6);
      rewrite E3; rewrite ?FB8; unfold ACtlCutP.Sfr; lia. }
  assert (RW5 := A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3)).
  assert (RW6 : forall w : word,
            LX.rng (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) (bv_unsigned w - SSH.ASAN_SET_SHADOW_K)
              SSH.ASAN_SET_SHADOW_K).
  { intros w. apply A.ProgBridge.rng_of_visible. unfold A.ProgBridge.range_visible, SSH.ASAN_SET_SHADOW_K.
    pose proof (bv_unsigned_in_range 64 w) as Hw. unfold bv_modulus in Hw.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Hw.
    split; [lia|]. split; [lia|]. intros a Ha. lia. }
  (* ===== G3: the cut's configuration in the run's state form, the walk moved to the run's map mkR_of regs3 ===== *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A80f88) with 0x80f88.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x80f88) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs.xregs_eqv_sym _ _ (LRegs.mkR_of_eqv regs3))].
  (* ===== G4: the run (ctrl's YK11 instance built from the core's fp state) and the lift ===== *)
  pose proof (@A.Prog.Seg.A3F.a3_evt_F (AK11.mkFP CK11.fp_regs CK11.fp_csr)
    (A.Prog.asan_set_shadowF.asan_set_shadow_f8_holds_F A.Prog.memset.memset_holds)
    (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) regs3 mem3 A fr (ACtlCutP.Sfr fr) j1 j2 j3 j4 P9 R22 P26
    C1 C2 C3 C4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)
    HIS Hcells Hroag (A.ProgBridge.rng_bytes_RNG_W _) RW1 RW2 RW3 RW4 RW5 (RW6 _)) as HRUN.
  unfold A.Prog.Seg.A3.KA in HRUN.
  change (@AK11.fp_regs (AK11.mkFP CK11.fp_regs CK11.fp_csr)) with (@CK11.fp_regs fx) in HRUN.
  change (@AK11.fp_csr (AK11.mkFP CK11.fp_regs CK11.fp_csr)) with (@CK11.fp_csr fx) in HRUN.
  change (@AK11.getr) with (@CK11.getr) in HRUN.
  change (@AK11.seg_rom) with (@CK11.seg_rom) in HRUN.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HRUN.
  apply (KM.kitmem_lift A.ACtlG.Kit.kit_wx W3 _ md3 _ _ (POST cx) HRUN (A.ProgBridge.fp_avoids_RNG_W _)).
  intros ms' md' Hrun HQ Hsbm.
  destruct HQ as (R & pc' & mem' & Ems & Hpc & MU & WM & HRO' & Hsp & Hh0 & Hh8 & Hh16 & Hsh68 & Hsh187 &
    K2 & K3 & K4 & K8 & K9 & K21 & K22 & K23 & K24 & K26 & K18 & K19 & K20 & K25).
  subst ms' pc'.
  (* ===== G5: the world across the run, then the exit cut C_A810e4 (ACtlCutP.v:1121-1133) ===== *)
  (* the run grows memory (ProgWorld.pws_fsteps_mem) *)
  pose proof (A.ProgWorld.pws_fsteps_mem segs (Reusable.YA0n.w_H W3) _ _ _ Hrun (A.ProgBridge.fp_avoids_RNG_W _))
    as [Hg _].
  change (CK1b.mem_grows mem3 mem') in Hg.
  (* a byte of the write set is in one of its three blocks *)
  assert (WRin : forall x, ~ LF.outside [(A + 304, A + 312); (fr, fr + 24); (ACtlCutP.Sfr fr, ACtlCutP.Sfr fr + 68);
                                       (ACtlCutP.Sfr fr + 68, ACtlCutP.Sfr fr + 255)] x ->
            (A + 304 <= x < A + 312) \/ (fr <= x < fr + 24) \/ (ACtlCutP.Sfr fr <= x < ACtlCutP.Sfr fr + 255)).
  { intros x Hx. destruct (KM.kitmem_not_outside _ x Hx) as (lo & hi & Hin & Hr).
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; subst lo hi; lia. }
  (* the journal (ProgWorld.ajournal_of_fsteps): the spill byte is the LLVMF window's, the header and shadow bytes
     the owned class-6 frame's *)
  assert (HJ' : Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 mem' md' k).
  { refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ _ Hrun (A.ProgBridge.fp_avoids_RNG_W _) MU Hsbm _); [exact HJ|].
    intros a _ Hno. destruct (WRin a Hno) as [Hx|[Hx|Hx]].
    - apply KM.kitmem_awr_win. unfold A.ACfn.LLVMF_STK. lia.
    - apply (KM.kitmem_awr_frame _ _ _ _ _ _ _ 6 (ACtlCut.c_fpos cx) fr);
        [symmetry; exact E3 | left; reflexivity | left; rewrite FB6; lia].
    - apply (KM.kitmem_awr_frame _ _ _ _ _ _ _ 6 (ACtlCut.c_fpos cx) fr);
        [symmetry; exact E3 | left; reflexivity | right; rewrite FB8; unfold ACtlCutP.Sfr in Hx; lia]. }
  (* ctl_rt_C at the exit (same ly3 S3, memory mem'): ctl_rt_C_of_AR at the exit journal's AR, with the entry's
     arodata_okS carried along the journal (KitMem.kitmem_arodataS_journal) *)
  assert (Hrt' : A.ACtlRtC.ctl_rt_C B ly3 S3 mem').
  { pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _) & _).
    pose proof HJ' as (HAR' & _).
    exact (A.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem' md' HAR'
             (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _
                (KM.kitmem_arodataS_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ' HROS)
                (Z.le_refl _) (Z.le_refl _))). }
  (* ProgBridge.cfg_at_MS read backwards (it is eq_refl), at the exit cut's pc *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A810e4) R mem' md') (POST cx)).
  apply (HX cx idx fr k ly3 S3 W3 R mem' md' HB HJ' HF HL Hk).
  - (* the exit body, C_A810e4 (ACtlCutP.v:1121-1133), at sel = fr *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A810e4].
    split; [exact HP|].
    split.
    { (* FRAHC (header 0x41b58ab3), built BY SHAPE from PREFC's A and sp and the run's post *)
      assert (Q2 : CK11.getr R 2 = Z_to_bv 64 sp) by (rewrite K2; exact P2).
      assert (Qspz : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ in *; rewrite K2; exact Pspz).
      assert (Q4 : CK11.getr R 4 = Z_to_bv 64 (Reusable.YG0f.as_tp B)) by (rewrite K4; exact P4).
      assert (Q8 : ACtlCut.rgv R 8 (ACtlCut.c_sp cx)) by (unfold ACtlCut.rgv in *; rewrite K8; exact P8).
      assert (Q3 : CK11.getr R 3 = CK11.getr (ACtlCut.c_regs cx) 3) by (rewrite K3; exact P3).
      assert (Q392 : exists sh, LM.bytes_at segs mem' (ACtlCutP.Sfr fr) sh /\
                                length sh = Z.to_nat ACtlCutP.FRAME_SHADOW).
      { (* the owned frame's shadow is in cut_shadow's (F) disjunct (HFsh); ctl_rt_C at mem' makes it present *)
        destruct Hrt' as (_ & Hcut' & _ & _).
        assert (ST : LF.stk A.Img0.rsegs mem' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 392)).
        { split; [lia|]. split; [lia|]. intros a Ha. exact (Hcut' a (HFsh a ltac:(lia)) (HSHI a ltac:(lia))). }
        destruct (LF.stk_bytes A.Img0.rsegs mem' _ _ ST ltac:(lia)) as (bs & Hl & Hb).
        exists bs. split; [exact Hb|]. rewrite Hl.
        replace (ACtlCutP.Sfr fr + 392 - ACtlCutP.Sfr fr) with 392 by ring. reflexivity. }
      assert (QSV : LM.bytes_at segs mem' (ACtlCut.c_sp cx - 104) (ACtlCutP.saved_bytes cx)).
      { apply (KM.kitmem_bytes_munch _ mem3 mem' _ _ PSAVED MU). rewrite KM.kitmem_saved_len.
        intros x Hx. cbn [LF.outside]. repeat split; intros [? ?]; lia. }
      unfold ACtlCutP.FRAHC. exists A, sp.
      (* each conjunct by its shape, not its position: a register / arithmetic fact, a word the run wrote, or a
         word of mem3 the run does not write (kitmem_q64_munch; none today, FRAHC's announced trailer word would
         take this arm once a cut before it carries the word) *)
      repeat (match goal with |- _ /\ _ => split end);
        first [ assumption | exact K9 | exact K19 | exact K26 | exact Hsp | exact Hh0 | exact Hh16
              | unfold ACtlCutP.FRAME_BYTES; lia
              | lazymatch goal with
                | |- ACtlCutP.q64 mem' ?a ?v =>
                    match goal with Hq : ACtlCutP.q64 mem3 a v |- _ =>
                      apply (KM.kitmem_q64_munch _ mem3 mem' a v Hq MU);
                      intros ? ?; cbn [LF.outside]; repeat split; intros [? ?]; lia end
                end ]. }
    split; [exact PNMAX|].
    split; [exact K18|].
    split; [exact K20|].
    split; [unfold ACtlCut.rgv; rewrite K21; exact R21|].
    split; [exact K22|].
    split; [unfold ACtlCut.rgv; rewrite K23; exact R23|].
    split; [unfold ACtlCut.rgv; rewrite K24; exact R24|].
    split; [exact K25|].
    split.
    + (* the input bytes: the input block is apart from the write set (KitMem.kitmem_input_apart) *)
      apply (KM.kitmem_bytes_munch _ mem3 mem' _ _ Hinb MU). rewrite Hlen.
      intros x Hx. cbn [LF.outside]. repeat split; intros [? ?]; lia.
    + (* their addressability: the input's shadow is apart from the write set *)
      intros Hn. pose proof (Hina Hn) as HA.
      apply (KM.kitmem_addressable_mrd mem3 mem' _ _ HA). intros i Hi.
      destruct HA as (_ & _ & _ & HAb). destruct (HAb i Hi) as (Happx & _).
      unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END in Happx.
      apply (KM.kitmem_mrd_munch _ mem3 mem' _ MU).
      * unfold ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia.
      * cbn [LF.outside]. unfold ART.shadow_addr, ART.ASAN_K. rewrite ESfr.
        repeat split; intros [? ?]; Z.div_mod_to_equations; lia.
  - (* ctl_rt at mem' *)
    exact Hrt'.
Qed.

End GlueA3.
