(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2748 of its 2845 lines of code are new or changed and 931 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e2.v, with its module paths and module names changed; 4090 of its 4391 lines of code are new or changed and 2544 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4c.v, with its module names and addresses changed; 411 of its 441 lines of code are new or changed and 4361 lines of the source are left out. *)
(* lib/A/ACtlG/F24.v -- GLUE for stage seg_F24 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:820).  Written by a Theorem Labs lane; single writer of this file.
   rule 24: no function proved (stage glue of a walk).

   WHAT IT PROVES
     glue_seg_F24 : forall POST (j : nat),
       CF POST (ix_cut C_A825d4_at [Z.of_nat j]) -> CF POST (ix_cut C_A825c8_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F24.  Segment F24 is 0x825c8 -> 0x825d4 (Seg/F24F.v:10-11): two moves and
   jal reac_ports_parse@0x8765c, landing at 0x825d4.

   ROUTE (a) -- NO LIFT, NO SPLIT (a Theorem Labs lane, 2026-10-29 "WHICH ROUTE APPLIES IS DECIDED BY YOUR SEGMENT'S
   _F TEXT").  The run lifted is Seg/F24Fon.v's f24_evt_F_on (this lane's route (C) twin of Seg/F24F.v's
   f24_evt_F, with no shadow premise); it takes reac_ports_parse_c.reac_ports_parse_contract_F_on AS A PREMISE and
   its run SPANS the call, so this file supplies that premise with the PROVED contract
   (A/Prog/reac_ports_parseF.v reac_ports_parse_F_holds_on) and lifts the WHOLE run once with
   Reusable.YA0nR.SRr_fevt_hid at RNG := A.ProgBridge.RNG_W (w_H W3).  It cites NO <f>_SRr_at.

   ROUTE (C) (a Theorem Labs lane 1502cba0417 / 1899bed1aee): the cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3.  The
   run needs no shadow byte from it (the callee's _on contract dropped its shadow premise).  The exit cut has the
   same state (ly3, S3), so the entry's two regions (cut_shadow B ly3 S3, img_shadow) are carried to it, each by
   A.ShadowRwOnT.shadow_rw_on_kept: the write set (the callee's stack window and the frame's ports words) is app
   memory, so no shadow byte moves (AsanRTFacts.munch_meta).

   THE PROOF, step by step (F26.v's shape; the b7g_* transport helpers are A.ACtlG.F26's, cited, not copied)
   G1  unfold the entry cut: ix_cut's index equation, then C_A825c8_at (ACtlCutP.v:2608-2618) = FRAC + b7_body
       with the tail (s4 = fr + 128, the three ports words at -7, addressable [fr + 128, fr + 140)).
   G2  the run's premises from the body and from VISIBLE state.  Geometry as in F26 (the callee's window
       [sp - 16, sp) lies above every byte the body reads below sp), plus the ONE new fact of this stage: the
       run also writes the ports words [fr + 128, fr + 140) of the class-6 frame (6, c_fpos cx), and
       fr = frame_addr ly3 6 (c_fpos cx) (ctl_from's frame law + layout_le's ly_F equation).  So:
         - the frame is app memory (A.ACtlG.F26.b7g_frame_app) and lies above the image (a Theorem Labs lane's
           A.ProgWorld.ctl_frame_above_img_stmt, proved premise-free by A.ProgWorld_Fs.ctl_frame_above_img), which
           keeps the runtime cells, the shadow and the read-only image off it;
         - the turn's block and the input block are separate from the frame (YCbq.sep_block_frame);
         - every frame-data conjunct of the b7 bundles lies in [fr + 2624, fr + FRAME_BYTES), above fr + 140.
       The frame bytes are visible by ProgWorldVisFrame.frame_vis (bytes and shadow word cover).
   G3  register maps: ProgBridge.cfg_at_MS and Reusable.YA0nR.SRr_xregs_eqv, as F26.
   G4  lift: ProgBridge.fevt_of_evtF + ProgBridge.tfibsegs_rsegs, then Reusable.YA0nR.SRr_fevt_hid, as F26.
   G5  the continuation at the run's own end map.  Write set W = [(sp - 16, sp); (fr + 128, fr + 140)].  The
       journal crosses it with Reusable.YCbq.ajournal_exec (awr_byte's stack case and its in_frames case at the
       owned frame (6, c_fpos cx)); the frame window `stk` crosses it with Lib.Frame.stk_transport (a frame
       byte written by the run stays present: f24_present); the exit tail: x10 = t_rp literally, PORTS from the
       run's post (decl = true) or from the entry's -7 words across the post's stack-only munch (decl = false),
       addressable by b7g_addr_app.

   SECTION HYPOTHESES (exact text in the file; why)
   - LAWS : Reusable.YG0d.AR_laws segs B -- the core's AR law record (YCbq.v:207), as ACtl.v:183 has it.
   No other Section hypothesis.  The kit's image facts are CITED from lib/A/ACtlG/Kit.v (glue base
   46eb24cd4b3, Kit.v blob 7e164a09a73, which builds): A.ACtlG.Kit.kit_wx (SRr_fevt_hid's wx_segs_nowrap) and
   A.ACtlG.Kit.kit_segs_low (ajournal_exec's image placement).  On the first base (eb89fed7fac, commit
   fe89f3b2df5) they were named Section hypotheses with the kit's exact text, because Kit.v did not compile
   there.  kit_frac_move is NOT used: this stage rebuilds FRAC from its own destructuring (the run keeps
   2 3 4 8 9 19 26).  kit_RNG0 is NOT used: the run reads and writes memory, so the footprint is RNG_W.

   The frame-above-image bound is CITED by name: A.ProgWorld.ctl_frame_above_img_stmt (proof
   A.ProgWorld_Fs.ctl_frame_above_img).  The TEMPORARY local copy A.ACtlG.F26.b7g_frame_GT it replaces is deleted.

   CLOSURE: every Require below is qualified; no statement of this file names a frame-route identifier
   (A.Contract and A/Prog/Seg/F24.v are named only inside proofs closed by Qed).  A module that has a second copy
   under the lib root (lib/{A,B,U}/Reusable, lib/{A,B}/Bz/Lib, lib/AZ/Lib) is Required by its FULL path, not by a
   `From lib Require` suffix: core Reusable.YK11 / YK1b / YM05 / YO09 / YI16 (whose lib/A/Reusable copies this
   closure also loads, through the _F file) and Lib.Mem / Frame / PropExec / MState.  A `Locate Module` run on
   this file (h14sf24b, 2026-10-29 05:47Z) found every other qualified name it uses resolving to ONE module.

   SHADOWED NAMES: getr / mkst / seg_rom are lib.Reusable.YK11-qualified and cfg_at Reusable.YG0d-qualified
   (through the local Reusable alias block) everywhere.

   BUILD STATE: type-checks on a working branch 1899bed1aee (a working branch); its build of
   record (cbrec) is reported by the lane, not here.  No Axiom, no Parameter, no unproved step. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YG0n Reusable.YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.ACfn A.AE2k A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorldVisWin A.ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.SlotModel A.Prog.SlotInv A.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.reac_ports_parse_c A.Prog.reac_ports_parseF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.B7Cuts A.Prog.Seg.F24 A.Prog.Seg.F24Fon.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Contract A.Reusable.YP09 A.MemNorm.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.ExecF Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.F26.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.ProgWorld_Fs.

(* The CORE's lib/Reusable modules that have NO second copy, bound once under the short name this file uses.  The
   three that do (YK11, YM05, YO09: ctrl's ASan-side copies lib/A/Reusable/<X>.v are in the _F closure, with
   DIFFERENT constants) are written lib.Reusable.<X>.<name> everywhere, which names the core copy only. *)
Module Reusable.
  Module YA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
  Module YA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
  Module YC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
  Module YCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
  Module YG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
  Module YG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
  Module YG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
  Module YG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
  Module YG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
  Module YG0v := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0v.
  Module YI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
  Module YK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
  Module YK06 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK06.
  Module YK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
End Reusable.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   0. The one helper this stage adds to F26.v's: a byte at or above the image that the old memory reads stays
   present (as a plain map entry) in a new memory that keeps writability.  stk_transport's second case. *)
Lemma f24_present : forall (m m' : word -> option byte) (a : Z),
  A.Prog.ImgBounds.IMG_HI <= a -> 0 <= a < 2 ^ 64 -> Lib.Frame.wmono A.Img0.rsegs m m' ->
  (exists b, Lib.Mem.mrd A.Img0.rsegs m (Lib.Mem.wa a) = Some b) ->
  exists b, m' (Lib.Mem.wa a) = Some b.
Proof.
  intros m m' a Hgt Ha WM (b & Hb).
  assert (Hgt' : A.Contract.GT <= a) by (unfold A.Contract.GT; unfold A.Prog.ImgBounds.IMG_HI in Hgt; lia).
  assert (Hu : bv_unsigned (Lib.Mem.wa a) = a) by (apply Lib.Mem.wa_unsigned; exact Ha).
  assert (Hm : m (Lib.Mem.wa a) <> None).
  { intros E. unfold Lib.Mem.mrd in Hb. rewrite E in Hb.
    rewrite (A.MemNorm.seg_rom_unmapped A.Img0.rsegs (Lib.Mem.wa a)) in Hb; [discriminate Hb |].
    rewrite Hu. exact (A.Prog.Seg.F24.b7_find_none a Hgt'). }
  pose proof (A.ACtlG.F26.b7g_grow m m' (Lib.Mem.wa a) ltac:(rewrite Hu; exact Hgt) WM Hm) as Hm'.
  destruct (m' (Lib.Mem.wa a)) as [b' |]; [exists b'; reflexivity | exfalso; exact (Hm' eq_refl)].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   1. The stage. *)

Section GlueF24.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:213, :217-218, :296-297), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A825c8_at := (ACtlCutP.C_A825c8_at B).
Local Notation C_A825d4_at := (ACtlCutP.C_A825d4_at B).

(* The core's AR law record (YCbq.v:207, Section a0's hypothesis), as ACtl.v:183 states it. *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* The kit's image facts are cited by name below: A.ACtlG.Kit.kit_wx and A.ACtlG.Kit.kit_segs_low. *)

Lemma glue_seg_F24 : forall POST (j : nat), CF POST (ix_cut C_A825d4_at [Z.of_nat j]) -> CF POST (ix_cut C_A825c8_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat j] (ACtlCut.v:232-234; C_A825c8_at, ACtlCutP.v:2608-2618). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A825c8_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & HBODY).
  destruct HBODY as (phi & HPerm & Hn26 & Hj255 & HHB & HFLSI & HB7K & HP).
  cbv beta in HP.
  destruct HP as (R20 & U0 & U4 & U8 & HADq).
  destruct Hrt as (HAC & Hcut & Himgsh & HRO).
  (* G2: the geometry. *)
  pose proof HJ as (HAR & Hly & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstkok & _ & _).
  destruct Hstkok as (_ & _ & Hceil & Hstklo & _ & _ & _ & _ & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)).
  { rewrite HF. cbv beta iota delta [ACtlCut.ix_cut ACtlCut.cut_own ACtlCutP.C_A825c8_at ACtlCut.own6].
    left. reflexivity. }
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  assert (Efr : fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)).
  { apply HL. cbv beta iota delta [ACtlCut.ix_cut ACtlCut.cut_own ACtlCutP.C_A825c8_at ACtlCut.own6].
    left. reflexivity. }
  (* the frame base at the CURRENT layout: layout_le keeps ly_F *)
  assert (Efr3 : fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite Efr. unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  assert (Hfr4096 : 4096 <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling).
  { change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hfceil.
    rewrite Efr. unfold Reusable.YG0f.frame_addr in *. rewrite <- EF. split; [exact Hf4096 | exact Hfceil]. }
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hcmin Hcmax] _].
  (* the frame lies above the loaded image (a Theorem Labs lane's statement, cited by name) and is app memory *)
  assert (HfrGT : A.Prog.ImgBounds.IMG_HI <= fr).
  { pose proof ((A.ProgWorld_Fs.ctl_frame_above_img B : A.ProgWorld.ctl_frame_above_img_stmt B)
                  ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6) as HFA.
    rewrite <- Efr3 in HFA. unfold A.Prog.ImgBounds.IMG_HI. lia. }
  assert (Happ : forall x, fr <= x < fr + 4096 -> A.AsanRT.app_mem x).
  { intros x Hx. apply (A.ACtlG.F26.b7g_frame_app B ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) x LAWS HAR Hin6).
    rewrite <- Efr3. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  (* FRAC's own names: HFR keeps the record WHOLE for the exit's walk (G5); the copy below names only the
     conjuncts this proof READS and ends in `& _`, so a conjunct appended to FRAC changes neither. *)
  destruct HFRAC as (Aa & sp & HFR).
  pose proof HFR as (R2 & Hsp16 & Hspz & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAle &
    HspA & HfrA & HA416 & Hsplo & HSapp & _).
  unfold A.ACfn.LLVMF_STK in Hstklo.
  unfold A.AsanRT.APPMEM_END in HSapp.
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (Hwin : fr + 3136 < sp - 16 /\ A.Prog.ImgBounds.IMG_HI <= sp - 16 /\ sp <= ACtlCut.c_sp cx).
  { unfold A.Prog.ImgBounds.IMG_HI. repeat split; lia. }
  destruct Hwin as (Hfrwin & Himg & Hspsp).
  assert (Hsp0 : 0 <= sp - 16 /\ sp < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
  (* the block of this turn is live, and apart from the frame *)
  assert (Hinblk : In (phi, ACtlCutP.flen cx j) (Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. left. reflexivity. }
  pose proof HB7K as (_ & _ & _ & Hphi0 & Hphi2 & Hflen & _).
  destruct (Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hinblk)
    as (_ & Hphi4096 & Hphiceil & _).
  assert (Hreq : Reusable.YG00.req_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j).
  { unfold Reusable.YG00.req_size. destruct (Z.eqb_spec (ACtlCutP.flen cx j) 0); lia. }
  rewrite Hreq in Hphiceil.
  assert (Hsepb : phi + ACtlCutP.flen cx j <= fr \/ fr + 4096 <= phi).
  { pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j)
                  6 (ACtlCut.c_fpos cx) HAR Hinblk Hin6) as Hz.
    rewrite Hreq, <- Efr3 in Hz. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hz.
    unfold Reusable.YG0f.zdisjoint in Hz. cbn [fst snd] in Hz. exact Hz. }
  (* the input block *)
  pose proof HB as (HBpre & _).
  pose proof HBpre as (_ & _ & _ & _ & Hinp & Hinlen & _).
  assert (Hinbound : 0 <= ACtlCut.c_p cx /\
                     ACtlCut.c_p cx + ACtlCut.c_n cx <= lib.Reusable.YM05.alloc_ceiling /\
                     (ACtlCut.c_p cx + ACtlCut.c_n cx <= fr + 128 \/ fr + 140 <= ACtlCut.c_p cx)).
  { destruct Hinp as [(Hn0 & Hp0) | (Hn0 & Hinb)].
    - rewrite Hp0, Hn0. unfold A.ACfn.A_EMPTY. unfold A.Prog.ImgBounds.IMG_HI in HfrGT. lia.
    - destruct (Reusable.YG0d.al_blocks _ _ LAWS (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx)
                  (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.c_p cx) (ACtlCut.c_n cx)
                  (proj1 (proj1 HBpre)) Hinb) as (_ & Hp4096 & Hpceil & _).
      assert (Hinb3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (Reusable.YG0d.ablocks B ly3 S3)).
      { apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hinb. }
      pose proof (Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 (ACtlCut.c_p cx) (ACtlCut.c_n cx)
                    6 (ACtlCut.c_fpos cx) HAR Hinb3 Hin6) as Hz.
      rewrite <- Efr3 in Hz. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Hz.
      unfold Reusable.YG0f.zdisjoint in Hz. cbn [fst snd] in Hz.
      unfold Reusable.YG00.req_size in Hpceil, Hz.
      destruct (Z.eqb_spec (ACtlCut.c_n cx) 0); lia. }
  destruct Hinbound as (Hinb0 & Hinceil & Hinsep).
  assert (Hinlen' : Z.of_nat (length (ACtlCut.c_in cx)) = ACtlCut.c_n cx) by lia.
  (* the frame window of the body, on the old memory *)
  pose proof (proj1 (proj2 (proj2 (proj1 HFLSI)))) as HSTK0.
  pose proof HSTK0 as (Hs0 & Hs1 & Hs).
  unfold ACtlCutP.FRAME_BYTES in Hs.
  (* G2b: the run's premises *)
  assert (Hstk : Lib.Frame.stk A.Img0.rsegs mem3 (sp - 16) sp).
  { split; [lia |]. split; [change (2 ^ 64) with 18446744073709551616; lia |].
    intros a Ha. destruct (Hpres a ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (_ & b & Hbv).
    assert (Hmrd : Lib.Mem.mrd A.Img0.rsegs mem3 (Lib.Mem.wa a) = Some b)
      by (unfold Lib.Mem.mrd, Lib.Mem.wa; rewrite Hbv; reflexivity).
    split; [| exists b; exact Hmrd].
    assert (Hga : A.Contract.GT <= a) by (unfold A.Contract.GT; unfold A.Prog.ImgBounds.IMG_HI in Himg; lia).
    pose proof (A.Prog.Seg.F24.b7_hi_wr mem3 a Hga ltac:(change (2 ^ 64) with 18446744073709551616; lia)
                  (ex_intro _ b Hmrd)) as HWa.
    unfold A.Reusable.YP09.writable_at in HWa. exact HWa. }
  assert (Hwr : Lib.Mem.wr_at A.Img0.rsegs mem3 (fr + 128) 12).
  { split; [lia |]. split; [unfold ACtlCutP.FRAME_BYTES in Hs1; lia |].
    intros i Hi. exact (proj1 (Hs (fr + 128 + i) ltac:(lia))). }
  assert (HOUT : forall x, A.AsanRT.GOT_CELL_K <= x < A.AsanRT.GOT_CELL_K + 8 \/
                           A.AsanRT.CELL_K <= x < A.AsanRT.CELL_K + 8 \/ A.AsanRT.in_shadow x ->
                  Lib.Frame.outside [(sp - 16, sp); (fr + 128, fr + 140)] x).
  { intros x Hx. cbn [Lib.Frame.outside]. split; [| split; [| exact I]].
    - unfold A.AsanRT.GOT_CELL_K, A.AsanRT.CELL_K, A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END,
        A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG in Hx.
      unfold A.Prog.ImgBounds.IMG_HI in Himg. lia.
    - intros Hr. pose proof (Happ x ltac:(lia)) as Hax.
      unfold A.AsanRT.app_mem in Hax.
      unfold A.AsanRT.GOT_CELL_K, A.AsanRT.CELL_K, A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END,
        A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in Hx, Hax.
      unfold A.Prog.ImgBounds.IMG_HI in HfrGT. lia. }
  assert (HADp : A.AsanRT.addressable mem3 (phi + 18) 20).
  { destruct HHB as (_ & Hadphi). unfold A.ACtlK.a_size in Hadphi.
    apply (A.AsanRTFacts.addressable_sub mem3 phi (Z.max (ACtlCutP.flen cx j) 1) 18 20 Hadphi); lia. }
  pose proof HB7K as (_ & _ & R22 & _ & _ & _ & Hblk & _).
  (* visibility of the six footprint regions *)
  assert (V1 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (sp - 16) 16).
  { apply (A.ProgWorldVisWin.win_vis B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx)
             (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
             (ACtlCut.cut_own (ix_cut C_A825c8_at [Z.of_nat j]) cx) ly3 S3 W3 mem3 md3 k (sp - 16) 16 HJ);
      unfold A.ACfn.LLVMF_STK; lia. }
  assert (VRT : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.AsanRT.RT_LO
                  (A.AsanRT.RT_HI - A.AsanRT.RT_LO)) by exact (A.ProgBridge.rt_vis_W W3).
  assert (V2 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.AsanRT.GOT_CELL_K 8).
  { apply (A.ProgBridge.range_visible_sub _ A.AsanRT.RT_LO (A.AsanRT.RT_HI - A.AsanRT.RT_LO) _ _ VRT);
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.AsanRT.GOT_CELL_K; lia. }
  assert (V3 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) A.AsanRT.CELL_K 8).
  { apply (A.ProgBridge.range_visible_sub _ A.AsanRT.RT_LO (A.AsanRT.RT_HI - A.AsanRT.RT_LO) _ _ VRT);
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI, A.AsanRT.CELL_K; lia. }
  assert (V4 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3) (phi + 18) 20).
  { apply (A.ProgWorldVisHeap.heap_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) (phi + 18) 20
             HAR Hinblk); rewrite ?Hreq; lia. }
  assert (V5 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3)
                 (A.AsanRT.shadow_addr (phi + 18))
                 (A.AsanRT.shadow_addr (phi + 18 + 19) - A.AsanRT.shadow_addr (phi + 18) + 1)).
  { destruct (A.ProgWorldVisHeap.heap_sh_vis B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j)
                (phi + 18) 20 HAR Hinblk ltac:(lia) ltac:(rewrite Hreq; lia) ltac:(lia)) as [Hz | Vsh];
      [lia |].
    apply (A.ProgBridge.range_visible_sub _ (A.Prog.rng_asan.sh_al8_lo (phi + 18))
             (A.Prog.rng_asan.sh_al8_hi (phi + 18) 20 - A.Prog.rng_asan.sh_al8_lo (phi + 18)) _ _ Vsh);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr;
      Z.div_mod_to_equations; lia. }
  destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (fr + 128) 12
              HAR Hin6 ltac:(rewrite <- Efr3; lia)
              ltac:(rewrite <- Efr3; change (Reusable.YG00.fs_frame_bytes 6) with 4096; lia)) as (V6 & Vsh6).
  assert (V7 : A.ProgBridge.range_visible (Reusable.YA0n.w_H W3)
                 (A.AsanRT.shadow_addr (fr + 128))
                 (A.AsanRT.shadow_addr (fr + 128 + 11) - A.AsanRT.shadow_addr (fr + 128) + 1)).
  { rewrite <- Efr3 in Vsh6. change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Vsh6.
    assert (Hal1 : fr <= 64 * ((fr + 128) / 64)) by (clear -Hfr32; Z.div_mod_to_equations; lia).
    assert (Hal2 : 64 * ((fr + 128 + 12 - 1) / 64) + 64 <= fr + 4096) by (clear -Hfr32; Z.div_mod_to_equations; lia).
    destruct (Vsh6 ltac:(lia) Hal1 Hal2) as [Hz | Vsh]; [lia |].
    apply (A.ProgBridge.range_visible_sub _ (A.Prog.rng_asan.sh_al8_lo (fr + 128))
             (A.Prog.rng_asan.sh_al8_hi (fr + 128) 12 - A.Prog.rng_asan.sh_al8_lo (fr + 128)) _ _ Vsh);
      unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi, A.AsanRT.shadow_addr;
      clear -Hfr32; Z.div_mod_to_equations; lia. }
  clear Vsh6.
  (* G3: the cut's configuration in the run's state form, then the walk at the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A825c8_at [Z.of_nat j])) with 0x825c8.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 lib.Reusable.YK11.fp_regs
           (Z_to_bv 64 0x825c8) lib.Reusable.YK11.fp_csr None mem3 (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the run, and the lift at RNG_W. *)
  unfold Lib.Regs6ss.mkR_of.
  pose proof (A.Prog.Seg.F24Fon.f24_evt_F_on (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
                A.Prog.reac_ports_parseF.reac_ports_parse_F_holds_on
                (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3)
                (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
                (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
                (lib.Reusable.YK11.getr regs3 10) (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12)
                (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15)
                (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18)
                (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21)
                (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23) (lib.Reusable.YK11.getr regs3 24)
                (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
                (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30)
                (lib.Reusable.YK11.getr regs3 31)
                lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3
                sp phi fr (sp - 16)
                (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j)
                R2 R22 R20 Hphi0 Hphi2 ltac:(lia)
                ltac:(unfold A.Prog.SlotInv.FRAME_BYTES; change (2 ^ 64) with 18446744073709551616; lia)
                Hfr32 ltac:(lia) Hstk ltac:(lia)
                (A.Prog.Seg.F24.b7_pbs_length (ACtlCut.c_in cx) j)
                (A.Prog.Seg.F24.b7_pbs_bytes mem3 (phi + 18) (ACtlCut.c_in cx) j Hblk)
                Hwr ltac:(lia) ltac:(left; lia) ltac:(left; lia)
                HAC HADp HADq HOUT
                (A.ProgBridge.rng_of_visible _ _ _ V1)
                (A.ProgBridge.rng_of_visible _ _ _ V2)
                (A.ProgBridge.rng_of_visible _ _ _ V3)
                (A.ProgBridge.rng_of_visible _ _ _ V4)
                (A.ProgBridge.rng_of_visible _ _ _ V5)
                (A.ProgBridge.rng_of_visible _ _ _ V6)
                (A.ProgBridge.rng_of_visible _ _ _ V7)) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 (A.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))
           _ (POST cx) HFS); [exact (A.ProgBridge.fp_avoids_RNG_W _) |].
  (* G5: the continuation. *)
  intros ms' md' HQ0 Hhid Hsbm.
  destruct HQ0 as (ra' & t0' & t1' & t2' & t3' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' &
                   Ems & MU & WM & Hdecl & Hndecl).
  subst ms'.
  cbn [ms_mem] in Hhid.
  (* the write set of this run *)
  set (W := [(sp - 16, sp); (fr + 128, fr + 140)] : list Lib.Frame.ivl).
  assert (AW : A.AsanRTFacts.all_app W).
  { unfold W. cbn [A.AsanRTFacts.all_app]. split; [| split; [| exact I]].
    - intros x Hx. unfold A.AsanRT.app_mem, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END.
      unfold A.Prog.ImgBounds.IMG_HI in Himg. right. lia.
    - intros x Hx. apply Happ. lia. }
  assert (Dlo : forall a n, 0 <= n -> a + n <= sp - 16 -> (a + n <= fr + 128 \/ fr + 140 <= a) ->
                  Lib.Frame.disjoint_from W a n).
  { intros a n Hn Ha Hf. unfold W. cbn [Lib.Frame.disjoint_from].
    split; [left; lia | split; [exact Hf | exact I]]. }
  assert (Dhi : forall a n, sp <= a -> Lib.Frame.disjoint_from W a n).
  { intros a n Ha. unfold W. cbn [Lib.Frame.disjoint_from]. split; [right; lia | split; [right; lia | exact I]]. }
  (* the register map of the end state *)
  set (R1 := Lib.Frame.mkR ra' (lib.Reusable.YK11.getr regs3 2)
               (lib.Reusable.YK11.getr regs3 3) (lib.Reusable.YK11.getr regs3 4) t0' t1' t2'
               (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
               (Z_to_bv 64 (if Prog.RcLeaf.decl (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j) then 0 else -1))
               a1' a2' a3' a4' a5' a6' a7'
               (lib.Reusable.YK11.getr regs3 18) (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20)
               (lib.Reusable.YK11.getr regs3 21) (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23)
               (lib.Reusable.YK11.getr regs3 24) (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26)
               (lib.Reusable.YK11.getr regs3 27) t3' (lib.Reusable.YK11.getr regs3 29)
               (lib.Reusable.YK11.getr regs3 30) (lib.Reusable.YK11.getr regs3 31)).
  (* the register equalities of the end map *)
  assert (E2 : lib.Reusable.YK11.getr R1 2 = lib.Reusable.YK11.getr regs3 2) by reflexivity.
  assert (E3 : lib.Reusable.YK11.getr R1 3 = lib.Reusable.YK11.getr regs3 3) by reflexivity.
  assert (E4 : lib.Reusable.YK11.getr R1 4 = lib.Reusable.YK11.getr regs3 4) by reflexivity.
  assert (E8 : lib.Reusable.YK11.getr R1 8 = lib.Reusable.YK11.getr regs3 8) by reflexivity.
  assert (E9 : lib.Reusable.YK11.getr R1 9 = lib.Reusable.YK11.getr regs3 9) by reflexivity.
  assert (E18 : lib.Reusable.YK11.getr R1 18 = lib.Reusable.YK11.getr regs3 18) by reflexivity.
  assert (E19 : lib.Reusable.YK11.getr R1 19 = lib.Reusable.YK11.getr regs3 19) by reflexivity.
  assert (E21 : lib.Reusable.YK11.getr R1 21 = lib.Reusable.YK11.getr regs3 21) by reflexivity.
  assert (E22 : lib.Reusable.YK11.getr R1 22 = lib.Reusable.YK11.getr regs3 22) by reflexivity.
  assert (E23 : lib.Reusable.YK11.getr R1 23 = lib.Reusable.YK11.getr regs3 23) by reflexivity.
  assert (E24 : lib.Reusable.YK11.getr R1 24 = lib.Reusable.YK11.getr regs3 24) by reflexivity.
  assert (E26 : lib.Reusable.YK11.getr R1 26 = lib.Reusable.YK11.getr regs3 26) by reflexivity.
  assert (E10 : lib.Reusable.YK11.getr R1 10 =
                Z_to_bv 64 (if Prog.RcLeaf.decl (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j) then 0 else -1))
    by reflexivity.
  (* the transporter record *)
  assert (TR : A.ACtlG.F26.b7g_tr (fun p n => Lib.Frame.disjoint_from W p n) mem3 m' regs3 R1).
  { split; [intros p n p' n' HK Hp Hn Hpn; exact (A.AsanRTFacts.disjoint_from_sub W p n p' n' HK Hp Hpn) |].
    split; [intros a bs n HK Hl Hby; apply (Lib.Frame.bytes_at_transport segs W mem3 m' a bs Hby MU);
            rewrite Hl; exact HK |].
    split; [intros p n _ Had; exact (A.ACtlG.F26.b7g_addr_app W mem3 m' p n MU AW Had) |].
    intros off v Ho0 Ho Hsp.
    apply (A.ACtlG.F26.b7g_spill_keep W mem3 m' regs3 R1 Aa off v R9 ltac:(lia)
             ltac:(change (2 ^ 64) with 18446744073709551616; lia) Ho0 Ho E9 MU); [| exact Hsp].
    apply Dhi. lia. }
  (* the frame window on the new memory: the run writes [fr + 128, fr + 140) inside it *)
  assert (HSTK1 : Lib.Frame.stk segs m' fr (fr + ACtlCutP.FRAME_BYTES)).
  { apply (Lib.Frame.stk_transport segs W mem3 m' fr (fr + ACtlCutP.FRAME_BYTES) HSTK0 MU WM).
    intros x Hx. unfold ACtlCutP.FRAME_BYTES in Hx.
    destruct (Z_lt_le_dec x (fr + 128)) as [H1 | H1].
    - left. unfold W. cbn [Lib.Frame.outside]. split; [lia | split; [lia | exact I]].
    - destruct (Z_lt_le_dec x (fr + 140)) as [H2 | H2].
      + right. apply (f24_present mem3 m' x); [lia | change (2 ^ 64) with 18446744073709551616; lia | exact WM |].
        exact (proj2 (Hs x ltac:(lia))).
      + left. unfold W. cbn [Lib.Frame.outside]. split; [lia | split; [lia | exact I]]. }
  (* ProgBridge.cfg_at_MS read backwards (it is eq_refl), at the exit cut's pc *)
  change (Reusable.YA0n.SRr segs W3
            (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A825d4_at [Z.of_nat j])) R1 m' md')
            (POST cx)).
  (* the exit cut *)
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R1 m' md' HB).
  - (* the journal crosses the callee's stack window and the frame's ports words *)
    eapply (Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
      with (Wr := fun a => (sp - 16 <= a < sp) \/ (fr + 128 <= a < fr + 140)).
    + exact HJ.
    + intros x Hx. unfold Reusable.YK04.mrestrict.
      destruct (Reusable.YA0n.w_H W3 x); [reflexivity |].
      apply (MU x). unfold W. cbn [Lib.Frame.outside].
      split; [intros H; apply Hx; left; exact H |].
      split; [intros H; apply Hx; right; exact H | exact I].
    + intros x Hx. unfold Reusable.YK04.mrestrict in *.
      destruct (Reusable.YA0n.w_H W3 x); [exact Hx |].
      destruct (A.Prog.Seg.F24.b7_out_dec W (bv_unsigned x)) as [Hout | Hout].
      * rewrite (MU x Hout). exact Hx.
      * destruct (A.Prog.Seg.F24.b7_in_cases W (bv_unsigned x) Hout) as (lo & hi & Hin & Hr).
        unfold W in Hin. cbn [In] in Hin. destruct Hin as [E | [E | []]]; injection E as <- <-.
        -- apply (A.ACtlG.F26.b7g_grow mem3 m' x); [unfold A.Prog.ImgBounds.IMG_HI in *; lia | exact WM | exact Hx].
        -- apply (A.ACtlG.F26.b7g_grow mem3 m' x); [lia | exact WM | exact Hx].
    + exact Hhid.
    + exact Hsbm.
    + intros a Ha. destruct Ha as [Ha | Ha].
      * left. unfold A.ACfn.LLVMF_STK. lia.
      * unfold Reusable.YCbq.awr_byte, Reusable.YCbq.in_frames.
        right. right. right. exists 6, (ACtlCut.c_fpos cx). split.
        -- cbv beta iota delta [ACtlCut.ix_cut ACtlCut.cut_own ACtlCutP.C_A825c8_at ACtlCut.own6].
           left. reflexivity.
        -- left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr3.
           change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 14 + 2j + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A825d4_at (ACtlCutP.v:2622-2630) *)
    split; [reflexivity |].
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A825d4_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    (* FRAC, re-established on the end map and the new memory by WALKING the record (a Theorem Labs lane 05:53Z):
       each conjunct of the entry's FRAC (HFR) is carried to the end state by its shape -- a q64 or bytes_at
       by the b7g transport, its kept-range side condition by Dhi (at or above sp) or Dlo (below sp - 16 and off
       the ports words [fr + 128, fr + 140)); the frame shadow likewise (it is off the frame: fr is app memory);
       every register or pure conjunct by conversion (the end map keeps registers 2 3 4 8 9 19 26).  A conjunct
       appended to FRAC is walked by the same step with no edit: a q64 at fr + 4088 (the class-6 frame's
       trailer) lies above fr + 140 and below fr + 4096 <= alloc_ceiling < sp - 16, so Dlo keeps it. *)
    split.
    { exists Aa, sp.
      pose proof HFR as HFRw.
      repeat lazymatch type of HFRw with
        | _ /\ _ => let C := fresh "C" in destruct HFRw as [C HFRw]; split; [revert C; clear HFRw | clear C]
        end.
      all: try revert HFRw.
      all: intros C; lazymatch goal with
        | |- ACtlCutP.q64 _ _ _ =>
            apply (A.ACtlG.F26.b7g_q64 _ _ _ _ _ TR); [first [apply Dhi; lia | apply Dlo; lia] | exact C]
        | |- Lib.Mem.bytes_at _ _ _ ?bs =>
            apply (A.ACtlG.F26.b7g_by _ _ _ _ _ TR _ _ (Z.of_nat (length bs)));
              [first [apply Dhi; lia | apply Dlo; lia] | reflexivity | exact C]
        | |- exists _, _ =>
            destruct C as (sh & Hsh & Hshlen); exists sh; split; [| exact Hshlen];
            apply (A.ACtlG.F26.b7g_by _ _ _ _ _ TR _ _ (Z.of_nat (length sh))); [| reflexivity | exact Hsh];
            pose proof (Happ fr ltac:(lia)) as Hafr;
            unfold A.AsanRT.app_mem, A.AsanRT.LOWMEM_END, A.AsanRT.HIGHMEM_BEG, A.AsanRT.APPMEM_END in Hafr;
            apply Dlo; [lia | |];
              unfold ACtlCutP.Sfr, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K;
              rewrite Hshlen; unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES;
              change (Z.of_nat (Z.to_nat (3136 / 8))) with 392;
              Z.div_mod_to_equations; lia
        | |- _ =>
            first [ exact C
                  | etransitivity; [eassumption | exact C]
                  | unfold ACtlCut.rgv in *; etransitivity; [eassumption | exact C]
                  | unfold Reusable.YG0d.spZ in *; rewrite <- C; f_equal; assumption ]
        end. }
    (* b7_body *)
    exists phi.
    split; [exact HPerm |]. split; [exact Hn26 |]. split; [exact Hj255 |].
    assert (KF : Lib.Frame.disjoint_from W (fr + 2624) (ACtlCutP.FRAME_BYTES - 2624))
      by (apply Dlo; unfold ACtlCutP.FRAME_BYTES; lia).
    assert (KI : Lib.Frame.disjoint_from W (ACtlCut.c_p cx) (ACtlCut.c_n cx)) by (apply Dlo; lia).
    assert (KB : Lib.Frame.disjoint_from W phi (ACtlCutP.flen cx j)) by (apply Dlo; lia).
    split.
    { apply (A.ACtlG.F26.b7g_HB _ _ _ _ _ phi (ACtlCutP.flen cx j) TR); [| exact HHB].
      apply Dlo; unfold A.ACtlK.a_size; lia. }
    split; [exact (A.ACtlG.F26.b7g_FLSI _ _ _ _ _ cx j fr TR KF KI Hinlen' HSTK1 HFLSI) |].
    split; [exact (A.ACtlG.F26.b7g_B7K _ _ _ _ _ cx j phi fr TR KF KB E18 E21 E22 E23 E24 HB7K) |].
    (* the tail of C_A825d4_at *)
    split; [unfold ACtlCut.rgv; exact E10 |].
    split.
    { unfold ACtlCutP.PORTS. unfold A.Prog.SlotModel.t_rp.
      destruct (Prog.RcLeaf.decl (A.Prog.SlotModel.t_pbs (ACtlCut.c_in cx) j)) eqn:Ed.
      - split; [intros _ | intros E; exfalso; exact (E eq_refl)].
        first [exact (Hdecl eq_refl) | exact (Hdecl Ed)].
      - split; [intros E; discriminate E | intros _].
        assert (MU1 : Lib.Frame.munch [(sp - 16, sp)] mem3 m')
          by (first [exact (Hndecl eq_refl) | exact (Hndecl Ed)]).
        assert (Ds : forall a n, a + n <= sp - 16 -> Lib.Frame.disjoint_from [(sp - 16, sp)] a n).
        { intros a n Ha. cbn [Lib.Frame.disjoint_from]. split; [left; exact Ha | exact I]. }
        unfold ACtlCutP.u32 in *.
        split; [apply (Lib.Frame.bytes_at_transport segs [(sp - 16, sp)] mem3 m' _ _ U0 MU1);
                rewrite Lib.Mem.length_le4; apply Ds; lia |].
        split; [apply (Lib.Frame.bytes_at_transport segs [(sp - 16, sp)] mem3 m' _ _ U4 MU1);
                rewrite Lib.Mem.length_le4; apply Ds; lia |].
        apply (Lib.Frame.bytes_at_transport segs [(sp - 16, sp)] mem3 m' _ _ U8 MU1).
        rewrite Lib.Mem.length_le4. apply Ds. lia. }
    exact (A.ACtlG.F26.b7g_addr_app W mem3 m' (fr + 128) 12 MU AW HADq).
  - (* ctl_rt_C at the same state (ly3, S3): the write set is the callee's stack window and the frame's ports
       words, both above the image and app memory, so no shadow byte moves and both regions carry over *)
    unfold A.ACtlRtC.ctl_rt_C.
    split.
    { unfold A.ACtlK.asan_cells_at in *.
      apply (A.AsanRTFacts.asan_cells_kept W mem3 m' HAC MU).
      apply Dlo; [unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia | |];
        unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI; unfold A.Prog.ImgBounds.IMG_HI in Himg, HfrGT; lia. }
    split.
    { exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Hcut (A.AsanRTFacts.munch_meta W mem3 m' MU AW) WM). }
    split.
    { exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Himgsh (A.AsanRTFacts.munch_meta W mem3 m' MU AW) WM). }
    apply (A.ACtlG.F26.b7g_ro W mem3 m' HRO MU).
    intros lo hi Hin. unfold W in Hin. cbn [In] in Hin. destruct Hin as [E | [E | []]];
      injection E as <- <-; lia.
Qed.

End GlueF24.

Print Assumptions glue_seg_F24.
