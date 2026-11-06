(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module names and numbers changed; 1086 of its 1232 lines of code are new or changed and 1651 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R7tail.v; 1150 of its 1202 lines of code are new or changed and 1180 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R7.v, with its module names changed; 269 of its 325 lines of code are new or changed and 1146 lines of the source are left out. *)
(* lib/A/ACtlG/P2.v -- GLUE for stage seg_P2 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:715):
     glue_seg_P2 : forall POST, CF POST C_A81b14 -> CF POST C_A81b10
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_P2.  Written by a Theorem Labs lane (piece W3a: P1, P1_70, P2, P4); single writer.
   rule 24: no function proved (stage glue of a walk).

   THE SEGMENT (Seg/P2.v at U 6a74d5929d2, seg_P2 :119; v1.9 0x81b10 -> 0x81b14): the single instruction
   `sb s2,332(s3)` with s3 = S(fr), one store of one byte into the OWN frame's shadow, at S(fr) + 332.  The exit
   cut C_A81b14 is C_A81b10's body with the stack pointer named (spv) and bounded.

   THE RUN LIFTED: a Theorem Labs lane's footprint run seg_P2_run_F (lib/A/Prog/Seg/P2F.v (at head lib/A/Prog/Seg/P2F.v:76) (an earlier version, blob 75f692c4dba, not in this delivery)) in its
   route-(C) form seg_P2_run_F_on (lib/A/Prog/Seg/P2F_on.v, this lane's twin; P2F.v's code is unchanged since release c5e779efe8c (comments edited) and differs from the blob above: 39 of its code lines changed or removed, 72 added).  The twin asks for
   the ONE shadow byte it stores, `shadow_rw_on (seg_P2_run_shadow_R fr)`, where the old run asked for the
   universal A.AsanRT.shadow_rw, which route (C)'s cut no longer carries.

   THE PROOF (glue-pattern.md section 3, L3-recipe.md section 2)
   G1  unfold the entry cut C_A81b10 (ACtlCutP.v:1859-1874).
   G2  numeric facts from VISIBLE state: FRAC's spill base A and its sp; the frame bounds (frames_bounds, the
       frame law, layout_le's ly_F, in_app) put the frame-shadow window [Sh, Sh + 392) in the ASan shadow and
       apart from the stack, the runtime cells and the frame itself; the stack geometry from the journal's astk_ok.
   G3  cfg_at_MS, then the walk moved to the run's canonical register map (YA0nR.SRr_xregs_eqv).
   G4  seg_P2_run_F_on at RNG := ProgBridge.RNG_W (w_H W3); its one footprint premise from visibility (KitMem K6),
       its one shadow byte from ctl_rt_C's cut_shadow (disjunct (F), the own frame), lifted by YA0nR.SRr_fsteps.
   G5  the exit cut C_A81b14 (ACtlCutP.v:1878-1894) at the run's end map R and memory m' = the one-byte write:
         journal   a Theorem Labs lane's ajournal_of_fsteps (write set [Sh + 332, Sh + 333): a frame-shadow byte of the class-6
                   frame, awr_byte's frame case, in_zr's shadow half);
         frames, frame law, k bound   unchanged (own6, kmax 14 on both cuts);
         body      registers through the run's post; spv is FRAC's own sp, bounded by FRAC; every application byte
                   is unchanged (the one written byte is a shadow byte); FRAC's 392 frame-shadow bytes are rebuilt
                   from the exit's own cut_shadow by a Theorem Labs lane's P1.p1_sh_bytes_on;
         ctl_rt_C  asan_cells by AsanRTFacts.asan_cells_kept (the runtime cells are not the written byte),
                   both shadow regions by p2_srw_on_write (a write only adds presence), ro_agree by
                   p2_ro_at_write (the written byte is above the image, so not a read-only address).

   ROUTE (C) (L3-recipe.md section 2 (a working note, not in this delivery), a Theorem Labs lane): the cut carries `A.ACtlRtC.ctl_rt_C B ly3 S3 mem3`
   (asan_cells_at /\ shadow_rw_on (cut_shadow B ly3 S3) /\ shadow_rw_on img_shadow /\ ro_agree_at).  This file is
   new, so it is written in that form from the start: it never names VIS0, OWNED_RO or ctlrt_of_AR.

   CITED BY NAME: a Theorem Labs lane's PROVED A.ProgWorld.ajournal_of_fsteps (ProgWorld.v:1091) and a Theorem Labs lane's PROVED
   A.ACtlG.KitMem.kitmem_rng_frame_sh / kitmem_addressable_mrd / kitmem_mrd_munch / kitmem_input_apart
   (a working branch 4a56e997c0f + dcdc870e8ff, merged); a Theorem Labs lane's PROVED
   A.Prog.Seg.P1.p1_sh_bytes_on (Seg/P1.v b2bcfe72edf (the blob this tree had at release c5e779efe8c), taken by path from a working branch
   a4e0d5b5a2e); a Theorem Labs lane's PROVED, premise-free A.ProgWorld_Fs.ctl_frame_above_img.
   SECTION HYPOTHESES (exact text below)
   - LAWS       : the core's AR laws (ACtl.v:183).

   CLOSURE: every Require is qualified.  The six modules that exist both as the core's lib/Reusable/<X> and as
   ctrl's lib/A/Reusable/<X> (YI04 YI16 YK11 YK1b YM05 YO09) are named by FULL path (aliases CK11 / CM05 / CO09
   below), as a Theorem Labs lane ruled (03:5xZ).

   BUILD STATE: see the commit message. *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* the doubled modules by absolute name: a From-form `Require Reusable.YK11` would also match lib.A.Reusable.YK11
   by suffix (porter 04:33Z) *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG01 Reusable.YG0f Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.MemNorm A.MemNormTr A.Prog.ImgBounds.
(* route (C): the narrowed runtime predicate and its leaf *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.P1 A.Prog.Seg.P2F_on.
(* lib/Lib by absolute name: ctrl's lib/A trees carry modules of the same short names *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem A.ProgWorld A.ProgWorld_Fs.
Import ListNotations.
Local Open Scope Z_scope.

(* The six doubled modules, by full path (a Theorem Labs lane 03:5xZ). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
(* Every `Lib.<X>` below is the unit's top-level lib/Lib module, by these aliases (lib/A/Bz/Lib has twins). *)
Module Lib.
  Module ExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
  Module MState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
  Module Regs6ss := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
  Module Frame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
  Module Mem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
  Module Step := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
  Module Cells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
  Module RngBytes := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
End Lib.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   Two transports across the segment's single store, both file-local (the pattern's rule: a helper a stage needs
   and the shared kit lacks stays in the stage until the kit's writer takes it).

   p2_srw_on_write: a write never removes a byte, so every region that is present and writable before it still is
   after it.  This is the route-(C) counterpart of what the old proof read off the run's `shadow_rw m'` post.  Its
   shape is lib/Lib/Frame.v's stk_write (:215-224). *)
Lemma p2_srw_on_write : forall (P : Z -> Prop) (m : word -> option byte) (a : Z) (bs : list byte),
  A.ShadowRwOn.shadow_rw_on P m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  A.ShadowRwOn.shadow_rw_on P (write_to_mem m (Lib.Mem.wa a) bs).
Proof.
  intros P m a bs H Ha Hl x Hp Hs. destruct (H x Hp Hs) as (Hw & b & Hb).
  pose proof (A.AsanRTFacts.in_shadow_range _ Hs) as Hxr.
  split; [exact (Lib.Mem.wview_write_mono A.Img0.rsegs m (Lib.Mem.wa a) bs _ Hw)|].
  unfold Lib.Mem.mrd in Hb |- *. rewrite Lib.Mem.write_to_mem_spec by lia.
  rewrite Lib.Mem.wa_unsigned by lia.
  destruct (Z.leb_spec0 a x) as [L|L]; destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))) as [R|R];
    cbn [andb]; try (exists b; exact Hb).
  destruct (nth_error bs (Z.to_nat (x - a))) as [c|] eqn:E; [exists c; reflexivity|].
  exfalso. apply nth_error_None in E. lia.
Qed.

(* p2_ro_at_write: a write outside the image's read-only addresses keeps ro_agree_at. *)
Lemma p2_ro_at_write : forall (m : word -> option byte) (a : Z) (bs : list byte),
  A.ACtlK.ro_agree_at m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  A.Prog.ImgBounds.IMG_HI <= a ->
  A.ACtlK.ro_agree_at (write_to_mem m (Lib.Mem.wa a) bs).
Proof.
  intros m a bs H Ha Hl Himg x Hx.
  pose proof (bv_unsigned_in_range 64 x) as Hxr. unfold bv_modulus in Hxr.
  unfold Lib.Mem.mrd in H |- *. rewrite Lib.Mem.write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)) as [L|L];
    destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))) as [R|R]; cbn [andb];
    try (exact (H x Hx)).
  exfalso.
  assert (Ex : Lib.Mem.wa (bv_unsigned x) = x) by (unfold Lib.Mem.wa; apply Z_to_bv_bv_unsigned).
  rewrite <- Ex in Hx.
  rewrite (A.MemNormTr.ro_addr_above_img (bv_unsigned x) ltac:(lia)) in Hx. discriminate Hx.
Qed.

Section GlueP2.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:217-218, :250-251), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81b10 := (ACtlCutP.C_A81b10 B).
Local Notation C_A81b14 := (ACtlCutP.C_A81b14 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_P2 : forall POST, CF POST C_A81b14 -> CF POST C_A81b10.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut (ACtlCutP.v:1859-1874). *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81b10] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & Hour & HCUR & HPRO & S144 &
    (A & idb & junk & R9 & R27 & HA & RW192 & RWidb & RWjunk & Q280 & Q240 & (jy & junk2 & RWjy & RWj2))).
  destruct Hrt as (HAC & Hcut & Himg & HRO).
  (* G2: numeric facts from visible state. *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & ESL & ESH & _).
  destruct Hastk as (_ & _ & Hceil_lo & Hstk_lo & Hstk_hi & _).
  pose proof (@CM05.alloc_ceiling_value rc) as ((Hceil0 & Hceil1) & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  pose proof (A.ProgWorld_Fs.ctl_frame_above_img B ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6) as Hfimg.
  assert (Efr : fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) ltac:(left; reflexivity)).
    unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite <- Efr, HFB6 in Hfceil, Hfapp. rewrite <- Efr in Hfimg, Hf4096.
  unfold A.Prog.ImgBounds.IMG_HI in Hfimg.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg,
    Reusable.YG0f.ASAN_CEIL in Hfapp.
  pose proof HFRAC as (Af & spf & F2 & F16 & FspZ & _ & _ & F9 & _ & F19 & _ & Ffr32 & FA32 & FAc & FspA & FfrA &
    FA416 & Fc4096 & Fapp & _).
  assert (EA : Af = A).
  { assert (E : Z_to_bv 64 Af = Z_to_bv 64 A) by (unfold ACtlCut.rgv in F9; rewrite <- F9; exact R9).
    apply (f_equal (@bv_unsigned 64)) in E.
    rewrite (Lib.MState.unsigned_lit Af) in E
      by (unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *; lia).
    rewrite (Lib.MState.unsigned_lit A) in E by lia. exact E. }
  subst Af.
  unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in FfrA, Fapp.
  unfold A.ACfn.LLVMF_STK in Hpres, Hstk_lo.
  (* the frame's shadow window: Sh = fr / 8 + ASAN_K, fr = 8 (fr / 8) *)
  set (Sh := ACtlCutP.Sfr fr) in *.
  assert (ESh : Sh = fr / 8 + 0x7fff8000) by reflexivity.
  assert (Efr8 : fr = 8 * (fr / 8)) by (pose proof (Z.div_mod fr 8 ltac:(lia)); lia).
  assert (HSH : forall i, 0 <= i < 392 -> A.AsanRT.in_shadow (Sh + i)).
  { intros i Hi. unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END,
      A.AsanRT.HIGHSHADOW_BEG, A.AsanRT.HIGHMEM_BEG. rewrite ESh. lia. }
  assert (HShlo : 0x7fff8000 <= Sh) by lia.
  assert (HShhi : Sh + 392 <= 0x10007fff8000) by lia.
  (* the stack pointer the exit cut names, and its bound: FRAC's own sp *)
  assert (Hsp0 : 0 <= spf < 2 ^ 64) by lia.
  (* the frame's shadow window lies in cut_shadow's own-frame disjunct (F) *)
  assert (HFsh : forall a, Sh <= a < Sh + 512 -> A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a Ha. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite <- Efr, HFB6, ESh in *. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
    change (4096 / 8) with 512. lia. }
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81b10) with 0x81b10.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81b10) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the run's two premises at RNG_W (w_H W3), then the run. *)
  pose (H3 := Reusable.YA0n.w_H W3).
  pose (RNG := A.ProgBridge.RNG_W H3).
  assert (RSH : Lib.ExecF.rng RNG (Sh + 332) 1).
  { apply (A.ACtlG.KitMem.kitmem_rng_frame_sh B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) (Sh + 332) 1
             HAR Hin6);
      rewrite <- Efr; change (A.AsanRT.shadow_addr fr) with Sh;
      [lia | rewrite HFB6; change (4096 / 8) with 512; lia]. }
  assert (HSW332 : A.ShadowRwOn.shadow_rw_on (A.Prog.Seg.P2F_on.seg_P2_run_shadow_R fr) mem3).
  { apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3)); [|exact Hcut].
    intros a Ha. unfold A.Prog.Seg.P2F_on.RFon.seg_P2_run_shadow_R in Ha.
    assert (Ea : a = Sh + 332) by (rewrite Ha; reflexivity).
    rewrite Ea. apply HFsh. lia. }
  pose proof (A.Prog.Seg.P2F_on.seg_P2_run_F_on (fx := A.Reusable.YK11.mkFP CK11.fp_regs CK11.fp_csr)
    regs3 mem3 fr RNG ltac:(unfold ACtlCut.rgv in F19; exact F19)
    ltac:(exact (HSH 332 ltac:(lia))) HSW332 ltac:(exact RSH)) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  destruct HFS as (ms' & Hrun & HQ0).
  apply (Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 _ ms' md3 RNG (POST cx) Hrun
           (A.ProgBridge.fp_avoids_RNG_W H3)).
  intros md' Hsbm.
  (* G5: the run's end state is the exit cut's state at the run's own map R and the written memory m'. *)
  destruct HQ0 as (R & pc' & m' & Ems & Epc & K2 & K3 & K4 & K8 & K9 & K26 & K19 & K27 & K22 & K25 &
    (bs & Em' & Ebs)).
  subst ms' pc'.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81b14) R m' md') (POST cx)).
  (* the one-byte write, as a munch and a wmono over the write set [Sh + 332, Sh + 333) *)
  assert (Hb1 : Z.of_nat (length bs) = 1) by (rewrite Ebs; reflexivity).
  assert (MU : Lib.Frame.munch [(Sh + 332, Sh + 333)] mem3 m').
  { rewrite Em'. apply (Lib.Frame.munch_write [(Sh + 332, Sh + 333)] mem3 mem3 (Sh + 332) bs
      (Lib.Frame.munch_refl _ _)); [lia | lia |]. cbn [Lib.Frame.inside]. left. lia. }
  assert (WM : Lib.Frame.wmono segs mem3 m')
    by (rewrite Em'; exact (Lib.Frame.wmono_write segs mem3 mem3 (Lib.Mem.wa (Sh + 332)) bs
          (Lib.Frame.wmono_refl segs mem3))).
  (* the registers the run keeps, on the core's getr *)
  assert (G2 : CK11.getr R 2 = CK11.getr regs3 2) by exact K2.
  assert (G3 : CK11.getr R 3 = CK11.getr regs3 3) by exact K3.
  assert (G4 : CK11.getr R 4 = CK11.getr regs3 4) by exact K4.
  assert (G8 : CK11.getr R 8 = CK11.getr regs3 8) by exact K8.
  assert (G9 : CK11.getr R 9 = CK11.getr regs3 9) by exact K9.
  assert (G19 : CK11.getr R 19 = CK11.getr regs3 19)
    by (transitivity (Z_to_bv 64 (ACtlCutP.Sfr fr)); [exact K19|];
        symmetry; unfold ACtlCut.rgv in F19; exact F19).
  assert (G26 : CK11.getr R 26 = CK11.getr regs3 26) by exact K26.
  assert (G27 : CK11.getr R 27 = CK11.getr regs3 27) by exact K27.
  assert (G22 : CK11.getr R 22 = CK11.getr regs3 22) by exact K22.
  assert (G25 : CK11.getr R 25 = CK11.getr regs3 25) by exact K25.
  assert (RA : CK11.getr R 9 = Z_to_bv 64 A) by (transitivity (CK11.getr regs3 9); [exact G9 | exact R9]).
  (* memory kept across the run: every application byte, and every shadow byte but the one written *)
  assert (Tb : forall a bs0, Lib.Mem.bytes_at segs mem3 a bs0 ->
                 (a + Z.of_nat (length bs0) <= Sh + 332 \/ Sh + 333 <= a) ->
                 Lib.Mem.bytes_at segs m' a bs0).
  { intros a bs0 Hb Hd. apply (Lib.Frame.bytes_at_transport segs [(Sh + 332, Sh + 333)] mem3 m' a bs0 Hb MU).
    cbn [Lib.Frame.disjoint_from]. lia. }
  assert (Tq : forall a v, ACtlCutP.q64 mem3 a v -> (a + 8 <= Sh + 332 \/ Sh + 333 <= a) ->
                 ACtlCutP.q64 m' a v).
  { intros a v Hq H1. unfold ACtlCutP.q64 in *. apply Tb; [exact Hq|]. rewrite Lib.Mem.length_le8. lia. }
  assert (Trw : forall a cs, Lib.Step.rw_cells segs mem3 a cs ->
                  (a + Z.of_nat (Lib.Cells.cells_size cs) <= Sh + 332 \/ Sh + 333 <= a) ->
                  Lib.Step.rw_cells segs m' a cs).
  { intros a cs Hc Hd. apply (Lib.Frame.rw_cells_transport segs [(Sh + 332, Sh + 333)] mem3 m' a cs Hc MU WM).
    cbn [Lib.Frame.disjoint_from]. lia. }
  assert (Tad : forall p n, A.AsanRT.addressable mem3 p n ->
                  (p + n <= fr + 2656 \/ fr + 2664 <= p) -> A.AsanRT.addressable m' p n).
  { intros p n Had Hpn. apply (A.ACtlG.KitMem.kitmem_addressable_mrd mem3 m' p n Had).
    intros i Hi. pose proof Had as (Hp0 & Hn0 & Hpe & _). unfold A.AsanRT.APPMEM_END in Hpe.
    pose proof (Z.div_mod (p + i) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p + i) 8 ltac:(lia)).
    apply (A.ACtlG.KitMem.kitmem_mrd_munch [(Sh + 332, Sh + 333)] mem3 m' _ MU).
    - unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. lia.
    - cbn [Lib.Frame.outside]. split; [|exact I].
      unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. rewrite ESh. lia. }
  assert (Tsp : forall off v, 0 <= off <= 312 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R m' off v).
  { intros off v Hoff (Ab & HAb & Hq). exists A. split; [exact RA|].
    assert (EAb : Ab = A).
    { pose proof Hq as Hbd. unfold ACtlCutP.q64 in Hbd. apply Lib.Mem.bytes_at_bound in Hbd.
      rewrite Lib.Mem.length_le8 in Hbd.
      assert (E : Z_to_bv 64 Ab = Z_to_bv 64 A) by (unfold ACtlCut.rgv in HAb; rewrite <- HAb; exact R9).
      apply (f_equal (@bv_unsigned 64)) in E. rewrite (Lib.MState.unsigned_lit A) in E by lia.
      rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
      destruct (Z_le_gt_dec 0 Ab) as [Pb|Pb].
      - rewrite Z.mod_small in E by lia. exact E.
      - exfalso. rewrite <- (Z.mod_add Ab 1 (2 ^ 64) ltac:(lia)) in E.
        rewrite Z.mod_small in E by lia. lia. }
    subst Ab. apply Tq; [exact Hq | lia]. }
  (* the in-block facts of the lib pre (KitMem K3) *)
  destruct (A.ACtlG.KitMem.kitmem_input_apart (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI cx [] ly3 S3 W3
              mem3 md3 k LAWS HB HJ HF HP
              (A.ProgWorld_Fs.ctl_frame_above_img B ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6))
    as (Hlin & Hp0 & Hpceil & Hpfr & Hpapp).
  rewrite <- Efr, HFB6 in Hpfr. unfold Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg in Hpapp.
  (* the exit's own shadow regions: a write only adds presence *)
  assert (Hcut' : A.ShadowRwOn.shadow_rw_on (A.ACtlRtC.cut_shadow B ly3 S3) m')
    by (rewrite Em'; exact (p2_srw_on_write _ mem3 (Sh + 332) bs Hcut ltac:(lia) ltac:(lia))).
  assert (Himg' : A.ShadowRwOn.shadow_rw_on A.ACtlRtC.img_shadow m')
    by (rewrite Em'; exact (p2_srw_on_write _ mem3 (Sh + 332) bs Himg ltac:(lia) ltac:(lia))).
  apply (HX cx [] fr k ly3 S3 W3 R m' md' HB).
  - (* journal: a Theorem Labs lane's ajournal_of_fsteps; the write set is one frame-shadow byte of the class-6 frame *)
    lazymatch type of Hrun with
    | Reusable.YK04R.fsteps _ _ ?s0 _ =>
        refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ s0 _ _ _ _ RNG
                  [(Sh + 332, Sh + 333)] HJ Hrun
                  (A.ProgBridge.fp_avoids_RNG_W H3) MU Hsbm _)
    end.
    intros a Ha Hw. cbn [Lib.Frame.outside] in Hw.
    unfold Reusable.YCbq.awr_byte. right; right; right.
    exists 6, (ACtlCut.c_fpos cx). split; [exact (in_eq _ _)|].
    right. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr, HFB6.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. rewrite ESh in Hw.
    change (4096 / 8) with 512. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: kmax 14 on both cuts *)
    exact Hk.
  - (* the exit body, C_A81b14 (ACtlCutP.v:1878-1894) *)
    cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_A81b14].
    split; [exact HP|].
    split.
    { (* FRAC: its registers through the run's post, its application bytes unchanged, its frame-shadow bytes
         rebuilt from the exit's own cut_shadow *)
      pose proof (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC G2 G3 G4 G8 G9 G19 G26) as HF1.
      destruct HF1 as (Af & spf2 & F1 & F2' & F3 & F4 & F5 & F6 & F7 & F8 & F9' & F10 & F11 & F12 & F13 & F14 &
        F15 & F16' & F17 & F18 & F19' & F20 & F21 & F22 & (sh & F23 & F23l) & F24).
      assert (EA' : Af = A).
      { assert (E : Z_to_bv 64 Af = Z_to_bv 64 A)
          by (unfold ACtlCut.rgv in F6; rewrite <- F6; exact RA).
        apply (f_equal (@bv_unsigned 64)) in E.
        rewrite (Lib.MState.unsigned_lit Af) in E
          by (unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *; lia).
        rewrite (Lib.MState.unsigned_lit A) in E by lia. exact E. }
      subst Af.
      exists A, spf2.
      do 17 (split; [assumption|]).
      split; [exact (Tq _ _ F18 ltac:(lia))|].
      split; [exact (Tq _ _ F19' ltac:(lia))|].
      split; [exact (Tq _ _ F20 ltac:(lia))|].
      split; [exact (Tq _ _ F21 ltac:(lia))|].
      split; [exact (Tq _ _ F22 ltac:(lia))|].
      split.
      - (* the 392 frame-shadow bytes: present after the write, by a Theorem Labs lane's p1_sh_bytes_on at the exit's cut_shadow *)
        unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES.
        change (Z.to_nat (3136 / 8)) with 392%nat.
        destruct (A.Prog.Seg.P1.p1_sh_bytes_on m' Sh 392
                    ltac:(apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3));
                          [intros a Ha; apply HFsh;
                           unfold A.Prog.Seg.P1.p1_sh_bytes_shadow_R in Ha; cbn [Z.of_nat] in Ha; lia
                          |exact Hcut'])
                    ltac:(intros i Hi; apply HSH; cbn [Z.of_nat] in Hi; lia) ltac:(lia) ltac:(lia))
          as (sh' & Hsh' & Hl').
        exists sh'. split; [exact Hsh' | exact Hl'].
      - (* the saved registers; and, once FRAC gains the announced fake-frame trailer word
           q64 m (fr + 4088) (flag_addr ..) as its last conjunct (two Theorem Labs lanes 05:0xZ), that word too *)
        first
          [ apply Tb; [exact F24|]; lia
          | destruct F24 as (F24 & F25); split; [apply Tb; [exact F24|]; lia | exact (Tq _ _ F25 ltac:(lia))] ]. }
    split; [exact Hn|].
    split.
    { unfold ACtlCutP.OURb in *. apply Tb; [exact Hour|].
      unfold A.Prog.SlotModel.OUR. rewrite length_map, length_seq. lia. }
    split.
    { destruct HCUR as (Hc & C22 & C25). split; [exact Hc|]. unfold ACtlCut.rgv in *.
      split; [transitivity (CK11.getr regs3 22); [exact G22 | exact C22]
             |transitivity (CK11.getr regs3 25); [exact G25 | exact C25]]. }
    split.
    { destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg &
        P184 & P256 & P264 & P272 & P32).
      split; [exact (Tsp 40 _ ltac:(lia) P40)|]. split; [exact (Tsp 120 _ ltac:(lia) P120)|].
      split; [exact (Tsp 136 _ ltac:(lia) P136)|]. split; [exact (Tsp 160 _ ltac:(lia) P160)|].
      split; [exact (Tsp 168 _ ltac:(lia) P168)|]. split; [exact (Tsp 176 _ ltac:(lia) P176)|].
      split; [exact (Tsp 208 _ ltac:(lia) P208)|]. split; [exact (Tsp 248 _ ltac:(lia) P248)|].
      split; [exact (Tad _ _ Pad ltac:(lia))|].
      split; [apply Tb; [exact Pin|]; rewrite Hlin; lia|].
      split; [intros Hn0; exact (Tad _ _ (Pg Hn0) ltac:(lia))|].
      split; [exact (Tsp 184 _ ltac:(lia) P184)|]. split; [exact (Tsp 256 _ ltac:(lia) P256)|].
      split; [exact (Tsp 264 _ ltac:(lia) P264)|]. split; [exact (Tsp 272 _ ltac:(lia) P272)|].
      exact (Tsp 32 _ ltac:(lia) P32). }
    split; [exact (Tsp 144 _ ltac:(lia) S144)|].
    (* the exit names the stack pointer: FRAC's own sp, bounded by FRAC *)
    exists spf, A, idb, junk.
    split; [transitivity (CK11.getr regs3 2); [exact G2 | exact F2]|].
    split; [exact RA|].
    split; [unfold ACtlCut.rgv in *; transitivity (CK11.getr regs3 27); [exact G27 | exact R27]|].
    split; [exact HA|].
    split; [exact Hsp0|].
    split; [apply Trw; [exact RW192|]; cbn [Lib.Cells.cells_size Lib.Cells.csize]; lia|].
    split; [apply Trw; [exact RWidb|]; cbn [Lib.Cells.cells_size Lib.Cells.csize]; lia|].
    split; [apply Trw; [exact RWjunk|]; cbn [Lib.Cells.cells_size Lib.Cells.csize]; lia|].
    split; [exact (Tq _ _ Q280 ltac:(lia))|].
    split; [exact (Tq _ _ Q240 ltac:(lia))|].
    exists jy, junk2.
    split; [apply Trw; [exact RWjy|]; cbn [Lib.Cells.cells_size Lib.Cells.csize]; lia|].
    apply Trw; [exact RWj2|]; cbn [Lib.Cells.cells_size Lib.Cells.csize]; lia.
  - (* ctl_rt_C m': the runtime cells are apart from the written byte, both shadow regions keep their presence,
       and the written byte is not a read-only address *)
    split; [exact (A.AsanRTFacts.asan_cells_kept [(Sh + 332, Sh + 333)] mem3 m' HAC MU
                     ltac:(cbn [Lib.Frame.disjoint_from]; unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia))|].
    split; [exact Hcut'|].
    split; [exact Himg'|].
    rewrite Em'.
    exact (p2_ro_at_write mem3 (Sh + 332) bs HRO ltac:(lia) ltac:(lia)
             ltac:(unfold A.Prog.ImgBounds.IMG_HI; lia)).
Qed.

End GlueP2.

Print Assumptions glue_seg_P2.
