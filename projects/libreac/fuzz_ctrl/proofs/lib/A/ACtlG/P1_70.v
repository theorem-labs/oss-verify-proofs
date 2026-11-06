(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module names and numbers changed; 1086 of its 1232 lines of code are new or changed and 1651 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R7tail.v; 1150 of its 1202 lines of code are new or changed and 1180 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R7.v, with its module names changed; 329 of its 397 lines of code are new or changed and 1134 lines of the source are left out. *)
(* lib/A/ACtlG/P1_70.v -- GLUE for stage seg_P1_70 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:713):
     glue_seg_P1_70 : forall POST, CF POST C_A81b10 -> CF POST C_A81ac8
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_P1_70.  Written by a Theorem Labs lane's glue lane (piece W3a: P1, P1_70, P2, P4); single writer.
   rule 24: no function proved (stage glue of a walk).

   THE SEGMENT (Seg/P1.v at U 6a74d5929d2, seg_P1_70 :728; v1.9 0x81ac8 -> 0x81b10): li s2,-8 ; fourteen one-byte
   stores `sb s2,K(s3)` into the frame shadow Sh = S(fr) (K = 272..276, 282..290) ; li a1,187 ; ld a0,152(s1) ;
   jal __asan_set_shadow_f8 (0x55008), return pc 0x81b10.  The callee fills [Q, Q + 187) of the frame shadow with
   0xf8 (Q is the [A + 152] spill, Sh <= Q, Q + 187 <= Sh + 328).

   THE RUN LIFTED, ONE PIECE (the split rule, a Theorem Labs lane 04:01Z / 04:3xZ: __asan_set_shadow_f8 has a PROVED footprint
   contract, so the stretch is consumed whole): a Theorem Labs lane's two ROUTE-(C) stretches of P1.p1_evt
   (lib/A/Prog/Seg/P1F.v, a working branch e4cf770da9b, blob 1dc297b725a), p1_evt_pre_F_on (:322, 0x81ac8
   -> the callee entry) and p1_evt_post_F_on (:387, the return pc, no step), joined by a Theorem Labs lane's PROVED footprint
   contract asan_set_shadowF.asan_set_shadow_f8_holds_F (asan_set_shadowF.v:172) over memset.memset_holds, exactly
   as P1F's p1_evt_of_pre_post_on (:422) joins them with the plain contract.  The join runs on `normalize rsegs m`
   (the stretches take mem_inv, which the cut does not carry: ACtlK.v:50) and is moved to the cut's memory by
   MemNormF.evtF_normalize_ro, as P4F.p4_evt_ro_F does; that composite is the local lemma p1_70_ro_F_on below
   (stated over the cut's ro_agree, as P1.p1_evt_ro_on is).

   ROUTE (C) (L3-recipe.md section 2): the cut carries `A.ACtlRtC.ctl_rt_C B ly3 S3 mem3`.  The run's region,
   a Theorem Labs lane's P1.p1_evt_shadow_R Sh Q (the 14 store targets and the callee's destination [Q, Q + 187)), lies in the own
   frame's shadow window [Sh, Sh + 512), cut_shadow's disjunct (F); the run's post keeps every region present and
   writable at entry, which gives the exit both cut_shadow and img_shadow and FRAC's 392 frame-shadow bytes.

   THE PROOF (glue-pattern.md section 3)
   G1  unfold the entry cut C_A81ac8 (ACtlCutP.v:1730-1746).
   G2  numeric facts from VISIBLE state: FRAC's spill base A and s3 = Sfr fr; the frame bounds (frames_bounds, the
       frame law, layout_le's ly_F, in_app) give the shadow window [Sh, Sh + 392) in the ASan shadow and apart
       from the stack, the runtime cells and the frame; the stack geometry from the journal's astk_ok.
   G3  cfg_at_MS, then the walk moved to the run's canonical register map (YA0nR.SRr_xregs_eqv).
   G4  p1_70_ro_F_on at RNG := ProgBridge.RNG_W (w_H W3); its footprint premises from visibility (the frame-shadow
       window, KitMem K6; the spill, VisWin win_vis; the image); lifted by YA0nR.SRr_fsteps.
   G5  the exit cut C_A81b10 (ACtlCutP.v:1750-1765) at the run's end map R and memory m':
         journal   a Theorem Labs lane's ajournal_of_fsteps (write set [Sh, Sh + 328): the class-6 frame's shadow, awr_byte's
                   frame case);
         frames, frame law, k bound   unchanged (own6, kmax 14 on both cuts);
         body      registers through the run's post; every application byte unchanged (the write set is shadow);
                   addressable ranges whose shadow avoids [Sh, Sh + 328) kept (KitMem K5);
         ctl_rt_C  AsanRTFacts.asan_cells_kept; cut_shadow and img_shadow through the run's keep conjunct; the
                   run's ro_agree.

   CITED BY NAME: a Theorem Labs lane's PROVED A.ProgWorld.ajournal_of_fsteps (ProgWorld.v (at head lib/A/ProgWorld.v:1091; from a working branch 7f07ac65e7b))
   and a Theorem Labs lane's PROVED A.ACtlG.KitMem.kitmem_rng_frame_sh / kitmem_addressable_mrd / kitmem_mrd_munch
   (a working branch 4a56e997c0f, merged).
   ALSO CITED: a Theorem Labs lane's PROVED, premise-free A.ProgWorld_Fs.ctl_frame_above_img (a live fake frame lies above
   the image; a Theorem Labs lane 07:4xZ: cited instead of the Section hypothesis kit_frame6_above_img).
   SECTION HYPOTHESES (exact text below)
   (KitMem K3 is a Theorem Labs lane's PROVED A.ACtlG.KitMem.kitmem_input_apart, a working branch dcdc870e8ff.)
   - LAWS       : the core's AR laws (ACtl.v:183).

   CLOSURE: every Require is qualified; the six doubled Reusable modules and lib/Lib, lib/Prog are named by
   absolute path (a Theorem Labs lane 03:5xZ, the porter 04:33Z).

   BUILD STATE: see the commit message (type-check only until the core builds as committed). *)

From Coq Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* the doubled modules by absolute name (porter 04:33Z) *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YA0nR Reusable.YG00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG01 Reusable.YG0f Reusable.YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0d Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YK04R.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.ACfn A.Img0 A.AsanRT A.AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlK A.ACtlCut A.ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.MemNorm A.MemNormF A.MemNormTr A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_set_shadow_c A.Prog.asan_set_shadow_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_set_shadowF A.Prog.memset.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_memsetF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.P1 A.Prog.Seg.P1F.
(* route (C): the narrowed runtime predicate, its transports and the cut's form *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT A.ACtlRtC.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem A.ProgWorld A.ProgWorld_Fs.
Import ListNotations.
Local Open Scope Z_scope.

(* The six doubled modules, by full path (a Theorem Labs lane 03:5xZ). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
(* lib/Lib's modules by FLAT aliases L<X>: a nested `Module Lib` wrapper's qualifier is a tail of both
   lib/Lib/<X>.v and lib/A/Bz/Lib/<X>.v (both in this file's closure), so the gate reads it as ambiguous. *)
Module LExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRegs6ss := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LRngBytes := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* ---------------------------------------------------------------------------------------------------------
   The composite run, ROUTE (C): a Theorem Labs lane's two `_on` stretches (written on a working branch e4cf770da9b) of P1.p1_evt (lib/A/Prog/Seg/P1F.v (an earlier version, blob 1dc297b725a, not in this delivery):
   p1_evt_pre_F_on :322 and p1_evt_post_F_on :387) joined
   by the PROVED footprint contract of __asan_set_shadow_f8, on the normalized memory, moved to the cut's memory
   (ro_agree).  Its region premise is a Theorem Labs lane's P1.p1_evt_shadow_R Sh Q (Seg/P1.v b2bcfe72edf (the blob this tree had at release c5e779efe8c), :224): the 14
   frame-shadow store targets of stretch 1 and the callee's destination [Q, Q + 187), which p1_rw_of_shadow_on reads
   and needs writable.  Its post carries every region present and writable at entry (the keep form of route (C))
   where the old one carried the universal A.AsanRT.shadow_rw, which route (C)'s cut no longer has.  The callee's
   stack window is empty (ASAN_SET_SHADOW_K = 0) and its written range [Q, Q + 187) lies in [Sh, Sh + 392). *)
Lemma p1_70_ro_F_on :
  forall (RNG : LExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Sh Q : Z),
    s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sh ->
    0 <= A < 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 328 ->
    (forall i, 0 <= i < 392 -> A.AsanRT.in_shadow (Sh + i)) ->
    LMem.bytes_at A.Img0.rsegs m (A + 152) (LMem.le8 (Z_to_bv 64 Q)) ->
    LFrame.disjoint_from [(Sh, Sh + 328)] (A + 152) 8 ->
    LFrame.disjoint_from [(Sh, Sh + 328)] A.AsanRT.RT_LO (A.AsanRT.RT_HI - A.AsanRT.RT_LO) ->
    A.AsanRT.asan_cells m -> A.ShadowRwOn.shadow_rw_on (A.Prog.Seg.P1.p1_evt_shadow_R Sh Q) m ->
    A.MemNorm.ro_agree A.Img0.rsegs m ->
    LExecF.rng RNG Sh 392 -> LExecF.rng RNG (A + 152) 8 ->
    LRngBytes.rng_bytes RNG ->
    LExecF.rng RNG A.Prog.ImgBounds.IMG_LO (A.Prog.ImgBounds.IMG_HI - A.Prog.ImgBounds.IMG_LO) ->
    LExecF.evtF A.Img0.rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = LMState.MS R F (Z_to_bv 64 0x81b10) fc None m' (CK11.seg_rom A.Img0.rsegs) /\
         CK11.getr R 2 = sp /\ CK11.getr R 3 = gp /\ CK11.getr R 4 = tp /\ CK11.getr R 8 = s0 /\
         CK11.getr R 9 = s1 /\ CK11.getr R 19 = s3 /\ CK11.getr R 26 = s10 /\ CK11.getr R 27 = s11 /\
         CK11.getr R 22 = s6 /\ CK11.getr R 25 = s9 /\
         LFrame.munch [(Sh, Sh + 328)] m m' /\ LFrame.wmono A.Img0.rsegs m m' /\
         A.MemNorm.ro_agree A.Img0.rsegs m' /\
         (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'))
      (LMState.MS (LFrame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
                                    s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x81ac8) fc None m (CK11.seg_rom A.Img0.rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Sh Q E1 E3 HA HQ1 HQ2 HSH HSP HSEP HDRT HAC HSW HRO RSH RSP RBY RIMG.
  pose proof (A.MemNorm.mem_rel_normalize A.Img0.rsegs m HRO) as REL.
  pose proof (A.AsanRTFacts.in_shadow_range _ (HSH 0 ltac:(lia))) as HS0. rewrite Z.add_0_r in HS0.
  pose proof (A.AsanRTFacts.in_shadow_range _ (HSH 391 ltac:(lia))) as HS391.
  pose proof (A.Prog.asan_set_shadowF.asan_set_shadow_f8_holds_F A.Prog.memset.memset_holds) as SET.
  unfold A.Prog.asan_set_shadow_cF.asan_set_shadow_f8_contract_F,
    A.Prog.asan_set_shadow_cF.asan_set_shadow_contract_F in SET.
  cbv zeta in SET.
  (* the run's region on the normalized memory (normalize keeps every shadow byte) *)
  pose proof (A.ShadowRwOnT.shadow_rw_on_normalize _ m HRO HSW) as HSWn.
  eapply LExecF.evtF_mono.
  - eapply (A.MemNormF.evtF_normalize_ro RNG _ _ F _ fc None m (CK11.seg_rom A.Img0.rsegs) HRO).
    eapply LExecF.evtF_cut.
    { (* stretch 1 on the normalized memory: 0x81ac8 -> the callee entry *)
      exact (A.Prog.Seg.P1F.p1_evt_pre_F_on RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
               s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (A.MemNorm.normalize A.Img0.rsegs m) A Sh Q E1 E3 HA HQ1 HQ2 HSH
               (A.MemNorm.bytes_at_normalize A.Img0.rsegs m _ _ HRO HSP) HSEP HDRT
               (A.MemNormTr.asan_cells_normalize m HRO HAC)
               (A.ShadowRwOn.shadow_rw_on_mono (A.Prog.Seg.P1.p1_evt_shadow_R Sh Q) _ _
                  (fun a Ha => match Ha with or_introl H => or_introl H | or_intror H => or_intror (or_introl H) end)
                  HSWn)
               (A.MemNorm.mem_inv_normalize A.Img0.rsegs m) RSH RSP). }
    intros ms1 (ra' & s2' & a0' & a1' & mc & -> & Era & Ea0 & Ea1 & HJ).
    pose proof HJ as (MUc & WMc & KPc & HMIc).
    assert (HQi : forall i, 0 <= i < Z.of_nat (Z.to_nat 187) -> A.AsanRT.in_shadow (Q + i))
      by (intros i Hi; replace (Q + i) with (Sh + (Q - Sh + i)) by lia; apply HSH; lia).
    (* the callee's destination, present and writable after stretch 1 (its keep conjunct) *)
    assert (HSWq : A.ShadowRwOn.shadow_rw_on (A.Prog.Seg.P1.p1_rw_of_shadow_shadow_R Q (Z.to_nat 187)) mc).
    { apply KPc. apply (A.ShadowRwOn.shadow_rw_on_mono (A.Prog.Seg.P1.p1_evt_shadow_R Sh Q)); [|exact HSWn].
      intros x Hx. unfold A.Prog.Seg.P1.p1_evt_shadow_R. right; right. exact Hx. }
    destruct (A.Prog.Seg.P1.p1_rw_of_shadow_on mc Q (Z.to_nat 187) HSWq HQi ltac:(lia) ltac:(lia))
      as (junk & RWj).
    eapply LExecF.evtF_cut.
    { (* the callee, by its proved footprint contract *)
      eapply SET with (RNG := RNG) (junk := junk).
      - rewrite Ea0, Ea1. intros i Hi. replace (Q + i) with (Sh + (Q - Sh + i)) by lia. apply HSH. lia.
      - rewrite Ea0, Ea1. exact RWj.
      - exact (A.AsanRTFacts.asan_cells_kept [(Sh, Sh + 328)] _ mc (A.MemNormTr.asan_cells_normalize m HRO HAC)
                 MUc HDRT).
      - exact HMIc.
      - exact RBY.
      - exact RIMG.
      - unfold A.Prog.asan_set_shadow_cF.ASAN_SET_SHADOW_K. rewrite Z.sub_0_r.
        apply A.Prog.asan_memsetF.rng_nil; [exact RBY|].
        pose proof (bv_unsigned_in_range _ sp) as Hsp. unfold bv_modulus in Hsp. lia.
      - rewrite Ea0, Ea1. exact (LExecF.rng_sub RNG Sh 392 Q 187 RSH ltac:(lia) ltac:(lia)). }
    intros ms2 (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' &
                E & MU & WM & MI' & RW).
    subst ms2.
    rewrite Ea0, Ea1 in MU, RW.
    replace (LMState.ret_pc ra') with (Z_to_bv 64 0x81b10)
      by (rewrite Era; symmetry; apply LMState.ret_pc_even; [lia | reflexivity]).
    (* stretch 2: the return pc, no step *)
    exact (A.Prog.Seg.P1F.p1_evt_post_F_on RNG ra' sp gp tp u0 u1 u2 s0 s1 a0' ua1 ua2 ua3 ua4 ua5 ua6 ua7 s2' s3
             s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc (A.MemNorm.normalize A.Img0.rsegs m) mc m' Sh Q _
             HQ1 HQ2 MUc WMc KPc HMIc MU WM MI' RW).
  - (* back to the cut's memory: the post's memory facts through mem_rel *)
    intros s (s0' & (R & m0' & -> & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P27 & P22 & P25 & MU0 & WM0 & MI0 & KP0)
              & MR & RS).
    destruct (A.MemNormTr.ms_rel_MS s _ _ _ _ _ _ _ MR) as (Es & Hmem).
    rewrite Es. exists R, (ms_mem s).
    split; [reflexivity|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P27|].
    split; [exact P22|]. split; [exact P25|].
    split; [exact (A.MemNorm.munch_rel A.Img0.rsegs _ m _ (ms_mem s) m0' REL Hmem RS MU0)|].
    split; [exact (A.MemNorm.wmono_rel A.Img0.rsegs m _ (ms_mem s) m0' REL Hmem RS WM0)|].
    split; [exact (A.MemNorm.ro_agree_same A.Img0.rsegs m (ms_mem s) HRO RS)|].
    (* every region present and writable at the cut's memory: across mem_rel to the normalized memory, through
       the run's keep conjunct, and back across mem_rel (A.ShadowRwOnT, both directions) *)
    intros P HP. apply (A.ShadowRwOnT.shadow_rw_on_of_rel P (ms_mem s) m0' Hmem).
    apply KP0. exact (A.ShadowRwOnT.shadow_rw_on_rel P m _ REL HP).
Qed.

Section GlueP1_70.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:217-218, :250-251), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81ac8 := (ACtlCutP.C_A81ac8 B).
Local Notation C_A81b10 := (ACtlCutP.C_A81b10 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.


(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_P1_70 : forall POST, CF POST C_A81b10 -> CF POST C_A81ac8.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut (ACtlCutP.v:1730-1746). *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81ac8] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & Hour & HCUR & HPRO & S144 & HA0 & (Q & SQ & HQ1 & HQ2) &
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
    rewrite (LMState.unsigned_lit Af) in E
      by (unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *; lia).
    rewrite (LMState.unsigned_lit A) in E by lia. exact E. }
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
  (* the frame's shadow window lies in cut_shadow's own-frame disjunct (F) (L3-recipe.md section 2, class (a)) *)
  assert (HFsh : forall a, Sh <= a < Sh + 512 -> A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a Ha. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite <- Efr, HFB6, ESh in *. unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF.
    change (4096 / 8) with 512. lia. }
  (* the run's region: the 14 store targets and the callee's destination [Q, Q + 187), all in the window *)
  assert (HSWr : A.ShadowRwOn.shadow_rw_on (A.Prog.Seg.P1.p1_evt_shadow_R Sh Q) mem3).
  { apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3)); [|exact Hcut].
    intros a Ha. apply HFsh.
    unfold A.Prog.Seg.P1.p1_evt_shadow_R, A.Prog.Seg.P1.p1_rw_of_shadow_shadow_R,
      A.Prog.Seg.P1.p1_sh_bytes_shadow_R in Ha.
    rewrite Z2Nat.id in Ha by lia. lia. }
  (* the [A + 152] spill is Q *)
  assert (HSP : LMem.bytes_at A.Img0.rsegs mem3 (A + 152) (LMem.le8 (Z_to_bv 64 Q))).
  { destruct SQ as (Ab & HAb & Hq).
    assert (EAb : Ab = A).
    { pose proof Hq as Hbd. unfold ACtlCutP.q64 in Hbd. apply LMem.bytes_at_bound in Hbd.
      rewrite LMem.length_le8 in Hbd.
      assert (E : Z_to_bv 64 Ab = Z_to_bv 64 A) by (unfold ACtlCut.rgv in HAb; rewrite <- HAb; exact R9).
      apply (f_equal (@bv_unsigned 64)) in E. rewrite (LMState.unsigned_lit A) in E by lia.
      rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
      destruct (Z_le_gt_dec 0 Ab) as [P|P].
      - rewrite Z.mod_small in E by lia. exact E.
      - exfalso. rewrite <- (Z.mod_add Ab 1 (2 ^ 64) ltac:(lia)) in E.
        rewrite Z.mod_small in E by lia. lia. }
    subst Ab. exact Hq. }
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81ac8) with 0x81ac8.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs6ss.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81ac8) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs6ss.xregs_eqv_sym _ _ (LRegs6ss.mkR_of_eqv regs3))].
  (* G4: the run's footprint premises at RNG_W (w_H W3), then the run. *)
  pose (H3 := Reusable.YA0n.w_H W3).
  pose (RNG := A.ProgBridge.RNG_W H3).
  assert (RSH : LExecF.rng RNG Sh 392).
  { apply (A.ACtlG.KitMem.kitmem_rng_frame_sh B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) Sh 392 HAR Hin6);
      rewrite <- Efr; change (A.AsanRT.shadow_addr fr) with Sh;
      [lia | rewrite HFB6; change (4096 / 8) with 512; lia]. }
  assert (RSP : LExecF.rng RNG (A + 152) 8).
  { exact (A.ACtlG.KitMem.kitmem_rng_win (SK := A.AE2k.tfib_sink_head) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (A + 152) 8 HJ ltac:(unfold A.ACfn.LLVMF_STK; lia) ltac:(lia)). }
  assert (RIMG : LExecF.rng RNG A.Prog.ImgBounds.IMG_LO (A.Prog.ImgBounds.IMG_HI - A.Prog.ImgBounds.IMG_LO))
    by exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3)).
  pose proof (p1_70_ro_F_on RNG
    (CK11.getr regs3 1) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4) (CK11.getr regs3 5)
    (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8) (CK11.getr regs3 9) (CK11.getr regs3 10)
    (CK11.getr regs3 11) (CK11.getr regs3 12) (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15)
    (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20)
    (CK11.getr regs3 21) (CK11.getr regs3 22) (CK11.getr regs3 23) (CK11.getr regs3 24) (CK11.getr regs3 25)
    (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30)
    (CK11.getr regs3 31) CK11.fp_regs CK11.fp_csr mem3 A Sh Q
    R9 ltac:(unfold ACtlCut.rgv in F19; exact F19) HA HQ1 HQ2 HSH HSP
    ltac:(cbn [LFrame.disjoint_from]; lia) ltac:(cbn [LFrame.disjoint_from];
      unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia)
    HAC HSWr HRO RSH RSP (A.ProgBridge.rng_bytes_RNG_W H3) RIMG) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  destruct HFS as (ms' & Hrun & HQ0).
  apply (Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 _ ms' md3 RNG (POST cx) Hrun
           (A.ProgBridge.fp_avoids_RNG_W H3)).
  intros md' Hsbm.
  (* G5: the run's end state is the exit cut's state at the run's own map R and memory m'. *)
  destruct HQ0 as (R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K27 & K22 & K25 & MU & WM & RO' & KP').
  subst ms'.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81b10) R m' md') (POST cx)).
  (* the registers the run keeps, on the core's getr *)
  assert (G2 : CK11.getr R 2 = CK11.getr regs3 2) by exact K2.
  assert (G3 : CK11.getr R 3 = CK11.getr regs3 3) by exact K3.
  assert (G4 : CK11.getr R 4 = CK11.getr regs3 4) by exact K4.
  assert (G8 : CK11.getr R 8 = CK11.getr regs3 8) by exact K8.
  assert (G9 : CK11.getr R 9 = CK11.getr regs3 9) by exact K9.
  assert (G19 : CK11.getr R 19 = CK11.getr regs3 19) by exact K19.
  assert (G26 : CK11.getr R 26 = CK11.getr regs3 26) by exact K26.
  assert (G27 : CK11.getr R 27 = CK11.getr regs3 27) by exact K27.
  assert (G22 : CK11.getr R 22 = CK11.getr regs3 22) by exact K22.
  assert (G25 : CK11.getr R 25 = CK11.getr regs3 25) by exact K25.
  assert (RA : CK11.getr R 9 = Z_to_bv 64 A) by (transitivity (CK11.getr regs3 9); [exact G9 | exact R9]).
  (* memory kept across the run: the write set [Sh, Sh + 328) is shadow, every application byte is kept *)
  assert (Tb : forall a bs, LMem.bytes_at segs mem3 a bs ->
                 (a + Z.of_nat (length bs) <= Sh \/ Sh + 328 <= a) -> LMem.bytes_at segs m' a bs).
  { intros a bs Hb Hd. apply (LFrame.bytes_at_transport segs [(Sh, Sh + 328)] mem3 m' a bs Hb MU).
    cbn [LFrame.disjoint_from]. lia. }
  assert (Tq : forall a v, ACtlCutP.q64 mem3 a v -> (a + 8 <= Sh \/ Sh + 328 <= a) -> ACtlCutP.q64 m' a v).
  { intros a v Hq H1. unfold ACtlCutP.q64 in *. apply Tb; [exact Hq|]. rewrite LMem.length_le8. lia. }
  assert (Trw : forall a cs, LStep.rw_cells segs mem3 a cs ->
                  (a + Z.of_nat (LCells.cells_size cs) <= Sh \/ Sh + 328 <= a) -> LStep.rw_cells segs m' a cs).
  { intros a cs Hc Hd. apply (LFrame.rw_cells_transport segs [(Sh, Sh + 328)] mem3 m' a cs Hc MU WM).
    cbn [LFrame.disjoint_from]. lia. }
  assert (Tad : forall p n, A.AsanRT.addressable mem3 p n ->
                  (p + n <= fr \/ fr + 2624 <= p) -> A.AsanRT.addressable m' p n).
  { intros p n Had Hpn. apply (A.ACtlG.KitMem.kitmem_addressable_mrd mem3 m' p n Had).
    intros i Hi. pose proof Had as (Hp0 & Hn0 & Hpe & _). unfold A.AsanRT.APPMEM_END in Hpe.
    pose proof (Z.div_mod (p + i) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p + i) 8 ltac:(lia)).
    apply (A.ACtlG.KitMem.kitmem_mrd_munch [(Sh, Sh + 328)] mem3 m' _ MU).
    - unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. lia.
    - cbn [LFrame.outside]. split; [|exact I].
      unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K. rewrite ESh. lia. }
  assert (Tsp : forall off v, 0 <= off <= 312 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R m' off v).
  { intros off v Hoff (Ab & HAb & Hq). exists A. split; [exact RA|].
    assert (EAb : Ab = A).
    { pose proof Hq as Hbd. unfold ACtlCutP.q64 in Hbd. apply LMem.bytes_at_bound in Hbd.
      rewrite LMem.length_le8 in Hbd.
      assert (E : Z_to_bv 64 Ab = Z_to_bv 64 A) by (unfold ACtlCut.rgv in HAb; rewrite <- HAb; exact R9).
      apply (f_equal (@bv_unsigned 64)) in E. rewrite (LMState.unsigned_lit A) in E by lia.
      rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
      destruct (Z_le_gt_dec 0 Ab) as [P|P].
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
  apply (HX cx [] fr k ly3 S3 W3 R m' md' HB).
  - (* journal: a Theorem Labs lane's ajournal_of_fsteps; the write set is the class-6 frame's shadow *)
    lazymatch type of Hrun with
    | Reusable.YK04R.fsteps _ _ ?s0 _ =>
        refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ s0 _ _ _ _ RNG
                  [(Sh, Sh + 328)] HJ Hrun
                  (A.ProgBridge.fp_avoids_RNG_W H3) MU Hsbm _)
    end.
    intros a Ha Hw. cbn [LFrame.outside] in Hw.
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
  - (* the exit body, C_A81b10 (ACtlCutP.v:1750-1765) *)
    cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_A81b10].
    split; [exact HP|].
    split.
    { (* FRAC: its registers through the run's post, its memory application bytes or the frame-shadow tail *)
      pose proof (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC G2 G3 G4 G8 G9 G19 G26) as HF1.
      destruct HF1 as (Af & spf2 & F1 & F2' & F3 & F4 & F5 & F6 & F7 & F8 & F9' & F10 & F11 & F12 & F13 & F14 &
        F15 & F16' & F17 & F18 & F19' & F20 & F21 & F22 & (sh & F23 & F23l) & F24).
      assert (EA' : Af = A).
      { assert (E : Z_to_bv 64 Af = Z_to_bv 64 A)
          by (unfold ACtlCut.rgv in F6; rewrite <- F6; exact RA).
        apply (f_equal (@bv_unsigned 64)) in E.
        rewrite (LMState.unsigned_lit Af) in E
          by (unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *; lia).
        rewrite (LMState.unsigned_lit A) in E by lia. exact E. }
      subst Af.
      exists A, spf2.
      do 17 (split; [assumption|]).
      split; [exact (Tq _ _ F18 ltac:(lia))|].
      split; [exact (Tq _ _ F19' ltac:(lia))|].
      split; [exact (Tq _ _ F20 ltac:(lia))|].
      split; [exact (Tq _ _ F21 ltac:(lia))|].
      split; [exact (Tq _ _ F22 ltac:(lia))|].
      split.
      - (* the 392 frame-shadow bytes: present after the run, which keeps every region present and writable at
           entry, here the frame's own window from ctl_rt_C's (F) disjunct (a Theorem Labs lane's P1.p1_sh_bytes_on) *)
        unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES.
        change (Z.to_nat (3136 / 8)) with 392%nat.
        assert (HSWsh : A.ShadowRwOn.shadow_rw_on (A.Prog.Seg.P1.p1_sh_bytes_shadow_R Sh 392) m').
        { apply KP'. apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3)); [|exact Hcut].
          intros a Ha. apply HFsh. unfold A.Prog.Seg.P1.p1_sh_bytes_shadow_R in Ha. cbn [Z.of_nat] in Ha. lia. }
        destruct (A.Prog.Seg.P1.p1_sh_bytes_on m' Sh 392 HSWsh ltac:(intros i Hi; apply HSH; lia) ltac:(lia)
                    ltac:(lia))
          as (sh' & Hsh' & Hl').
        exists sh'. split; [exact Hsh' | exact Hl'].
      - (* the saved registers; and, once FRAC gains the announced fake-frame trailer word
           q64 m (fr + 4088) (flag_addr ..) as its last conjunct (two Theorem Labs lanes 05:0xZ), that word too:
           an application byte of the frame, apart from the shadow window *)
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
    exists A, idb, junk.
    split; [exact RA|].
    split; [unfold ACtlCut.rgv in *; transitivity (CK11.getr regs3 27); [exact G27 | exact R27]|].
    split; [exact HA|].
    split; [apply Trw; [exact RW192|]; cbn [LCells.cells_size LCells.csize]; lia|].
    split; [apply Trw; [exact RWidb|]; cbn [LCells.cells_size LCells.csize]; lia|].
    split; [apply Trw; [exact RWjunk|]; cbn [LCells.cells_size LCells.csize]; lia|].
    split; [exact (Tq _ _ Q280 ltac:(lia))|].
    split; [exact (Tq _ _ Q240 ltac:(lia))|].
    exists jy, junk2.
    split; [apply Trw; [exact RWjy|]; cbn [LCells.cells_size LCells.csize]; lia|].
    apply Trw; [exact RWj2|]; cbn [LCells.cells_size LCells.csize]; lia.
  - (* ctl_rt_C m': the runtime cells are apart from the shadow window; both shadow regions of the entry cut are
       present and writable after the run (its keep conjunct); the run keeps ro_agree *)
    split; [exact (A.AsanRTFacts.asan_cells_kept [(Sh, Sh + 328)] mem3 m' HAC MU
                     ltac:(cbn [LFrame.disjoint_from]; unfold A.AsanRT.RT_LO, A.AsanRT.RT_HI; lia))|].
    split; [exact (KP' _ Hcut)|].
    split; [exact (KP' _ Himg)|].
    exact RO'.
Qed.

End GlueP1_70.

Print Assumptions p1_70_ro_F_on.
Print Assumptions glue_seg_P1_70.
