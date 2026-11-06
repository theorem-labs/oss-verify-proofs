(* lib/A/ACtlG/F28b.v -- GLUE for stage seg_F28b of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput
   (lib/A/ACtl.v:831).  Written by a Theorem Labs lane on the pattern of the pilot lib/A/ACtlG/A5.v
   (brief glue-pattern.md (a working note, not in this delivery)); single writer.
   rule 24: no function proved.  proves no function (kind: segment lemma).

   WHAT IT PROVES
     glue_seg_F28b : forall POST (j : nat),
       CF POST (ix_cut C_A82750_at [Z.of_nat j]) -> CF POST (ix_cut C_A826d4_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section
   hypothesis seg_F28b.  Segment F28b is 0x826d4 -> 0x82750 (Seg/F28b.v:1-12): the check_ports post-loop checks.
   The run reads the three ports words at fr + 128 / + 132 / + 136, the spill cells [A + 120] / [A + 176], the
   byte first at fr + 160, blk[7] at phi + 25 and its shadow byte, takes none of the branches to 0x82bf4, and
   WRITES NO MEMORY.

   THE PROOF (glue-pattern.md section 3)
   G1  unfold the entry cut: ix_cut's index equation, C_A826d4_at's FRAC and b7_body (ACtlCutP.v:2690-2702,
       :1065-1073) and B7K (ACtlCutP.v:943-952).
   G2  the run's premises.  Registers from the body's rgv conjuncts; the ports words, the byte first, the two
       spill cells, blk[7] and its shadow byte from the body's bytes facts, through Seg/F28b.v's own read lemmas
       (f28b_rd4 / rd8 / rdb / f28b_spill / f28b_blk7 / f28b_shadow, all outside its Section, no frame-route
       premise).  The EIGHT footprint ranges by A.ProgBridge.rng_of_visible from a range_visible fact each, whose
       bounds are the SIX f28b_run_of_F_bounded bounds (tsv rows 322-327) plus the two phi ranges:
         fr + 128 (4), fr + 132 (4), fr + 136 (4), fr + 160 (1)   the OWNED class-6 frame [fr, fr + 4096): the
             frame law fr = frame_addr (c_ly cx) 6 (c_fpos cx), layout_le's ly_F, the journal's AR frame law
             (AR_frames_law: every byte present and visible) and frames_bounds (4096 <= fr); the upper bound from
            FRAC (fr + FRAME_BYTES <= A <= c_sp cx <= APPMEM_END; batch 4 B5.4: the top is non-strict);
         A + 120 (8), A + 176 (8)   the stack window [c_sp cx - LLVMF_STK, c_sp cx) of the journal (every byte
            present): FRAC's c_sp cx - 4096 < sp <= A and A + 416 <= c_sp cx <= APPMEM_END;
         phi + 25 (1)   the live block (phi, flen cx j) (the body's Permutation of the live list, AR_blocks_law);
         shadow_addr (phi + 25) (1)   the same block's shadow hull (AR_shadow_law: shadow_hull_vis).
   G3  cfg_at_MS, then the walk moved from the cut's map regs3 to the run's mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  lift: ProgBridge.fevt_of_evtF, tfibsegs_rsegs, YA0nR.SRr_fevt at RNG := ProgBridge.RNG_W (w_H W3)
       (fp_avoids by fp_avoids_RNG_W).  A read-only run: SRr_fevt suffices (glue-pattern.md G4).
   G5  the continuation at MS R .. 0x82750 .. mem3 (memory unchanged, f28b_K): the exit cut's ctl_from at the same
       cx, [Z.of_nat j], fr, k, ly3, S3, W3, mem3, the map R and the materialized model md':
         journal  ajournal_exec with the empty write set (A5's call);
         frames, frame law, k bound   unchanged (own6 and kmax 14 + 2 j + 1 on both cuts);
         body     the same phi; FRAC through its seven registers and, for its last conjunct (the fake-frame trailer
                  word q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx)), Batch3), through the memory, which
                  is the entry cut's mem3 (Kit.kit_frac_move); FLSI and LT through register 9 (spills);
                  LK / FLS from B7K, f28b_K's kept registers and s9 = fr + 64 (FLS's s6 = phi + 18 because
                  B7K's 50 <= flen gives t_big = true, as B7Cuts.b7_a826a4 does);
        ctl_rt_C unchanged (route (C), a working branch: the cut's A.ACtlRtC.ctl_rt_C B ly3 S3 mem3; same state, same memory).

   _F RUN (Required, not a hypothesis): A.Prog.Seg.F28bF.f28b_run_F (lib/A/Prog/Seg/F28bF.v blob 5a906a1e2cf,
   a Theorem Labs lane's re-run of Seg/F28b.v's f28b_run, on the glue base since 5dbd293c250), instantiated at its fx :=
   A.Reusable.YK11.mkFP over the Section's fx (glue-pattern.md section 6 (a working note, not in this delivery)).  f28b_run_of_F_bounded is NOT used: its
   twelve bound premises are discharged here at the use site, inside the range_visible facts of the eight ranges.

   SECTION HYPOTHESES (exact text below; source of each)
   - LAWS: the core's AR law record (YCbq Section a0 / YG0d Section j), as A5.v and ACtl.v:210 take it.
   That is the only one.  FROM THE SHARED KIT lib/A/ACtlG/Kit.v (Required qualified, never copied):
   Kit.kit_wx (SRr_fevt's image premise), Kit.kit_segs_low (ajournal_exec's), Kit.kit_frac_move (FRAC along the
   run's end map, which keeps registers 2 3 4 8 9 19 26, at the same memory: FRAC's trailer word reads memory only).
   Proved here, Qed (no frame-route premise): f28b_vis_of_aview (a byte the view reads is visible: w_Hoff).

   CLOSURE: every project Require is qualified (no Import / Export of a project module); no statement names a
   frame-route identifier; the proof cites Seg/F28b.v's read lemmas (outside its Section F28b, no frame-route
   premise).  Twin modules (YI04 YI16 YK11 YK1b YM05 YO09, and YP09) only as lib.Reusable.X / A.Reusable.X. *)

From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YG00 YG0n YA0n YA0nR YG0f YG01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0d YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k ACfn Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACtlK ACtlCut ACtlCutP ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F28b F28bF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* A byte the core's view reads is visible: a hidden byte lies in no segment (w_Hoff), so the view reads None. *)
Lemma f28b_vis_of_aview : forall (W : lib.Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem a <> None ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a Hv.
  destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Eh; [|reflexivity].
  exfalso. apply Hv.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict.
  rewrite Eh. unfold lib.Reusable.YK11.seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (lib.Reusable.YA0n.w_Hoff W _ Eh). reflexivity.
Qed.

Section GlueF28b.

(* ACtl.v's Section shape (ACtl.v:183-187), restricted to what this stage uses. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:257, :261-262, :343-344), the same constants: ACtl.v writes the partial paths
   ACtlCut.X / ACtlCutP.X, this file the A.-qualified ones. *)
Local Notation ix_cut := A.ACtlCut.ix_cut.
Local Notation CF POST X :=
  (A.ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A826d4_at := (A.ACtlCutP.C_A826d4_at B).
Local Notation C_A82750_at := (A.ACtlCutP.C_A82750_at B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:210). *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage: its statement is ACtl.v:692's seg_F28b byte for byte, on one line as there. *)
Lemma glue_seg_F28b : forall POST (j : nat), CF POST (ix_cut C_A82750_at [Z.of_nat j]) -> CF POST (ix_cut C_A826d4_at [Z.of_nat j]).
Proof.
  intros POST j HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [j] (ix_cut, ACtlCut.v:234-236; C_A826d4_at, ACtlCutP.v:2690-2702). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCutP.C_A826d4_at A.ACtlCutP.ixn A.ACtlCutP.b7_body nth]
    in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HFRAC & phi & Hperm & Hcn & Hj & HHB & HFLSI & HK & Hrp & Hunk0 & H20 & H7 & HPO & HFI &
    H12 & H11 & H13 & H17).
  pose proof HK as ((Hj' & H21 & HOUR) & H23 & H22 & Hphi0 & Hphi50 & Hfl & Hblk & H280 & H24 & H18 & H152 &
    Hg & Hph & Hlen & HLT & (S136 & S120 & S176)).
  (* each fact used below, read by its statement *)
  assert (Hphi0' : 0 < phi) by exact Hphi0.
  assert (Hphi50' : phi + 50 <= 2 ^ 64) by exact Hphi50.
  assert (Hfl' : 50 <= A.ACtlCutP.flen cx j) by exact Hfl.
  pose proof HFRAC as (Asp & sp & _ & _ & _ & _ & _ & R9 & _ & _ & R26 & _ & _ & _ & HspA & HfrA & HA416 &
    HSsp & HSapp & _).
  assert (R9' : A.ACtlCut.rgv regs3 9 Asp) by exact R9.
  assert (HspA' : sp <= Asp) by exact HspA.
  assert (HfrA' : fr + A.ACtlCutP.FRAME_BYTES <= Asp) by exact HfrA.
  assert (HA416' : Asp + 416 <= A.ACtlCut.c_sp cx) by exact HA416.
  assert (HSsp' : A.ACtlCut.c_sp cx - 4096 < sp) by exact HSsp.
  assert (HSapp' : A.ACtlCut.c_sp cx <= A.AsanRT.APPMEM_END) by exact HSapp.
  unfold A.ACtlCutP.FRAME_BYTES in HfrA'. unfold A.AsanRT.APPMEM_END in HSapp'.
  (* G2a: the journal's facts: its AR, layout_le's ly_F, the stack window *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  assert (HAR' : lib.Reusable.YG0n.AR segs B ly3 S3 W3 mem3 md3) by exact HAR.
  assert (Hpres' : forall a, A.ACtlCut.c_sp cx - A.ACfn.LLVMF_STK <= a < A.ACtlCut.c_sp cx ->
            lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W3) mem3 a) by exact Hpres.
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (EF' : lib.Reusable.YG0f.ly_F ly3 = lib.Reusable.YG0f.ly_F (A.ACtlCut.c_ly cx)) by exact EF.
  (* G2b: the owned frame [fr, fr + 4096): bounds and visibility *)
  assert (Hin6 : In (6, A.ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR' Hin6)
    as (Hf4096 & _ & _).
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr (A.ACtlCut.c_ly cx) 6 (A.ACtlCut.c_fpos cx))
    by (apply HL; left; reflexivity).
  assert (Efr3 : fr = lib.Reusable.YG0f.frame_addr ly3 6 (A.ACtlCut.c_fpos cx)).
  { rewrite Efr. unfold lib.Reusable.YG0f.frame_addr. rewrite <- EF'. reflexivity. }
  assert (Hfr4096 : 4096 <= fr) by (rewrite Efr3; exact Hf4096).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (A.ACtlCut.c_fpos cx) HAR' Hin6)
    as (_ & _ & Hfrv & _).
  assert (HVfr : forall a, fr <= a < fr + 4096 -> lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. rewrite Efr3 in Ha.
    assert (E4096 : lib.Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
    destruct (Hfrv a ltac:(rewrite E4096; lia)) as ((Hh & _) & _). exact Hh. }
  (* G2c: the stack window holds the spill area [A, A + 416) *)
  assert (HVsp : forall a, Asp <= a < Asp + 416 -> lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (Hpres' a ltac:(unfold A.ACfn.LLVMF_STK; lia)) as (Hh & _). exact Hh. }
  (* G2d: the live block (phi, flen cx j): blk[7] and its shadow byte *)
  assert (Hinphi : In (phi, A.ACtlCutP.flen cx j) (lib.Reusable.YG0d.ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
  assert (Ereq : lib.Reusable.YG00.req_size (A.ACtlCutP.flen cx j) = A.ACtlCutP.flen cx j).
  { unfold lib.Reusable.YG00.req_size. destruct (Z.eqb_spec (A.ACtlCutP.flen cx j) 0); lia. }
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (A.ACtlCutP.flen cx j) HAR' Hinphi)
    as (_ & _ & _ & _ & Hblv & _).
  destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 phi (A.ACtlCutP.flen cx j) HAR' Hinphi)
    as (_ & Hhull).
  assert (HV25 : lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 (phi + 25)) = false).
  { destruct (Hblv (phi + 25) ltac:(rewrite Ereq; lia)) as ((Hh & _) & _). exact Hh. }
  assert (Esh : Z.shiftr (phi + 25) 3 + A.AsanRT.ASAN_K = lib.Reusable.YG0f.shadow_addr (phi + 25)).
  { rewrite Z.shiftr_div_pow2 by lia. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF,
      A.AsanRT.ASAN_K. change (2 ^ 3) with 8. lia. }
  assert (HVsh : lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 (lib.Reusable.YG0f.shadow_addr (phi + 25))) = false).
  { apply (f28b_vis_of_aview W3 mem3). unfold lib.Reusable.YG0d.shadow_hull_vis in Hhull. apply Hhull.
    rewrite Ereq.
    pose proof (lib.Reusable.YCbq.shadow_mono phi (phi + 25) ltac:(lia)) as M1.
    pose proof (lib.Reusable.YCbq.shadow_mono (phi + 25) (phi + A.ACtlCutP.flen cx j - 1) ltac:(lia)) as M2.
    set (s0 := lib.Reusable.YG0f.shadow_addr phi) in *.
    set (s2 := lib.Reusable.YG0f.shadow_addr (phi + A.ACtlCutP.flen cx j - 1)) in *.
    pose proof (Z.mul_div_le s0 8 ltac:(lia)) as D0.
    pose proof (Z.div_mod s2 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound s2 8 ltac:(lia)) as D2'.
    lia. }
  (* G2e: the eight footprint ranges, each with its bounds (f28b_run_of_F_bounded's six, F28bF.v:184-190) *)
  assert (RV128 : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (fr + 128) 4).
  { split; [lia|]. split; [lia|]. intros a Ha. apply HVfr. lia. }
  assert (RV132 : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (fr + 132) 4).
  { split; [lia|]. split; [lia|]. intros a Ha. apply HVfr. lia. }
  assert (RV136 : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (fr + 136) 4).
  { split; [lia|]. split; [lia|]. intros a Ha. apply HVfr. lia. }
  assert (RV160 : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (fr + 160) 1).
  { split; [lia|]. split; [lia|]. intros a Ha. apply HVfr. lia. }
  assert (RV120 : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (Asp + 120) 8).
  { split; [lia|]. split; [lia|]. intros a Ha. apply HVsp. lia. }
  assert (RV176 : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (Asp + 176) 8).
  { split; [lia|]. split; [lia|]. intros a Ha. apply HVsp. lia. }
  assert (RV25 : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) (phi + 25) 1).
  { split; [lia|]. split; [lia|]. intros a Ha. replace a with (phi + 25) by lia. exact HV25. }
  assert (RVsh : A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3)
                   (Z.shiftr (phi + 25) 3 + A.AsanRT.ASAN_K) 1).
  { rewrite Esh. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    pose proof (Z.div_pos (phi + 25) 8 ltac:(lia) ltac:(lia)) as D0.
    pose proof (Z.div_le_upper_bound (phi + 25) 8 (phi + 25) ltac:(lia) ltac:(lia)) as D1.
    split; [lia|]. split; [lia|]. intros a Ha.
    replace a with (lib.Reusable.YG0f.shadow_addr (phi + 25))
      by (unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF; lia).
    exact HVsh. }
  (* G2f: the run's memory premises from the body (Seg/F28b.v:479-511, the source's own instantiation) *)
  pose proof (proj2 (A.Prog.Seg.F28b.b7_unk_rp0 (A.ACtlCut.c_in cx) j Hrp)) as Ed.
  unfold A.Prog.SlotModel.t_unk in H20. rewrite Ed in H20. cbv iota in H20.
  unfold A.ACtlCutP.FIRSTb, A.Prog.SlotModel.t_first in HFI. rewrite Ed in HFI. cbv iota in HFI.
  pose proof (proj1 (proj1 HPO Hrp)) as P0.
  pose proof (proj1 (proj2 (proj1 HPO Hrp))) as P4.
  pose proof (proj2 (proj2 (proj1 HPO Hrp))) as P8.
  pose proof (A.Prog.Seg.F28b.f28b_spill regs3 mem3 Asp 120 _ R9' ltac:(lia) ltac:(lia) ltac:(lia) S120)
    as Q120.
  pose proof (A.Prog.Seg.F28b.f28b_spill regs3 mem3 Asp 176 _ R9' ltac:(lia) ltac:(lia) ltac:(lia) S176)
    as Q176.
  assert (Had25 : A.AsanRT.addressable mem3 (phi + 25) 1).
  { destruct HHB as (_ & HAd).
    apply (A.AsanRTFacts.addressable_sub mem3 phi (A.ACtlK.a_size (A.ACtlCutP.flen cx j)) 25 1 HAd);
      unfold A.ACtlK.a_size; lia. }
  destruct (A.Prog.Seg.F28b.f28b_shadow mem3 (phi + 25) Had25) as (b25 & HRsh & OK25 & BD25).
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (A.ACtlCut.cut_pc (ix_cut C_A826d4_at [Z.of_nat j])) with 0x826d4.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3
           lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x826d4) lib.Reusable.YK11.fp_csr None mem3
           (lib.Reusable.YK11.seg_rom segs) md3 (POST cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  (* G4: the lift, at the footprint of every visible range *)
  pose proof (@A.Prog.Seg.F28bF.f28b_run_F
                (A.Reusable.YK11.mkFP lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr)
                (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) regs3 mem3 fr Asp phi _ _ _ _ _ _
                (nth 7 (A.Prog.SlotModel.t_pbs (A.ACtlCut.c_in cx) j) (Z_to_bv 8 0)) b25
                H7 H20 R9' H13 H12 H11 H17 H22 R26
                (A.Prog.Seg.F28b.b7_n_in_range _) (A.Prog.Seg.F28b.b7_n_out_range _)
                (A.Prog.Seg.F28b.b7_emp_range _) (A.Prog.Seg.F28b.b7_nu_range _)
                (A.Prog.Seg.F28b.b7_sum12 _) (A.Prog.Seg.F28b.b7_pf_range _)
                Hphi0' Hphi50' (A.Prog.Seg.F28b.b7_hb _)
                (A.Prog.Seg.F28b.f28b_rd4 mem3 _ _ P0) (A.Prog.Seg.F28b.f28b_rd4 mem3 _ _ P4)
                (A.Prog.Seg.F28b.f28b_rd4 mem3 _ _ P8)
                (A.Prog.Seg.F28b.f28b_rd8 mem3 _ _ Q120) (A.Prog.Seg.F28b.f28b_rdb mem3 _ _ HFI)
                (A.Prog.Seg.F28b.f28b_rd8 mem3 _ _ Q176)
                HRsh OK25 BD25 (A.Prog.Seg.F28b.f28b_blk7 mem3 phi (A.ACtlCut.c_in cx) j Hblk)
                (A.ProgBridge.rng_of_visible _ _ _ RV128) (A.ProgBridge.rng_of_visible _ _ _ RV132)
                (A.ProgBridge.rng_of_visible _ _ _ RV136) (A.ProgBridge.rng_of_visible _ _ _ RV120)
                (A.ProgBridge.rng_of_visible _ _ _ RV160) (A.ProgBridge.rng_of_visible _ _ _ RV176)
                (A.ProgBridge.rng_of_visible _ _ _ RVsh) (A.ProgBridge.rng_of_visible _ _ _ RV25))
    as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  apply (lib.Reusable.YA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3
           (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) _
           (POST cx) HFS).
  { exact (A.ProgBridge.fp_avoids_RNG_W (lib.Reusable.YA0n.w_H W3)). }
  (* G5: the continuation at MS R .. 0x82750 .. mem3 (f28b_K, Seg/F28b.v:446-453) *)
  intros ms' md' HQ0 Hsbm.
  destruct HQ0 as (R & pc' & mem' & Ems & Hpc & Hmem & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 &
    K26 & K18 & K25).
  subst ms' pc' mem'.
  change (lib.Reusable.YA0n.SRr segs W3
            (lib.Reusable.YG0d.cfg_at segs (A.ACtlCut.cut_pc (ix_cut C_A82750_at [Z.of_nat j])) R mem3 md')
            (POST cx)).
  (* the end map's kept registers, in the core's getr *)
  assert (K9c : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by exact K9.
  assert (Hsp : forall off v, A.ACtlCutP.spill regs3 mem3 off v -> A.ACtlCutP.spill R mem3 off v).
  { intros off v (Ab & HAb & Hq). exists Ab. split; [exact (eq_trans K9c HAb) | exact Hq]. }
  assert (HFLSI_R : A.ACtlCutP.FLSI cx j fr R mem3).
  { pose proof HFLSI as X.
    unfold A.ACtlCutP.FLSI, A.ACtlCutP.FLSH, A.ACtlCutP.PRO, A.ACtlCutP.FLC, A.ACtlCutP.spill,
      A.ACtlCut.rgv in X |- *.
    first [rewrite K9c | rewrite K9]; exact X. }
  assert (HLT_R : A.ACtlCutP.LT cx fr j R mem3).
  { pose proof HLT as X.
    unfold A.ACtlCutP.LT, A.ACtlCutP.IFS, A.ACtlCutP.FSj, A.ACtlCutP.FSb, A.ACtlCutP.spill,
      A.ACtlCut.rgv in X |- *.
    first [rewrite K9c | rewrite K9]; exact X. }
  assert (Ebig : A.Prog.SlotModel.t_big (A.ACtlCut.c_in cx) j = true).
  { unfold A.Prog.SlotModel.t_big. apply Z.leb_le. exact Hfl'. }
  apply (HX cx [Z.of_nat j] fr k ly3 S3 W3 R mem3 md' HB).
  - (* journal: no byte written, the model materialized (ajournal_exec, YCbq.v:636-643, A5.v's call) *)
    eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: 14 + 2 j + 1 on both cuts *)
    exact Hk.
  - (* the exit body, C_A82750_at (ACtlCutP.v:2706-2716), at the same turn j and the same block phi *)
    split; [reflexivity|].
    cbv beta iota zeta delta [A.ACtlCut.cut_body A.ACtlCutP.C_A82750_at A.ACtlCutP.ixn nth].
    rewrite Nat2Z.id.
    exists phi.
    split; [exact Hperm|].
    split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
    split; [exact Hcn|]. split; [exact Hj|]. split; [exact HHB|].
    split; [exact HFLSI_R|].
    split.
    { (* LK *)
      split; [exact Hj'|]. split; [exact (eq_trans K21 H21) | exact HOUR]. }
    split.
    { (* FLS (B7Cuts.b7_a826a4's shape) *)
      split; [exact HFLSI_R|].
      split; [exact (eq_trans K18 H18)|].
      split; [rewrite Ebig; exact (eq_trans K22 H22)|].
      split; [exact (eq_trans K23 H23)|].
      split; [exact (eq_trans K24 H24)|].
      split; [exact K25|].
      split; [intros _; exact (conj Hphi0' (conj Hphi50' (conj Hg (conj Hph Hlen))))|].
      split; [exact (Hsp _ _ H152) | exact (Hsp _ _ H280)]. }
    exact HLT_R.
  - (* ctl_rt_C (route (C)): the state and the memory are the entry cut's *)
    exact Hrt.
Qed.

End GlueF28b.
