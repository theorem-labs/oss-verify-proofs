(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names changed; 1977 of its 2075 lines of code are new or changed and 2368 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3b.v, with its module paths, module names and numbers changed; 884 of its 966 lines of code are new or changed and 1993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/F13.v, with its module names changed; 426 of its 465 lines of code are new or changed and 927 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/ACtlG/R8.v, with its module paths and module names changed; 288 of its 337 lines of code are new or changed and 416 lines of the source are left out. *)
(* lib/A/ACtlG/P4.v -- GLUE for stage seg_P4 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v:719):
     glue_seg_P4 : forall POST, CF POST C_A81b90 -> CF POST C_A81b80
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's Section hypothesis
   seg_P4.  Written by a Theorem Labs lane's glue lane (piece W3a: P1, P1_70, P2, P4); single writer.  Route (C)
   re-fit (the cut's ctl_rt -> A.ACtlRtC.ctl_rt_C, the run -> its _on twin) by a Theorem Labs lane, slice P4.
   rule 24: no function proved (stage glue of a walk).

   THE SEGMENT (Seg/P4.v at U 6a74d5929d2; v1.9 0x81b80 -> 0x81b90): li a2,72 ; ld a0,192(s1) ; li a1,0 ;
   jal __asan_memset (0x524c4), return pc 0x81b90.  The callee clears the 72 bytes of the fragment record at
   D = fr + 2768 and uses its own stack window [sp - ASAN_MEMSET_K, sp) (ASAN_MEMSET_K = 2208).

   THE RUN LIFTED: P4F_on.p4_evt_ro_F_on (lib/A/Prog/Seg/P4F_on.v), the route (C) twin of a Theorem Labs lane's
   P4F.p4_evt_ro_F (lib/A/Prog/Seg/P4F.v (not in this delivery), unchanged), the footprint twin of P4.p4_evt_ro: the run on the memory
   the cut carries (MemNorm.ro_agree, not mem_inv).  Its shadow premise is a REGION, a Theorem Labs lane's
   P4.p4_evt_ro_shadow_R D (the memset's aligned shadow-word span of [D, D + 72)), not the universal shadow_rw.
   Its callee premise asan_memset_contract_F_on is DISCHARGED by a Theorem Labs lane's PROVED
   asan_memsetF_on.asan_memset_holds_F_on over memset.memset_holds (memset.v:4).  The split rule (a Theorem Labs lane
   04:01Z): __asan_memset has a proved _F, so the run is lifted straight, no split.

   THE PROOF (glue-pattern.md section 3)
   G1  unfold the entry cut C_A81b80 (ACtlCutP.v:1789-1820): 11 conjuncts and the memset window record (26); the
       cut's route (C) runtime conjunct A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 into asan_cells_at, the two shadow regions
       (cut_shadow B ly3 S3, img_shadow) and ro_agree_at.
   G2  numeric facts from VISIBLE state: FRAC's spill base and sp are the body's A and spv (one register each);
       the frame bounds (frames_bounds, the frame law, layout_le's ly_F); the stack geometry (the journal's
       astk_ok and layout_le's stack bounds); fr above the image (KitMem K1).
   G3  cfg_at_MS, then the walk moved to the run's canonical register map (YA0nR.SRr_xregs_eqv).
   G4  the run p4_evt_ro_F_on at RNG := ProgBridge.RNG_W (w_H W3); its eight footprint premises from visibility
       (VisWin win_vis / win_sh_vis, VisFrame frame_vis, ProgBridge img_vis_W / rng_bytes_RNG_W); its shadow
       premise by ShadowRwOn.shadow_rw_on_mono from the cut's cut_shadow region, through its (F) disjunct: the span
       of D = fr + 2768 lies in the owned class-6 frame's shadow [shadow_addr fr, shadow_addr fr + 4096 / 8);
       lifted by YA0nR.SRr_fsteps (the fsteps run is kept for the journal step).
   G5  the exit cut C_A81b90 (ACtlCutP.v:1824-1838) at the run's end map R and memory m':
         journal   a Theorem Labs lane's ajournal_of_fsteps (write set [D, D + 72) in the class-6 frame, [spv - 2208, spv) in the
                   LLVMF stack window: awr_byte's frame and stack cases);
         frames, frame law, k bound   unchanged (own6, kmax 14 on both cuts);
         body      registers through the run's post; memory conjuncts kept across `munch W mem3 m'` by
                   LFrame.bytes_at_transport / rw_cells_transport and AsanRTFacts.addressable_kept
                   (W is application memory, so no shadow byte changes: munch_meta); the new fragment record
                   z72 from the callee's post;
         ctl_rt_C  AsanRTFacts.asan_cells_kept (rt_disjoint W), ShadowRwOnT.shadow_rw_on_kept for each of the two
                   regions (the world ly3 S3 does not move; W is application memory: meta_kept), the run's ro_agree.

   CITED BY NAME: a Theorem Labs lane's PROVED A.ProgWorld.ajournal_of_fsteps (ProgWorld.v (at head lib/A/ProgWorld.v:1091; from a working branch 7f07ac65e7b))
   and a Theorem Labs lane's PROVED A.ACtlG.KitMem.kitmem_stk_of_present (a working branch 4a56e997c0f,
   merged).
   ALSO CITED: a Theorem Labs lane's PROVED, premise-free A.ProgWorld_Fs.ctl_frame_above_img (a live fake frame lies above
   the image; a Theorem Labs lane 07:4xZ: cited instead of the Section hypothesis kit_frame6_above_img).
   SECTION HYPOTHESES (exact text below)
   (KitMem K3 is a Theorem Labs lane's PROVED A.ACtlG.KitMem.kitmem_input_apart, a working branch dcdc870e8ff.)
   - LAWS       : the core's AR laws (ACtl.v:183).

   CLOSURE: every Require is qualified.  The six modules that exist both as the core's lib/Reusable/<X> and as
   ctrl's lib/A/Reusable/<X> (YI04 YI16 YK11 YK1b YM05 YO09) are named by FULL path (aliases CK11 / CM05 / CO09
   below), as a Theorem Labs lane ruled (03:5xZ).

   BUILD STATE: see the commit message (type-check only until the core builds as committed). *)

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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgBridge A.ProgWorldVisWin A.ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.MemNorm A.Prog.rng_asan A.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_memset_c A.Prog.asan_memset_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_memsetF_on A.Prog.memset.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.P4F_on.
(* route (C): the cut's ctl_rt_C and its regions; a Theorem Labs lane's region of the run and the definitions it unfolds to *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.P4 A.Prog.asan_memset_c_on A.Prog.sh_word_on.
(* lib/Lib and lib/Prog by absolute name: ctrl's lib/A trees carry modules of the same short names (A/Bz/Lib/Frame,
   Step, Mem ...), which a From-form Require or a partial reference can reach (measured: the partial
   reference to lib/Lib/Frame resolved to a twin whose rw_cells is not ACtlCutP's) *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit A.ACtlG.KitMem A.ProgWorld A.ProgWorld_Fs.
Import ListNotations.
Local Open Scope Z_scope.

(* The six doubled modules, by full path (a Theorem Labs lane 03:5xZ). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
(* lib/Lib's modules by FLAT aliases L<X>, lib/Prog's RcIdentModel as Prog.RcIdentModel: a nested `Lib.<X>` is a
   tail of both lib/Lib/<X>.v and lib/A/Bz/Lib/<X>.v (both in this file's closure), so the gate reads it as ambiguous. *)
Module LExecF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LMState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRegs6ss := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LStep := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCells := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LRngBytes := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Module Prog.
  Module RcIdentModel := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
End Prog.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* Two intervals: a range all of whose bytes are outside both is disjoint from both (the cut body states its
   kept ranges in the `outside` form, LFrame.bytes_at_transport takes the `disjoint_from` form). *)
Lemma p4_disj2_of_out : forall lo1 hi1 lo2 hi2 a n,
  0 < n -> lo1 < hi1 -> lo2 < hi2 ->
  (forall x, a <= x < a + n -> LFrame.outside [(lo1, hi1); (lo2, hi2)] x) ->
  LFrame.disjoint_from [(lo1, hi1); (lo2, hi2)] a n.
Proof.
  intros lo1 hi1 lo2 hi2 a n Hn H1 H2 H. cbn [LFrame.disjoint_from].
  split; [|split; [|exact I]].
  - destruct (Z_le_gt_dec (a + n) lo1) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec hi1 a) as [R|R]; [right; exact R|].
    exfalso. destruct (H (Z.max a lo1) ltac:(lia)) as (Hx & _). apply Hx. lia.
  - destruct (Z_le_gt_dec (a + n) lo2) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec hi2 a) as [R|R]; [right; exact R|].
    exfalso. destruct (H (Z.max a lo2) ltac:(lia)) as (_ & Hx & _). apply Hx. lia.
Qed.

(* The run's write set: the fragment record [D, D + 72) and __asan_memset's stack window [spv - 2208, spv)
   (ASAN_MEMSET_K = 2208, asan_memset_c.v). *)
Definition p4_W (D spv : Z) : list LFrame.ivl := [(D, D + 72); (spv - 2208, spv)].

Section GlueP4.

(* ACtl.v's Section shape (ACtl.v:170-174), restricted to what this stage uses. *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v:217-218, :253-254), verbatim. *)
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A81b80 := (ACtlCutP.C_A81b80 B).
Local Notation C_A81b90 := (ACtlCutP.C_A81b90 B).

(* ---------------------------------------------------------------------------------------------------------
   Section hypotheses (sources in the header). *)

(* The core's AR laws (YCbq.v:207, Section a0's hypothesis; ACtl.v:183). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* ---------------------------------------------------------------------------------------------------------
   The stage. *)
Lemma glue_seg_P4 : forall POST, CF POST C_A81b90 -> CF POST C_A81b80.
Proof.
  intros POST HX cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut (ACtlCutP.v:1789-1820). *)
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81b80] in Hbody.
  destruct Hbody as (HP & HFRAC & Hn & Hour & HCUR & HPRO & S144 & Had2691 & HadF & Had2688 & HID &
    (D & spv & A & junk & R2 & R9 & HA & HD & Hspv & HLD & RWD & HAD & HE & HA7 & HRT & HSEP &
     O1 & O2 & O3 & O4 & O5 & O6 & O7 & Hallapp & Hrtd & ED & Q280 & Q240 & (jy & junk2 & RWjy & RWj2) &
     Had2880)).
  destruct Hrt as (HAC & Hcut & Himg & HRO).
  (* G2: numeric facts from visible state. *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & ESL & ESH & _).
  destruct Hastk as (_ & _ & Hceil_lo & Hstk_lo & Hstk_hi & _).
  pose proof (@CM05.alloc_ceiling_value rc) as ((Hceil0 & _) & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  pose proof (A.ProgWorld_Fs.ctl_frame_above_img B ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6) as Hfimg.
  assert (Efr : fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) ltac:(left; reflexivity)).
    unfold Reusable.YG0f.frame_addr. rewrite EF. reflexivity. }
  assert (HFB6 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite <- Efr, HFB6 in Hfceil. rewrite <- Efr in Hfimg, Hf4096.
  unfold A.Prog.ImgBounds.IMG_HI in Hfimg.
  pose proof HFRAC as (Af & spf & F2 & F16 & FspZ & _ & _ & F9 & _ & _ & _ & Ffr32 & FA32 & FAc & FspA & FfrA &
    FA416 & Fc4096 & Fapp & _).
  assert (EA : Af = A).
  { assert (E : Z_to_bv 64 Af = Z_to_bv 64 A) by (unfold ACtlCut.rgv in F9; rewrite <- F9; exact R9).
    apply (f_equal (@bv_unsigned 64)) in E.
    rewrite (LMState.unsigned_lit Af) in E
      by (unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *; lia).
    rewrite (LMState.unsigned_lit A) in E by lia. exact E. }
  assert (Esp : spf = spv).
  { assert (E : Z_to_bv 64 spf = Z_to_bv 64 spv) by (rewrite <- F2; exact R2).
    apply (f_equal (@bv_unsigned 64)) in E.
    rewrite (LMState.unsigned_lit spf) in E
      by (unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *; lia).
    rewrite (LMState.unsigned_lit spv) in E by lia. exact E. }
  subst Af spf.
  unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in FfrA, Fapp.
  unfold A.ACfn.LLVMF_STK in Hpres, Hstk_lo.
  assert (HK : A.Prog.asan_memset_c.ASAN_MEMSET_K = 2208) by reflexivity.
  (* the stack window of the run and of the callee lies in the journal's LLVMF window, above the frame *)
  assert (Hgeo : CM05.alloc_ceiling + 32768 <= ACtlCut.c_sp cx) by lia.
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc C_A81b80) with 0x81b80.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (LRegs6ss.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x81b80) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRegs6ss.xregs_eqv_sym _ _ (LRegs6ss.mkR_of_eqv regs3))].
  (* G4: the run's premises at RNG_W (w_H W3), then the run. *)
  pose (H3 := Reusable.YA0n.w_H W3).
  pose (RNG := A.ProgBridge.RNG_W H3).
  assert (HSTK : LFrame.stk A.Img0.rsegs mem3 (spv - 2208) spv).
  { apply (A.ACtlG.KitMem.kitmem_stk_of_present H3); [lia | lia |]. intros a Ha. apply Hpres. lia. }
  assert (G192 : LExecF.rng RNG (A + 192) 8).
  { exact (A.ACtlG.KitMem.kitmem_rng_win (SK := A.AE2k.tfib_sink_head) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (A + 192) 8 HJ ltac:(unfold A.ACfn.LLVMF_STK; lia) ltac:(lia)). }
  assert (Gstk : LExecF.rng RNG (spv - 2208) 2208).
  { exact (A.ACtlG.KitMem.kitmem_rng_win (SK := A.AE2k.tfib_sink_head) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (spv - 2208) 2208 HJ ltac:(unfold A.ACfn.LLVMF_STK; lia) ltac:(lia)). }
  assert (Gimg : LExecF.rng RNG A.Prog.ImgBounds.IMG_LO (A.Prog.ImgBounds.IMG_HI - A.Prog.ImgBounds.IMG_LO))
    by exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3)).
  destruct (A.ProgWorldVisFrame.frame_vis B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) D 72 HAR Hin6
              ltac:(rewrite <- Efr; lia) ltac:(rewrite <- Efr, HFB6; lia)) as (VD & VshD).
  assert (Gd : LExecF.rng RNG D 72) by exact (A.ProgBridge.rng_of_visible _ _ _ VD).
  assert (Gshd : A.Prog.rng_asan.sh_word_rng RNG D 72).
  { destruct (VshD ltac:(lia)
                ltac:(rewrite <- Efr; pose proof (Z.div_mod D 64 ltac:(lia));
                      pose proof (Z.mod_pos_bound D 64 ltac:(lia)); lia)
                ltac:(rewrite <- Efr, HFB6; pose proof (Z.div_mod (D + 72 - 1) 64 ltac:(lia));
                      pose proof (Z.mod_pos_bound (D + 72 - 1) 64 ltac:(lia)); lia)) as [E0 | V].
    - left. exact E0.
    - right. exact (A.ProgBridge.rng_of_visible _ _ _ V). }
  assert (Gshs : A.Prog.rng_asan.sh_word_rng RNG (spv - 2208) 2208).
  { destruct (A.ProgWorldVisWin.win_sh_vis B LAWS ly3 S3 W3 mem3 md3 (spv - 2208) 2208 HAR
                ltac:(rewrite ESL; lia) ltac:(rewrite ESH; lia) ltac:(lia)) as [E0 | V].
    - left. exact E0.
    - right. exact (A.ProgBridge.rng_of_visible _ _ _ V). }
  (* the run's one shadow premise, the memset's shadow-word span of [D, D + 72) (a Theorem Labs lane's P4.p4_evt_ro_shadow_R), from
     the cut's cut_shadow through its (F) disjunct: D = fr + 2768 is in the owned class-6 frame, so the span lies in
     that frame's shadow [shadow_addr fr, shadow_addr fr + 4096 / 8) *)
  assert (HSWD : A.ShadowRwOn.shadow_rw_on (A.Prog.Seg.P4.p4_evt_ro_shadow_R D) mem3).
  { apply (A.ShadowRwOn.shadow_rw_on_mono (A.ACtlRtC.cut_shadow B ly3 S3)); [|exact Hcut].
    intros a Ha.
    unfold A.Prog.Seg.P4.p4_evt_ro_shadow_R, A.Prog.Seg.P4.p4_evt_shadow_R,
      A.Prog.asan_memset_c_on.asan_memset_shadow_R, A.Prog.sh_word_on.sh_word_on in Ha.
    cbv beta in Ha.
    rewrite (LMState.unsigned_lit D), (LMState.unsigned_lit 72) in Ha by lia.
    destruct Ha as (_ & Ha).
    left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite <- Efr, HFB6.
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Ha.
    clear - Ha ED Ffr32.
    unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF, A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in *.
    Z.div_mod_to_equations; lia. }
  pose proof (A.Prog.Seg.P4F_on.p4_evt_ro_F_on
    (A.Prog.asan_memsetF_on.asan_memset_holds_F_on A.Prog.memset.memset_holds) RNG
    (CK11.getr regs3 1) (CK11.getr regs3 2) (CK11.getr regs3 3) (CK11.getr regs3 4) (CK11.getr regs3 5)
    (CK11.getr regs3 6) (CK11.getr regs3 7) (CK11.getr regs3 8) (CK11.getr regs3 9) (CK11.getr regs3 10)
    (CK11.getr regs3 11) (CK11.getr regs3 12) (CK11.getr regs3 13) (CK11.getr regs3 14) (CK11.getr regs3 15)
    (CK11.getr regs3 16) (CK11.getr regs3 17) (CK11.getr regs3 18) (CK11.getr regs3 19) (CK11.getr regs3 20)
    (CK11.getr regs3 21) (CK11.getr regs3 22) (CK11.getr regs3 23) (CK11.getr regs3 24) (CK11.getr regs3 25)
    (CK11.getr regs3 26) (CK11.getr regs3 27) (CK11.getr regs3 28) (CK11.getr regs3 29) (CK11.getr regs3 30)
    (CK11.getr regs3 31) CK11.fp_regs CK11.fp_csr mem3 spv A D (spv - 2208) junk
    R2 R9 HA HD Hspv ltac:(lia) ltac:(lia) HLD RWD HAD HE HA7 HRT HSEP HSTK ltac:(rewrite HK; lia)
    ltac:(unfold A.AsanRT.HIGHMEM_BEG; lia) ltac:(unfold A.AsanRT.APPMEM_END; lia) HAC HSWD HRO
    G192 (A.ProgBridge.rng_bytes_RNG_W H3) Gimg ltac:(rewrite HK; exact Gstk) Gd Gshd
    ltac:(rewrite HK; exact Gshs)) as HRUN.
  pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
  rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
  destruct HFS as (ms' & Hrun & HQ0).
  apply (Reusable.YA0nR.SRr_fsteps segs A.ACtlG.Kit.kit_wx W3 _ ms' md3 RNG (POST cx) Hrun
           (A.ProgBridge.fp_avoids_RNG_W H3)).
  intros md' Hsbm.
  (* G5: the run's end state is the exit cut's state at the run's own map R and memory m'. *)
  destruct HQ0 as (R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K22 & K25 & MU & WM & RO' & _ & RWz).
  subst ms'.
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81b90) R m' md') (POST cx)).
  rewrite HK in MU. change (LFrame.munch (p4_W D spv) mem3 m') in MU.
  (* the registers the run keeps, on the core's getr *)
  assert (G2 : CK11.getr R 2 = CK11.getr regs3 2) by exact K2.
  assert (G3 : CK11.getr R 3 = CK11.getr regs3 3) by exact K3.
  assert (G4 : CK11.getr R 4 = CK11.getr regs3 4) by exact K4.
  assert (G8 : CK11.getr R 8 = CK11.getr regs3 8) by exact K8.
  assert (G9 : CK11.getr R 9 = CK11.getr regs3 9) by exact K9.
  assert (G19 : CK11.getr R 19 = CK11.getr regs3 19) by exact K19.
  assert (G26 : CK11.getr R 26 = CK11.getr regs3 26) by exact K26.
  assert (G22 : CK11.getr R 22 = CK11.getr regs3 22) by exact K22.
  assert (G25 : CK11.getr R 25 = CK11.getr regs3 25) by exact K25.
  assert (RA : CK11.getr R 9 = Z_to_bv 64 A) by (transitivity (CK11.getr regs3 9); [exact G9 | exact R9]).
  (* memory kept across the run: an 8-byte word, a byte range, a cell list, an addressable range *)
  assert (Tb : forall a bs, LMem.bytes_at segs mem3 a bs ->
                 LFrame.disjoint_from (p4_W D spv) a (Z.of_nat (length bs)) -> LMem.bytes_at segs m' a bs).
  { intros a bs Hb Hd. exact (LFrame.bytes_at_transport segs (p4_W D spv) mem3 m' a bs Hb MU Hd). }
  assert (Tq : forall a v, ACtlCutP.q64 mem3 a v ->
                 (a + 8 <= D \/ D + 72 <= a) -> (a + 8 <= spv - 2208 \/ spv <= a) -> ACtlCutP.q64 m' a v).
  { intros a v Hq H1 H2. unfold ACtlCutP.q64 in *. apply Tb; [exact Hq|].
    rewrite LMem.length_le8. cbn [p4_W LFrame.disjoint_from]. lia. }
  assert (MK : A.AsanRTFacts.meta_kept mem3 m')
    by exact (A.AsanRTFacts.munch_meta (p4_W D spv) mem3 m' MU Hallapp).
  assert (Tad : forall p n, A.AsanRT.addressable mem3 p n -> A.AsanRT.addressable m' p n)
    by (intros p n Had; exact (A.AsanRTFacts.addressable_kept mem3 m' p n Had MK)).
  (* a spill of the cut moves to the exit map R and memory m' (s1 = A kept; the spill word is apart from W) *)
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
    subst Ab. apply Tq; [exact Hq | lia | lia]. }
  (* the in-block facts of the lib pre (KitMem K3) *)
  destruct (A.ACtlG.KitMem.kitmem_input_apart (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI cx [] ly3 S3 W3
              mem3 md3 k LAWS HB HJ HF HP
              (A.ProgWorld_Fs.ctl_frame_above_img B ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6))
    as (Hlin & Hp0 & Hpceil & Hpfr & Hpapp).
  rewrite <- Efr, HFB6 in Hpfr.
  apply (HX cx [] fr k ly3 S3 W3 R m' md' HB).
  - (* journal: a Theorem Labs lane's ajournal_of_fsteps; the write set is the frame's fragment record and the stack window *)
    lazymatch type of Hrun with
    | Reusable.YK04R.fsteps _ _ ?s0 _ =>
        refine (A.ProgWorld.ajournal_of_fsteps B LAWS A.ACtlG.Kit.kit_wx _ _ _ _ _ _ _ _ _ _ _ _ s0 _ _ _ _ RNG
                  (p4_W D spv) HJ Hrun
                  (A.ProgBridge.fp_avoids_RNG_W H3) MU Hsbm _)
    end.
    intros a Ha Hw. cbn [p4_W LFrame.outside] in Hw.
    unfold Reusable.YCbq.awr_byte.
    destruct (Z_le_gt_dec (spv - 2208) a) as [L1|L1];
      [destruct (Z_le_gt_dec spv a) as [L2|L2]|].
    + (* not in the stack window: in the fragment record, a byte of the class-6 frame *)
      right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [exact (in_eq _ _)|].
      left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr, HFB6. lia.
    + left. unfold A.ACfn.LLVMF_STK. lia.
    + right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [exact (in_eq _ _)|].
      left. unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr, HFB6. lia.
  - (* frames: own6 on both cuts *)
    exact HF.
  - (* the frame law: own6 on both cuts *)
    exact HL.
  - (* the event bound: kmax 14 on both cuts *)
    exact Hk.
  - (* the exit body, C_A81b90 (ACtlCutP.v:1824-1838) *)
    cbv beta iota delta [ACtlCut.cut_body ACtlCutP.C_A81b90].
    split; [exact HP|].
    split.
    { (* FRAC: its registers through the run's post, its memory apart from W *)
      pose proof (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R mem3 HFRAC G2 G3 G4 G8 G9 G19 G26) as HF1.
      destruct HF1 as (Af & spf & F1 & F2' & F3 & F4 & F5 & F6 & F7 & F8 & F9' & F10 & F11 & F12 & F13 & F14 &
        F15 & F16' & F17 & F18 & F19 & F20 & F21 & F22 & (sh & F23 & F23l) & F24).
      assert (EA' : Af = A).
      { assert (E : Z_to_bv 64 Af = Z_to_bv 64 A)
          by (unfold ACtlCut.rgv in F6; rewrite <- F6; exact RA).
        apply (f_equal (@bv_unsigned 64)) in E.
        rewrite (LMState.unsigned_lit Af) in E
          by (unfold ACtlCutP.FRAME_BYTES, A.AsanRT.APPMEM_END in *; lia).
        rewrite (LMState.unsigned_lit A) in E by lia. exact E. }
      subst Af.
      exists A, spf.
      do 17 (split; [assumption|]).
      split; [exact (Tq _ _ F18 ltac:(lia) ltac:(lia))|].
      split; [exact (Tq _ _ F19 ltac:(lia) ltac:(lia))|].
      split; [exact (Tq _ _ F20 ltac:(lia) ltac:(lia))|].
      split; [exact (Tq _ _ F21 ltac:(lia) ltac:(lia))|].
      split; [exact (Tq _ _ F22 ltac:(lia) ltac:(lia))|].
      split.
      - exists sh. split; [|exact F23l]. apply Tb; [exact F23|]. rewrite F23l.
        unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in *.
        change (Z.of_nat (Z.to_nat (3136 / 8))) with 392.
        apply p4_disj2_of_out; [lia | lia | lia |].
        intros x Hx. apply O6. change (3136 / 8) with 392. lia.
      - (* the saved registers at [c_sp - 104, c_sp); and, once FRAC gains the announced fake-frame trailer
           word q64 m (fr + 4088) (flag_addr ..) as its last conjunct (two Theorem Labs lanes 05:0xZ), that word too:
           it lies in the frame above the fragment record and below the stack window *)
        first
          [ apply Tb; [exact F24|]; cbn [p4_W LFrame.disjoint_from]; lia
          | destruct F24 as (F24 & F25); split;
            [ apply Tb; [exact F24|]; cbn [p4_W LFrame.disjoint_from]; lia
            | exact (Tq _ _ F25 ltac:(lia) ltac:(lia)) ] ]. }
    split; [exact Hn|].
    split.
    { (* OURb: the six bytes at fr + 2624 lie below the fragment record and in the frame *)
      unfold ACtlCutP.OURb in *. apply Tb; [exact Hour|].
      unfold A.Prog.SlotModel.OUR. rewrite length_map, length_seq. cbn [p4_W LFrame.disjoint_from]. lia. }
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
      split; [exact (Tad _ _ Pad)|].
      split; [apply Tb; [exact Pin|]; rewrite Hlin; cbn [p4_W LFrame.disjoint_from]; lia|].
      split; [intros Hn0; exact (Tad _ _ (Pg Hn0))|].
      split; [exact (Tsp 184 _ ltac:(lia) P184)|]. split; [exact (Tsp 256 _ ltac:(lia) P256)|].
      split; [exact (Tsp 264 _ ltac:(lia) P264)|]. split; [exact (Tsp 272 _ ltac:(lia) P272)|].
      exact (Tsp 32 _ ltac:(lia) P32). }
    split; [exact (Tsp 144 _ ltac:(lia) S144)|].
    split; [exact (Tad _ _ Had2691)|].
    split.
    { (* the fragment-record spill [A + 192] = D = fragb fr, from the entry's rw_cells *)
      exists A. split; [exact RA|].
      destruct HLD as ((_ & Hb192) & _). cbn [LCells.cells_bytes LCells.cbytes] in Hb192.
      rewrite ?app_nil_r in Hb192. unfold ACtlCutP.fragb. rewrite <- ED.
      apply Tq; [exact Hb192 | lia | lia]. }
    split; [exact (Tad _ _ HadF)|].
    split; [exact (Tad _ _ Had2688)|].
    split.
    { unfold ACtlCutP.IDBe in *. apply Tb; [exact HID|].
      unfold Prog.RcIdentModel.ID0. rewrite repeat_length. unfold Prog.RcIdentModel.ID_SIZE.
      cbn [p4_W LFrame.disjoint_from]. lia. }
    split.
    { (* the fragment record is now the callee's 72 zero bytes *)
      unfold ACtlCutP.FGBe. rewrite <- ED. destruct RWz as ((_ & Hbz) & _).
      cbn [LCells.cells_bytes LCells.cbytes] in Hbz. rewrite ?app_nil_r in Hbz.
      exact Hbz. }
    exists A, jy, junk2.
    split; [exact RA|].
    split; [lia|].
    split; [exact (Tq _ _ Q280 ltac:(lia) ltac:(lia))|].
    split; [exact (Tq _ _ Q240 ltac:(lia) ltac:(lia))|].
    split; [exact (LFrame.rw_cells_transport segs (p4_W D spv) mem3 m' _ _ RWjy MU WM
                     ltac:(cbn [p4_W LFrame.disjoint_from LCells.cells_size LCells.csize]; lia))|].
    split; [exact (LFrame.rw_cells_transport segs (p4_W D spv) mem3 m' _ _ RWj2 MU WM
                     ltac:(cbn [p4_W LFrame.disjoint_from LCells.cells_size LCells.csize]; lia))|].
    exact (Tad _ _ Had2880).
  - (* ctl_rt_C B ly3 S3 m' (the world does not move): the runtime cells are apart from the write set, no shadow
       byte changes (meta_kept), so each region is kept; the run keeps ro_agree *)
    split; [exact (A.AsanRTFacts.asan_cells_kept (p4_W D spv) mem3 m' HAC MU (proj1 Hrtd))|].
    split; [exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Hcut MK WM)|].
    split; [exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Himg MK WM)|].
    exact RO'.
Qed.

End GlueP4.

Print Assumptions glue_seg_P4.
