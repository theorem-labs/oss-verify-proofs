(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths and module names changed; 717 of its 758 lines of code are new or changed and 110 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F31.v, with its module paths and module names changed; 494 of its 571 lines of code are new or changed and 681 lines of the source are left out. *)
(* lib/A/ACtlG/F31.v -- GLUE for stage seg_F31 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   Hypothesis seg_F31).  Written by a Theorem Labs lane; single writer.  rule 24: no function proved (stage
   glue of a walk; the released-proof position of LLVMFuzzerTestOneInput was settled for this unit: At ossv/recipes c5e779efe8c (2026-10-31), no released proof of it outside this unit).
   Pattern: glue-pattern.md (a working note, not in this delivery) (G1-G5), worked example lib/A/ACtlG/A5.v.

   WHAT IT PROVES
     glue_seg_F31 : forall POST (j : nat),
       CF POST (ix_cut C_A827d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A82800_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A82798_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's seg_F31.  The entry
   is C_A82798_at j (pc 0x82798); the two exits are C_A827d8_at j (the bcmp wrapper returned) and C_A82800_at j (the
   target of `bnez a0` at 0x82798).  The source segment is Seg/F31.v seg_F31 :550 (6a74d5929d2).

   THE RUNS LIFTED (lib/A/Prog/Seg/F31F.v, this worker's v1.9 footprint re-run of Seg/F31.v)
     F31F.f31n_evt_F   classify = None (a0 = -1): the branch to 0x82800, register-only.
     F31F.f31c_norm_F_on  classify = Some e (a0 = 0): the three byte checks fall through and the bcmp wrapper at
                       0x827d4 compares the 6 source bytes at fr + 452 with our[] at fr + 2624; the wrapper writes only
                       its stack window [sp - 4560, sp).  Route (C) form (a working branch 2f98bce6530): its
                       callee premise `bcmp_wrap_F_at_on RNG` (bcmp_wrap_c_on.v's narrowed footprint contract at one
                       footprint) is DISCHARGED AT THE CALL by a Theorem Labs lane's A.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on
                       (Qed) through F31F.F31BWO.bcmp_wrap_F_at_on_owner; its shadow premise is
                       `shadow_rw_on (F31F.f31c_norm_F_shadow_R O R) m`, the wrapper's two strings' shadow-word spans.

   THE PROOF (G1-G5)
   G1  ix_cut's index equation; C_A82798_at's body (ACtlCutP.v); the classify result in a0 (F31.f31_cls_r).
   G2  the run's premises: spills (FLSH / PRO through register 9), the source field (F31.f31_B_src over the body's
       t_B bytes), our[] (LK), the wrapper's stack window from the journal's presence fact, the runtime cells from
       ctl_rt_C (asan_cells; the run's shadow region from cut_shadow's (F) disjunct, since both strings lie in the
       owned class-6 frame and their shadow words in its shadow [S(fr), S(fr) + 512); ro_agree) and, for the five
       bcmp cells REAL_BCMP / REAL_MEMCMP / GOT_CF / CF+254 / CF+255, from the core's AR (am_const) under CtrlTSyms
       (f31g_rt_cells below); every rng premise from the
       visibility lemmas (A.ProgWorldVisWin.win_vis, A.ProgWorldVisFrame.frame_vis, A.ProgBridge.img_vis_W); every
       numeric bound from visible state (FRAC, frames_bounds, astk_ok, the AR frame law, layout_le).
   G3  cfg_at is MS by eq_refl; the walk moves to the run's canonical map mkR_of regs3 (YA0nR.SRr_xregs_eqv).
   G4  ProgBridge.fevt_of_evtF; YA0nR.SRr_fevt (register-only arm) / SRr_fevt_hid (the wrapper arm).
   G5  the exit cut at the run's end map: journal by YCbq.ajournal_exec (write set = the wrapper's stack window,
       awr_byte's stack case), frames / frame law / k unchanged, the body across the window (f31g_keep, f31g_frac_mem,
       Kit.kit_frac_move), ctl_rt_C across the window (AsanRTFacts.asan_cells_kept, ShadowRwOnT.shadow_rw_on_kept for
       both shadow regions at the same state ly3 S3, f31g_ro_keep).

   SECTION HYPOTHESES: LAWS and TFIB_SYMS, ACtl.v's own (Section Ctl).  Nothing else.

   CLOSURE (glue closure rule): every project module is Required qualified, never Imported; no statement here names a
   frame-route identifier (the proof-internal lemmas cite F31F / F31 / bcmp_wrap_on / Tac-free AsanRTFacts by name).
   Every Require names the module's FULL directory in its From clause, and every lib/Reusable, lib/Lib and lib/Prog
   module this file names is reached through a Module alias bound to its FULL path (a Theorem Labs lane 05:28Z).  The lib/A modules
   are named by their A.<...> path (each Locate-checked to one module); ACtl.v's notation block is copied verbatim.
   SHADOWED NAMES: getr / mkst / seg_rom / cfg_at only through the full-path aliases CK11 / CG0d.

   BUILD STATE: route (C) L3 switch (a Theorem Labs lane, recipe L3-recipe.md section 2 (a working note, not in this delivery)): the
   entry cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (ctl_from on a working branch).  Built on a working branch +
   a working branch by cbrec v8 (build of record, .prov under (internal path)).
   Batch3's FRAC trailer word at 0x827d8 is kept by f31g_frac_mem (the wrapper's window lies above the whole class-6
   frame).  Print Assumptions glue_seg_F31 = the Rocq primitives and functional_extensionality_dep. *)

From Coq Require Import ZArith List Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YK04 YM05 YO09 YA0n YA0nR YG00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG01 YG0f YG0d YG0n YC5d YCbq YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k AF0m Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACfn ACtlK ACtlCut ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgBridge ProgWorld ProgWorldVisWin ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds rng_asan SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame PropExec RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcClassify RcParse RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require bcmp_wrap_c_on bcmp_wrap_on sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F31 F31F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* Full-path aliases for every lib/Reusable, lib/Lib and lib/Prog module this file names (a Theorem Labs lane 05:28Z: 175 image-A
   module names also exist under lib/A/Reusable, lib/U, lib/B, lib/A/Bz/Lib, lib/AZ/Lib (not in this delivery); a partial path can bind
   the wrong copy). *)
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module CK04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK04.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CO09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.
Module CA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module CA0nR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module CG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module CG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module CG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module CG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module CG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module CC5d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YC5d.
Module CCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Module CP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module SG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F31.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F31F.
Module CTP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Module CT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.

(* The core's segment list, as ACtlCut.v and ACtl.v bind it. *)
Local Notation segs := A.AB1v.tfibsegs.
Local Notation rsegs := A.Img0.rsegs.

(* =================================================================================================================
   1. Proof-internal helpers (statements over lib/Lib's memory predicates and the cut bundles; no frame-route name). *)

(* A word spilled at s1 + off, read at the FRAC spill base A (the base of `spill` is existential; F31.f31_spill's
   argument, over the cut layer's rgv / spill / q64). *)
Lemma f31g_spill : forall regs m off v A, CTP.spill regs m off v -> CT.rgv regs 9 A ->
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off <= 400 -> CTP.q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  unfold CT.rgv in HA, HA'. rewrite HA in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite MEM.length_le8 in Hq1.
  assert (E : A' = A).
  { apply (f_equal bv_unsigned) in HA'. rewrite !LMS.unsigned_lit_wrap in HA'.
    rewrite (Z.mod_small A) in HA' by lia. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* Every byte of a range that is in_app (the core's form) is app memory (ctrl's form). *)
Lemma f31g_app_of_in_app {rc : CM05.RunCeil} : forall lo len a,
  CG0f.in_app lo len -> lo <= a < lo + len -> ART.app_mem a.
Proof.
  intros lo len a [H0 [HL | [HH1 HH2]]] Ha; pose proof CG0f.ASAN_CEIL_range as [CR _];
    unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END, CG0f.kLowShadowBeg, CG0f.kHighMemBeg in *;
    [left | right]; lia.
Qed.

(* A present byte (the core's apresent) is a writable, readable byte of ctrl's stk. *)
Lemma f31g_stk_of_pres : forall (H : word -> bool) (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> CG0n.apresent H m a) -> FRM.stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 HP. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HP a Ha) as [_ [b Hb]]. unfold MEM.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold MEM.mrd. rewrite Hb. reflexivity.
Qed.

(* A readable byte off the image is a present byte of the memory itself (seg_rom is None there). *)
Lemma f31g_mrd_off_img : forall (m : word -> option byte) x b, 0 <= x < 2 ^ 64 -> ~ CG0d.in_img segs x ->
  MEM.mrd rsegs m (MEM.wa x) = Some b -> m (Z_to_bv 64 x) = Some b.
Proof.
  intros m x b Hx Hn H. unfold MEM.mrd, MEM.wa in H. destruct (m (Z_to_bv 64 x)) as [b'|] eqn:E; [exact H|].
  change (LPE.seg_rom rsegs (Z_to_bv 64 x)) with (CK11.seg_rom segs (Z_to_bv 64 x)) in H.
  rewrite (CCbq.seg_rom_none segs x Hx Hn) in H. discriminate H.
Qed.

(* An address at or above kLowMemEnd is not an image byte. *)
Lemma f31g_not_img : forall x, CG0f.kLowMemEnd <= x -> ~ CG0d.in_img segs x.
Proof. intros x Hx Hi. pose proof (A.ACtlG.Kit.kit_segs_low x Hi). lia. Qed.

(* A read-only byte is an image byte, so it lies below kLowMemEnd. *)
Lemma f31g_ro_low : forall a : word, MEM.ro_addr rsegs a = true -> bv_unsigned a < CG0f.kLowMemEnd.
Proof.
  intros a H. destruct (Z_lt_le_dec (bv_unsigned a) CG0f.kLowMemEnd) as [Hl|Hge]; [exact Hl|]. exfalso.
  unfold MEM.ro_addr in H. change A.Img0.rsegs with A.AB1v.tfibsegs in H.
  rewrite (CCbq.find_segment_none segs (bv_unsigned a) (f31g_not_img _ Hge)) in H. discriminate H.
Qed.

(* ro_agree across a write set W all of whose bytes lie at or above kLowMemEnd. *)
Lemma f31g_ro_keep : forall W m m', A.ACtlK.ro_agree_at m -> FRM.munch W m m' ->
  (forall x, x < CG0f.kLowMemEnd -> FRM.outside W x) -> A.ACtlK.ro_agree_at m'.
Proof.
  intros W m m' H MU HW a Ha. unfold MEM.mrd. rewrite (MU a).
  - exact (H a Ha).
  - apply HW. exact (f31g_ro_low a Ha).
Qed.

(* One byte of the core's view of an image byte is the byte ctrl's mrd reads (image bytes are visible in every
   world, A.ProgBridge.img_vis_W). *)
Lemma f31g_cell_byte {fx : CK11.FPState} {rc : CM05.RunCeil} :
  forall (W : CA0n.world segs) (mem : word -> option byte) (x z : Z),
  0x10000 <= x < 0x5fe000 -> CG0n.aview segs (CA0n.w_H W) mem x = Some z ->
  exists b, MEM.mrd rsegs mem (MEM.wa x) = Some b /\ bv_unsigned b = z.
Proof.
  intros W mem x z Hx Hv.
  pose proof (A.ProgBridge.img_vis_W W) as (_ & _ & Hvis).
  assert (Hh : CA0n.w_H W (Z_to_bv 64 x) = false)
    by (apply Hvis; unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia).
  unfold CG0n.aview, CP09.mbyte, CK04.mrestrict in Hv. rewrite Hh in Hv.
  unfold MEM.mrd, MEM.wa.
  destruct (mem (Z_to_bv 64 x)) as [b|] eqn:Em.
  - cbn in Hv. injection Hv as <-. exists b. split; reflexivity.
  - change (LPE.seg_rom rsegs (Z_to_bv 64 x)) with (CK11.seg_rom segs (Z_to_bv 64 x)).
    destruct (CK11.seg_rom segs (Z_to_bv 64 x)) as [b|]; cbn in Hv; [|discriminate Hv].
    injection Hv as <-. exists b. split; reflexivity.
Qed.

(* One byte of an 8-byte image cell, read through mrd: the shape every bytes_at goal below reduces to. *)
Ltac f31g_cell_goal Hcell W mem :=
  let i := fresh "i" in let Hi := fresh "Hi" in let b := fresh "b" in let Eb := fresh "Eb" in
  let Ub := fresh "Ub" in let o := fresh "o" in let Eo := fresh "Eo" in
  split; [lia|]; split; [rewrite ?MEM.length_le8; cbn [length]; lia|];
  intros i Hi; rewrite ?MEM.length_le8 in Hi; cbn [length] in Hi;
  do 8 (destruct i as [|i]; [
    match goal with |- MEM.mrd _ _ (MEM.wa (?a + Z.of_nat ?k)) = _ =>
      destruct (f31g_cell_byte W mem (a + Z.of_nat k) _ ltac:(cbn; lia)
                  ltac:(first [ exact (Hcell k ltac:(lia)) | exact (Hcell 6%nat ltac:(lia))
                              | exact (Hcell 7%nat ltac:(lia)) ])) as (b & Eb & Ub)
    end;
    rewrite Eb; remember (nth_error _ _) as o eqn:Eo; vm_compute in Eo; subst o;
    f_equal; apply bv_eq; rewrite Ub; vm_compute; reflexivity |]);
  lia.

Section GlueF31.

(* ACtl.v's Section Ctl shape (its contexts, variables and the hypotheses this stage uses, in its order). *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : CG0f.asyms.
Variable MT : CC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis LAWS : CG0d.AR_laws segs B.
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A82798_at := (ACtlCutP.C_A82798_at B).
Local Notation C_A827d8_at := (ACtlCutP.C_A827d8_at B).
Local Notation C_A82800_at := (ACtlCutP.C_A82800_at B).

(* The five runtime cells the bcmp wrapper reads (bcmp_wrap_c.v's REAL_BCMP, REAL_MEMCMP, GOT_CF, CF + 254,
   CF + 255, under Seg/F31.v's own names), from the core's AR: am_const (YG0n.v ARm) over the bundle's const table,
   which CtrlTSyms fixes to A/AF0m.v's Tfib_const (rows 0xa17f0 -> 0x97b0c, 0xa17e8 -> 0x97bdc, 0x9fac0 -> 0x13a3a8,
   0x13a4a0 -> 0x101010101010101). *)
Lemma f31g_rt_cells : forall ly S (W : CA0n.world segs) mem md, CG0n.AR segs B ly S W mem md ->
  MEM.bytes_at rsegs mem SG.REAL_BCMP (MEM.le8 (MEM.wa SG.BCMP)) /\
  MEM.bytes_at rsegs mem SG.REAL_MEMCMP (MEM.le8 (MEM.wa SG.MEMCMP)) /\
  MEM.bytes_at rsegs mem SG.GOT_CF (MEM.le8 (MEM.wa SG.CF)) /\
  MEM.bytes_at rsegs mem (SG.CF + 254) [Z_to_bv 8 1] /\ MEM.bytes_at rsegs mem (SG.CF + 255) [Z_to_bv 8 1].
Proof.
  intros ly S W mem md HAR.
  destruct HAR as (HARm & _).
  pose proof (CG0n.am_const _ _ _ _ HARm) as HC.
  rewrite (A.AF0m.ts_const _ TFIB_SYMS ly) in HC.
  assert (Hrow : forall c, In c A.AF0m.Tfib_const_abs ->
            CG0f.cell_holds B ly (CG0n.aview segs (CA0n.w_H W) mem) c).
  { intros c Hc. apply (proj1 (Forall_forall _ _) HC). unfold A.AF0m.Tfib_const.
    apply in_or_app. right. apply in_or_app. left. exact Hc. }
  assert (Hin : forall a v, In (CG0f.z8 (CG0f.ANum a) v) A.AF0m.Tfib_const_abs ->
            forall k, (k < 8)%nat -> CG0n.aview segs (CA0n.w_H W) mem (a + Z.of_nat k) = Some (CG0f.le_byte v 8 k)).
  { intros a v H k Hk. exact (Hrow _ H k Hk). }
  assert (R1 : In (CG0f.z8 (CG0f.ANum 0xa17f0) 0x97b0c) A.AF0m.Tfib_const_abs)
    by (unfold A.AF0m.Tfib_const_abs; repeat (first [left; reflexivity | right])).
  assert (R2 : In (CG0f.z8 (CG0f.ANum 0xa17e8) 0x97bdc) A.AF0m.Tfib_const_abs)
    by (unfold A.AF0m.Tfib_const_abs; repeat (first [left; reflexivity | right])).
  assert (R3 : In (CG0f.z8 (CG0f.ANum 0x9fac0) 0x13a3a8) A.AF0m.Tfib_const_abs)
    by (unfold A.AF0m.Tfib_const_abs; repeat (first [left; reflexivity | right])).
  assert (R4 : In (CG0f.z8 (CG0f.ANum 0x13a4a0) 0x101010101010101) A.AF0m.Tfib_const_abs)
    by (unfold A.AF0m.Tfib_const_abs; repeat (first [left; reflexivity | right])).
  pose proof (Hin _ _ R1) as H1. pose proof (Hin _ _ R2) as H2. pose proof (Hin _ _ R3) as H3.
  pose proof (Hin _ _ R4) as H4.
  unfold SG.REAL_BCMP, SG.BCMP, SG.REAL_MEMCMP, SG.MEMCMP, SG.GOT_CF, SG.CF.
  split; [f31g_cell_goal H1 W mem|].
  split; [f31g_cell_goal H2 W mem|].
  split; [f31g_cell_goal H3 W mem|].
  split.
  - split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
    destruct i as [|i]; [|lia].
    destruct (f31g_cell_byte W mem (0x13a4a0 + Z.of_nat 6) _ ltac:(cbn; lia) (H4 6%nat ltac:(lia))) as (b & Eb & Ub).
    replace (0x13a3a8 + 254 + Z.of_nat 0) with (0x13a4a0 + Z.of_nat 6) by (cbn; lia).
    rewrite Eb. cbn [nth_error]. f_equal. apply bv_eq. rewrite Ub. vm_compute. reflexivity.
  - split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
    destruct i as [|i]; [|lia].
    destruct (f31g_cell_byte W mem (0x13a4a0 + Z.of_nat 7) _ ltac:(cbn; lia) (H4 7%nat ltac:(lia))) as (b & Eb & Ub).
    replace (0x13a3a8 + 255 + Z.of_nat 0) with (0x13a4a0 + Z.of_nat 7) by (cbn; lia).
    rewrite Eb. cbn [nth_error]. f_equal. apply bv_eq. rewrite Ub. vm_compute. reflexivity.
Qed.

(* FRAC's memory part across a write set [lo, hi) that lies above the whole class-6 frame [fr, fr + 4096) and its
   shadow and below the cut's sp (the spill area, the frame header words, the frame shadow, the saved registers and
   the fake-frame trailer word [fr + 4088, fr + 4096), FRAC's last conjunct since Batch3, are all apart from it). *)
Lemma f31g_frac_mem : forall cx fr sel regs m m' lo hi,
  ACtlCutP.FRAC B cx fr sel regs m -> FRM.munch [(lo, hi)] m m' ->
  ART.HIGHMEM_BEG <= lo -> fr + 4096 <= lo -> hi <= CG0d.spZ regs ->
  ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros cx fr sel regs m m' lo hi HF MU Hlo Hfr Hhi.
  destruct HF as (A & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAS & HspA & HfrA &
                  HA416 & HSsp & HSapp & Q304 & Q24 & Q16 & Qhdr & Qent & (sh & Hsh & Hshl) & Hsaved & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold ART.HIGHMEM_BEG in Hlo. unfold ART.APPMEM_END in HSapp.
  rewrite HspZ in Hhi.
  pose proof Qhdr as (Qh0 & _).
  assert (KB : forall a bs, MEM.bytes_at segs m a bs ->
            (a + Z.of_nat (length bs) <= lo \/ hi <= a) -> MEM.bytes_at segs m' a bs).
  { intros a bs Hb Hd. apply (FRM.bytes_at_transport segs [(lo, hi)] m m' a bs Hb MU). cbn. split; [lia | exact I]. }
  exists A, sp. repeat (split; [assumption|]).
  split; [apply KB; [exact Q304 | unfold ACtlCutP.q64 in *; rewrite MEM.length_le8; right; lia]|].
  split; [apply KB; [exact Q24 | rewrite MEM.length_le8; right; lia]|].
  split; [apply KB; [exact Q16 | rewrite MEM.length_le8; right; lia]|].
  split; [apply KB; [exact Qhdr | rewrite MEM.length_le8; left; lia]|].
  split; [apply KB; [exact Qent | rewrite MEM.length_le8; left; lia]|].
  split.
  - exists sh. split; [|exact Hshl]. apply KB; [exact Hsh|]. left. rewrite Hshl.
    unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES, ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K.
    change (3136 / 8) with 392. rewrite Z2Nat.id by lia. Z.div_mod_to_equations. lia.
  - split.
    + apply KB; [exact Hsaved|]. right.
      unfold ACtlCut.c_sp in *. lia.
    + apply KB; [exact Qtr | rewrite MEM.length_le8; left; lia].
Qed.

(* FLSI, LK, FLS, LT, HB and the classify event word across a write set [lo, hi) that the spill area, the frame,
   the turn's block and the input block all miss, with every addressable range kept (the shadow is not written) and
   the registers the bundles read kept (s1 9, s2 18, s5 21, s6 22, s7 23, s8 24, s9 25).  F31.f31_keep's argument,
   over the cut layer's bundles. *)
Lemma f31g_keep : forall cx j phi fr regs regs' m m' lo hi A,
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.LK cx fr j regs m -> ACtlCutP.FLS cx j phi fr regs m ->
  ACtlCutP.LT cx fr j regs m ->
  FRM.munch [(lo, hi)] m m' -> FRM.wmono rsegs m m' ->
  (forall p n, ART.addressable m p n -> ART.addressable m' p n) ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> CK11.getr regs' 18 = CK11.getr regs 18 ->
  CK11.getr regs' 21 = CK11.getr regs 21 -> CK11.getr regs' 22 = CK11.getr regs 22 ->
  CK11.getr regs' 23 = CK11.getr regs 23 -> CK11.getr regs' 24 = CK11.getr regs 24 ->
  CK11.getr regs' 25 = CK11.getr regs 25 ->
  CT.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> hi <= A ->
  fr + 3136 <= lo ->
  (50 <= ACtlCutP.flen cx j -> phi + ACtlCutP.flen cx j <= lo) ->
  (ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) <= lo) ->
  ACtlCutP.FLSI cx j fr regs' m' /\ ACtlCutP.LK cx fr j regs' m' /\ ACtlCutP.FLS cx j phi fr regs' m' /\
  ACtlCutP.LT cx fr j regs' m'.
Proof.
  intros cx j phi fr regs regs' m m' lo hi A HI HLK HS HLT MU WM HAD E9 E18 E21 E22 E23 E24 E25 Hr9 HA0 HA1
    HhiA Hfrlo Hphlo Hplo.
  assert (KB : forall a bs, MEM.bytes_at segs m a bs ->
            (a + Z.of_nat (length bs) <= lo \/ hi <= a) -> MEM.bytes_at segs m' a bs).
  { intros a bs Hb Hd. apply (FRM.bytes_at_transport segs [(lo, hi)] m m' a bs Hb MU). cbn. split; [lia | exact I]. }
  assert (SP : forall off v, 0 <= off <= 400 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v Ho Hs. pose proof (f31g_spill regs m off v A Hs Hr9 HA0 HA1 Ho) as Hq.
    exists A. split; [unfold CT.rgv in Hr9 |- *; rewrite E9; exact Hr9|].
    unfold ACtlCutP.q64 in Hq |- *. apply KB; [exact Hq|]. right. lia. }
  assert (Hfr0 : 0 <= fr).
  { destruct HI as ((_ & _ & Hstk & _) & _). destruct Hstk as (H0 & _). exact H0. }
  destruct HI as (((H40 & H120 & H136 & H160 & H168 & H176 & H208 & H248p & HadO & Hbyp0 & Hadp0 & P184 & P256 &
                    P264 & P272 & P32) & H128 & Hstk & H144 & Had2691) & H216 & H224 & H248 & (Hadp & Hbyp) &
                  (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & CadF & CadI & C72 & C64 & C56 & C48)).
  destruct HLK as (Hj & H21 & HOUR).
  destruct HS as (_ & H18 & H22 & H23 & H24 & H25 & Hrec & H152 & H280).
  destruct HLT as ((HIDB & Hidok) & (HFGB & Hfgok) & (H104 & H112 & Hbody & Hadbody & HFI)).
  assert (HI' : ACtlCutP.FLSI cx j fr regs' m').
  { split.
    - split.
      + split; [apply SP; [lia | exact H40]|].
        split; [apply SP; [lia | exact H120]|].
        split; [apply SP; [lia | exact H136]|].
        split; [apply SP; [lia | exact H160]|].
        split; [apply SP; [lia | exact H168]|].
        split; [apply SP; [lia | exact H176]|].
        split; [apply SP; [lia | exact H208]|].
        split; [apply SP; [lia | exact H248p]|].
        split; [exact (HAD _ _ HadO)|].
        split; [apply KB; [exact Hbyp0 | left; lia]|].
        split; [intros Hn; exact (HAD _ _ (Hadp0 Hn))|].
        split; [apply SP; [lia | exact P184]|].
        split; [apply SP; [lia | exact P256]|].
        split; [apply SP; [lia | exact P264]|].
        split; [apply SP; [lia | exact P272] | apply SP; [lia | exact P32]].
      + split; [apply SP; [lia | exact H128]|].
        split.
        * apply (FRM.stk_transport_disjoint segs [(lo, hi)] m m' fr (fr + ACtlCutP.FRAME_BYTES) Hstk MU WM).
          cbn. unfold ACtlCutP.FRAME_BYTES. split; [lia | exact I].
        * split; [apply SP; [lia | exact H144] | exact (HAD _ _ Had2691)].
    - split; [apply SP; [lia | exact H216]|].
      split; [apply SP; [lia | exact H224]|].
      split; [apply SP; [lia | exact H248]|].
      split.
      + split; [exact (HAD _ _ Hadp)|]. apply KB; [exact Hbyp | left; lia].
      + split; [apply SP; [lia | exact C256]|].
        split; [apply SP; [lia | exact C184]|].
        split; [apply SP; [lia | exact C192]|].
        split; [apply SP; [lia | exact C80]|].
        split; [apply SP; [lia | exact C88]|].
        split; [apply SP; [lia | exact C96]|].
        split; [apply SP; [lia | exact C272]|].
        split; [apply SP; [lia | exact C264]|].
        split; [exact (HAD _ _ CadF)|]. split; [exact (HAD _ _ CadI)|].
        split; [apply SP; [lia | exact C72]|]. split; [apply SP; [lia | exact C64]|].
        split; [apply SP; [lia | exact C56] | apply SP; [lia | exact C48]]. }
  assert (HLK' : ACtlCutP.LK cx fr j regs' m').
  { split; [exact Hj|]. split; [unfold CT.rgv in H21 |- *; rewrite E21; exact H21|].
    unfold ACtlCutP.OURb in HOUR |- *. apply KB; [exact HOUR|]. rewrite SM.OUR_length. left. lia. }
  assert (HS' : ACtlCutP.FLS cx j phi fr regs' m').
  { split; [exact HI'|].
    split; [unfold CT.rgv in H18 |- *; rewrite E18; exact H18|].
    split; [unfold CT.rgv in H22 |- *; rewrite E22; exact H22|].
    split; [unfold CT.rgv in H23 |- *; rewrite E23; exact H23|].
    split; [unfold CT.rgv in H24 |- *; rewrite E24; exact H24|].
    split; [unfold CT.rgv in H25 |- *; rewrite E25; exact H25|].
    split.
    - intros H50. destruct (Hrec H50) as (Hp0 & Hp1 & Hg & Hpb & Hpl). pose proof (Hphlo H50) as Hpl50.
      split; [exact Hp0|]. split; [exact Hp1|].
      split.
      + apply KB; [exact Hg|]. unfold SM.t_g. rewrite SM.fr50_length. left. lia.
      + split; [|exact Hpl]. apply KB; [exact Hpb|]. left. unfold ACtlCutP.flen in *. lia.
    - split; [apply SP; [lia | exact H152] | apply SP; [lia | exact H280]]. }
  assert (HLT' : ACtlCutP.LT cx fr j regs' m').
  { split; [|split].
    - split; [|exact Hidok]. unfold ACtlCutP.IDBe in HIDB |- *. apply KB; [exact HIDB|].
      rewrite SG.f31_tID_len. unfold RIM.ID_SIZE. left. lia.
    - split; [|exact Hfgok]. unfold ACtlCutP.FGBe in HFGB |- *. apply KB; [exact HFGB|].
      rewrite SG.f31_tFG_len. left. lia.
    - split; [apply SP; [lia | exact H104]|]. split; [apply SP; [lia | exact H112]|].
      split.
      + apply KB; [exact Hbody|]. pose proof (SG.f31_fs_body_len (ACtlCut.c_in cx) (S j)) as Hl. left. lia.
      + split; [exact (HAD _ _ Hadbody) | exact HFI]. }
  exact (conj HI' (conj HLK' (conj HS' HLT'))).
Qed.

(* -----------------------------------------------------------------------------------------------------------------
   2. The stage. *)
Lemma glue_seg_F31 : forall POST (j : nat),
  CF POST (ix_cut C_A827d8_at [Z.of_nat j]) -> CF POST (ix_cut C_A82800_at [Z.of_nat j]) -> CF POST (ix_cut C_A82798_at [Z.of_nat j]).
Proof using LAWS TFIB_SYMS.
  intros POST j HX7d8 HX800 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [j] (ix_cut; C_A82798_at, ACtlCutP.v). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82798_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HPerm & HFRAC & Hn & Hj & HHB & HFLSI & HLK & HFLS & H10 & HtB & Had452 & Hev & HLT).
  (* G3: the cut's configuration in the run's state form, then the walk moved to the run's canonical map. *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82798_at [Z.of_nat j])) with 0x82798.
  apply (CA0nR.SRr_xregs_eqv segs W3 (LRG.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x82798) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRG.xregs_eqv_sym _ _ (LRG.mkR_of_eqv regs3))].
  unfold LRG.mkR_of.
  destruct (SG.f31_cls_r (SM.t_cls (ACtlCut.c_in cx) j)) as [Er | Er]; rewrite Er in H10.
  2: {
    (* classify = None (a0 = -1): `bnez a0` at 0x82798 is taken to 0x82800; register-only, the empty footprint. *)
    eapply (CA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx)).
    { apply A.ProgBridge.fevt_of_evtF. apply (SF.f31n_evt_F A.ACtlG.Kit.kit_RNG0). exact H10. }
    { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
    intros ms' md' Ems Hsbm. cbv beta in Ems. subst ms'.
    (* the end map is the start map: move the walk back to the cut's own map regs3 *)
    apply (CA0nR.SRr_xregs_eqv segs W3 regs3 (LRG.mkR_of regs3) CK11.fp_regs
             (Z_to_bv 64 0x82800) CK11.fp_csr None mem3 (CK11.seg_rom segs) md' (POST cx));
      [| exact (LRG.mkR_of_eqv regs3)].
    change (CA0n.SRr segs W3 (CG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82800_at [Z.of_nat j])) regs3 mem3 md')
              (POST cx)).
    apply (HX800 cx [Z.of_nat j] fr k ly3 S3 W3 regs3 mem3 md' HB).
    - eapply (CCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply CK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    - exact HF.
    - exact HL.
    - exact Hk.
    - cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A82800_at ACtlCutP.ixn nth].
      rewrite Nat2Z.id. split; [reflexivity|].
      exists phi. exact (conj HPerm (conj HFRAC (conj Hn (conj Hj (conj HHB (conj HFLSI
        (conj HLK (conj HFLS HLT)))))))).
    - exact Hrt. }
  (* classify = Some e (a0 = 0): the source field is 00 40 ab c9 c10 c11 (F31.f31_B_src) and the bcmp wrapper
     compares it with our[]. *)
  destruct (SG.f31_cls_some _ Er) as (e & Ecl).
  pose proof (SG.f31_B_src (ACtlCut.c_in cx) j e Ecl) as Esrc.
  set (c9 := RP.cp_b (SM.t_g (ACtlCut.c_in cx) j) 9) in *.
  set (c10 := RP.cp_b (SM.t_g (ACtlCut.c_in cx) j) 10) in *.
  set (c11 := RP.cp_b (SM.t_g (ACtlCut.c_in cx) j) 11) in *.
  set (lsc := [Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 171; c9; c10; c11]) in *.
  assert (HLs : MEM.bytes_at rsegs mem3 (fr + 448 + 4) lsc).
  { rewrite <- Esrc. change (fr + 448 + 4) with (fr + 448 + Z.of_nat 4).
    apply SG.f31_ba_sub; [exact HtB | rewrite SG.f31_B_length; lia]. }
  destruct (A.Spec.StrFun.memcmp_model_total lsc (SM.OUR (ACtlCut.c_in cx)) 6 ltac:(cbn; lia)
              ltac:(rewrite SM.OUR_length; lia)) as (v & Hv).
  destruct (SG.f31_mm_spec 6 lsc (SM.OUR (ACtlCut.c_in cx)) v eq_refl (SM.OUR_length _) Hv) as [Hiff Hvr].
  (* G2: the visible state. *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
  pose proof Hstatic as (_ & _ & Hceil & Hslo & _).
  pose proof CCbq.asan_consts as (HAC & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (CG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (CCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  assert (Efr : fr = CG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) ltac:(left; reflexivity)). unfold CG0f.frame_addr. rewrite EF. reflexivity. }
  assert (EFB : CG00.fs_frame_bytes 6 = 4096) by reflexivity.
  rewrite <- Efr in Hf4096, Hfceil, Hfapp. rewrite EFB in Hfceil, Hfapp.
  assert (Happ : forall a, fr <= a < fr + 4096 -> ART.app_mem a)
    by (intros a Ha; exact (f31g_app_of_in_app fr 4096 a Hfapp Ha)).
  pose proof HFRAC as (Asp & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA416 & HSsp & HSapp & _).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold ART.APPMEM_END in HSapp.
  unfold A.ACfn.LLVMF_STK in Hslo, Hpres.
  assert (Esp : bv_unsigned (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 2) = sp).
  { change (LinuxProcessSemantics.Riscv.Sem.reg_get regs3 2 = Z_to_bv 64 sp) in R2. rewrite R2.
    apply LMS.unsigned_lit. lia. }
  pose proof Hceil as Hceil0.
  pose proof HFLSI as (((_ & _ & _ & _ & HS168 & _ & HS208 & _ & Had2624 & _) & HS128 & _) & _).
  pose proof HLK as (_ & _ & HOUR).
  pose proof Hrt as (HAC0 & Hcut & Himg & HRO0).
  (* ctl_rt_C's (F) disjunct: the owned class-6 frame's shadow [S(fr), S(fr) + 512) *)
  assert (HFsh : forall a, ART.shadow_addr fr <= a < ART.shadow_addr fr + 512 -> A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a Ha. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite <- Efr, EFB. change (4096 / 8) with 512.
    unfold CG0f.shadow_addr, CG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K in Ha |- *. lia. }
  (* the run's region, the wrapper's two strings' shadow-word spans (sh_word_on (fr + 452) 6, sh_word_on (fr + 2624)
     6), lies in that frame shadow *)
  assert (HR31 : forall a, SF.f31c_norm_F_shadow_R (fr + 448) (fr + 2624) a -> A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a Ha. apply HFsh.
    unfold SF.f31c_norm_F_shadow_R, SF.f31c_evt_F_shadow_R, A.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R,
      A.Prog.sh_word_on.sh_word_on, A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Ha.
    revert Ha. clear. unfold ART.shadow_addr, ART.ASAN_K, CG0f.shadow_addr, CG0f.SHADOW_OFF.
    intros [(_ & Ha) | (_ & Ha)]; Z.div_mod_to_equations; lia. }
  destruct (f31g_rt_cells ly3 S3 W3 mem3 md3 HAR) as (HRB & HRM & HGC & HC254 & HC255).
  pose proof (A.ProgWorldVisWin.win_vis B) as WV.
  unfold A.ProgWorld.win_vis_stmt in WV.
  pose proof (A.ProgWorldVisFrame.frame_vis B) as FV.
  unfold A.ProgWorld.frame_vis_stmt in FV. specialize (FV LAWS).
  set (RNG := A.ProgBridge.RNG_W (CA0n.w_H W3)).
  assert (Vwin : forall a n, ACtlCut.c_sp cx - 32768 <= a -> a + n <= ACtlCut.c_sp cx -> LEF.rng RNG a n).
  { intros a n H1 H2. apply A.ProgBridge.rng_of_visible. exact (WV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a n HJ H1 H2). }
  assert (Vfr : forall a n, fr <= a -> a + n <= fr + 4096 -> LEF.rng RNG a n).
  { intros a n H1 H2. apply A.ProgBridge.rng_of_visible.
    rewrite Efr in H1, H2.
    exact (proj1 (FV _ _ _ _ _ _ _ a n HAR Hin6 H1 ltac:(rewrite EFB; exact H2))). }
  assert (Vsh : forall a n, 0 < n -> fr <= 64 * (a / 64) -> 64 * ((a + n - 1) / 64) + 64 <= fr + 4096 ->
            LEF.rng RNG (8 * (ART.shadow_addr a / 8))
              (8 * (ART.shadow_addr (a + n - 1) / 8) + 8 - 8 * (ART.shadow_addr a / 8))).
  { intros a n Hn0 H1 H2. assert (Hle : fr <= a) by (Z.div_mod_to_equations; lia).
    assert (Hhi : a + n <= fr + 4096) by (Z.div_mod_to_equations; lia).
    rewrite Efr in Hle, Hhi, H1, H2.
    destruct (proj2 (FV _ _ _ _ _ _ _ a n HAR Hin6 Hle ltac:(rewrite EFB; exact Hhi)) ltac:(lia) H1
                ltac:(rewrite EFB; exact H2)) as [E0 | Hvis]; [lia|].
    apply A.ProgBridge.rng_of_visible.
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Hvis.
    assert (E1 : 8 * (ART.shadow_addr a / 8) = ART.shadow_addr a / 8 * 8) by ring.
    assert (E2 : 8 * (ART.shadow_addr (a + n - 1) / 8) = ART.shadow_addr (a + n - 1) / 8 * 8) by ring.
    rewrite E1, E2. exact Hvis. }
  (* G4: the lift of the wrapper arm (it writes memory: SRr_fevt_hid). *)
  eapply (CA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF.
    eapply SF.f31c_norm_F_on with (A := Asp) (O := fr + 448) (R := fr + 2624) (c9 := c9) (c10 := c10) (c11 := c11)
      (rs := SM.OUR (ACtlCut.c_in cx)) (vcmp := v) (lo := ACtlCut.c_sp cx - 32768).
    - exact R9.
    - exact H10.
    - lia.
    - lia.
    - replace (fr + 448 + 4) with (fr + 452) by lia. exact (f31g_spill _ _ _ _ Asp HS128 R9 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (f31g_spill _ _ _ _ Asp HS208 R9 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (f31g_spill _ _ _ _ Asp HS168 R9 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact HLs.
    - exact HOUR.
    - apply SM.OUR_length.
    - exact Hv.
    - exact HRO0.
    - replace (fr + 448 + 4) with (fr + 452) by lia. exact Had452.
    - exact Had2624.
    - apply Happ; lia.
    - apply Happ; lia.
    - apply Happ; lia.
    - apply Happ; lia.
    - rewrite Esp. left. unfold SG.BCMP_WRAP_K. lia.
    - rewrite Esp. left. unfold SG.BCMP_WRAP_K. lia.
    - rewrite Esp. apply (f31g_stk_of_pres (CA0n.w_H W3)); [lia | lia |].
      intros a Ha. apply Hpres. lia.
    - rewrite Esp. unfold SG.BCMP_WRAP_K. lia.
    - unfold ART.HIGHMEM_BEG. lia.
    - rewrite Esp. unfold ART.APPMEM_END. lia.
    - exact HAC0.
    - exact (A.ShadowRwOn.shadow_rw_on_mono _ _ mem3 HR31 Hcut).
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255.
    - apply Vwin; lia.
    - apply Vwin; lia.
    - apply Vwin; lia.
    - apply A.ProgBridge.rng_bytes_RNG_W.
    - exact (A.ProgBridge.rng_of_visible _ _ _ (A.ProgBridge.img_vis_W W3)).
    - rewrite Esp. unfold SG.BCMP_WRAP_K. apply Vwin; lia.
    - apply Vfr; lia.
    - replace (fr + 448 + 9) with (fr + 448 + 4 + 6 - 1) by lia.
      apply Vsh; [lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
    - apply Vfr; lia.
    - replace (fr + 2624 + 5) with (fr + 2624 + 6 - 1) by lia.
      apply Vsh; [lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
    - exact (proj1 SF.F31BWO.bcmp_wrap_F_at_on_owner A.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on RNG). }
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  (* G5: the continuation at the wrapper's return 0x827d8, the run's end map R1 and memory m'. *)
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m' &
                  Ems & MU & WM & ST').
  subst ms'.
  rewrite Esp in MU, ST'. unfold SG.BCMP_WRAP_K in MU.
  match goal with |- context [LMS.MS ?R _ _ _ _ _ _] => set (R1 := R) end.
  change (CA0n.SRr segs W3 (CG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A827d8_at [Z.of_nat j])) R1 m' md')
            (POST cx)).
  assert (K2 : CK11.getr R1 2 = CK11.getr regs3 2) by reflexivity.
  assert (K3 : CK11.getr R1 3 = CK11.getr regs3 3) by reflexivity.
  assert (K4 : CK11.getr R1 4 = CK11.getr regs3 4) by reflexivity.
  assert (K8 : CK11.getr R1 8 = CK11.getr regs3 8) by reflexivity.
  assert (K9 : CK11.getr R1 9 = CK11.getr regs3 9) by (unfold CT.rgv in R9; rewrite R9; reflexivity).
  assert (K18 : CK11.getr R1 18 = CK11.getr regs3 18) by reflexivity.
  assert (K19 : CK11.getr R1 19 = CK11.getr regs3 19) by reflexivity.
  assert (K21 : CK11.getr R1 21 = CK11.getr regs3 21) by reflexivity.
  assert (K22 : CK11.getr R1 22 = CK11.getr regs3 22) by reflexivity.
  assert (K23 : CK11.getr R1 23 = CK11.getr regs3 23) by reflexivity.
  assert (K24 : CK11.getr R1 24 = CK11.getr regs3 24) by reflexivity.
  assert (K25 : CK11.getr R1 25 = CK11.getr regs3 25) by reflexivity.
  assert (K26 : CK11.getr R1 26 = CK11.getr regs3 26) by reflexivity.
  assert (K10 : CK11.getr R1 10 = Z_to_bv 64 v) by reflexivity.
  (* the window [sp - 4560, sp) is high app memory: the shadow is not written, so every addressable range stays *)
  assert (HAW : ARF.all_app [(sp - 4560, sp)]).
  { cbn [ARF.all_app]. split; [|exact I]. intros a Ha. unfold ART.app_mem, ART.HIGHMEM_BEG, ART.APPMEM_END. right.
    lia. }
  pose proof (ARF.munch_meta _ _ _ MU HAW) as MK.
  assert (HAD : forall p n, ART.addressable mem3 p n -> ART.addressable m' p n)
    by (intros p n Hp; exact (ARF.addressable_kept _ _ _ _ Hp MK)).
  (* the turn's block and the input block are live heap blocks, so below alloc_ceiling *)
  assert (Hph : In (phi, ACtlCutP.flen cx j) (CG0d.ablocks B ly3 S3))
    by (eapply Permutation_in; [symmetry; exact HPerm | apply in_or_app; right; left; reflexivity]).
  destruct (CG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hph)
    as (_ & _ & Hphceil & _).
  pose proof (CCbq.req_size_pos (ACtlCutP.flen cx j)) as Hrq.
  assert (Hinp : ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) <= ACtlCut.c_sp cx - 32768).
  { pose proof HB as ((_ & _ & _ & _ & Hpn & Hlen & _) & _).
    rewrite <- Hlen. destruct Hpn as [(Hn0 & Hp0) | (Hn0 & Hpin)].
    - rewrite Hn0, Hp0. unfold A.ACfn.A_EMPTY. lia.
    - assert (Hpin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (CG0d.ablocks B ly3 S3))
        by (eapply Permutation_in; [symmetry; exact HPerm | apply in_or_app; left; exact Hpin]).
      destruct (CG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hpin3) as (_ & _ & Hpc & _).
      pose proof (CCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)). lia. }
  apply (HX7d8 cx [Z.of_nat j] fr k ly3 S3 W3 R1 m' md' HB).
  - (* journal: the write set is the wrapper's stack window (awr_byte's stack case) *)
    eapply (CCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun a : Z => sp - 4560 <= a < sp).
    + exact HJ.
    + intros x Hx. unfold CK04.mrestrict. rewrite (MU x); [reflexivity|]. cbn. split; [exact Hx | exact I].
    + intros x Hx. unfold CK04.mrestrict in *. destruct (CA0n.w_H W3 x) eqn:Eh; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (sp - 4560)) as [Hl|Hl];
        [rewrite (MU x); [exact Hx | cbn; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) sp) as [Hl2|Hl2];
        [|rewrite (MU x); [exact Hx | cbn; split; [lia | exact I]]].
      pose proof (bv_unsigned_in_range 64 x) as Hrx. unfold bv_modulus in Hrx. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrx.
      destruct ST' as (_ & _ & Hst). destruct (Hst (bv_unsigned x) ltac:(lia)) as (_ & b & Hb).
      pose proof (f31g_mrd_off_img m' (bv_unsigned x) b ltac:(lia)
                    ltac:(apply f31g_not_img; unfold CG0f.kLowMemEnd; lia) Hb) as Hm'.
      rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hm'. congruence.
    + exact Hhid.
    + exact Hsbm.
    + intros a Ha. left. unfold A.ACfn.LLVMF_STK. lia.
  - exact HF.
  - exact HL.
  - exact Hk.
  - (* the exit body, C_A827d8_at, at the same turn j *)
    cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A827d8_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id. split; [reflexivity|].
    destruct (f31g_keep cx j phi fr regs3 R1 mem3 m' (sp - 4560) sp Asp HFLSI HLK HFLS HLT MU WM HAD
                K9 K18 K21 K22 K23 K24 K25 R9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros H50; pose proof (Hrq ltac:(lia)); unfold ACtlCutP.flen in *; lia) ltac:(lia))
      as (HI' & HLK' & HS' & HLT').
    exists phi.
    split; [exact HPerm|].
    split.
    { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R1 m'); [| exact K2 | exact K3 | exact K4 | exact K8
        | exact K9 | exact K19 | exact K26].
      apply (f31g_frac_mem cx fr fr regs3 mem3 m' (sp - 4560) sp HFRAC MU); unfold ART.HIGHMEM_BEG; lia. }
    split; [exact Hn|]. split; [exact Hj|].
    split; [split; [exact (proj1 HHB) | exact (HAD _ _ (proj2 HHB))]|].
    split; [exact HI'|].
    split; [exact HLK'|]. split; [exact HS'|].
    split; [rewrite Ecl; discriminate|].
    split.
    { change (CK11.getr R1 10 = Z_to_bv 64 0 <->
              firstn 6 (skipn 4 (SM.t_B (ACtlCut.c_in cx) j)) = SM.OUR (ACtlCut.c_in cx)).
      rewrite K10, (SG.f31_lit0 v Hvr), Esrc. exact Hiff. }
    split; [|exact HLT'].
    intros e0 He0. pose proof (Hev e0 He0) as Hq. unfold ACtlCutP.u32 in Hq |- *.
    apply (FRM.bytes_at_transport segs [(sp - 4560, sp)] mem3 m' _ _ Hq MU).
    rewrite MEM.length_le4. cbn. split; [lia | exact I].
  - (* ctl_rt_C across the window, same state ly3 S3: the runtime cells and read-only bytes are image bytes, the
       shadow is not written (both regions kept by ShadowRwOnT.shadow_rw_on_kept) *)
    split; [|split; [|split]].
    + apply (ARF.asan_cells_kept [(sp - 4560, sp)] mem3 m' HAC0 MU).
      cbn. split; [unfold ART.RT_LO, ART.RT_HI; lia | exact I].
    + exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Hcut MK WM).
    + exact (A.ShadowRwOnT.shadow_rw_on_kept _ mem3 m' Himg MK WM).
    + apply (f31g_ro_keep [(sp - 4560, sp)] mem3 m' HRO0 MU).
      intros x Hx. cbn. split; [unfold CG0f.kLowMemEnd in Hx; lia | exact I].
Qed.

End GlueF31.
