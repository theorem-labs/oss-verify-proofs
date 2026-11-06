(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths and module names changed; 717 of its 758 lines of code are new or changed and 110 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F31.v, with its module paths and module names changed; 753 of its 826 lines of code are new or changed and 685 lines of the source are left out. *)
(* lib/A/ACtlG/F32.v -- GLUE for stage seg_F32 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v,
   Hypothesis seg_F32).  Written by a Theorem Labs lane; single writer.  rule 24: no function proved (stage
   glue of a walk; the released-proof position of LLVMFuzzerTestOneInput was settled for this unit: At ossv/recipes c5e779efe8c (2026-10-31), no released proof of it outside this unit).
   Pattern: glue-pattern.md (a working note, not in this delivery) (G1-G5), worked example lib/A/ACtlG/A5.v.

   WHAT IT PROVES
     glue_seg_F32 : forall POST (j : nat),
       CF POST (ix_cut C_A828c8_at [Z.of_nat j]) -> CF POST (ix_cut C_A8285c_at [Z.of_nat j]) ->
       CF POST (ix_cut C_A827d8_at [Z.of_nat j]) /\ CF POST (ix_cut C_A82800_at [Z.of_nat j])
   with ACtl.v's own CF notation (SK := A.AE2k.tfib_sink_head, FP := []), i.e. exactly ACtl.v's seg_F32.  A two-entry
   segment (ACtl.v's note, ctrl's S_F32 Slot.v:218): both entries are proved, the entry 0x82800 first (f32g_e800) and
   the entry 0x827d8 from it (f32g_e7d8: its run ends at 0x82800).  The source segment is Seg/F32.v seg_F32 :1353
   (6a74d5929d2).

   THE RUNS LIFTED (lib/A/Prog/Seg/F32F.v, this worker's v1.9 footprint re-run of Seg/F32.v)
     F32F.f32_evt_a_F  0x827d8 -> 0x82800: the three branches to 0x82bf4 are not taken (reads only).
     F32F.f32_evt_n_F  0x82800, k <> 9: the branch to 0x828c8 (register-only).
     F32F.f32_evt_m_F_on  0x82800, k = 9: the two record-byte tests, then 0x828c8 (row not selected, memory
                       unchanged) or the two stores and the call of reac_box_catalogue at 0x82858, back at 0x8285c.
                       Route (C) form (a working branch b02bd9e287c): its callee premise
                       reac_box_catalogue_contract_F_on (premise-free; statement blob d3c4f4d7f9d, a working branch)
                       is discharged by a Theorem Labs lane's CLOSED theorem A.Prog.reac_box_catalogueF.reac_box_catalogue_F_holds_on
                       (Qed; file by path from a working branch 330e60af39d), and the whole run is lifted
                       once; the run has no shadow_rw premise (dropped), and the write permission of its store to
                       S(fr) + 4 (its rw_cells premise) is read off ctl_rt_C's cut_shadow (F) disjunct.

   THE PROOF (G1-G5) as in ACtlG/F31.v; the write set of the catalogue arm is the callee's frame [sp - 16, sp), the
   frame shadow byte S(fr) + 4 and the count variable [fr + 32, fr + 40) (awr_byte's stack and in_frames cases).
   The cut carries A.ACtlRtC.ctl_rt_C B ly3 S3 mem3: the entry reads cut_shadow's (F) disjunct for S(fr) + 4 and the
   run's region; the 0x8285c exit keeps both shadow_rw_on regions at the same state ly3 S3 (S(fr) + 4 written, every
   other shadow byte untouched) and reads the 392 frame-shadow bytes for FRAC from the kept cut_shadow region.

   SECTION HYPOTHESES: LAWS, ACtl.v's own (Section Ctl).  Nothing else.

   CLOSURE / SHADOWED NAMES: as ACtlG/F31.v (every Require with its FULL directory in the From clause; every
   lib/Reusable, lib/Lib and lib/Prog module through a full-path Module alias; lib/A modules Locate-checked).

   BUILD STATE: route (C) L3 switch (a Theorem Labs lane, recipe L3-recipe.md section 2 (a working note, not in this delivery)), built
   on working branches by cbrec (build of record, .prov under
   (internal path)).  Batch3's FRAC trailer word at 0x8285c is kept by f32g_frac_mem (the write
   set misses [fr + 4088, fr + 4096)); the other exits keep FRAC's memory.  Print Assumptions glue_seg_F32 = the Rocq
   primitives and functional_extensionality_dep. *)

From Coq Require Import ZArith List Lia Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YK04 YM05 YO09 YA0n YA0nR YG00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG01 YG0f YG0d YG0n YC5d YCbq YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v AE2k Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ACfn ACtlK ACtlCut ACtlCutP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ProgBridge ProgWorld ProgWorldVisWin ProgWorldVisFrame ProgWorldVisHeap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds rng_asan SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState Regs6ss Mem Frame PropExec Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_c reac_box_catalogueF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F32 F32F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlG Require Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* Full-path aliases for every lib/Reusable, lib/Lib and lib/Prog module this file names (a Theorem Labs lane 05:28Z: 175 image-A
   module names also exist under lib/A/Reusable, lib/U, lib/B, lib/A/Bz/Lib, lib/AZ/Lib (not in this delivery); a partial path can bind
   the wrong copy, e.g. Lib.Cells, whose cell is a different inductive in the Bz copy). *)
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
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LRG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module LEF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LCE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module ARF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module SIV := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotInv.
Module SG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F32.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.F32F.
Module CATc := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.
Module CATF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogueF.
Module CTP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCutP.
Module CT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ACtlCut.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.

Local Notation segs := A.AB1v.tfibsegs.
Local Notation rsegs := A.Img0.rsegs.
Local Notation RG := LinuxProcessSemantics.Riscv.Sem.reg_get.

(* =================================================================================================================
   1. Proof-internal helpers (over lib/Lib's memory predicates and the cut bundles; no frame-route name in a
   statement).  The first five are ACtlG/F31.v's, restated here (each stage in its own file; offered to the kit's
   writer a Theorem Labs lane, see the report). *)

Lemma f32g_spill : forall regs m off v A, CTP.spill regs m off v -> CT.rgv regs 9 A ->
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

Lemma f32g_app_of_in_app {rc : CM05.RunCeil} : forall lo len a,
  CG0f.in_app lo len -> lo <= a < lo + len -> ART.app_mem a.
Proof.
  intros lo len a [H0 [HL | [HH1 HH2]]] Ha; pose proof CG0f.ASAN_CEIL_range as [CR _];
    unfold ART.app_mem, ART.LOWMEM_END, ART.HIGHMEM_BEG, ART.APPMEM_END, CG0f.kLowShadowBeg, CG0f.kHighMemBeg in *;
    [left | right]; lia.
Qed.

Lemma f32g_stk_of_pres : forall (H : word -> bool) (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> CG0n.apresent H m a) -> FRM.stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 HP. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HP a Ha) as [_ [b Hb]]. unfold MEM.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold MEM.mrd. rewrite Hb. reflexivity.
Qed.

Lemma f32g_mrd_off_img : forall (m : word -> option byte) x b, 0 <= x < 2 ^ 64 -> ~ CG0d.in_img segs x ->
  MEM.mrd rsegs m (MEM.wa x) = Some b -> m (Z_to_bv 64 x) = Some b.
Proof.
  intros m x b Hx Hn H. unfold MEM.mrd, MEM.wa in H. destruct (m (Z_to_bv 64 x)) as [b'|] eqn:E; [exact H|].
  change (LPE.seg_rom rsegs (Z_to_bv 64 x)) with (CK11.seg_rom segs (Z_to_bv 64 x)) in H.
  rewrite (CCbq.seg_rom_none segs x Hx Hn) in H. discriminate H.
Qed.

(* The loaded image ends at 0x5fe000 (A.ProgBridge.rsegs_spans): no byte at or above it is an image byte. *)
Lemma f32g_hi_not_img : forall x, 0x5fe000 <= x -> ~ CG0d.in_img segs x.
Proof.
  intros x Hx (sg & Hin & Hr).
  apply (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs sg) in Hin.
  change A.AB1v.tfibsegs with A.Img0.rsegs in Hin. rewrite A.ProgBridge.rsegs_spans in Hin.
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin.
Qed.

(* A read-only byte is an image byte, so it lies below 0x5fe000. *)
Lemma f32g_ro_low : forall a : word, MEM.ro_addr rsegs a = true -> bv_unsigned a < 0x5fe000.
Proof.
  intros a H. destruct (Z_lt_le_dec (bv_unsigned a) 0x5fe000) as [Hl|Hge]; [exact Hl|]. exfalso.
  unfold MEM.ro_addr in H. change A.Img0.rsegs with A.AB1v.tfibsegs in H.
  rewrite (CCbq.find_segment_none segs (bv_unsigned a) (f32g_hi_not_img _ Hge)) in H. discriminate H.
Qed.

(* ro_agree across a write set W all of whose bytes lie at or above 0x5fe000. *)
Lemma f32g_ro_keep : forall W m m', A.ACtlK.ro_agree_at m -> FRM.munch W m m' ->
  (forall x, x < 0x5fe000 -> FRM.outside W x) -> A.ACtlK.ro_agree_at m'.
Proof.
  intros W m m' H MU HW a Ha. unfold MEM.mrd. rewrite (MU a).
  - exact (H a Ha).
  - apply HW. exact (f32g_ro_low a Ha).
Qed.

(* The core's shadow_addr (YG0f, SHADOW_OFF + a / 8) is ctrl's (AsanRT, a / 8 + ASAN_K). *)
Lemma f32g_shadow_eq : forall a, CG0f.shadow_addr a = ART.shadow_addr a.
Proof. intros a. unfold CG0f.shadow_addr, CG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K. ring. Qed.

(* FLS without its register-24 pin is FLSX, and back (ACtlCutP.v's two bundles). *)
Lemma f32g_flsx_of_fls : forall cx j phi fr regs m,
  ACtlCutP.FLS cx j phi fr regs m -> ACtlCutP.FLSX cx j phi fr regs m.
Proof.
  intros cx j phi fr regs m (HI & H18 & H22 & H23 & _ & H25 & Hrec & H152 & H280).
  exact (conj HI (conj H18 (conj H22 (conj H23 (conj H25 (conj Hrec (conj H152 H280))))))).
Qed.

Lemma f32g_fls_of_flsx : forall cx j phi fr regs m,
  ACtlCutP.FLSX cx j phi fr regs m -> CT.rgv regs 24 (SM.t_k (ACtlCut.c_in cx) j) ->
  ACtlCutP.FLS cx j phi fr regs m.
Proof.
  intros cx j phi fr regs m (HI & H18 & H22 & H23 & H25 & Hrec & H152 & H280) H24.
  exact (conj HI (conj H18 (conj H22 (conj H23 (conj H24 (conj H25 (conj Hrec (conj H152 H280)))))))).
Qed.

Section GlueF32.

(* ACtl.v's Section Ctl shape (its contexts, variables and the hypotheses this stage uses, in its order). *)
Context {fx : CK11.FPState} {rc : CM05.RunCeil} {LS : CO09.lib_shape}.
Variable B : CG0f.asyms.
Variable MT : CC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis LAWS : CG0d.AR_laws segs B.

(* ACtl.v's notation block, verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A827d8_at := (ACtlCutP.C_A827d8_at B).
Local Notation C_A82800_at := (ACtlCutP.C_A82800_at B).
Local Notation C_A828c8_at := (ACtlCutP.C_A828c8_at B).
Local Notation C_A8285c_at := (ACtlCutP.C_A8285c_at B).

(* The class-6 frame lies above the image: its base is ly_F (in_app, so >= 4096, layout_ok) plus the class-6 offset
   kFakeFramesOff + 6 * 2^20 + pos * 4096 with 0 <= pos (the fake stack's live list, Wf). *)
Lemma f32g_fr_hi : forall ly S W mem md pos, CG0n.AR segs B ly S W mem md -> In (6, pos) (CG01.frames S) ->
  6283264 <= CG0f.frame_addr ly 6 pos.
Proof.
  intros ly S W mem md pos HAR Hin.
  destruct HAR as (HARm & _).
  pose proof HARm as HL0. apply CG0n.am_layout in HL0. apply CG0f.lo_app in HL0.
  pose proof HARm as HW0. apply CG0n.am_wf in HW0. apply CG01.wf_fakestack in HW0. apply CG01.wfs_live in HW0.
  assert (HF : CG0f.in_app (CG0f.ly_F ly) CG0f.kFakeStackSize).
  { apply (proj1 (Forall_forall _ _) HL0 (CG0f.ly_F ly, CG0f.kFakeStackSize)).
    unfold CG0f.owned_extents. right. right. right. left. reflexivity. }
  pose proof (proj1 (Forall_forall _ _) HW0 (6, pos) Hin) as (_ & Hpos & _). cbn [fst snd] in Hpos.
  destruct HF as (HF0 & _).
  assert (E1 : Z.shiftl 1 CG00.kStackSizeLog = 1048576) by reflexivity.
  assert (E2 : CG00.fs_frame_bytes 6 = 4096) by reflexivity.
  unfold CG0f.frame_addr, CG0f.fs_frame_off. rewrite E1, E2. unfold CG0f.kFakeFramesOff. lia.
Qed.

(* FRAC's memory part across a write set W that misses the frame header words [fr, fr + 24), the fake-frame trailer
   word [fr + 4088, fr + 4096) (FRAC's last conjunct since Batch3), everything at or above the cut's sp (the spill
   area, its words at A + 16 / 24 / 304, the saved registers), given a frame shadow witness at the new memory. *)
Lemma f32g_frac_mem : forall cx fr sel regs m m' W,
  ACtlCutP.FRAC B cx fr sel regs m -> FRM.munch W m m' ->
  (forall x, CG0d.spZ regs <= x -> FRM.outside W x) -> (forall x, fr <= x < fr + 24 -> FRM.outside W x) ->
  (forall x, fr + 4088 <= x < fr + 4096 -> FRM.outside W x) ->
  (exists sh, MEM.bytes_at segs m' (ACtlCutP.Sfr fr) sh /\ length sh = Z.to_nat ACtlCutP.FRAME_SHADOW) ->
  ACtlCutP.FRAC B cx fr sel regs m'.
Proof.
  intros cx fr sel regs m m' W HF MU HWA HWh HWt Hsh'.
  destruct HF as (A & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAS & HspA & HfrA &
                  HA416 & HSsp & HSapp & Q304 & Q24 & Q16 & Qhdr & Qent & _ & Hsaved & Qtr).
  rewrite HspZ in HWA. unfold ACtlCutP.FRAME_BYTES in HfrA.
  assert (KB : forall a bs, MEM.bytes_at segs m a bs ->
            (forall x, a <= x < a + Z.of_nat (length bs) -> FRM.outside W x) -> MEM.bytes_at segs m' a bs).
  { intros a bs (Ha & Hl & Hb) Hd. split; [exact Ha|]. split; [exact Hl|].
    intros i Hi. unfold MEM.mrd. rewrite MU; [apply Hb; exact Hi|].
    rewrite MEM.wa_unsigned by lia. apply Hd. lia. }
  exists A, sp. repeat (split; [assumption|]).
  split; [apply KB; [exact Q304 | unfold ACtlCutP.q64 in *; rewrite MEM.length_le8; intros x Hx; apply HWA; lia]|].
  split; [apply KB; [exact Q24 | rewrite MEM.length_le8; intros x Hx; apply HWA; lia]|].
  split; [apply KB; [exact Q16 | rewrite MEM.length_le8; intros x Hx; apply HWA; lia]|].
  split; [apply KB; [exact Qhdr | rewrite MEM.length_le8; intros x Hx; apply HWh; lia]|].
  split; [apply KB; [exact Qent | rewrite MEM.length_le8; intros x Hx; apply HWh; lia]|].
  split; [exact Hsh'|].
  split; [apply KB; [exact Hsaved|]; intros x Hx; apply HWA; unfold ACtlCut.c_sp in *; lia|].
  apply KB; [exact Qtr | rewrite MEM.length_le8; intros x Hx; apply HWt; lia].
Qed.

(* FLSI, LK, FLSX and LT across a write set W that misses the spill area, the frame except the count variable
   [fr + 32, fr + 40), the turn's block and the input block; every addressable range that misses the count variable
   is kept, every count-variable byte is present at the new memory, and the registers the bundles read are kept
   (s1 9, s2 18, s5 21, s6 22, s7 23, s9 25).  A register-only run is the case W = [], m' = m. *)
Lemma f32g_keep : forall cx j phi fr regs regs' m m' W A,
  ACtlCutP.FLSI cx j fr regs m -> ACtlCutP.LK cx fr j regs m -> ACtlCutP.FLSX cx j phi fr regs m ->
  ACtlCutP.LT cx fr j regs m ->
  FRM.munch W m m' -> FRM.wmono rsegs m m' ->
  (forall p n, ART.addressable m p n -> (forall x, p <= x < p + n -> ~ (fr + 32 <= x < fr + 40)) ->
     ART.addressable m' p n) ->
  CK11.getr regs' 9 = CK11.getr regs 9 -> CK11.getr regs' 18 = CK11.getr regs 18 ->
  CK11.getr regs' 21 = CK11.getr regs 21 -> CK11.getr regs' 22 = CK11.getr regs 22 ->
  CK11.getr regs' 23 = CK11.getr regs 23 -> CK11.getr regs' 25 = CK11.getr regs 25 ->
  CT.rgv regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> FRM.outside W x) ->
  (forall x, fr <= x < fr + 32 \/ fr + 40 <= x < fr + 3136 -> FRM.outside W x) ->
  (forall x, fr + 32 <= x < fr + 40 -> FRM.outside W x \/ exists b, m' (MEM.wa x) = Some b) ->
  (50 <= ACtlCutP.flen cx j -> forall x, phi <= x < phi + ACtlCutP.flen cx j -> FRM.outside W x) ->
  (forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + Z.of_nat (length (ACtlCut.c_in cx)) -> FRM.outside W x) ->
  (ART.addressable m (ACtlCut.c_p cx) (ACtlCut.c_n cx) -> ART.addressable m' (ACtlCut.c_p cx) (ACtlCut.c_n cx)) ->
  ACtlCutP.FLSI cx j fr regs' m' /\ ACtlCutP.LK cx fr j regs' m' /\ ACtlCutP.FLSX cx j phi fr regs' m' /\
  ACtlCutP.LT cx fr j regs' m'.
Proof.
  intros cx j phi fr regs regs' m m' W A HI HLK HS HLT MU WM HAD E9 E18 E21 E22 E23 E25 Hr9 HA0 HA1
    HWA HWfr Hcnt HWB HWP HadPk.
  assert (KB : forall a bs, MEM.bytes_at segs m a bs ->
            (forall x, a <= x < a + Z.of_nat (length bs) -> FRM.outside W x) -> MEM.bytes_at segs m' a bs).
  { intros a bs (Ha & Hl & Hb) Hd. split; [exact Ha|]. split; [exact Hl|].
    intros i Hi. unfold MEM.mrd. rewrite MU; [apply Hb; exact Hi|].
    rewrite MEM.wa_unsigned by lia. apply Hd. lia. }
  assert (SP : forall off v, 0 <= off <= 400 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v Ho Hs. pose proof (f32g_spill regs m off v A Hs Hr9 HA0 HA1 Ho) as Hq.
    exists A. split; [unfold CT.rgv in Hr9 |- *; rewrite E9; exact Hr9|].
    unfold ACtlCutP.q64 in Hq |- *. apply KB; [exact Hq|]. rewrite MEM.length_le8. intros x Hx. apply HWA. lia. }
  assert (FR : forall a n, fr + 40 <= a -> a + n <= fr + 3136 -> forall x, a <= x < a + n -> FRM.outside W x)
    by (intros a n H1 H2 x Hx; apply HWfr; right; lia).
  assert (ADF : forall p n, ART.addressable m p n -> fr + 40 <= p -> ART.addressable m' p n)
    by (intros p n Hp Hge; apply (HAD p n Hp); intros x Hx; lia).
  destruct HI as (((H40 & H120 & H136 & H160 & H168 & H176 & H208 & H248p & HadO & Hbyp0 & Hadp0 & P184 & P256 &
                    P264 & P272 & P32) & H128 & Hstk & H144 & Had2691) & H216 & H224 & H248 & (Hadp & Hbyp) &
                  (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & CadF & CadI & C72 & C64 & C56 & C48)).
  assert (Hfr0 : 0 <= fr) by (destruct Hstk as (H0 & _); exact H0).
  destruct HLK as (Hj & H21 & HOUR).
  destruct HS as (_ & H18 & H22 & H23 & H25 & Hrec & H152 & H280).
  destruct HLT as ((HIDB & Hidok) & (HFGB & Hfgok) & (H104 & H112 & Hbody & Hadbody & HFI)).
  assert (HadP : ART.addressable m' (ACtlCut.c_p cx) (ACtlCut.c_n cx)) by exact (HadPk Hadp).
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
        split; [apply ADF; [exact HadO | lia]|].
        split; [apply KB; [exact Hbyp0 | exact HWP]|].
        split; [intros _; exact HadP|].
        split; [apply SP; [lia | exact P184]|].
        split; [apply SP; [lia | exact P256]|].
        split; [apply SP; [lia | exact P264]|].
        split; [apply SP; [lia | exact P272] | apply SP; [lia | exact P32]].
      + split; [apply SP; [lia | exact H128]|].
        split.
        * apply (FRM.stk_transport segs W m m' fr (fr + ACtlCutP.FRAME_BYTES) Hstk MU WM).
          intros x Hx. unfold ACtlCutP.FRAME_BYTES in Hx.
          destruct (Z_lt_le_dec x (fr + 32)) as [Hl|Hl]; [left; apply HWfr; left; lia|].
          destruct (Z_lt_le_dec x (fr + 40)) as [Hl2|Hl2]; [exact (Hcnt x ltac:(lia)) | left; apply HWfr; right; lia].
        * split; [apply SP; [lia | exact H144] | apply ADF; [exact Had2691 | lia]].
    - split; [apply SP; [lia | exact H216]|].
      split; [apply SP; [lia | exact H224]|].
      split; [apply SP; [lia | exact H248]|].
      split.
      + split; [exact HadP|]. apply KB; [exact Hbyp | exact HWP].
      + split; [apply SP; [lia | exact C256]|].
        split; [apply SP; [lia | exact C184]|].
        split; [apply SP; [lia | exact C192]|].
        split; [apply SP; [lia | exact C80]|].
        split; [apply SP; [lia | exact C88]|].
        split; [apply SP; [lia | exact C96]|].
        split; [apply SP; [lia | exact C272]|].
        split; [apply SP; [lia | exact C264]|].
        split; [apply ADF; [exact CadF | unfold ACtlCutP.fragb; lia]|].
        split; [apply ADF; [exact CadI | lia]|].
        split; [apply SP; [lia | exact C72]|]. split; [apply SP; [lia | exact C64]|].
        split; [apply SP; [lia | exact C56] | apply SP; [lia | exact C48]]. }
  assert (HLK' : ACtlCutP.LK cx fr j regs' m').
  { split; [exact Hj|]. split; [unfold CT.rgv in H21 |- *; rewrite E21; exact H21|].
    unfold ACtlCutP.OURb in HOUR |- *. apply KB; [exact HOUR|]. rewrite SM.OUR_length. apply FR; lia. }
  assert (HS' : ACtlCutP.FLSX cx j phi fr regs' m').
  { split; [exact HI'|].
    split; [unfold CT.rgv in H18 |- *; rewrite E18; exact H18|].
    split; [unfold CT.rgv in H22 |- *; rewrite E22; exact H22|].
    split; [unfold CT.rgv in H23 |- *; rewrite E23; exact H23|].
    split; [unfold CT.rgv in H25 |- *; rewrite E25; exact H25|].
    split.
    - intros H50. destruct (Hrec H50) as (Hp0 & Hp1 & Hg & Hpb & Hpl).
      split; [exact Hp0|]. split; [exact Hp1|].
      split.
      + apply KB; [exact Hg|]. unfold SM.t_g. rewrite SM.fr50_length. intros x Hx. apply (HWB H50). lia.
      + split; [|exact Hpl]. apply KB; [exact Hpb|]. intros x Hx. apply (HWB H50). unfold ACtlCutP.flen in *. lia.
    - split; [apply SP; [lia | exact H152] | apply SP; [lia | exact H280]]. }
  assert (HLT' : ACtlCutP.LT cx fr j regs' m').
  { split; [|split].
    - split; [|exact Hidok]. unfold ACtlCutP.IDBe in HIDB |- *. apply KB; [exact HIDB|].
      rewrite SG.f32_tID_length. unfold RIM.ID_SIZE. apply FR; lia.
    - split; [|exact Hfgok]. unfold ACtlCutP.FGBe in HFGB |- *. apply KB; [exact HFGB|].
      rewrite SG.f32_tFG_length. apply FR; lia.
    - split; [apply SP; [lia | exact H104]|]. split; [apply SP; [lia | exact H112]|].
      split.
      + apply KB; [exact Hbody|]. pose proof (SG.f32_fs_body_len (ACtlCut.c_in cx) (S j)) as Hl. apply FR; lia.
      + split; [apply ADF; [exact Hadbody | lia] | exact HFI]. }
  exact (conj HI' (conj HLK' (conj HS' HLT'))).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   2. The entry 0x82800 (C_A82800_at j): k <> 9 to 0x828c8; k = 9 to 0x828c8 or, through the catalogue, 0x8285c. *)
Lemma f32g_e800 : forall POST (j : nat),
  CF POST (ix_cut C_A828c8_at [Z.of_nat j]) -> CF POST (ix_cut C_A8285c_at [Z.of_nat j]) ->
  CF POST (ix_cut C_A82800_at [Z.of_nat j]).
Proof using LAWS.
  (* ACtl.v's seg_F32 does not take XN_LIB.  Without this clear, one tactic step below resolves a free Z -> Z
     instance to it, and `Proof using LAWS` then fails at Qed. *)
  clear XN_LIB.
  intros POST j HX8c8 HX85c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A82800_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HPerm & HFRAC & Hn & Hj & HHB & HFLSI & HLK & HFLS & HLT).
  pose proof HFLS as (_ & H18 & H22 & H23 & H24 & H25 & Hrec & H152 & H280).
  pose proof (f32g_flsx_of_fls _ _ _ _ _ _ HFLS) as HFLSX.
  pose proof HFRAC as (Asp & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA416 & HSsp & HSapp & _).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold ART.APPMEM_END in HSapp.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
  pose proof Hstatic as (_ & _ & Hceil & Hslo & _).
  pose proof CCbq.asan_consts as (HAC & _).
  unfold A.ACfn.LLVMF_STK in Hslo, Hpres.
  (* G3 *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A82800_at [Z.of_nat j])) with 0x82800.
  apply (CA0nR.SRr_xregs_eqv segs W3 (LRG.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x82800) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRG.xregs_eqv_sym _ _ (LRG.mkR_of_eqv regs3))].
  unfold LRG.mkR_of.
  (* the register-only exit at 0x828c8 (row not selected), shared by the k <> 9 arm and the k = 9 test arm *)
  assert (EXIT8c8 : forall (y10 y11 y12 : word) md',
            SM.t_rowsel (ACtlCut.c_in cx) j = false -> CK04.same_but_materialized md3 md' ->
            CA0n.SRr segs W3
              (mkCfg (LMS.MS (FRM.mkR (RG regs3 1) (RG regs3 2) (RG regs3 3) (RG regs3 4) (RG regs3 5) (RG regs3 6)
                                    (RG regs3 7) (RG regs3 8) (RG regs3 9) y10 y11 y12 (RG regs3 13)
                                    (RG regs3 14) (RG regs3 15) (RG regs3 16) (RG regs3 17) (RG regs3 18)
                                    (RG regs3 19) (RG regs3 20) (RG regs3 21) (RG regs3 22) (RG regs3 23)
                                    (RG regs3 24) (RG regs3 25) (RG regs3 26) (RG regs3 27) (RG regs3 28)
                                    (RG regs3 29) (RG regs3 30) (RG regs3 31))
                             CK11.fp_regs (Z_to_bv 64 0x828c8) CK11.fp_csr None mem3 (CK11.seg_rom segs)) md')
              (POST cx)).
  { intros y10 y11 y12 md' Hrow Hsbm.
    set (R1 := FRM.mkR (RG regs3 1) (RG regs3 2) (RG regs3 3) (RG regs3 4) (RG regs3 5) (RG regs3 6)
                      (RG regs3 7) (RG regs3 8) (RG regs3 9) y10 y11 y12 (RG regs3 13)
                      (RG regs3 14) (RG regs3 15) (RG regs3 16) (RG regs3 17) (RG regs3 18)
                      (RG regs3 19) (RG regs3 20) (RG regs3 21) (RG regs3 22) (RG regs3 23)
                      (RG regs3 24) (RG regs3 25) (RG regs3 26) (RG regs3 27) (RG regs3 28)
                      (RG regs3 29) (RG regs3 30) (RG regs3 31)).
    change (CA0n.SRr segs W3 (CG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A828c8_at [Z.of_nat j])) R1 mem3 md')
              (POST cx)).
    assert (K2 : CK11.getr R1 2 = CK11.getr regs3 2) by reflexivity.
    assert (K3 : CK11.getr R1 3 = CK11.getr regs3 3) by reflexivity.
    assert (K4 : CK11.getr R1 4 = CK11.getr regs3 4) by reflexivity.
    assert (K8 : CK11.getr R1 8 = CK11.getr regs3 8) by reflexivity.
    assert (K9 : CK11.getr R1 9 = CK11.getr regs3 9) by reflexivity.
    assert (K18 : CK11.getr R1 18 = CK11.getr regs3 18) by reflexivity.
    assert (K19 : CK11.getr R1 19 = CK11.getr regs3 19) by reflexivity.
    assert (K21 : CK11.getr R1 21 = CK11.getr regs3 21) by reflexivity.
    assert (K22 : CK11.getr R1 22 = CK11.getr regs3 22) by reflexivity.
    assert (K23 : CK11.getr R1 23 = CK11.getr regs3 23) by reflexivity.
    assert (K24 : CK11.getr R1 24 = CK11.getr regs3 24) by reflexivity.
    assert (K25 : CK11.getr R1 25 = CK11.getr regs3 25) by reflexivity.
    assert (K26 : CK11.getr R1 26 = CK11.getr regs3 26) by reflexivity.
    destruct (f32g_keep cx j phi fr regs3 R1 mem3 mem3 [] Asp HFLSI HLK HFLSX HLT (FRM.munch_refl [] mem3)
                (FRM.wmono_refl rsegs mem3) (fun p n H _ => H) K9 K18 K21 K22 K23 K25 R9 ltac:(lia) ltac:(lia)
                (fun _ _ => I) (fun _ _ => I) (fun _ _ => or_introl I) (fun _ _ _ => I) (fun _ _ => I)
                (fun H => H))
      as (HI' & HLK' & HS' & HLT').
    apply (HX8c8 cx [Z.of_nat j] fr k ly3 S3 W3 R1 mem3 md' HB).
    - eapply (CCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
        [exact HJ | intros x _; reflexivity | apply CK1b.mem_grows_refl | intros x _; reflexivity
        | exact Hsbm | intros a Ha; destruct Ha].
    - exact HF.
    - exact HL.
    - exact Hk.
    - cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A828c8_at ACtlCutP.ixn nth].
      rewrite Nat2Z.id. split; [reflexivity|].
      exists phi.
      split; [exact HPerm|].
      split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R1 mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
      split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HI'|].
      split; [exact HLK'|].
      split; [apply f32g_fls_of_flsx; [exact HS' | unfold CT.rgv in H24 |- *; rewrite K24; exact H24]|].
      split; [exact Hrow | exact HLT'].
    - exact Hrt. }
  destruct (Z.eq_dec (SM.t_k (ACtlCut.c_in cx) j) 9) as [Ek|Ek].
  2: {
    (* k <> 9: the branch at 0x82804 is taken to 0x828c8; register-only, the empty footprint *)
    eapply (CA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 A.ACtlG.Kit.kit_RNG0 _ (POST cx)).
    { apply A.ProgBridge.fevt_of_evtF.
      apply (SF.f32_evt_n_F A.ACtlG.Kit.kit_RNG0) with (k := SM.t_k (ACtlCut.c_in cx) j);
        [exact H24 | apply SG.f32_k_range | exact Ek]. }
    { intros ? ? Hrng0. unfold A.ACtlG.Kit.kit_RNG0 in Hrng0. destruct Hrng0. }
    intros ms' md' HQ Hsbm. destruct HQ as (y10 & Ems). subst ms'.
    exact (EXIT8c8 y10 (RG regs3 11) (RG regs3 12) md' (SG.f32_rowsel_k _ j Ek) Hsbm). }
  (* k = 9: the row arm reads the record, so 50 <= len_j (f32_k_big) and FLS's record part holds *)
  assert (Hl50 : 50 <= ACtlCutP.flen cx j) by (unfold ACtlCutP.flen; apply SG.f32_k_big; lia).
  destruct (Hrec Hl50) as (Hp0 & Hp1 & Htg & Hph & Hphl).
  pose proof HFLSI as (((Hsp40 & _ & _ & _ & _ & _ & _ & _ & Had2624 & _) & _ & Hstkfr & _ & Had2691) &
                       _ & _ & _ & _ & HFLC).
  pose proof HHB as (Hphinz & Hphiad).
  assert (Hsz : A.ACtlK.a_size (ACtlCutP.flen cx j) = ACtlCutP.flen cx j) by (unfold A.ACtlK.a_size; lia).
  rewrite Hsz in Hphiad.
  pose proof (SG.f32_phi_length (ACtlCut.c_in cx) j) as Hplen.
  assert (Hkbig : 50 <= SM.t_len (ACtlCut.c_in cx) j) by exact Hl50.
  (* the frame: its base, bounds and app band (frames_bounds, the frame law, f32g_fr_hi) *)
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (CG01.frames S3)) by (rewrite HF; left; reflexivity).
  destruct (CCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & Hfapp).
  assert (Efr : fr = CG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) ltac:(left; reflexivity)). unfold CG0f.frame_addr. rewrite EF. reflexivity. }
  assert (EFB : CG00.fs_frame_bytes 6 = 4096) by reflexivity.
  pose proof (f32g_fr_hi ly3 S3 W3 mem3 md3 _ HAR Hin6) as Hfrhi.
  rewrite <- Efr in Hf4096, Hfceil, Hfapp, Hfrhi. rewrite EFB in Hfceil, Hfapp.
  assert (Happ : forall a, fr <= a < fr + 4096 -> ART.app_mem a)
    by (intros a Ha; exact (f32g_app_of_in_app fr 4096 a Hfapp Ha)).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfr32; clear; Z.div_mod_to_equations; lia).
  assert (Esp : bv_unsigned (RG regs3 2) = sp).
  { change (RG regs3 2 = Z_to_bv 64 sp) in R2. rewrite R2. apply LMS.unsigned_lit. lia. }
  (* the frame shadow byte S(fr) + 4 (the shadow of the count variable) *)
  assert (Hin4 : ART.in_shadow (ACtlCutP.Sfr fr + 4)).
  { pose proof (SG.f32_shadow_in fr 0 Hfr8 ltac:(lia)) as Hs. unfold SIV.Sfr in Hs. rewrite Z.add_0_r in Hs.
    unfold ACtlCutP.Sfr. rewrite <- Hs. apply ARF.shadow_of_app. apply Happ. lia. }
  pose proof Hrt as (HAC0 & Hcut & Himg & HRO0).
  (* ctl_rt_C's (F) disjunct: the owned class-6 frame's shadow [S(fr), S(fr) + 512) *)
  assert (HFsh : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 -> A.ACtlRtC.cut_shadow B ly3 S3 a).
  { intros a Ha. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin6|].
    rewrite <- Efr, EFB. change (4096 / 8) with 512.
    unfold ACtlCutP.Sfr, CG0f.shadow_addr, CG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K in Ha |- *. lia. }
  (* the two shadow bytes and the two record bytes of the turn's block *)
  destruct (ARF.meta_byte mem3 (phi + 16) 1
              (ARF.addressable_sub mem3 phi (ACtlCutP.flen cx j) 16 1 Hphiad ltac:(lia) ltac:(lia) ltac:(lia))
              ltac:(lia)) as (b16 & Rc16 & Hok16 & Hin16).
  destruct (ARF.meta_byte mem3 (phi + 17) 1
              (ARF.addressable_sub mem3 phi (ACtlCutP.flen cx j) 17 1 Hphiad ltac:(lia) ltac:(lia) ltac:(lia))
              ltac:(lia)) as (b17 & Rc17 & Hok17 & Hin17).
  set (v16 := bv_unsigned (nth 16 (SM.t_phi (ACtlCut.c_in cx) j) (Z_to_bv 8 0))).
  set (v17 := bv_unsigned (nth 17 (SM.t_phi (ACtlCut.c_in cx) j) (Z_to_bv 8 0))).
  (* the frame shadow bytes, the count variable's cells and the spill [A + 40] *)
  pose proof HFRAC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                       _ & (sh & Hshb & Hshl) & _).
  unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in Hshl. change (3136 / 8) with 392 in Hshl.
  assert (HST40 : FRM.stk segs mem3 fr (fr + 40))
    by (destruct (FRM.stk_split segs mem3 fr (fr + 40) (fr + ACtlCutP.FRAME_BYTES) Hstkfr
                    ltac:(unfold ACtlCutP.FRAME_BYTES; lia)) as (H1 & _); exact H1).
  destruct (FRM.stk_carve segs mem3 fr (fr + 40) 8 HST40 ltac:(lia)) as (_ & junk & RWfr0).
  pose proof (f32g_spill _ _ _ _ Asp Hsp40 R9 ltac:(lia) ltac:(lia) ltac:(lia)) as Q40.
  (* the visible ranges *)
  pose proof (A.ProgWorldVisWin.win_vis B) as WV.
  unfold A.ProgWorld.win_vis_stmt in WV.
  pose proof (A.ProgWorldVisFrame.frame_vis B) as FV.
  unfold A.ProgWorld.frame_vis_stmt in FV. specialize (FV LAWS).
  pose proof (A.ProgWorldVisHeap.heap_vis B) as HV.
  unfold A.ProgWorld.heap_vis_stmt in HV. specialize (HV LAWS).
  pose proof (A.ProgWorldVisHeap.heap_sh_vis B) as HSV.
  unfold A.ProgWorld.heap_sh_vis_stmt in HSV. specialize (HSV LAWS).
  assert (Hph3 : In (phi, ACtlCutP.flen cx j) (CG0d.ablocks B ly3 S3))
    by (eapply Permutation_in; [symmetry; exact HPerm | apply in_or_app; right; left; reflexivity]).
  pose proof (CCbq.req_size_pos (ACtlCutP.flen cx j) ltac:(lia)) as Hrq.
  set (RNG := A.ProgBridge.RNG_W (CA0n.w_H W3)).
  assert (Vwin : forall a n, ACtlCut.c_sp cx - 32768 <= a -> a + n <= ACtlCut.c_sp cx -> LEF.rng RNG a n).
  { intros a n H1 H2. apply A.ProgBridge.rng_of_visible. exact (WV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a n HJ H1 H2). }
  assert (Vfr : forall a n, fr <= a -> a + n <= fr + 4096 -> LEF.rng RNG a n).
  { intros a n H1 H2. apply A.ProgBridge.rng_of_visible. rewrite Efr in H1, H2.
    exact (proj1 (FV _ _ _ _ _ _ _ a n HAR Hin6 H1 ltac:(rewrite EFB; exact H2))). }
  assert (Vhp : forall a, phi <= a < phi + 50 -> LEF.rng RNG a 1).
  { intros a Ha. apply A.ProgBridge.rng_of_visible. exact (HV _ _ _ _ _ _ _ a 1 HAR Hph3 ltac:(lia) ltac:(lia)). }
  assert (Vhs : forall a, phi <= a < phi + 50 -> LEF.rng RNG (Z.shiftr a 3 + ART.ASAN_K) 1).
  { intros a Ha. destruct (HSV _ _ _ _ _ _ _ a 1 HAR Hph3 ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 | Hvis]; [lia|].
    apply A.ProgBridge.rng_of_visible.
    unfold A.Prog.rng_asan.sh_al8_lo, A.Prog.rng_asan.sh_al8_hi in Hvis.
    replace (a + 1 - 1) with a in Hvis by lia.
    assert (Esh : Z.shiftr a 3 + ART.ASAN_K = ART.shadow_addr a)
      by (unfold ART.shadow_addr; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite Esh. apply (A.ProgBridge.range_visible_sub _ _ _ _ _ Hvis); Z.div_mod_to_equations; lia. }
  assert (Vimg : forall a n, 0x10000 <= a -> a + n <= 0x5fe000 -> 0 <= n -> LEF.rng RNG a n).
  { intros a n H1 H2 H3. apply A.ProgBridge.rng_of_visible.
    apply (A.ProgBridge.range_visible_sub _ _ _ _ _ (A.ProgBridge.img_vis_W W3));
      unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI; lia. }
  (* G4: the lift of the k = 9 arm (it writes memory: SRr_fevt_hid) *)
  eapply (CA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF.
    eapply (SF.f32_evt_m_F_on CATF.reac_box_catalogue_F_holds_on RNG) with (Asp := Asp) (fr := fr) (phi := phi)
      (spv := sp) (lo := ACtlCut.c_sp cx - 32768) (v16 := v16) (v17 := v17) (b16 := b16) (b17 := b17)
      (b4 := nth 4 sh (Z_to_bv 8 0)) (junk := junk).
    - exact R2.
    - exact R9.
    - exact R19.
    - exact H23.
    - unfold CT.rgv in H24. rewrite Ek in H24. exact H24.
    - exact R26.
    - lia.
    - exact Hp1.
    - apply SG.f32_rd1. destruct Rc16 as (_ & Hb16). cbn [LCE.cells_bytes LCE.cbytes] in Hb16.
      rewrite app_nil_r in Hb16. exact Hb16.
    - destruct Hok16 as [H|H]; [left; exact H | right; lia].
    - apply SG.f32_rd1. destruct Rc17 as (_ & Hb17). cbn [LCE.cells_bytes LCE.cbytes] in Hb17.
      rewrite app_nil_r in Hb17. exact Hb17.
    - destruct Hok17 as [H|H]; [left; exact H | right; lia].
    - subst v16. rewrite SG.f32_byte_lit.
      pose proof (SG.f32_rd_nth mem3 phi (SM.t_phi (ACtlCut.c_in cx) j) 16 Hph ltac:(rewrite Hplen; lia)) as HH.
      change (Z.of_nat 16) with 16 in HH. exact HH.
    - exact (SG.f32_bz_range _).
    - subst v17. rewrite SG.f32_byte_lit.
      pose proof (SG.f32_rd_nth mem3 phi (SM.t_phi (ACtlCut.c_in cx) j) 17 Hph ltac:(rewrite Hplen; lia)) as HH.
      change (Z.of_nat 17) with 17 in HH. exact HH.
    - exact (SG.f32_bz_range _).
    - apply ARF.ro_c8. exact Q40.
    - apply SG.f32_rw1.
      + pose proof (SG.f32_ba_nth mem3 (ACtlCutP.Sfr fr) sh 4 Hshb ltac:(lia)) as HB4.
        change (Z.of_nat 4) with 4 in HB4. exact HB4.
      + exact (proj1 (Hcut _ (HFsh (ACtlCutP.Sfr fr + 4) ltac:(lia)) Hin4)).
    - replace (fr + 32) with (fr + 40 - Z.of_nat 8) by lia. exact RWfr0.
    - lia.
    - exact Hfr8.
    - exact Hfrhi.
    - exact HfrA.
    - lia.
    - unfold SIV.Sfr, ART.shadow_addr, ART.ASAN_K. Z.div_mod_to_equations. lia.
    - unfold SIV.Sfr, ART.shadow_addr, ART.ASAN_K. pose proof (CG0f.ASAN_CEIL_range) as [CR _].
      Z.div_mod_to_equations. lia.
    - lia.
    - unfold ART.HIGHMEM_BEG. lia.
    - lia.
    - exact HspA.
    - lia.
    - left. lia.
    - destruct (ARF.app_ivl_meta fr (fr + 4096) (ACtlCutP.Sfr fr + 4) Happ Hin4) as [Hq|Hq];
        unfold ACtlCutP.Sfr in Hq; unfold SIV.Sfr; [left | right]; lia.
    - apply (f32g_stk_of_pres (CA0n.w_H W3)); [lia | lia |]. intros a Ha. apply Hpres. lia.
    - intros a Ha. apply Happ. lia.
    - exact HAC0.
    - apply Vhs. lia.
    - apply Vhp. lia.
    - apply Vhs. lia.
    - apply Vhp. lia.
    - apply A.ProgBridge.rng_of_visible. unfold SIV.Sfr.
      split; [unfold ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia|].
      split; [unfold ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia|].
      intros a Ha. replace a with (ART.shadow_addr (CG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)) + 4)
        by (rewrite <- Efr; lia).
      destruct (CG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6) as (_ & _ & _ & Hsh).
      pose proof (proj1 (proj1 (Hsh 4 ltac:(rewrite EFB; lia)))) as Hh.
      rewrite (f32g_shadow_eq (CG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx))) in Hh. exact Hh.
    - apply Vwin; lia.
    - apply Vfr; lia.
    - apply Vwin; lia.
    - apply Vimg; unfold ART.GOT_CELL_K; lia.
    - apply Vimg; unfold ART.CELL_K; lia. }
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  (* G5 *)
  intros ms' md' HQ Hhid Hsbm.
  destruct HQ as [ (y10 & y11 & y12 & Ems & Hbad)
                 | (y11 & y12 & m' & Ems & Ev16 & Ev17 & MUc & WMc & STc & BAc & MRc) ].
  - (* the row is not selected: 0x828c8, memory unchanged *)
    subst ms'.
    apply (EXIT8c8 y10 y11 y12 md'); [|exact Hsbm].
    destruct Hbad as [Hb|Hb]; [exact (SG.f32_rowsel_16 _ j Ek Hb) | exact (SG.f32_rowsel_17 _ j Ek Hb)].
  - (* the catalogue returned: 0x8285c, memory m' *)
    subst ms'.
    unfold SIV.Sfr in MUc, MRc. change (ART.shadow_addr fr) with (ACtlCutP.Sfr fr) in MUc, MRc.
    match goal with |- context [LMS.MS ?R _ _ _ _ _ _] => set (R1 := R) end.
    change (CA0n.SRr segs W3 (CG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A8285c_at [Z.of_nat j])) R1 m' md')
              (POST cx)).
    assert (K2 : CK11.getr R1 2 = CK11.getr regs3 2) by reflexivity.
    assert (K3 : CK11.getr R1 3 = CK11.getr regs3 3) by reflexivity.
    assert (K4 : CK11.getr R1 4 = CK11.getr regs3 4) by reflexivity.
    assert (K8 : CK11.getr R1 8 = CK11.getr regs3 8) by reflexivity.
    assert (K9 : CK11.getr R1 9 = CK11.getr regs3 9) by reflexivity.
    assert (K18 : CK11.getr R1 18 = CK11.getr regs3 18) by reflexivity.
    assert (K19 : CK11.getr R1 19 = CK11.getr regs3 19) by reflexivity.
    assert (K21 : CK11.getr R1 21 = CK11.getr regs3 21) by reflexivity.
    assert (K22 : CK11.getr R1 22 = CK11.getr regs3 22) by reflexivity.
    assert (K23 : CK11.getr R1 23 = CK11.getr regs3 23) by reflexivity.
    assert (K25 : CK11.getr R1 25 = CK11.getr regs3 25) by reflexivity.
    assert (K26 : CK11.getr R1 26 = CK11.getr regs3 26) by reflexivity.
    assert (K10 : CK11.getr R1 10 = Z_to_bv 64 CATc.BOX_CATALOGUE) by reflexivity.
    assert (K24 : CK11.getr R1 24 = Z_to_bv 64 (fr + 32)) by reflexivity.
    set (W3w := [(sp - 16, sp); (ACtlCutP.Sfr fr + 4, ACtlCutP.Sfr fr + 5); (fr + 32, fr + 40)]).
    (* where the write set lies: the callee frame is high stack, S(fr) + 4 is a shadow byte, the count variable
       sits in the frame; everything else the exit reads is apart *)
    assert (HSfr : ACtlCutP.Sfr fr + 5 <= ART.HIGHMEM_BEG)
      by (unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K, ART.HIGHMEM_BEG; Z.div_mod_to_equations; lia).
    assert (HSfrlo : 0x5fe000 <= ACtlCutP.Sfr fr)
      by (unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia).
    assert (OutApp : forall x, ART.app_mem x -> ~ (fr + 32 <= x < fr + 40) -> x < sp - 16 -> FRM.outside W3w x).
    { intros x Hx Hnc Hlt. subst W3w. cbn [FRM.outside]. split; [lia|]. split; [|split; [exact Hnc | exact I]].
      intros Hc. apply (ARF.app_not_shadow x Hx). replace x with (ACtlCutP.Sfr fr + 4) by lia. exact Hin4. }
    assert (OutHi : forall x, sp <= x -> FRM.outside W3w x).
    { intros x Hx. subst W3w. cbn [FRM.outside]. unfold ART.HIGHMEM_BEG in HSfr.
      split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (OutSh : forall x, ART.in_shadow x -> x <> ACtlCutP.Sfr fr + 4 -> FRM.outside W3w x).
    { intros x Hx Hne. pose proof (SG.in_shadow_bnd x Hx) as Hb. subst W3w. cbn [FRM.outside].
      unfold ART.LOWMEM_END, ART.HIGHMEM_BEG in Hb.
      split; [lia|]. split; [lia|]. split; [|exact I].
      intros Hc. exact (ARF.app_not_shadow x (Happ x ltac:(lia)) Hx). }
    (* the turn's block and the input block: live blocks, below alloc_ceiling and apart from the frame *)
    destruct (CG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) HAR Hph3) as (_ & _ & Hphceil & _).
    pose proof (CCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 phi (ACtlCutP.flen cx j) 6 (ACtlCut.c_fpos cx)
                  HAR Hph3 Hin6) as Hsepph.
    unfold CG0f.zdisjoint in Hsepph. cbn [fst snd] in Hsepph. rewrite <- Efr, EFB in Hsepph.
    assert (Hphapp : forall x, phi <= x < phi + ACtlCutP.flen cx j -> ART.app_mem x).
    { intros x Hx. replace x with (phi + (x - phi)) by lia.
      exact (proj1 (proj2 (proj2 (proj2 Hphiad)) (x - phi) ltac:(lia))). }
    pose proof HB as ((_ & _ & _ & _ & Hpn & Hlen & _) & _).
    assert (HPblk : ACtlCut.c_n cx = 0 \/
                    (ACtlCut.c_p cx + ACtlCut.c_n cx <= ACtlCut.c_sp cx - 32768 /\
                     (ACtlCut.c_p cx + ACtlCut.c_n cx <= fr \/ fr + 4096 <= ACtlCut.c_p cx))).
    { destruct Hpn as [(Hn0 & _) | (Hn0 & Hpin)]; [left; exact Hn0 | right].
      assert (Hpin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (CG0d.ablocks B ly3 S3))
        by (eapply Permutation_in; [symmetry; exact HPerm | apply in_or_app; left; exact Hpin]).
      destruct (CG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hpin3) as (_ & _ & Hpc & _).
      pose proof (CCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)).
      pose proof (CCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx) HAR Hpin3 Hin6)
        as Hsep.
      unfold CG0f.zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite <- Efr, EFB in Hsep. lia. }
    pose proof HFLSI as (_ & _ & _ & _ & (HadP & _) & _).
    assert (HpPapp : forall x, ACtlCut.c_p cx <= x < ACtlCut.c_p cx + ACtlCut.c_n cx -> ART.app_mem x).
    { intros x Hx. replace x with (ACtlCut.c_p cx + (x - ACtlCut.c_p cx)) by lia.
      exact (proj1 (proj2 (proj2 (proj2 HadP)) (x - ACtlCut.c_p cx) ltac:(lia))). }
    (* addressable ranges that miss the count variable keep their shadow *)
    assert (HAD : forall p n, ART.addressable mem3 p n -> (forall x, p <= x < p + n -> ~ (fr + 32 <= x < fr + 40)) ->
              ART.addressable m' p n).
    { intros p n Hp Hnc. apply (SG.addr_keep W3w mem3 m' p n Hp MUc). intros i Hi.
      pose proof (ARF.addressable_app _ _ _ Hp (p + i) ltac:(lia)) as Hai.
      apply OutSh; [exact (ARF.shadow_of_app _ Hai)|].
      intros He. apply (Hnc (p + i) ltac:(lia)). apply (SG.f32_shadow_eq_inv fr (p + i) Hfr8). exact He. }
    (* every written byte is present at m' (they are off the image) *)
    assert (Hcnt : forall x, fr + 32 <= x < fr + 40 -> exists b, m' (MEM.wa x) = Some b).
    { intros x Hx. destruct (SG.ba_some m' (fr + 32) _ (x - (fr + 32)) BAc
                               ltac:(rewrite MEM.length_le8; cbn; lia)) as (b & Hb).
      replace (fr + 32 + (x - (fr + 32))) with x in Hb by lia.
      exists b. exact (f32g_mrd_off_img m' x b ltac:(lia) (f32g_hi_not_img x ltac:(lia)) Hb). }
    destruct (f32g_keep cx j phi fr regs3 R1 mem3 m' W3w Asp HFLSI HLK HFLSX HLT MUc WMc HAD
                K9 K18 K21 K22 K23 K25 R9 ltac:(lia) ltac:(lia)
                ltac:(intros x Hx; apply OutHi; lia)
                ltac:(intros x Hx; apply OutApp; [apply Happ | | ]; lia)
                ltac:(intros x Hx; right; exact (Hcnt x Hx))
                ltac:(intros _ x Hx; apply OutApp; [apply Hphapp | | ]; lia)
                ltac:(intros x Hx; rewrite <- Hlen in Hx; destruct HPblk as [Hn0 | (Hpc & Hpf)]; [lia|];
                      apply OutApp; [apply HpPapp | | ]; lia)
                ltac:(intros Hp; apply (HAD _ _ Hp); intros x Hx Hc; destruct HPblk as [Hn0 | (Hpc & Hpf)]; lia))
      as (HI' & HLK' & HS' & HLT').
    (* both shadow_rw_on regions at m' (same state ly3 S3): S(fr) + 4 holds 0 (MRc), every other shadow byte is
       untouched *)
    assert (Hkeep : forall P, A.ShadowRwOn.shadow_rw_on P mem3 -> A.ShadowRwOn.shadow_rw_on P m').
    { intros P HP x Hp Hx. destruct (Z.eq_dec x (ACtlCutP.Sfr fr + 4)) as [->|Hne].
      - split; [apply WMc; exact (proj1 (HP _ Hp Hx)) | exists (Z_to_bv 8 0); exact MRc].
      - pose proof (ARF.in_shadow_range x Hx) as Hxr.
        assert (Em : m' (MEM.wa x) = mem3 (MEM.wa x)).
        { apply MUc. rewrite MEM.wa_unsigned by lia. exact (OutSh x Hx Hne). }
        destruct (HP x Hp Hx) as (Hw & bx & Hbx). split.
        + unfold wview. rewrite Em. exact Hw.
        + exists bx. unfold MEM.mrd. rewrite Em. exact Hbx. }
    pose proof (Hkeep _ Hcut) as Hcut'. pose proof (Hkeep _ Himg) as Himg'.
    apply (HX85c cx [Z.of_nat j] fr k ly3 S3 W3 R1 m' md' HB).
    + (* journal: the callee frame (stack case), the frame shadow byte and the count variable (in_frames) *)
      eapply (CCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low)
        with (Wr := fun a : Z => (sp - 16 <= a < sp) \/ (ACtlCutP.Sfr fr + 4 <= a < ACtlCutP.Sfr fr + 5) \/
                                 (fr + 32 <= a < fr + 40)).
      * exact HJ.
      * intros x Hx. unfold CK04.mrestrict. rewrite (MUc x); [reflexivity|].
        cbn [FRM.outside]. repeat split; try exact I; intros Hc; apply Hx; tauto.
      * intros x Hx. unfold CK04.mrestrict in *. destruct (CA0n.w_H W3 x) eqn:Eh; [exact Hx|].
        pose proof (bv_unsigned_in_range 64 x) as Hrx. unfold bv_modulus in Hrx.
        change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrx.
        destruct (Z_lt_le_dec (bv_unsigned x) (sp - 16)) as [L1|L1];
          [|destruct (Z_lt_le_dec (bv_unsigned x) sp) as [L2|L2]].
        -- destruct (Z.eq_dec (bv_unsigned x) (ACtlCutP.Sfr fr + 4)) as [E4|E4].
           ++ pose proof (f32g_mrd_off_img m' (bv_unsigned x) (Z_to_bv 8 0) ltac:(lia)
                            (f32g_hi_not_img (bv_unsigned x) ltac:(lia)) ltac:(rewrite E4; exact MRc)) as Hm'.
              rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hm'. congruence.
           ++ destruct (Z_lt_le_dec (bv_unsigned x) (fr + 32)) as [L3|L3];
                [|destruct (Z_lt_le_dec (bv_unsigned x) (fr + 40)) as [L4|L4]].
              ** rewrite (MUc x); [exact Hx|]. cbn [FRM.outside]. repeat split; try exact I; lia.
              ** destruct (Hcnt (bv_unsigned x) ltac:(lia)) as (b & Hb). unfold MEM.wa in Hb.
                 rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb. congruence.
              ** rewrite (MUc x); [exact Hx|]. cbn [FRM.outside]. repeat split; try exact I; lia.
        -- destruct STc as (_ & _ & Hst). destruct (Hst (bv_unsigned x) ltac:(lia)) as (_ & b & Hb).
           pose proof (f32g_mrd_off_img m' (bv_unsigned x) b ltac:(lia)
                         (f32g_hi_not_img (bv_unsigned x) ltac:(lia)) Hb) as Hm'.
           rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hm'. congruence.
        -- rewrite (MUc x); [exact Hx|]. cbn [FRM.outside]. unfold ART.HIGHMEM_BEG in HSfr.
           repeat split; try exact I; lia.
      * exact Hhid.
      * exact Hsbm.
      * intros a [Ha | [Ha | Ha]].
        -- left. unfold A.ACfn.LLVMF_STK. lia.
        -- right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
           right. unfold CG0n.in_zr. cbn [fst snd]. rewrite <- Efr, EFB, f32g_shadow_eq.
           unfold ACtlCutP.Sfr in Ha. lia.
        -- right. right. right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|].
           left. unfold CG0n.in_zr. cbn [fst snd]. rewrite <- Efr, EFB. lia.
    + exact HF.
    + exact HL.
    + exact Hk.
    + (* the exit body, C_A8285c_at, at the same turn j *)
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A8285c_at ACtlCutP.ixn nth].
      rewrite Nat2Z.id. split; [reflexivity|].
      exists phi.
      split; [exact HPerm|].
      split.
      { apply (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R1 m'); [| exact K2 | exact K3 | exact K4 | exact K8
          | exact K9 | exact K19 | exact K26].
        apply (f32g_frac_mem cx fr fr regs3 mem3 m' W3w HFRAC MUc).
        - intros x Hx. apply OutHi. rewrite HspZ in Hx. exact Hx.
        - intros x Hx. apply OutApp; [apply Happ | |]; lia.
        - intros x Hx. apply OutApp; [apply Happ | |]; lia.
        - assert (Hstk' : FRM.stk segs m' (ACtlCutP.Sfr fr) (ACtlCutP.Sfr fr + 392)).
          { split; [unfold ACtlCutP.Sfr, ART.shadow_addr, ART.ASAN_K; Z.div_mod_to_equations; lia|].
            split; [unfold ART.HIGHMEM_BEG in HSfr; lia|].
            intros a Ha. apply (Hcut' a); [apply HFsh; lia|]. unfold ACtlCutP.Sfr in Ha |- *.
            replace a with (ART.shadow_addr (fr + 8 * (a - ART.shadow_addr fr))).
            - apply ARF.shadow_of_app. apply Happ. unfold ART.shadow_addr in *. Z.div_mod_to_equations. lia.
            - unfold ART.shadow_addr in *. Z.div_mod_to_equations. lia. }
          destruct (FRM.stk_bytes segs m' _ _ Hstk' ltac:(lia)) as (sh' & Hl' & Hb').
          exists sh'. split; [exact Hb'|]. rewrite Hl'. unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES.
          f_equal. lia. }
      split; [exact Hn|]. split; [exact Hj|].
      split.
      { split; [exact Hphinz|]. rewrite Hsz. apply HAD; [exact Hphiad | intros x Hx; lia]. }
      split; [exact HI'|].
      split; [exact HLK'|]. split; [exact HS'|].
      split; [exact (SG.f32_rowsel_true _ j Ek Ev16 Ev17)|].
      split; [exact K10|]. split; [exact K24|].
      split; [exact BAc | exact HLT'].
    + (* ctl_rt_C at m', same state ly3 S3 *)
      split; [|split; [|split]].
      * apply (ARF.asan_cells_kept W3w mem3 m' HAC0 MUc). subst W3w. cbn [FRM.disjoint_from].
        unfold ART.RT_LO, ART.RT_HI. unfold ART.HIGHMEM_BEG in HSfr.
        split; [lia|]. split; [lia|]. split; [lia | exact I].
      * exact Hcut'.
      * exact Himg'.
      * apply (f32g_ro_keep W3w mem3 m' HRO0 MUc). intros x Hx. subst W3w. cbn [FRM.outside].
        split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   3. The entry 0x827d8 (C_A827d8_at j): the three branches to 0x82bf4 are not taken, then the entry 0x82800. *)
Lemma f32g_e7d8 : forall POST (j : nat),
  CF POST (ix_cut C_A82800_at [Z.of_nat j]) -> CF POST (ix_cut C_A827d8_at [Z.of_nat j]).
Proof using LAWS.
  intros POST j HX800 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A827d8_at ACtlCutP.ixn nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (phi & HPerm & HFRAC & Hn & Hj & HHB & HFLSI & HLK & HFLS & Hcls & Hiff & Hev & HLT).
  destruct (SM.t_cls (ACtlCut.c_in cx) j) as [e|] eqn:Ecl; [|exfalso; exact (Hcls eq_refl)].
  pose proof (SG.f32_cls_e _ j e Ecl) as (He5 & Hk0 & Hlen50).
  pose proof (SG.f32_cls_src _ j e Ecl) as Hsrc.
  pose proof (SG.f32_cls_TF _ j e Ecl) as HTF.
  pose proof HFLS as (_ & H18 & H22 & H23 & H24 & H25 & _ & H152 & H280).
  pose proof (f32g_flsx_of_fls _ _ _ _ _ _ HFLS) as HFLSX.
  pose proof HFLSI as (((_ & _ & _ & H160 & _) & _) & _).
  pose proof HFRAC as (Asp & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32 & HA32 & HAS & HspA &
                       HfrA & HA416 & HSsp & HSapp & _).
  unfold ACtlCutP.FRAME_BYTES in HfrA. unfold ART.APPMEM_END in HSapp.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
  pose proof Hstatic as (_ & _ & Hceil & Hslo & _).
  pose proof CCbq.asan_consts as (HAC & _).
  unfold A.ACfn.LLVMF_STK in Hslo, Hpres.
  destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (Hin6 : In (6, ACtlCut.c_fpos cx) (CG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : fr = CG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) ltac:(left; reflexivity)). unfold CG0f.frame_addr. rewrite EF. reflexivity. }
  assert (EFB : CG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (CCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin6)
    as (Hf4096 & Hfceil & _).
  rewrite <- Efr in Hf4096, Hfceil. rewrite EFB in Hfceil.
  pose proof (f32g_spill _ _ _ _ Asp H152 R9 ltac:(lia) ltac:(lia) ltac:(lia)) as Q152.
  pose proof (f32g_spill _ _ _ _ Asp H280 R9 ltac:(lia) ltac:(lia) ltac:(lia)) as Q280.
  pose proof (f32g_spill _ _ _ _ Asp H160 R9 ltac:(lia) ltac:(lia) ltac:(lia)) as Q160.
  pose proof (Hev e ltac:(first [exact Ecl | reflexivity])) as Hu32.
  pose proof (A.ProgWorldVisWin.win_vis B) as WV.
  unfold A.ProgWorld.win_vis_stmt in WV.
  pose proof (A.ProgWorldVisFrame.frame_vis B) as FV.
  unfold A.ProgWorld.frame_vis_stmt in FV. specialize (FV LAWS).
  set (RNG := A.ProgBridge.RNG_W (CA0n.w_H W3)).
  (* G3 *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A827d8_at [Z.of_nat j])) with 0x827d8.
  apply (CA0nR.SRr_xregs_eqv segs W3 (LRG.mkR_of regs3) regs3 CK11.fp_regs
           (Z_to_bv 64 0x827d8) CK11.fp_csr None mem3 (CK11.seg_rom segs) md3 (POST cx));
    [| exact (LRG.xregs_eqv_sym _ _ (LRG.mkR_of_eqv regs3))].
  unfold LRG.mkR_of.
  (* G4: a run that only reads (SRr_fevt over the visible footprint) *)
  eapply (CA0nR.SRr_fevt segs A.ACtlG.Kit.kit_wx W3 _ md3 RNG _ (POST cx)).
  { apply A.ProgBridge.fevt_of_evtF.
    eapply SF.f32_evt_a_F with (A := Asp) (EV := fr + 528) (tf := SM.b2z (SM.t_tfill (ACtlCut.c_in cx) j))
      (so := SM.b2z (SM.t_sum_ok (ACtlCut.c_in cx) j)) (ev := e).
    - exact R9.
    - lia.
    - lia.
    - apply Bool.not_true_iff_false. intros HC. unfold bv_eqb in HC. apply Z.eqb_eq in HC. apply bv_eq in HC.
      exact (Hsrc (proj1 Hiff HC)).
    - apply SG.f32_rd8; [exact Q152 | apply MEM.length_le8].
    - unfold SM.b2z; destruct (SM.t_tfill (ACtlCut.c_in cx) j); [right | left]; reflexivity.
    - apply SG.f32_rd8; [exact Q280 | apply MEM.length_le8].
    - unfold SM.b2z; destruct (SM.t_sum_ok (ACtlCut.c_in cx) j); [right | left]; reflexivity.
    - intros (Htf0 & Hso0). unfold SM.b2z in Htf0, Hso0.
      destruct HTF as [Hs|Ht]; [rewrite Hs in Hso0; discriminate | rewrite Ht in Htf0; discriminate].
    - apply SG.f32_rd8; [exact Q160 | apply MEM.length_le8].
    - lia.
    - lia.
    - apply SG.f32_rd4; [exact Hu32 | apply MEM.length_le4].
    - lia.
    - apply A.ProgBridge.rng_of_visible. eapply WV; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia].
    - apply A.ProgBridge.rng_of_visible. eapply WV; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia].
    - apply A.ProgBridge.rng_of_visible. eapply WV; [exact HJ | unfold A.ACfn.LLVMF_STK; lia | lia].
    - apply A.ProgBridge.rng_of_visible.
      assert (H1 : CG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) <= fr + 528) by (rewrite <- Efr; lia).
      assert (H2 : fr + 528 + 4 <= CG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) + CG00.fs_frame_bytes 6)
        by (rewrite EFB, <- Efr; lia).
      exact (proj1 (FV _ _ _ _ _ _ _ (fr + 528) 4 HAR Hin6 H1 H2)). }
  { apply A.ProgBridge.fp_avoids_RNG_W. }
  (* G5: the entry 0x82800 at the run's end map *)
  intros ms' md' HQ Hsbm. destruct HQ as (y10 & y11 & Ems). subst ms'.
  match goal with |- context [LMS.MS ?R _ _ _ _ _ _] => set (R1 := R) end.
  change (CA0n.SRr segs W3 (CG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A82800_at [Z.of_nat j])) R1 mem3 md')
            (POST cx)).
  assert (K2 : CK11.getr R1 2 = CK11.getr regs3 2) by reflexivity.
  assert (K3 : CK11.getr R1 3 = CK11.getr regs3 3) by reflexivity.
  assert (K4 : CK11.getr R1 4 = CK11.getr regs3 4) by reflexivity.
  assert (K8 : CK11.getr R1 8 = CK11.getr regs3 8) by reflexivity.
  assert (K9 : CK11.getr R1 9 = CK11.getr regs3 9) by reflexivity.
  assert (K18 : CK11.getr R1 18 = CK11.getr regs3 18) by reflexivity.
  assert (K19 : CK11.getr R1 19 = CK11.getr regs3 19) by reflexivity.
  assert (K21 : CK11.getr R1 21 = CK11.getr regs3 21) by reflexivity.
  assert (K22 : CK11.getr R1 22 = CK11.getr regs3 22) by reflexivity.
  assert (K23 : CK11.getr R1 23 = CK11.getr regs3 23) by reflexivity.
  assert (K24 : CK11.getr R1 24 = CK11.getr regs3 24) by reflexivity.
  assert (K25 : CK11.getr R1 25 = CK11.getr regs3 25) by reflexivity.
  assert (K26 : CK11.getr R1 26 = CK11.getr regs3 26) by reflexivity.
  destruct (f32g_keep cx j phi fr regs3 R1 mem3 mem3 [] Asp HFLSI HLK HFLSX HLT (FRM.munch_refl [] mem3)
              (FRM.wmono_refl rsegs mem3) (fun p n H _ => H) K9 K18 K21 K22 K23 K25 R9 ltac:(lia) ltac:(lia)
              (fun _ _ => I) (fun _ _ => I) (fun _ _ => or_introl I) (fun _ _ _ => I) (fun _ _ => I)
              (fun H => H))
    as (HI' & HLK' & HS' & HLT').
  apply (HX800 cx [Z.of_nat j] fr k ly3 S3 W3 R1 mem3 md' HB).
  - eapply (CCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ : Z => False);
      [exact HJ | intros x _; reflexivity | apply CK1b.mem_grows_refl | intros x _; reflexivity
      | exact Hsbm | intros a Ha; destruct Ha].
  - exact HF.
  - exact HL.
  - exact Hk.
  - cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A82800_at ACtlCutP.ixn nth].
    rewrite Nat2Z.id. split; [reflexivity|].
    exists phi.
    split; [exact HPerm|].
    split; [exact (A.ACtlG.Kit.kit_frac_move B cx fr fr regs3 R1 mem3 HFRAC K2 K3 K4 K8 K9 K19 K26)|].
    split; [exact Hn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HI'|].
    split; [exact HLK'|].
    split; [apply f32g_fls_of_flsx; [exact HS' | unfold CT.rgv in H24 |- *; rewrite K24; exact H24] | exact HLT'].
  - exact Hrt.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   4. The stage: both entries. *)
Lemma glue_seg_F32 : forall POST (j : nat),
  CF POST (ix_cut C_A828c8_at [Z.of_nat j]) -> CF POST (ix_cut C_A8285c_at [Z.of_nat j]) ->
  CF POST (ix_cut C_A827d8_at [Z.of_nat j]) /\ CF POST (ix_cut C_A82800_at [Z.of_nat j]).
Proof using LAWS.
  intros POST j HX8c8 HX85c.
  pose proof (f32g_e800 POST j HX8c8 HX85c) as H800.
  exact (conj (f32g_e7d8 POST j H800) H800).
Qed.

End GlueF32.
