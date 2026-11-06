(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_model_block (0x85b44) on fuzz_ctrl's ASan build, image A: the o-window premises of the glue's bmb_body
   (rows 3 HO, 4 AO, 25 Hvis, 26 Hni and 31 HOm of a Theorem Labs lane's tmb-goals.md (a working note, not in this delivery)), as range, separation and
   presence facts that the theorem pb_reac_box_model_block cites.  rule 24: no function is proved here.
   Each lemma is stated in the proof context of the theorem at the eapply of bmb_body: its Section variables and
   hypotheses carry the names and types of that context, and each lemma closes over only the ones it uses, so the
   theorem applies it by name.  This file Requires the glue for its lemmas bmb_ho, in_img_rsegs, bmb_ao_stack and
   bmb_ao_frame; the theorem lives downstream of the glue, so there is no cycle. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six core modules that ctrl's lib/A/Reusable duplicates (YI04, YI16, YK11, YK1b, YM05, YO09) are Required, never
   Imported, and written lib.Reusable.X.n (porter 04:24Z / 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YI04 YI16 YM05 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK0h YK0i YK14 YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlFrame
CtrlRo YC85.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth.
(* the statement, qualified *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_box_model_block.
#[local] Existing Instance CtrlImg.PI_ctrl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The lib.Lib family is doubled under lib/A/Bz/Lib: Required from its own directory and named lib.Lib.X (a Theorem Labs lane 05:20Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec MState Mem Frame Cells Step ExecF StepF Regs6ss
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Reusable.YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Img0 A.AsanRT A.ProgBridge A.MemNorm A.MemNormF
  A.MemNormTr A.ProgWorld A.ProgWorld_Fs A.ProgWorldShadow A.ProgWorldAstack A.ProgWorldCtlRt
  A.ProgWorldVisFrame A.ProgWorldVisWin A.ProgWorldVisHeap A.Prog.CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.RcAsanFPLib
  A.Prog.reac_box_model_block_c A.Prog.reac_box_model_block_cF A.Prog.rng_asan A.Prog.reac_box_model_block_base
  A.Prog.asan_memsetF A.Prog.ImgBounds A.Prog.reac_box_model_block_baseF A.Prog.reac_box_model_block_epi A.Prog.reac_box_model_block_epiF.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_model_block_glue.
Module BmbGlueO.
Import reac_box_model_block_glue.BmbGlue.
Import lib.Lib.PropExec lib.Lib.MState lib.Lib.Mem lib.Lib.Frame lib.Lib.Cells lib.Lib.Step.
Import A.Img0 A.AsanRT A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.reac_box_model_block_c.
Import Reusable.YK04R Reusable.YA0nR A.ProgBridge A.MemNorm A.MemNormTr.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals), as in the _F files. *)
Import lib.Lib.ExecF lib.Lib.StepF.
Import ListNotations.
Local Open Scope Z_scope.

(* A visible byte outside the image is present: the view reads the raw memory there. *)
Lemma bmb_o_present_of_view : forall (H : word -> bool) (mem : word -> option byte) (a : Z),
  0 <= a < 2 ^ 64 -> ~ in_img AB1v.tfibsegs a -> aview AB1v.tfibsegs H mem a <> None -> apresent H mem a.
Proof.
  intros H mem a Ha Hni Hv. unfold aview, mbyte, mrestrict in Hv. unfold apresent.
  destruct (H (Z_to_bv 64 a)) eqn:EH.
  - exfalso. apply Hni. eapply Reusable.YG0s.seg_rom_in_img; [exact Ha|].
    intros E. apply Hv. rewrite E. reflexivity.
  - destruct (mem (Z_to_bv 64 a)) as [b|] eqn:EM; [split; [reflexivity | exists b; reflexivity]|].
    exfalso. apply Hni. eapply Reusable.YG0s.seg_rom_in_img; [exact Ha|].
    intros E. apply Hv. rewrite E. reflexivity.
Qed.

(* A range with no image byte lies wholly below the image or wholly above it (the image is all of
   [0x10000, 0x5fe000), in_img_rsegs). *)
Lemma bmb_o_off_img : forall q n, 0 < n -> (forall x, q <= x < q + n -> ~ in_img AB1v.tfibsegs x) ->
  q + n <= 0x10000 \/ 0x5fe000 <= q.
Proof.
  intros q n Hn Hx.
  destruct (Z_le_gt_dec (q + n) 0x10000) as [L | L]; [left; exact L|].
  destruct (Z_le_gt_dec 0x5fe000 q) as [R | R]; [right; exact R|].
  exfalso. apply (Hx (Z.max q 0x10000)); [lia|]. apply in_img_rsegs. lia.
Qed.

Section O.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws AB1v.tfibsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z)) (lyc : alayout)
  (Sc : astate) (W : world AB1v.tfibsegs) (memc : word -> option byte) (mdc : Model) (regs : bvmap 5 word) (o : Z).
Hypothesis HOs :
  o <> 0 ->
  C_reac_box_model_block.tbmb_o_home lyc Sc o /\
  (forall x : Z, o <= x < o + 32 -> ~ in_img AB1v.tfibsegs x) /\
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o 32 /\ tsrc_ok W memc (spZ regs) o 32 /\
  (spZ regs <= o \/ o + 32 <= spZ regs - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK).
Hypothesis HAR : AR AB1v.tfibsegs B lyc Sc W memc mdc.
Variables (S2 : astate) (mem2 : word -> option byte) (md2 : Model).
Hypothesis HK2 :
  acall_kept AB1v.tfibsegs B lyc Sc W memc W mem2 (spZ regs - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK)
    (spZ regs) (fun _ : Z => False).
Hypothesis HAR2 : AR AB1v.tfibsegs B lyc S2 W mem2 md2.
Hypothesis Hro2 : ro_agree rsegs mem2.
Hypothesis OFACTS :
  o <> 0 ->
  (forall a : Z, o <= a < o + 32 -> aview AB1v.tfibsegs (w_H W) mem2 a <> None) /\
  shadow_hull_vis (aview AB1v.tfibsegs (w_H W) mem2) o 32 /\ ly_F lyc + 8 <= o /\ o + 32 <= APPMEM_END.

(* Row 26 Hni: no byte of o's window is an image byte (HOs 2nd conjunct). *)
Lemma bmb_o_Hni : forall x : Z, o <> 0 -> o <= x < o + 32 -> ~ in_img AB1v.tfibsegs x.
Proof.
  intros x Ho Hx. destruct (HOs Ho) as (_ & Hni & _). exact (Hni x Hx).
Qed.

(* Row 31 HOm: every byte of o's window is present at the entry memory (twr_ok, HOs 3rd conjunct). *)
Lemma bmb_o_HOm : o <> 0 -> forall a : Z, o <= a < o + 32 -> apresent (w_H W) memc a.
Proof.
  intros Ho a Ha. destruct (HOs Ho) as (_ & _ & Htwr & _). exact (proj1 (proj2 (Htwr a Ha))).
Qed.

(* Row 25 Hvis: every byte of o's window is visible (the first half of twr_ok's presence). *)
Lemma bmb_o_Hvis : forall x : Z, o <> 0 -> o <= x < o + 32 -> w_H W (Z_to_bv 64 x) = false.
Proof.
  intros x Ho Hx. destruct (HOs Ho) as (_ & _ & Htwr & _). exact (proj1 (proj1 (proj2 (Htwr x Hx)))).
Qed.

(* Row 3 HO: o's 32 bytes as one cell block at the normalized return memory (bmb_ho, its presence from OFACTS 1st
   and HOs 2nd), apart from the real-stack window (HOs 5th) and from the two JOIN blocks, which are image bytes
   (HOs 2nd with bmb_o_off_img).  The witness comes before the o <> 0 guard: the theorem fixes it before its case
   split. *)
Lemma bmb_o_HO : exists ob : list byte,
  o <> 0 ->
  rw_cells rsegs (normalize rsegs mem2) o [CB 32 ob] /\
  (bv_unsigned (lib.Reusable.YK11.getr regs 2) <= o \/ o + 32 <= bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4272) /\
  (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
Proof.
  destruct (Z.eq_dec o 0) as [E0 | Ho].
  - exists (repeat (Z_to_bv 8 0) 32). intros Ho. contradiction.
  - destruct (HOs Ho) as (_ & Hni & _ & Htsrc & Hsep).
    destruct (OFACTS Ho) as (Hv2 & _ & _ & Hend).
    destruct Htsrc as (_ & _ & _ & _ & Ho0 & Ho63).
    assert (Hpres : forall a, o <= o -> o <= a < o + 32 -> apresent (w_H W) mem2 a).
    { intros a _ Ha. apply bmb_o_present_of_view; [lia | exact (Hni a Ha) | exact (Hv2 a Ha)]. }
    assert (ESTK : C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK = 4320) by reflexivity.
    rewrite ESTK in Hsep.
    (* spZ stays folded for lia; the goal's bv_unsigned (getr regs 2) is spZ regs by delta *)
    destruct (bmb_ho W mem2 o (spZ regs) Hpres Hni Ho0 Hend ltac:(lia)) as (ob & Hc & Hs & _).
    exists ob. intros _. split; [exact Hc|]. split; [exact Hs|].
    unfold JOIN_0013, JOIN_0014. destruct (bmb_o_off_img o 32 ltac:(lia) Hni) as [L | R]; [left | right]; lia.
Qed.

(* Row 4 AO: o's window is addressable at the normalized return memory, its end is application memory, and it is
   apart from the runtime's window [RT_LO, RT_HI), which is image bytes.  Addressable: on the stack arm of
   tbmb_o_home the caller's stack is addressable at any AR state (bmb_ao_stack at HAR2); on the frame arm the
   frame's shadow is kept across the call (bmb_ao_frame with HK2 and tsrc_ok's range_addressable).  app_mem: from
   tsrc_ok's amem_range. *)
Lemma bmb_o_AO : o <> 0 -> addressable (normalize rsegs mem2) o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
Proof.
  intros Ho. destruct (HOs Ho) as (Hhome & Hni & _ & Htsrc & _).
  destruct Htsrc as (_ & HRA & _ & Hamr & Ho0 & Ho63).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
  assert (Happ : forall x, o <= x <= o + 32 -> app_mem x).
  { intros x Hx. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia. }
  split; [|split; [apply Happ; lia|]].
  - unfold C_reac_box_model_block.tbmb_o_home in Hhome.
    destruct Hhome as [(cid & pos & Hin & Hcid & Hx) | [Hs1 Hs2]].
    + destruct (Reusable.YG0s.frame_facts B lyc Sc _ cid pos (proj1 HAR) Hin)
        as (Hc10 & Hpos' & HFapp & _ & HFal & Hfo1 & Hfo2 & Hfo64 & Hfb64 & Hfbm & Hflb).
      assert (Hfa8 : frame_addr lyc cid pos mod 8 = 0).
      { unfold frame_addr, page_aligned in *.
        pose proof (Z.div_mod (ly_F lyc) 4096 ltac:(lia)) as D1. rewrite HFal in D1.
        pose proof (Z.div_mod (fs_frame_off cid pos) 64 ltac:(lia)) as D2. rewrite Hfo64 in D2.
        replace (ly_F lyc + fs_frame_off cid pos)
          with ((512 * (ly_F lyc / 4096) + 8 * (fs_frame_off cid pos / 64)) * 8) by lia.
        apply Z.mod_mul. lia. }
      assert (Hfb8 : fs_frame_bytes cid mod 8 = 0).
      { apply Z.mod_divide in Hfbm; [|lia]. destruct Hfbm as [k Hk].
        apply (proj2 (Z.mod_divide _ 8 ltac:(lia))). exists (8 * k). lia. }
      apply (bmb_ao_frame B lyc Sc W memc mem2 _ _ _ o 32 cid pos HK2 Hro2 Hin Hx (fun _ _ F => F) Hfa8 Hfb8 Ho0);
        [lia | unfold APPMEM_END; lia | intros x Hx'; apply Happ; lia | exact HRA].
    + apply (bmb_ao_stack B LAWS lyc S2 W mem2 md2 o 32 HAR2 Hro2); lia.
  - unfold RT_LO, RT_HI. destruct (bmb_o_off_img o 32 ltac:(lia) Hni) as [L | R]; [left | right]; lia.
Qed.
End O.
End BmbGlueO.
