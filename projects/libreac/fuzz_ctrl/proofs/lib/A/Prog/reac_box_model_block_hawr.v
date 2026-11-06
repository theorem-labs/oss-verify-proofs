(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_model_block (0x85b44) on fuzz_ctrl's ASan build, image A: obligation Hawr of the glue proof of
   pb_reac_box_model_block (lib/A/Prog/reac_box_model_block_glue.v, bmb_body's premise at :2737-2738): every byte
   the tail may write (reac_box_model_block_glue_defs.bmb_WR) is a byte the caller's journal lets this call write
   (awr_byte over the frames own plus the class-0 frame (0, pos) the call took), or the frame's flag byte.
   The statement is Hawr of tmb-goals.md row 24 (a working note, not in this delivery), reviewed in
   tmb-goals-review.md sections (1) and (2) (a working note, not in this delivery): the conclusion is the row verbatim, the premises are the TMB theorem's own
   hypotheses at that goal (bmbthm.v (not in this delivery): Hlo, Hhi, Eab2, HOs or its twr_ok conjunct).  The lemmas take no premise
   that comes from VIS0, SR2, AC2 or rt_facts.
   rule 24: no function is proved here (a standalone lemma of the glue; it Requires the glue's own Requires, never the
   glue).  The names resolve as in the glue's Module BmbGlue: outside is lib.Lib.Frame's, awr_byte / in_frames are
   YCbq's (YCbq.v:460-464, not YCe5's), ablocks is YG0d's, flag_addr / frame_addr are YG0f's, twr_ok / tsrc_ok are
   CtrlCallerJ's at CtrlImg.PI_ctrl. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth RcSynthLib.
(* the statement, qualified *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_box_model_block.
#[local] Existing Instance CtrlImg.PI_ctrl.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* Of the glue's later Requires (its lines 57-68), the three that bmb_WR is stated over, and bmb_WR itself. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AsanRT A.Prog.asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_model_block_glue_defs.

Module BmbHawr.
(* the glue's Module BmbGlue imports these three (with others that define none of the names below) *)
Import lib.Lib.Frame A.AsanRT A.Prog.asan_stack_malloc_c.
Import ListNotations.
Local Open Scope Z_scope.

(* A byte that is not outside a list of intervals lies in one of them. *)
Lemma not_outside_in : forall (L : list (Z * Z)) (a : Z),
  ~ outside L a -> exists lo hi, In (lo, hi) L /\ lo <= a < hi.
Proof.
  induction L as [|[lo hi] L IH]; intros a H; cbn [outside] in H.
  - exfalso. exact (H I).
  - destruct (Z_le_dec lo a) as [h1 | h1]; [destruct (Z_lt_dec a hi) as [h2 | h2] |].
    + exists lo, hi. split; [left; reflexivity | lia].
    + destruct (IH a) as (lo' & hi' & Hin & Hr); [intros Ho; apply H; split; [lia | exact Ho] |].
      exists lo', hi'. split; [right; exact Hin | exact Hr].
    + destruct (IH a) as (lo' & hi' & Hin & Hr); [intros Ho; apply H; split; [lia | exact Ho] |].
      exists lo', hi'. split; [right; exact Hin | exact Hr].
Qed.

Section Hawr.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.

(* Hawr (a Theorem Labs lane's tmb-goals.md row 24 (a working note, not in this delivery), `hawr`), stated over the hypotheses of the theorem's context at that goal
   (regs, the spec's Hlo / Hhi with ESTK rewritten, Eab2, the spec's HOs): the tail's write set (bmb_WR at
   sp := getr regs 2, FS := ly_F lyc, jj := pos) lies in what the caller's journal lets the call write.  The window
   [sp - 4272, sp) is in [sp0 - STK, sp0) since sp0 - STK <= sp - 4320 and sp <= sp0; the flag byte is
   flag_addr lyc 0 pos; the frame and its 8 shadow bytes are in_frames of (0, pos); the 32 bytes at o (bmb_WR has them
   only when p <> 0 and o <> 0) are the caller's awr_byte over own, weakened to (0, pos) :: own, at
   ablocks B lyc S2 = ablocks B lyc Sc. *)
Lemma bmb_hawr : forall (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (regs : bvmap 5 word) (p o : Z) (S2 : astate) (pos : Z),
  sp0 - STK <= spZ regs - 4320 -> spZ regs <= sp0 ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  (p <> 0 -> o <> 0 -> forall a, o <= a < o + 32 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  forall a : Z, 0 <= a < 2 ^ 64 ->
    ~ outside (reac_box_model_block_glue_defs.bmb_WR (lib.Reusable.YK11.getr regs 2) p o (ly_F lyc) pos) a ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S2) lyc ((0, pos) :: own) a \/ a = flag_addr lyc 0 pos.
Proof.
  intros STK sp0 FP ly S own lyc Sc regs p o S2 pos Hlo Hhi Eab Ho a Ha Hout.
  change (spZ regs) with (bv_unsigned (lib.Reusable.YK11.getr regs 2)) in Hlo, Hhi.
  (* the class-0 frame and flag byte of the allocator (asan_stack_malloc_c.v) are cgif's frame_addr / flag_addr
     (YG0f.v:340-341) of the layout lyc, whose fake stack is ly_F lyc *)
  assert (Efr : frame_addr lyc 0 pos = fs_frame (ly_F lyc) 0 pos).
  { unfold frame_addr, fs_frame_off, fs_frame, fs_B, kFakeFramesOff.
    change (fs_frame_bytes 0) with 64. change (Z.of_nat 0%nat) with 0. change (2 ^ 0) with 1. lia. }
  assert (Efl : fs_flag (ly_F lyc) 0 pos = flag_addr lyc 0 pos).
  { unfold flag_addr, fs_flag_off, fs_flag, kFakeFlagsOff.
    change (fs_flags_off 0) with 0. change (2 ^ (15 - Z.of_nat 0%nat)) with 32768. change (2 ^ 15) with 32768.
    lia. }
  destruct (not_outside_in _ a Hout) as (lo & hi & Hin & Hr).
  unfold reac_box_model_block_glue_defs.bmb_WR in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - cbn [In] in Hin. destruct Hin as [E | [E | [E | [E | []]]]]; injection E as E1 E2; subst lo hi.
    + (* the machine-stack window: the caller's own stack window [sp0 - STK, sp0) *)
      left. unfold awr_byte. left. lia.
    + (* the flag byte *)
      right. rewrite <- Efl. lia.
    + (* the frame (0, pos) *)
      left. unfold awr_byte. right. right. right. unfold in_frames. exists 0, pos.
      split; [left; reflexivity |]. left. unfold in_zr. cbn [fst snd]. rewrite Efr.
      change (fs_frame_bytes 0) with 64. lia.
    + (* the frame's 8 shadow bytes *)
      left. unfold awr_byte. right. right. right. unfold in_frames. exists 0, pos.
      split; [left; reflexivity |]. right. unfold in_zr. cbn [fst snd]. rewrite Efr.
      change (fs_frame_bytes 0 / 8) with 8.
      unfold YG0f.shadow_addr, YG0f.SHADOW_OFF. unfold A.AsanRT.shadow_addr, A.AsanRT.ASAN_K in Hr. lia.
  - (* the 32 bytes at o, when the row is read *)
    revert Hin. destruct ((p =? 0) || (o =? 0)) eqn:Epo; intros Hin; cbn [In] in Hin; [destruct Hin |].
    destruct Hin as [E | []]. injection E as E1 E2; subst lo hi.
    apply orb_false_iff in Epo as [Ep Eo]. apply Z.eqb_neq in Ep, Eo.
    left. rewrite Eab. pose proof (Ho Ep Eo a Hr) as Hw. unfold awr_byte in *.
    destruct Hw as [X | [X | [X | X]]]; [left; exact X | right; left; exact X | right; right; left; exact X |].
    right. right. right. unfold in_frames in *. destruct X as (cid & pos' & Hc & Hx).
    exists cid, pos'. split; [right; exact Hc | exact Hx].
Qed.

(* Hawr from the spec's form of the caller's right to let the call write o (twr_ok's first conjunct). *)
Lemma bmb_hawr_twr : forall (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : YA0n.world AB1v.tfibsegs) (memc : word -> option byte)
    (regs : bvmap 5 word) (p o : Z) (S2 : astate) (pos : Z),
  sp0 - STK <= spZ regs - 4320 -> spZ regs <= sp0 ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  (o <> 0 -> twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o 32) ->
  forall a : Z, 0 <= a < 2 ^ 64 ->
    ~ outside (reac_box_model_block_glue_defs.bmb_WR (lib.Reusable.YK11.getr regs 2) p o (ly_F lyc) pos) a ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S2) lyc ((0, pos) :: own) a \/ a = flag_addr lyc 0 pos.
Proof.
  intros STK sp0 FP ly S own lyc Sc W memc regs p o S2 pos Hlo Hhi Eab Htwr.
  apply (bmb_hawr STK sp0 FP ly S own lyc Sc regs p o S2 pos Hlo Hhi Eab).
  intros _ Ho a Ha. exact (proj1 (Htwr Ho a Ha)).
Qed.

(* Hawr from the spec's whole premise on o (HOs of treac_box_model_block_spec, C_reac_box_model_block.v:167-171):
   the theorem passes HOs as it is. *)
Lemma bmb_hawr_hos : forall (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : YA0n.world AB1v.tfibsegs) (memc : word -> option byte)
    (regs : bvmap 5 word) (p o : Z) (S2 : astate) (pos : Z),
  sp0 - STK <= spZ regs - 4320 -> spZ regs <= sp0 ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  (o <> 0 -> C_reac_box_model_block.tbmb_o_home lyc Sc o /\
             (forall x, o <= x < o + 32 -> ~ in_img AB1v.tfibsegs x) /\
             twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o 32 /\
             tsrc_ok W memc (spZ regs) o 32 /\
             (spZ regs <= o \/ o + 32 <= spZ regs - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK)) ->
  forall a : Z, 0 <= a < 2 ^ 64 ->
    ~ outside (reac_box_model_block_glue_defs.bmb_WR (lib.Reusable.YK11.getr regs 2) p o (ly_F lyc) pos) a ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S2) lyc ((0, pos) :: own) a \/ a = flag_addr lyc 0 pos.
Proof.
  intros STK sp0 FP ly S own lyc Sc W memc regs p o S2 pos Hlo Hhi Eab HOs.
  apply (bmb_hawr_twr STK sp0 FP ly S own lyc Sc W memc regs p o S2 pos Hlo Hhi Eab).
  intros Ho. exact (proj1 (proj2 (proj2 (HOs Ho)))).
Qed.
End Hawr.
End BmbHawr.
