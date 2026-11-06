(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_model_block (0x85b44) on fuzz_ctrl's ASan build, image A: the RANGE obligations RP RPs RO ROs RN RNs RJ13s
   RJ14s of the glue proof of pb_reac_box_model_block (in a Theorem Labs lane's goal list tmb-goals.md rows 9-16 (a working note, not in this delivery)), as standalone
   lemmas.  Each one is a premise of reac_box_model_block_glue.BmbGlue.bmb_body that `eassumption` does not close at
   the point where a Theorem Labs lane's theorem applies bmb_body.  rule 24: no function is proved here (range facts of the
   glue of an already-proved run).
   Writer: a Theorem Labs lane; a working branch.

   The shape of each lemma.  The premises are the facts of the theorem's context at that point that the proof needs,
   each stated with the type it has there; the name in [brackets] is its name there.  The conclusion is the goal as
   it prints there, with the footprint written out: RNG_W (hidden_plus (w_H W) (ly_F lyc)).  So
   `exact (bmb_rng2_X ... facts)` or `eapply bmb_rng2_X; eassumption` closes the goal.  The AR premise is the AR of
   any state of lyc and W ([HAR] or [HAR2]): only ly_F lyc and the visibility of W are read.
   No premise comes from VIS0, SR2, AC2 or rt_facts, and none is AMEMSET, AMEMCPY, JE, HJT_*, HJ13, HJ14, HZS_J13 or
   HZS_J14.  [HPs] [HNs] [HIMGSH] [Ro] [HAR] are the spec's premises; [HAR2] is AR of the journal [HJ2] at the
   allocator's return; [FAgt] [FAapp] are bmb_FS_app of [HAR2]; [ROIMG] is from RELRO (img_bounds_of_in_img);
   [OFACTS] is bmb_o_facts of [HOs] [HAR] [HAR2] [HK2] (bmbthm.v:396-402).

   The covers (BmbGlue):
     RP  RN          img_rng_plus: an image range, apart from the hint word [ly_F, ly_F + 8)
     RPs RNs RJ13s RJ14s
                     img_sh_cover_plus / img_sh_cover_strict: the shadow of an image range, from img_shadow_vis
     RO  ROs         rng_plus over the o facts at the allocator's return (a Theorem Labs lane's OFACTS): o's bytes and the
                     shadow words around them are visible, and both lie apart from the hint word
   The image bounds of the row come from the spec's row premise (IMG_LO + 64 <= p, p + 296 + 64 <= IMG_HI); the
   name's from its in_roP bytes ([ROIMG]) and name_ok's 1 <= length nb.  JOIN_0013 / JOIN_0014 are constants.
   BmbGlueSR (reac_box_model_block_glue_sr.v) covers the shadow_rw_on premise, not the footprint, so no lemma of it
   is used here. *)
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
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope bv_scope.
Local Open Scope Z_scope.
(* The lib.Lib family is doubled under lib/A/Bz/Lib: Required from its own directory and named lib.Lib.X (a Theorem Labs lane 05:20Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec MState Mem Frame Cells Step ExecF StepF Regs6ss
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Reusable.YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Img0 A.AsanRT A.ProgBridge A.MemNorm A.MemNormF
  A.MemNormTr A.ProgWorld A.ProgWorld_Fs A.ProgWorldShadow A.ProgWorldAstack A.ProgWorldCtlRt
  A.ProgWorldVisFrame A.ProgWorldVisWin A.ProgWorldVisHeap A.Prog.CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.RcAsanFPLib
  A.Prog.reac_box_model_block_c A.Prog.reac_box_model_block_cF A.Prog.rng_asan A.Prog.reac_box_model_block_base
  A.Prog.asan_memsetF A.Prog.ImgBounds A.Prog.reac_box_model_block_baseF A.Prog.reac_box_model_block_epi
  A.Prog.reac_box_model_block_epiF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_model_block_glue.

Module BmbGlueRng2.
Import reac_box_model_block_glue.BmbGlue.
Import lib.Lib.PropExec lib.Lib.MState lib.Lib.Mem lib.Lib.Frame lib.Lib.Cells lib.Lib.Step.
Import A.Img0 A.AsanRT A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.reac_box_model_block_c.
Import Reusable.YK04R Reusable.YA0nR A.ProgBridge A.MemNorm A.MemNormTr.
Import lib.Lib.ExecF lib.Lib.StepF.
Import ListNotations.
Local Open Scope Z_scope.

Section Rng2.
Context {rc : lib.Reusable.YM05.RunCeil}.

(* row 9, RP: the row's 296 bytes are an image range.  [HPs] [FAgt] *)
Lemma bmb_rng2_RP : forall (B : asyms) (GLOBS : list (Z * Z)) (RLO RHI : Z) (W : world AB1v.tfibsegs)
    (memc : word -> option byte) (lyc : alayout) (p o : Z) (row : list byte),
  (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\
     garr8 AB1v.tfibsegs (mrestrict (w_H W) memc) p (C_reac_box_model_block.bmb_z row) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= p /\ p + 296 <= q + sz) /\
     IMG_LO + 64 <= p /\ p + 296 + 64 <= IMG_HI /\
     (forall x, p <= x < p + 296 -> in_roP AB1v.tfibsegs RLO RHI x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
     (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
  ASAN_GT <= ly_F lyc ->
  p <> 0 -> rng (RNG_W (hidden_plus (w_H W) (ly_F lyc))) p 296.
Proof.
  intros B GLOBS RLO RHI W memc lyc p o row HPs FAgt Hp.
  destruct (HPs Hp) as (_ & _ & _ & _ & P5 & P6 & _).
  unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI in P5, P6.
  apply (img_rng_plus W (ly_F lyc)); lia.
Qed.

(* row 10, RPs: the shadow of the row's bytes.  [HIMGSH] [HPs] [HAR] *)
Lemma bmb_rng2_RPs : forall (B : asyms) (GLOBS : list (Z * Z)) (RLO RHI : Z) (W : world AB1v.tfibsegs)
    (memc : word -> option byte) (lyc : alayout) (S : astate) (m : word -> option byte) (md : Model) (p o : Z)
    (row : list byte),
  img_shadow_vis AB1v.tfibsegs B ->
  (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\
     garr8 AB1v.tfibsegs (mrestrict (w_H W) memc) p (C_reac_box_model_block.bmb_z row) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= p /\ p + 296 <= q + sz) /\
     IMG_LO + 64 <= p /\ p + 296 + 64 <= IMG_HI /\
     (forall x, p <= x < p + 296 -> in_roP AB1v.tfibsegs RLO RHI x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
     (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
  AR AB1v.tfibsegs B lyc S W m md ->
  p <> 0 -> A.Prog.reac_box_model_block_cF.sh_cover (RNG_W (hidden_plus (w_H W) (ly_F lyc))) p 296.
Proof.
  intros B GLOBS RLO RHI W memc lyc S m md p o row HIMGSH HPs HAR Hp.
  destruct (HPs Hp) as (_ & _ & _ & _ & P5 & P6 & _).
  unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI in P5, P6.
  apply (img_sh_cover_plus B lyc S W m md _ p 296 HIMGSH HAR eq_refl); lia.
Qed.

(* row 11, RO: o's 32 bytes are visible at the allocator's return and lie above the hint word.  [Ro] [OFACTS] *)
Lemma bmb_rng2_RO : forall (W : world AB1v.tfibsegs) (mem2 : word -> option byte) (lyc : alayout) (o : Z),
  0 <= o < 2 ^ 64 ->
  (o <> 0 -> (forall a, o <= a < o + 32 -> aview AB1v.tfibsegs (w_H W) mem2 a <> None) /\
     shadow_hull_vis (aview AB1v.tfibsegs (w_H W) mem2) o 32 /\ ly_F lyc + 8 <= o /\ o + 32 <= APPMEM_END) ->
  o <> 0 -> rng (RNG_W (hidden_plus (w_H W) (ly_F lyc))) o 32.
Proof.
  intros W mem2 lyc o Ro OFACTS Ho. destruct (OFACTS Ho) as (V1 & _ & Hdj & Hhi).
  unfold APPMEM_END in Hhi.
  apply (rng_plus W _ _ (ly_F lyc)); [| right; lia].
  split; [lia|]. split; [lia|].
  intros a Ha. exact (A.ProgWorldVisFrame.vis_of_aview AB1v.tfibsegs W mem2 a (V1 a Ha)).
Qed.

(* row 12, ROs: the shadow words around o are visible (shadow_hull_vis) and lie apart from the hint word: above
   it when the side stack is low, below it when the side stack is in high memory.  [Ro] [OFACTS] [FAapp] *)
Lemma bmb_rng2_ROs : forall (W : world AB1v.tfibsegs) (mem2 : word -> option byte) (lyc : alayout) (o : Z),
  0 <= o < 2 ^ 64 ->
  (o <> 0 -> (forall a, o <= a < o + 32 -> aview AB1v.tfibsegs (w_H W) mem2 a <> None) /\
     shadow_hull_vis (aview AB1v.tfibsegs (w_H W) mem2) o 32 /\ ly_F lyc + 8 <= o /\ o + 32 <= APPMEM_END) ->
  ly_F lyc + 11571200 <= 2147446784 \/
    17594333495296 <= ly_F lyc /\ ly_F lyc + 11571200 <= lib.Reusable.YM05.alloc_ceiling ->
  o <> 0 -> A.Prog.reac_box_model_block_cF.sh_cover (RNG_W (hidden_plus (w_H W) (ly_F lyc))) o 32.
Proof.
  intros W mem2 lyc o Ro OFACTS FAapp Ho. destruct (OFACTS Ho) as (_ & V2 & Hdj & Hhi).
  unfold APPMEM_END in Hhi.
  assert (ESH : forall y, shadow_addr y = YG0f.shadow_addr y)
    by (destruct (A.ProgWorld.ctl_fs_geom 0 0 0 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & HE); exact HE).
  unfold A.Prog.reac_box_model_block_cF.sh_cover. rewrite !ESH.
  apply (rng_plus W _ _ (ly_F lyc)).
  - split; [unfold YG0f.shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia|].
    split; [unfold YG0f.shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia|].
    intros a Ha. apply (A.ProgWorldVisFrame.vis_of_aview AB1v.tfibsegs W mem2).
    apply V2. lia.
  - unfold YG0f.shadow_addr, SHADOW_OFF in *.
    destruct FAapp as [HFlow | [HFh1 HFh2]]; [right | left]; Z.div_mod_to_equations; lia.
Qed.

(* row 13, RN: the name's bytes are an image range (in_roP, and 1 <= length nb by name_ok).  [HNs] [ROIMG] [FAgt] *)
Lemma bmb_rng2_RN : forall (B : asyms) (GLOBS : list (Z * Z)) (RLO RHI : Z) (W : world AB1v.tfibsegs)
    (memc : word -> option byte) (lyc : alayout) (p b o : Z) (row nb : list byte),
  (p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
     RcBox.name_ok nb /\
     garr8 AB1v.tfibsegs (mrestrict (w_H W) memc) (RcSynth.rname row) (C_reac_box_model_block.bmb_z nb) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname row /\
        RcSynth.rname row + Z.of_nat (length nb) <= q + sz) /\
     (forall x, RcSynth.rname row <= x < RcSynth.rname row + Z.of_nat (length nb) ->
        in_roP AB1v.tfibsegs RLO RHI x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
     (o = 0 \/ o + 32 <= RcSynth.rname row \/ RcSynth.rname row + Z.of_nat (length nb) <= o)) ->
  (forall x, in_roP AB1v.tfibsegs RLO RHI x -> 65536 <= x < 6283264) ->
  ASAN_GT <= ly_F lyc ->
  p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  rng (RNG_W (hidden_plus (w_H W) (ly_F lyc))) (RcSynth.rname row) (Z.of_nat (length nb)).
Proof.
  intros B GLOBS RLO RHI W memc lyc p b o row nb HNs ROIMG FAgt Hp Hb Hh Hr.
  destruct (HNs Hp Hb Hh Hr) as (Hok & _ & _ & Hx & _).
  pose proof Hok as ((L1 & L2) & _ & _).
  pose proof (ROIMG _ (proj1 (Hx (RcSynth.rname row) ltac:(lia)))) as B0.
  pose proof (ROIMG _ (proj1 (Hx (RcSynth.rname row + Z.of_nat (length nb) - 1) ltac:(lia)))) as B1.
  apply (img_rng_plus W (ly_F lyc)); lia.
Qed.

(* row 14, RNs: the shadow of the name's bytes.  [HIMGSH] [HNs] [HAR] [ROIMG] *)
Lemma bmb_rng2_RNs : forall (B : asyms) (GLOBS : list (Z * Z)) (RLO RHI : Z) (W : world AB1v.tfibsegs)
    (memc : word -> option byte) (lyc : alayout) (S : astate) (m : word -> option byte) (md : Model) (p b o : Z)
    (row nb : list byte),
  img_shadow_vis AB1v.tfibsegs B ->
  (p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
     RcBox.name_ok nb /\
     garr8 AB1v.tfibsegs (mrestrict (w_H W) memc) (RcSynth.rname row) (C_reac_box_model_block.bmb_z nb) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname row /\
        RcSynth.rname row + Z.of_nat (length nb) <= q + sz) /\
     (forall x, RcSynth.rname row <= x < RcSynth.rname row + Z.of_nat (length nb) ->
        in_roP AB1v.tfibsegs RLO RHI x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
     (o = 0 \/ o + 32 <= RcSynth.rname row \/ RcSynth.rname row + Z.of_nat (length nb) <= o)) ->
  AR AB1v.tfibsegs B lyc S W m md ->
  (forall x, in_roP AB1v.tfibsegs RLO RHI x -> 65536 <= x < 6283264) ->
  p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
  A.Prog.reac_box_model_block_cF.sh_cover (RNG_W (hidden_plus (w_H W) (ly_F lyc))) (RcSynth.rname row)
    (Z.of_nat (length nb)).
Proof.
  intros B GLOBS RLO RHI W memc lyc S m md p b o row nb HIMGSH HNs HAR ROIMG Hp Hb Hh Hr.
  destruct (HNs Hp Hb Hh Hr) as (Hok & _ & _ & Hx & _).
  pose proof Hok as ((L1 & L2) & _ & _).
  pose proof (ROIMG _ (proj1 (Hx (RcSynth.rname row) ltac:(lia)))) as B0.
  pose proof (ROIMG _ (proj1 (Hx (RcSynth.rname row + Z.of_nat (length nb) - 1) ltac:(lia)))) as B1.
  apply (img_sh_cover_strict B lyc S W m md _ (RcSynth.rname row) (Z.of_nat (length nb)) HIMGSH HAR eq_refl);
    lia.
Qed.

(* row 15, RJ13s: the shadow of JOIN_0013's 32 bytes (an image constant).  [HIMGSH] [HAR] *)
Lemma bmb_rng2_RJ13s : forall (B : asyms) (W : world AB1v.tfibsegs) (lyc : alayout) (S : astate)
    (m : word -> option byte) (md : Model) (b : Z),
  img_shadow_vis AB1v.tfibsegs B ->
  AR AB1v.tfibsegs B lyc S W m md ->
  b = 2 -> A.Prog.reac_box_model_block_cF.sh_cover (RNG_W (hidden_plus (w_H W) (ly_F lyc))) JOIN_0013 32.
Proof.
  intros B W lyc S m md b HIMGSH HAR _.
  apply (img_sh_cover_plus B lyc S W m md _ JOIN_0013 32 HIMGSH HAR eq_refl); unfold JOIN_0013; lia.
Qed.

(* row 16, RJ14s: the shadow of JOIN_0014's 32 bytes (an image constant).  [HIMGSH] [HAR] *)
Lemma bmb_rng2_RJ14s : forall (B : asyms) (W : world AB1v.tfibsegs) (lyc : alayout) (S : astate)
    (m : word -> option byte) (md : Model) (b : Z),
  img_shadow_vis AB1v.tfibsegs B ->
  AR AB1v.tfibsegs B lyc S W m md ->
  b = 1 -> A.Prog.reac_box_model_block_cF.sh_cover (RNG_W (hidden_plus (w_H W) (ly_F lyc))) JOIN_0014 32.
Proof.
  intros B W lyc S m md b HIMGSH HAR _.
  apply (img_sh_cover_plus B lyc S W m md _ JOIN_0014 32 HIMGSH HAR eq_refl); unfold JOIN_0014; lia.
Qed.

End Rng2.
End BmbGlueRng2.
