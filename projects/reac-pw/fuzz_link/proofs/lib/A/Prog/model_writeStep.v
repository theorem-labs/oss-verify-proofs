(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v, with its module names changed; 115 of its 154 lines of code are new or changed and 300 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A: how a cut's `mw_base` (lib/A/Prog/model_writeDefs.v) moves along
   the walk, and what it gives at a cut:
   - mw_akept_un: the kept clause of a step that changes no byte outside a set X' and the step's window (a symbolic
     run's frame, a runtime call's post), relative to the step's start;
   - mw_base_step: the base at the end of a step from the base at its start and the step's kept clause, when the
     step leaves the registers the base names, the saves and F's flag-address word alone;
   - mw_rd_at / mw_blk_at: a byte of the read set, and a byte of the model block, at a cut before talk (X = NoX)
     is the call's;
   - mw_pf_refuse: the EXIT cut's result clause for a refusal (the code returns rcv <= 0 and writes no model byte).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC88.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs model_writeKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Set Default Proof Using "All".

(* the call's window and its realigned sp *)
Lemma mw_sp_facts : forall cx, mw_pre SK B cx ->
  alloc_ceiling + MODEL_WRITE_AK <= mw_sp cx /\ mw_sp cx <= 2 ^ 47 /\ mw_sp cx mod 16 = 0 /\
  mw_sp cx - 144 <= mw_sp1 cx <= mw_sp cx - 128 /\ mw_sp1 cx mod 32 = 0 /\ mw_sp1 cx mod 16 = 0 /\
  mw_sp0 cx - mw_STK cx <= mw_sp cx - MODEL_WRITE_AK /\ mw_sp cx <= mw_sp0 cx.
Proof.
  intros cx HPX. pose proof HPX as ((HJ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _) & _ & _).
  pose proof (aj_window_bounds SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hceil & H47 & HSTK & HXO).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity.
  pose proof asan_consts as ((C1a & C1b) & _).
  unfold mw_sp1, mw_sp, MW_FRAME in *.
  destruct (sp1_facts (spZ (mw_regs cx) - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
    as (H1 & H2 & H3).
  repeat split; lia.
Qed.

(* ---- the kept clause of a step that changes no byte outside X' and its window ---- *)
Lemma mw_akept_un : forall ly3 S3 (W3 : world SEGS) m3 md3 m4 slo shi (X' : Z -> Prop),
  AR SEGS B ly3 S3 W3 m3 md3 -> alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, slo <= a < shi -> apresent (w_H W3) m3 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X' a -> ~ (slo <= a < shi) -> aview SEGS (w_H W3) m4 a = aview SEGS (w_H W3) m3 a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H W3) m3 a -> apresent (w_H W3) m4 a) ->
  akept SEGS B ly3 S3 W3 m3 W3 m4 slo shi X'.
Proof.
  intros ly3 S3 W3 m3 md3 m4 slo shi X' HAR Hslo Hshi Hwin UN Hpr.
  eapply (akept_step SK SEGS B LAWS pa_segs_low ly3 S3 W3 m3 md3 W3 m3 W3 m4 slo shi X' X'
    (fun a => X' a \/ slo <= a < shi) HAR Hslo Hshi).
  - exact (akept_refl SK SEGS B LAWS pa_segs_low ly3 S3 W3 m3 slo shi X' Hwin).
  - intros a Ha Hn. apply UN; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H].
  - exact Hpr.
  - intros a H; exact H.
  - intros a [H | H]; [left; exact H | right; exact H].
Qed.

(* the registers a cut's base names, unchanged from R to R' *)
Definition mw_rsame (R R' : bvmap 5 word) : Prop :=
  getr R' 2 = getr R 2 /\ getr R' 9 = getr R 9 /\ getr R' 8 = getr R 8 /\ getr R' 18 = getr R 18 /\
  getr R' 27 = getr R 27 /\ getr R' 21 = getr R 21 /\ getr R' 23 = getr R 23 /\ getr R' 19 = getr R 19 /\
  getr R' 20 = getr R 20 /\ getr R' 3 = getr R 3 /\ getr R' 4 = getr R 4.

(* ---- the base along a step ---- *)
Lemma mw_base_step : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3 ly4 S4 W4
    (ms4 : machine_state) md4 slo shi (X' : Z -> Prop),
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  ms_resv ms4 = None -> ms_svc_pending ms4 = None -> ms_rom ms4 = seg_rom SEGS ->
  ms_fregs ms4 = fp_regs -> ms_fcsr ms4 = fp_csr ->
  ajournal_gx SEGS B (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx)
    ly4 S4 W4 (ms_mem ms4) md4 (mw_k cx) ->
  frames S4 = frames S3 -> (exists fs, S4 = set_fs fs (mw_Sc cx)) ->
  Permutation (ablocks B ly4 S4) (ablocks B (mw_lyc cx) (mw_Sc cx)) ->
  akept SEGS B ly3 S3 W3 (ms_mem ms3) W4 (ms_mem ms4) slo shi X' ->
  mw_sp cx - MODEL_WRITE_AK <= slo -> shi <= mw_sp1 cx ->
  (forall a, X' a -> X a \/ aside_rng (mw_lyc cx) MW_CID fpos a) ->
  (forall a, mw_sp cx - 104 <= a < mw_sp cx -> ~ X' a) ->
  (forall a, mw_F cx fpos + MW_FLAGPTR <= a < mw_F cx fpos + MW_FLAGPTR + 8 -> ~ X' a) ->
  mw_rsame (ms_regs ms3) (ms_regs ms4) ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  mw_base SK B cx fpos X ly4 S4 W4 ms4 md4.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 ly4 S4 W4 ms4 md4 slo shi X' HPX HB Hr Hs Hro Hf Hc HJ4 Hfr4 HfS4 Hperm4
    HK4 Hslo Hshi HX' HXs HXf HR Hfd Hfs.
  pose proof (mw_sp_facts cx HPX) as (Hsp1 & Hsp2 & Hsp3 & Hsp4 & Hsp5 & Hsp6 & Hsp7 & Hsp8).
  pose proof (mw_pre_jc SK B cx HPX) as HJc.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKv : MODEL_WRITE_AK = 8416) by reflexivity.
  unfold mw_base in HB |- *. cbv zeta in HB |- *.
  destruct HB as (_ & _ & _ & _ & _ & HJ3 & Hfrs3 & Hnin & Hfpos & HfS & Hperm & Hwit & Hfa &
    R2 & R9 & R8 & R18 & R27 & R21 & R23 & R19 & R20 & R3 & R4 & Hsra & Hsav & Hflw & HK & Hfd3 & Hfs3).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HARc.
  assert (Hfin3 : In (MW_CID, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 MW_CID fpos HAR3 Hfin3) as (HF4096 & HFceil & _).
  rewrite Hfa in HF4096, HFceil. change (fs_frame_bytes MW_CID) with 1024 in HFceil.
  pose proof HK4 as (K1 & _ & _ & K4 & _ & _).
  assert (Hsav4 : forall a, mw_sp cx - 104 <= a < mw_sp cx - 7 ->
     rdword (aview SEGS (w_H W4) (ms_mem ms4)) a = rdword (aview SEGS (w_H W3) (ms_mem ms3)) a).
  { intros a Ha. apply mw_rdword_ext. intros i Hi. apply K1; [lia | lia | apply HXs; lia]. }
  assert (Hflw4 : rdword (aview SEGS (w_H W4) (ms_mem ms4)) (mw_F cx fpos + MW_FLAGPTR) =
                  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (mw_F cx fpos + MW_FLAGPTR)).
  { apply mw_rdword_ext. intros i Hi. apply (K4 MW_CID fpos); [exact Hfin3 | | apply HXf; lia].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes MW_CID) with 1024.
    unfold mw_F, MW_FLAGPTR. lia. }
  split; [exact Hr|]. split; [exact Hs|]. split; [exact Hro|]. split; [exact Hf|]. split; [exact Hc|].
  split; [exact HJ4|]. split; [rewrite Hfr4; exact Hfrs3|]. split; [exact Hnin|]. split; [exact Hfpos|].
  split; [exact HfS4|]. split; [exact Hperm4|]. split; [exact Hwit|].
  split.
  { intros c q. rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ4)).
    rewrite <- (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJc)).
    reflexivity. }
  destruct HR as (H2 & H9 & H8 & H18 & H27 & H21 & H23 & H19 & H20 & H3 & H4).
  split; [rewrite H2; exact R2|].
  split; [rewrite H9; exact R9|].
  split; [rewrite H8; exact R8|].
  split; [rewrite H18; exact R18|].
  split; [rewrite H27; exact R27|].
  split; [rewrite H21; exact R21|].
  split; [rewrite H23; exact R23|].
  split; [rewrite H19; exact R19|].
  split; [rewrite H20; exact R20|].
  split; [rewrite H3; exact R3|].
  split; [rewrite H4; exact R4|].
  split; [rewrite Hsav4 by lia; exact Hsra|].
  split; [intros j Hj; rewrite Hsav4 by lia; exact (Hsav j Hj)|].
  split; [rewrite Hflw4; exact Hflw|].
  split.
  { eapply (akept_trans_ly SK SEGS B LAWS pa_segs_low (mw_lyc cx) (mw_Sc cx) (mw_W cx) (mw_memc cx) ly3 S3 W3
      (ms_mem ms3) W4 (ms_mem ms4) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) slo shi _ X' _ ltac:(lia) ltac:(lia) HK HK4).
    - lia.
    - lia.
    - intros bb mm Hb. apply (Permutation_in (l := ablocks B (mw_lyc cx) (mw_Sc cx)));
        [apply Permutation_sym; exact Hperm | exact Hb].
    - intros f Hf'. rewrite Hfrs3. right. exact Hf'.
    - exact Hfa.
    - intros a H; exact H.
    - exact HX'. }
  split; [rewrite Hfd; exact Hfd3 | rewrite Hfs; exact Hfs3].
Qed.

End b.
End a.
