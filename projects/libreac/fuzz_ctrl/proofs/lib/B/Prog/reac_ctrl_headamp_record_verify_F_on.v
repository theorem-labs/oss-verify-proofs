(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_ctrl_classify_box_frameLib.v, with its module names and numbers changed; 4975 of its 5172 lines of code are new or changed and 792 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_ctrl_identity_replyRB.v, with its module paths, module names and numbers changed; 460 of its 504 lines of code are new or changed and 5128 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_finishF_on.v, with its module paths changed; 43 of its 67 lines of code are new or changed and 480 lines of the source are left out. *)
(* lib/B/Prog/reac_ctrl_headamp_record_verify_F_on.v -- route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane): the PROOFS of
   the `_on` statements in lib/B/Prog/reac_ctrl_headamp_record_verify_c_on.v. reac_ctrl_headamp_record_verify_c.v,
   reac_ctrl_headamp_record_verify.v (not in this delivery) and reac_ctrl_headamp_record_verify_F.v stay identical apart from comments; the run's Section
   BodyF (hentry_F and the lemmas under it) and the tactic rc_falseF of reac_ctrl_headamp_record_verify_F.v are reused.
   rule 24: no function proved here that is not already proved.
   This is the image-B twin of image A's route (C) proofs (lib/A/Prog/reac_ctrl_headamp_record_verify_F.v at
   36bfd511da3, :179-221 and :242-256): reac_ctrl_headamp_record_verify_holds_F_on is image B's accepted
   reac_ctrl_headamp_record_verify_holds_F (reac_ctrl_headamp_record_verify_F.v:189-231) without HSW in its intros
   (:194; that script never uses HSW), and reac_ctrl_headamp_record_verify_contract_of_F_on is image B's
   reac_ctrl_headamp_record_verify_contract_of_F (:234-246) without HSW. Image A also re-proves its old holds_F from the
   _on form; image B's holds_F is accepted and stays as it is. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcLeaf RcLeafLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT reac_ctrl_headamp_record_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_headamp_record_verify_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_headamp_record_verify_F.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Route (C): the proof of the footprint contract without the shadow_rw premise. The old script never used that
   premise. *)
Theorem reac_ctrl_headamp_record_verify_holds_F_on : reac_ctrl_headamp_record_verify_contract_F_on.
Proof.
  unfold reac_ctrl_headamp_record_verify_contract_F_on, REAC_CTRL_HEADAMP_RECORD_VERIFY,
    REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p lo b0 b1 rec -> Hp Hp40 HB Hlen HR ST HLO HD1 HD2 HCE HADR1 HADR2 HW RFR RGOT RCELL RB1 RB2 RS1 RS2.
  unfold GOT_CELL_K in RGOT. unfold CELL_K in RCELL. unfold shadow_addr in RS1, RS2.
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  pose proof (rt_shadow_rd m (p + 18) 2 _ HADR1 (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR1.
  pose proof (rt_shadow_rd m (p + 34) 6 _ HADR2 (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR2.
  pose proof (rt_addressable m (p + 18) 2 HADR1) as HAD1.
  pose proof (rt_addressable m (p + 34) 6 HADR2) as HAD2.
  set (off := ASAN_K) in HRT, HSR1, HSR2, HAD1, HAD2, RS1, RS2. clearbody off.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  step. rc_falseF.
  step. step. rc_falseF.
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_shadow_rd_munch rsegs m m1 off (p + 18) 2 _ _ HSR1 MU (fun x Hx => Hx)) as HSR1'.
  pose proof (asan_shadow_rd_munch rsegs m m1 off (p + 34) 6 _ _ HSR2 MU (fun x Hx => Hx)) as HSR2'.
  pose proof (asan_addressable_munch rsegs m m1 off (p + 18) 2 _ _ HAD1 HSR1 MU (fun x Hx => Hx)) as HAD1'.
  pose proof (asan_addressable_munch rsegs m m1 off (p + 34) 6 _ _ HAD2 HSR2 MU (fun x Hx => Hx)) as HAD2'.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  step. step. step.
  clear RG RC.
  refine (hentry_F ra _ gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p off b0 b1 rec _ _
            RNG Hp Hp40 HB Hlen HR HSR1' HSR2' HAD1' HAD2' RB1 RB2 RS1 RS2 _ _ _ _ _ _ _ _).
  intros x5 x10 x11 x13 x15 x16 x17.
  step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. cbv beta. do 9 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) | exact ST].
Qed.

(* The same step between the statements without the premise (reac_ctrl_headamp_record_verify_contract_of_F's
   script). The old theorem (reac_ctrl_headamp_record_verify_F.v:234) keeps its own proof: its premise contract_F does
   not give contract_F_on. *)
Theorem reac_ctrl_headamp_record_verify_contract_of_F_on :
  reac_ctrl_headamp_record_verify_contract_F_on -> reac_ctrl_headamp_record_verify_contract_on.
Proof.
  unfold reac_ctrl_headamp_record_verify_contract_F_on, reac_ctrl_headamp_record_verify_contract_on.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p lo b0 b1 rec E0 Hp Hp40 HB Hlen HR ST HLO HD1 HD2 HCE HADR1 HADR2 HW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  apply (evtF_evt rsegs RNG_all).
  apply (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m p lo b0 b1 rec E0 Hp Hp40 HB Hlen HR ST HLO HD1 HD2 HCE HADR1 HADR2 HW);
    apply rng_all; unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K in *; lia.
Qed.
