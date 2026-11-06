(* The footprint twin of reac_braid_encode_ns0.v reac_braid_encode_ns0_holds (image B; RECIPE.md steps 1-2 (a working note, not in this delivery)):
   the same run as an ExecF.evtF under a footprint RNG, by the script of reac_braid_encode_ns0.v over
   StepF's step. The run's only data accesses are the saves and the restores in its own 128-byte frame, closed
   from the one rng premise of the statement. reac_braid_encode_ns0.v and its theorem are unchanged (the halts
   proofs use them). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_braid_encode_ns0_c reac_braid_encode_ns0.
(* Last: StepF's step / if_cases (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_braid_encode_ns0_F_holds : reac_braid_encode_ns0_contract_F.
Proof.
  unfold reac_braid_encode_ns0_contract_F, REAC_BRAID_ENCODE, REAC_BRAID_ENCODE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ns
    Hns Ha4 ST RFR.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 128 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; exact (rc_wv_stk rsegs m _ _ x ST Hx)).
  carve_frame 128%nat ST.
  do 15 step.
  replace (bv_lts (Z_to_bv 64 0) a4) with false by (rewrite Ha4; symmetry; apply rbe_lts0; lia). cbn [negb].
  do 15 step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) | exact ST].
Qed.

(* RECIPE step 1: the old theorem's statement, back from the footprint form at ExecF.RNG_all. *)
Theorem reac_braid_encode_ns0_holds_of_F : reac_braid_encode_ns0_contract.
Proof. exact (reac_braid_encode_ns0_contract_of_F reac_braid_encode_ns0_F_holds). Qed.
