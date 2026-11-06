(* check_counter walk, fuzz_wire plain c8763dfc4e81 0x13124..0x13168 (fuzz_wire.c:133-144); new. rp_counter is the
   named Section hypothesis HRC (its contract, rp_counter_c.v). The abort() call at 0x13164 is unreachable:
   rp_counter's post gives a0 = counter_result bs = bs[14] + 256 * bs[15], the very value the harness computes from
   f[14], f[15] (0x13140..0x1314c), so the `bne a0, a1` at 0x13150 falls through. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import FrameBytes rp_counter_c check_counter_c.
Import ListNotations.
Open Scope Z_scope.

Lemma chk_lor16 : forall x y : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned y) 8))) (bv_unsigned x))
  = Z_to_bv 64 (bv_unsigned x + 256 * bv_unsigned y).
Proof.
  intros x y. apply bv_eq. rewrite lor_bytes16.
  pose proof (byte_range x). pose proof (byte_range y). rewrite unsigned_lit by lia. reflexivity.
Qed.

Section C.
Hypothesis HRC : rp_counter_contract.

Theorem check_counter_holds : check_counter_contract.
Proof.
  unfold check_counter_contract, CHECK_COUNTER, CHECK_COUNTER_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    LEN BA ST HLO DJ.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  pose proof BA as (B0 & B1 & _).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  do 3 step.
  do 2 step. if_cases HL.
  - zify_cond HL. do 4 step.
    apply evt_done. do 16 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
    release_frame FR ST (bv_unsigned sp). exact ST.
  - zify_cond HL. do 2 step.
    eapply evt_cut; [eapply HRC; [ | exact BA ]; lia |].
    intros ms' (a1' & ->).
    replace (ret_pc (Z_to_bv 64 78144)) with (Z_to_bv 64 78144) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (rd1 mm _ bs 14 BA ltac:(lia)) as R14; pose proof (rd1 mm _ bs 15 BA ltac:(lia)) as R15 end.
    change (Z.of_nat 14) with 14 in R14. change (Z.of_nat 15) with 15 in R15.
    remember (nth 14 bs (Z_to_bv 8 0)) as b14 eqn:E14.
    remember (nth 15 bs (Z_to_bv 8 0)) as b15 eqn:E15.
    do 4 step.
    unfold zxb. rewrite !zxb_u, chk_lor16.
    replace (counter_result bs) with (bv_unsigned b14 + 256 * bv_unsigned b15)
      by (unfold counter_result, counter_byte; rewrite <- E14, <- E15; reflexivity).
    step. first [if_true | if_false].
    do 4 step.
    apply evt_done. do 16 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
    release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

End C.
