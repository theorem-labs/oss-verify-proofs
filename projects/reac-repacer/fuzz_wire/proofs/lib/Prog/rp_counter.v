From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import FrameBytes rp_counter_c.
Import ListNotations.
Open Scope Z_scope.

(* Ported from libreac/fuzz_decode lib/Prog/reac_frame_counter.v (origin/ossv/recipes 25e3d17bdb5, blob 52dfb2ae061e):
   fuzz_wire's rp_counter (0x13608) is decode's reac_frame_counter without the slli/srli 48 pair before `ret`, so the
   walk takes 5 steps in place of 7 and the value needs no shift rewrite. *)

Lemma lor16_lit : forall x y : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned y) 8))) (bv_unsigned x))
  = Z_to_bv 64 (bv_unsigned x + 256 * bv_unsigned y).
Proof.
  intros x y. apply bv_eq. rewrite lor_bytes16.
  pose proof (byte_range x). pose proof (byte_range y). rewrite unsigned_lit by lia. reflexivity.
Qed.

Theorem rp_counter_holds : rp_counter_contract.
Proof.
  unfold rp_counter_contract, RP_COUNTER.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs LEN BA.
  pose proof (rd1 m _ bs 14 BA ltac:(lia)) as R14. change (Z.of_nat 14) with 14 in R14.
  pose proof (rd1 m _ bs 15 BA ltac:(lia)) as R15. change (Z.of_nat 15) with 15 in R15.
  remember (nth 14 bs (Z_to_bv 8 0)) as b14 eqn:E14.
  remember (nth 15 bs (Z_to_bv 8 0)) as b15 eqn:E15.
  do 5 step.
  apply evt_done.
  unfold zxb. rewrite !zxb_u, lor16_lit.
  replace (bv_unsigned b14 + 256 * bv_unsigned b15) with (counter_result bs)
    by (unfold counter_result, counter_byte; rewrite <- E14, <- E15; reflexivity).
  eexists. reflexivity.
Qed.
