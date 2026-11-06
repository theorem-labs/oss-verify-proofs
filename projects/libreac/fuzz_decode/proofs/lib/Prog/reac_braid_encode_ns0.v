From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import reac_braid_encode_ns0_c.
Import ListNotations.
Open Scope Z_scope.

Lemma rbe_lts0 : forall ns, -2^63 <= ns <= 0 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 ns) = false.
Proof.
  intros ns Hns. rewrite bv_lts_zero_l, unsigned_lit_wrap.
  destruct (Z.eq_dec ns 0) as [->|Hne].
  - reflexivity.
  - rewrite <- (Z.mod_add ns 1) by lia. rewrite Z.mod_small by lia.
    apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

Theorem reac_braid_encode_ns0_holds : reac_braid_encode_ns0_contract.
Proof.
  unfold reac_braid_encode_ns0_contract, REAC_BRAID_ENCODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ns
    Hns Ha4.
  step.
  replace (bv_lts (Z_to_bv 64 0) a4) with false by (rewrite Ha4; symmetry; apply rbe_lts0; lia). cbn [negb].
  step.
  apply evt_done. reflexivity.
Qed.
