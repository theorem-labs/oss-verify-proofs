From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import FrameBytes rp_meter_counter_c.
Import ListNotations.
Open Scope Z_scope.

(* rp_meter_counter at 0x13588 (32 words). eo is 12 or 16 by the branch at 0x13598 / 0x135a0; the shared tail at
   0x135b0 reads f[eo..eo+3] through a0 + eo and stores the counter with `sh a0, 0(a2)` (0x135f0). *)

Lemma lor16_lit : forall x y : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned y) 8))) (bv_unsigned x))
  = Z_to_bv 64 (bv_unsigned x + 256 * bv_unsigned y).
Proof.
  intros x y. apply bv_eq. rewrite lor_bytes16.
  pose proof (byte_range x). pose proof (byte_range y). rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma meter_eo_12a : forall n bs, meter_byte bs 12 <> 0x81 -> meter_eo n bs = 12%nat.
Proof. intros n bs H. unfold meter_eo. rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity. Qed.

Lemma meter_eo_12b : forall n bs, meter_byte bs 13 <> 0 -> meter_eo n bs = 12%nat.
Proof. intros n bs H. unfold meter_eo. rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity. Qed.

Lemma meter_eo_16 : forall n bs, 13 < n -> meter_byte bs 12 = 0x81 -> meter_byte bs 13 = 0 -> meter_eo n bs = 16%nat.
Proof.
  intros n bs H H12 H13. unfold meter_eo.
  rewrite (proj2 (Z.ltb_lt _ _) H), (proj2 (Z.eqb_eq _ _) H12), (proj2 (Z.eqb_eq _ _) H13). reflexivity.
Qed.

Lemma meter_ok_small : forall n bs, n < 1000 -> meter_ok n bs = false.
Proof. intros n bs H. unfold meter_ok. cbv zeta. rewrite (proj2 (Z.leb_gt _ _) H), andb_false_r. reflexivity. Qed.

Lemma meter_ok_12 : forall n bs, meter_eo n bs = 12%nat ->
  meter_ok n bs = (18 <=? n) && (1000 <=? n) && (meter_byte bs 12 =? 0x88) && (meter_byte bs 13 =? 0x19).
Proof. intros n bs E. unfold meter_ok. cbv zeta. rewrite E. reflexivity. Qed.

Lemma meter_ok_16 : forall n bs, meter_eo n bs = 16%nat ->
  meter_ok n bs = (22 <=? n) && (1000 <=? n) && (meter_byte bs 16 =? 0x88) && (meter_byte bs 17 =? 0x19).
Proof. intros n bs E. unfold meter_ok. cbv zeta. rewrite E. reflexivity. Qed.

Lemma meter_value_12 : forall n bs, meter_eo n bs = 12%nat ->
  meter_value n bs = meter_byte bs 14 + 256 * meter_byte bs 15.
Proof. intros n bs E. unfold meter_value. cbv zeta. rewrite E. reflexivity. Qed.

Lemma meter_value_16 : forall n bs, meter_eo n bs = 16%nat ->
  meter_value n bs = meter_byte bs 18 + 256 * meter_byte bs 19.
Proof. intros n bs E. unfold meter_value. cbv zeta. rewrite E. reflexivity. Qed.

Local Ltac zc H := zify_cond H; rewrite ?zxb_u in H.

Local Ltac dec :=
  repeat match goal with
  | |- context [Z.eqb ?x ?c] => destruct (Z.eqb_spec x c); try (exfalso; lia)
  | |- context [Z.leb ?x ?c] => destruct (Z.leb_spec x c); try (exfalso; lia)
  | |- context [Z.ltb ?x ?c] => destruct (Z.ltb_spec x c); try (exfalso; lia)
  end.

Local Ltac rw_bytes :=
  repeat match goal with Eb : ?b = nth ?i ?l ?d |- context [nth ?i ?l ?d] => rewrite <- Eb end.

(* meter_ok decided from the branch facts, given eo *)
Local Ltac okb EO :=
  first [rewrite (meter_ok_12 _ _ EO) | rewrite (meter_ok_16 _ _ EO)]; unfold meter_byte; rw_bytes; dec; reflexivity.

(* an exit taken because n < 14 or n < 1000 *)
Local Ltac fin_small := apply evt_done; rewrite meter_ok_small by lia; do 4 eexists; reflexivity.

(* an exit past the eo choice: meter_ok and meter_value decided from the branch facts; on the store path the
   machine's stored value is f[eo+2] | f[eo+3] << 8 at a2 *)
Local Ltac fin :=
  apply evt_done;
  match goal with EO : meter_eo _ _ = _ |- _ =>
    first [rewrite (meter_ok_12 _ _ EO), (meter_value_12 _ _ EO) | rewrite (meter_ok_16 _ _ EO), (meter_value_16 _ _ EO)]
  end;
  unfold meter_byte; rw_bytes; dec;
  unfold zxb; rewrite ?zxb_u, ?lor16_lit;
  do 4 eexists; reflexivity.

(* from 0x135b0 when n < 1000 *)
Local Ltac small_tail := step; step; step; if_true; step; step; fin_small.

(* from 0x135b0 when n >= 1000, eo in a4 *)
Local Ltac store_ok_hyp :=
  match goal with
  | EO : meter_eo ?n ?bs = _, HW : meter_ok ?n ?bs = true -> wr_at _ _ (bv_unsigned ?a2) 2 |- _ =>
      let OK := fresh "OK" in let HS := fresh "HS" in
      assert (OK : meter_ok n bs = true) by okb EO;
      pose proof (wr_at_store_ok rsegs _ (bv_unsigned a2) 2 0 2 (HW OK) ltac:(lia) ltac:(lia)) as HS;
      replace (wa (bv_unsigned a2 + 0)) with a2 in HS
        by (unfold wa; rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)
  end.

Local Ltac big_tail :=
  let HE0 := fresh "HE0" in let HE1 := fresh "HE1" in
  step; step; step; if_false; step; step; if_false;
  step; step; step; step; if_cases HE0;
  [ zc HE0; step; step; step; fin
  | zc HE0; step; step; step; if_cases HE1;
    [ zc HE1; step; step; step; fin
    | zc HE1; store_ok_hyp; do 9 step; fin ] ].

Theorem rp_meter_counter_holds : rp_meter_counter_contract.
Proof.
  unfold rp_meter_counter_contract, RP_METER_COUNTER.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    HB H1000 HW.
  step. step. if_cases HL.
  { zc HL. step. step. step. fin_small. }
  zc HL. destruct (HB HL) as [LEN BA].
  pose proof (rd1 m _ bs 12 BA ltac:(lia)) as R12. change (Z.of_nat 12) with 12 in R12.
  pose proof (rd1 m _ bs 13 BA ltac:(lia)) as R13. change (Z.of_nat 13) with 13 in R13.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  destruct (Z.lt_ge_cases (bv_unsigned a1) 1000) as [SMALL|BIG].
  - step. step. step. if_cases H81.
    + step. step. small_tail.
    + step. step. if_cases H00; [step; small_tail | step; step; small_tail].
  - pose proof (H1000 BIG) as L20.
    pose proof (rd1 m _ bs 14 BA ltac:(lia)) as R14. change (Z.of_nat 14) with 14 in R14.
    pose proof (rd1 m _ bs 15 BA ltac:(lia)) as R15. change (Z.of_nat 15) with 15 in R15.
    pose proof (rd1 m _ bs 16 BA ltac:(lia)) as R16. change (Z.of_nat 16) with 16 in R16.
    pose proof (rd1 m _ bs 17 BA ltac:(lia)) as R17. change (Z.of_nat 17) with 17 in R17.
    pose proof (rd1 m _ bs 18 BA ltac:(lia)) as R18. change (Z.of_nat 18) with 18 in R18.
    pose proof (rd1 m _ bs 19 BA ltac:(lia)) as R19. change (Z.of_nat 19) with 19 in R19.
    remember (nth 14 bs (Z_to_bv 8 0)) as b14 eqn:E14.
    remember (nth 15 bs (Z_to_bv 8 0)) as b15 eqn:E15.
    remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
    remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
    remember (nth 18 bs (Z_to_bv 8 0)) as b18 eqn:E18.
    remember (nth 19 bs (Z_to_bv 8 0)) as b19 eqn:E19.
    step. step. step. if_cases H81.
    + zc H81.
      assert (EO : meter_eo (bv_unsigned a1) bs = 12%nat)
        by (apply meter_eo_12a; unfold meter_byte; rewrite <- E12; exact H81).
      step. step. big_tail.
    + zc H81. step. step. if_cases H00.
      * zc H00.
        assert (EO : meter_eo (bv_unsigned a1) bs = 16%nat)
          by (apply meter_eo_16; [lia | unfold meter_byte; rewrite <- E12; exact H81
                                     | unfold meter_byte; rewrite <- E13; exact H00]).
        step. big_tail.
      * zc H00.
        assert (EO : meter_eo (bv_unsigned a1) bs = 12%nat)
          by (apply meter_eo_12b; unfold meter_byte; rewrite <- E13; exact H00).
        step. step. big_tail.
Qed.
