(* Word-level facts shared by the UBSan walks of reac-repacer's [digits] (repace_conf.c:101, 0x13540) and the
   harness's [number] (fuzz_lock.c:64, 0x131cc): the two functions compile to the same instructions. Each lemma
   decides one branch condition the walk meets, in the form the step machinery leaves it.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import StrFun LockSpec.
Import ListNotations.
Open Scope Z_scope.

Lemma firstn1_skipn : forall {X} (l : list X) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma rdb : forall m A l (i : nat) b, bytes_at rsegs m A l -> nth_error l i = Some b ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m A l i b BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m A l i 1 BL ltac:(lia)). f_equal. apply firstn1_skipn. exact N.
Qed.

Lemma skipn_nth : forall {X} (l : list X) i b, nth_error l i = Some b -> skipn i l = b :: skipn (S i) l.
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma byte_at : forall (l : list byte) i, (i < length l)%nat -> exists b, nth_error l i = Some b.
Proof. intros l i Hi. destruct (nth_error l i) eqn:N; [eexists; reflexivity|]. apply nth_error_None in N. lia. Qed.

Lemma sgn_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec z (2^63)); lia. Qed.

Lemma pow_step : forall i : nat, 10 ^ Z.of_nat (S i) = 10 * 10 ^ Z.of_nat i.
Proof. intros i. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. Qed.

Lemma pow_le17 : forall i : nat, (i <= 17)%nat -> 10 ^ Z.of_nat i <= 10 ^ 17.
Proof. intros i Hi. apply Z.pow_le_mono_r; lia. Qed.

Lemma land15 : forall c, 48 <= c <= 57 -> Z.land c 15 = c - 48.
Proof.
  intros c Hc. pose proof (Z.land_ones c 4 ltac:(lia)) as LO.
  change (Z.ones 4) with 15 in LO. change (2 ^ 4) with 16 in LO. rewrite LO.
  Z.div_mod_to_equations. lia.
Qed.

(* the length test at +0x8 [addi a2,a1,-19; li a3,-18; bgeu a2,a3]: taken iff 1 <= len <= 18 *)
Lemma len_test : forall n, 0 <= n < 2^64 ->
  bv_ltu (Z_to_bv 64 (n + -19)) (Z_to_bv 64 (-18)) = (n =? 0) || (18 <? n).
Proof.
  intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  change ((-18) mod 2^64) with 18446744073709551598.
  destruct (Z_lt_le_dec n 19) as [L|L].
  - rewrite <- (Z.mod_add (n + -19) 1 (2^64)) by lia. rewrite Z.mod_small by lia.
    apply eq_true_iff_eq. rewrite orb_true_iff, Z.ltb_lt, Z.eqb_eq, Z.ltb_lt. lia.
  - rewrite Z.mod_small by lia.
    apply eq_true_iff_eq. rewrite orb_true_iff, Z.ltb_lt, Z.eqb_eq, Z.ltb_lt. lia.
Qed.

(* [snez a3,a0] at +0x18 with a0 = s <> 0 *)
Lemma snez_ok : forall s, 0 < s < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 s) = Z_to_bv 64 1.
Proof.
  intros s Hs. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit s) by lia.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. destruct (Z.ltb_spec 0 s); [reflexivity | lia].
Qed.

(* UBSan pointer check at +0x30..+0x38 [seqz t0,a6; xor t0,a3,t0; beqz t0 -> trap]: with a3 = 1 (s <> 0) and
   a6 = p <> 0 the trap branch is not taken *)
Lemma seqz_ok : forall p, 0 < p < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.lxor 1 (bv_unsigned (v_sltiu (Z_to_bv 64 p) 1)))) (Z_to_bv 64 0) = false.
Proof.
  intros p Hp. unfold v_sltiu. rewrite (unsigned_lit p) by lia.
  change (bv_wrap 64 1) with 1. destruct (Z.ltb_spec p 1); [lia|]. vm_compute. reflexivity.
Qed.

(* the digit test at +0x44..+0x48 [addi t1,t0,-58; bltu t1,a4(-10)]: taken iff the byte is no decimal digit *)
Lemma dig_test : forall b : byte,
  bv_ltu (Z_to_bv 64 (bv_unsigned (zxb b) + -58)) (Z_to_bv 64 (-10)) = negb ((48 <=? bz b) && (bz b <=? 57)).
Proof.
  intros b. pose proof (byte_range b) as R. unfold zxb, bz. rewrite (unsigned_lit (bv_unsigned b)) by lia.
  pose proof (brute256_ok (fun c => Bool.eqb (bv_ltu (Z_to_bv 64 (c + -58)) (Z_to_bv 64 (-10)))
                                              (negb ((48 <=? c) && (c <=? 57))))
                ltac:(vm_compute; reflexivity) (bv_unsigned b) R) as H.
  apply Bool.eqb_prop in H. exact H.
Qed.

(* UBSan overflow check of v * 10 at +0x4c..+0x58 [mulh t2,a2,a5; mul t1,a2,a5; srai a2,t1,63; bne t2,a2 -> trap]:
   no overflow while v < 10^17 *)
Lemma mul_ok : forall v, 0 <= v < 10 ^ 17 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 v) * 10) 64))
               (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v) * 10))) 63))) = false.
Proof.
  intros v Hv. rewrite (sgn_small v) by lia. rewrite (unsigned_lit v) by lia. rewrite (sgn_small (v * 10)) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  rewrite (Z.div_small (v * 10) (2 ^ 64)) by lia. rewrite (Z.div_small (v * 10) (2 ^ 63)) by lia.
  vm_compute. reflexivity.
Qed.

(* UBSan overflow check of v * 10 + d at +0x5c..+0x6c [andi t0,t0,15; add a2,t1,t0; slt t1,a2,t1; slti t0,t0,0;
   bne t0,t1 -> trap]: no overflow while v < 10^17 and the byte is a digit *)
Lemma add_ok : forall v (b : byte), 0 <= v < 10 ^ 17 -> (48 <=? bz b) && (bz b <=? 57) = true ->
  negb (bv_eqb (v_slti (Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) 15)) 0)
               (v_slt (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v) * 10 + Z.land (bv_unsigned (zxb b)) 15))
                      (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v) * 10)))) = false.
Proof.
  intros v b Hv D. apply andb_true_iff in D. destruct D as [D1 D2]. apply Z.leb_le in D1, D2. unfold bz in D1, D2.
  unfold zxb. rewrite (unsigned_lit (bv_unsigned b)) by lia. rewrite (unsigned_lit v) by lia.
  rewrite (land15 (bv_unsigned b)) by lia.
  unfold v_slti, v_slt, c_lts, zsig, bv_lts.
  rewrite (sgn_small (bv_unsigned b - 48)) by lia.
  rewrite (sgn_small (v * 10 + (bv_unsigned b - 48))) by lia. rewrite (sgn_small (v * 10)) by lia.
  destruct (Z.ltb_spec (bv_unsigned b - 48) 0); [lia|].
  destruct (Z.ltb_spec (v * 10 + (bv_unsigned b - 48)) (v * 10)); [lia|].
  vm_compute. reflexivity.
Qed.

(* the value [add a2,t1,t0] leaves: v * 10 + (c - 48) *)
Lemma dval : forall v (b : byte), 0 <= v < 10 ^ 17 -> (48 <=? bz b) && (bz b <=? 57) = true ->
  bv_unsigned (Z_to_bv 64 v) * 10 + Z.land (bv_unsigned (zxb b)) 15 = v * 10 + (bz b - 48).
Proof.
  intros v b Hv D. apply andb_true_iff in D. destruct D as [D1 D2]. apply Z.leb_le in D1, D2. unfold bz in *.
  unfold zxb. rewrite (unsigned_lit (bv_unsigned b)) by lia. rewrite (unsigned_lit v) by lia.
  rewrite (land15 (bv_unsigned b)) by lia. reflexivity.
Qed.

(* the digits' value bound: one more digit keeps it below 10^(i+1) *)
Lemma dig_bound : forall (i : nat) v (b : byte), 0 <= v < 10 ^ Z.of_nat i -> (48 <=? bz b) && (bz b <=? 57) = true ->
  0 <= v * 10 + (bz b - 48) < 10 ^ Z.of_nat (S i).
Proof.
  intros i v b Hv D. apply andb_true_iff in D. destruct D as [D1 D2]. apply Z.leb_le in D1, D2.
  rewrite pow_step. lia.
Qed.
