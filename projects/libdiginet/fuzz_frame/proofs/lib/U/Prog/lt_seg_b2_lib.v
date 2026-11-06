(* helper lemmas and the body-sum loop of the walk lt_b2 of fuzz_frame's LLVMFuzzerTestOneInput in fuzz_frame.ubsan. *)
(* Helpers for U/Prog/lt_seg_b2_walk.v: the big-endian header fields as the machine builds them from bytes (slli and
   or), the frame codes of DgnSpec.fr_code, and the body-sum loop 0x12f78-0x12f8c of LLVMFuzzerTestOneInput in
   fuzz_frame.ubsan, with its UBSan check (0x12f78: the address body + i must not wrap past 2 ^ 64). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import FrameBytes.
Import ListNotations.
Open Scope Z_scope.

(** * Bits *)

Lemma b2_lor_add : forall a b k, 0 <= k -> 0 <= a -> 0 <= b < 2 ^ k -> Z.lor (a * 2 ^ k) b = a * 2 ^ k + b.
Proof.
  intros a b k Hk Ha Hb.
  rewrite <- Z.shiftl_mul_pow2 by lia.
  assert (L : Z.land (Z.shiftl a k) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases i k).
    - rewrite (Z.testbit_neg_r a (i - k)) by lia. reflexivity.
    - destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 b i); [apply andb_false_r | lia |].
      apply Z.lt_le_trans with k; [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

Lemma b2_lor_mul : forall a c k, 0 <= k -> Z.lor (a * 2 ^ k) (c * 2 ^ k) = Z.lor a c * 2 ^ k.
Proof. intros a c k Hk. rewrite <- !Z.shiftl_mul_pow2 by lia. symmetry. apply Z.shiftl_lor. Qed.

(* lbu, lbu, slli 8, or: the be16 at index i. *)
Lemma b2_r16 : forall (l : list byte) (i : nat),
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth i l (b8 0)))) 8)))
        (bv_unsigned (zxb (nth (S i) l (b8 0)))) = be16 l i.
Proof.
  intros l i. unfold be16, at8, bz, zxb. rewrite !zxb_u.
  pose proof (byte_range (nth i l (b8 0))) as R0. pose proof (byte_range (nth (S i) l (b8 0))) as R1.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia.
  apply b2_lor_add; lia.
Qed.

(* Four lbu, slli 16, slli 24, or, slli 8, or, or: the be32 at index i. *)
Lemma b2_r32 : forall (l : list byte) (i : nat),
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth (S i) l (b8 0)))) 16)))
                                         (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth i l (b8 0)))) 24))))))
        (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth (S (S i)) l (b8 0)))) 8)))
                                         (bv_unsigned (zxb (nth (S (S (S i))) l (b8 0)))))))
  = be32 l i.
Proof.
  intros l i. unfold be32, at8, bz, zxb. rewrite !zxb_u.
  set (x0 := bv_unsigned (nth i l (b8 0))). set (x1 := bv_unsigned (nth (S i) l (b8 0))).
  set (x2 := bv_unsigned (nth (S (S i)) l (b8 0))). set (x3 := bv_unsigned (nth (S (S (S i))) l (b8 0))).
  pose proof (byte_range (nth i l (b8 0))) as R0. pose proof (byte_range (nth (S i) l (b8 0))) as R1.
  pose proof (byte_range (nth (S (S i)) l (b8 0))) as R2. pose proof (byte_range (nth (S (S (S i))) l (b8 0))) as R3.
  fold x0 x1 x2 x3 in R0, R1, R2, R3.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (x1 * 2 ^ 16)) by lia. rewrite (unsigned_lit (x0 * 2 ^ 24)) by lia.
  rewrite (unsigned_lit (x2 * 2 ^ 8)) by lia.
  rewrite (b2_lor_add x2 x3 8) by lia.
  rewrite (Z.lor_comm (x1 * 2 ^ 16) (x0 * 2 ^ 24)).
  replace (x0 * 2 ^ 24) with ((x0 * 2 ^ 8) * 2 ^ 16) by lia.
  rewrite (b2_lor_mul (x0 * 2 ^ 8) x1 16) by lia.
  rewrite (b2_lor_add x0 x1 8) by lia.
  rewrite (unsigned_lit ((x0 * 2 ^ 8 + x1) * 2 ^ 16)) by lia.
  rewrite (unsigned_lit (x2 * 2 ^ 8 + x3)) by lia.
  rewrite (b2_lor_add (x0 * 2 ^ 8 + x1) (x2 * 2 ^ 8 + x3) 16) by lia.
  lia.
Qed.

(* The low 16 bits of a sum, as the sh at 0x13000 stores them. *)
Lemma b2_le2_mod : forall s, 0 <= s < 2 ^ 64 -> le2 (Z_to_bv 64 (s mod 2 ^ 16)) = le2 (Z_to_bv 64 s).
Proof.
  intros s Hs. pose proof (Z.mod_pos_bound s (2 ^ 16) ltac:(lia)) as M. unfold le2.
  rewrite (unsigned_lit (s mod 2 ^ 16)) by lia. rewrite (unsigned_lit s) by lia.
  apply Z_to_le_bytes_mod. lia.
Qed.

Lemma b2_mod16_8 : forall z, z mod 16 = 0 -> z mod 8 = 0.
Proof. intros z H. Z.div_mod_to_equations. lia. Qed.

(** * Bytes and cells *)

Lemma b2_rd : forall m a (bs : list byte) (k : Z), bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) 1 = Some [nth (Z.to_nat k) bs (b8 0)].
Proof.
  intros m a bs k H Hk Hl.
  pose proof (rd1 m a bs (Z.to_nat k) H Hl) as R. rewrite Z2Nat.id in R by lia. exact R.
Qed.

Lemma b2_bytes_sub : forall m a l (i j : nat), bytes_at rsegs m a l -> (i + j <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat i) (firstn j (skipn i l)).
Proof.
  intros m a l i j H Hij. rewrite <- (firstn_skipn i l) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min i (length l)) with i in H by lia.
  rewrite <- (firstn_skipn j (skipn i l)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma b2_rw_ro : forall m A cs, rw_cells rsegs m A cs -> ro_cells rsegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

Lemma b2_rw_hd : forall m A c cs, rw_cells rsegs m A (c :: cs) -> ro_cells rsegs m A [c].
Proof.
  intros m A c cs [[Hwf Hb] _]. cbn [cells_wf] in Hwf. destruct Hwf as [Hc _]. split.
  - cbn [cells_wf]. split; [exact Hc | exact I].
  - cbn [cells_bytes] in *. rewrite app_nil_r. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

(* The same bytes under other cells. *)
Lemma b2_rw_same : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Hb' Hs. split; [split|].
  - exact Hwf'.
  - rewrite Hb'. exact Hb.
  - rewrite Hs. exact Hw.
Qed.

(** * Frame codes *)

Lemma b2_code_short : forall b, (length b < 30)%nat -> fr_code b = -2.
Proof. intros b H. unfold fr_code. rewrite (proj2 (Nat.ltb_lt _ _) H). reflexivity. Qed.

Lemma b2_code_eth : forall b, (30 <= length b)%nat -> fr_ethertype b <> 0x885f -> fr_code b = -3.
Proof.
  intros b H E. unfold fr_code. rewrite (proj2 (Nat.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) E). reflexivity.
Qed.

Lemma b2_code_len : forall b, (30 <= length b)%nat -> fr_ethertype b = 0x885f ->
  fr_numbytes b < 16 \/ Z.of_nat (length b) - 14 < fr_numbytes b -> fr_code b = -4.
Proof.
  intros b H E L. unfold fr_code. rewrite (proj2 (Nat.ltb_ge _ _) H), (proj2 (Z.eqb_eq _ _) E). cbn [negb].
  destruct L as [L|L].
  - rewrite (proj2 (Z.ltb_lt _ _) L). reflexivity.
  - rewrite (proj2 (Z.ltb_lt _ _) L), orb_true_r. reflexivity.
Qed.

Lemma b2_code_zero : forall b, (30 <= length b)%nat -> fr_ethertype b = 0x885f ->
  16 <= fr_numbytes b -> fr_numbytes b <= Z.of_nat (length b) - 14 -> fr_code b = 0.
Proof.
  intros b H E L1 L2. unfold fr_code. rewrite (proj2 (Nat.ltb_ge _ _) H), (proj2 (Z.eqb_eq _ _) E). cbn [negb].
  rewrite (proj2 (Z.ltb_ge _ _) L1), (proj2 (Z.ltb_ge _ _) L2). reflexivity.
Qed.

(** * Tactics *)

Ltac b2_rdb BB k :=
  let HR := fresh "HR" in
  pose proof (b2_rd _ _ _ k BB ltac:(lia) ltac:(lia)) as HR;
  let n := eval vm_compute in (Z.to_nat k) in change (Z.to_nat k) with n in HR.

Ltac b2_uns := rewrite ?unsigned_lit by lia.
Ltac b2_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; b2_uns; solve_cond_rec]
  end.
(* A branch on a closed condition. *)
Ltac b2_br_vm v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(** * The body-sum loop, 0x12f78-0x12f8c *)
(* a1 is the body address A, a2 its length n, a3 the index i, a0 the sum of the first i bytes, a4 is not A
   (0x12f74). Each pass: the UBSan check not A <u i (0x12f78, to the trap at 0x1300c), a5 = A + i, lbu a5,
   i += 1, a0 += a5, bne a2, a3. *)
Section Loop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A n : Z) (l : list byte).
Hypothesis HBL : bytes_at rsegs m A l.
Hypothesis HN : n = Z.of_nat (length l).
Hypothesis HA4 : bv_unsigned a4 = 18446744073709551615 - A.
Hypothesis HLN : Z.of_nat (length l) < 2 ^ 26.

Local Abbreviation ST pc a0 a3 a5 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 A) (Z_to_bv 64 n) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma b2_loop : forall (Q : machine_state -> Prop) (r i : nat) (a5 : word),
  (i + S r = length l)%nat ->
  (forall a5' : word, evt rsegs Q (ST 0x12f90 (Z_to_bv 64 (sum_bytes l)) (Z_to_bv 64 n) a5')) ->
  evt rsegs Q (ST 0x12f78 (Z_to_bv 64 (sum_bytes (firstn i l))) (Z_to_bv 64 (Z.of_nat i)) a5).
Proof.
  intros Q r. induction r as [|r IH]; intros i a5 Hi K.
  all: pose proof (bytes_at_bound _ _ _ _ HBL) as HB.
  all: pose proof (rd1 m A l i HBL ltac:(lia)) as HR.
  all: pose proof (sum_bytes_range (firstn i l)) as SR; rewrite length_firstn in SR.
  all: pose proof (byte_range (nth i l (Z_to_bv 8 0))) as RB.
  all: step; b2_br false; step; step; clear HR; step; step; step.
  all: assert (ES : sum_bytes (firstn (S i) l) = sum_bytes (firstn i l) + bv_unsigned (zxb (nth i l (Z_to_bv 8 0))))
         by (rewrite sum_bytes_firstn_S by lia; unfold at8, bz, zxb, b8; rewrite zxb_u; reflexivity).
  all: rewrite <- ES; replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
  - b2_br false. rewrite firstn_all2 by lia. replace (Z.of_nat (S i)) with n by lia. apply K.
  - b2_br true. apply (IH (S i)); [lia | exact K].
Qed.

End Loop.
