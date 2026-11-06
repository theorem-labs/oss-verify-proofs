(* proves the UBSan contract of the static rd32 (fuzz_frame.ubsan, 0x13c00), with its two pointer-overflow traps not taken. *)
(* Walk of rd32 (src/diginet_frame.c:12-15 at 835f336c) in fuzz_frame.ubsan, 0x13c00.
   The UBSan checks at 0x13c04 (p = 2^64 - 1) and 0x13c10 (p + 3 wraps to 0 or 1) branch to the trap
   at 0x13c40; bytes_at of the 4 bytes gives p + 4 <= 2^64, so neither is taken. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import FrameBytes rd32_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

(* An or of disjoint bit ranges is a sum. *)
Lemma lor_mul_add : forall a b k, 0 <= a -> 0 <= k -> 0 <= b < 2^k -> Z.lor (a * 2^k) b = a * 2^k + b.
Proof.
  intros a b k Ha Hk Hb.
  assert (L : Z.land (a * 2^k) b = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k) as [Hnk|Hnk].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite <- (Z.mod_small b (2^k)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

(* bv_swrap 32 of a 32-bit value, as a 64-bit register. *)
Lemma sw32_u : forall v, -2^31 <= v < 2^32 ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 v)) = if v mod 2^32 <? 2^31 then v mod 2^32 else v mod 2^32 + 2^64 - 2^32.
Proof.
  intros v Hv. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity.
  replace (bv_modulus 32) with (2^32) by reflexivity.
  destruct (Z.ltb_spec (v mod 2^32) (2^31)); Z.div_mod_to_equations; lia.
Qed.

(* The value of a0 at 0x13c3c: the four bytes, big-endian, sign-extended from bit 31. *)
Lemma rd32_val : forall b0 b1 b2 b3 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 16)))
                                                  (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (zxb b0)) 24)))))))
                     (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b2)) 8)))
                                                     (bv_unsigned (zxb b3))))))
  = sx32 (Z_to_bv 64 (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16 + bv_unsigned b2 * 2^8 + bv_unsigned b3)).
Proof.
  intros b0 b1 b2 b3.
  pose proof (byte_range b0) as X0. pose proof (byte_range b1) as X1.
  pose proof (byte_range b2) as X2. pose proof (byte_range b3) as X3.
  apply bv_eq. unfold zxb, sx32. rewrite !zxb_u, !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (bv_unsigned b1 * 2^16)) by lia.
  rewrite (unsigned_lit (bv_unsigned b2 * 2^8)) by lia.
  rewrite (lor_mul_add (bv_unsigned b2) (bv_unsigned b3) 8) by lia.
  rewrite (unsigned_lit (bv_unsigned b2 * 2^8 + bv_unsigned b3)) by lia.
  rewrite (unsigned_lit (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16 + bv_unsigned b2 * 2^8 + bv_unsigned b3)) by lia.
  rewrite !sw32_u by lia.
  rewrite (Z.mod_small (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16 + bv_unsigned b2 * 2^8 + bv_unsigned b3)) by lia.
  rewrite (Z.lor_comm (bv_unsigned b1 * 2^16)).
  destruct (Z.ltb_spec (bv_unsigned b0) 128) as [H0|H0].
  - rewrite (Z.mod_small (bv_unsigned b0 * 2^24)) by lia.
    replace (bv_unsigned b0 * 2^24 <? 2^31) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16 + bv_unsigned b2 * 2^8 + bv_unsigned b3 <? 2^31)
      with true by (symmetry; apply Z.ltb_lt; lia).
    cbv iota.
    rewrite (lor_mul_add (bv_unsigned b0) (bv_unsigned b1 * 2^16) 24) by lia.
    rewrite (unsigned_lit (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16)) by lia.
    replace (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16) with ((bv_unsigned b0 * 2^8 + bv_unsigned b1) * 2^16) by ring.
    rewrite (lor_mul_add (bv_unsigned b0 * 2^8 + bv_unsigned b1) (bv_unsigned b2 * 2^8 + bv_unsigned b3) 16) by lia.
    rewrite unsigned_lit by lia. ring.
  - rewrite (Z.mod_small (bv_unsigned b0 * 2^24)) by lia.
    replace (bv_unsigned b0 * 2^24 <? 2^31) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16 + bv_unsigned b2 * 2^8 + bv_unsigned b3 <? 2^31)
      with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    replace (bv_unsigned b0 * 2^24 + 2^64 - 2^32) with ((bv_unsigned b0 + 2^40 - 2^8) * 2^24) by ring.
    rewrite (lor_mul_add (bv_unsigned b0 + 2^40 - 2^8) (bv_unsigned b1 * 2^16) 24) by lia.
    rewrite (unsigned_lit ((bv_unsigned b0 + 2^40 - 2^8) * 2^24 + bv_unsigned b1 * 2^16)) by lia.
    replace ((bv_unsigned b0 + 2^40 - 2^8) * 2^24 + bv_unsigned b1 * 2^16)
      with ((bv_unsigned b0 * 2^8 + 2^48 - 2^16 + bv_unsigned b1) * 2^16) by ring.
    rewrite (lor_mul_add (bv_unsigned b0 * 2^8 + 2^48 - 2^16 + bv_unsigned b1) (bv_unsigned b2 * 2^8 + bv_unsigned b3) 16)
      by lia.
    rewrite unsigned_lit by lia. ring.
Qed.

Theorem rd32_holds : rd32_contract.
Proof.
  unfold rd32_contract, RD32.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p l
    Hlen BA.
  pose proof (bytes_at_bound rsegs m p l BA) as BB. rewrite Hlen in BB. change (Z.of_nat 4) with 4 in BB.
  pose proof (rd1 m _ l 0 BA ltac:(lia)) as R0. change (Z.of_nat 0) with 0 in R0. rewrite Z.add_0_r in R0.
  pose proof (rd1 m _ l 1 BA ltac:(lia)) as R1. change (Z.of_nat 1) with 1 in R1.
  pose proof (rd1 m _ l 2 BA ltac:(lia)) as R2. change (Z.of_nat 2) with 2 in R2.
  pose proof (rd1 m _ l 3 BA ltac:(lia)) as R3. change (Z.of_nat 3) with 3 in R3.
  remember (nth 0 l (Z_to_bv 8 0)) as b0 eqn:E0.
  remember (nth 1 l (Z_to_bv 8 0)) as b1 eqn:E1.
  remember (nth 2 l (Z_to_bv 8 0)) as b2 eqn:E2.
  remember (nth 3 l (Z_to_bv 8 0)) as b3 eqn:E3.
  pose proof (byte_range b0) as X0. pose proof (byte_range b1) as X1.
  pose proof (byte_range b2) as X2. pose proof (byte_range b3) as X3.
  assert (BE : be32 l 0 = bv_unsigned b0 * 2^24 + bv_unsigned b1 * 2^16 + bv_unsigned b2 * 2^8 + bv_unsigned b3).
  { unfold be32, at8, bz, b8. rewrite <- E0, <- E1, <- E2, <- E3. reflexivity. }
  rewrite BE.
  (* 0x13c04 beq a0, -1: the UBSan trap of p + 1, not taken (p + 4 <= 2^64). *)
  step. step. br false.
  (* 0x13c10 bltu p + 3, 2: the UBSan trap of p + 3, not taken. *)
  step. step. step. br false.
  (* the four byte loads, the shifts and ors, ret *)
  step. step. step. step.
  step. step. step. step. step. step.
  rewrite rd32_val.
  step.
  apply evt_done. do 3 eexists. reflexivity.
Qed.
