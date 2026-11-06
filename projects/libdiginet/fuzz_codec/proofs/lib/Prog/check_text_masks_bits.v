From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
Import ListNotations.
Open Scope Z_scope.

(** A boolean test of the integers lo, ..., lo + k - 1, checked by computation. *)
Lemma ctm_range : forall (f : Z -> bool) (lo : Z) (k : nat),
  forallb f (map (fun i => lo + Z.of_nat i) (seq 0 k)) = true ->
  forall x, lo <= x < lo + Z.of_nat k -> f x = true.
Proof.
  intros f lo k H x Hx. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma ctm_s32_lo : forall n, n < 2 ^ 31 -> s32 n = n.
Proof. intros n H. unfold s32. rewrite (proj2 (Z.ltb_lt n (2 ^ 31)) H). reflexivity. Qed.

Lemma ctm_s32_hi : forall n, 2 ^ 31 <= n -> s32 n = n - 2 ^ 32.
Proof. intros n H. unfold s32. rewrite (proj2 (Z.ltb_ge n (2 ^ 31)) H). reflexivity. Qed.

(** The register of an unsigned 32-bit argument n, sign-extended from bit 31: n itself below 2^31, else
    at least 2^63. *)
Lemma ctm_u : forall n, 0 <= n < 2 ^ 32 ->
  (n < 2 ^ 31 /\ bv_unsigned (Z_to_bv 64 (s32 n)) = n) \/
  (2 ^ 31 <= n /\ 2 ^ 63 <= bv_unsigned (Z_to_bv 64 (s32 n))).
Proof.
  intros n Hn. destruct (Z.lt_ge_cases n (2 ^ 31)) as [H|H].
  - left. split; [exact H|]. rewrite ctm_s32_lo by exact H. apply unsigned_lit. lia.
  - right. split; [exact H|]. rewrite ctm_s32_hi by exact H. rewrite unsigned_lit_wrap.
    rewrite <- (Z.mod_add (n - 2 ^ 32) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(** The clamp [bltu a0, 14]: taken, the register is min(n, 14); not taken, n >= 14. *)
Lemma ctm_lit_lt : forall n (w : word), 0 <= n < 2 ^ 32 -> w = Z_to_bv 64 (s32 n) ->
  bv_ltu w (Z_to_bv 64 14) = true -> bv_unsigned w = Z.min n 14.
Proof.
  intros n w Hn Hw K. rewrite bv_ltu_Z in K. rewrite (unsigned_lit 14) in K by lia.
  apply Z.ltb_lt in K. subst w. destruct (ctm_u n Hn) as [[H1 H2]|[H1 H2]]; lia.
Qed.

Lemma ctm_lit_ge : forall n (w : word), 0 <= n < 2 ^ 32 -> w = Z_to_bv 64 (s32 n) ->
  bv_ltu w (Z_to_bv 64 14) = false -> 14 <= n.
Proof.
  intros n w Hn Hw K. rewrite bv_ltu_Z in K. rewrite (unsigned_lit 14) in K by lia.
  apply Z.ltb_ge in K. subst w. destruct (ctm_u n Hn) as [[H1 H2]|[H1 H2]]; lia.
Qed.

(** Check 1: [(sllw -1, lit) xor mask] is all ones when mask = 2^lit - 1, lit = min(n, 14). *)
Lemma ctm_mm_ok : forall n (w : word), 0 <= n -> bv_unsigned w = Z.min n 14 ->
  bv_eqb (Z_to_bv 64 (Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (bv_unsigned w mod 32))
                               mod 18446744073709551616)
                             (owed_meter_mask n mod 18446744073709551616)))
         (Z_to_bv 64 (-1)) = true.
Proof.
  intros n w Hn Hw. rewrite Hw. unfold owed_meter_mask.
  assert (HL : 0 <= Z.min n 14 < 0 + Z.of_nat 15) by lia.
  remember (Z.min n 14) as L eqn:EL. clear EL Hw.
  refine (ctm_range (fun L => bv_eqb (Z_to_bv 64 (Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (L mod 32))
                                                            mod 18446744073709551616)
                                                          ((2 ^ L - 1) mod 18446744073709551616)))
                                      (Z_to_bv 64 (-1))) 0 15 _ L HL).
  vm_compute. reflexivity.
Qed.

(** [sllw -1, j] for j in 0..14, read unsigned: 2^64 - 2^j. *)
Lemma ctm_pow_m1 : forall j, 0 <= j < 15 ->
  bv_swrap 32 (Z.shiftl 18446744073709551615 (j mod 32)) mod 18446744073709551616 = 18446744073709551616 - 2 ^ j.
Proof.
  intros j Hj. apply Z.eqb_eq.
  refine (ctm_range (fun j => bv_swrap 32 (Z.shiftl 18446744073709551615 (j mod 32)) mod 18446744073709551616
                              =? 18446744073709551616 - 2 ^ j) 0 15 _ j ltac:(lia)).
  vm_compute. reflexivity.
Qed.

(** The test of the inlined spec_segments loop at index j: [(sllw -1, j) xor mask == -1] is mask = 2^j - 1. *)
Lemma ctm_seg_test : forall j mask, 0 <= j < 15 -> 0 <= mask < 2 ^ 16 ->
  bv_eqb (Z_to_bv 64 (Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (j mod 32)) mod 18446744073709551616)
                             mask))
         (Z_to_bv 64 (-1)) = (mask =? 2 ^ j - 1).
Proof.
  intros j mask Hj Hm. rewrite ctm_pow_m1 by exact Hj.
  assert (P1 : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 2 ^ j <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 14) with 16384 in P2. change (2 ^ 16) with 65536 in Hm.
  set (a := 18446744073709551616 - 2 ^ j).
  assert (Ra : 0 <= a < 2 ^ 64) by (unfold a; lia).
  assert (Rx : inr64 (Z.lxor a mask)) by (apply zr_lxor; unfold inr64; lia).
  unfold inr64 in Rx.
  unfold bv_eqb. rewrite !unsigned_lit_wrap. rewrite (Z.mod_small (Z.lxor a mask)) by lia.
  change ((-1) mod 2 ^ 64) with 18446744073709551615.
  assert (Ea : Z.lxor a 18446744073709551615 = 2 ^ j - 1) by (rewrite zb_lxor_ones by lia; unfold a; lia).
  destruct (Z.eqb_spec mask (2 ^ j - 1)) as [E|E].
  - apply Z.eqb_eq. rewrite E, <- Ea, <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity.
  - apply Z.eqb_neq. intros C. apply E.
    rewrite <- Ea, <- C, <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity.
Qed.

(** ring_dot's comparison: [(-(s0 <u 15)) and (sllw 1, s0)] is owed_ring_dot n. *)
Lemma ctm_rd_ok : forall n (w : word), 0 <= n < 2 ^ 32 -> w = Z_to_bv 64 (s32 n) ->
  bv_eqb (Z_to_bv 64 (Z.land ((0 - Z.b2z (bv_unsigned w <? 15)) mod 18446744073709551616)
                             (bv_swrap 32 (Z.shiftl 1 (bv_unsigned w mod 32)) mod 18446744073709551616)))
         (Z_to_bv 64 (owed_ring_dot n)) = true.
Proof.
  intros n w Hn Hw. destruct (Z.lt_ge_cases n 15) as [Hs|Hb].
  - assert (Eu : bv_unsigned w = n).
    { subst w. destruct (ctm_u n Hn) as [[_ H]|[H _]]; [exact H | lia]. }
    rewrite Eu.
    refine (ctm_range (fun n => bv_eqb (Z_to_bv 64 (Z.land ((0 - Z.b2z (n <? 15)) mod 18446744073709551616)
                                                         (bv_swrap 32 (Z.shiftl 1 (n mod 32)) mod 18446744073709551616)))
                                       (Z_to_bv 64 (owed_ring_dot n))) 0 15 _ n ltac:(lia)).
    vm_compute. reflexivity.
  - assert (Eu : (bv_unsigned w <? 15) = false).
    { apply Z.ltb_ge. subst w. destruct (ctm_u n Hn) as [[_ H]|[_ H]]; lia. }
    rewrite Eu. unfold owed_ring_dot. rewrite (proj2 (Z.ltb_ge n 15) Hb).
    change ((0 - Z.b2z false) mod 18446744073709551616) with 0. rewrite Z.land_0_l. apply bv_eqb_refl.
Qed.

(** ring_fill's comparison in the plain image: [(-(s0 <u 16)) and sext32((sllw 1, s0) - 1)] is
    owed_ring_fill n. *)
Lemma ctm_rf_ok_p : forall n (w : word), 0 <= n < 2 ^ 32 -> w = Z_to_bv 64 (s32 n) ->
  bv_eqb (Z_to_bv 64 (Z.land ((0 - Z.b2z (bv_unsigned w <? 16)) mod 18446744073709551616)
                             (bv_swrap 32 (bv_swrap 32 (Z.shiftl 1 (bv_unsigned w mod 32)) mod 18446744073709551616 + -1)
                              mod 18446744073709551616)))
         (Z_to_bv 64 (owed_ring_fill n)) = true.
Proof.
  intros n w Hn Hw. destruct (Z.lt_ge_cases n 16) as [Hs|Hb].
  - assert (Eu : bv_unsigned w = n).
    { subst w. destruct (ctm_u n Hn) as [[_ H]|[H _]]; [exact H | lia]. }
    rewrite Eu.
    refine (ctm_range (fun n => bv_eqb (Z_to_bv 64 (Z.land ((0 - Z.b2z (n <? 16)) mod 18446744073709551616)
                                                         (bv_swrap 32 (bv_swrap 32 (Z.shiftl 1 (n mod 32))
                                                                       mod 18446744073709551616 + -1)
                                                          mod 18446744073709551616)))
                                       (Z_to_bv 64 (owed_ring_fill n))) 0 16 _ n ltac:(lia)).
    vm_compute. reflexivity.
  - assert (Eu : (bv_unsigned w <? 16) = false).
    { apply Z.ltb_ge. subst w. destruct (ctm_u n Hn) as [[_ H]|[_ H]]; lia. }
    rewrite Eu. unfold owed_ring_fill. rewrite (proj2 (Z.leb_gt n 15) ltac:(lia)).
    change ((0 - Z.b2z false) mod 18446744073709551616) with 0. rewrite Z.land_0_l. apply bv_eqb_refl.
Qed.

(** ring_fill's comparison in the ubsan image: [(-(s0 <u 16)) and not(sllw -1, s0)] is owed_ring_fill n. *)
Lemma ctm_rf_ok_u : forall n (w : word), 0 <= n < 2 ^ 32 -> w = Z_to_bv 64 (s32 n) ->
  bv_eqb (Z_to_bv 64 (Z.land ((0 - Z.b2z (bv_unsigned w <? 16)) mod 18446744073709551616)
                             (Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (bv_unsigned w mod 32))
                                      mod 18446744073709551616)
                                     18446744073709551615)))
         (Z_to_bv 64 (owed_ring_fill n)) = true.
Proof.
  intros n w Hn Hw. destruct (Z.lt_ge_cases n 16) as [Hs|Hb].
  - assert (Eu : bv_unsigned w = n).
    { subst w. destruct (ctm_u n Hn) as [[_ H]|[H _]]; [exact H | lia]. }
    rewrite Eu.
    refine (ctm_range (fun n => bv_eqb (Z_to_bv 64 (Z.land ((0 - Z.b2z (n <? 16)) mod 18446744073709551616)
                                                         (Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (n mod 32))
                                                                  mod 18446744073709551616)
                                                                 18446744073709551615)))
                                       (Z_to_bv 64 (owed_ring_fill n))) 0 16 _ n ltac:(lia)).
    vm_compute. reflexivity.
  - assert (Eu : (bv_unsigned w <? 16) = false).
    { apply Z.ltb_ge. subst w. destruct (ctm_u n Hn) as [[_ H]|[_ H]]; lia. }
    rewrite Eu. unfold owed_ring_fill. rewrite (proj2 (Z.leb_gt n 15) ltac:(lia)).
    change ((0 - Z.b2z false) mod 18446744073709551616) with 0. rewrite Z.land_0_l. apply bv_eqb_refl.
Qed.

(** The loop counter [addiw a1, a1, 1] below 15. *)
Lemma ctm_cnt : forall j, 0 <= j < 15 -> bv_swrap 32 (j + 1) = j + 1.
Proof. intros j Hj. apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia. Qed.
