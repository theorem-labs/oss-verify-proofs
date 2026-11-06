(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libdiginet/fuzz_decode/lib/U/Prog/diginet_meter_segments.v, with its module paths, module names and addresses changed. *)
(* New for libdiginet/fuzz_decode: the walk of diginet_meter_segments (src/diginet_codec.c:209-215) on the UBSan
   image, the leaf at 0x15ba4 (14 words, all walked: no call, no frame, no UBSan check site, no abort site), against
   lib/U/Prog/diginet_meter_segments_dec_c.v.
   - 0x15ba4 `mv a1, zero` is n = 0.
   - The loop 0x15ba8-0x15bbc (`loop` below, by induction on the fuel of DgnLib.v's meter_count): 0x15ba8 `srlw`
     and 0x15bac `andi 1` give bit n of the mask (srlw_small, bit_shiftr, bit_pow2: for a mask below 2^16 the
     32-bit shift is the plain shift, and its bit 0 is the model's mask & (1 << n)); when it is 0, 0x15bb0 jumps to
     0x15bc4 `mv a2, a1` (a2 = n); else 0x15bb4 `addiw a1, a1, 1` counts on, and 0x15bbc `bne a1, a2(14)` loops back
     until n = 14, where 0x15bc0 `j` goes on with a2 = 14 (set at 0x15bb8).
   - 0x15bc8-0x15bd8 (`fin_val`): srlw / seqz / addiw -1 / or return (mask >> n) == 0 ? n : -1, sign-extended. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import diginet_meter_segments_dec_c.
Open Scope Z_scope.

(* srlw on a mask below 2^16 by n < 32: the low 32 bits are the mask, and the result is below 2^31 *)
Lemma srlw_small : forall x n, 0 <= x < 2 ^ 16 -> 0 <= n < 32 ->
  bv_swrap 32 (bv_wrap 32 x ≫ (n mod 32)) = Z.shiftr x n.
Proof.
  intros x n Hx Hn.
  assert (W : bv_wrap 32 x = x).
  { unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). apply Z.mod_small. lia. }
  rewrite W, (Z.mod_small n 32) by lia.
  assert (S : 0 <= Z.shiftr x n < 2 ^ 16).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with x; [apply Z.div_le_upper_bound; [lia|]|lia].
    pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)). nia. }
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  rewrite Z.mod_small by lia. lia.
Qed.

(* bit 0 of mask >> n is bit n of mask *)
Lemma bit_shiftr : forall x n, 0 <= n -> (Z.land (Z.shiftr x n) 1 =? 0) = negb (Z.testbit x n).
Proof.
  intros x n Hn. change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
  rewrite Zmod_odd, <- Z.bit0_odd, Z.shiftr_spec by lia. rewrite Z.add_0_l.
  destruct (Z.testbit x n); reflexivity.
Qed.

(* the model's mask & (1 << n) is 0 exactly when bit n of mask is clear *)
Lemma bit_pow2 : forall x n, 0 <= n -> (Z.land x (Z.shiftl 1 n) =? 0) = negb (Z.testbit x n).
Proof.
  intros x n Hn. rewrite Z.shiftl_1_l. destruct (Z.testbit x n) eqn:E; cbn [negb].
  - apply Z.eqb_neq. intros H0. apply (f_equal (fun z => Z.testbit z n)) in H0. cbv beta in H0.
    rewrite Z.land_spec, Z.pow2_bits_eqb, Z.eqb_refl, E, Z.bits_0 in H0 by lia. discriminate.
  - apply Z.eqb_eq. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec n i) as [<-|_]; [rewrite E; reflexivity | apply andb_false_r].
Qed.

Lemma meter_count_range : forall x f n, 0 <= n -> n + Z.of_nat f <= 14 -> n <= meter_count x n f <= 14.
Proof.
  intros x f; induction f as [|f IH]; intros n Hn Hf; cbn [meter_count]; [lia|].
  destruct ((n <? DIGINET_METER_SEGMENTS) && negb (Z.land x (Z.shiftl 1 n) =? 0)); [|lia].
  specialize (IH (n + 1) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma lor_ones_small : forall n, 0 <= n <= 14 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 + -1)))) n) = Z_to_bv 64 (-1).
Proof.
  intros n Hn.
  assert (H : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/
              n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    apply bv_eq; vm_compute; reflexivity.
Qed.

(* 0x15bc8-0x15bd4: (mask >> n) == 0 ? n : -1 *)
Lemma fin_val : forall x n, 0 <= x < 2 ^ 16 -> 0 <= n <= 14 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned
      (v_sltiu (Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 x ≫ (bv_unsigned (Z_to_bv 64 n) mod 32)))) 1) + -1))))
    (bv_unsigned (Z_to_bv 64 n)))
  = Z_to_bv 64 (if negb (Z.shiftr x n =? 0) then -1 else n).
Proof.
  intros x n Hx Hn. rewrite (unsigned_lit n) by lia. rewrite srlw_small by lia.
  assert (S : 0 <= Z.shiftr x n) by (apply Z.shiftr_nonneg; lia).
  assert (S2 : Z.shiftr x n < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia.
    apply Z.le_lt_trans with x; [apply Z.div_le_upper_bound; [lia|]|lia].
    pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)). nia. }
  unfold v_sltiu. rewrite (unsigned_lit (Z.shiftr x n)) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec (Z.shiftr x n) 0) as [E|E]; cbn [negb].
  - rewrite E. change (0 <? 1) with true. cbv iota.
    replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 1) + -1)))) with 0
      by (vm_compute; reflexivity).
    reflexivity.
  - replace (Z.shiftr x n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    change (bv_unsigned (Z_to_bv 64 0)) with 0. apply lor_ones_small. exact Hn.
Qed.

Section Walk.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).

Local Notation ST pc a1 a2 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* the loop from 0x15ba8 with n in a1 to 0x15bc8 with a2 = meter_count mask n f *)
Lemma loop : forall (Q : machine_state -> Prop) f n (a2 : word),
  bv_unsigned a0 < 2 ^ 16 -> 0 <= n < 14 -> n + Z.of_nat f = 14 ->
  (forall a1' : word, evt rsegs Q (ST 0x15bc8 a1' (Z_to_bv 64 (meter_count (bv_unsigned a0) n f)))) ->
  evt rsegs Q (ST 0x15ba8 (Z_to_bv 64 n) a2).
Proof.
  intros Q f; induction f as [|f IH]; intros n a2 HA Hn Hf K; [lia|].
  pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0.
  step. step. step. if_cases H1.
  - zify_cond H1. rewrite srlw_small in H1 by lia.
    rewrite Z.mod_small in H1
      by (split; [apply Z.shiftr_nonneg; lia|]; rewrite Z.shiftr_div_pow2 by lia;
          apply Z.le_lt_trans with (bv_unsigned a0); [apply Z.div_le_upper_bound; [lia|];
          pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)); nia | lia]).
    assert (B : Z.testbit (bv_unsigned a0) n = false).
    { pose proof (bit_shiftr (bv_unsigned a0) n ltac:(lia)) as E. rewrite H1 in E.
      destruct (Z.testbit (bv_unsigned a0) n); [discriminate | reflexivity]. }
    assert (M : meter_count (bv_unsigned a0) n (S f) = n).
    { cbn [meter_count]. rewrite bit_pow2, B by lia. rewrite andb_false_r. reflexivity. }
    rewrite M in K. step. apply (K (Z_to_bv 64 n)).
  - zify_cond H1. rewrite srlw_small in H1 by lia.
    rewrite Z.mod_small in H1
      by (split; [apply Z.shiftr_nonneg; lia|]; rewrite Z.shiftr_div_pow2 by lia;
          apply Z.le_lt_trans with (bv_unsigned a0); [apply Z.div_le_upper_bound; [lia|];
          pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)); nia | lia]).
    assert (B : Z.testbit (bv_unsigned a0) n = true).
    { pose proof (bit_shiftr (bv_unsigned a0) n ltac:(lia)) as E. apply Z.eqb_neq in H1. rewrite H1 in E.
      destruct (Z.testbit (bv_unsigned a0) n); [reflexivity | discriminate]. }
    assert (M : meter_count (bv_unsigned a0) n (S f) = meter_count (bv_unsigned a0) (n + 1) f).
    { cbn [meter_count]. rewrite bit_pow2, B by lia. unfold DIGINET_METER_SEGMENTS.
      rewrite (proj2 (Z.ltb_lt n 14)) by lia. reflexivity. }
    rewrite M in K.
    assert (W : bv_swrap 32 (bv_unsigned (Z_to_bv 64 n) + 1) = n + 1).
    { rewrite unsigned_lit by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
      change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
      rewrite Z.mod_small by lia. lia. }
    step. step. step. rewrite W. if_cases H2.
    + zify_cond H2. try rewrite Z.mod_small in H2 by lia.
      apply (IH (n + 1) (Z_to_bv 64 14)); [exact HA | lia | lia | exact K].
    + zify_cond H2. try rewrite Z.mod_small in H2 by lia.
      assert (f = O) by lia. subst f. cbn [meter_count] in K. replace (n + 1) with 14 in K by lia.
      step. apply (K (Z_to_bv 64 (n + 1))).
Qed.

(* 0x15bc8 with a2 = n to the return *)
Lemma fin : forall n (a1 : word), bv_unsigned a0 < 2 ^ 16 -> 0 <= n <= 14 ->
  evt rsegs
    (fun ms' => exists a1' a2' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                     (Z_to_bv 64 (if negb (Z.shiftr (bv_unsigned a0) n =? 0) then -1 else n)) a1' a2' a3
                     a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m (seg_rom rsegs))
    (ST 0x15bc8 a1 (Z_to_bv 64 n)).
Proof.
  intros n a1 HA Hn. pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0.
  step. step. step. step. step. apply evt_done.
  rewrite fin_val by lia. do 2 eexists. reflexivity.
Qed.

End Walk.

Theorem diginet_meter_segments_holds : diginet_meter_segments_contract.
Proof.
  unfold diginet_meter_segments_contract, DIGINET_METER_SEGMENTS_ENTRY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HA.
  step.
  apply (loop ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
           _ 14 0 a2 HA ltac:(lia) ltac:(lia)).
  intros a1'. pose proof (meter_count_range (bv_unsigned a0) 14 0 ltac:(lia) ltac:(lia)) as R.
  unfold diginet_meter_segments. cbv zeta.
  apply (fin ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
           (meter_count (bv_unsigned a0) 0 14) a1' HA R).
Qed.
