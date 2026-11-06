(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_decode to fuzz_codec.plain (addresses, module paths; its contract module is diginet_meter_segments_dec_c here); the proof is unchanged. *)
(* Modified by Theorem Labs, 2026-10: lines 14-16, 18, 20 and 22-132 of lib/Prog/diginet_meter_segments_dec.v (the pure facts of the plain walk of diginet_meter_segments) for the image-A walk lib/A/Prog/diginet_meter_segments_F.v; the walk, its contract and the image module are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Step ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnLib.
Open Scope Z_scope.

(* ---- pure facts: the 32-bit shift, bit 0, and meter_count ---- *)

Lemma swrap_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma wrap32_small : forall z, 0 <= z < 2 ^ 32 -> bv_wrap 32 z = z.
Proof.
  intros z Hz. unfold bv_wrap. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  apply Z.mod_small. exact Hz.
Qed.

Lemma shiftr_range : forall x n, 0 <= x < 2 ^ 16 -> 0 <= n -> 0 <= Z.shiftr x n < 2 ^ 16.
Proof.
  intros x n Hx Hn. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn) as P.
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with x; [|lia].
  apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

(* `srlw` (0x15760, 0x15780) of a mask below 2^16 by n < 32 is the plain shift *)
Lemma srlw_small : forall x n, 0 <= x < 2 ^ 16 -> 0 <= n < 32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 x) (n mod 32)) = Z.shiftr x n.
Proof.
  intros x n Hx Hn. rewrite wrap32_small by lia. rewrite (Z.mod_small n 32) by lia.
  pose proof (shiftr_range x n Hx ltac:(lia)). apply swrap_small. lia.
Qed.

(* `andi 1` (0x15764): bit 0 of mask >> n is bit n of mask *)
Lemma land1_bit : forall x n, 0 <= n -> Z.land (Z.shiftr x n) 1 = Z.b2z (Z.testbit x n).
Proof.
  intros x n Hn. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Zmod_odd, <- Z.bit0_odd, Z.shiftr_spec by lia. rewrite Z.add_0_l.
  destruct (Z.testbit x n); reflexivity.
Qed.

(* the model's mask & (1 << n) is 0 exactly when bit n of mask is clear *)
Lemma land_pow2 : forall x n, 0 <= n -> (Z.land x (Z.shiftl 1 n) =? 0) = negb (Z.testbit x n).
Proof.
  intros x n Hn. rewrite Z.shiftl_1_l. destruct (Z.testbit x n) eqn:E; cbn [negb].
  - apply Z.eqb_neq. intros H0. apply (f_equal (fun z => Z.testbit z n)) in H0. cbv beta in H0.
    rewrite Z.land_spec, Z.pow2_bits_eqb, Z.eqb_refl, E, Z.bits_0 in H0 by lia. discriminate.
  - apply Z.eqb_eq. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec n i) as [<-|_]; [rewrite E; reflexivity | apply andb_false_r].
Qed.

Lemma mc_stop : forall x n f, 0 <= n -> Z.testbit x n = false -> meter_count x n (S f) = n.
Proof.
  intros x n f Hn B. cbn [meter_count]. rewrite (land_pow2 x n Hn), B. cbn [negb]. rewrite andb_false_r.
  reflexivity.
Qed.

Lemma mc_go : forall x n f, 0 <= n < 14 -> Z.testbit x n = true ->
  meter_count x n (S f) = meter_count x (n + 1) f.
Proof.
  intros x n f Hn B. cbn [meter_count]. rewrite (land_pow2 x n ltac:(lia)), B. unfold DIGINET_METER_SEGMENTS.
  rewrite (proj2 (Z.ltb_lt n 14)) by lia. reflexivity.
Qed.

Lemma mc_range : forall x f n, 0 <= n -> n + Z.of_nat f <= 14 -> n <= meter_count x n f <= 14.
Proof.
  intros x f; induction f as [|f IH]; intros n Hn Hf; cbn [meter_count]; [lia|].
  match goal with |- context [if ?c then _ else _] => destruct c end; [|lia].
  specialize (IH (n + 1) ltac:(lia) ltac:(lia)). lia.
Qed.

(* the value 0x15780-0x1578c computes from n = meter_count mask 0 14 *)
Definition fin_val (x n : Z) : Z := if negb (Z.shiftr x n =? 0) then -1 else n.

Lemma meter_fin : forall x, diginet_meter_segments x = fin_val x (meter_count x 0 14).
Proof. reflexivity. Qed.

Lemma z2bv_mod : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
  intros a b H. rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 a)), <- (Z_to_bv_bv_unsigned (Z_to_bv 64 b)).
  rewrite !unsigned_lit_wrap, H. reflexivity.
Qed.

(* 0x15780-0x1578c: `srlw a0, a0, a2; seqz a0, a0; addiw a0, a0, -1; or a0, a0, a2` is (mask >> n) ? -1 : n *)
Lemma fin_eq : forall x n, 0 <= x < 2 ^ 16 -> 0 <= n <= 14 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned
      (v_sltiu (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 x)))
                                                  (bv_unsigned (Z_to_bv 64 n) mod 32)))) 1) + -1))))
    (bv_unsigned (Z_to_bv 64 n)))
  = Z_to_bv 64 (fin_val x n).
Proof.
  intros x n Hx Hn.
  rewrite (unsigned_lit x), (unsigned_lit n) by lia. rewrite srlw_small by lia.
  pose proof (shiftr_range x n Hx ltac:(lia)) as R.
  unfold v_sltiu. rewrite (unsigned_lit (Z.shiftr x n)) by lia. change (bv_wrap 64 1) with 1.
  unfold fin_val. apply z2bv_mod.
  destruct (Z.eqb_spec (Z.shiftr x n) 0) as [E|E].
  - rewrite E.
    assert (C : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/
                n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14) by lia.
    clear - C.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      vm_compute; reflexivity.
  - replace (Z.shiftr x n <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [negb].
    assert (C : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/
                n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14) by lia.
    clear - C.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      vm_compute; reflexivity.
Qed.
