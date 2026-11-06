(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libdiginet/fuzz_decode/lib/Prog/diginet_meter_segments.v, with its module paths, module names and addresses changed. *)
(* New for libdiginet/fuzz_decode: the walk of diginet_meter_segments (src/diginet_codec.c:209-215) on the plain
   image, the leaf at 0x1575c (14 instructions, every one stepped: no call, no frame, no load, no store). It proves
   diginet_meter_segments_contract (diginet_meter_segments_dec_c.v): a0 is DgnLib.v's diginet_meter_segments mask.
   - 0x1575c `mv a1, zero` is n = 0.
   - `loop` (0x15760-0x1577c), by induction on the fuel of DgnLib.v's meter_count: 0x15760 `srlw` and 0x15764
     `andi 1` give bit n of the mask (srlw_small: for a mask below 2^16 the 32-bit shift is Z.shiftr; land1_bit:
     its bit 0 is Z.testbit mask n, which land_pow2 ties to the model's mask & (1 << n)). A clear bit takes
     0x15768 `beqz` to 0x1577c `mv a2, a1` (a2 = n); a set bit counts on at 0x1576c `addiw`, and 0x15774
     `bne a1, a2` (a2 = 14 from 0x15770) loops back until n = 14, where 0x15778 `j` goes on with a2 = 14.
   - `fin` (0x15780-0x15790): srlw / seqz / addiw -1 / or give (mask >> n) == 0 ? n : -1 (fin_eq), then ret. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Step ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import diginet_meter_segments_dec_c.
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

(* the branch condition of a stepped goal, decided by a closed computation *)
Ltac br b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (vm_compute; reflexivity); cbv iota
  end.
(* the same, with a given proof of `b = c` *)
Ltac br_by b tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by tac; cbv iota
  end.

(* ---- the walk ---- *)

Section Walk.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mask : Z).

Local Abbreviation ST pc a0 a1 a2 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* 0x15760 with n in a1 (n < 14, fuel f = 14 - n) to 0x15780 with a2 = meter_count mask n f *)
Lemma loop : forall (Q : machine_state -> Prop) f n (a2 : word),
  0 <= mask < 2 ^ 16 -> 0 <= n < 14 -> n + Z.of_nat f = 14 ->
  (forall a1' : word, evt rsegs Q (ST 0x15780 (Z_to_bv 64 mask) a1' (Z_to_bv 64 (meter_count mask n f)))) ->
  evt rsegs Q (ST 0x15760 (Z_to_bv 64 mask) (Z_to_bv 64 n) a2).
Proof.
  intros Q f; induction f as [|f IH]; intros n a2 HM Hn Hf K; [lia|].
  pose proof (shiftr_range mask n HM ltac:(lia)) as R.
  step. step. step.
  rewrite (unsigned_lit mask), (unsigned_lit n) by lia. rewrite (srlw_small mask n) by lia.
  rewrite (unsigned_lit (Z.shiftr mask n)) by lia. rewrite (land1_bit mask n) by lia.
  destruct (Z.testbit mask n) eqn:B.
  - (* bit n set: n += 1, and on to the next round unless n = 14 *)
    br false. rewrite (mc_go mask n f Hn B) in K.
    step. step. step.
    rewrite (unsigned_lit n) by lia. rewrite (swrap_small (n + 1)) by lia.
    destruct (Z.eq_dec n 13) as [E13|N13].
    + subst n. br false. step.
      assert (f = O) by lia. subst f.
      exact (K (Z_to_bv 64 (13 + 1))).
    + br_by true ltac:(unfold bv_eqb; rewrite !unsigned_lit by lia;
                       rewrite (proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
      exact (IH (n + 1) (Z_to_bv 64 14) HM ltac:(lia) ltac:(lia) K).
  - (* bit n clear: a2 = n *)
    br true. rewrite (mc_stop mask n f ltac:(lia) B) in K.
    step. exact (K (Z_to_bv 64 n)).
Qed.

(* 0x15780 with a2 = n to the return *)
Lemma fin : forall n (a1 : word), 0 <= mask < 2 ^ 16 -> 0 <= n <= 14 ->
  evt rsegs
    (fun ms' => exists a1' a2' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fin_val mask n)) a1' a2' a3
                     a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m (seg_rom rsegs))
    (ST 0x15780 (Z_to_bv 64 mask) a1 (Z_to_bv 64 n)).
Proof.
  intros n a1 HM Hn.
  step. step. step. step. step. apply evt_done.
  rewrite (fin_eq mask n HM Hn). do 2 eexists. reflexivity.
Qed.

End Walk.

Theorem diginet_meter_segments_holds : diginet_meter_segments_contract.
Proof.
  unfold diginet_meter_segments_contract, DIGINET_METER_SEGMENTS_PC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask HM.
  step.
  apply (loop ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask
           _ 14%nat 0 a2 HM ltac:(lia) ltac:(lia)).
  intros a1'. rewrite meter_fin.
  pose proof (mc_range mask 14%nat 0 ltac:(lia) ltac:(lia)) as R.
  exact (fin ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mask
           (meter_count mask 0 14) a1' HM ltac:(lia)).
Qed.
