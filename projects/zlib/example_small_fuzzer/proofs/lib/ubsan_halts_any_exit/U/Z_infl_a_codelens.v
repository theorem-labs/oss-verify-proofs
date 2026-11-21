(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.

Module Z_infl_c_pure.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateOkb.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb.RefInflateA_MATCH1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition hide (P : Prop) : Prop := P.

Definition mt_idx (s : inflate_state) : Z :=
  if is_wnext s <? is_offset s then is_wsize s - (is_offset s - is_wnext s) else is_wnext s - is_offset s.

Lemma arm_MATCH_pat : forall s c r,
  is_sane s = 1 -> ir_left r = 1 -> ir_out r = 1 -> ir_put r = 0 -> 1 <= arr_len (ic_outbuf c) ->
  1 <= is_offset s < 2^32 -> 1 <= is_length s < 2^32 -> 0 <= is_whave s < 2^32 -> 0 <= is_wnext s < 2^32 -> 0 <= is_wsize s < 2^32 ->
  is_whave s <= is_wsize s ->
  arm_MATCH ivar_ref (mkW s c r) =
    if is_whave s <? is_offset s then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_distance_too_far_back) r)
    else
      let s1 := iset_length s (is_length s - 1) in
      let c1 := icset_outbuf c (arr_set (ic_outbuf c) 0 (arr_get (is_window s) (mt_idx s))) in
      let r1 := irset_put (irset_left r 0) 1 in
      if is_length s - 1 =? 0 then ARun tt (mkW (iset_mode s1 LEN) c1 r1) else ARun tt (mkW s1 c1 r1).
Proof.
  intros s c r Hsane HL HO HP HA Hoff Hlen Hwh Hwn Hws Hle.
  rewrite (arm_MATCH_eq s c r Hsane). rewrite HL. change (1 =? 0) with false. cbv iota.
  unfold mt_plan. rewrite HL, HO. change (wrap32 (1 - 1)) with 0.
  replace (0 <? is_offset s) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite Z.sub_0_r. rewrite (wrap32_id (is_offset s)) by lia.
  destruct (Z.ltb_spec (is_whave s) (is_offset s)) as [Hfar|Hok]; [reflexivity|].
  unfold mt_idx.
  destruct (Z.ltb_spec (is_wnext s) (is_offset s)) as [Hw|Hw]; cbn [fst snd].
  - rewrite (wrap32_id (is_offset s - is_wnext s)) by lia.
    set (cp := if is_length s <? is_offset s - is_wnext s then is_length s else is_offset s - is_wnext s).
    assert (Hcp : 1 <= cp) by (unfold cp; destruct (Z.ltb_spec (is_length s) (is_offset s - is_wnext s)); lia).
    unfold mt_clamp. rewrite HL. replace (1 <? cp) with (negb (cp =? 1)) by (destruct (Z.eqb_spec cp 1); destruct (Z.ltb_spec 1 cp); try reflexivity; lia).
    assert (E1 : (if negb (cp =? 1) then 1 else cp) = 1) by (destruct (Z.eqb_spec cp 1); cbn; lia).
    rewrite E1. rewrite HP.
    rewrite (match_copy_eq (is_window s) (ic_outbuf c) 0 _ 1) by (try exact I; lia).
    change (Z.to_nat 1) with 1%nat. cbn [mc_obn mc_src Z.of_nat]. rewrite !Z.add_0_r.
    rewrite (wrap32_id (is_length s - 1)) by lia. rewrite (wrap32_id (1 - 1)) by lia. change (1 - 1) with 0. change (0 + 1) with 1.
    destruct (is_length s - 1 =? 0); reflexivity.
  - set (cp := if is_length s <? is_offset s then is_length s else is_offset s).
    assert (Hcp : 1 <= cp) by (unfold cp; destruct (Z.ltb_spec (is_length s) (is_offset s)); lia).
    unfold mt_clamp. rewrite HL. replace (1 <? cp) with (negb (cp =? 1)) by (destruct (Z.eqb_spec cp 1); destruct (Z.ltb_spec 1 cp); try reflexivity; lia).
    assert (E1 : (if negb (cp =? 1) then 1 else cp) = 1) by (destruct (Z.eqb_spec cp 1); cbn; lia).
    rewrite E1. rewrite HP.
    rewrite (match_copy_eq (is_window s) (ic_outbuf c) 0 _ 1) by (try exact I; lia).
    change (Z.to_nat 1) with 1%nat. cbn [mc_obn mc_src Z.of_nat]. rewrite !Z.add_0_r.
    rewrite (wrap32_id (is_length s - 1)) by lia. rewrite (wrap32_id (1 - 1)) by lia. change (1 - 1) with 0. change (0 + 1) with 1.
    destruct (is_length s - 1 =? 0); reflexivity.
Qed.

Lemma match_win_facts : forall s, CORE s -> is_wbits s = 15 ->
  0 <= is_wsize s <= 32768 /\ 0 <= is_whave s <= is_wsize s /\ 0 <= is_wnext s <= is_wsize s
  /\ (1 <= is_offset s <= is_whave s -> is_wsize s = 32768 /\ is_window_blk s <> None /\ 0 <= mt_idx s < 32768 /\ is_wnext s < 32768).
Proof.
  intros s (C1 & C2 & C3 & C4 & C5 & C6 & C7 & _) Pwb.
  destruct (Z.eq_dec (is_wsize s) 0) as [E|NE].
  - destruct (C6 E) as [E1 E2]. rewrite E, E1, E2. repeat split; try lia.
  - pose proof (C3 NE) as E. rewrite Pwb in E. change (shl32 1 15) with 32768 in E. destruct (C7 NE) as [H1 H2].
    split; [lia|]. split; [lia|]. split; [lia|]. intros Ho. split; [exact E|]. split; [intros EN; exact (NE (C1 EN))|].
    unfold mt_idx. destruct (Z.ltb_spec (is_wnext s) (is_offset s)); lia.
Qed.

Lemma land_swrap32 : forall x, 0 <= x < 2^32 ->
  Z.land (bv_swrap 32 x) 18446744073709551615 = if x <? 2147483648 then x else x + 18446744069414584320.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2 ^ 32) with 4294967296 in H. change (2 ^ 64) with 18446744073709551616.
  destruct (Z.ltb_spec x 2147483648); Z.div_mod_to_equations; lia.
Qed.
Lemma sx32u_le_small : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^31 -> (Z.land (bv_swrap 32 x) 18446744073709551615 <= y <-> x <= y).
Proof. intros x y Hx Hy. rewrite land_swrap32 by exact Hx. destruct (Z.ltb_spec x 2147483648); lia. Qed.
Lemma sx32u_lt_small : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^31 -> (y < Z.land (bv_swrap 32 x) 18446744073709551615 <-> y < x).
Proof. intros x y Hx Hy. rewrite land_swrap32 by exact Hx. destruct (Z.ltb_spec x 2147483648); lia. Qed.

Lemma le1_wz_byte : forall v, 0 <= v < 256 -> le1 (wz v) = [Z_to_bv 8 v].
Proof.
  intros v H. unfold le1. rewrite (Z_to_bv_unsigned 64 v), (bv_wrap_small 64 v) by (unfold bv_modulus; cbn; lia).
  cbn [Z_to_le_bytes]. reflexivity.
Qed.
Lemma le4_swrap32 : forall x, le4 (wz (bv_swrap 32 x)) = le4 (wz x).
Proof.
  intros x. apply le4_wz_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change (4294967296 / 2) with 2147483648. Z.div_mod_to_equations; lia.
Qed.
Lemma bv_swrap32_zero_iff : forall x, 0 <= x < 2^32 -> (bv_swrap 32 x = 0 <-> x = 0).
Proof.
  intros x H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296 in H. split; intros E; Z.div_mod_to_equations; lia.
Qed.
Lemma bv_swrap32_range : forall x, - 2^31 <= bv_swrap 32 x < 2^31.
Proof.
  intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^31) with 2147483648. Z.div_mod_to_equations; lia.
Qed.
Lemma sx32_swrap_zero : forall x, 0 <= x < 2^32 -> (bv_unsigned (sx32 (wz (bv_swrap 32 x))) = 0 <-> x = 0).
Proof.
  intros x H. rewrite sx32_wz by apply bv_swrap32_range. rewrite Z_to_bv_unsigned. pose proof (bv_swrap32_range x) as R.
  rewrite <- (bv_swrap32_zero_iff x H). unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (2^31) with 2147483648 in R. split; intros E; Z.div_mod_to_equations; lia.
Qed.
Lemma land64_zero_iff : forall x, - 2^63 <= x < 2^63 -> (Z.land x 18446744073709551615 = 0 <-> x = 0).
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2^63) with 9223372036854775808 in H. change (2^64) with 18446744073709551616. split; intros E; Z.div_mod_to_equations; lia.
Qed.
Lemma sx32_wz_u : forall x, sx32 (wz x) = wz (bv_swrap 32 x).
Proof.
  intros x. unfold sx32. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.div].
  change (4294967296 / 2) with 2147483648. Z.div_mod_to_equations. lia.
Qed.
Lemma bv_swrap32_sub_swrap : forall a b, bv_swrap 32 (bv_swrap 32 a - b) = bv_swrap 32 (a - b).
Proof.
  intros a b. apply bv_swrap32_eqm. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.
Lemma bv_swrap32_sub_land : forall a b, bv_swrap 32 (Z.land (bv_swrap 32 a) 18446744073709551615 - b) = bv_swrap 32 (a - b).
Proof.
  intros a b. apply bv_swrap32_eqm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296. change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.

Lemma clang_mask32 : forall n, 0 <= n <= 31 ->
  Z.lxor (Z.land (bv_swrap 32 (18446744073709551615 ≪ (n mod 32))) 18446744073709551615) 18446744073709551615 = Z.ones n.
Proof.
  intros n H.
  assert (C : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15
              \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/ n = 31) by lia.
  repeat (destruct C as [->|C]; [vm_compute; reflexivity|]). subst n. vm_compute. reflexivity.
Qed.
Lemma land_ones_rng : forall h n, 0 <= n -> 0 <= Z.land h (Z.ones n) < 2 ^ n.
Proof. intros h n Hn. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.
Lemma le4_back_add : forall b e, le4 (wz (bv_swrap 32 b + e)) = le4 (wz (swrap32 (b + e))).
Proof.
  intros b e. apply le4_wz_mod. rewrite Z_to_bv_unsigned. unfold swrap32, two31. rewrite wrap32_mod.
  unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.
Lemma le4_swrap32_r : forall x, le4 (wz x) = le4 (wz (swrap32 x)).
Proof.
  intros x. apply le4_wz_mod. rewrite Z_to_bv_unsigned. unfold swrap32, two31. rewrite wrap32_mod.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (2^32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.
Lemma nb_r1_facts : forall c r r1 n, REGS c r -> arr_len (ic_input c) <= 1 -> n <= 32 ->
  ((r1 = r /\ n <= ir_bits r) \/ (r1 = pullr c r /\ 0 < ir_have r /\ ir_bits r < n <= ir_bits r + 8)) ->
  ir_in r1 = ir_in r /\ ir_out r1 = ir_out r /\ ir_ret r1 = ir_ret r /\ ir_put r1 = ir_put r /\ ir_left r1 = ir_left r
  /\ n <= ir_bits r1 <= 63 /\ 0 <= ir_hold r1 < 2^64 /\ 0 <= ir_have r1 < 2^32 /\ 0 <= ir_next r1.
Proof.
  intros c r r1 n (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo) Hin Hn HR1.
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  destruct HR1 as [[-> H3]|(-> & H1 & H2)].
  - repeat split; try reflexivity; lia.
  - pose proof (Rin (ir_next r)) as RBy.
    pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
    pullr_rw c r. repeat split; try reflexivity; try lia.
    eapply Z.lt_le_trans; [exact (proj2 PR)|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma PATI_step_put : forall X s c r s' c' r' v, PATI X (mkW s c r) ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = 0 ->
  ~ (FLAGS <= is_mode s' <= HCRC) -> is_window_blk s' = is_window_blk s ->
  ic_input c' = ic_input c -> ic_outbuf c' = arr_set (ic_outbuf c) (ir_put r) v -> 0 <= v < 256 -> 0 <= ir_put r < arr_len (ic_outbuf c) ->
  ir_put r' = ir_put r + 1 -> is_window s' = is_window s ->
  0 <= ir_out r' - ir_left r' <= ir_put r' -> NOPUTb (is_mode s') (ir_put r') = false ->
  ISR s' -> (bk_ok s -> bk_ok s') -> PATI X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' v (P1 & P2 & P3 & _ & _ & P6 & P7 & P8 & P9 & P10 & _ & (P12 & P13 & _ & _ & P16) & PBK) E1 E2 E3 E4 NG E6 E7 E8 Hv Hp E9 E10 HO HN HI HBK.
  unfold PATI, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3, E6, E7, E8, E9, E10. rewrite E9 in HO. rewrite arr_len_set.
  repeat (split; [first [assumption | left; assumption]|]).
  split; [|exact (HBK PBK)].
  split; [|split; [exact P13| split; [exact HO| split; [rewrite <- E9; exact HN| exact P16]]]].
  intros i Hi. destruct (Z.eq_dec i (ir_put r)) as [->|NE].
  - rewrite arr_get_set_same by lia. exact Hv.
  - rewrite arr_get_set_other by lia. apply P12. lia.
Qed.

Lemma land64_cases : forall op, 0 <= op < 256 -> 0 <= Z.land op 64 <= 64.
Proof.
  intros op Hop.
  assert (H : forallb (fun i : nat => (0 <=? Z.land (Z.of_nat i) 64) && (Z.land (Z.of_nat i) 64 <=? 64)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat op) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma land15_range : forall op, 0 <= Z.land op 15 < 16.
Proof. intros op. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma land32_cases : forall op, 0 <= op < 256 -> 0 <= Z.land op 32 <= 32.
Proof.
  intros op Hop.
  assert (H : forallb (fun i : nat => (0 <=? Z.land (Z.of_nat i) 32) && (Z.land (Z.of_nat i) 32 <=? 32)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat op) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma le4_back_add2 : forall b l h, le4 (wz (bv_swrap 32 b + l + h)) = le4 (wz (swrap32 (swrap32 (b + l) + h))).
Proof.
  intros b l h. apply le4_wz_mod. rewrite Z_to_bv_unsigned. unfold swrap32, two31. rewrite !wrap32_mod.
  unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.

Definition DREGS (c : icall) (r : iregs) : Prop :=
  0 <= ir_next r /\ 0 <= ir_have r <= 1 /\ ir_next r + ir_have r = arr_len (ic_input c) /\ 0 <= ir_bits r <= 63 /\ 0 <= ir_hold r < 2 ^ ir_bits r.
Lemma DREGS_of_REGS : forall c r, REGS c r -> arr_len (ic_input c) <= 1 -> DREGS c r.
Proof. intros c r (Rn & Rh & Rnh & _ & _ & _ & [RB RH] & _) Hin. unfold DREGS. repeat split; try lia. Qed.
Lemma dec_r1_facts : forall c r r1, DREGS c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  (r1 = r \/ (r1 = pullr c r /\ ir_have r = 1 /\ ir_bits r <= 31)) ->
  DREGS c r1 /\ ir_in r1 = ir_in r /\ ir_out r1 = ir_out r /\ ir_ret r1 = ir_ret r /\ ir_put r1 = ir_put r /\ ir_left r1 = ir_left r.
Proof.
  intros c r r1 (Rn & Rh & Rnh & RB & RH) Rin [->|(-> & H1 & HB)]; [repeat split; try reflexivity; try lia|].
  pose proof (Rin (ir_next r)) as RBy.
  pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
  unfold DREGS. pullr_rw c r. repeat split; try reflexivity; lia.
Qed.
Lemma DREGS_hold64 : forall c r, DREGS c r -> 0 <= ir_hold r < 2^64.
Proof. intros c r (_ & _ & _ & RB & RH). split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. Qed.

Lemma addback2 : forall s l h, addback (addback s l) h = iset_back s (swrap32 (swrap32 (is_back s + l) + h)).
Proof. intros. reflexivity. Qed.

Lemma addback1 : forall s h, addback s h = iset_back s (swrap32 (is_back s + h)).
Proof. intros. reflexivity. Qed.



Lemma DREGS_nb : forall c r r1 n, DREGS c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) -> n <= 32 ->
  ((r1 = r /\ n <= ir_bits r) \/ (r1 = pullr c r /\ 0 < ir_have r /\ ir_bits r < n <= ir_bits r + 8)) ->
  DREGS c r1 /\ n <= ir_bits r1 /\ ir_in r1 = ir_in r /\ ir_out r1 = ir_out r /\ ir_ret r1 = ir_ret r /\ ir_put r1 = ir_put r /\ ir_left r1 = ir_left r.
Proof.
  intros c r r1 n DR Rin Hn [[-> H]|(-> & H1 & H2)].
  - repeat split; try reflexivity; try lia; apply DR.
  - pose proof DR as (Rn & Rh & Rnh & RB & RH).
    assert (A1 : ir_have r = 1) by lia. assert (A2 : ir_bits r <= 31) by lia.
    destruct (dec_r1_facts c r (pullr c r) DR Rin (or_intror (conj eq_refl (conj A1 A2)))) as (DR1 & F).
    split; [exact DR1|]. split; [rewrite pullr_bits by lia; lia| exact F].
Qed.

Lemma DREGS_drop : forall c r n, DREGS c r -> 0 <= n <= ir_bits r -> DREGS c (ddrop r n).
Proof.
  intros c r n (Rn & Rh & Rnh & RB & RH) Hn. unfold DREGS, ddrop. destruct r; cbn in *. rewrite wrap32_id by lia.
  pose proof (hold_drop ir_hold ir_bits n Hn RH) as HD. rewrite Z.shiftr_div_pow2 by lia. repeat split; lia.
Qed.
End Z_infl_c_pure.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_c_tab.

Module Z_infl_t_iface.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition PC_LENLENS_E : Z := 0x1f690.
Definition PC_CODELENS_E : Z := 0x1f828.

Definition lenlens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPh X w PC_LENLENS_E q ms ->
  h17 q = wz (is_have (w_s w)) -> h14 q = wz (il_NI (ix_L X) + ir_next (w_r w)) -> h12 q = wz (ir_have (w_r w)) ->
  h9 q = wz (il_NO (ix_L X) + ir_put (w_r w)) -> h11 q = wz (ix_flush X) -> h13 q = wz (il_S (ix_L X)) ->
  h18 q = wz (ir_bits (w_r w)) -> h22 q = wz (ir_hold (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> is_mode (w_s w) = LENLENS ->
  evt usegs (fun ms' => IPOST X (arm_LENLENS ivar_ref flush w) ms' /\ PATI X (wof (arm_LENLENS ivar_ref flush w))) ms.

Definition codelens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPh X w PC_CODELENS_E q ms ->
  h9 q = wz (il_NO (ix_L X) + ir_put (w_r w)) -> h10 q = wz (-2) -> h18 q = wz (ir_bits (w_r w)) -> h22 q = wz (ir_hold (w_r w)) ->
  h24 q = wz (ir_have (w_r w)) -> h25 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> is_mode (w_s w) = CODELENS ->
  evt usegs (fun ms' => IPOST X (arm_CODELENS ivar_ref flush w) ms' /\ PATI X (wof (arm_CODELENS ivar_ref flush w))) ms.

Definition len__core_stmt : Prop := forall X w x26 x12 ms,
  ILOOP X w PC_LEN_ x26 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LEN_ ->
  evt usegs (fun ms' => IPOST X (arm_LEN_ ivar_ref w) ms' /\ PATI X (wof (arm_LEN_ ivar_ref w))) ms.
End Z_infl_t_iface.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.

Module Z_infl_a_match.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateOkb.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb.RefInflateA_MATCH1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_MATCH_J : Z := 0x21050.
Definition PC_MATCH_T : Z := 0x21078.

Definition mt_s1 (s : inflate_state) : inflate_state := iset_length s (is_length s - 1).
Definition mt_c1 (s : inflate_state) (c : icall) : icall := icset_outbuf c (arr_set (ic_outbuf c) 0 (arr_get (is_window s) (mt_idx s))).
Definition mt_r1 (r : iregs) : iregs := irset_put (irset_left r 0) 1.

Lemma match_tail : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_MATCH_T q ms ->
  h9 q = wz (il_NO (ix_L X) + ir_put r) -> h10 q = wz (-2) -> h18 q = wz (ir_bits r) -> h22 q = wz (ir_hold r) ->
  h24 q = wz (ir_have r) -> h25 q = wz (il_NI (ix_L X) + ir_next r) ->
  h11 q = wz (il_Aw (ix_L X) + mt_idx s) -> h12 q = wz 1 -> h13 q = wz (bv_swrap 32 (is_length s)) -> h14 q = wz 1 ->
  ix_ok X -> ix_hasw X = true -> is_window_blk s <> None -> 0 <= mt_idx s < 32768 -> 0 <= arr_get (is_window s) (mt_idx s) < 256 ->
  ir_left r = 1 -> ir_put r = 0 -> arr_len (ic_outbuf c) = 1 -> length (ix_rest0 X) = 1%nat -> 1 <= is_length s < 2^32 -> 0 <= is_mode s < 2^31 ->
  evt usegs (IPOST X (if is_length s - 1 =? 0 then ARun tt (mkW (iset_mode (mt_s1 s) LEN) (mt_c1 s c) (mt_r1 r)) else ARun tt (mkW (mt_s1 s) (mt_c1 s c) (mt_r1 r)))) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         E9 E10 E18 E22 E24 E25 E11 E12 E13 E14 XO HASW NWB RIDX RBYTE HL1 HP0 HOB HR0 RLEN RMODE.
  iarm_openh HL. subst. ix_open XO.
  pose proof (xo_win _ XO HASW) as XWin.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (av8_zlength (is_window s) 32768 ltac:(lia)) as LWIN.
  open_IST ST. open_isA GA.
  unfold iwin in Gwin. destruct (is_window_blk s) as [wb|] eqn:EWB; [|contradiction]. clear NWB.
  pose proof (munch_refl (ix_Wf X) m) as MUf; unfold ix_Wf in MUf; pose proof (wmono_refl usegs m) as WMf.
  unfold PC_MATCH_T.
  do 2 zs.
  zs. rewrite bv_swrap32_sub_land. set (l1 := bv_swrap 32 (is_length s - 1)). pose proof (bv_swrap32_range (is_length s - 1)) as Rl1. fold l1 in Rl1.
  do 3 zs.
  do 2 zs. gF. zs. gF.
  ld8 Gwin (is_window s) 32768 (il_Aw (ix_L X)) (mt_idx s) ltac:(exact RBYTE).
  do 3 zs.
  pose proof (u8arr_store_ok usegs _ _ _ (ir_put r) (wa (il_NO (ix_L X) + ir_put r)) OUT ltac:(lia) eq_refl) as SOK.
  zs. rewrite le1_wz_byte by exact RBYTE.
  pose proof (u8arr_write usegs _ _ _ (ir_put r) (Z_to_bv 8 (arr_get (is_window s) (mt_idx s))) OUT ltac:(lia)) as OUT2. clear OUT LOB.
  store_done.
  rewrite iout_bytes_store in OUT2 by lia.
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) (arr_get (is_window s) (mt_idx s)))) (ir_put r + 1) ltac:(lia)) as LOB.
  apply (f_equal Z.of_nat) in LOB.
  zs. gF. do 4 zs. zstep. br_cases K.
  - apply (proj1 (land64_zero_iff l1 ltac:(lia))) in K. unfold l1 in K. apply (proj1 (bv_swrap32_zero_iff (is_length s - 1) ltac:(lia))) in K.
    replace (is_length s - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; exact K).
    do 4 zs. itr_groups MUf WMf.
    apply evt_done. cbn [IPOST]. eexists _, _. eapply ILOOP_intro; unfold mt_s1, mt_c1, mt_r1; ired; try ireg.
    rewrite HP0 in OUT2. change (0 + 1) with 1 in OUT2.
    apply IMEM_intro; ired.
    + exists j0, jf. exact FRM.
    + exact STK.
    + exact ZS.
    + constructor; ired; [unfold isA, isA_cells; ired; rewrite EWB; close_cells GA; apply le4_swrap32| exact GT| exact Gl| exact Gw| exact Gc| unfold iwin; ired; rewrite EWB; exact Gwin| exact ARRS| unfold ilay_ok in *; ired; exact LAY].
    + exact IN.
    + unfold iout; exact OUT2.
    + eassumption.
    + exact MU.
    + exact WM.
  - assert (K' : is_length s - 1 <> 0).
    { intros E. apply K. apply (proj2 (land64_zero_iff l1 ltac:(lia))). unfold l1. apply (proj2 (bv_swrap32_zero_iff (is_length s - 1) ltac:(lia))). exact E. }
    replace (is_length s - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact K').
    zs. itr_groups MUf WMf.
    apply evt_done. cbn [IPOST]. eexists _, _. eapply ILOOP_intro; unfold mt_s1, mt_c1, mt_r1; ired; try ireg.
    rewrite HP0 in OUT2. change (0 + 1) with 1 in OUT2.
    apply IMEM_intro; ired.
    + exists j0, jf. exact FRM.
    + exact STK.
    + exact ZS.
    + constructor; ired; [unfold isA, isA_cells; ired; rewrite EWB; close_cells GA; apply le4_swrap32| exact GT| exact Gl| exact Gw| exact Gc| unfold iwin; ired; rewrite EWB; exact Gwin| exact ARRS| unfold ilay_ok in *; ired; exact LAY].
    + exact IN.
    + unfold iout; exact OUT2.
    + eassumption.
    + exact MU.
    + exact WM.
Qed.


Local Ltac fin_cut HMEM EIDX :=
  apply evt_done; eexists; split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|];
  cbn [h9 h10 h11 h12 h13 h14 h18 h22 h24 h25]; rewrite EIDX; rewrite ?land_u32_small by lia; repeat split; ireg.
Local Ltac clamps HMEM EIDX ESL sl s :=
  let K5 := fresh "K5" in
  do 3 zs; gX; zs; rewrite ESL; zstep; br_cases K5;
  [ zs; gF; zs; fin_cut HMEM EIDX
  |
    let Esl := fresh "Esl" in let B1 := fresh "B" in let B2 := fresh "B" in
    let K6 := fresh "K6" in
    assert (B1 : 0 <= is_length s < 2^32) by lia; pose proof K5 as K6; unfold sl in K6;
    lazymatch type of K6 with _ <= ?y => assert (B2 : 0 <= y < 2^31) by lia end;
    apply (proj1 (sx32u_le_small (is_length s) _ B1 B2)) in K6;
    assert (Esl : sl = is_length s) by (unfold sl; apply bv_swrap32_id; lia);
    zs; rewrite Esl; zs; gF; zs; rewrite <- Esl; fin_cut HMEM EIDX ].

Lemma match_core : forall X w x26 x12 ms,
  ILOOP X w PC_MATCH x26 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = MATCH ->
  evt usegs (fun ms' => IPOST X (arm_MATCH ivar_ref w) ms' /\ PATI X (wof (arm_MATCH ivar_ref w))) ms.
Proof.
  intros X [s c r] x26 x12 ms HL XO HW HP HM.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  destruct HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & (POB & POW & POL & PNP & PHW) & PBK). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & Hlen1 & Hoff).
  destruct (match_win_facts s HCORE Pwb) as (Hws & Hwh & Hwn & HWIN). apply (id : _ -> hide _) in HWIN.
  assert (Csane : is_sane s = 1) by (destruct HCORE as (_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
  assert (Clen : 0 <= is_length s < 2^32) by (destruct HCORE as (_&_&_&_&_&_&_&_&_&_&_&_&_&H); exact H).
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (RMODE : 0 <= is_mode s < 2^31) by (rewrite HM; unfold MATCH; lia).
  apply (id : _ -> hide _) in Pisr. apply (id : _ -> hide _) in Pwin. apply (id : _ -> hide _) in POW.
  clear HCORE HWF HWB Pfl Pgz PNP RH Rin PHW.
  pose proof HMEM as ((j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_MATCH.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  zs. zstep. br_cases K.
  -
    assert (Kl : ir_left r = 0) by lia.
    rewrite (arm_MATCH_eq s c r Csane). replace (ir_left r =? 0) with true by (symmetry; apply Z.eqb_eq; exact Kl).
    do 3 zs. unfold hide in Pwin.
    itr_groups MUf WMf.
    apply evt_done. split; [|exact HP].
    cbn [IPOST]. eapply ILEAVE_intro; ired; try ireg.
    apply IMEML_intro; ired.
    + exists (wz (ir_ret r)), j0, jf. unfold iframe_cells. rewrite Kl. exact FRM.
    + exact STK.
    + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; ired; close_cells ZS.
    + constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
    + exact IN.
    + exact OUT.
    + eassumption.
    + exact MU.
    + exact WM.
  - assert (HL1 : ir_left r = 1) by lia. assert (HP0 : ir_put r = 0) by lia. assert (HO1 : ir_out r = 1) by lia.
    rewrite (arm_MATCH_pat s c r Csane HL1 HO1 HP0) by lia.
    do 4 zs. rewrite Z.add_0_r. zs. br_cases K2.
    { exfalso. rewrite HO1, HL1 in K2. change (1 - 1) with 0 in K2. apply (proj2 (Z.nlt_ge _ _)) in K2. apply K2. apply sx32u_lt_small; lia. }
    clear K2. replace (ir_out r - ir_left r) with 0 by lia.
    do 3 zs. rewrite Z.sub_0_r in *. br_cases K3.
    2:{
        assert (Kf : is_whave s < is_offset s) by (apply Z.nle_gt; intros C; apply (proj2 (Z.nle_gt _ _) K3); apply sx32u_le_small; lia).
        replace (is_whave s <? is_offset s) with true by (symmetry; apply Z.ltb_lt; exact Kf).
        open_isT GT. do 2 zs. rewrite Csane. zs. br_false.
        do 5 zs. unfold hide in Pwin.
        itr_groups MUf WMf.
        apply evt_done. split.
        - cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; try ireg.
          apply IMEM_intro; ired.
          + exists j0, jf. exact FRM.
          + exact STK.
          + eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; ired; close_cells ZS.
          + constructor; ired; [unfold isA, isA_cells; ired; close_cells GA| unfold isT, isT_cells; exists padT; ired; close_cells GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
          + exact IN.
          + unfold iout; exact OUT.
          + eassumption.
          + exact MU.
          + exact WM.
        - cbn [wof]. unfold hide in Pisr. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..| exact Pisr| bk_keep]. }
    assert (Kok : is_offset s <= is_whave s) by (apply (proj1 (sx32u_le_small (is_offset s) (is_whave s) ltac:(lia) ltac:(lia))); exact K3).
    replace (is_whave s <? is_offset s) with false by (symmetry; apply Z.ltb_ge; exact Kok).
    destruct (HWIN ltac:(lia)) as (EWS & NWB & RIDX & WN).
    assert (HASW : ix_hasw X = true) by (apply Pwin; exact NWB).
    assert (RBYTE : 0 <= arr_get (is_window s) (mt_idx s) < 256).
    { apply POW. destruct ARRS as (_ & _ & _ & AW). rewrite (AW NWB). exact RIDX. }
    assert (EWA : win_addr (ix_L X) (is_window_blk s) = il_Aw (ix_L X)) by (destruct (is_window_blk s); [reflexivity| contradiction]).
    rewrite EWA in GA. pose proof (xo_win _ XO HASW) as XWin.
    pose proof (bv_swrap32_range (is_length s)) as RSL. pose proof (sx32_wz_u (is_length s)) as ESL.
    set (sl := bv_swrap 32 (is_length s)) in *. rewrite HL1 in FRM.
    eapply (evt_cut usegs (fun ms1 => exists q, ILOOPh X (mkW s c r) PC_MATCH_T q ms1
         /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
         /\ h24 q = wz (ir_have r) /\ h25 q = wz (il_NI (ix_L X) + ir_next r)
         /\ h11 q = wz (il_Aw (ix_L X) + mt_idx s) /\ h12 q = wz 1 /\ h13 q = wz sl /\ h14 q = wz 1)).
    { rewrite (bv_swrap32_id (is_offset s)) by lia. do 2 zs. br_cases K4.
      -
        assert (EIDX : mt_idx s = is_wnext s - is_offset s) by (unfold mt_idx; replace (is_wnext s <? is_offset s) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        do 5 zs. rewrite land_u32_small by lia. gF. clamps HMEM EIDX ESL sl s.
      -
        assert (EIDX : mt_idx s = is_wsize s - (is_offset s - is_wnext s)) by (unfold mt_idx; replace (is_wnext s <? is_offset s) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
        do 7 zs. rewrite land_u32_small by lia. gT. clamps HMEM EIDX ESL sl s. }
    intros ms1 (q & HJ & E9 & E10 & E18 & E22 & E24 & E25 & E11 & E12 & E13 & E14).
    eapply evt_mono; [exact (match_tail X s c r q ms1 HJ E9 E10 E18 E22 E24 E25 E11 E12 E13 E14 XO HASW NWB RIDX RBYTE HL1 HP0 ltac:(lia) ltac:(lia) ltac:(lia) RMODE)|].
    intros ms' HPO. split; [exact HPO|]. unfold hide in Pisr.
    destruct (is_length s - 1 =? 0); cbn [wof];
      (eapply (PATI_step_put X s c r _ _ _ (arr_get (is_window s) (mt_idx s)));
       [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| ired; rewrite ?HM; unfold LEN, MATCH, FLAGS, HCRC; lia| reflexivity| reflexivity
       | ired; rewrite HP0; reflexivity| exact RBYTE| lia| ired; lia| reflexivity| ired; lia| ired; rewrite ?HM; reflexivity| exact Pisr| bk_keep]).
Qed.

Lemma arm_MATCH_ok : forall flush, arm_stmt flush MATCH PC_MATCH (arm_MATCH ivar_ref).
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (match_core X w _ x12 ms HL XO HW HP HM). Qed.
End Z_infl_a_match.

Module Z_infl_a_distext.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_match.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb.RefInflateA_MATCH1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1.RefInflateA_DISTEXT OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_DISTEXT_E : Z := 0x20ebc.
Definition PC_DISTEXT_J : Z := 0x20f38.

Definition DXE (X : ictx) (s : inflate_state) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
  /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r) /\ h25 q = wz (il_NI (ix_L X) + ir_next r)
  /\ h14 q = wz (is_extra s) /\ h12 q = wz (ir_have r).

Definition DXQ (X : ictx) (s : inflate_state) (r : iregs) (r1 : iregs) (q : iscrh) : Prop :=
  h14 q = wz (is_extra s) /\ h13 q = wz (il_NI (ix_L X) + ir_next r1) /\ h11 q = wz (ir_bits r1) /\ h24 q = wz (ir_have r1)
  /\ h22 q = wz (ir_hold r1) /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2).

Lemma distext_nb : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_DISTEXT_E q ms -> DXE X s r q ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> 1 <= is_extra s <= 15 ->
  evt usegs (NBJq X s c r (is_extra s) PC_DISTEXT_J (DXQ X s r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E9 & E10 & E11 & E13 & E18 & E22 & E25 & E14 & E12) XO HREGS HP REX.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *. subst.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  unfold PC_DISTEXT_E. ix_open XO.
  zs. br_false. zs. br_cases K.
  -
    do 3 zs. apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
    + unfold DXQ. cbn [h9 h10 h11 h13 h14 h22 h24]. repeat split; reflexivity.
  - do 8 zs. rewrite !land_u32_small by lia. zstep. br_cases K2.
    +
      assert (H0 : ir_have r = 0) by lia.
      do 9 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
    +
      assert (H1 : ir_have r = 1) by lia.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      do 2 zs. gF. zs. gF.
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 7 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      zstep. br_cases K3.
      *
        zstep. br_true. do 9 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [|split].
        -- apply nb_pull_dry; lia.
        -- right. reflexivity.
        -- unfold hide in RH. eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
      * zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
        -- apply nb_pull_ok; lia.
        -- right. split; [reflexivity| lia].
        -- eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
        -- unfold hide in RH. unfold DXQ. cbn [h9 h10 h11 h13 h14 h22 h24]. pullr_rw c r. repeat split; ireg.
Qed.


Lemma distext_fin : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_DISTEXT_J q ms -> DXQ X s r r1 q ->
  ix_ok X -> PATI X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  1 <= is_extra s <= 15 -> 1 <= is_offset s < 2^16 -> is_extra s <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2^64 ->
  0 <= ir_have r1 < 2^32 -> 0 <= ir_next r1 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists x26 x12, ILOOP X (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s))) PC_MATCH x26 x12 ms') ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E14 & E13 & E11 & E24 & E22 & E9 & E10) XO HP EI EO ER EP EL REX ROFF RB1 RH1 RHV1 RN1 RPUT.
  apply (ILOOPh_regs X s c r r1) in HL; [|assumption..].
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_DISTEXT_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r1) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  pose proof (bv_swrap32_range (is_back s)) as RBK. pose proof (sx32_wz_u (is_back s)) as EBK. set (bk := bv_swrap 32 (is_back s)) in *.
  zs. gF. do 4 zs. rewrite EBK. do 4 zs. rewrite clang_mask32 by lia.
  pose proof (land_ones_rng (ir_hold r1) (is_extra s) ltac:(lia)) as RV. set (v := Z.land (ir_hold r1) (Z.ones (is_extra s))) in *.
  assert (RV' : 0 <= v < 32768) by (split; [lia|]; eapply Z.lt_le_trans; [exact (proj2 RV)|]; change 32768 with (2^15); apply Z.pow_le_mono_r; lia).
  clear RV.
  assert (EV : BITSv (ir_hold r1) (is_extra s) = v) by (unfold v; apply BITSv_land; lia).
  do 10 zs. rewrite (land63_small (is_extra s)) by lia.
  itr_groups MUf WMf.
  apply evt_done. eexists _, _. eapply ILOOP_intro; unfold dx_s, dx_r; ired; [ireg .. |].
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; rewrite EV, (wrap32_id (is_offset s + v)) by lia; close_cells GA
                        | unfold isT, isT_cells; exists padT; inorm; close_cells GT; unfold bk; apply le4_back_add
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Lemma distext_core : forall X w q ms,
  ILOOPh X w PC_DISTEXT_E q ms -> DXE X (w_s w) (w_r w) q ->
  ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = DISTEXT ->
  evt usegs (fun ms' => IPOST X (arm_DISTEXT ivar_ref w) ms' /\ PATI X (wof (arm_DISTEXT ivar_ref w))) ms.
Proof.
  intros X [s c r] q ms HL HE XO HW HP HM. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & Hlen1 & REX & ROFF).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  destruct (Z.eq_dec (is_extra s) 0) as [E0|NE0].
  -
    rewrite (arm_DISTEXT_off s c r E0).
    assert (HN : distext_next (mkW s c r) = Some (mkW (iset_mode s MATCH) c r)).
    { unfold distext_next. cbn [w_s w_c w_r]. rewrite E0. reflexivity. }
    destruct (distext_next_WINV _ _ HW HM HN) as [HW2 HM2].
    assert (HP2 : PATI X (mkW (iset_mode s MATCH) c r)).
    { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold MATCH, FLAGS, HCRC; cbn; lia| reflexivity..| exact Pisr| bk_keep]. }
    eapply (evt_cut usegs (fun ms1 => exists x26 x12, ILOOP X (mkW (iset_mode s MATCH) c r) PC_MATCH x26 x12 ms1)).
    2:{ intros ms1 (x26' & x12' & H1). exact (match_core X _ x26' x12' ms1 H1 XO HW2 HP2 HM2). }
    destruct q as [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31].
    destruct HE as (E9 & E10 & E11 & E13 & E18 & E22 & E25 & E14 & E12).
    destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
    clear HW HW2 HP2 HCORE HWF HWB Pfl Pgz Pisr POBY RH Rin HP.
    iarm_openh HL. subst. ix_open XO. unfold PC_DISTEXT_E.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. ifine m.
    zs. rewrite E0. br_true. do 4 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; inorm;
    [ exists j0, jf; exact FRM | exact STK | exact ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
  - rewrite (arm_DISTEXT_on s c r NE0).
    eapply evt_cut; [exact (distext_nb X s c r q ms HL HE XO HREGS HP ltac:(lia))|].
    intros ms1 [(r1 & q1 & EN & HR1 & HJ & HQ)|(r1 & EN & HR1 & HLV)].
    2:{ rewrite EN. apply evt_done. split; [exact HLV|]. cbn [wof].
        destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
    rewrite EN.
    assert (HN : distext_next (mkW s c r) = Some (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s)))).
    { unfold distext_next. cbn [w_s w_c w_r]. replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0). rewrite EN. reflexivity. }
    destruct (distext_next_WINV _ _ HW HM HN) as [HW2 HM2].
    destruct (nb_r1_facts c r r1 (is_extra s) HREGS ltac:(rewrite Pin; exact Pin1) ltac:(lia) HR1) as (EI & EO & ER & EP & EL & RB1 & RH1 & RHV1 & RN1).
    assert (HP2 : PATI X (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s)))).
    { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold MATCH, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
      unfold bk_ok, dx_s. rewrite HM. cbn -[Z.add Z.mul Z.opp Z.sub Z.le Z.lt Z.eqb swrap32]. unfold bkmax. cbn -[swrap32 Z.le Z.add]. intros [B1 B2].
      rewrite swrap32_id by lia. lia. }
    eapply evt_cut.
    { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
      exact (distext_fin X s c r r1 q1 ms1 HJ HQ XO HP EI EO ER EP EL ltac:(lia) ROFF RB1 RH1 RHV1 RN1 ltac:(lia)). }
    intros ms2 (x26' & x12' & H2). exact (match_core X _ x26' x12' ms2 H2 XO HW2 HP2 HM2).
Qed.

Lemma arm_DISTEXT_ok : forall flush, arm_stmt flush DISTEXT PC_DISTEXT (arm_DISTEXT ivar_ref).
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. cbn [w_s] in HM.
  eapply (evt_cut usegs (fun ms1 => exists q, ILOOPh X (mkW s c r) PC_DISTEXT_E q ms1 /\ DXE X s r q)).
  2:{ intros ms1 (q & H1 & HE). exact (distext_core X _ q ms1 H1 HE XO HW HP HM). }
  pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF. rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & _ & REX & _).
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
  unfold PC_DISTEXT. do 3 zs.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
  unfold DXE. cbn [h9 h10 h11 h12 h13 h14 h18 h22 h25]. repeat split; reflexivity.
Qed.
End Z_infl_a_distext.

Module Z_infl_a_dist1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_c_tab.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_match OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_distext.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_DIST2 RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition DECJ (X : ictx) (s : inflate_state) (c : icall) (r0 r : iregs) (p : codeptr) (index need : Z -> Z) (pcj : Z)
    (Q : iregs -> iscrh -> Prop) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 q, DECODE_k 8 p index need (mkW s c r) = ARun (code_at s p (index (ir_hold r1))) (mkW s c r1)
                  /\ dchk 8 c index need (ctab_size p) (code_at s p) r = Some r1
                  /\ need (code_at s p (index (ir_hold r1))) <= ir_bits r1
                  /\ 0 <= index (ir_hold r1) < ctab_size p
                  /\ (r1 = r \/ (r1 = pullr c r /\ ir_have r = 1 /\ ir_bits r <= 31))
                  /\ ILOOPh X (mkW s c r0) pcj q ms' /\ Q r1 q)
    \/ (exists r1, DECODE_k 8 p index need (mkW s c r) = ALeave (mkW s c r1) /\ (r1 = r \/ (r1 = pullr c r /\ ir_have r = 1 /\ ir_bits r <= 31)) /\ ILEAVE X (mkW s c r1) ms').

Definition PC_DIST_L1 : Z := 0x20cb8.
Definition PC_DIST_J1 : Z := 0x20d38.
Definition dist_Q1 (X : ictx) (s : inflate_state) (r : iregs) (r1 : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)) in
  h30 q = wz (code_w e) /\ h28 q = wz (code_bits e) /\ h7 q = wz (code_w e ≫ 8)
  /\ h15 q = wz (ir_bits r1) /\ h14 q = wz (ir_bits r1) /\ h22 q = wz (ir_hold r1)
  /\ h12 q = wz (ir_have r1) /\ h16 q = wz (ir_have r1) /\ h17 q = wz (8 * ir_have r1)
  /\ h5 q = wz (il_NI (ix_L X) + ir_next r1) /\ h6 q = wz (il_NI (ix_L X) + ir_next r1)
  /\ h11 q = wz (cp_addr (ix_L X) (is_distcode s)) /\ h13 q = wz 1
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2).

Definition DE (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h24 q = wz (ir_have r) /\ h25 q = wz (il_NI (ix_L X) + ir_next r).
Lemma DE_of_hhome : forall X r q, hhome X r q -> DE X r q.
Proof. intros X r q (E9 & E10 & _ & _ & E18 & E22 & E24 & E25). repeat split; assumption. Qed.

Lemma dist_lvl1 : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_DIST q ms -> DE X r q -> ix_ok X -> REGS c r -> PATI X (mkW s c r) ->
  0 <= is_distbits s <= 15 -> cp_ofs_ok (is_distcode s) ->
  dlvl c s (is_distcode s) (dec_idx1 (is_distbits s)) code_bits r ->
  evt usegs (DECJ X s c r r (is_distcode s) (dec_idx1 (is_distbits s)) code_bits PC_DIST_J1 (dist_Q1 X s r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E9 & E10 & E18 & E22 & E24 & E25) XO HREGS HP RN CPO DL.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x9 x10 x18 x22 x24 x25.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. open_isA GA.
  unfold PC_DIST. ix_open XO.
  set (p := is_distcode s) in *. set (n := is_distbits s) in *.
  pose proof (dec_idx1_land n (ir_hold r) ltac:(lia) RN) as EI0. pose proof (dec_idx1_range n (ir_hold r) ltac:(lia) RN) as RI0'.
  pose proof (dl_i0 _ _ _ _ _ _ DL) as RI0. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN0. pose proof (ones_range15 n RN) as RMK.
  do 2 zs. gF. do 4 zs. rewrite clang_mask32 by lia. zs. rewrite EI0.
  set (i0 := dec_idx1 n (ir_hold r)) in *. set (e0 := code_at s p i0) in *.
  pose proof (code_bits_range e0) as RB0. pose proof (cp_addr_rng (ix_L X) p i0 CPO RI0 ltac:(lia)) as CPR.
  zs. rewrite (Z.shiftl_mul_pow2 i0 2) by lia. change (2^2) with 4. zs. gF. do 3 zs. gX.
  replace (0 <? cp_addr (ix_L X) p) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  do 9 zs. rewrite !land_u32_small by lia.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2 + 2)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e0); lia). clear RD.
  pose proof (code_rd_lo m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e0); lia). clear RD.
  do 2 zs. rewrite code_w_or_step. pose proof (code_w_range e0) as RW0. do 2 zs. rewrite code_w_bits.
  rewrite (shl32_shr29 (ir_have r)) by lia.
  zstep. br_cases K.
  -
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i0; fold e0; lia)) as [ED EC].
    apply evt_done. left. eexists r, _. split; [exact ED|]. split; [exact EC|]. split; [fold i0; fold e0; lia|]. split; [exact RI0|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold dist_Q1. cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h22 h28 h30]. fold p. fold n. fold i0. fold e0. repeat split; try reflexivity; ireg.
  - assert (K' : ir_bits r < code_bits (code_at s p (dec_idx1 n (ir_hold r)))) by (fold i0; fold e0; exact K).
    zstep. br_cases K2.
    +
      assert (H0 : ir_have r = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 10 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
    +
      assert (H1 : ir_have r = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI1 RN1].
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      do 2 zs. gF. zs. gF.
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      assert (EH1 : arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r + ir_hold r = ir_hold (pullr c r)).
      { unfold hide in RH. rewrite pullr_hold by (first [assumption | lia]). lia. }
      pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
      assert (RH1 : 0 <= ir_hold (pullr c r) < 2^64).
      { rewrite <- EH1. split; [lia|]. eapply Z.lt_le_trans; [rewrite Z.add_comm; exact (proj2 PR)|]. apply Z.pow_le_mono_r; lia. }
      rewrite EH1. clear PR EH1.
      pose proof (dec_idx1_land n (ir_hold (pullr c r)) ltac:(lia) RN) as EI1. pose proof (dec_idx1_range n (ir_hold (pullr c r)) ltac:(lia) RN) as RI1'.
      set (h1 := ir_hold (pullr c r)) in *.
      zs. rewrite EI1. set (i1 := dec_idx1 n h1) in *. set (e1 := code_at s p i1) in *. pose proof (code_bits_range e1) as RB1.
      pose proof (cp_addr_rng (ix_L X) p i1 CPO RI1 ltac:(lia)) as CPR1.
      zs. rewrite (Z.shiftl_mul_pow2 i1 2) by lia. change (2^2) with 4. zs. gF.
      do 6 zs. rewrite xor_guard1 by lia. do 2 zs. zstep. br_true.
      do 2 zs.
      pose proof (code_rd_val m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 2)) MI Gc CPO RI1 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e1 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e1); lia). clear RD.
      pose proof (code_rd_lo m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2)) MI Gc CPO RI1 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e1 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e1); lia). clear RD.
      do 2 zs. rewrite code_w_or_step. pose proof (code_w_range e1) as RW1. do 2 zs. rewrite code_w_bits.
      zstep. br_cases K3.
      * assert (K3' : code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r)))) <= ir_bits (pullr c r)) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        apply evt_done. left. eexists (pullr c r), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI1|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold dist_Q1. cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h22 h28 h30]. fold p. fold n. fold h1. fold i1. fold e1.
        repeat split; try reflexivity; try (pullr_rw c r; ireg).
      *
        assert (K3' : ir_bits (pullr c r) < code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r))))) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zstep. br_true. do 10 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e1 i1 h1. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| reflexivity..]]; pullr_rw c r; ireg.
Qed.

Definition PC_DIST_T : Z := 0x20e6c.
Definition dist_QT (X : ictx) (here : Z) (rt : iregs) (r0 : iregs) (q : iscrh) : Prop :=
  h30 q = wz (code_w here) /\ h29 q = wz (code_op here) /\ h20 q = wz (code_bits here) /\ h21 q = wz (code_w here ≫ 8)
  /\ h14 q = wz (ir_bits rt) /\ h22 q = wz (ir_hold rt) /\ h12 q = wz (ir_have rt) /\ h25 q = wz (il_NI (ix_L X) + ir_next rt)
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r0) /\ h10 q = wz (-2).

Lemma dist_direct : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J1 q ms -> dist_Q1 X s r0 r1 q -> ix_ok X ->
  dist_two (code_op (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))) = false ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW s c r0) PC_DIST_T q' ms'
                                   /\ dist_QT X (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))) r1 r0 q') ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO TWO.
  destruct HQ as (E30 & E28 & E7 & E15 & E14 & E22 & E12 & E16 & E17 & E5 & E6 & E11 & E13 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *. subst.
  iarm_openh_keep HL HMEM.
  set (p := is_distcode s) in *. set (i := dec_idx1 (is_distbits s) (ir_hold r1)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_w_range e) as RW.
  assert (K16 : 16 <= code_op e).
  { unfold dist_two in TWO. rewrite (land240_le15 _ ROP) in TWO. apply Z.leb_gt in TWO. lia. }
  ix_open XO. unfold PC_DIST_J1.
  zs. rewrite code_w_op. do 2 zs. br_true. do 4 zs.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
  unfold dist_QT. cbn [h9 h10 h12 h14 h20 h21 h22 h25 h29 h30]. repeat split; reflexivity.
Qed.

Definition PC_DIST_L2 : Z := 0x20da8.
Definition PC_DIST_J2 : Z := 0x20e44.
Definition dist_Q2 (X : ictx) (s : inflate_state) (last : Z) (r1 r2 : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_distcode s) (dec_idx2 last (ir_hold r2)) in
  h30 q = wz (code_w e) /\ h21 q = wz (code_w e ≫ 8) /\ h20 q = wz (code_bits e) /\ h24 q = wz (code_bits e + code_bits last)
  /\ h19 q = wz (ir_bits r2) /\ h22 q = wz (ir_hold r2) /\ h12 q = wz (ir_have r2) /\ h25 q = wz (il_NI (ix_L X) + ir_next r2)
  /\ h14 q = wz (ir_bits r1) /\ h15 q = wz (ir_bits r1) /\ h16 q = wz (ir_have r1) /\ h17 q = wz (8 * ir_have r1) /\ h5 q = wz (il_NI (ix_L X) + ir_next r1)
  /\ h18 q = wz (code_bits last + ir_bits r1 - ir_bits r2)
  /\ h28 q = wz (code_bits last) /\ h29 q = wz (code_val last) /\ h7 q = wz (code_w last ≫ 8)
  /\ h11 q = wz (cp_addr (ix_L X) (is_distcode s)) /\ h13 q = wz 1
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r1) /\ h10 q = wz (-2).

Lemma dist_lvl2 : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J1 q ms -> dist_Q1 X s r0 r1 q -> ix_ok X -> PATI X (mkW s c r0) ->
  ir_in r1 = ir_in r0 -> ir_out r1 = ir_out r0 -> ir_put r1 = ir_put r0 -> ir_left r1 = ir_left r0 -> ir_ret r1 = ir_ret r0 ->
  0 <= ir_have r1 <= 1 -> 0 <= ir_next r1 -> ir_next r1 + ir_have r1 = arr_len (ic_input c) -> 0 <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  0 <= dec_idx1 (is_distbits s) (ir_hold r1) < ctab_size (is_distcode s) -> cp_ofs_ok (is_distcode s) ->
  forall last, last = code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)) ->
  dist_two (code_op last) = true -> code_bits last <= ir_bits r1 -> code_bits last + code_op last <= 31 ->
  dlvl c s (is_distcode s) (dec_idx2 last) (dec_need2 last) r1 ->
  evt usegs (DECJ X s c r0 r1 (is_distcode s) (dec_idx2 last) (dec_need2 last) PC_DIST_J2 (dist_Q2 X s last r1)) ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP EI EO EP EL ER
         RHV RNX RNH RB RH Rin RI CPO last ELAST TWO KB K31 DL.
  destruct HQ as (E30 & E28 & E7 & E15 & E14 & E22 & E12 & E16 & E17 & E5 & E6 & E11 & E13 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x30 x28 x7 x15 x14 x22 x12 x16 x17 x5 x6 x11 x13 x9 x10.
  iarm_openh_keep HL HMEM.
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  set (p := is_distcode s) in *. set (i := dec_idx1 (is_distbits s) (ir_hold r1)) in *. rewrite <- ELAST in *.
  pose proof (code_op_range last) as ROP. pose proof (code_val_range last) as RVAL. pose proof (code_bits_range last) as RBITS. pose proof (code_w_range last) as RWL.
  assert (K15 : code_op last <= 15).
  { unfold dist_two in TWO. rewrite (land240_le15 _ ROP) in TWO. apply Z.leb_le in TWO. exact TWO. }
  assert (RH64 : 0 <= ir_hold r1 < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  pose proof (Rin (ir_next r1)) as RBy. apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. ix_open XO. unfold PC_DIST_J1.
  zs. rewrite code_w_op. do 2 zs. br_false.
  do 2 zs. rewrite code_w_ge000 by lia. gF.
  zs. rewrite code_w_land15, (land15_small (code_op last)) by lia. do 2 zs. gF.
  zs. rewrite code_w_val.
  pose proof (ones_range31 (code_bits last + code_op last) ltac:(lia)) as RMK2.
  pose proof (land_ones_le (ir_hold r1) (code_bits last + code_op last) ltac:(lia)) as RHM.
  do 3 zs. rewrite clang_mask32 by lia. set (mk2 := Z.ones (code_bits last + code_op last)) in *.
  zs. set (hm := Z.land (ir_hold r1) mk2) in *.
  pose proof (shiftr_le hm (code_bits last) ltac:(lia) ltac:(lia)) as RSH.
  zs. rewrite (srlw_small hm (code_bits last)) by lia. set (sh := hm ≫ code_bits last) in *.
  zs.
  assert (EI2 : sh + code_val last = dec_idx2 last (ir_hold r1)) by (rewrite dec_idx2_clang by lia; reflexivity).
  pose proof (dl_i0 _ _ _ _ _ _ DL) as RI2. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN2.
  do 2 zs. rewrite (zext32_x4 (sh + code_val last)) by lia. rewrite EI2.
  set (i2 := dec_idx2 last (ir_hold r1)) in *. set (e2 := code_at s p i2) in *. pose proof (code_bits_range e2) as RB2. pose proof (code_w_range e2) as RW2.
  assert (EN2 : dec_need2 last e2 = code_bits last + code_bits e2) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
  rewrite EN2 in *.
  pose proof (cp_addr_rng (ix_L X) p i2 CPO RI2 ltac:(lia)) as CPR2.
  zs. gF. do 2 zs. rewrite xor_guard1 by lia. zstep. br_false. zs. do 3 zs. rewrite (land_u32_small i2) by lia.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i2 (wa (cp_addr (ix_L X) p + i2 ≪ 2 + 2)) MI Gc CPO RI2 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e2 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e2); lia). clear RD.
  pose proof (code_rd_lo m (ix_L X) s p i2 (wa (cp_addr (ix_L X) p + i2 ≪ 2)) MI Gc CPO RI2 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e2 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e2); lia). clear RD.
  do 2 zs. rewrite code_w_or_step. do 2 zs. rewrite code_w_bits. zs.
  zstep. br_cases K.
  -
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i2; fold e2; rewrite EN2; lia)) as [ED EC].
    apply evt_done. left. eexists r1, _. split; [exact ED|]. split; [exact EC|]. split; [fold i2; fold e2; rewrite EN2; lia|]. split; [exact RI2|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold dist_Q2. cbn [h5 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h28 h29 h30 h31]. fold p. fold i2. fold e2.
    repeat split; try reflexivity; ireg.
  - assert (K' : ir_bits r1 < dec_need2 last (code_at s p (dec_idx2 last (ir_hold r1)))) by (fold i2; fold e2; rewrite EN2; lia).
    zstep. br_cases K2.
    +
      assert (H0 : ir_have r1 = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 7 zs. rewrite H0. rewrite ?Z.add_0_r, ?Z.mul_0_r, ?Z.add_0_l.
      apply evt_done. right. exists r1. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| assumption..].
    +
      assert (H1 : ir_have r1 = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI3 RN3].
      assert (NXT : 0 <= ir_next r1 < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      do 2 zs. gF. zs. gF.
      pose proof (u8ro_read usegs _ _ _ (ir_next r1) _ (wa (il_NI (ix_L X) + ir_next r1)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      assert (EH2 : arr_get (ic_input c) (ir_next r1) * 2 ^ ir_bits r1 + ir_hold r1 = ir_hold (pullr c r1)).
      { unfold hide in RH. rewrite pullr_hold by (first [assumption | lia]). lia. }
      pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r1)) (ir_bits r1) (ir_hold r1) RBy ltac:(lia) RH) as PR.
      assert (RH2 : 0 <= ir_hold (pullr c r1) < 2^64).
      { rewrite <- EH2. split; [lia|]. eapply Z.lt_le_trans; [rewrite Z.add_comm; exact (proj2 PR)|]. apply Z.pow_le_mono_r; lia. }
      rewrite EH2. clear PR EH2.
      pose proof (land_ones_le (ir_hold (pullr c r1)) (code_bits last + code_op last) ltac:(lia)) as RHM3. fold mk2 in RHM3.
      assert (EI3 : (Z.land (ir_hold (pullr c r1)) mk2 ≫ code_bits last) + code_val last = dec_idx2 last (ir_hold (pullr c r1))) by (rewrite dec_idx2_clang by lia; reflexivity).
      set (h2 := ir_hold (pullr c r1)) in *.
      zs. set (hm3 := Z.land h2 mk2) in *.
      pose proof (shiftr_le hm3 (code_bits last) ltac:(lia) ltac:(lia)) as RSH3.
      zs. rewrite (srlw_small hm3 (code_bits last)) by lia. set (sh3 := hm3 ≫ code_bits last) in *.
      zs. rewrite EI3.
      set (i3 := dec_idx2 last h2) in *. set (e3 := code_at s p i3) in *. pose proof (code_bits_range e3) as RB3. pose proof (code_w_range e3) as RW3.
      assert (EN3 : dec_need2 last e3 = code_bits last + code_bits e3) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
      rewrite EN3 in *.
      pose proof (cp_addr_rng (ix_L X) p i3 CPO RI3 ltac:(lia)) as CPR3.
      do 2 zs. rewrite (zext32_x4 i3) by lia. zs. gF.
      do 3 zs. rewrite (land_u32_small i3) by lia. do 2 zs. rewrite xor_guard1 by lia. do 2 zs. zstep. br_true.
      do 2 zs.
      pose proof (code_rd_val m (ix_L X) s p i3 (wa (cp_addr (ix_L X) p + i3 ≪ 2 + 2)) MI Gc CPO RI3 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e3 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e3); lia). clear RD.
      pose proof (code_rd_lo m (ix_L X) s p i3 (wa (cp_addr (ix_L X) p + i3 ≪ 2)) MI Gc CPO RI3 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e3 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e3); lia). clear RD.
      do 2 zs. rewrite code_w_or_step. do 2 zs. rewrite code_w_bits. zs.
      zstep. br_cases K3.
      * assert (K3' : dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r1)))) <= ir_bits (pullr c r1)) by (fold h2; fold i3; fold e3; rewrite EN3; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        apply evt_done. left. eexists (pullr c r1), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI3|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold dist_Q2. cbn [h5 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h28 h29 h30 h31]. fold p. fold h2. fold i3. fold e3.
        repeat split; try reflexivity; try (pullr_rw c r1; ireg).
      *
        assert (K3' : ir_bits (pullr c r1) < dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r1))))) by (fold h2; fold i3; fold e3; rewrite EN3; rewrite pullr_bits by lia; lia).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zstep. br_true. do 7 zs. rewrite H1.
        apply evt_done. right. exists (pullr c r1). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e3 i3 sh3 hm3 h2. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| assumption..]]; pullr_rw c r1; ireg.
Qed.

Lemma dist_j2 : forall X s c r0 r1 r2 last q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J2 q ms -> dist_Q2 X s last r1 r2 q -> ix_ok X -> PATI X (mkW s c r0) ->
  0 <= dec_idx2 last (ir_hold r2) < ctab_size (is_distcode s) -> cp_ofs_ok (is_distcode s) ->
  code_bits last <= ir_bits r2 <= 63 -> 0 <= ir_hold r2 < 2^64 -> 0 <= ir_bits r1 <= 63 -> code_bits last + code_op last <= 31 ->
  -1 <= is_back s <= 525 -> 0 <= ir_put r0 <= Z.of_nat (length (ix_rest0 X)) -> ir_put r1 = ir_put r0 ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (addback s (code_bits last)) c r0) PC_DIST_T q' ms'
                                   /\ dist_QT X (code_at s (is_distcode s) (dec_idx2 last (ir_hold r2))) (ddrop r2 (code_bits last)) r0 q') ms.
Proof.
  intros X s c r0 r1 r2 last [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP RI CPO RB RH RB1 K31 BK RPUT EP.
  destruct HQ as (E30 & E21 & E20 & E23 & E19 & E22 & E12 & E25 & E14 & E15 & E16 & E17 & E5 & E18 & E28 & E29 & E7 & E11 & E13 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x30 x21 x20 x24 x19 x22 x12 x25 x14 x15 x16 x17 x5 x18 x28 x29 x7 x11 x13 x9 x10.
  iarm_openh HL.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  set (p := is_distcode s) in *. set (i := dec_idx2 last (ir_hold r2)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_bits_range e) as RBITS. pose proof (code_w_range e) as RWE.
  pose proof (code_bits_range last) as RLB. pose proof (code_op_range last) as RLO. pose proof (code_w_range last) as RWL.
  ix_open XO. unfold PC_DIST_J2.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r0) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  do 4 zs. rewrite addw_land64 by lia. gF.
  zs. rewrite subw_land64 by lia. zs. rewrite code_w_g31 by lia. zs. rewrite code_w_op. zs. rewrite (land63_small (code_bits last)) by lia.
  zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]|].
  - unfold addback. apply IMEM_intro; inorm;
    [ exists j0, jf; exact FRM | exact STK | exact ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA
                          | unfold isT, isT_cells; exists padT; inorm; close_cells GT; apply le4_swrap32_r
                          | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
  - unfold dist_QT, ddrop. cbn [h9 h10 h12 h14 h20 h21 h22 h25 h29 h30 ir_bits ir_hold ir_have ir_next irset_bits irset_hold].
    rewrite EP. repeat split; try reflexivity. all: rewrite ?wrap32_id by lia; f_equal; lia.
Qed.

End Z_infl_a_dist1.


Module Z_infl_a_dist.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_match OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_distext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_DIST2 RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition dt_bad (s : inflate_state) (c : icall) (here : Z) (rt : iregs) (Bm : Z) : iw :=
  mkW (iset_mode (iset_back s Bm) BAD) (icset_msg c MSG_invalid_distance_code) (ddrop rt (code_bits here)).
Definition dt_ok (s : inflate_state) (c : icall) (here : Z) (rt : iregs) (Bm : Z) : iw :=
  mkW (iset_mode (iset_extra (iset_offset (iset_back s Bm) (code_val here)) (Z.land (code_op here) 15)) DISTEXT) c (ddrop rt (code_bits here)).

Lemma dist_tail_walk : forall X sb c r0 rt here q ms,
  ILOOPh X (mkW sb c r0) PC_DIST_T q ms -> dist_QT X here rt r0 q -> ix_ok X -> (is_window_blk sb <> None -> ix_hasw X = true) ->
  ir_in rt = ir_in r0 -> ir_out rt = ir_out r0 -> ir_ret rt = ir_ret r0 -> ir_put rt = ir_put r0 -> ir_left rt = ir_left r0 ->
  -1 <= is_back sb <= 780 ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  0 <= ir_put r0 <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' =>
     if negb (Z.land (code_op here) 64 =? 0) then exists x26 x12, ILOOP X (dt_bad sb c here rt (swrap32 (is_back sb + code_bits here))) PC_DISPATCH x26 x12 ms'
     else exists q', ILOOPh X (dt_ok sb c here rt (swrap32 (is_back sb + code_bits here))) PC_DISTEXT_E q'  ms'
                     /\ DXE X (w_s (dt_ok sb c here rt (swrap32 (is_back sb + code_bits here)))) (w_r (dt_ok sb c here rt (swrap32 (is_back sb + code_bits here)))) q') ms.
Proof.
  intros X sb c r0 rt here [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP
         EI EO ER EP EL BK RB RH RHV RNX RPUT.
  destruct HQ as (E30 & E29 & E20 & E21 & E14 & E22 & E12 & E25 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x30 x29 x20 x21 x14 x22 x12 x25 x9 x10.
  apply (ILOOPh_regs X sb c r0 rt) in HL; [|assumption..].
  iarm_openh HL. rename HP into Pwin.
  pose proof (code_op_range here) as ROP. pose proof (code_val_range here) as RVAL. pose proof (code_bits_range here) as RBITS. pose proof (code_w_range here) as RW.
  ix_open XO. unfold PC_DIST_T.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put rt) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT. open_izs ZS.
  pose proof (munch_refl [(il_S (ix_L X), il_S (ix_L X) + 112); (ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168);
                          (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  pose proof (land64_cases (code_op here) ROP) as R64. pose proof (land15_range (code_op here)) as R15.
  zs. rewrite (code_w_g192 here) by lia. gF.
  do 4 zs. rewrite addw_land64 by lia. zs. gF.
  zs. zs. rewrite (code_w_g63 here) by lia. do 3 zs.
  zstep. br_cases K.
  -
    replace (Z.land (code_op here) 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    do 6 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; unfold dt_bad, ddrop; ired; [ireg .. |].
    apply IMEM_intro; inorm;
    [ exists j0, jf; exact FRM | exact STK
    | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT; apply le4_swrap32_r
                          | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
  - replace (Z.land (code_op here) 64 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
    zs. rewrite code_w_val. do 5 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold dt_ok, ddrop; ired; [ireg .. |]| unfold DXE, dt_ok, ddrop; cbn [w_s w_r h9 h10 h11 h12 h13 h14 h18 h22 h25 ir_bits ir_hold ir_have ir_next ir_put irset_bits irset_hold is_extra iset_mode iset_extra iset_offset iset_back]; repeat split; try reflexivity; ireg].
    apply IMEM_intro; inorm;
    [ exists j0, jf; exact FRM | exact STK
    | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT; apply le4_swrap32_r
                          | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.


Lemma cpok_ofs_ok : forall ty codes p root, cpok ty codes p root -> cp_ofs_ok p.
Proof. intros ty codes [ofs| |] root H; cbn in *; [exact (proj1 H)| exact I| exact I]. Qed.

Lemma dist_fin : forall X s sb c r rt here q ms,
  ILOOPh X (mkW sb c r) PC_DIST_T q ms -> dist_QT X here rt r q -> ix_ok X -> WINV (mkW s c r) -> PATI X (mkW s c r) -> is_mode s = DIST ->
  is_window_blk sb = is_window_blk s -> -1 <= is_back sb <= 780 -> (forall B, iset_back sb B = iset_back s B) ->
  ir_in rt = ir_in r -> ir_out rt = ir_out r -> ir_ret rt = ir_ret r -> ir_put rt = ir_put r -> ir_left rt = ir_left r ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  dist_next (mkW s c r) = dist_tailnext s c here rt sb ->
  evt usegs (fun ms' => IPOST X (dist_tail c here rt sb) ms' /\ PATI X (wof (dist_tail c here rt sb))) ms.
Proof.
  intros X s sb c r rt here q ms HL HQ XO HW HP HM EWB BKS ESBB EI EO ER EP EL RB RH RHV RNX HN.
  pose proof HW as (_ & HREGS & _). cbn [w_s w_c w_r] in HREGS. destruct HREGS as (_ & _ & _ & Rp & Rl & Rpl & _).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  pose proof (code_bits_range here) as RBITS. pose proof (code_op_range here) as ROP. pose proof (land15_range (code_op here)) as R15.
  eapply evt_cut; [exact (dist_tail_walk X sb c r rt here q ms HL HQ XO ltac:(rewrite EWB; exact Pwin) EI EO ER EP EL BKS RB RH RHV RNX ltac:(lia))|].
  intros ms1 H1. unfold dist_tail. unfold dist_tailnext, dt_s in HN. cbv zeta. unfold addback. unfold dt_bad, dt_ok in H1. rewrite !ESBB in H1 |- *.
  set (Bm := swrap32 (is_back sb + code_bits here)) in *.
  assert (RBm : -1 <= Bm <= 1035) by (unfold Bm; rewrite swrap32_id by lia; lia).
  destruct (negb (Z.land (code_op here) 64 =? 0)).
  - destruct H1 as (x26' & x12' & H1). apply evt_done. split; [cbn [IPOST]; exists x26', x12'; exact H1|]. cbn [wof].
    eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
    unfold bk_ok, bkmax. cbn -[Z.le Z.add Z.opp]. intros _. lia.
  - destruct H1 as (q' & H1 & HE).
    destruct (dist_next_WINV _ _ HW HM HN) as [HW3 HM3].
    refine (distext_core X _ q' ms1 H1 HE XO HW3 _ HM3).
    eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DISTEXT, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
    unfold bk_ok, bkmax. cbn -[Z.le Z.add Z.opp]. intros _. lia.
Qed.

Lemma dist_core : forall X w q ms,
  ILOOPh X w PC_DIST q ms -> DE X (w_r w) q -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = DIST ->
  evt usegs (fun ms' => IPOST X (arm_DIST ivar_ref w) ms' /\ PATI X (wof (arm_DIST ivar_ref w))) ms.
Proof.
  intros X [s c r] q ms HL HE XO HW HP HM. cbn [w_s w_r] in HM, HE.
  pose proof (WINV_dist_okb _ HW HM) as OKB. unfold dist_okb in OKB. cbn [w_s w_c w_r] in OKB.
  pose proof HW as (HCORE & HREGS & HMF & _). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & [_ TD] & _).
  pose proof (cpok_ofs_ok _ _ _ _ TD) as CPO.
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  pose proof (PATI_bk _ _ _ _ HP) as PBK. assert (BK0 : -1 <= is_back s <= 525) by (unfold bk_ok, bkmax in PBK; rewrite HM in PBK; cbn in PBK; lia).
  assert (HIN1 : arr_len (ic_input c) <= 1) by (rewrite Pin; exact Pin1).
  pose proof (DREGS_of_REGS c r HREGS HIN1) as DR.
  assert (Rin : forall i, 0 <= arr_get (ic_input c) i < 256) by (destruct HREGS as (_&_&_&_&_&_&_&H&_); exact H).
  assert (RPUT : 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X))) by (destruct HREGS as (_&_&_&Rp&Rl&Rpl&_); lia).
  destruct (decode_okb_lvl1 _ _ _ _ _ _ OKB) as [RN D1].
  pose proof (dlvl_of_dchk c s _ _ _ r D1 ltac:(destruct DR as (_&H&_); exact H) ltac:(destruct DR as (_&_&_&H&_); lia)) as DL1.
  rewrite arm_DIST_eq. change (DECODE1 (is_distcode s) (is_distbits s)) with (DECODE_k 8 (is_distcode s) (dec_idx1 (is_distbits s)) code_bits).
  eapply evt_cut; [exact (dist_lvl1 X s c r q ms HL HE XO HREGS HP RN CPO DL1)|].
  intros ms1 [(r1 & q1 & ED1 & EC1 & KB1 & RI1 & HR1 & HJ1 & HQ1)|(r1 & ED1 & HR1 & HLV)].
  2:{ rewrite ED1. apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct (dec_r1_facts c r r1 DR Rin HR1) as (_ & _ & EO1 & _ & EP1 & EL1). eapply PATI_regs; [exact HP| assumption..]. }
  rewrite ED1.
  destruct (dec_r1_facts c r r1 DR Rin HR1) as (DR1 & EI1 & EO1 & ER1 & EP1 & EL1).
  assert (HN0 : dist_next (mkW s c r) =
                if dist_two (code_op (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))) then
                  match DECODE_k 8 (is_distcode s) (dec_idx2 (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))))
                                 (dec_need2 (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))) (mkW s c r1) with
                  | ARun here (mkW _ _ r2) => dist_tailnext s c here (ddrop r2 (code_bits (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))))
                                                (addback s (code_bits (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))))
                  | _ => None
                  end
                else dist_tailnext s c (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))) r1 s).
  { unfold dist_next. cbn [w_s w_c w_r]. change (DECODE1 (is_distcode s) (is_distbits s)) with (DECODE_k 8 (is_distcode s) (dec_idx1 (is_distbits s)) code_bits).
    rewrite ED1. reflexivity. }
  set (last := code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))) in *.
  pose proof (code_bits_range last) as RLB. pose proof (code_op_range last) as RLO.
  pose proof (DREGS_hold64 c r1 DR1) as RH1. destruct DR1 as (RNX1 & RHV1 & RNH1 & RB1 & RHB1).
  change (Z.land (code_op last) 240 =? 0) with (dist_two (code_op last)).
  change (DECODE2 (is_distcode s) last) with (DECODE_k 8 (is_distcode s) (dec_idx2 last) (dec_need2 last)).
  destruct (dist_two (code_op last)) eqn:TWO.
  -
    destruct (decode_okb_lvl2 _ _ _ _ _ _ r1 OKB EC1 KB1 TWO) as [K31 D2]. fold last in K31, D2.
    pose proof (dlvl_of_dchk c s _ _ _ r1 D2 RHV1 ltac:(lia)) as DL2.
    eapply evt_cut; [exact (dist_lvl2 X s c r r1 q1 ms1 HJ1 HQ1 XO HP EI1 EO1 EP1 EL1 ER1 RHV1 RNX1 RNH1 RB1 RHB1 Rin RI1 CPO last eq_refl TWO KB1 K31 DL2)|].
    intros ms2 [(r2 & q2 & ED2 & EC2 & KB2 & RI2 & HR2 & HJ2 & HQ2)|(r2 & ED2 & HR2 & HLV)].
    2:{ rewrite ED2. apply evt_done. split; [exact HLV|]. cbn [wof].
        destruct (dec_r1_facts c r1 r2 (conj RNX1 (conj RHV1 (conj RNH1 (conj RB1 RHB1)))) Rin HR2) as (_ & _ & EO2 & _ & EP2 & EL2).
        eapply PATI_regs; [exact HP| congruence..]. }
    rewrite ED2. rewrite ED2 in HN0.
    destruct (dec_r1_facts c r1 r2 (conj RNX1 (conj RHV1 (conj RNH1 (conj RB1 RHB1)))) Rin HR2) as (DR2 & EI2 & EO2 & ER2 & EP2 & EL2).
    pose proof (DREGS_hold64 c r2 DR2) as RH2. destruct DR2 as (RNX2 & RHV2 & RNH2 & RB2 & RHB2).
    set (e2 := code_at s (is_distcode s) (dec_idx2 last (ir_hold r2))) in *. pose proof (code_bits_range e2) as RHB.
    assert (KB2' : code_bits last + code_bits e2 <= ir_bits r2) by (unfold dec_need2 in KB2; rewrite wrap32_id in KB2 by lia; exact KB2).
    eapply evt_cut; [exact (dist_j2 X s c r r1 r2 last q2 ms2 HJ2 HQ2 XO HP RI2 CPO ltac:(lia) RH2 ltac:(lia) K31 BK0 RPUT EP1)|].
    intros ms3 (q3 & HJ3 & HQ3). fold e2 in HQ3.
    destruct (ddrop_facts' r2 (code_bits last) ltac:(lia) ltac:(lia) RH2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    refine (dist_fin X s (addback s (code_bits last)) c r (ddrop r2 (code_bits last)) e2 q3 ms3 HJ3 HQ3 XO HW HP HM eq_refl _ (fun B => eq_refl) _ _ _ _ _ _ F7 _ _ HN0);
      try congruence; try lia.
    unfold addback. cbn [is_back iset_back]. rewrite swrap32_id by lia. lia.
  -
    eapply evt_cut; [exact (dist_direct X s c r r1 q1 ms1 HJ1 HQ1 XO TWO)|].
    intros ms3 (q3 & HJ3 & HQ3). fold last in HQ3.
    refine (dist_fin X s s c r r1 last q3 ms3 HJ3 HQ3 XO HW HP HM eq_refl _ (fun B => eq_refl) EI1 EO1 ER1 EP1 EL1 _ RH1 _ _ HN0); lia.
Qed.

Lemma arm_DIST_ok : forall flush, arm_stmt flush DIST PC_DIST (arm_DIST ivar_ref).
Proof.
  intros flush X w x12 ms _ HL XO HW _ HP HM. destruct (ILOOPh_of_ILOOP _ _ _ _ _ _ HL) as (q & HLh & _ & _ & HH).
  exact (dist_core X w q ms HLh (DE_of_hhome _ _ _ HH) XO HW HP HM).
Qed.
End Z_infl_a_dist.


Module Z_infl_a_lenext.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_match OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_distext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST.RefInflateA_LENEXT OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_LENEXT_NB : Z := 0x1f0b0.
Definition PC_LENEXT_OFF : Z := 0x20c3c.
Definition PC_LENEXT_J : Z := 0x1fd04.

Definition LXE (X : ictx) (s : inflate_state) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h11 q = wz (is_extra s) /\ h12 q = wz (ir_have r) /\ h14 q = wz (il_NI (ix_L X) + ir_next r).
Definition LXO (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h12 q = wz (ir_have r) /\ h14 q = wz (il_NI (ix_L X) + ir_next r).
Definition LXQ (X : ictx) (s : inflate_state) (r : iregs) (r1 : iregs) (q : iscrh) : Prop :=
  h11 q = wz (is_extra s) /\ h13 q = wz (ir_bits r1) /\ h22 q = wz (ir_hold r1) /\ h24 q = wz (ir_have r1)
  /\ h25 q = wz (il_NI (ix_L X) + ir_next r1) /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2).

Lemma lenext_nb : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LENEXT_NB q ms -> LXE X s r q ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> 1 <= is_extra s <= 15 ->
  evt usegs (NBJq X s c r (is_extra s) PC_LENEXT_J (LXQ X s r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E9 & E10 & E18 & E22 & E11 & E12 & E14) XO HREGS HP REX.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *. subst.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  unfold PC_LENEXT_NB. ix_open XO.
  zs. br_cases K.
  -
    do 3 zs. apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
    + unfold LXQ. cbn [h9 h10 h11 h13 h22 h24 h25]. repeat split; reflexivity.
  - do 8 zs. rewrite !land_u32_small by lia. zstep. br_cases K2.
    +
      assert (H1 : ir_have r = 1) by lia.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      do 2 zs. gT. zs. gT.
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 7 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      zstep. br_cases K3.
      *
        zstep. br_false. do 10 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [|split].
        -- apply nb_pull_dry; lia.
        -- right. reflexivity.
        -- unfold hide in RH. eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
      * zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
        -- apply nb_pull_ok; lia.
        -- right. split; [reflexivity| lia].
        -- eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
        -- unfold hide in RH. unfold LXQ. cbn [h9 h10 h11 h13 h22 h24 h25]. pullr_rw c r. repeat split; ireg.
    +
      assert (H0 : ir_have r = 0) by lia.
      do 10 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma lenext_fin : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_LENEXT_J q ms -> LXQ X s r r1 q ->
  ix_ok X -> PATI X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  1 <= is_extra s <= 15 -> 1 <= is_length s < 2^16 -> is_extra s <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2^64 ->
  0 <= ir_have r1 < 2^32 -> 0 <= ir_next r1 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (lx_fin (lx_s s (ir_hold r1))) c (ddrop r1 (is_extra s))) PC_DIST q' ms'
                                   /\ DE X (ddrop r1 (is_extra s)) q') ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E11 & E13 & E22 & E24 & E25 & E9 & E10) XO HP EI EO ER EP EL REX RLEN RB1 RH1 RHV1 RN1 RPUT.
  apply (ILOOPh_regs X s c r r1) in HL; [|assumption..].
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LENEXT_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r1) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  pose proof (bv_swrap32_range (is_back s)) as RBK. pose proof (sx32_wz_u (is_back s)) as EBK. set (bk := bv_swrap 32 (is_back s)) in *.
  zs. gT. do 4 zs. rewrite EBK. do 4 zs. rewrite clang_mask32 by lia.
  pose proof (land_ones_rng (ir_hold r1) (is_extra s) ltac:(lia)) as RV. set (v := Z.land (ir_hold r1) (Z.ones (is_extra s))) in *.
  assert (RV' : 0 <= v < 32768) by (split; [lia|]; eapply Z.lt_le_trans; [exact (proj2 RV)|]; change 32768 with (2^15); apply Z.pow_le_mono_r; lia).
  clear RV.
  assert (EV : BITSv (ir_hold r1) (is_extra s) = v) by (unfold v; apply BITSv_land; lia).
  do 6 zs. rewrite (land63_small (is_extra s)) by lia.
  do 5 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold lx_fin, lx_s, ddrop; ired; [ireg .. |]
                                 | unfold DE, lx_fin, lx_s, ddrop; cbn [h9 h10 h18 h22 h24 h25 ir_bits ir_hold ir_have ir_next ir_put irset_bits irset_hold]; repeat split; try reflexivity; ireg].
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; rewrite EV, (wrap32_id (is_length s + v)) by lia; close_cells GA
                        | unfold isT, isT_cells; exists padT; inorm; rewrite EV, (wrap32_id (is_length s + v)) by lia; close_cells GT; unfold bk; apply le4_back_add
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Local Ltac close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA | unfold isT, isT_cells; exists padT; inorm; close_cells GT
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma lenext_off : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LENEXT_OFF q ms -> LXO X r q ->
  ix_ok X -> PATI X (mkW s c r) -> 1 <= is_length s < 2^16 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (lx_fin s) c r) PC_DIST q' ms' /\ DE X r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E9 & E10 & E18 & E22 & E12 & E14) XO HP RLEN RPUT.
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *. subst.
  iarm_openh HL.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LENEXT_OFF.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  do 7 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold lx_fin; ired; [ireg .. |]
                                 | unfold DE; cbn [h9 h10 h18 h22 h24 h25]; repeat split; reflexivity].
  close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma lenext_core_on : forall X w q ms,
  ILOOPh X w PC_LENEXT_NB q ms -> LXE X (w_s w) (w_r w) q ->
  ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LENEXT -> is_extra (w_s w) <> 0 ->
  evt usegs (fun ms' => IPOST X (arm_LENEXT ivar_ref w) ms' /\ PATI X (wof (arm_LENEXT ivar_ref w))) ms.
Proof.
  intros X [s c r] q ms HL HE XO HW HP HM NE0. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & REX & RLEN).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  rewrite (arm_LENEXT_on s c r NE0).
  eapply evt_cut; [exact (lenext_nb X s c r q ms HL HE XO HREGS HP ltac:(lia))|].
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & HQ)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite EN. apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  rewrite EN.
  assert (HN : lenext_next (mkW s c r) = Some (mkW (lx_fin (lx_s s (ir_hold r1))) c (ddrop r1 (is_extra s)))).
  { unfold lenext_next. cbn [w_s w_c w_r]. replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0). rewrite EN. reflexivity. }
  destruct (lenext_next_WINV _ _ HW HM HN) as [HW2 HM2].
  destruct (nb_r1_facts c r r1 (is_extra s) HREGS ltac:(rewrite Pin; exact Pin1) ltac:(lia) HR1) as (EI & EO & ER & EP & EL & RB1 & RH1 & RHV1 & RN1).
  assert (HP2 : PATI X (mkW (lx_fin (lx_s s (ir_hold r1))) c (ddrop r1 (is_extra s)))).
  { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold lx_fin; cbn [is_mode iset_mode]; unfold DIST, FLAGS, HCRC; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
    unfold bk_ok, lx_fin, lx_s. rewrite HM. cbn -[Z.add Z.mul Z.opp Z.sub Z.le Z.lt Z.eqb swrap32 wrap32 BITSv]. unfold bkmax. cbn -[swrap32 wrap32 BITSv Z.le Z.add].
    intros [B1 B2]. rewrite swrap32_id by lia. lia. }
  eapply evt_cut.
  { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
    exact (lenext_fin X s c r r1 q1 ms1 HJ HQ XO HP EI EO ER EP EL ltac:(lia) RLEN RB1 RH1 RHV1 RN1 ltac:(lia)). }
  intros ms2 (q2 & H2 & HE2). exact (dist_core X _ q2 ms2 H2 HE2 XO HW2 HP2 HM2).
Qed.

Lemma lenext_core_off : forall X w q ms,
  ILOOPh X w PC_LENEXT_OFF q ms -> LXO X (w_r w) q ->
  ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LENEXT -> is_extra (w_s w) = 0 ->
  evt usegs (fun ms' => IPOST X (arm_LENEXT ivar_ref w) ms' /\ PATI X (wof (arm_LENEXT ivar_ref w))) ms.
Proof.
  intros X [s c r] q ms HL HE XO HW HP HM E0. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & REX & RLEN).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  rewrite (arm_LENEXT_off s c r E0).
  assert (HN : lenext_next (mkW s c r) = Some (mkW (lx_fin s) c r)).
  { unfold lenext_next. cbn [w_s w_c w_r]. rewrite E0. reflexivity. }
  destruct (lenext_next_WINV _ _ HW HM HN) as [HW2 HM2].
  assert (HP2 : PATI X (mkW (lx_fin s) c r)).
  { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold lx_fin; cbn [is_mode iset_mode]; unfold DIST, FLAGS, HCRC; lia| reflexivity..| exact Pisr|].
    unfold bk_ok, lx_fin. rewrite HM. cbn -[Z.add Z.mul Z.opp Z.sub Z.le Z.lt Z.eqb]. unfold bkmax. cbn -[Z.le Z.add]. lia. }
  eapply evt_cut.
  { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _). exact (lenext_off X s c r q ms HL HE XO HP RLEN ltac:(lia)). }
  intros ms2 (q2 & H2 & HE2). exact (dist_core X _ q2 ms2 H2 HE2 XO HW2 HP2 HM2).
Qed.

Lemma arm_LENEXT_ok : forall flush, arm_stmt flush LENEXT PC_LENEXT (arm_LENEXT ivar_ref).
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. cbn [w_s] in HM.
  pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF. rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & REX & _).
  destruct (Z.eq_dec (is_extra s) 0) as [E0|NE0].
  - eapply (evt_cut usegs (fun ms1 => exists q, ILOOPh X (mkW s c r) PC_LENEXT_OFF q ms1 /\ LXO X r q)).
    2:{ intros ms1 (q & H1 & HE). exact (lenext_core_off X _ q ms1 H1 HE XO HW HP HM E0). }
    destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
    unfold PC_LENEXT. zs. rewrite E0. do 3 zs. br_false. zs.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|]. unfold LXO. cbn [h9 h10 h12 h14 h18 h22]. repeat split; reflexivity.
  - eapply (evt_cut usegs (fun ms1 => exists q, ILOOPh X (mkW s c r) PC_LENEXT_NB q ms1 /\ LXE X s r q)).
    2:{ intros ms1 (q & H1 & HE). exact (lenext_core_on X _ q ms1 H1 HE XO HW HP HM NE0). }
    destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
    pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
    unfold PC_LENEXT. do 4 zs. br_true.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|]. unfold LXE. cbn [h9 h10 h11 h12 h14 h18 h22]. repeat split; reflexivity.
Qed.
End Z_infl_a_lenext.

Module Z_infl_a_len1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_match OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_distext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_DIST2 RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_LEN.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2.RefInflateA_LEN1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LEN OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_LEN_D : Z := 0x209e0.
Definition PC_LEN_J1 : Z := 0x20ab8.

Lemma len_pre : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LEN q ms -> DE X r q -> ix_ok X -> REGS c r -> PATI X (mkW s c r) -> 0 <= is_lenbits s <= 15 ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (iset_back s 0) c r) PC_LEN_D q' ms' /\ DE X r q'
                                   /\ h11 q' = wz (is_lenbits s) /\ h12 q' = wz 31) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E9 & E10 & E18 & E22 & E24 & E25) XO HREGS HP RN.
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *. subst.
  iarm_openh HL.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  clear RH Rin. ix_open XO. unfold PC_LEN.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  do 2 zs. br_true. do 4 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]| unfold DE; cbn [h9 h10 h11 h12 h18 h22 h24 h25]; repeat split; reflexivity].
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA | unfold isT, isT_cells; exists padT; inorm; close_cells GT
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Definition len_Q1 (X : ictx) (s : inflate_state) (r : iregs) (r1 : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  h19 q = wz (code_w e) /\ h7 q = wz (code_bits e) /\ h28 q = wz (code_w e ≫ 8)
  /\ h16 q = wz (ir_bits r1) /\ h11 q = wz (ir_bits r1) /\ h22 q = wz (ir_hold r1)
  /\ h12 q = wz (ir_have r1) /\ h17 q = wz (ir_have r1) /\ h5 q = wz (8 * ir_have r1)
  /\ h14 q = wz (il_NI (ix_L X) + ir_next r1) /\ h6 q = wz (il_NI (ix_L X) + ir_next r1)
  /\ h13 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ h15 q = wz 1
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2).

Lemma len_lvl1 : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LEN_D q ms -> DE X r q -> h11 q = wz (is_lenbits s) -> h12 q = wz 31 -> ix_ok X -> REGS c r -> PATI X (mkW s c r) ->
  0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  dlvl c s (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits r ->
  evt usegs (DECJ X s c r r (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits PC_LEN_J1 (len_Q1 X s r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E9 & E10 & E18 & E22 & E24 & E25) E11 E12 XO HREGS HP RN CPO DL.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x9 x10 x18 x22 x24 x25 x11 x12.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. open_isA GA.
  unfold PC_LEN_D. ix_open XO.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *.
  pose proof (dec_idx1_land n (ir_hold r) ltac:(lia) RN) as EI0. pose proof (dec_idx1_range n (ir_hold r) ltac:(lia) RN) as RI0'.
  pose proof (dl_i0 _ _ _ _ _ _ DL) as RI0. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN0. pose proof (ones_range15 n RN) as RMK.
  gF. do 4 zs. rewrite clang_mask32 by lia. zs. rewrite EI0.
  set (i0 := dec_idx1 n (ir_hold r)) in *. set (e0 := code_at s p i0) in *.
  pose proof (code_bits_range e0) as RB0. pose proof (cp_addr_rng (ix_L X) p i0 CPO RI0 ltac:(lia)) as CPR.
  zs. rewrite (Z.shiftl_mul_pow2 i0 2) by lia. change (2^2) with 4. zs. gF. do 3 zs. gX.
  replace (0 <? cp_addr (ix_L X) p) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  do 9 zs. rewrite !land_u32_small by lia.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2 + 2)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e0); lia). clear RD.
  pose proof (code_rd_lo m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e0); lia). clear RD.
  do 2 zs. rewrite code_w_or_step. pose proof (code_w_range e0) as RW0. do 2 zs. rewrite code_w_bits.
  rewrite (shl32_shr29 (ir_have r)) by lia.
  zstep. br_cases K.
  -
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i0; fold e0; lia)) as [ED EC].
    apply evt_done. left. eexists r, _. split; [exact ED|]. split; [exact EC|]. split; [fold i0; fold e0; lia|]. split; [exact RI0|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold len_Q1. cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h19 h22 h28]. fold p. fold n. fold i0. fold e0. repeat split; try reflexivity; ireg.
  - assert (K' : ir_bits r < code_bits (code_at s p (dec_idx1 n (ir_hold r)))) by (fold i0; fold e0; exact K).
    zstep. br_cases K2.
    +
      assert (H0 : ir_have r = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 9 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
    +
      assert (H1 : ir_have r = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI1 RN1].
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      do 2 zs. gF. zs. gF.
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      assert (EH1 : arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r + ir_hold r = ir_hold (pullr c r)).
      { unfold hide in RH. rewrite pullr_hold by (first [assumption | lia]). lia. }
      pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
      assert (RH1 : 0 <= ir_hold (pullr c r) < 2^64).
      { rewrite <- EH1. split; [lia|]. eapply Z.lt_le_trans; [rewrite Z.add_comm; exact (proj2 PR)|]. apply Z.pow_le_mono_r; lia. }
      rewrite EH1. clear PR EH1.
      pose proof (dec_idx1_land n (ir_hold (pullr c r)) ltac:(lia) RN) as EI1. pose proof (dec_idx1_range n (ir_hold (pullr c r)) ltac:(lia) RN) as RI1'.
      set (h1 := ir_hold (pullr c r)) in *.
      zs. rewrite EI1. set (i1 := dec_idx1 n h1) in *. set (e1 := code_at s p i1) in *. pose proof (code_bits_range e1) as RB1.
      pose proof (cp_addr_rng (ix_L X) p i1 CPO RI1 ltac:(lia)) as CPR1.
      zs. rewrite (Z.shiftl_mul_pow2 i1 2) by lia. change (2^2) with 4. zs. gF.
      do 6 zs. rewrite xor_guard1 by lia. do 2 zs. zstep. br_true.
      do 2 zs.
      pose proof (code_rd_val m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 2)) MI Gc CPO RI1 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e1 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e1); lia). clear RD.
      pose proof (code_rd_lo m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2)) MI Gc CPO RI1 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e1 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e1); lia). clear RD.
      do 2 zs. rewrite code_w_or_step. pose proof (code_w_range e1) as RW1. do 2 zs. rewrite code_w_bits.
      zstep. br_cases K3.
      * assert (K3' : code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r)))) <= ir_bits (pullr c r)) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        apply evt_done. left. eexists (pullr c r), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI1|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold len_Q1. cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h19 h22 h28]. fold p. fold n. fold h1. fold i1. fold e1.
        repeat split; try reflexivity; try (pullr_rw c r; ireg).
      *
        assert (K3' : ir_bits (pullr c r) < code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r))))) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zstep. br_true. do 9 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e1 i1 h1. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| reflexivity..]]; pullr_rw c r; ireg.
Qed.

Definition PC_LEN_T : Z := 0x20be0.
Definition len_QT (X : ictx) (here : Z) (rt : iregs) (Bv : Z) (r0 : iregs) (q : iscrh) : Prop :=
  h19 q = wz (code_w here) /\ h29 q = wz (code_op here) /\ h28 q = wz (code_w here ≫ 8) /\ h7 q = wz Bv
  /\ h11 q = wz (ir_bits rt) /\ h22 q = wz (ir_hold rt) /\ h12 q = wz (ir_have rt) /\ h14 q = wz (il_NI (ix_L X) + ir_next rt)
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r0) /\ h10 q = wz (-2).

Lemma len_two_cases : forall op, 0 <= op < 256 -> len_two op = false -> op = 0 \/ 16 <= op.
Proof.
  intros op Hop H. unfold len_two in H. destruct (Z.eqb_spec op 0) as [E|NE]; [left; exact E| right].
  cbn [negb andb] in H. rewrite (land240_le15 _ Hop) in H. apply Z.leb_gt in H. lia.
Qed.
Lemma len_two_true : forall op, 0 <= op < 256 -> len_two op = true -> 1 <= op <= 15.
Proof.
  intros op Hop H. unfold len_two in H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite (land240_le15 _ Hop) in H2. apply Z.leb_le in H2. apply negb_true_iff in H1. apply Z.eqb_neq in H1. lia.
Qed.

Lemma len_direct : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_LEN_J1 q ms -> len_Q1 X s r0 r1 q -> ix_ok X ->
  len_two (code_op (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)))) = false ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW s c r0) PC_LEN_T q' ms'
                                   /\ len_QT X (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) r1 0 r0 q') ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO TWO.
  destruct HQ as (E19 & E7 & E28 & E16 & E11 & E22 & E12 & E17 & E5 & E14 & E6 & E13 & E15 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *. subst.
  iarm_openh_keep HL HMEM.
  set (p := is_lencode s) in *. set (i := dec_idx1 (is_lenbits s) (ir_hold r1)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_w_range e) as RW.
  ix_open XO. unfold PC_LEN_J1.
  zs. rewrite code_w_op.
  destruct (len_two_cases _ ROP TWO) as [E0|K16].
  - rewrite E0. do 2 zs. zstep. br_true. do 2 zs.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold len_QT. cbn [h7 h9 h10 h11 h12 h14 h19 h22 h28 h29]. rewrite E0. repeat split; reflexivity.
  - do 2 zs. zstep. br_true. do 2 zs.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold len_QT. cbn [h7 h9 h10 h11 h12 h14 h19 h22 h28 h29]. repeat split; reflexivity.
Qed.

Definition PC_LEN_L2 : Z := 0x20b2c.
Definition PC_LEN_J2 : Z := 0x20bc0.
Definition len_Q2 (X : ictx) (s : inflate_state) (last : Z) (r1 r2 : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_lencode s) (dec_idx2 last (ir_hold r2)) in
  h19 q = wz (code_w e) /\ h21 q = wz (code_w e ≫ 8) /\ h24 q = wz (code_bits e + code_bits last) /\ h20 q = wz (ir_bits r2)
  /\ h22 q = wz (ir_hold r2) /\ h12 q = wz (ir_have r2) /\ h31 q = wz (il_NI (ix_L X) + ir_next r2)
  /\ h11 q = wz (ir_bits r1) /\ h16 q = wz (ir_bits r1) /\ h17 q = wz (ir_have r1) /\ h5 q = wz (8 * ir_have r1) /\ h14 q = wz (il_NI (ix_L X) + ir_next r1)
  /\ h18 q = wz (code_bits last + ir_bits r1 - ir_bits r2)
  /\ h7 q = wz (code_bits last) /\ h29 q = wz (code_val last) /\ h28 q = wz (code_w last ≫ 8)
  /\ h13 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ h15 q = wz 1
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r1) /\ h10 q = wz (-2).

Lemma len_lvl2 : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_LEN_J1 q ms -> len_Q1 X s r0 r1 q -> ix_ok X -> PATI X (mkW s c r0) ->
  ir_in r1 = ir_in r0 -> ir_out r1 = ir_out r0 -> ir_put r1 = ir_put r0 -> ir_left r1 = ir_left r0 -> ir_ret r1 = ir_ret r0 ->
  0 <= ir_have r1 <= 1 -> 0 <= ir_next r1 -> ir_next r1 + ir_have r1 = arr_len (ic_input c) -> 0 <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) ->
  forall last, last = code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) ->
  len_two (code_op last) = true -> code_bits last <= ir_bits r1 -> code_bits last + code_op last <= 31 ->
  dlvl c s (is_lencode s) (dec_idx2 last) (dec_need2 last) r1 ->
  evt usegs (DECJ X s c r0 r1 (is_lencode s) (dec_idx2 last) (dec_need2 last) PC_LEN_J2 (len_Q2 X s last r1)) ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP EI EO EP EL ER
         RHV RNX RNH RB RH Rin RI CPO last ELAST TWO KB K31 DL.
  destruct HQ as (E19 & E7 & E28 & E16 & E11 & E22 & E12 & E17 & E5 & E14 & E6 & E13 & E15 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x19 x7 x28 x16 x11 x22 x12 x17 x5 x14 x6 x13 x15 x9 x10.
  iarm_openh_keep HL HMEM.
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  set (p := is_lencode s) in *. set (i := dec_idx1 (is_lenbits s) (ir_hold r1)) in *. rewrite <- ELAST in *.
  pose proof (code_op_range last) as ROP. pose proof (code_val_range last) as RVAL. pose proof (code_bits_range last) as RBITS. pose proof (code_w_range last) as RWL.
  pose proof (len_two_true _ ROP TWO) as K15.
  assert (RH64 : 0 <= ir_hold r1 < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  pose proof (Rin (ir_next r1)) as RBy. apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. ix_open XO. unfold PC_LEN_J1.
  zs. rewrite code_w_op. do 3 zs. br_false.
  do 2 zs. rewrite code_w_ge000 by lia. gF.
  zs. rewrite code_w_op. do 2 zs. gF.
  zs. rewrite code_w_val.
  pose proof (ones_range31 (code_bits last + code_op last) ltac:(lia)) as RMK2.
  pose proof (land_ones_le (ir_hold r1) (code_bits last + code_op last) ltac:(lia)) as RHM.
  do 3 zs. rewrite clang_mask32 by lia. set (mk2 := Z.ones (code_bits last + code_op last)) in *.
  zs. set (hm := Z.land (ir_hold r1) mk2) in *.
  pose proof (shiftr_le hm (code_bits last) ltac:(lia) ltac:(lia)) as RSH.
  zs. rewrite (srlw_small hm (code_bits last)) by lia. set (sh := hm ≫ code_bits last) in *.
  zs.
  assert (EI2 : sh + code_val last = dec_idx2 last (ir_hold r1)) by (rewrite dec_idx2_clang by lia; reflexivity).
  pose proof (dl_i0 _ _ _ _ _ _ DL) as RI2. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN2.
  do 2 zs. rewrite (zext32_x4 (sh + code_val last)) by lia. rewrite EI2.
  set (i2 := dec_idx2 last (ir_hold r1)) in *. set (e2 := code_at s p i2) in *. pose proof (code_bits_range e2) as RB2. pose proof (code_w_range e2) as RW2.
  assert (EN2 : dec_need2 last e2 = code_bits last + code_bits e2) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
  rewrite EN2 in *.
  pose proof (cp_addr_rng (ix_L X) p i2 CPO RI2 ltac:(lia)) as CPR2.
  zs. gF. do 2 zs. rewrite xor_guard1 by lia. zstep. br_false. zs. do 3 zs. rewrite (land_u32_small i2) by lia.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i2 (wa (cp_addr (ix_L X) p + i2 ≪ 2 + 2)) MI Gc CPO RI2 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e2 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e2); lia). clear RD.
  pose proof (code_rd_lo m (ix_L X) s p i2 (wa (cp_addr (ix_L X) p + i2 ≪ 2)) MI Gc CPO RI2 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e2 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e2); lia). clear RD.
  do 2 zs. rewrite code_w_or_step. do 2 zs. rewrite code_w_bits. zs.
  zstep. br_cases K.
  -
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i2; fold e2; rewrite EN2; lia)) as [ED EC].
    apply evt_done. left. eexists r1, _. split; [exact ED|]. split; [exact EC|]. split; [fold i2; fold e2; rewrite EN2; lia|]. split; [exact RI2|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold len_Q2. cbn [h5 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h28 h29 h31]. fold p. fold i2. fold e2.
    repeat split; try reflexivity; ireg.
  - assert (K' : ir_bits r1 < dec_need2 last (code_at s p (dec_idx2 last (ir_hold r1)))) by (fold i2; fold e2; rewrite EN2; lia).
    zstep. br_cases K2.
    +
      assert (H0 : ir_have r1 = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 7 zs. rewrite H0. rewrite ?Z.add_0_r, ?Z.mul_0_r, ?Z.add_0_l.
      apply evt_done. right. exists r1. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| assumption..].
    +
      assert (H1 : ir_have r1 = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI3 RN3].
      assert (NXT : 0 <= ir_next r1 < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      do 2 zs. gF. zs. gF.
      pose proof (u8ro_read usegs _ _ _ (ir_next r1) _ (wa (il_NI (ix_L X) + ir_next r1)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      assert (EH2 : arr_get (ic_input c) (ir_next r1) * 2 ^ ir_bits r1 + ir_hold r1 = ir_hold (pullr c r1)).
      { unfold hide in RH. rewrite pullr_hold by (first [assumption | lia]). lia. }
      pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r1)) (ir_bits r1) (ir_hold r1) RBy ltac:(lia) RH) as PR.
      assert (RH2 : 0 <= ir_hold (pullr c r1) < 2^64).
      { rewrite <- EH2. split; [lia|]. eapply Z.lt_le_trans; [rewrite Z.add_comm; exact (proj2 PR)|]. apply Z.pow_le_mono_r; lia. }
      rewrite EH2. clear PR EH2.
      pose proof (land_ones_le (ir_hold (pullr c r1)) (code_bits last + code_op last) ltac:(lia)) as RHM3. fold mk2 in RHM3.
      assert (EI3 : (Z.land (ir_hold (pullr c r1)) mk2 ≫ code_bits last) + code_val last = dec_idx2 last (ir_hold (pullr c r1))) by (rewrite dec_idx2_clang by lia; reflexivity).
      set (h2 := ir_hold (pullr c r1)) in *.
      zs. set (hm3 := Z.land h2 mk2) in *.
      pose proof (shiftr_le hm3 (code_bits last) ltac:(lia) ltac:(lia)) as RSH3.
      zs. rewrite (srlw_small hm3 (code_bits last)) by lia. set (sh3 := hm3 ≫ code_bits last) in *.
      zs. rewrite EI3.
      set (i3 := dec_idx2 last h2) in *. set (e3 := code_at s p i3) in *. pose proof (code_bits_range e3) as RB3. pose proof (code_w_range e3) as RW3.
      assert (EN3 : dec_need2 last e3 = code_bits last + code_bits e3) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
      rewrite EN3 in *.
      pose proof (cp_addr_rng (ix_L X) p i3 CPO RI3 ltac:(lia)) as CPR3.
      do 2 zs. rewrite (zext32_x4 i3) by lia. zs. gF.
      do 3 zs. rewrite (land_u32_small i3) by lia. do 2 zs. rewrite xor_guard1 by lia. do 2 zs. zstep. br_true.
      do 2 zs.
      pose proof (code_rd_val m (ix_L X) s p i3 (wa (cp_addr (ix_L X) p + i3 ≪ 2 + 2)) MI Gc CPO RI3 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e3 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e3); lia). clear RD.
      pose proof (code_rd_lo m (ix_L X) s p i3 (wa (cp_addr (ix_L X) p + i3 ≪ 2)) MI Gc CPO RI3 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e3 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e3); lia). clear RD.
      do 2 zs. rewrite code_w_or_step. do 2 zs. rewrite code_w_bits. zs.
      zstep. br_cases K3.
      * assert (K3' : dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r1)))) <= ir_bits (pullr c r1)) by (fold h2; fold i3; fold e3; rewrite EN3; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        apply evt_done. left. eexists (pullr c r1), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI3|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold len_Q2. cbn [h5 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h28 h29 h31]. fold p. fold h2. fold i3. fold e3.
        repeat split; try reflexivity; try (pullr_rw c r1; ireg).
      *
        assert (K3' : ir_bits (pullr c r1) < dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r1))))) by (fold h2; fold i3; fold e3; rewrite EN3; rewrite pullr_bits by lia; lia).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zstep. br_true. do 7 zs. rewrite H1.
        apply evt_done. right. exists (pullr c r1). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e3 i3 sh3 hm3 h2. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| assumption..]]; pullr_rw c r1; ireg.
Qed.

Lemma len_j2 : forall X s c r0 r1 r2 last q ms,
  ILOOPh X (mkW s c r0) PC_LEN_J2 q ms -> len_Q2 X s last r1 r2 q -> ix_ok X -> PATI X (mkW s c r0) ->
  0 <= dec_idx2 last (ir_hold r2) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) ->
  code_bits last <= ir_bits r2 <= 63 -> 0 <= ir_hold r2 < 2^64 -> 0 <= ir_bits r1 <= 63 -> code_bits last + code_op last <= 31 ->
  0 <= ir_put r0 <= Z.of_nat (length (ix_rest0 X)) -> ir_put r1 = ir_put r0 ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (iset_back s (code_bits last)) c r0) PC_LEN_T q' ms'
                                   /\ len_QT X (code_at s (is_lencode s) (dec_idx2 last (ir_hold r2))) (ddrop r2 (code_bits last)) (code_bits last) r0 q') ms.
Proof.
  intros X s c r0 r1 r2 last [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP RI CPO RB RH RB1 K31 RPUT EP.
  destruct HQ as (E19 & E21 & E23 & E20 & E22 & E12 & E31 & E11 & E16 & E17 & E5 & E14 & E18 & E7 & E29 & E28 & E13 & E15 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x19 x21 x24 x20 x22 x12 x31 x11 x16 x17 x5 x14 x18 x7 x29 x28 x13 x15 x9 x10.
  iarm_openh HL.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  set (p := is_lencode s) in *. set (i := dec_idx2 last (ir_hold r2)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_bits_range e) as RBITS. pose proof (code_w_range e) as RWE.
  pose proof (code_bits_range last) as RLB. pose proof (code_op_range last) as RLO. pose proof (code_w_range last) as RWL.
  ix_open XO. unfold PC_LEN_J2.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r0) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  zs. rewrite code_w_op. zs. rewrite subw_land64 by lia. zs. rewrite code_w_g31 by lia. zs. rewrite (land63_small (code_bits last)) by lia.
  do 4 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]|].
  - apply IMEM_intro; inorm;
    [ exists j0, jf; exact FRM | exact STK | exact ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA
                          | unfold isT, isT_cells; exists padT; inorm; close_cells GT
                          | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
  - unfold len_QT, ddrop. cbn [h7 h9 h10 h11 h12 h14 h19 h22 h28 h29 ir_bits ir_hold ir_have ir_next irset_bits irset_hold].
    rewrite EP. repeat split; try reflexivity. all: rewrite ?wrap32_id by lia; f_equal; lia.
Qed.
End Z_infl_a_len1.

Module Z_infl_a_len.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_match OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_distext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_lenext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_len1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_DIST2 RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_DIST2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_LEN.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST.RefInflateA_LENEXT OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST2.RefInflateA_LEN1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LEN OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition lt_s1 (s : inflate_state) (here Bv : Z) : inflate_state := iset_length (iset_back s (Bv + code_bits here)) (code_val here).
Definition lt_lx (s : inflate_state) (c : icall) (here : Z) (rt : iregs) (Bv : Z) : iw :=
  mkW (iset_mode (iset_extra (lt_s1 s here Bv) (Z.land (code_op here) 15)) LENEXT) c (ddrop rt (code_bits here)).

Local Ltac close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma len_tail_walk : forall X sb c r0 rt here Bv q ms,
  ILOOPh X (mkW sb c r0) PC_LEN_T q ms -> len_QT X here rt Bv r0 q -> ix_ok X -> (is_window_blk sb <> None -> ix_hasw X = true) ->
  ir_in rt = ir_in r0 -> ir_out rt = ir_out r0 -> ir_ret rt = ir_ret r0 -> ir_put rt = ir_put r0 -> ir_left rt = ir_left r0 ->
  0 <= Bv < 256 ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  0 <= ir_put r0 <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' =>
     if code_op here =? 0 then exists x26 x12, ILOOP X (mkW (iset_mode (lt_s1 sb here Bv) LIT) c (ddrop rt (code_bits here))) PC_DISPATCH x26 x12 ms'
     else if negb (Z.land (code_op here) 32 =? 0)
     then exists x26 x12, ILOOP X (mkW (iset_mode (iset_back (lt_s1 sb here Bv) (-1)) TYPE) c (ddrop rt (code_bits here))) PC_DISPATCH x26 x12 ms'
     else if negb (Z.land (code_op here) 64 =? 0)
     then exists x26 x12, ILOOP X (mkW (iset_mode (lt_s1 sb here Bv) BAD) (icset_msg c MSG_invalid_literal_length_code) (ddrop rt (code_bits here))) PC_DISPATCH x26 x12 ms'
     else if Z.land (code_op here) 15 =? 0
     then exists q', ILOOPh X (lt_lx sb c here rt Bv) PC_LENEXT_OFF q' ms' /\ LXO X (ddrop rt (code_bits here)) q'
     else exists q', ILOOPh X (lt_lx sb c here rt Bv) PC_LENEXT_NB q' ms'
                     /\ LXE X (w_s (lt_lx sb c here rt Bv)) (ddrop rt (code_bits here)) q') ms.
Proof.
  intros X sb c r0 rt here Bv [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO Pwin
         EI EO ER EP EL RBv RB RH RHV RNX RPUT.
  destruct HQ as (E19 & E29 & E28 & E7 & E11 & E22 & E12 & E14 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x19 x29 x28 x7 x11 x22 x12 x14 x9 x10.
  apply (ILOOPh_regs X sb c r0 rt) in HL; [|assumption..].
  iarm_openh HL.
  pose proof (code_op_range here) as ROP. pose proof (code_val_range here) as RVAL. pose proof (code_bits_range here) as RBITS. pose proof (code_w_range here) as RW.
  pose proof (land32_cases (code_op here) ROP) as R32. pose proof (land64_cases (code_op here) ROP) as R64. pose proof (land15_range (code_op here)) as R15.
  ix_open XO. unfold PC_LEN_T.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put rt) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT. open_izs ZS.
  pose proof (munch_refl [(il_S (ix_L X), il_S (ix_L X) + 112); (ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168);
                          (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  zs. rewrite (code_w_g192 here) by lia. gF.
  zs. rewrite code_w_val. zs. rewrite (code_w_g63 here) by lia. zs. rewrite (code_w_g63 here) by lia.
  do 5 zs.
  zstep. br_cases K0.
  -
    replace (code_op here =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    do 8 zs. itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; unfold lt_s1, ddrop; ired; [ireg .. |].
    close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  - replace (code_op here =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    do 3 zs. zstep. br_cases K32.
    +
      replace (Z.land (code_op here) 32 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      do 9 zs. itr_groups MUf WMf.
      apply evt_done. eexists _, _. eapply ILOOP_intro; unfold lt_s1, ddrop; ired; [ireg .. |].
      close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + replace (Z.land (code_op here) 32 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
      zs. zstep. br_cases K64.
      *
        replace (Z.land (code_op here) 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
        do 8 zs. itr_groups MUf WMf.
        apply evt_done. eexists _, _. eapply ILOOP_intro; unfold lt_s1, ddrop; ired; [ireg .. |].
        close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * replace (Z.land (code_op here) 64 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
        do 4 zs. zstep. br_cases K15.
        -- replace (Z.land (code_op here) 15 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
           itr_groups MUf WMf.
           apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold lt_lx, lt_s1, ddrop; ired; [ireg .. |]
                                          | unfold LXO, ddrop; cbn [h9 h10 h12 h14 h18 h22 ir_bits ir_hold ir_have ir_next ir_put irset_bits irset_hold]; repeat split; try reflexivity; ireg].
           close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        -- replace (Z.land (code_op here) 15 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
           zs. itr_groups MUf WMf.
           apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold lt_lx, lt_s1, ddrop; ired; [ireg .. |]
                                          | unfold LXE, lt_lx, lt_s1, ddrop; cbn [w_s h9 h10 h11 h12 h14 h18 h22 ir_bits ir_hold ir_have ir_next ir_put irset_bits irset_hold is_extra iset_mode iset_extra iset_length iset_back]; repeat split; try reflexivity; ireg].
           close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma len_fin : forall X s0 sb c r rt here Bv q ms,
  ILOOPh X (mkW sb c r) PC_LEN_T q ms -> len_QT X here rt Bv r q -> ix_ok X -> PATI X (mkW s0 c r) -> is_flags s0 = 0 ->
  is_window_blk sb = is_window_blk s0 -> is_back sb = Bv -> (forall B, iset_back sb B = iset_back s0 B) ->
  ir_in rt = ir_in r -> ir_out rt = ir_out r -> ir_ret rt = ir_ret r -> ir_put rt = ir_put r -> ir_left rt = ir_left r ->
  0 <= Bv < 256 ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  (forall w2, len_tailnext c here rt sb = Some w2 -> WINV w2 /\ is_mode (w_s w2) = LENEXT) ->
  evt usegs (fun ms' => IPOST X (len_tail c here rt sb) ms' /\ PATI X (wof (len_tail c here rt sb))) ms.
Proof.
  intros X s0 sb c r rt here Bv q ms HL HQ XO HP Pf0 EWB EBV ESBB EI EO ER EP EL RBv RB RH RHV RNX RPUT HWN.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  pose proof (code_bits_range here) as RBITS. pose proof (code_op_range here) as ROP. pose proof (land15_range (code_op here)) as R15.
  eapply evt_cut; [exact (len_tail_walk X sb c r rt here Bv q ms HL HQ XO ltac:(rewrite EWB; exact Pwin) EI EO ER EP EL RBv RB RH RHV RNX RPUT)|].
  intros ms1 H1. unfold len_tail. unfold len_tailnext in HWN. cbv zeta.
  assert (ESB : addback sb (code_bits here) = iset_back s0 (Bv + code_bits here)).
  { unfold addback. rewrite EBV, swrap32_id by lia. apply ESBB. }
  rewrite ESB. rewrite ESB in HWN. unfold lt_lx, lt_s1 in H1. rewrite !ESBB in H1.
  set (Bm := Bv + code_bits here) in *. assert (RBm : 0 <= Bm <= 510) by (subst Bm; lia).
  destruct (code_op here =? 0).
  { destruct H1 as (x26' & x12' & H1). apply evt_done. split; [cbn [IPOST]; exists x26', x12'; exact H1|]. cbn [wof].
    eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LIT, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
    unfold bk_ok, bkmax. cbn -[Z.le Z.add Z.opp]. intros _. lia. }
  destruct (negb (Z.land (code_op here) 32 =? 0)).
  { destruct H1 as (x26' & x12' & H1). apply evt_done. split; [cbn [IPOST]; exists x26', x12'; exact H1|]. cbn [wof].
    eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
    unfold bk_ok, bkmax. cbn -[Z.le Z.add Z.opp]. intros _. lia. }
  destruct (negb (Z.land (code_op here) 64 =? 0)).
  { destruct H1 as (x26' & x12' & H1). apply evt_done. split; [cbn [IPOST]; exists x26', x12'; exact H1|]. cbn [wof].
    eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
    unfold bk_ok, bkmax. cbn -[Z.le Z.add Z.opp]. intros _. lia. }
  cbn [orb] in HWN. destruct (HWN _ eq_refl) as [HW3 HM3].
  assert (HP3 : PATI X (mkW (iset_mode (iset_extra (iset_length (iset_back s0 Bm) (code_val here)) (Z.land (code_op here) 15)) LENEXT) c (ddrop rt (code_bits here)))).
  { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LENEXT, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
    unfold bk_ok, bkmax. cbn -[Z.le Z.add Z.opp]. intros _. lia. }
  destruct (Z.eqb_spec (Z.land (code_op here) 15) 0) as [E0|NE0].
  - destruct H1 as (q' & H1 & HE). exact (lenext_core_off X _ q' ms1 H1 HE XO HW3 HP3 HM3 E0).
  - destruct H1 as (q' & H1 & HE). exact (lenext_core_on X _ q' ms1 H1 HE XO HW3 HP3 HM3 NE0).
Qed.

Lemma len_core : forall X w q ms,
  ILOOPh X w PC_LEN q ms -> DE X (w_r w) q -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LEN ->
  evt usegs (fun ms' => IPOST X (arm_LEN ivar_ref w) ms' /\ PATI X (wof (arm_LEN ivar_ref w))) ms.
Proof.
  intros X [s c r] q ms HL HE XO HW HP HM. cbn [w_s w_r] in HM, HE.
  pose proof (WINV_len_okb _ HW HM) as OKB. unfold len_okb in OKB. cbn [w_s w_c w_r] in OKB.
  pose proof HW as (HCORE & HREGS & HMF & _). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & [TL _]).
  pose proof (cpok_ofs_ok _ _ _ _ TL) as CPO.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HIN1 : arr_len (ic_input c) <= 1) by (rewrite Pin; exact Pin1).
  pose proof (DREGS_of_REGS c r HREGS HIN1) as DR.
  assert (Rin : forall i, 0 <= arr_get (ic_input c) i < 256) by (destruct HREGS as (_&_&_&_&_&_&_&H&_); exact H).
  assert (RPUT : 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X))) by (destruct HREGS as (_&_&_&Rp&Rl&Rpl&_); lia).
  (* the fast entry also needs bits < 8; here have <= 1, so the first test fails *)
  assert (HSLOW : ir_have r < 6 \/ ir_left r < 258 \/ 8 <= ir_bits r) by (left; destruct DR as (_&H&_); lia).
  replace ((6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)) with false in OKB
    by (symmetry; apply andb_false_iff; left; apply andb_false_iff; left; apply Z.leb_gt; destruct DR as (_&H&_); lia).
  apply andb_prop in OKB. destruct OKB as [OKB OKD]. apply andb_prop in OKB. destruct OKB as [OKB _]. apply andb_prop in OKB. destruct OKB as [OKB _].
  apply andb_prop in OKB. destruct OKB as [RN1 RN2]. apply Z.leb_le in RN1, RN2.
  rewrite (arm_LEN_slow s c r HSLOW). cbv zeta.
  set (s0 := iset_back s 0) in *.
  assert (OKD0 : decode_okb len_two s0 c r (is_lencode s0) (is_lenbits s0) = true) by exact OKD.
  change (is_lencode s) with (is_lencode s0). change (is_lenbits s) with (is_lenbits s0).
  assert (HP0 : PATI X (mkW s0 c r)).
  { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| cbn; rewrite HM; unfold LEN, FLAGS, HCRC; lia| reflexivity..| |exact Pisr|].
    - cbn [is_mode s0 iset_back]. rewrite HM. reflexivity.
    - unfold bk_ok. cbn [is_back is_mode s0 iset_back]. pose proof (bkmax_range (is_mode s)). lia. }
  destruct (decode_okb_lvl1 _ _ _ _ _ _ OKD0) as [RN D1].
  pose proof (dlvl_of_dchk c s0 _ _ _ r D1 ltac:(destruct DR as (_&H&_); exact H) ltac:(destruct DR as (_&_&_&H&_); lia)) as DL1.
  change (DECODE1 (is_lencode s0) (is_lenbits s0)) with (DECODE_k 8 (is_lencode s0) (dec_idx1 (is_lenbits s0)) code_bits).
  eapply evt_cut; [exact (len_pre X s c r q ms HL HE XO HREGS HP ltac:(lia))|].
  intros ms0 (q0 & HL0 & HE0 & E11 & E12).
  eapply evt_cut; [exact (len_lvl1 X s0 c r q0 ms0 HL0 HE0 E11 E12 XO HREGS HP0 RN CPO DL1)|].
  intros ms1 [(r1 & q1 & ED1 & EC1 & KB1 & RI1 & HR1 & HJ1 & HQ1)|(r1 & ED1 & HR1 & HLV)].
  2:{ rewrite ED1. apply evt_done. split; [exact HLV|]. cbn [wof].
      destruct (dec_r1_facts c r r1 DR Rin HR1) as (_ & _ & EO1 & _ & EP1 & EL1). eapply PATI_regs; [exact HP0| assumption..]. }
  rewrite ED1.
  destruct (dec_r1_facts c r r1 DR Rin HR1) as (DR1 & EI1 & EO1 & ER1 & EP1 & EL1).
  assert (HN0 : len_next (mkW s c r) =
                if len_two (code_op (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))) then
                  match DECODE_k 8 (is_lencode s0) (dec_idx2 (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1))))
                                 (dec_need2 (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))) (mkW s0 c r1) with
                  | ARun here (mkW _ _ r2) => len_tailnext c here (ddrop r2 (code_bits (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))))
                                                (addback s0 (code_bits (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))))
                  | _ => None
                  end
                else len_tailnext c (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1))) r1 s0).
  { unfold len_next. cbn [w_s w_c w_r]. cbv zeta.
    replace ((6 <=? ir_have r) && (258 <=? ir_left r)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; destruct DR as (_&H&_); lia).
    fold s0. change (is_lencode s) with (is_lencode s0). change (is_lenbits s) with (is_lenbits s0).
    change (DECODE1 (is_lencode s0) (is_lenbits s0)) with (DECODE_k 8 (is_lencode s0) (dec_idx1 (is_lenbits s0)) code_bits).
    rewrite ED1. reflexivity. }
  set (last := code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1))) in *.
  pose proof (code_bits_range last) as RLB. pose proof (code_op_range last) as RLO.
  pose proof (DREGS_hold64 c r1 DR1) as RH1. destruct DR1 as (RNX1 & RHV1 & RNH1 & RB1 & RHB1).
  change (negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0)) with (len_two (code_op last)).
  change (DECODE2 (is_lencode s0) last) with (DECODE_k 8 (is_lencode s0) (dec_idx2 last) (dec_need2 last)).
  assert (HWN : forall sbx herex rtx, len_next (mkW s c r) = len_tailnext c herex rtx sbx ->
                forall w2, len_tailnext c herex rtx sbx = Some w2 -> WINV w2 /\ is_mode (w_s w2) = LENEXT).
  { intros sbx herex rtx E w2 E2. rewrite <- E in E2. exact (len_next_WINV _ _ HW HM E2). }
  destruct (len_two (code_op last)) eqn:TWO.
  -
    destruct (decode_okb_lvl2 _ _ _ _ _ _ r1 OKD0 EC1 KB1 TWO) as [K31 D2]. fold last in K31, D2.
    pose proof (dlvl_of_dchk c s0 _ _ _ r1 D2 RHV1 ltac:(lia)) as DL2.
    eapply evt_cut; [exact (len_lvl2 X s0 c r r1 q1 ms1 HJ1 HQ1 XO HP0 EI1 EO1 EP1 EL1 ER1 RHV1 RNX1 RNH1 RB1 RHB1 Rin RI1 CPO last eq_refl TWO KB1 K31 DL2)|].
    intros ms2 [(r2 & q2 & ED2 & EC2 & KB2 & RI2 & HR2 & HJ2 & HQ2)|(r2 & ED2 & HR2 & HLV)].
    2:{ rewrite ED2. apply evt_done. split; [exact HLV|]. cbn [wof].
        destruct (dec_r1_facts c r1 r2 (conj RNX1 (conj RHV1 (conj RNH1 (conj RB1 RHB1)))) Rin HR2) as (_ & _ & EO2 & _ & EP2 & EL2).
        eapply PATI_regs; [exact HP0| congruence..]. }
    rewrite ED2. rewrite ED2 in HN0.
    destruct (dec_r1_facts c r1 r2 (conj RNX1 (conj RHV1 (conj RNH1 (conj RB1 RHB1)))) Rin HR2) as (DR2 & EI2 & EO2 & ER2 & EP2 & EL2).
    pose proof (DREGS_hold64 c r2 DR2) as RH2. destruct DR2 as (RNX2 & RHV2 & RNH2 & RB2 & RHB2).
    set (e2 := code_at s0 (is_lencode s0) (dec_idx2 last (ir_hold r2))) in *. pose proof (code_bits_range e2) as RHB.
    assert (KB2' : code_bits last + code_bits e2 <= ir_bits r2) by (unfold dec_need2 in KB2; rewrite wrap32_id in KB2 by lia; exact KB2).
    eapply evt_cut; [exact (len_j2 X s0 c r r1 r2 last q2 ms2 HJ2 HQ2 XO HP0 RI2 CPO ltac:(lia) RH2 ltac:(lia) K31 RPUT EP1)|].
    intros ms3 (q3 & HJ3 & HQ3). fold e2 in HQ3.
    destruct (ddrop_facts' r2 (code_bits last) ltac:(lia) ltac:(lia) RH2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    rewrite (addback0 s0 (code_bits last) eq_refl RLB). rewrite (addback0 s0 (code_bits last) eq_refl RLB) in HN0.
    refine (len_fin X s0 (iset_back s0 (code_bits last)) c r (ddrop r2 (code_bits last)) e2 (code_bits last) q3 ms3 HJ3 HQ3 XO HP0 Pf0 eq_refl eq_refl (fun B => eq_refl) _ _ _ _ _ _ _ F7 _ _ RPUT (HWN _ _ _ HN0));
      try congruence; try lia.
  -
    eapply evt_cut; [exact (len_direct X s0 c r r1 q1 ms1 HJ1 HQ1 XO TWO)|].
    intros ms3 (q3 & HJ3 & HQ3). fold last in HQ3.
    refine (len_fin X s0 s0 c r r1 last 0 q3 ms3 HJ3 HQ3 XO HP0 Pf0 eq_refl eq_refl (fun B => eq_refl) EI1 EO1 ER1 EP1 EL1 _ _ RH1 _ _ RPUT (HWN _ _ _ HN0)); lia.
Qed.

Lemma arm_LEN_ok : forall flush, arm_stmt flush LEN PC_LEN (arm_LEN ivar_ref).
Proof.
  intros flush X w x12 ms _ HL XO HW _ HP HM. destruct (ILOOPh_of_ILOOP _ _ _ _ _ _ HL) as (q & HLh & _ & _ & HH).
  exact (len_core X w q ms HLh (DE_of_hhome _ _ _ HH) XO HW HP HM).
Qed.

Lemma len__core : forall X w x26 x12 ms,
  ILOOP X w PC_LEN_ x26 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LEN_ ->
  evt usegs (fun ms' => IPOST X (arm_LEN_ ivar_ref w) ms' /\ PATI X (wof (arm_LEN_ ivar_ref w))) ms.
Proof.
  intros X [s c r] x26 x12 ms HL XO HW HP HM. cbn [w_s] in HM.
  rewrite arm_LEN__eq.
  pose proof (WINV_LEN_ s c r HW HM) as HW2.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HP2 : PATI X (mkW (iset_mode s LEN) c r)).
  { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LEN, FLAGS, HCRC; cbn; lia| reflexivity..| exact Pisr| bk_keep]. }
  eapply (evt_cut usegs (fun ms1 => exists q, ILOOPh X (mkW (iset_mode s LEN) c r) PC_LEN q ms1 /\ DE X r q)).
  2:{ intros ms1 (q & H1 & HE). exact (len_core X _ q ms1 H1 HE XO HW2 HP2 eq_refl). }
  pose proof HW as (_ & HREGS & _). cbn [w_s w_c w_r] in HREGS. destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
  clear HW HW2 HP HP2 Pfl Pgz Pisr POBY PBK.
  iarm_open HL. ix_open XO. unfold PC_LEN_.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  do 2 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |] | unfold DE; cbn [h9 h10 h18 h22 h24 h25]; repeat split; reflexivity].
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Lemma arm_LEN__ok : forall flush, arm_stmt flush LEN_ PC_LEN_ (arm_LEN_ ivar_ref).
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (len__core X w _ x12 ms HL XO HW HP HM). Qed.
End Z_infl_a_len.


Module Z_infl_a_lenlens1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_t_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate Inftrees ItableModel RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 RefInflateSafeOK3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LENLENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rod_order : forall m, mem_inv usegs m -> bytes_at usegs m Z_ORDER (u16s (av16 order_a 19)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_ORDER; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma order_rd : forall m i a, mem_inv usegs m -> 0 <= i < 19 -> a = wa (Z_ORDER + 2 * i) ->
  ov_read_bytes usegs m a 2 = Some (le2 (wz (arr_get order_a i))).
Proof.
  intros m i a MI Hi ->. eapply u16ro_read; [exact (rod_order m MI)| apply av16_nth; exact Hi| lia| reflexivity].
Qed.

Lemma ll_arm_entry : forall X s c r x26 x12 ms,
  ILOOP X (mkW s c r) PC_LENLENS x26 x12 ms -> 0 <= is_have s <= 19 ->
  evt usegs (fun ms' => exists q, ILOOPh X (mkW s c r) PC_LENLENS_E q ms' /\ h17 q = wz (is_have s) /\ h14 q = wz (il_NI (ix_L X) + ir_next r)
                                  /\ h12 q = wz (ir_have r) /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h11 q = wz (ix_flush X) /\ h13 q = wz (il_S (ix_L X))
                                  /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)) ms.
Proof.
  intros X s c r x26 x12 ms HL RH.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM).
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
  unfold PC_LENLENS. do 4 zs.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; try reflexivity; exact HMEM|]. hred. repeat split; reflexivity.
Qed.

Definition PC_LL1_H : Z := 0x1f6c4.
Definition PC_LL1_B : Z := 0x1f6fc.
Definition PC_LL2 : Z := 0x1f764.

Definition ll1_Q (X : ictx) (s : inflate_state) (r : iregs) (q : iscrh) : Prop :=
  h10 q = wz Z_ORDER /\ h11 q = wz (is_ncode s) /\ h13 q = wz 18446744073709551597 /\ h15 q = wz (is_have s + 1) /\ h16 q = wz (18446744073709551616 - is_ncode s)
  /\ h17 q = wz (2 * is_have s) /\ h14 q = wz (il_NI (ix_L X) + ir_next r) /\ h12 q = wz (ir_have r)
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r).

Lemma zext32_x2 : forall x, 0 <= x < 4294967296 -> Z.land (x ≪ 32) 18446744073709551615 ≫ 31 = 2 * x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296. change (2^64) with 18446744073709551616. change (2^31) with 2147483648. Z.div_mod_to_equations. lia.
Qed.

Lemma ll_entry : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LENLENS_E q ms ->
  h17 q = wz (is_have s) -> h14 q = wz (il_NI (ix_L X) + ir_next r) -> h12 q = wz (ir_have r) ->
  h9 q = wz (il_NO (ix_L X) + ir_put r) -> h18 q = wz (ir_bits r) -> h22 q = wz (ir_hold r) ->
  0 <= is_have s < is_ncode s -> is_ncode s <= 19 ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW s c r) PC_LL1_H q' ms' /\ ll1_Q X s r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL E17 E14 E12 E9 E18 E22 RH RN.
  destruct HL as (m & -> & HMEM). hred_in E17. hred_in E14. hred_in E12. hred_in E9. hred_in E18. hred_in E22. subst x17 x14 x12 x9 x18 x22.
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
  unfold PC_LENLENS_E.
  do 4 zs. br_false. do 3 zs. br_false. do 6 zs.
  rewrite unsigned_lit by lia. rewrite zext32_x2 by lia.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; try reflexivity; exact HMEM|].
  unfold ll1_Q. hred. unfold Z_ORDER. repeat split; ireg.
Qed.

Definition PC_LL1_DRY : Z := 0x21334.

Lemma ll1_head : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL1_H q ms -> ll1_Q X s r q -> ix_ok X -> DREGS c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) -> PATI X (mkW s c r) ->
  evt usegs (NBJq X s c r 3 PC_LL1_B (fun r1 q1 => ll1_Q X s r1 q1)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO DR Rin HP.
  unfold ll1_Q in HQ. hred_in HQ. destruct HQ as (E10 & E11 & E13 & E15 & E16 & E17 & E14 & E12 & E9 & E18 & E22). subst x10 x11 x13 x15 x16 x17 x14 x12 x9 x18 x22.
  destruct HL as (m & -> & HMEM). hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct DR as (Rn & [Rh HAV] & Rnh & RB & RH).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  unfold PC_LL1_H. ix_open XO.
  do 2 zs. br_cases K.
  -
    apply evt_done. left. eexists r, _. split; [|split; [|split]].
    + apply nb_enough. lia.
    + left. split; [reflexivity| lia].
    + eapply ILOOPh_intro; try reflexivity. exact HMEM.
    + unfold ll1_Q. hred. repeat split; reflexivity.
  - zs. br_cases K2.
    +
      assert (H1 : ir_have r = 1) by lia.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. zs. zs. br_cases KG; [| exfalso; lia].
      zs. zs. zs. clear RD. zs. zs. zs. rewrite <- Pin. rewrite !pull_shift by lia. rewrite lor8_small by lia.
      apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
      * apply nb_pull_ok; lia.
      * right. split; [reflexivity| lia].
      * unfold hide in RH. eapply ILOOPh_intro; try reflexivity. exact HMEM.
      * unfold ll1_Q. hred. pullr_rw c r. repeat split; ireg.
    +
      do 7 zs.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Ltac st16 ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok usegs _ A (av16 a n) idx (wa (A + 2 * idx)) ARR ltac:(rewrite av16_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av16_write m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      unfold u16arr in ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "L16" in pose proof (av16_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNA" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Lemma swrap32_negadd : forall k x c, c = 18446744073709551616 - k -> - 2^31 <= x - k < 2^31 -> bv_swrap 32 (c + x) = x - k.
Proof. intros k x c -> H. rewrite Z.add_comm. apply swrap32_sub; [reflexivity| exact H]. Qed.
Lemma swrap32_negadd' : forall k x, - 2^31 <= x - k < 2^31 -> 0 <= k < 2^32 -> bv_swrap 32 (- k + x) = x - k.
Proof.
  intros k x H Hk. apply (bv_swrap32_eqm (- k + x) (x - k + 0)) || idtac.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^31) with 2147483648 in H. Z.div_mod_to_equations. lia.
Qed.

Lemma land64_np : forall x, - 4294967296 <= x <= 0 -> Z.land x 18446744073709551615 = 1 -> False.
Proof.
  intros x Hx K. destruct (Z.eq_dec x 0) as [E|NE]; [rewrite E in K; discriminate K|].
  rewrite land_ones64_neg in K by lia. lia.
Qed.

Definition LL2Q (X : ictx) (s : inflate_state) (r : iregs) (q : iscrh) : Prop :=
  h17 q = wz (is_have s) /\ h14 q = wz (il_NI (ix_L X) + ir_next r) /\ h12 q = wz (ir_have r) /\ h10 q = wz Z_ORDER
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r).

Local Ltac close_ll j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| unfold ilens, u16arr; inorm; rewrite ?EV; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma ll1_body : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL1_B q ms -> ll1_Q X s r q -> ix_ok X -> PATI X (mkW s c r) ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < is_ncode s -> is_ncode s <= 19 ->
  3 <= ir_bits r <= 63 -> 0 <= ir_hold r < 2^64 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q',
     if is_ncode s - is_have s - 1 =? 0
     then ILOOPh X (mkW (ll_s s (ir_hold r)) c (ll_r r)) PC_LL2 q' ms' /\ LL2Q X (ll_s s (ir_hold r)) (ll_r r) q'
     else ILOOPh X (mkW (ll_s s (ir_hold r)) c (ll_r r)) PC_LL1_H q' ms' /\ ll1_Q X (ll_s s (ir_hold r)) (ll_r r) q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP LL RHV RNC RB RH RPUT.
  unfold ll1_Q in HQ. hred_in HQ. destruct HQ as (E10 & E11 & E13 & E15 & E16 & E17 & E14 & E12 & E9 & E18 & E22).
  iarm_openh HL. subst x10 x11 x13 x15 x16 x17 x14 x12 x9 x18 x22.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL1_B, Z_ORDER.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  pose proof (order_lt19 (is_have s) ltac:(lia)) as ROR. set (od := arr_get order_a (is_have s)) in *.
  assert (EV : wrap16 (BITSv (ir_hold r) 3) = Z.land (ir_hold r) 7) by (rewrite wrap16_bits3 by lia; rewrite land7_mod; reflexivity).
  pose proof (land7_range (ir_hold r)) as R7. set (v := Z.land (ir_hold r) 7) in *.
  zs. rewrite (swrap32_negadd 19) by lia. zs. zs. itr_groups MUf WMf. clear MUf WMf.
  zstep. if_cases K; br_norm K; [clear K | exfalso; eapply land64_np; [|exact K]; lia].
  zs. change (Z.lxor 75100 18446744073709551615) with 18446744073709476515. gT.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  lazymatch goal with MI' : mem_inv usegs ?m1 |- _ =>
    pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m1) as MUf;
    pose proof (wmono_refl usegs m1) as WMf;
    pose proof (order_rd m1 (is_have s) (wa (Z_ORDER + 2 * is_have s)) MI' ltac:(lia) eq_refl) as RD end.
  fold od in RD. unfold Z_ORDER in RD. zs. zs. rewrite (zx16_small od) by lia. clear RD.
  zs. replace (od ≪ 1) with (2 * od) by (rewrite Z.shiftl_mul_pow2 by lia; lia). zs.
  zstep. rewrite (zb_lxor_ones (il_As (ix_L X) + 168)) by lia. br_true.
  do 6 zs.
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) od v ltac:(reflexivity).
  zs. rewrite (swrap32_negadd (is_ncode s)) by lia. zs. zs.
  destruct (Z.eqb_spec (is_ncode s - is_have s - 1) 0) as [E0|NE0].
  -
    replace (is_have s + 2 - is_ncode s) with 1 by lia. zstep. br_false. zs. itr_groups MUf WMf.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold ll_s, ll_r; ired; try reflexivity|].
    + close_ll j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV.
    + unfold LL2Q, ll_s, ll_r. hred. ired. rewrite (wrap32_id (is_have s + 1)) by lia. repeat split; ireg.
  - zstep. if_cases K; br_norm K; [clear K | exfalso; eapply land64_np; [|exact K]; lia]. itr_groups MUf WMf.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold ll_s, ll_r; ired; try reflexivity|].
    + close_ll j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV.
    + unfold ll1_Q, ll_s, ll_r. hred. ired. rewrite (wrap32_id (is_have s + 1)) by lia. unfold Z_ORDER. repeat split; ireg.
Qed.

Definition LL1POST (X : ictx) (res : ares unit) : machine_state -> Prop :=
  match res with
  | ARun _ w1 => fun ms' => (exists q, ILOOPh X w1 PC_LL2 q ms' /\ LL2Q X (w_s w1) (w_r w1) q)
                            /\ PATI X w1 /\ 0 <= is_have (w_s w1) <= 19 /\ is_mode (w_s w1) = LENLENS
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATI X w'
  | ARet _ _ => fun _ => False
  end.

Lemma ll1_loop : forall k X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL1_H q ms -> ll1_Q X s r q -> ix_ok X -> DREGS c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  PATI X (mkW s c r) -> is_mode s = LENLENS ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < is_ncode s -> is_ncode s <= 19 -> is_ncode s - is_have s <= Z.of_nat k ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (LL1POST X (lenlens_while1 k (mkW s c r))) ms.
Proof.
  induction k as [|k IH]; intros X s c r q ms HL HQ XO DR Rin HP HM LL RHV RNC RK RPUT; [cbn [Z.of_nat] in RK; lia|].
  rewrite lenlens_while1_S. replace (is_have s <? is_ncode s) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  eapply evt_cut; [exact (ll1_head X s c r q ms HL HQ XO DR Rin HP)|].
  intros ms1 [(r1 & q1 & EN & HR1 & HJ & HQ1)|(r1 & EN & HR1 & HLV)].
  2:{ rewrite EN. cbn [LL1POST]. apply evt_done. split; [exact HLV|].
      destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
  rewrite EN.
  destruct (DREGS_nb c r r1 3 DR Rin ltac:(lia) HR1) as (DR1 & RB3 & EI & EO & ER & EP & EL).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  pose proof (DREGS_hold64 c r1 DR1) as RH1. pose proof DR1 as (_ & _ & _ & RB1 & _).
  assert (HP2 : PATI X (mkW (ll_s s (ir_hold r1)) c (ll_r r1))).
  { eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0| unfold ll_s; cbn [is_mode iset_have iset_lens]; rewrite HM; unfold LENLENS, FLAGS, HCRC; lia
                      | reflexivity..| |exact Pisr| bk_keep].
    unfold ll_s, ll_r. cbn [is_mode iset_have iset_lens ir_put irset_bits irset_hold]. rewrite HM. reflexivity. }
  eapply evt_cut; [exact (ll1_body X s c r1 q1 ms1 (ILOOPh_regs X s c r r1 _ q1 ms1 HJ EI EO ER EP EL) HQ1 XO HP1 LL RHV RNC ltac:(lia) RH1 ltac:(lia))|].
  intros ms2 (q2 & H2).
  assert (EH' : is_have (ll_s s (ir_hold r1)) = is_have s + 1) by (unfold ll_s; cbn [is_have iset_have]; apply wrap32_id; lia).
  assert (EN' : is_ncode (ll_s s (ir_hold r1)) = is_ncode s) by reflexivity.
  destruct (Z.eqb_spec (is_ncode s - is_have s - 1) 0) as [E0|NE0].
  -
    destruct H2 as (H2 & HQ2).
    rewrite lenlens_while1_stop by (rewrite EH', EN'; lia). cbn [LL1POST w_s w_r].
    apply evt_done. split; [exists q2; split; [exact H2| exact HQ2]|].
    split; [exact HP2|]. split; [rewrite EH'; lia| unfold ll_s; cbn [is_mode iset_have iset_lens]; exact HM].
  - destruct H2 as (H2 & HQ2).
    refine (IH X _ c _ q2 ms2 H2 HQ2 XO (DREGS_drop c r1 3 DR1 ltac:(lia)) Rin HP2 _ _ _ _ _ _).
    + unfold ll_s; cbn [is_mode iset_have iset_lens]; exact HM.
    + unfold ll_s. cbn [is_lens iset_have iset_lens]. rewrite arr_len_set. exact LL.
    + rewrite EH', EN'. lia.
    + rewrite EN'. exact RNC.
    + rewrite EH', EN'. lia.
    + unfold ll_r. cbn [ir_put irset_bits irset_hold]. lia.
Qed.
End Z_infl_a_lenlens1.


Module Z_infl_a_lenlens.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_t_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_lenlens1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate Inftrees ItableModel RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 RefInflateSafeOK3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LENLENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.

Definition PC_LL2_B : Z := 0x1f780.
Definition PC_LL2_X : Z := 0x1f7c0.
Definition PC_LL_CALL : Z := 0x1f7c8.
Definition PC_LL_RET : Z := 0x1f7fc.

Definition HC (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h24 q = wz (ir_have r) /\ h25 q = wz (il_NI (ix_L X) + ir_next r).
Definition L2B (X : ictx) (r : iregs) (i : Z) (q : iscrh) : Prop :=
  h10 q = wz Z_ORDER /\ h11 q = wz (2 * i) /\ h12 q = wz (Z_ORDER + 2 * i) /\ HC X r q.

Lemma ll2_pre : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL2 q ms -> LL2Q X s r q -> 0 <= is_have s <= 19 ->
  evt usegs (fun ms' => exists q',
     if is_have s <? 19 then ILOOPh X (mkW s c r) PC_LL2_B q' ms' /\ L2B X r (is_have s) q'
     else ILOOPh X (mkW s c r) PC_LL_CALL q' ms' /\ HC X r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ RH.
  unfold LL2Q in HQ. hred_in HQ. destruct HQ as (E17 & E14 & E12 & E10 & E9 & E18 & E22).
  destruct HL as (m & -> & HMEM). hred. subst x17 x14 x12 x10 x9 x18 x22.
  unfold PC_LL2, Z_ORDER.
  do 4 zs. br_cases K.
  - replace (is_have s <? 19) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; try reflexivity; exact HMEM|]. unfold HC. hred. repeat split; reflexivity.
  - replace (is_have s <? 19) with true by (symmetry; apply Z.ltb_lt; lia).
    do 3 zs.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; try reflexivity; exact HMEM|].
    unfold L2B, HC. hred. unfold Z_ORDER. repeat split; ireg.
Qed.

Local Ltac close_k j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [exact GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma ll2_body : forall X s c r i q ms,
  ILOOPh X (mkW s c r) PC_LL2_B q ms -> L2B X r i q ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i < 19 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q',
     if i + 1 =? 19
     then ILOOPh X (mkW (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r) PC_LL2_X q' ms' /\ HC X r q'
     else ILOOPh X (mkW (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r) PC_LL2_B q' ms' /\ L2B X r (i + 1) q') ms.
Proof.
  intros X s c r i [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP LL Ri RPUT.
  unfold L2B, HC in HQ. hred_in HQ. destruct HQ as (E10 & E11 & E12 & E9 & E18 & E22 & E24 & E25).
  iarm_openh HL. subst x10 x11 x12 x9 x18 x22 x24 x25.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL2_B, Z_ORDER.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST.
  pose proof (munch_refl [(il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  pose proof (order_lt19 i ltac:(lia)) as ROR. set (od := arr_get order_a i) in *.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  pose proof (order_rd m i (wa (Z_ORDER + 2 * i)) MI ltac:(lia) eq_refl) as RD. fold od in RD. unfold Z_ORDER in RD.
  zs. change (Z.lxor 75100 18446744073709551615) with 18446744073709476515. gT.
  zs. rewrite (zx16_small od) by lia. clear RD.
  zs. replace (od ≪ 1) with (2 * od) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zs. zstep. rewrite (zb_lxor_ones (il_As (ix_L X) + 168)) by lia. br_true.
  do 4 zs.
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) od 0 ltac:(reflexivity).
  do 2 zs. itr_groups MUf WMf.
  destruct (Z.eqb_spec (i + 1) 19) as [E|NE].
  - replace (2 * i + 2) with 38 by lia. zstep. br_false.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; try reflexivity| unfold HC; hred; repeat split; reflexivity].
    close_k j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  - zstep. br_true.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; try reflexivity|].
    + close_k j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + unfold L2B, HC. hred. unfold Z_ORDER. repeat split; ireg.
Qed.

Lemma zlens_19 : forall n a, zlens n a 19 = a.
Proof. intros [|n] a; reflexivity. Qed.

Lemma ll2_loop : forall n X s c r i q ms,
  ILOOPh X (mkW s c r) PC_LL2_B q ms -> L2B X r i q ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i < 19 -> 19 - i <= Z.of_nat n ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (iset_lens s (zlens n (is_lens s) i)) c r) PC_LL2_X q' ms' /\ HC X r q') ms.
Proof.
  induction n as [|n IH]; intros X s c r i q ms HL HQ XO HP LL Ri Rn RPUT; [cbn [Z.of_nat] in Rn; lia|].
  cbn [zlens]. replace (i <? 19) with true by (symmetry; apply Z.ltb_lt; lia).
  eapply evt_cut; [exact (ll2_body X s c r i q ms HL HQ XO HP LL Ri RPUT)|].
  intros ms1 (q1 & H1).
  destruct (Z.eqb_spec (i + 1) 19) as [E|NE].
  - rewrite E, zlens_19. apply evt_done. exists q1. exact H1.
  - destruct H1 as (H1 & HQ1).
    refine (IH X (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r (i + 1) q1 ms1 H1 HQ1 XO _ _ _ _ RPUT).
    + exact HP.
    + cbn [is_lens iset_lens]. rewrite arr_len_set. exact LL.
    + lia.
    + rewrite Nat2Z.inj_succ in Rn. lia.
Qed.

Local Ltac close_kA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma ll2_exit : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL2_X q ms -> HC X r q -> ix_ok X -> PATI X (mkW s c r) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (iset_have s 19) c r) PC_LL_CALL q' ms' /\ HC X r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP RPUT.
  unfold HC in HQ. hred_in HQ. destruct HQ as (E9 & E18 & E22 & E24 & E25).
  iarm_openh HL. subst x9 x18 x22 x24 x25.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL2_X.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  zs. zs. itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; try reflexivity| unfold HC; hred; repeat split; reflexivity].
  close_kA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma ll2_walk : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LL2 q ms -> LL2Q X s r q ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= is_have s <= 19 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (ll2 19 s) c r) PC_LL_CALL q' ms' /\ HC X r q') ms.
Proof.
  intros X s c r q ms HL HQ XO HP LL RH RPUT.
  eapply evt_cut; [exact (ll2_pre X s c r q ms HL HQ RH)|]. intros ms1 (q1 & H1).
  destruct (Z.ltb_spec (is_have s) 19) as [LT|GE].
  - destruct H1 as (H1 & HQ1).
    rewrite (ll2_zlens 19 s) by (cbn; lia).
    eapply evt_cut; [exact (ll2_loop 19 X s c r (is_have s) q1 ms1 H1 HQ1 XO HP LL ltac:(lia) ltac:(cbn; lia) RPUT)|].
    intros ms2 (q2 & H2 & HQ2).
    exact (ll2_exit X _ c r q2 ms2 H2 HQ2 XO HP RPUT).
  - rewrite ll2_stop by lia. apply evt_done. exists q1. exact H1.
Qed.

Definition ILOOPc (X : ictx) (w : iw) (pc : Z) (x1 : word) (q : iscrh) : machine_state -> Prop :=
  fun ms => exists m,
    ms = MS (mkR x1 (wz (bv_unsigned (ix_sp X) + -256)) (ix_gp X) (ix_tp X) (h5 q) (h6 q) (h7 q) (wz (il_As (ix_L X))) (h9 q) (h10 q) (h11 q) (h12 q) (h13 q) (h14 q) (h15 q) (h16 q) (h17 q) (wz (il_S (ix_L X))) (h18 q) (h19 q) (h20 q) (h21 q) (h24 q) (h23 q) (h22 q) (h25 q) (h26 q) (h28 q) (h29 q) (h30 q) (h31 q))
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom usegs)
    /\ IMEM X w m.

Lemma ILOOPc_intro : forall X w pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (ix_sp X) + -256) -> x3 = ix_gp X -> x4 = ix_tp X ->
  x8 = wz (il_S (ix_L X)) -> x27 = wz (il_As (ix_L X)) -> F = ix_F X -> fc = ix_fc X ->
  IMEM X w m ->
  ILOOPc X w pc x1 (mkSH x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31)
         (MS (mkR x1 x2 x3 x4 x5 x6 x7 x27 x9 x10 x11 x12 x13 x14 x15 x16 x17 x8 x18 x19 x20 x21 x24 x23 x22 x25 x26 x28 x29 x30 x31)
             F (wz pc) fc None m (seg_rom usegs)).
Proof. intros. subst. unfold ILOOPc. eexists. split; [reflexivity| assumption]. Qed.

Local Ltac close_A j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; unfold iframe_cells; inorm; close_cells FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Definition HCC (X : ictx) (r : iregs) (q : iscrh) : Prop := HC X r q /\ h10 q = wz (-2).

Lemma ll_after : forall X s3 c r x1 q ms ret,
  ILOOPc X (mkW s3 c r) PC_LL_RET x1 q ms -> h10 q = wz (ret mod 2 ^ 64) -> HC X r q -> (ret = 0 \/ ret = 1 \/ ret = -1) -> ix_ok X ->
  (is_window_blk s3 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) <= 1 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' =>
    if negb (ret =? 0)
    then exists x26 x12, ILOOP X (mkW (iset_mode s3 BAD) (icset_msg c MSG_invalid_code_lengths_set) (irset_ret r ret)) PC_DISPATCH x26 x12 ms'
    else exists q', ILOOPh X (mkW (iset_mode (iset_have s3 0) CODELENS) c (irset_ret r ret)) PC_CODELENS_E q' ms' /\ HCC X r q') ms.
Proof.
  intros X s3 c r x1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms ret HL E10 HQ RRET XO Pwin Pin Pin1 Pout RPUT.
  unfold HC in HQ. hred_in HQ. hred_in E10. destruct HQ as (E9 & E18 & E22 & E24 & E25).
  destruct HL as (m & -> & (j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU. hred. cbn [w_s w_c w_r] in *.
  subst x10 x9 x18 x22 x24 x25.
  ix_open XO. unfold PC_LL_RET.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  assert (RM : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  zs. br_cases K.
  -
    assert (R0 : ret = 0) by (destruct RRET as [R|[R|R]]; rewrite R in K; [exact R| |]; exfalso; revert K; vm_compute; discriminate).
    clear RRET K RM. subst ret. cbn [Z.eqb negb].
    do 6 zs. itr_groups MUf WMf.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; try reflexivity| unfold HCC, HC; hred; repeat split; reflexivity].
    close_A j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  -
    assert (R1 : (ret =? 0) = false) by (apply Z.eqb_neq; intros R; rewrite R in K; apply K; reflexivity). rewrite R1. cbn [negb].
    clear RRET K.
    do 4 zs. do 7 zs. itr_groups MUf WMf.
    apply evt_done. do 2 eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_A j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Section LLcall.
Variable flush : Z.
Hypothesis CODELENS_CORE : codelens_core_stmt flush.
Hypothesis ITABLE : inflate_table_stmt.

Lemma ll_call : forall X s c r q ms ret tbl nxt lb wk,
  ILOOPh X (mkW s c r) PC_LL_CALL q ms -> HC X r q -> ix_ok X -> PATI X (mkW s c r) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) = (ret, tbl, nxt, lb, wk) ->
  it_safe CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) = true ->
  ATY s -> (forall i, 0 <= i < 19 -> arr_get (is_lens s) i <= 15) ->
  evt usegs (fun ms' =>
    if negb (ret =? 0)
    then exists x26 x12, ILOOP X (mkW (iset_mode (ll_tab s tbl nxt lb wk) BAD) (icset_msg c MSG_invalid_code_lengths_set) (irset_ret r ret)) PC_DISPATCH x26 x12 ms'
    else exists q', ILOOPh X (mkW (ll_s2 (ll_tab s tbl nxt lb wk)) c (irset_ret r ret)) PC_CODELENS_E q' ms' /\ HCC X r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms ret tbl nxt lb wk HL HQ XO HP RPUT EIT SAFE HA HL15.
  unfold HC in HQ. hred_in HQ. destruct HQ as (E9 & E18 & E22 & E24 & E25).
  iarm_openh HL. subst x9 x18 x22 x24 x25.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL_CALL.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  do 13 zs. itr_groups MUf WMf. clear MUf WMf.
  (* CODELENS also sets distcode = codes *)
  set (spre := iset_distcode (iset_lencode (iset_next (iset_lenbits s 7) 0) (CDyn 0)) (CDyn 0)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
  assert (ST' : IST m1 (ix_L X) spre);
  [ subst spre; constructor; inorm;
    [ unfold isA, isA_cells; inorm; unfold cp_addr; close_cells GA | exact GT | exact Gl | exact Gw | exact Gc | exact Gwin
    | unfold iarrs in *; inorm; exact ARRS | exact LAY ]
  | clear GA GT Gl Gw Gc Gwin ] end.
  pose proof (inflate_table_ret _ _ _ _ _ _ _ _ _ _ _ _ _ EIT) as RRET.
  eapply evt_cut.
  { eapply (ITABLE (ix_L X) spre CODES false 0 19 (ix_lo X));
      [ exact ST' | eassumption | rewrite unsigned_lit by lia; exact STK | rewrite unsigned_lit by lia; unfold Z_ITABLE_STACK; lia | lia
      | intros NE; subst spre; cbn in NE; pose proof (xo_win _ XO (Pwin NE)); lia
      | lia | lia | lia | subst spre; cbn; lia | subst spre; cbn; lia
      | subst spre; cbn [it_bits_get is_lens is_codes is_next is_work is_lenbits iset_distcode iset_lencode iset_next iset_lenbits]; exact SAFE
      | exact HA
      | subst spre; cbn [is_lens iset_distcode iset_lencode iset_next iset_lenbits]; intros i Hi; rewrite Z.add_0_l; exact (HL15 i Hi)
      | cbn [it_codes_ok]; first [exact I | lia]
      | reflexivity | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STKc & EA0 & STc).
  rewrite unsigned_lit in MUc, STKc by lia.
  assert (ER : it_result CODES false 0 19 spre = (ret, ll_tab s tbl nxt lb wk)).
  { unfold it_result. subst spre. cbn [it_bits_get it_bits_set is_lens is_codes is_next is_work is_lenbits iset_distcode iset_lencode iset_next iset_lenbits].
    rewrite EIT.
    unfold ll_tab, it_bits_set. cbv [iset_work iset_lenbits iset_next iset_lencode iset_codes
      is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk
      is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next
      is_lens is_work is_codes is_sane is_back is_was is_self_blk]. reflexivity. }
  rewrite ER in EA0, STc. cbn [fst snd] in EA0, STc. subst a0'. clear ER ST' spre.
  lazymatch type of WMc with wmono _ ?ma _ => itr_groups MUc WMc; transport_after_call usegs ma m' MUc WMc end. clear MUc WMc MI ARRS LAY.
  replace (ret_pc (wz 129020)) with (wz 129020) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  unfold ll_s2.
  eapply (ll_after X (ll_tab s tbl nxt lb wk) c r _ _ _ ret); [ | | | exact RRET | exact XO | exact Pwin | exact Pin | exact Pin1 | exact Pout | exact RPUT].
  { eapply ILOOPc_intro; ired; [ireg .. |].
    apply IMEM_intro; [ exists j0, jf; exact FRM | exact STKc | exact ZS | exact STc | exact IN | exact OUT | exact MIc | exact MU | exact WM ]. }
  { hred. reflexivity. }
  { unfold HC. hred. repeat split; reflexivity. }
Qed.

Lemma lenlens_core : lenlens_core_stmt flush.
Proof.
  intros X [s c r] q ms EF HL E17 E14 E12 E9 E11 E13 E18 E22 XO HW HA HP HM. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & Rin & _).
  assert (LL : arr_len (is_lens s) = 320) by (destruct HCORE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  assert (HIN1 : arr_len (ic_input c) <= 1) by (rewrite Pin; exact Pin1).
  pose proof (DREGS_of_REGS c r HREGS HIN1) as DR.
  rewrite arm_LENLENS_eq.
  eapply evt_cut; [exact (ll_entry X s c r q ms HL E17 E14 E12 E9 E18 E22 Hh (proj2 Hnc))|]. intros ms1 (q1 & H1 & HQ1).
  eapply evt_cut; [exact (ll1_loop 19 X s c r q1 ms1 H1 HQ1 XO DR Rin HP HM LL Hh (proj2 Hnc) ltac:(cbn; lia) ltac:(lia))|]. intros ms2 H2.
  pose proof (lenlens_facts s c r HW HA HM) as [_ F].
  pose proof (WINV_lenlens_okb s c r HW HA HM) as OKB. unfold lenlens_okb in OKB. cbn [w_s] in OKB.
  pose proof (lenlens_next_WINV s c r HW HA HM) as NXW. unfold lenlens_next in NXW.
  destruct (lenlens_while1 19 (mkW s c r)) as [[] [s1 c1 r1] | w' | rc w']; cbn [LL1POST w_s w_r] in H2.
  2:{ apply evt_done. cbn [IPOST wof]. exact H2. }
  2:{ destruct H2. }
  destruct H2 as ((q2 & HL2 & HQ2) & HP1 & Hh1 & HM1).
  destruct F as (-> & lens19 & EL2 & HL19 & HLs19 & HT19 & HC1 & HR1 & HCm1 & Hb1 & Hnl1 & Hnd1 & HWF1 & HWB1 & HA1).
  apply andb_prop in OKB. destruct OKB as [_ OKB]. apply ll_call_ok_sound in OKB. destruct OKB as (CL15 & SAFE & _).
  assert (LL1 : arr_len (is_lens s1) = 320) by (destruct HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  pose proof HR1 as (Rn1 & Rh1 & Rnh1 & Rp1 & Rl1 & Rpl1 & _).
  pose proof HP1 as (_ & _ & _ & _ & _ & Pwin1 & Pin' & _ & Pout' & _ & Pisr1 & _). cbn [w_s w_c w_r] in *.
  assert (RPUT1 : 0 <= ir_put r1 <= Z.of_nat (length (ix_rest0 X))) by (rewrite <- Pout; lia).
  eapply evt_cut; [exact (ll2_walk X s1 c r1 q2 ms2 HL2 HQ2 XO HP1 LL1 Hh1 RPUT1)|]. intros ms3 (q3 & H3 & HQ3).
  unfold ll_fin. rewrite EL2 in H3, CL15, SAFE, NXW |- *. cbv zeta in NXW.
  cbn [is_lens is_codes is_work iset_have iset_lens] in CL15, SAFE, NXW |- *.
  destruct (inflate_table CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)) as [[[[ret tbl] nxt] lb] wk] eqn:EIT. cbv zeta.
  assert (Pf1 : is_flags s1 = 0).
  { destruct HP1 as (_ & _ & _ & Pfl1 & _). cbn [w_s w_r] in Pfl1. destruct Pfl1 as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM1 in E; discriminate E. }
  assert (HPA : PATI X (mkW (iset_have (iset_lens s1 lens19) 19) c r1)).
  { eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_have iset_lens]; rewrite HM1; unfold LENLENS, FLAGS, HCRC; lia| reflexivity..| |exact Pisr1| bk_keep].
    cbn [is_mode iset_have iset_lens]. rewrite HM1. reflexivity. }
  assert (HAA : ATY (iset_have (iset_lens s1 lens19) 19)).
  { unfold ATY. cbn [is_lens is_work is_codes iset_have iset_lens]. split; [exact HT19| destruct HA1 as [_ H]; exact H]. }
  eapply evt_cut.
  { eapply (ll_call X (iset_have (iset_lens s1 lens19) 19) c r1 q3 ms3 ret tbl nxt lb wk H3 HQ3 XO HPA RPUT1);
      cbn [is_lens is_codes is_work iset_have iset_lens]; [exact EIT | exact SAFE | exact HAA | exact CL15]. }
  intros ms4 H4.
  destruct (Z.eqb_spec ret 0) as [R0|R1]; cbn [negb] in H4 |- *.
  -
    destruct H4 as (q4 & HL4 & (E9' & E18' & E22' & E24' & E25') & E10').
    specialize (NXW _ eq_refl). destruct NXW as (HW2 & HA2 & HM2).
    refine (CODELENS_CORE X _ q4 ms4 EF HL4 _ _ _ _ _ _ XO HW2 HA2 _ HM2); cbn [w_s w_c w_r]; ired; try assumption.
    unfold ll_s2, ll_tab. eapply PATI_step; [exact HPA| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode iset_have]; unfold CODELENS, FLAGS, HCRC; lia| reflexivity..| exact Pisr1| bk_keep].
  -
    destruct H4 as (x26' & x12' & HL4).
    apply evt_done. split; [cbn [IPOST]; exists x26', x12'; exact HL4|]. cbn [wof].
    unfold ll_tab. eapply PATI_step; [exact HPA| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| reflexivity..| exact Pisr1| bk_keep].
Qed.

Lemma arm_LENLENS_of : arm_stmt flush LENLENS PC_LENLENS (arm_LENLENS ivar_ref flush).
Proof.
  intros X [s c r] x12 ms EF HL XO HW HA HP HM.
  pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF. rewrite HM in HMF. unfold MF in HMF. cbn in HMF.
  destruct HMF as (_ & _ & Hnc & _ & _ & Hh & _).
  eapply evt_cut; [exact (ll_arm_entry X s c r _ x12 ms HL ltac:(lia))|]. intros ms1 (q1 & H1 & E17 & E14 & E12 & E9 & E11 & E13 & E18 & E22).
  exact (lenlens_core X (mkW s c r) q1 ms1 EF H1 E17 E14 E12 E9 E11 E13 E18 E22 XO HW HA HP HM).
Qed.
End LLcall.
End Z_infl_a_lenlens.


Module Z_infl_a_codelens1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_t_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_lenlens1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_lenlens.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate Inftrees ItableModel InffastMem RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 RefInflateSafeOK3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LENLENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.

Definition PC_CL_B : Z := 0x1f858.
Definition PC_CL_J : Z := 0x1f940.
Definition PC_CL_X : Z := 0x1fbf0.

Definition CLK (X : ictx) (s : inflate_state) (q : iscrh) : Prop :=
  h11 q = wz (is_nlen s + is_ndist s) /\ h12 q = wz (is_nlen s) /\ h13 q = wz (is_lenbits s)
  /\ h14 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ h15 q = wz (Z.ones (is_lenbits s)).

Definition CLB (X : ictx) (s : inflate_state) (r : iregs) (hv : Z) (q : iscrh) : Prop :=
  CLK X s q /\ h16 q = wz hv /\ h17 q = wz (il_NI (ix_L X) + ir_next r) /\ h31 q = wz (ir_have r) /\ HCC X r q.

Definition CLX (X : ictx) (s : inflate_state) (r : iregs) (q : iscrh) : Prop := h12 q = wz (is_nlen s) /\ HCC X r q.

Lemma cl_entry : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CODELENS_E q ms -> HCC X r q ->
  0 <= is_have s <= 320 -> 257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 -> 0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  evt usegs (fun ms' => exists q',
     if is_have s <? is_nlen s + is_ndist s
     then ILOOPh X (mkW s c r) PC_CL_B q' ms' /\ CLB X s r (is_have s) q'
     else ILOOPh X (mkW s c r) PC_CL_X q' ms' /\ CLX X s r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ Rh Rnl Rnd Rlb CPO.
  unfold HCC, HC in HQ. hred_in HQ. destruct HQ as ((E9 & E18 & E22 & E24 & E25) & E10).
  destruct HL as (m & -> & HMEM). hred. subst x9 x18 x22 x24 x25 x10.
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
  unfold PC_CODELENS_E.
  do 4 zs. zstep. br_cases K.
  - replace (is_have s <? is_nlen s + is_ndist s) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold CLX, HCC, HC. hred. repeat split; ireg.
  - replace (is_have s <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
    rd_sub GA 120%nat 0%nat 4%nat. do 7 zs. rewrite clang_mask32 by lia.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold CLB, CLK, HCC, HC. hred. repeat split; ireg.
Qed.

Definition cl_QJ (X : ictx) (s : inflate_state) (r r1 : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  h23 q = wz (code_w e) /\ h30 q = wz (code_bits e) /\ h29 q = wz (code_w e ≫ 8)
  /\ h7 q = wz (ir_bits r1) /\ h5 q = wz (ir_bits r1) /\ h19 q = wz (- ir_bits r1) /\ h22 q = wz (ir_hold r1)
  /\ h6 q = wz (ir_have r1) /\ h24 q = wz (ir_have r1) /\ h25 q = wz (il_NI (ix_L X) + ir_next r1) /\ h28 q = wz (il_NI (ix_L X) + ir_next r1)
  /\ h16 q = wz (is_have s) /\ CLK X s q /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h18 q = wz (ir_bits r).

Lemma cl_dec : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CL_B q ms -> CLB X s r (is_have s) q ->
  ix_ok X -> DREGS c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) -> PATI X (mkW s c r) ->
  0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  dlvl c s (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits r ->
  evt usegs (DECJ X s c r r (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits PC_CL_J (cl_QJ X s r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO DR Rin HP RN CPO DL.
  unfold CLB, CLK, HCC, HC in HQ. hred_in HQ.
  destruct HQ as ((E11 & E12 & E13 & E14 & E15) & E16 & E17 & E31 & (E9 & E18 & E22 & E24 & E25) & E10).
  destruct HL as (m & -> & HMEM). hred. subst x11 x12 x13 x14 x15 x16 x17 x31 x9 x18 x22 x24 x25 x10.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  destruct DR as (Rn & Rh & Rnh & RB & RH).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST.
  unfold PC_CL_B. ix_open XO.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *.
  pose proof (dec_idx1_land n (ir_hold r) ltac:(lia) RN) as EI0. pose proof (dec_idx1_range n (ir_hold r) ltac:(lia) RN) as RI0'.
  pose proof (dl_i0 _ _ _ _ _ _ DL) as RI0. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN0. pose proof (ones_range15 n RN) as RMK.
  zs. gT. zs. rewrite EI0.
  set (i0 := dec_idx1 n (ir_hold r)) in *. set (e0 := code_at s p i0) in *.
  pose proof (code_bits_range e0) as RB0. pose proof (cp_addr_rng (ix_L X) p i0 CPO RI0 ltac:(lia)) as CPR.
  zs. rewrite (Z.shiftl_mul_pow2 i0 2) by lia. change (2^2) with 4. zs. gT.
  do 3 zs. rewrite xor_guard by lia. gT.
  replace (0 <? cp_addr (ix_L X) p) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  do 9 zs. rewrite ?land_u32_small by lia.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2 + 2)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e0); lia). clear RD.
  pose proof (code_rd_lo m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e0); lia). clear RD.
  do 2 zs. rewrite code_w_or_step. pose proof (code_w_range e0) as RW0. do 2 zs. rewrite code_w_bits.
  zstep. br_cases K.
  -
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i0; fold e0; lia)) as [ED EC].
    apply evt_done. left. eexists r, _. split; [exact ED|]. split; [exact EC|]. split; [fold i0; fold e0; lia|]. split; [exact RI0|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold cl_QJ, CLK. hred. fold p. fold n. fold i0. fold e0. repeat split; try reflexivity; ireg.
  - assert (K' : ir_bits r < code_bits (code_at s p (dec_idx1 n (ir_hold r)))) by (fold i0; fold e0; exact K).
    zstep. br_cases K2.
    +
      assert (H1 : ir_have r = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI1 RN1].
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      do 2 zs. gT. zs. gT.
      pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      assert (EH1 : arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r + ir_hold r = ir_hold (pullr c r)).
      { unfold hide in RH. rewrite pullr_hold by (first [assumption | lia]). lia. }
      pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
      assert (RH1 : 0 <= ir_hold (pullr c r) < 2^64).
      { rewrite <- EH1. split; [lia|]. eapply Z.lt_le_trans; [rewrite Z.add_comm; exact (proj2 PR)|]. apply Z.pow_le_mono_r; lia. }
      rewrite EH1. clear PR EH1.
      pose proof (dec_idx1_land n (ir_hold (pullr c r)) ltac:(lia) RN) as EI1. pose proof (dec_idx1_range n (ir_hold (pullr c r)) ltac:(lia) RN) as RI1'.
      set (h1 := ir_hold (pullr c r)) in *.
      zs. rewrite EI1. set (i1 := dec_idx1 n h1) in *. set (e1 := code_at s p i1) in *. pose proof (code_bits_range e1) as RB1.
      pose proof (cp_addr_rng (ix_L X) p i1 CPO RI1 ltac:(lia)) as CPR1.
      zs. rewrite (Z.shiftl_mul_pow2 i1 2) by lia. change (2^2) with 4. zs. gT.
      do 6 zs. rewrite xor_guard1 by lia. do 2 zs. zstep. br_true.
      do 2 zs.
      pose proof (code_rd_val m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 2)) MI Gc CPO RI1 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e1 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e1); lia). clear RD.
      pose proof (code_rd_lo m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2)) MI Gc CPO RI1 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e1 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e1); lia). clear RD.
      do 2 zs. rewrite code_w_or_step. pose proof (code_w_range e1) as RW1. do 2 zs. rewrite code_w_bits.
      zstep. br_cases K3.
      * assert (K3' : code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r)))) <= ir_bits (pullr c r)) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        apply evt_done. left. eexists (pullr c r), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI1|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold cl_QJ, CLK. hred. fold p. fold n. fold h1. fold i1. fold e1.
        repeat split; try reflexivity; try (pullr_rw c r; ireg).
      *
        assert (K3' : ir_bits (pullr c r) < code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r))))) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zstep. br_false. do 9 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e1 i1 h1. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| reflexivity..]]; pullr_rw c r; ireg.
    +
      assert (H0 : ir_have r = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 9 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Lemma code_w_sh20 : forall v, code_w v ≫ 20 = code_val v ≫ 4.
Proof.
  intros v. unfold code_w. pose proof (code_lo_range v) as RL. pose proof (code_val_range v) as RV.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 20) with (65536 * 16). change (2 ^ 4) with 16.
  rewrite <- Z.div_div by lia. rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite (Z.div_small (code_lo v)) by lia.
  rewrite Z.add_0_r. reflexivity.
Qed.
Lemma code_w_sl48 : forall v, Z.land (code_w v ≪ 48) 18446744073709551615 ≫ 56 = code_bits v.
Proof.
  intros v. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  unfold code_w, code_lo. pose proof (code_op_range v) as RO. pose proof (code_bits_range v) as RB. pose proof (code_val_range v) as RV.
  replace ((code_op v + 256 * code_bits v + 65536 * code_val v) * 2 ^ 48) with ((code_op v + 256 * code_bits v) * 2 ^ 48 + code_val v * 2 ^ 64)
    by (change (2 ^ 64) with (65536 * 2 ^ 48); lia).
  rewrite Z.mod_add by lia. rewrite Z.mod_small by (change (2 ^ 64) with (65536 * 2 ^ 48); lia).
  change (2 ^ 56) with (2 ^ 48 * 2 ^ 8). rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. change (2 ^ 8) with 256.
  rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Local Ltac close_lit j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV EP :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; unfold iframe_cells; inorm; close_cells FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_litw : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_CL_J q ms -> cl_QJ X s r r1 q -> ix_ok X -> PATI X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2^64 ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) -> 0 <= is_lenbits s <= 15 ->
  code_val (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) < 16 ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < is_nlen s + is_ndist s -> 257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_have r1 -> 0 <= ir_next r1 ->
  let here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  let s' := cl_lit s (code_val here) in let r' := ddrop r1 (code_bits here) in
  evt usegs (fun ms' => exists q',
     if is_have s + 1 <? is_nlen s + is_ndist s
     then ILOOPh X (mkW s' c r') PC_CL_B q' ms' /\ CLB X s' r' (is_have s + 1) q'
     else ILOOPh X (mkW s' c r') PC_CL_X q' ms' /\ CLX X s' r' q') ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP EI EO ER EP EL RB RH RI CPO RN RV LL Rh Rnl Rnd RPUT Rh1 Rn1.
  unfold cl_QJ, CLK in HQ. hred_in HQ.
  destruct HQ as (E23 & E30 & E29 & E7 & E5 & E19 & E22 & E6 & E24 & E25 & E28 & E16 & (E11 & E12 & E13 & E14 & E15) & E9 & E10 & E18).
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *. set (i1 := dec_idx1 n (ir_hold r1)) in *. set (e1 := code_at s p i1) in *.
  pose proof (code_bits_range e1) as RB1. pose proof (code_val_range e1) as RV1. pose proof (code_w_range e1) as RW1.
  cbv zeta.
  zs. rewrite code_w_sh20. rewrite (Z.shiftr_div_pow2 (code_val e1) 4) by lia. change (2 ^ 4) with 16. rewrite (Z.div_small (code_val e1) 16) by lia.
  zs. rewrite code_w_val.
  zstep. br_false.
  zs. gT.
  zs. zs. zs. itr_groups MUf WMf. clear MUf WMf.
  gT.
  zs. replace (is_have s ≪ 1) with (2 * is_have s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zs. zstep. rewrite (zb_lxor_ones (il_As (ix_L X) + 168)) by lia. br_true.
  zs. rewrite code_w_g63 by lia.
  zs. zs. rewrite subw_land64 by lia. replace (0 - - ir_bits r1) with (ir_bits r1) by lia.
  zs. zs. zs. rewrite code_w_sl48. zs.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  lazymatch goal with MI' : mem_inv usegs ?m1 |- _ =>
    pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m1) as MUf;
    pose proof (wmono_refl usegs m1) as WMf end.
  assert (EV : wrap16 (code_val e1) = code_val e1) by (apply wrap16_id; lia).
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) (is_have s) (wrap16 (code_val e1)) ltac:(rewrite EV; reflexivity).
  do 3 zs. itr_groups MUf WMf.
  zstep. br_cases K.
  - replace (is_have s + 1 <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold cl_lit, ddrop; ired; [ireg .. |]|].
    + close_lit j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV EP.
    + unfold CLB, CLK, HCC, HC, cl_lit, ddrop. hred. ired. fold p n. repeat split; ireg.
  - zs. replace (is_have s + 1 <? is_nlen s + is_ndist s) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold cl_lit, ddrop; ired; [ireg .. |]|].
    + close_lit j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV EP.
    + unfold CLX, HCC, HC, cl_lit, ddrop. hred. ired. repeat split; ireg.
Qed.

Definition cl_pcx (val : Z) : Z := if val =? 16 then 0x1fb08 else if val =? 17 then 0x1fad4 else 0x1fb6c.

Definition cl_QN (X : ictx) (s : inflate_state) (r r1 r2 : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  h5 q = wz (ir_bits r2) /\ h7 q = wz (ir_bits r2) /\ h17 q = wz (il_NI (ix_L X) + ir_next r2) /\ h28 q = wz (il_NI (ix_L X) + ir_next r2)
  /\ h22 q = wz (ir_hold r2) /\ h24 q = wz (ir_have r2)
  /\ h30 q = wz (code_bits e) /\ h29 q = wz (code_w e ≫ 8) /\ h23 q = wz (code_w e)
  /\ h16 q = wz (is_have s) /\ CLK X s q /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2).

Definition NBJc (X : ictx) (s : inflate_state) (c : icall) (r r1 : iregs) (n pcx : Z) : machine_state -> Prop :=
  fun ms' =>
    (exists r2 q', NEEDBITS n (mkW s c r1) = ARun tt (mkW s c r2)
                   /\ ((r2 = r1 /\ n <= ir_bits r1) \/ (r2 = pullr c r1 /\ 0 < ir_have r1 /\ ir_bits r1 < n <= ir_bits r1 + 8))
                   /\ ILOOPh X (mkW s c r) pcx q' ms' /\ cl_QN X s r r1 r2 q')
    \/ (exists r2, NEEDBITS n (mkW s c r1) = ALeave (mkW s c r2) /\ (r2 = r1 \/ r2 = pullr c r1) /\ ILEAVE X (mkW s c r2) ms').

Local Ltac nb_site_tac X c r1 Pin IN HMEM RH EI EO EP ER :=
  let K := fresh "K" in let K2 := fresh "K" in let K3 := fresh "K" in
  zs; zstep; br_cases K;
  [
    do 2 zs; apply evt_done; left; eexists r1, _; split; [apply nb_enough; lia|]; split; [left; split; [reflexivity| lia]|];
    split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|];
    unfold cl_QN, CLK; hred; repeat split; ireg
  | zs; zstep; br_cases K2;
    [
      let H1 := fresh "H1" in let NXT := fresh "NXT" in let RD := fresh "RD" in
      assert (H1 : ir_have r1 = 1) by lia;
      assert (NXT : 0 <= ir_next r1 < arr_len (ix_input X)) by (rewrite <- Pin; lia);
      do 2 zs; gT; zs; gT;
      pose proof (u8ro_read usegs _ _ _ (ir_next r1) _ (wa (il_NI (ix_L X) + ir_next r1)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD;
      zs; clear RD; do 7 zs; rewrite <- Pin; rewrite !pull_shift by lia; zstep; br_cases K3;
      [
        zstep; br_false; do 7 zs; rewrite H1; change (Z.land 1 4294967295) with 1;
        apply evt_done; right; exists (pullr c r1); split; [apply nb_pull_dry; lia|]; split; [right; reflexivity|];
        unfold hide in RH; eapply ILEAVE_intro; pullr_rw c r1; ired; [ireg .. |]; eapply IMEML_of_IMEM; [exact HMEM| rewrite ?pullr_in, ?pullr_out, ?pullr_put, ?pullr_left; assumption ..]
      | zs; apply evt_done; left; eexists (pullr c r1), _; split; [apply nb_pull_ok; lia|]; split; [right; split; [reflexivity| lia]|];
        split; [unfold hide in RH; eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|];
        unfold hide in RH; unfold cl_QN, CLK; hred; pullr_rw c r1;
        rewrite H1; change (Z.land 1 4294967295) with 1; repeat split; ireg ]
    |
      let H0 := fresh "H0" in assert (H0 : ir_have r1 = 0) by lia;
      do 7 zs; rewrite H0; apply evt_done; right; exists r1; split; [apply nb_dry; lia|]; split; [left; reflexivity|];
      eapply ILEAVE_intro; ired; [ireg .. |]; eapply IMEML_of_IMEM; [exact HMEM| assumption ..] ] ].

Lemma cl_need : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_CL_J q ms -> cl_QJ X s r r1 q -> ix_ok X -> DREGS c r1 -> (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  PATI X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= ir_bits r1 ->
  code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) <= 32 ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) -> 0 <= is_lenbits s <= 15 ->
  16 <= code_val (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) ->
  let here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  evt usegs (NBJc X s c r r1 (code_bits here + cl_nb (code_val here)) (cl_pcx (code_val here))) ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO DR Rin HP EI EO ER EP EL RB RB32 RI CPO RN RV.
  unfold cl_QJ, CLK in HQ. hred_in HQ.
  destruct HQ as (E23 & E30 & E29 & E7 & E5 & E19 & E22 & E6 & E24 & E25 & E28 & E16 & (E11 & E12 & E13 & E14 & E15) & E9 & E10 & E18).
  destruct HL as (m & -> & HMEM). hred. subst.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  destruct DR as (Rn & Rh & Rnh & RB1 & RH).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r1)) as RBy.
  assert (RH64 : 0 <= ir_hold r1 < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. ix_open XO. unfold PC_CL_J.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *. set (i1 := dec_idx1 n (ir_hold r1)) in *. set (e1 := code_at s p i1) in *.
  pose proof (code_bits_range e1) as RBe. pose proof (code_val_range e1) as RVe. pose proof (code_w_range e1) as RWe.
  cbv zeta.
  zs. rewrite code_w_sh20.
  assert (V4 : 0 < code_val e1 ≫ 4) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 4) with 16; Z.div_mod_to_equations; lia).
  pose proof (shiftr_le (code_val e1) 4 ltac:(lia) ltac:(lia)) as V4'.
  zs. rewrite code_w_val.
  zstep. br_true.
  zs. zs. rewrite subw_land64 by lia. replace (0 - - ir_bits r1) with (ir_bits r1) by lia.
  zstep. br_cases K16.
  { unfold cl_nb, cl_pcx. replace (code_val e1 =? 16) with true by (symmetry; apply Z.eqb_eq; lia).
    nb_site_tac X c r1 Pin IN HMEM RH EI EO EP ER. }
  zs. zstep. br_cases K17.
  { unfold cl_nb, cl_pcx. replace (code_val e1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (code_val e1 =? 17) with false by (symmetry; apply Z.eqb_neq; lia).
    nb_site_tac X c r1 Pin IN HMEM RH EI EO EP ER. }
  unfold cl_nb, cl_pcx. replace (code_val e1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (code_val e1 =? 17) with true by (symmetry; apply Z.eqb_eq; lia).
  nb_site_tac X c r1 Pin IN HMEM RH EI EO EP ER.
Qed.

Definition PC_CL_R : Z := 0x1fbb0.
Definition PC_CL_RX : Z := 0x1fbe0.

Definition CLR (X : ictx) (s : inflate_state) (r : iregs) (i cnt v : Z) (q : iscrh) : Prop :=
  h16 q = wz i /\ h5 q = wz cnt /\ h6 q = wz v /\ h7 q = wz 320 /\ h17 q = wz (il_NI (ix_L X) + ir_next r)
  /\ CLK X s q /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2)
  /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r) /\ h24 q = wz (ir_have r).

Local Ltac close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; unfold iframe_cells; inorm; close_cells FRM | exact STK
  | first [exact ZS | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS]
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; rewrite ?EP; exact OUT | eassumption | exact MU | exact WM ].

Local Ltac bad_stub MUf WMf := do 6 zs; itr_groups MUf WMf.

Lemma cl_rep_hd : forall X s c r r1 r2 q ms,
  let here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) in
  let val := code_val here in let nb := cl_nb val in
  let r3 := ddrop r2 (code_bits here) in
  let len := (if val =? 16 then arr_get (is_lens s) (is_have s - 1) else 0) in
  let copy := cl_base val + BITSv (ir_hold r3) nb in
  let r4 := ddrop r3 nb in
  ILOOPh X (mkW s c r) (cl_pcx val) q ms -> cl_QN X s r r1 r2 q -> ix_ok X -> PATI X (mkW s c r) ->
  ir_in r2 = ir_in r -> ir_out r2 = ir_out r -> ir_ret r2 = ir_ret r -> ir_put r2 = ir_put r -> ir_left r2 = ir_left r ->
  code_bits here + nb <= ir_bits r2 <= 63 -> 0 <= ir_hold r2 < 2^64 -> 0 <= ir_have r2 -> 16 <= val ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s <= is_nlen s + is_ndist s -> is_nlen s + is_ndist s <= 320 ->
  (forall i, 0 <= i < is_have s -> 0 <= arr_get (is_lens s) i <= 15) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_next r2 ->
  evt usegs (fun ms' =>
    if (val =? 16) && (is_have s =? 0) then exists x26 x12, ILOOP X (cl_bad s c r3) PC_DISPATCH x26 x12 ms'
    else if is_nlen s + is_ndist s <? is_have s + copy then exists x26 x12, ILOOP X (cl_bad s c r4) PC_DISPATCH x26 x12 ms'
    else exists q', ILOOPh X (mkW s c r4) PC_CL_R q' ms' /\ CLR X s r4 (is_have s) copy len q') ms.
Proof.
  intros X s c r r1 r2 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms.
  intros here val nb r3 len copy r4 HL HQ XO HP EI EO ER EP EL RB RH RHV RV LL Rh Rnd HLs RPUT Rn2.
  unfold cl_QN, CLK in HQ. hred_in HQ.
  destruct HQ as (E5 & E7 & E17 & E28 & E22 & E24 & E30 & E29 & E23 & E16 & (E11 & E12 & E13 & E14 & E15) & E9 & E10).
  iarm_openh HL. subst x5 x7 x17 x28 x22 x24 x30 x29 x23 x16 x11 x12 x13 x14 x15 x9 x10.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  fold here. set (cb := code_bits here) in *. pose proof (code_bits_range here) as RCB. fold cb in RCB. pose proof (code_w_range here) as RW.
  assert (Rnb : 2 <= nb <= 7) by (subst nb; unfold cl_nb; destruct (val =? 16); [lia|]; destruct (val =? 17); lia).
  pose proof (shiftr_le (ir_hold r2) cb ltac:(lia) ltac:(lia)) as RH3.
  assert (EH3 : ir_hold r3 = ir_hold r2 ≫ cb) by reflexivity.
  pose proof (BITSv_land (ir_hold r3) nb ltac:(rewrite EH3; lia) ltac:(lia)) as EBV. pose proof (land_ones_rng (ir_hold r3) nb ltac:(lia)) as RBV. rewrite <- EBV in RBV.
  assert (Rcp : 3 <= copy <= 138).
  { subst copy. assert (P7 : 2 ^ nb <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). change (2 ^ 7) with 128 in P7.
    unfold cl_base. destruct (val =? 16); [lia|]. destruct (val =? 17); lia. }
  unfold cl_pcx.
  destruct (Z.eqb_spec val 16) as [V16|NV16].
  -
    assert (Enb : nb = 2) by (subst nb; unfold cl_nb; rewrite V16; reflexivity).
    assert (Ecp : copy = 3 + Z.land (ir_hold r3) 3) by (subst copy; rewrite EBV, Enb; unfold cl_base; rewrite V16; reflexivity).
    zs. gT. zs. rewrite code_w_g63 by lia. fold cb. zs. zstep. br_cases K0.
    + replace (is_have s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      pose proof (HLs (is_have s - 1) ltac:(lia)) as RLEN.
      zs. gT. zs. zs. replace ((is_have s + -1) ≪ 1) with (2 * (is_have s - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      zs. zstep. rewrite (zb_lxor_ones (il_As (ix_L X) + 168)) by lia. br_true. zs. zs.
      pose proof Gl as Gl'. unfold ilens, u16arr in Gl'. ld16 Gl' (is_lens s) 320 (il_As (ix_L X) + 168) (is_have s - 1) ltac:(lia). clear Gl'.
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 2 ltac:(lia)) as R3. change (Z.ones 2) with 3 in R3. change (2 ^ 2) with 4 in R3.
      rewrite EH3 in Ecp.
      do 5 zs. zs. rewrite ?addw_land64 by lia. zstep. br_cases K1.
      *
        replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        do 2 zs. zstep. br_false. zs.
        apply evt_done. eexists. split; [eapply ILOOPh_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP. }
        unfold CLR, CLK. subst r4 r3. unfold ddrop. hred. ired. rewrite ?Enb. repeat split; ireg.
      *
        replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. bad_stub MUf WMf.
        apply evt_done. eexists _, _. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
    +
      replace (is_have s =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb].
      zs. do 2 zs. bad_stub MUf WMf.
      apply evt_done. eexists _, _. unfold cl_bad. subst r3. unfold ddrop. eapply ILOOP_intro; ired; [ireg .. |].
      close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
  - cbn [andb].
    destruct (Z.eqb_spec val 17) as [V17|NV17].
    + assert (Enb : nb = 3) by (subst nb; unfold cl_nb; rewrite V17; reflexivity).
      assert (Ecp : copy = 3 + Z.land (ir_hold r3) 7) by (subst copy; rewrite EBV, Enb; unfold cl_base; rewrite V17; reflexivity).
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 3 ltac:(lia)) as R3. change (Z.ones 3) with 7 in R3. change (2 ^ 3) with 8 in R3.
      rewrite EH3 in Ecp.
      zs. gT. zs. zs. rewrite code_w_g63 by lia. fold cb. do 6 zs.
      zs. rewrite ?addw_land64 by lia. zstep. br_cases K1.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        do 2 zs. zstep. br_false. zs.
        apply evt_done. eexists. split; [eapply ILOOPh_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP. }
        unfold CLR, CLK. subst r4 r3. unfold ddrop. hred. ired. rewrite ?Enb. repeat split; ireg.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. bad_stub MUf WMf.
        apply evt_done. eexists _, _. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
    + assert (Enb : nb = 7).
      { subst nb; unfold cl_nb. replace (val =? 16) with false by (symmetry; apply Z.eqb_neq; exact NV16).
        replace (val =? 17) with false by (symmetry; apply Z.eqb_neq; exact NV17). reflexivity. }
      assert (Ecp : copy = 11 + Z.land (ir_hold r3) 127).
      { subst copy; rewrite EBV, Enb; unfold cl_base. replace (val =? 16) with false by (symmetry; apply Z.eqb_neq; exact NV16).
        replace (val =? 17) with false by (symmetry; apply Z.eqb_neq; exact NV17). reflexivity. }
      pose proof (land_ones_rng (ir_hold r2 ≫ cb) 7 ltac:(lia)) as R3. change (Z.ones 7) with 127 in R3. change (2 ^ 7) with 128 in R3.
      rewrite EH3 in Ecp.
      zs. gT. zs. zs. rewrite code_w_g63 by lia. fold cb. do 5 zs.
      zs. rewrite ?addw_land64 by lia. zstep. br_cases K1.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with false by (symmetry; apply Z.ltb_ge; lia).
        do 2 zs. zstep. br_false. zs.
        apply evt_done. eexists. split; [eapply ILOOPh_intro; subst r4 r3; unfold ddrop; ired; rewrite ?Enb; [ireg .. |]|].
        { close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP. }
        unfold CLR, CLK. subst r4 r3. unfold ddrop. hred. ired. rewrite ?Enb. repeat split; ireg.
      * replace (is_nlen s + is_ndist s <? is_have s + copy) with true by (symmetry; apply Z.ltb_lt; lia).
        do 4 zs. bad_stub MUf WMf.
        apply evt_done. eexists _, _. unfold cl_bad. subst r4 r3. unfold ddrop. eapply ILOOP_intro; ired; rewrite ?Enb; [ireg .. |].
        close_keep j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EP.
Qed.
End Z_infl_a_codelens1.


Module Z_infl_a_codelens2.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_infl_c_tab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_t_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_lenlens1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_lenlens OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_codelens1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate Inftrees ItableModel InffastMem RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 RefInflateSafeOK3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LENLENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.

Local Ltac close_l j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [exact GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_rep_body : forall X s c r i cnt v q ms,
  ILOOPh X (mkW s c r) PC_CL_R q ms -> CLR X s r i cnt v q ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i -> 1 <= cnt -> i + cnt <= 320 -> 0 <= v < 16 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q',
     (if cnt - 1 =? 0 then ILOOPh X (mkW (iset_lens s (arr_set (is_lens s) i v)) c r) PC_CL_RX q' ms'
      else ILOOPh X (mkW (iset_lens s (arr_set (is_lens s) i v)) c r) PC_CL_R q' ms')
     /\ CLR X (iset_lens s (arr_set (is_lens s) i v)) r (i + 1) (cnt - 1) v q') ms.
Proof.
  intros X s c r i cnt v [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP LL Ri Rc Ric Rv RPUT.
  unfold CLR, CLK in HQ. hred_in HQ.
  destruct HQ as (E16 & E5 & E6 & E7 & E17 & (E11 & E12 & E13 & E14 & E15) & E9 & E10 & E18 & E22 & E24).
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_R.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST.
  pose proof (munch_refl [(il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  zstep. br_true.
  zs. replace (i ≪ 1) with (2 * i) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zs. zstep. rewrite (zb_lxor_ones (il_As (ix_L X) + 168)) by lia. br_true.
  zs. zs. zs.
  assert (EV : wrap16 v = v) by (apply wrap16_id; lia).
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) i v ltac:(reflexivity).
  zs. itr_groups MUf WMf. zstep. br_cases K.
  - replace (cnt - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]|].
    + close_l j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + unfold CLR, CLK. hred. ired. repeat split; ireg.
  - replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]|].
    + close_l j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + unfold CLR, CLK. hred. ired. repeat split; ireg.
Qed.

Lemma fill_S' : forall n a i v, fill (S n) a i v = fill n (arr_set a i v) (i + 1) v.
Proof. intros. reflexivity. Qed.

Lemma cl_rep_loop : forall n X s c r i cnt v q ms,
  ILOOPh X (mkW s c r) PC_CL_R q ms -> CLR X s r i cnt v q ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i -> cnt = Z.of_nat n -> (0 < n)%nat -> i + cnt <= 320 -> 0 <= v < 16 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (iset_lens s (fill n (is_lens s) i v)) c r) PC_CL_RX q' ms'
     /\ CLR X (iset_lens s (fill n (is_lens s) i v)) r (i + cnt) 0 v q') ms.
Proof.
  induction n as [|n IH]; intros X s c r i cnt v q ms HL HQ XO HP LL Ri Ec Hn Ric Rv RPUT; [lia|].
  rewrite fill_S'.
  eapply evt_cut; [exact (cl_rep_body X s c r i cnt v q ms HL HQ XO HP LL Ri ltac:(lia) Ric Rv RPUT)|].
  intros ms1 (q1 & H1 & HQ1).
  destruct (Z.eqb_spec (cnt - 1) 0) as [E|NE].
  - assert (n = 0)%nat as -> by lia. cbn [fill]. apply evt_done. exists q1. replace (i + cnt) with (i + 1) by lia. replace 0 with (cnt - 1) by lia.
    split; assumption.
  - replace (i + cnt) with (i + 1 + (cnt - 1)) by lia.
    refine (IH X (iset_lens s (arr_set (is_lens s) i v)) c r (i + 1) (cnt - 1) v q1 ms1 H1 HQ1 XO _ _ _ _ _ _ Rv RPUT).
    + exact HP.
    + cbn [is_lens iset_lens]. rewrite arr_len_set. exact LL.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Local Ltac close_gA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_rep_tl : forall X s c r t v q ms,
  ILOOPh X (mkW s c r) PC_CL_RX q ms -> CLR X s r t 0 v q -> ix_ok X -> PATI X (mkW s c r) ->
  0 <= t <= 320 -> 257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' => exists q',
     if t <? is_nlen s + is_ndist s
     then ILOOPh X (mkW (iset_have s t) c r) PC_CL_B q' ms' /\ CLB X (iset_have s t) r t q'
     else ILOOPh X (mkW (iset_have s t) c r) PC_CL_X q' ms' /\ CLX X (iset_have s t) r q') ms.
Proof.
  intros X s c r t v [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP Rt Rnl Rnd RPUT.
  unfold CLR, CLK in HQ. hred_in HQ.
  destruct HQ as (E16 & E5 & E6 & E7 & E17 & (E11 & E12 & E13 & E14 & E15) & E9 & E10 & E18 & E22 & E24).
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_RX.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  zs. itr_groups MUf WMf. do 2 zs.
  zstep. br_cases K.
  - replace (t <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]| unfold CLB, CLK, HCC, HC; hred; ired; repeat split; ireg].
    close_gA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  - replace (t <? is_nlen s + is_ndist s) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]| unfold CLX, HCC, HC; hred; ired; repeat split; ireg].
    close_gA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Definition CLBPOST (X : ictx) (res : ares bool) : machine_state -> Prop :=
  match res with
  | ARun true w1 => fun ms' =>
      (exists q, if is_have (w_s w1) <? is_nlen (w_s w1) + is_ndist (w_s w1)
                 then ILOOPh X w1 PC_CL_B q ms' /\ CLB X (w_s w1) (w_r w1) (is_have (w_s w1)) q
                 else ILOOPh X w1 PC_CL_X q ms' /\ CLX X (w_s w1) (w_r w1) q)
      /\ PATI X w1
  | ARun false w1 => fun ms' => (exists x26 x12, ILOOP X w1 PC_DISPATCH x26 x12 ms') /\ PATI X w1
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATI X w'
  | ARet _ _ => fun _ => False
  end.

Lemma cl_rep_run : forall X s c r copy len q ms,
  ILOOPh X (mkW s c r) PC_CL_R q ms -> CLR X s r (is_have s) copy len q -> ix_ok X -> PATI X (mkW s c r) ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s -> 3 <= copy -> is_have s + copy <= 320 -> 0 <= len < 16 ->
  is_mode s = CODELENS -> is_flags s = 0 -> ISR s -> 257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (CLBPOST X (ARun true (mkW (cl_rep s copy len) c r))) ms.
Proof.
  intros X s c r copy len q ms HL HQ XO HP LL Rh Rc Rhc Rlen HM Pf0 Pisr Rnl Rnd RPUT. cbn [CLBPOST w_s w_r].
  rewrite (cl_rep_fill s copy len) by lia. rewrite (wrap16_id len) by lia.
  eapply evt_cut.
  { exact (cl_rep_loop (Z.to_nat copy) X s c r (is_have s) copy len q ms HL HQ XO HP LL Rh ltac:(lia) ltac:(lia) Rhc Rlen RPUT). }
  intros ms1 (q1 & H1 & HQ1).
  eapply evt_cut.
  { exact (cl_rep_tl X _ c r (is_have s + copy) len q1 ms1 H1 HQ1 XO HP ltac:(lia) Rnl Rnd RPUT). }
  intros ms2 (q2 & H2). apply evt_done. split.
  - exists q2. cbn [is_have is_nlen is_ndist iset_have iset_lens] in *. exact H2.
  - eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0
      | cbn [is_mode iset_have iset_lens]; rewrite HM; unfold CODELENS, FLAGS, HCRC; lia| reflexivity ..| | exact Pisr| bk_keep].
    cbn [is_mode iset_have iset_lens]. rewrite HM. reflexivity.
Qed.

Lemma cl_r2_facts : forall c r r1 n, DREGS c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) -> n <= 48 ->
  ((r1 = r /\ n <= ir_bits r) \/ (r1 = pullr c r /\ 0 < ir_have r /\ ir_bits r < n <= ir_bits r + 8)) ->
  DREGS c r1 /\ n <= ir_bits r1 /\ ir_in r1 = ir_in r /\ ir_out r1 = ir_out r /\ ir_ret r1 = ir_ret r /\ ir_put r1 = ir_put r /\ ir_left r1 = ir_left r.
Proof.
  intros c r r1 n DR Rin Hn [[-> H]|(-> & H1 & H2)]; [split; [exact DR| repeat split; try reflexivity; lia]|].
  pose proof DR as (Rn & Rh & Rnh & RB & RH). assert (A1 : ir_have r = 1) by lia.
  pose proof (Rin (ir_next r)) as RBy.
  pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r)) (ir_bits r) (ir_hold r) RBy ltac:(lia) RH) as PR.
  unfold DREGS. pullr_rw c r. repeat split; try reflexivity; lia.
Qed.

Lemma cl_body : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CL_B q ms -> CLB X s r (is_have s) q ->
  ix_ok X -> CL s c r -> PATI X (mkW s c r) -> is_have s < is_nlen s + is_ndist s ->
  decode_okb cl_two s c r (is_lencode s) (is_lenbits s) = true ->
  evt usegs (CLBPOST X (codelens_body (mkW s c r))) ms.
Proof.
  intros X s c r q ms HL HQ XO HCL HP LT OKD.
  pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E'|E'] & _)]; [exact Pf| |]; rewrite E in E'; discriminate E').
  clear Pfl.
  pose proof HR as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & Rin & _).
  assert (HIN1 : arr_len (ic_input c) <= 1) by (rewrite Pin; exact Pin1).
  pose proof (DREGS_of_REGS c r HR HIN1) as DR.
  assert (LL : arr_len (is_lens s) = 320) by (destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  pose proof (cpok_ofs_ok _ _ _ _ HT) as CPO.
  assert (RPUT : 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X))) by (rewrite <- Pout; lia).
  destruct (decode_okb_lvl1 _ _ _ _ _ _ OKD) as [RN D1].
  pose proof (dlvl_of_dchk c s _ _ _ r D1 ltac:(destruct DR as (_&H&_); exact H) ltac:(destruct DR as (_&_&_&H&_); lia)) as DL.
  rewrite codelens_body_eq. change (DECODE1 (is_lencode s) (is_lenbits s)) with (DECODE_k 8 (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits).
  eapply evt_cut; [exact (cl_dec X s c r q ms HL HQ XO DR Rin HP RN CPO DL)|].
  intros ms1 [(r1 & q1 & ED & EC & KB & RI & HR1 & HJ & HQJ)|(r1 & ED & HR1 & HLV)].
  2:{ rewrite ED. cbn [CLBPOST]. apply evt_done. split; [exact HLV|].
      destruct (dec_r1_facts c r r1 DR Rin HR1) as (_ & _ & EO1 & _ & EP1 & EL1). eapply PATI_regs; [exact HP| assumption..]. }
  rewrite ED.
  destruct (dec_r1_facts c r r1 DR Rin HR1) as (DR1 & EI1 & EO1 & ER1 & EP1 & EL1).
  pose proof (dchk_sound 8 s c _ _ _ r r1 EC) as SND. cbv zeta in SND. destruct SND as (_ & RN32 & _).
  set (here := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) in *.
  pose proof (code_bits_range here) as RCB. pose proof (code_val_range here) as RCV.
  pose proof (DREGS_hold64 c r1 DR1) as RH1. pose proof DR1 as (Rn1 & Rh1 & Rnh1 & RB1 & RHB1).
  assert (HP1 : PATI X (mkW s c r1)) by (eapply PATI_regs; [exact HP| assumption..]).
  destruct (Z.ltb_spec (code_val here) 16) as [V|V].
  -
    eapply evt_cut; [exact (cl_litw X s c r r1 q1 ms1 HJ HQJ XO HP EI1 EO1 ER1 EP1 EL1 (conj KB (proj2 RB1)) RH1 RI CPO RN V LL ltac:(lia) Hnl Hnd RPUT (proj1 Rh1) Rn1)|].
    intros ms2 (q2 & H2). cbv zeta in H2. fold here in H2. cbn [CLBPOST w_s w_r]. apply evt_done. split.
    + exists q2. unfold cl_lit in *. cbn [is_have is_nlen is_ndist iset_have iset_lens] in *. rewrite (wrap32_id (is_have s + 1)) in * by lia. exact H2.
    + destruct (ddrop_facts' r1 (code_bits here) ltac:(lia) ltac:(lia) RH1) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
      unfold cl_lit. eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf0
        | cbn [is_mode iset_have iset_lens]; rewrite E; unfold CODELENS, FLAGS, HCRC; lia| try reflexivity ..]; [| exact Pisr| bk_keep].
      cbn [is_mode iset_have iset_lens]. rewrite E. reflexivity.
  -
    eapply evt_cut; [exact (cl_need X s c r r1 q1 ms1 HJ HQJ XO DR1 Rin HP EI1 EO1 ER1 EP1 EL1 KB (proj2 RN32) RI CPO RN V)|].
    intros ms2 [(r2 & q2 & EN & HR2 & HJ2 & HQ2)|(r2 & EN & HR2 & HLV)].
    2:{ fold here in EN. rewrite EN. cbn [CLBPOST]. apply evt_done. split; [exact HLV|].
        destruct HR2 as [-> | ->]; [exact HP1| eapply PATI_regs; [exact HP1| reflexivity..]]. }
    fold here in EN. rewrite EN.
    destruct (cl_r2_facts c r1 r2 (code_bits here + cl_nb (code_val here)) DR1 Rin ltac:(unfold cl_nb; destruct (code_val here =? 16); [lia|]; destruct (code_val here =? 17); lia) HR2)
      as (DR2 & KB2 & EI2 & EO2 & ER2 & EP2 & EL2).
    pose proof (DREGS_hold64 c r2 DR2) as RH2. pose proof DR2 as (Rn2 & Rh2 & Rnh2 & RB2 & RHB2).
    assert (HP2 : PATI X (mkW s c r2)) by (eapply PATI_regs; [exact HP1| assumption..]).
    fold here in HJ2.
    assert (EIr : ir_in r2 = ir_in r) by congruence. assert (EOr : ir_out r2 = ir_out r) by congruence.
    assert (ERr : ir_ret r2 = ir_ret r) by congruence. assert (EPr : ir_put r2 = ir_put r) by congruence. assert (ELr : ir_left r2 = ir_left r) by congruence.
    unfold cl_after. cbv zeta. fold here.
    eapply evt_cut; [exact (cl_rep_hd X s c r r1 r2 q2 ms2 HJ2 HQ2 XO HP EIr EOr ERr EPr ELr (conj KB2 (proj2 RB2)) RH2 (proj1 Rh2) V LL
                             ltac:(lia) ltac:(lia) HLs RPUT Rn2)|].
    intros ms3 H3. cbv zeta in H3. fold here in H3.
    set (cb := code_bits here) in *. set (nb := cl_nb (code_val here)) in *.
    set (r3 := ddrop r2 cb) in *. set (copy := cl_base (code_val here) + BITSv (ir_hold r3) nb) in *. set (r4 := ddrop r3 nb) in *.
    assert (Rnb : 2 <= nb <= 7) by (subst nb; unfold cl_nb; destruct (code_val here =? 16); [lia|]; destruct (code_val here =? 17); lia).
    destruct (ddrop_facts' r2 cb ltac:(lia) ltac:(lia) RH2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). fold r3 in F1, F2, F3, F4, F5, F6, F7, F8, F9.
    destruct (ddrop_facts' r3 nb ltac:(lia) ltac:(lia) F7) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). fold r4 in G1, G2, G3, G4, G5, G6, G7, G8, G9.
    pose proof (BITSv_range (ir_hold r3) nb ltac:(lia) ltac:(lia)) as RBV.
    assert (P7 : 2 ^ nb <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). change (2 ^ 7) with 128 in P7.
    assert (Rcp : 3 <= copy <= 138) by (subst copy; unfold cl_base; destruct (code_val here =? 16); [lia|]; destruct (code_val here =? 17); lia).
    assert (HP3 : PATI X (mkW s c r3)) by (eapply PATI_regs; [exact HP2| assumption..]).
    assert (HP4 : PATI X (mkW s c r4)) by (eapply PATI_regs; [exact HP3| assumption..]).
    assert (BADP : forall rr, PATI X (mkW s c rr) -> PATI X (cl_bad s c rr)).
    { intros rr HPr. unfold cl_bad. eapply PATI_step; [exact HPr| reflexivity| reflexivity| reflexivity| exact Pf0
        | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]; [exact Pisr| bk_keep]. }
    revert H3. destruct (Z.eqb_spec (code_val here) 16) as [V16|NV16]; [destruct (Z.eqb_spec (is_have s) 0) as [H0|H0]|]; cbn [andb]; intros H3.
    1:{ cbn [CLBPOST]. apply evt_done. split; [exact H3| apply BADP; exact HP3]. }
    all: revert H3; destruct (Z.ltb_spec (is_nlen s + is_ndist s) (is_have s + copy)) as [OV|OV]; intros H3.
    1,3: cbn [CLBPOST]; apply evt_done; split; [exact H3| apply BADP; exact HP4].
    all: destruct H3 as (q3 & HL3 & HQ3).
    + pose proof (HLs (is_have s - 1) ltac:(lia)) as RL.
      exact (cl_rep_run X s c r4 copy _ q3 ms3 HL3 HQ3 XO HP4 LL ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E Pf0 Pisr Hnl Hnd ltac:(lia)).
    + exact (cl_rep_run X s c r4 copy _ q3 ms3 HL3 HQ3 XO HP4 LL ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv iota; lia) E Pf0 Pisr Hnl Hnd ltac:(lia)).
Qed.

Definition CLPOST (X : ictx) (res : ares unit) : machine_state -> Prop :=
  match res with
  | ARun _ w1 => fun ms' =>
      (if is_mode (w_s w1) =? BAD then exists x26 x12, ILOOP X w1 PC_DISPATCH x26 x12 ms'
       else exists q, ILOOPh X w1 PC_CL_X q ms' /\ CLX X (w_s w1) (w_r w1) q)
      /\ PATI X w1
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATI X w'
  | ARet _ _ => fun _ => False
  end.

Lemma cl_loop : forall k X s c r q ms,
  ILOOPh X (mkW s c r) PC_CL_B q ms -> CLB X s r (is_have s) q ->
  ix_ok X -> CL s c r -> PATI X (mkW s c r) -> is_have s < is_nlen s + is_ndist s -> clw_chk k s c r = true ->
  is_nlen s + is_ndist s - is_have s <= Z.of_nat k ->
  evt usegs (CLPOST X (codelens_while k (mkW s c r))) ms.
Proof.
  induction k as [|k IH]; intros X s c r q ms HL HQ XO HCL HP LT CHK RK; [cbn [Z.of_nat] in RK; lia|].
  rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1.codelens_while_S. cbn [clw_chk] in CHK.
  replace (is_have s <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (is_have s <? is_nlen s + is_ndist s) with true in CHK by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in CHK. destruct CHK as [OKD CHK].
  pose proof (codelens_body_spec c s r HCL LT) as BS.
  eapply evt_cut; [exact (cl_body X s c r q ms HL HQ XO HCL HP LT OKD)|]. intros ms1 H1.
  destruct (codelens_body (mkW s c r)) as [[|] [s1 c1 r1] | w' | rc w']; cbn [CLBPOST w_s w_r] in H1.
  - destruct BS as (-> & HCL1 & Hlt1 & Hb1 & En1 & Ed1 & _ & Ep1). destruct H1 as ((q1 & H1') & HP1).
    pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & Hbx1 & Hnl1 & Hnd1 & Hh1 & _).
    destruct (Z.ltb_spec (is_have s1) (is_nlen s1 + is_ndist s1)) as [LT1|GE1].
    + destruct H1' as (HL1 & HQ1).
      exact (IH X s1 c r1 q1 ms1 HL1 HQ1 XO HCL1 HP1 LT1 CHK ltac:(rewrite Nat2Z.inj_succ in RK; lia)).
    + destruct H1' as (HL1 & HQ1).
      rewrite codelens_while_stop by lia. cbn [CLPOST w_s w_r]. rewrite E1. change (CODELENS =? BAD) with false.
      apply evt_done. split; [exists q1; split; assumption| exact HP1].
  - destruct BS as (HM1 & _). cbn [CLPOST w_s w_r]. rewrite HM1. change (BAD =? BAD) with true. apply evt_done. exact H1.
  - apply evt_done. cbn [CLPOST]. exact H1.
  - destruct BS.
Qed.

Lemma cl_while : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CODELENS_E q ms -> HCC X r q ->
  ix_ok X -> WINV (mkW s c r) -> ATY s -> PATI X (mkW s c r) -> is_mode s = CODELENS ->
  evt usegs (CLPOST X (codelens_while 321 (mkW s c r))) ms.
Proof.
  intros X s c r q ms HL HQ XO HW HA HP HM.
  pose proof (codelens_facts s c r HW HA HM) as (HCL & Hlt & _).
  pose proof (WINV_codelens_okb s c r HW HA HM) as OKB. unfold codelens_okb in OKB. cbn [w_s w_c w_r] in OKB.
  apply andb_prop in OKB. destruct OKB as [OKB _]. apply andb_prop in OKB. destruct OKB as [Rnd CHK]. apply Z.leb_le in Rnd.
  pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd' & Hh & HLs & HT & _).
  destruct (decode_okb_lvl1 _ _ _ _ _ _ ltac:(cbn [clw_chk] in CHK; replace (is_have s <? is_nlen s + is_ndist s) with true in CHK by (symmetry; apply Z.ltb_lt; lia); apply andb_prop in CHK; exact (proj1 CHK))) as [RN _].
  eapply evt_cut; [exact (cl_entry X s c r q ms HL HQ ltac:(lia) Hnl Hnd' RN (cpok_ofs_ok _ _ _ _ HT))|]. intros ms1 (q1 & H1).
  replace (is_have s <? is_nlen s + is_ndist s) with true in H1 by (symmetry; apply Z.ltb_lt; lia).
  destruct H1 as (HL1 & HQ1).
  exact (cl_loop 321 X s c r q1 ms1 HL1 HQ1 XO HCL HP Hlt CHK ltac:(cbn; lia)).
Qed.
End Z_infl_a_codelens2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_t_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_len OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_lenlens1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_lenlens OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_codelens1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_infl_a_codelens.Z_infl_a_codelens2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate Inftrees ItableModel InffastMem RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 RefInflateSafeOK3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_DIST1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LENLENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_CODELENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.

Definition PC_CL_C1 : Z := 0x1fc08.
Definition PC_CL_RET1 : Z := 0x1fc34.
Definition PC_CL_C2 : Z := 0x1ff10.
Definition PC_CL_RET2 : Z := 0x1ff60.

Local Ltac close_gen j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; unfold iframe_cells; inorm; close_cells FRM | exact STK
  | first [exact ZS | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS]
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma cl_x256 : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_CL_X q ms -> CLX X s r q -> ix_ok X -> PATI X (mkW s c r) ->
  arr_len (is_lens s) = 320 -> ty16 (is_lens s) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' =>
    if arr_get (is_lens s) 256 =? 0
    then exists x26 x12, ILOOP X (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_code_missing_end_of_block) r) PC_DISPATCH x26 x12 ms'
    else exists q', ILOOPh X (mkW s c r) PC_CL_C1 q' ms' /\ CLX X s r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP LL TY RPUT.
  unfold CLX, HCC, HC in HQ. hred_in HQ. destruct HQ as (E12 & (E9 & E18 & E22 & E24 & E25) & E10).
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_X.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  pose proof (TY 256) as R256.
  zs. replace (wz (-513)) with (wz 18446744073709551103) by (apply Z_to_bv_eqm; reflexivity).
  zs. zstep. br_true.
  pose proof Gl as Gl'. unfold ilens, u16arr in Gl'. ld16 Gl' (is_lens s) 320 (il_As (ix_L X) + 168) 256 ltac:(lia). clear Gl'.
  zstep. br_cases K.
  - replace (arr_get (is_lens s) 256 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    do 7 zs. itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  - replace (arr_get (is_lens s) 256 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | ]| unfold CLX, HCC, HC; hred; repeat split; reflexivity].
    close_gen j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma cl_after2 : forall X s4 c r x1 q ms ret,
  ILOOPc X (mkW s4 c r) PC_CL_RET2 x1 q ms -> h10 q = wz (ret mod 2 ^ 64) -> HC X r q -> (ret = 0 \/ ret = 1 \/ ret = -1) -> ix_ok X ->
  0 <= ix_flush X <= 4 ->
  (is_window_blk s4 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) <= 1 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' =>
    if negb (ret =? 0)
    then exists x26 x12, ILOOP X (mkW (iset_mode s4 BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret)) PC_DISPATCH x26 x12 ms'
    else exists x26 x12, ILOOP X (mkW (iset_mode s4 LEN_) c (irset_ret r ret)) PC_LEN_ x26 x12 ms') ms.
Proof.
  intros X s4 c r x1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms ret HL E10 HQ RRET XO RF Pwin Pin Pin1 Pout RPUT.
  unfold HC in HQ. hred_in HQ. hred_in E10. destruct HQ as (E9 & E18 & E22 & E24 & E25).
  destruct HL as (m & -> & (j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU. hred. cbn [w_s w_c w_r] in *.
  subst x10 x9 x18 x22 x24 x25.
  ix_open XO. unfold PC_CL_RET2.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  assert (RM : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  zs. zs. br_cases K.
  -
    assert (R0 : ret = 0) by (destruct RRET as [R|[R|R]]; rewrite R in K; [exact R| |]; exfalso; revert K; vm_compute; discriminate).
    clear RRET K RM. subst ret. cbn [Z.eqb negb].
    do 8 zs. zstep. br_false. itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  -
    assert (R1 : (ret =? 0) = false) by (apply Z.eqb_neq; intros R; rewrite R in K; apply K; reflexivity). rewrite R1. cbn [negb].
    clear RRET K.
    do 2 zs. do 7 zs. itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Section CLcalls.
Variable flush : Z.
Hypothesis ITABLE : inflate_table_stmt.

Lemma cl_call2 : forall X s3 c r x1 q ms ret tbl nxt db wk,
  ILOOPc X (mkW s3 c r) PC_CL_C2 x1 q ms -> HC X r q -> ix_ok X -> 0 <= ix_flush X <= 4 ->
  (is_window_blk s3 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) <= 1 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = (ret, tbl, nxt, db, wk) ->
  it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true ->
  ATY s3 -> (forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15) ->
  257 <= is_nlen s3 <= 286 -> 1 <= is_ndist s3 <= 30 -> 0 <= is_next s3 <= 1444 -> iarrs s3 ->
  evt usegs (fun ms' =>
    if negb (ret =? 0)
    then exists x26 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl nxt db wk) BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret)) PC_DISPATCH x26 x12 ms'
    else exists x26 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl nxt db wk) LEN_) c (irset_ret r ret)) PC_LEN_ x26 x12 ms') ms.
Proof.
  intros X s3 c r x1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms ret tbl nxt db wk
         HL HQ XO RF Pwin Pin Pin1 Pout RPUT EIT SAFE HA HL15 Rnl Rnd Rnx HARR.
  unfold HC in HQ. hred_in HQ. destruct HQ as (E9 & E18 & E22 & E24 & E25).
  destruct HL as (m & -> & (j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU. hred. cbn [w_s w_c w_r] in *.
  subst x9 x18 x22 x24 x25.
  ix_open XO. unfold PC_CL_C2.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  do 6 zs. itr_groups MUf WMf. clear MUf WMf.
  gT. zs. replace (is_nlen s3 ≪ 1) with (2 * is_nlen s3) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zs. zstep. rewrite (zb_lxor_ones (il_As (ix_L X) + 168)) by lia. br_true.
  do 8 zs.
  set (spre := iset_distbits (iset_distcode s3 (CDyn (is_next s3))) 6).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
  assert (ST' : IST m1 (ix_L X) spre);
  [ subst spre; constructor; inorm;
    [ unfold isA, isA_cells; inorm; unfold cp_addr at 2; close_cells GA | exact GT | exact Gl | exact Gw | exact Gc | exact Gwin
    | unfold iarrs in *; inorm; exact HARR | exact LAY ]
  | clear GA GT Gl Gw Gc Gwin ] end.
  pose proof (inflate_table_ret _ _ _ _ _ _ _ _ _ _ _ _ _ EIT) as RRET.
  eapply evt_cut.
  { eapply (ITABLE (ix_L X) spre DISTS true (is_nlen s3) (is_ndist s3) (ix_lo X));
      [ exact ST' | eassumption | rewrite unsigned_lit by lia; exact STK | rewrite unsigned_lit by lia; unfold Z_ITABLE_STACK; lia | lia
      | intros NE; subst spre; cbn in NE; pose proof (xo_win _ XO (Pwin NE)); lia
      | lia | lia | lia | subst spre; cbn; lia | subst spre; cbn; lia
      | subst spre; cbn [it_bits_get is_lens is_codes is_next is_work is_distbits iset_distcode iset_distbits]; exact SAFE
      | exact HA
      | subst spre; cbn [is_lens is_nlen iset_distcode iset_distbits]; exact HL15
      | cbn [it_codes_ok]; first [exact I | lia]
      | reflexivity | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STKc & EA0 & STc).
  rewrite unsigned_lit in MUc, STKc by lia.
  assert (ER : it_result DISTS true (is_nlen s3) (is_ndist s3) spre = (ret, cl_tab2 s3 tbl nxt db wk)).
  { unfold it_result. subst spre. cbn [it_bits_get it_bits_set is_lens is_codes is_next is_work is_distbits iset_distcode iset_distbits].
    rewrite EIT.
    unfold cl_tab2, it_bits_set. cbv [iset_work iset_distbits iset_next iset_distcode iset_codes
      is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk
      is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next
      is_lens is_work is_codes is_sane is_back is_was is_self_blk]. reflexivity. }
  rewrite ER in EA0, STc. cbn [fst snd] in EA0, STc. subst a0'. clear ER ST' spre.
  lazymatch type of WMc with wmono _ ?ma _ => itr_groups MUc WMc; transport_after_call usegs ma m' MUc WMc end. clear MUc WMc MI HARR LAY.
  replace (ret_pc (wz 130912)) with (wz 130912) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply (cl_after2 X (cl_tab2 s3 tbl nxt db wk) c r _ _ _ ret); [ | | | exact RRET | exact XO | exact RF | exact Pwin | exact Pin | exact Pin1 | exact Pout | exact RPUT].
  { eapply ILOOPc_intro; ired; [ireg .. |].
    apply IMEM_intro; [ exists j0, jf; exact FRM | exact STKc | exact ZS | exact STc | exact IN | exact OUT | exact MIc | exact MU | exact WM ]. }
  { hred. reflexivity. }
  { unfold HC. hred. repeat split; reflexivity. }
Qed.

Lemma cl_after1 : forall X s3 c r x1 q ms ret ret2 tbl2 nxt2 db wk2,
  ILOOPc X (mkW s3 c r) PC_CL_RET1 x1 q ms -> h10 q = wz (ret mod 2 ^ 64) -> HC X r q -> (ret = 0 \/ ret = 1 \/ ret = -1) -> ix_ok X ->
  0 <= ix_flush X <= 4 ->
  (is_window_blk s3 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) <= 1 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  (ret = 0 -> inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = (ret2, tbl2, nxt2, db, wk2)) ->
  (ret = 0 -> it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true) ->
  (ret = 0 -> ATY s3) -> (ret = 0 -> forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15) ->
  257 <= is_nlen s3 <= 286 -> 1 <= is_ndist s3 <= 30 -> (ret = 0 -> 0 <= is_next s3 <= 1444) ->
  evt usegs (fun ms' =>
    if negb (ret =? 0)
    then exists x26 x12, ILOOP X (mkW (iset_mode s3 BAD) (icset_msg c MSG_invalid_literal_lengths_set) (irset_ret r ret)) PC_DISPATCH x26 x12 ms'
    else if negb (ret2 =? 0)
    then exists x26 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret2)) PC_DISPATCH x26 x12 ms'
    else exists x26 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) LEN_) c (irset_ret r ret2)) PC_LEN_ x26 x12 ms') ms.
Proof.
  intros X s3 c r x1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms ret ret2 tbl2 nxt2 db wk2
         HL E10 HQ RRET XO RF Pwin Pin Pin1 Pout RPUT EIT2 SAFE2 HA3 HL15 Rnl Rnd Rnx.
  pose proof HL as HL0. pose proof HQ as HQ0.
  unfold HC in HQ. hred_in HQ. hred_in E10. destruct HQ as (E9 & E18 & E22 & E24 & E25).
  destruct HL as (m & -> & (j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU. hred. cbn [w_s w_c w_r] in *.
  subst x10 x9 x18 x22 x24 x25.
  ix_open XO. unfold PC_CL_RET1.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  assert (RM : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  zs. br_cases K.
  -
    assert (R0 : ret = 0) by (destruct RRET as [R|[R|R]]; rewrite R in K; [exact R| |]; exfalso; revert K; vm_compute; discriminate).
    clear RRET K RM. subst ret. cbn [Z.eqb negb].
    eapply (cl_call2 X s3 c r _ _ _ ret2 tbl2 nxt2 db wk2); [| | exact XO | exact RF | exact Pwin | exact Pin | exact Pin1 | exact Pout | exact RPUT
      | exact (EIT2 eq_refl) | exact (SAFE2 eq_refl) | exact (HA3 eq_refl) | exact (HL15 eq_refl) | exact Rnl | exact Rnd | exact (Rnx eq_refl) | exact ARRS ].
    { eapply ILOOPc_intro; ired; [ireg .. |].
      close_gen j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM. }
    unfold HC. hred. repeat split; reflexivity.
  -
    assert (R1 : (ret =? 0) = false) by (apply Z.eqb_neq; intros R; rewrite R in K; apply K; reflexivity). rewrite R1. cbn [negb].
    clear RRET K.
    do 4 zs. do 7 zs. itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    close_gen j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma cl_call1 : forall X s c r q ms ret tbl nxt lb wk ret2 tbl2 nxt2 db wk2,
  let s3 := cl_tab1 s tbl nxt lb wk in
  ILOOPh X (mkW s c r) PC_CL_C1 q ms -> CLX X s r q ->
  ix_ok X -> 0 <= ix_flush X <= 4 -> PATI X (mkW s c r) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) = (ret, tbl, nxt, lb, wk) ->
  it_safe LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) = true ->
  ATY s -> (forall i, 0 <= i < is_nlen s -> arr_get (is_lens s) (0 + i) <= 15) ->
  257 <= is_nlen s <= 286 -> 1 <= is_ndist s <= 30 ->
  (ret = 0 -> inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = (ret2, tbl2, nxt2, db, wk2)) ->
  (ret = 0 -> it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true) ->
  (ret = 0 -> ATY s3) -> (ret = 0 -> forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15) ->
  (ret = 0 -> 0 <= is_next s3 <= 1444) ->
  evt usegs (fun ms' =>
    if negb (ret =? 0)
    then exists x26 x12, ILOOP X (mkW (iset_mode s3 BAD) (icset_msg c MSG_invalid_literal_lengths_set) (irset_ret r ret)) PC_DISPATCH x26 x12 ms'
    else if negb (ret2 =? 0)
    then exists x26 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) BAD) (icset_msg c MSG_invalid_distances_set) (irset_ret r ret2)) PC_DISPATCH x26 x12 ms'
    else exists x26 x12, ILOOP X (mkW (iset_mode (cl_tab2 s3 tbl2 nxt2 db wk2) LEN_) c (irset_ret r ret2)) PC_LEN_ x26 x12 ms') ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms ret tbl nxt lb wk ret2 tbl2 nxt2 db wk2 s3
         HL HQ XO RF HP RPUT EIT SAFE HA HL15 Rnl Rnd EIT2 SAFE2 HA3 HL15' Rnx.
  unfold CLX, HCC, HC in HQ. hred_in HQ. destruct HQ as (E12 & (E9 & E18 & E22 & E24 & E25) & E10).
  iarm_openh HL. subst.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_CL_C1.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  do 11 zs. itr_groups MUf WMf. clear MUf WMf.
  set (spre := iset_lencode (iset_next (iset_lenbits s 9) 0) (CDyn 0)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
  assert (ST' : IST m1 (ix_L X) spre);
  [ subst spre; constructor; inorm;
    [ unfold isA, isA_cells; inorm; unfold cp_addr at 1; close_cells GA | exact GT | exact Gl | exact Gw | exact Gc | exact Gwin
    | unfold iarrs in *; inorm; exact ARRS | exact LAY ]
  | clear GA GT Gl Gw Gc Gwin ] end.
  pose proof (inflate_table_ret _ _ _ _ _ _ _ _ _ _ _ _ _ EIT) as RRET.
  eapply evt_cut.
  { eapply (ITABLE (ix_L X) spre LENS false 0 (is_nlen s) (ix_lo X));
      [ exact ST' | eassumption | rewrite unsigned_lit by lia; exact STK | rewrite unsigned_lit by lia; unfold Z_ITABLE_STACK; lia | lia
      | intros NE; subst spre; cbn in NE; pose proof (xo_win _ XO (Pwin NE)); lia
      | lia | lia | lia | subst spre; cbn; lia | subst spre; cbn; lia
      | subst spre; cbn [it_bits_get is_lens is_codes is_next is_work is_lenbits iset_lencode iset_next iset_lenbits]; exact SAFE
      | exact HA
      | subst spre; cbn [is_lens iset_lencode iset_next iset_lenbits]; exact HL15
      | cbn [it_codes_ok]; first [exact I | lia]
      | reflexivity | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MIc & STKc & EA0 & STc).
  rewrite unsigned_lit in MUc, STKc by lia.
  assert (ER : it_result LENS false 0 (is_nlen s) spre = (ret, s3)).
  { unfold it_result. subst spre s3. cbn [it_bits_get it_bits_set is_lens is_codes is_next is_work is_lenbits iset_lencode iset_next iset_lenbits].
    rewrite EIT.
    unfold cl_tab1, it_bits_set. cbv [iset_work iset_lenbits iset_next iset_lencode iset_codes
      is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext is_window is_window_blk
      is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next
      is_lens is_work is_codes is_sane is_back is_was is_self_blk]. reflexivity. }
  rewrite ER in EA0, STc. cbn [fst snd] in EA0, STc. subst a0'. clear ER ST' spre.
  lazymatch type of WMc with wmono _ ?ma _ => itr_groups MUc WMc; transport_after_call usegs ma m' MUc WMc end. clear MUc WMc MI ARRS LAY.
  replace (ret_pc (wz 130100)) with (wz 130100) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (Pwin3 : is_window_blk s3 <> None -> ix_hasw X = true) by exact Pwin.
  eapply (cl_after1 X s3 c r _ _ _ ret ret2 tbl2 nxt2 db wk2);
    [ | | | exact RRET | exact XO | exact RF | exact Pwin3 | exact Pin | exact Pin1 | exact Pout | exact RPUT
    | exact EIT2 | exact SAFE2 | exact HA3 | exact HL15' | exact Rnl | exact Rnd | exact Rnx ].
  { eapply ILOOPc_intro; ired; [ireg .. |].
    apply IMEM_intro; [ exists j0, jf; exact FRM | exact STKc | exact ZS | exact STc | exact IN | exact OUT | exact MIc | exact MU | exact WM ]. }
  { hred. reflexivity. }
  { unfold HC. hred. repeat split; reflexivity. }
Qed.
End CLcalls.

Lemma irset_ret_twice : forall r a b, irset_ret (irset_ret r a) b = irset_ret r b.
Proof. intros [n h p l ho b' i o rt] a b. reflexivity. Qed.

Section CLcore.
Variable flush : Z.
Hypothesis ITABLE : inflate_table_stmt.
Hypothesis RF : 0 <= flush <= 4.

Lemma codelens_core : codelens_core_stmt flush.
Proof.
  intros X [s c r] q ms EF HL E9 E10 E18 E22 E24 E25 XO HW HA HP HM. cbn [w_s w_c w_r] in *.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (RFX : 0 <= ix_flush X <= 4) by (rewrite EF; exact RF).
  assert (HQ : HCC X r q) by (unfold HCC, HC; repeat split; assumption).
  rewrite arm_CODELENS_eq.
  pose proof (codelens_facts s c r HW HA HM) as (HCL & Hlt & F).
  pose proof (WINV_codelens_okb s c r HW HA HM) as OKB. unfold codelens_okb in OKB. cbn [w_s w_c w_r] in OKB.
  apply andb_prop in OKB. destruct OKB as [_ OKB].
  pose proof (codelens_next_WINV flush s c r HW HA HM) as NXW. unfold codelens_next in NXW.
  eapply evt_cut; [exact (cl_while X s c r q ms HL HQ XO HW HA HP HM)|]. intros ms1 H1.
  destruct (codelens_while 321 (mkW s c r)) as [[] [s1 c1 r1] | w' | rc w']; cbn [CLPOST w_s w_r] in H1.
  2:{ apply evt_done. cbn [IPOST wof]. exact H1. }
  2:{ destruct H1. }
  destruct (Z.eqb_spec (is_mode s1) BAD) as [EB|NB].
  { destruct H1 as [H1 HP1]. apply evt_done. split; [cbn [IPOST w_s]; first [exact H1 | rewrite EB; exact H1] | exact HP1]. }
  destruct F as [EB|(-> & HCL1 & Hh1 & Hb1 & HA1)]; [contradiction|].
  destruct H1 as [(q1 & HL1 & HQ1) HP1].
  pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & Hbx1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HT1 & HWF1 & HWB1).
  assert (LL1 : arr_len (is_lens s1) = 320) by (destruct HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  pose proof HR1 as (Rn1 & Rh1 & Rnh1 & Rp1 & Rl1 & Rpl1 & _).
  pose proof HP1 as (_ & _ & _ & Pfl1 & _ & _ & _ & _ & _ & _ & Pisr1 & _). cbn [w_s w_c w_r] in Pfl1, Pisr1.
  assert (Pf1 : is_flags s1 = 0) by (destruct Pfl1 as [Pf|(Pf & [E'|E'] & _)]; [exact Pf| |]; rewrite E1 in E'; discriminate E').
  assert (RPUT1 : 0 <= ir_put r1 <= Z.of_nat (length (ix_rest0 X))) by (rewrite <- Pout; lia).
  pose proof HA1 as (TY1 & TYw1 & TYc1).
  unfold cl_post_ok in OKB. unfold cl_post.
  eapply evt_cut; [exact (cl_x256 X s1 c r1 q1 ms1 HL1 HQ1 XO HP1 LL1 TY1 RPUT1)|]. intros ms2 H2.
  revert OKB NXW H2. destruct (Z.eqb_spec (arr_get (is_lens s1) 256) 0) as [Z0|NZ]; intros OKB NXW H2.
  {
    apply evt_done. split; [cbn [IPOST w_s]; exact H2|]. cbn [wof].
    eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]; [exact Pisr1| bk_keep]. }
  destruct H2 as (q2 & HL2 & HQ2).
  revert OKB NXW. destruct (inflate_table LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)) as [[[[ret tbl] nxt] lb] wk] eqn:EIT1.
  cbv zeta. intros OKB NXW.
  apply andb_prop in OKB. destruct OKB as [OKB REST]. apply andb_prop in OKB. destruct OKB as [L15 SAFE1].
  apply andb_prop in REST. destruct REST as [LPO1 REST].
  pose proof (lens15b_sound _ _ _ L15 ltac:(lia) ltac:(lia)) as HL15. rewrite Z.sub_0_r in HL15.
  destruct (ll_post_ok_sound _ _ _ _ LPO1) as (Ltbl & Lwk & Rnxt & Rlb & Ttbl & Twk).
  pose proof (inflate_table_typed LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1) TYc1 TYw1) as TT. rewrite EIT1 in TT. destruct TT as [TT1 TT2].
  set (s3 := cl_tab1 s1 tbl nxt lb wk) in *.
  assert (HA3 : ATY s3) by (split; [exact TY1| split; [exact TT2| exact TT1]]).
  revert REST NXW. destruct (inflate_table DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3)) as [[[[ret2 tbl2] nxt2] db] wk2] eqn:EIT2.
  intros REST NXW.
  assert (C2 : ret = 0 -> (forall i, 0 <= i < is_ndist s3 -> arr_get (is_lens s3) (is_nlen s3 + i) <= 15)
                         /\ it_safe DISTS (is_lens s3) (is_nlen s3) (is_ndist s3) (is_codes s3) (is_next s3) 6 (is_work s3) = true).
  { intros R0. rewrite R0 in REST. cbn [Z.eqb] in REST. apply andb_prop in REST. destruct REST as [REST _]. apply andb_prop in REST. destruct REST as [L15' SAFE2].
    split; [|exact SAFE2]. pose proof (lens15b_sound _ _ _ L15' ltac:(cbn; lia) ltac:(cbn; lia)) as H. intros i Hi. apply H. lia. }
  eapply evt_cut.
  { exact (cl_call1 ITABLE X s1 c r1 q2 ms2 ret tbl nxt lb wk ret2 tbl2 nxt2 db wk2 HL2 HQ2 XO RFX HP1 RPUT1 EIT1 SAFE1 HA1 HL15 Hnl1 Hnd1
             (fun _ => EIT2) (fun R0 => proj2 (C2 R0)) (fun _ => HA3) (fun R0 => proj1 (C2 R0)) (fun _ => Rnxt)). }
  intros ms3 H3. cbv zeta in H3. fold s3 in H3.
  revert H3 NXW. destruct (Z.eqb_spec ret 0) as [R0|R1]; cbn [negb]; intros H3 NXW.
  2:{
      apply evt_done. split; [cbn [IPOST w_s]; exact H3|]. cbn [wof]. subst s3. unfold cl_tab1.
      eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]; [exact Pisr1| bk_keep]. }
  rewrite irset_ret_twice. rewrite irset_ret_twice in NXW.
  revert H3 NXW. destruct (Z.eqb_spec ret2 0) as [R0'|R1']; cbn [negb]; intros H3 NXW.
  2:{
      apply evt_done. split; [cbn [IPOST w_s]; exact H3|]. cbn [wof]. subst s3. unfold cl_tab1, cl_tab2.
      eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| try reflexivity ..]; [exact Pisr1| bk_keep]. }
  replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia).
  replace (flush =? Z_TREES) with false in NXW by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia).
  destruct H3 as (x26' & x12' & HL3).
  destruct (NXW _ eq_refl) as [HW2 HM2].
  refine (len__core X _ x26' x12' ms3 HL3 XO HW2 _ HM2).
  subst s3. unfold cl_tab1, cl_tab2.
  eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold LEN_, FLAGS, HCRC; lia| try reflexivity ..]; [exact Pisr1| bk_keep].
Qed.

Lemma arm_CODELENS_of : arm_stmt flush CODELENS PC_CODELENS (arm_CODELENS ivar_ref flush).
Proof.
  intros X [s c r] x12 ms EF HL XO HW HA HP HM.
  destruct (ILOOPh_of_ILOOP X _ _ _ _ ms HL) as (q & HLh & _ & _ & (E9 & E10 & _ & _ & E18 & E22 & E24 & E25)). cbn [w_r] in *.
  exact (codelens_core X (mkW s c r) q ms EF HLh E9 E10 E18 E22 E24 E25 XO HW HA HP HM).
Qed.
End CLcore.
