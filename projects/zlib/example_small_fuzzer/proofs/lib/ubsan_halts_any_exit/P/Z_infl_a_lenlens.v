(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_iface Z_infl_c_defs.

Module Z_infl_c_pure.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2.
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
  ISR s' -> PATI X (mkW s' c' r').
Proof.
  intros X s c r s' c' r' v (P1 & P2 & P3 & _ & _ & P6 & P7 & P8 & P9 & P10 & _ & (P12 & P13 & _ & _ & P16)) E1 E2 E3 E4 NG E6 E7 E8 Hv Hp E9 E10 HO HN HI.
  unfold PATI, OBYT in *. cbn [w_s w_c w_r] in *. rewrite E1, E2, E3, E6, E7, E8, E9, E10. rewrite E9 in HO. rewrite arr_len_set.
  repeat (split; [first [assumption | left; assumption]|]).
  split; [|split; [exact P13| split; [exact HO| split; [rewrite <- E9; exact HN| exact P16]]]].
  intros i Hi. destruct (Z.eq_dec i (ir_put r)) as [->|NE].
  - rewrite arr_get_set_same by lia. exact Hv.
  - rewrite arr_get_set_other by lia. apply P12. lia.
Qed.
End Z_infl_c_pure.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_c_tab.

Module Z_infl_a_match.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure.
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

Definition PC_MATCH_T : Z := 0x1e840.
Definition mt_s1 (s : inflate_state) : inflate_state := iset_length s (is_length s - 1).
Definition mt_c1 (s : inflate_state) (c : icall) : icall := icset_outbuf c (arr_set (ic_outbuf c) 0 (arr_get (is_window s) (mt_idx s))).
Definition mt_r1 (r : iregs) : iregs := irset_put (irset_left r 0) 1.

Lemma match_tail : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_MATCH_T q ms -> sc12 q = wz 1 -> sc13 q = wz (il_Aw (ix_L X) + mt_idx s) -> sc14 q = wz (bv_swrap 32 (is_length s)) ->
  sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> ix_hasw X = true -> is_window_blk s <> None -> 0 <= mt_idx s < 32768 -> 0 <= arr_get (is_window s) (mt_idx s) < 256 ->
  ir_left r = 1 -> ir_put r = 0 -> arr_len (ic_outbuf c) = 1 -> length (ix_rest0 X) = 1%nat -> 1 <= is_length s < 2^32 -> 0 <= is_mode s < 2^31 ->
  evt psegs (IPOST X (if is_length s - 1 =? 0 then ARun tt (mkW (iset_mode (mt_s1 s) LEN) (mt_c1 s c) (mt_r1 r)) else ARun tt (mkW (mt_s1 s) (mt_c1 s c) (mt_r1 r)))) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E12 E13 E14 E26 XO HASW NWB RIDX RBYTE HL1 HP0 HOB HR0 RLEN RMODE.
  iarm_openg HL. subst x12 x13 x14 x26. ix_open XO.
  pose proof (xo_win _ XO HASW) as XWin.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (av8_zlength (is_window s) 32768 ltac:(lia)) as LWIN.
  open_IST ST. open_isA GA. 
  unfold iwin in Gwin. destruct (is_window_blk s) as [wb|] eqn:EWB; [|contradiction]. clear NWB.
  pose proof (munch_refl (ix_Wf X) m) as MUf; unfold ix_Wf in MUf; pose proof (wmono_refl psegs m) as WMf.
  unfold PC_MATCH_T.
  zs. rewrite bv_swrap32_sub_land. set (l1 := bv_swrap 32 (is_length s - 1)). pose proof (bv_swrap32_range (is_length s - 1)) as Rl1. fold l1 in Rl1.
  do 6 zs.
  ld8 Gwin (is_window s) 32768 (il_Aw (ix_L X)) (mt_idx s) ltac:(exact RBYTE).
  zs.
  pose proof (u8arr_store_ok psegs _ _ _ (ir_put r) (wa (il_NO (ix_L X) + ir_put r)) OUT ltac:(lia) eq_refl) as SOK.
  zs. rewrite le1_wz_byte by exact RBYTE.
  pose proof (u8arr_write psegs _ _ _ (ir_put r) (Z_to_bv 8 (arr_get (is_window s) (mt_idx s))) OUT ltac:(lia)) as OUT2. clear OUT LOB.
  store_done.
  rewrite iout_bytes_store in OUT2 by lia.
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (arr_set (ic_outbuf c) (ir_put r) (arr_get (is_window s) (mt_idx s)))) (ir_put r + 1) ltac:(lia)) as LOB.
  apply (f_equal Z.of_nat) in LOB.
  do 3 zs. br_false. do 3 zs. br_cases K.
  - apply (proj1 (land64_zero_iff l1 ltac:(lia))) in K. unfold l1 in K. apply (proj1 (bv_swrap32_zero_iff (is_length s - 1) ltac:(lia))) in K. replace (is_length s - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; exact K).
    do 6 zs. itr_groups MUf WMf.
    apply evt_done. cbn [IPOST]. eexists. eapply ILOOP_intro; unfold mt_s1, mt_c1, mt_r1; ired; [ireg .. |].
    rewrite HP0 in OUT2. change (0 + 1) with 1 in OUT2.
    apply IMEM_intro; inorm;
    [ exists jf; exact FRM | exact STK | exact ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; rewrite EWB; close_cells GA; apply le4_swrap32| exact GT| exact Gl| exact Gw| exact Gc| unfold iwin; inorm; rewrite EWB; exact Gwin| exact ARRS| unfold ilay_ok in *; inorm; exact LAY]
    | exact IN | unfold iout; exact OUT2 | eassumption | exact MU | exact WM ].
  - assert (K' : is_length s - 1 <> 0).
    { intros E. apply K. apply (proj2 (land64_zero_iff l1 ltac:(lia))). unfold l1. apply (proj2 (bv_swrap32_zero_iff (is_length s - 1) ltac:(lia))). exact E. }
    replace (is_length s - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact K').
    do 4 zs. itr_groups MUf WMf.
    apply evt_done. cbn [IPOST]. eexists. eapply ILOOP_intro; unfold mt_s1, mt_c1, mt_r1; ired; [ireg .. |].
    rewrite HP0 in OUT2. change (0 + 1) with 1 in OUT2.
    apply IMEM_intro; inorm;
    [ exists jf; exact FRM | exact STK | exact ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; rewrite EWB; close_cells GA; apply le4_swrap32| exact GT| exact Gl| exact Gw| exact Gc| unfold iwin; inorm; rewrite EWB; exact Gwin| exact ARRS| unfold ilay_ok in *; inorm; exact LAY]
    | exact IN | unfold iout; exact OUT2 | eassumption | exact MU | exact WM ].
Qed.

Local Ltac close_memT jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Local Ltac fin_cut HMEM EIDX :=
  apply evt_done; eexists; split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|];
  cbn [sc12 sc13 sc14 sc26]; rewrite EIDX; rewrite ?land_u32_small by lia; repeat split; ireg.

Lemma match_core : forall X w x8 x12 ms,
  ILOOP X w PC_MATCH x8 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = MATCH ->
  evt psegs (fun ms' => IPOST X (arm_MATCH ivar_ref w) ms' /\ PATI X (wof (arm_MATCH ivar_ref w))) ms.
Proof.
  intros X [s c r] x8 x12 ms HL XO HW HP HM.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  destruct HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & (POB & POW & POL & PNP & PHW)). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & Hlen1 & Hoff).
  destruct (match_win_facts s HCORE Pwb) as (Hws & Hwh & Hwn & HWIN). apply (id : _ -> hide _) in HWIN.
  assert (Csane : is_sane s = 1) by (destruct HCORE as (_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
  assert (Clen : 0 <= is_length s < 2^32) by (destruct HCORE as (_&_&_&_&_&_&_&_&_&_&_&_&_&H); exact H).
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (RMODE : 0 <= is_mode s < 2^31) by (rewrite HM; unfold MATCH; lia).
  apply (id : _ -> hide _) in Pisr. apply (id : _ -> hide _) in Pwin. apply (id : _ -> hide _) in POW.
  clear HCORE HWF HWB Pfl Pgz PNP RH Rin PHW.
  pose proof HMEM as ((jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_MATCH.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  zstep. br_cases K.
  -
    assert (Kl : ir_left r = 0) by lia.
    rewrite (arm_MATCH_eq s c r Csane). replace (ir_left r =? 0) with true by (symmetry; apply Z.eqb_eq; exact Kl).
    zs.
    apply evt_done. split; [|exact HP].
    cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
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
        do 8 zs. unfold hide in Pwin.
        itr_groups MUf WMf.
        apply evt_done. split.
        - cbn [IPOST]. eexists. eapply ILOOP_intro; ired; [ireg .. |].
          close_memT jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        - cbn [wof]. eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact Pisr. }
    assert (Kok : is_offset s <= is_whave s) by (apply (proj1 (sx32u_le_small (is_offset s) (is_whave s) ltac:(lia) ltac:(lia))); exact K3).
    replace (is_whave s <? is_offset s) with false by (symmetry; apply Z.ltb_ge; exact Kok).
    destruct (HWIN ltac:(lia)) as (EWS & NWB & RIDX & WN).
    assert (HASW : ix_hasw X = true) by (apply Pwin; exact NWB).
    assert (RBYTE : 0 <= arr_get (is_window s) (mt_idx s) < 256).
    { apply POW. destruct ARRS as (_ & _ & _ & AW). rewrite (AW NWB). exact RIDX. }
    assert (EWA : win_addr (ix_L X) (is_window_blk s) = il_Aw (ix_L X)) by (destruct (is_window_blk s); [reflexivity| contradiction]).
    rewrite EWA in GA. pose proof (xo_win _ XO HASW) as XWin.
    pose proof (bv_swrap32_range (is_length s)) as RSL. pose proof (sx32_wz_u (is_length s)) as ESL.
    set (sl := bv_swrap 32 (is_length s)) in *.
    eapply (evt_cut psegs (fun ms1 => exists q, ILOOPg X (mkW s c r) PC_MATCH_T q ms1 /\ sc12 q = wz 1 /\ sc13 q = wz (il_Aw (ix_L X) + mt_idx s)
                                               /\ sc14 q = wz sl /\ sc26 q = wz (il_NI (ix_L X) + ir_next r))).
    { rewrite (bv_swrap32_id (is_offset s)) by lia. do 2 zs. br_cases K4.
      -
        assert (EIDX : mt_idx s = is_wnext s - is_offset s) by (unfold mt_idx; replace (is_wnext s <? is_offset s) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        do 2 zs. rewrite ESL. zs. br_cases K5.
        + do 5 zs. br_false. do 1 zs. fin_cut HMEM EIDX.
        + assert (Esl : sl = is_length s) by (unfold sl; apply bv_swrap32_id; apply (proj1 (sx32u_le_small (is_length s) (is_offset s) ltac:(lia) ltac:(lia))) in K5; lia).
          zs. rewrite Esl. do 5 zs. br_false. do 1 zs. rewrite <- Esl. fin_cut HMEM EIDX.
      -
        assert (EIDX : mt_idx s = is_wsize s - (is_offset s - is_wnext s)) by (unfold mt_idx; replace (is_wnext s <? is_offset s) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
        do 5 zs. rewrite ESL. zs. br_cases K5.
        + do 5 zs. br_false. do 1 zs. fin_cut HMEM EIDX.
        + assert (Esl : sl = is_length s) by (unfold sl; apply bv_swrap32_id; apply (proj1 (sx32u_le_small (is_length s) (is_offset s - is_wnext s) ltac:(lia) ltac:(lia))) in K5; lia).
          zs. rewrite Esl. do 5 zs. br_false. do 1 zs. rewrite <- Esl. fin_cut HMEM EIDX. }
    intros ms1 (q & HJ & E12 & E13 & E14 & E26).
    eapply evt_mono; [exact (match_tail X s c r q ms1 HJ E12 E13 E14 E26 XO HASW NWB RIDX RBYTE HL1 HP0 ltac:(lia) ltac:(lia) ltac:(lia) RMODE)|].
    intros ms' HPO. split; [exact HPO|]. unfold hide in Pisr.
    destruct (is_length s - 1 =? 0); cbn [wof];
      (eapply (PATI_step_put X s c r _ _ _ (arr_get (is_window s) (mt_idx s)));
       [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| ired; rewrite ?HM; unfold LEN, MATCH, FLAGS, HCRC; lia| reflexivity| reflexivity
       | ired; rewrite HP0; reflexivity| exact RBYTE| lia| ired; lia| reflexivity| ired; lia| ired; rewrite ?HM; reflexivity| exact Pisr]).
Qed.

Lemma arm_MATCH_ok : forall flush, arm_stmt flush MATCH PC_MATCH (arm_MATCH ivar_ref).
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (match_core X w _ x12 ms HL XO HW HP HM). Qed.
End Z_infl_a_match.

Module Z_infl_a_distext.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_defs.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_match.
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

Definition PC_DISTEXT_E : Z := 0x1e708.
Definition PC_DISTEXT_J : Z := 0x1e768.

Lemma distext_nb : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_DISTEXT_E q ms -> sc13 q = wz (is_extra s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> REGS c r -> PATI X (mkW s c r) -> 1 <= is_extra s <= 15 ->
  evt psegs (NBJh X s c r (is_extra s) PC_DISTEXT_J) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E13 E26 XO HREGS HP REX.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x13 x26.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
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
    + cbn [h12 h13 h14 h15 h22 h29 h31]. repeat split; reflexivity.
  - do 4 zs. br_cases K2.
    +
      assert (H0 : ir_have r = 0) by lia.
      do 8 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
    +
      assert (H1 : ir_have r = 1) by lia.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 7 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      br_cases K3.
      *
        zs. br_true. do 8 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [|split].
        -- apply nb_pull_dry; lia.
        -- right. reflexivity.
        -- unfold hide in RH. eapply ILEAVE_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
      * zs. apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
        -- apply nb_pull_ok; lia.
        -- right. split; [reflexivity| lia].
        -- eapply ILOOPh_intro; ired; [ireg .. |]. exact HMEM.
        -- unfold hide in RH. cbn [h12 h13 h14 h15 h22 h29 h31]. pullr_rw c r. repeat split; ireg.
Qed.

Lemma distext_fin : forall X s c r r1 q ms,
  ILOOPh X (mkW s c r) PC_DISTEXT_J q ms ->
  h12 q = wz (ir_have r1) -> h13 q = wz (is_extra s) -> h14 q = wz (ir_bits r1) -> h15 q = wz (il_NI (ix_L X) + ir_next r1) ->
  h22 q = wz (ir_hold r1) -> h29 q = wz 30 -> h31 q = wz (-16180) ->
  ix_ok X -> PATI X (mkW s c r) ->
  ir_in r1 = ir_in r -> ir_out r1 = ir_out r -> ir_ret r1 = ir_ret r -> ir_put r1 = ir_put r -> ir_left r1 = ir_left r ->
  1 <= is_extra s <= 15 -> 1 <= is_offset s < 2^16 -> is_extra s <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2^64 ->
  0 <= ir_have r1 < 2^32 -> 0 <= ir_next r1 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists x8 x12, ILOOP X (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s))) PC_MATCH x8 x12 ms') ms.
Proof.
  intros X s c r r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL E12 E13 E14 E15 E22 E29 E31 XO HP
         EI EO ER EP EL REX ROFF RB1 RH1 RHV1 RN1 RPUT.
  apply (ILOOPh_regs X s c r r1) in HL; [|assumption..].
  iarm_openh HL. subst x12 x13 x14 x15 x22 x29 x31.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_DISTEXT_J.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r1) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  pose proof (bv_swrap32_range (is_back s)) as RBK. pose proof (sx32_wz_u (is_back s)) as EBK. set (bk := bv_swrap 32 (is_back s)) in *.
  do 4 zs. rewrite EBK. do 4 zs. rewrite clang_mask32 by lia.
  pose proof (land_ones_rng (ir_hold r1) (is_extra s) ltac:(lia)) as RV. set (v := Z.land (ir_hold r1) (Z.ones (is_extra s))) in *.
  assert (RV' : 0 <= v < 32768) by (split; [lia|]; eapply Z.lt_le_trans; [exact (proj2 RV)|]; change 32768 with (2^15); apply Z.pow_le_mono_r; lia).
  clear RV.
  assert (EV : BITSv (ir_hold r1) (is_extra s) = v) by (unfold v; apply BITSv_land; lia).
  do 9 zs. rewrite (land63_small (is_extra s)) by lia.
  itr_groups MUf WMf.
  apply evt_done. eexists _, _. eapply ILOOP_intro; unfold dx_s, dx_r; ired; [ireg .. |].
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; rewrite EV, (wrap32_id (is_offset s + v)) by lia; close_cells GA
                        | unfold isT, isT_cells; exists padT; inorm; close_cells GT; unfold bk; apply le4_back_add
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Lemma distext_core : forall X w q ms,
  ILOOPg X w PC_DISTEXT_E q ms -> sc13 q = wz (is_extra (w_s w)) -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = DISTEXT ->
  evt psegs (fun ms' => IPOST X (arm_DISTEXT ivar_ref w) ms' /\ PATI X (wof (arm_DISTEXT ivar_ref w))) ms.
Proof.
  intros X [s c r] q ms HL E13 E26 XO HW HP HM. cbn [w_s w_c w_r] in *.
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
    { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold MATCH, FLAGS, HCRC; cbn; lia| reflexivity..|]. exact Pisr. }
    eapply (evt_cut psegs (fun ms1 => exists x8 x12, ILOOP X (mkW (iset_mode s MATCH) c r) PC_MATCH x8 x12 ms1)).
    2:{ intros ms1 (x8' & x12' & H1). exact (match_core X _ x8' x12' ms1 H1 XO HW2 HP2 HM2). }
    destruct q as [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30].
    destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
    clear HW HW2 HP2 HCORE HWF HWB Pfl Pgz Pisr POBY RH Rin HP.
    iarm_openg HL. subst x13 x26. ix_open XO. unfold PC_DISTEXT_E.
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
    pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
    open_IST ST. open_isA GA. ifine m.
    zs. rewrite E0. br_true. do 2 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    apply IMEM_intro; inorm;
    [ exists jf; exact FRM | exact STK | exact ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
  - rewrite (arm_DISTEXT_on s c r NE0).
    eapply evt_cut; [exact (distext_nb X s c r q ms HL E13 E26 XO HREGS HP ltac:(lia))|].
    intros ms1 [(r1 & q1 & EN & HR1 & HJ & E12 & E13' & E14 & E15 & E22 & E29 & E31)|(r1 & EN & HR1 & HLV)].
    2:{ rewrite EN. apply evt_done. split; [exact HLV|]. cbn [wof].
        destruct HR1 as [->| ->]; [exact HP| eapply PATI_regs; [exact HP| reflexivity..]]. }
    rewrite EN.
    assert (HN : distext_next (mkW s c r) = Some (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s)))).
    { unfold distext_next. cbn [w_s w_c w_r]. replace (is_extra s =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0). rewrite EN. reflexivity. }
    destruct (distext_next_WINV _ _ HW HM HN) as [HW2 HM2].
    destruct (nb_r1_facts c r r1 (is_extra s) HREGS ltac:(rewrite Pin; exact Pin1) ltac:(lia) HR1) as (EI & EO & ER & EP & EL & RB1 & RH1 & RHV1 & RN1).
    assert (HP2 : PATI X (mkW (iset_mode (dx_s s (ir_hold r1)) MATCH) c (dx_r r1 (is_extra s)))).
    { eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold MATCH, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity|]. exact Pisr. }
    eapply evt_cut.
    { destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
      exact (distext_fin X s c r r1 q1 ms1 HJ E12 E13' E14 E15 E22 E29 E31 XO HP EI EO ER EP EL ltac:(lia) ROFF RB1 RH1 RHV1 RN1 ltac:(lia)). }
    intros ms2 (x8' & x12' & H2). exact (match_core X _ x8' x12' ms2 H2 XO HW2 HP2 HM2).
Qed.

Lemma arm_DISTEXT_ok : forall flush, arm_stmt flush DISTEXT PC_DISTEXT (arm_DISTEXT ivar_ref).
Proof.
  intros flush X [s c r] x12 ms _ HL XO HW _ HP HM. cbn [w_s] in HM.
  eapply (evt_cut psegs (fun ms1 => exists q, ILOOPg X (mkW s c r) PC_DISTEXT_E q ms1 /\ sc13 q = wz (is_extra s) /\ sc26 q = wz (il_NI (ix_L X) + ir_next r))).
  2:{ intros ms1 (q & H1 & E13 & E26). exact (distext_core X _ q ms1 H1 E13 E26 XO HW HP HM). }
  pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF. rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & _ & REX & _).
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s] in GA.
  unfold PC_DISTEXT. do 2 zs.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|]. cbn [sc13 sc26]. split; reflexivity.
Qed.
End Z_infl_a_distext.

Module Z_infl_a_dist1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_c_tab.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_match OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_distext.
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

Definition PC_DIST_J1 : Z := 0x1e5f0.
Definition dist_Q1 (X : ictx) (s : inflate_state) (r1 : iregs) (q : iscrh) : Prop :=
  h12 q = wz (ir_have r1) /\ h13 q = wz (ir_bits r1) /\ h27 q = wz (il_NI (ix_L X) + ir_next r1) /\ h22 q = wz (ir_hold r1)
  /\ h14 q = wz (code_bits (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))))
  /\ h16 q = wz (cp_addr (ix_L X) (is_distcode s) + 4 * dec_idx1 (is_distbits s) (ir_hold r1))
  /\ h15 q = wz (cp_addr (ix_L X) (is_distcode s)) /\ h29 q = wz 30 /\ h31 q = wz (-16180).

Lemma dist_lvl1 : forall X s c r x8 x12 ms,
  ILOOP X (mkW s c r) PC_DIST x8 x12 ms -> ix_ok X -> REGS c r -> PATI X (mkW s c r) ->
  0 <= is_distbits s <= 15 -> cp_ofs_ok (is_distcode s) ->
  dlvl c s (is_distcode s) (dec_idx1 (is_distbits s)) code_bits r ->
  evt psegs (DECJ X s c r r (is_distcode s) (dec_idx1 (is_distbits s)) code_bits PC_DIST_J1 (dist_Q1 X s)) ms.
Proof.
  intros X s c r x8 x12 ms HL XO HREGS HP RN CPO DL.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
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
  do 5 zs. rewrite clang_mask32 by lia. zs. rewrite EI0.
  set (i0 := dec_idx1 n (ir_hold r)) in *. set (e0 := code_at s p i0) in *.
  pose proof (code_bits_range e0) as RB0.
  do 2 zs.
  pose proof (code_rd_bits m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2 + 1)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e0)) by exact RB0. clear RD.
  zs. br_cases K.
  -
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i0; fold e0; lia)) as [ED EC].
    do 3 zs. apply evt_done. left. eexists r, _. split; [exact ED|]. split; [exact EC|]. split; [fold i0; fold e0; lia|]. split; [exact RI0|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold dist_Q1. cbn [h12 h13 h14 h15 h16 h22 h27 h29 h31]. fold p. fold n. fold i0. fold e0. repeat split; try reflexivity.
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia.
  - assert (K' : ir_bits r < code_bits (code_at s p (dec_idx1 n (ir_hold r)))) by (fold i0; fold e0; exact K).
    do 5 zs. br_cases K2.
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
      pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
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
      do 2 zs.
      pose proof (code_rd_bits m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 1)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      fold e1 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e1)) by exact RB1. clear RD.
      do 6 zs. br_cases K3.
      *
        assert (K3' : ir_bits (pullr c r) < code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r))))) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; exact K3).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zs. br_true. do 9 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e1 i1 h1. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| reflexivity..]]; pullr_rw c r; ireg.
      * assert (K3' : code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r)))) <= ir_bits (pullr c r)) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        zs. apply evt_done. left. eexists (pullr c r), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI1|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold dist_Q1. cbn [h12 h13 h14 h15 h16 h22 h27 h29 h31]. fold p. fold n. fold h1. fold i1. fold e1.
        repeat split; try reflexivity; try (pullr_rw c r; ireg).
        f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Definition PC_DIST_T : Z := 0x1e6d4.
Definition dist_QT (X : ictx) (here : Z) (rt : iregs) (B : Z) (q : iscrh) : Prop :=
  h6 q = wz (code_op here) /\ h16 q = wz (code_val here) /\ h14 q = wz (code_bits here) /\ h15 q = wz B
  /\ h13 q = wz (ir_bits rt) /\ h22 q = wz (ir_hold rt) /\ h12 q = wz (ir_have rt) /\ h27 q = wz (il_NI (ix_L X) + ir_next rt)
  /\ h9 q = wz (il_As (ix_L X) + 7160) /\ h29 q = wz 30 /\ h31 q = wz (-16180).

Lemma dist_direct : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J1 q ms -> dist_Q1 X s r1 q -> ix_ok X ->
  0 <= dec_idx1 (is_distbits s) (ir_hold r1) < ctab_size (is_distcode s) -> cp_ofs_ok (is_distcode s) ->
  dist_two (code_op (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))) = false ->
  evt psegs (fun ms' => exists q', ILOOPh X (mkW s c r0) PC_DIST_T q' ms'
                                   /\ dist_QT X (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))) r1 (bv_swrap 32 (is_back s)) q') ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO RI CPO TWO.
  destruct HQ as (E12 & E13 & E27 & E22 & E14 & E16 & E15 & E29 & E31).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x12 x13 x27 x22 x14 x16 x15 x29 x31.
  iarm_openh_keep HL HMEM.
  set (p := is_distcode s) in *. set (i := dec_idx1 (is_distbits s) (ir_hold r1)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_val_range e) as RVAL. pose proof (code_bits_range e) as RBITS.
  assert (K16 : 16 <= code_op e).
  { unfold dist_two in TWO. rewrite (land240_le15 _ ROP) in TWO. apply Z.leb_gt in TWO. lia. }
  open_IST ST. open_isT GT. ix_open XO. unfold PC_DIST_J1.
  pose proof (code_rd_op m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. cbv beta. rewrite (bv8_small (code_op e)) by exact ROP. clear RD.
  pose proof (code_rd_val m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i + 2)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. rewrite (zx16_small (code_val e)) by exact RVAL. clear RD.
  do 3 zs. br_true.
  pose proof (bv_swrap32_range (is_back s)) as RBK. pose proof (sx32_wz_u (is_back s)) as EBK.
  zs. rewrite EBK. zs.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
  unfold dist_QT. cbn [h6 h9 h12 h13 h14 h15 h16 h22 h27 h29 h31]. repeat split; reflexivity.
Qed.

Definition PC_DIST_J2 : Z := 0x1e6a8.
Definition dist_Q2 (X : ictx) (s : inflate_state) (last : Z) (r2 : iregs) (q : iscrh) : Prop :=
  h17 q = wz (ir_have r2) /\ h5 q = wz (ir_bits r2) /\ h30 q = wz (il_NI (ix_L X) + ir_next r2) /\ h22 q = wz (ir_hold r2)
  /\ h7 q = wz (code_bits (code_at s (is_distcode s) (dec_idx2 last (ir_hold r2))))
  /\ h28 q = wz (cp_addr (ix_L X) (is_distcode s) + 4 * dec_idx2 last (ir_hold r2))
  /\ h14 q = wz (code_bits last) /\ h9 q = wz (il_As (ix_L X) + 7160).

Lemma dist_lvl2 : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J1 q ms -> dist_Q1 X s r1 q -> ix_ok X -> PATI X (mkW s c r0) ->
  ir_in r1 = ir_in r0 -> ir_out r1 = ir_out r0 -> ir_put r1 = ir_put r0 -> ir_left r1 = ir_left r0 -> ir_ret r1 = ir_ret r0 ->
  0 <= ir_have r1 <= 1 -> 0 <= ir_next r1 -> ir_next r1 + ir_have r1 = arr_len (ic_input c) -> 0 <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  0 <= dec_idx1 (is_distbits s) (ir_hold r1) < ctab_size (is_distcode s) -> cp_ofs_ok (is_distcode s) ->
  forall last, last = code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)) ->
  dist_two (code_op last) = true -> code_bits last <= ir_bits r1 -> code_bits last + code_op last <= 31 ->
  dlvl c s (is_distcode s) (dec_idx2 last) (dec_need2 last) r1 ->
  evt psegs (DECJ X s c r0 r1 (is_distcode s) (dec_idx2 last) (dec_need2 last) PC_DIST_J2 (dist_Q2 X s last)) ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO HP EI EO EP EL ER
         RHV RNX RNH RB RH Rin RI CPO last ELAST TWO KB K31 DL.
  destruct HQ as (E12 & E13 & E27 & E22 & E14 & E16 & E15 & E29 & E31).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x12 x13 x27 x22 x14 x16 x15 x29 x31.
  iarm_openh_keep HL HMEM.
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  set (p := is_distcode s) in *. set (i := dec_idx1 (is_distbits s) (ir_hold r1)) in *. rewrite <- ELAST in *.
  pose proof (code_op_range last) as ROP. pose proof (code_val_range last) as RVAL. pose proof (code_bits_range last) as RBITS.
  assert (K15 : code_op last <= 15).
  { unfold dist_two in TWO. rewrite (land240_le15 _ ROP) in TWO. apply Z.leb_le in TWO. exact TWO. }
  assert (RH64 : 0 <= ir_hold r1 < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  pose proof (Rin (ir_next r1)) as RBy. apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. ix_open XO. unfold PC_DIST_J1.
  pose proof (code_rd_op m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i)) MI Gc CPO RI eq_refl) as RD.
  rewrite <- ELAST in RD. zs. cbv beta. rewrite (bv8_small (code_op last)) by exact ROP. clear RD.
  pose proof (code_rd_val m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i + 2)) MI Gc CPO RI eq_refl) as RD.
  rewrite <- ELAST in RD. zs. rewrite (zx16_small (code_val last)) by exact RVAL. clear RD.
  do 3 zs. br_false.
  pose proof (ones_range31 (code_bits last + code_op last) ltac:(lia)) as RMK2.
  pose proof (land_ones_le (ir_hold r1) (code_bits last + code_op last) ltac:(lia)) as RHM.
  do 4 zs. rewrite clang_mask32 by lia. set (mk2 := Z.ones (code_bits last + code_op last)) in *.
  zs. set (hm := Z.land (ir_hold r1) mk2) in *.
  pose proof (shiftr_le hm (code_bits last) ltac:(lia) ltac:(lia)) as RSH.
  zs. rewrite (srlw_small hm (code_bits last)) by lia. set (sh := hm ≫ code_bits last) in *.
  do 3 zs. rewrite (zext32_x4 (sh + code_val last)) by lia.
  assert (EI2 : sh + code_val last = dec_idx2 last (ir_hold r1)) by (rewrite dec_idx2_clang by lia; reflexivity).
  rewrite EI2. pose proof (dl_i0 _ _ _ _ _ _ DL) as RI2. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN2.
  set (i2 := dec_idx2 last (ir_hold r1)) in *. set (e2 := code_at s p i2) in *. pose proof (code_bits_range e2) as RB2.
  assert (EN2 : dec_need2 last e2 = code_bits last + code_bits e2) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
  rewrite EN2 in *.
  zs.
  pose proof (code_rd_bits m (ix_L X) s p i2 (wa (cp_addr (ix_L X) p + 4 * i2 + 1)) MI Gc CPO ltac:(lia) eq_refl) as RD.
  fold e2 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e2)) by exact RB2. clear RD.
  do 2 zs. br_cases K.
  -
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i2; fold e2; rewrite EN2; lia)) as [ED EC].
    do 3 zs. apply evt_done. left. eexists r1, _. split; [exact ED|]. split; [exact EC|]. split; [fold i2; fold e2; rewrite EN2; lia|]. split; [exact RI2|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold dist_Q2. cbn [h5 h7 h9 h14 h17 h22 h28 h30]. fold p. fold i2. fold e2. repeat split; reflexivity.
  - assert (K' : ir_bits r1 < dec_need2 last (code_at s p (dec_idx2 last (ir_hold r1)))) by (fold i2; fold e2; rewrite EN2; exact K).
    do 5 zs. br_cases K2.
    +
      assert (H0 : ir_have r1 = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 8 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite ?Z.add_0_r, ?Z.add_0_l.
      apply evt_done. right. exists r1. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| assumption..].
    +
      assert (H1 : ir_have r1 = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI3 RN3].
      assert (NXT : 0 <= ir_next r1 < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r1) _ (wa (il_NI (ix_L X) + ir_next r1)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
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
      do 3 zs. rewrite (zext32_x4 (sh3 + code_val last)) by lia. rewrite EI3.
      set (i3 := dec_idx2 last h2) in *. set (e3 := code_at s p i3) in *. pose proof (code_bits_range e3) as RB3.
      assert (EN3 : dec_need2 last e3 = code_bits last + code_bits e3) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
      rewrite EN3 in *.
      zs.
      pose proof (code_rd_bits m (ix_L X) s p i3 (wa (cp_addr (ix_L X) p + 4 * i3 + 1)) MI Gc CPO ltac:(lia) eq_refl) as RD.
      fold e3 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e3)) by exact RB3. clear RD.
      do 7 zs. br_cases K3.
      *
        assert (K3' : ir_bits (pullr c r1) < dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r1))))) by (fold h2; fold i3; fold e3; rewrite EN3; rewrite pullr_bits by lia; exact K3).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zs. br_true. do 8 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r1). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e3 i3 sh3 hm3 h2. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| assumption..]]; pullr_rw c r1; ireg.
      * assert (K3' : dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r1)))) <= ir_bits (pullr c r1)) by (fold h2; fold i3; fold e3; rewrite EN3; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        zs. apply evt_done. left. eexists (pullr c r1), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI3|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold dist_Q2. cbn [h5 h7 h9 h14 h17 h22 h28 h30]. fold p. fold h2. fold i3. fold e3.
        repeat split; try reflexivity; try (pullr_rw c r1; ireg).
Qed.

Lemma dist_j2 : forall X s c r0 r2 last q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J2 q ms -> dist_Q2 X s last r2 q -> ix_ok X ->
  0 <= dec_idx2 last (ir_hold r2) < ctab_size (is_distcode s) -> cp_ofs_ok (is_distcode s) ->
  code_bits last <= ir_bits r2 <= 63 -> 0 <= ir_hold r2 < 2^64 ->
  evt psegs (fun ms' => exists q', ILOOPh X (mkW s c r0) PC_DIST_T q' ms'
                                   /\ dist_QT X (code_at s (is_distcode s) (dec_idx2 last (ir_hold r2))) (ddrop r2 (code_bits last))
                                              (bv_swrap 32 (is_back s) + code_bits last) q') ms.
Proof.
  intros X s c r0 r2 last [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO RI CPO RB RH.
  destruct HQ as (E17 & E5 & E30 & E22 & E7 & E28 & E14 & E9).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x17 x5 x30 x22 x7 x28 x14 x9.
  iarm_openh_keep HL HMEM.
  set (p := is_distcode s) in *. set (i := dec_idx2 last (ir_hold r2)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_val_range e) as RVAL. pose proof (code_bits_range e) as RBITS.
  pose proof (code_bits_range last) as RLB.
  open_IST ST. open_isT GT. ix_open XO. unfold PC_DIST_J2.
  pose proof (bv_swrap32_range (is_back s)) as RBK. pose proof (sx32_wz_u (is_back s)) as EBK.
  zs. rewrite EBK.
  pose proof (code_rd_op m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. cbv beta. rewrite (bv8_small (code_op e)) by exact ROP. clear RD.
  pose proof (code_rd_val m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i + 2)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. rewrite (zx16_small (code_val e)) by exact RVAL. clear RD.
  do 8 zs. rewrite (land63_small (code_bits last)) by lia.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
  unfold dist_QT, ddrop. cbn [h6 h9 h12 h13 h14 h15 h16 h22 h27 h29 h31 ir_bits ir_hold ir_have ir_next irset_bits irset_hold].
  repeat split; try reflexivity; ireg.
Qed.
End Z_infl_a_dist1.


Module Z_infl_a_dist.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_c_tab.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_match OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_distext OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist1.
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

Definition dt_sb (s : inflate_state) (Bm : Z) : inflate_state := iset_back s Bm.
Definition dt_bad (s : inflate_state) (c : icall) (here : Z) (rt : iregs) (Bm : Z) : iw :=
  mkW (iset_mode (iset_back s Bm) BAD) (icset_msg c MSG_invalid_distance_code) (ddrop rt (code_bits here)).
Definition dt_ok (s : inflate_state) (c : icall) (here : Z) (rt : iregs) (Bm : Z) : iw :=
  mkW (iset_mode (iset_extra (iset_offset (iset_back s Bm) (code_val here)) (Z.land (code_op here) 15)) DISTEXT) c (ddrop rt (code_bits here)).

Lemma dist_tail_walk : forall X s c r0 rt here B Bm q ms,
  ILOOPh X (mkW s c r0) PC_DIST_T q ms -> dist_QT X here rt B q -> ix_ok X -> PATI X (mkW s c r0) ->
  ir_in rt = ir_in r0 -> ir_out rt = ir_out r0 -> ir_ret rt = ir_ret r0 -> ir_put rt = ir_put r0 -> ir_left rt = ir_left r0 ->
  le4 (wz (B + code_bits here)) = le4 (wz Bm) -> - 2^31 <= B < 2^31 + 256 ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  0 <= ir_put r0 <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
     if negb (Z.land (code_op here) 64 =? 0) then exists x8, ILOOP X (dt_bad s c here rt Bm) PC_DISPATCH x8 (wz BAD) ms'
     else exists q', ILOOPg X (dt_ok s c here rt Bm) PC_DISTEXT_E q' ms' /\ sc13 q' = wz (Z.land (code_op here) 15)
                     /\ sc26 q' = wz (il_NI (ix_L X) + ir_next rt)) ms.
Proof.
  intros X s c r0 rt here B Bm [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO HP
         EI EO ER EP EL HB RBv RB RH RHV RNX RPUT.
  destruct HQ as (E6 & E16 & E14 & E15 & E13 & E22 & E12 & E27 & E9 & E29 & E31).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x6 x16 x14 x15 x13 x22 x12 x27 x9 x29 x31.
  apply (ILOOPh_regs X s c r0 rt) in HL; [|assumption..].
  iarm_openh HL.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  pose proof (code_op_range here) as ROP. pose proof (code_val_range here) as RVAL. pose proof (code_bits_range here) as RBITS.
  ix_open XO. unfold PC_DIST_T.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put rt) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT. open_izs ZS.
  pose proof (munch_refl [(il_S (ix_L X), il_S (ix_L X) + 112); (ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168);
                          (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  pose proof (land64_cases (code_op here) ROP) as R64. pose proof (land15_range (code_op here)) as R15.
  do 4 zs. rewrite (land63_small (code_bits here)) by lia.
  do 2 zs. br_cases K.
  -
    replace (Z.land (code_op here) 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    do 8 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; unfold dt_bad, ddrop; ired; [ireg .. |].
    apply IMEM_intro; inorm;
    [ exists jf; exact FRM | exact STK
    | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT; exact HB
                          | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
  - replace (Z.land (code_op here) 64 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
    do 7 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists. split; [eapply ILOOPg_intro; unfold dt_ok, ddrop; ired; [ireg .. |]|cbn [sc13 sc26]; split; reflexivity].
    apply IMEM_intro; inorm;
    [ exists jf; exact FRM | exact STK
    | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT; exact HB
                          | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Lemma cpok_ofs_ok : forall ty codes p root, cpok ty codes p root -> cp_ofs_ok p.
Proof. intros ty codes [ofs| |] root H; cbn in *; [exact (proj1 H)| exact I| exact I]. Qed.

Lemma dist_fin : forall X s c r rt here sb B q ms,
  ILOOPh X (mkW s c r) PC_DIST_T q ms -> dist_QT X here rt B q -> ix_ok X -> WINV (mkW s c r) -> PATI X (mkW s c r) -> is_mode s = DIST ->
  ir_in rt = ir_in r -> ir_out rt = ir_out r -> ir_ret rt = ir_ret r -> ir_put rt = ir_put r -> ir_left rt = ir_left r ->
  (addback sb (code_bits here) = iset_back s (swrap32 (is_back sb + code_bits here))) ->
  le4 (wz (B + code_bits here)) = le4 (wz (swrap32 (is_back sb + code_bits here))) -> - 2^31 <= B < 2^31 + 256 ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  dist_next (mkW s c r) = dist_tailnext s c here rt sb ->
  evt psegs (fun ms' => IPOST X (dist_tail c here rt sb) ms' /\ PATI X (wof (dist_tail c here rt sb))) ms.
Proof.
  intros X s c r rt here sb B q ms HL HQ XO HW HP HM EI EO ER EP EL ESB HB RBv RB RH RHV RNX HN.
  pose proof HW as (_ & HREGS & _). cbn [w_s w_c w_r] in HREGS. destruct HREGS as (_ & _ & _ & Rp & Rl & Rpl & _).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  eapply evt_cut; [exact (dist_tail_walk X s c r rt here B _ q ms HL HQ XO HP EI EO ER EP EL HB RBv RB RH RHV RNX ltac:(lia))|].
  intros ms1 H1. unfold dist_tail. unfold dist_tailnext, dt_s in HN. cbv zeta. rewrite ESB. unfold dt_bad, dt_ok in H1.
  destruct (negb (Z.land (code_op here) 64 =? 0)).
  - destruct H1 as (x8' & H1). apply evt_done. split; [cbn [IPOST]; exists x8'; exact H1|]. cbn [wof].
    eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity|]. exact Pisr.
  - destruct H1 as (q' & H1 & E13 & E26).
    destruct (dist_next_WINV _ _ HW HM HN) as [HW3 HM3].
    refine (distext_core X _ q' ms1 H1 E13 E26 XO HW3 _ HM3).
    eapply PATI_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DISTEXT, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity|]. exact Pisr.
Qed.

Lemma ddrop_facts' : forall r n, 0 <= n <= ir_bits r -> ir_bits r <= 63 -> 0 <= ir_hold r < 2^64 ->
  ir_in (ddrop r n) = ir_in r /\ ir_out (ddrop r n) = ir_out r /\ ir_ret (ddrop r n) = ir_ret r /\ ir_put (ddrop r n) = ir_put r
  /\ ir_left (ddrop r n) = ir_left r /\ ir_bits (ddrop r n) = ir_bits r - n /\ 0 <= ir_hold (ddrop r n) < 2^64
  /\ ir_have (ddrop r n) = ir_have r /\ ir_next (ddrop r n) = ir_next r.
Proof.
  intros r n Hn Hb Hh. unfold ddrop. destruct r; cbn in *. rewrite wrap32_id by lia.
  pose proof (shiftr_le ir_hold n ltac:(lia) ltac:(lia)). repeat split; try reflexivity; lia.
Qed.

Lemma dist_core : forall X w x8 x12 ms,
  ILOOP X w PC_DIST x8 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = DIST ->
  evt psegs (fun ms' => IPOST X (arm_DIST ivar_ref w) ms' /\ PATI X (wof (arm_DIST ivar_ref w))) ms.
Proof.
  intros X [s c r] x8 x12 ms HL XO HW HP HM. cbn [w_s] in HM.
  pose proof (WINV_dist_okb _ HW HM) as OKB. unfold dist_okb in OKB. cbn [w_s w_c w_r] in OKB.
  pose proof HW as (HCORE & HREGS & HMF & _). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & [_ TD] & _).
  pose proof (cpok_ofs_ok _ _ _ _ TD) as CPO.
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  assert (HIN1 : arr_len (ic_input c) <= 1) by (rewrite Pin; exact Pin1).
  pose proof (DREGS_of_REGS c r HREGS HIN1) as DR.
  assert (Rin : forall i, 0 <= arr_get (ic_input c) i < 256) by (destruct HREGS as (_&_&_&_&_&_&_&H&_); exact H).
  destruct (decode_okb_lvl1 _ _ _ _ _ _ OKB) as [RN D1].
  pose proof (dlvl_of_dchk c s _ _ _ r D1 ltac:(destruct DR as (_&H&_); exact H) ltac:(destruct DR as (_&_&_&H&_); lia)) as DL1.
  rewrite arm_DIST_eq. change (DECODE1 (is_distcode s) (is_distbits s)) with (DECODE_k 8 (is_distcode s) (dec_idx1 (is_distbits s)) code_bits).
  eapply evt_cut; [exact (dist_lvl1 X s c r x8 x12 ms HL XO HREGS HP RN CPO DL1)|].
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
  pose proof (code_bits_range last) as RLB.
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
    eapply evt_cut; [exact (dist_j2 X s c r r2 last q2 ms2 HJ2 HQ2 XO RI2 CPO ltac:(lia) RH2)|].
    intros ms3 (q3 & HJ3 & HQ3). fold e2 in HQ3.
    destruct (ddrop_facts' r2 (code_bits last) ltac:(lia) ltac:(lia) RH2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    pose proof (bv_swrap32_range (is_back s)) as RBK.
    refine (dist_fin X s c r (ddrop r2 (code_bits last)) e2 (addback s (code_bits last)) _ q3 ms3 HJ3 HQ3 XO HW HP HM _ _ _ _ _ eq_refl (le4_back_add2 (is_back s) (code_bits last) (code_bits e2)) _ _ F7 _ _ HN0);
      try congruence; try lia.
  -
    eapply evt_cut; [exact (dist_direct X s c r r1 q1 ms1 HJ1 HQ1 XO RI1 CPO TWO)|].
    intros ms3 (q3 & HJ3 & HQ3). fold last in HQ3.
    pose proof (bv_swrap32_range (is_back s)) as RBK.
    refine (dist_fin X s c r r1 last s _ q3 ms3 HJ3 HQ3 XO HW HP HM EI1 EO1 ER1 EP1 EL1 eq_refl (le4_back_add (is_back s) (code_bits last)) _ _ RH1 _ _ HN0); lia.
Qed.

Lemma arm_DIST_ok : forall flush, arm_stmt flush DIST PC_DIST (arm_DIST ivar_ref).
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (dist_core X w _ x12 ms HL XO HW HP HM). Qed.
End Z_infl_a_dist.


Module Z_infl_t_iface.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate RefInflateSafeD RefInflateSafeTY.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition PC_LENLENS_E : Z := 0x1d548.
Definition PC_CODELENS_E : Z := 0x1d694.

Definition lenlens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPg X w PC_LENLENS_E q ms ->
  sc12 q = wz (is_ncode (w_s w)) -> sc15 q = wz (is_have (w_s w)) -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> is_mode (w_s w) = LENLENS ->
  evt psegs (fun ms' => IPOST X (arm_LENLENS ivar_ref flush w) ms' /\ PATI X (wof (arm_LENLENS ivar_ref flush w))) ms.

Definition codelens_core_stmt (flush : Z) : Prop := forall X w q ms,
  ix_flush X = flush -> ILOOPg X w PC_CODELENS_E q ms ->
  sc13 q = wz (is_have (w_s w)) -> sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w)) ->
  ix_ok X -> WINV w -> ATY (w_s w) -> PATI X w -> is_mode (w_s w) = CODELENS ->
  evt psegs (fun ms' => IPOST X (arm_CODELENS ivar_ref flush w) ms' /\ PATI X (wof (arm_CODELENS ivar_ref flush w))) ms.

Definition len__core_stmt : Prop := forall X w x8 x12 ms,
  ILOOP X w PC_LEN_ x8 x12 ms -> ix_ok X -> WINV w -> PATI X w -> is_mode (w_s w) = LEN_ ->
  evt psegs (fun ms' => IPOST X (arm_LEN_ ivar_ref w) ms' /\ PATI X (wof (arm_LEN_ ivar_ref w))) ms.
End Z_infl_t_iface.


Module Z_infl_a_lenlens1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_iface Z_infl_c_defs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_infl_c_tab.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_t_iface.
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

Lemma rod_order : forall m, mem_inv psegs m -> bytes_at psegs m Z_ORDER (u16s (av16 order_a 19)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold Z_ORDER; lia | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma order_rd : forall m i a, mem_inv psegs m -> 0 <= i < 19 -> a = wa (Z_ORDER + 2 * i) ->
  ov_read_bytes psegs m a 2 = Some (le2 (wz (arr_get order_a i))).
Proof.
  intros m i a MI Hi ->. pose proof (rod_order m MI) as Hb.
  pose proof (av16_nth order_a 19 i Hi) as Hn.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i) with (Z.of_nat (2 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read psegs m Z_ORDER _ (2 * Z.to_nat i) 2 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le2; lia).
  rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Ltac st16 ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok psegs _ A (av16 a n) idx (wa (A + 2 * idx)) ARR ltac:(rewrite av16_length; lia) eq_refl) as SOK;
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

Definition PC_LL1_H : Z := 0x1d5a4.
Definition PC_LL1_B : Z := 0x1d574.
Definition PC_LL2 : Z := 0x1d5d4.

Definition ll1_Q (X : ictx) (s : inflate_state) (r : iregs) (q : iscr) : Prop :=
  sc12 q = wz (is_ncode s) /\ sc13 q = wz (Z_ORDER + 2 * is_have s) /\ sc14 q = wz (is_ncode s - is_have s)
  /\ sc15 q = wz (is_have s + 1) /\ sc26 q = wz (il_NI (ix_L X) + ir_next r).

Lemma ll1_head : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LL1_H q ms -> ll1_Q X s r q -> ix_ok X -> DREGS c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) -> PATI X (mkW s c r) ->
  evt psegs (NBJg X s c r 3 PC_LL1_B (fun r1 q1 => ll1_Q X s r1 q1)) ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL (E12 & E13 & E14 & E15 & E26) XO HREGS Rin HP.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x12 x13 x14 x15 x26.
  pose proof HMEM as ((jf & FRM) & _ & _ & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r] in FRM.
  destruct HREGS as (Rn & [Rh HAV] & Rnh & RB & RH).
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
    + eapply ILOOPg_intro; ired; [ireg .. |]. exact HMEM.
    + unfold ll1_Q. cbn [sc12 sc13 sc14 sc15 sc26]. repeat split; reflexivity.
  - zs. br_cases K2.
    +
      assert (H1 : ir_have r = 1) by lia.
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 6 zs. rewrite <- Pin. rewrite !pull_shift by lia. rewrite lor8_small by lia.
      apply evt_done. left. eexists (pullr c r), _. split; [|split; [|split]].
      * apply nb_pull_ok; lia.
      * right. split; [reflexivity| lia].
      * unfold hide in RH. eapply ILOOPg_intro; pullr_rw c r; ired; [ireg .. |]. eapply IMEM_regs; [exact HMEM| reflexivity..].
      * unfold ll1_Q. cbn [sc12 sc13 sc14 sc15 sc26]. pullr_rw c r. repeat split; ireg.
    +
      do 2 zs.
      apply evt_done. right. exists r. split; [|split].
      * apply nb_dry; lia.
      * left. reflexivity.
      * eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
Qed.

Local Ltac close_ll jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| unfold ilens, u16arr; inorm; rewrite ?EV; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma ll1_body : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LL1_B q ms -> ll1_Q X s r q -> ix_ok X -> PATI X (mkW s c r) ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < is_ncode s -> is_ncode s <= 19 ->
  3 <= ir_bits r <= 63 -> 0 <= ir_hold r < 2^64 -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists q',
     if is_ncode s - is_have s - 1 =? 0
     then ILOOPg X (mkW (ll_s s (ir_hold r)) c (ll_r r)) PC_LL2 q' ms' /\ sc15 q' = wz (is_ncode s) /\ sc26 q' = wz (il_NI (ix_L X) + ir_next r)
     else ILOOPg X (mkW (ll_s s (ir_hold r)) c (ll_r r)) PC_LL1_H q' ms' /\ ll1_Q X (ll_s s (ir_hold r)) (ll_r r) q') ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL (E12 & E13 & E14 & E15 & E26) XO HP LL RHV RNC RB RH RPUT.
  iarm_openg HL. subst x12 x13 x14 x15 x26.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL1_B.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  pose proof (order_lt19 (is_have s) ltac:(lia)) as ROR. set (od := arr_get order_a (is_have s)) in *.
  assert (EV : wrap16 (BITSv (ir_hold r) 3) = Z.land (ir_hold r) 7) by (rewrite wrap16_bits3 by lia; rewrite land7_mod; reflexivity).
  pose proof (land7_range (ir_hold r)) as R7. set (v := Z.land (ir_hold r) 7) in *.
  do 2 zs. itr_groups MUf WMf. clear MUf WMf.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  lazymatch goal with MI' : mem_inv psegs ?m1 |- _ =>
    pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m1) as MUf;
    pose proof (wmono_refl psegs m1) as WMf;
    pose proof (order_rd m1 (is_have s) (wa (Z_ORDER + 2 * is_have s)) MI' ltac:(lia) eq_refl) as RD end.
  fold od in RD. zs. rewrite (zx16_small od) by lia. clear RD.
  do 5 zs. replace (od ≪ 1) with (2 * od) by (rewrite Z.shiftl_mul_pow2 by lia; lia). zs.
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) od v ltac:(reflexivity).
  do 2 zs. itr_groups MUf WMf. br_cases K.
  - replace (is_ncode s - is_have s - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    zs. apply evt_done. eexists. (split; [eapply ILOOPg_intro; unfold ll_s, ll_r; ired; [ireg .. |]| cbn [sc15 sc26]; split; reflexivity]).
    close_ll jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV.
  - replace (is_ncode s - is_have s - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. eexists. split; [eapply ILOOPg_intro; unfold ll_s, ll_r; ired; [ireg .. |]|].
    + close_ll jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM EV.
    + unfold ll1_Q, ll_s, ll_r. cbn [sc12 sc13 sc14 sc15 sc26]. ired. rewrite (wrap32_id (is_have s + 1)) by lia. repeat split; ireg.
Qed.

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

Definition LL1POST (X : ictx) (res : ares unit) : machine_state -> Prop :=
  match res with
  | ARun _ w1 => fun ms' => (exists q, ILOOPg X w1 PC_LL2 q ms' /\ sc15 q = wz (is_have (w_s w1)) /\ sc26 q = wz (il_NI (ix_L X) + ir_next (w_r w1)))
                            /\ PATI X w1 /\ 0 <= is_have (w_s w1) <= 19 /\ is_mode (w_s w1) = LENLENS
  | ALeave w' => fun ms' => ILEAVE X w' ms' /\ PATI X w'
  | ARet _ _ => fun _ => False
  end.

Lemma ll1_loop : forall k X s c r q ms,
  ILOOPg X (mkW s c r) PC_LL1_H q ms -> ll1_Q X s r q -> ix_ok X -> DREGS c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  PATI X (mkW s c r) -> is_mode s = LENLENS ->
  arr_len (is_lens s) = 320 -> 0 <= is_have s < is_ncode s -> is_ncode s <= 19 -> is_ncode s - is_have s <= Z.of_nat k ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (LL1POST X (lenlens_while1 k (mkW s c r))) ms.
Proof.
  induction k as [|k IH]; intros X s c r q ms HL HQ XO DR Rin HP HM LL RHV RNC RK RPUT; [cbn [Z.of_nat] in RK; lia|].
  rewrite lenlens_while1_S. replace (is_have s <? is_ncode s) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
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
                      | reflexivity..| |exact Pisr].
    unfold ll_s, ll_r. cbn [is_mode iset_have iset_lens ir_put irset_bits irset_hold]. rewrite HM. reflexivity. }
  eapply evt_cut; [exact (ll1_body X s c r1 q1 ms1 HJ HQ1 XO HP1 LL RHV RNC ltac:(lia) RH1 ltac:(lia))|].
  intros ms2 (q2 & H2).
  assert (EH' : is_have (ll_s s (ir_hold r1)) = is_have s + 1) by (unfold ll_s; cbn [is_have iset_have]; apply wrap32_id; lia).
  assert (EN' : is_ncode (ll_s s (ir_hold r1)) = is_ncode s) by reflexivity.
  destruct (Z.eqb_spec (is_ncode s - is_have s - 1) 0) as [E0|NE0].
  -
    destruct H2 as (H2 & E15 & E26).
    rewrite lenlens_while1_stop by (rewrite EH', EN'; lia). cbn [LL1POST w_s w_r].
    apply evt_done. split; [exists q2; split; [exact H2| split; [rewrite EH'; rewrite E15; f_equal; lia| exact E26]]|].
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

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_ikit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_defs2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_pure2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_defs OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_c_pure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_c_tab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_t_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_infl_a_lenlens.Z_infl_a_lenlens1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Inflate Inftrees ItableModel RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_LENLENS1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateA_CODELENS11.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateSafeOK2 RefInflateSafeOK3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ItableModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeTY OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateArmLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateOkb OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_LENLENS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateA_CODELENS11.RefInflateA_LENLENS2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2.RefInflateSafeOK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateSafeOK3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque inflate_table.

Record iscrk : Type := mkSK {
  k1 : word; k5 : word; k6 : word; k7 : word; k10 : word; k11 : word; k12 : word; k13 : word; k14 : word; k15 : word;
  k16 : word; k17 : word; k27 : word; k28 : word; k29 : word; k30 : word; k31 : word }.

Definition ILOOPk (X : ictx) (w : iw) (pc : Z) (q : iscrk) : machine_state -> Prop :=
  fun ms => exists m,
    ms = MS (mkR (k1 q) (wz (bv_unsigned (ix_sp X) + -224)) (ix_gp X) (ix_tp X) (k5 q) (k6 q) (k7 q) (wz (il_As (ix_L X)))
                 (wz (ir_left (w_r w))) (k10 q) (k11 q) (k12 q) (k13 q) (k14 q) (k15 q) (k16 q) (k17 q)
                 (wz (ir_have (w_r w))) (wz (il_NO (ix_L X) + ir_put (w_r w))) (wz 16209) (wz (-2))
                 (wz (il_As (ix_L X) + 168)) (wz (ir_hold (w_r w))) (wz (ir_bits (w_r w))) (wz 74976)
                 (k27 q) (wz (il_NI (ix_L X) + ir_next (w_r w))) (k28 q) (k29 q) (k30 q) (k31 q))
            (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs)
    /\ IMEM X w m.

Lemma ILOOPk_intro : forall X w pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (ix_sp X) + -224) -> x3 = ix_gp X -> x4 = ix_tp X -> x8 = wz (ir_left (w_r w)) ->
  x9 = wz (ir_have (w_r w)) ->
  x18 = wz (il_NO (ix_L X) + ir_put (w_r w)) -> x19 = wz 16209 -> x20 = wz (-2) -> x21 = wz (il_As (ix_L X) + 168) ->
  x22 = wz (ir_hold (w_r w)) -> x23 = wz (ir_bits (w_r w)) -> x24 = wz 74976 -> x25 = wz (il_As (ix_L X)) ->
  x26 = wz (il_NI (ix_L X) + ir_next (w_r w)) -> F = ix_F X -> fc = ix_fc X ->
  IMEM X w m ->
  ILOOPk X w pc (mkSK x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31)
         (MS (mkR x1 x2 x3 x4 x5 x6 x7 x25 x8 x10 x11 x12 x13 x14 x15 x16 x17 x9 x18 x19 x20 x21 x22 x23 x24 x27 x26 x28 x29 x30 x31)
             F (wz pc) fc None m (seg_rom psegs)).
Proof. intros. subst. unfold ILOOPk. eexists. split; [reflexivity| assumption]. Qed.

Ltac iarm_openk HL :=
  let m := fresh "m" in let jf := fresh "jf" in
  let FRM := fresh "FRM" in let STK := fresh "STK" in let ZS := fresh "ZS" in let ST := fresh "ST" in let IN := fresh "IN" in
  let OUT := fresh "OUT" in let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in
  destruct HL as (m & -> & (jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM);
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU;
  cbn [w_s w_c w_r k1 k5 k6 k7 k10 k11 k12 k13 k14 k15 k16 k17 k27 k28 k29 k30 k31] in *.

Lemma zext32_x2 : forall x, 0 <= x < 4294967296 -> Z.land (x ≪ 32) 18446744073709551615 ≫ 31 = 2 * x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296. change (2^64) with 18446744073709551616. change (2^31) with 2147483648. Z.div_mod_to_equations. lia.
Qed.

Lemma ll_entry : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LENLENS_E q ms ->
  sc12 q = wz (is_ncode s) -> sc15 q = wz (is_have s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  0 <= is_have s < is_ncode s -> is_ncode s <= 19 ->
  evt psegs (fun ms' => exists q', ILOOPg X (mkW s c r) PC_LL1_H q' ms' /\ ll1_Q X s r q') ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E12 E15 E26 RH RN.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x12 x15 x26.
  unfold PC_LENLENS_E.
  do 11 zs. rewrite zext32_x2 by lia. rewrite !land_u32_small by lia.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|].
  unfold ll1_Q. cbn [sc12 sc13 sc14 sc15 sc26]. unfold Z_ORDER. repeat split; ireg.
Qed.

Lemma ll_arm_entry : forall X s c r x8 x12 ms,
  ILOOP X (mkW s c r) PC_LENLENS x8 x12 ms -> 0 <= is_have s < is_ncode s -> is_ncode s <= 19 ->
  evt psegs (fun ms' => exists q, ILOOPg X (mkW s c r) PC_LENLENS_E q ms' /\ sc12 q = wz (is_ncode s) /\ sc15 q = wz (is_have s)
                                  /\ sc26 q = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s c r x8 x12 ms HL RH RN.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM).
  pose proof HMEM as (_ & _ & [_ ST] & _). open_IST ST. open_isA GA. cbn [w_s w_c w_r] in *.
  unfold PC_LENLENS.
  do 3 zs. br_true.
  apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. | exact HMEM]|].
  cbn [sc12 sc15 sc26]. repeat split; reflexivity.
Qed.

Definition PC_LL2_B : Z := 0x1d5fc.
Definition PC_LL2_X : Z := 0x1d620.
Definition PC_LL_CALL : Z := 0x1d624.

Lemma ll2_pre : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LL2 q ms -> sc15 q = wz (is_have s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) -> 0 <= is_have s <= 19 ->
  evt psegs (fun ms' => exists k,
     if is_have s <? 19
     then ILOOPk X (mkW s c r) PC_LL2_B k ms' /\ k10 k = wz 4294967295 /\ k11 k = wz (Z_ORDER + 2 * is_have s) /\ k15 k = wz (is_have s + 1)
     else ILOOPk X (mkW s c r) PC_LL_CALL k ms') ms.
Proof.
  intros X s c r [x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x26 x27 x28 x30] ms HL E15 E26 RH.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r sc5 sc6 sc7 sc8 sc12 sc13 sc14 sc15 sc16 sc17 sc26 sc27 sc28 sc30] in *. subst x15 x26.
  unfold PC_LL2.
  do 3 zs. br_cases K.
  - replace (is_have s <? 19) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. eexists. eapply ILOOPk_intro; ired; [ireg .. | exact HMEM].
  - replace (is_have s <? 19) with true by (symmetry; apply Z.ltb_lt; lia).
    do 7 zs.
    apply evt_done. eexists. split; [eapply ILOOPk_intro; ired; [ireg .. | exact HMEM]|].
    cbn [k10 k11 k15]. unfold Z_ORDER. repeat split; ireg.
Qed.

Local Ltac close_k jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [exact GA| exact GT| unfold ilens, u16arr; inorm; exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma ll2_body : forall X s c r i k ms,
  ILOOPk X (mkW s c r) PC_LL2_B k ms -> k10 k = wz 4294967295 -> k11 k = wz (Z_ORDER + 2 * i) -> k15 k = wz (i + 1) ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i < 19 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists k',
     if i + 1 =? 19
     then ILOOPk X (mkW (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r) PC_LL2_X k' ms' /\ k12 k' = wz 19
     else ILOOPk X (mkW (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r) PC_LL2_B k' ms'
          /\ k10 k' = wz 4294967295 /\ k11 k' = wz (Z_ORDER + 2 * (i + 1)) /\ k15 k' = wz (i + 1 + 1)) ms.
Proof.
  intros X s c r i [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms HL E10 E11 E15 XO HP LL Ri RPUT.
  iarm_openk HL. subst x10 x11 x15.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL2_B.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST.
  pose proof (munch_refl [(il_As (ix_L X) + 168, il_As (ix_L X) + 808)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
  pose proof (order_lt19 i ltac:(lia)) as ROR. set (od := arr_get order_a i) in *.
  unfold ilens, u16arr in Gl. pose proof (av16_zlength (is_lens s) 320 ltac:(lia)) as L16.
  pose proof (order_rd m i (wa (Z_ORDER + 2 * i)) MI ltac:(lia) eq_refl) as RD.
  fold od in RD. zs. rewrite (zx16_small od) by lia. clear RD.
  do 4 zs. replace (od ≪ 1) with (2 * od) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite (land_u32_small (i + 1)) by lia.
  st16 Gl (is_lens s) 320 (il_As (ix_L X) + 168) od 0 ltac:(reflexivity).
  do 3 zs. itr_groups MUf WMf. br_cases K.
  - replace (i + 1 =? 19) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. eexists. split; [eapply ILOOPk_intro; ired; [ireg .. |]|].
    + close_k jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + cbn [k10 k11 k15]. repeat split; ireg.
  - replace (i + 1 =? 19) with true by (symmetry; apply Z.eqb_eq; lia).
    apply evt_done. eexists. split; [eapply ILOOPk_intro; ired; [ireg .. |]| cbn [k12]; reflexivity].
    close_k jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma zlens_19 : forall n a, zlens n a 19 = a.
Proof. intros [|n] a; reflexivity. Qed.

Lemma ll2_loop : forall n X s c r i k ms,
  ILOOPk X (mkW s c r) PC_LL2_B k ms -> k10 k = wz 4294967295 -> k11 k = wz (Z_ORDER + 2 * i) -> k15 k = wz (i + 1) ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= i < 19 -> 19 - i <= Z.of_nat n ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists k', ILOOPk X (mkW (iset_lens s (zlens n (is_lens s) i)) c r) PC_LL2_X k' ms' /\ k12 k' = wz 19) ms.
Proof.
  induction n as [|n IH]; intros X s c r i k ms HL E10 E11 E15 XO HP LL Ri Rn RPUT; [cbn [Z.of_nat] in Rn; lia|].
  cbn [zlens]. replace (i <? 19) with true by (symmetry; apply Z.ltb_lt; lia).
  eapply evt_cut; [exact (ll2_body X s c r i k ms HL E10 E11 E15 XO HP LL Ri RPUT)|].
  intros ms1 (k1 & H1).
  destruct (Z.eqb_spec (i + 1) 19) as [E|NE].
  - rewrite E, zlens_19. apply evt_done. exists k1. exact H1.
  - destruct H1 as (H1 & E10' & E11' & E15').
    refine (IH X (iset_lens s (arr_set (is_lens s) (arr_get order_a i) 0)) c r (i + 1) k1 ms1 H1 E10' E11' E15' XO _ _ _ _ RPUT).
    + exact HP.
    + cbn [is_lens iset_lens]. rewrite arr_len_set. exact LL.
    + lia.
    + rewrite Nat2Z.inj_succ in Rn. lia.
Qed.

Local Ltac close_kA jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma ll2_exit : forall X s c r k ms,
  ILOOPk X (mkW s c r) PC_LL2_X k ms -> k12 k = wz 19 -> ix_ok X -> PATI X (mkW s c r) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists k', ILOOPk X (mkW (iset_have s 19) c r) PC_LL_CALL k' ms') ms.
Proof.
  intros X s c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms HL E12 XO HP RPUT.
  iarm_openk HL. subst x12.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL2_X.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  zs. itr_groups MUf WMf.
  apply evt_done. eexists. eapply ILOOPk_intro; ired; [ireg .. |].
  close_kA jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.

Lemma ll2_walk : forall X s c r q ms,
  ILOOPg X (mkW s c r) PC_LL2 q ms -> sc15 q = wz (is_have s) -> sc26 q = wz (il_NI (ix_L X) + ir_next r) ->
  ix_ok X -> PATI X (mkW s c r) -> arr_len (is_lens s) = 320 -> 0 <= is_have s <= 19 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' => exists k, ILOOPk X (mkW (ll2 19 s) c r) PC_LL_CALL k ms') ms.
Proof.
  intros X s c r q ms HL E15 E26 XO HP LL RH RPUT.
  eapply evt_cut; [exact (ll2_pre X s c r q ms HL E15 E26 RH)|]. intros ms1 (k1 & H1).
  destruct (Z.ltb_spec (is_have s) 19) as [LT|GE].
  - destruct H1 as (H1 & E10 & E11 & E15').
    rewrite (ll2_zlens 19 s) by (cbn; lia).
    eapply evt_cut; [exact (ll2_loop 19 X s c r (is_have s) k1 ms1 H1 E10 E11 E15' XO HP LL ltac:(lia) ltac:(cbn; lia) RPUT)|].
    intros ms2 (k2 & H2 & E12).
    exact (ll2_exit X _ c r k2 ms2 H2 E12 XO HP RPUT).
  - rewrite ll2_stop by lia. apply evt_done. exists k1. exact H1.
Qed.

Definition PC_LL_RET : Z := 0x1d658.

Local Ltac close_A jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists jf; unfold iframe_cells; inorm; close_cells FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                        | unfold iarrs in *; inorm; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma ll_after : forall X s3 c r k ms ret,
  ILOOPk X (mkW s3 c r) PC_LL_RET k ms -> k10 k = wz (ret mod 2 ^ 64) -> (ret = 0 \/ ret = 1 \/ ret = -1) -> ix_ok X ->
  (is_window_blk s3 <> None -> ix_hasw X = true) -> ic_input c = ix_input X -> arr_len (ix_input X) <= 1 ->
  arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode s3 BAD) (icset_msg c MSG_invalid_code_lengths_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else exists q, ILOOPg X (mkW (iset_mode (iset_have s3 0) CODELENS) c (irset_ret r ret)) PC_CODELENS_E q ms'
                   /\ sc13 q = wz 0 /\ sc26 q = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s3 c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms ret HL E10 RRET XO Pwin Pin Pin1 Pout RPUT.
  iarm_openk HL. subst x10.
  ix_open XO. unfold PC_LL_RET.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  assert (RM : 0 <= ret mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  zs. br_cases K.
  -
    assert (R0 : ret = 0) by (destruct RRET as [R|[R|R]]; rewrite R in K; [exact R| |]; exfalso; revert K; vm_compute; discriminate).
    clear RRET K RM. subst ret. cbn [Z.eqb negb].
    do 10 zs. itr_groups MUf WMf.
    apply evt_done. eexists. split; [eapply ILOOPg_intro; ired; [ireg .. |]| cbn [sc13 sc26]; split; reflexivity].
    close_A jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  -
    assert (R1 : (ret =? 0) = false) by (apply Z.eqb_neq; intros R; rewrite R in K; apply K; reflexivity). rewrite R1. cbn [negb].
    clear RRET K.
    do 4 zs. do 5 zs. do 5 zs. do 2 zs. itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; ired; [ireg .. |].
    close_A jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.


Section LLcall.
Variable flush : Z.
Hypothesis CODELENS_CORE : codelens_core_stmt flush.
Hypothesis ITABLE : inflate_table_stmt.

Lemma ll_call : forall X s c r k ms ret tbl nxt lb wk,
  ILOOPk X (mkW s c r) PC_LL_CALL k ms -> ix_ok X -> PATI X (mkW s c r) ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) = (ret, tbl, nxt, lb, wk) ->
  it_safe CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) = true ->
  ATY s -> (forall i, 0 <= i < 19 -> arr_get (is_lens s) i <= 15) ->
  evt psegs (fun ms' =>
    if negb (ret =? 0)
    then exists x8, ILOOP X (mkW (iset_mode (ll_tab s tbl nxt lb wk) BAD) (icset_msg c MSG_invalid_code_lengths_set) (irset_ret r ret)) PC_DISPATCH x8 (wz BAD) ms'
    else exists q, ILOOPg X (mkW (ll_s2 (ll_tab s tbl nxt lb wk)) c (irset_ret r ret)) PC_CODELENS_E q ms'
                   /\ sc13 q = wz 0 /\ sc26 q = wz (il_NI (ix_L X) + ir_next r)) ms.
Proof.
  intros X s c r [x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31] ms ret tbl nxt lb wk HL XO HP RPUT EIT SAFE HA HL15.
  iarm_openk HL.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_LL_CALL.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  do 13 zs. itr_groups MUf WMf. clear MUf WMf.

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
      | cbn [it_codes_ok]; lia
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
  lazymatch type of WMc with wmono _ ?ma _ => itr_groups MUc WMc; transport_after_call psegs ma m' MUc WMc end. clear MUc WMc MI ARRS LAY.
  replace (ret_pc (wz 120408)) with (wz 120408) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  unfold ll_s2.
  eapply (ll_after X (ll_tab s tbl nxt lb wk) c r _ _ ret); [ | | exact RRET | exact XO | exact Pwin | exact Pin | exact Pin1 | exact Pout | exact RPUT].
  { eapply ILOOPk_intro; ired; [ireg .. |].
    apply IMEM_intro; [ exists jf; exact FRM | exact STKc | exact ZS | exact STc | exact IN | exact OUT | exact MIc | exact MU | exact WM ]. }
  reflexivity.
Qed.

Lemma lenlens_core : lenlens_core_stmt flush.
Proof.
  intros X [s c r] q ms EF HL E12 E15 E26 XO HW HA HP HM. cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _ & Rin & _).
  assert (LL : arr_len (is_lens s) = 320) by (destruct HCORE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  assert (HIN1 : arr_len (ic_input c) <= 1) by (rewrite Pin; exact Pin1).
  pose proof (DREGS_of_REGS c r HREGS HIN1) as DR.
  rewrite arm_LENLENS_eq.
  eapply evt_cut; [exact (ll_entry X s c r q ms HL E12 E15 E26 Hh (proj2 Hnc))|]. intros ms1 (q1 & H1 & HQ1).
  eapply evt_cut; [exact (ll1_loop 19 X s c r q1 ms1 H1 HQ1 XO DR Rin HP HM LL Hh (proj2 Hnc) ltac:(cbn; lia) ltac:(lia))|]. intros ms2 H2.
  pose proof (lenlens_facts s c r HW HA HM) as [_ F].
  pose proof (WINV_lenlens_okb s c r HW HA HM) as OKB. unfold lenlens_okb in OKB. cbn [w_s] in OKB.
  pose proof (lenlens_next_WINV s c r HW HA HM) as NXW. unfold lenlens_next in NXW.
  destruct (lenlens_while1 19 (mkW s c r)) as [[] [s1 c1 r1] | w' | rc w']; cbn [LL1POST w_s w_r] in H2.
  2:{ apply evt_done. cbn [IPOST wof]. exact H2. }
  2:{ destruct H2. }
  destruct H2 as ((q2 & HL2 & E15' & E26') & HP1 & Hh1 & HM1).
  destruct F as (-> & lens19 & EL2 & HL19 & HLs19 & HT19 & HC1 & HR1 & HCm1 & Hb1 & Hnl1 & Hnd1 & HWF1 & HWB1 & HA1).
  apply andb_prop in OKB. destruct OKB as [_ OKB]. apply ll_call_ok_sound in OKB. destruct OKB as (CL15 & SAFE & _).
  assert (LL1 : arr_len (is_lens s1) = 320) by (destruct HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & L & _); exact L).
  pose proof HR1 as (Rn1 & Rh1 & Rnh1 & Rp1 & Rl1 & Rpl1 & _).
  pose proof HP1 as (_ & _ & _ & _ & _ & Pwin1 & Pin' & _ & Pout' & _ & Pisr1 & _). cbn [w_s w_c w_r] in *.
  assert (RPUT1 : 0 <= ir_put r1 <= Z.of_nat (length (ix_rest0 X))) by (rewrite <- Pout; lia).
  eapply evt_cut; [exact (ll2_walk X s1 c r1 q2 ms2 HL2 E15' E26' XO HP1 LL1 Hh1 RPUT1)|]. intros ms3 (k3 & H3).
  unfold ll_fin. rewrite EL2 in H3, CL15, SAFE, NXW |- *. cbv zeta in NXW.
  cbn [is_lens is_codes is_work iset_have iset_lens] in CL15, SAFE, NXW |- *.
  destruct (inflate_table CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)) as [[[[ret tbl] nxt] lb] wk] eqn:EIT. cbv zeta.
  assert (Pf1 : is_flags s1 = 0).
  { destruct HP1 as (_ & _ & _ & Pfl1 & _). cbn [w_s w_r] in Pfl1. destruct Pfl1 as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM1 in E; discriminate E. }
  assert (HPA : PATI X (mkW (iset_have (iset_lens s1 lens19) 19) c r1)).
  { eapply PATI_step; [exact HP1| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_have iset_lens]; rewrite HM1; unfold LENLENS, FLAGS, HCRC; lia| reflexivity..| |exact Pisr1].
    cbn [is_mode iset_have iset_lens]. rewrite HM1. reflexivity. }
  assert (HAA : ATY (iset_have (iset_lens s1 lens19) 19)).
  { unfold ATY. cbn [is_lens is_work is_codes iset_have iset_lens]. split; [exact HT19| destruct HA1 as [_ H]; exact H]. }
  eapply evt_cut.
  { eapply (ll_call X (iset_have (iset_lens s1 lens19) 19) c r1 k3 ms3 ret tbl nxt lb wk H3 XO HPA RPUT1);
      cbn [is_lens is_codes is_work iset_have iset_lens]; [exact EIT | exact SAFE | exact HAA | exact CL15]. }
  intros ms4 H4.
  destruct (Z.eqb_spec ret 0) as [R0|R1]; cbn [negb] in H4 |- *.
  -
    destruct H4 as (q4 & HL4 & E13 & E26'').
    specialize (NXW _ eq_refl). destruct NXW as (HW2 & HA2 & HM2).
    refine (CODELENS_CORE X _ q4 ms4 EF HL4 E13 E26'' XO HW2 HA2 _ HM2).
    unfold ll_s2, ll_tab. eapply PATI_step; [exact HPA| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode iset_have]; unfold CODELENS, FLAGS, HCRC; lia| reflexivity..|].
    exact Pisr1.
  -
    destruct H4 as (x8' & HL4).
    apply evt_done. split; [cbn [IPOST]; exists x8'; exact HL4|]. cbn [wof].
    unfold ll_tab. eapply PATI_step; [exact HPA| reflexivity| reflexivity| reflexivity| exact Pf1 | cbn [is_mode iset_mode]; unfold BAD, FLAGS, HCRC; lia| reflexivity..|].
    exact Pisr1.
Qed.

Lemma arm_LENLENS_of : arm_stmt flush LENLENS PC_LENLENS (arm_LENLENS ivar_ref flush).
Proof.
  intros X [s c r] x12 ms EF HL XO HW HA HP HM.
  pose proof HW as (_ & _ & HMF & _). cbn [w_s w_c w_r] in HMF. rewrite HM in HMF. unfold MF in HMF. cbn in HMF.
  destruct HMF as (_ & _ & Hnc & _ & _ & Hh & _).
  eapply evt_cut; [exact (ll_arm_entry X s c r _ x12 ms HL Hh (proj2 Hnc))|]. intros ms1 (q1 & H1 & E12 & E15 & E26).
  exact (lenlens_core X (mkW s c r) q1 ms1 EF H1 E12 E15 E26 XO HW HA HP HM).
Qed.
End LLcall.
