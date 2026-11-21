(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs Z_infl_pure Z_infl_pure2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_MATCH1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition hide (P : Prop) : Prop := P.

(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

Lemma land64_zero_iff : forall x, - 2^63 <= x < 2^63 -> (Z.land x 18446744073709551615 = 0 <-> x = 0).
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2^63) with 9223372036854775808 in H. change (2^64) with 18446744073709551616. split; intros E; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Lemma sx32_wz_u : forall x, sx32 (wz x) = wz (bv_swrap 32 x).
Proof.
  intros x. unfold sx32. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.div].
  change (4294967296 / 2) with 2147483648. Z.div_mod_to_equations. lia.
Qed.

Lemma bv_swrap32_sub_land : forall a b, bv_swrap 32 (Z.land (bv_swrap 32 a) 18446744073709551615 - b) = bv_swrap 32 (a - b).
Proof.
  intros a b. apply bv_swrap32_eqm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296. change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
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
(* [comment removed for export] *)
Lemma le4_back_add : forall b e, le4 (wz (bv_swrap 32 b + e)) = le4 (wz (swrap32 (b + e))).
Proof.
  intros b e. apply le4_wz_mod. rewrite Z_to_bv_unsigned. unfold swrap32, two31. rewrite wrap32_mod.
  unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma le4_swrap32_r : forall x, le4 (wz x) = le4 (wz (swrap32 x)).
Proof.
  intros x. apply le4_wz_mod. rewrite Z_to_bv_unsigned. unfold swrap32, two31. rewrite wrap32_mod.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (2^32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
