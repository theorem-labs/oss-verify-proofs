(* Model-side facts for the tagged path of case 4 of the ubsan LLVMFuzzerTestOneInput: the world the machine's
   write order leaves against the model's (fuzz/fuzz_transport.c:1108-1120), the signed / unsigned reading of the
   32-bit counters, submit_find_at unrolled once, the inlined coalescable test (:1097), and g_fail_next across
   every write of the arm. No machine here. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells
  Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem
  TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid
  LLVMFuzzerTestOneInput_op4_tag_lib.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- 32-bit counters, signed and unsigned *)

Lemma t4_s32_mod : forall B k, s32_at B k mod 2 ^ 32 = u_at B k 4 mod 2 ^ 32.
Proof.
  intros B k. unfold s32_at, bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma t4_s32_iff : forall B k v, 0 <= v < 2 ^ 31 -> (s32_at B k = v <-> u_at B k 4 = v).
Proof.
  intros B k v Hv.
  pose proof (u_at_range B k 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
  unfold s32_at, bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  split; intros E.
  - destruct (Z.lt_ge_cases (u_at B k 4) (2 ^ 31)) as [H|H].
    + rewrite Z.mod_small in E by lia. lia.
    + rewrite <- (Z.mod_add (u_at B k 4 + 2 ^ 31) (-1) (2 ^ 32)) in E by lia.
      rewrite Z.mod_small in E by lia. lia.
  - rewrite E. rewrite Z.mod_small by lia. lia.
Qed.

Lemma t4_s32_small : forall B k, 0 <= u_at B k 4 < 2 ^ 31 -> s32_at B k = u_at B k 4.
Proof. intros B k H. apply (proj2 (t4_s32_iff B k (u_at B k 4) H)). reflexivity. Qed.

Lemma t4_s32_eqb : forall B k v, 0 <= v < 2 ^ 31 -> (s32_at B k =? v) = (u_at B k 4 =? v).
Proof. intros B k v Hv. apply eq_true_iff_eq. rewrite !Z.eqb_eq. apply t4_s32_iff. exact Hv. Qed.

Lemma t4_put4_cong : forall x y, x mod 2 ^ 32 = y mod 2 ^ 32 -> put 4 x = put 4 y.
Proof. intros x y H. rewrite <- (t4_put4_mod x), <- (t4_put4_mod y), H. reflexivity. Qed.

Lemma t4_put4_s32 : forall B k d, put 4 (s32_at B k + d) = put 4 (u_at B k 4 + d).
Proof.
  intros B k d. apply t4_put4_cong.
  rewrite <- (Zplus_mod_idemp_l (s32_at B k)), <- (Zplus_mod_idemp_l (u_at B k 4)), t4_s32_mod.
  reflexivity.
Qed.

(* ---------------------------------------------------------------- the world the arm writes *)

Lemma t4_gf_upd : forall (X v : list byte) k, length X = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN ->
  (k + Z.of_nat (length v) <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) ->
  g_fail_next (upd X k v) = g_fail_next X.
Proof.
  intros X v k HL Hk Hv Hd. unfold g_fail_next. apply u_at_upd_out.
  - exact Hk.
  - unfold OFF_g_fail_next. lia.
  - change (Z.of_nat 1) with 1. lia.
  - rewrite HL, Z2Nat.id by (unfold W_LEN; lia). exact Hv.
Qed.

Lemma t4_len_upd : forall (X v : list byte) k, length X = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> length (upd X k v) = Z.to_nat W_LEN.
Proof.
  intros X v k HL Hk Hv. rewrite length_upd; [exact HL | exact Hk |].
  rewrite HL, Z2Nat.id by (unfold W_LEN; lia). exact Hv.
Qed.

(* the five writes that record the command (:1108-1112), in the machine's order *)
Lemma t4_cmdw : forall B5 serial key display len cb,
  upd (upd (upd (upd (upd B5 (A_Cmd_st serial) (put 4 1))
                  (A_Cmd_key serial) (put 4 key))
             (A_Cmd_display serial) (put 4 display))
        (A_Cmd_len serial) (put 1 len))
      (A_Cmd_bytes serial) (firstn (Z.to_nat len) cb)
  = t4_Bw B5 serial key display len cb.
Proof. intros. reflexivity. Qed.

(* :1114-1115, the coalescing arm, in the machine's order *)
Lemma t4_coalw : forall Bw q at_ serial,
  upd (upd Bw (A_Cmd_st q) (put 4 3)) (OFF_g_q + 4 * at_) (put 4 serial)
  = set_Q_at (set_Cmd_st Bw q REPLACED) at_ serial.
Proof. intros. reflexivity. Qed.

(* :1117, the append arm: the machine stores g_nq before g_q[nq], the model after; the spans are disjoint *)
Lemma t4_appw : forall Bw nq serial, length Bw = Z.to_nat W_LEN -> 0 <= nq < CMDS_MAX ->
  upd (upd Bw OFF_g_nq (put 4 (nq + 1))) (OFF_g_q + 4 * nq) (put 4 serial)
  = set_g_nq (set_Q_at Bw nq serial) ((nq + 1) mod 2 ^ 32).
Proof.
  intros Bw nq serial HL Hnq. unfold set_g_nq, set_Q_at.
  rewrite (t4_put4_mod (nq + 1)).
  apply upd_upd_comm;
    rewrite ?length_put, ?HL, ?Z2Nat.id;
    unfold OFF_g_nq, OFF_g_q, CMDS_MAX, W_LEN in *; lia.
Qed.

(* :1120, g_ncmd++ read signed and written back *)
Lemma t4_ncmdw : forall B6, upd B6 OFF_g_ncmd (put 4 (s32_at B6 OFF_g_ncmd + 1))
  = set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32).
Proof.
  intros B6. unfold set_g_ncmd, g_ncmd.
  rewrite (t4_put4_mod (u_at B6 OFF_g_ncmd 4 + 1)). rewrite t4_put4_s32. reflexivity.
Qed.

(* the first len bytes of the struct are the first len bytes of its 24 command bytes *)
Lemma t4_firstn_cs : forall B1 D c3 display key, length (t4_cb B1 D c3) = 24%nat -> 3 <= t4_len D c3 <= 24 ->
  firstn (Z.to_nat (t4_len D c3)) (t4_cs B1 D c3 display key)
  = firstn (Z.to_nat (t4_len D c3)) (t4_cb B1 D c3).
Proof.
  intros B1 D c3 display key L H. unfold t4_cs, cmd_struct.
  rewrite firstn_app. replace (Z.to_nat (t4_len D c3) - length (t4_cb B1 D c3))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

(* ---------------------------------------------------------------- submit_find_at *)

Lemma t4_findat_step : forall f B key i,
  submit_find_at (S f) B key i =
    (if i <? g_nq B then
       if CMDS_MAX <=? i then None
       else if CMDS_MAX <=? Q_at B i then None
       else if Cmd_key B (Q_at B i) =? key then Some i
       else submit_find_at f B key (i + 1)
     else Some (-1)).
Proof. intros. reflexivity. Qed.

Lemma t4_findat_rng : forall f B key i j, 0 <= i -> submit_find_at f B key i = Some j ->
  (i <= j < CMDS_MAX \/ j = -1).
Proof.
  induction f as [|f IH]; intros B key i j Hi H; cbn [submit_find_at] in H; [discriminate H|].
  destruct (i <? g_nq B); [|injection H as <-; right; reflexivity].
  destruct (Z.leb_spec CMDS_MAX i) as [E|E]; [discriminate H|].
  destruct (CMDS_MAX <=? Q_at B i); [discriminate H|].
  destruct (Cmd_key B (Q_at B i) =? key).
  - injection H as <-. left. lia.
  - destruct (IH B key (i + 1) j ltac:(lia) H) as [HR|HR]; [left; lia | right; exact HR].
Qed.

(* ---------------------------------------------------------------- the inlined coalescable test *)

Lemma t4_mask16 : forall x m, 0 <= x -> 0 <= m ->
  Z.land x (Z.shiftl m 16) = Z.shiftl (Z.land (Z.shiftr x 16) m) 16.
Proof.
  intros x m Hx Hm. rewrite Z.shiftl_land.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 16) as [H|H].
  - rewrite (Z.shiftl_spec_low m 16 i) by lia. rewrite !andb_false_r. reflexivity.
  - rewrite (Z.shiftl_spec (Z.shiftr x 16) 16 i) by lia. rewrite Z.shiftr_spec by lia.
    replace (i - 16 + 16) with i by lia. reflexivity.
Qed.

Lemma t4_land_mod : forall y m, 0 <= y -> 0 <= m < 256 -> Z.land (y mod 256) m = Z.land y m.
Proof.
  intros y m Hy Hm.
  replace (y mod 256) with (Z.land y 255)
    by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; reflexivity).
  rewrite <- Z.land_assoc. f_equal.
  rewrite Z.land_comm. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

Lemma t4_f7 : forall k, 0 <= k < 256 -> (Z.land k 247 = 0 <-> (k = 0 \/ k = 8)).
Proof.
  intros k Hk. split.
  - intros H.
    assert (E7 : Z.land k 7 = 0).
    { change 7 with (Z.land 247 7) at 1. rewrite Z.land_assoc, H. reflexivity. }
    assert (E240 : Z.land k 240 = 0).
    { change 240 with (Z.land 247 240) at 1. rewrite Z.land_assoc, H. reflexivity. }
    assert (EK : k = Z.land k 15).
    { replace k with (Z.land k 255) at 1
        by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
      change 255 with (Z.lor 240 15). rewrite Z.land_lor_distr_r, E240, Z.lor_0_l. reflexivity. }
    assert (R : 0 <= Z.land k 15 < 16).
    { rewrite Z.land_comm. change 16 with (2 ^ 4). apply land_lt_pow2; [cbn; lia | lia]. }
    assert (M8 : k mod 8 = 0).
    { rewrite <- E7. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. }
    rewrite <- EK in R. lia.
  - intros [E|E]; rewrite E; reflexivity.
Qed.

Lemma t4_coal0 : forall key, 0 <= key < 2 ^ 32 ->
  (h_coalescable_m key = 0 <-> (Z.land key 16187392 = 0 \/ Z.land key 16711680 = 589824)).
Proof.
  intros key Hk.
  assert (HS : 0 <= Z.shiftr key 16) by (apply Z.shiftr_nonneg; lia).
  set (k := Z.shiftr key 16 mod 256).
  assert (HKR : 0 <= k < 256) by (unfold k; apply Z.mod_pos_bound; lia).
  assert (E1 : Z.land key 16187392 = Z.shiftl (Z.land k 247) 16).
  { change 16187392 with (Z.shiftl 247 16). rewrite (t4_mask16 key 247) by lia.
    unfold k. rewrite (t4_land_mod (Z.shiftr key 16) 247) by lia. reflexivity. }
  assert (E2 : Z.land key 16711680 = Z.shiftl k 16).
  { change 16711680 with (Z.shiftl 255 16). rewrite (t4_mask16 key 255) by lia.
    unfold k. f_equal. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. }
  rewrite E1, E2. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536.
  unfold h_coalescable_m, b2z, SPEC_KEY_INPUT, SPEC_KEY_KEEPALIVE.
  change (Z.shiftr key 16 mod 2 ^ 8) with k.
  split.
  - intros H.
    destruct (Z.eqb_spec k 0) as [E|E]; cbn [negb andb] in H.
    { left. rewrite E. reflexivity. }
    destruct (Z.eqb_spec k 8) as [E8|E8]; cbn [negb andb] in H.
    { left. rewrite E8. reflexivity. }
    destruct (Z.eqb_spec k 9) as [E9|E9]; cbn [negb andb] in H; [|discriminate H].
    right. lia.
  - intros [H|H].
    + assert (HL : Z.land k 247 = 0) by lia.
      apply (proj1 (t4_f7 k HKR)) in HL. destruct HL as [E|E]; rewrite E; reflexivity.
    + assert (E9 : k = 9) by lia. rewrite E9. reflexivity.
Qed.
