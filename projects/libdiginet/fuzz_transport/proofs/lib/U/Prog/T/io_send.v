From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import io_send_c spec_read_frame_c tagged_of_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import check_sent_frame_c check_ack_frame_c check_latest_control_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import check_inflight_retry_c check_state_wake_c check_inflight_new_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import check_latest_frame_c check_keepalive_due_c check_latest_sent_c check_latest_display_c.
Import ListNotations.
Open Scope Z_scope.

(* ================ 1. bitwise and word helpers ================ *)

Lemma is_land_pow2 : forall n x y, 0 <= n -> 0 <= x < 2 ^ n -> 0 <= Z.land x y < 2 ^ n.
Proof.
  intros n x y Hn Hx.
  assert (NN : 0 <= Z.land x y) by (apply Z.land_nonneg; left; lia).
  assert (E : Z.land x y = Z.land x y mod 2 ^ n).
  { rewrite <- Z.land_ones by lia.
    rewrite (Z.land_comm x y), <- Z.land_assoc, Z.land_ones by lia.
    rewrite (Z.mod_small x) by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (Z.land x y) (2 ^ n) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
Qed.

Lemma is_lor_pow2 : forall n x y, 0 <= n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lor x y < 2 ^ n.
Proof.
  intros n x y Hn Hx Hy.
  assert (NN : 0 <= Z.lor x y) by (apply (proj2 (Z.lor_nonneg x y)); lia).
  assert (E : Z.lor x y = Z.lor x y mod 2 ^ n).
  { rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
    rewrite !Z.mod_small by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (Z.lor x y) (2 ^ n) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
Qed.

Lemma is_lor_neg : forall a b, a < 0 \/ b < 0 -> Z.lor a b < 0.
Proof.
  intros a b H. destruct (Z_lt_le_dec (Z.lor a b) 0) as [L|L]; [lia|].
  apply (proj1 (Z.lor_nonneg a b)) in L. lia.
Qed.

Lemma is_lnot_lor : forall a b, - Z.lor a b - 1 = Z.land (- a - 1) (- b - 1).
Proof.
  intros a b. apply Z.bits_inj'. intros n Hn.
  replace (- Z.lor a b - 1) with (Z.lnot (Z.lor a b)) by (unfold Z.lnot; lia).
  replace (- a - 1) with (Z.lnot a) by (unfold Z.lnot; lia).
  replace (- b - 1) with (Z.lnot b) by (unfold Z.lnot; lia).
  rewrite Z.land_spec, !Z.lnot_spec by lia. rewrite Z.lor_spec. apply negb_orb.
Qed.

Lemma is_lor_s32 : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 -> -2^31 <= Z.lor a b < 2^31.
Proof.
  intros a b Ha Hb.
  destruct (Z_le_gt_dec 0 a) as [A|A]; destruct (Z_le_gt_dec 0 b) as [B|B].
  - pose proof (is_lor_pow2 31 a b ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - pose proof (is_lor_neg a b ltac:(lia)).
    pose proof (is_lnot_lor a b) as D. rewrite Z.land_comm in D.
    pose proof (is_land_pow2 31 (- b - 1) (- a - 1) ltac:(lia) ltac:(lia)). lia.
  - pose proof (is_lor_neg a b ltac:(lia)).
    pose proof (is_lnot_lor a b) as D.
    pose proof (is_land_pow2 31 (- a - 1) (- b - 1) ltac:(lia) ltac:(lia)). lia.
  - pose proof (is_lor_neg a b ltac:(lia)).
    pose proof (is_lnot_lor a b) as D.
    pose proof (is_land_pow2 31 (- a - 1) (- b - 1) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma is_signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite unsigned_lit_wrap.
  assert (E : bv_swrap 64 (z mod 2^64) = bv_swrap 64 z).
  { unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2^64). rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite E. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63). lia.
Qed.

Lemma is_lts_lit : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_lts. rewrite !is_signed_lit by assumption. reflexivity. Qed.

Lemma is_ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma is_eqb_lit : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb.
  assert (K : forall z, -2^63 <= z < 2^63 -> bv_unsigned (Z_to_bv 64 z) = if z <? 0 then z + 2^64 else z).
  { intros z Hz. rewrite unsigned_lit_wrap. destruct (Z.ltb_spec z 0).
    - rewrite <- (Z.mod_add z 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
    - apply Z.mod_small. lia. }
  rewrite !K by assumption.
  destruct (Z.eqb_spec a b) as [->|N].
  - destruct (Z.ltb_spec b 0); rewrite !Z.eqb_refl; reflexivity.
  - replace (a =? b) with false by (symmetry; apply Z.eqb_neq; exact N).
    apply Z.eqb_neq. destruct (Z.ltb_spec a 0); destruct (Z.ltb_spec b 0); lia.
Qed.

Lemma is_swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma is_put_swrap32 : forall v, put 4 (bv_swrap 32 v) = put 4 v.
Proof.
  intros v. unfold put.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_swrap 32 v) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 v 32) by (cbn; lia).
  f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

(* ================ 2. bytes_at helpers ================ *)

Lemma is_ba_skipn : forall m a bs k, 0 <= k -> (Z.to_nat k <= length bs)%nat ->
  bytes_at rsegs m a bs -> bytes_at rsegs m (a + k) (skipn (Z.to_nat k) bs).
Proof.
  intros m a bs k Hk Hl H.
  rewrite <- (firstn_skipn (Z.to_nat k) bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  replace (a + Z.of_nat (Z.to_nat k)) with (a + k) in H by lia. exact H.
Qed.

Lemma is_ba_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n H. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H. tauto.
Qed.

Lemma is_ba_det : forall m a u v, bytes_at rsegs m a u -> bytes_at rsegs m a v -> length u = length v -> u = v.
Proof.
  intros m a u v (_ & _ & Hu) (_ & _ & Hv) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length u)) as [Hi|Hi].
  - rewrite <- Hu by lia. rewrite <- Hv by lia. reflexivity.
  - rewrite (proj2 (nth_error_None u i)) by lia. rewrite (proj2 (nth_error_None v i)) by lia. reflexivity.
Qed.

Lemma is_rwc_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

(* ================ 3. struct spec_frame bytes ================ *)

Lemma is_u_at_app_r : forall (u v : list byte) k n, Z.of_nat (length u) <= k ->
  u_at (u ++ v) k n = u_at v (k - Z.of_nat (length u)) n.
Proof.
  intros u v k n H. unfold u_at, sub. f_equal.
  rewrite skipn_app, skipn_all2 by lia. cbn [app]. do 2 f_equal. lia.
Qed.

Lemma is_skipn0 : forall (l : list byte), skipn (Z.to_nat 0) l = l.
Proof. intros l. reflexivity. Qed.

Lemma is_firstn_app_all : forall (l1 l2 : list byte) n, length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
  intros l1 l2 n <-. induction l1 as [|x l1 IH]; cbn [length firstn app]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma is_u_at_put_hd : forall w v (u : list byte), u_at (put w v ++ u) 0 w = v mod 2 ^ (8 * Z.of_nat w).
Proof.
  intros w v u. unfold u_at, sub. rewrite is_skipn0.
  rewrite (is_firstn_app_all (put w v) u w (length_put w v)).
  apply bytes_le_to_Z_put.
Qed.

Lemma is_length_sfb : forall fa f, length (sf_bytes fa f) = 80%nat.
Proof.
  intros fa f. unfold sf_bytes.
  rewrite !length_app, !length_put, !repeat_length. reflexivity.
Qed.

Ltac is_fld :=
  unfold sf_bytes;
  repeat (rewrite is_u_at_app_r by (rewrite ?length_put, ?repeat_length; cbn; lia));
  match goal with
  | |- context [u_at (put ?w ?v ++ ?u) ?k ?w] => replace k with 0 by (rewrite ?length_put, ?repeat_length; cbn; lia)
  end;
  rewrite is_u_at_put_hd; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul].

(* ================ 4. spec_read_frame field facts ================ *)

Lemma is_byte_at_range : forall (l : list byte) i, 0 <= byte_at (zs l) i < 256.
Proof.
  intros l i. unfold byte_at, zs.
  destruct (nth_in_or_default (Z.to_nat i) (map bv_unsigned l) 0) as [Hin|E].
  - apply in_map_iff in Hin. destruct Hin as (x & <- & _). pose proof (bz_range x). unfold bz in *. lia.
  - rewrite E. lia.
Qed.

Lemma is_be16_range : forall (l : list byte) p, 0 <= spec_be16 (zs l) p < 2^16.
Proof. intros l p. unfold spec_be16, u16. pose proof (Z.mod_pos_bound (Z.lor (Z.shiftl (byte_at (zs l) p) 8) (byte_at (zs l) (p + 1))) 65536 ltac:(lia)). lia. Qed.

Lemma is_be32_range : forall (l : list byte) p, 0 <= spec_be32 (zs l) p < 2^32.
Proof.
  intros l p. unfold spec_be32, u32.
  pose proof (is_byte_at_range l (p + 3)).
  pose proof (Z.mod_pos_bound (Z.shiftl (byte_at (zs l) p) 24) (2^32) ltac:(lia)).
  pose proof (Z.mod_pos_bound (Z.shiftl (byte_at (zs l) (p + 1)) 16) (2^32) ltac:(lia)).
  pose proof (Z.mod_pos_bound (Z.shiftl (byte_at (zs l) (p + 2)) 8) (2^32) ltac:(lia)).
  apply is_lor_pow2; [lia | lia |].
  apply is_lor_pow2; [lia | lia |].
  apply is_lor_pow2; lia.
Qed.

Lemma is_sum_range : forall b p n, 0 <= spec_sum_at b p n < 2^16.
Proof. intros b p n. unfold spec_sum_at, u16. pose proof (Z.mod_pos_bound (spec_sum_loop b p 0 0 (Z.to_nat n)) 65536 ltac:(lia)). lia. Qed.

Lemma is_rf_ranges : forall fr,
  -2^31 <= sf_code (rf fr) < 2^31 /\ 0 <= sf_ethertype (rf fr) < 2^16 /\
  0 <= sf_numbytes (rf fr) < 2^16 /\ 0 <= sf_sum (rf fr) < 2^16 /\ 0 <= sf_retry (rf fr) < 2^16 /\
  0 <= sf_send (rf fr) < 2^32 /\ 0 <= sf_ack (rf fr) < 2^32 /\ 0 <= sf_cmd (rf fr) < 2^8 /\
  0 <= sf_ncmds (rf fr) < 2^8 /\ 0 <= sf_body_sum (rf fr) < 2^16 /\
  0 <= sf_dst (rf fr) <= 6 /\ 0 <= sf_src (rf fr) <= 6 /\ 0 <= sf_body (rf fr) <= 30 /\
  0 <= sf_body_len (rf fr) < 2^16 /\ 0 <= sf_pad_len (rf fr) <= Z.of_nat (length fr).
Proof.
  intros fr. unfold rf, spec_read_frame. cbv zeta.
  pose proof (is_be16_range fr 12). pose proof (is_be16_range fr SPEC_AT_NUMBYTES).
  pose proof (is_be16_range fr SPEC_AT_SUM). pose proof (is_be16_range fr SPEC_AT_RETRY).
  pose proof (is_be32_range fr SPEC_AT_SEND). pose proof (is_be32_range fr SPEC_AT_ACK).
  pose proof (is_byte_at_range fr SPEC_AT_CMD). pose proof (is_byte_at_range fr SPEC_AT_NCMDS).
  pose proof (is_sum_range (zs fr) SPEC_BODY_AT (spec_be16 (zs fr) SPEC_AT_NUMBYTES - SPEC_HDR)).
  destruct (Z.of_nat (length fr) <? SPEC_BODY_AT) eqn:E1.
  { cbn [sf_code sf_dst sf_src sf_ethertype sf_numbytes sf_sum sf_retry sf_send sf_ack sf_cmd sf_ncmds
         sf_body sf_body_len sf_pad_len sf_body_sum]. unfold SPEC_E_SHORT. lia. }
  destruct (negb (spec_be16 (zs fr) 12 =? SPEC_ETHERTYPE)) eqn:E2.
  { cbn [sf_code sf_dst sf_src sf_ethertype sf_numbytes sf_sum sf_retry sf_send sf_ack sf_cmd sf_ncmds
         sf_body sf_body_len sf_pad_len sf_body_sum]. unfold SPEC_E_ETHERTYPE. lia. }
  destruct ((spec_be16 (zs fr) SPEC_AT_NUMBYTES <? SPEC_HDR)
            || (Z.of_nat (length fr) - SPEC_ETH_HDR <? spec_be16 (zs fr) SPEC_AT_NUMBYTES)) eqn:E3.
  { cbn [sf_code sf_dst sf_src sf_ethertype sf_numbytes sf_sum sf_retry sf_send sf_ack sf_cmd sf_ncmds
         sf_body sf_body_len sf_pad_len sf_body_sum]. unfold SPEC_E_LENGTH. lia. }
  apply orb_false_iff in E3. destruct E3 as [E3a E3b].
  apply Z.ltb_ge in E3a. apply Z.ltb_ge in E3b. apply Z.ltb_ge in E1.
  cbn [sf_code sf_dst sf_src sf_ethertype sf_numbytes sf_sum sf_retry sf_send sf_ack sf_cmd sf_ncmds
       sf_body sf_body_len sf_pad_len sf_body_sum].
  unfold SPEC_OK, SPEC_MAC, SPEC_BODY_AT, SPEC_HDR, SPEC_ETH_HDR in *. lia.
Qed.

Lemma is_rf_ok : forall fr, sf_code (rf fr) = SPEC_OK ->
  sf_dst (rf fr) = 0 /\ sf_src (rf fr) = SPEC_MAC /\ sf_body (rf fr) = SPEC_BODY_AT /\
  SPEC_BODY_AT + sf_body_len (rf fr) <= Z.of_nat (length fr) /\ SPEC_BODY_AT <= Z.of_nat (length fr).
Proof.
  intros fr H. revert H. unfold rf, spec_read_frame. cbv zeta.
  destruct (Z.of_nat (length fr) <? SPEC_BODY_AT) eqn:E1.
  { cbn [sf_code]. unfold SPEC_E_SHORT, SPEC_OK. lia. }
  destruct (negb (spec_be16 (zs fr) 12 =? SPEC_ETHERTYPE)) eqn:E2.
  { cbn [sf_code]. unfold SPEC_E_ETHERTYPE, SPEC_OK. lia. }
  destruct ((spec_be16 (zs fr) SPEC_AT_NUMBYTES <? SPEC_HDR)
            || (Z.of_nat (length fr) - SPEC_ETH_HDR <? spec_be16 (zs fr) SPEC_AT_NUMBYTES)) eqn:E3.
  { cbn [sf_code]. unfold SPEC_E_LENGTH, SPEC_OK. lia. }
  apply orb_false_iff in E3. destruct E3 as [E3a E3b].
  apply Z.ltb_ge in E3a. apply Z.ltb_ge in E3b. apply Z.ltb_ge in E1.
  cbn [sf_code sf_dst sf_src sf_body sf_body_len].
  intros _. unfold SPEC_BODY_AT, SPEC_HDR, SPEC_ETH_HDR, SPEC_MAC in *. lia.
Qed.

(* ================ 5. what the checks keep of the world below g_cmd ================ *)

Definition is_keep (B B' : list byte) : Prop :=
  length B' = length B /\
  forall q n, 0 <= q -> q + Z.of_nat n <= OFF_g_cmd -> sub B' q n = sub B q n.

Lemma is_keep_refl : forall B, is_keep B B.
Proof. intros B. split; [reflexivity|]. intros; reflexivity. Qed.

Lemma is_keep_trans : forall B1 B2 B3, is_keep B1 B2 -> is_keep B2 B3 -> is_keep B1 B3.
Proof.
  intros B1 B2 B3 [L1 H1] [L2 H2]. split; [lia|].
  intros q n Hq Hn. rewrite (H2 q n Hq Hn), (H1 q n Hq Hn). reflexivity.
Qed.

Lemma is_keep_upd : forall B k v, OFF_g_cmd <= k -> k + Z.of_nat (length v) <= Z.of_nat (length B) ->
  is_keep B (upd B k v).
Proof.
  intros B k v Hk Hl. unfold OFF_g_cmd in Hk. split.
  - apply length_upd; lia.
  - intros q n Hq Hn. apply sub_upd_out; unfold OFF_g_cmd in *; lia.
Qed.

Lemma is_tof : forall B b n B' t, tagged_of_m B b n = Some (B', t) ->
  B' = B /\ match t with Some s => 0 <= s < CMDS_MAX | None => True end.
Proof.
  intros B b n B' t H. unfold tagged_of_m in H.
  destruct (n <? 3); [inversion H; subst; split; [reflexivity | exact I]|].
  destruct (length b <? 1)%nat; [discriminate|].
  destruct (negb (at8 b 0 =? TAG)); [inversion H; subst; split; [reflexivity | exact I]|].
  destruct (length b <? 3)%nat; [discriminate|].
  destruct (Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7) <? g_ncmd B) eqn:E5.
  - destruct (CMDS_MAX <=? Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7)) eqn:E6; [discriminate|].
    inversion H; subst. split; [reflexivity|].
    apply Z.leb_gt in E6. split; [|exact E6].
    apply (proj2 (Z.lor_nonneg _ _)). split; [apply at8_range|].
    rewrite Z.shiftl_nonneg. apply at8_range.
  - inversion H; subst. split; [reflexivity | exact I].
Qed.

Lemma is_qrl : forall fuel B s nq i k B' k', 0 <= k -> k <= i ->
  length B = Z.to_nat W_LEN -> q_remove_loop fuel B s nq i k = Some (B', k') -> is_keep B B'.
Proof.
  induction fuel as [|fuel IH]; intros B s nq i k B' k' Hk Hki HL H; cbn in H; [discriminate|].
  destruct (i <? nq) eqn:E1.
  - destruct (CMDS_MAX <=? i) eqn:E2; [discriminate|].
    apply Z.leb_gt in E2. unfold CMDS_MAX in E2.
    destruct (Q_at B i =? s) eqn:E3.
    + exact (IH B s nq (i + 1) k B' k' Hk ltac:(lia) HL H).
    + assert (K1 : is_keep B (set_Q_at B k (Q_at B i))).
      { unfold set_Q_at. apply is_keep_upd.
        - unfold OFF_g_cmd, OFF_g_q. lia.
        - rewrite length_put, HL. unfold W_LEN, OFF_g_q. lia. }
      assert (L1 : length (set_Q_at B k (Q_at B i)) = Z.to_nat W_LEN)
        by (destruct K1 as [L1 _]; rewrite L1; exact HL).
      eapply is_keep_trans; [exact K1|].
      exact (IH (set_Q_at B k (Q_at B i)) s nq (i + 1) (k + 1) B' k' ltac:(lia) ltac:(lia) L1 H).
  - inversion H; subst. apply is_keep_refl.
Qed.

Lemma is_qr : forall B s B' u, length B = Z.to_nat W_LEN -> q_remove_m B s = Some (B', u) -> is_keep B B'.
Proof.
  intros B s B' u HL H. unfold q_remove_m in H.
  destruct (q_remove_loop (S (Z.to_nat CMDS_MAX)) B s (g_nq B) 0 0) as [[B1 k1]|] eqn:E; [|discriminate].
  inversion H; subst B'.
  pose proof (is_qrl (S (Z.to_nat CMDS_MAX)) B s (g_nq B) 0 0 B1 k1 ltac:(lia) ltac:(lia) HL E) as K1.
  eapply is_keep_trans; [exact K1|].
  unfold set_g_nq. apply is_keep_upd.
  - unfold OFF_g_cmd, OFF_g_nq. lia.
  - rewrite length_put. destruct K1 as [L1 _]. rewrite L1, HL. unfold W_LEN, OFF_g_nq. lia.
Qed.

Lemma is_lsl : forall fuel B body len pos disp B' d, length B = Z.to_nat W_LEN ->
  latest_sent_loop fuel B body len pos disp = Some (B', d) -> is_keep B B'.
Proof.
  induction fuel as [|fuel IH]; intros B body len pos disp B' d HL H; cbn in H; [discriminate|].
  destruct (pos <? len) eqn:E1; [|inversion H; subst; apply is_keep_refl].
  destruct (tagged_of_m B (skipn (Z.to_nat pos) body) (len - pos)) as [[B0 t]|] eqn:E2; [|discriminate].
  pose proof (is_tof _ _ _ _ _ E2) as [-> Ht].
  destruct t as [s|]; [|discriminate].
  destruct (negb (Cmd_st B s =? PENDING) || (len - pos <? Cmd_len B s)
            || negb (beq_bytes (firstn (Z.to_nat (Cmd_len B s)) (skipn (Z.to_nat pos) body))
                      (sub B (A_Cmd_bytes s) (Z.to_nat (Cmd_len B s))))); [discriminate|].
  destruct (q_remove_m (set_Cmd_st B s SENT) s) as [[B2 u]|] eqn:E4; [|discriminate].
  assert (K1 : is_keep B (set_Cmd_st B s SENT)).
  { unfold set_Cmd_st. apply is_keep_upd.
    - unfold A_Cmd_st, OFF_g_cmd. lia.
    - rewrite length_put, HL. unfold A_Cmd_st, OFF_g_cmd, W_LEN, CMDS_MAX in *. lia. }
  assert (L1 : length (set_Cmd_st B s SENT) = Z.to_nat W_LEN) by (destruct K1 as [L1 _]; rewrite L1; exact HL).
  pose proof (is_qr _ _ _ _ L1 E4) as K2.
  assert (L2 : length B2 = Z.to_nat W_LEN) by (destruct K2 as [L2 _]; rewrite L2; exact L1).
  eapply is_keep_trans; [exact K1|]. eapply is_keep_trans; [exact K2|].
  eapply IH; [ exact L2 | exact H ].
Qed.

Lemma is_cls_keep : forall B body len B' disp, length B = Z.to_nat W_LEN ->
  check_latest_sent_m B body len = Some (B', disp) -> is_keep B B'.
Proof. intros B body len B' disp HL H. unfold check_latest_sent_m in H. eapply is_lsl; eassumption. Qed.

Lemma is_lsl_disp : forall fuel B body len pos disp B' d, -2^31 <= disp < 2^31 ->
  latest_sent_loop fuel B body len pos disp = Some (B', d) -> -2^31 <= d < 2^31.
Proof.
  induction fuel as [|fuel IH]; intros B body len pos disp B' d Hd H; cbn in H; [discriminate|].
  destruct (pos <? len) eqn:E1; [|inversion H; subst; exact Hd].
  destruct (tagged_of_m B (skipn (Z.to_nat pos) body) (len - pos)) as [[B0 t]|] eqn:E2; [|discriminate].
  destruct t as [s|]; [|discriminate].
  destruct (negb (Cmd_st B s =? PENDING) || (len - pos <? Cmd_len B s)
            || negb (beq_bytes (firstn (Z.to_nat (Cmd_len B s)) (skipn (Z.to_nat pos) body))
                      (sub B (A_Cmd_bytes s) (Z.to_nat (Cmd_len B s))))); [discriminate|].
  destruct (q_remove_m (set_Cmd_st B s SENT) s) as [[B2 u]|] eqn:E4; [|discriminate].
  eapply IH; [|exact H]. apply is_lor_s32; [exact Hd | apply s32_range].
Qed.

Lemma is_cls_disp : forall B body len B' disp, check_latest_sent_m B body len = Some (B', disp) ->
  -2^31 <= disp < 2^31.
Proof.
  intros B body len B' disp H. unfold check_latest_sent_m in H.
  eapply is_lsl_disp; [|exact H]. lia.
Qed.

(* ================ 6. the struct spec_frame the walk sees ================ *)

Lemma is_swrap32_mod : forall x, bv_swrap 32 (x mod 2^32) = bv_swrap 32 x.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma is_sframe : forall m fp fa f, 0 < fp -> fp mod 8 = 0 ->
  bytes_at rsegs m fp (sf_bytes fa f) ->
  -2^31 <= sf_code f < 2^31 -> 0 <= sf_ethertype f < 2^16 -> 0 <= sf_numbytes f < 2^16 ->
  0 <= sf_sum f < 2^16 -> 0 <= sf_retry f < 2^16 -> 0 <= sf_send f < 2^32 -> 0 <= sf_ack f < 2^32 ->
  0 <= sf_cmd f < 2^8 -> 0 <= sf_ncmds f < 2^8 -> 0 <= sf_body_sum f < 2^16 ->
  0 <= sf_body_len f < 2^64 -> 0 <= sf_pad_len f < 2^64 ->
  0 <= sf_ptr fa f (sf_dst f) < 2^64 -> 0 <= sf_ptr fa f (sf_src f) < 2^64 ->
  0 <= sf_ptr fa f (sf_body f) < 2^64 ->
  sframe_at m fp fa f.
Proof.
  intros m fp fa f Hfp H8 HB Hcode Het Hnb Hsum Hret Hsend Hack Hcmd Hncmds Hbsum Hblen Hpad Hdst Hsrc Hbody.
  unfold sframe_at. split; [exact Hfp|]. split; [exact H8|].
  exists (sf_bytes fa f). split; [exact HB|]. split; [apply is_length_sfb|].
  repeat split;
    first [ (unfold s32_at; is_fld; rewrite is_swrap32_mod; apply is_swrap32_small; lia)
          | (is_fld; apply Z.mod_small; lia) ].
Qed.

Lemma is_csf : forall B frame B' u, check_sent_frame_m B frame = Some (B', u) ->
  B' = B /\ sf_code (rf frame) = SPEC_OK.
Proof.
  intros B frame B' u H. unfold check_sent_frame_m in H.
  destruct (negb (sf_code (rf frame) =? SPEC_OK)
            || negb (beq_bytes (sub frame (sf_src (rf frame)) 6) HOST)
            || negb (truth (M_desk_known B))
            || negb (beq_bytes (sub frame (sf_dst (rf frame)) 6) (M_desk B))
            || (0 <=? spec_system_at (zs (skipn (Z.to_nat (sf_body (rf frame))) frame))
                        (sf_body_len (rf frame)))) eqn:E; [discriminate|].
  destruct (negb (Z.of_nat (length frame) =?
              (if SPEC_BODY_AT + sf_body_len (rf frame) <? SPEC_MIN_FRAME then SPEC_MIN_FRAME
               else SPEC_BODY_AT + sf_body_len (rf frame)))
            || negb (forallb (fun x => bz x =? 0)
                       (skipn (Z.to_nat (SPEC_BODY_AT + sf_body_len (rf frame))) frame))
            || negb (sf_sum (rf frame) =?
                     (if Cfg_sum_mode B =? DIGINET_SUM_ZERO then 0
                      else spec_sum_at (zs frame) (sf_body (rf frame)) (sf_body_len (rf frame)))));
    [discriminate|].
  inversion H. split; [reflexivity|].
  apply orb_false_iff in E; destruct E as [E _].
  apply orb_false_iff in E; destruct E as [E _].
  apply orb_false_iff in E; destruct E as [E _].
  apply orb_false_iff in E; destruct E as [E _].
  apply negb_false_iff in E. apply Z.eqb_eq in E. exact E.
Qed.

(* ================ 7. world reads and writes of io_send, by name ================ *)

Lemma is_r_now : forall B, u_at B 65000 8 = g_now B.           Proof. reflexivity. Qed.
Lemma is_r_retries : forall B, u_at B 108 4 = M_fly_retries B. Proof. reflexivity. Qed.
Lemma is_r_ka : forall B, u_at B 65048 4 = Cfg_keepalive_ms B. Proof. reflexivity. Qed.

Lemma is_w_fail : forall B v, upd B 64968 (put 1 v) = set_g_fail_next B v.      Proof. reflexivity. Qed.
Lemma is_w_lastc : forall B v, upd B 64976 (put 4 v) = set_g_last_counter B v.  Proof. reflexivity. Qed.
Lemma is_w_acks : forall B v, upd B 65288 (put 4 v) = set_GOT_acks B v.         Proof. reflexivity. Qed.
Lemma is_w_e2 : forall B v, upd B 65280 (put 4 v) = set_GOT_e2 B v.             Proof. reflexivity. Qed.
Lemma is_w_e3 : forall B v, upd B 65284 (put 4 v) = set_GOT_e3 B v.             Proof. reflexivity. Qed.
Lemma is_w_retries : forall B v, upd B 108 (put 4 v) = set_M_fly_retries B v.   Proof. reflexivity. Qed.
Lemma is_w_flysent : forall B v, upd B 112 (put 8 v) = set_M_fly_sent B v.      Proof. reflexivity. Qed.
Lemma is_w_hostc : forall B v, upd B 84 (put 4 v) = set_M_host_counter B v.     Proof. reflexivity. Qed.
Lemma is_w_nextka : forall B v, upd B 48 (put 8 v) = set_M_next_ka B v.         Proof. reflexivity. Qed.
Lemma is_w_lastd : forall B v, upd B 64 (put 8 v) = set_M_last_display B v.     Proof. reflexivity. Qed.
Lemma is_w_dsent : forall B v, upd B 72 (put 4 v) = set_M_display_sent B v.     Proof. reflexivity. Qed.
Lemma is_w_flyon : forall B v, upd B 96 (put 4 v) = set_M_fly_on B v.           Proof. reflexivity. Qed.
Lemma is_w_flycmd : forall B v, upd B 100 (put 1 v) = set_M_fly_cmd B v.        Proof. reflexivity. Qed.
Lemma is_w_flycnt : forall B v, upd B 104 (put 4 v) = set_M_fly_counter B v.    Proof. reflexivity. Qed.
Lemma is_w_flylen : forall B v, upd B 1640 (put 8 v) = set_M_fly_len B v.       Proof. reflexivity. Qed.
Lemma is_w_flyfr : forall B v, upd B 120 v = set_M_fly_frame B v.               Proof. reflexivity. Qed.

(* ================ 8. splitting the walk's own stack frame ================ *)

Lemma is_rwc_split : forall m A A2 cs1 cs2, A2 = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m A2 cs2.
Proof.
  intros m A A2 cs1 cs2 -> [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2.
  rewrite cells_size_app in Hw. destruct Hw as (Ha & Hl & Hww).
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hww. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hww. lia.
Qed.

Lemma is_carve4 : forall m A junk (n1 n2 n3 n4 : nat) (A1 A2 A3 : Z),
  A1 = A + Z.of_nat n1 -> A2 = A + Z.of_nat (n1 + n2)%nat -> A3 = A + Z.of_nat (n1 + n2 + n3)%nat ->
  rw_cells rsegs m A [CB (n1 + n2 + n3 + n4)%nat junk] ->
  exists j1 j2 j3 j4,
    rw_cells rsegs m A [CB n1 j1] /\ rw_cells rsegs m A1 [CB n2 j2] /\
    rw_cells rsegs m A2 [CB n3 j3] /\ rw_cells rsegs m A3 [CB n4 j4].
Proof.
  intros m A junk n1 n2 n3 n4 A1 A2 A3 -> -> -> H0.
  apply (rw_cells_split_CB rsegs m A [] (n1 + n2 + n3 + n4)%nat junk [] [n1;n2;n3;n4]%nat) in H0;
    [| cbn [sum_nat]; lia].
  cbn [app mk_CB_cells] in H0.
  destruct (is_rwc_split m A (A + Z.of_nat n1) [CB n1 (firstn n1 junk)] _
              ltac:(cbn [cells_size csize]; lia) H0) as [Ha Hb].
  destruct (is_rwc_split m (A + Z.of_nat n1) (A + Z.of_nat (n1 + n2)%nat)
              [CB n2 (firstn n2 (skipn n1 junk))] _
              ltac:(cbn [cells_size csize]; lia) Hb) as [Hc Hd].
  destruct (is_rwc_split m (A + Z.of_nat (n1 + n2)%nat) (A + Z.of_nat (n1 + n2 + n3)%nat)
              [CB n3 (firstn n3 (skipn n2 (skipn n1 junk)))] _
              ltac:(cbn [cells_size csize]; lia) Hd) as [He Hf].
  exists (firstn n1 junk), (firstn n2 (skipn n1 junk)), (firstn n3 (skipn n2 (skipn n1 junk))),
         (firstn n4 (skipn n3 (skipn n2 (skipn n1 junk)))).
  split; [exact Ha|]. split; [exact Hc|]. split; [exact He|]. exact Hf.
Qed.

(* The three low pieces of the frame given back to the stack: [S - 160, S - 64). *)
Lemma is_lowrel : forall m lo S cs0 cs1 bs,
  stk rsegs m lo (S + -160) -> lo <= S + -160 ->
  rw_cells rsegs m (S + -160) cs0 -> cells_size cs0 = 12%nat ->
  rw_cells rsegs m (S + -148) cs1 -> cells_size cs1 = 4%nat ->
  bytes_at rsegs m (S + -144) bs -> wr_at rsegs m (S + -144) 80 -> length bs = 80%nat ->
  stk rsegs m lo (S + -64).
Proof.
  intros m lo S cs0 cs1 bs ST HL R0 L0 R1 L1 BB WW LB.
  pose proof (stk_release rsegs m lo _ cs0 ST R0 HL) as ST1. rewrite L0 in ST1.
  replace (S + -160 + Z.of_nat 12) with (S + -148) in ST1 by lia.
  pose proof (stk_release rsegs m lo _ cs1 ST1 R1 ltac:(lia)) as ST2. rewrite L1 in ST2.
  replace (S + -148 + Z.of_nat 4) with (S + -144) in ST2 by lia.
  assert (R2 : rw_cells rsegs m (S + -144) [CB 80 bs]).
  { split; [split|].
    - cbn [cells_wf cell_wf]. split; [exact LB | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BB.
    - cbn [cells_size csize Nat.add]. exact WW. }
  pose proof (stk_release rsegs m lo _ _ ST2 R2 ltac:(lia)) as ST3.
  cbn [cells_size csize Nat.add] in ST3.
  replace (S + -144 + Z.of_nat 80) with (S + -64) in ST3 by lia. exact ST3.
Qed.

(* ================ 9. small facts the branches use ================ *)

(* 0x14ad8-0x14ae0: slli s3,s3,63; srai a0,s3,63; andi a0,a0,-5 with s3 = g_fail_next (0 or 1) *)
Lemma is_retv : forall f, 0 <= f <= 1 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 f)) 63))) 63)))
                     18446744073709551611)
  = Z_to_bv 64 (if truth f then - EIO else 0).
Proof.
  intros f Hf. assert (E : f = 0 \/ f = 1) by lia.
  destruct E as [ -> | -> ]; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma is_int_inc : forall x y, int_inc x = Some y -> x <> INT_MAX /\ y = x + 1.
Proof.
  intros x y H. unfold int_inc in H. destruct (Z.eqb_spec x INT_MAX); [discriminate|].
  injection H as <-. split; [assumption | reflexivity].
Qed.

Lemma is_addiw1 : forall g, -2^31 <= g < 2^31 - 1 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 g) + 1)) = Z_to_bv 64 (g + 1).
Proof.
  intros g Hg. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

Lemma is_put4_congr : forall x y, x mod 2^32 = y mod 2^32 -> put 4 x = put 4 y.
Proof.
  intros x y H. unfold put.
  rewrite <- (Z_to_le_bytes_mod 4 x 32) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 4 y 32) by (cbn; lia).
  rewrite H. reflexivity.
Qed.

Lemma is_put8_congr : forall x y, x mod 2^64 = y mod 2^64 -> put 8 x = put 8 y.
Proof.
  intros x y H. unfold put.
  rewrite <- (Z_to_le_bytes_mod 8 x 64) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 8 y 64) by (cbn; lia).
  rewrite H. reflexivity.
Qed.

Lemma is_u_at1 : forall (l : list byte) (k : Z), 0 <= k -> (Z.to_nat k < length l)%nat ->
  u_at l k 1 = at8 (skipn (Z.to_nat k) l) 0.
Proof.
  intros l k Hk H. unfold u_at, sub, at8, bz.
  destruct (skipn (Z.to_nat k) l) as [|x rest] eqn:E.
  - exfalso. apply (f_equal (@length byte)) in E. rewrite length_skipn in E. cbn [length] in E. lia.
  - cbn [firstn nth bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

(* A stack range survives a callee that wrote exactly [X, X + n) and left its bytes there (memcpy), even when the
   range reaches below the world. *)
Lemma is_stk_fill : forall m m' lo hi X n src,
  stk rsegs m lo hi -> munch [(X, X + n)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' X [CB (Z.to_nat n) src] -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi X n src (H1 & H2 & H) MU WM [[Hwf (HXa & HXl & HB)] _].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LS _].
  cbn [cells_bytes cbytes] in HXl, HB. rewrite app_nil_r in HXl, HB.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw [b Hb]]. split; [apply WM; exact Hw|].
  destruct (Z_le_gt_dec X a) as [L1|L1]; [destruct (Z_lt_le_dec a (X + n)) as [L2|L2]|].
  - replace (wa a) with (wa (X + Z.of_nat (Z.to_nat (a - X)))) by (f_equal; lia).
    rewrite HB by (rewrite LS; lia).
    destruct (nth_error src (Z.to_nat (a - X))) eqn:N; [eexists; reflexivity|].
    apply nth_error_None in N. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia | exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia | exact I].
Qed.

(* the frame in flight, fuzz_transport.c:883-889 (io_send_m's fly) *)
Definition is_fly (frame : list byte) (Bx : list byte) : list byte :=
  let f := rf frame in
  let len := Z.of_nat (length frame) in
  let flen := if len <? SPEC_MAX_FRAME then len else SPEC_MAX_FRAME in
  set_M_fly_frame (set_M_fly_len (set_M_fly_sent (set_M_fly_retries (set_M_fly_counter
    (set_M_fly_cmd (set_M_fly_on Bx 1) (sf_cmd f)) (sf_send f)) 0) (g_now Bx)) flen)
    (firstn (Z.to_nat flen) frame).

(* the facts about the walk's memory at a program point: footprint, stack, world, the four stack pieces, the
   frame bytes *)
Definition is_fr (m0 m4 : word -> option byte) (sp : word) (lo : Z) (B4 : list byte) (p : Z)
    (frame j0 : list byte) (cs1 : list cell) (SB : list byte) (P3cs : list cell) : Prop :=
  munch [(bv_unsigned sp - 288, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m4 /\
  wmono rsegs m0 m4 /\ mem_inv rsegs m4 /\ stk rsegs m4 lo (bv_unsigned sp + -160) /\ wmem rsegs m4 B4 /\
  rw_cells rsegs m4 (bv_unsigned sp + -160) [CB 12 j0] /\ rw_cells rsegs m4 (bv_unsigned sp + -148) cs1 /\
  bytes_at rsegs m4 (bv_unsigned sp + -144) SB /\ wr_at rsegs m4 (bv_unsigned sp + -144) 80 /\
  rw_cells rsegs m4 (bv_unsigned sp + -64) P3cs /\ bytes_at rsegs m4 p frame.

(* After a callee that wrote the world above g_s (check_latest_sent): the frame bytes are back, either because
   they lie off the world and off the callee's footprint, or because they lie in g_s, which the callee kept. *)
Lemma is_frame_back : forall (m0 m1 : word -> option byte) (B0 B1 : list byte) p (frame : list byte) (W : list ivl),
  bytes_at rsegs m0 p frame -> wmem rsegs m0 B0 -> wmem rsegs m1 B1 -> is_keep B0 B1 -> munch W m0 m1 ->
  ((p + Z.of_nat (length frame) <= 209664 \/ 275280 <= p) -> disjoint_from W p (Z.of_nat (length frame))) ->
  (p + Z.of_nat (length frame) <= 209664 \/ 275280 <= p) \/
    (211312 <= p /\ p + Z.of_nat (length frame) <= 229576) ->
  bytes_at rsegs m1 p frame.
Proof.
  intros m0 m1 B0 B1 p frame W BF W0 W1 [KL KS] MU DJ AT.
  destruct AT as [A|A].
  - eapply bytes_at_transport; [exact BF | exact MU | exact (DJ A)].
  - pose proof (wm_len rsegs W_BASE_UBSAN m0 B0 W0) as L0.
    assert (LW : Z.of_nat (length B0) = 65616) by (rewrite L0; vm_compute; reflexivity).
    set (k := p - 209664).
    assert (S0 : bytes_at rsegs m0 p (sub B0 k (length frame))).
    { apply (wm_src rsegs W_BASE_UBSAN m0 B0 k (length frame) p W0);
        [ unfold k, W_BASE_UBSAN; lia | unfold k; lia | unfold k, W_LEN; lia ]. }
    assert (E0 : frame = sub B0 k (length frame)).
    { apply (is_ba_det m0 p); [exact BF | exact S0 |]. rewrite length_sub; [reflexivity | unfold k; lia | unfold k; lia]. }
    assert (E1 : sub B1 k (length frame) = sub B0 k (length frame)) by (apply KS; unfold k, OFF_g_cmd; lia).
    rewrite E0. rewrite <- E1.
    apply (wm_src rsegs W_BASE_UBSAN m1 B1 k (length frame) p W1);
      [ unfold k, W_BASE_UBSAN; lia | unfold k; lia | unfold k, W_LEN; lia ].
Qed.

Definition is_ka (frame : list byte) : bool :=
  (sf_body_len (rf frame) =? 1) && (at8 (skipn (Z.to_nat (sf_body (rf frame))) frame) 0 =? 0)
  && (sf_ncmds (rf frame) =? 1).

Lemma is_cl_range : forall fuel B body blen pos cmds c, 0 <= cmds < 2^32 ->
  cmds_loop fuel B body blen pos cmds = Some c -> 0 <= c < 2^32.
Proof.
  induction fuel as [|fuel IH]; intros B body blen pos cmds c Hc H; cbn in H; [discriminate|].
  destruct (pos <? blen); [|injection H as <-; exact Hc].
  destruct (tagged_of_m B (skipn (Z.to_nat pos) body) (blen - pos)) as [[B0 t]|]; [|discriminate].
  destruct t as [s|]; cbv beta iota in H;
    [ destruct (Cmd_len B s =? 0) | destruct (blen - pos =? 0) ]; try discriminate;
    (eapply IH; [|exact H]; unfold u32; apply Z.mod_pos_bound; lia).
Qed.

(* the world / memory hypotheses after a step, by name *)
Ltac is_wname X :=
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB (Z.to_nat W_LEN) _] |- _ => rename H into X end.
Ltac is_mname X := lazymatch goal with H : mem_inv rsegs ?mm |- _ => rename mm into X end.
(* destruct the head option match of a model equation *)
Ltac is_dmp H nB E :=
  lazymatch type of H with
  | match ?X with Some _ => _ | None => _ end = _ =>
      destruct X as [[nB []]|] eqn:E; cbv beta iota in H; [|discriminate H]
  end.
(* 0x14a10-0x14a14: seqz a2,a0; and a2,a2,s5 with a0 = g_raw, s5 = the keepalive flag *)
Lemma is_seqz_and : forall g (k : bool), -2^63 <= g < 2^63 ->
  Z_to_bv 64 (Z.land (bv_unsigned (v_sltiu (Z_to_bv 64 g) 1)) (bv_unsigned (Z_to_bv 64 (b2z k))))
  = Z_to_bv 64 (b2z (negb (truth g) && k)).
Proof.
  intros g k Hg. rewrite v_sltiu_b2z. f_equal.
  assert (E : (bv_unsigned (Z_to_bv 64 g) <? bv_wrap 64 1) = (g =? 0)).
  { rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
    destruct (Z.eqb_spec g 0) as [->|N]; [reflexivity|].
    apply Z.ltb_ge. destruct (Z_lt_le_dec g 0).
    - rewrite <- (Z.mod_add g 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
    - rewrite Z.mod_small by lia. lia. }
  rewrite E. unfold truth. rewrite negb_involutive.
  destruct (g =? 0); destruct k; reflexivity.
Qed.

(* 0x14b10-0x14b14: addi a0,a0,-1; seqz s5,a0 with a0 = f.ncmds *)
Lemma is_seqz_dec : forall n, 0 <= n < 256 -> v_sltiu (Z_to_bv 64 (n + -1)) 1 = Z_to_bv 64 (b2z (n =? 1)).
Proof.
  intros n Hn. rewrite v_sltiu_b2z. f_equal. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec n 1) as [->|N]; [reflexivity|].
  destruct (Z.eqb_spec n 0) as [->|N0]; [reflexivity|].
  rewrite Z.mod_small by lia. replace (n + -1 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* 0x149a8-0x149b4: snez a2,a2; seqz a3,a0; xor a2,a2,a3; beqz a2 with a2 = f.body, a0 = f.body + at, both non-NULL *)
Lemma is_ptrchk : forall a b, 0 < a < 2^64 -> 0 < b < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 a)))
                             (bv_unsigned (v_sltiu (Z_to_bv 64 b) 1))))
         (Z_to_bv 64 0) = false.
Proof.
  intros a b Ha Hb. rewrite v_sltu_b2z, v_sltiu_b2z.
  rewrite (unsigned_lit 0), (unsigned_lit a), (unsigned_lit b) by lia.
  replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? bv_wrap 64 1) with false by (symmetry; apply Z.ltb_ge; change (bv_wrap 64 1) with 1; lia).
  reflexivity.
Qed.

(* 0x149c4: andi a1,a0,3 with a0 = &g_cmd[s] = W_BASE_UBSAN + A_Cmd_st s (the ubsan alignment check of struct tagged) *)
Lemma is_tret : forall s, tagged_of_ret (Some s) = 229576 + 40 * s.
Proof. intros s. unfold tagged_of_ret, A_Cmd_st, W_BASE_UBSAN, OFF_g_cmd. lia. Qed.

Lemma is_al4 : forall s, 0 <= s < 1024 -> Z.land (bv_unsigned (Z_to_bv 64 (229576 + 40 * s))) 3 = 0.
Proof.
  intros s Hs. rewrite unsigned_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
  apply Z.mod_divide; [lia|]. exists (57394 + 10 * s). lia.
Qed.

Lemma is_eqb_ulit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma is_swrap32_mod64 : forall x, bv_swrap 32 (x mod 2^64) = bv_swrap 32 x.
Proof.
  intros x. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite (Z.mod_eq x (2^64)) by lia.
  replace (x - 2^64 * (x / 2^64) + bv_half_modulus 32)
    with ((x + bv_half_modulus 32) + (- (2^32 * (x / 2^64))) * 2^32) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma is_sx32_small : forall d, -2^31 <= d < 2^31 -> sx32 (Z_to_bv 64 d) = Z_to_bv 64 d.
Proof.
  intros d Hd. unfold sx32. f_equal. rewrite unsigned_lit_wrap, is_swrap32_mod64.
  apply is_swrap32_small. exact Hd.
Qed.

(* one round of the command count loop *)
Lemma is_cl_step : forall fuel B body blen pos cmds r, pos < blen ->
  cmds_loop (S fuel) B body blen pos cmds = Some r ->
  exists B0 t, tagged_of_m B (skipn (Z.to_nat pos) body) (blen - pos) = Some (B0, t) /\
    (match t with Some s => Cmd_len B s | None => blen - pos end) <> 0 /\
    cmds_loop fuel B body blen (pos + match t with Some s => Cmd_len B s | None => blen - pos end)
      (u32 (cmds + 1)) = Some r.
Proof.
  intros fuel B body blen pos cmds r Hp H. cbn [cmds_loop] in H.
  rewrite (proj2 (Z.ltb_lt pos blen) Hp) in H. cbv beta iota zeta in H.
  destruct (tagged_of_m B (skipn (Z.to_nat pos) body) (blen - pos)) as [[B0 t]|] eqn:E;
    cbv beta iota zeta in H; [|discriminate H].
  exists B0, t. split; [reflexivity|].
  destruct t as [s|]; cbv beta iota in H |- *;
    [ destruct (Cmd_len B s =? 0) eqn:Z0 | destruct (blen - pos =? 0) eqn:Z0 ]; try discriminate H;
    (split; [apply Z.eqb_neq; exact Z0 | exact H]).
Qed.

Lemma is_cl_end : forall fuel B body blen pos cmds r, blen <= pos ->
  cmds_loop fuel B body blen pos cmds = Some r -> r = cmds.
Proof.
  intros fuel B body blen pos cmds r Hp H. destruct fuel as [|fuel]; cbn [cmds_loop] in H; [discriminate H|].
  rewrite (proj2 (Z.ltb_ge pos blen) Hp) in H. injection H as <-. reflexivity.
Qed.

Ltac is_regeq := first [ reflexivity | lia | (rewrite ?unsigned_lit by lia; lia) | (f_equal; lia)
                       | (f_equal; rewrite ?unsigned_lit by lia; lia) | word_eq_tac ].

(* 0x149e4: addiw s2,s2,1 with s2 = the command count as the sign extension of a uint32 *)
Lemma is_addiw_sw : forall c,
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 c)) + 1)) = Z_to_bv 64 (bv_swrap 32 (u32 (c + 1))).
Proof.
  intros c. f_equal. unfold u32, bv_swrap, bv_wrap. rewrite unsigned_lit_wrap.
  change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

(* prove an is_fr from the hypotheses, conjunct by conjunct (no unfolding of stk / rw_cells / bytes_at) *)
Ltac is_fr_intro :=
  unfold is_fr; repeat lazymatch goal with |- _ /\ _ => split; [eassumption|] end; eassumption.
(* reads of a world through writes elsewhere; the side conditions are offsets and lengths *)
Ltac is_lside := rewrite ?length_put; first [ lia | (rewrite length_upd; [ is_lside | lia | is_lside ]) ].
Ltac is_wread := repeat first [ rewrite s32_at_upd_out by is_lside | rewrite u_at_upd_out by is_lside ].
Ltac is_dmv H nv E :=
  lazymatch type of H with
  | match ?X with Some _ => _ | None => _ end = _ =>
      destruct X as [nv|] eqn:E; cbv beta iota in H; [|discriminate H]
  end.

(* ================ 10. the walk ================ *)

Theorem io_send_holds :
  spec_read_frame_contract -> tagged_of_contract -> memcpy_contract ->
  check_sent_frame_contract -> check_ack_frame_contract -> check_latest_control_contract ->
  check_inflight_retry_contract -> check_state_wake_contract -> check_inflight_new_contract ->
  check_latest_frame_contract -> check_keepalive_due_contract -> check_latest_sent_contract ->
  check_latest_display_contract -> io_send_contract.
Proof.
  intros SRF TOF MCPY CSF CAF CLC CIR CSW CIN CLF CKD CLS CLD.
  unfold spec_read_frame_contract, spec_read_frame_ENTRY, spec_read_frame_FRAME in SRF.
  unfold tagged_of_contract, tagged_of_ENTRY, tagged_of_FRAME in TOF.
  unfold check_sent_frame_contract, check_sent_frame_ENTRY, check_sent_frame_FRAME in CSF.
  unfold check_ack_frame_contract, check_ack_frame_ENTRY, check_ack_frame_FRAME in CAF.
  unfold check_latest_control_contract, check_latest_control_ENTRY, check_latest_control_FRAME in CLC.
  unfold check_inflight_retry_contract, check_inflight_retry_ENTRY, check_inflight_retry_FRAME in CIR.
  unfold check_state_wake_contract, check_state_wake_ENTRY, check_state_wake_FRAME in CSW.
  unfold check_inflight_new_contract, check_inflight_new_ENTRY, check_inflight_new_FRAME in CIN.
  unfold check_latest_frame_contract, check_latest_frame_ENTRY, check_latest_frame_FRAME in CLF.
  unfold check_keepalive_due_contract, check_keepalive_due_ENTRY, check_keepalive_due_FRAME in CKD.
  unfold check_latest_sent_contract, check_latest_sent_ENTRY, check_latest_sent_FRAME in CLS.
  unfold check_latest_display_contract, check_latest_display_ENTRY, check_latest_display_FRAME in CLD.
  unfold io_send_contract, io_send_ENTRY, io_send_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo B B' p r frame Ea1 Ea2 Hp BF AT PLT OWp GFN SP16 ST LO WOS MI WM MODEL.
  subst a1 a2.
  pose proof (bytes_at_bound rsegs m p frame BF) as [Hp0 Hplen].
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  unfold w_off_stack in WOS. unfold off_window in OWp.
  unfold io_send_frame_at, off_world, W_BASE_UBSAN, W_LEN, OFF_g_s, SZ_g_s in AT.
  wk_facts.
  assert (LB : Z.of_nat (length B) = 65616)
    by (rewrite (wm_len rsegs W_BASE_UBSAN m B WM); vm_compute; reflexivity).
  assert (LB0 : Z.of_nat (length (set_g_fail_next B 0)) = 65616).
  { unfold set_g_fail_next. rewrite length_upd_put; [exact LB | unfold OFF_g_fail_next; lia | rewrite LB].
    unfold OFF_g_fail_next. lia. }
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160)
    by (apply unsigned_lit; lia).
  cbv beta zeta delta [io_send_m] in MODEL.
  destruct (check_sent_frame_m (set_g_fail_next B 0) frame) as [[B1 []]|] eqn:CSFm;
    cbv beta iota in MODEL; [|discriminate].
  pose proof (is_csf _ _ _ _ CSFm) as [EB1 OKC]. subst B1.
  lazymatch type of MODEL with
  | match ?X with Some _ => _ | None => _ end = _ =>
      destruct X as [[B2 []]|] eqn:BR; cbv beta iota in MODEL; [|discriminate]
  end.
  injection MODEL as EB2 Er. subst B' r.
  pose proof (is_rf_ok frame OKC) as (Hdst & Hsrc & Hbody & Hbl & Hlen30).
  unfold SPEC_BODY_AT, SPEC_MAC in Hbody, Hsrc, Hbl, Hlen30.
  pose proof (is_rf_ranges frame) as
    (Rcode & Ret & Rnb & Rsum & Rret & Rsend & Rack & Rcmd & Rncmds & Rbsum & Rdst & Rsrc & Rbody & Rblen & Rpad).
  assert (GF0 : 0 <= g_fail_next B) by (pose proof (u_at_range B OFF_g_fail_next 1); unfold g_fail_next; lia).
  pose proof (munch_refl [(bv_unsigned sp - 288, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 160%nat ST.
  destruct (is_carve4 m (bv_unsigned sp + -160) junk 12 4 80 64
              (bv_unsigned sp + -148) (bv_unsigned sp + -144) (bv_unsigned sp + -64)
              ltac:(lia) ltac:(lia) ltac:(lia) FR)
    as (j0 & j1 & j2 & j3 & P0 & P1 & P2 & P3).
  clear FR.
  do 14 step.
  change (u_at B 64968 1) with (g_fail_next B).
  step.                              (* sb zero,0(s4): g_fail_next := 0 *)
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB (Z.to_nat W_LEN) _] |- _ => rename H into WM1 end.
  rewrite is_w_fail in WM1.
  lazymatch goal with H : mem_inv rsegs ?mm |- _ => rename mm into m1 end.
  do 4 step.                              (* addi a2,sp,16; mv a0,a1; mv a1,s0; jal spec_read_frame *)
  eapply evt_cut.
  { eapply SRF with (p := p) (len := Z.of_nat (length frame)) (fp := bv_unsigned sp + -144)
      (fr := frame) (junk := j2) (lo := lo) (B := set_g_fail_next B 0);
      [ reflexivity | reflexivity | reflexivity | exact Hp | exact BF | lia | lia
      | Z.div_mod_to_equations; lia | rewrite Hsp; lia | exact P2 | lia
      | unfold off_window; rewrite Hsp; lia
      | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | exact MI | exact WM1 ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 &
              Eq & MUc & WMc & MI2 & ST2 & WM2 & SFC).
  subst ms'. rewrite Hsp in MUc, ST2. clear WM1.
  transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI. try clear m1.
  rewrite (ret_pc_even 0x14878) by (first [lia | reflexivity]).
  (* the struct spec_frame f at sp' + 16 = sp - 144: its bytes and writability *)
  fold (rf frame) in SFC.
  pose proof (is_rwc_bytes m2 _ 80 _ SFC) as SBAT.
  pose proof (proj2 SFC) as SWR. cbn [cells_size csize Nat.add] in SWR. change (Z.of_nat 80) with 80 in SWR.
  clear SFC.
  assert (SBL : length (sf_bytes p (rf frame)) = 80%nat) by apply is_length_sfb.
  assert (SPd : sf_ptr p (rf frame) (sf_dst (rf frame)) = p)
    by (unfold sf_ptr; rewrite OKC, Z.eqb_refl, Hdst; lia).
  assert (SPs : sf_ptr p (rf frame) (sf_src (rf frame)) = p + 6)
    by (unfold sf_ptr; rewrite OKC, Z.eqb_refl, Hsrc; reflexivity).
  assert (SPb : sf_ptr p (rf frame) (sf_body (rf frame)) = p + 30)
    by (unfold sf_ptr; rewrite OKC, Z.eqb_refl, Hbody; reflexivity).
  assert (Fcmd : u_at (sf_bytes p (rf frame)) 40 1 = sf_cmd (rf frame)) by (is_fld; apply Z.mod_small; lia).
  assert (Fret : u_at (sf_bytes p (rf frame)) 30 2 = sf_retry (rf frame)) by (is_fld; apply Z.mod_small; lia).
  assert (Fblen : u_at (sf_bytes p (rf frame)) 56 8 = sf_body_len (rf frame)) by (is_fld; apply Z.mod_small; lia).
  assert (Fbody : u_at (sf_bytes p (rf frame)) 48 8 = p + 30) by (is_fld; rewrite SPb; apply Z.mod_small; lia).
  assert (Fsend : u_at (sf_bytes p (rf frame)) 32 4 = sf_send (rf frame)) by (is_fld; apply Z.mod_small; lia).
  assert (Fncmds : u_at (sf_bytes p (rf frame)) 41 1 = sf_ncmds (rf frame)) by (is_fld; apply Z.mod_small; lia).
  assert (MKSF : forall mm, bytes_at rsegs mm (bv_unsigned sp + -144) (sf_bytes p (rf frame)) ->
                 sframe_at mm (bv_unsigned sp + -144) p (rf frame)).
  { intros mm HBm. apply is_sframe;
      first [ exact HBm | (Z.div_mod_to_equations; lia) | lia
            | (rewrite SPd; lia) | (rewrite SPs; lia) | (rewrite SPb; lia) ]. }
  (* jal check_sent_frame (frame, len, &f) *)
  do 4 step.
  eapply evt_cut.
  { eapply CSF with (fa := p) (fp := bv_unsigned sp + -144) (frame := frame) (lo := lo)
      (B := set_g_fail_next B 0) (B' := set_g_fail_next B 0);
      [ reflexivity | reflexivity | reflexivity | exact Hp | exact BF
      | unfold off_window; rewrite Hsp; lia | apply MKSF; exact SBAT
      | unfold off_window; rewrite Hsp; lia | exact WM2 | exact CSFm
      | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST2 | rewrite Hsp; lia
      | unfold w_off_stack; rewrite Hsp; lia | exact MI2 ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 &
              Eq & MUc & WMc & MI3 & ST3 & EB & WM3).
  subst ms'. rewrite Hsp in MUc, ST3. clear WM2 EB.
  transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI2. try clear m2.
  rewrite (ret_pc_even 0x14888) by (first [lia | reflexivity]).
  (* ---- the epilogue, 0x14ad8: a0 = -EIO or 0 by bit 0 of g_fail_next; restore; ret ---- *)
  assert (EPI : forall (m4 : word -> option byte)
                  (y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 : word),
    munch [(bv_unsigned sp - 288, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m4 ->
    wmono rsegs m m4 -> mem_inv rsegs m4 -> stk rsegs m4 lo (bv_unsigned sp + -64) ->
    wmem rsegs m4 B2 ->
    rw_cells rsegs m4 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14
                          y15 (Z_to_bv 64 (g_fail_next B)) y16 y17 y18 s7 s8 s9 s10 s11 y19 y20 y21 y22)
                     F (Z_to_bv 64 0x14ad8) fc None m4 (seg_rom rsegs))).
  { intros m4 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 MU4 WM4 MI4 ST4 WMm4 P34.
    do 3 step.                             (* slli s3,s3,63; srai a0,s3,63; andi a0,a0,-5 *)
    rewrite (is_retv (g_fail_next B)) by lia.
    do 8 step.                             (* ld ra, s0..s6 *)
    release_frame P34 ST4 (bv_unsigned sp).
    do 2 step.                             (* addi sp,sp,160; ret *)
    apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
    split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|]. split; [exact ST4|]. exact WMm4. }
  (* ---- the frame in flight, 0x14a90-0x14ad4, then the epilogue ---- *)
  assert (PS : put 4 (s32_at (sf_bytes p (rf frame)) 32) = put 4 (sf_send (rf frame)))
    by (unfold s32_at; rewrite Fsend; apply is_put_swrap32).
  assert (FLY : forall (m4 : word -> option byte) (Bx : list byte) (cs1 : list cell)
                  (y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 : word),
    is_fr m m4 sp lo Bx p frame j0 cs1 (sf_bytes p (rf frame))
      [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    cells_size cs1 = 4%nat -> B2 = is_fly frame Bx ->
    evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y2 y3 y4
                          (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p)
                          (Z_to_bv 64 (s32_at (sf_bytes p (rf frame)) 32)) y5 y6 y7 y8 y9 y10 y11
                          y12 (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 274632) y13 y14 s7 s8 s9 s10 s11
                          y15 y16 y17 y18)
                     F (Z_to_bv 64 0x14a90) fc None m4 (seg_rom rsegs))).
  { intros m4 Bx cs1 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 FR4 L1 EB2.
    destruct FR4 as (MU4 & WM4 & MI4 & ST4 & WMm4 & Q0 & Q1 & SB4 & SW4 & Q3 & BF4).
    subst B2.
    assert (R40 : ov_read_bytes rsegs m4 (Z_to_bv 64 (bv_unsigned sp + -104)) 1
                  = Some (sub (sf_bytes p (rf frame)) 40 1)).
    { replace (bv_unsigned sp + -104) with (bv_unsigned sp + -144 + 40) by lia.
      exact (bytes_at_read rsegs m4 _ _ 40 1 SB4 ltac:(lia) ltac:(rewrite SBL; lia)). }
    do 3 step.                             (* auipc a1; li a2,1; lbu a3,56(sp) *)
    clear R40. rewrite ?wm_lbu, Fcmd.
    step.                                  (* ld a4,32(s4): g_now *)
    change (u_at Bx 65000 8) with (g_now Bx).
    do 2 step.                             (* li a5,1514; addi a1,a1,-1920 *)
    step. is_wname W1. rewrite is_w_flyon in W1.            (* sw a2,96(a1) *)
    step. is_wname W2. rewrite is_w_flycmd in W2.           (* sb a3,100(a1) *)
    step. is_wname W3. rewrite PS, is_w_flycnt in W3.       (* sw a0,104(a1) *)
    step. is_wname W4. rewrite is_w_retries in W4.          (* sw zero,108(a1) *)
    step. is_wname W5. rewrite is_w_flysent in W5.          (* sd a4,112(a1) *)
    step.                                  (* bltu s0,a5 *)
    rewrite is_ltu_lit by lia.
    destruct (Z.ltb_spec (Z.of_nat (length frame)) 1514) as [LT|GE]; cbv iota.
    - step. is_wname W6. rewrite is_w_flylen in W6. is_mname mF.   (* sd s0,1640(a1) *)
      do 4 step.                           (* addi a0,a1,120; mv a1,s1; mv a2,s0; jal memcpy *)
      eapply evt_cut.
      { eapply MCPY with (src := firstn (Z.to_nat (Z.of_nat (length frame))) frame).
        - rewrite unsigned_lit by lia. apply is_ba_firstn. exact BF4.
        - rewrite unsigned_lit by lia. rewrite length_firstn. lia.
        - rewrite !unsigned_lit by lia. eapply (wm_piece rsegs W_BASE_UBSAN _ _ 120);
            [exact W6 | reflexivity | lia | lia | unfold W_LEN; lia].
        - rewrite !unsigned_lit by lia. lia.
        - exact MI4. }
      intros ms' POST. unfold memcpy_post in POST.
      destruct POST as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & Eq & MUc & WMc & MI5 & DST & SRC).
      subst ms'. clear SRC.
      rewrite !unsigned_lit in MUc, DST by lia.
      pose proof (is_stk_fill _ _ _ _ _ _ _ ST4 MUc WMc DST) as ST4f.
      wk_facts. wk_world_after_call rsegs mF m5.
      transport_after_call rsegs mF m5 MUc WMc. clear MUc WMc MI4. try clear mF.
      rewrite (ret_pc_even 0x14ad8) by (first [lia | reflexivity]).
      is_wname W7. rewrite is_w_flyfr in W7.
      pose proof (is_lowrel m5 lo (bv_unsigned sp) _ _ _ ST4f ltac:(lia) Q0 eq_refl Q1 L1 SB4 SW4 SBL) as ST5.
      eapply EPI; [exact MU4 | exact WM4 | exact MI5 | exact ST5 | | exact Q3].
      unfold is_fly. cbv zeta.
      replace (Z.of_nat (length frame) <? SPEC_MAX_FRAME) with true
        by (symmetry; apply Z.ltb_lt; unfold SPEC_MAX_FRAME; lia).
      cbv iota. exact W7.
    - step.                                (* li s0,1514 *)
      step. is_wname W6. rewrite is_w_flylen in W6. is_mname mF.   (* sd s0,1640(a1) *)
      do 4 step.                           (* addi a0,a1,120; mv a1,s1; mv a2,s0; jal memcpy *)
      eapply evt_cut.
      { eapply MCPY with (src := firstn (Z.to_nat 1514) frame).
        - rewrite unsigned_lit by lia. apply is_ba_firstn. exact BF4.
        - rewrite unsigned_lit by lia. rewrite length_firstn. lia.
        - rewrite !unsigned_lit by lia. eapply (wm_piece rsegs W_BASE_UBSAN _ _ 120);
            [exact W6 | reflexivity | lia | lia | unfold W_LEN; lia].
        - rewrite !unsigned_lit by lia. lia.
        - exact MI4. }
      intros ms' POST. unfold memcpy_post in POST.
      destruct POST as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & Eq & MUc & WMc & MI5 & DST & SRC).
      subst ms'. clear SRC.
      rewrite !unsigned_lit in MUc, DST by lia.
      pose proof (is_stk_fill _ _ _ _ _ _ _ ST4 MUc WMc DST) as ST4f.
      wk_facts. wk_world_after_call rsegs mF m5.
      transport_after_call rsegs mF m5 MUc WMc. clear MUc WMc MI4. try clear mF.
      rewrite (ret_pc_even 0x14ad8) by (first [lia | reflexivity]).
      is_wname W7. rewrite is_w_flyfr in W7.
      pose proof (is_lowrel m5 lo (bv_unsigned sp) _ _ _ ST4f ltac:(lia) Q0 eq_refl Q1 L1 SB4 SW4 SBL) as ST5.
      eapply EPI; [exact MU4 | exact WM4 | exact MI5 | exact ST5 | | exact Q3].
      unfold is_fly. cbv zeta.
      replace (Z.of_nat (length frame) <? SPEC_MAX_FRAME) with false
        by (symmetry; apply Z.ltb_ge; unfold SPEC_MAX_FRAME; lia).
      cbv iota. exact W7. }
  (* ---- E2 and DATA share 0x148e8; proved below ---- *)
  enough (E2DP : forall (y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 : word),
    sf_cmd (rf frame) = 0 \/ sf_cmd (rf frame) = 226 ->
    evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y2 y3 y4
                          (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p) (Z_to_bv 64 (sf_cmd (rf frame)))
                          y5 y6 y7 y8 y9 y10 y11 y12 (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 274632) y13 y14
                          s7 s8 s9 s10 s11 y15 y16 y17 y18)
                     F (Z_to_bv 64 0x148e8) fc None m3 (seg_rom rsegs))).
  { (* ---- the dispatch on f.cmd, 0x14888 ---- *)
  assert (R40 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + -104)) 1
                = Some (sub (sf_bytes p (rf frame)) 40 1)).
  { replace (bv_unsigned sp + -104) with (bv_unsigned sp + -144 + 40) by lia.
    exact (bytes_at_read rsegs m3 _ _ 40 1 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
  step. clear R40.
  rewrite ?wm_lbu. rewrite Fcmd.
  step. step.                              (* li a1,225; blt a1,a0 *)
  rewrite is_lts_lit by lia.
  destruct (Z.ltb_spec 225 (sf_cmd (rf frame))) as [C1|C1]; cbv iota.
  - step. step.                            (* li a1,226; beq a0,a1 *)
    rewrite is_eqb_lit by lia.
    destruct (Z.eqb_spec (sf_cmd (rf frame)) 226) as [C2|C2]; cbv iota.
    + eapply E2DP. right. exact C2.        (* E2 *)
    + step. step.                          (* li a1,227; bne a0,a1 *)
      rewrite is_eqb_lit by lia.
      destruct (Z.eqb_spec (sf_cmd (rf frame)) 227) as [C3|C3]; cbv beta iota delta [negb].
      * (* E3: GOT.e3++, check_latest_control *)
        assert (KA : (sf_cmd (rf frame) =? SPEC_CMD_ACK) = false) by (apply Z.eqb_neq; unfold SPEC_CMD_ACK; lia).
        assert (KE : ((sf_cmd (rf frame) =? SPEC_CMD_E2) || (sf_cmd (rf frame) =? SPEC_CMD_DATA)) = false)
          by (apply orb_false_iff; split; apply Z.eqb_neq; unfold SPEC_CMD_E2, SPEC_CMD_DATA; lia).
        assert (K3 : (sf_cmd (rf frame) =? SPEC_CMD_E3) = true) by (apply Z.eqb_eq; unfold SPEC_CMD_E3; lia).
        rewrite KA, KE, K3 in BR. cbv beta iota in BR.
        is_dmv BR e3 IE. apply is_int_inc in IE. destruct IE as [IE1 ->].
        pose proof (s32_range (set_g_fail_next B 0) A_GOT_e3) as RG.
        change (s32_at (set_g_fail_next B 0) A_GOT_e3) with (GOT_e3 (set_g_fail_next B 0)) in RG.
        step.                              (* lw a1,316(s4) *)
        change (s32_at (set_g_fail_next B 0) 65284) with (GOT_e3 (set_g_fail_next B 0)).
        step.                              (* addiw a0,a1,1 *)
        rewrite is_addiw1 by (unfold INT_MAX in *; lia).
        step.                              (* blt a0,a1 *)
        rewrite is_lts_lit by lia.
        destruct (Z.ltb_spec (GOT_e3 (set_g_fail_next B 0) + 1) (GOT_e3 (set_g_fail_next B 0))); [lia|].
        cbv iota.
        step. is_wname WE. rewrite is_w_e3 in WE. is_mname mE.   (* sw a0,316(s4) *)
        do 2 step.                         (* addi a0,sp,16; jal check_latest_control *)
        eapply evt_cut.
        { eapply CLC with (fp := bv_unsigned sp + -144) (fa := p) (frame := frame) (lo := lo)
            (B := set_GOT_e3 (set_g_fail_next B 0) (GOT_e3 (set_g_fail_next B 0) + 1)) (B' := B2);
            [ reflexivity | apply MKSF; exact SBAT | unfold off_window; rewrite Hsp; lia | exact WE | exact BR
            | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST3 | rewrite Hsp; lia
            | unfold w_off_stack; rewrite Hsp; lia | exact MI3 ]. }
        intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 &
                    Eq & MUc & WMc & MI5 & ST5 & EB & WM5).
        subst ms'. rewrite Hsp in MUc, ST5. clear WE. subst B2.
        transport_after_call rsegs mE m5 MUc WMc. clear MUc WMc MI3. try clear mE.
        rewrite (ret_pc_even 0x148e4) by (first [lia | reflexivity]).
        step.                              (* j 14ad8 *)
        pose proof (is_lowrel m5 lo (bv_unsigned sp) _ _ _ ST5 ltac:(lia) P0 eq_refl P1 eq_refl SBAT SWR SBL) as ST6.
        eapply EPI; [exact MU | exact WMO | exact MI5 | exact ST6 | exact WM5 | exact P3].
      * (* any other command: nothing more; the world is set_g_fail_next B 0 *)
        assert (K : B2 = set_g_fail_next B 0).
        { revert BR.
          replace (sf_cmd (rf frame) =? SPEC_CMD_ACK) with false by (symmetry; apply Z.eqb_neq; unfold SPEC_CMD_ACK; lia).
          replace (sf_cmd (rf frame) =? SPEC_CMD_E2) with false by (symmetry; apply Z.eqb_neq; unfold SPEC_CMD_E2; lia).
          replace (sf_cmd (rf frame) =? SPEC_CMD_DATA) with false by (symmetry; apply Z.eqb_neq; unfold SPEC_CMD_DATA; lia).
          replace (sf_cmd (rf frame) =? SPEC_CMD_E3) with false by (symmetry; apply Z.eqb_neq; unfold SPEC_CMD_E3; lia).
          cbv beta iota delta [orb]. intros BR. injection BR as <-. reflexivity. }
        subst B2.
        pose proof (is_lowrel m3 lo (bv_unsigned sp) _ _ _ ST3 ltac:(lia) P0 eq_refl P1 eq_refl SBAT SWR SBL) as ST4.
        eapply EPI; [exact MU | exact WMO | exact MI3 | exact ST4 | exact WM3 | exact P3].
  - step.                                  (* beqz a0 *)
    rewrite is_eqb_lit by lia.
    destruct (Z.eqb_spec (sf_cmd (rf frame)) 0) as [C2|C2]; cbv iota.
    + eapply E2DP. left. exact C2.         (* DATA *)
    + step. step.                          (* li a1,160; bne a0,a1 *)
      rewrite is_eqb_lit by lia.
      destruct (Z.eqb_spec (sf_cmd (rf frame)) 160) as [C3|C3]; cbv beta iota delta [negb].
      * (* ACK: GOT.acks++, check_ack_frame, check_latest_control *)
        assert (KA : (sf_cmd (rf frame) =? SPEC_CMD_ACK) = true) by (apply Z.eqb_eq; unfold SPEC_CMD_ACK; lia).
        rewrite KA in BR. cbv beta iota in BR.
        is_dmv BR a IA.
        is_dmp BR B3 CAm.
        apply is_int_inc in IA. destruct IA as [IA1 ->].
        pose proof (s32_range (set_g_fail_next B 0) A_GOT_acks) as RG.
        change (s32_at (set_g_fail_next B 0) A_GOT_acks) with (GOT_acks (set_g_fail_next B 0)) in RG.
        step.                              (* lw a1,320(s4) *)
        change (s32_at (set_g_fail_next B 0) 65288) with (GOT_acks (set_g_fail_next B 0)).
        step.                              (* addiw a0,a1,1 *)
        rewrite is_addiw1 by (unfold INT_MAX in *; lia).
        step.                              (* blt a0,a1 *)
        rewrite is_lts_lit by lia.
        destruct (Z.ltb_spec (GOT_acks (set_g_fail_next B 0) + 1) (GOT_acks (set_g_fail_next B 0))); [lia|].
        cbv iota.
        step. is_wname WA. rewrite is_w_acks in WA. is_mname mA.   (* sw a0,320(s4) *)
        do 2 step.                         (* addi a0,sp,16; jal check_ack_frame *)
        eapply evt_cut.
        { eapply CAF with (fp := bv_unsigned sp + -144) (fa := p) (frame := frame) (lo := lo)
            (B := set_GOT_acks (set_g_fail_next B 0) (GOT_acks (set_g_fail_next B 0) + 1)) (B' := B3);
            [ reflexivity | apply MKSF; exact SBAT | unfold off_window; rewrite Hsp; lia | exact WA | exact CAm
            | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST3 | rewrite Hsp; lia
            | unfold w_off_stack; rewrite Hsp; lia | exact MI3 ]. }
        intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 &
                    Eq & MUc & WMc & MI4 & ST4 & EB & WM4).
        subst ms'. rewrite Hsp in MUc, ST4. clear WA. subst B3.
        transport_after_call rsegs mA m4 MUc WMc. clear MUc WMc MI3. try clear mA.
        rewrite (ret_pc_even 0x148b8) by (first [lia | reflexivity]).
        do 3 step.                         (* j 148dc; addi a0,sp,16; jal check_latest_control *)
        eapply evt_cut.
        { eapply CLC with (fp := bv_unsigned sp + -144) (fa := p) (frame := frame) (lo := lo)
            (B := set_GOT_acks (set_g_fail_next B 0) (GOT_acks (set_g_fail_next B 0) + 1)) (B' := B2);
            [ reflexivity | apply MKSF; exact SBAT | unfold off_window; rewrite Hsp; lia | exact WM4 | exact BR
            | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST4 | rewrite Hsp; lia
            | unfold w_off_stack; rewrite Hsp; lia | exact MI4 ]. }
        intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 &
                    Eq & MUc & WMc & MI5 & ST5 & EB & WM5).
        subst ms'. rewrite Hsp in MUc, ST5. clear WM4. subst B2.
        transport_after_call rsegs m4 m5 MUc WMc. clear MUc WMc MI4. try clear m4.
        rewrite (ret_pc_even 0x148e4) by (first [lia | reflexivity]).
        step.                              (* j 14ad8 *)
        pose proof (is_lowrel m5 lo (bv_unsigned sp) _ _ _ ST5 ltac:(lia) P0 eq_refl P1 eq_refl SBAT SWR SBL) as ST6.
        eapply EPI; [exact MU | exact WMO | exact MI5 | exact ST6 | exact WM5 | exact P3].
      * assert (K : B2 = set_g_fail_next B 0).
        { revert BR.
          replace (sf_cmd (rf frame) =? SPEC_CMD_ACK) with false by (symmetry; apply Z.eqb_neq; unfold SPEC_CMD_ACK; lia).
          replace (sf_cmd (rf frame) =? SPEC_CMD_E2) with false by (symmetry; apply Z.eqb_neq; unfold SPEC_CMD_E2; lia).
          replace (sf_cmd (rf frame) =? SPEC_CMD_DATA) with false by (symmetry; apply Z.eqb_neq; unfold SPEC_CMD_DATA; lia).
          replace (sf_cmd (rf frame) =? SPEC_CMD_E3) with false by (symmetry; apply Z.eqb_neq; unfold SPEC_CMD_E3; lia).
          cbv beta iota delta [orb]. intros BR. injection BR as <-. reflexivity. }
        subst B2.
        pose proof (is_lowrel m3 lo (bv_unsigned sp) _ _ _ ST3 ltac:(lia) P0 eq_refl P1 eq_refl SBAT SWR SBL) as ST4.
        eapply EPI; [exact MU | exact WMO | exact MI3 | exact ST4 | exact WM3 | exact P3]. }
  (* ---- 0x148e8: E2 or DATA ---- *)
  intros y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 CE.
  assert (KA : (sf_cmd (rf frame) =? SPEC_CMD_ACK) = false) by (apply Z.eqb_neq; unfold SPEC_CMD_ACK; lia).
  assert (KE : ((sf_cmd (rf frame) =? SPEC_CMD_E2) || (sf_cmd (rf frame) =? SPEC_CMD_DATA)) = true)
    by (apply orb_true_iff; destruct CE; [right|left]; apply Z.eqb_eq; unfold SPEC_CMD_E2, SPEC_CMD_DATA; lia).
  rewrite KA, KE in BR. cbv beta iota in BR.
  assert (R30 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + -114)) 2
                = Some (sub (sf_bytes p (rf frame)) 30 2)).
  { replace (bv_unsigned sp + -114) with (bv_unsigned sp + -144 + 30) by lia.
    exact (bytes_at_read rsegs m3 _ _ 30 2 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
  step. clear R30. rewrite ?wm_lhu, Fret.  (* lhu a1,46(sp): f.retry *)
  step.                                    (* beqz a1 *)
  rewrite is_eqb_lit by lia.
  destruct (Z.eqb_spec (sf_retry (rf frame)) 0) as [RT0|RT1]; cbv iota.
  2: { (* a retry: check_inflight_retry, M.fly.retries++, M.fly.sent = g_now *)
    assert (TR : truth (sf_retry (rf frame)) = true) by (unfold truth; apply negb_true_iff, Z.eqb_neq; exact RT1).
    rewrite TR in BR. cbv beta iota in BR.
    is_dmp BR B3 CIRm.
    injection BR as EB2. subst B2.
    do 4 step.                             (* addi a2,sp,16; mv a0,s1; mv a1,s0; jal check_inflight_retry *)
    eapply evt_cut.
    { eapply CIR with (fa := p) (fp := bv_unsigned sp + -144) (frame := frame) (lo := lo)
        (B := set_g_fail_next B 0) (B' := B3);
        [ reflexivity | reflexivity | reflexivity | exact Hp | lia | exact BF
        | unfold off_window; rewrite Hsp; lia | apply MKSF; exact SBAT
        | unfold off_window; rewrite Hsp; lia | exact WM3 | exact CIRm
        | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST3 | rewrite Hsp; lia
        | unfold w_off_stack; rewrite Hsp; lia | exact MI3 ]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 &
                Eq & MUc & WMc & MI4 & ST4 & EB & WM4).
    subst ms'. rewrite Hsp in MUc, ST4. clear WM3. subst B3.
    transport_after_call rsegs m3 m4 MUc WMc. clear MUc WMc MI3. try clear m3.
    rewrite (ret_pc_even 0x14900) by (first [lia | reflexivity]).
    do 3 step.                             (* auipc a0; addi a0,a0,-1520; lw a1,108(a0) *)
    step.                                  (* ld a2,32(s4) *)
    change (u_at (set_g_fail_next B 0) 65000 8) with (g_now (set_g_fail_next B 0)).
    step.                                  (* addi a1,a1,1 *)
    step. is_wname WR.                     (* sw a1,108(a0) *)
    lazymatch type of WR with context [upd _ 108 (put 4 ?V)] =>
      assert (PV : put 4 V = put 4 (u32 (M_fly_retries (set_g_fail_next B 0) + 1)))
        by (apply is_put4_congr; unfold u32, s32_at, bv_swrap, bv_wrap; rewrite ?unsigned_lit_wrap;
            change (bv_modulus 32) with (2^32); change (bv_half_modulus 32) with (2^31);
            rewrite ?is_r_retries; Z.div_mod_to_equations; lia);
      rewrite PV in WR
    end.
    rewrite is_w_retries in WR.
    step. is_wname WS. rewrite is_w_flysent in WS. is_mname mR.   (* sd a2,112(a0) *)
    step.                                  (* j 14ad8 *)
    pose proof (is_lowrel mR lo (bv_unsigned sp) _ _ _ ST4 ltac:(lia) P0 eq_refl P1 eq_refl SBAT SWR SBL) as ST5.
    eapply EPI; [exact MU | exact WMO | exact MI4 | exact ST5 | exact WS | exact P3]. }
  assert (TR : truth (sf_retry (rf frame)) = false) by (unfold truth; rewrite RT0; reflexivity).
  rewrite TR in BR. cbv beta iota in BR.
  step. step.                              (* li a1,226; bne a0,a1 *)
  rewrite is_eqb_lit by lia.
  destruct (Z.eq_dec (sf_cmd (rf frame)) 226) as [CE2|CN].
  { (* E2: check_state_wake, check_latest_control, GOT.e2++, g_last_counter, the frame in flight unless fail *)
    assert (K2 : (sf_cmd (rf frame) =? SPEC_CMD_E2) = true) by (apply Z.eqb_eq; unfold SPEC_CMD_E2; lia).
    rewrite K2 in BR. cbv beta iota in BR.
    replace (sf_cmd (rf frame) =? 226) with true by (symmetry; apply Z.eqb_eq; exact CE2).
    cbv beta iota delta [negb].
    is_dmp BR B3 CSWm.
    is_dmp BR B4 CLCm.
    is_dmv BR e2 IE.
    apply is_int_inc in IE. destruct IE as [IE1 ->].
    step.                                  (* jal check_state_wake *)
    eapply evt_cut.
    { eapply CSW with (lo := lo) (B := set_g_fail_next B 0) (B' := B3);
        [ exact WM3 | exact CSWm | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST3
        | rewrite Hsp; lia | unfold w_off_stack; rewrite Hsp; lia | exact MI3 ]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 &
                Eq & MUc & WMc & MI4 & ST4 & EB & WM4).
    subst ms'. rewrite Hsp in MUc, ST4. clear WM3. subst B3.
    transport_after_call rsegs m3 m4 MUc WMc. clear MUc WMc MI3. try clear m3.
    rewrite (ret_pc_even 0x1492c) by (first [lia | reflexivity]).
    do 2 step.                             (* addi a0,sp,16; jal check_latest_control *)
    eapply evt_cut.
    { eapply CLC with (fp := bv_unsigned sp + -144) (fa := p) (frame := frame) (lo := lo)
        (B := set_g_fail_next B 0) (B' := B4);
        [ reflexivity | apply MKSF; exact SBAT | unfold off_window; rewrite Hsp; lia | exact WM4 | exact CLCm
        | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST4 | rewrite Hsp; lia
        | unfold w_off_stack; rewrite Hsp; lia | exact MI4 ]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 &
                Eq & MUc & WMc & MI5 & ST5 & EB & WM5).
    subst ms'. rewrite Hsp in MUc, ST5. clear WM4. subst B4.
    transport_after_call rsegs m4 m5 MUc WMc. clear MUc WMc MI4. try clear m4.
    rewrite (ret_pc_even 0x14934) by (first [lia | reflexivity]).
    pose proof (s32_range (set_g_fail_next B 0) A_GOT_e2) as RG.
    change (s32_at (set_g_fail_next B 0) A_GOT_e2) with (GOT_e2 (set_g_fail_next B 0)) in RG.
    step.                                  (* lw a0,312(s4) *)
    change (s32_at (set_g_fail_next B 0) 65280) with (GOT_e2 (set_g_fail_next B 0)).
    step.                                  (* addiw a1,a0,1 *)
    rewrite is_addiw1 by (unfold INT_MAX in *; lia).
    step.                                  (* blt a1,a0 *)
    rewrite is_lts_lit by lia.
    destruct (Z.ltb_spec (GOT_e2 (set_g_fail_next B 0) + 1) (GOT_e2 (set_g_fail_next B 0))); [lia|].
    cbv iota.
    assert (R48 : ov_read_bytes rsegs m5 (Z_to_bv 64 (bv_unsigned sp + -112)) 4
                  = Some (sub (sf_bytes p (rf frame)) 32 4)).
    { replace (bv_unsigned sp + -112) with (bv_unsigned sp + -144 + 32) by lia.
      exact (bytes_at_read rsegs m5 _ _ 32 4 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
    step. clear R48. rewrite ?wm_lw.       (* lw a0,48(sp): f.send *)
    step. is_wname WE. rewrite is_w_e2 in WE.   (* sw a1,312(s4) *)
    step.                                  (* andi a1,s3,1 *)
    step. is_wname WL. rewrite PS, is_w_lastc in WL. is_mname mL.   (* sw a0,8(s4) *)
    step.                                  (* beqz a1 *)
    assert (FV : g_fail_next B = 0 \/ g_fail_next B = 1) by lia.
    destruct FV as [F0|F1].
    - (* not failing: the frame goes in flight *)
      lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with true by (rewrite F0; vm_compute; reflexivity) end.
      cbv iota.
      assert (TF : truth (g_fail_next B) = false) by (rewrite F0; reflexivity).
      rewrite TF in BR. cbv beta iota in BR.
      eapply FLY with (Bx := set_g_last_counter (set_GOT_e2 (set_g_fail_next B 0)
                               (GOT_e2 (set_g_fail_next B 0) + 1)) (sf_send (rf frame))).
      + is_fr_intro.
      + reflexivity.
      + injection BR as <-. reflexivity.
    - (* failing: return -EIO with the frame not in flight *)
      lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false by (rewrite F1; vm_compute; reflexivity) end.
      cbv iota.
      assert (TF : truth (g_fail_next B) = true) by (rewrite F1; reflexivity).
      rewrite TF in BR. cbv beta iota in BR. injection BR as <-.
      step.                                (* j 14ad8 *)
      pose proof (is_lowrel mL lo (bv_unsigned sp) _ _ _ ST5 ltac:(lia) P0 eq_refl P1 eq_refl SBAT SWR SBL) as ST6.
      eapply EPI; [exact MU | exact WMO | exact MI5 | exact ST6 | exact WL | exact P3]. }
  (* ---- DATA, 0x14958 ---- *)
  assert (CD : sf_cmd (rf frame) = 0) by (destruct CE; [assumption | contradiction]).
  assert (K2 : (sf_cmd (rf frame) =? SPEC_CMD_E2) = false) by (apply Z.eqb_neq; unfold SPEC_CMD_E2; lia).
  rewrite K2 in BR. cbv beta iota in BR.
  replace (sf_cmd (rf frame) =? 226) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv beta iota delta [negb].
  change ((sf_body_len (rf frame) =? 1) && (at8 (skipn (Z.to_nat (sf_body (rf frame))) frame) 0 =? 0)
          && (sf_ncmds (rf frame) =? 1)) with (is_ka frame) in BR.
  is_dmp BR B3 CINm.
  assert (EB3 : B3 = set_g_fail_next B 0).
  { unfold check_inflight_new_m in CINm.
    destruct (negb (M_state (set_g_fail_next B 0) =? S_ONLINE) || truth (M_fly_on (set_g_fail_next B 0)));
      [discriminate|].
    destruct (g_now (set_g_fail_next B 0) <? M_backoff_until (set_g_fail_next B 0)); [discriminate|].
    injection CINm as <-. reflexivity. }
  subst B3.
  is_dmv BR cmdsM CMDm.
  is_dmp BR B4 CLFm.
  is_dmp BR B6 B6m.
  assert (EB2 : B2 = is_fly frame B6) by (injection BR as <-; reflexivity).
  clear BR.
  assert (CMR : 0 <= cmdsM < 2^32).
  { revert CMDm. destruct (negb (truth (g_raw (set_g_fail_next B 0))) && negb (is_ka frame)); intros CMDm.
    - eapply is_cl_range; [|exact CMDm]. lia.
    - injection CMDm as <-. lia. }
  (* -- 0x149fc: check_latest_frame (&f, cmds), then the bookkeeping and the frame in flight -- *)
  pose proof (s32_range (set_g_fail_next B 0) OFF_g_raw) as RGR.
  change (s32_at (set_g_fail_next B 0) OFF_g_raw) with (g_raw (set_g_fail_next B 0)) in RGR.
  assert (CONT : forall (m4 : word -> option byte) (cs1 : list cell)
                   (y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 S2 : word),
    S2 = Z_to_bv 64 (bv_swrap 32 cmdsM) ->
    is_fr m m4 sp lo (set_g_fail_next B 0) p frame j0 cs1 (sf_bytes p (rf frame))
      [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    cells_size cs1 = 4%nat ->
    evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y2 y3 y4
                          (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p) y5 y6 y7 y8 y9 y10 y11 y12
                          S2 (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 274632) (Z_to_bv 64 (b2z (is_ka frame))) y13
                          s7 s8 s9 s10 s11 y14 y15 y16 y17)
                     F (Z_to_bv 64 0x149fc) fc None m4 (seg_rom rsegs))).
  { intros m4 cs1 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 S2 ES2 FR4 L1. subst S2.
    destruct FR4 as (MU4 & WM4 & MI4 & ST4 & WMm4 & Q0 & Q1 & SB4 & SW4 & Q3 & BF4).
    do 3 step.                             (* addi a0,sp,16; mv a1,s2; jal check_latest_frame *)
    eapply evt_cut.
    { eapply CLF with (fp := bv_unsigned sp + -144) (fa := p) (frame := frame) (cmds := cmdsM) (lo := lo)
        (B := set_g_fail_next B 0) (B' := B4);
        [ reflexivity | reflexivity | exact CMR | apply MKSF; exact SB4 | unfold off_window; rewrite Hsp; lia
        | exact WMm4 | exact CLFm | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST4
        | rewrite Hsp; lia | unfold w_off_stack; rewrite Hsp; lia | exact MI4 ]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 &
                Eq & MUc & WMc & MI5 & ST5 & EB & WM5).
    subst ms'. rewrite Hsp in MUc, ST5. clear WMm4. subst B4.
    transport_after_call rsegs m4 m5 MUc WMc. clear MUc WMc MI4. try clear m4.
    rewrite (ret_pc_even 0x14a08) by (first [lia | reflexivity]).
    step.                                  (* lw a0,4(s4): g_raw *)
    change (s32_at (set_g_fail_next B 0) 64972) with (g_raw (set_g_fail_next B 0)).
    assert (R48 : ov_read_bytes rsegs m5 (Z_to_bv 64 (bv_unsigned sp + -112)) 4
                  = Some (sub (sf_bytes p (rf frame)) 32 4)).
    { replace (bv_unsigned sp + -112) with (bv_unsigned sp + -144 + 32) by lia.
      exact (bytes_at_read rsegs m5 _ _ 32 4 SB4 ltac:(lia) ltac:(rewrite SBL; lia)). }
    step. clear R48. rewrite ?wm_lw.       (* lw a1,48(sp): f.send *)
    step. step.                            (* seqz a2,a0; and a2,a2,s5 *)
    rewrite is_seqz_and by lia.
    do 2 step.                             (* auipc a3; addi s2,a3,-1800 *)
    step. is_wname WH. rewrite PS, is_w_hostc in WH.         (* sw a1,84(s2): M.host_counter *)
    step. is_wname WC. rewrite PS, is_w_lastc in WC. is_mname mC.   (* sw a1,8(s4): g_last_counter *)
    set (B5 := set_g_last_counter (set_M_host_counter (set_g_fail_next B 0) (sf_send (rf frame)))
                 (sf_send (rf frame))) in *.
    assert (LB5 : Z.of_nat (length B5) = 65616)
      by (rewrite (wm_len rsegs W_BASE_UBSAN mC B5 WC); vm_compute; reflexivity).
    assert (GR5 : g_raw B5 = g_raw (set_g_fail_next B 0)).
    { unfold B5, g_raw, set_g_last_counter, set_M_host_counter, OFF_g_raw, OFF_g_last_counter, A_M_host_counter, OFF_M.
      is_wread. reflexivity. }
    pose proof (s32_range B5 OFF_g_raw) as RG5. change (s32_at B5 OFF_g_raw) with (g_raw B5) in RG5.
    step.                                  (* beqz a2 *)
    rewrite is_eqb_lit by (unfold b2z; destruct (negb (truth (g_raw (set_g_fail_next B 0))) && is_ka frame); lia).
    rewrite <- GR5.
    destruct (negb (truth (g_raw B5)) && is_ka frame) eqn:KC.
    - (* a keepalive: check_keepalive_due, M.next_ka *)
      replace (b2z true =? 0) with false by reflexivity. cbv iota.
      is_dmp B6m Bk CKDm.
      step.                                (* jal check_keepalive_due *)
      eapply evt_cut.
      { eapply CKD with (lo := lo) (B := B5) (B' := Bk);
          [ exact WC | exact CKDm | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST5
          | rewrite Hsp; lia | unfold w_off_stack; rewrite Hsp; lia | exact MI5 ]. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 &
                  Eq & MUc & WMc & MI6 & ST6 & EB & WM6).
      subst ms'. rewrite Hsp in MUc, ST6. clear WC. subst Bk.
      transport_after_call rsegs mC m6 MUc WMc. clear MUc WMc MI5. try clear mC.
      rewrite (ret_pc_even 0x14a30) by (first [lia | reflexivity]).
      step. change (u_at B5 65048 4) with (Cfg_keepalive_ms B5).   (* lwu a1,80(s4) *)
      step. change (u_at B5 48 8) with (M_next_ka B5).            (* ld a2,48(s2) *)
      step. change (u_at B5 65000 8) with (g_now B5).             (* ld a0,32(s4) *)
      step. step.                          (* li a3,1000; mul a1,a1,a3 *)
      pose proof (u_at_range B5 65048 4) as RK0. change (u_at B5 65048 4) with (Cfg_keepalive_ms B5) in RK0.
      change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in RK0.
      pose proof (u_at_range B5 48 8) as RN0. change (u_at B5 48 8) with (M_next_ka B5) in RN0.
      change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RN0.
      pose proof (u_at_range B5 65000 8) as RG0. change (u_at B5 65000 8) with (g_now B5) in RG0.
      change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RG0.
      rewrite (unsigned_lit (Cfg_keepalive_ms B5)) by lia.
      assert (GN : forall nv, g_now (set_M_next_ka B5 nv) = g_now B5).
      { intros nv. rewrite <- !is_r_now, <- is_w_nextka.
        rewrite u_at_upd_out; [reflexivity | lia | lia | rewrite length_put; lia | rewrite length_put; lia]. }
      assert (CK : forall nv, Cfg_keepalive_ms (set_M_next_ka B5 nv) = Cfg_keepalive_ms B5).
      { intros nv. rewrite <- !is_r_ka, <- is_w_nextka.
        rewrite u_at_upd_out; [reflexivity | lia | lia | rewrite length_put; lia | rewrite length_put; lia]. }
      rewrite GN, CK in B6m.
      set (nk := u64 (M_next_ka B5 + h_ms_m (Cfg_keepalive_ms B5))) in *.
      assert (Rnk : 0 <= nk < 2^64) by (unfold nk, u64; apply Z.mod_pos_bound; lia).
      step.                                (* add a2,a1,a2 *)
      step.                                (* sd a2,48(s2) *)
      is_wname WK.
      lazymatch type of WK with context [upd B5 48 (put 8 ?V)] =>
                replace (put 8 V) with (put 8 nk) in WK
                  by (symmetry; apply is_put8_congr; unfold nk, h_ms_m, u64; rewrite ?unsigned_lit_wrap;
                      Z.div_mod_to_equations; lia) end.
      rewrite is_w_nextka in WK. is_mname mK.
      step.                                (* bltu a0,a2 *)
      lazymatch goal with |- context [bv_ltu (Z_to_bv 64 (g_now B5)) ?y] =>
                replace y with (Z_to_bv 64 nk)
                  by (apply bv_eq; rewrite ?unsigned_lit_wrap; unfold nk, h_ms_m, u64; Z.div_mod_to_equations; lia) end.
      rewrite is_ltu_lit by lia.
      destruct (Z.ltb_spec (g_now B5) nk) as [LTn|GEn]; cbv iota.
      + replace (nk <=? g_now B5) with false in B6m by (symmetry; apply Z.leb_gt; lia).
        cbv beta iota in B6m. injection B6m as <-.
        assert (R48 : ov_read_bytes rsegs mK (Z_to_bv 64 (bv_unsigned sp + -112)) 4
                      = Some (sub (sf_bytes p (rf frame)) 32 4)).
        { replace (bv_unsigned sp + -112) with (bv_unsigned sp + -144 + 32) by lia.
          exact (bytes_at_read rsegs mK _ _ 32 4 SB4 ltac:(lia) ltac:(rewrite SBL; lia)). }
        step. clear R48. rewrite ?wm_lw.   (* lw a0,48(sp): f.send *)
        eapply FLY with (Bx := set_M_next_ka B5 nk); [is_fr_intro | exact L1 | exact EB2].
      + replace (nk <=? g_now B5) with true in B6m by (symmetry; apply Z.leb_le; lia).
        cbv beta iota in B6m. injection B6m as <-.
        step.                              (* add a0,a0,a1 *)
        step.                              (* sd a0,48(s2) *)
        is_wname WK2.
        lazymatch type of WK2 with context [upd (set_M_next_ka B5 nk) 48 (put 8 ?V)] =>
                  replace (put 8 V) with (put 8 (u64 (g_now B5 + h_ms_m (Cfg_keepalive_ms B5)))) in WK2
                    by (symmetry; apply is_put8_congr; unfold h_ms_m, u64; rewrite ?unsigned_lit_wrap;
                        Z.div_mod_to_equations; lia) end.
        rewrite is_w_nextka in WK2. is_mname mK2.
        step.                              (* j 14a8c *)
        assert (R48 : ov_read_bytes rsegs mK2 (Z_to_bv 64 (bv_unsigned sp + -112)) 4
                      = Some (sub (sf_bytes p (rf frame)) 32 4)).
        { replace (bv_unsigned sp + -112) with (bv_unsigned sp + -144 + 32) by lia.
          exact (bytes_at_read rsegs mK2 _ _ 32 4 SB4 ltac:(lia) ltac:(rewrite SBL; lia)). }
        step. clear R48. rewrite ?wm_lw.   (* lw a0,48(sp): f.send *)
        eapply FLY with (Bx := set_M_next_ka (set_M_next_ka B5 nk) (u64 (g_now B5 + h_ms_m (Cfg_keepalive_ms B5))));
          [is_fr_intro | exact L1 | exact EB2].
    - replace (b2z false =? 0) with true by reflexivity. cbv iota.
      step.                                (* bnez a0: g_raw *)
      rewrite is_eqb_lit by lia.
      destruct (Z.eqb_spec (g_raw B5) 0) as [G50|G51]; cbv beta iota delta [negb].
      + (* neither raw nor a keepalive: check_latest_sent, maybe check_latest_display *)
        assert (NG : negb (truth (g_raw B5)) = true) by (unfold truth; rewrite G50; reflexivity).
        try (lazymatch type of B6m with (if ?c then _ else _) = _ =>
               replace c with true in B6m by (first [reflexivity | rewrite <- NG; reflexivity]) end).
        cbv beta iota in B6m.
        lazymatch type of B6m with
        | match ?X with Some _ => _ | None => _ end = _ =>
            destruct X as [[Bs disp]|] eqn:CLSm; cbv beta iota in B6m; [|discriminate B6m]
        end.
        assert (R64 : ov_read_bytes rsegs mC (Z_to_bv 64 (bv_unsigned sp + -96)) 8
                      = Some (sub (sf_bytes p (rf frame)) 48 8)).
        { replace (bv_unsigned sp + -96) with (bv_unsigned sp + -144 + 48) by lia.
          exact (bytes_at_read rsegs mC _ _ 48 8 SB4 ltac:(lia) ltac:(rewrite SBL; lia)). }
        step. clear R64. rewrite ?wm_ld, Fbody.     (* ld a0,64(sp): f.body *)
        assert (R72 : ov_read_bytes rsegs mC (Z_to_bv 64 (bv_unsigned sp + -88)) 8
                      = Some (sub (sf_bytes p (rf frame)) 56 8)).
        { replace (bv_unsigned sp + -88) with (bv_unsigned sp + -144 + 56) by lia.
          exact (bytes_at_read rsegs mC _ _ 56 8 SB4 ltac:(lia) ltac:(rewrite SBL; lia)). }
        step. clear R72. rewrite ?wm_ld, Fblen.     (* ld a1,72(sp): f.body_len *)
        step. step.                        (* addi a2,sp,12; jal check_latest_sent *)
        destruct (rw_cells_forget _ _ _ _ Q1) as [jd Q1']. rewrite L1 in Q1'.
        pose proof (conj BF4 WC) as KEEP.
        eapply evt_cut.
        { eapply CLS with (bp := p + 30) (len := sf_body_len (rf frame)) (dp := bv_unsigned sp + -148)
            (body := firstn (Z.to_nat (sf_body_len (rf frame))) (skipn (Z.to_nat (sf_body (rf frame))) frame))
            (junk := jd) (lo := lo) (B := B5) (B' := Bs) (disp := disp);
            [ reflexivity | reflexivity | reflexivity | lia
            | rewrite Hbody; apply is_ba_firstn; apply (is_ba_skipn mC p frame 30); [lia | lia | exact BF4]
            | rewrite length_firstn, length_skipn, Hbody; lia
            | unfold W_BASE_UBSAN, OFF_g_cmd, W_LEN; lia
            | unfold off_window; rewrite Hsp; lia
            | Z.div_mod_to_equations; lia | exact Q1' | unfold off_world, W_BASE_UBSAN, W_LEN; lia
            | unfold off_window; rewrite Hsp; lia | lia | exact WC | exact CLSm
            | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST5 | rewrite Hsp; lia
            | unfold w_off_stack; rewrite Hsp; lia | exact MI5 ]. }
        intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 &
                    Eq & MUc & WMc & MI6 & ST6 & DSP & WM6).
        subst ms'. rewrite Hsp in MUc, ST6.
        pose proof (is_frame_back mC m6 B5 Bs p frame _ (proj1 KEEP) (proj2 KEEP) WM6
                      (is_cls_keep _ _ _ _ _ (wm_len rsegs W_BASE_UBSAN mC B5 WC) CLSm) MUc
                      ltac:(intros HA; cbn [disjoint_from]; repeat split; lia) AT) as BF6.
        clear WC KEEP.
        transport_after_call rsegs mC m6 MUc WMc. clear MUc WMc MI5. try clear mC.
        rewrite (ret_pc_even 0x14a70) by (first [lia | reflexivity]).
        step.                              (* lw a0,12(sp): display *)
        pose proof (is_cls_disp _ _ _ _ _ CLSm) as RD.
        rewrite is_sx32_small by lia.
        step.                              (* beqz a0 *)
        rewrite is_eqb_lit by lia.
        destruct (Z.eqb_spec disp 0) as [D0|D1]; cbv iota.
        * replace (truth disp) with false in B6m by (unfold truth; rewrite D0; reflexivity).
          cbv beta iota in B6m. injection B6m as <-.
          assert (R48 : ov_read_bytes rsegs m6 (Z_to_bv 64 (bv_unsigned sp + -112)) 4
                        = Some (sub (sf_bytes p (rf frame)) 32 4)).
          { replace (bv_unsigned sp + -112) with (bv_unsigned sp + -144 + 32) by lia.
            exact (bytes_at_read rsegs m6 _ _ 32 4 SB4 ltac:(lia) ltac:(rewrite SBL; lia)). }
          step. clear R48. rewrite ?wm_lw. (* lw a0,48(sp): f.send *)
          eapply FLY with (Bx := Bs); [is_fr_intro | reflexivity | exact EB2].
        * replace (truth disp) with true in B6m
            by (unfold truth; symmetry; apply negb_true_iff, Z.eqb_neq; exact D1).
          cbv beta iota in B6m.
          is_dmp B6m Bd CLDm.
          step.                            (* jal check_latest_display *)
          eapply evt_cut.
          { eapply CLD with (lo := lo) (B := Bs) (B' := Bd);
              [ exact WM6 | exact CLDm | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST6
              | rewrite Hsp; lia | unfold w_off_stack; rewrite Hsp; lia | exact MI6 ]. }
          intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 &
                      Eq & MUc & WMc & MI7 & ST7 & EB & WM7).
          subst ms'. rewrite Hsp in MUc, ST7. clear WM6. subst Bd.
          injection B6m as <-.
          transport_after_call rsegs m6 m7 MUc WMc. clear MUc WMc MI6. try clear m6.
          rewrite (ret_pc_even 0x14a7c) by (first [lia | reflexivity]).
          assert (LBs : Z.of_nat (length Bs) = 65616)
            by (rewrite (wm_len rsegs W_BASE_UBSAN m7 Bs WM7); vm_compute; reflexivity).
          step. change (u_at Bs 65000 8) with (g_now Bs).   (* ld a0,32(s4) *)
          step.                            (* li a1,1 *)
          step. is_wname WD1. rewrite is_w_lastd in WD1.     (* sd a0,64(s2) *)
          step. is_wname WD2. rewrite is_w_dsent in WD2. is_mname mD.   (* sw a1,72(s2) *)
          assert (CMt : set_M_display_sent (set_M_last_display Bs (g_now Bs)) 1
                        = set_M_last_display (set_M_display_sent Bs 1) (g_now Bs)).
          { rewrite <- !is_w_lastd, <- !is_w_dsent. apply upd_upd_comm; rewrite ?length_put; lia. }
          rewrite CMt in WD2.
          assert (R48 : ov_read_bytes rsegs mD (Z_to_bv 64 (bv_unsigned sp + -112)) 4
                        = Some (sub (sf_bytes p (rf frame)) 32 4)).
          { replace (bv_unsigned sp + -112) with (bv_unsigned sp + -144 + 32) by lia.
            exact (bytes_at_read rsegs mD _ _ 32 4 SB4 ltac:(lia) ltac:(rewrite SBL; lia)). }
          step. clear R48. rewrite ?wm_lw. (* lw a0,48(sp): f.send *)
          eapply FLY with (Bx := set_M_last_display (set_M_display_sent Bs 1) (g_now Bs));
            [is_fr_intro | reflexivity | exact EB2].
      + (* raw: nothing more *)
        assert (TG5 : truth (g_raw B5) = true) by (unfold truth; apply negb_true_iff, Z.eqb_neq; exact G51).
        assert (NG : negb (truth (g_raw B5)) = false) by (rewrite TG5; reflexivity).
        try (lazymatch type of B6m with (if ?c then _ else _) = _ =>
               replace c with false in B6m by (first [reflexivity | rewrite <- NG; reflexivity]) end).
        cbv beta iota in B6m. injection B6m as E6. subst B6.
        assert (R48 : ov_read_bytes rsegs mC (Z_to_bv 64 (bv_unsigned sp + -112)) 4
                      = Some (sub (sf_bytes p (rf frame)) 32 4)).
        { replace (bv_unsigned sp + -112) with (bv_unsigned sp + -144 + 32) by lia.
          exact (bytes_at_read rsegs mC _ _ 32 4 SB4 ltac:(lia) ltac:(rewrite SBL; lia)). }
        step. clear R48. rewrite ?wm_lw.   (* lw a0,48(sp): f.send *)
        eapply FLY with (Bx := B5); [is_fr_intro | exact L1 | exact EB2]. }
  (* -- 0x1499c: the command count loop (fuzz_transport.c:859-862) -- *)
  assert (LOOP : forall fuel pos cmds (m4 : word -> option byte) (cs1 : list cell)
                   (y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 S2 S6 : word),
    0 <= pos < sf_body_len (rf frame) -> 0 <= cmds < 2^32 ->
    S2 = Z_to_bv 64 (bv_swrap 32 cmds) -> S6 = Z_to_bv 64 pos ->
    cmds_loop fuel (set_g_fail_next B 0) (skipn (Z.to_nat (sf_body (rf frame))) frame) (sf_body_len (rf frame))
      pos cmds = Some cmdsM ->
    is_fr m m4 sp lo (set_g_fail_next B 0) p frame j0 cs1 (sf_bytes p (rf frame))
      [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    cells_size cs1 = 4%nat ->
    evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y2 y3 y4
                          (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p) y5
                          (Z_to_bv 64 (sf_body_len (rf frame))) y6 y7 y8 y9 y10 y11
                          S2 (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 274632) (Z_to_bv 64 (b2z (is_ka frame))) S6
                          s7 s8 s9 s10 s11 y12 y13 y14 y15)
                     F (Z_to_bv 64 0x1499c) fc None m4 (seg_rom rsegs))).
  { induction fuel as [|fuel IH];
      intros pos cmds m4 cs1 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 S2 S6 HP HC ES2 ES6 CL FR4 L1;
      [discriminate CL|].
    subst S2 S6.
    destruct FR4 as (MU4 & WM4 & MI4 & ST4 & WMm4 & Q0 & Q1 & SB4 & SW4 & Q3 & BF4).
    assert (R64 : ov_read_bytes rsegs m4 (Z_to_bv 64 (bv_unsigned sp + -96)) 8
                  = Some (sub (sf_bytes p (rf frame)) 48 8)).
    { replace (bv_unsigned sp + -96) with (bv_unsigned sp + -144 + 48) by lia.
      exact (bytes_at_read rsegs m4 _ _ 48 8 SB4 ltac:(lia) ltac:(rewrite SBL; lia)). }
    step. clear R64. rewrite ?wm_ld, Fbody. (* ld a2,64(sp) *)
    step.                                  (* add a0,s6,a2 *)
    step.                                  (* bltu a0,a2 -> trap *)
    rewrite is_ltu_lit by lia.
    destruct (Z.ltb_spec (pos + (p + 30)) (p + 30)); [lia|]. cbv iota.
    do 3 step.                             (* snez a2,a2; seqz a3,a0; xor a2,a2,a3 *)
    step.                                  (* beqz a2 -> trap *)
    rewrite is_ptrchk by lia. cbv iota.
    step.                                  (* sub a1,a1,s6 *)
    step.                                  (* jal tagged_of *)
    destruct (is_cl_step fuel (set_g_fail_next B 0) (skipn (Z.to_nat (sf_body (rf frame))) frame)
                (sf_body_len (rf frame)) pos cmds cmdsM ltac:(lia) CL) as (Bt & t & TOm & SNZ & CL').
    pose proof (is_tof _ _ _ _ _ TOm) as [EBt Ht]. subst Bt.
    eapply evt_cut.
    { eapply TOF with (p := pos + (p + 30)) (n := sf_body_len (rf frame) - pos) (lo := lo)
        (B := set_g_fail_next B 0) (B' := set_g_fail_next B 0) (t := t)
        (b := skipn (Z.to_nat pos) (skipn (Z.to_nat (sf_body (rf frame))) frame));
        [ is_regeq | is_regeq | lia | lia
        | rewrite Hbody; replace (pos + (p + 30)) with (p + 30 + pos) by lia;
          apply is_ba_skipn; [lia | rewrite length_skipn; lia | apply (is_ba_skipn m4 p frame 30); [lia | lia | exact BF4]]
        | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST4 | rewrite Hsp; lia
        | unfold w_off_stack; rewrite Hsp; lia | exact MI4 | exact WMm4 | exact TOm ]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 &
                Eq & MUc & WMc & MI5 & ST5 & EB & WM5).
    subst ms'. rewrite Hsp in MUc, ST5. clear EB WMm4.
    transport_after_call rsegs m4 m5 MUc WMc. clear MUc WMc MI4. try clear m4.
    rewrite (ret_pc_even 0x149c0) by (first [lia | reflexivity]).
    assert (R72 : ov_read_bytes rsegs m5 (Z_to_bv 64 (bv_unsigned sp + -88)) 8
                  = Some (sub (sf_bytes p (rf frame)) 56 8)).
    { replace (bv_unsigned sp + -88) with (bv_unsigned sp + -144 + 56) by lia.
      exact (bytes_at_read rsegs m5 _ _ 56 8 SB4 ltac:(lia) ltac:(rewrite SBL; lia)). }
    (* the step of this round: the command's length, or the rest of the body *)
    assert (TAIL : forall (stp : Z) (z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 : word),
      stp = match t with Some s => Cmd_len (set_g_fail_next B 0) s | None => sf_body_len (rf frame) - pos end ->
      evt rsegs QQ (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp z2 z3 z4
                            (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p) (Z_to_bv 64 stp)
                            (Z_to_bv 64 (sf_body_len (rf frame))) z5 z6 z7 z8 z9 z10
                            (Z_to_bv 64 (bv_swrap 32 cmds)) (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 274632)
                            (Z_to_bv 64 (b2z (is_ka frame))) (Z_to_bv 64 pos)
                            s7 s8 s9 s10 s11 z11 z12 z13 z14)
                       F (Z_to_bv 64 0x149e0) fc None m5 (seg_rom rsegs))).
    { intros stp z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 Estp.
      assert (RS : 0 < stp < 2^16).
      { rewrite Estp. destruct t as [s|].
        - pose proof (u_at_range (set_g_fail_next B 0) (A_Cmd_len s) 1) as RCL0.
          change (u_at (set_g_fail_next B 0) (A_Cmd_len s) 1) with (Cmd_len (set_g_fail_next B 0) s) in RCL0.
          change (2 ^ (8 * Z.of_nat 1)) with 256 in RCL0. lia.
        - lia. }
      rewrite <- Estp in SNZ, CL'.
      step.                                (* add s6,a0,s6 *)
      step.                                (* addiw s2,s2,1 *)
      rewrite is_addiw_sw.
      step.                                (* bltu s6,a1 *)
      rewrite is_ltu_lit by lia.
      destruct (Z.ltb_spec (stp + pos) (sf_body_len (rf frame))) as [LT|GE]; cbv iota.
      - eapply IH with (pos := pos + stp) (cmds := u32 (cmds + 1));
          [ lia | unfold u32; apply Z.mod_pos_bound; lia | reflexivity | is_regeq | exact CL'
          | is_fr_intro | exact L1 ].
      - pose proof (is_cl_end fuel (set_g_fail_next B 0) (skipn (Z.to_nat (sf_body (rf frame))) frame)
                      (sf_body_len (rf frame)) (pos + stp) (u32 (cmds + 1)) cmdsM ltac:(lia) CL') as CM.
        step.                              (* j 149fc *)
        eapply CONT; [ rewrite CM; reflexivity | is_fr_intro | exact L1 ]. }
    destruct t as [s|].
    - cbv beta iota in Ht. unfold CMDS_MAX in Ht.
      rewrite is_tret.
      step.                                (* beqz a0 *)
      rewrite is_eqb_ulit by lia.
      replace (229576 + 40 * s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step.                                (* andi a1,a0,3 *)
      rewrite is_al4 by lia.
      step.                                (* bnez a1 -> trap *)
      try (rewrite is_eqb_ulit by lia). try rewrite Z.eqb_refl. cbv beta iota delta [negb].
      assert (RCL : ov_read_bytes rsegs m5 (Z_to_bv 64 (229576 + 40 * s + 36)) 1
                    = Some (sub (set_g_fail_next B 0) (A_Cmd_len s) 1)).
      { apply (wm_read rsegs W_BASE_UBSAN m5 (set_g_fail_next B 0) (A_Cmd_len s) 1);
          [ exact WM5 | unfold A_Cmd_len, OFF_g_cmd; lia | unfold A_Cmd_len, OFF_g_cmd; lia
          | unfold A_Cmd_len, OFF_g_cmd; f_equal; lia ]. }
      step.                                (* lbu a0,36(a0): t->len *)
      clear RCL. rewrite ?wm_lbu.
      try change (u_at (set_g_fail_next B 0) (A_Cmd_len s) 1) with (Cmd_len (set_g_fail_next B 0) s).
      step. clear R72. rewrite ?wm_ld, Fblen.   (* ld a1,72(sp) *)
      step.                                (* j 149e0 *)
      eapply TAIL; reflexivity.
    - change (tagged_of_ret None) with 0.
      step.                                (* beqz a0 *)
      rewrite is_eqb_ulit by lia. rewrite Z.eqb_refl. cbv iota.
      step. clear R72. rewrite ?wm_ld, Fblen.   (* ld a1,72(sp) *)
      step.                                (* sub a0,a1,s6 *)
      eapply TAIL; is_regeq. }
  (* -- 0x14978: display = 0, check_inflight_new, the command count -- *)
  assert (D78 : forall (y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 S5 : word),
    S5 = Z_to_bv 64 (b2z (is_ka frame)) ->
    evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp y2 y3 y4
                          (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p) y5 y6 y7 y8 y9 y10 y11 y12
                          y13 (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 274632) S5 y14
                          s7 s8 s9 s10 s11 y15 y16 y17 y18)
                     F (Z_to_bv 64 0x14978) fc None m3 (seg_rom rsegs))).
  { intros d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 S5 ES5. subst S5.
    step. is_mname mD.                     (* sw zero,12(sp): display = 0 *)
    step.                                  (* jal check_inflight_new *)
    eapply evt_cut.
    { eapply CIN with (lo := lo) (B := set_g_fail_next B 0) (B' := set_g_fail_next B 0);
        [ exact WM3 | exact CINm | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact ST3
        | rewrite Hsp; lia | unfold w_off_stack; rewrite Hsp; lia | exact MI3 ]. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 &
                Eq & MUc & WMc & MI4 & ST4 & EB & WM4).
    subst ms'. rewrite Hsp in MUc, ST4. clear WM3 EB.
    transport_after_call rsegs mD m4 MUc WMc. clear MUc WMc MI3. try clear mD.
    rewrite (ret_pc_even 0x14980) by (first [lia | reflexivity]).
    step.                                  (* lw a0,4(s4): g_raw *)
    change (s32_at (set_g_fail_next B 0) 64972) with (g_raw (set_g_fail_next B 0)).
    step.                                  (* bnez a0 *)
    rewrite is_eqb_lit by lia.
    destruct (Z.eqb_spec (g_raw (set_g_fail_next B 0)) 0) as [GR0|GR1]; cbv beta iota delta [negb].
    2: { (* g_raw: cmds = f.ncmds *)
      assert (TG : truth (g_raw (set_g_fail_next B 0)) = true)
        by (unfold truth; apply negb_true_iff, Z.eqb_neq; exact GR1).
      rewrite TG in CMDm. cbv beta iota delta [negb andb] in CMDm. injection CMDm as CM.
      assert (R57 : ov_read_bytes rsegs m4 (Z_to_bv 64 (bv_unsigned sp + -103)) 1
                    = Some (sub (sf_bytes p (rf frame)) 41 1)).
      { replace (bv_unsigned sp + -103) with (bv_unsigned sp + -144 + 41) by lia.
        exact (bytes_at_read rsegs m4 _ _ 41 1 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
      step. clear R57. rewrite ?wm_lbu, Fncmds.   (* lbu s2,57(sp) *)
      step.                                (* j 149fc *)
      eapply CONT.
      - rewrite <- CM, is_swrap32_small by lia. reflexivity.
      - is_fr_intro.
      - reflexivity. }
    assert (TG : truth (g_raw (set_g_fail_next B 0)) = false) by (unfold truth; rewrite GR0; reflexivity).
    rewrite TG in CMDm.
    step.                                  (* bnez s5 *)
    rewrite is_eqb_lit by (unfold b2z; destruct (is_ka frame); lia).
    assert (KAD : is_ka frame = true \/ is_ka frame = false) by (destruct (is_ka frame); auto).
    destruct KAD as [KAT|KAF].
    { (* a keepalive: cmds = f.ncmds *)
      replace (b2z (is_ka frame) =? 0) with false by (rewrite KAT; reflexivity). cbv beta iota delta [negb].
      rewrite KAT in CMDm. cbv beta iota delta [negb andb] in CMDm. injection CMDm as CM.
      assert (R57 : ov_read_bytes rsegs m4 (Z_to_bv 64 (bv_unsigned sp + -103)) 1
                    = Some (sub (sf_bytes p (rf frame)) 41 1)).
      { replace (bv_unsigned sp + -103) with (bv_unsigned sp + -144 + 41) by lia.
        exact (bytes_at_read rsegs m4 _ _ 41 1 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
      step. clear R57. rewrite ?wm_lbu, Fncmds.   (* lbu s2,57(sp) *)
      step.                                (* j 149fc *)
      eapply CONT.
      - rewrite <- CM, is_swrap32_small by lia. reflexivity.
      - is_fr_intro.
      - reflexivity. }
    replace (b2z (is_ka frame) =? 0) with true by (rewrite KAF; reflexivity). cbv beta iota delta [negb].
    rewrite KAF in CMDm. cbv beta iota delta [negb andb] in CMDm.
    assert (R72 : ov_read_bytes rsegs m4 (Z_to_bv 64 (bv_unsigned sp + -88)) 8
                  = Some (sub (sf_bytes p (rf frame)) 56 8)).
    { replace (bv_unsigned sp + -88) with (bv_unsigned sp + -144 + 56) by lia.
      exact (bytes_at_read rsegs m4 _ _ 56 8 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
    step. clear R72. rewrite ?wm_ld, Fblen.  (* ld a1,72(sp) *)
    step.                                  (* beqz a1 *)
    rewrite is_eqb_lit by lia.
    destruct (Z.eqb_spec (sf_body_len (rf frame)) 0) as [BL0|BLN]; cbv iota.
    - (* no body: cmds = 0 *)
      assert (CM : cmdsM = 0).
      { rewrite BL0 in CMDm. simpl in CMDm. injection CMDm as <-. reflexivity. }
      step.                                (* li s2,0 *)
      eapply CONT.
      + rewrite CM. reflexivity.
      + is_fr_intro.
      + reflexivity.
    - step. step.                          (* li s2,0; li s6,0 *)
      eapply LOOP with (fuel := S (Z.to_nat (sf_body_len (rf frame)))) (pos := 0) (cmds := 0).
      + lia.
      + lia.
      + reflexivity.
      + reflexivity.
      + exact CMDm.
      + is_fr_intro.
      + reflexivity. }
  (* -- 0x14958: the keepalive test (s5) -- *)
  assert (R72 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + -88)) 8
                = Some (sub (sf_bytes p (rf frame)) 56 8)).
  { replace (bv_unsigned sp + -88) with (bv_unsigned sp + -144 + 56) by lia.
    exact (bytes_at_read rsegs m3 _ _ 56 8 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
  step. clear R72. rewrite ?wm_ld, Fblen.  (* ld a0,72(sp) *)
  step. step.                              (* li a1,1; bne a0,a1 *)
  rewrite is_eqb_lit by lia.
  destruct (Z.eqb_spec (sf_body_len (rf frame)) 1) as [BL1|BL1]; cbv beta iota delta [negb].
  2: { assert (KAF : is_ka frame = false).
       { unfold is_ka. replace (sf_body_len (rf frame) =? 1) with false by (symmetry; apply Z.eqb_neq; exact BL1).
         reflexivity. }
       step.                               (* li s5,0 *)
       eapply D78. rewrite KAF. reflexivity. }
  assert (R64 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + -96)) 8
                = Some (sub (sf_bytes p (rf frame)) 48 8)).
  { replace (bv_unsigned sp + -96) with (bv_unsigned sp + -144 + 48) by lia.
    exact (bytes_at_read rsegs m3 _ _ 48 8 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
  step. clear R64. rewrite ?wm_ld, Fbody.  (* ld a0,64(sp): f.body *)
  step.                                    (* beqz a0 *)
  rewrite is_eqb_ulit by lia.
  replace (p + 30 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  assert (RB : ov_read_bytes rsegs m3 (Z_to_bv 64 (p + 30)) 1 = Some (sub frame 30 1)).
  { exact (bytes_at_read rsegs m3 p frame 30 1 BF ltac:(lia) ltac:(lia)). }
  step. clear RB. rewrite ?wm_lbu.         (* lbu a0,0(a0): body[0] *)
  rewrite (is_u_at1 frame 30) by lia.
  pose proof (at8_range (skipn (Z.to_nat 30) frame) 0) as RA.
  step.                                    (* beqz a0 *)
  rewrite is_eqb_lit by lia.
  destruct (Z.eqb_spec (at8 (skipn (Z.to_nat 30) frame) 0) 0) as [AZ|ANZ]; cbv iota.
  2: { assert (KAF : is_ka frame = false).
       { unfold is_ka. rewrite Hbody.
         replace (at8 (skipn (Z.to_nat 30) frame) 0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact ANZ).
         rewrite andb_false_r. reflexivity. }
       step.                               (* li s5,0 *)
       eapply D78. rewrite KAF. reflexivity. }
  (* 0x14b0c: s5 = (f.ncmds == 1) *)
  assert (R57 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + -103)) 1
                = Some (sub (sf_bytes p (rf frame)) 41 1)).
  { replace (bv_unsigned sp + -103) with (bv_unsigned sp + -144 + 41) by lia.
    exact (bytes_at_read rsegs m3 _ _ 41 1 SBAT ltac:(lia) ltac:(rewrite SBL; lia)). }
  step. clear R57. rewrite ?wm_lbu, Fncmds.   (* lbu a0,57(sp) *)
  step. step.                              (* addi a0,a0,-1; seqz s5,a0 *)
  rewrite ?unsigned_lit by lia.
  rewrite is_seqz_dec by lia.
  step.                                    (* j 14978 *)
  eapply D78. unfold is_ka. rewrite Hbody, BL1, AZ. reflexivity.
Qed.

Print Assumptions io_send_holds.
