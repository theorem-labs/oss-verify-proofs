(* Model facts the ubsan walk of on_announce (transport/src/diginet_session.c:184-221; TSess.v on_announce_m) uses
   beyond its callee contracts: on_announce_m cut at the points where the binary's paths meet, the world after the
   session's own stores, the DESK and FOREIGN notices keeping the one-byte g_fail_next, the personality pointer
   diginet_personality_from_name returns, and bcmp's answer as the model's memeq. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require codec_cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU.
Import ListNotations.
Open Scope Z_scope.

(* ---- on_announce_m, cut where the binary's paths meet ---- *)

(* the announce a the notices carry, and the name diginet_personality_from_name reads (:191) *)
Definition oa_ann (b : list byte) : tann :=
  TAnn (ann_field (skipn 15 (fr_body b))) (ann_field (skipn 24 (fr_body b))).
Definition oa_name (b : list byte) : list byte :=
  firstn (copy_len 10 9 (skipn 24 (fr_body b))) (skipn 24 (fr_body b)).
Definition oa_p (b : list byte) : option Z := diginet_personality_from_name (oa_name b).
Definition oa_pv (I : timg) (b : list byte) : Z :=
  match oa_p b with Some i => ti_personalities I + 24 * i | None => 0 end.
(* the world after :192-193 *)
Definition oa_B1 (I : timg) (B b : list byte) : list byte :=
  match oa_p b with Some _ => set_S_personality B (oa_pv I b) | None => B end.
(* :194 *)
Definition oa_off (B1 b : list byte) : Z :=
  if fr_cmd b =? DIGINET_CMD_ANNOUNCE_SESSION
  then find_mac_m (ann_unknown (fr_body b)) 15 (S_cfg_host_mac B1) else -1.

(* :204-206, from the world after :201-203 *)
Definition oa_wake_m (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * unit) :=
  if (S_state B =? DIGINET_S_IDLE) && negb (S_cfg_auto_wake B =? 0) then
    match diginet_session_wake_m I F B now with
    | None => None
    | Some (B, _) => Some (B, tt)
    end
  else Some (B, tt).

(* :200-220, from the world after the DESK notice *)
Definition oa_after_m (I : timg) (F : option tframe) (B : list byte) (b : list byte) (off now : Z)
    : option (list byte * unit) :=
  if fr_cmd b =? DIGINET_CMD_ANNOUNCE then
    let B := set_S_foreign B 0 in
    let lost := if S_state B =? DIGINET_S_ONLINE
                then session_lost_m I F B DIGINET_R_DESK_OFFLINE else Some (B, tt) in
    match lost with
    | None => None
    | Some (B, _) => oa_wake_m I F B now
    end
  else if 0 <=? off then
    let B := set_S_foreign B 0 in
    let B := set_S_e1_named_us B 1 in
    maybe_online_m I F B
  else
    let B := set_S_foreign B 1 in
    let fn := Ntc DIGINET_N_FOREIGN (S_state B) 0 0 0 0 0 0 (Some (oa_ann b)) [] 0 in
    match call_notify I F B fn with
    | None => None
    | Some (B, _) =>
        if (S_state B =? DIGINET_S_ONLINE) || (S_state B =? DIGINET_S_WAKING)
        then session_lost_m I F B DIGINET_R_FOREIGN else Some (B, tt)
    end.

(* :196-220, from the world B1 after :192-193, with the personality pointer pv and the offset off of :194 *)
Definition oa_desk_m (I : timg) (F : option tframe) (B1 : list byte) (b : list byte) (pv off now : Z)
    : option (list byte * unit) :=
  let n := Ntc DIGINET_N_DESK (S_state B1) 0 0 0 0 off pv (Some (oa_ann b)) [] 0 in
  match call_notify I F B1 n with
  | None => None
  | Some (B, _) => oa_after_m I F B b off now
  end.

Lemma on_announce_m_eq : forall I F B b now,
  on_announce_m I F B b now =
  if negb (ann_code (fr_cmd b) (fr_body_len b) =? DIGINET_OK)
  then Some (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)), tt)
  else oa_desk_m I F (oa_B1 I B b) b (oa_pv I b) (oa_off (oa_B1 I B b) b) now.
Proof. reflexivity. Qed.

(* ---- the DESK and FOREIGN notices write GOT only: g_fail_next stays ---- *)

(* check_state_desk answers None or the world it was given *)
Lemma oa_check_state_desk_same : forall I F X n B' u,
  check_state_desk_m I F X n = Some (B', u) -> B' = X.
Proof.
  intros I F X n B' u. unfold check_state_desk_m. cbv zeta.
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
  intros H; congruence.
Qed.

(* a write at or above GOT leaves the byte of g_fail_next *)
Lemma oa_g_fail_next_upd : forall B k v, length B = Z.to_nat W_LEN ->
  OFF_g_fail_next + 1 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  g_fail_next (upd B k v) = g_fail_next B.
Proof.
  intros B k v HL H1 H2. unfold g_fail_next. apply u_at_upd_out.
  - unfold OFF_g_fail_next in H1. lia.
  - unfold OFF_g_fail_next. lia.
  - left. lia.
  - rewrite HL, Z2Nat.id by (unfold W_LEN; lia). exact H2.
Qed.

Lemma notice_desk_fail_next : forall I F B n B', length B = Z.to_nat W_LEN -> n_kind n = DIGINET_N_DESK ->
  notice_m I F B n = Some (B', tt) -> g_fail_next B' = g_fail_next B.
Proof.
  intros I F B n B' HL Hk. unfold notice_m. rewrite Hk.
  cbv [DIGINET_N_DESK N_STATE N_ACKED N_ACK_LOST N_DESK]. cbn [Z.eqb Pos.eqb].
  destruct (int_inc (GOT_desk B)) as [d|]; [|intros H; discriminate H].
  intros H. apply oa_check_state_desk_same in H. subst B'.
  unfold set_GOT_desk. apply oa_g_fail_next_upd; [exact HL| |];
    rewrite ?length_put; unfold A_GOT_desk, OFF_GOT, OFF_g_fail_next, W_LEN; lia.
Qed.

Lemma notice_foreign_fail_next : forall I F B n B', length B = Z.to_nat W_LEN -> n_kind n = DIGINET_N_FOREIGN ->
  notice_m I F B n = Some (B', tt) -> g_fail_next B' = g_fail_next B.
Proof.
  intros I F B n B' HL Hk. unfold notice_m. rewrite Hk.
  cbv [DIGINET_N_FOREIGN N_STATE N_ACKED N_ACK_LOST N_DESK N_DATA N_FOREIGN]. cbn [Z.eqb Pos.eqb].
  destruct (int_inc (GOT_foreign B)) as [fo|]; [|intros H; discriminate H].
  intros H. inversion H; subst B'; clear H.
  unfold set_GOT_foreign. apply oa_g_fail_next_upd; [exact HL| |];
    rewrite ?length_put; unfold A_GOT_foreign, OFF_GOT, OFF_g_fail_next, W_LEN; lia.
Qed.

(* ---- the personality pointer (:191): diginet_personality_from_name's contract answers from_name_res of the
   10 bytes of a.name, which diginet_announce_parse filled as ann_name ---- *)

(* z_list_eqb decides equality of number lists *)
Lemma oa_z_list_eqb_eq : forall x y, z_list_eqb x y = true <-> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y]; cbn [z_list_eqb]; try (split; intros H; discriminate H).
  - split; intros _; reflexivity.
  - split.
    + intros H. apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst. reflexivity.
    + intros H. injection H as -> ->. apply andb_true_iff. split; [apply Z.eqb_refl | apply IH; reflexivity].
Qed.

(* the C string of copy_strz's field is the bytes it copied *)
Lemma oa_cstring_copy : forall n (l rest : list byte),
  codec_cells.cstring (codec_cells.zb (firstn (nz_run (firstn n l)) l ++ b8 0 :: rest)) =
  map bz (firstn (nz_run (firstn n l)) l).
Proof.
  unfold codec_cells.zb. induction n as [|n IH]; intros [|x l] rest; try reflexivity.
  cbn [firstn nz_run]. destruct (bz x =? 0) eqn:E; [reflexivity|].
  cbn [firstn app map codec_cells.cstring]. unfold bz in E. rewrite E.
  change (bz x) with (bv_unsigned x). f_equal. apply IH.
Qed.

(* personality_name_find over the two personalities *)
Lemma oa_pnf : forall L, personality_name_find personalities 0 L =
  if z_list_eqb L codec_cells.NAME_C24 then Some 0 else if z_list_eqb L codec_cells.NAME_PC then Some 1 else None.
Proof. reflexivity. Qed.

Lemma from_name_res_pv : forall b old,
  codec_cells.from_name_res (ann_name (fr_body b) old) = oa_pv timg_ubsan b.
Proof.
  intros b old. unfold codec_cells.from_name_res, ann_name, copy_strz.
  change (copy_len 10 9 (skipn 24 (fr_body b))) with (nz_run (firstn 9 (skipn 24 (fr_body b)))).
  rewrite oa_cstring_copy.
  unfold oa_pv, oa_p, oa_name, diginet_personality_from_name.
  change (copy_len 10 9 (skipn 24 (fr_body b))) with (nz_run (firstn 9 (skipn 24 (fr_body b)))).
  rewrite oa_pnf.
  destruct (list_eq_dec Z.eq_dec (map bz (firstn (nz_run (firstn 9 (skipn 24 (fr_body b)))) (skipn 24 (fr_body b))))
    codec_cells.NAME_C24) as [E1|E1].
  - rewrite E1. reflexivity.
  - destruct (list_eq_dec Z.eq_dec (map bz (firstn (nz_run (firstn 9 (skipn 24 (fr_body b)))) (skipn 24 (fr_body b))))
      codec_cells.NAME_PC) as [E2|E2].
    + rewrite E2. reflexivity.
    + destruct (z_list_eqb (map bz (firstn (nz_run (firstn 9 (skipn 24 (fr_body b)))) (skipn 24 (fr_body b))))
        codec_cells.NAME_C24) eqn:Z1; [apply oa_z_list_eqb_eq in Z1; contradiction|].
      destruct (z_list_eqb (map bz (firstn (nz_run (firstn 9 (skipn 24 (fr_body b)))) (skipn 24 (fr_body b))))
        codec_cells.NAME_PC) eqn:Z2; [apply oa_z_list_eqb_eq in Z2; contradiction|].
      reflexivity.
Qed.

Lemma oa_pv_cases : forall B b,
  (oa_pv timg_ubsan b = 0 /\ oa_B1 timg_ubsan B b = B) \/
  (0 < oa_pv timg_ubsan b < 2^63 /\ oa_B1 timg_ubsan B b = set_S_personality B (oa_pv timg_ubsan b)).
Proof.
  intros B b. unfold oa_B1. unfold oa_pv. unfold oa_p. unfold diginet_personality_from_name. rewrite oa_pnf.
  destruct (z_list_eqb (map bz (oa_name b)) codec_cells.NAME_C24);
    [|destruct (z_list_eqb (map bz (oa_name b)) codec_cells.NAME_PC)].
  - right. split; [unfold timg_ubsan; cbn [ti_personalities]; lia | reflexivity].
  - right. split; [unfold timg_ubsan; cbn [ti_personalities]; lia | reflexivity].
  - left. split; reflexivity.
Qed.

(* ---- bcmp's answer (U/Spec/StrFun.v memcmp_model) against the model's memeq (TSess0.v) ---- *)

Lemma oa_forallb_map : forall {A C} (f : C -> bool) (g : A -> C) l, forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof. intros A C f g l. induction l as [|a l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma oa_memeq_cons : forall n a l b r,
  memeq (S n) (a :: l) (b :: r) = (bv_unsigned a =? bv_unsigned b) && memeq n l r.
Proof.
  intros n a l b r. unfold memeq. cbn [seq forallb]. rewrite <- seq_shift, oa_forallb_map. reflexivity.
Qed.

Lemma oa_byte_range : forall x : byte, 0 <= bv_unsigned x < 256.
Proof.
  intros x. pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma memcmp_memeq : forall n l r, (n <= length l)%nat -> (n <= length r)%nat ->
  exists v, StrFun.memcmp_model l r n = Some v /\ -256 < v < 256 /\ (v =? 0) = memeq n l r.
Proof.
  intros n. induction n as [|n IH]; intros l r Hl Hr.
  - exists 0. split; [reflexivity|]. split; [lia | reflexivity].
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn [length] in Hl, Hr. rewrite oa_memeq_cons. cbn [StrFun.memcmp_model].
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + cbn [andb]. apply IH; lia.
    + exists (bv_unsigned a - bv_unsigned b). pose proof (oa_byte_range a). pose proof (oa_byte_range b).
      split; [reflexivity|]. split; [lia|]. cbn [andb]. apply Z.eqb_neq. lia.
Qed.

(* find_mac's result is -1 or an index the loop reached *)
Lemma find_mac_loop_range : forall U mac i f, 0 <= i ->
  -1 <= find_mac_loop U mac i f < i + Z.of_nat f.
Proof.
  intros U mac i f. revert i. induction f as [|f IH]; intros i Hi; cbn [find_mac_loop].
  - lia.
  - destruct (memeq 6 _ mac); [lia|]. specialize (IH (i + 1) ltac:(lia)). lia.
Qed.

(* ---- the session's own stores, in the binary's form ---- *)

(* two bytes that agree mod 2^8 head equal byte lists *)
Lemma oa_cons_bv8 : forall a b (l l' : list byte), a mod 2^8 = b mod 2^8 -> l = l' ->
  Z_to_bv 8 a :: l = Z_to_bv 8 b :: l'.
Proof.
  intros a b l l' H E. subst l'. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H.
Qed.

Lemma oa_put8_split : put 8 4294967296 = put 4 0 ++ put 4 1.
Proof.
  unfold put. cbn [Z_to_le_bytes app].
  repeat (apply oa_cons_bv8; [reflexivity|]). reflexivity.
Qed.

(* a write of v ++ w is the write of v, then the write of w after it *)
Lemma oa_upd_app : forall (bs v w : list byte) k k', 0 <= k -> k' = k + Z.of_nat (length v) ->
  k + Z.of_nat (length v) + Z.of_nat (length w) <= Z.of_nat (length bs) ->
  upd bs k (v ++ w) = upd (upd bs k v) k' w.
Proof.
  intros bs v w k k' Hk Hk' Hl.
  assert (L1 : length (upd bs k v) = length bs) by (apply length_upd; lia).
  apply nth_error_ext. intros i.
  rewrite (ne_upd (upd bs k v) w k' i) by (rewrite ?L1; lia).
  rewrite (ne_upd bs v k i) by lia.
  rewrite (ne_upd bs (v ++ w) k i) by (rewrite ?length_app; lia).
  rewrite length_app.
  replace (Z.to_nat k') with (Z.to_nat k + length v)%nat by lia.
  repeat match goal with
  | |- context [(?a <=? ?b)%nat] => destruct (Nat.leb_spec a b)
  | |- context [(?a <? ?b)%nat] => destruct (Nat.ltb_spec a b)
  end; cbn [andb]; try lia; try reflexivity.
  all: first [ rewrite nth_error_app2 by lia; f_equal; lia | rewrite nth_error_app1 by lia; reflexivity ].
Qed.

(* :211-212 as the one store sd a0, 136(s0) with a0 = 1 << 32 *)
Lemma foreign_e1_store : forall B, length B = Z.to_nat W_LEN ->
  set_S_e1_named_us (set_S_foreign B 0) 1 = upd B A_S_foreign (put 8 4294967296).
Proof.
  intros B HL. unfold set_S_e1_named_us, set_S_foreign. symmetry.
  rewrite oa_put8_split. apply oa_upd_app.
  - unfold A_S_foreign, OFF_g_s. lia.
  - rewrite length_put. unfold A_S_e1_named_us, A_S_foreign, OFF_g_s. lia.
  - rewrite !length_put, HL, Z2Nat.id by (unfold W_LEN; lia). unfold A_S_foreign, OFF_g_s, W_LEN. lia.
Qed.
