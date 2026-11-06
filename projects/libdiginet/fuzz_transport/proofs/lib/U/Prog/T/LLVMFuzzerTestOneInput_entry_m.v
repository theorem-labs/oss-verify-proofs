(* The model side of the entry of LLVMFuzzerTestOneInput (fuzz_transport.c:1124-1166; TModel/TOps.v:351-397): the
   prologue of LLVMFuzzerTestOneInput_m up to diginet_session_init as one world function, the config bytes read
   from the cursor in a closed form (cbyte / cur), and the world algebra the machine's store order needs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TCb TSess0 TOps.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the prologue of the model *)

(* TOps.v:353-391, verbatim: the world diginet_session_init is called on (B24), from the world after
   diginet_session_config_default (B1). *)
Definition ent_B24 (D : list byte) (B1 : list byte) : list byte :=
  let size := Z.of_nat (length D) in
  let c0 := fuzz_in_m size in
  let (c1, flags) := fuzz_u8_m D c0 in
  let B2 := set_Cfg_host_mac B1 HOST in
  let B3 := set_Cfg_auto_wake B2 (Z.land flags 1) in
  let B4 := set_Cfg_sum_mode B3
              (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO) in
  let B5 := set_Cfg_desk_mac_set B4 (Z.land (Z.shiftr flags 2) 1) in
  let B6 := set_Cfg_desk_mac B5 DESK in
  let (c2, v1) := fuzz_u8_m D c1 in
  let B7 := set_Cfg_max_retries B6 (v1 mod 8) in
  let (c3, v2) := fuzz_u8_m D c2 in
  let B8 := set_Cfg_ack_timeout_ms B7 ((1 + v2) mod 2^32) in
  let (c4, v3) := fuzz_u16_m D c3 in
  let B9 := set_Cfg_keepalive_ms B8 ((1 + v3) mod 2^32) in
  let (c5, v4) := fuzz_u8_m D c4 in
  let B10 := set_Cfg_backoff_ms B9 v4 in
  let (c6, v5) := fuzz_u16_m D c5 in
  let B11 := set_Cfg_offline_ms B10 ((1 + v5) mod 2^32) in
  let (c7, v6) := fuzz_u16_m D c6 in
  let B12 := set_Cfg_wake_timeout_ms B11 ((1 + v6) mod 2^32) in
  let (c8, v7) := fuzz_u16_m D c7 in
  let B13 := set_Cfg_display_gap_us B12 v7 in
  let (c9, v8) := fuzz_u8_m D c8 in
  let B14 := set_Cfg_max_cmds B13 ((1 + v8 mod 255) mod 2^32) in
  let (c10, v9) := fuzz_u16_m D c9 in
  let B15 := set_Cfg_max_body B14
               ((SPEC_CMD_MAX + v9 mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2^32) in
  let B16 := set_g_raw B15 (Z.land (Z.shiftr flags 3) 1) in
  let B17 := set_g_now B16 1000000 in
  let B18 := set_g_fail_next B17 0 in
  let B19 := set_g_last_counter B18 0 in
  let B20 := upd B19 OFF_M (repeat (b8 0) (Z.to_nat SZ_M)) in
  let B21 := set_M_desk_known B20 (Cfg_desk_mac_set B20) in
  let B22 := set_M_desk B21 DESK in
  let B23 := set_g_ncmd (set_g_nq B22 0) 0 in
  let B24 := set_g_rx B23 0 in
  B24.

(* the cursor after the config (c10) *)
Definition ent_c10 (D : list byte) : fuzz_in :=
  let size := Z.of_nat (length D) in
  let c0 := fuzz_in_m size in
  let (c1, flags) := fuzz_u8_m D c0 in
  let (c2, v1) := fuzz_u8_m D c1 in
  let (c3, v2) := fuzz_u8_m D c2 in
  let (c4, v3) := fuzz_u16_m D c3 in
  let (c5, v4) := fuzz_u8_m D c4 in
  let (c6, v5) := fuzz_u16_m D c5 in
  let (c7, v6) := fuzz_u16_m D c6 in
  let (c8, v7) := fuzz_u16_m D c7 in
  let (c9, v8) := fuzz_u8_m D c8 in
  let (c10, v9) := fuzz_u16_m D c9 in
  c10.

Lemma ent_model : forall I B A D, Z.of_nat (length D) < FUZZ_INPUT_MAX ->
  LLVMFuzzerTestOneInput_m I B A D =
  match diginet_session_config_default_m B with
  | Some (B1, _) =>
      match diginet_session_init_m (ent_B24 D B1) 0 (ti_io_send I) (ti_io_recv I) (ti_io_now I) (ti_notice I) 0 with
      | Some (B25, rc) =>
          if negb (rc =? SPEC_OK) then None
          else match LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) I B25 A D (ent_c10 D) O with
               | Some (B26, _) => Some (B26, 0)
               | None => None
               end
      | None => None
      end
  | None => None
  end.
Proof.
  intros I B A D HS. unfold LLVMFuzzerTestOneInput_m, ent_B24, ent_c10. cbv zeta.
  destruct (FUZZ_INPUT_MAX <=? Z.of_nat (length D)) eqn:E; [apply Z.leb_le in E; lia|].
  destruct (fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D)))) as [c1 flags].
  destruct (diginet_session_config_default_m B) as [[B1 u]|]; [|cbv beta iota; reflexivity].
  destruct (fuzz_u8_m D c1) as [c2 v1].
  destruct (fuzz_u8_m D c2) as [c3 v2].
  destruct (fuzz_u16_m D c3) as [c4 v3].
  destruct (fuzz_u8_m D c4) as [c5 v4].
  destruct (fuzz_u16_m D c5) as [c6 v5].
  destruct (fuzz_u16_m D c6) as [c7 v6].
  destruct (fuzz_u16_m D c7) as [c8 v7].
  destruct (fuzz_u8_m D c8) as [c9 v8].
  destruct (fuzz_u16_m D c9) as [c10 v9].
  cbv beta iota.
  lazymatch goal with |- ?a = ?a => reflexivity end.
Qed.

(* ---------------------------------------------------------------- the config bytes in closed form *)

(* the k-th byte after the cursor (FuzzIn o n), 0 past its end *)
Definition cbyte (D : list byte) (o n k : Z) : Z := if k <? n then at8 D (Z.to_nat (o + k)) else 0.

(* the cursor (FuzzIn o n) after k bytes were asked for *)
Definition cur (o n k : Z) : fuzz_in := FuzzIn (o + Z.min k n) (n - Z.min k n).

Lemma cur0 : forall o n, 0 <= n -> cur o n 0 = FuzzIn o n.
Proof. intros o n Hn. unfold cur. rewrite Z.min_l by lia. f_equal; lia. Qed.

Lemma fu8_cur : forall D o n k k', 0 <= n -> 0 <= k -> k' = k + 1 ->
  fuzz_u8_m D (cur o n k) = (cur o n k', cbyte D o n k).
Proof.
  intros D o n k k' Hn Hk ->. unfold fuzz_u8_m, cur, cbyte. cbn [fi_off fi_n].
  destruct (Z.ltb_spec k n) as [L|L].
  - rewrite (Z.min_l k n), (Z.min_l (k + 1) n) by lia.
    destruct (Z.eqb_spec (n - k) 0) as [E|E]; [lia|].
    f_equal. f_equal; lia.
  - rewrite (Z.min_r k n), (Z.min_r (k + 1) n) by lia.
    destruct (Z.eqb_spec (n - n) 0) as [E|E]; [reflexivity | lia].
Qed.

Lemma fu16_cur : forall D o n k k1 k', 0 <= n -> 0 <= k -> k1 = k + 1 -> k' = k + 2 ->
  fuzz_u16_m D (cur o n k) =
  (cur o n k', Z.lor (cbyte D o n k) (Z.shiftl (cbyte D o n k1) 8) mod 2^16).
Proof.
  intros D o n k k1 k' Hn Hk -> ->. unfold fuzz_u16_m.
  rewrite (fu8_cur D o n k (k + 1)) by lia.
  rewrite (fu8_cur D o n (k + 1) (k + 2)) by lia.
  reflexivity.
Qed.

(* ---------------------------------------------------------------- the world of the model in stages *)

(* B2 .. B6: g_cfg.host_mac, auto_wake, sum_mode, desk_mac_set, desk_mac from the flags byte *)
Definition ent_W6 (flags : Z) (B1 : list byte) : list byte :=
  let B2 := set_Cfg_host_mac B1 HOST in
  let B3 := set_Cfg_auto_wake B2 (Z.land flags 1) in
  let B4 := set_Cfg_sum_mode B3
              (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO) in
  let B5 := set_Cfg_desk_mac_set B4 (Z.land (Z.shiftr flags 2) 1) in
  set_Cfg_desk_mac B5 DESK.

(* B7 .. B14: the config fields from the bytes cb 0 .. cb 11 *)
Definition ent_W14 (cb : Z -> Z) (B6 : list byte) : list byte :=
  let B7 := set_Cfg_max_retries B6 (cb 0 mod 8) in
  let B8 := set_Cfg_ack_timeout_ms B7 ((1 + cb 1) mod 2^32) in
  let B9 := set_Cfg_keepalive_ms B8 ((1 + Z.lor (cb 2) (Z.shiftl (cb 3) 8) mod 2^16) mod 2^32) in
  let B10 := set_Cfg_backoff_ms B9 (cb 4) in
  let B11 := set_Cfg_offline_ms B10 ((1 + Z.lor (cb 5) (Z.shiftl (cb 6) 8) mod 2^16) mod 2^32) in
  let B12 := set_Cfg_wake_timeout_ms B11 ((1 + Z.lor (cb 7) (Z.shiftl (cb 8) 8) mod 2^16) mod 2^32) in
  let B13 := set_Cfg_display_gap_us B12 (Z.lor (cb 9) (Z.shiftl (cb 10) 8) mod 2^16) in
  set_Cfg_max_cmds B13 ((1 + cb 11 mod 255) mod 2^32).

(* B15 .. B24: max_body from v9, the scalars, M *)
Definition ent_Wt (flags v9 : Z) (B14 : list byte) : list byte :=
  let B15 := set_Cfg_max_body B14
               ((SPEC_CMD_MAX + v9 mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2^32) in
  let B16 := set_g_raw B15 (Z.land (Z.shiftr flags 3) 1) in
  let B17 := set_g_now B16 1000000 in
  let B18 := set_g_fail_next B17 0 in
  let B19 := set_g_last_counter B18 0 in
  let B20 := upd B19 OFF_M (repeat (b8 0) (Z.to_nat SZ_M)) in
  let B21 := set_M_desk_known B20 (Cfg_desk_mac_set B20) in
  let B22 := set_M_desk B21 DESK in
  let B23 := set_g_ncmd (set_g_nq B22 0) 0 in
  set_g_rx B23 0.

Definition ent_v9 (cb : Z -> Z) : Z := Z.lor (cb 12) (Z.shiftl (cb 13) 8) mod 2^16.

Lemma ent_B24_eq : forall D B1 o n flags,
  fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D))) = (FuzzIn o n, flags) -> 0 <= n ->
  ent_B24 D B1 = ent_Wt flags (ent_v9 (cbyte D o n)) (ent_W14 (cbyte D o n) (ent_W6 flags B1)) /\
  ent_c10 D = cur o n 14.
Proof.
  intros D B1 o n flags H Hn. unfold ent_B24, ent_c10. cbv zeta. rewrite H. cbv beta iota.
  rewrite <- (cur0 o n Hn).
  rewrite (fu8_cur D o n 0 1) by lia.
  rewrite (fu8_cur D o n 1 2) by lia.
  rewrite (fu16_cur D o n 2 3 4) by lia.
  rewrite (fu8_cur D o n 4 5) by lia.
  rewrite (fu16_cur D o n 5 6 7) by lia.
  rewrite (fu16_cur D o n 7 8 9) by lia.
  rewrite (fu16_cur D o n 9 10 11) by lia.
  rewrite (fu8_cur D o n 11 12) by lia.
  rewrite (fu16_cur D o n 12 13 14) by lia.
  cbv beta iota. unfold ent_Wt, ent_v9, ent_W14, ent_W6. cbv beta zeta.
  split; lazymatch goal with |- ?a = ?a => reflexivity end.
Qed.

(* ---------------------------------------------------------------- world algebra (worlds of W_LEN bytes) *)

Lemma ent_some_inv : forall (X Y : Type) (a a' : X) (b b' : Y), Some (a, b) = Some (a', b') -> a = a' /\ b = b'.
Proof. intros X Y a a' b b' H. injection H as -> ->. split; reflexivity. Qed.

(* reflexivity only on syntactically equal sides (never a conversion that could unfold a world) *)
Ltac e_refl := lazymatch goal with |- ?a = ?a => reflexivity end.

Lemma e_ne_repeat : forall (x : byte) n i, (i < n)%nat -> nth_error (repeat x n) i = Some x.
Proof. induction n as [|n IH]; intros i Hi; [lia|]. destruct i as [|i]; cbn; [reflexivity | apply IH; lia]. Qed.

Lemma e_lu : forall (Bx v : list byte) k, length Bx = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> length (upd Bx k v) = Z.to_nat W_LEN.
Proof. intros Bx v k L Hk Hv. rewrite length_upd; [exact L | lia | rewrite L; unfold W_LEN in *; lia]. Qed.

Lemma e_len_sub : forall (bs : list byte) k n, length bs = Z.to_nat W_LEN -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  length (sub bs k n) = n.
Proof. intros bs k n L Hk Hn. apply length_sub; [lia | rewrite L; unfold W_LEN in *; lia]. Qed.

Lemma e_len_HOST : length HOST = 6%nat.
Proof. reflexivity. Qed.
Lemma e_len_DESK : length DESK = 6%nat.
Proof. reflexivity. Qed.

Ltac e_lens L :=
  rewrite ?length_put, ?repeat_length, ?e_len_HOST, ?e_len_DESK, ?(e_len_sub _ _ _ L) by (unfold W_LEN; lia).

Ltac e_wlen L :=
  first [ exact L
        | apply e_lu; [ e_wlen L | lia | e_lens L; unfold W_LEN; lia ] ].

Lemma e_comm : forall (bs v w : list byte) k k', length bs = Z.to_nat W_LEN -> 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat (length w) <= k \/ k + Z.of_nat (length v) <= k') ->
  k + Z.of_nat (length v) <= W_LEN -> k' + Z.of_nat (length w) <= W_LEN ->
  upd (upd bs k v) k' w = upd (upd bs k' w) k v.
Proof.
  intros bs v w k k' L Hk Hk' Hd Hv Hw. apply upd_upd_comm; try lia; rewrite L; unfold W_LEN in *; lia.
Qed.

Lemma e_uo : forall (Bx v : list byte) (k k' : Z) (nn : nat),
  length Bx = Z.to_nat W_LEN -> 0 <= k -> 0 <= k' -> k + Z.of_nat (length v) <= W_LEN ->
  (k' + Z.of_nat nn <= k \/ k + Z.of_nat (length v) <= k') ->
  u_at (upd Bx k v) k' nn = u_at Bx k' nn.
Proof. intros Bx v k k' nn L Hk Hk' Hv Hd. apply u_at_upd_out; try lia; rewrite L; unfold W_LEN in *; lia. Qed.

Ltac e_side L :=
  first [ e_wlen L
        | (e_lens L; unfold W_LEN; lia)
        | lia ].

(* diginet_session_init writes only g_s: g_fail_next is kept *)
Lemma ent_init_gfn : forall B a b c d e f B' r, length B = Z.to_nat W_LEN ->
  diginet_session_init_m B a b c d e f = Some (B', r) -> g_fail_next B' = g_fail_next B.
Proof.
  intros B a b c d e f B' r L H. unfold diginet_session_init_m in H. cbv zeta in H.
  repeat match type of H with context [if ?t then _ else _] => destruct t end;
    apply ent_some_inv in H; destruct H as [<- _]; try e_refl;
    unfold g_fail_next, set_S_desk_known, set_S_desk_mac, set_S_state, set_S_notify_ctx, set_S_notify,
      set_S_io_now_us, set_S_io_recv, set_S_io_send, set_S_io_ctx, A_S_desk_known, A_S_desk_mac, A_S_state,
      A_S_notify_ctx, A_S_notify, A_S_io_now_us, A_S_io_recv, A_S_io_send, A_S_io_ctx, A_S_cfg_host_mac,
      Cfg_desk_mac, A_Cfg_desk_mac, OFF_g_s, SZ_g_s, OFF_g_cfg, SZ_g_cfg, OFF_g_fail_next;
    repeat (rewrite e_uo by e_side L); e_refl.
Qed.

Lemma e_up : forall (Bx : list byte) k n v, length Bx = Z.to_nat W_LEN -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  u_at (upd Bx k (put n v)) k n = v mod 2 ^ (8 * Z.of_nat n).
Proof. intros Bx k n v L Hk Hn. apply u_at_upd_put; [lia | rewrite L; unfold W_LEN in *; lia]. Qed.

(* g_fail_next of the world init is called on: 0 (fuzz_transport.c:1152) *)
Lemma ent_Wt_gfn : forall flags v9 W14, length W14 = Z.to_nat W_LEN -> g_fail_next (ent_Wt flags v9 W14) = 0.
Proof.
  intros flags v9 W14 L. unfold ent_Wt. cbv zeta.
  unfold g_fail_next, set_g_rx, set_g_ncmd, set_g_nq, set_M_desk, set_M_desk_known, set_g_last_counter,
    set_g_fail_next, set_g_now, set_g_raw, set_Cfg_max_body, A_M_desk, A_M_desk_known, A_Cfg_max_body,
    OFF_g_rx, OFF_g_ncmd, OFF_g_nq, OFF_M, SZ_M, OFF_g_last_counter, OFF_g_fail_next, OFF_g_now, OFF_g_raw,
    OFF_g_cfg.
  do 7 (rewrite e_uo by e_side L).
  rewrite e_up by e_side L. reflexivity.
Qed.

(* memset(&M + 8, 0, 0x668), M.desk_known, memcpy(M.desk, ..): the model's memset of all of M, then the two *)
Lemma ent_M_eq : forall (X a d : list byte), length X = Z.to_nat W_LEN -> length a = 4%nat -> length d = 6%nat ->
  upd (upd (upd X 8 (repeat (b8 0) 1640)) 0 a) 4 d =
  upd (upd (upd X OFF_M (repeat (b8 0) (Z.to_nat SZ_M))) 0 a) 4 d.
Proof.
  intros X a d L La Ld. unfold OFF_M, SZ_M. change (Z.to_nat 1648) with 1648%nat.
  assert (LX : (1648 <= length X)%nat) by (rewrite L; unfold W_LEN; lia).
  assert (L1 : length (upd X 8 (repeat (b8 0) 1640)) = length X)
    by (apply length_upd; [lia | rewrite repeat_length; lia]).
  assert (L2 : length (upd (upd X 8 (repeat (b8 0) 1640)) 0 a) = length X)
    by (rewrite length_upd; [exact L1 | lia | rewrite La, L1; lia]).
  assert (R1 : length (upd X 0 (repeat (b8 0) 1648)) = length X)
    by (apply length_upd; [lia | rewrite repeat_length; lia]).
  assert (R2 : length (upd (upd X 0 (repeat (b8 0) 1648)) 0 a) = length X)
    by (rewrite length_upd; [exact R1 | lia | rewrite La, R1; lia]).
  apply nth_error_ext. intros i.
  rewrite (ne_upd _ d 4 i) by (try rewrite L2; try rewrite Ld; cbn; lia).
  rewrite (ne_upd _ d 4 i) by (try rewrite R2; try rewrite Ld; cbn; lia).
  rewrite (ne_upd _ a 0 i) by (try rewrite L1; try rewrite La; cbn; lia).
  rewrite (ne_upd _ a 0 i) by (try rewrite R1; try rewrite La; cbn; lia).
  rewrite (ne_upd X _ 8 i) by (rewrite ?repeat_length; cbn; lia).
  rewrite (ne_upd X _ 0 i) by (rewrite ?repeat_length; cbn; lia).
  rewrite Ld, La, !repeat_length.
  change (Z.to_nat 4) with 4%nat. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 8) with 8%nat.
  cbn [Nat.add].
  destruct (Nat.leb_spec 4 i); destruct (Nat.ltb_spec i 10); cbn [andb]; try e_refl;
  destruct (Nat.leb_spec 0 i); destruct (Nat.ltb_spec i 4); cbn [andb]; try e_refl; try lia;
  destruct (Nat.leb_spec 8 i); destruct (Nat.ltb_spec i 1648); cbn [andb]; try lia;
  rewrite ?e_ne_repeat by lia; try e_refl; lia.
Qed.

(* ---------------------------------------------------------------- the machine's arithmetic on bytes *)

(* a check of p at z, z + 1, .., z + fuel - 1 (evaluated by vm_compute) *)
Fixpoint e_chk (p : Z -> bool) (fuel : nat) (z : Z) : bool :=
  match fuel with O => true | S f => if p z then e_chk p f (z + 1) else false end.

Lemma e_chk_ok : forall p fuel z, e_chk p fuel z = true -> forall w, z <= w < z + Z.of_nat fuel -> p w = true.
Proof.
  induction fuel as [|f IH]; intros z H w Hw; cbn in H; [lia|].
  destruct (p z) eqn:E; [|discriminate].
  destruct (Z.eq_dec w z) as [->|NE]; [exact E|].
  apply (IH (z + 1) H). lia.
Qed.

Lemma e_brange : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma e_put4_eq : forall x y, x mod 2 ^ 32 = y mod 2 ^ 32 -> put 4 x = put 4 y.
Proof.
  intros x y H. unfold put.
  rewrite <- (Z_to_le_bytes_mod 4 x 32) by lia. rewrite <- (Z_to_le_bytes_mod 4 y 32) by lia.
  rewrite H. reflexivity.
Qed.

(* a two-byte check through the index a + 256 b *)
Lemma e_two : forall (p : Z -> Z -> bool),
  e_chk (fun w => p (w mod 256) (w / 256)) (Z.to_nat 65536) 0 = true ->
  forall a b, 0 <= a < 256 -> 0 <= b < 256 -> p a b = true.
Proof.
  intros p H a b Ha Hb.
  pose proof (e_chk_ok _ _ _ H (a + 256 * b) ltac:(rewrite Z2Nat.id by lia; lia)) as E. cbv beta in E.
  replace ((a + 256 * b) mod 256) with a in E by (rewrite Z.mul_comm, Z.mod_add by lia; rewrite Z.mod_small; lia).
  replace ((a + 256 * b) / 256) with b in E by (rewrite Z.mul_comm, Z.div_add by lia; rewrite Z.div_small; lia).
  exact E.
Qed.

Lemma e_lor1 : forall a b, 0 <= a < 256 -> 0 <= b < 256 ->
  Z.lor a (Z.shiftl b 8 mod 18446744073709551616) = a + 256 * b.
Proof.
  intros a b Ha Hb. apply Z.eqb_eq.
  exact (e_two (fun a b => Z.lor a (Z.shiftl b 8 mod 18446744073709551616) =? a + 256 * b)
           ltac:(vm_compute; reflexivity) a b Ha Hb).
Qed.

Lemma e_lor2 : forall a b, 0 <= a < 256 -> 0 <= b < 256 ->
  Z.lor (Z.shiftl b 8 mod 18446744073709551616) a = a + 256 * b.
Proof.
  intros a b Ha Hb. apply Z.eqb_eq.
  exact (e_two (fun a b => Z.lor (Z.shiftl b 8 mod 18446744073709551616) a =? a + 256 * b)
           ltac:(vm_compute; reflexivity) a b Ha Hb).
Qed.

Lemma e_lor16 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.lor a (Z.shiftl b 8) mod 2 ^ 16 = a + 256 * b.
Proof.
  intros a b Ha Hb. apply Z.eqb_eq.
  exact (e_two (fun a b => Z.lor a (Z.shiftl b 8) mod 2 ^ 16 =? a + 256 * b)
           ltac:(vm_compute; reflexivity) a b Ha Hb).
Qed.

Lemma e_land7 : forall b, 0 <= b -> Z.land b 7 = b mod 8.
Proof. intros b Hb. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* max_cmds: b & 255, masked by (b == 255) - 1 *)
Lemma e_mc : forall b, 0 <= b < 256 ->
  Z.land (Z.land b 255) ((Z.b2z ((Z.land b 255 + -255) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616)
  = b mod 255.
Proof.
  intros b Hb. apply Z.eqb_eq.
  apply (e_chk_ok (fun b => Z.land (Z.land b 255)
                     ((Z.b2z ((Z.land b 255 + -255) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616)
                     =? b mod 255) (Z.to_nat 256) 0); [vm_compute; reflexivity | rewrite Z2Nat.id by lia; lia].
Qed.

(* max_body: v - (v * 22967 >> 25) * 1461 is v % 1461 for v < 65536; + 24, as a uint16 *)
Lemma e_mb : forall v, 0 <= v < 65536 ->
  ((bv_swrap 32 (v - Z.shiftr ((v * 22967) mod 18446744073709551616) 25 * 1461 mod 18446744073709551616) + 24)
     mod 18446744073709551616) mod 65536 = 24 + v mod 1461.
Proof.
  intros v Hv. apply Z.eqb_eq.
  apply (e_chk_ok (fun v => ((bv_swrap 32 (v - Z.shiftr ((v * 22967) mod 18446744073709551616) 25 * 1461
                                            mod 18446744073709551616) + 24)
                              mod 18446744073709551616) mod 65536 =? 24 + v mod 1461) (Z.to_nat 65536) 0);
    [vm_compute; reflexivity | rewrite Z2Nat.id by lia; lia].
Qed.

(* g_raw: bit 3 of the flags byte, (flags << 60) >> 63 *)
Lemma e_raw : forall f, 0 <= f < 256 -> Z.shiftr (Z.shiftl f 60 mod 18446744073709551616) 63 = Z.land (Z.shiftr f 3) 1.
Proof.
  intros f Hf. apply Z.eqb_eq.
  apply (e_chk_ok (fun f => Z.shiftr (Z.shiftl f 60 mod 18446744073709551616) 63 =? Z.land (Z.shiftr f 3) 1)
           (Z.to_nat 256) 0); [vm_compute; reflexivity | rewrite Z2Nat.id by lia; lia].
Qed.

(* the eight config stores of the machine (max_retries .. max_cmds, in the model's order), each value equal to the
   model's modulo 2^32, are the model's B7 .. B14 *)
Lemma ent_W14_eq : forall (W6 : list byte) (cb : Z -> Z) x1 x2 x3 x4 x5 x6 x7 x8,
  x1 mod 2 ^ 32 = (cb 0 mod 8) mod 2 ^ 32 ->
  x2 mod 2 ^ 32 = ((1 + cb 1) mod 2^32) mod 2 ^ 32 ->
  x3 mod 2 ^ 32 = ((1 + Z.lor (cb 2) (Z.shiftl (cb 3) 8) mod 2^16) mod 2^32) mod 2 ^ 32 ->
  x4 mod 2 ^ 32 = cb 4 mod 2 ^ 32 ->
  x5 mod 2 ^ 32 = ((1 + Z.lor (cb 5) (Z.shiftl (cb 6) 8) mod 2^16) mod 2^32) mod 2 ^ 32 ->
  x6 mod 2 ^ 32 = ((1 + Z.lor (cb 7) (Z.shiftl (cb 8) 8) mod 2^16) mod 2^32) mod 2 ^ 32 ->
  x7 mod 2 ^ 32 = (Z.lor (cb 9) (Z.shiftl (cb 10) 8) mod 2^16) mod 2 ^ 32 ->
  x8 mod 2 ^ 32 = ((1 + cb 11 mod 255) mod 2^32) mod 2 ^ 32 ->
  upd (upd (upd (upd (upd (upd (upd (upd W6 65056 (put 4 x1)) 65052 (put 4 x2)) 65048 (put 4 x3))
    65060 (put 4 x4)) 65064 (put 4 x5)) 65068 (put 4 x6)) 65072 (put 4 x7)) 65076 (put 4 x8)
  = ent_W14 cb W6.
Proof.
  intros W6 cb x1 x2 x3 x4 x5 x6 x7 x8 E1 E2 E3 E4 E5 E6 E7 E8.
  rewrite (e_put4_eq _ _ E1), (e_put4_eq _ _ E2), (e_put4_eq _ _ E3), (e_put4_eq _ _ E4),
    (e_put4_eq _ _ E5), (e_put4_eq _ _ E6), (e_put4_eq _ _ E7), (e_put4_eq _ _ E8).
  unfold ent_W14, set_Cfg_max_retries, set_Cfg_ack_timeout_ms, set_Cfg_keepalive_ms, set_Cfg_backoff_ms,
    set_Cfg_offline_ms, set_Cfg_wake_timeout_ms, set_Cfg_display_gap_us, set_Cfg_max_cmds,
    A_Cfg_max_retries, A_Cfg_ack_timeout_ms, A_Cfg_keepalive_ms, A_Cfg_backoff_ms, A_Cfg_offline_ms,
    A_Cfg_wake_timeout_ms, A_Cfg_display_gap_us, A_Cfg_max_cmds, OFF_g_cfg.
  cbv beta zeta.
  change (65024 + 32) with 65056. change (65024 + 28) with 65052. change (65024 + 24) with 65048.
  change (65024 + 36) with 65060. change (65024 + 40) with 65064. change (65024 + 44) with 65068.
  change (65024 + 48) with 65072. change (65024 + 52) with 65076.
  e_refl.
Qed.

(* the flag bits 1 and 2 as the machine extracts them: (flags << 62) >> 63, (flags << 61) >> 63 *)
Lemma e_bit1 : forall f, 0 <= f < 256 -> Z.shiftr (Z.shiftl f 62 mod 18446744073709551616) 63 =
  (if Z.land f 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO).
Proof.
  intros f Hf. apply Z.eqb_eq.
  apply (e_chk_ok (fun f => Z.shiftr (Z.shiftl f 62 mod 18446744073709551616) 63 =?
                            (if Z.land f 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO))
           (Z.to_nat 256) 0); [vm_compute; reflexivity | rewrite Z2Nat.id by lia; lia].
Qed.

Lemma e_bit2 : forall f, 0 <= f < 256 -> Z.shiftr (Z.shiftl f 61 mod 18446744073709551616) 63 = Z.land (Z.shiftr f 2) 1.
Proof.
  intros f Hf. apply Z.eqb_eq.
  apply (e_chk_ok (fun f => Z.shiftr (Z.shiftl f 61 mod 18446744073709551616) 63 =? Z.land (Z.shiftr f 2) 1)
           (Z.to_nat 256) 0); [vm_compute; reflexivity | rewrite Z2Nat.id by lia; lia].
Qed.

Lemma e_bit2_range : forall f, 0 <= Z.land (Z.shiftr f 2) 1 < 2.
Proof. intros f. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

(* the machine's g_cfg stores (host_mac, desk_mac_set, auto_wake, sum_mode, desk_mac) are the model's B2 .. B6 *)
Lemma ent_W6_eq : forall B1 flags, length B1 = Z.to_nat W_LEN ->
  upd (upd (upd (upd (upd B1 65024 HOST) 65036 (put 4 (Z.land (Z.shiftr flags 2) 1))) 65040 (put 4 (Z.land flags 1)))
    65044 (put 4 (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO))) 65030 DESK
  = ent_W6 flags B1.
Proof.
  intros B1 flags L.
  rewrite (e_comm (upd B1 65024 HOST) (put 4 (Z.land (Z.shiftr flags 2) 1)) (put 4 (Z.land flags 1)) 65036 65040)
    by e_side L.
  rewrite (e_comm (upd (upd B1 65024 HOST) 65040 (put 4 (Z.land flags 1))) (put 4 (Z.land (Z.shiftr flags 2) 1))
             (put 4 (if Z.land flags 2 =? 0 then DIGINET_SUM_BODY else DIGINET_SUM_ZERO)) 65036 65044) by e_side L.
  unfold ent_W6, set_Cfg_host_mac, set_Cfg_auto_wake, set_Cfg_sum_mode, set_Cfg_desk_mac_set, set_Cfg_desk_mac,
    A_Cfg_host_mac, A_Cfg_auto_wake, A_Cfg_sum_mode, A_Cfg_desk_mac_set, A_Cfg_desk_mac, OFF_g_cfg.
  cbv beta zeta.
  change (65024 + 0) with 65024. change (65024 + 16) with 65040. change (65024 + 20) with 65044.
  change (65024 + 12) with 65036. change (65024 + 6) with 65030.
  e_refl.
Qed.

(* desk_mac_set of B14 is the flags bit 2 *)
Lemma ent_W14_dms : forall cb flags B1, length B1 = Z.to_nat W_LEN ->
  s32_at (ent_W14 cb (ent_W6 flags B1)) 65036 = Z.land (Z.shiftr flags 2) 1.
Proof.
  intros cb flags B1 L.
  unfold ent_W14, ent_W6, s32_at, set_Cfg_max_retries, set_Cfg_ack_timeout_ms, set_Cfg_keepalive_ms,
    set_Cfg_backoff_ms, set_Cfg_offline_ms, set_Cfg_wake_timeout_ms, set_Cfg_display_gap_us, set_Cfg_max_cmds,
    set_Cfg_host_mac, set_Cfg_auto_wake, set_Cfg_sum_mode, set_Cfg_desk_mac_set, set_Cfg_desk_mac,
    A_Cfg_max_retries, A_Cfg_ack_timeout_ms, A_Cfg_keepalive_ms, A_Cfg_backoff_ms, A_Cfg_offline_ms,
    A_Cfg_wake_timeout_ms, A_Cfg_display_gap_us, A_Cfg_max_cmds, A_Cfg_host_mac, A_Cfg_auto_wake, A_Cfg_sum_mode,
    A_Cfg_desk_mac_set, A_Cfg_desk_mac, OFF_g_cfg.
  cbv beta zeta.
  do 9 (rewrite e_uo by e_side L).
  change (65024 + 12) with 65036. rewrite e_up by e_side L.
  pose proof (e_bit2_range flags) as R.
  rewrite Z.mod_small by (change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia).
  apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

(* the machine's stores from max_body to g_rx (fuzz_transport.c:1148-1158) are the model's B15 .. B24 *)
Lemma ent_Wt_eq : forall W14 flags v9 MB RAW, length W14 = Z.to_nat W_LEN ->
  s32_at W14 65036 = Z.land (Z.shiftr flags 2) 1 ->
  MB mod 2 ^ 32 = ((SPEC_CMD_MAX + v9 mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2^32) mod 2 ^ 32 ->
  RAW = Z.land (Z.shiftr flags 3) 1 ->
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd W14 65080 (put 4 MB)) OFF_g_fail_next (put 1 0))
    64972 (put 4 RAW)) 64976 (put 4 0)) 65000 (put 8 1000000)) 8 (repeat (b8 0) 1640))
    0 (put 4 (Z.land (Z.shiftr flags 2) 1))) 4 DESK) 64980 (put 4 0)) 64984 (put 4 0)) 65008 (put 8 0)
  = ent_Wt flags v9 W14.
Proof.
  intros W14 flags v9 MB RAW L HD HMB ->.
  rewrite (e_put4_eq MB _ HMB).
  set (mb := (SPEC_CMD_MAX + v9 mod (SPEC_MAX_BODY - SPEC_CMD_MAX + 1)) mod 2^32).
  set (X := upd W14 65080 (put 4 mb)).
  assert (LX : length X = Z.to_nat W_LEN) by (unfold X; e_side L).
  unfold OFF_g_fail_next.
  (* g_fail_next after g_raw and g_now, as the model has them *)
  rewrite (e_comm X (put 1 0) (put 4 (Z.land (Z.shiftr flags 3) 1)) 64968 64972) by e_side LX.
  rewrite (e_comm (upd (upd X 64972 (put 4 (Z.land (Z.shiftr flags 3) 1))) 64968 (put 1 0)) (put 4 0)
             (put 8 1000000) 64976 65000) by e_side LX.
  rewrite (e_comm (upd X 64972 (put 4 (Z.land (Z.shiftr flags 3) 1))) (put 1 0) (put 8 1000000) 64968 65000)
    by e_side LX.
  set (Y := upd (upd (upd (upd X 64972 (put 4 (Z.land (Z.shiftr flags 3) 1))) 65000 (put 8 1000000))
                  64968 (put 1 0)) 64976 (put 4 0)).
  assert (LY : length Y = Z.to_nat W_LEN) by (unfold Y; e_side LX).
  rewrite (ent_M_eq Y (put 4 (Z.land (Z.shiftr flags 2) 1)) DESK LY (length_put 4 _) e_len_DESK).
  (* the model's M.desk_known reads desk_mac_set back *)
  assert (HDY : s32_at (upd Y OFF_M (repeat (b8 0) (Z.to_nat SZ_M))) (OFF_g_cfg + 12) = Z.land (Z.shiftr flags 2) 1).
  { rewrite <- HD. unfold Y, X, s32_at, OFF_M, SZ_M, OFF_g_cfg. f_equal. change (65024 + 12) with 65036.
    do 6 (rewrite e_uo by e_side L). reflexivity. }
  unfold ent_Wt, set_Cfg_max_body, set_g_raw, set_g_now, set_g_fail_next, set_g_last_counter, set_M_desk_known,
    set_M_desk, set_g_nq, set_g_ncmd, set_g_rx, Cfg_desk_mac_set, A_Cfg_max_body, A_Cfg_desk_mac_set,
    A_M_desk_known, A_M_desk.
  cbv beta zeta. fold mb.
  unfold OFF_g_raw, OFF_g_now, OFF_g_fail_next, OFF_g_last_counter, OFF_g_nq, OFF_g_ncmd, OFF_g_rx.
  change (OFF_g_cfg + 56) with 65080. fold X.
  fold Y.
  first [ rewrite HDY | match goal with |- ?G => idtac "WTEQ" G; fail end ].
  unfold Y, OFF_M.
  change (0x0 + 0) with 0. change (0x0 + 4) with 4.
  e_refl.
Qed.

(* ---------------------------------------------------------------- the worlds keep W_LEN bytes *)

Lemma ent_cd_len : forall B B1, length B = Z.to_nat W_LEN -> diginet_session_config_default_m B = Some (B1, tt) ->
  length B1 = Z.to_nat W_LEN.
Proof.
  intros B B1 L H. unfold diginet_session_config_default_m in H. cbv zeta in H.
  apply ent_some_inv in H. destruct H as [<- _].
  unfold set_Cfg_auto_wake, set_Cfg_sum_mode, set_Cfg_keepalive_ms, set_Cfg_ack_timeout_ms, set_Cfg_max_retries,
    set_Cfg_backoff_ms, set_Cfg_offline_ms, set_Cfg_wake_timeout_ms, set_Cfg_display_gap_us, set_Cfg_max_cmds,
    set_Cfg_max_body, A_Cfg_auto_wake, A_Cfg_sum_mode, A_Cfg_keepalive_ms, A_Cfg_ack_timeout_ms, A_Cfg_max_retries,
    A_Cfg_backoff_ms, A_Cfg_offline_ms, A_Cfg_wake_timeout_ms, A_Cfg_display_gap_us, A_Cfg_max_cmds, A_Cfg_max_body,
    OFF_g_cfg, SZ_g_cfg.
  e_wlen L.
Qed.

Lemma ent_W6_len : forall flags B1, length B1 = Z.to_nat W_LEN -> length (ent_W6 flags B1) = Z.to_nat W_LEN.
Proof.
  intros flags B1 L. unfold ent_W6, set_Cfg_host_mac, set_Cfg_auto_wake, set_Cfg_sum_mode, set_Cfg_desk_mac_set,
    set_Cfg_desk_mac, A_Cfg_host_mac, A_Cfg_auto_wake, A_Cfg_sum_mode, A_Cfg_desk_mac_set, A_Cfg_desk_mac, OFF_g_cfg.
  cbv beta zeta. e_wlen L.
Qed.

Lemma ent_W14_len : forall cb W6, length W6 = Z.to_nat W_LEN -> length (ent_W14 cb W6) = Z.to_nat W_LEN.
Proof.
  intros cb W6 L. unfold ent_W14, set_Cfg_max_retries, set_Cfg_ack_timeout_ms, set_Cfg_keepalive_ms,
    set_Cfg_backoff_ms, set_Cfg_offline_ms, set_Cfg_wake_timeout_ms, set_Cfg_display_gap_us, set_Cfg_max_cmds,
    A_Cfg_max_retries, A_Cfg_ack_timeout_ms, A_Cfg_keepalive_ms, A_Cfg_backoff_ms, A_Cfg_offline_ms,
    A_Cfg_wake_timeout_ms, A_Cfg_display_gap_us, A_Cfg_max_cmds, OFF_g_cfg.
  cbv beta zeta. e_wlen L.
Qed.

Lemma ent_Wt_len : forall flags v9 W14, length W14 = Z.to_nat W_LEN -> length (ent_Wt flags v9 W14) = Z.to_nat W_LEN.
Proof.
  intros flags v9 W14 L. unfold ent_Wt, set_Cfg_max_body, set_g_raw, set_g_now, set_g_fail_next, set_g_last_counter,
    set_M_desk_known, set_M_desk, set_g_nq, set_g_ncmd, set_g_rx, A_Cfg_max_body, A_M_desk_known, A_M_desk,
    OFF_g_cfg, OFF_g_raw, OFF_g_now, OFF_g_fail_next, OFF_g_last_counter, OFF_M, SZ_M, OFF_g_nq, OFF_g_ncmd, OFF_g_rx.
  cbv beta zeta. e_wlen L.
Qed.
