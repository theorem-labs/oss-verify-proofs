(* The walk of diginet_session_rx (transport/src/diginet_session.c:263-318) in the plain image, 0x1662c, 118
   instructions. diginet_frame_parse fills the local struct diginet_frame at sp + 8; four bcmp compare f.src with
   g_s.cfg.host_mac, f.dst with host_mac and BROADCAST (.rodata 0x104ce) and f.src with g_s.desk_mac; a Digidesign
   announce from an unknown desk is learnt (diginet_mac_is_digidesign, then desk_known and the six desk_mac bytes
   as three halfword stores); an accepted frame counts stats.rx_frames, records last_rx_us, goes to on_announce /
   on_ack / on_data / session_lost (or stats.rx_ignored) and ends in diginet_session_tick. The paths that meet share
   one continuation each: EPI (0x166ec, the epilogue), IGN (0x166e0, stats.rx_ignored++), TICK (0x167f4), ACC
   (0x16744, the accepted frame) and D0 (0x166c0, the desk_known test). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import StrFun DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import bcmp_c diginet_frame_parse_c
  diginet_mac_is_digidesign_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC
  on_announce_c on_ack_c on_data_c session_lost_c diginet_session_tick_c diginet_session_rx_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the model, in the order the binary tests it ---- *)

Definition rx_ign (B : list byte) : list byte := set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)).

(* :298-316, the switch on the command *)
Definition rx_sw_m (I : timg) (F : option tframe) (buf : list byte) (now : Z) (B : list byte)
    : option (list byte * unit) :=
  let cmd := fr_cmd buf in
  if (cmd =? DIGINET_CMD_ANNOUNCE) || (cmd =? DIGINET_CMD_ANNOUNCE_SESSION) then on_announce_m I F B buf now
  else if cmd =? DIGINET_CMD_ACK then on_ack_m I F B buf
  else if cmd =? DIGINET_CMD_DATA then on_data_m I F B buf now
  else if cmd =? DIGINET_CMD_DISCONNECT then
    (if (S_state B =? DIGINET_S_ONLINE) || (S_state B =? DIGINET_S_WAKING)
     then session_lost_m I F B DIGINET_R_DESK_DISCONNECT else Some (B, tt))
  else Some (set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)), tt).

(* :293-317, once the source is the desk's *)
Definition rx_accept_m (I : timg) (F : option tframe) (buf : list byte) (now : Z) (B : list byte)
    : option (list byte * Z) :=
  if S_state B =? DIGINET_S_CLOSED then Some (B, DIGINET_OK)
  else
  let B := set_S_stats_rx_frames B (u64 (S_stats_rx_frames B + 1)) in
  let B := set_S_last_rx_us B now in
  match rx_sw_m I F buf now B with
  | None => None
  | Some (B, _) => diginet_session_tick_m I F B now
  end.

(* :278-291, from the desk_known test on *)
Definition rx_rest_m (I : timg) (F : option tframe) (buf : list byte) (now : Z) (B : list byte)
    : option (list byte * Z) :=
  if negb (S_desk_known B =? 0) then
    if negb (memeq 6 (fr_src buf) (S_desk_mac B)) then Some (rx_ign B, DIGINET_OK) else rx_accept_m I F buf now B
  else if negb ((fr_cmd buf =? DIGINET_CMD_ANNOUNCE) || (fr_cmd buf =? DIGINET_CMD_ANNOUNCE_SESSION))
  then Some (B, DIGINET_OK)
  else if negb (oui_of (fr_src buf)) then Some (rx_ign B, DIGINET_OK)
  else rx_accept_m I F buf now (set_S_desk_known (set_S_desk_mac B (fr_src buf)) 1).

Lemma rx_m_eq : forall I F B buf now, diginet_session_rx_m I F B buf now =
  if negb (fr_code buf =? DIGINET_OK) then Some (rx_ign B, fr_code buf)
  else if memeq 6 (fr_src buf) (S_cfg_host_mac B) ||
          (negb (memeq 6 (fr_dst buf) (S_cfg_host_mac B)) && negb (memeq 6 (fr_dst buf) BROADCAST))
  then Some (rx_ign B, DIGINET_OK)
  else rx_rest_m I F buf now B.
Proof. reflexivity. Qed.

Lemma rx_sw_ann : forall I F buf now B, fr_cmd buf = 224 \/ fr_cmd buf = 225 ->
  rx_sw_m I F buf now B = on_announce_m I F B buf now.
Proof. intros I F buf now B [H|H]; unfold rx_sw_m; rewrite H; reflexivity. Qed.

Lemma rx_sw_ack : forall I F buf now B, fr_cmd buf = 160 -> rx_sw_m I F buf now B = on_ack_m I F B buf.
Proof. intros I F buf now B H. unfold rx_sw_m. rewrite H. reflexivity. Qed.

Lemma rx_sw_data : forall I F buf now B, fr_cmd buf = 0 -> rx_sw_m I F buf now B = on_data_m I F B buf now.
Proof. intros I F buf now B H. unfold rx_sw_m. rewrite H. reflexivity. Qed.

Lemma rx_sw_disc : forall I F buf now B, fr_cmd buf = 227 ->
  rx_sw_m I F buf now B =
  if (S_state B =? 2) || (S_state B =? 1) then session_lost_m I F B 7 else Some (B, tt).
Proof. intros I F buf now B H. unfold rx_sw_m. rewrite H. reflexivity. Qed.

Lemma rx_sw_other : forall I F buf now B, fr_cmd buf <> 224 -> fr_cmd buf <> 225 -> fr_cmd buf <> 160 ->
  fr_cmd buf <> 0 -> fr_cmd buf <> 227 -> rx_sw_m I F buf now B = Some (rx_ign B, tt).
Proof.
  intros I F buf now B H1 H2 H3 H4 H5. unfold rx_sw_m, rx_ign. cbv zeta.
  unfold DIGINET_CMD_ANNOUNCE, DIGINET_CMD_ANNOUNCE_SESSION, DIGINET_CMD_ACK, DIGINET_CMD_DATA,
    DIGINET_CMD_DISCONNECT.
  rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2), (proj2 (Z.eqb_neq _ _) H3),
    (proj2 (Z.eqb_neq _ _) H4), (proj2 (Z.eqb_neq _ _) H5).
  reflexivity.
Qed.

(* ---- words and branch conditions ---- *)

Lemma rx_mod_neg : forall z, -2^64 <= z < 0 -> z mod 2^64 = z + 2^64.
Proof. intros z Hz. rewrite <- (Z_mod_plus_full z 1 (2^64)). rewrite Z.mod_small by lia. lia. Qed.

Lemma rx_unsigned_neg : forall z, -2^63 <= z < 0 -> bv_unsigned (Z_to_bv 64 z) = z + 2^64.
Proof. intros z Hz. rewrite unsigned_lit_wrap. apply rx_mod_neg. lia. Qed.

Lemma rx_eqb : forall v k, -2^63 <= v < 2^63 -> 0 <= k < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 k) = (v =? k).
Proof.
  intros v k Hv Hk. unfold bv_eqb. rewrite (unsigned_lit k) by lia.
  destruct (Z.leb_spec 0 v) as [P|N].
  - rewrite unsigned_lit by lia. reflexivity.
  - rewrite rx_unsigned_neg by lia.
    destruct (Z.eqb_spec v k) as [E|E]; [exfalso; lia|]. apply Z.eqb_neq. lia.
Qed.

Lemma rx_signed_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite unsigned_lit by lia. apply bv_swrap_small.
  change (bv_half_modulus 64) with (2^63). lia.
Qed.

Lemma rx_lts : forall a c, 0 <= a < 2^63 -> 0 <= c < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 c) = (a <? c).
Proof. intros a c Ha Hc. unfold bv_lts. rewrite !rx_signed_small by lia. reflexivity. Qed.

Lemma rx_ltu : forall a c, 0 <= a < 2^64 -> 0 <= c < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 c) = (a <? c).
Proof. intros a c Ha Hc. unfold bv_ltu. rewrite (unsigned_lit a), (unsigned_lit c) by lia. reflexivity. Qed.

(* 0x1670c-0x16714: cmd - 226 <u -2 unless cmd is 224 or 225 *)
Lemma rx_ann_cond : forall c, 0 <= c < 256 ->
  bv_ltu (Z_to_bv 64 (c + -226)) (Z_to_bv 64 (-2)) = negb ((c =? 224) || (c =? 225)).
Proof.
  intros c Hc. unfold bv_ltu. rewrite (rx_unsigned_neg (-2)) by lia.
  destruct (Z.leb_spec 226 c) as [P|N].
  - rewrite unsigned_lit by lia.
    destruct (Z.eqb_spec c 224); [exfalso; lia|]. destruct (Z.eqb_spec c 225); [exfalso; lia|].
    cbn [orb negb]. apply Z.ltb_lt. lia.
  - rewrite rx_unsigned_neg by lia.
    destruct (Z.eqb_spec c 224) as [E|E]; [subst c; reflexivity|].
    destruct (Z.eqb_spec c 225) as [E'|E']; [subst c; reflexivity|].
    cbn [orb negb]. apply Z.ltb_lt. lia.
Qed.

Lemma rx_swrap_per : forall z, bv_swrap 32 (z + 2^64) = bv_swrap 32 z.
Proof.
  intros z. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  replace (z + 2^64 + 2^31) with ((z + 2^31) + 2^32 * 2^32) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

(* 0x167b8-0x167c0: state - 1 (addiw) >u 1 unless the state is ONLINE (2) or WAKING (1) *)
Lemma rx_state_cond : forall st, -2^31 <= st < 2^31 ->
  bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 st) + -1))) =
  negb ((st =? 2) || (st =? 1)).
Proof.
  intros st Hst. unfold bv_ltu. rewrite (unsigned_lit 1) by lia.
  assert (E : bv_swrap 32 (bv_unsigned (Z_to_bv 64 st) + -1) = bv_swrap 32 (st - 1)).
  { destruct (Z.leb_spec 0 st) as [P|N].
    - rewrite unsigned_lit by lia. f_equal; lia.
    - rewrite rx_unsigned_neg by lia. replace (st + 2^64 + -1) with ((st - 1) + 2^64) by lia. apply rx_swrap_per. }
  rewrite E.
  destruct (Z.leb_spec (-2^31 + 1) st) as [P|N].
  - rewrite (bv_swrap_small 32 (st - 1)) by (change (bv_half_modulus 32) with (2^31); lia).
    destruct (Z.leb_spec 1 st) as [P1|N1].
    + rewrite unsigned_lit by lia.
      destruct (Z.eqb_spec st 2) as [E2|E2]; destruct (Z.eqb_spec st 1) as [E1|E1]; cbn [orb negb].
      * exfalso; lia.
      * apply Z.ltb_ge. lia.
      * apply Z.ltb_ge. lia.
      * apply Z.ltb_lt. lia.
    + rewrite rx_unsigned_neg by lia.
      destruct (Z.eqb_spec st 2); [exfalso; lia|]. destruct (Z.eqb_spec st 1); [exfalso; lia|].
      cbn [orb negb]. apply Z.ltb_lt. lia.
  - assert (Em : st = -2^31) by lia. subst st. vm_compute. reflexivity.
Qed.

Lemma rx_zxb : forall c, 0 <= c < 256 -> zxb (b8 c) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold zxb, b8. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma rx_at8_range : forall l i, 0 <= at8 l i < 256.
Proof.
  intros l i. unfold at8, bz. pose proof (bv_unsigned_in_range 8 (nth i l (b8 0))) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

(* ---- bcmp and the model's memeq ---- *)

Lemma rx_memcmp : forall n l r v, (n <= length l)%nat -> (n <= length r)%nat -> memcmp_model l r n = Some v ->
  (v = 0 <-> firstn n l = firstn n r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr Hm.
  - cbn in Hm. injection Hm as <-. cbn [firstn]. split; [split; intros; reflexivity | lia].
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn in Hl, Hr, Hm. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    unfold bv_modulus in Ra, Rb. change (2 ^ Z.of_N 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) Hm) as [[I1 I2] I3]. split; [|exact I3].
      assert (a = b) by (apply bv_eq; exact E). subst b. cbn [firstn]. split.
      * intros Hv. f_equal. tauto.
      * intros Q. injection Q as Q. tauto.
    + injection Hm as <-. split; [|lia]. cbn [firstn]. split.
      * intros. lia.
      * intros Q. injection Q as Q1 Q2. subst. lia.
Qed.

Lemma rx_memeq : forall l r : list byte, length l = 6%nat -> length r = 6%nat -> (memeq 6 l r = true <-> l = r).
Proof.
  intros l r Hl Hr.
  destruct l as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; cbn in Hl; try lia.
  destruct r as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|? ?]]]]]]]; cbn in Hr; try lia.
  unfold memeq, at8, bz. cbn [seq forallb nth].
  rewrite !andb_true_iff, !Z.eqb_eq. split.
  - intros (E0 & E1 & E2 & E3 & E4 & E5 & _).
    apply bv_eq in E0. apply bv_eq in E1. apply bv_eq in E2. apply bv_eq in E3. apply bv_eq in E4.
    apply bv_eq in E5. subst. reflexivity.
  - intros E. inversion E. subst. repeat split.
Qed.

Lemma rx_bcmp_eq : forall ls rs v, length ls = 6%nat -> length rs = 6%nat -> memcmp_model ls rs 6 = Some v ->
  (v =? 0) = memeq 6 ls rs /\ -256 < v < 256.
Proof.
  intros ls rs v Hl Hr Hm. destruct (rx_memcmp 6 ls rs v ltac:(lia) ltac:(lia) Hm) as [Hv R]. split; [|exact R].
  rewrite firstn_all2 in Hv by lia. rewrite firstn_all2 in Hv by lia.
  pose proof (rx_memeq ls rs Hl Hr) as Q.
  destruct (Z.eqb_spec v 0) as [E|E]; destruct (memeq 6 ls rs) eqn:M; try reflexivity.
  - apply Hv in E. apply Q in E. discriminate E.
  - exfalso. apply E. apply Hv. apply Q. reflexivity.
Qed.

(* ---- bytes and the world ---- *)

Lemma rx_le_roundtrip : forall l, Z_to_le_bytes (length l) (bytes_le_to_Z l) = l.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbn [length Z_to_le_bytes].
  pose proof (bv_unsigned_in_range 8 x) as Rx. unfold bv_modulus in Rx. change (2 ^ Z.of_N 8) with 256 in Rx.
  pose proof (bytes_le_to_Z_nonneg l) as Pl.
  assert (E : bytes_le_to_Z (x :: l) = bv_unsigned x + 256 * bytes_le_to_Z l).
  { rewrite !bytes_le_to_Z_le_val. reflexivity. }
  rewrite E. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. exact IH.
Qed.

Lemma rx_swrap16_mod : forall u, bv_swrap 16 u mod 2 ^ 16 = u mod 2 ^ 16.
Proof.
  intros u. unfold bv_swrap, bv_wrap. change (bv_half_modulus 16) with (2 ^ 15). change (bv_modulus 16) with (2 ^ 16).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma rx_le2_sx : forall w : word, le2 (sx16 w) = le2 w.
Proof.
  intros w. unfold le2, sx16. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z_to_le_bytes_mod 2 (bv_swrap 16 (bv_unsigned w)) 64) by lia.
  rewrite <- (Z_to_le_bytes_mod 2 (bv_swrap 16 (bv_unsigned w)) 16) by lia.
  rewrite rx_swrap16_mod. apply Z_to_le_bytes_mod. lia.
Qed.

Lemma rx_le2_ble : forall l, length l = 2%nat -> le2 (le_bytes_to_word l) = l.
Proof.
  intros l Hl. unfold le2, le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- Hl at 1. apply rx_le_roundtrip.
Qed.

(* the two bytes an lh loads and an sh stores back *)
Lemma rx_le2_lh : forall l, length l = 2%nat -> le2 (sext 64 (bv_extract 0 16 (le_bytes_to_word l))) = l.
Proof.
  intros l Hl.
  transitivity (le2 (sext 64 (bv_extract 0 16 (le_bytes_to_word (le2 (le_bytes_to_word l)))))).
  { rewrite (rx_le2_ble l Hl). reflexivity. }
  rewrite sext_extract_le2, rx_le2_sx. apply rx_le2_ble. exact Hl.
Qed.

Lemma rx_src3 : forall src : list byte, length src = 6%nat -> sub src 0 2 ++ sub src 2 2 ++ sub src 4 2 = src.
Proof.
  intros src H. destruct src as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 r]]]]]]; cbn in H; try lia.
  destruct r; [reflexivity | cbn in H; lia].
Qed.

Lemma rx_upd_app : forall (B x y : list byte) k k', 0 <= k -> k' = k + Z.of_nat (length x) ->
  (Z.to_nat k + length x + length y <= length B)%nat -> upd (upd B k x) k' y = upd B k (x ++ y).
Proof.
  intros B x y k k' Hk -> Hl. rewrite !upd_upd_bytes. unfold upd_bytes.
  set (n := Z.to_nat k) in *.
  replace (Z.to_nat (k + Z.of_nat (length x))) with (n + length x)%nat by (unfold n; lia).
  set (P := firstn n B). set (Q := skipn (n + length x) B).
  assert (LP : length P = n) by (unfold P; rewrite length_firstn; lia).
  assert (E : P ++ x ++ Q = (P ++ x) ++ Q) by apply app_assoc.
  rewrite E.
  assert (LPx : length (P ++ x) = (n + length x)%nat) by (rewrite length_app, LP; reflexivity).
  assert (F1 : firstn (n + length x) ((P ++ x) ++ Q) = P ++ x) by (rewrite <- LPx; apply firstn_app_exact).
  assert (F2 : skipn (n + length x + length y) ((P ++ x) ++ Q) = skipn (length y) Q).
  { replace (n + length x + length y)%nat with (length y + length (P ++ x))%nat by (rewrite LPx; lia).
    rewrite <- skipn_skipn. rewrite skipn_app_exact. reflexivity. }
  rewrite F1, F2. unfold Q. rewrite skipn_skipn. rewrite length_app. rewrite <- !app_assoc.
  replace (length y + (n + length x))%nat with (n + (length x + length y))%nat by lia.
  reflexivity.
Qed.

(* 0x16730-0x16740: desk_known = 1, then desk_mac as three halfwords *)
Lemma rx_learn_eq : forall B src w0 w1 w2, length B = Z.to_nat W_LEN -> length src = 6%nat ->
  le2 w0 = sub src 0 2 -> le2 w1 = sub src 2 2 -> le2 w2 = sub src 4 2 ->
  upd (upd (upd (upd B 1764 (put 4 1)) 1768 (le2 w0)) 1770 (le2 w1)) 1772 (le2 w2) =
  set_S_desk_known (set_S_desk_mac B src) 1.
Proof.
  intros B src w0 w1 w2 LB Ls E0 E1 E2. rewrite E0, E1, E2.
  assert (L0 : length (sub src 0 2) = 2%nat) by (apply length_sub; lia).
  assert (L2 : length (sub src 2 2) = 2%nat) by (apply length_sub; lia).
  assert (L4 : length (sub src 4 2) = 2%nat) by (apply length_sub; lia).
  assert (LU : length (upd B 1764 (put 4 1)) = length B) by (apply length_upd_put; unfold W_LEN in *; lia).
  rewrite (rx_upd_app _ (sub src 0 2) (sub src 2 2) 1768 1770) by (rewrite ?L0, ?L2, ?LU; unfold W_LEN in *; lia).
  rewrite (rx_upd_app _ (sub src 0 2 ++ sub src 2 2) (sub src 4 2) 1768 1772)
    by (rewrite ?length_app, ?L0, ?L2, ?L4, ?LU; unfold W_LEN in *; lia).
  rewrite <- app_assoc, (rx_src3 src Ls).
  unfold set_S_desk_known, set_S_desk_mac, A_S_desk_known, A_S_desk_mac, OFF_g_s.
  apply upd_upd_comm; rewrite ?length_put, ?Ls; unfold W_LEN in *; lia.
Qed.

Lemma rx_ign_eq : forall B, upd B 19832 (put 8 (u_at B 19832 8 + 1)) = rx_ign B.
Proof.
  intros B. unfold rx_ign, set_S_stats_rx_ignored, S_stats_rx_ignored, u64. rewrite put_mod64 by lia. reflexivity.
Qed.

Lemma rx_acc_eq : forall B now,
  upd (upd B 19800 (put 8 (u_at B 19800 8 + 1))) 1824 (put 8 now) =
  set_S_last_rx_us (set_S_stats_rx_frames B (u64 (S_stats_rx_frames B + 1))) now.
Proof.
  intros B now. unfold set_S_last_rx_us, set_S_stats_rx_frames, S_stats_rx_frames, u64.
  rewrite put_mod64 by lia. reflexivity.
Qed.

Lemma rx_len_upd : forall (B v : list byte) k, length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> length (upd B k v) = Z.to_nat W_LEN.
Proof. intros B v k H Hk Hv. rewrite length_upd; [exact H | exact Hk | rewrite H; unfold W_LEN in *; lia]. Qed.

Ltac rx_len :=
  lazymatch goal with
  | |- length (upd ?X ?k ?v) = Z.to_nat W_LEN =>
      apply rx_len_upd;
      [ rx_len | unfold OFF_g_s; lia
      | rewrite ?length_put, ?length_le2, ?length_le4, ?length_le8; unfold OFF_g_s, W_LEN; lia ]
  | |- _ => assumption
  end.

Lemma rx_gf_upd : forall (B v : list byte) k, 0 <= k -> k + Z.of_nat (length v) <= OFF_g_fail_next ->
  length B = Z.to_nat W_LEN -> g_fail_next (upd B k v) = g_fail_next B.
Proof.
  intros B v k Hk Hv LB. unfold g_fail_next. apply u_at_upd_out; unfold OFF_g_fail_next, W_LEN in *; lia.
Qed.

Lemma rx_st_upd : forall (B v : list byte) k, 0 <= k -> (k + Z.of_nat (length v) <= 1760 \/ 1764 <= k) ->
  k + Z.of_nat (length v) <= W_LEN -> length B = Z.to_nat W_LEN -> S_state (upd B k v) = S_state B.
Proof.
  intros B v k Hk Hd Hv LB. unfold S_state, A_S_state. apply s32_at_upd_out; unfold OFF_g_s, W_LEN in *; lia.
Qed.

Ltac rx_side :=
  first [ lia
        | (rewrite ?length_put, ?length_le2, ?length_le4, ?length_le8; unfold OFF_g_s, OFF_g_fail_next, W_LEN in *; lia)
        | rx_len ].

(* ---- the frame struct at sp + 8 after diginet_frame_parse answered 0 ---- *)

Lemma rx_fbytes : forall m f bufp b fj, rw_cells rsegs m f (parse_cells bufp b fj) ->
  bytes_at rsegs m f (fr_dst b) /\ bytes_at rsegs m (f + 6) (fr_src b) /\
  length (fr_dst b) = 6%nat /\ length (fr_src b) = 6%nat.
Proof.
  intros m f bufp b fj [[Hwf Hb] _]. unfold parse_cells in Hwf, Hb. cbn [cells_wf cell_wf] in Hwf.
  destruct Hwf as (L1 & L2 & _). cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [B1 Hb]. apply bytes_at_app in Hb. destruct Hb as [B2 _].
  rewrite L1 in B2. refine (conj B1 (conj B2 (conj L1 L2))).
Qed.

Lemma rx_rd : forall m a bs k n x, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  x = a + k -> ov_read_bytes rsegs m (Z_to_bv 64 x) n = Some (sub bs k n).
Proof. intros m a bs k n x H Hk Hn ->. apply (bytes_at_read rsegs m a bs k n H Hk). lia. Qed.

(* the byte h.cmd at f + 30 *)
Lemma rx_cmd_rd : forall m f bufp b fj x, rw_cells rsegs m f (parse_cells bufp b fj) -> x = f + 30 ->
  ov_read_bytes rsegs m (Z_to_bv 64 x) 1 = Some [b8 (fr_cmd b)].
Proof.
  intros m f bufp b fj x H ->.
  exact (rw_cells_read_at rsegs m f (parse_cells bufp b fj) 30 (C1 (b8 (fr_cmd b))) 1 (Z_to_bv 64 (f + 30)) H
           eq_refl eq_refl eq_refl).
Qed.

Lemma rx_ro_bytes : forall m A bs, mem_inv rsegs m -> ro_bytes_b rsegs A bs = true -> 0 <= A ->
  A + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs m A bs.
Proof. intros m A bs MI H H0 H1. apply ro_bytes_at; try assumption. apply ro_bytes_b_sound. exact H. Qed.

(* rx's frame f, parsed, as on_announce / on_ack / on_data receive it (rx's sp is spz) *)
Lemma rx_dframe : forall m (sp : word) K bufp b fj, fr_code b = 0 -> bytes_at rsegs m bufp b ->
  rw_cells rsegs m (bv_unsigned sp + -104) (parse_cells bufp b fj) ->
  0 < bufp -> bufp + Z.of_nat (length b) < 2^64 ->
  (bufp + Z.of_nat (length b) <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= bufp) ->
  (bufp + Z.of_nat (length b) <= bv_unsigned sp - 2272 \/ bv_unsigned sp <= bufp) ->
  bv_unsigned sp mod 16 = 0 -> W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 2272 -> 2272 <= bv_unsigned sp ->
  0 <= K -> 112 + K <= 2272 ->
  dframe_at m (Z_to_bv 64 (bv_unsigned sp + -112)) K (bv_unsigned sp + -104) bufp b fj.
Proof.
  intros m sp K bufp b fj C0 BUF FR H0 H64 OW OWin S16 WOS LO K0 K1.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (U : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  unfold dframe_at, arg_blk, off_window, off_world in *. rewrite U.
  refine (conj C0 (conj BUF (conj _ (conj FR (conj _ _))))).
  - split; [lia|]. split; [lia|]. split; [exact OW | lia].
  - unfold W_BASE_PLAIN, W_LEN in *. split; [lia|]. split; [lia|]. split; lia.
  - Z.div_mod_to_equations. lia.
Qed.

(* ---- the entry memory's heap frame and RELRO tables, carried to a callee ---- *)

Local Abbreviation rx_fp s := ([(bv_unsigned s - 2272, bv_unsigned s); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)]).

Lemma rx_tframe : forall m0 m (sp sp' : word) K' TF, tframe_at m0 sp 2272 TF -> munch (rx_fp sp) m0 m ->
  bv_unsigned sp - 2272 <= bv_unsigned sp' - K' -> bv_unsigned sp' <= bv_unsigned sp -> tframe_at m sp' K' TF.
Proof.
  intros m0 m sp sp' K' TF T MU H1 H2. destruct TF as [fr|]; [|exact I].
  unfold tframe_at in *. destruct T as (P & BA & OW & OWin). unfold off_world, off_window in *.
  refine (conj P (conj _ (conj OW _))); [| lia].
  eapply bytes_at_transport; [exact BA | exact MU |]. cbn [disjoint_from].
  refine (conj _ (conj _ I)); lia.
Qed.

Lemma rx_relro : forall m0 m (sp : word), relro_img m0 -> munch (rx_fp sp) m0 m ->
  W_BASE_PLAIN + W_LEN <= bv_unsigned sp - 2272 -> relro_img m.
Proof.
  intros m0 m sp R MU H i Hi. unfold mrd. rewrite (MU (wa (RELRO_BASE + i))); [exact (R i Hi) |].
  unfold RELRO_BASE, RELRO_LEN in *. cbn [outside]. rewrite wa_unsigned by lia.
  unfold W_BASE_PLAIN, W_LEN in *. refine (conj _ (conj _ I)); lia.
Qed.

(* ---- rx's own frame: [sp - 112, sp - 104) unused, f at sp - 104 (64 bytes), the saves at sp - 40 ---- *)

Lemma rx_stk_close : forall m lo (z : Z) cs, stk rsegs m lo (z + -112) -> stk rsegs m (z + -112) (z + -104) ->
  rw_cells rsegs m (z + -104) cs -> cells_size cs = 64%nat -> lo <= z + -112 -> stk rsegs m lo (z + -40).
Proof.
  intros m lo z cs H1 H2 H3 H4 H5.
  pose proof (stk_merge rsegs m lo (z + -112) (z + -104) H1 H2 ltac:(lia)) as H.
  pose proof (stk_release rsegs m lo (z + -104) cs H H3 ltac:(lia)) as H'.
  rewrite H4 in H'. replace (z + -104 + Z.of_nat 64) with (z + -40) in H' by lia. exact H'.
Qed.

Lemma rx_stk_u : forall m (z : Z) cs, stk rsegs m (z + -112) (z + -104) -> rw_cells rsegs m (z + -104) cs ->
  cells_size cs = 64%nat -> stk rsegs m (z + -112) (z + -40).
Proof.
  intros m z cs H1 H2 H3.
  pose proof (stk_release rsegs m (z + -112) (z + -104) cs H1 H2 ltac:(lia)) as H'.
  rewrite H3 in H'. replace (z + -104 + Z.of_nat 64) with (z + -40) in H' by lia. exact H'.
Qed.

(* ---- tactics ---- *)

Ltac rx_br v tac :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v; [cbv iota | symmetry; tac]
  end.

Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

(* replace the world of the current memory by Bn (tac proves the two equal, in either direction) *)
Ltac rx_rw_world Bn tac :=
  let mm := cur_mem in
  lazymatch goal with
  | H : rw_cells rsegs mm W_BASE_PLAIN [CB _ ?X] |- _ =>
      replace X with Bn in H by (first [ (symmetry; tac) | tac ])
  end.

(* after a callee walk: its stk in rx's terms *)
Ltac rx_after_call Usp :=
  repeat match goal with
  | H : stk rsegs _ _ (bv_unsigned (Z_to_bv 64 (bv_unsigned ?s + -112))) |- _ => rewrite Usp in H
  end.

Ltac rx_clear_post :=
  repeat match goal with
  | H : bytes_at rsegs _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H
  end.

Theorem diginet_session_rx_holds :
  bcmp_contract -> diginet_frame_parse_contract -> diginet_mac_is_digidesign_contract ->
  on_announce_contract -> on_ack_contract -> on_data_contract -> session_lost_contract ->
  diginet_session_tick_contract -> diginet_session_rx_contract.
Proof.
  intros BC PARSE MAC ONA ONK OND SLC TKC.
  unfold bcmp_contract, BCMP in BC.
  unfold diginet_frame_parse_contract, DIGINET_FRAME_PARSE in PARSE.
  unfold diginet_mac_is_digidesign_contract, DIGINET_MAC_IS_DIGIDESIGN in MAC.
  unfold on_announce_contract, on_announce_ENTRY, on_announce_FRAME in ONA.
  unfold on_ack_contract, on_ack_ENTRY, on_ack_FRAME in ONK.
  unfold on_data_contract, on_data_ENTRY, on_data_FRAME in OND.
  unfold session_lost_contract, session_lost_ENTRY, session_lost_FRAME in SLC.
  unfold diginet_session_tick_contract, diginet_session_tick_ENTRY, diginet_session_tick_FRAME in TKC.
  unfold diginet_session_rx_contract, diginet_session_rx_ENTRY, diginet_session_rx_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    bufp now r b B B' TF -> -> -> -> Hnow BUF ARG WM GF HM TFA RR S16 ST LO WOS MI.
  unfold arg_blk, off_world, off_window in ARG. destruct ARG as (Hb0 & Hb64 & OWb & OWinb).
  unfold w_off_stack in WOS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  pose proof (bytes_at_bound rsegs m bufp b BUF) as BB.
  wk_facts.
  assert (EOFF : OFF_g_s = 1648) by reflexivity.
  assert (Usp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112)
    by (apply unsigned_lit; lia).
  pose proof (rx_at8_range b 28) as Rc. change (at8 b 28) with (fr_cmd b) in Rc.
  rewrite rx_m_eq in HM. change DIGINET_OK with 0 in HM.
  pose proof (munch_refl (rx_fp sp) m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  rename m into m0.
  carve_frame 40%nat ST. rename FR into FRh.
  carve_frame 64%nat ST. rename FR into FRf. rename junk0 into fj.
  destruct (stk_split rsegs m0 lo (bv_unsigned sp + -112) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STb].
  clear ST. rename ST1 into ST.
  (* 0x1662c-0x16640: addi sp, sp, -112; sd ra, s0, s1, s2, s3 *)
  do 6 step.
  lazymatch goal with HF : rw_cells _ _ (bv_unsigned sp + -40) ?cs |- _ => set (SV := cs) in HF end.
  assert (LSV : cells_size SV = 40%nat) by reflexivity.

  (* ==== EPI, 0x166ec: ld ra, s0, s1, s2, s3; addi sp, sp, 112; ret ==== *)
  assert (EPI : forall (m4 : word -> option byte)
                  (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
      wmem rsegs m4 B' -> g_fail_next B' <= 1 ->
      rw_cells rsegs m4 (bv_unsigned sp + -40) SV -> stk rsegs m4 lo (bv_unsigned sp + -40) ->
      munch (rx_fp sp) m0 m4 -> wmono rsegs m0 m4 -> mem_inv rsegs m4 ->
      evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r)
                          x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x166ec) fc None m4 (seg_rom rsegs))).
  { intros m4 x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 WM4 GF4 FR4 ST4 MU4 WMo4 MI4.
    unfold SV in FR4.
    do 5 step.
    release_frame FR4 ST4 (bv_unsigned sp).
    do 2 step.
    apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity |].
    refine (conj MU4 (conj WMo4 (conj MI4 (conj ST4 (conj WM4 GF4))))). }

  (* ==== IGN, 0x166e0: stats.rx_ignored++ (ld, addi, sd), then EPI ==== *)
  assert (IGN : forall (m4 : word -> option byte) (Bi : list byte)
                  (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
      B' = rx_ign Bi -> wmem rsegs m4 Bi -> g_fail_next Bi <= 1 ->
      rw_cells rsegs m4 (bv_unsigned sp + -40) SV -> stk rsegs m4 lo (bv_unsigned sp + -40) ->
      munch (rx_fp sp) m0 m4 -> wmono rsegs m0 m4 -> mem_inv rsegs m4 ->
      evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r)
                          x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18152))
                          s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x166e0) fc None m4 (seg_rom rsegs))).
  { intros m4 Bi x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 EB WM4 GF4 FR4 ST4 MU4 WMo4 MI4.
    pose proof (wm_len _ _ _ _ WM4) as LB4.
    do 3 step.
    rx_rw_world (rx_ign Bi) ltac:(apply rx_ign_eq).
    eapply EPI; [rewrite EB; assumption | | exact FR4 | exact ST4 | exact MU4 | exact WMo4 | exact MI4].
    rewrite EB. unfold rx_ign, set_S_stats_rx_ignored, A_S_stats_rx_ignored.
    rewrite rx_gf_upd by rx_side. exact GF4. }

  (* 0x16644-0x16670: mv s1, a0; li a0, -1; beqz s1; beqz a1; mv s0, a3; mv a3, a2; lui a0, 4;
     addiw s3, a0, 1768; add s3, s1, s3; addi a2, sp, 8; mv a0, a1; mv a1, a3 *)
  do 3 step.
  rx_br false ltac:(rewrite rx_eqb by lia; apply Z.eqb_neq; lia).
  step.
  rx_br false ltac:(unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  do 8 step.
  (* 0x16674: jal diginet_frame_parse (buf, len, &f) *)
  step.
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply PARSE with (buf := bufp) (f := bv_unsigned sp + -104) (lo := lo) (b := b) (fj := fj);
      [ lia | lia | exact BUF | exact FRf | lia | rewrite Usp; exact ST | rewrite Usp; lia | rewrite Usp; lia
      | rewrite Usp; lia | assumption ]
    | wk_post_call rsegs mm ].
  rx_after_call Usp.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -104) (if _ then _ else _) |- _ => rename H into FRf end.
  lazymatch goal with H : stk rsegs _ lo (bv_unsigned sp + -112) |- _ => rename H into ST end.
  (* 0x16678: bnez a0, 0x166e0 *)
  step.
  destruct (Z.eqb_spec (fr_code b) 0) as [C0|C0].
  2:{
    (* the frame does not parse: stats.rx_ignored++, return its code *)
    rx_br true ltac:(rewrite rx_eqb by (pose proof (fr_code_cases b); lia);
                     rewrite (proj2 (Z.eqb_neq _ _) C0); reflexivity).
    try rewrite (proj2 (Z.eqb_neq _ _) C0) in FRf. try rewrite (proj2 (Z.eqb_neq _ _) C0) in HM.
    cbv iota in FRf. cbn [negb] in HM.
    injection HM as EB Er. subst r.
    eapply IGN with (Bi := B);
      [ congruence | exact WM | exact GF | exact FRh
      | apply (rx_stk_close _ _ _ _ ST STb FRf eq_refl); lia | exact MU0 | exact WM0 | assumption ]. }
  rx_br false ltac:(rewrite C0; vm_compute; reflexivity).
  try rewrite (proj2 (Z.eqb_eq _ _) C0) in FRf. try rewrite (proj2 (Z.eqb_eq _ _) C0) in HM.
  cbv iota in FRf. cbn [negb] in HM.
  assert (Ecs : cells_size (parse_cells bufp b fj) = 64%nat) by reflexivity.
  destruct (rx_fbytes _ _ _ _ _ FRf) as (BDST & BSRC & LDST & LSRC).
  replace (bv_unsigned sp + -104 + 6) with (bv_unsigned sp + -98) in BSRC by lia.

  (* ==== TICK, 0x167f4: mv a0, s1; mv a1, s0; jal diginet_session_tick; j 0x166ec ==== *)
  assert (TICK : forall (m4 : word -> option byte) (Bt : list byte)
                   (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      diginet_session_tick_m timg_plain TF Bt now = Some (B', r) ->
      wmem rsegs m4 Bt -> g_fail_next Bt <= 1 -> rw_cells rsegs m4 (bv_unsigned sp + -40) SV ->
      stk rsegs m4 lo (bv_unsigned sp + -112) -> stk rsegs m4 (bv_unsigned sp + -112) (bv_unsigned sp + -40) ->
      munch (rx_fp sp) m0 m4 -> wmono rsegs m0 m4 -> mem_inv rsegs m4 ->
      evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 now)
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (bv_unsigned sp + -98)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18152))
                          s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x167f4) fc None m4 (seg_rom rsegs))).
  { intros m4 Bt ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HT WM4 GF4 FR4 ST4 STu4 MU4 WMo4 MI4.
    do 3 step.
    eapply evt_cut;
      [ eapply TKC with (lo := lo) (now := now) (r := r) (B := Bt) (B' := B') (TF := TF);
        [ reflexivity | reflexivity | exact Hnow | exact WM4 | exact GF4 | exact HT
        | eapply rx_tframe; [exact TFA | exact MU4 | rewrite Usp; lia | rewrite Usp; lia]
        | eapply rx_relro; [exact RR | exact MU4 | lia]
        | rewrite Usp; Z.div_mod_to_equations; lia | rewrite Usp; exact ST4 | rewrite Usp; lia
        | unfold w_off_stack; rewrite Usp; lia | exact MI4 ]
      | wk_post_call rsegs m4 ].
    rx_after_call Usp.
    step.
    let mm := cur_mem in
    lazymatch goal with H : stk rsegs mm lo (bv_unsigned sp + -112) |- _ =>
      pose proof (stk_merge rsegs mm lo _ _ H STu4 ltac:(lia)) as STc end.
    eapply EPI; eassumption. }

  (* ==== ACC, 0x16744: the frame is the desk's ==== *)
  assert (ACC : forall (m4 : word -> option byte) (Ba : list byte)
                  (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      rx_accept_m timg_plain TF b now Ba = Some (B', r) ->
      wmem rsegs m4 Ba -> g_fail_next Ba <= 1 -> rw_cells rsegs m4 (bv_unsigned sp + -40) SV ->
      rw_cells rsegs m4 (bv_unsigned sp + -104) (parse_cells bufp b fj) ->
      stk rsegs m4 lo (bv_unsigned sp + -112) -> stk rsegs m4 (bv_unsigned sp + -112) (bv_unsigned sp + -104) ->
      bytes_at rsegs m4 bufp b -> munch (rx_fp sp) m0 m4 -> wmono rsegs m0 m4 -> mem_inv rsegs m4 ->
      evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 now)
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (bv_unsigned sp + -98)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18152))
                          s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x16744) fc None m4 (seg_rom rsegs))).
  { intros m4 Ba ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HA WM4 GF4 FR4 FF4 ST4 STb4 BUF4
      MU4 WMo4 MI4.
    pose proof (wm_len _ _ _ _ WM4) as LB4.
    pose proof (rx_stk_u _ _ _ STb4 FF4 Ecs) as STu4.
    pose proof (s32_range Ba A_S_state) as RSa. change (s32_at Ba A_S_state) with (S_state Ba) in RSa.
    unfold rx_accept_m in HA.
    (* 0x16744-0x1674c: lw a0, 112(s1); li a1, 3; bne a0, a1, 0x16758 *)
    step. change (s32_at Ba 1760) with (S_state Ba).
    do 2 step.
    destruct (Z.eqb_spec (S_state Ba) DIGINET_S_CLOSED) as [SC|SC].
    { (* CLOSED: 0x16750 li a0, 0; j 0x166ec *)
      rx_br false ltac:(rewrite rx_eqb by lia; rewrite SC; reflexivity).
      try rewrite (proj2 (Z.eqb_eq _ _) SC) in HA. cbv iota in HA. injection HA as EB Er. subst r.
      do 2 step.
      eapply EPI;
        [ rewrite <- EB; exact WM4 | rewrite <- EB; exact GF4 | exact FR4
        | apply (rx_stk_close _ _ _ _ ST4 STb4 FF4 Ecs); lia | exact MU4 | exact WMo4 | exact MI4 ]. }
    rx_br true ltac:(rewrite rx_eqb by lia; apply negb_true_iff; apply Z.eqb_neq; exact SC).
    try rewrite (proj2 (Z.eqb_neq _ _) SC) in HA. cbv iota zeta in HA.
    (* 0x16758-0x1676c: ld a2, 0(s3); lbu a1, 38(sp); addi a2, a2, 1; sd a2, 0(s3); li a2, 223; sd s0, 176(s1) *)
    pose proof (rx_cmd_rd m4 _ _ _ _ (bv_unsigned sp + -74) FF4 ltac:(lia)) as HRc.
    do 2 step.
    rewrite (rx_zxb (fr_cmd b) Rc).
    do 4 step.
    rx_rw_world (set_S_last_rx_us (set_S_stats_rx_frames Ba (u64 (S_stats_rx_frames Ba + 1))) now)
      ltac:(apply rx_acc_eq).
    set (B1 := set_S_last_rx_us (set_S_stats_rx_frames Ba (u64 (S_stats_rx_frames Ba + 1))) now) in *.
    assert (LB1 : length B1 = Z.to_nat W_LEN)
      by (unfold B1, set_S_last_rx_us, set_S_stats_rx_frames, A_S_last_rx_us, A_S_stats_rx_frames; rx_len).
    assert (GB1 : g_fail_next B1 = g_fail_next Ba)
      by (unfold B1, set_S_last_rx_us, set_S_stats_rx_frames, A_S_last_rx_us, A_S_stats_rx_frames;
          rewrite !rx_gf_upd by rx_side; reflexivity).
    assert (SB1 : S_state B1 = S_state Ba)
      by (unfold B1, set_S_last_rx_us, set_S_stats_rx_frames, A_S_last_rx_us, A_S_stats_rx_frames;
          rewrite !rx_st_upd by rx_side; reflexivity).
    (* 0x16770: bge a2, a1, 0x16794 *)
    step.
    destruct (Z.leb_spec (fr_cmd b) 223) as [Cle|Cgt].
    - (* cmd <= 223: 0x16794 beqz a1, 0x167d4 *)
      rx_br true ltac:(rewrite rx_lts by lia; apply negb_true_iff; apply Z.ltb_ge; lia).
      step.
      destruct (Z.eqb_spec (fr_cmd b) 0) as [Cd|Cd].
      + (* DATA: 0x167d4 addi a1, sp, 8; mv a0, s1; mv a2, s0; jal on_data; j 0x167f4 *)
        rx_br true ltac:(rewrite rx_eqb by lia; apply Z.eqb_eq; exact Cd).
        rewrite (rx_sw_data timg_plain TF b now B1 Cd) in HA.
        destruct (on_data_m timg_plain TF B1 b now) as [[B2 []]|] eqn:HO; try rewrite HO in HA; cbv beta iota in HA;
          [|discriminate HA].
        do 4 step.
        let mm := cur_mem in
        eapply evt_cut;
          [ eapply OND with (lo := lo) (fp := bv_unsigned sp + -104) (buf := bufp) (now := now) (b := b) (fj := fj)
              (B := B1) (B' := B2) (TF := TF);
            [ reflexivity | reflexivity | reflexivity | exact Hnow
            | apply rx_dframe; first [assumption | lia]
            | assumption | rewrite GB1; exact GF4 | exact HO
            | eapply rx_tframe; [exact TFA | exact MU4 | rewrite Usp; lia | rewrite Usp; lia]
            | eapply rx_relro; [exact RR | exact MU4 | lia]
            | rewrite Usp; Z.div_mod_to_equations; lia | rewrite Usp; exact ST4 | rewrite Usp; lia
            | unfold w_off_stack; rewrite Usp; lia | assumption ]
          | wk_post_call rsegs mm ].
        rx_after_call Usp.
        step.
        eapply TICK; eassumption.
      + rx_br false ltac:(rewrite rx_eqb by lia; apply Z.eqb_neq; exact Cd).
        (* 0x16798-0x1679c: li a0, 160; bne a1, a0, 0x167e8 *)
        do 2 step.
        destruct (Z.eqb_spec (fr_cmd b) 160) as [Ck|Ck].
        * (* ACK: 0x167a0 addi a1, sp, 8; mv a0, s1; jal on_ack; j 0x167f4 *)
          rx_br false ltac:(rewrite rx_eqb by lia; rewrite Ck; reflexivity).
          rewrite (rx_sw_ack timg_plain TF b now B1 Ck) in HA.
          destruct (on_ack_m timg_plain TF B1 b) as [[B2 []]|] eqn:HO; try rewrite HO in HA; cbv beta iota in HA;
            [|discriminate HA].
          do 3 step.
          let mm := cur_mem in
          eapply evt_cut;
            [ eapply ONK with (lo := lo) (fp := bv_unsigned sp + -104) (buf := bufp) (b := b) (fj := fj)
                (B := B1) (B' := B2) (TF := TF);
              [ reflexivity | reflexivity
              | apply rx_dframe; first [assumption | lia]
              | assumption | rewrite GB1; exact GF4 | exact HO
              | eapply rx_tframe; [exact TFA | exact MU4 | rewrite Usp; lia | rewrite Usp; lia]
              | eapply rx_relro; [exact RR | exact MU4 | lia]
              | rewrite Usp; Z.div_mod_to_equations; lia | rewrite Usp; exact ST4 | rewrite Usp; lia
              | unfold w_off_stack; rewrite Usp; lia | assumption ]
            | wk_post_call rsegs mm ].
          rx_after_call Usp.
          step.
          eapply TICK; eassumption.
        * (* not handled: 0x167e8 stats.rx_ignored++; 0x167f4 *)
          rx_br true ltac:(rewrite rx_eqb by lia; apply negb_true_iff; apply Z.eqb_neq; exact Ck).
          rewrite (rx_sw_other timg_plain TF b now B1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in HA.
          cbv beta iota in HA.
          do 3 step.
          rx_rw_world (rx_ign B1) ltac:(apply rx_ign_eq).
          eapply TICK; [exact HA | assumption | | eassumption ..].
          unfold rx_ign, set_S_stats_rx_ignored, A_S_stats_rx_ignored. rewrite rx_gf_upd by rx_side.
          rewrite GB1. exact GF4.
    - (* cmd > 223: 0x16774 addi a2, a1, -224; li a3, 2; bgeu a2, a3, 0x167b0 *)
      rx_br false ltac:(rewrite rx_lts by lia; apply negb_false_iff; apply Z.ltb_lt; lia).
      do 3 step.
      destruct (Z.ltb_spec (fr_cmd b) 226) as [Ca|Ca].
      + (* ANNOUNCE, ANNOUNCE_SESSION: 0x16780 addi a1, sp, 8; mv a0, s1; mv a2, s0; jal on_announce *)
        rx_br false ltac:(rewrite rx_ltu by lia; apply negb_false_iff; apply Z.ltb_lt; lia).
        rewrite (rx_sw_ann timg_plain TF b now B1 ltac:(lia)) in HA.
        destruct (on_announce_m timg_plain TF B1 b now) as [[B2 []]|] eqn:HO; try rewrite HO in HA;
          cbv beta iota in HA; [|discriminate HA].
        do 4 step.
        let mm := cur_mem in
        eapply evt_cut;
          [ eapply ONA with (lo := lo) (fp := bv_unsigned sp + -104) (buf := bufp) (now := now) (b := b) (fj := fj)
              (B := B1) (B' := B2) (TF := TF);
            [ reflexivity | reflexivity | reflexivity | exact Hnow
            | apply rx_dframe; first [assumption | lia]
            | assumption | rewrite GB1; exact GF4 | exact HO
            | eapply rx_tframe; [exact TFA | exact MU4 | rewrite Usp; lia | rewrite Usp; lia]
            | eapply rx_relro; [exact RR | exact MU4 | lia]
            | rewrite Usp; Z.div_mod_to_equations; lia | rewrite Usp; exact ST4 | rewrite Usp; lia
            | unfold w_off_stack; rewrite Usp; lia | assumption ]
          | wk_post_call rsegs mm ].
        rx_after_call Usp.
        step.
        eapply TICK; eassumption.
      + rx_br true ltac:(rewrite rx_ltu by lia; apply negb_true_iff; apply Z.ltb_ge; lia).
        (* 0x167b0-0x167b4: li a2, 227; bne a1, a2, 0x167e8 *)
        do 2 step.
        destruct (Z.eqb_spec (fr_cmd b) 227) as [Cx|Cx].
        * (* DISCONNECT: 0x167b8 addiw a0, a0, -1; li a1, 1; bltu a1, a0, 0x167f4 *)
          rx_br false ltac:(rewrite rx_eqb by lia; rewrite Cx; reflexivity).
          rewrite (rx_sw_disc timg_plain TF b now B1 Cx), SB1 in HA.
          do 3 step.
          destruct ((S_state Ba =? 2) || (S_state Ba =? 1)) eqn:SW; try rewrite SW in HA; cbv beta iota in HA.
          -- (* ONLINE or WAKING: 0x167c4 li a1, 7; mv a0, s1; jal session_lost; j 0x167f4 *)
             rx_br false ltac:(rewrite (rx_state_cond (S_state Ba) RSa), SW; reflexivity).
             destruct (session_lost_m timg_plain TF B1 7) as [[B2 []]|] eqn:HO; try rewrite HO in HA;
               cbv beta iota in HA; [|discriminate HA].
             do 3 step.
             let mm := cur_mem in
             eapply evt_cut;
               [ eapply SLC with (lo := lo) (why := 7) (B := B1) (B' := B2) (TF := TF);
                 [ reflexivity | reflexivity | lia | assumption | rewrite GB1; exact GF4 | exact HO
                 | eapply rx_tframe; [exact TFA | exact MU4 | rewrite Usp; lia | rewrite Usp; lia]
                 | eapply rx_relro; [exact RR | exact MU4 | lia]
                 | rewrite Usp; Z.div_mod_to_equations; lia | rewrite Usp; exact ST4 | rewrite Usp; lia
                 | unfold w_off_stack; rewrite Usp; lia | assumption ]
               | wk_post_call rsegs mm ].
             rx_after_call Usp.
             step.
             eapply TICK; eassumption.
          -- (* neither: straight to 0x167f4 *)
             rx_br true ltac:(rewrite (rx_state_cond (S_state Ba) RSa), SW; reflexivity).
             eapply TICK; [exact HA | assumption | rewrite GB1; exact GF4 | eassumption ..].
        * (* not handled: 0x167e8 stats.rx_ignored++; 0x167f4 *)
          rx_br true ltac:(rewrite rx_eqb by lia; apply negb_true_iff; apply Z.eqb_neq; exact Cx).
          rewrite (rx_sw_other timg_plain TF b now B1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in HA.
          cbv beta iota in HA.
          do 3 step.
          rx_rw_world (rx_ign B1) ltac:(apply rx_ign_eq).
          eapply TICK; [exact HA | assumption | | eassumption ..].
          unfold rx_ign, set_S_stats_rx_ignored, A_S_stats_rx_ignored. rewrite rx_gf_upd by rx_side.
          rewrite GB1. exact GF4. }

  (* ==== D0, 0x166c0: lw a0, 116(s1); beqz a0, 0x16708 ==== *)
  assert (D0 : forall (m4 : word -> option byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      wmem rsegs m4 B -> rw_cells rsegs m4 (bv_unsigned sp + -40) SV ->
      rw_cells rsegs m4 (bv_unsigned sp + -104) (parse_cells bufp b fj) ->
      stk rsegs m4 lo (bv_unsigned sp + -112) -> stk rsegs m4 (bv_unsigned sp + -112) (bv_unsigned sp + -104) ->
      bytes_at rsegs m4 bufp b -> munch (rx_fp sp) m0 m4 -> wmono rsegs m0 m4 -> mem_inv rsegs m4 ->
      rx_rest_m timg_plain TF b now B = Some (B', r) ->
      evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 now)
                          (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s)) x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (bv_unsigned sp + -98)) (Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s + 18152))
                          s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x166c0) fc None m4 (seg_rom rsegs))).
  { intros m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? WM4 FR4 FF4 ST4 STb4 BUF4 MU4 WMo4 MI4 HR.
    destruct (rx_fbytes _ _ _ _ _ FF4) as (BDST4 & BSRC4 & _ & _).
    replace (bv_unsigned sp + -104 + 6) with (bv_unsigned sp + -98) in BSRC4 by lia.
    unfold rx_rest_m in HR.
    pose proof (s32_range B A_S_desk_known) as RDK. change (s32_at B A_S_desk_known) with (S_desk_known B) in RDK.
    step. change (s32_at B 1764) with (S_desk_known B).
    step.
    destruct (Z.eqb_spec (S_desk_known B) 0) as [DK|DK].
    - (* the desk is not known: 0x16708 lbu a0, 38(sp); addi a0, a0, -226; li a1, -2; bltu a0, a1, 0x16750 *)
      rx_br true ltac:(rewrite rx_eqb by lia; apply Z.eqb_eq; exact DK).
      try rewrite (proj2 (Z.eqb_eq _ _) DK) in HR. cbn [negb] in HR.
      unfold DIGINET_CMD_ANNOUNCE, DIGINET_CMD_ANNOUNCE_SESSION in HR.
      pose proof (rx_cmd_rd m4 _ _ _ _ (bv_unsigned sp + -74) FF4 ltac:(lia)) as HRc.
      step.
      rewrite (rx_zxb (fr_cmd b) Rc).
      do 3 step.
      destruct ((fr_cmd b =? 224) || (fr_cmd b =? 225)) eqn:ANN; try rewrite ANN in HR; cbn [negb] in HR.
      + (* an announce: 0x16718 mv a0, s2; jal diginet_mac_is_digidesign; beqz a0, 0x166e0 *)
        rx_br false ltac:(rewrite (rx_ann_cond (fr_cmd b) Rc), ANN; reflexivity).
        do 2 step.
        eapply evt_cut.
        { eapply MAC with (mac := bv_unsigned sp + -98) (l := fr_src b); [lia | exact LSRC | exact BSRC4]. }
        intros ms' (a1' & a2' & ->).
        rewrite (ret_pc_even 0x16720) by (first [lia | reflexivity]).
        step.
        destruct (oui_of (fr_src b)) eqn:OUI; try rewrite OUI in HR; cbn [negb] in HR.
        * (* learn the desk: 0x16724 lh a0/a1/a2, 0/2/4(s2); li a3, 1; sw a3, 116(s1);
             sh a0/a1/a2, 120/122/124(s1) *)
          rx_br false ltac:(vm_compute; reflexivity).
          pose proof (rx_rd m4 _ (fr_src b) 0 2 (bv_unsigned sp + -98) BSRC4 ltac:(lia) ltac:(rewrite LSRC; lia)
                        ltac:(lia)) as HR0.
          pose proof (rx_rd m4 _ (fr_src b) 2 2 (bv_unsigned sp + -96) BSRC4 ltac:(lia) ltac:(rewrite LSRC; lia)
                        ltac:(lia)) as HR2.
          pose proof (rx_rd m4 _ (fr_src b) 4 2 (bv_unsigned sp + -94) BSRC4 ltac:(lia) ltac:(rewrite LSRC; lia)
                        ltac:(lia)) as HR4.
          do 3 step.
          do 5 step.
          rx_rw_world (set_S_desk_known (set_S_desk_mac B (fr_src b)) 1)
            ltac:(apply rx_learn_eq; [exact LB | exact LSRC | (apply rx_le2_lh; apply length_sub; lia) ..]).
          eapply ACC; [exact HR | assumption | | eassumption ..].
          unfold set_S_desk_known, set_S_desk_mac, A_S_desk_known, A_S_desk_mac.
          rewrite !rx_gf_upd by rx_side. exact GF.
        * (* not a Digidesign source: 0x166e0 *)
          rx_br true ltac:(vm_compute; reflexivity).
          injection HR as EB Er. subst r.
          eapply IGN with (Bi := B);
            [ congruence | exact WM4 | exact GF | exact FR4
            | apply (rx_stk_close _ _ _ _ ST4 STb4 FF4 Ecs); lia | exact MU4 | exact WMo4 | exact MI4 ].
      + (* not an announce: 0x16750 li a0, 0; j 0x166ec *)
        rx_br true ltac:(rewrite (rx_ann_cond (fr_cmd b) Rc), ANN; reflexivity).
        injection HR as EB Er. subst r.
        do 2 step.
        eapply EPI;
          [ rewrite <- EB; exact WM4 | rewrite <- EB; exact GF | exact FR4
          | apply (rx_stk_close _ _ _ _ ST4 STb4 FF4 Ecs); lia | exact MU4 | exact WMo4 | exact MI4 ].
    - (* the desk is known: 0x166c8 addi a1, s1, 120; li a2, 6; mv a0, s2; jal bcmp (src, desk_mac, 6) *)
      rx_br false ltac:(rewrite rx_eqb by lia; apply Z.eqb_neq; exact DK).
      try rewrite (proj2 (Z.eqb_neq _ _) DK) in HR. cbn [negb] in HR.
      do 4 step.
      assert (L1768 : length (sub B 1768 6) = 6%nat) by (apply length_sub; lia).
      destruct (memcmp_model_total (fr_src b) (sub B 1768 6) 6 ltac:(lia) ltac:(lia)) as [v4 Hv4].
      destruct (rx_bcmp_eq _ _ _ LSRC L1768 Hv4) as [EV4 RV4].
      change (sub B 1768 6) with (S_desk_mac B) in EV4.
      let mm := cur_mem in
      eapply evt_cut;
        [ eapply BC with (ls := fr_src b) (rs := sub B 1768 6) (v := v4);
          [ rewrite unsigned_lit by lia; exact BSRC4
          | rewrite unsigned_lit by lia; apply (wm_src rsegs W_BASE_PLAIN mm B 1768 6); [exact WM4 | lia | lia | lia]
          | rewrite unsigned_lit by lia; exact Hv4
          | assumption ]
        | wk_post_call rsegs mm ].
      rx_clear_post.
      (* 0x166d8: beqz a0, 0x16744 *)
      step.
      destruct (memeq 6 (fr_src b) (S_desk_mac B)) eqn:M4; try rewrite M4 in HR; cbn [negb] in HR.
      + rx_br true ltac:(rewrite rx_eqb by lia; rewrite EV4; first [exact M4 | reflexivity]).
        eapply ACC; [exact HR | eassumption ..].
      + rx_br false ltac:(rewrite rx_eqb by lia; rewrite EV4; first [exact M4 | reflexivity]).
        injection HR as EB Er. subst r.
        step.
        eapply IGN with (Bi := B);
          [ congruence | exact WM4 | exact GF | exact FR4
          | apply (rx_stk_close _ _ _ _ ST4 STb4 FF4 Ecs); lia | exact MU4 | exact WMo4 | assumption ]. }

  (* ==== the main path after the parse: 0x1667c-0x1668c addi s2, sp, 14; li a2, 6; mv a0, s2; mv a1, s1;
     jal bcmp (src, host_mac, 6) ==== *)
  do 5 step.
  assert (L1648 : length (sub B 1648 6) = 6%nat) by (apply length_sub; lia).
  destruct (memcmp_model_total (fr_src b) (sub B 1648 6) 6 ltac:(lia) ltac:(lia)) as [v1 Hv1].
  destruct (rx_bcmp_eq _ _ _ LSRC L1648 Hv1) as [EV1 RV1].
  change (sub B 1648 6) with (S_cfg_host_mac B) in EV1.
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply BC with (ls := fr_src b) (rs := sub B 1648 6) (v := v1);
      [ rewrite unsigned_lit by lia; exact BSRC
      | rewrite unsigned_lit by lia; apply (wm_src rsegs W_BASE_PLAIN mm B 1648 6); [exact WM | lia | lia | lia]
      | rewrite unsigned_lit by lia; exact Hv1
      | assumption ]
    | wk_post_call rsegs mm ].
  rx_clear_post.
  (* 0x16690: beqz a0, 0x166dc *)
  step.
  destruct (memeq 6 (fr_src b) (S_cfg_host_mac B)) eqn:M1; try rewrite M1 in HM; cbn [orb] in HM.
  { (* the source is the host: 0x166dc li a0, 0; IGN *)
    rx_br true ltac:(rewrite rx_eqb by lia; rewrite EV1; first [exact M1 | reflexivity]).
    cbv iota in HM. injection HM as EB Er. subst r.
    step.
    eapply IGN with (Bi := B);
      [ congruence | exact WM | exact GF | exact FRh
      | apply (rx_stk_close _ _ _ _ ST STb FRf Ecs); lia | exact MU0 | exact WM0 | assumption ]. }
  rx_br false ltac:(rewrite rx_eqb by lia; rewrite EV1; first [exact M1 | reflexivity]).
  (* 0x16694-0x166a0: addi a0, sp, 8; li a2, 6; mv a1, s1; jal bcmp (dst, host_mac, 6) *)
  do 4 step.
  destruct (memcmp_model_total (fr_dst b) (sub B 1648 6) 6 ltac:(lia) ltac:(lia)) as [v2 Hv2].
  destruct (rx_bcmp_eq _ _ _ LDST L1648 Hv2) as [EV2 RV2].
  change (sub B 1648 6) with (S_cfg_host_mac B) in EV2.
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply BC with (ls := fr_dst b) (rs := sub B 1648 6) (v := v2);
      [ rewrite unsigned_lit by lia; exact BDST
      | rewrite unsigned_lit by lia; apply (wm_src rsegs W_BASE_PLAIN mm B 1648 6); [exact WM | lia | lia | lia]
      | rewrite unsigned_lit by lia; exact Hv2
      | assumption ]
    | wk_post_call rsegs mm ].
  rx_clear_post.
  (* 0x166a4: beqz a0, 0x166c0 *)
  step.
  destruct (memeq 6 (fr_dst b) (S_cfg_host_mac B)) eqn:M2; try rewrite M2 in HM; cbn [negb andb orb] in HM.
  { (* the destination is the host: D0 *)
    rx_br true ltac:(rewrite rx_eqb by lia; rewrite EV2; first [exact M2 | reflexivity]).
    eapply D0; eassumption. }
  rx_br false ltac:(rewrite rx_eqb by lia; rewrite EV2; first [exact M2 | reflexivity]).
  (* 0x166a8-0x166b8: auipc a1; addi a0, sp, 8; addi a1, a1, -474 (BROADCAST); li a2, 6; jal bcmp (dst, BROADCAST, 6) *)
  do 5 step.
  assert (LBC : length BROADCAST = 6%nat) by reflexivity.
  destruct (memcmp_model_total (fr_dst b) BROADCAST 6 ltac:(lia) ltac:(lia)) as [v3 Hv3].
  destruct (rx_bcmp_eq _ _ _ LDST LBC Hv3) as [EV3 RV3].
  let mm := cur_mem in
  assert (BBC : bytes_at rsegs mm 66766 BROADCAST)
    by (apply rx_ro_bytes; [assumption | vm_compute; reflexivity | lia | rewrite LBC; lia]).
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply BC with (ls := fr_dst b) (rs := BROADCAST) (v := v3);
      [ rewrite unsigned_lit by lia; exact BDST
      | rewrite unsigned_lit by lia; exact BBC
      | rewrite unsigned_lit by lia; exact Hv3
      | assumption ]
    | wk_post_call rsegs mm ].
  rx_clear_post.
  (* 0x166bc: bnez a0, 0x166dc *)
  step.
  destruct (memeq 6 (fr_dst b) BROADCAST) eqn:M3; try rewrite M3 in HM; cbn [negb andb orb] in HM.
  { (* broadcast: D0 *)
    rx_br false ltac:(rewrite rx_eqb by lia; rewrite EV3; try rewrite M3; reflexivity).
    eapply D0; eassumption. }
  (* addressed to another host: 0x166dc li a0, 0; IGN *)
  rx_br true ltac:(rewrite rx_eqb by lia; rewrite EV3; try rewrite M3; reflexivity).
  injection HM as EB Er. subst r.
  step.
  eapply IGN with (Bi := B);
    [ congruence | exact WM | exact GF | exact FRh
    | apply (rx_stk_close _ _ _ _ ST STb FRf Ecs); lia | exact MU0 | exact WM0 | assumption ].
Qed.

Print Assumptions diginet_session_rx_holds.
