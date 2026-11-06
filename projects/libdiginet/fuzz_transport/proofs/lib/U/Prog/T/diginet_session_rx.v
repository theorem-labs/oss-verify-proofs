From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes Arr ZBridge Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import bcmp_c diginet_frame_parse_c
  diginet_mac_is_digidesign_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC
  on_announce_c on_ack_c on_data_c set_state_c diginet_session_tick_c diginet_session_rx_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the model, restated in the order the binary tests it ---- *)

Definition rx_ign (B : list byte) : list byte := set_S_stats_rx_ignored B (u64 (S_stats_rx_ignored B + 1)).

(* :298-316, the dispatch on the command *)
Definition rx_sw (I : timg) (F : option tframe) (B : list byte) (buf : list byte) (now : Z)
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
Definition rx_acc (I : timg) (F : option tframe) (B : list byte) (buf : list byte) (now : Z)
    : option (list byte * Z) :=
  if S_state B =? DIGINET_S_CLOSED then Some (B, DIGINET_OK)
  else
  match rx_sw I F (set_S_last_rx_us (set_S_stats_rx_frames B (u64 (S_stats_rx_frames B + 1))) now) buf now with
  | None => None
  | Some (B, _) => diginet_session_tick_m I F B now
  end.

(* :278-291, a frame from a foreign desk or an announce that names the desk *)
Definition rx_dk (I : timg) (F : option tframe) (B : list byte) (buf : list byte) (now : Z)
    : option (list byte * Z) :=
  if negb (S_desk_known B =? 0) then
    (if negb (memeq 6 (fr_src buf) (sub B 1768 6)) then Some (rx_ign B, DIGINET_OK) else rx_acc I F B buf now)
  else if negb ((fr_cmd buf =? 224) || (fr_cmd buf =? 225)) then Some (B, DIGINET_OK)
  else if negb (oui_of (fr_src buf)) then Some (rx_ign B, DIGINET_OK)
  else rx_acc I F (set_S_desk_known (set_S_desk_mac B (fr_src buf)) 1) buf now.

Lemma rx_m_eq : forall I F B buf now, diginet_session_rx_m I F B buf now =
  if negb (fr_code buf =? DIGINET_OK) then Some (rx_ign B, fr_code buf)
  else if memeq 6 (fr_src buf) (sub B 1648 6) ||
          (negb (memeq 6 (fr_dst buf) (sub B 1648 6)) && negb (memeq 6 (fr_dst buf) BROADCAST))
  then Some (rx_ign B, DIGINET_OK)
  else rx_dk I F B buf now.
Proof. reflexivity. Qed.

Lemma rx_sw_ann : forall I F B buf now, fr_cmd buf = 224 \/ fr_cmd buf = 225 ->
  rx_sw I F B buf now = on_announce_m I F B buf now.
Proof. intros I F B buf now [E|E]; unfold rx_sw; rewrite E; reflexivity. Qed.

Lemma rx_sw_ack : forall I F B buf now, fr_cmd buf = 160 -> rx_sw I F B buf now = on_ack_m I F B buf.
Proof. intros I F B buf now E. unfold rx_sw. rewrite E. reflexivity. Qed.

Lemma rx_sw_data : forall I F B buf now, fr_cmd buf = 0 -> rx_sw I F B buf now = on_data_m I F B buf now.
Proof. intros I F B buf now E. unfold rx_sw. rewrite E. reflexivity. Qed.

Lemma rx_sw_disc : forall I F B buf now, fr_cmd buf = 227 ->
  rx_sw I F B buf now =
  if (S_state B =? 2) || (S_state B =? 1) then session_lost_m I F B DIGINET_R_DESK_DISCONNECT else Some (B, tt).
Proof. intros I F B buf now E. unfold rx_sw. rewrite E. reflexivity. Qed.

Lemma rx_sw_ign : forall I F B buf now,
  fr_cmd buf <> 224 -> fr_cmd buf <> 225 -> fr_cmd buf <> 160 -> fr_cmd buf <> 0 -> fr_cmd buf <> 227 ->
  rx_sw I F B buf now = Some (rx_ign B, tt).
Proof.
  intros I F B buf now E1 E2 E3 E4 E5. unfold rx_sw. cbv zeta.
  assert (F1 : (fr_cmd buf =? DIGINET_CMD_ANNOUNCE) = false) by (apply Z.eqb_neq; exact E1).
  assert (F2 : (fr_cmd buf =? DIGINET_CMD_ANNOUNCE_SESSION) = false) by (apply Z.eqb_neq; exact E2).
  assert (F3 : (fr_cmd buf =? DIGINET_CMD_ACK) = false) by (apply Z.eqb_neq; exact E3).
  assert (F4 : (fr_cmd buf =? DIGINET_CMD_DATA) = false) by (apply Z.eqb_neq; exact E4).
  assert (F5 : (fr_cmd buf =? DIGINET_CMD_DISCONNECT) = false) by (apply Z.eqb_neq; exact E5).
  rewrite F1, F2, F3, F4, F5. reflexivity.
Qed.

(* ---- words ---- *)

Lemma rx_eqb_s : forall v w, -2^63 <= v < 2^63 -> -2^63 <= w < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
  intros v w Hv Hw. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec v w) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  assert (D : (v - w) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in D; [|lia]. destruct D as [c Ec]. nia.
Qed.

Lemma rx_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. apply rx_eqb_s; lia. Qed.

Lemma rx_ltu : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma rx_lts : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt x (2^63))), (proj2 (Z.ltb_lt y (2^63))) by lia. reflexivity.
Qed.

(* bltu a1 (= 1), a0 (= the state minus one, addiw): the state is neither ONLINE nor WAKING *)
Lemma rx_state_ltu : forall st, -2^31 <= st < 2^31 ->
  bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 st) + -1))) =
  negb ((st =? 2) || (st =? 1)).
Proof.
  intros st H. destruct (Z.eqb_spec st 2) as [->|N2]; [vm_compute; reflexivity|].
  destruct (Z.eqb_spec st 1) as [->|N1]; [vm_compute; reflexivity|]. cbn [orb negb].
  unfold bv_ltu. rewrite unsigned_lit by lia. rewrite !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Lemma rx_byte_range : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R. exact R. Qed.

Lemma rx_cmd_range : forall b, 0 <= fr_cmd b < 256.
Proof. intros b. unfold fr_cmd, at8, bz. apply rx_byte_range. Qed.

Lemma rx_zxb : forall c, 0 <= c < 256 -> zxb (b8 c) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold zxb, b8. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

(* andi a0, a0, 254 against 224: the command is ANNOUNCE (0xe0) or ANNOUNCE_SESSION (0xe1) *)
Lemma rx_land254 : forall c, 0 <= c < 256 ->
  0 <= Z.land c 254 < 256 /\ (Z.land c 254 =? 224) = ((c =? 224) || (c =? 225)).
Proof.
  intros c Hc.
  assert (H : forallb (fun n => (Z.leb 0 (Z.land (Z.of_nat n) 254) && Z.ltb (Z.land (Z.of_nat n) 254) 256) &&
                                Bool.eqb (Z.land (Z.of_nat n) 254 =? 224) ((Z.of_nat n =? 224) || (Z.of_nat n =? 225)))
                      (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat c)). rewrite Z2Nat.id in H by lia.
  assert (I : In (Z.to_nat c) (seq 0 256)) by (apply in_seq; lia).
  specialize (H I). apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [H1a H1b].
  apply Z.leb_le in H1a. apply Z.ltb_lt in H1b. apply Bool.eqb_prop in H2. split; [lia | exact H2].
Qed.

(* ---- memcmp and memeq ---- *)

Lemma rx_memeq_shift : forall n k x y l r,
  forallb (fun i => at8 (x :: l) i =? at8 (y :: r) i) (seq (S k) n) =
  forallb (fun i => at8 l i =? at8 r i) (seq k n).
Proof.
  induction n as [|n IH]; intros k x y l r; [reflexivity|].
  cbn [seq forallb]. rewrite IH. reflexivity.
Qed.

Lemma rx_memeq_cons : forall n x y l r,
  memeq (S n) (x :: l) (y :: r) = (bv_unsigned x =? bv_unsigned y) && memeq n l r.
Proof. intros n x y l r. unfold memeq. cbn [seq forallb]. rewrite rx_memeq_shift. reflexivity. Qed.

Lemma rx_memcmp_eq : forall n l r v, (n <= length l)%nat -> (n <= length r)%nat -> memcmp_model l r n = Some v ->
  (v =? 0) = memeq n l r /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr Hm.
  - cbn in Hm. injection Hm as <-. split; [reflexivity | lia].
  - destruct l as [|x l]; [cbn in Hl; lia|]. destruct r as [|y r]; [cbn in Hr; lia|].
    cbn [length] in Hl, Hr. rewrite rx_memeq_cons. cbn [memcmp_model] in Hm.
    pose proof (rx_byte_range x) as Rx. pose proof (rx_byte_range y) as Ry.
    destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|E].
    + cbn [andb]. apply (IH l r v); [lia | lia | exact Hm].
    + injection Hm as <-. cbn [andb]. split; [apply Z.eqb_neq; lia | lia].
Qed.

Lemma rx_cmp6 : forall l r, length l = 6%nat -> length r = 6%nat ->
  exists v, memcmp_model l r 6 = Some v /\ (v =? 0) = memeq 6 l r /\ -256 < v < 256.
Proof.
  intros l r Hl Hr. destruct (memcmp_model_total l r 6 ltac:(lia) ltac:(lia)) as [v Hv].
  exists v. split; [exact Hv|]. apply (rx_memcmp_eq 6 l r v); [lia | lia | exact Hv].
Qed.

(* BROADCAST in .rodata at 0x1049e *)
Lemma rx_bcast : forall m, mem_inv rsegs m -> bytes_at rsegs m 66718 BROADCAST.
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

(* ---- the frame struct after a parse that answered 0 ---- *)

Lemma rx_src_len : forall b, fr_code b = 0 -> length (fr_src b) = 6%nat.
Proof.
  intros b H. destruct (fr_code_ok b H) as (L & _). unfold fr_src. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma rx_dst_len : forall b, fr_code b = 0 -> length (fr_dst b) = 6%nat.
Proof. intros b H. destruct (fr_code_ok b H) as (L & _). unfold fr_dst. rewrite length_firstn. lia. Qed.

Lemma rx_pc_bytes : forall m f bufp b fj, rw_cells rsegs m f (parse_cells bufp b fj) -> fr_code b = 0 ->
  bytes_at rsegs m f (fr_dst b) /\ bytes_at rsegs m (f + 6) (fr_src b).
Proof.
  intros m f bufp b fj [[_ Hb] _] FC. unfold parse_cells in Hb. cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb as [H1 Hb]. apply bytes_at_app in Hb as [H2 _].
  rewrite (rx_dst_len b FC) in H2. split; [exact H1 | exact H2].
Qed.

(* the three halfword loads lh of f.src, as the kit reads them from its bytes *)
Lemma rx_src3 : forall X : list byte, length X = 6%nat ->
  firstn 2 (skipn 0 X) ++ firstn 2 (skipn 2 X) ++ firstn 2 (skipn 4 X) = X.
Proof.
  intros X L. do 6 (destruct X as [|? X]; [discriminate L|]). destruct X; [reflexivity | discriminate L].
Qed.

Lemma rx_le_bytes_rt : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|x bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (rx_byte_range x) as Hx. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite (lor_shiftl8_add (bv_unsigned x) (bytes_le_to_Z bs) Hx Hr). f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    Z.div_mod_to_equations. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned x + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
    Z.div_mod_to_equations. lia.
Qed.

Lemma rx_lh_le2 : forall bs, length bs = 2%nat -> le2 (sext 64 (bv_extract 0 16 (le_bytes_to_word bs))) = bs.
Proof.
  intros bs L. unfold le2. rewrite sext_small, signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite !Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1. rewrite L in H1.
  change (8 * Z.of_nat 2) with 16 in H1.
  rewrite (bv_wrap_small 64 (bytes_le_to_Z bs)) by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  unfold bv_wrap at 1. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite (Z_to_le_bytes_mod 2 _ 64) by lia.
  rewrite <- (Z_to_le_bytes_mod 2 _ 16) by lia.
  replace (bv_swrap 16 (bytes_le_to_Z bs) mod 2 ^ 16) with (bytes_le_to_Z bs).
  - rewrite <- L at 1. apply rx_le_bytes_rt.
  - unfold bv_swrap, bv_wrap. change (bv_half_modulus 16) with (2^15). change (bv_modulus 16) with (2^16).
    Z.div_mod_to_equations. lia.
Qed.

Lemma rx_lh_put2 : forall bs, length bs = 2%nat -> put 2 (bv_signed (bv_extract 0 16 (le_bytes_to_word bs))) = bs.
Proof. intros bs L. rewrite <- le2_put. exact (rx_lh_le2 bs L). Qed.

(* ---- the heap frame and the RELRO tables, from the entry memory to a callee ---- *)

Lemma rx_tframe_move : forall m m' (sp sp' : word) K K' TF,
  tframe_at m sp K TF ->
  munch [(bv_unsigned sp - K, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  bv_unsigned sp - K <= bv_unsigned sp' - K' -> bv_unsigned sp' <= bv_unsigned sp ->
  tframe_at m' sp' K' TF.
Proof.
  intros m m' sp sp' K K' TF T MU H1 H2. destruct TF as [fr|]; [|exact I].
  unfold tframe_at in *. destruct T as (P & BA & OW & OWin). unfold off_world, off_window in *.
  refine (conj P (conj _ (conj OW _))); [| lia].
  eapply bytes_at_transport; [exact BA | exact MU |]. cbn [disjoint_from].
  refine (conj _ (conj _ I)); lia.
Qed.

Lemma rx_relro_move : forall m m' (sp : word) K, relro_img m ->
  munch [(bv_unsigned sp - K, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' ->
  W_BASE_UBSAN + W_LEN <= bv_unsigned sp - K -> relro_img m'.
Proof.
  intros m m' sp K R MU H i Hi. unfold mrd. rewrite (MU (wa (RELRO_BASE + i))); [exact (R i Hi) |].
  unfold RELRO_BASE, RELRO_LEN in *. cbn [outside]. rewrite wa_unsigned by lia.
  unfold W_BASE_UBSAN, W_LEN in *. refine (conj _ (conj _ I)); lia.
Qed.

(* ---- the world algebra the walk needs ---- *)

Lemma rx_len_upd : forall (B v : list byte) k, length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> length (upd B k v) = Z.to_nat W_LEN.
Proof. intros B v k L Hk H. rewrite length_upd; [exact L | exact Hk |]. rewrite L. unfold W_LEN in *. lia. Qed.

Lemma rx_gf_upd : forall B k v, length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= OFF_g_fail_next -> g_fail_next (upd B k v) = g_fail_next B.
Proof.
  intros B k v L Hk H. unfold g_fail_next. apply u_at_upd_out; [lia | unfold OFF_g_fail_next; lia | lia |].
  rewrite L. unfold OFF_g_fail_next, W_LEN in *. lia.
Qed.

Lemma rx_ign_eq : forall B, rx_ign B = upd B 19832 (put 8 (u_at B 19832 8 + 1)).
Proof. intros B. unfold rx_ign, set_S_stats_rx_ignored, S_stats_rx_ignored, u64. rewrite put_mod64 by lia. reflexivity. Qed.

Lemma rx_ign_len : forall B, length B = Z.to_nat W_LEN -> length (rx_ign B) = Z.to_nat W_LEN.
Proof. intros B L. rewrite rx_ign_eq. apply rx_len_upd; [exact L | lia | rewrite length_put; unfold W_LEN; lia]. Qed.

Lemma rx_ign_gf : forall B, length B = Z.to_nat W_LEN -> g_fail_next (rx_ign B) = g_fail_next B.
Proof.
  intros B L. rewrite rx_ign_eq. apply rx_gf_upd; [exact L | lia |]. rewrite length_put. unfold OFF_g_fail_next. lia.
Qed.

Definition rx_b2 (B : list byte) (now : Z) : list byte :=
  set_S_last_rx_us (set_S_stats_rx_frames B (u64 (S_stats_rx_frames B + 1))) now.

Lemma rx_b2_eq : forall B now,
  rx_b2 B now = upd (upd B 19800 (put 8 (u_at B 19800 8 + 1))) 1824 (put 8 now).
Proof.
  intros B now. unfold rx_b2, set_S_last_rx_us, set_S_stats_rx_frames, S_stats_rx_frames, u64.
  rewrite put_mod64 by lia. reflexivity.
Qed.

Lemma rx_b2_len : forall B now, length B = Z.to_nat W_LEN -> length (rx_b2 B now) = Z.to_nat W_LEN.
Proof.
  intros B now L. rewrite rx_b2_eq.
  apply rx_len_upd; [apply rx_len_upd; [exact L | lia | rewrite length_put; unfold W_LEN; lia] | lia |].
  rewrite length_put. unfold W_LEN. lia.
Qed.

Lemma rx_b2_gf : forall B now, length B = Z.to_nat W_LEN -> g_fail_next (rx_b2 B now) = g_fail_next B.
Proof.
  intros B now L. rewrite rx_b2_eq. rewrite rx_gf_upd.
  - apply rx_gf_upd; [exact L | lia |]. rewrite length_put. unfold OFF_g_fail_next. lia.
  - apply rx_len_upd; [exact L | lia |]. rewrite length_put. unfold W_LEN. lia.
  - lia.
  - rewrite length_put. unfold OFF_g_fail_next. lia.
Qed.

Lemma rx_b2_state : forall B now, length B = Z.to_nat W_LEN -> S_state (rx_b2 B now) = S_state B.
Proof.
  intros B now L. rewrite rx_b2_eq.
  assert (L1 : length (upd B 19800 (put 8 (u_at B 19800 8 + 1))) = Z.to_nat W_LEN)
    by (apply rx_len_upd; [exact L | lia | rewrite length_put; unfold W_LEN; lia]).
  unfold S_state, A_S_state, OFF_g_s.
  rewrite s32_at_upd_out by (rewrite ?length_put, ?L1; unfold W_LEN; lia).
  rewrite s32_at_upd_out by (rewrite ?length_put, ?L; unfold W_LEN; lia).
  reflexivity.
Qed.

(* the desk learned at :290-291 *)
Lemma rx_desk_len : forall B X, length B = Z.to_nat W_LEN -> length X = 6%nat ->
  length (set_S_desk_known (set_S_desk_mac B X) 1) = Z.to_nat W_LEN.
Proof.
  intros B X L LX. unfold set_S_desk_known, set_S_desk_mac, A_S_desk_known, A_S_desk_mac, OFF_g_s.
  apply rx_len_upd; [apply rx_len_upd; [exact L | lia | rewrite LX; unfold W_LEN; lia] | lia |].
  rewrite length_put. unfold W_LEN. lia.
Qed.

Lemma rx_desk_gf : forall B X, length B = Z.to_nat W_LEN -> length X = 6%nat ->
  g_fail_next (set_S_desk_known (set_S_desk_mac B X) 1) = g_fail_next B.
Proof.
  intros B X L LX. unfold set_S_desk_known, set_S_desk_mac, A_S_desk_known, A_S_desk_mac, OFF_g_s.
  rewrite rx_gf_upd.
  - apply rx_gf_upd; [exact L | lia |]. rewrite LX. unfold OFF_g_fail_next. lia.
  - apply rx_len_upd; [exact L | lia |]. rewrite LX. unfold W_LEN. lia.
  - lia.
  - rewrite length_put. unfold OFF_g_fail_next. lia.
Qed.

(* session_lost's two stores (:162-163) *)
Lemma rx_lost_len : forall B, length B = Z.to_nat W_LEN ->
  length (set_S_desk_counter_valid (set_S_inflight B 0) 0) = Z.to_nat W_LEN.
Proof.
  intros B L. unfold set_S_desk_counter_valid, set_S_inflight, A_S_desk_counter_valid, A_S_inflight, OFF_g_s.
  apply rx_len_upd; [apply rx_len_upd; [exact L | lia | rewrite length_put; unfold W_LEN; lia] | lia |].
  rewrite length_put. unfold W_LEN. lia.
Qed.

Lemma rx_lost_gf : forall B, length B = Z.to_nat W_LEN ->
  g_fail_next (set_S_desk_counter_valid (set_S_inflight B 0) 0) = g_fail_next B.
Proof.
  intros B L. unfold set_S_desk_counter_valid, set_S_inflight, A_S_desk_counter_valid, A_S_inflight, OFF_g_s.
  rewrite rx_gf_upd.
  - apply rx_gf_upd; [exact L | lia |]. rewrite length_put. unfold OFF_g_fail_next. lia.
  - apply rx_len_upd; [exact L | lia |]. rewrite length_put. unfold W_LEN. lia.
  - lia.
  - rewrite length_put. unfold OFF_g_fail_next. lia.
Qed.

Lemma rx_upd_app : forall (C v w : list byte) k k', 0 <= k -> k' = k + Z.of_nat (length v) ->
  k + Z.of_nat (length v) + Z.of_nat (length w) <= Z.of_nat (length C) ->
  upd (upd C k v) k' w = upd C k (v ++ w).
Proof.
  intros C v w k k' Hk -> Hl. rewrite !upd_upd_bytes.
  replace (Z.to_nat (k + Z.of_nat (length v))) with (length (firstn (Z.to_nat k) C ++ v))
    by (rewrite length_app, length_firstn; lia).
  unfold upd_bytes at 2.
  rewrite <- (firstn_skipn (length w) (skipn (Z.to_nat k + length v) C)).
  rewrite app_assoc.
  rewrite upd_bytes_mid by (rewrite length_firstn, length_skipn; lia).
  unfold upd_bytes. rewrite length_app, skipn_skipn, <- !app_assoc. do 3 f_equal. f_equal. lia.
Qed.

Lemma rx_upd3 : forall (C v0 v1 v2 : list byte) k0 k1 k2, length v0 = 2%nat -> length v1 = 2%nat ->
  length v2 = 2%nat -> 0 <= k0 -> k1 = k0 + 2 -> k2 = k0 + 4 -> k0 + 6 <= Z.of_nat (length C) ->
  upd (upd (upd C k0 v0) k1 v1) k2 v2 = upd C k0 (v0 ++ v1 ++ v2).
Proof.
  intros C v0 v1 v2 k0 k1 k2 L0 L1 L2 Hk -> -> HC.
  rewrite (rx_upd_app C v0 v1 k0 (k0 + 2)) by (rewrite ?L0, ?L1; lia).
  rewrite (rx_upd_app C (v0 ++ v1) v2 k0 (k0 + 4)) by (rewrite ?length_app, ?L0, ?L1, ?L2; lia).
  rewrite app_assoc. reflexivity.
Qed.

Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.
Ltac rx_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v; [cbv iota | ]
  end.
Ltac rx_neg := cbv beta iota delta [negb].
(* after a call: the callee's stk (its sp read back), mem_inv, world and g_fail_next under fixed names *)
Ltac rx_names Hsp ST MI WM GF :=
  try (lazymatch goal with H : stk _ _ _ (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite Hsp in H; rename H into ST end);
  try (lazymatch goal with H : mem_inv rsegs _ |- _ => rename H into MI end);
  try (lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN _ |- _ => rename H into WM end);
  try (lazymatch goal with H : g_fail_next _ <= 1 |- _ => rename H into GF end).
Ltac rx_dups := repeat match goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.

Theorem diginet_session_rx_holds :
  bcmp_contract -> diginet_frame_parse_contract -> diginet_mac_is_digidesign_contract ->
  on_announce_contract -> on_ack_contract -> on_data_contract -> set_state_contract ->
  diginet_session_tick_contract -> diginet_session_rx_contract.
Proof.
  intros BC PARSE MACD ONANN ONACK ONDATA SETST TICK.
  unfold on_announce_contract, on_announce_ENTRY, on_announce_FRAME in ONANN.
  unfold on_ack_contract, on_ack_ENTRY, on_ack_FRAME in ONACK.
  unfold on_data_contract, on_data_ENTRY, on_data_FRAME in ONDATA.
  unfold set_state_contract, set_state_ENTRY, set_state_FRAME in SETST.
  unfold diginet_session_tick_contract, diginet_session_tick_ENTRY, diginet_session_tick_FRAME in TICK.
  unfold diginet_session_rx_contract, diginet_session_rx_ENTRY, diginet_session_rx_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    bufp now r b B B' TF -> -> -> -> Hnow BUF ARG WM GF HM TFA RR S16 ST LO WOS MI.
  unfold w_off_stack in WOS.
  destruct ARG as (Hbuf0 & Hbuf1 & Hbufw & Hbufs). unfold off_world, off_window in Hbufw, Hbufs.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  pose proof (wm_len _ _ _ _ WM) as LB.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* the heap frame and the RELRO tables at a callee of the frame [sp - 112, sp) *)
  assert (TFR : forall (mm : word -> option byte) K,
    munch [(bv_unsigned sp - 2256, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mm -> 0 <= K <= 2144 ->
    tframe_at mm (Z_to_bv 64 (bv_unsigned sp + -112)) K TF).
  { intros mm K HMU HK. eapply rx_tframe_move; [exact TFA | exact HMU | rewrite Hsp; lia | rewrite Hsp; lia]. }
  assert (RRM : forall (mm : word -> option byte),
    munch [(bv_unsigned sp - 2256, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mm -> relro_img mm).
  { intros mm HMU. eapply rx_relro_move; [exact RR | exact HMU | lia]. }
  (* ---- the epilogue at 0x16ed8: reload ra, s0-s3, pop the frame, return a0 ---- *)
  assert (EPI : forall (ra' t0' t1' t2' c0 c1 a1' a2' a3' a4' a5' a6' a7' c2 c3 t3' t4' t5' t6' : word)
                       (mm : word -> option byte) (j3' : list byte) (cs : list cell) (B1 : list byte) (r1 : Z),
    rw_cells rsegs mm (bv_unsigned sp + -112) [CB 8 j3'] ->
    rw_cells rsegs mm (bv_unsigned sp + -104) cs -> cells_size cs = 64%nat ->
    rw_cells rsegs mm (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mm lo (bv_unsigned sp + -112) ->
    wmem rsegs mm B1 -> g_fail_next B1 <= 1 -> mem_inv rsegs mm ->
    munch [(bv_unsigned sp - 2256, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mm ->
    wmono rsegs m mm -> B1 = B' -> r1 = r ->
    evt rsegs QQ
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' c0 c1 (Z_to_bv 64 r1)
               a1' a2' a3' a4' a5' a6' a7' c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x16ed8) fc None mm (seg_rom rsegs))).
  { intros ra' t0' t1' t2' c0 c1 a1' a2' a3' a4' a5' a6' a7' c2 c3 t3' t4' t5' t6' mm j3' cs B1 r1
      H3 H2 H2s H1 STm WMm GFm MIm MUm WMom EB Er.
    subst B1 r1. clear BUF WM HM TFA RR ST MI TFR RRM.
    do 6 step.
    release_frame H3 STm (bv_unsigned sp + -104).
    eapply stk_release in H2; [ | exact STm | lia ]. clear STm. rewrite H2s in H2.
    replace (bv_unsigned sp + -104 + Z.of_nat 64) with (bv_unsigned sp + -40) in H2 by lia.
    release_frame H1 H2 (bv_unsigned sp).
    step.
    apply evt_done. unfold QQ. do 15 eexists. split; [reflexivity|].
    split; [exact MUm|]. split; [exact WMom|]. split; [exact MIm|]. split; [exact H2|].
    split; [exact WMm | exact GFm]. }
  (* ---- 0x16ecc: stats.rx_ignored++, then the epilogue ---- *)
  assert (IGN : forall (ra' t0' t1' t2' c0 c1 a1' a2' a3' a4' a5' a6' a7' c2 c3 t3' t4' t5' t6' : word)
                       (mm : word -> option byte) (j3' : list byte) (cs : list cell) (B1 : list byte) (r1 : Z),
    rw_cells rsegs mm (bv_unsigned sp + -112) [CB 8 j3'] ->
    rw_cells rsegs mm (bv_unsigned sp + -104) cs -> cells_size cs = 64%nat ->
    rw_cells rsegs mm (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mm lo (bv_unsigned sp + -112) ->
    wmem rsegs mm B1 -> g_fail_next B1 <= 1 -> mem_inv rsegs mm ->
    munch [(bv_unsigned sp - 2256, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mm ->
    wmono rsegs m mm ->
    rx_ign B1 = B' -> r1 = r -> c3 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 18152) ->
    evt rsegs QQ
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' c0 c1 (Z_to_bv 64 r1)
               a1' a2' a3' a4' a5' a6' a7' c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x16ecc) fc None mm (seg_rom rsegs))).
  { intros ra' t0' t1' t2' c0 c1 a1' a2' a3' a4' a5' a6' a7' c2 c3 t3' t4' t5' t6' mm j3' cs B1 r1
      H3 H2 H2s H1 STm WMm GFm MIm MUm WMom EB Er Ec3.
    subst c3. clear BUF WM HM TFA RR ST MI TFR RRM.
    pose proof (wm_len _ _ _ _ WMm) as LB1.
    (* ld a1, 32(s3); addi a1, a1, 1; sd a1, 32(s3) *)
    do 3 step.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
      replace X with (rx_ign B1) in H by (apply rx_ign_eq); rename H into WM2 end.
    eapply EPI; [exact H3 | exact H2 | exact H2s | exact H1 | exact STm | exact WM2 | | exact MIm | exact MUm
                | exact WMom | exact EB | exact Er].
    rewrite rx_ign_gf by exact LB1. exact GFm. }
  (* ---- 0x16fec: diginet_session_tick (s, now), then the epilogue ---- *)
  assert (TICKT : forall (ra' t0' t1' t2' c0 c1 a0' a1' a2' a3' a4' a5' a6' a7' c2 c3 t3' t4' t5' t6' : word)
                         (mm : word -> option byte) (j3' : list byte) (cs : list cell) (B3 : list byte),
    rw_cells rsegs mm (bv_unsigned sp + -112) [CB 8 j3'] ->
    rw_cells rsegs mm (bv_unsigned sp + -104) cs -> cells_size cs = 64%nat ->
    rw_cells rsegs mm (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mm lo (bv_unsigned sp + -112) ->
    wmem rsegs mm B3 -> g_fail_next B3 <= 1 -> mem_inv rsegs mm ->
    munch [(bv_unsigned sp - 2256, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mm ->
    wmono rsegs m mm ->
    diginet_session_tick_m timg_ubsan TF B3 now = Some (B', r) ->
    c0 = Z_to_bv 64 now -> c1 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    evt rsegs QQ
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' c0 c1 a0'
               a1' a2' a3' a4' a5' a6' a7' c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x16fec) fc None mm (seg_rom rsegs))).
  { intros ra' t0' t1' t2' c0 c1 a0' a1' a2' a3' a4' a5' a6' a7' c2 c3 t3' t4' t5' t6' mm j3' cs B3
      H3 H2 H2s H1 STm WMm GFm MIm MUm WMom HT Ec0 Ec1.
    subst c0 c1. clear BUF WM HM ST MI.
    (* mv a0, s1; mv a1, s0; jal diginet_session_tick *)
    do 3 step.
    let mm0 := cur_mem in
    eapply evt_cut;
      [ eapply TICK with (now := now) (B := B3) (B' := B') (r := r) (TF := TF) (lo := lo);
        [ reflexivity | reflexivity | exact Hnow | exact WMm | exact GFm | exact HT
        | apply TFR; [exact MUm | lia] | apply RRM; exact MUm
        | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STm | rewrite Hsp; lia
        | unfold w_off_stack; rewrite Hsp; lia | exact MIm ]
      | wk_post_call rsegs mm0 ].
    rx_names Hsp ST4 MI4 WM4 GF4.
    (* j 0x16ed8 *)
    step.
    eapply EPI; [exact H3 | exact H2 | exact H2s | exact H1 | exact ST4 | exact WM4 | exact GF4 | exact MI4
                | exact MUm | exact WMom | reflexivity | reflexivity]. }
  (* ---- 0x16f30: the source is the desk's (:293-317) ---- *)
  assert (ACC : forall (ra' t0' t1' t2' c0 c1 a0' a1' a2' a3' a4' a5' a6' a7' c2 c3 t3' t4' t5' t6' : word)
                       (mm : word -> option byte) (j3' fj : list byte) (B1 : list byte),
    fr_code b = 0 ->
    rw_cells rsegs mm (bv_unsigned sp + -112) [CB 8 j3'] ->
    rw_cells rsegs mm (bv_unsigned sp + -104) (parse_cells bufp b fj) ->
    rw_cells rsegs mm (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mm lo (bv_unsigned sp + -112) ->
    bytes_at rsegs mm bufp b ->
    wmem rsegs mm B1 -> g_fail_next B1 <= 1 -> mem_inv rsegs mm ->
    munch [(bv_unsigned sp - 2256, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mm ->
    wmono rsegs m mm ->
    rx_acc timg_ubsan TF B1 b now = Some (B', r) ->
    c0 = Z_to_bv 64 now -> c1 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    c3 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 18152) ->
    evt rsegs QQ
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' c0 c1 a0'
               a1' a2' a3' a4' a5' a6' a7' c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x16f30) fc None mm (seg_rom rsegs))).
  { intros ra' t0' t1' t2' c0 c1 a0' a1' a2' a3' a4' a5' a6' a7' c2 c3 t3' t4' t5' t6' mm j3' fj B1
      FC H3 H2 H1 STm BUFm WMm GFm MIm MUm WMom HA Ec0 Ec1 Ec3.
    subst c0 c1 c3. clear BUF WM HM ST MI.
    pose proof (wm_len _ _ _ _ WMm) as LB1.
    pose proof (rx_cmd_range b) as RC.
    unfold parse_cells in H2.
    (* lw a0, 112(s1): the state; li a1, 3; bne a0, a1 *)
    step. change (s32_at B1 1760) with (S_state B1).
    pose proof (s32_range B1 1760) as RS. change (s32_at B1 1760) with (S_state B1) in RS.
    step. step. rx_br (negb (S_state B1 =? 3)); [| rewrite rx_eqb_s by lia; reflexivity].
    unfold rx_acc in HA. change DIGINET_S_CLOSED with 3 in HA.
    destruct (Z.eqb_spec (S_state B1) 3) as [SC|SC]; rx_neg; cbv iota in HA.
    { (* CLOSED: li a0, 0; j 0x16ed8 *)
      injection HA as EB Er. do 2 step.
      eapply EPI; [exact H3 | exact H2 | reflexivity | exact H1 | exact STm | exact WMm | exact GFm | exact MIm
                  | exact MUm | exact WMom | exact EB | exact Er]. }
    fold (rx_b2 B1 now) in HA.
    destruct (rx_sw timg_ubsan TF (rx_b2 B1 now) b now) as [[B3 []]|] eqn:HSW; [| discriminate HA].
    (* ld a2, 0(s3); lbu a1, 38(sp); addi a2, a2, 1; sd a2, 0(s3) (stats.rx_frames++); li a2, 223;
       sd s0, 176(s1) (last_rx_us = now) *)
    do 6 step.
    lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
      replace X with (rx_b2 B1 now) in H by (apply rx_b2_eq); rename H into WM2 end.
    assert (GF2 : g_fail_next (rx_b2 B1 now) <= 1) by (rewrite rx_b2_gf by exact LB1; exact GFm).
    pose proof (rx_b2_len B1 now LB1) as LB2.
    pose proof (rx_b2_state B1 now LB1) as SB2.
    rewrite (rx_zxb (fr_cmd b) RC).
    let mm2 := cur_mem in
    assert (DF : forall K, 0 <= K <= 2144 ->
              dframe_at mm2 (Z_to_bv 64 (bv_unsigned sp + -112)) K (bv_unsigned sp + -104) bufp b fj).
    { intros K HK. unfold dframe_at, arg_blk, off_world, off_window. rewrite Hsp.
      refine (conj FC (conj BUFm (conj _ (conj H2 (conj _ _))))); try (repeat split; lia).
      all: Z.div_mod_to_equations; lia. }
    (* bge a2, a1: the command against 223 *)
    step. rx_br (negb (223 <? fr_cmd b)); [| rewrite rx_lts by lia; reflexivity].
    destruct (Z.ltb_spec 223 (fr_cmd b)) as [CH|CL]; rx_neg.
    - (* addi a2, a1, -224; li a3, 2; bgeu a2, a3 *)
      do 2 step. step. rx_br (negb (fr_cmd b + -224 <? 2)); [| rewrite rx_ltu by lia; reflexivity].
      destruct (Z.ltb_spec (fr_cmd b + -224) 2) as [CN|CN]; rx_neg.
      + (* ANNOUNCE / ANNOUNCE_SESSION: addi a1, sp, 8; mv a0, s1; mv a2, s0; jal on_announce *)
        rewrite rx_sw_ann in HSW by lia.
        do 4 step.
        let mm0 := cur_mem in
        eapply evt_cut;
          [ eapply ONANN with (fp := bv_unsigned sp + -104) (buf := bufp) (now := now) (b := b) (fj := fj)
                              (B := rx_b2 B1 now) (B' := B3) (TF := TF) (lo := lo);
            [ reflexivity | reflexivity | reflexivity | exact Hnow | apply DF; lia | exact WM2 | exact GF2
            | exact HSW | apply TFR; [exact MUm | lia] | apply RRM; exact MUm
            | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STm | rewrite Hsp; lia
            | unfold w_off_stack; rewrite Hsp; lia | exact MIm ]
          | wk_post_call rsegs mm0 ].
        rx_names Hsp ST4 MI4 WM4 GF4.
        step.
        eapply TICKT; [exact H3 | exact H2 | reflexivity | exact H1 | exact ST4 | exact WM4 | exact GF4
                      | exact MI4 | exact MUm | exact WMom | exact HA | reflexivity | reflexivity].
      + (* li a2, 227; bne a1, a2 *)
        step. step. rx_br (negb (fr_cmd b =? 227)); [| rewrite rx_eqb_s by lia; reflexivity].
        destruct (Z.eqb_spec (fr_cmd b) 227) as [CD|CD]; rx_neg.
        * (* DISCONNECT: addiw a0, a0, -1; li a1, 1; bltu a1, a0 *)
          rewrite rx_sw_disc in HSW by exact CD. rewrite SB2 in HSW.
          do 2 step. step. rx_br (negb ((S_state B1 =? 2) || (S_state B1 =? 1)));
            [| rewrite rx_state_ltu by lia; reflexivity].
          destruct ((S_state B1 =? 2) || (S_state B1 =? 1)) eqn:SL; rx_neg.
          -- (* session_lost, inlined: sw zero, 168(s1); sw zero, 212(s1); li a2, 7; mv a0, s1; li a1, 0;
                jal set_state *)
             unfold session_lost_m in HSW.
             do 2 step.
             lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
               replace X with (set_S_desk_counter_valid (set_S_inflight (rx_b2 B1 now) 0) 0) in H;
                 [rename H into WM5 |] end.
             2: { unfold set_S_desk_counter_valid, set_S_inflight, A_S_desk_counter_valid, A_S_inflight, OFF_g_s.
                  apply upd_upd_comm; rewrite ?length_put, ?length_upd, ?LB2; unfold W_LEN; lia. }
             assert (GF5 : g_fail_next (set_S_desk_counter_valid (set_S_inflight (rx_b2 B1 now) 0) 0) <= 1)
               by (rewrite rx_lost_gf by exact LB2; exact GF2).
             do 4 step.
             let mm0 := cur_mem in
             eapply evt_cut;
               [ eapply SETST with (st := 0) (why := 7)
                                   (B := set_S_desk_counter_valid (set_S_inflight (rx_b2 B1 now) 0) 0)
                                   (B' := B3) (TF := TF) (lo := lo);
                 [ reflexivity | reflexivity | reflexivity | lia | lia | exact WM5 | exact GF5
                 | exact HSW | apply TFR; [exact MUm | lia] | apply RRM; exact MUm
                 | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STm | rewrite Hsp; lia
                 | unfold w_off_stack; rewrite Hsp; lia | exact MIm ]
               | wk_post_call rsegs mm0 ].
             rx_names Hsp ST4 MI4 WM4 GF4.
             step.
             eapply TICKT; [exact H3 | exact H2 | reflexivity | exact H1 | exact ST4 | exact WM4 | exact GF4
                           | exact MI4 | exact MUm | exact WMom | exact HA | reflexivity | reflexivity].
          -- (* not ONLINE / WAKING: nothing *)
             injection HSW as EB3. rewrite <- EB3 in HA.
             eapply TICKT; [exact H3 | exact H2 | reflexivity | exact H1 | exact STm | exact WM2 | exact GF2
                           | exact MIm | exact MUm | exact WMom | exact HA | reflexivity | reflexivity].
        * (* another command: ld a0, 32(s3); addi a0, a0, 1; sd a0, 32(s3) (stats.rx_ignored++) *)
          rewrite rx_sw_ign in HSW by lia. injection HSW as EB3. rewrite <- EB3 in HA.
          do 3 step.
          lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
            replace X with (rx_ign (rx_b2 B1 now)) in H by (apply rx_ign_eq); rename H into WM3 end.
          eapply TICKT; [exact H3 | exact H2 | reflexivity | exact H1 | exact STm | exact WM3
                        | rewrite rx_ign_gf by exact LB2; exact GF2
                        | exact MIm | exact MUm | exact WMom | exact HA | reflexivity | reflexivity].
    - (* beqz a1: DATA *)
      step. rx_br (fr_cmd b =? 0); [| rewrite rx_eqb0 by lia; reflexivity].
      destruct (Z.eqb_spec (fr_cmd b) 0) as [C0|C0]; cbv iota.
      + (* addi a1, sp, 8; mv a0, s1; mv a2, s0; jal on_data *)
        rewrite rx_sw_data in HSW by exact C0.
        do 4 step.
        let mm0 := cur_mem in
        eapply evt_cut;
          [ eapply ONDATA with (fp := bv_unsigned sp + -104) (buf := bufp) (now := now) (b := b) (fj := fj)
                               (B := rx_b2 B1 now) (B' := B3) (TF := TF) (lo := lo);
            [ reflexivity | reflexivity | reflexivity | exact Hnow | apply DF; lia | exact WM2 | exact GF2
            | exact HSW | apply TFR; [exact MUm | lia] | apply RRM; exact MUm
            | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STm | rewrite Hsp; lia
            | unfold w_off_stack; rewrite Hsp; lia | exact MIm ]
          | wk_post_call rsegs mm0 ].
        rx_names Hsp ST4 MI4 WM4 GF4.
        step.
        eapply TICKT; [exact H3 | exact H2 | reflexivity | exact H1 | exact ST4 | exact WM4 | exact GF4
                      | exact MI4 | exact MUm | exact WMom | exact HA | reflexivity | reflexivity].
      + (* li a0, 160; bne a1, a0 *)
        step. step. rx_br (negb (fr_cmd b =? 160)); [| rewrite rx_eqb_s by lia; reflexivity].
        destruct (Z.eqb_spec (fr_cmd b) 160) as [CA|CA]; rx_neg.
        * (* ACK: addi a1, sp, 8; mv a0, s1; jal on_ack *)
          rewrite rx_sw_ack in HSW by exact CA.
          do 3 step.
          let mm0 := cur_mem in
          eapply evt_cut;
            [ eapply ONACK with (fp := bv_unsigned sp + -104) (buf := bufp) (b := b) (fj := fj)
                                (B := rx_b2 B1 now) (B' := B3) (TF := TF) (lo := lo);
              [ reflexivity | reflexivity | apply DF; lia | exact WM2 | exact GF2
              | exact HSW | apply TFR; [exact MUm | lia] | apply RRM; exact MUm
              | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STm | rewrite Hsp; lia
              | unfold w_off_stack; rewrite Hsp; lia | exact MIm ]
            | wk_post_call rsegs mm0 ].
          rx_names Hsp ST4 MI4 WM4 GF4.
          step.
          eapply TICKT; [exact H3 | exact H2 | reflexivity | exact H1 | exact ST4 | exact WM4 | exact GF4
                        | exact MI4 | exact MUm | exact WMom | exact HA | reflexivity | reflexivity].
        * (* another command: stats.rx_ignored++ *)
          rewrite rx_sw_ign in HSW by lia. injection HSW as EB3. rewrite <- EB3 in HA.
          do 3 step.
          lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
            replace X with (rx_ign (rx_b2 B1 now)) in H by (apply rx_ign_eq); rename H into WM3 end.
          eapply TICKT; [exact H3 | exact H2 | reflexivity | exact H1 | exact STm | exact WM3
                        | rewrite rx_ign_gf by exact LB2; exact GF2
                        | exact MIm | exact MUm | exact WMom | exact HA | reflexivity | reflexivity]. }
  (* ---- 0x16eac: a frame addressed to the host, from the desk or announcing it (:278-291) ---- *)
  assert (DK : forall (ra' t0' t1' t2' c0 c1 a0' a1' a2' a3' a4' a5' a6' a7' c2 c3 t3' t4' t5' t6' : word)
                      (mm : word -> option byte) (j3' fj : list byte),
    fr_code b = 0 ->
    rw_cells rsegs mm (bv_unsigned sp + -112) [CB 8 j3'] ->
    rw_cells rsegs mm (bv_unsigned sp + -104) (parse_cells bufp b fj) ->
    rw_cells rsegs mm (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mm lo (bv_unsigned sp + -112) ->
    bytes_at rsegs mm bufp b ->
    wmem rsegs mm B -> mem_inv rsegs mm ->
    munch [(bv_unsigned sp - 2256, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m mm ->
    wmono rsegs m mm ->
    rx_dk timg_ubsan TF B b now = Some (B', r) ->
    c0 = Z_to_bv 64 now -> c1 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    c2 = Z_to_bv 64 (bv_unsigned sp + -98) -> c3 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s + 18152) ->
    evt rsegs QQ
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' c0 c1 a0'
               a1' a2' a3' a4' a5' a6' a7' c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x16eac) fc None mm (seg_rom rsegs))).
  { intros ra' t0' t1' t2' c0 c1 a0' a1' a2' a3' a4' a5' a6' a7' c2 c3 t3' t4' t5' t6' mm j3' fj
      FC H3 H2 H1 STm BUFm WMm MIm MUm WMom HD Ec0 Ec1 Ec2 Ec3.
    subst c0 c1 c2 c3. clear BUF WM HM ST MI.
    pose proof (rx_cmd_range b) as RC.
    assert (LSRC : length (fr_src b) = 6%nat) by (apply rx_src_len; exact FC).
    assert (LDM : length (sub B 1768 6) = 6%nat) by (apply length_sub; lia).
    assert (HPS : cells_size (parse_cells bufp b fj) = 64%nat) by reflexivity.
    destruct (rx_pc_bytes _ _ _ _ _ H2 FC) as [BDST BSRC]. clear BDST.
    replace (bv_unsigned sp + -104 + 6) with (bv_unsigned sp + -98) in BSRC by lia.
    (* an unfolded copy of the struct for the kit's loads; H2 stays in the form the callees take *)
    pose proof H2 as H2u. unfold parse_cells in H2u.
    (* lw a0, 116(s1): desk_known; beqz a0 *)
    step. change (s32_at B 1764) with (S_desk_known B).
    pose proof (s32_range B 1764) as RK. change (s32_at B 1764) with (S_desk_known B) in RK.
    step. rx_br (S_desk_known B =? 0); [| rewrite rx_eqb0 by lia; reflexivity].
    unfold rx_dk in HD.
    destruct (Z.eqb_spec (S_desk_known B) 0) as [K0|K1]; cbv iota; rx_neg; cbv beta iota delta [negb] in HD.
    - (* the desk is not known: lbu a0, 38(sp); andi a0, a0, 254; li a1, 224; bne a0, a1 *)
      step. rewrite (rx_zxb (fr_cmd b) RC).
      do 2 step. step.
      destruct (rx_land254 (fr_cmd b) RC) as [RL EL].
      rx_br (negb ((fr_cmd b =? 224) || (fr_cmd b =? 225)));
        [| rewrite (unsigned_lit (fr_cmd b)) by lia; rewrite rx_eqb_s by lia; rewrite EL; reflexivity].
      destruct ((fr_cmd b =? 224) || (fr_cmd b =? 225)) eqn:CA; rx_neg; cbv beta iota delta [negb] in HD.
      + (* an announce: mv a0, s2; jal diginet_mac_is_digidesign *)
        do 2 step.
        eapply evt_cut;
          [ eapply MACD with (mac := bv_unsigned sp + -98) (l := fr_src b); [lia | exact LSRC | exact BSRC] | ].
        intros ms' (ax1 & ax2 & ->).
        rewrite (ret_pc_even 0x16f0c) by (first [lia | reflexivity]).
        (* beqz a0 *)
        step. rx_br (negb (oui_of (fr_src b))); [| destruct (oui_of (fr_src b)); reflexivity].
        destruct (oui_of (fr_src b)) eqn:OU; rx_neg; cbv beta iota delta [negb] in HD.
        * (* a Digidesign desk: lh a0, 0(s2); lh a1, 2(s2); lh a2, 4(s2); li a3, 1; sw a3, 116(s1);
             sh a0, 120(s1); sh a1, 122(s1); sh a2, 124(s1): the memcpy of :290 and desk_known = 1 *)
          assert (L1764 : length (upd B 1764 (put 4 1)) = Z.to_nat W_LEN)
            by (apply rx_len_upd; [exact LB | lia | rewrite length_put; unfold W_LEN; lia]).
          do 8 step.
          lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ ?X] |- _ =>
            replace X with (set_S_desk_known (set_S_desk_mac B (fr_src b)) 1) in H; [rename H into WMl |] end.
          2: { unfold set_S_desk_known, set_S_desk_mac, A_S_desk_known, A_S_desk_mac, OFF_g_s.
               rewrite !rx_lh_le2 by (rewrite length_firstn, length_skipn; lia).
               rewrite (rx_upd3 (upd B 1764 (put 4 1)) _ _ _ 1768 1770 1772)
                 by (rewrite ?length_firstn, ?length_skipn, ?L1764; unfold W_LEN; lia).
               rewrite (rx_src3 (fr_src b) LSRC).
               apply upd_upd_comm; rewrite ?length_put, ?LSRC, ?LB; unfold W_LEN; lia. }
          eapply ACC; [exact FC | exact H3 | exact H2 | exact H1 | exact STm | exact BUFm | exact WMl
                      | rewrite rx_desk_gf by first [exact LB | exact LSRC]; exact GF
                      | exact MIm | exact MUm | exact WMom | exact HD | reflexivity | reflexivity | reflexivity].
        * (* not a Digidesign source: stats.rx_ignored++ *)
          injection HD as EB Er.
          eapply IGN; [exact H3 | exact H2 | exact HPS | exact H1 | exact STm | exact WMm | exact GF | exact MIm
                      | exact MUm | exact WMom | exact EB | exact Er | reflexivity].
      + (* not an announce: li a0, 0; j 0x16ed8 *)
        injection HD as EB Er. do 2 step.
        eapply EPI; [exact H3 | exact H2 | exact HPS | exact H1 | exact STm | exact WMm | exact GF
                    | exact MIm | exact MUm | exact WMom | exact EB | exact Er].
    - (* the desk is known: addi a1, s1, 120; li a2, 6; mv a0, s2; jal bcmp: memcmp (f.src, s->desk_mac, 6) *)
      do 4 step.
      destruct (rx_cmp6 (fr_src b) (sub B 1768 6) LSRC LDM) as (v4 & Hv4 & E4 & R4).
      let mm0 := cur_mem in
      eapply evt_cut;
        [ eapply BC with (ls := fr_src b) (rs := sub B 1768 6) (v := v4);
          [ rewrite unsigned_lit by lia; exact BSRC
          | rewrite unsigned_lit by lia; apply (wm_src rsegs W_BASE_UBSAN mm0 B 1768 6); [exact WMm | lia | lia | lia]
          | rewrite unsigned_lit by lia; exact Hv4
          | exact MIm ]
        | wk_post_call rsegs mm0 ].
      rx_dups.
      lazymatch goal with H : mem_inv rsegs _ |- _ => rename H into MI4 end.
      (* beqz a0 *)
      step. rx_br (memeq 6 (fr_src b) (sub B 1768 6)); [| rewrite rx_eqb0 by lia; symmetry; exact E4].
      destruct (memeq 6 (fr_src b) (sub B 1768 6)) eqn:M4; cbv iota; cbv beta iota delta [negb] in HD.
      + eapply ACC; [exact FC | exact H3 | exact H2 | exact H1 | exact STm | exact BUFm | exact WMm | exact GF
                    | exact MI4 | exact MUm | exact WMom | exact HD | reflexivity | reflexivity | reflexivity].
      + (* another source: li a0, 0; stats.rx_ignored++ *)
        injection HD as EB Er. step.
        eapply IGN; [exact H3 | exact H2 | exact HPS | exact H1 | exact STm | exact WMm | exact GF | exact MI4
                    | exact MUm | exact WMom | exact EB | exact Er | reflexivity]. }
  (* ---- the walk from the entry ---- *)
  pose proof (munch_refl [(bv_unsigned sp - 2256, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  carve_frame 40%nat ST. rename FR into FR1. rename junk into j1.
  carve_frame 64%nat ST. rename FR into FR2. rename junk into j2.
  carve_frame 8%nat ST. rename FR into FR3. rename junk into j3.
  (* prologue: addi sp, sp, -112; sd ra, s0, s1, s2, s3; mv s1, a0; li a0, -1 *)
  do 8 step.
  (* beqz s1: s = &g_s is not NULL *)
  step. rx_br false; [| vm_compute; reflexivity].
  (* beqz a1: buf is not NULL *)
  step. rx_br false; [| unfold bv_eqb; rewrite !unsigned_lit by lia; symmetry; apply Z.eqb_neq; lia].
  (* mv s0, a3; mv a3, a2; lui a0, 4; addiw s3, a0, 1768; add s3, s1, s3 (= &s->stats); addi a2, sp, 8;
     mv a0, a1; mv a1, a3; jal diginet_frame_parse (buf, len, &f) *)
  do 9 step.
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply PARSE with (buf := bufp) (f := bv_unsigned sp + -104) (lo := lo) (b := b) (fj := j2);
      [ lia | lia | lia | Z.div_mod_to_equations; lia | exact BUF | exact FR2 | lia
      | rewrite Hsp; exact ST | rewrite Hsp; lia | rewrite Hsp; lia | rewrite Hsp; lia | exact MI ]
    | wk_post_call rsegs mm ].
  try clear FR2. try clear ST.
  lazymatch goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite Hsp in H; rename H into ST end.
  lazymatch goal with H : rw_cells _ _ _ (if _ then _ else _) |- _ => rename H into FR2 end.
  lazymatch goal with H : mem_inv rsegs _ |- _ => rename H into MI1 end.
  pose proof (fr_code_cases b) as FCC.
  rewrite rx_m_eq in HM.
  (* beqz a0: the parse's code *)
  step. rx_br (fr_code b =? 0); [| rewrite rx_eqb0 by lia; reflexivity].
  destruct (Z.eqb_spec (fr_code b) 0) as [FC0|FCn]; cbv iota in FR2 |- *.
  2: {
    (* the parse failed: andi s1, s1, 7; beqz s1 (the UBSan alignment check of s passes); stats.rx_ignored++ *)
    assert (E0 : (fr_code b =? DIGINET_OK) = false) by (apply Z.eqb_neq; exact FCn).
    rewrite E0 in HM. cbn [negb] in HM. injection HM as EB Er.
    step. step. rx_br true; [| vm_compute; reflexivity].
    eapply IGN; [exact FR3 | exact FR2 | reflexivity | exact FR1 | exact ST | exact WM | exact GF | exact MI1
                | exact MU | exact WMo | exact EB | exact Er | reflexivity]. }
  replace (fr_code b =? DIGINET_OK) with true in HM by (rewrite FC0; reflexivity). cbn [negb] in HM.
  assert (LSRC : length (fr_src b) = 6%nat) by (apply rx_src_len; exact FC0).
  assert (LDST : length (fr_dst b) = 6%nat) by (apply rx_dst_len; exact FC0).
  assert (LHM : length (sub B 1648 6) = 6%nat) by (apply length_sub; lia).
  assert (LBC : length BROADCAST = 6%nat) by reflexivity.
  assert (HPS : cells_size (parse_cells bufp b j2) = 64%nat) by reflexivity.
  destruct (rx_pc_bytes _ _ _ _ _ FR2 FC0) as [BDST BSRC].
  replace (bv_unsigned sp + -104 + 6) with (bv_unsigned sp + -98) in BSRC by lia.
  (* andi a0, s1, 7; bnez a0 (the UBSan alignment check of s passes) *)
  step. step. rx_br false; [| vm_compute; reflexivity].
  (* addi s2, sp, 14; li a2, 6; mv a0, s2; mv a1, s1; jal bcmp: memcmp (f.src, s->cfg.host_mac, 6) *)
  do 5 step.
  destruct (rx_cmp6 (fr_src b) (sub B 1648 6) LSRC LHM) as (v1 & Hv1 & E1 & R1).
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply BC with (ls := fr_src b) (rs := sub B 1648 6) (v := v1);
      [ rewrite unsigned_lit by lia; exact BSRC
      | rewrite unsigned_lit by lia; apply (wm_src rsegs W_BASE_UBSAN mm B 1648 6); [exact WM | lia | lia | lia]
      | rewrite unsigned_lit by lia; exact Hv1
      | exact MI1 ]
    | wk_post_call rsegs mm ].
  rx_dups. lazymatch goal with H : mem_inv rsegs _ |- _ => rename H into MI2 end.
  (* beqz a0 *)
  step. rx_br (memeq 6 (fr_src b) (sub B 1648 6)); [| rewrite rx_eqb0 by lia; symmetry; exact E1].
  destruct (memeq 6 (fr_src b) (sub B 1648 6)) eqn:M1; cbv iota; cbn [orb] in HM.
  { (* the source is the host's own MAC: li a0, 0; stats.rx_ignored++ *)
    injection HM as EB Er. step.
    eapply IGN; [exact FR3 | exact FR2 | exact HPS | exact FR1 | exact ST | exact WM | exact GF | exact MI2
                | exact MU | exact WMo | exact EB | exact Er | reflexivity]. }
  (* addi a0, sp, 8; li a2, 6; mv a1, s1; jal bcmp: memcmp (f.dst, s->cfg.host_mac, 6) *)
  do 4 step.
  destruct (rx_cmp6 (fr_dst b) (sub B 1648 6) LDST LHM) as (v2 & Hv2 & E2 & R2).
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply BC with (ls := fr_dst b) (rs := sub B 1648 6) (v := v2);
      [ rewrite unsigned_lit by lia; exact BDST
      | rewrite unsigned_lit by lia; apply (wm_src rsegs W_BASE_UBSAN mm B 1648 6); [exact WM | lia | lia | lia]
      | rewrite unsigned_lit by lia; exact Hv2
      | exact MI2 ]
    | wk_post_call rsegs mm ].
  rx_dups. lazymatch goal with H : mem_inv rsegs _ |- _ => rename H into MI3 end.
  (* beqz a0 *)
  step. rx_br (memeq 6 (fr_dst b) (sub B 1648 6)); [| rewrite rx_eqb0 by lia; symmetry; exact E2].
  destruct (memeq 6 (fr_dst b) (sub B 1648 6)) eqn:M2; cbv iota; cbn [orb andb negb] in HM.
  { (* addressed to the host *)
    eapply DK; [exact FC0 | exact FR3 | exact FR2 | exact FR1 | exact ST | exact BUF | exact WM | exact MI3
               | exact MU | exact WMo | exact HM | reflexivity | reflexivity | reflexivity | reflexivity]. }
  (* auipc a1; addi a0, sp, 8; addi a1, a1, 1546 (BROADCAST); li a2, 6; jal bcmp: memcmp (f.dst, BROADCAST, 6) *)
  do 5 step.
  destruct (rx_cmp6 (fr_dst b) BROADCAST LDST LBC) as (v3 & Hv3 & E3 & R3).
  let mm := cur_mem in
  eapply evt_cut;
    [ eapply BC with (ls := fr_dst b) (rs := BROADCAST) (v := v3);
      [ rewrite unsigned_lit by lia; exact BDST
      | rewrite unsigned_lit by lia; apply rx_bcast; exact MI3
      | rewrite unsigned_lit by lia; exact Hv3
      | exact MI3 ]
    | wk_post_call rsegs mm ].
  rx_dups. lazymatch goal with H : mem_inv rsegs _ |- _ => rename H into MI4 end.
  (* bnez a0 *)
  step. rx_br (negb (memeq 6 (fr_dst b) BROADCAST)); [| rewrite rx_eqb0 by lia; rewrite E3; reflexivity].
  destruct (memeq 6 (fr_dst b) BROADCAST) eqn:M3; rx_neg; cbn [orb andb negb] in HM.
  { (* broadcast *)
    eapply DK; [exact FC0 | exact FR3 | exact FR2 | exact FR1 | exact ST | exact BUF | exact WM | exact MI4
               | exact MU | exact WMo | exact HM | reflexivity | reflexivity | reflexivity | reflexivity]. }
  (* addressed to another host: li a0, 0; stats.rx_ignored++ *)
  injection HM as EB Er. step.
  eapply IGN; [exact FR3 | exact FR2 | exact HPS | exact FR1 | exact ST | exact WM | exact GF | exact MI4
              | exact MU | exact WMo | exact EB | exact Er | reflexivity].
Qed.
