(* Walk of on_data in the ubsan image: on_data_contract from send_control_contract,
   diginet_frame_is_keepalive_contract and notice_contract. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_frame_is_keepalive_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC
  send_control_c notice_c on_data_c.
Import ListNotations.
Open Scope Z_scope.

(* ==== 1. arithmetic and byte-list helpers ==== *)

Lemma od_put_mod_eq : forall n z1 z2,
  z1 mod 2 ^ (8 * Z.of_nat n) = z2 mod 2 ^ (8 * Z.of_nat n) -> put n z1 = put n z2.
Proof.
  intros n z1 z2 H. unfold put.
  rewrite <- (Z_to_le_bytes_mod n z1 (8 * Z.of_nat n)) by lia.
  rewrite <- (Z_to_le_bytes_mod n z2 (8 * Z.of_nat n)) by lia.
  rewrite H. reflexivity.
Qed.

Lemma od_swrap_mod : forall n z, bv_swrap n z mod bv_modulus n = z mod bv_modulus n.
Proof.
  intros n z. unfold bv_swrap, bv_wrap.
  rewrite Zminus_mod, Zmod_mod, <- Zminus_mod. f_equal. lia.
Qed.

Lemma od_swrap_mod32 : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof. intros z. change (2 ^ 32)%Z with (bv_modulus 32). apply od_swrap_mod. Qed.

Lemma od_swrap_mod16 : forall z, bv_swrap 16 z mod 2 ^ 16 = z mod 2 ^ 16.
Proof. intros z. change (2 ^ 16)%Z with (bv_modulus 16). apply od_swrap_mod. Qed.

Lemma od_swrap32_range : forall z, -2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof.
  intros z. pose proof (bv_swrap_in_range 32 z ltac:(first [lia | discriminate])) as H.
  change (bv_half_modulus 32) with (2 ^ 31)%Z in H. exact H.
Qed.

Lemma od_put4_swrap32 : forall x, put 4 (bv_swrap 32 x) = put 4 x.
Proof. intros x. apply od_put_mod_eq. change (8 * Z.of_nat 4)%Z with 32%Z. apply od_swrap_mod32. Qed.

Lemma od_swrap_mod_eq : forall n z1 z2,
  z1 mod bv_modulus n = z2 mod bv_modulus n -> bv_swrap n z1 = bv_swrap n z2.
Proof.
  intros n z1 z2 H. unfold bv_swrap, bv_wrap. f_equal.
  rewrite Zplus_mod, H, <- Zplus_mod. reflexivity.
Qed.

Lemma od_s32_of_mod : forall z, -2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 (z mod 2 ^ 32) = z.
Proof.
  intros z Hz. rewrite (od_swrap_mod_eq 32 (z mod 2 ^ 32) z).
  - apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31)%Z. lia.
  - change (bv_modulus 32) with (2 ^ 32)%Z. apply Z.mod_mod. lia.
Qed.

(* the side goals of od_u_at_cells *)
Ltac od_side := first [ (cbn [cells_wf cell_wf]; tauto) | reflexivity | (cbn [csize]; lia) | lia ].

Lemma od_eqb0 : forall v, -2 ^ 63 <= v < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Lemma od_eqb_swrap32 : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  pose proof (od_swrap32_range x) as Rx. pose proof (od_swrap32_range y) as Ry.
  destruct (Z.eqb_spec x y) as [->|N]; [rewrite !Z.eqb_refl; reflexivity|].
  apply Z.eqb_neq. intros E.
  assert (Exy : bv_swrap 32 x = bv_swrap 32 y).
  { assert (D : (bv_swrap 32 x - bv_swrap 32 y) mod 2 ^ 64 = 0)
      by (rewrite Zminus_mod, E, Z.sub_diag; apply Zmod_0_l).
    apply Z.mod_divide in D; [|lia]. destruct D as [c Ec]. nia. }
  apply N.
  assert (M : x mod 2 ^ 32 = y mod 2 ^ 32)
    by (rewrite <- (od_swrap_mod32 x), <- (od_swrap_mod32 y), Exy; reflexivity).
  rewrite !Z.mod_small in M by lia. exact M.
Qed.

Lemma od_sx32_lit : forall z, 0 <= z < 2 ^ 64 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 (bv_swrap 32 z).
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma od_sx16_lit : forall z, 0 <= z < 2 ^ 64 -> sx16 (Z_to_bv 64 z) = Z_to_bv 64 (bv_swrap 16 z).
Proof. intros z Hz. unfold sx16. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma od_zx16_lit : forall z, 0 <= z < 2 ^ 16 -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* reads of a piece of an append *)
Lemma od_sub_app_r : forall (u v : list byte) k k' n, k = Z.of_nat (length u) + k' -> 0 <= k' ->
  sub (u ++ v) k n = sub v k' n.
Proof.
  intros u v k k' n -> Hk. unfold sub. f_equal.
  replace (Z.to_nat (Z.of_nat (length u) + k')) with (length u + Z.to_nat k')%nat by lia.
  rewrite skipn_app, skipn_all2 by lia. cbn [app].
  replace (length u + Z.to_nat k' - length u)%nat with (Z.to_nat k') by lia. reflexivity.
Qed.

Lemma od_sub_app_l : forall (u v : list byte) k n, 0 <= k -> (Z.to_nat k + n <= length u)%nat ->
  sub (u ++ v) k n = sub u k n.
Proof.
  intros u v k n Hk Hn. unfold sub.
  rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length u - Z.to_nat k))%nat with 0%nat by lia. cbn [firstn].
  rewrite app_nil_r. reflexivity.
Qed.

(* a field of a cell list, by its cell and the offset inside it *)
Lemma od_u_at_cells : forall cs (k : Z) n c (kc : nat) (d : Z),
  cells_wf cs -> cell_at cs kc = Some c -> 0 <= d -> (Z.to_nat d + n <= csize c)%nat ->
  k = Z.of_nat kc + d -> u_at (cells_bytes cs) k n = u_at (cbytes c) d n.
Proof.
  intros cs k n c kc d Hwf Hc Hd Hn ->.
  destruct (cell_at_split cs kc c c Hc) as (pre & post & -> & Hsz & _).
  apply cells_wf_app in Hwf. destruct Hwf as [Hwp [Hwc Hwpost]].
  rewrite cells_bytes_app. cbn [cells_bytes].
  assert (Lp : length (cells_bytes pre) = kc) by (rewrite cells_bytes_length by assumption; exact Hsz).
  assert (Lc : length (cbytes c) = csize c) by (apply cbytes_length; assumption).
  unfold u_at.
  rewrite (od_sub_app_r (cells_bytes pre) (cbytes c ++ cells_bytes post) (Z.of_nat kc + d) d n) by lia.
  rewrite (od_sub_app_l (cbytes c) (cells_bytes post) d n) by lia.
  reflexivity.
Qed.

Lemma od_u_at_le8 : forall v, u_at (le8 (Z_to_bv 64 v)) 0 8 = v mod 2 ^ 64.
Proof.
  intros v. unfold u_at. rewrite sub_all by apply length_le8.
  rewrite <- (store_bytes_8 (Z_to_bv 64 v)). change (width_bytes 64) with 8%nat.
  rewrite bytes_le_to_Z_to_le_bytes by (apply bv_unsigned_in_range).
  rewrite unsigned_lit_wrap. change (8 * Z.of_nat 8)%Z with 64%Z. apply mod_mod_pow2. lia.
Qed.

Lemma od_u_at_le4 : forall v, u_at (le4 (Z_to_bv 64 v)) 0 4 = v mod 2 ^ 32.
Proof.
  intros v. unfold u_at. rewrite sub_all by apply length_le4.
  rewrite bytes_le_to_Z_le4, unsigned_lit_wrap. apply mod_mod_pow2. lia.
Qed.

Lemma od_u_at_le2 : forall v, u_at (le2 (Z_to_bv 64 v)) 0 2 = v mod 2 ^ 16.
Proof.
  intros v. unfold u_at. rewrite sub_all by apply length_le2.
  rewrite bytes_le_to_Z_le2, unsigned_lit_wrap. apply mod_mod_pow2. lia.
Qed.

(* bytes of a slice of a cell list in memory *)
Lemma od_cells_slice : forall m A cs1 cs2 cs3,
  rw_cells rsegs m A (cs1 ++ cs2 ++ cs3) ->
  bytes_at rsegs m (A + Z.of_nat (cells_size cs1)) (cells_bytes cs2).
Proof.
  intros m A cs1 cs2 cs3 [[Hwf Hb] _].
  apply cells_wf_app in Hwf. destruct Hwf as [Hw1 Hw23].
  apply cells_wf_app in Hw23. destruct Hw23 as [Hw2 Hw3].
  rewrite !cells_bytes_app in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb2].
  rewrite (cells_bytes_length _ Hw1) in Hb2.
  apply bytes_at_app in Hb2. destruct Hb2 as [Hb3 _]. exact Hb3.
Qed.

Lemma od_cells_cut : forall m A cs i j,
  rw_cells rsegs m A cs ->
  bytes_at rsegs m (A + Z.of_nat (cells_size (firstn i cs))) (cells_bytes (firstn j (skipn i cs))).
Proof.
  intros m A cs i j H.
  apply (od_cells_slice m A (firstn i cs) (firstn j (skipn i cs)) (skipn j (skipn i cs))).
  rewrite !firstn_skipn. exact H.
Qed.

Lemma od_bytes_slice : forall m a bs k n, bytes_at rsegs m a bs ->
  0 <= k -> (Z.to_nat k + n <= length bs)%nat ->
  bytes_at rsegs m (a + k) (firstn n (skipn (Z.to_nat k) bs)).
Proof.
  intros m a bs k n H Hk Hn.
  rewrite <- (firstn_skipn (Z.to_nat k) bs) in H. apply bytes_at_app in H. destruct H as [_ H2].
  rewrite length_firstn in H2.
  replace (Z.of_nat (Init.Nat.min (Z.to_nat k) (length bs))) with k in H2 by lia.
  rewrite <- (firstn_skipn n (skipn (Z.to_nat k) bs)) in H2.
  apply bytes_at_app in H2. destruct H2 as [H3 _]. exact H3.
Qed.

(* transport of the facts the kit does not know *)
Lemma od_relro_munch : forall W m m', relro_img m -> munch W m m' ->
  (forall x, RELRO_BASE <= x < RELRO_BASE + RELRO_LEN -> outside W x) -> relro_img m'.
Proof.
  intros W m m' HR HM HO i Hi.
  assert (E : m' (wa (RELRO_BASE + i)) = m (wa (RELRO_BASE + i))).
  { apply HM. rewrite wa_unsigned by (unfold RELRO_BASE, RELRO_LEN in *; lia).
    apply HO. unfold RELRO_LEN in *; lia. }
  unfold mrd in *. rewrite E. apply HR. exact Hi.
Qed.

Lemma od_tframe_munch : forall W m m' sp K sp' K' Fr,
  tframe_at m sp K Fr -> munch W m m' ->
  (forall fr, Fr = Some fr -> disjoint_from W (tf_addr fr) (Z.of_nat (length (tf_bytes fr)))) ->
  (forall fr, Fr = Some fr -> off_window sp' K' (tf_addr fr) (Z.of_nat (length (tf_bytes fr)))) ->
  tframe_at m' sp' K' Fr.
Proof.
  intros W m m' sp K sp' K' Fr HT HM HD HW. destruct Fr as [fr|]; [|exact I].
  destruct HT as (H0 & HB & HOW & _).
  split; [exact H0|]. split; [|split; [exact HOW | apply HW; reflexivity]].
  eapply bytes_at_transport; [exact HB | exact HM | apply HD; reflexivity].
Qed.

(* g_fail_next is untouched by a write that misses its byte *)
Lemma od_gfn_upd : forall Bw k v, 0 <= k ->
  (64969 <= k \/ k + Z.of_nat (length v) <= 64968) ->
  k + Z.of_nat (length v) <= Z.of_nat (length Bw) -> g_fail_next (upd Bw k v) = g_fail_next Bw.
Proof.
  intros Bw k v Hk Hd Hlen. unfold g_fail_next.
  apply u_at_upd_out;
    [ lia | unfold OFF_g_fail_next; lia | unfold OFF_g_fail_next; cbn [Z.of_nat]; lia | lia ].
Qed.

Lemma od_gfn_upd' : forall Bw k v, 0 <= k -> k + Z.of_nat (length v) <= 64968 ->
  Z.of_nat (length Bw) = 65616 -> g_fail_next (upd Bw k v) = g_fail_next Bw.
Proof. intros Bw k v Hk Hle HL. apply od_gfn_upd; [ lia | right; lia | lia ]. Qed.

Lemma od_len_upd : forall Bw k v, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length Bw) ->
  Z.of_nat (length (upd Bw k v)) = Z.of_nat (length Bw).
Proof. intros Bw k v Hk Hle. rewrite length_upd; [reflexivity | lia | lia]. Qed.

Lemma od_len_upd' : forall Bw k v, 0 <= k -> k + Z.of_nat (length v) <= 65616 ->
  Z.of_nat (length Bw) = 65616 -> Z.of_nat (length (upd Bw k v)) = 65616.
Proof. intros Bw k v Hk Hle HL. rewrite od_len_upd; [exact HL | lia | lia]. Qed.

(* the length and the g_fail_next bound of a world the session writes built from Bw *)
Ltac od_len65 HL := repeat (apply od_len_upd'; [lia | rewrite length_put; lia | ]); exact HL.
Ltac od_gf65 HG HL :=
  repeat (rewrite od_gfn_upd' by (first [ lia | (rewrite length_put; lia) | od_len65 HL ]));
  exact HG.

(* ==== 2. the model of on_data, split at the two merge points ==== *)

Definition od_acks (Bw : list byte) (r : Z) : list byte :=
  if r =? 0 then set_S_stats_tx_acks Bw (u64 (S_stats_tx_acks Bw + 1)) else Bw.

Definition od_data (Bw : list byte) : list byte :=
  set_S_stats_rx_data Bw (u64 (S_stats_rx_data Bw + 1)).

Definition od_retry (Bw bb : list byte) (nw : Z) : list byte :=
  if fr_retry bb =? 0 then Bw
  else let Bx := set_S_stats_rx_desk_retries Bw (u64 (S_stats_rx_desk_retries Bw + 1)) in
       set_S_backoff_until_us Bx (u64 (nw + ms_m (S_cfg_backoff_ms Bx))).

Definition od_mid (B1 b : list byte) (now r : Z) : list byte :=
  od_retry (od_data (od_acks B1 r)) b now.

Definition od_tail_store (TF : option tframe) (B2 b : list byte) : option (list byte * unit) :=
  let B := set_S_desk_counter B2 (fr_send b) in
  let B := set_S_desk_counter_valid B 1 in
  if fr_keepalive b then Some (B, tt)
  else
    let n := Ntc DIGINET_N_DATA (S_state B) 0 0 (fr_send b) (fr_retry b) 0 0 None
                 (fr_body b) (fr_body_len b) in
    call_notify timg_ubsan TF B n.

Definition od_tail_dup (TF : option tframe) (B2 b : list byte) : option (list byte * unit) :=
  if negb (S_desk_counter_valid B2 =? 0) && (fr_send b =? S_desk_counter B2) && negb (fr_retry b =? 0)
  then Some (set_S_stats_rx_duplicates B2 (u64 (S_stats_rx_duplicates B2 + 1)), tt)
  else od_tail_store TF B2 b.

Lemma od_m_split : forall TF B b now,
  on_data_m timg_ubsan TF B b now =
  match send_control_m timg_ubsan TF B DIGINET_CMD_ACK (fr_send b) with
  | None => None
  | Some (B1, (r, _)) => od_tail_dup TF (od_mid B1 b now r) b
  end.
Proof. intros. reflexivity. Qed.

(* the result of send_control is one of three small numbers *)
Lemma od_fbc_nil : forall mode, diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN mode = -1 \/
                                diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN mode = 60.
Proof.
  intros mode. unfold diginet_frame_build_code.
  destruct (negb ((mode =? 0) || (mode =? 1))); [left; reflexivity | right; vm_compute; reflexivity].
Qed.

Lemma od_io_send_r : forall I Bw frame B1 r,
  io_send_m I Bw frame = Some (B1, r) -> -2 ^ 63 <= r < 2 ^ 63.
Proof.
  intros I Bw frame B1 r H. unfold io_send_m in H. cbv zeta in H.
  repeat (lazymatch type of H with
          | match ?e with _ => _ end = _ => destruct e as [[? []]|]; [|discriminate H]
          end).
  injection H as _ Hr. subst r. destruct (truth (g_fail_next Bw)); unfold EIO; lia.
Qed.

Lemma od_send_raw_r : forall I F Bw frame B1 r,
  send_raw_m I F Bw frame = Some (B1, r) -> -2 ^ 63 <= r < 2 ^ 63.
Proof.
  intros I F Bw frame B1 r H. unfold send_raw_m in H.
  lazymatch type of H with
  | match ?e with _ => _ end = _ => destruct e as [[B2 r2]|] eqn:E; [|discriminate H]
  end.
  unfold call_send in E. destruct (S_io_send Bw =? ti_io_send I); [|discriminate E].
  apply od_io_send_r in E.
  destruct (r2 =? 0); injection H as _ Hr; subst r; exact E.
Qed.

Lemma od_sc_r : forall I F Bw cmd ack B' r f,
  send_control_m I F Bw cmd ack = Some (B', (r, f)) -> -2 ^ 63 <= r < 2 ^ 63.
Proof.
  intros I F Bw cmd ack B' r f H. unfold send_control_m in H. cbv zeta in H.
  set (n := diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN (S_cfg_sum_mode Bw)) in *.
  assert (Hn : n = -1 \/ n = 60) by apply od_fbc_nil. clearbody n.
  destruct (Z.ltb_spec n 0) as [Hlt|Hge]; cbv iota in H.
  - injection H as _ Hr _. subst r. destruct Hn; lia.
  - lazymatch type of H with
    | match ?e with _ => _ end = _ => destruct e as [[B1 r1]|] eqn:E; [|discriminate H]
    end.
    injection H as _ Hr _. subst r. eapply od_send_raw_r. exact E.
Qed.

(* notice of a DATA notice leaves g_fail_next alone *)
Lemma od_csd_id : forall F Bw n B1, check_state_data_m F Bw n = Some (B1, tt) -> B1 = Bw.
Proof.
  intros F Bw n B1 H. unfold check_state_data_m in H. cbv zeta in H.
  repeat (lazymatch type of H with
          | (if ?c then _ else _) = _ => destruct c; [discriminate H|]
          | match ?e with _ => _ end = _ => destruct e; [|discriminate H]
          end).
  injection H as HE. symmetry. exact HE.
Qed.

Lemma od_notice_gfn : forall I F Bw n Bw',
  notice_m I F Bw n = Some (Bw', tt) -> n_kind n = 3 -> Z.of_nat (length Bw) = 65616 ->
  g_fail_next Bw' = g_fail_next Bw.
Proof.
  intros I F Bw n Bw' H HK HL. unfold notice_m in H. cbv zeta in H. rewrite HK in H.
  change (3 =? N_STATE) with false in H. change (3 =? N_ACKED) with false in H.
  change (3 =? N_ACK_LOST) with false in H. change (3 =? N_DESK) with false in H.
  change (3 =? N_DATA) with true in H. cbv iota in H.
  destruct (check_state_data_m F Bw n) as [[B1 []]|] eqn:E1; [|discriminate H].
  apply od_csd_id in E1. subst B1.
  destruct (int_inc (GOT_ndata Bw)) as [d|]; [|discriminate H].
  injection H as HE. subst Bw'.
  unfold set_GOT_ndata. apply od_gfn_upd;
    [ unfold A_GOT_ndata, OFF_GOT; lia
    | left; unfold A_GOT_ndata, OFF_GOT; lia
    | rewrite length_put, HL; unfold A_GOT_ndata, OFF_GOT; lia ].
Qed.

(* ==== 3. the model's setters as world writes at literal offsets ==== *)

Lemma od_e_tx_acks : forall Bw x, set_S_stats_tx_acks Bw (u64 x) = upd Bw 19856 (put 8 x).
Proof. intros Bw x. unfold set_S_stats_tx_acks, u64. rewrite (put_mod64 8 x) by lia. reflexivity. Qed.

Lemma od_e_rx_data : forall Bw x, set_S_stats_rx_data Bw (u64 x) = upd Bw 19808 (put 8 x).
Proof. intros Bw x. unfold set_S_stats_rx_data, u64. rewrite (put_mod64 8 x) by lia. reflexivity. Qed.

Lemma od_e_rx_retr : forall Bw x, set_S_stats_rx_desk_retries Bw (u64 x) = upd Bw 19824 (put 8 x).
Proof.
  intros Bw x. unfold set_S_stats_rx_desk_retries, u64. rewrite (put_mod64 8 x) by lia. reflexivity.
Qed.

Lemma od_e_rx_dup : forall Bw x, set_S_stats_rx_duplicates Bw (u64 x) = upd Bw 19816 (put 8 x).
Proof.
  intros Bw x. unfold set_S_stats_rx_duplicates, u64. rewrite (put_mod64 8 x) by lia. reflexivity.
Qed.

Lemma od_e_backoff : forall Bw x now,
  set_S_backoff_until_us Bw (u64 (now + ms_m x)) = upd Bw 1840 (put 8 (x * 1000 + now)).
Proof.
  intros Bw x now. unfold set_S_backoff_until_us.
  replace (put 8 (u64 (now + ms_m x))) with (put 8 (x * 1000 + now)); [reflexivity|].
  apply od_put_mod_eq. change (8 * Z.of_nat 8)%Z with 64%Z.
  unfold ms_m, u64. rewrite Z.mod_mod by lia. rewrite Z.add_mod_idemp_r by lia.
  f_equal. lia.
Qed.

(* the model reads s->cfg.backoff_ms after the desk_retries write, the binary before it *)
Lemma od_backoff_ms_upd : forall Bw v, length v = 8%nat -> Z.of_nat (length Bw) = 65616 ->
  S_cfg_backoff_ms (upd Bw 19824 v) = S_cfg_backoff_ms Bw.
Proof.
  intros Bw v Hv HL. unfold S_cfg_backoff_ms.
  apply u_at_upd_out; unfold A_S_cfg_backoff_ms, OFF_g_s; [lia | lia | left; lia | rewrite Hv; lia].
Qed.

Lemma od_e_desk_counter : forall Bw x, set_S_desk_counter Bw x = upd Bw 1812 (put 4 x).
Proof. reflexivity. Qed.

Lemma od_e_dcv : forall Bw x, set_S_desk_counter_valid Bw x = upd Bw 1816 (put 4 x).
Proof. reflexivity. Qed.

(* ---- the three pieces of od_mid, in the form the binary's world has ---- *)

Lemma od_acks_T : forall Bw r, (r =? 0) = true ->
  upd Bw 19856 (put 8 (u_at Bw 19856 8 + 1)) = od_acks Bw r.
Proof.
  intros Bw r E. unfold od_acks. rewrite E. cbv iota.
  unfold set_S_stats_tx_acks, S_stats_tx_acks, u64.
  change A_S_stats_tx_acks with 19856.
  rewrite (put_mod64 8 (u_at Bw 19856 8 + 1)) by lia. reflexivity.
Qed.

Lemma od_acks_F : forall Bw r, (r =? 0) = false -> Bw = od_acks Bw r.
Proof. intros Bw r E. unfold od_acks. rewrite E. reflexivity. Qed.

Lemma od_data_M : forall Bw, upd Bw 19808 (put 8 (u_at Bw 19808 8 + 1)) = od_data Bw.
Proof.
  intros Bw. unfold od_data, set_S_stats_rx_data, S_stats_rx_data, u64.
  change A_S_stats_rx_data with 19808.
  rewrite (put_mod64 8 (u_at Bw 19808 8 + 1)) by lia. reflexivity.
Qed.

Lemma od_retry_T : forall Bw bb nw, (fr_retry bb =? 0) = true -> Bw = od_retry Bw bb nw.
Proof. intros Bw bb nw E. unfold od_retry. rewrite E. reflexivity. Qed.

Lemma od_retry_F : forall Bw bb nw, (fr_retry bb =? 0) = false -> Z.of_nat (length Bw) = 65616 ->
  upd (upd Bw 19824 (put 8 (u_at Bw 19824 8 + 1))) 1840 (put 8 (u_at Bw 1684 4 * 1000 + nw))
  = od_retry Bw bb nw.
Proof.
  intros Bw bb nw E HL. unfold od_retry. rewrite E. cbv iota zeta.
  unfold set_S_backoff_until_us, set_S_stats_rx_desk_retries, S_stats_rx_desk_retries,
         S_cfg_backoff_ms, ms_m, u64.
  change A_S_stats_rx_desk_retries with 19824.
  change A_S_backoff_until_us with 1840.
  change A_S_cfg_backoff_ms with 1684.
  rewrite (put_mod64 8 (u_at Bw 19824 8 + 1)) by lia.
  rewrite (u_at_upd_out Bw (put 8 (u_at Bw 19824 8 + 1)) 19824 1684 4)
    by (first [ lia | (rewrite length_put, HL; lia) ]).
  f_equal. apply od_put_mod_eq. change (8 * Z.of_nat 8)%Z with 64%Z.
  rewrite Z.mod_mod by lia. rewrite Z.add_mod_idemp_r by lia. f_equal. lia.
Qed.

Lemma od_ok_acks : forall Bw r, Z.of_nat (length Bw) = 65616 ->
  g_fail_next (od_acks Bw r) = g_fail_next Bw /\ Z.of_nat (length (od_acks Bw r)) = 65616.
Proof.
  intros Bw r HL. destruct (r =? 0) eqn:E.
  - rewrite <- (od_acks_T Bw r E). split.
    + apply od_gfn_upd'; [lia | rewrite length_put; lia | exact HL].
    + apply od_len_upd'; [lia | rewrite length_put; lia | exact HL].
  - rewrite <- (od_acks_F Bw r E). split; [reflexivity | exact HL].
Qed.

Lemma od_ok_data : forall Bw, Z.of_nat (length Bw) = 65616 ->
  g_fail_next (od_data Bw) = g_fail_next Bw /\ Z.of_nat (length (od_data Bw)) = 65616.
Proof.
  intros Bw HL. rewrite <- (od_data_M Bw). split.
  - apply od_gfn_upd'; [lia | rewrite length_put; lia | exact HL].
  - apply od_len_upd'; [lia | rewrite length_put; lia | exact HL].
Qed.

Lemma od_ok_retry : forall Bw bb nw, Z.of_nat (length Bw) = 65616 ->
  g_fail_next (od_retry Bw bb nw) = g_fail_next Bw /\
  Z.of_nat (length (od_retry Bw bb nw)) = 65616.
Proof.
  intros Bw bb nw HL. destruct (fr_retry bb =? 0) eqn:E.
  - rewrite <- (od_retry_T Bw bb nw E). split; [reflexivity | exact HL].
  - rewrite <- (od_retry_F Bw bb nw E HL).
    assert (L1 : Z.of_nat (length (upd Bw 19824 (put 8 (u_at Bw 19824 8 + 1)))) = 65616)
      by (apply od_len_upd'; [lia | rewrite length_put; lia | exact HL]).
    split.
    + rewrite od_gfn_upd' by (first [lia | (rewrite length_put; lia) | exact L1]).
      apply od_gfn_upd'; [lia | rewrite length_put; lia | exact HL].
    + apply od_len_upd'; [lia | rewrite length_put; lia | exact L1].
Qed.

(* ==== 4. the walk ==== *)

Definition od_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (lo : Z) (B' : list byte) :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 752, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m' /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    wmem rsegs m' B' /\ g_fail_next B' <= 1.

Section Walk.

Hypothesis SC : send_control_contract.
Hypothesis KA : diginet_frame_is_keepalive_contract.
Hypothesis NO : notice_contract.

Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variable lo : Z.
Variables fp buf now : Z.
Variables b fj : list byte.
Variable TF : option tframe.
Variable B' : list byte.

Hypothesis Hnow : 0 <= now < 2 ^ 64.
Hypothesis Hcode : fr_code b = 0.
Hypothesis BUF0 : bytes_at rsegs m0 buf b.
Hypothesis Hbuf0 : 0 < buf.
Hypothesis Hbuf1 : buf + Z.of_nat (length b) < 2 ^ 64.
Hypothesis Hbufw : buf + Z.of_nat (length b) <= W_BASE_UBSAN \/ W_BASE_UBSAN + W_LEN <= buf.
Hypothesis Hbufs : buf + Z.of_nat (length b) <= bv_unsigned sp - 752 \/ bv_unsigned sp <= buf.
Hypothesis DFC0 : rw_cells rsegs m0 fp (dframe_cells buf b fj).
Hypothesis Hfp0 : 0 < fp.
Hypothesis Hfp1 : fp + 64 < 2 ^ 64.
Hypothesis Hfpw : fp + 64 <= W_BASE_UBSAN \/ W_BASE_UBSAN + W_LEN <= fp.
Hypothesis Hfps : fp + 64 <= bv_unsigned sp - 752 \/ bv_unsigned sp <= fp.
Hypothesis Hfp8 : fp mod 8 = 0.
Hypothesis HTF0 : tframe_at m0 sp 752 TF.
Hypothesis HRO0 : relro_img m0.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis LO0 : 0 <= lo.
Hypothesis LOB : lo + 752 <= bv_unsigned sp.
Hypothesis WOS : W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 752.

Local Abbreviation QQ := (od_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B').

Ltac od_facts :=
  pose proof W_LEN_val as EWL;
  assert (EWB : W_BASE_UBSAN = 209664) by reflexivity;
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP;
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112)
    by (apply unsigned_lit; lia);
  pose proof (fr_code_ok b Hcode) as (L30 & _ & N16 & NLE);
  pose proof (fr_body_len_ok b Hcode) as (BL0 & PL0 & BSUM);
  pose proof (length_fr_body b Hcode) as LFB;
  pose proof (be32_range b 18) as RSEND; change (be32 b 18) with (fr_send b) in RSEND;
  pose proof (be16_range b 26) as RRETRY; change (be16 b 26) with (fr_retry b) in RRETRY;
  pose proof (at8_range b 28) as RCMD; change (at8 b 28) with (fr_cmd b) in RCMD;
  assert (RBL : 0 <= fr_body_len b < 2 ^ 16) by
    (pose proof (be16_range b 14); unfold fr_body_len, fr_numbytes in *; lia).

(* the world hypothesis for the current memory *)
Ltac od_wrw tac :=
  match goal with
  | H : rw_cells rsegs _ W_BASE_UBSAN [CB (Z.to_nat W_LEN) _] |- _ => tac H
  end.

(* carry the world hypothesis from the binary's form to the model's *)
Ltac od_world E := od_wrw ltac:(fun H => rewrite E in H).

Ltac od_epi :=
  match goal with
  | FRh : rw_cells rsegs _ (bv_unsigned sp + -112) _, STh : stk rsegs _ lo (bv_unsigned sp + -112) |- _ =>
      release_frame FRh STh (bv_unsigned sp)
  end.

(* 0x17424: the store path; the model is od_tail_store *)
Lemma od_walk_store : forall (m : word -> option byte) (B2 junk : list byte)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 72 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B2 -> g_fail_next B2 <= 1 ->
  od_tail_store TF B2 b = Some (B', tt) ->
  munch [(bv_unsigned sp - 752, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -112) ->
  evt rsegs QQ
    (MS (mkR (Z_to_bv 64 0x173a8) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2
             (Z_to_bv 64 fp) (Z_to_bv 64 211312) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 now) (Z_to_bv 64 229472) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17424) fc None m (seg_rom rsegs)).
Proof.
  intros m B2 junk t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 FR WM GF HM MU WMO MI ST.
  od_facts.
  pose proof (wm_len rsegs W_BASE_UBSAN m B2 WM) as LB2.
  pose proof KA as KA0.
  unfold diginet_frame_is_keepalive_contract, DIGINET_FRAME_IS_KEEPALIVE in KA0.
  pose proof NO as NO0. unfold notice_contract, notice_ENTRY, notice_FRAME in NO0.
  assert (DFC : rw_cells rsegs m fp (dframe_cells buf b fj)).
  { eapply rw_cells_transport; [ exact DFC0 | exact MU | exact WMO | ].
    change (cells_size (dframe_cells buf b fj)) with 64%nat. cbn [disjoint_from]. lia. }
  assert (BUF : bytes_at rsegs m buf b).
  { eapply bytes_at_transport; [ exact BUF0 | exact MU | cbn [disjoint_from]; lia ]. }
  unfold dframe_cells in DFC.
  unfold od_tail_store in HM. cbv zeta in HM.
  rewrite od_e_desk_counter, od_e_dcv in HM.
  (* lw a0,20(s0): f->h.send_counter *)
  step. rewrite od_sx32_lit by lia.
  (* li a1,1 *)
  step.
  (* sw a0,164(s1); sw a1,168(s1) *)
  step. step.
  od_wrw ltac:(fun H => rewrite od_put4_swrap32 in H).
  (* mv a0,s0; jal diginet_frame_is_keepalive *)
  step. step.
  eapply evt_cut.
  { eapply KA0 with (f := fp) (cmd := fr_cmd b) (body := buf + 30) (bb := fr_body b).
    - lia.
    - exact Hfp8.
    - lia.
    - lia.
    - pose proof (od_cells_cut m fp _ 9%nat 1%nat DFC) as HC.
      cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HC.
      change (Z.of_nat 30) with 30 in HC. exact HC.
    - pose proof (od_cells_cut m fp _ 11%nat 2%nat DFC) as HC.
      cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HC.
      change (Z.of_nat 32) with 32 in HC. rewrite app_nil_r in HC.
      replace (Z.of_nat (length (fr_body b))) with (fr_body_len b) by (rewrite LFB; lia).
      exact HC.
    - pose proof (od_bytes_slice m buf b 30 (Z.to_nat (fr_body_len b)) BUF ltac:(lia) ltac:(lia)) as HC.
      exact HC. }
  intros ms' (ka1 & ka2 & Eq). subst ms'.
  rewrite (ret_pc_even 0x1743c) by (first [lia | reflexivity]).
  replace (keepalive_of (fr_cmd b) (Z.of_nat (length (fr_body b))) (fr_body b))
     with (fr_keepalive b) by (unfold fr_keepalive; rewrite LFB; f_equal; f_equal; lia).
  (* bnez a0 *)
  step.
  destruct (fr_keepalive b) eqn:HKA; cbv iota in HM |- *.
  - (* keepalive: return *)
    if_true.
    injection HM as HB'. subst B'.
    do 5 step. od_epi. do 2 step.
    apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WMO|]. split; [exact MI|].
    match goal with STh : stk rsegs _ lo (bv_unsigned sp) |- _ => split; [exact STh|] end.
    od_wrw ltac:(fun H => split; [exact H|]).
    assert (L1 : Z.of_nat (length B2) = 65616) by (rewrite LB2; unfold W_LEN; lia).
    assert (L2 : Z.of_nat (length (upd B2 1812 (put 4 (fr_send b)))) = 65616)
      by (rewrite od_len_upd; [exact L1 | lia | rewrite length_put; lia]).
    rewrite (od_gfn_upd' _ 1816 (put 4 1)) by (first [lia | rewrite length_put; lia | exact L2]).
    rewrite (od_gfn_upd' _ 1812 (put 4 (fr_send b))) by (first [lia | rewrite length_put; lia | exact L1]).
    exact GF.
  - (* not a keepalive: build the DATA notice and call it through g_s.notify *)
    if_false.
    unfold call_notify in HM.
    lazymatch type of HM with
    | (if ?c then _ else _) = _ => destruct c eqn:SN; [|discriminate HM]
    end.
    apply Z.eqb_eq in SN.
    (* lw a1,112(s1): s->state *)
    step.
    (* ld a2,96(s1): s->notify, the address of notice *)
    step.
    lazymatch goal with
    | |- context [u_at ?BB 1744 8] => change (u_at BB 1744 8) with (S_notify BB)
    end.
    rewrite SN. change (ti_notice timg_ubsan) with 0x14bc8.
    (* ld a0,104(s1): s->notify_ctx; li a3,3 *)
    step. step.
    (* sw a3,0(sp); sw a1,4(sp); sd zero,8(sp); sd s0,16(sp) *)
    step. step. step. step.
    (* lw a1,20(s0); lh a3,28(s0); ld a4,32(s0); ld a5,40(s0) *)
    step. rewrite od_sx32_lit by lia.
    step. rewrite od_sx16_lit by lia.
    step. step.
    (* the ten remaining stores of the struct diginet_notice *)
    step. step. step. step. step. step. step. step.
    (* mv a1,sp *)
    step.
    (* the notice's own facts about this memory *)
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (HROn : relro_img mm) by
          (eapply od_relro_munch; [ exact HRO0 | exact MU |
           intros x Hx; cbn [outside]; unfold RELRO_BASE, RELRO_LEN in Hx; lia ]);
        assert (HTFn : tframe_at mm (Z_to_bv 64 (bv_unsigned sp + -112)) 48 TF) by
          (eapply od_tframe_munch; [ exact HTF0 | exact MU | |];
           intros fr Efr; unfold tframe_at in HTF0; rewrite Efr in HTF0; cbv iota in HTF0;
           destruct HTF0 as (_ & _ & HOW & HWD); unfold off_world, off_window in *;
           first [ (cbn [disjoint_from]; lia) | (rewrite Hsp; lia) ]);
        assert (BODY30 : bytes_at rsegs mm (buf + 30) (fr_body b)) by
          (match goal with
           | Hb : bytes_at rsegs mm buf b |- _ =>
               exact (od_bytes_slice mm buf b 30 (Z.to_nat (fr_body_len b)) Hb ltac:(lia) ltac:(lia))
           end)
    end.
    (* the struct diginet_notice at sp - 112 *)
    lazymatch goal with
    | FRh : rw_cells rsegs ?mm (bv_unsigned sp + -112) ?cs |- _ =>
        pose proof (od_cells_cut mm (bv_unsigned sp + -112) cs 0%nat 12%nat FRh) as NBAT
    end.
    cbn [firstn skipn cells_size csize Nat.add] in NBAT.
    change (Z.of_nat 0) with 0 in NBAT. rewrite Z.add_0_r in NBAT.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (NTC : ntc_at mm (bv_unsigned sp + -112)
        (Ntc DIGINET_N_DATA (S_state (upd (upd B2 1812 (put 4 (fr_send b))) 1816 (put 4 1))) 0 0
             (fr_send b) (fr_retry b) 0 0 None (fr_body b) (fr_body_len b))
        (Z_to_bv 64 (bv_unsigned sp + -112)) 48)
    end.
    { unfold ntc_at.
      split; [lia|]. split; [Z.div_mod_to_equations; lia|].
      split; [unfold off_world; lia|].
      split; [unfold off_window; rewrite Hsp; lia|].
      eexists. split; [exact NBAT|].
      split; [rewrite cells_bytes_length by (cbn [cells_wf cell_wf]; tauto); cbn [cells_size csize]; reflexivity|].
      split.
      { unfold s32_at. rewrite (od_u_at_cells _ 0 4 (C4 (Z_to_bv 64 3)) 0%nat 0) by od_side.
        cbn [cbytes n_kind]. rewrite od_u_at_le4. vm_compute; reflexivity. }
      split.
      { unfold s32_at.
        lazymatch goal with
        | |- bv_swrap 32 (u_at _ 4 4) = _ =>
            rewrite (od_u_at_cells _ 4 4 (C4 (Z_to_bv 64 (s32_at (upd (upd B2 1812 (put 4 (fr_send b))) 1816 (put 4 1)) 1760))) 4%nat 0) by od_side
        end.
        cbn [cbytes n_state]. rewrite od_u_at_le4. apply od_s32_of_mod. apply s32_range. }
      split.
      { unfold s32_at. rewrite (od_u_at_cells _ 8 4 (C8 (Z_to_bv 64 0)) 8%nat 0) by od_side.
        cbn [cbytes n_old]. vm_compute; reflexivity. }
      split.
      { unfold s32_at. rewrite (od_u_at_cells _ 12 4 (C8 (Z_to_bv 64 0)) 8%nat 4) by od_side.
        cbn [cbytes n_reason]. vm_compute; reflexivity. }
      split.
      { rewrite (od_u_at_cells _ 32 8 (C8 (Z_to_bv 64 0)) 32%nat 0) by od_side.
        cbn [cbytes n_pers]. vm_compute; reflexivity. }
      split.
      { unfold s32_at. rewrite (od_u_at_cells _ 40 4 (C8 (Z_to_bv 64 0)) 40%nat 0) by od_side.
        cbn [cbytes n_mac_offset]. vm_compute; reflexivity. }
      split.
      { rewrite (od_u_at_cells _ 56 8 (C8 (Z_to_bv 64 (fr_body_len b))) 56%nat 0) by od_side.
        cbn [cbytes n_body_len]. rewrite od_u_at_le8. apply Z.mod_small. lia. }
      split.
      { rewrite (od_u_at_cells _ 64 4 (C4 (Z_to_bv 64 (bv_swrap 32 (fr_send b)))) 64%nat 0) by od_side.
        cbn [cbytes n_counter]. rewrite od_u_at_le4, od_swrap_mod32. apply Z.mod_small. lia. }
      split.
      { rewrite (od_u_at_cells _ 68 2 (C2 (Z_to_bv 64 (bv_swrap 16 (fr_retry b)))) 68%nat 0) by od_side.
        cbn [cbytes n_retry]. rewrite od_u_at_le2, od_swrap_mod16. apply Z.mod_small. lia. }
      rewrite (od_u_at_cells _ 48 8 (C8 (Z_to_bv 64 (buf + 30))) 48%nat 0) by od_side.
      cbn [cbytes n_body n_ann]. rewrite od_u_at_le8, (Z.mod_small (buf + 30)) by lia.
      split; [exact BODY30|].
      split; [unfold off_world; rewrite LFB; lia|].
      split; [unfold off_window; rewrite Hsp, LFB; lia|].
      rewrite (od_u_at_cells _ 24 8 (C8 (Z_to_bv 64 0)) 24%nat 0) by od_side.
      cbn [cbytes]. vm_compute; reflexivity. }
    (* jalr a2: the call through the cell *)
    step.
    eapply evt_cut.
    { eapply NO0 with (p := bv_unsigned sp + -112) (lo := lo).
      - reflexivity.
      - exact NTC.
      - exact HTFn.
      - exact HROn.
      - od_wrw ltac:(fun H => exact H).
      - exact HM.
      - rewrite Hsp; Z.div_mod_to_equations; lia.
      - rewrite Hsp; match goal with STh : stk rsegs _ lo _ |- _ => exact STh end.
      - rewrite Hsp; lia.
      - unfold w_off_stack; rewrite Hsp; lia.
      - assumption. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mN &
                EqN & MUc & WMc & MIN & STN & WMN).
    subst ms'. rewrite Hsp in MUc, STN.
    rewrite (ret_pc_even 0x17498) by (first [lia | reflexivity]).
    lazymatch goal with
    | FRh : rw_cells rsegs ?mm (bv_unsigned sp + -112) _ |- _ =>
        match goal with
        | Hw : rw_cells rsegs mm W_BASE_UBSAN [CB (Z.to_nat W_LEN) _] |- _ => clear Hw
        end;
        transport_after_call rsegs mm mN MUc WMc
    end.
    clear MUc WMc.
    (* the epilogue *)
    do 5 step. od_epi. do 2 step.
    apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
    match goal with MUh : munch _ m0 mN |- _ => split; [exact MUh|] end.
    match goal with WMh : wmono rsegs m0 mN |- _ => split; [exact WMh|] end.
    split; [exact MIN|].
    match goal with STh : stk rsegs mN lo (bv_unsigned sp) |- _ => split; [exact STh|] end.
    split; [exact WMN|].
    assert (L1 : Z.of_nat (length B2) = 65616) by (rewrite LB2; unfold W_LEN; lia).
    assert (L2 : Z.of_nat (length (upd B2 1812 (put 4 (fr_send b)))) = 65616)
      by (rewrite od_len_upd; [exact L1 | lia | rewrite length_put; lia]).
    assert (L3 : Z.of_nat (length (upd (upd B2 1812 (put 4 (fr_send b))) 1816 (put 4 1))) = 65616)
      by (rewrite od_len_upd; [exact L2 | lia | rewrite length_put; lia]).
    rewrite (od_notice_gfn timg_ubsan TF _ _ B' HM ltac:(reflexivity) L3).
    rewrite (od_gfn_upd' _ 1816 (put 4 1)) by (first [lia | rewrite length_put; lia | exact L2]).
    rewrite (od_gfn_upd' _ 1812 (put 4 (fr_send b))) by (first [lia | rewrite length_put; lia | exact L1]).
    exact GF.
Qed.

(* 0x173fc: the duplicate test; the model is od_tail_dup *)
Lemma od_walk_dup : forall (m : word -> option byte) (B2 junk : list byte)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rw_cells rsegs m (bv_unsigned sp + -112) [CB 72 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B2 -> g_fail_next B2 <= 1 ->
  od_tail_dup TF B2 b = Some (B', tt) ->
  munch [(bv_unsigned sp - 752, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -112) ->
  evt rsegs QQ
    (MS (mkR (Z_to_bv 64 0x173a8) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2
             (Z_to_bv 64 fp) (Z_to_bv 64 211312) (Z_to_bv 64 (fr_retry b)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 now) (Z_to_bv 64 229472) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x173fc) fc None m (seg_rom rsegs)).
Proof.
  intros m B2 junk t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 FR WM GF HM MU WMO MI ST.
  od_facts.
  pose proof (wm_len rsegs W_BASE_UBSAN m B2 WM) as LB2.
  assert (DFC : rw_cells rsegs m fp (dframe_cells buf b fj)).
  { eapply rw_cells_transport; [ exact DFC0 | exact MU | exact WMO | ].
    change (cells_size (dframe_cells buf b fj)) with 64%nat. cbn [disjoint_from]. lia. }
  unfold dframe_cells in DFC.
  unfold od_tail_dup in HM.
  pose proof (s32_range B2 1816) as RV.
  change (s32_at B2 1816) with (S_desk_counter_valid B2) in RV.
  (* lw a1,168(s1): s->desk_counter_valid; beqz a1 *)
  step. change (s32_at B2 1816) with (S_desk_counter_valid B2).
  step. rewrite (od_eqb0 (S_desk_counter_valid B2)) by lia.
  destruct (S_desk_counter_valid B2 =? 0) eqn:V0; cbv iota.
  - try rewrite V0 in HM. cbn [negb andb] in HM.
    eapply od_walk_store; [exact FR|exact WM|exact GF|exact HM|exact MU|exact WMO|exact MI|exact ST].
  - try rewrite V0 in HM. cbn [negb andb] in HM.
    (* beqz a0: the retry field *)
    step. rewrite (od_eqb0 (fr_retry b)) by lia.
    destruct (fr_retry b =? 0) eqn:R0; cbv iota.
    + try rewrite R0 in HM. cbn [negb] in HM. rewrite andb_false_r in HM. cbv iota in HM.
      eapply od_walk_store; [exact FR|exact WM|exact GF|exact HM|exact MU|exact WMO|exact MI|exact ST].
    + try rewrite R0 in HM. cbn [negb] in HM. rewrite andb_true_r in HM.
      (* lw a0,164(s1); lw a1,20(s0); bne a1,a0 *)
      step. change (s32_at B2 1812) with (bv_swrap 32 (S_desk_counter B2)).
      step. rewrite od_sx32_lit by lia.
      step.
      rewrite (od_eqb_swrap32 (fr_send b) (S_desk_counter B2)) by
        (first [lia | (pose proof (u_at_range B2 1812 4) as HR;
                       change (8 * Z.of_nat 4)%Z with 32%Z in HR;
                       change (u_at B2 1812 4) with (S_desk_counter B2) in HR; lia)]).
      destruct (fr_send b =? S_desk_counter B2) eqn:C0; [ if_false | if_true ].
      * (* the duplicate *)
        try rewrite C0 in HM. cbv iota in HM.
        injection HM as HB'. subst B'. rewrite od_e_rx_dup.
        (* ld a0,8(s3); addi a0,a0,1; sd a0,8(s3); j 174b4 *)
        step. step. step. step.
        do 5 step. od_epi. do 2 step.
        apply evt_done. hnf. do 16 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WMO|]. split; [exact MI|].
        match goal with STh : stk rsegs _ lo (bv_unsigned sp) |- _ => split; [exact STh|] end.
        od_wrw ltac:(fun H => split; [exact H|]).
        assert (L1 : Z.of_nat (length B2) = 65616) by (rewrite LB2; unfold W_LEN; lia).
        od_gf65 GF L1.
      * try rewrite C0 in HM. cbv iota in HM.
        eapply od_walk_store; [exact FR|exact WM|exact GF|exact HM|exact MU|exact WMO|exact MI|exact ST].
Qed.

(* the common stretch 0x173c8 .. 0x173f8 *)
Ltac od_seg_rx := step; step; rewrite od_zx16_lit by lia; step; step.

Ltac od_seg_backoff :=
  step; step; step; step;
  lazymatch goal with
  | |- context [bv_unsigned (Z_to_bv 64 (u_at ?BB 1684 4))] =>
      rewrite (unsigned_lit (u_at BB 1684 4)) by
        (pose proof (u_at_range BB 1684 4) as HR;
         change (8 * Z.of_nat 4)%Z with 32%Z in HR; lia)
  end;
  step; step; step; step.

(* each of the four leaves of the mid stretch hands the world, in the model's form, to od_walk_dup *)
(* 0x17358: the whole function; m is the entry memory (m0 itself, from the contract), kept apart from the
   section's m0 so that the kit's transport never rewrites the section hypotheses *)
Lemma od_walk_main : forall (m : word -> option byte) (B : list byte)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rw_cells rsegs m fp (dframe_cells buf b fj) ->
  munch [(bv_unsigned sp - 752, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  wmono rsegs m0 m ->
  wmem rsegs m B -> g_fail_next B <= 1 ->
  on_data_m timg_ubsan TF B b now = Some (B', tt) ->
  stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
  evt rsegs QQ
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 211312) (Z_to_bv 64 fp) (Z_to_bv 64 now)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17358) fc None m (seg_rom rsegs)).
Proof.
  intros m B t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 DFC MU WMO WM GF HM ST MI.
  od_facts.
  pose proof (wm_len rsegs W_BASE_UBSAN m B WM) as LB.
  pose proof SC as SC0. unfold send_control_contract, send_control_ENTRY, send_control_FRAME in SC0.
  rewrite od_m_split in HM.
  destruct (send_control_m timg_ubsan TF B DIGINET_CMD_ACK (fr_send b)) as [[B1 [r f]]|] eqn:HSC;
    [|discriminate HM].
  pose proof (od_sc_r _ _ _ _ _ _ _ _ HSC) as RR.
  unfold dframe_cells in DFC.
  carve_frame 112%nat ST.
  (* addi sp,sp,-112; the five sd; mv s0,a1 *)
  do 7 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
  (* andi a1,a1,7: the alignment check of f *)
  step.
  lazymatch goal with |- context [Z.land (bv_unsigned (Z_to_bv 64 fp)) ?X] =>
    replace (Z.land (bv_unsigned (Z_to_bv 64 fp)) X) with 0
      by (rewrite unsigned_lit by lia; change X with (Z.ones 3);
          rewrite Z.land_ones by lia; symmetry; exact Hfp8)
  end.
  step. if_false.
  (* mv s2,a2; mv s1,a0; lw a2,20(s0) *)
  do 3 step. rewrite od_sx32_lit by lia.
  (* lui; addiw; add; li a1,160; mv a0,s1; li a3,0; li a4,0; jal send_control *)
  do 8 step.
  eapply evt_cut.
  { eapply SC0 with (lo := lo) (cmd := 160) (ack := fr_send b) (kp := 0) (klp := 0)
                    (K := []) (KL := []) (B := B) (B' := B1) (r := r) (f := f) (TF := TF).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - left; reflexivity.
    - exact WM.
    - exact GF.
    - exact HSC.
    - rewrite Hsp; Z.div_mod_to_equations; lia.
    - rewrite Hsp; exact ST.
    - rewrite Hsp; lia.
    - unfold w_off_stack; rewrite Hsp; lia.
    - exact MI. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 &
              Eq & MUc & WMc & MI1 & ST1 & WM1 & GF1 & _).
  subst ms'. rewrite Hsp in MUc, ST1.
  cbn [Z.eqb app] in MUc.
  clear WM. transport_after_call rsegs mA m1 MUc WMc. clear MUc WMc MI.
  clear SC0.
  rewrite (ret_pc_even 0x173a8) by (first [lia | reflexivity]).
  assert (LB1 : Z.of_nat (length B1) = 65616)
    by (rewrite (wm_len rsegs W_BASE_UBSAN m1 B1 WM1); unfold W_LEN; lia).
  (* andi a1,s1,7: zero by computation; beqz a0 on the result of send_control *)
  step. step.
  rewrite (od_eqb0 r) by lia.
  destruct (r =? 0) eqn:E0; cbv iota.
  - (* r = 0: the ack counter is bumped *)
    step. if_false.
    step. step. step.
    od_world (od_acks_T B1 r E0).
    od_seg_rx.
    od_world (od_data_M (od_acks B1 r)).
    step. rewrite (od_eqb0 (fr_retry b)) by lia.
    destruct (fr_retry b =? 0) eqn:R0; cbv iota.
    + od_world (od_retry_T (od_data (od_acks B1 r)) b now R0).
      eapply od_walk_dup;
        [ exact FR | od_wrw ltac:(fun H => exact H)
        | destruct (od_ok_acks B1 r LB1) as [GAx LAx];
          destruct (od_ok_data _ LAx) as [GDx LDx];
          destruct (od_ok_retry _ b now LDx) as [GRx _];
          rewrite GRx, GDx, GAx; exact GF1
        | exact HM | exact MU | exact WMO | exact MI1 | exact ST1 ].
    + od_seg_backoff.
      od_world (od_retry_F (od_data (od_acks B1 r)) b now R0
                  ltac:(destruct (od_ok_acks B1 r LB1) as [_ LAx];
                        destruct (od_ok_data _ LAx) as [_ LDx]; exact LDx)).
      eapply od_walk_dup;
        [ exact FR | od_wrw ltac:(fun H => exact H)
        | destruct (od_ok_acks B1 r LB1) as [GAx LAx];
          destruct (od_ok_data _ LAx) as [GDx LDx];
          destruct (od_ok_retry _ b now LDx) as [GRx _];
          rewrite GRx, GDx, GAx; exact GF1
        | exact HM | exact MU | exact WMO | exact MI1 | exact ST1 ].
  - (* r <> 0: no ack counter *)
    step. if_true.
    od_world (od_acks_F B1 r E0).
    od_seg_rx.
    od_world (od_data_M (od_acks B1 r)).
    step. rewrite (od_eqb0 (fr_retry b)) by lia.
    destruct (fr_retry b =? 0) eqn:R0; cbv iota.
    + od_world (od_retry_T (od_data (od_acks B1 r)) b now R0).
      eapply od_walk_dup;
        [ exact FR | od_wrw ltac:(fun H => exact H)
        | destruct (od_ok_acks B1 r LB1) as [GAx LAx];
          destruct (od_ok_data _ LAx) as [GDx LDx];
          destruct (od_ok_retry _ b now LDx) as [GRx _];
          rewrite GRx, GDx, GAx; exact GF1
        | exact HM | exact MU | exact WMO | exact MI1 | exact ST1 ].
    + od_seg_backoff.
      od_world (od_retry_F (od_data (od_acks B1 r)) b now R0
                  ltac:(destruct (od_ok_acks B1 r LB1) as [_ LAx];
                        destruct (od_ok_data _ LAx) as [_ LDx]; exact LDx)).
      eapply od_walk_dup;
        [ exact FR | od_wrw ltac:(fun H => exact H)
        | destruct (od_ok_acks B1 r LB1) as [GAx LAx];
          destruct (od_ok_data _ LAx) as [GDx LDx];
          destruct (od_ok_retry _ b now LDx) as [GRx _];
          rewrite GRx, GDx, GAx; exact GF1
        | exact HM | exact MU | exact WMO | exact MI1 | exact ST1 ].
Qed.

End Walk.

Theorem on_data_holds :
  send_control_contract -> diginet_frame_is_keepalive_contract -> notice_contract -> on_data_contract.
Proof.
  intros SC KA NO.
  unfold on_data_contract, on_data_ENTRY, on_data_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo fp buf now b fj B B' TF A0 A1 A2 Hnow DF WM GF HM HTF HRO SP16 ST LOB WOS MI.
  subst a0 a1 a2.
  destruct DF as (Hcode & BUF0 & (Hbuf0 & Hbuf1 & Hbufw & Hbufs) & DFC0 & (Hfp0 & Hfp1 & Hfpw & Hfps) & Hfp8).
  unfold off_world, off_window, w_off_stack in *.
  pose proof ST as (LO0 & _ & _).
  change (W_BASE_UBSAN + OFF_g_s) with 211312.
  eapply od_walk_main.
  all: first [ exact SC | exact KA | exact NO | exact DFC0 | exact WM | exact HM | exact ST | exact MI
             | apply munch_refl | apply wmono_refl | eassumption ].
Qed.

Print Assumptions on_data_holds.
