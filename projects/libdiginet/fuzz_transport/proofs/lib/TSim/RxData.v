(* A data frame (command 0x00) from the known desk. The model (m_rx's DATA arm, FT:344-365) counts the ACK it
   expects (OW.acks + 1), clears M.fail, moves M.backoff_until on a retry, stops on a duplicate, takes the counter,
   stops on a keepalive, and else records the frame in OW.dn[OW.ndata] (FT:358-363) and counts it (OW.ndata + 1).
   The library (on_data, DS:239-261) sends the ACK (send_control, io_send FT:823: GOT.acks + 1, g_fail_next = 0),
   counts, moves backoff_until_us on a retry, and makes the same three-way choice; the N_DATA notice it sends on a
   data frame passes check_state_data (FT:559-569) against OW.dn[GOT.ndata] (GOT.ndata + 1). Before the frame
   OW.acks = GOT.acks and OW.ndata = GOT.ndata, each 0 or 1 (ow_room: the reception may be the second of its
   operation). The desk is known: an unknown desk sends only announces (rx_accepts' ra_unknown), so learn_M
   changes nothing. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SimLib QueueFacts RxDefs RxBase
  RxList RxFrame RxW RxCore SendOk.
Import ListNotations.
Open Scope Z_scope.

(* the world functions stay folded for the unifier (RxW.v header); the getters unfold to them *)
Local Opaque sub upd u_at s32_at put.

Local Notation "'let*' p ':=' c1 'in' c2" := (match c1 with Some p => c2 | None => None end)
  (at level 200, p pattern, c1 at level 200, c2 at level 200).

Definition cond_data (B buf : list byte) : Prop := fr_cmd buf = DIGINET_CMD_DATA.

(* ---- closed facts ---- *)

(* x + 1 of a count that is 0 or 1: far from INT_MAX *)
Lemma rxdata_inc : forall x, 0 <= x <= 1 -> int_inc x = Some (x + 1).
Proof.
  intros x Hx. unfold int_inc. destruct (Z.eqb_spec x INT_MAX) as [E|E]; [unfold INT_MAX in E; lia | reflexivity].
Qed.
Lemma rxdata_lt60 : (DIGINET_MIN_FRAME_LEN <? 0) = false.
Proof. reflexivity. Qed.
Lemma rxdata_eio : (- EIO =? 0) = false.
Proof. reflexivity. Qed.
Lemma rxdata_c_e0 : (SPEC_CMD_DATA =? SPEC_CMD_E0) = false.
Proof. reflexivity. Qed.
Lemma rxdata_c_e1 : (SPEC_CMD_DATA =? SPEC_CMD_E1) = false.
Proof. reflexivity. Qed.
Lemma rxdata_c_ack : (SPEC_CMD_DATA =? SPEC_CMD_ACK) = false.
Proof. reflexivity. Qed.
Lemma rxdata_c_data : (SPEC_CMD_DATA =? SPEC_CMD_DATA) = true.
Proof. reflexivity. Qed.

(* a read through a chain of writes (RxW's wget without its closing step) *)
Ltac rxd_rd := wunf_get; wunf_set; repeat wr1.

(* a read at index k = 0 or 1 (Hk : k = 0 \/ k = 1) across the frame H: fget decides the ranges on numerals *)
Ltac rxd_k Hk H := let Ek := fresh "Ek" in destruct Hk as [Ek|Ek]; rewrite Ek; fget H.

(* ---- the ranges each part writes ---- *)

(* the model: OW.acks, M.fail, M.backoff_until (FT:348-351); the counter (FT:354-355), OW.dn[OW.ndata]
   (FT:358-363: OW.dn[0] or OW.dn[1], so both entries, 2 * 24 bytes), OW.ndata (FT:364) *)
Definition rxdata_R_m4 : list (Z * Z) := [(A_OW_acks, 4); (A_M_fail, 4); (A_M_backoff_until, 8)].
Definition rxdata_R_mt : list (Z * Z) :=
  [(A_M_desk_counter, 4); (A_M_desk_counter_valid, 4); (A_OW_dn_body 0, 48); (A_OW_ndata, 4)].
(* the library: the ACK (io_send FT:829, :834; send_raw DS:91-92; DS:242-243), the stats and backoff
   (DS:244-247), the duplicate, the counter, the notice (DS:249-260, notice FT:965) *)
Definition rxdata_R_ack : list (Z * Z) :=
  [(OFF_g_fail_next, 4); (A_GOT_acks, 4); (A_S_stats_tx_frames, 8); (A_S_stats_tx_acks, 8)].
Definition rxdata_R_w4 : list (Z * Z) :=
  [(A_S_stats_rx_data, 8); (A_S_stats_rx_desk_retries, 8); (A_S_backoff_until_us, 8)].
Definition rxdata_R_lt : list (Z * Z) :=
  [(A_S_stats_rx_duplicates, 8); (A_S_desk_counter, 4); (A_S_desk_counter_valid, 4); (A_GOT_ndata, 4)].
Definition rxdata_R_lib : list (Z * Z) := rxdata_R_ack ++ (rxdata_R_w4 ++ rxdata_R_lt).
(* the whole reception: m_rx (last_rx, then its DATA arm), the library's prologue (R_start), its DATA arm *)
Definition rxdata_RS : list (Z * Z) :=
  (([(A_M_last_rx, 8)] ++ (rxdata_R_m4 ++ rxdata_R_mt)) ++ R_start) ++ rxdata_R_lib.

(* ---- the pieces of the two DATA arms ---- *)

(* the model's B4 (FT:348-352): OW.acks = ak, M.fail = 0, then the backoff on a retry *)
Definition rxdata_mB4 (B2 : list byte) (retry ak : Z) : list byte :=
  let B3 := set_M_fail (set_OW_acks B2 ak) 0 in
  if truth retry then set_M_backoff_until B3 (u64 (g_now B3 + h_ms_m (Cfg_backoff_ms B3))) else B3.

(* the model's arm from B4 on (FT:353-364), m_rx_sw's text *)
Definition rxdata_mtail (fr : tframe) (n : Z) (B4 : list byte) : option (list byte * unit) :=
  let bytes := tf_bytes fr in
  let f := spec_read_frame (zs bytes) n in
  let bodyp := tf_addr fr + sf_body f in
  let body := skipn (Z.to_nat (sf_body f)) bytes in
  let blen := sf_body_len f in
  let retry := sf_retry f in
  let send := sf_send f in
  if truth (M_desk_counter_valid B4) && (send =? M_desk_counter B4) && truth retry then Some (B4, tt)
  else
  let B5 := set_M_desk_counter_valid (set_M_desk_counter B4 send) 1 in
  if (blen =? 1) && (at8 body 0 =? 0) then Some (B5, tt)
  else
  let nd := OW_ndata B5 in
  let* B6 :=
    if nd <? 2 then
      if nd <? 0 then None
      else Some (set_OW_dn_retry (set_OW_dn_counter (set_OW_dn_len (set_OW_dn_body B5 nd bodyp)
                    nd blen) nd send) nd retry)
    else Some B5 in
  let* nd1 := int_inc nd in
  Some (set_OW_ndata B6 nd1, tt).

(* the model's duplicate test (FT:353), over the world before its arm *)
Definition rxdata_dupM (X buf : list byte) : bool :=
  truth (M_desk_counter_valid X) && (fr_send buf =? M_desk_counter X) && truth (fr_retry buf).

(* the library's world after the ACK's tx_acks (DS:242-243) *)
Definition rxdata_W2 (W1 : list byte) (r : Z) : list byte :=
  if r =? 0 then set_S_stats_tx_acks W1 (u64 (S_stats_tx_acks W1 + 1)) else W1.

(* the library's world after rx_data and the retry (DS:244-247), on_data_m's text *)
Definition rxdata_W4 (W2 buf : list byte) (now : Z) : list byte :=
  let B := set_S_stats_rx_data W2 (u64 (S_stats_rx_data W2 + 1)) in
  if fr_retry buf =? 0 then B
  else let B := set_S_stats_rx_desk_retries B (u64 (S_stats_rx_desk_retries B + 1)) in
       set_S_backoff_until_us B (u64 (now + ms_m (S_cfg_backoff_ms B))).

(* the library's duplicate test (DS:249) *)
Definition rxdata_dupL (B buf : list byte) : bool :=
  negb (S_desk_counter_valid B =? 0) && (fr_send buf =? S_desk_counter B) && negb (fr_retry buf =? 0).

(* the library's arm from the duplicate test on (DS:249-260) *)
Definition rxdata_ltail (I : timg) (F : option tframe) (B buf : list byte) : option (list byte * unit) :=
  if rxdata_dupL B buf then Some (set_S_stats_rx_duplicates B (u64 (S_stats_rx_duplicates B + 1)), tt)
  else
    let B5 := set_S_desk_counter_valid (set_S_desk_counter B (fr_send buf)) 1 in
    if fr_keepalive buf then Some (B5, tt)
    else call_notify I F B5 (Ntc DIGINET_N_DATA (S_state B5) 0 0 (fr_send buf) (fr_retry buf) 0 0 None
                               (fr_body buf) (fr_body_len buf)).

(* ---- equations ---- *)

Lemma rxdata_m_eq : forall I fr n X, sf_cmd (spec_read_frame (zs (tf_bytes fr)) n) = SPEC_CMD_DATA ->
  m_rx_sw I fr n X =
  match int_inc (OW_acks X) with
  | None => None
  | Some ak => rxdata_mtail fr n (rxdata_mB4 X (sf_retry (spec_read_frame (zs (tf_bytes fr)) n)) ak)
  end.
Proof.
  intros I fr n X Hc. unfold m_rx_sw. cbv zeta. rewrite Hc.
  rewrite rxdata_c_e0, rxdata_c_e1, rxdata_c_ack, rxdata_c_data. cbv beta iota delta [orb].
  unfold rxdata_mtail, rxdata_mB4. cbv beta zeta. reflexivity.
Qed.

Lemma rxdata_on_data : forall I F W buf now W1 r f,
  send_control_m I F W DIGINET_CMD_ACK (fr_send buf) = Some (W1, (r, f)) ->
  on_data_m I F W buf now = rxdata_ltail I F (rxdata_W4 (rxdata_W2 W1 r) buf now) buf.
Proof.
  intros I F W buf now W1 r f H. unfold on_data_m. rewrite H.
  unfold rxdata_ltail, rxdata_dupL, rxdata_W4, rxdata_W2. cbv beta iota zeta. reflexivity.
Qed.

Lemma rxdata_notice : forall I F B st c r body blen,
  notice_m I F B (Ntc DIGINET_N_DATA st 0 0 c r 0 0 None body blen) =
  let* (B1, _) := check_state_data_m F B (Ntc DIGINET_N_DATA st 0 0 c r 0 0 None body blen) in
  let* d := int_inc (GOT_ndata B1) in
  Some (set_GOT_ndata B1 d, tt).
Proof. intros. reflexivity. Qed.

(* the model's keepalive test (FT:357) is the frame's (L6's shape, cmd = DATA) *)
Lemma rxdata_ka_eq : forall fr n, rx_frame_facts fr n -> fr_cmd (rxbuf fr n) = DIGINET_CMD_DATA ->
  (fr_body_len (rxbuf fr n) =? 1) && (at8 (skipn (Z.to_nat 30) (tf_bytes fr)) 0 =? 0) = fr_keepalive (rxbuf fr n).
Proof.
  intros fr n Hf Hc. unfold fr_keepalive, keepalive_of. rewrite Hc, <- (rf_body_bytes _ _ Hf).
  change (Z.to_nat 30) with 30%nat.
  destruct (Z.eqb_spec (fr_body_len (rxbuf fr n)) 1) as [E|E].
  - rewrite E, at8_firstn by (simpl; lia). reflexivity.
  - reflexivity.
Qed.

(* the two duplicate tests agree under B6 *)
Lemma rxdata_dup_eq : forall v c1 c2 s r, bit01 v -> (v = 1 -> c1 = c2) ->
  negb (v =? 0) && (s =? c1) && negb (r =? 0) = truth v && (s =? c2) && truth r.
Proof.
  intros v c1 c2 s r [E|E] Hc; unfold truth.
  - subst v. reflexivity.
  - rewrite (Hc E). reflexivity.
Qed.

(* now + backoff never wraps (agree_time c_now, ops <= OPS_MAX; a1_backoff) *)
Lemma rxdata_bo_eq : forall now b, 0 <= now <= 1000000 + 1024 * 65535000000 -> 0 <= b <= 255 ->
  u64 (now + h_ms_m b) = now + b * 1000.
Proof.
  intros now b Hn Hb. unfold h_ms_m, u64.
  change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_small (b * 1000) 18446744073709551616) by lia.
  rewrite (Z.mod_small (now + b * 1000) 18446744073709551616) by lia.
  reflexivity.
Qed.

(* ---- the library ---- *)

(* send_control (s, ACK, f.send) (DS:242, :97-109): the ACK passes io_send's checks (SendOk), GOT.acks + 1 *)
Lemma rxdata_ack : forall (HL : links) I F W s a,
  length W = WN -> S_io_send W = ti_io_send I ->
  M_desk_known W = 1 -> S_desk_mac W = M_desk W -> length (M_desk W) = 6%nat ->
  S_cfg_host_mac W = HOST -> S_cfg_sum_mode W = Cfg_sum_mode W ->
  (Cfg_sum_mode W = DIGINET_SUM_BODY \/ Cfg_sum_mode W = DIGINET_SUM_ZERO) ->
  S_host_counter W = M_host_counter W -> g_rx_send W = s -> GOT_acks W = a -> 0 <= a <= 1 ->
  exists W1 r f, send_control_m I F W DIGINET_CMD_ACK s = Some (W1, (r, f)) /\
    wframe (in_rs rxdata_R_ack) W (rxdata_W2 W1 r) /\ g_fail_next (rxdata_W2 W1 r) = 0 /\
    GOT_acks (rxdata_W2 W1 r) = a + 1 /\ length (rxdata_W2 W1 r) = WN.
Proof.
  intros HL I F W s a HW Hio Hk Hdm Hdl Hhm Hsm Hmode Hhc Hrx HG Ha.
  assert (Hok : build_ok (S_desk_mac W) (S_cfg_host_mac W) (S_host_counter W) s 0 SPEC_CMD_ACK 0 []
                  (S_cfg_sum_mode W)).
  { apply control_build_ok.
    - rewrite Hdm. exact Hdl.
    - rewrite Hhm. reflexivity.
    - rewrite Hsm. exact Hmode.
    - unfold S_host_counter. exact (rw_u_range W A_S_host_counter 4).
    - rewrite <- Hrx. unfold g_rx_send. exact (rw_u_range W OFF_g_rx_send 4).
    - wcl. }
  assert (Ecode : diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN (S_cfg_sum_mode W) = DIGINET_MIN_FRAME_LEN)
    by exact (proj1 (control_frame_ok HL W _ _ _ _ _ _ Hok)).
  assert (HG' : GOT_acks W <> INT_MAX) by (rewrite HG; clear - Ha; unfold INT_MAX; lia).
  assert (Eio : io_send_m I W (lib_frame (S_desk_mac W) (S_cfg_host_mac W) (S_host_counter W) s 0 DIGINET_CMD_ACK
                  0 [] (S_cfg_sum_mode W)) =
                Some (set_GOT_acks (set_g_fail_next W 0) (GOT_acks W + 1),
                      if truth (g_fail_next W) then - EIO else 0))
    by exact (io_send_ack_ok HL I W _ _ _ _ _ HW Hok Hhm Hk (eq_sym Hdm) (eq_sym Hsm) (eq_sym Hrx) Hhc HG').
  rewrite HG in Eio.
  case_eq (truth (g_fail_next W)); intros Ef; rewrite Ef in Eio.
  - exists (set_GOT_acks (set_g_fail_next W 0) (a + 1)), (- EIO),
      (lib_frame (S_desk_mac W) (S_cfg_host_mac W) (S_host_counter W) s 0 DIGINET_CMD_ACK 0 [] (S_cfg_sum_mode W)).
    assert (E2 : rxdata_W2 (set_GOT_acks (set_g_fail_next W 0) (a + 1)) (- EIO) =
                 set_GOT_acks (set_g_fail_next W 0) (a + 1))
      by reflexivity.
    rewrite E2. split; [| split; [wfrs | split; [wget | split; [wget | wlen]]]].
    unfold send_control_m. cbv zeta. rewrite Ecode, rxdata_lt60. cbv beta iota.
    unfold send_raw_m, call_send. rewrite Hio, (Z.eqb_refl (ti_io_send I)). cbv beta iota.
    rewrite Eio. cbv beta iota. rewrite rxdata_eio. cbv beta iota. reflexivity.
  - exists (set_S_stats_tx_frames (set_GOT_acks (set_g_fail_next W 0) (a + 1))
              (u64 (S_stats_tx_frames (set_GOT_acks (set_g_fail_next W 0) (a + 1)) + 1))), 0,
      (lib_frame (S_desk_mac W) (S_cfg_host_mac W) (S_host_counter W) s 0 DIGINET_CMD_ACK 0 [] (S_cfg_sum_mode W)).
    assert (E2 : rxdata_W2 (set_S_stats_tx_frames (set_GOT_acks (set_g_fail_next W 0) (a + 1))
                   (u64 (S_stats_tx_frames (set_GOT_acks (set_g_fail_next W 0) (a + 1)) + 1))) 0 =
                 set_S_stats_tx_acks (set_S_stats_tx_frames (set_GOT_acks (set_g_fail_next W 0) (a + 1))
                   (u64 (S_stats_tx_frames (set_GOT_acks (set_g_fail_next W 0) (a + 1)) + 1)))
                   (u64 (S_stats_tx_acks (set_S_stats_tx_frames (set_GOT_acks (set_g_fail_next W 0) (a + 1))
                      (u64 (S_stats_tx_frames (set_GOT_acks (set_g_fail_next W 0) (a + 1)) + 1))) + 1)))
      by reflexivity.
    rewrite E2. split; [| split; [wfrs | split; [wget | split; [wget | wlen]]]].
    unfold send_control_m. cbv zeta. rewrite Ecode, rxdata_lt60. cbv beta iota.
    unfold send_raw_m, call_send. rewrite Hio, (Z.eqb_refl (ti_io_send I)). cbv beta iota.
    rewrite Eio. cbv beta iota. rewrite (Z.eqb_refl 0). cbv beta iota. reflexivity.
Qed.

(* DS:244-247: rx_data, and on a retry rx_desk_retries and the backoff *)
Lemma rxdata_W4_ok : forall W2 buf now, length W2 = WN ->
  wframe (in_rs rxdata_R_w4) W2 (rxdata_W4 W2 buf now) /\ length (rxdata_W4 W2 buf now) = WN /\
  S_backoff_until_us (rxdata_W4 W2 buf now) =
    (if fr_retry buf =? 0 then S_backoff_until_us W2 else u64 (now + ms_m (S_cfg_backoff_ms W2))).
Proof.
  intros W2 buf now HW. unfold rxdata_W4. cbv zeta. destruct (fr_retry buf =? 0); cbv beta iota.
  - split; [wfrs|]. split; [wlen | wget].
  - split; [wfrs|]. split; [wlen|].
    rxd_rd. apply rw_mod_id. unfold u64. apply Z.mod_pos_bound. wcl.
Qed.

(* DS:249-260 from W4, the world after DS:247; W the world on_data started from, GOT.ndata = g *)
Lemma rxdata_ltail_ok : forall (HL : links) I fr n W W4 g,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) -> fr_code (rxbuf fr n) = DIGINET_OK ->
  wframe (in_rs (rxdata_R_ack ++ rxdata_R_w4)) W W4 -> length W = WN ->
  S_notify W = ti_notice I -> GOT_ndata W = g -> 0 <= g <= 1 ->
  (rxdata_dupL W (rxbuf fr n) = false -> fr_keepalive (rxbuf fr n) = false ->
     OW_ndata W = g + 1 /\ OW_dn_len W g = fr_body_len (rxbuf fr n) /\ OW_dn_body W g = tf_addr fr + 30 /\
     OW_dn_counter W g = fr_send (rxbuf fr n) /\ OW_dn_retry W g = fr_retry (rxbuf fr n)) ->
  exists W', rxdata_ltail I (Some fr) W4 (rxbuf fr n) = Some (W', tt) /\
    wframe (in_rs rxdata_R_lt) W4 W' /\ length W' = WN /\
    S_desk_counter_valid W' = (if rxdata_dupL W (rxbuf fr n) then S_desk_counter_valid W else 1) /\
    S_desk_counter W' = (if rxdata_dupL W (rxbuf fr n) then S_desk_counter W else fr_send (rxbuf fr n)) /\
    GOT_ndata W' = (if rxdata_dupL W (rxbuf fr n) || fr_keepalive (rxbuf fr n) then g else g + 1).
Proof.
  intros HL I fr n W W4 g Hn Hcode H4 HW Hnot HG Hg Hdat.
  assert (Hnn : (Z.to_nat n <= length (tf_bytes fr))%nat) by lia.
  assert (L4 : length W4 = WN) by exact (wframe_len _ _ _ H4 HW).
  assert (V4 : S_desk_counter_valid W4 = S_desk_counter_valid W) by fget H4.
  assert (C4 : S_desk_counter W4 = S_desk_counter W) by fget H4.
  assert (G4 : GOT_ndata W4 = g) by (transitivity (GOT_ndata W); [fget H4 | exact HG]).
  assert (Ed : rxdata_dupL W4 (rxbuf fr n) = rxdata_dupL W (rxbuf fr n))
    by (unfold rxdata_dupL; rewrite V4, C4; reflexivity).
  pose proof (be32_range (rxbuf fr n) 18) as Rs.
  assert (Rs' : 0 <= fr_send (rxbuf fr n) < 2 ^ (8 * Z.of_nat 4)) by exact Rs.
  unfold rxdata_ltail. rewrite Ed.
  destruct (rxdata_dupL W (rxbuf fr n)) eqn:Edup.
  - (* DS:249-251, a duplicate *)
    exists (set_S_stats_rx_duplicates W4 (u64 (S_stats_rx_duplicates W4 + 1))). cbv beta iota zeta delta [orb].
    split; [reflexivity|]. split; [wfrs|]. split; [wlen|].
    split; [transitivity (S_desk_counter_valid W4); [wget | exact V4]|].
    split; [transitivity (S_desk_counter W4); [wget | exact C4]|].
    transitivity (GOT_ndata W4); [wget | exact G4].
  - destruct (fr_keepalive (rxbuf fr n)) eqn:Eka.
    + (* DS:253-256, a keepalive *)
      exists (set_S_desk_counter_valid (set_S_desk_counter W4 (fr_send (rxbuf fr n))) 1).
      cbv beta iota zeta delta [orb].
      split; [reflexivity|]. split; [wfrs|]. split; [wlen|].
      split; [wget|]. split; [rxd_rd; apply rw_mod_id; exact Rs'|].
      transitivity (GOT_ndata W4); [wget | exact G4].
    + (* DS:257-260, the N_DATA notice *)
      destruct (Hdat eq_refl eq_refl) as (D1 & D2 & D3 & D4 & D5).
      cbv beta iota zeta delta [orb].
      remember (set_S_desk_counter_valid (set_S_desk_counter W4 (fr_send (rxbuf fr n))) 1) as W5 eqn:EW5.
      assert (L5 : length W5 = WN) by (subst W5; wlen).
      assert (H45 : wframe (in_rs rxdata_R_lt) W4 W5) by (subst W5; wfrs).
      pose proof (wframe_trans_rs _ _ _ _ _ H4 H45) as H5.
      assert (N5 : S_notify W5 = ti_notice I) by (transitivity (S_notify W); [fget H5 | exact Hnot]).
      assert (G5 : GOT_ndata W5 = g) by (transitivity (GOT_ndata W4); [subst W5; wget | exact G4]).
      assert (O5 : OW_ndata W5 = g + 1) by (transitivity (OW_ndata W); [fget H5 | exact D1]).
      assert (Hk : g = 0 \/ g = 1) by (clear - Hg; lia).
      assert (E1 : OW_dn_len W5 g = fr_body_len (rxbuf fr n))
        by (transitivity (OW_dn_len W g); [rxd_k Hk H5 | exact D2]).
      assert (E2 : OW_dn_body W5 g = tf_addr fr + 30) by (transitivity (OW_dn_body W g); [rxd_k Hk H5 | exact D3]).
      assert (E3 : OW_dn_counter W5 g = fr_send (rxbuf fr n))
        by (transitivity (OW_dn_counter W g); [rxd_k Hk H5 | exact D4]).
      assert (E4 : OW_dn_retry W5 g = fr_retry (rxbuf fr n))
        by (transitivity (OW_dn_retry W g); [rxd_k Hk H5 | exact D5]).
      assert (Efr : TFrame (tf_addr fr) (tf_bytes fr) = fr) by (destruct fr; reflexivity).
      pose proof (check_state_data_ok HL W5 (tf_addr fr) (tf_bytes fr) (Z.to_nat n) (S_state W5) g Hnn) as C.
      cbv zeta in C. fold (rxbuf fr n) in C. rewrite Efr in C.
      assert (Zg2 : 0 <= g < 2) by (clear - Hg; lia).
      assert (Zgn : g < OW_ndata W5) by (rewrite O5; clear - Hg; lia).
      specialize (C Hcode G5 Zg2 Zgn E1 E2 E3 E4).
      exists (set_GOT_ndata W5 (g + 1)).
      split.
      * unfold call_notify. rewrite N5, (Z.eqb_refl (ti_notice I)). cbv beta iota.
        rewrite (rxdata_notice I (Some fr) W5 (S_state W5) (fr_send (rxbuf fr n)) (fr_retry (rxbuf fr n))
                   (fr_body (rxbuf fr n)) (fr_body_len (rxbuf fr n))), C.
        cbv beta iota. rewrite G5, (rxdata_inc g Hg). cbv beta iota. reflexivity.
      * split; [subst W5; wfrs|]. split; [subst W5; wlen|].
        split; [subst W5; wget|]. split; [subst W5; rxd_rd; apply rw_mod_id; exact Rs'|].
        wget.
Qed.

(* the library's switch on a data frame (DS:298-316 -> on_data DS:239-261), from GOT.acks = a, GOT.ndata = g *)
Lemma rxdata_lib : forall (HL : links) I fr n W now a g,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) -> fr_code (rxbuf fr n) = DIGINET_OK ->
  fr_cmd (rxbuf fr n) = DIGINET_CMD_DATA ->
  length W = WN -> S_io_send W = ti_io_send I -> S_notify W = ti_notice I ->
  M_desk_known W = 1 -> S_desk_mac W = M_desk W -> length (M_desk W) = 6%nat ->
  S_cfg_host_mac W = HOST -> S_cfg_sum_mode W = Cfg_sum_mode W ->
  (Cfg_sum_mode W = DIGINET_SUM_BODY \/ Cfg_sum_mode W = DIGINET_SUM_ZERO) ->
  S_host_counter W = M_host_counter W -> g_rx_send W = fr_send (rxbuf fr n) -> GOT_acks W = a -> 0 <= a <= 1 ->
  GOT_ndata W = g -> 0 <= g <= 1 ->
  (rxdata_dupL W (rxbuf fr n) = false -> fr_keepalive (rxbuf fr n) = false ->
     OW_ndata W = g + 1 /\ OW_dn_len W g = fr_body_len (rxbuf fr n) /\ OW_dn_body W g = tf_addr fr + 30 /\
     OW_dn_counter W g = fr_send (rxbuf fr n) /\ OW_dn_retry W g = fr_retry (rxbuf fr n)) ->
  exists W', rx_sw I (Some fr) W (rxbuf fr n) now = Some (W', tt) /\
    wframe (in_rs rxdata_R_lib) W W' /\ length W' = WN /\ g_fail_next W' = 0 /\ GOT_acks W' = a + 1 /\
    S_backoff_until_us W' =
      (if fr_retry (rxbuf fr n) =? 0 then S_backoff_until_us W else u64 (now + ms_m (S_cfg_backoff_ms W))) /\
    S_desk_counter_valid W' = (if rxdata_dupL W (rxbuf fr n) then S_desk_counter_valid W else 1) /\
    S_desk_counter W' = (if rxdata_dupL W (rxbuf fr n) then S_desk_counter W else fr_send (rxbuf fr n)) /\
    GOT_ndata W' = (if rxdata_dupL W (rxbuf fr n) || fr_keepalive (rxbuf fr n) then g else g + 1).
Proof.
  intros HL I fr n W now a g Hn Hcode Hc HW Hio Hnot Hk Hdm Hdl Hhm Hsm Hmode Hhc Hrx HGa Ha HGn Hg Hdat.
  destruct (rxdata_ack HL I (Some fr) W (fr_send (rxbuf fr n)) a HW Hio Hk Hdm Hdl Hhm Hsm Hmode Hhc Hrx HGa Ha)
    as (W1 & r & f & Esc & Hfa & Fa & Ga & La).
  destruct (rxdata_W4_ok (rxdata_W2 W1 r) (rxbuf fr n) now La) as (Hf4 & L4 & Bo4).
  pose proof (wframe_trans_rs _ _ _ _ _ Hfa Hf4) as H24.
  destruct (rxdata_ltail_ok HL I fr n W (rxdata_W4 (rxdata_W2 W1 r) (rxbuf fr n) now) g Hn Hcode H24 HW Hnot HGn Hg
              Hdat)
    as (W' & Elt & Hlt & LW' & Sv & Sc & Gn).
  pose proof (wframe_trans_rs _ _ _ _ _ Hf4 Hlt) as H2'.
  assert (F1 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE) = false) by (rewrite Hc; reflexivity).
  assert (F2 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE_SESSION) = false) by (rewrite Hc; reflexivity).
  assert (F3 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ACK) = false) by (rewrite Hc; reflexivity).
  assert (F4 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_DATA) = true) by (rewrite Hc; reflexivity).
  assert (Sb2 : S_backoff_until_us (rxdata_W2 W1 r) = S_backoff_until_us W) by fget Hfa.
  assert (Sk2 : S_cfg_backoff_ms (rxdata_W2 W1 r) = S_cfg_backoff_ms W) by fget Hfa.
  exists W'. split.
  - unfold rx_sw. cbv zeta. rewrite F1, F2, F3, F4. cbv beta iota delta [orb].
    rewrite (rxdata_on_data I (Some fr) W (rxbuf fr n) now W1 r f Esc). exact Elt.
  - split; [exact (wframe_trans_rs _ _ _ _ _ Hfa (wframe_trans_rs _ _ _ _ _ Hf4 Hlt))|].
    split; [exact LW'|].
    split; [transitivity (g_fail_next (rxdata_W2 W1 r)); [fget H2' | exact Fa]|].
    split; [transitivity (GOT_acks (rxdata_W2 W1 r)); [fget H2' | exact Ga]|].
    split.
    + transitivity (S_backoff_until_us (rxdata_W4 (rxdata_W2 W1 r) (rxbuf fr n) now)); [fget Hlt|].
      rewrite Bo4, Sb2, Sk2. reflexivity.
    + exact (conj Sv (conj Sc Gn)).
Qed.

(* ---- the model ---- *)

(* FT:348-351, OW.acks := ak (the old count + 1) *)
Lemma rxdata_mB4_ok : forall X retry ak, length X = WN -> 0 <= ak <= 2 ->
  wframe (in_rs rxdata_R_m4) X (rxdata_mB4 X retry ak) /\ length (rxdata_mB4 X retry ak) = WN /\
  OW_acks (rxdata_mB4 X retry ak) = ak /\
  M_backoff_until (rxdata_mB4 X retry ak) =
    (if truth retry then u64 (g_now X + h_ms_m (Cfg_backoff_ms X)) else M_backoff_until X).
Proof.
  intros X retry ak HX Hak. unfold rxdata_mB4. cbv zeta. destruct (truth retry); cbv beta iota.
  - split; [wfrs|]. split; [wlen|]. split; [wget|].
    rxd_rd. apply rw_mod_id. unfold u64. apply Z.mod_pos_bound. wcl.
  - split; [wfrs|]. split; [wlen|]. split; [wget | wget].
Qed.

(* FT:352-364 from B4 (X the world m_rx's switch started from, OW.ndata = nd) *)
Lemma rxdata_mtail_ok : forall fr n X B4 nd,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  0 < tf_addr fr /\ tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64 ->
  rx_frame_facts fr n -> fr_cmd (rxbuf fr n) = DIGINET_CMD_DATA ->
  wframe (in_rs rxdata_R_m4) X B4 -> length X = WN -> OW_ndata X = nd -> 0 <= nd <= 1 ->
  exists Bm, rxdata_mtail fr n B4 = Some (Bm, tt) /\ wframe (in_rs rxdata_R_mt) B4 Bm /\ length Bm = WN /\
    M_desk_counter_valid Bm = (if rxdata_dupM X (rxbuf fr n) then M_desk_counter_valid X else 1) /\
    M_desk_counter Bm = (if rxdata_dupM X (rxbuf fr n) then M_desk_counter X else fr_send (rxbuf fr n)) /\
    OW_ndata Bm = (if rxdata_dupM X (rxbuf fr n) || fr_keepalive (rxbuf fr n) then nd else nd + 1) /\
    (rxdata_dupM X (rxbuf fr n) = false -> fr_keepalive (rxbuf fr n) = false ->
       OW_dn_len Bm nd = fr_body_len (rxbuf fr n) /\ OW_dn_body Bm nd = tf_addr fr + 30 /\
       OW_dn_counter Bm nd = fr_send (rxbuf fr n) /\ OW_dn_retry Bm nd = fr_retry (rxbuf fr n)).
Proof.
  intros fr n X B4 nd Hn Ha Hf Hc H4 HX N0 Hnd.
  pose proof (rf_blen _ _ Hf) as Rb.
  assert (Rb' : 0 <= fr_body_len (rxbuf fr n) < 2 ^ (8 * Z.of_nat 8)).
  { change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). destruct Ha as [Ha1 Ha2]. lia. }
  assert (Ra' : 0 <= tf_addr fr + 30 < 2 ^ (8 * Z.of_nat 8)).
  { change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). destruct Ha as [Ha1 Ha2]. lia. }
  pose proof (be32_range (rxbuf fr n) 18) as Rs.
  assert (Rs' : 0 <= fr_send (rxbuf fr n) < 2 ^ (8 * Z.of_nat 4)) by exact Rs.
  pose proof (be16_range (rxbuf fr n) 26) as Rr.
  assert (Rr' : 0 <= fr_retry (rxbuf fr n) < 2 ^ (8 * Z.of_nat 2)) by exact Rr.
  assert (L4 : length B4 = WN) by exact (wframe_len _ _ _ H4 HX).
  assert (V4 : M_desk_counter_valid B4 = M_desk_counter_valid X) by fget H4.
  assert (C4 : M_desk_counter B4 = M_desk_counter X) by fget H4.
  assert (N4 : OW_ndata B4 = nd) by (transitivity (OW_ndata X); [fget H4 | exact N0]).
  unfold rxdata_mtail. cbv zeta.
  rewrite (rf_send _ _ Hf), (rf_retry _ _ Hf), (rf_body_len _ _ Hf), (rf_body _ _ Hf).
  assert (Ed : truth (M_desk_counter_valid B4) && (fr_send (rxbuf fr n) =? M_desk_counter B4) &&
               truth (fr_retry (rxbuf fr n)) = rxdata_dupM X (rxbuf fr n))
    by (unfold rxdata_dupM; rewrite V4, C4; reflexivity).
  rewrite Ed, (rxdata_ka_eq fr n Hf Hc).
  destruct (rxdata_dupM X (rxbuf fr n)) eqn:Edup.
  - (* FT:352-353, a duplicate *)
    cbv beta iota delta [orb].
    exists B4. split; [reflexivity|]. split; [apply wframe_refl|]. split; [exact L4|].
    split; [exact V4|]. split; [exact C4|]. split; [exact N4|]. intros H; discriminate H.
  - destruct (fr_keepalive (rxbuf fr n)) eqn:Eka.
    + (* FT:354-357, a keepalive *)
      cbv beta iota delta [orb].
      exists (set_M_desk_counter_valid (set_M_desk_counter B4 (fr_send (rxbuf fr n))) 1).
      split; [reflexivity|]. split; [wfrs|]. split; [wlen|].
      split; [wget|]. split; [rxd_rd; apply rw_mod_id; exact Rs'|].
      split; [transitivity (OW_ndata B4); [wget | exact N4]|]. intros _ H; discriminate H.
    + (* FT:358-364, OW.dn[nd] (nd < 2) and OW.ndata = nd + 1 *)
      cbv beta iota delta [orb].
      assert (N5 : OW_ndata (set_M_desk_counter_valid (set_M_desk_counter B4 (fr_send (rxbuf fr n))) 1) = nd)
        by (transitivity (OW_ndata B4); [wget | exact N4]).
      assert (Lt2 : (nd <? 2) = true) by (apply Z.ltb_lt; clear - Hnd; lia).
      assert (Lt0 : (nd <? 0) = false) by (apply Z.ltb_ge; clear - Hnd; lia).
      rewrite N5, Lt2, Lt0, (rxdata_inc nd Hnd). cbv beta iota.
      exists (set_OW_ndata (set_OW_dn_retry (set_OW_dn_counter (set_OW_dn_len (set_OW_dn_body
          (set_M_desk_counter_valid (set_M_desk_counter B4 (fr_send (rxbuf fr n))) 1) nd (tf_addr fr + 30)) nd
          (fr_body_len (rxbuf fr n))) nd (fr_send (rxbuf fr n))) nd (fr_retry (rxbuf fr n))) (nd + 1)).
      split; [reflexivity|].
      (* the reads below decide their offsets on numerals (wcl), so nd is 0 or 1 from here *)
      assert (Hk : nd = 0 \/ nd = 1) by (clear - Hnd; lia).
      destruct Hk as [Ek|Ek]; rewrite Ek;
        (split; [wfrs|]; split; [wlen|];
         split; [wget|]; split; [rxd_rd; apply rw_mod_id; exact Rs'|]; split; [wget|];
         intros _ _; split; [|split; [|split]];
         [ rxd_rd; apply rw_mod_id; exact Rb' | rxd_rd; apply rw_mod_id; exact Ra'
         | rxd_rd; apply rw_mod_id; exact Rs' | rxd_rd; apply rw_mod_id; exact Rr' ]).
Qed.

(* ---- after the switch ---- *)

(* the transition tables of GOT and OW (OFF + 4, 16 entries of 12 bytes) across a frame that misses them *)
Lemma rxdata_t_fr : forall rs X Y, wframe (in_rs rs) X Y ->
  disj_rs (OFF_GOT + 4) 192 rs = true -> disj_rs (OFF_OW + 4) 192 rs = true ->
  forall i, 0 <= i < TRANS_MAX ->
  GOT_t_state Y i = GOT_t_state X i /\ GOT_t_old Y i = GOT_t_old X i /\ GOT_t_reason Y i = GOT_t_reason X i /\
  OW_t_state Y i = OW_t_state X i /\ OW_t_old Y i = OW_t_old X i /\ OW_t_reason Y i = OW_t_reason X i.
Proof.
  intros rs X Y H Hg Ho i Hi. unfold TRANS_MAX in Hi.
  pose proof (disj_rs_ok _ _ rs Hg) as HG. pose proof (disj_rs_ok _ _ rs Ho) as HO.
  unfold GOT_t_state, GOT_t_old, GOT_t_reason, OW_t_state, OW_t_old, OW_t_reason, A_GOT_t_state, A_GOT_t_old,
    A_GOT_t_reason, A_OW_t_state, A_OW_t_old, A_OW_t_reason.
  (* the offsets hold i: lia closes the sides (fget's wcl would vm_compute them, which is slow on a variable) *)
  split; [|split; [|split; [|split; [|split]]]];
    (apply (wframe_s32_at _ _ _ _ H);
     [unfold OFF_GOT, OFF_OW; lia | intros a Ha; first [apply HG; lia | apply HO; lia]]).
Qed.

(* B the world before m_rx (OW = GOT, room for this reception), W' the world after the library's switch *)
Lemma rxdata_post : forall I ops B W',
  agree_core I ops B -> ow_room B -> M_desk_known B = 1 ->
  wframe (in_rs rxdata_RS) B W' ->
  S_desk_known W' = 1 -> S_desk_mac W' = M_desk B -> M_last_rx W' = g_now B -> S_last_rx_us W' = g_now B ->
  S_backoff_until_us W' = M_backoff_until W' -> M_backoff_until W' <= g_now B + 255000 ->
  S_desk_counter_valid W' = M_desk_counter_valid W' -> bit01 (M_desk_counter_valid W') ->
  (M_desk_counter_valid W' = 1 -> S_desk_counter W' = M_desk_counter W') ->
  g_fail_next W' = 0 -> OW_acks W' = OW_acks B + 1 -> GOT_acks W' = OW_acks B + 1 ->
  GOT_ndata W' = OW_ndata W' -> OW_ndata B <= OW_ndata W' <= OW_ndata B + 1 ->
  agree_core I ops W' /\ ow_got_eq W' /\ ow_step B W'.
Proof.
  intros I ops B W' Hcore Hroom Hk1 Hall Pdk Pdm Plr Plu Pbo Pbl Pv Pv01 Pc Pfn Pak Pga Pnd Pndr.
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (HB : length B = WN) by exact Hlen.
  assert (U0 : M_desk_known W' = 1) by (transitivity (M_desk_known B); [fget Hall | exact Hk1]).
  assert (Ud : M_desk W' = M_desk B) by fget Hall.
  assert (U1 : S_state W' = S_state B) by fget Hall.
  assert (U2 : M_state W' = M_state B) by fget Hall.
  assert (U3 : S_foreign W' = S_foreign B) by fget Hall.
  assert (U4 : M_foreign W' = M_foreign B) by fget Hall.
  assert (U5 : S_e1_named_us W' = S_e1_named_us B) by fget Hall.
  assert (U6 : M_e1_us W' = M_e1_us B) by fget Hall.
  assert (U7 : S_wake_acked W' = S_wake_acked B) by fget Hall.
  assert (U8 : M_e2_acked W' = M_e2_acked B) by fget Hall.
  assert (U9 : S_wake_sent_us W' = S_wake_sent_us B) by fget Hall.
  assert (U10 : M_wake_sent W' = M_wake_sent B) by fget Hall.
  assert (U13 : g_raw W' = g_raw B) by fget Hall.
  assert (U14 : S_next_keepalive_us W' = S_next_keepalive_us B) by fget Hall.
  assert (U15 : M_next_ka W' = M_next_ka B) by fget Hall.
  assert (U16 : S_display_sent W' = S_display_sent B) by fget Hall.
  assert (U17 : M_display_sent W' = M_display_sent B) by fget Hall.
  assert (U18 : S_last_display_us W' = S_last_display_us B) by fget Hall.
  assert (U19 : M_last_display W' = M_last_display B) by fget Hall.
  assert (U24 : S_host_counter W' = S_host_counter B) by fget Hall.
  assert (U25 : M_host_counter W' = M_host_counter B) by fget Hall.
  assert (U26 : M_fly_on W' = M_fly_on B) by fget Hall.
  assert (U33 : M_fly_sent W' = M_fly_sent B) by fget Hall.
  assert (U37 : Cfg_max_retries W' = Cfg_max_retries B) by fget Hall.
  assert (U38 : Cfg_sum_mode W' = Cfg_sum_mode B) by fget Hall.
  assert (U39 : g_now W' = g_now B) by fget Hall.
  assert (U40 : Cfg_wake_timeout_ms W' = Cfg_wake_timeout_ms B) by fget Hall.
  assert (U41 : Cfg_offline_ms W' = Cfg_offline_ms B) by fget Hall.
  assert (U42 : Cfg_ack_timeout_ms W' = Cfg_ack_timeout_ms B) by fget Hall.
  assert (U44 : S_personality W' = S_personality B) by fget Hall.
  assert (Hst' : agree_st W').
  { constructor; rw_eqs W'.
    - exact (b1_state _ Hst).
    - exact (b1_state_range _ Hst).
    - wsyn.
    - right; wsyn.
    - intros _; wsyn.
    - exact (b3_foreign _ Hst).
    - exact (b3_foreign01 _ Hst).
    - exact (b3_e1 _ Hst).
    - exact (b3_e1_01 _ Hst).
    - exact (b3_e2 _ Hst).
    - exact (b3_e2_01 _ Hst).
    - exact (b4_wake_sent _ Hst).
    - wsyn.
    - wsyn.
    - exact (b5_next_ka _ Hst).
    - exact (b5_display_sent _ Hst).
    - exact (b5_display_sent01 _ Hst).
    - exact (b5_last_display _ Hst).
    - wsyn.
    - exact Pv01.
    - exact Pc.
    - exact (b7_host_counter _ Hst).
    - exact (b9_idle _ Hst).
    - intros _; wsyn. }
  assert (Hfl' : agree_fly W').
  { apply (agree_fly_fr _ B W' Hall); [vm_compute; reflexivity | vm_compute; reflexivity | exact U24
      | exact U37 | exact U38 | | exact Hfly].
    intros Hon. split; [exact Ud | rewrite U2; exact (b8_state _ Hfly Hon)]. }
  assert (Hti' : agree_time ops W').
  { constructor; rw_eqs W'.
    - exact (c_now _ _ Htime).
    - apply Z.le_refl.
    - exact (c1_wake_sent _ _ Htime).
    - exact (c1_fly_sent _ _ Htime).
    - exact (c1_last_display _ _ Htime).
    - exact Pbl.
    - exact (c1_next_ka _ _ Htime).
    - exact (c2_wake _ _ Htime).
    - intros _. rewrite Z.sub_diag. pose proof (a1_offline _ Hcfg) as Ho. clear - Ho. lia.
    - exact (c2_fly _ _ Htime). }
  assert (Hmi' : agree_misc I W').
  { constructor; rw_eqs W'; [left; wsyn | exact (e2_personality _ _ Hmisc)]. }
  (* OW and GOT: the counts a data frame does not move, and the transition tables, from B *)
  assert (Z1 : OW_n W' = OW_n B) by fget Hall.
  assert (Z2 : OW_e2 W' = OW_e2 B) by fget Hall.
  assert (Z3 : OW_e3 W' = OW_e3 B) by fget Hall.
  assert (Z4 : OW_desk W' = OW_desk B) by fget Hall.
  assert (Z5 : OW_foreign W' = OW_foreign B) by fget Hall.
  assert (Z6 : OW_acked W' = OW_acked B) by fget Hall.
  assert (Y1 : GOT_n W' = GOT_n B) by fget Hall.
  assert (Y2 : GOT_e2 W' = GOT_e2 B) by fget Hall.
  assert (Y3 : GOT_e3 W' = GOT_e3 B) by fget Hall.
  assert (Y4 : GOT_desk W' = GOT_desk B) by fget Hall.
  assert (Y5 : GOT_foreign W' = GOT_foreign B) by fget Hall.
  assert (Y6 : GOT_acked W' = GOT_acked B) by fget Hall.
  pose proof (rxdata_t_fr rxdata_RS B W' Hall ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as Tt.
  pose proof (wr_og _ Hroom) as [O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 O16 O17].
  pose proof Hroom as [_ Rn Re2 Re3 Rak Rdk Rfg Rad Rnd].
  split; [| split].
  - apply (agree_core_rx I ops B W' Hcore); [| exact Hst' | exact Hfl' | exact Hti' | exact Hmi'].
    eapply wframe_rx; [| exact Hall]. vm_compute. reflexivity.
  - constructor.
    + rewrite Y1, Z1. exact O1.
    + rewrite Z1. exact O2.
    + intros i Hi Hi2. rewrite Z1 in Hi.
      assert (Hi3 : 0 <= i < TRANS_MAX) by (clear - Hi Hi2; lia).
      destruct (Tt i Hi3) as (T1 & T2 & T3 & T4 & T5 & T6).
      rewrite T1, T2, T3, T4, T5, T6. exact (O3 i Hi Hi2).
    + rewrite Y2, Z2. exact O4.
    + rewrite Z2. exact O5.
    + rewrite Y3, Z3. exact O6.
    + rewrite Z3. exact O7.
    + rewrite Pga, Pak. reflexivity.
    + rewrite Pak. clear - O9 Rak. lia.
    + rewrite Y4, Z4. exact O10.
    + rewrite Z4. exact O11.
    + rewrite Y5, Z5. exact O12.
    + rewrite Z5. exact O13.
    + rewrite Y6, Z6. exact O14.
    + rewrite Z6. exact O15.
    + exact Pnd.
    + clear - O17 Rnd Pndr. lia.
  - constructor.
    + rewrite Z1. clear - O2. lia.
    + rewrite Z2. clear - O5. lia.
    + rewrite Z3. clear - O7. lia.
    + rewrite Pak. clear - O9. lia.
    + rewrite Z4. clear - O11. lia.
    + rewrite Z5. clear - O13. lia.
    + rewrite Z6. clear - O15. lia.
    + clear - Pndr. lia.
Qed.

(* ---- the branch ---- *)

(* any reception of the operation: OW.acks = GOT.acks and OW.ndata = GOT.ndata, each 0 or 1, before the frame *)
Lemma rx_data_g : forall (HL : links), rx_branch_g cond_data.
Proof.
  intros HL. unfold rx_branch_g. intros I ops fr n B. cbv zeta. intros Hn Ha Hpre Hacc Hc.
  unfold cond_data in Hc.
  pose proof (ra_code _ _ Hacc) as Hcode.
  pose proof (rx_frame_ok HL fr n Hn Hcode) as Hf.
  destruct Hpre as [Hcore Hka Hroom _ Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (HB : length B = WN) by exact Hlen.
  pose proof (wr_og _ Hroom) as Hog.
  assert (Rak : 0 <= OW_acks B <= 1).
  { pose proof (og_acks_range _ Hog) as R1. pose proof (wr_acks _ Hroom) as R2. clear - R1 R2. lia. }
  assert (Rak2 : 0 <= OW_acks B + 1 <= 2) by (clear - Rak; lia).
  assert (Rnd : 0 <= OW_ndata B <= 1).
  { pose proof (og_ndata_range _ Hog) as R1. pose proof (wr_ndata _ Hroom) as R2. clear - R1 R2. lia. }
  pose proof (rf_cmd _ _ Hf) as Ecmd.
  pose proof (rf_src_len _ _ Hf) as Hsl.
  (* the desk is known: an unknown desk is heard only on an announce (ra_unknown) *)
  assert (Hk1 : M_desk_known B = 1).
  { destruct (b2_desk_known01 _ Hst) as [E|E]; [|exact E]. exfalso.
    destruct (ra_unknown _ _ Hacc E) as [Hann _]. rewrite Hc in Hann. vm_compute in Hann. discriminate Hann. }
  assert (EBk : learn_M B (rxbuf fr n) = B) by (unfold learn_M; rewrite Hk1; reflexivity).
  rewrite EBk.
  remember (set_M_last_rx B (g_now B)) as X eqn:EX.
  assert (HX : length X = WN) by (subst X; wlen).
  assert (HBX : wframe (in_rs [(A_M_last_rx, 8)]) B X) by (subst X; wfrs).
  assert (A0 : OW_acks X = OW_acks B) by fget HBX.
  assert (N0 : OW_ndata X = OW_ndata B) by fget HBX.
  assert (XLr : M_last_rx X = g_now B) by (subst X; wget).
  assert (XNw : g_now X = g_now B) by fget HBX.
  assert (XCb : Cfg_backoff_ms X = Cfg_backoff_ms B) by fget HBX.
  assert (XMb : M_backoff_until X = M_backoff_until B) by fget HBX.
  assert (XMv : M_desk_counter_valid X = M_desk_counter_valid B) by fget HBX.
  assert (XMc : M_desk_counter X = M_desk_counter B) by fget HBX.
  (* the model's switch, FT:344-365 *)
  assert (Hcm : sf_cmd (spec_read_frame (zs (tf_bytes fr)) n) = SPEC_CMD_DATA) by (rewrite Ecmd; exact Hc).
  rewrite (rxdata_m_eq I fr n X Hcm), A0, (rxdata_inc (OW_acks B) Rak). cbv beta iota.
  rewrite (rf_retry _ _ Hf).
  destruct (rxdata_mB4_ok X (fr_retry (rxbuf fr n)) (OW_acks B + 1) HX Rak2) as (Hf4 & L4 & Ak4 & Bo4).
  destruct (rxdata_mtail_ok fr n X (rxdata_mB4 X (fr_retry (rxbuf fr n)) (OW_acks B + 1)) (OW_ndata B) Hn Ha Hf Hc
              Hf4 HX N0 Rnd)
    as (Bm & Em & Hfm & LBm & Mv & Mc & Mn & Md).
  pose proof (wframe_trans_rs _ _ _ _ _ Hf4 Hfm) as HXm.
  pose proof (wframe_trans_rs _ _ _ _ _ HBX HXm) as Hm.
  assert (Mst : M_state Bm = M_state B) by fget Hm.
  assert (Mws : M_wake_sent Bm = M_wake_sent B) by fget Hm.
  assert (Mnw : g_now Bm = g_now B) by fget Hm.
  assert (Mlr : M_last_rx Bm = g_now B) by (transitivity (M_last_rx X); [fget HXm | exact XLr]).
  assert (Mcw : Cfg_wake_timeout_ms Bm = Cfg_wake_timeout_ms B) by fget Hm.
  assert (Mco : Cfg_offline_ms Bm = Cfg_offline_ms B) by fget Hm.
  exists Bm. split; [exact Em | split; [| split]].
  - (* FT:373 *)
    apply m_tick_quiet.
    + rw_eqs Bm. intros Hw. split; [exact (c1_wake_sent _ _ Htime) | exact (c2_wake _ _ Htime Hw)].
    + rw_eqs Bm. intros _. split; [apply Z.le_refl|]. rewrite Z.sub_diag.
      pose proof (a1_offline _ Hcfg) as Ho. clear - Ho. lia.
    + rw_eqs Bm. exact (proj2 (a1_wake_timeout _ Hcfg)).
    + rw_eqs Bm. exact (proj2 (a1_offline _ Hcfg)).
  - (* the model wrote only M and OW *)
    apply (wframe_rs_incl ([(A_M_last_rx, 8)] ++ (rxdata_R_m4 ++ rxdata_R_mt)) R_mod B Bm);
      [vm_compute; reflexivity | exact Hm].
  - intros W HW.
    pose proof HW as (HWf & HWk & HWm & HWl).
    assert (HWf' : wframe (in_rs R_start) Bm W) by exact HWf.
    assert (HWn : length W = WN) by exact (wframe_len _ _ _ HWf' LBm).
    pose proof (wframe_trans_rs _ _ _ _ _ Hm HWf') as HmW.
    (* the reads of the library's arm, on W *)
    assert (Wio : S_io_send W = ti_io_send I) by (transitivity (S_io_send B); [fget HmW | exact (a3_io_send _ _ Hio)]).
    assert (Wnt : S_notify W = ti_notice I) by (transitivity (S_notify B); [fget HmW | exact (a3_notify _ _ Hio)]).
    assert (Wk : M_desk_known W = 1) by (transitivity (M_desk_known B); [fget HmW | exact Hk1]).
    assert (Wmd : M_desk W = fr_src (rxbuf fr n))
      by (transitivity (M_desk B); [fget HmW | symmetry; exact (ra_known _ _ Hacc Hk1)]).
    assert (Wdm : S_desk_mac W = M_desk W) by (rewrite HWm; symmetry; exact Wmd).
    assert (Wdl : length (M_desk W) = 6%nat) by (rewrite Wmd; exact Hsl).
    assert (Whm : S_cfg_host_mac W = HOST)
      by (transitivity (S_cfg_host_mac B); [fget HmW | exact (a2_host_mac _ Hcfg)]).
    assert (WcsB : Cfg_sum_mode W = Cfg_sum_mode B) by fget HmW.
    assert (Wsm : S_cfg_sum_mode W = Cfg_sum_mode W).
    { rewrite WcsB. transitivity (S_cfg_sum_mode B); [fget HmW | exact (a2_sum_mode _ Hcfg)]. }
    assert (Wmode : Cfg_sum_mode W = DIGINET_SUM_BODY \/ Cfg_sum_mode W = DIGINET_SUM_ZERO)
      by (rewrite WcsB; exact (a1_sum_mode _ Hcfg)).
    assert (Whc : S_host_counter W = M_host_counter W).
    { transitivity (S_host_counter B); [fget HmW|].
      transitivity (M_host_counter B); [exact (b7_host_counter _ Hst) | symmetry; fget HmW]. }
    assert (Wrx : g_rx_send W = fr_send (rxbuf fr n))
      by (transitivity (g_rx_send B); [fget HmW | exact (Hsend Hcode)]).
    assert (Wga : GOT_acks W = OW_acks B) by (transitivity (GOT_acks B); [fget HmW | exact (og_acks _ Hog)]).
    assert (Wgn : GOT_ndata W = OW_ndata B) by (transitivity (GOT_ndata B); [fget HmW | exact (og_ndata _ Hog)]).
    assert (WSv : S_desk_counter_valid W = M_desk_counter_valid B)
      by (transitivity (S_desk_counter_valid B); [fget HmW | exact (b6_valid _ Hst)]).
    assert (WSc : S_desk_counter W = S_desk_counter B) by fget HmW.
    assert (WSb : S_backoff_until_us W = M_backoff_until B)
      by (transitivity (S_backoff_until_us B); [fget HmW | exact (b4_backoff _ Hst)]).
    assert (WSk : S_cfg_backoff_ms W = Cfg_backoff_ms B)
      by (transitivity (S_cfg_backoff_ms B); [fget HmW | exact (a2_backoff _ Hcfg)]).
    assert (Edup : rxdata_dupL W (rxbuf fr n) = rxdata_dupM X (rxbuf fr n)).
    { unfold rxdata_dupL, rxdata_dupM. rewrite WSv, WSc, XMv, XMc.
      exact (rxdata_dup_eq _ _ _ _ _ (b6_valid01 _ Hst) (b6_counter _ Hst)). }
    assert (Wdat : rxdata_dupL W (rxbuf fr n) = false -> fr_keepalive (rxbuf fr n) = false ->
       OW_ndata W = OW_ndata B + 1 /\ OW_dn_len W (OW_ndata B) = fr_body_len (rxbuf fr n) /\
       OW_dn_body W (OW_ndata B) = tf_addr fr + 30 /\ OW_dn_counter W (OW_ndata B) = fr_send (rxbuf fr n) /\
       OW_dn_retry W (OW_ndata B) = fr_retry (rxbuf fr n)).
    { intros Hd Hk'. rewrite Edup in Hd. destruct (Md Hd Hk') as (D1 & D2 & D3 & D4).
      assert (Hk2 : OW_ndata B = 0 \/ OW_ndata B = 1) by (clear - Rnd; lia).
      split; [| split; [| split; [| split]]].
      - transitivity (OW_ndata Bm); [fget HWf'|]. rewrite Mn, Hd, Hk'. reflexivity.
      - transitivity (OW_dn_len Bm (OW_ndata B)); [rxd_k Hk2 HWf' | exact D1].
      - transitivity (OW_dn_body Bm (OW_ndata B)); [rxd_k Hk2 HWf' | exact D2].
      - transitivity (OW_dn_counter Bm (OW_ndata B)); [rxd_k Hk2 HWf' | exact D3].
      - transitivity (OW_dn_retry Bm (OW_ndata B)); [rxd_k Hk2 HWf' | exact D4]. }
    (* the library's switch, DS:298-316 *)
    destruct (rxdata_lib HL I fr n W (g_now B) (OW_acks B) (OW_ndata B) Hn Hcode Hc HWn Wio Wnt Wk Wdm Wdl Whm Wsm
                Wmode Whc Wrx Wga Rak Wgn Rnd Wdat) as (W' & Elib & HfL & LW' & Fn' & Ga' & Bo' & Sv' & Sc' & Gn').
    exists W'. split; [exact Elib|].
    pose proof (wframe_trans_rs _ _ _ _ _ HmW HfL) as Hall.
    pose proof (wframe_trans_rs _ _ _ _ _ HWf' HfL) as HmW'.
    (* the fields the reception wrote, on W' *)
    assert (Pdk : S_desk_known W' = 1) by (transitivity (S_desk_known W); [fget HfL | exact HWk]).
    assert (Pdm : S_desk_mac W' = M_desk B)
      by (transitivity (S_desk_mac W); [fget HfL | rewrite HWm; exact (ra_known _ _ Hacc Hk1)]).
    assert (Plr : M_last_rx W' = g_now B) by (transitivity (M_last_rx Bm); [fget HmW' | exact Mlr]).
    assert (Plu : S_last_rx_us W' = g_now B) by (transitivity (S_last_rx_us W); [fget HfL | rewrite HWl; exact Mnw]).
    assert (EBo : M_backoff_until W' =
                  (if truth (fr_retry (rxbuf fr n)) then u64 (g_now B + h_ms_m (Cfg_backoff_ms B))
                   else M_backoff_until B)).
    { transitivity (M_backoff_until Bm); [fget HmW'|].
      transitivity (M_backoff_until (rxdata_mB4 X (fr_retry (rxbuf fr n)) (OW_acks B + 1))); [fget Hfm|].
      rewrite Bo4, XNw, XCb, XMb. reflexivity. }
    assert (ESb : S_backoff_until_us W' =
                  (if fr_retry (rxbuf fr n) =? 0 then M_backoff_until B
                   else u64 (g_now B + ms_m (Cfg_backoff_ms B)))) by (rewrite Bo', WSb, WSk; reflexivity).
    assert (Pbo : S_backoff_until_us W' = M_backoff_until W').
    { rewrite ESb, EBo. unfold truth, h_ms_m, ms_m.
      destruct (fr_retry (rxbuf fr n) =? 0); cbv beta iota delta [negb]; reflexivity. }
    assert (Pbl : M_backoff_until W' <= g_now B + 255000).
    { rewrite EBo. destruct (truth (fr_retry (rxbuf fr n))); cbv beta iota.
      - pose proof (c_now _ _ Htime) as Hnow. pose proof (d3_ops _ _ Hq) as Hops. unfold OPS_MAX in Hops.
        assert (Pn : 0 <= g_now B) by (unfold g_now; apply u_at_nonneg).
        assert (Pb : 0 <= Cfg_backoff_ms B) by (unfold Cfg_backoff_ms; apply u_at_nonneg).
        pose proof (a1_backoff _ Hcfg) as Hb.
        rewrite (rxdata_bo_eq (g_now B) (Cfg_backoff_ms B));
          [clear - Hb; lia | clear - Hnow Hops Pn; lia | clear - Pb Hb; lia].
      - exact (c1_backoff _ _ Htime). }
    assert (EMv : M_desk_counter_valid W' =
                  (if rxdata_dupM X (rxbuf fr n) then M_desk_counter_valid B else 1)).
    { transitivity (M_desk_counter_valid Bm); [fget HmW'|]. rewrite Mv, XMv. reflexivity. }
    assert (ESv : S_desk_counter_valid W' =
                  (if rxdata_dupM X (rxbuf fr n) then M_desk_counter_valid B else 1))
      by (rewrite Sv', Edup, WSv; reflexivity).
    assert (EMc : M_desk_counter W' =
                  (if rxdata_dupM X (rxbuf fr n) then M_desk_counter B else fr_send (rxbuf fr n))).
    { transitivity (M_desk_counter Bm); [fget HmW'|]. rewrite Mc, XMc. reflexivity. }
    assert (ESc : S_desk_counter W' =
                  (if rxdata_dupM X (rxbuf fr n) then S_desk_counter B else fr_send (rxbuf fr n)))
      by (rewrite Sc', Edup, WSc; reflexivity).
    assert (Pv : S_desk_counter_valid W' = M_desk_counter_valid W') by (rewrite ESv, EMv; reflexivity).
    assert (Pv01 : bit01 (M_desk_counter_valid W')).
    { rewrite EMv. destruct (rxdata_dupM X (rxbuf fr n)); cbv beta iota;
        [exact (b6_valid01 _ Hst) | right; reflexivity]. }
    assert (Pc : M_desk_counter_valid W' = 1 -> S_desk_counter W' = M_desk_counter W').
    { rewrite ESc, EMc, EMv. destruct (rxdata_dupM X (rxbuf fr n)); cbv beta iota; intros H1;
        [exact (b6_counter _ Hst H1) | reflexivity]. }
    assert (Pak : OW_acks W' = OW_acks B + 1).
    { transitivity (OW_acks Bm); [fget HmW'|].
      transitivity (OW_acks (rxdata_mB4 X (fr_retry (rxbuf fr n)) (OW_acks B + 1))); [fget Hfm | exact Ak4]. }
    assert (EON : OW_ndata W' =
                  (if rxdata_dupM X (rxbuf fr n) || fr_keepalive (rxbuf fr n) then OW_ndata B else OW_ndata B + 1))
      by (transitivity (OW_ndata Bm); [fget HmW' | exact Mn]).
    assert (Pnd : GOT_ndata W' = OW_ndata W') by (rewrite Gn', EON, Edup; reflexivity).
    assert (Pndr : OW_ndata B <= OW_ndata W' <= OW_ndata B + 1).
    { rewrite EON. destruct (rxdata_dupM X (rxbuf fr n) || fr_keepalive (rxbuf fr n)); clear - Rnd; lia. }
    assert (Hall' : wframe (in_rs rxdata_RS) B W') by exact Hall.
    destruct (rxdata_post I ops B W' Hcore Hroom Hk1 Hall' Pdk Pdm Plr Plu Pbo Pbl Pv Pv01 Pc Fn' Pak Ga' Pnd Pndr)
      as (Hc' & Hog' & Hstep).
    constructor.
    + constructor; [exact Hc' | exact Hog' | fget HfL | fget HfL | fget HfL | fget HfL | fget HfL].
    + exact Hstep.
    + fget HfL.
    + (* a data frame is not the announce that wakes *)
      unfold rx_wake_buf. intros [Hw _]. exfalso. rewrite Hc in Hw. vm_compute in Hw. discriminate Hw.
Qed.

Lemma rx_data : forall (HL : links), rx_branch cond_data.
Proof. intros HL. exact (rx_branch_of_g cond_data (rx_data_g HL)). Qed.
