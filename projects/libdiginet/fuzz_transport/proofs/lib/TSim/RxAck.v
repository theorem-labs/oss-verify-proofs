(* A frame from the desk whose command is a0 (ACK). After `M.last_rx = g_now` (FT:301) the model takes the ack
   when its frame is in flight and the ack names its counter (FT:332-342): OW.acked++, OW.acked_counter /
   acked_retry, the flight off, and in WAKING M.e2_acked = 1 and m_maybe_online (FT:237-243), which goes ONLINE
   (m_set, FT:196-207) once the e1 named the host. The library, after its rx_frames / last_rx_us (DS:296-297),
   does the same (on_ack, DS:223-237): the flight off, the N_ACKED notice (FT:951-953, check_inflight_acked
   FT:476-484), and in WAKING wake_acked = 1 and maybe_online (DS:176-182), whose N_STATE notice (FT:941-949)
   logs the transition in GOT.t[GOT.n] and checks check_state_online (FT:497-505) on the model's flags. An ack
   for no frame in flight is ignored by the model and counted by the library (DS:225-227). The flight is on
   only in WAKING or ONLINE (B8). An unknown desk only passes the filters with e0 / e1 (FT:291-293,
   DS:286-288), so here the desk is known on both sides.
   Any reception of the operation (rx_pre_g, RxBase.v): OW and GOT agree on entry, with a = OW.acked = GOT.acked
   at most 1 and k = OW.n = GOT.n at most 4. The ack takes both acked counts to a + 1, and the transition to
   ONLINE is logged at index k on both sides (FT:200-206, FT:942-947). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SimLib QueueFacts RxDefs RxBase
  RxList RxFrame RxW RxCore.
Import ListNotations.
Open Scope Z_scope.

(* the world functions stay folded for the unifier (RxW.v header); the getters unfold to them *)
Local Opaque sub upd u_at s32_at put.

Definition cond_ack (B buf : list byte) : Prop := fr_cmd buf = DIGINET_CMD_ACK.

(* the read of an 8-byte cell that holds a u64 value (what wget leaves on `M_next_ka` / `S_next_keepalive_us`) *)
Ltac rxack_mod64 := lazymatch goal with
  | |- ?x mod 2 ^ (8 * Z.of_nat 8) = ?y => wis x y; apply rw_mod_id; unfold u64;
      change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); apply Z.mod_pos_bound; wcl
  end.

(* wget / wlen / fget_in for writes and reads at an index (k, i) that is a variable: an open offset side goal
   goes to lia (wnum's vm_compute on an open offset is slow); a closed one keeps the computation *)
Ltac rxack_closed := match goal with |- context [?v] => is_var v; fail 1 | _ => idtac end.
Ltac rxack_num := wlenput; wunf_off; first [rxack_closed; wcl | wclear; lia].
Ltac rxack_len_go := lazymatch goal with
  | |- length (upd ?B ?k ?v) = WN => apply rw_len; [rxack_len_go | rxack_num | rxack_num]
  | |- length ?B = WN => assumption
  end.
Ltac rxack_len := wunf_set; rxack_len_go.
Ltac rxack_sd := first [ rxack_len
                       | lazymatch goal with |- length _ = _ => wlenput; first [reflexivity | assumption] end
                       | rxack_num ].
Ltac rxack_r1 := match goal with
  | |- context [s32_at (upd ?B ?k ?v) ?j] =>
      first [ wis k j; lazymatch v with put 4 ?x => rewrite (rw_s_p B k x) by rxack_sd end
            | rewrite (rw_s_d B k v j) by rxack_sd ]
  | |- context [u_at (upd ?B ?k ?v) ?j ?n] =>
      first [ wis k j; lazymatch v with put ?m ?x => wis m n; rewrite (rw_u_p B k n x) by rxack_sd end
            | rewrite (rw_u_d B k v j n) by rxack_sd ]
  | |- context [sub (upd ?B ?k ?v) ?j ?n] =>
      first [ wis k j; rewrite (rw_sub_p B k v n) by rxack_sd
            | rewrite (rw_sub_d B k v j n) by rxack_sd ]
  end.
Ltac rxack_get := wunf_get; wunf_set; repeat rxack_r1;
  first [ wsyn
        | rewrite rw_swrap_id; [wsyn | wclear; lia]
        | rewrite rw_mod_id; [wsyn | first [apply rw_u_range | wclear; cbn; lia]]
        | idtac ].
Ltac rxack_fin H Hd := wunf_get; apply (fr_s _ _ _ _ H);
  [rxack_num | apply (disj_rs_sub _ _ _ _ _ Hd); wunf_off; wclear; lia].

(* x + 1 in int for a count of one reception (INT_MAX is far): OW.acked++ (FT:334), OW.n++ (FT:205), GOT.n++
   (FT:947), GOT.acked++ (FT:952) *)
Lemma rxack_int_inc : forall x, 0 <= x <= 8 -> int_inc x = Some (x + 1).
Proof.
  intros x Hx. unfold int_inc, INT_MAX. destruct (Z.eqb_spec x (2 ^ 31 - 1)) as [E | E]; [exfalso; lia | reflexivity].
Qed.

(* OW.t and GOT.t, entry by entry, across a frame that misses both logs *)
Lemma rxack_t_fr : forall rs X Y, wframe (in_rs rs) X Y ->
  disj_rs (A_GOT_t_state 0) 192 rs = true -> disj_rs (A_OW_t_state 0) 192 rs = true ->
  forall i, 0 <= i < TRANS_MAX ->
  GOT_t_state Y i = GOT_t_state X i /\ GOT_t_old Y i = GOT_t_old X i /\ GOT_t_reason Y i = GOT_t_reason X i /\
  OW_t_state Y i = OW_t_state X i /\ OW_t_old Y i = OW_t_old X i /\ OW_t_reason Y i = OW_t_reason X i.
Proof.
  intros rs X Y H Hg Ho i Hi. unfold TRANS_MAX in Hi.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
    [rxack_fin H Hg | rxack_fin H Hg | rxack_fin H Hg | rxack_fin H Ho | rxack_fin H Ho | rxack_fin H Ho].
Qed.

(* ---- the model: the ACK arm (FT:332-342) on X = the world after FT:301 ---- *)

(* FT:334-337: OW.acked = a + 1 (a = OW.acked at the reception), the flight's counter and retries, the flight
   off *)
Definition rxack_mA (X : list byte) (a : Z) : list byte :=
  set_M_fly_on (set_OW_acked_retry (set_OW_acked_counter (set_OW_acked X (a + 1)) (M_fly_counter X))
    (M_fly_retries X)) 0.

(* FT:339, in WAKING *)
Definition rxack_mE (X : list byte) (a : Z) : list byte := set_M_e2_acked (rxack_mA X a) 1.

(* FT:240-241: m_maybe_online, then m_set (ONLINE, R_ONLINE) from WAKING, logged in OW.t[k] with k = OW.n
   (FT:200-206) *)
Definition rxack_mO (X : list byte) (a k : Z) : list byte :=
  set_M_state (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state
    (set_M_next_ka (rxack_mE X a) (u64 (M_last_rx X + h_ms_m (Cfg_keepalive_ms X)))) k S_ONLINE) k S_WAKING)
    k R_ONLINE) (k + 1)) S_ONLINE.

Definition rxack_RA : list (Z * Z) := [(A_OW_acked, 4); (A_OW_acked_counter, 4); (A_OW_acked_retry, 4); (A_M_fly_on, 4)].
Definition rxack_RE : list (Z * Z) := rxack_RA ++ [(A_M_e2_acked, 4)].
(* the whole of OW.t (16 entries of 12 bytes), so that the list is closed for every k *)
Definition rxack_RO : list (Z * Z) :=
  rxack_RE ++ [(A_M_next_ka, 8); (A_OW_t_state 0, 192); (A_OW_n, 4); (A_M_state, 4)].

(* FT:333 false: the switch leaves X *)
Lemma rxack_m_none : forall I fr n X,
  sf_cmd (spec_read_frame (zs (tf_bytes fr)) n) = SPEC_CMD_ACK ->
  (truth (M_fly_on X) && (sf_ack (spec_read_frame (zs (tf_bytes fr)) n) =? M_fly_counter X)) = false ->
  m_rx_sw I fr n X = Some (X, tt).
Proof.
  intros I fr n X Hc Ht. unfold m_rx_sw. cbv zeta. rewrite Hc, Ht.
  change ((SPEC_CMD_ACK =? SPEC_CMD_E0) || (SPEC_CMD_ACK =? SPEC_CMD_E1)) with false.
  change (SPEC_CMD_ACK =? SPEC_CMD_ACK) with true.
  cbv beta iota. reflexivity.
Qed.

(* FT:333 true: FT:334-337, then the state test of FT:338 *)
Lemma rxack_m_sw : forall I fr n X a, length X = WN ->
  sf_cmd (spec_read_frame (zs (tf_bytes fr)) n) = SPEC_CMD_ACK ->
  M_fly_on X = 1 -> sf_ack (spec_read_frame (zs (tf_bytes fr)) n) = M_fly_counter X ->
  OW_acked X = a -> 0 <= a <= 1 ->
  m_rx_sw I fr n X = if M_state X =? S_WAKING then m_maybe_online_m (rxack_mE X a) else Some (rxack_mA X a, tt).
Proof.
  intros I fr n X a HX Hc Hon Hk Ha Har. unfold m_rx_sw. cbv zeta.
  rewrite Hc, Hon, Hk, (Z.eqb_refl (M_fly_counter X)), Ha.
  rewrite (rxack_int_inc a) by lia.
  change ((SPEC_CMD_ACK =? SPEC_CMD_E0) || (SPEC_CMD_ACK =? SPEC_CMD_E1)) with false.
  change (SPEC_CMD_ACK =? SPEC_CMD_ACK) with true.
  change (truth 1 && true) with true.
  cbv beta iota.
  assert (G1 : M_fly_counter (set_OW_acked X (a + 1)) = M_fly_counter X) by wget.
  rewrite G1.
  assert (G2 : M_fly_retries (set_OW_acked_counter (set_OW_acked X (a + 1)) (M_fly_counter X)) = M_fly_retries X)
    by wget.
  rewrite G2.
  assert (G3 : M_state (set_M_fly_on (set_OW_acked_retry (set_OW_acked_counter (set_OW_acked X (a + 1))
                 (M_fly_counter X)) (M_fly_retries X)) 0) = M_state X) by wget.
  rewrite G3. unfold rxack_mE, rxack_mA. reflexivity.
Qed.

(* FT:239-241 with the e1 named: ONLINE, logged at k = OW.n (FT:200-206) *)
Lemma rxack_m_online : forall X a k, length X = WN -> M_state X = S_WAKING -> M_e1_us X = 1 -> OW_n X = k ->
  0 <= k <= 4 -> m_maybe_online_m (rxack_mE X a) = Some (rxack_mO X a k, tt).
Proof.
  intros X a k HX Hs He Hn Hk.
  assert (HE : length (rxack_mE X a) = WN) by (unfold rxack_mE, rxack_mA; wlen).
  assert (G1 : M_state (rxack_mE X a) = S_WAKING)
    by (transitivity (M_state X); [unfold rxack_mE, rxack_mA; wget | exact Hs]).
  assert (G2 : M_e2_acked (rxack_mE X a) = 1) by (unfold rxack_mE, rxack_mA; wget).
  assert (G3 : M_e1_us (rxack_mE X a) = 1)
    by (transitivity (M_e1_us X); [unfold rxack_mE, rxack_mA; wget | exact He]).
  assert (G4 : M_last_rx (rxack_mE X a) = M_last_rx X) by (unfold rxack_mE, rxack_mA; wget).
  assert (G5 : Cfg_keepalive_ms (rxack_mE X a) = Cfg_keepalive_ms X) by (unfold rxack_mE, rxack_mA; wget).
  assert (G6 : OW_n (rxack_mE X a) = k) by (transitivity (OW_n X); [unfold rxack_mE, rxack_mA; wget | exact Hn]).
  unfold m_maybe_online_m. rewrite G1, G2, G3, G4, G5.
  change ((S_WAKING =? S_WAKING) && truth 1 && truth 1) with true.
  cbv beta iota zeta.
  unfold m_set_m. cbv zeta.
  assert (G7 : M_state (set_M_next_ka (rxack_mE X a) (u64 (M_last_rx X + h_ms_m (Cfg_keepalive_ms X)))) = S_WAKING)
    by (transitivity (M_state (rxack_mE X a)); [wget | exact G1]).
  assert (G8 : OW_n (set_M_next_ka (rxack_mE X a) (u64 (M_last_rx X + h_ms_m (Cfg_keepalive_ms X)))) = k)
    by (transitivity (OW_n (rxack_mE X a)); [wget | exact G6]).
  rewrite G7, G8.
  change (S_WAKING =? S_ONLINE) with false.
  rewrite (proj2 (Z.ltb_lt k TRANS_MAX)) by (unfold TRANS_MAX; lia).
  rewrite (proj2 (Z.ltb_ge k 0)) by lia.
  rewrite (rxack_int_inc k) by lia.
  cbv beta iota. unfold rxack_mO. reflexivity.
Qed.

(* FT:239 with the e1 not yet named: nothing more *)
Lemma rxack_m_wait : forall X a, length X = WN -> M_e1_us X = 0 ->
  m_maybe_online_m (rxack_mE X a) = Some (rxack_mE X a, tt).
Proof.
  intros X a HX He. unfold m_maybe_online_m.
  assert (G : M_e1_us (rxack_mE X a) = 0)
    by (transitivity (M_e1_us X); [unfold rxack_mE, rxack_mA; wget | exact He]).
  rewrite G. change (truth 0) with false.
  rewrite (andb_false_r ((M_state (rxack_mE X a) =? S_WAKING) && truth (M_e2_acked (rxack_mE X a)))).
  cbv beta iota. reflexivity.
Qed.

Lemma rxack_mA_frame : forall X a, length X = WN ->
  wframe (in_rs rxack_RA) X (rxack_mA X a) /\ length (rxack_mA X a) = WN.
Proof. intros X a HX. unfold rxack_mA. split; [unfold rxack_RA; wfrs | wlen]. Qed.

Lemma rxack_mE_frame : forall X a, length X = WN ->
  wframe (in_rs rxack_RE) X (rxack_mE X a) /\ length (rxack_mE X a) = WN.
Proof. intros X a HX. unfold rxack_mE, rxack_mA. split; [unfold rxack_RE, rxack_RA; wfrs | wlen]. Qed.

(* wfrs decides the ranges on closed offsets: one case per k *)
Lemma rxack_mO_frame : forall X a k, length X = WN -> 0 <= k <= 4 ->
  wframe (in_rs rxack_RO) X (rxack_mO X a k) /\ length (rxack_mO X a k) = WN.
Proof.
  intros X a k HX Hk. unfold rxack_mO, rxack_mE, rxack_mA. split; [| rxack_len].
  unfold rxack_RO, rxack_RE, rxack_RA.
  assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
  destruct E as [E | [E | [E | [E | E]]]]; subst k; wfrs.
Qed.

Lemma rxack_mA_get : forall X a, length X = WN -> 0 <= a <= 1 ->
  M_fly_on (rxack_mA X a) = 0 /\ OW_acked (rxack_mA X a) = a + 1 /\
  OW_acked_counter (rxack_mA X a) = M_fly_counter X /\ OW_acked_retry (rxack_mA X a) = M_fly_retries X.
Proof. intros X a HX Ha. unfold rxack_mA. refine (conj _ (conj _ (conj _ _))); wget. Qed.

Lemma rxack_mE_get : forall X a, length X = WN -> 0 <= a <= 1 ->
  M_fly_on (rxack_mE X a) = 0 /\ OW_acked (rxack_mE X a) = a + 1 /\
  OW_acked_counter (rxack_mE X a) = M_fly_counter X /\ OW_acked_retry (rxack_mE X a) = M_fly_retries X /\
  M_e2_acked (rxack_mE X a) = 1.
Proof. intros X a HX Ha. unfold rxack_mE, rxack_mA. refine (conj _ (conj _ (conj _ (conj _ _)))); wget. Qed.

Lemma rxack_mO_get : forall X a k, length X = WN -> 0 <= a <= 1 -> 0 <= k <= 4 ->
  M_fly_on (rxack_mO X a k) = 0 /\ OW_acked (rxack_mO X a k) = a + 1 /\
  OW_acked_counter (rxack_mO X a k) = M_fly_counter X /\ OW_acked_retry (rxack_mO X a k) = M_fly_retries X /\
  M_e2_acked (rxack_mO X a k) = 1 /\
  M_next_ka (rxack_mO X a k) = u64 (M_last_rx X + h_ms_m (Cfg_keepalive_ms X)) /\
  M_state (rxack_mO X a k) = S_ONLINE /\ OW_n (rxack_mO X a k) = k + 1 /\
  OW_t_state (rxack_mO X a k) k = S_ONLINE /\ OW_t_old (rxack_mO X a k) k = S_WAKING /\
  OW_t_reason (rxack_mO X a k) k = R_ONLINE.
Proof.
  intros X a k HX Ha Hk. unfold rxack_mO, rxack_mE, rxack_mA, S_ONLINE, S_WAKING, R_ONLINE.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))));
    rxack_get; try rxack_mod64.
Qed.

(* the log entries the model's transition leaves: all of GOT.t, and OW.t below k *)
Lemma rxack_mO_t : forall X a k, length X = WN -> 0 <= k <= 4 -> forall i, 0 <= i < TRANS_MAX ->
  GOT_t_state (rxack_mO X a k) i = GOT_t_state X i /\ GOT_t_old (rxack_mO X a k) i = GOT_t_old X i /\
  GOT_t_reason (rxack_mO X a k) i = GOT_t_reason X i /\
  (i < k -> OW_t_state (rxack_mO X a k) i = OW_t_state X i /\ OW_t_old (rxack_mO X a k) i = OW_t_old X i /\
            OW_t_reason (rxack_mO X a k) i = OW_t_reason X i).
Proof.
  intros X a k HX Hk i Hi. unfold TRANS_MAX in Hi. unfold rxack_mO, rxack_mE, rxack_mA.
  refine (conj _ (conj _ (conj _ _))); [rxack_get | rxack_get | rxack_get |].
  intros Hik. refine (conj _ (conj _ _)); rxack_get.
Qed.

(* ---- the library: on_ack (DS:223-237) on W = the world the switch starts from ---- *)

(* DS:229-232: the flight off, the N_ACKED notice (GOT.acked = a + 1, a = GOT.acked at the reception) *)
Definition rxack_sA (W : list byte) (a : Z) : list byte := set_GOT_acked (set_S_inflight W 0) (a + 1).

(* DS:234, in WAKING *)
Definition rxack_sE (W : list byte) (a : Z) : list byte := set_S_wake_acked (rxack_sA W a) 1.

(* DS:179-180: maybe_online, set_state (ONLINE, R_ONLINE) from WAKING, its N_STATE notice logged in GOT.t[k]
   with k = GOT.n (FT:942-947) *)
Definition rxack_sO (W : list byte) (a k : Z) : list byte :=
  set_GOT_n (set_GOT_t_reason (set_GOT_t_old (set_GOT_t_state
    (set_S_state (set_S_next_keepalive_us (rxack_sE W a) (u64 (S_last_rx_us W + ms_m (S_cfg_keepalive_ms W))))
      DIGINET_S_ONLINE) k DIGINET_S_ONLINE) k DIGINET_S_WAKING) k DIGINET_R_ONLINE) (k + 1).

Definition rxack_SA : list (Z * Z) := [(A_S_inflight, 4); (A_GOT_acked, 4)].
Definition rxack_SE : list (Z * Z) := rxack_SA ++ [(A_S_wake_acked, 4)].
(* the whole of GOT.t, as in rxack_RO *)
Definition rxack_SO : list (Z * Z) :=
  rxack_SE ++ [(A_S_next_keepalive_us, 8); (A_S_state, 4); (A_GOT_t_state 0, 192); (A_GOT_n, 4)].

(* DS:225 false: DS:229-232 (check_inflight_acked passes, FT:482-483, with OW.acked = GOT.acked = a + 1),
   then the state test of DS:233 *)
Lemma rxack_s_ack : forall I F W buf a, length W = WN -> S_inflight W = 1 -> fr_ack buf = S_inflight_counter W ->
  S_notify W = ti_notice I -> GOT_acked W = a -> OW_acked W = a + 1 -> 0 <= a <= 1 ->
  OW_acked_counter W = fr_ack buf -> OW_acked_retry W = u16 (S_inflight_retries W) ->
  on_ack_m I F W buf =
  if S_state W =? DIGINET_S_WAKING then maybe_online_m I F (rxack_sE W a) else Some (rxack_sA W a, tt).
Proof.
  intros I F W buf a HW Hi Hc Hno Hg Ha Har Hac Hrt.
  assert (T : ((S_inflight W =? 0) || negb (fr_ack buf =? S_inflight_counter W)) = false)
    by (rewrite Hi, Hc, (Z.eqb_refl (S_inflight_counter W)); reflexivity).
  unfold on_ack_m. rewrite T. cbv beta iota zeta.
  unfold call_notify.
  assert (N1 : S_notify (set_S_inflight W 0) = ti_notice I) by (transitivity (S_notify W); [wget | exact Hno]).
  rewrite N1, (Z.eqb_refl (ti_notice I)). cbv beta iota.
  unfold notice_m. cbv beta zeta. cbn [n_kind].
  change (DIGINET_N_ACKED =? N_STATE) with false. change (DIGINET_N_ACKED =? N_ACKED) with true.
  cbv beta iota.
  assert (N2 : GOT_acked (set_S_inflight W 0) = a) by (transitivity (GOT_acked W); [wget | exact Hg]).
  rewrite N2. rewrite (rxack_int_inc a) by lia. cbv beta iota.
  unfold check_inflight_acked_m. cbn [n_counter n_retry].
  assert (K1 : OW_acked (set_GOT_acked (set_S_inflight W 0) (a + 1)) = a + 1)
    by (transitivity (OW_acked W); [wget | exact Ha]).
  assert (K2 : GOT_acked (set_GOT_acked (set_S_inflight W 0) (a + 1)) = a + 1) by wget.
  assert (K3 : OW_acked_counter (set_GOT_acked (set_S_inflight W 0) (a + 1)) = fr_ack buf)
    by (transitivity (OW_acked_counter W); [wget | exact Hac]).
  assert (K4 : OW_acked_retry (set_GOT_acked (set_S_inflight W 0) (a + 1)) = u16 (S_inflight_retries W))
    by (transitivity (OW_acked_retry W); [wget | exact Hrt]).
  assert (K5 : S_inflight_retries (set_S_inflight W 0) = S_inflight_retries W) by wget.
  rewrite K1, K2, K3, K4, K5, Z.ltb_irrefl, (Z.eqb_refl (fr_ack buf)), (Z.eqb_refl (u16 (S_inflight_retries W))).
  change (false || negb true || negb true) with false.
  cbv beta iota.
  assert (K6 : S_state (set_GOT_acked (set_S_inflight W 0) (a + 1)) = S_state W) by wget.
  rewrite K6. unfold rxack_sE, rxack_sA. reflexivity.
Qed.

(* DS:178-180 with the e1 named: ONLINE, the N_STATE notice logged at k = GOT.n (FT:942-947), check_state_online
   on the model's flags *)
Lemma rxack_s_online : forall I F W a k, length W = WN -> S_state W = DIGINET_S_WAKING -> S_e1_named_us W = 1 ->
  S_notify W = ti_notice I -> GOT_n W = k -> 0 <= k <= 4 -> M_e2_acked W = 1 -> M_e1_us W = 1 ->
  maybe_online_m I F (rxack_sE W a) = Some (rxack_sO W a k, tt).
Proof.
  intros I F W a k HW Hs He Hno Hg Hk Hm2 Hm1.
  assert (HE : length (rxack_sE W a) = WN) by (unfold rxack_sE, rxack_sA; wlen).
  assert (G1 : S_state (rxack_sE W a) = DIGINET_S_WAKING)
    by (transitivity (S_state W); [unfold rxack_sE, rxack_sA; wget | exact Hs]).
  assert (G2 : S_wake_acked (rxack_sE W a) = 1) by (unfold rxack_sE, rxack_sA; wget).
  assert (G3 : S_e1_named_us (rxack_sE W a) = 1)
    by (transitivity (S_e1_named_us W); [unfold rxack_sE, rxack_sA; wget | exact He]).
  assert (G4 : S_last_rx_us (rxack_sE W a) = S_last_rx_us W) by (unfold rxack_sE, rxack_sA; wget).
  assert (G5 : S_cfg_keepalive_ms (rxack_sE W a) = S_cfg_keepalive_ms W) by (unfold rxack_sE, rxack_sA; wget).
  assert (G6 : S_notify (rxack_sE W a) = ti_notice I)
    by (transitivity (S_notify W); [unfold rxack_sE, rxack_sA; wget | exact Hno]).
  assert (G7 : GOT_n (rxack_sE W a) = k)
    by (transitivity (GOT_n W); [unfold rxack_sE, rxack_sA; wget | exact Hg]).
  assert (G8 : M_e2_acked (rxack_sE W a) = 1)
    by (transitivity (M_e2_acked W); [unfold rxack_sE, rxack_sA; wget | exact Hm2]).
  assert (G9 : M_e1_us (rxack_sE W a) = 1)
    by (transitivity (M_e1_us W); [unfold rxack_sE, rxack_sA; wget | exact Hm1]).
  unfold maybe_online_m. rewrite G1, G2, G3.
  change ((DIGINET_S_WAKING =? DIGINET_S_WAKING) && negb (1 =? 0) && negb (1 =? 0)) with true.
  cbv beta iota zeta.
  rewrite G4, G5.
  remember (set_S_next_keepalive_us (rxack_sE W a) (u64 (S_last_rx_us W + ms_m (S_cfg_keepalive_ms W)))) as W4 eqn:EW4.
  unfold set_state_m.
  assert (H4s : S_state W4 = DIGINET_S_WAKING)
    by (subst W4; transitivity (S_state (rxack_sE W a)); [wget | exact G1]).
  rewrite H4s. change (DIGINET_S_WAKING =? DIGINET_S_ONLINE) with false. cbv beta iota zeta.
  unfold call_notify.
  assert (H4n : S_notify (set_S_state W4 DIGINET_S_ONLINE) = ti_notice I)
    by (subst W4; transitivity (S_notify (rxack_sE W a)); [wget | exact G6]).
  rewrite H4n, (Z.eqb_refl (ti_notice I)). cbv beta iota.
  unfold notice_m. cbv beta zeta. cbn [n_kind n_state n_old n_reason].
  change (DIGINET_N_STATE =? N_STATE) with true. cbv beta iota zeta.
  assert (H4g : GOT_n (set_S_state W4 DIGINET_S_ONLINE) = k)
    by (subst W4; transitivity (GOT_n (rxack_sE W a)); [wget | exact G7]).
  rewrite H4g.
  rewrite (proj2 (Z.ltb_lt k TRANS_MAX)) by (unfold TRANS_MAX; lia).
  rewrite (proj2 (Z.ltb_ge k 0)) by lia.
  rewrite (rxack_int_inc k) by lia.
  change (DIGINET_S_ONLINE =? S_ONLINE) with true.
  cbv beta iota.
  assert (HO1 : M_e2_acked (set_GOT_n (set_GOT_t_reason (set_GOT_t_old (set_GOT_t_state
                  (set_S_state W4 DIGINET_S_ONLINE) k DIGINET_S_ONLINE) k DIGINET_S_WAKING) k DIGINET_R_ONLINE)
                  (k + 1)) = 1)
    by (subst W4; transitivity (M_e2_acked (rxack_sE W a)); [rxack_get | exact G8]).
  assert (HO2 : M_e1_us (set_GOT_n (set_GOT_t_reason (set_GOT_t_old (set_GOT_t_state
                  (set_S_state W4 DIGINET_S_ONLINE) k DIGINET_S_ONLINE) k DIGINET_S_WAKING) k DIGINET_R_ONLINE)
                  (k + 1)) = 1)
    by (subst W4; transitivity (M_e1_us (rxack_sE W a)); [rxack_get | exact G9]).
  rewrite (check_state_online_ok _ HO1 HO2). subst W4. unfold rxack_sO. reflexivity.
Qed.

(* DS:178 with the e1 not yet named: nothing more *)
Lemma rxack_s_wait : forall I F W a, length W = WN -> S_e1_named_us W = 0 ->
  maybe_online_m I F (rxack_sE W a) = Some (rxack_sE W a, tt).
Proof.
  intros I F W a HW He. unfold maybe_online_m.
  assert (G : S_e1_named_us (rxack_sE W a) = 0)
    by (transitivity (S_e1_named_us W); [unfold rxack_sE, rxack_sA; wget | exact He]).
  rewrite G. change (negb (0 =? 0)) with false.
  rewrite (andb_false_r ((S_state (rxack_sE W a) =? DIGINET_S_WAKING) && negb (S_wake_acked (rxack_sE W a) =? 0))).
  cbv beta iota. reflexivity.
Qed.

Lemma rxack_sA_frame : forall W a, length W = WN ->
  wframe (in_rs rxack_SA) W (rxack_sA W a) /\ length (rxack_sA W a) = WN.
Proof. intros W a HW. unfold rxack_sA. split; [unfold rxack_SA; wfrs | wlen]. Qed.

Lemma rxack_sE_frame : forall W a, length W = WN ->
  wframe (in_rs rxack_SE) W (rxack_sE W a) /\ length (rxack_sE W a) = WN.
Proof. intros W a HW. unfold rxack_sE, rxack_sA. split; [unfold rxack_SE, rxack_SA; wfrs | wlen]. Qed.

(* one case per k, as rxack_mO_frame *)
Lemma rxack_sO_frame : forall W a k, length W = WN -> 0 <= k <= 4 ->
  wframe (in_rs rxack_SO) W (rxack_sO W a k) /\ length (rxack_sO W a k) = WN.
Proof.
  intros W a k HW Hk. unfold rxack_sO, rxack_sE, rxack_sA. split; [| rxack_len].
  unfold rxack_SO, rxack_SE, rxack_SA.
  assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
  destruct E as [E | [E | [E | [E | E]]]]; subst k; wfrs.
Qed.

Lemma rxack_sA_get : forall W a, length W = WN -> 0 <= a <= 1 ->
  S_inflight (rxack_sA W a) = 0 /\ GOT_acked (rxack_sA W a) = a + 1.
Proof. intros W a HW Ha. unfold rxack_sA. split; wget. Qed.

Lemma rxack_sE_get : forall W a, length W = WN -> 0 <= a <= 1 ->
  S_inflight (rxack_sE W a) = 0 /\ GOT_acked (rxack_sE W a) = a + 1 /\ S_wake_acked (rxack_sE W a) = 1.
Proof. intros W a HW Ha. unfold rxack_sE, rxack_sA. refine (conj _ (conj _ _)); wget. Qed.

Lemma rxack_sO_get : forall W a k, length W = WN -> 0 <= a <= 1 -> 0 <= k <= 4 ->
  S_inflight (rxack_sO W a k) = 0 /\ GOT_acked (rxack_sO W a k) = a + 1 /\ S_wake_acked (rxack_sO W a k) = 1 /\
  S_next_keepalive_us (rxack_sO W a k) = u64 (S_last_rx_us W + ms_m (S_cfg_keepalive_ms W)) /\
  S_state (rxack_sO W a k) = DIGINET_S_ONLINE /\ GOT_n (rxack_sO W a k) = k + 1 /\
  GOT_t_state (rxack_sO W a k) k = DIGINET_S_ONLINE /\ GOT_t_old (rxack_sO W a k) k = DIGINET_S_WAKING /\
  GOT_t_reason (rxack_sO W a k) k = DIGINET_R_ONLINE.
Proof.
  intros W a k HW Ha Hk.
  unfold rxack_sO, rxack_sE, rxack_sA, DIGINET_S_ONLINE, DIGINET_S_WAKING, DIGINET_R_ONLINE.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); rxack_get; try rxack_mod64.
Qed.

(* the log entries the library's transition leaves: all of OW.t, and GOT.t below k *)
Lemma rxack_sO_t : forall W a k, length W = WN -> 0 <= k <= 4 -> forall i, 0 <= i < TRANS_MAX ->
  OW_t_state (rxack_sO W a k) i = OW_t_state W i /\ OW_t_old (rxack_sO W a k) i = OW_t_old W i /\
  OW_t_reason (rxack_sO W a k) i = OW_t_reason W i /\
  (i < k -> GOT_t_state (rxack_sO W a k) i = GOT_t_state W i /\ GOT_t_old (rxack_sO W a k) i = GOT_t_old W i /\
            GOT_t_reason (rxack_sO W a k) i = GOT_t_reason W i).
Proof.
  intros W a k HW Hk i Hi. unfold TRANS_MAX in Hi. unfold rxack_sO, rxack_sE, rxack_sA.
  refine (conj _ (conj _ (conj _ _))); [rxack_get | rxack_get | rxack_get |].
  intros Hik. refine (conj _ (conj _ _)); rxack_get.
Qed.

(* ---- after the switch ---- *)

(* m_tick (FT:246-252) after the ACK arm: nothing overdue (the state is B's, or ONLINE with last_rx = now) *)
Lemma rxack_tick : forall ops B Bm, agree_cfg B -> agree_time ops B ->
  (M_state Bm = M_state B \/ M_state Bm = S_ONLINE) ->
  M_last_rx Bm = g_now B -> M_wake_sent Bm = M_wake_sent B -> g_now Bm = g_now B ->
  Cfg_wake_timeout_ms Bm = Cfg_wake_timeout_ms B -> Cfg_offline_ms Bm = Cfg_offline_ms B ->
  m_tick_m Bm = Some (Bm, tt).
Proof.
  intros ops B Bm Hcfg Htime Hs Hlr Hws Hnw Hcw Hco. apply m_tick_quiet.
  - intros Hw. rewrite Hws, Hnw, Hcw.
    assert (Hb : M_state B = S_WAKING).
    { destruct Hs as [E | E]; rewrite E in Hw; [exact Hw | unfold S_ONLINE, S_WAKING in Hw; discriminate Hw]. }
    split; [exact (c1_wake_sent _ _ Htime) | exact (c2_wake _ _ Htime Hb)].
  - intros _. rewrite Hlr, Hnw, Hco, (Z.sub_diag (g_now B)). pose proof (a1_offline _ Hcfg) as Ho.
    split; [apply Z.le_refl | clear - Ho; lia].
  - rewrite Hcw. exact (proj2 (a1_wake_timeout _ Hcfg)).
  - rewrite Hco. exact (proj2 (a1_offline _ Hcfg)).
Qed.

(* the keepalive deadline ONLINE sets (FT:240 / DS:179) is within C1's bound: now < 2^47, ka <= 65536 *)
Lemma rxack_ka_le : forall now ka, 0 <= now <= 1000000 + 1024 * 65535000000 -> 0 <= ka <= 65536 ->
  u64 (now + u64 (ka * 1000)) <= now + 65536000.
Proof.
  intros now ka Hn Hk. unfold u64.
  rewrite (Z.mod_small (ka * 1000) (2 ^ 64)) by lia.
  rewrite (Z.mod_small (now + ka * 1000) (2 ^ 64)) by lia.
  lia.
Qed.

(* every range an accepted ack writes, on either side, with the prologue's *)
Definition rxack_R : list (Z * Z) := ((R_learn ++ [(A_M_last_rx, 8)]) ++ rxack_RO) ++ (R_start ++ rxack_SO).

(* agree_core, ow_got_eq and the step after an accepted ack, from the fields it moves: OW.acked and GOT.acked
   go from OW.acked B to OW.acked B + 1, OW.n = GOT.n grows by at most one, and the logs agree below it *)
Lemma rxack_post : forall I ops B W',
  agree_core I ops B -> ow_room B -> wframe (in_rs rxack_R) B W' ->
  M_desk_known W' = 1 -> S_desk_known W' = 1 -> S_desk_mac W' = M_desk W' ->
  M_last_rx W' = g_now B -> S_last_rx_us W' = g_now B ->
  S_state W' = M_state W' -> (M_state W' = M_state B \/ M_state W' = S_ONLINE) ->
  S_wake_acked W' = M_e2_acked W' -> bit01 (M_e2_acked W') ->
  (g_raw B = 0 -> S_next_keepalive_us W' = M_next_ka W' /\ M_next_ka W' <= g_now B + 65536000) ->
  M_fly_on W' = 0 -> S_inflight W' = 0 ->
  GOT_n W' = OW_n W' -> OW_n B <= OW_n W' <= OW_n B + 1 ->
  (forall i, 0 <= i < OW_n W' -> i < TRANS_MAX ->
     GOT_t_state W' i = OW_t_state W' i /\ GOT_t_old W' i = OW_t_old W' i /\ GOT_t_reason W' i = OW_t_reason W' i) ->
  OW_acked W' = OW_acked B + 1 -> GOT_acked W' = OW_acked B + 1 ->
  agree_core I ops W' /\ ow_got_eq W' /\ ow_step B W'.
Proof.
  intros I ops B W' Hcore Hroom Hall Wdk Wsk Wdm Wlr Wsl Wss Wst Wwa We2 Wka Wfo Wsi Wgn Wn Wt Woa Wga.
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  destruct Hroom as [Hog Rn R2 R3 R4 R5 R6 R7 R8].
  assert (Hrange : 0 <= M_state W' <= 3).
  { destruct Wst as [E | E]; rewrite E; [exact (b1_state_range _ Hst) | unfold S_ONLINE; wcl]. }
  assert (Hwk : M_state W' = S_WAKING -> M_state B = S_WAKING).
  { intros H. destruct Wst as [E | E]; rewrite E in H; [exact H | unfold S_ONLINE, S_WAKING in H; discriminate H]. }
  clear Wst.
  (* the fields nobody wrote *)
  assert (U3 : S_foreign W' = S_foreign B) by fget Hall.
  assert (U4 : M_foreign W' = M_foreign B) by fget Hall.
  assert (U5 : S_e1_named_us W' = S_e1_named_us B) by fget Hall.
  assert (U6 : M_e1_us W' = M_e1_us B) by fget Hall.
  assert (U9 : S_wake_sent_us W' = S_wake_sent_us B) by fget Hall.
  assert (U10 : M_wake_sent W' = M_wake_sent B) by fget Hall.
  assert (U11 : S_backoff_until_us W' = S_backoff_until_us B) by fget Hall.
  assert (U12 : M_backoff_until W' = M_backoff_until B) by fget Hall.
  assert (U13 : g_raw W' = g_raw B) by fget Hall.
  assert (U16 : S_display_sent W' = S_display_sent B) by fget Hall.
  assert (U17 : M_display_sent W' = M_display_sent B) by fget Hall.
  assert (U18 : S_last_display_us W' = S_last_display_us B) by fget Hall.
  assert (U19 : M_last_display W' = M_last_display B) by fget Hall.
  assert (U20 : S_desk_counter_valid W' = S_desk_counter_valid B) by fget Hall.
  assert (U21 : M_desk_counter_valid W' = M_desk_counter_valid B) by fget Hall.
  assert (U22 : S_desk_counter W' = S_desk_counter B) by fget Hall.
  assert (U23 : M_desk_counter W' = M_desk_counter B) by fget Hall.
  assert (U24 : S_host_counter W' = S_host_counter B) by fget Hall.
  assert (U25 : M_host_counter W' = M_host_counter B) by fget Hall.
  assert (U39 : g_now W' = g_now B) by fget Hall.
  assert (U40 : Cfg_wake_timeout_ms W' = Cfg_wake_timeout_ms B) by fget Hall.
  assert (U41 : Cfg_offline_ms W' = Cfg_offline_ms B) by fget Hall.
  assert (U43 : g_fail_next W' = g_fail_next B) by fget Hall.
  assert (U44 : S_personality W' = S_personality B) by fget Hall.
  (* the counts nobody moved *)
  assert (O2 : OW_e2 W' = OW_e2 B) by fget Hall.
  assert (O3 : OW_e3 W' = OW_e3 B) by fget Hall.
  assert (O4 : OW_acks W' = OW_acks B) by fget Hall.
  assert (O5 : OW_desk W' = OW_desk B) by fget Hall.
  assert (O6 : OW_foreign W' = OW_foreign B) by fget Hall.
  assert (O7 : OW_ndata W' = OW_ndata B) by fget Hall.
  assert (G2 : GOT_e2 W' = GOT_e2 B) by fget Hall.
  assert (G3 : GOT_e3 W' = GOT_e3 B) by fget Hall.
  assert (G4 : GOT_acks W' = GOT_acks B) by fget Hall.
  assert (G5 : GOT_desk W' = GOT_desk B) by fget Hall.
  assert (G6 : GOT_foreign W' = GOT_foreign B) by fget Hall.
  assert (G7 : GOT_ndata W' = GOT_ndata B) by fget Hall.
  assert (Hst' : agree_st W').
  { constructor; rw_eqs W'.
    - reflexivity.
    - exact Hrange.
    - reflexivity.
    - right; reflexivity.
    - intros _; reflexivity.
    - exact (b3_foreign _ Hst).
    - exact (b3_foreign01 _ Hst).
    - exact (b3_e1 _ Hst).
    - exact (b3_e1_01 _ Hst).
    - reflexivity.
    - exact We2.
    - exact (b4_wake_sent _ Hst).
    - reflexivity.
    - exact (b4_backoff _ Hst).
    - intros Hr. exact (proj1 (Wka Hr)).
    - exact (b5_display_sent _ Hst).
    - exact (b5_display_sent01 _ Hst).
    - exact (b5_last_display _ Hst).
    - exact (b6_valid _ Hst).
    - exact (b6_valid01 _ Hst).
    - exact (b6_counter _ Hst).
    - exact (b7_host_counter _ Hst).
    - intros _; reflexivity.
    - intros _; reflexivity. }
  assert (Hfl' : agree_fly W').
  { constructor; rw_eqs W'; [reflexivity | left; reflexivity | intros H; discriminate H ..]. }
  assert (Hti' : agree_time ops W').
  { constructor; rw_eqs W'.
    - exact (c_now _ _ Htime).
    - apply Z.le_refl.
    - exact (c1_wake_sent _ _ Htime).
    - intros H; discriminate H.
    - exact (c1_last_display _ _ Htime).
    - exact (c1_backoff _ _ Htime).
    - intros Hr. exact (proj2 (Wka Hr)).
    - intros H. exact (c2_wake _ _ Htime (Hwk H)).
    - intros _. rewrite (Z.sub_diag (g_now B)). pose proof (a1_offline _ Hcfg) as Ho. clear - Ho. lia.
    - intros H; discriminate H. }
  assert (Hmi' : agree_misc I W').
  { constructor; rw_eqs W'; [exact (e1_fail_next _ _ Hmisc) | exact (e2_personality _ _ Hmisc)]. }
  pose proof (og_n_range _ Hog) as N0.
  pose proof (og_acked_range _ Hog) as A0.
  split; [| split].
  - apply (agree_core_rx I ops B W' Hcore); [| exact Hst' | exact Hfl' | exact Hti' | exact Hmi'].
    eapply wframe_rx; [| exact Hall]. vm_compute. reflexivity.
  - constructor.
    + exact Wgn.
    + slia.
    + exact Wt.
    + rewrite G2, O2. exact (og_e2 _ Hog).
    + rewrite O2. exact (og_e2_range _ Hog).
    + rewrite G3, O3. exact (og_e3 _ Hog).
    + rewrite O3. exact (og_e3_range _ Hog).
    + rewrite G4, O4. exact (og_acks _ Hog).
    + rewrite O4. exact (og_acks_range _ Hog).
    + rewrite G5, O5. exact (og_desk _ Hog).
    + rewrite O5. exact (og_desk_range _ Hog).
    + rewrite G6, O6. exact (og_foreign _ Hog).
    + rewrite O6. exact (og_foreign_range _ Hog).
    + rewrite Wga, Woa. reflexivity.
    + rewrite Woa. slia.
    + rewrite G7, O7. exact (og_ndata _ Hog).
    + rewrite O7. exact (og_ndata_range _ Hog).
  - constructor; [slia | rewrite O2; slia | rewrite O3; slia | rewrite O4; slia | rewrite O5; slia
                 | rewrite O6; slia | rewrite Woa; slia | rewrite O7; slia].
Qed.

(* any reception of the operation (rx_pre_g): an ack for the frame in flight takes OW.acked and GOT.acked from
   a to a + 1 and may log ONLINE at index k = OW.n = GOT.n; an ack for no frame in flight moves no OW or GOT
   count. An ack is no e0, so it never wakes. *)
Lemma rx_ack_g : forall (HL : links), rx_branch_g cond_ack.
Proof.
  intros HL. unfold rx_branch_g. intros I ops fr n B. cbv zeta. intros Hn Hadr Hpre Hacc Hc.
  unfold cond_ack in Hc.
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  destruct Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hroom) as Hog.
  assert (HB : length B = WN) by exact Hlen.
  pose proof (rf_cmd _ _ Hf) as Ecmd.
  pose proof (rf_ack _ _ Hf) as Eack.
  pose proof (rf_src_len _ _ Hf) as Hsl.
  destruct (learn_M_frame B (rxbuf fr n) HB Hsl) as [Hlf Hll].
  destruct (learn_M_desk B (rxbuf fr n) HB Hsl (b2_desk_known01 _ Hst) (ra_known _ _ Hacc)) as [Lk Ld].
  remember (learn_M B (rxbuf fr n)) as Bk eqn:EBk.
  assert (Ecmd' : sf_cmd (spec_read_frame (zs (tf_bytes fr)) n) = SPEC_CMD_ACK) by (rewrite Ecmd, Hc; reflexivity).
  assert (F1 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE) = false) by (rewrite Hc; reflexivity).
  assert (F2 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE_SESSION) = false) by (rewrite Hc; reflexivity).
  assert (F3 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ACK) = true) by (rewrite Hc; reflexivity).
  assert (Hnw : ~ rx_wake_buf (rxbuf fr n)) by (intros [Hw _]; rewrite Hw, Z.eqb_refl in F1; discriminate F1).
  (* the model's world at its switch (FT:301) *)
  remember (set_M_last_rx Bk (g_now B)) as X0 eqn:EX0.
  assert (HX0 : length X0 = WN) by (subst X0; wlen).
  assert (Hk0 : wframe (in_rs [(A_M_last_rx, 8)]) Bk X0) by (subst X0; wfrs).
  pose proof (wframe_trans_rs _ _ _ _ _ Hlf Hk0) as HB0.
  assert (Mst0 : M_state X0 = M_state B) by fget HB0.
  assert (Mlr0 : M_last_rx X0 = g_now B) by (subst X0; wget).
  assert (Mws0 : M_wake_sent X0 = M_wake_sent B) by fget HB0.
  assert (Mnw0 : g_now X0 = g_now B) by fget HB0.
  assert (Mcw0 : Cfg_wake_timeout_ms X0 = Cfg_wake_timeout_ms B) by fget HB0.
  assert (Mco0 : Cfg_offline_ms X0 = Cfg_offline_ms B) by fget HB0.
  assert (MF0 : M_fly_on X0 = M_fly_on B) by fget HB0.
  assert (MC0 : M_fly_counter X0 = M_fly_counter B) by fget HB0.
  assert (Hcase : (M_fly_on B = 1 /\ fr_ack (rxbuf fr n) = M_fly_counter B) \/
                  (M_fly_on B = 0 \/ fr_ack (rxbuf fr n) <> M_fly_counter B)).
  { destruct (b8_on01 _ Hfly) as [H0 | H1]; [right; left; exact H0 |].
    destruct (Z.eq_dec (fr_ack (rxbuf fr n)) (M_fly_counter B)) as [E | E];
      [left; split; [exact H1 | exact E] | right; right; exact E]. }
  destruct Hcase as [[Hon Hk] | Hnm].
  2: {
    (* the ack names no frame in flight: the model ignores it (FT:333), the library counts it (DS:225-227) *)
    assert (Tm : (truth (M_fly_on X0) && (sf_ack (spec_read_frame (zs (tf_bytes fr)) n) =? M_fly_counter X0)) = false).
    { rewrite MF0, MC0, Eack. destruct Hnm as [H0 | Hne]; [rewrite H0; reflexivity |].
      rewrite (proj2 (Z.eqb_neq (fr_ack (rxbuf fr n)) (M_fly_counter B)) Hne). apply andb_false_r. }
    exists X0. split; [|split; [|split]].
    { exact (rxack_m_none I fr n X0 Ecmd' Tm). }
    { apply (rxack_tick ops B X0 Hcfg Htime);
        [left; exact Mst0 | exact Mlr0 | exact Mws0 | exact Mnw0 | exact Mcw0 | exact Mco0]. }
    { apply (wframe_rs_incl (R_learn ++ [(A_M_last_rx, 8)]) R_mod B X0); [vm_compute; reflexivity | exact HB0]. }
    intros W HW.
    pose proof HW as (HWf & HWk & HWm & HWl).
    assert (HWn : length W = WN) by (eapply wframe_len; [exact HWf | exact HX0]).
    assert (SiW : S_inflight W = M_fly_on B)
      by (transitivity (S_inflight X0); [fget HWf | transitivity (S_inflight B); [fget HB0 | exact (b8_on _ Hfly)]]).
    assert (Lt : ((S_inflight W =? 0) || negb (fr_ack (rxbuf fr n) =? S_inflight_counter W)) = true).
    { rewrite SiW. destruct (b8_on01 _ Hfly) as [H0 | H1]; [rewrite H0; reflexivity |].
      destruct Hnm as [H0 | Hne]; [rewrite H1 in H0; discriminate H0 |].
      assert (ScW : S_inflight_counter W = M_fly_counter B)
        by (transitivity (S_inflight_counter X0); [fget HWf | transitivity (S_inflight_counter B);
              [fget HB0 | exact (b8_counter _ Hfly H1)]]).
      rewrite ScW, (proj2 (Z.eqb_neq (fr_ack (rxbuf fr n)) (M_fly_counter B)) Hne). apply orb_true_r. }
    exists (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1))). split.
    { (* DS:225-227 *)
      unfold rx_sw. cbv zeta. rewrite F1, F2, F3. unfold on_ack_m. rewrite Lt. reflexivity. }
    remember (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1))) as W' eqn:EW'.
    assert (HW' : wframe (in_rs [(A_S_stats_rx_ignored, 8)]) W W') by (subst W'; wfrs).
    pose proof (wframe_trans_rs _ _ _ _ _ HWf HW') as Hmw.
    pose proof (wframe_trans_rs _ _ _ _ _ HB0 Hmw) as Hall.
    pose proof (wframe_trans_rs _ _ _ _ _ Hk0 Hmw) as Hkw.
    (* the written fields *)
    assert (W1 : M_desk_known W' = 1) by (transitivity (M_desk_known Bk); [fget Hkw | exact Lk]).
    assert (W2 : M_desk W' = fr_src (rxbuf fr n)) by (transitivity (M_desk Bk); [fget Hkw | exact Ld]).
    assert (W3 : M_last_rx W' = g_now B) by (transitivity (M_last_rx X0); [fget Hmw | exact Mlr0]).
    assert (W4 : S_desk_known W' = 1) by (transitivity (S_desk_known W); [fget HW' | exact HWk]).
    assert (W5 : S_desk_mac W' = fr_src (rxbuf fr n)) by (transitivity (S_desk_mac W); [fget HW' | exact HWm]).
    assert (W6 : S_last_rx_us W' = g_now B)
      by (transitivity (S_last_rx_us W); [fget HW' | rewrite HWl; exact Mnw0]).
    clear HWl.
    (* the fields nobody wrote *)
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
    assert (U11 : S_backoff_until_us W' = S_backoff_until_us B) by fget Hall.
    assert (U12 : M_backoff_until W' = M_backoff_until B) by fget Hall.
    assert (U13 : g_raw W' = g_raw B) by fget Hall.
    assert (U14 : S_next_keepalive_us W' = S_next_keepalive_us B) by fget Hall.
    assert (U15 : M_next_ka W' = M_next_ka B) by fget Hall.
    assert (U16 : S_display_sent W' = S_display_sent B) by fget Hall.
    assert (U17 : M_display_sent W' = M_display_sent B) by fget Hall.
    assert (U18 : S_last_display_us W' = S_last_display_us B) by fget Hall.
    assert (U19 : M_last_display W' = M_last_display B) by fget Hall.
    assert (U20 : S_desk_counter_valid W' = S_desk_counter_valid B) by fget Hall.
    assert (U21 : M_desk_counter_valid W' = M_desk_counter_valid B) by fget Hall.
    assert (U22 : S_desk_counter W' = S_desk_counter B) by fget Hall.
    assert (U23 : M_desk_counter W' = M_desk_counter B) by fget Hall.
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
    assert (U43 : g_fail_next W' = g_fail_next B) by fget Hall.
    assert (U44 : S_personality W' = S_personality B) by fget Hall.
    assert (Hst' : agree_st W').
    { constructor; rw_eqs W'.
      - exact (b1_state _ Hst).
      - exact (b1_state_range _ Hst).
      - reflexivity.
      - right; reflexivity.
      - intros _; reflexivity.
      - exact (b3_foreign _ Hst).
      - exact (b3_foreign01 _ Hst).
      - exact (b3_e1 _ Hst).
      - exact (b3_e1_01 _ Hst).
      - exact (b3_e2 _ Hst).
      - exact (b3_e2_01 _ Hst).
      - exact (b4_wake_sent _ Hst).
      - reflexivity.
      - exact (b4_backoff _ Hst).
      - exact (b5_next_ka _ Hst).
      - exact (b5_display_sent _ Hst).
      - exact (b5_display_sent01 _ Hst).
      - exact (b5_last_display _ Hst).
      - exact (b6_valid _ Hst).
      - exact (b6_valid01 _ Hst).
      - exact (b6_counter _ Hst).
      - exact (b7_host_counter _ Hst).
      - exact (b9_idle _ Hst).
      - intros _; reflexivity. }
    assert (Hfl' : agree_fly W').
    { apply (agree_fly_fr _ B W' Hall); [vm_compute; reflexivity | vm_compute; reflexivity | exact U24
        | exact U37 | exact U38 | | exact Hfly].
      intros Hon. split.
      - rewrite W2. apply (ra_known _ _ Hacc). apply (b9_known _ Hst). exact (b8_state _ Hfly Hon).
      - rewrite U2. exact (b8_state _ Hfly Hon). }
    assert (Hti' : agree_time ops W').
    { constructor; rw_eqs W'.
      - exact (c_now _ _ Htime).
      - apply Z.le_refl.
      - exact (c1_wake_sent _ _ Htime).
      - exact (c1_fly_sent _ _ Htime).
      - exact (c1_last_display _ _ Htime).
      - exact (c1_backoff _ _ Htime).
      - exact (c1_next_ka _ _ Htime).
      - exact (c2_wake _ _ Htime).
      - intros _. rewrite (Z.sub_diag (g_now B)). pose proof (a1_offline _ Hcfg) as Ho. clear - Ho. lia.
      - exact (c2_fly _ _ Htime). }
    assert (Hmi' : agree_misc I W').
    { constructor; rw_eqs W'; [exact (e1_fail_next _ _ Hmisc) | exact (e2_personality _ _ Hmisc)]. }
    constructor; [constructor | | |].
    - apply (agree_core_rx I ops B W' Hcore); [| exact Hst' | exact Hfl' | exact Hti' | exact Hmi'].
      eapply wframe_rx; [| exact Hall]. vm_compute. reflexivity.
    - (* neither side wrote OW or GOT *)
      apply (ow_got_eq_fr _ B W' Hall); [vm_compute; reflexivity | exact Hog].
    - fget HW'.
    - fget HW'.
    - fget HW'.
    - fget HW'.
    - fget HW'.
    - apply (ow_step_fr _ B B W' Hall); [vm_compute; reflexivity | apply ow_step_refl].
    - fget HW'.
    - intros Hw. exfalso. exact (Hnw Hw). }
  (* the ack names the frame in flight (FT:333-337, DS:229-232); a = OW.acked = GOT.acked, k = OW.n = GOT.n *)
  assert (Hon0 : M_fly_on X0 = 1) by (rewrite MF0; exact Hon).
  assert (Ek0 : sf_ack (spec_read_frame (zs (tf_bytes fr)) n) = M_fly_counter X0) by (rewrite Eack, MC0; exact Hk).
  assert (Har : 0 <= OW_acked B <= 1)
    by (pose proof (og_acked_range _ Hog); pose proof (wr_acked _ Hroom); slia).
  assert (Hk4 : 0 <= OW_n B <= 4) by (pose proof (og_n_range _ Hog); pose proof (wr_n _ Hroom); slia).
  assert (Ha0 : OW_acked X0 = OW_acked B) by fget HB0.
  pose proof (rxack_m_sw I fr n X0 (OW_acked B) HX0 Ecmd' Hon0 Ek0 Ha0 Har) as Em.
  assert (Hn0 : OW_n X0 = OW_n B) by fget HB0.
  assert (MR0 : M_fly_retries X0 = M_fly_retries B) by fget HB0.
  assert (Mka0 : Cfg_keepalive_ms X0 = Cfg_keepalive_ms B) by fget HB0.
  assert (Me10 : M_e1_us X0 = M_e1_us B) by fget HB0.
  pose proof (b8_retries _ Hfly Hon) as Hret.
  assert (Hu16 : u16 (M_fly_retries B) = M_fly_retries B).
  { unfold u16. apply Z.mod_small. pose proof (b8_retries_le _ Hfly Hon) as R1.
    pose proof (a1_max_retries _ Hcfg) as R2.
    assert (R0 : 0 <= M_fly_retries B) by (unfold M_fly_retries; apply u_at_nonneg). clear - R0 R1 R2. lia. }
  destruct (b8_state _ Hfly Hon) as [Hwk | Hol].
  2: {
    (* ONLINE: the ack only ends the flight (FT:338 false, DS:233 false) *)
    assert (Ts : (M_state X0 =? S_WAKING) = false) by (rewrite Mst0, Hol; reflexivity).
    destruct (rxack_mA_frame X0 (OW_acked B) HX0) as [H0m HBm].
    destruct (rxack_mA_get X0 (OW_acked B) HX0 Har) as (Bf & Ba & Bc & Br).
    remember (rxack_mA X0 (OW_acked B)) as Bm eqn:EBm.
    pose proof (wframe_trans_rs _ _ _ _ _ HB0 H0m) as HBm'.
    exists Bm. split; [|split; [|split]].
    { rewrite Em, Ts. reflexivity. }
    { apply (rxack_tick ops B Bm Hcfg Htime);
        [left; fget HBm' | transitivity (M_last_rx X0); [fget H0m | exact Mlr0] | fget HBm' | fget HBm'
        | fget HBm' | fget HBm']. }
    { apply (wframe_rs_incl ((R_learn ++ [(A_M_last_rx, 8)]) ++ rxack_RA) R_mod B Bm);
        [vm_compute; reflexivity | exact HBm']. }
    intros W HW.
    pose proof HW as (HWf & HWk & HWm & HWl).
    assert (HWn : length W = WN) by (eapply wframe_len; [exact HWf | exact HBm]).
    assert (SiW : S_inflight W = 1)
      by (transitivity (S_inflight Bm); [fget HWf | transitivity (S_inflight B);
            [fget HBm' | rewrite (b8_on _ Hfly); exact Hon]]).
    assert (ScW : fr_ack (rxbuf fr n) = S_inflight_counter W).
    { rewrite Hk. symmetry. transitivity (S_inflight_counter Bm);
        [fget HWf | transitivity (S_inflight_counter B); [fget HBm' | exact (b8_counter _ Hfly Hon)]]. }
    assert (NoW : S_notify W = ti_notice I)
      by (transitivity (S_notify Bm); [fget HWf | transitivity (S_notify B); [fget HBm' | exact (a3_notify _ _ Hio)]]).
    assert (GaW : GOT_acked W = OW_acked B)
      by (transitivity (GOT_acked Bm); [fget HWf | transitivity (GOT_acked B); [fget HBm' | exact (og_acked _ Hog)]]).
    assert (OaW : OW_acked W = OW_acked B + 1) by (transitivity (OW_acked Bm); [fget HWf | exact Ba]).
    assert (OcW : OW_acked_counter W = fr_ack (rxbuf fr n))
      by (transitivity (OW_acked_counter Bm); [fget HWf | rewrite Bc, MC0; symmetry; exact Hk]).
    assert (SrW : S_inflight_retries W = M_fly_retries B)
      by (transitivity (S_inflight_retries Bm); [fget HWf | transitivity (S_inflight_retries B); [fget HBm' | exact Hret]]).
    assert (OrW : OW_acked_retry W = u16 (S_inflight_retries W))
      by (transitivity (OW_acked_retry Bm); [fget HWf | rewrite Br, MR0, SrW, Hu16; reflexivity]).
    pose proof (rxack_s_ack I (Some fr) W (rxbuf fr n) (OW_acked B) HWn SiW ScW NoW GaW OaW Har OcW OrW) as Elib.
    assert (SsW : S_state W = M_state B)
      by (transitivity (S_state Bm); [fget HWf | transitivity (S_state B); [fget HBm' | exact (b1_state _ Hst)]]).
    assert (Lt : (S_state W =? DIGINET_S_WAKING) = false) by (rewrite SsW, Hol; reflexivity).
    destruct (rxack_sA_frame W (OW_acked B) HWn) as [HW' HW'n].
    destruct (rxack_sA_get W (OW_acked B) HWn Har) as (Si & Sga).
    remember (rxack_sA W (OW_acked B)) as W' eqn:EW'.
    exists W'. split.
    { unfold rx_sw. cbv zeta. rewrite F1, F2, F3, Elib, Lt. reflexivity. }
    pose proof (wframe_trans_rs _ _ _ _ _ HWf HW') as Hmw.
    pose proof (wframe_trans_rs _ _ _ _ _ HBm' Hmw) as Hall.
    pose proof (wframe_trans_rs _ _ _ _ _ H0m Hmw) as H0w.
    pose proof (wframe_trans_rs _ _ _ _ _ Hk0 H0w) as Hkw.
    assert (Wsm : S_desk_mac W' = fr_src (rxbuf fr n)) by (transitivity (S_desk_mac W); [fget HW' | exact HWm]).
    assert (Wmd : M_desk W' = fr_src (rxbuf fr n)) by (transitivity (M_desk Bk); [fget Hkw | exact Ld]).
    assert (Wms : M_state W' = M_state B) by fget Hall.
    assert (Wss : S_state W' = M_state B) by (transitivity (S_state W); [fget HW' | exact SsW]).
    assert (Wsw : S_wake_acked W' = S_wake_acked B) by fget Hall.
    assert (Wme : M_e2_acked W' = M_e2_acked B) by fget Hall.
    assert (Wsk : S_next_keepalive_us W' = S_next_keepalive_us B) by fget Hall.
    assert (Wmk : M_next_ka W' = M_next_ka B) by fget Hall.
    assert (Wgn : GOT_n W' = GOT_n B) by fget Hall.
    assert (Won : OW_n W' = OW_n B) by fget Hall.
    pose proof (rxack_t_fr _ B W' Hall ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as TB.
    assert (P : agree_core I ops W' /\ ow_got_eq W' /\ ow_step B W').
    { apply (rxack_post I ops B W' Hcore Hroom).
      - eapply (wframe_rs_incl _ rxack_R B W'); [| exact Hall]. vm_compute. reflexivity.
      - transitivity (M_desk_known Bk); [fget Hkw | exact Lk].
      - transitivity (S_desk_known W); [fget HW' | exact HWk].
      - rewrite Wsm, Wmd. reflexivity.
      - transitivity (M_last_rx X0); [fget H0w | exact Mlr0].
      - transitivity (S_last_rx_us W); [fget HW' | rewrite HWl; fget HBm'].
      - rewrite Wss, Wms. reflexivity.
      - left. exact Wms.
      - rewrite Wsw, Wme. exact (b3_e2 _ Hst).
      - rewrite Wme. exact (b3_e2_01 _ Hst).
      - intros Hr. rewrite Wsk, Wmk. split; [exact (b5_next_ka _ Hst Hr) | exact (c1_next_ka _ _ Htime Hr)].
      - transitivity (M_fly_on Bm); [fget Hmw | exact Bf].
      - exact Si.
      - rewrite Wgn, Won. exact (og_n _ Hog).
      - rewrite Won. slia.
      - intros i Hi Hi2. rewrite Won in Hi.
        destruct (TB i (conj (proj1 Hi) Hi2)) as (T1 & T2 & T3 & T4 & T5 & T6).
        rewrite T1, T2, T3, T4, T5, T6. exact (og_t _ Hog i Hi Hi2).
      - transitivity (OW_acked Bm); [fget Hmw | exact Ba].
      - exact Sga. }
    destruct P as (Pc & Pg & Ps).
    constructor; [constructor; [exact Pc | exact Pg | fget HW' | fget HW' | fget HW' | fget HW' | fget HW']
                 | exact Ps | fget HW' | intros Hw; exfalso; exact (Hnw Hw)]. }
  (* WAKING: the wake's e2 is acked (FT:338-339, DS:233-234) *)
  assert (Ts : (M_state X0 =? S_WAKING) = true) by (rewrite Mst0, Hwk; reflexivity).
  destruct (b3_e1_01 _ Hst) as [He0 | He1].
  { (* the e1 not yet named: still WAKING (FT:239 false, DS:178 false) *)
    assert (Me0 : M_e1_us X0 = 0) by (rewrite Me10; exact He0).
    pose proof (rxack_m_wait X0 (OW_acked B) HX0 Me0) as Ew.
    destruct (rxack_mE_frame X0 (OW_acked B) HX0) as [H0m HBm].
    destruct (rxack_mE_get X0 (OW_acked B) HX0 Har) as (Bf & Ba & Bc & Br & Be).
    remember (rxack_mE X0 (OW_acked B)) as Bm eqn:EBm.
    pose proof (wframe_trans_rs _ _ _ _ _ HB0 H0m) as HBm'.
    exists Bm. split; [|split; [|split]].
    { rewrite Em, Ts, Ew. reflexivity. }
    { apply (rxack_tick ops B Bm Hcfg Htime);
        [left; fget HBm' | transitivity (M_last_rx X0); [fget H0m | exact Mlr0] | fget HBm' | fget HBm'
        | fget HBm' | fget HBm']. }
    { apply (wframe_rs_incl ((R_learn ++ [(A_M_last_rx, 8)]) ++ rxack_RE) R_mod B Bm);
        [vm_compute; reflexivity | exact HBm']. }
    intros W HW.
    pose proof HW as (HWf & HWk & HWm & HWl).
    assert (HWn : length W = WN) by (eapply wframe_len; [exact HWf | exact HBm]).
    assert (SiW : S_inflight W = 1)
      by (transitivity (S_inflight Bm); [fget HWf | transitivity (S_inflight B);
            [fget HBm' | rewrite (b8_on _ Hfly); exact Hon]]).
    assert (ScW : fr_ack (rxbuf fr n) = S_inflight_counter W).
    { rewrite Hk. symmetry. transitivity (S_inflight_counter Bm);
        [fget HWf | transitivity (S_inflight_counter B); [fget HBm' | exact (b8_counter _ Hfly Hon)]]. }
    assert (NoW : S_notify W = ti_notice I)
      by (transitivity (S_notify Bm); [fget HWf | transitivity (S_notify B); [fget HBm' | exact (a3_notify _ _ Hio)]]).
    assert (GaW : GOT_acked W = OW_acked B)
      by (transitivity (GOT_acked Bm); [fget HWf | transitivity (GOT_acked B); [fget HBm' | exact (og_acked _ Hog)]]).
    assert (OaW : OW_acked W = OW_acked B + 1) by (transitivity (OW_acked Bm); [fget HWf | exact Ba]).
    assert (OcW : OW_acked_counter W = fr_ack (rxbuf fr n))
      by (transitivity (OW_acked_counter Bm); [fget HWf | rewrite Bc, MC0; symmetry; exact Hk]).
    assert (SrW : S_inflight_retries W = M_fly_retries B)
      by (transitivity (S_inflight_retries Bm); [fget HWf | transitivity (S_inflight_retries B); [fget HBm' | exact Hret]]).
    assert (OrW : OW_acked_retry W = u16 (S_inflight_retries W))
      by (transitivity (OW_acked_retry Bm); [fget HWf | rewrite Br, MR0, SrW, Hu16; reflexivity]).
    pose proof (rxack_s_ack I (Some fr) W (rxbuf fr n) (OW_acked B) HWn SiW ScW NoW GaW OaW Har OcW OrW) as Elib.
    assert (SsW : S_state W = M_state B)
      by (transitivity (S_state Bm); [fget HWf | transitivity (S_state B); [fget HBm' | exact (b1_state _ Hst)]]).
    assert (Lt : (S_state W =? DIGINET_S_WAKING) = true) by (rewrite SsW, Hwk; reflexivity).
    assert (SeW : S_e1_named_us W = 0)
      by (transitivity (S_e1_named_us Bm); [fget HWf | transitivity (S_e1_named_us B);
            [fget HBm' | rewrite (b3_e1 _ Hst); exact He0]]).
    pose proof (rxack_s_wait I (Some fr) W (OW_acked B) HWn SeW) as Ew'.
    destruct (rxack_sE_frame W (OW_acked B) HWn) as [HW' HW'n].
    destruct (rxack_sE_get W (OW_acked B) HWn Har) as (Si & Sga & Swa).
    remember (rxack_sE W (OW_acked B)) as W' eqn:EW'.
    exists W'. split.
    { unfold rx_sw. cbv zeta. rewrite F1, F2, F3, Elib, Lt, Ew'. reflexivity. }
    pose proof (wframe_trans_rs _ _ _ _ _ HWf HW') as Hmw.
    pose proof (wframe_trans_rs _ _ _ _ _ HBm' Hmw) as Hall.
    pose proof (wframe_trans_rs _ _ _ _ _ H0m Hmw) as H0w.
    pose proof (wframe_trans_rs _ _ _ _ _ Hk0 H0w) as Hkw.
    assert (Wsm : S_desk_mac W' = fr_src (rxbuf fr n)) by (transitivity (S_desk_mac W); [fget HW' | exact HWm]).
    assert (Wmd : M_desk W' = fr_src (rxbuf fr n)) by (transitivity (M_desk Bk); [fget Hkw | exact Ld]).
    assert (Wms : M_state W' = M_state B) by fget Hall.
    assert (Wss : S_state W' = M_state B) by (transitivity (S_state W); [fget HW' | exact SsW]).
    assert (Wme : M_e2_acked W' = 1) by (transitivity (M_e2_acked Bm); [fget Hmw | exact Be]).
    assert (Wsk : S_next_keepalive_us W' = S_next_keepalive_us B) by fget Hall.
    assert (Wmk : M_next_ka W' = M_next_ka B) by fget Hall.
    assert (Wgn : GOT_n W' = GOT_n B) by fget Hall.
    assert (Won : OW_n W' = OW_n B) by fget Hall.
    pose proof (rxack_t_fr _ B W' Hall ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as TB.
    assert (P : agree_core I ops W' /\ ow_got_eq W' /\ ow_step B W').
    { apply (rxack_post I ops B W' Hcore Hroom).
      - eapply (wframe_rs_incl _ rxack_R B W'); [| exact Hall]. vm_compute. reflexivity.
      - transitivity (M_desk_known Bk); [fget Hkw | exact Lk].
      - transitivity (S_desk_known W); [fget HW' | exact HWk].
      - rewrite Wsm, Wmd. reflexivity.
      - transitivity (M_last_rx X0); [fget H0w | exact Mlr0].
      - transitivity (S_last_rx_us W); [fget HW' | rewrite HWl; fget HBm'].
      - rewrite Wss, Wms. reflexivity.
      - left. exact Wms.
      - rewrite Swa, Wme. reflexivity.
      - rewrite Wme. right. reflexivity.
      - intros Hr. rewrite Wsk, Wmk. split; [exact (b5_next_ka _ Hst Hr) | exact (c1_next_ka _ _ Htime Hr)].
      - transitivity (M_fly_on Bm); [fget Hmw | exact Bf].
      - exact Si.
      - rewrite Wgn, Won. exact (og_n _ Hog).
      - rewrite Won. slia.
      - intros i Hi Hi2. rewrite Won in Hi.
        destruct (TB i (conj (proj1 Hi) Hi2)) as (T1 & T2 & T3 & T4 & T5 & T6).
        rewrite T1, T2, T3, T4, T5, T6. exact (og_t _ Hog i Hi Hi2).
      - transitivity (OW_acked Bm); [fget Hmw | exact Ba].
      - exact Sga. }
    destruct P as (Pc & Pg & Ps).
    constructor; [constructor; [exact Pc | exact Pg | fget HW' | fget HW' | fget HW' | fget HW' | fget HW']
                 | exact Ps | fget HW' | intros Hw; exfalso; exact (Hnw Hw)]. }
  (* the e1 already named: both sides go ONLINE (FT:239-241, DS:178-180), logged at k on both sides *)
  assert (Me1 : M_e1_us X0 = 1) by (rewrite Me10; exact He1).
  assert (Ms0 : M_state X0 = S_WAKING) by (rewrite Mst0; exact Hwk).
  pose proof (rxack_m_online X0 (OW_acked B) (OW_n B) HX0 Ms0 Me1 Hn0 Hk4) as Eo.
  destruct (rxack_mO_frame X0 (OW_acked B) (OW_n B) HX0 Hk4) as [H0m HBm].
  destruct (rxack_mO_get X0 (OW_acked B) (OW_n B) HX0 Har Hk4)
    as (Bf & Ba & Bc & Br & Be & Bnk & Bs & Bn & Bts & Bto & Btr).
  pose proof (rxack_mO_t X0 (OW_acked B) (OW_n B) HX0 Hk4) as Mt.
  pose proof (rxack_t_fr _ B X0 HB0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as T0.
  remember (rxack_mO X0 (OW_acked B) (OW_n B)) as Bm eqn:EBm.
  pose proof (wframe_trans_rs _ _ _ _ _ HB0 H0m) as HBm'.
  exists Bm. split; [|split; [|split]].
  { rewrite Em, Ts, Eo. reflexivity. }
  { apply (rxack_tick ops B Bm Hcfg Htime);
      [right; exact Bs | transitivity (M_last_rx X0); [fget H0m | exact Mlr0] | fget HBm' | fget HBm'
      | fget HBm' | fget HBm']. }
  { apply (wframe_rs_incl ((R_learn ++ [(A_M_last_rx, 8)]) ++ rxack_RO) R_mod B Bm);
      [vm_compute; reflexivity | exact HBm']. }
  intros W HW.
  pose proof HW as (HWf & HWk & HWm & HWl).
  assert (HWn : length W = WN) by (eapply wframe_len; [exact HWf | exact HBm]).
  assert (SiW : S_inflight W = 1)
    by (transitivity (S_inflight Bm); [fget HWf | transitivity (S_inflight B);
          [fget HBm' | rewrite (b8_on _ Hfly); exact Hon]]).
  assert (ScW : fr_ack (rxbuf fr n) = S_inflight_counter W).
  { rewrite Hk. symmetry. transitivity (S_inflight_counter Bm);
      [fget HWf | transitivity (S_inflight_counter B); [fget HBm' | exact (b8_counter _ Hfly Hon)]]. }
  assert (NoW : S_notify W = ti_notice I)
    by (transitivity (S_notify Bm); [fget HWf | transitivity (S_notify B); [fget HBm' | exact (a3_notify _ _ Hio)]]).
  assert (GaW : GOT_acked W = OW_acked B)
    by (transitivity (GOT_acked Bm); [fget HWf | transitivity (GOT_acked B); [fget HBm' | exact (og_acked _ Hog)]]).
  assert (OaW : OW_acked W = OW_acked B + 1) by (transitivity (OW_acked Bm); [fget HWf | exact Ba]).
  assert (OcW : OW_acked_counter W = fr_ack (rxbuf fr n))
    by (transitivity (OW_acked_counter Bm); [fget HWf | rewrite Bc, MC0; symmetry; exact Hk]).
  assert (SrW : S_inflight_retries W = M_fly_retries B)
    by (transitivity (S_inflight_retries Bm); [fget HWf | transitivity (S_inflight_retries B); [fget HBm' | exact Hret]]).
  assert (OrW : OW_acked_retry W = u16 (S_inflight_retries W))
    by (transitivity (OW_acked_retry Bm); [fget HWf | rewrite Br, MR0, SrW, Hu16; reflexivity]).
  pose proof (rxack_s_ack I (Some fr) W (rxbuf fr n) (OW_acked B) HWn SiW ScW NoW GaW OaW Har OcW OrW) as Elib.
  assert (SsW : S_state W = M_state B)
    by (transitivity (S_state Bm); [fget HWf | transitivity (S_state B); [fget HBm' | exact (b1_state _ Hst)]]).
  assert (Lt : (S_state W =? DIGINET_S_WAKING) = true) by (rewrite SsW, Hwk; reflexivity).
  assert (SsW' : S_state W = DIGINET_S_WAKING) by (rewrite SsW, Hwk; reflexivity).
  assert (SeW : S_e1_named_us W = 1)
    by (transitivity (S_e1_named_us Bm); [fget HWf | transitivity (S_e1_named_us B);
          [fget HBm' | rewrite (b3_e1 _ Hst); exact He1]]).
  assert (GnW : GOT_n W = OW_n B)
    by (transitivity (GOT_n Bm); [fget HWf | transitivity (GOT_n B); [fget HBm' | exact (og_n _ Hog)]]).
  assert (Me2W : M_e2_acked W = 1) by (transitivity (M_e2_acked Bm); [fget HWf | exact Be]).
  assert (Me1W : M_e1_us W = 1)
    by (transitivity (M_e1_us Bm); [fget HWf | transitivity (M_e1_us X0); [fget H0m | exact Me1]]).
  pose proof (rxack_s_online I (Some fr) W (OW_acked B) (OW_n B) HWn SsW' SeW NoW GnW Hk4 Me2W Me1W) as Eon.
  assert (Ska : S_cfg_keepalive_ms W = Cfg_keepalive_ms B)
    by (transitivity (S_cfg_keepalive_ms Bm); [fget HWf | transitivity (S_cfg_keepalive_ms B);
          [fget HBm' | exact (a2_keepalive _ Hcfg)]]).
  assert (Mnwm : g_now Bm = g_now B) by fget HBm'.
  assert (Slr : S_last_rx_us W = g_now B) by (rewrite HWl; exact Mnwm).
  destruct (rxack_sO_frame W (OW_acked B) (OW_n B) HWn Hk4) as [HW' HW'n].
  destruct (rxack_sO_get W (OW_acked B) (OW_n B) HWn Har Hk4)
    as (Si & Sga & Swa & Snk & Ss & Sgn & Sts & Sto & Str).
  pose proof (rxack_sO_t W (OW_acked B) (OW_n B) HWn Hk4) as St.
  pose proof (rxack_t_fr _ Bm W HWf ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as TW.
  remember (rxack_sO W (OW_acked B) (OW_n B)) as W' eqn:EW'.
  exists W'. split.
  { unfold rx_sw. cbv zeta. rewrite F1, F2, F3, Elib, Lt, Eon. reflexivity. }
  pose proof (wframe_trans_rs _ _ _ _ _ HWf HW') as Hmw.
  pose proof (wframe_trans_rs _ _ _ _ _ HBm' Hmw) as Hall.
  pose proof (wframe_trans_rs _ _ _ _ _ H0m Hmw) as H0w.
  pose proof (wframe_trans_rs _ _ _ _ _ Hk0 H0w) as Hkw.
  assert (Wsm : S_desk_mac W' = fr_src (rxbuf fr n)) by (transitivity (S_desk_mac W); [fget HW' | exact HWm]).
  assert (Wmd : M_desk W' = fr_src (rxbuf fr n)) by (transitivity (M_desk Bk); [fget Hkw | exact Ld]).
  assert (Wms : M_state W' = S_ONLINE) by (transitivity (M_state Bm); [fget Hmw | exact Bs]).
  assert (Wme : M_e2_acked W' = 1) by (transitivity (M_e2_acked Bm); [fget Hmw | exact Be]).
  assert (Wmk : M_next_ka W' = u64 (g_now B + h_ms_m (Cfg_keepalive_ms B)))
    by (transitivity (M_next_ka Bm); [fget Hmw | rewrite Bnk, Mlr0, Mka0; reflexivity]).
  assert (Wsk : S_next_keepalive_us W' = u64 (g_now B + h_ms_m (Cfg_keepalive_ms B)))
    by (rewrite Snk, Slr, Ska; unfold ms_m, h_ms_m; reflexivity).
  assert (Won : OW_n W' = OW_n B + 1) by (transitivity (OW_n Bm); [fget Hmw | exact Bn]).
  assert (Hnow : 0 <= g_now B <= 1000000 + 1024 * 65535000000).
  { pose proof (c_now _ _ Htime) as C0. pose proof (d3_ops _ _ Hq) as D0. unfold OPS_MAX in D0.
    assert (N0 : 0 <= g_now B) by (unfold g_now; apply u_at_nonneg). clear - C0 D0 N0. lia. }
  assert (Hkav : 0 <= Cfg_keepalive_ms B <= 65536) by (pose proof (a1_keepalive _ Hcfg) as K0; clear - K0; lia).
  assert (P : agree_core I ops W' /\ ow_got_eq W' /\ ow_step B W').
  { apply (rxack_post I ops B W' Hcore Hroom).
    - eapply (wframe_rs_incl _ rxack_R B W'); [| exact Hall]. vm_compute. reflexivity.
    - transitivity (M_desk_known Bk); [fget Hkw | exact Lk].
    - transitivity (S_desk_known W); [fget HW' | exact HWk].
    - rewrite Wsm, Wmd. reflexivity.
    - transitivity (M_last_rx X0); [fget H0w | exact Mlr0].
    - transitivity (S_last_rx_us W); [fget HW' | exact Slr].
    - rewrite Ss, Wms. reflexivity.
    - right. exact Wms.
    - rewrite Swa, Wme. reflexivity.
    - rewrite Wme. right. reflexivity.
    - intros _. rewrite Wsk, Wmk. split; [reflexivity |].
      unfold h_ms_m. exact (rxack_ka_le (g_now B) (Cfg_keepalive_ms B) Hnow Hkav).
    - transitivity (M_fly_on Bm); [fget Hmw | exact Bf].
    - exact Si.
    - rewrite Sgn, Won. reflexivity.
    - rewrite Won. slia.
    - (* below k both logs are B's (og_t of B); at k both hold the transition to ONLINE *)
      intros i Hi Hi2. rewrite Won in Hi.
      assert (Hi' : 0 <= i < TRANS_MAX) by (split; [exact (proj1 Hi) | exact Hi2]).
      destruct (St i Hi') as (S1 & S2 & S3 & S4).
      destruct (TW i Hi') as (V1 & V2 & V3 & V4 & V5 & V6).
      destruct (Z.lt_ge_cases i (OW_n B)) as [Hlt | Hge].
      + destruct (S4 Hlt) as (S5 & S6 & S7).
        destruct (Mt i Hi') as (M1 & M2 & M3 & M4).
        destruct (M4 Hlt) as (M5 & M6 & M7).
        destruct (T0 i Hi') as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
        rewrite S5, S6, S7, S1, S2, S3, V1, V2, V3, V4, V5, V6, M1, M2, M3, M5, M6, M7, Z1, Z2, Z3, Z4, Z5, Z6.
        exact (og_t _ Hog i (conj (proj1 Hi) Hlt) Hi2).
      + assert (Ei : i = OW_n B) by (clear - Hi Hge; lia). subst i.
        rewrite Sts, Sto, Str, S1, S2, S3, V4, V5, V6, Bts, Bto, Btr.
        split; [reflexivity | split; reflexivity].
    - transitivity (OW_acked Bm); [fget Hmw | exact Ba].
    - exact Sga. }
  destruct P as (Pc & Pg & Ps).
  constructor; [constructor; [exact Pc | exact Pg | fget HW' | fget HW' | fget HW' | fget HW' | fget HW']
               | exact Ps | fget HW' | intros Hw; exfalso; exact (Hnw Hw)].
Qed.

Lemma rx_ack : forall (HL : links), rx_branch cond_ack.
Proof. intros HL. exact (rx_branch_of_g cond_ack (rx_ack_g HL)). Qed.
