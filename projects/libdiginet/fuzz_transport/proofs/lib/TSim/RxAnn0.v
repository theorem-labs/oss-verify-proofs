(* A frame from the desk whose command is e0 (DIGINET_CMD_ANNOUNCE): m_rx (FT:303-318) and the library's
   on_announce (DS:184-206), then diginet_session_wake (DS:119-145) when the session is idle and auto_wake is on.
   The desk may have been learnt by both (FT:296-297, DS:290-291). A body under 33 bytes: the model does nothing,
   the library counts the frame ignored. Else both name the desk (OW.desk / N_DESK), clear foreign, lose an online
   session (R_DESK_OFFLINE) and, idle with auto_wake, send the wake E2 (io_send FT:846-852) and go WAKING unless
   g_fail_next made the send fail. Any reception of the operation (rx_pre_g): OW.desk and GOT.desk, OW.e2 and
   GOT.e2 go one up from the counts both agree on, the transitions go at OW.n = GOT.n (m_set FT:200-206, notice
   FT:942-946), and a wake leaves M.fail = g_fail_next = 0 (FT:228, :829). *)
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

(* ---- closed facts ---- *)

(* int_inc (TCb) of a count far from INT_MAX *)
Lemma rxe0_int_inc : forall x, 0 <= x <= 8 -> int_inc x = Some (x + 1).
Proof. intros x Hx. unfold int_inc. rewrite (proj2 (Z.eqb_neq x INT_MAX)) by (unfold INT_MAX; lia). reflexivity. Qed.
Lemma rxe0_truth0 : truth 0 = false.
Proof. reflexivity. Qed.
Lemma rxe0_truth1 : truth 1 = true.
Proof. reflexivity. Qed.

Ltac rxe0_consts := unfold S_IDLE, S_WAKING, S_ONLINE, R_WAKE, R_DESK_OFFLINE, DIGINET_S_IDLE, DIGINET_S_WAKING,
  DIGINET_S_ONLINE, DIGINET_R_WAKE, DIGINET_R_DESK_OFFLINE.

(* a read that wget must close *)
Ltac wg := solve [wget].

(* reads and lengths through writes at an offset with a free variable (an entry index k or i): wget / wlen / fget
   with every side condition closed by lia (wnum's vm_compute does not finish fast on a free variable) *)
Ltac wnl := wlenput; wunf_off; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; wclear; lia.
Ltac wlenl_go := lazymatch goal with
  | |- length (upd ?B ?k ?v) = WN => apply rw_len; [wlenl_go | wnl | wnl]
  | |- length ?B = WN => assumption
  end.
Ltac wlenl := wunf_set; wlenl_go.
Ltac wsdl := first [ wlenl
                   | lazymatch goal with |- length _ = _ => wlenput; first [reflexivity | assumption] end
                   | wnl ].
Ltac wr1l := match goal with
  | |- context [s32_at (upd ?B ?k ?v) ?j] =>
      first [ wis k j; lazymatch v with put 4 ?x => rewrite (rw_s_p B k x) by wsdl end
            | rewrite (rw_s_d B k v j) by wsdl ]
  | |- context [u_at (upd ?B ?k ?v) ?j ?n] =>
      first [ wis k j; lazymatch v with put ?m ?x => wis m n; rewrite (rw_u_p B k n x) by wsdl end
            | rewrite (rw_u_d B k v j n) by wsdl ]
  | |- context [sub (upd ?B ?k ?v) ?j ?n] =>
      first [ wis k j; rewrite (rw_sub_p B k v n) by wsdl
            | rewrite (rw_sub_d B k v j n) by wsdl ]
  end.
Ltac wgetl := wunf_get; wunf_set; repeat wr1l;
  first [ wsyn
        | rewrite rw_swrap_id; [wsyn | wclear; lia]
        | rewrite rw_mod_id; [wsyn | first [apply rw_u_range | wclear; cbn; lia]]
        | idtac ].
Ltac wgl := solve [wgetl].
Ltac fgetl H Hd := wunf_get;
  lazymatch goal with
  | |- s32_at _ _ = s32_at _ _ => apply (fr_s _ _ _ _ H)
  | |- u_at _ _ _ = u_at _ _ _ => apply (fr_u _ _ _ _ _ H)
  | |- sub _ _ _ = sub _ _ _ => apply (fr_sub _ _ _ _ _ H)
  end;
  [ wnl | apply (disj_rs_sub _ _ _ _ _ Hd); wunf_off; wclear; lia ].

(* ---- the transition entries below an index (OW.t, m_set FT:200-203; GOT.t, notice FT:942-946) ---- *)

(* the model's entries of Y below m are those of X *)
Definition rxe0_tko (X Y : list byte) (m : Z) : Prop := forall i, 0 <= i < m ->
  OW_t_state Y i = OW_t_state X i /\ OW_t_old Y i = OW_t_old X i /\ OW_t_reason Y i = OW_t_reason X i.

(* the library's entries of Y below m are those of X *)
Definition rxe0_tkg (X Y : list byte) (m : Z) : Prop := forall i, 0 <= i < m ->
  GOT_t_state Y i = GOT_t_state X i /\ GOT_t_old Y i = GOT_t_old X i /\ GOT_t_reason Y i = GOT_t_reason X i.

Lemma rxe0_tko_trans : forall X Y W m, rxe0_tko X Y m -> rxe0_tko Y W m -> rxe0_tko X W m.
Proof.
  intros X Y W m H1 H2 i Hi. destruct (H1 i Hi) as (A1 & A2 & A3). destruct (H2 i Hi) as (C1 & C2 & C3).
  exact (conj (eq_trans C1 A1) (conj (eq_trans C2 A2) (eq_trans C3 A3))).
Qed.

Lemma rxe0_tkg_trans : forall X Y W m, rxe0_tkg X Y m -> rxe0_tkg Y W m -> rxe0_tkg X W m.
Proof.
  intros X Y W m H1 H2 i Hi. destruct (H1 i Hi) as (A1 & A2 & A3). destruct (H2 i Hi) as (C1 & C2 & C3).
  exact (conj (eq_trans C1 A1) (conj (eq_trans C2 A2) (eq_trans C3 A3))).
Qed.

Lemma rxe0_tko_le : forall X Y m m', rxe0_tko X Y m -> m' <= m -> rxe0_tko X Y m'.
Proof. intros X Y m m' H Hm i Hi. apply H. lia. Qed.

Lemma rxe0_tkg_le : forall X Y m m', rxe0_tkg X Y m -> m' <= m -> rxe0_tkg X Y m'.
Proof. intros X Y m m' H Hm i Hi. apply H. lia. Qed.

(* across a frame that misses the 16 entries of 12 bytes *)
Lemma rxe0_tko_fr : forall rs X Y, wframe (in_rs rs) X Y -> disj_rs (A_OW_t_state 0) 192 rs = true ->
  rxe0_tko X Y TRANS_MAX.
Proof.
  intros rs X Y H Hd i Hi. unfold TRANS_MAX in Hi.
  split; [fgetl H Hd|]. split; [fgetl H Hd | fgetl H Hd].
Qed.

Lemma rxe0_tkg_fr : forall rs X Y, wframe (in_rs rs) X Y -> disj_rs (A_GOT_t_state 0) 192 rs = true ->
  rxe0_tkg X Y TRANS_MAX.
Proof.
  intros rs X Y H Hd i Hi. unfold TRANS_MAX in Hi.
  split; [fgetl H Hd|]. split; [fgetl H Hd | fgetl H Hd].
Qed.

(* the entries below OW.n B agree on both sides when they are those of B (ow_got_eq B) *)
Lemma rxe0_t_below : forall B X, ow_got_eq B -> rxe0_tkg B X (OW_n B) -> rxe0_tko B X (OW_n B) ->
  forall i, 0 <= i < OW_n B -> i < TRANS_MAX ->
  GOT_t_state X i = OW_t_state X i /\ GOT_t_old X i = OW_t_old X i /\ GOT_t_reason X i = OW_t_reason X i.
Proof.
  intros B X Hog Hg Ho i Hi Hi2. destruct (Hg i Hi) as (G1 & G2 & G3). destruct (Ho i Hi) as (O1 & O2 & O3).
  destruct (og_t _ Hog i Hi Hi2) as (E1 & E2 & E3).
  rewrite G1, G2, G3, O1, O2, O3. exact (conj E1 (conj E2 E3)).
Qed.

(* the same across one frame that misses the entries of both sides *)
Lemma rxe0_t_fr : forall rs B X, ow_got_eq B -> wframe (in_rs rs) B X ->
  disj_rs (A_GOT_t_state 0) 192 rs = true -> disj_rs (A_OW_t_state 0) 192 rs = true ->
  forall i, 0 <= i < OW_n B -> i < TRANS_MAX ->
  GOT_t_state X i = OW_t_state X i /\ GOT_t_old X i = OW_t_old X i /\ GOT_t_reason X i = OW_t_reason X i.
Proof.
  intros rs B X Hog H Hg Ho. pose proof (og_n_range _ Hog) as Hr.
  apply (rxe0_t_below B X Hog).
  - apply (rxe0_tkg_le _ _ TRANS_MAX); [exact (rxe0_tkg_fr rs B X H Hg) | unfold TRANS_MAX; lia].
  - apply (rxe0_tko_le _ _ TRANS_MAX); [exact (rxe0_tko_fr rs B X H Ho) | unfold TRANS_MAX; lia].
Qed.

(* ---- the model's transitions (TCb m_set_m, m_lost_m, m_wake_m) ---- *)

Definition rxe0_mset (X : list byte) (k st old why : Z) : list byte :=
  set_M_state (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state X k st) k old) k why) (k + 1)) st.

Lemma rxe0_m_set : forall X st why k, M_state X <> st -> OW_n X = k -> 0 <= k < TRANS_MAX ->
  m_set_m X st why = Some (rxe0_mset X k st (M_state X) why, tt).
Proof.
  intros X st why k Hs Hn Hk. unfold m_set_m. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) Hs), Hn.
  rewrite (proj2 (Z.ltb_lt k TRANS_MAX) (proj2 Hk)).
  rewrite (proj2 (Z.ltb_ge k 0) (proj1 Hk)).
  unfold int_inc. rewrite (proj2 (Z.eqb_neq k INT_MAX)) by (unfold TRANS_MAX, INT_MAX in *; lia).
  cbv beta iota. unfold rxe0_mset. exact eq_refl.
Qed.

(* the entries' range stands for the one entry m_set writes (at OW.n, FT:201-203) *)
Definition R_mlost : list (Z * Z) :=
  [(A_M_fly_on, 4); (A_M_desk_counter_valid, 4); (A_OW_t_state 0, 192); (A_OW_n, 4); (A_M_state, 4)].

(* m_lost (FT:210-215) of an online model: the transition at k = OW.n *)
Lemma rxe0_m_lost : forall X k, length X = WN -> M_state X = S_ONLINE -> OW_n X = k -> 0 <= k <= 4 ->
  exists X', m_lost_m X R_DESK_OFFLINE = Some (X', tt) /\ length X' = WN /\ wframe (in_rs R_mlost) X X' /\
    rxe0_tko X X' k /\
    M_state X' = S_IDLE /\ M_fly_on X' = 0 /\ M_desk_counter_valid X' = 0 /\ OW_n X' = k + 1 /\
    OW_t_state X' k = S_IDLE /\ OW_t_old X' k = S_ONLINE /\ OW_t_reason X' k = R_DESK_OFFLINE.
Proof.
  intros X k HX Hs Hn Hk.
  remember (set_M_desk_counter_valid (set_M_fly_on X 0) 0) as Y eqn:EY.
  assert (HY : length Y = WN) by (subst Y; wlen).
  assert (Ys : M_state Y = S_ONLINE) by (rewrite <- Hs; subst Y; wget).
  assert (Yn : OW_n Y = k) by (transitivity (OW_n X); [subst Y; wget | exact Hn]).
  exists (rxe0_mset Y k S_IDLE S_ONLINE R_DESK_OFFLINE).
  split.
  { unfold m_lost_m. rewrite <- EY. rewrite <- Ys. apply rxe0_m_set;
      [rewrite Ys; unfold S_ONLINE, S_IDLE; lia | exact Yn | unfold TRANS_MAX; lia]. }
  unfold rxe0_mset. subst Y. rxe0_consts.
  split; [wlenl|]. split.
  { assert (Ek : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
    destruct Ek as [-> | [-> | [-> | [-> | ->]]]]; wfrs. }
  split; [intros i Hi; split; [wgl|]; split; [wgl | wgl]|].
  split; [wgl|]. split; [wgl|]. split; [wgl|]. split; [wgl|].
  split; [wgl|]. split; [wgl | wgl].
Qed.

(* m_wake (FT:218-233) from an idle model whose desk is known and not foreign *)
Definition rxe0_mwake_pre (X : list byte) (now e2 : Z) : list byte :=
  set_M_fail (set_OW_e2 (set_M_wake_sent (set_M_e1_us (set_M_e2_acked X 0) 0) now) e2) 0.

Definition R_mwake : list (Z * Z) :=
  [(A_M_e2_acked, 4); (A_M_e1_us, 4); (A_M_wake_sent, 8); (A_OW_e2, 4); (A_M_fail, 4);
   (A_OW_t_state 0, 192); (A_OW_n, 4); (A_M_state, 4)].

Definition R_mwfail : list (Z * Z) :=
  [(A_M_e2_acked, 4); (A_M_e1_us, 4); (A_M_wake_sent, 8); (A_OW_e2, 4); (A_M_fail, 4)].

Lemma rxe0_m_wake_fail : forall X e, length X = WN -> M_desk_known X = 1 -> M_foreign X = 0 -> OW_e2 X = e ->
  0 <= e <= 1 -> M_fail X = 1 ->
  exists X', m_wake_m X = Some (X', - EIO) /\ length X' = WN /\ wframe (in_rs R_mwfail) X X' /\
    M_e2_acked X' = 0 /\ M_e1_us X' = 0 /\ M_wake_sent X' = g_now X /\ OW_e2 X' = e + 1 /\ M_fail X' = 0.
Proof.
  intros X e HX Hk Hf He Her Hm.
  assert (G1 : g_now (set_M_e1_us (set_M_e2_acked X 0) 0) = g_now X) by wget.
  assert (G2 : OW_e2 (set_M_wake_sent (set_M_e1_us (set_M_e2_acked X 0) 0) (g_now X)) = e)
    by (transitivity (OW_e2 X); [wget | exact He]).
  assert (G3 : M_fail (set_OW_e2 (set_M_wake_sent (set_M_e1_us (set_M_e2_acked X 0) 0) (g_now X)) (e + 1)) = 1)
    by (transitivity (M_fail X); [wget | exact Hm]).
  exists (rxe0_mwake_pre X (g_now X) (e + 1)). split.
  { unfold m_wake_m. cbv zeta. rewrite Hk, Hf, rxe0_truth1, rxe0_truth0. cbv beta iota delta [negb].
    rewrite G1, G2, (rxe0_int_inc e ltac:(lia)). cbv beta iota. rewrite G3, rxe0_truth1. cbv beta iota.
    unfold rxe0_mwake_pre. exact eq_refl. }
  unfold rxe0_mwake_pre.
  split; [wlen|]. split; [wfrs|].
  split; [wg|]. split; [wg|]. split; [wg|]. split; [wg|]. wg.
Qed.

Lemma rxe0_m_wake_ok : forall X e k, length X = WN -> M_desk_known X = 1 -> M_foreign X = 0 -> OW_e2 X = e ->
  0 <= e <= 1 -> M_fail X = 0 -> M_state X = S_IDLE -> OW_n X = k -> 0 <= k <= 5 ->
  exists X', m_wake_m X = Some (X', SPEC_OK) /\ length X' = WN /\ wframe (in_rs R_mwake) X X' /\
    rxe0_tko X X' k /\
    M_e2_acked X' = 0 /\ M_e1_us X' = 0 /\ M_wake_sent X' = g_now X /\ OW_e2 X' = e + 1 /\ M_fail X' = 0 /\
    M_state X' = S_WAKING /\ OW_n X' = k + 1 /\
    OW_t_state X' k = S_WAKING /\ OW_t_old X' k = S_IDLE /\ OW_t_reason X' k = R_WAKE.
Proof.
  intros X e k HX Hk Hf He Her Hm Hs Hn Hkr.
  assert (G1 : g_now (set_M_e1_us (set_M_e2_acked X 0) 0) = g_now X) by wget.
  assert (G2 : OW_e2 (set_M_wake_sent (set_M_e1_us (set_M_e2_acked X 0) 0) (g_now X)) = e)
    by (transitivity (OW_e2 X); [wget | exact He]).
  assert (G3 : M_fail (set_OW_e2 (set_M_wake_sent (set_M_e1_us (set_M_e2_acked X 0) 0) (g_now X)) (e + 1)) = 0)
    by (transitivity (M_fail X); [wget | exact Hm]).
  remember (rxe0_mwake_pre X (g_now X) (e + 1)) as Y eqn:EY.
  assert (HY : length Y = WN) by (subst Y; unfold rxe0_mwake_pre; wlen).
  assert (Ys : M_state Y = S_IDLE) by (transitivity (M_state X); [subst Y; unfold rxe0_mwake_pre; wget | exact Hs]).
  assert (Yn : OW_n Y = k) by (transitivity (OW_n X); [subst Y; unfold rxe0_mwake_pre; wget | exact Hn]).
  exists (rxe0_mset Y k S_WAKING S_IDLE R_WAKE). split.
  { unfold m_wake_m. cbv zeta. rewrite Hk, Hf, rxe0_truth1, rxe0_truth0. cbv beta iota delta [negb].
    rewrite G1, G2, (rxe0_int_inc e ltac:(lia)). cbv beta iota. rewrite G3, rxe0_truth0. cbv beta iota.
    change (set_M_fail (set_OW_e2 (set_M_wake_sent (set_M_e1_us (set_M_e2_acked X 0) 0) (g_now X)) (e + 1)) 0) with
      (rxe0_mwake_pre X (g_now X) (e + 1)).
    rewrite <- EY.
    rewrite (rxe0_m_set Y S_WAKING R_WAKE k) by
      first [rewrite Ys; unfold S_WAKING, S_IDLE; lia | exact Yn | unfold TRANS_MAX; lia].
    rewrite Ys. cbv beta iota. exact eq_refl. }
  subst Y. unfold rxe0_mset, rxe0_mwake_pre. rxe0_consts.
  split; [wlenl|]. split.
  { assert (Ek : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
    destruct Ek as [-> | [-> | [-> | [-> | [-> | ->]]]]]; wfrs. }
  split; [intros i Hi; split; [wgl|]; split; [wgl | wgl]|].
  split; [wgl|]. split; [wgl|]. split; [wgl|]. split; [wgl|]. split; [wgl|].
  split; [wgl|]. split; [wgl|]. split; [wgl|]. split; [wgl | wgl].
Qed.

(* ---- the library's notices and transitions (TSess set_state_m, session_lost_m) ---- *)

Definition rxe0_gset (X : list byte) (g st old why : Z) : list byte :=
  set_GOT_n (set_GOT_t_reason (set_GOT_t_old (set_GOT_t_state X g st) g old) g why) (g + 1).

(* notice (FT:941-949) of an N_STATE notice that is not ONLINE *)
Lemma rxe0_notice_state : forall I F X st old why g, GOT_n X = g -> 0 <= g < TRANS_MAX -> st <> S_ONLINE ->
  notice_m I F X (Ntc DIGINET_N_STATE st old why 0 0 0 0 None [] 0) = Some (rxe0_gset X g st old why, tt).
Proof.
  intros I F X st old why g Hg Hr Hst. unfold notice_m. cbv zeta. cbn [n_kind n_state n_old n_reason].
  change (DIGINET_N_STATE =? N_STATE) with true. cbv beta iota.
  rewrite Hg, (proj2 (Z.ltb_lt g TRANS_MAX) (proj2 Hr)), (proj2 (Z.ltb_ge g 0) (proj1 Hr)). cbv beta iota.
  unfold int_inc. rewrite (proj2 (Z.eqb_neq g INT_MAX)) by (unfold TRANS_MAX, INT_MAX in *; lia). cbv beta iota.
  rewrite (proj2 (Z.eqb_neq st S_ONLINE) Hst). cbv beta iota. unfold rxe0_gset. exact eq_refl.
Qed.

(* notice (FT:959-961) of an N_DESK notice: GOT.desk d goes to d + 1 *)
Lemma rxe0_notice_desk : forall I F X n d, n_kind n = DIGINET_N_DESK -> GOT_desk X = d -> 0 <= d <= 1 ->
  notice_m I F X n = check_state_desk_m I F (set_GOT_desk X (d + 1)) n.
Proof.
  intros I F X n d Hk Hg Hd. unfold notice_m. cbv zeta. rewrite Hk.
  change (DIGINET_N_DESK =? N_STATE) with false. change (DIGINET_N_DESK =? N_ACKED) with false.
  change (DIGINET_N_DESK =? N_ACK_LOST) with false. change (DIGINET_N_DESK =? N_DESK) with true.
  cbv beta iota. rewrite Hg, (rxe0_int_inc d ltac:(lia)). cbv beta iota. exact eq_refl.
Qed.

(* set_state (DS:79-86) to a state other than ONLINE *)
Lemma rxe0_set_state : forall I F X st why g, length X = WN -> S_state X <> st -> S_notify X = ti_notice I ->
  GOT_n X = g -> 0 <= g < TRANS_MAX -> st <> S_ONLINE ->
  set_state_m I F X st why = Some (rxe0_gset (set_S_state X st) g st (S_state X) why, tt).
Proof.
  intros I F X st why g HX Hs Hno Hg Hr Hst. unfold set_state_m. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) Hs). cbv beta iota.
  assert (E1 : S_notify (set_S_state X st) = ti_notice I) by (rewrite <- Hno; wget).
  assert (E2 : GOT_n (set_S_state X st) = g) by (rewrite <- Hg; wget).
  unfold call_notify. rewrite E1, (Z.eqb_refl (ti_notice I)). cbv beta iota.
  exact (rxe0_notice_state I F (set_S_state X st) st (S_state X) why g E2 Hr Hst).
Qed.

(* the entries' range stands for the one entry the notice writes (at GOT.n, FT:942-946) *)
Definition R_llost : list (Z * Z) :=
  [(A_S_inflight, 4); (A_S_desk_counter_valid, 4); (A_S_state, 4); (A_GOT_t_state 0, 192); (A_GOT_n, 4)].

(* session_lost (DS:160-165) of an online session: the transition at k = GOT.n *)
Lemma rxe0_lib_lost : forall I F X k, length X = WN -> S_state X = S_ONLINE -> S_notify X = ti_notice I ->
  GOT_n X = k -> 0 <= k <= 4 ->
  exists X', session_lost_m I F X DIGINET_R_DESK_OFFLINE = Some (X', tt) /\ length X' = WN /\
    wframe (in_rs R_llost) X X' /\ rxe0_tkg X X' k /\
    S_state X' = S_IDLE /\ S_inflight X' = 0 /\ S_desk_counter_valid X' = 0 /\ GOT_n X' = k + 1 /\
    GOT_t_state X' k = S_IDLE /\ GOT_t_old X' k = S_ONLINE /\ GOT_t_reason X' k = R_DESK_OFFLINE.
Proof.
  intros I F X k HX Hs Hno Hn Hk.
  remember (set_S_desk_counter_valid (set_S_inflight X 0) 0) as Y eqn:EY.
  assert (HY : length Y = WN) by (subst Y; wlen).
  assert (Ys : S_state Y = S_ONLINE) by (rewrite <- Hs; subst Y; wget).
  assert (Yno : S_notify Y = ti_notice I) by (rewrite <- Hno; subst Y; wget).
  assert (Yn : GOT_n Y = k) by (transitivity (GOT_n X); [subst Y; wget | exact Hn]).
  exists (rxe0_gset (set_S_state Y DIGINET_S_IDLE) k DIGINET_S_IDLE S_ONLINE DIGINET_R_DESK_OFFLINE).
  split.
  { unfold session_lost_m. cbv zeta. rewrite <- EY. rewrite <- Ys.
    apply rxe0_set_state; [exact HY | rewrite Ys; unfold S_ONLINE, DIGINET_S_IDLE; lia | exact Yno | exact Yn
      | unfold TRANS_MAX; lia | unfold S_ONLINE, DIGINET_S_IDLE; lia]. }
  unfold rxe0_gset. subst Y. rxe0_consts.
  split; [wlenl|]. split.
  { assert (Ek : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
    destruct Ek as [-> | [-> | [-> | [-> | ->]]]]; wfrs. }
  split; [intros i Hi; split; [wgl|]; split; [wgl | wgl]|].
  split; [wgl|]. split; [wgl|]. split; [wgl|]. split; [wgl|].
  split; [wgl|]. split; [wgl | wgl].
Qed.

(* ---- io_send (FT:823-899) of the wake E2 (send_control DS:97-109 from diginet_session_wake DS:134-136) ---- *)

(* io_send's writes before the frame in flight (FT:829, :849-850), GOT.e2 to e2 *)
Definition rxe0_e2w (Y : list byte) (e2 send : Z) : list byte :=
  set_g_last_counter (set_GOT_e2 (set_g_fail_next Y 0) e2) send.

Definition rxe0_fly (Y : list byte) (send now : Z) (f : list byte) : list byte :=
  set_M_fly_frame (set_M_fly_len (set_M_fly_sent (set_M_fly_retries (set_M_fly_counter
    (set_M_fly_cmd (set_M_fly_on Y 1) DIGINET_CMD_WAKE) send) 0) now) 60) f.

Lemma rxe0_wake_build_ok : forall dst send mode, length dst = 6%nat ->
  (mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO) -> 0 <= send < 2 ^ 32 ->
  build_ok dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode.
Proof.
  intros dst send mode Hd Hm Hs. apply control_build_ok; [exact Hd | reflexivity | exact Hm | exact Hs | |].
  - split; [lia | vm_compute; reflexivity].
  - unfold DIGINET_CMD_WAKE. split; [lia | vm_compute; reflexivity].
Qed.

Lemma rxe0_cmd_wake_ack : (DIGINET_CMD_WAKE =? SPEC_CMD_ACK) = false.
Proof. reflexivity. Qed.
Lemma rxe0_cmd_wake_e2 : (DIGINET_CMD_WAKE =? SPEC_CMD_E2) = true.
Proof. reflexivity. Qed.
Lemma rxe0_60_max : (60 <? SPEC_MAX_FRAME) = true.
Proof. reflexivity. Qed.

(* what io_send's E2 path reads of the world it is handed; e = GOT.e2 *)
Record rxe0_io (Y dst : list byte) (send mode e : Z) : Prop := {
  io_len : length Y = WN;
  io_dst : length dst = 6%nat;
  io_mode : mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO;
  io_send_rng : 0 <= send < 2 ^ 32;
  io_known : M_desk_known Y = 1;
  io_desk : M_desk Y = dst;
  io_sum : Cfg_sum_mode Y = mode;
  io_foreign : M_foreign Y = 0;
  io_host : M_host_counter Y = send;
  io_e2 : GOT_e2 Y = e;
  io_e2_rng : 0 <= e <= 1;
}.

(* the checks of FT:831 and :846-848 pass, and the reads io_send makes *)
Lemma rxe0_io_facts : forall (HL : links) Y dst send mode e, rxe0_io Y dst send mode e ->
  check_sent_frame_m (set_g_fail_next Y 0) (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode) =
    Some (set_g_fail_next Y 0, tt) /\
  check_state_wake_m (set_g_fail_next Y 0) = Some (set_g_fail_next Y 0, tt) /\
  check_latest_control_m (set_g_fail_next Y 0) (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode) =
    Some (set_g_fail_next Y 0, tt) /\
  GOT_e2 (set_g_fail_next Y 0) = e /\
  sf_cmd (rf (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode)) = DIGINET_CMD_WAKE /\
  sf_send (rf (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode)) = send /\
  sf_retry (rf (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode)) = 0 /\
  Z.of_nat (length (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode)) = 60 /\
  length (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode) = 60%nat.
Proof.
  intros HL Y dst send mode e [HY Hd Hm Hs Hk Hdk Hsm Hfo Hhc He2 Her].
  pose proof (rxe0_wake_build_ok dst send mode Hd Hm Hs) as Hok.
  assert (K0 : M_desk_known (set_g_fail_next Y 0) = 1) by (rewrite <- Hk; wget).
  assert (D0 : M_desk (set_g_fail_next Y 0) = dst) by (rewrite <- Hdk; wget).
  assert (S0 : Cfg_sum_mode (set_g_fail_next Y 0) = mode) by (rewrite <- Hsm; wget).
  assert (F0 : M_foreign (set_g_fail_next Y 0) = 0) by (rewrite <- Hfo; wget).
  assert (H0 : M_host_counter (set_g_fail_next Y 0) = send) by (rewrite <- Hhc; wget).
  pose proof (rf_lib_frame HL dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode Hok) as R. cbv zeta in R.
  destruct R as (Hlen & _ & _ & _ & _ & Hcm & Hse & _ & Hre & _).
  change (frame_len (length (@nil byte))) with 60 in Hlen.
  split; [exact (sent_frame_ok HL _ dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode Hok eq_refl K0 D0 S0)|].
  split; [unfold check_state_wake_m; rewrite F0, rxe0_truth0; cbv beta iota; exact eq_refl|].
  split; [exact (latest_control_ok HL _ dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode Hok (eq_sym H0))|].
  split; [transitivity (GOT_e2 Y); [wget | exact He2]|].
  split; [exact Hcm|]. split; [exact Hse|]. split; [exact Hre|]. split; [exact Hlen|]. lia.
Qed.

Lemma rxe0_io_send_ok : forall (HL : links) I Y dst send mode e, rxe0_io Y dst send mode e -> g_fail_next Y = 0 ->
  io_send_m I Y (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode) =
  Some (rxe0_fly (rxe0_e2w Y (e + 1) send) send (g_now Y) (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode),
        0).
Proof.
  intros HL I Y dst send mode e Hio Hfn.
  destruct (rxe0_io_facts HL Y dst send mode e Hio) as (CS & CW & CL & G0 & Hcm & Hse & Hre & Hlen & Hln).
  pose proof (io_len _ _ _ _ _ Hio) as HY.
  pose proof (io_e2_rng _ _ _ _ _ Hio) as Her.
  assert (GN : g_now (rxe0_e2w Y (e + 1) send) = g_now Y) by (unfold rxe0_e2w; wget).
  unfold io_send_m. cbv beta zeta.
  rewrite CS. cbv beta iota.
  rewrite Hcm, rxe0_cmd_wake_ack, rxe0_cmd_wake_e2. cbv beta iota delta [orb].
  rewrite Hre, rxe0_truth0. cbv beta iota.
  rewrite CW. cbv beta iota. rewrite CL. cbv beta iota.
  rewrite G0, (rxe0_int_inc e ltac:(lia)). cbv beta iota.
  rewrite Hse, Hfn, rxe0_truth0. cbv beta iota.
  rewrite Hlen, rxe0_60_max. cbv beta iota.
  rewrite (@firstn_all2 byte (Z.to_nat 60) (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode))
    by (rewrite Hln; apply Nat.le_refl).
  change (set_g_last_counter (set_GOT_e2 (set_g_fail_next Y 0) (e + 1)) send) with (rxe0_e2w Y (e + 1) send).
  rewrite GN. unfold rxe0_fly. wsyn.
Qed.

Lemma rxe0_io_send_fail : forall (HL : links) I Y dst send mode e, rxe0_io Y dst send mode e -> g_fail_next Y = 1 ->
  io_send_m I Y (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode) = Some (rxe0_e2w Y (e + 1) send, - EIO).
Proof.
  intros HL I Y dst send mode e Hio Hfn.
  destruct (rxe0_io_facts HL Y dst send mode e Hio) as (CS & CW & CL & G0 & Hcm & Hse & Hre & Hlen & Hln).
  pose proof (io_e2_rng _ _ _ _ _ Hio) as Her.
  unfold io_send_m. cbv beta zeta.
  rewrite CS. cbv beta iota.
  rewrite Hcm, rxe0_cmd_wake_ack, rxe0_cmd_wake_e2. cbv beta iota delta [orb].
  rewrite Hre, rxe0_truth0. cbv beta iota.
  rewrite CW. cbv beta iota. rewrite CL. cbv beta iota.
  rewrite G0, (rxe0_int_inc e ltac:(lia)). cbv beta iota.
  rewrite Hse, Hfn, rxe0_truth1. cbv beta iota.
  unfold rxe0_e2w. wsyn.
Qed.

(* ---- diginet_session_wake (DS:119-145) of an idle session whose desk is known and not foreign ---- *)

(* the entries' range stands for the one entry the notice writes (at GOT.n, FT:942-946) *)
Definition R_got : list (Z * Z) := [(A_GOT_t_state 0, 192); (A_GOT_n, 4)].

Definition R_lwake : list (Z * Z) :=
  [(A_S_e1_named_us, 4); (A_S_wake_acked, 4); (A_S_wake_sent_us, 8); (OFF_g_fail_next, 4); (A_GOT_e2, 4);
   (OFF_g_last_counter, 4); (A_M_fly_on, 1552); (A_S_stats_tx_frames, 8); (A_S_inflight, 1548);
   (A_S_stats_tx_wakes, 8); (A_S_state, 4); (A_GOT_t_state 0, 192); (A_GOT_n, 4)].

Definition R_lwfail : list (Z * Z) :=
  [(A_S_e1_named_us, 4); (A_S_wake_acked, 4); (A_S_wake_sent_us, 8); (OFF_g_fail_next, 4); (A_GOT_e2, 4);
   (OFF_g_last_counter, 4)].

Definition rxe0_lw_pre (X : list byte) (now : Z) : list byte :=
  set_S_wake_sent_us (set_S_wake_acked (set_S_e1_named_us X 0) 0) now.

(* what diginet_session_wake reads, besides io_send's reads *)
Record rxe0_lw (I : timg) (X dst : list byte) (send mode e : Z) : Prop := {
  lw_io : rxe0_io X dst send mode e;
  lw_known : S_desk_known X = 1;
  lw_foreign : S_foreign X = 0;
  lw_dst : S_desk_mac X = dst;
  lw_host : S_cfg_host_mac X = HOST;
  lw_counter : S_host_counter X = send;
  lw_sum : S_cfg_sum_mode X = mode;
  lw_send : S_io_send X = ti_io_send I;
  lw_notify : S_notify X = ti_notice I;
  lw_state : S_state X = S_IDLE;
}.

Lemma rxe0_lw_pre_ok : forall I X dst send mode e now, rxe0_lw I X dst send mode e ->
  rxe0_lw I (rxe0_lw_pre X now) dst send mode e /\ g_now (rxe0_lw_pre X now) = g_now X /\
  g_fail_next (rxe0_lw_pre X now) = g_fail_next X /\ GOT_n (rxe0_lw_pre X now) = GOT_n X.
Proof.
  intros I X dst send mode e now [[HX Hd Hm Hs Hk Hdk Hsm Hfo Hhc He2 Her] Sk Sf Sd Sh Sc Sm Sio Sno Sst].
  unfold rxe0_lw_pre.
  split; [|split; [wg|split; [wg|wg]]].
  constructor; [constructor|..].
  - wlen.
  - exact Hd.
  - exact Hm.
  - exact Hs.
  - rewrite <- Hk; wg.
  - rewrite <- Hdk; wg.
  - rewrite <- Hsm; wg.
  - rewrite <- Hfo; wg.
  - rewrite <- Hhc; wg.
  - transitivity (GOT_e2 X); [wg | exact He2].
  - exact Her.
  - rewrite <- Sk; wg.
  - rewrite <- Sf; wg.
  - rewrite <- Sd; wg.
  - rewrite <- Sh; wg.
  - rewrite <- Sc; wg.
  - rewrite <- Sm; wg.
  - rewrite <- Sio; wg.
  - rewrite <- Sno; wg.
  - rewrite <- Sst; wg.
Qed.

Lemma rxe0_build_60 : forall (HL : links) (dst : list byte) send mode, length dst = 6%nat ->
  (mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO) -> 0 <= send < 2 ^ 32 ->
  diginet_frame_build_code [] DIGINET_MIN_FRAME_LEN mode = DIGINET_MIN_FRAME_LEN.
Proof.
  intros HL dst send mode Hd Hm Hs.
  exact (proj1 (control_frame_ok HL [] dst HOST send 0 DIGINET_CMD_WAKE mode (rxe0_wake_build_ok dst send mode Hd Hm Hs))).
Qed.

(* the wake's writes in layers (DS:129-131, io_send, send_raw, DS:139-143), each over a world variable: a read
   walks one layer only *)
Definition rxe0_W3 (Y : list byte) : list byte := set_S_stats_tx_frames Y (u64 (S_stats_tx_frames Y + 1)).
Definition rxe0_W4 (Y : list byte) (fw : list byte) : list byte :=
  set_S_stats_tx_wakes (set_S_inflight_len (set_S_inflight_frame Y fw) 60)
    (u64 (S_stats_tx_wakes (set_S_inflight_len (set_S_inflight_frame Y fw) 60) + 1)).
Definition rxe0_W5 (Y : list byte) (send now : Z) : list byte :=
  set_S_inflight_sent_us (set_S_inflight_retries (set_S_inflight_counter (set_S_inflight Y 1) send) 0) now.

Definition RW0 : list (Z * Z) := [(A_S_e1_named_us, 4); (A_S_wake_acked, 4); (A_S_wake_sent_us, 8)].
Definition RW1 : list (Z * Z) := [(OFF_g_fail_next, 4); (A_GOT_e2, 4); (OFF_g_last_counter, 4)].
Definition RW2 : list (Z * Z) := [(A_M_fly_on, 1552)].
Definition RW3 : list (Z * Z) := [(A_S_stats_tx_frames, 8)].
Definition RW4 : list (Z * Z) := [(A_S_inflight, 1548); (A_S_stats_tx_wakes, 8)].
Definition RW5 : list (Z * Z) := [(A_S_inflight, 4); (A_S_inflight_counter, 16)].

Lemma rxe0_L0 : forall X now, length X = WN -> 0 <= now < 2 ^ 64 ->
  length (rxe0_lw_pre X now) = WN /\ wframe (in_rs RW0) X (rxe0_lw_pre X now) /\
  S_e1_named_us (rxe0_lw_pre X now) = 0 /\ S_wake_acked (rxe0_lw_pre X now) = 0 /\
  S_wake_sent_us (rxe0_lw_pre X now) = now.
Proof. intros X now HX Hnow. unfold rxe0_lw_pre. split; [wlen|]. split; [wfrs|]. split; [wg|]. split; [wg|]. wg. Qed.

Lemma rxe0_L1 : forall Y e2 send, length Y = WN -> 0 <= e2 <= 2 -> 0 <= send < 2 ^ 32 ->
  length (rxe0_e2w Y e2 send) = WN /\ wframe (in_rs RW1) Y (rxe0_e2w Y e2 send) /\
  g_fail_next (rxe0_e2w Y e2 send) = 0 /\ GOT_e2 (rxe0_e2w Y e2 send) = e2.
Proof. intros Y e2 send HY He Hs. unfold rxe0_e2w. split; [wlen|]. split; [wfrs|]. split; [wg|]. wg. Qed.

Lemma rxe0_L2 : forall Y send now fw, length Y = WN -> length fw = 60%nat -> 0 <= send < 2 ^ 32 ->
  0 <= now < 2 ^ 64 ->
  length (rxe0_fly Y send now fw) = WN /\ wframe (in_rs RW2) Y (rxe0_fly Y send now fw) /\
  M_fly_on (rxe0_fly Y send now fw) = 1 /\ M_fly_cmd (rxe0_fly Y send now fw) = SPEC_CMD_E2 /\
  M_fly_counter (rxe0_fly Y send now fw) = send /\ M_fly_retries (rxe0_fly Y send now fw) = 0 /\
  M_fly_sent (rxe0_fly Y send now fw) = now /\ M_fly_len (rxe0_fly Y send now fw) = 60 /\
  sub (rxe0_fly Y send now fw) A_M_fly_frame 60 = fw.
Proof.
  intros Y send now fw HY Hf Hs Hnow. unfold rxe0_fly, DIGINET_CMD_WAKE, SPEC_CMD_E2.
  split; [wlen|]. split; [wfrs|].
  split; [wg|]. split; [wg|]. split; [wg|]. split; [wg|]. split; [wg|]. split; [wg|]. wg.
Qed.

Lemma rxe0_L3 : forall Y, length Y = WN -> length (rxe0_W3 Y) = WN /\ wframe (in_rs RW3) Y (rxe0_W3 Y).
Proof. intros Y HY. unfold rxe0_W3. split; [wlen | wfrs]. Qed.

Lemma rxe0_L4 : forall Y fw, length Y = WN -> length fw = 60%nat ->
  length (rxe0_W4 Y fw) = WN /\ wframe (in_rs RW4) Y (rxe0_W4 Y fw) /\
  S_inflight_len (rxe0_W4 Y fw) = 60 /\ sub (rxe0_W4 Y fw) A_S_inflight_frame 60 = fw.
Proof. intros Y fw HY Hf. unfold rxe0_W4. split; [wlen|]. split; [wfrs|]. split; [wg|]. wg. Qed.

Lemma rxe0_L5 : forall Y send now, length Y = WN -> 0 <= send < 2 ^ 32 -> 0 <= now < 2 ^ 64 ->
  length (rxe0_W5 Y send now) = WN /\ wframe (in_rs RW5) Y (rxe0_W5 Y send now) /\
  S_inflight (rxe0_W5 Y send now) = 1 /\ S_inflight_counter (rxe0_W5 Y send now) = send /\
  S_inflight_retries (rxe0_W5 Y send now) = 0 /\ S_inflight_sent_us (rxe0_W5 Y send now) = now.
Proof.
  intros Y send now HY Hs Hnow. unfold rxe0_W5.
  split; [wlen|]. split; [wfrs|]. split; [wg|]. split; [wg|]. split; [wg|]. wg.
Qed.

Lemma rxe0_istart : forall Y c t, inflight_start_m Y c t = Some (rxe0_W5 Y c t, tt).
Proof. intros. unfold inflight_start_m, rxe0_W5. exact eq_refl. Qed.

(* send_control (DS:97-109) of the wake, on the world after DS:129-131 *)
Lemma rxe0_send_control_ok : forall (HL : links) I F Y dst send mode e, rxe0_lw I Y dst send mode e ->
  g_fail_next Y = 0 ->
  send_control_m I F Y DIGINET_CMD_WAKE 0 =
  Some (rxe0_W3 (rxe0_fly (rxe0_e2w Y (e + 1) send) send (g_now Y)
                  (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode)),
        (0, lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode)).
Proof.
  intros HL I F Y dst send mode e [Hio Sk Sf Sd Sh Sc Sm Sio Sno Sst] Hfn.
  pose proof Hio as [HY Hd Hm Hs _ _ _ _ _ _ _].
  unfold send_control_m. cbv zeta. rewrite Sm, (rxe0_build_60 HL dst send mode Hd Hm Hs).
  change (DIGINET_MIN_FRAME_LEN <? 0) with false. cbv beta iota.
  rewrite Sd, Sh, Sc. unfold send_raw_m, call_send. rewrite Sio, (Z.eqb_refl (ti_io_send I)). cbv beta iota.
  rewrite (rxe0_io_send_ok HL I Y dst send mode e Hio Hfn). cbv beta iota.
  change (0 =? 0) with true. cbv beta iota. unfold rxe0_W3. wsyn.
Qed.

Lemma rxe0_send_control_fail : forall (HL : links) I F Y dst send mode e, rxe0_lw I Y dst send mode e ->
  g_fail_next Y = 1 ->
  send_control_m I F Y DIGINET_CMD_WAKE 0 =
  Some (rxe0_e2w Y (e + 1) send, (- EIO, lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode)).
Proof.
  intros HL I F Y dst send mode e [Hio Sk Sf Sd Sh Sc Sm Sio Sno Sst] Hfn.
  pose proof Hio as [HY Hd Hm Hs _ _ _ _ _ _ _].
  unfold send_control_m. cbv zeta. rewrite Sm, (rxe0_build_60 HL dst send mode Hd Hm Hs).
  change (DIGINET_MIN_FRAME_LEN <? 0) with false. cbv beta iota.
  rewrite Sd, Sh, Sc. unfold send_raw_m, call_send. rewrite Sio, (Z.eqb_refl (ti_io_send I)). cbv beta iota.
  rewrite (rxe0_io_send_fail HL I Y dst send mode e Hio Hfn). cbv beta iota.
  change (- EIO =? 0) with false. cbv beta iota. wsyn.
Qed.

Lemma rxe0_lib_wake_fail : forall (HL : links) I F X dst send mode e now, rxe0_lw I X dst send mode e ->
  g_fail_next X = 1 -> g_now X = now ->
  exists X', diginet_session_wake_m I F X now = Some (X', - EIO) /\ length X' = WN /\
    wframe (in_rs R_lwfail) X X' /\
    S_e1_named_us X' = 0 /\ S_wake_acked X' = 0 /\ S_wake_sent_us X' = now /\ g_fail_next X' = 0 /\
    GOT_e2 X' = e + 1.
Proof.
  intros HL I F X dst send mode e now Hlw Hfn Hnow. subst now.
  pose proof Hlw as [[HX Hd Hm Hs _ _ _ _ _ _ Her] Sk Sf _ _ _ _ _ _ _].
  destruct (rxe0_lw_pre_ok I X dst send mode e (g_now X) Hlw) as (HlwY & GY & FY & NY).
  rewrite Hfn in FY.
  exists (rxe0_e2w (rxe0_lw_pre X (g_now X)) (e + 1) send). split.
  { unfold diginet_session_wake_m. cbv zeta. rewrite Sk, Sf.
    change (1 =? 0) with false. change (0 =? 0) with true. cbv beta iota delta [negb].
    change (set_S_wake_sent_us (set_S_wake_acked (set_S_e1_named_us X 0) 0) (g_now X)) with
      (rxe0_lw_pre X (g_now X)).
    rewrite (rxe0_send_control_fail HL I F (rxe0_lw_pre X (g_now X)) dst send mode e HlwY FY).
    cbv beta iota. change (- EIO <? 0) with true. cbv beta iota. exact eq_refl. }
  unfold rxe0_e2w, rxe0_lw_pre.
  split; [wlen|]. split; [wfrs|].
  split; [wg|]. split; [wg|]. split; [wg|]. split; [wg|]. wg.
Qed.

(* the wake that goes out: GOT.e2 e to e + 1, and the transition IDLE -> WAKING at k = GOT.n *)
Lemma rxe0_lib_wake_ok : forall (HL : links) I F X dst send mode e now k, rxe0_lw I X dst send mode e ->
  g_fail_next X = 0 -> g_now X = now -> GOT_n X = k -> 0 <= k <= 5 ->
  exists X', diginet_session_wake_m I F X now = Some (X', DIGINET_OK) /\ length X' = WN /\
    wframe (in_rs R_lwake) X X' /\ rxe0_tkg X X' k /\
    S_e1_named_us X' = 0 /\ S_wake_acked X' = 0 /\ S_wake_sent_us X' = now /\ g_fail_next X' = 0 /\
    GOT_e2 X' = e + 1 /\
    S_state X' = S_WAKING /\ GOT_n X' = k + 1 /\
    GOT_t_state X' k = S_WAKING /\ GOT_t_old X' k = S_IDLE /\ GOT_t_reason X' k = R_WAKE /\
    S_inflight X' = 1 /\ S_inflight_counter X' = send /\ S_inflight_retries X' = 0 /\ S_inflight_sent_us X' = now /\
    S_inflight_len X' = 60 /\
    M_fly_on X' = 1 /\ M_fly_cmd X' = SPEC_CMD_E2 /\ M_fly_counter X' = send /\ M_fly_retries X' = 0 /\
    M_fly_sent X' = now /\ M_fly_len X' = 60 /\
    sub X' A_M_fly_frame 60 = lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode /\
    sub X' A_S_inflight_frame 60 = lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode.
Proof.
  intros HL I F X dst send mode e now k Hlw Hfn Hnow Hgn Hkr. subst now.
  pose proof Hlw as [[HX Hd Hm Hs _ _ _ _ _ _ Her] Sk Sf _ _ _ _ _ Sno Sst].
  destruct (rxe0_lw_pre_ok I X dst send mode e (g_now X) Hlw) as (HlwY & GY & FY & NY).
  rewrite Hfn in FY. rewrite Hgn in NY.
  destruct (rxe0_io_facts HL _ _ _ _ _ (lw_io _ _ _ _ _ _ HlwY)) as (_ & _ & _ & _ & _ & _ & _ & Hlen & Hln).
  pose proof HlwY as [[HY _ _ _ _ _ _ _ _ _ _] _ _ _ _ ScY _ _ SnoY SstY].
  pose proof (rw_u_range X OFF_g_now 8) as Hnow. change (8 * Z.of_nat 8) with 64 in Hnow.
  change (u_at X OFF_g_now 8) with (g_now X) in Hnow.
  (* the frame stays a variable: no tactic may compute the length of lib_frame of variables *)
  remember (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode) as fw eqn:Efw.
  try rewrite <- Efw in Hlen. try rewrite <- Efw in Hln.
  (* the layers *)
  destruct (rxe0_L0 X (g_now X) HX Hnow) as (L0 & F0 & V0a & V0b & V0c).
  set (Y0 := rxe0_lw_pre X (g_now X)) in *.
  destruct (rxe0_L1 Y0 (e + 1) send L0 ltac:(lia) Hs) as (L1 & F1 & V1a & V1b).
  set (Y1 := rxe0_e2w Y0 (e + 1) send) in *.
  destruct (rxe0_L2 Y1 send (g_now X) fw L1 Hln Hs Hnow) as (L2 & F2 & V2a & V2b & V2c & V2d & V2e & V2f & V2g).
  set (Y2 := rxe0_fly Y1 send (g_now X) fw) in *.
  destruct (rxe0_L3 Y2 L2) as (L3 & F3).
  set (Y3 := rxe0_W3 Y2) in *.
  destruct (rxe0_L4 Y3 fw L3 Hln) as (L4 & F4 & V4a & V4b).
  set (Y4 := rxe0_W4 Y3 fw) in *.
  destruct (rxe0_L5 Y4 send (g_now X) L4 Hs Hnow) as (L5 & F5 & V5a & V5b & V5c & V5d).
  set (Y5 := rxe0_W5 Y4 send (g_now X)) in *.
  pose proof (wframe_trans_rs _ _ _ _ _ F4 F5) as G35.
  pose proof (wframe_trans_rs _ _ _ _ _ F3 G35) as G25.
  pose proof (wframe_trans_rs _ _ _ _ _ F2 G25) as G15.
  pose proof (wframe_trans_rs _ _ _ _ _ F1 G15) as G05.
  pose proof (wframe_trans_rs _ _ _ _ _ F1 (wframe_trans_rs _ _ _ _ _ F2 (wframe_trans_rs _ _ _ _ _ F3 F4))) as G04.
  assert (E4 : S_host_counter Y4 = send) by (transitivity (S_host_counter Y0); [fget G04 | exact ScY]).
  assert (Z2 : S_state Y5 = S_IDLE) by (transitivity (S_state Y0); [fget G05 | exact SstY]).
  assert (Z3 : S_notify Y5 = ti_notice I) by (transitivity (S_notify Y0); [fget G05 | exact SnoY]).
  assert (Z4 : GOT_n Y5 = k) by (transitivity (GOT_n Y0); [fget G05 | exact NY]).
  exists (rxe0_gset (set_S_state Y5 DIGINET_S_WAKING) k DIGINET_S_WAKING S_IDLE DIGINET_R_WAKE). split.
  { unfold diginet_session_wake_m. cbv zeta. rewrite Sk, Sf.
    change (1 =? 0) with false. change (0 =? 0) with true. cbv beta iota delta [negb].
    change (set_S_wake_sent_us (set_S_wake_acked (set_S_e1_named_us X 0) 0) (g_now X)) with Y0.
    rewrite (rxe0_send_control_ok HL I F Y0 dst send mode e HlwY FY).
    rewrite <- Efw. rewrite GY.
    change (rxe0_W3 (rxe0_fly (rxe0_e2w Y0 (e + 1) send) send (g_now X) fw)) with Y3.
    cbv beta iota. change (0 <? 0) with false. cbv beta iota.
    rewrite Hlen.
    change (set_S_stats_tx_wakes (set_S_inflight_len (set_S_inflight_frame Y3 fw) 60)
              (u64 (S_stats_tx_wakes (set_S_inflight_len (set_S_inflight_frame Y3 fw) 60) + 1))) with Y4.
    rewrite E4, (rxe0_istart Y4 send (g_now X)). cbv beta iota.
    change (rxe0_W5 Y4 send (g_now X)) with Y5.
    rewrite (rxe0_set_state I F Y5 DIGINET_S_WAKING DIGINET_R_WAKE k L5
               ltac:(rewrite Z2; unfold S_IDLE, DIGINET_S_WAKING; lia) Z3 Z4
               ltac:(unfold TRANS_MAX; lia) ltac:(unfold S_ONLINE, DIGINET_S_WAKING; lia)).
    rewrite Z2. cbv beta iota. exact eq_refl. }
  (* the last layer: the state and its notice *)
  assert (L6 : length (set_S_state Y5 DIGINET_S_WAKING) = WN) by wlen.
  assert (F6 : wframe (in_rs [(A_S_state, 4)]) Y5 (set_S_state Y5 DIGINET_S_WAKING)) by wfrs.
  assert (V6 : S_state (set_S_state Y5 DIGINET_S_WAKING) = S_WAKING) by (unfold DIGINET_S_WAKING, S_WAKING; wg).
  set (Y6 := set_S_state Y5 DIGINET_S_WAKING) in *.
  pose proof (wframe_trans_rs _ _ _ _ _ F5 F6) as G46.
  pose proof (wframe_trans_rs _ _ _ _ _ F4 G46) as G36.
  pose proof (wframe_trans_rs _ _ _ _ _ F3 G36) as G26.
  pose proof (wframe_trans_rs _ _ _ _ _ F2 G26) as G16.
  pose proof (wframe_trans_rs _ _ _ _ _ F1 G16) as G06.
  pose proof (wframe_trans_rs _ _ _ _ _ F0 G06) as Gx6.
  assert (W0a : S_e1_named_us Y6 = 0) by (transitivity (S_e1_named_us Y0); [fget G06 | exact V0a]).
  assert (W0b : S_wake_acked Y6 = 0) by (transitivity (S_wake_acked Y0); [fget G06 | exact V0b]).
  assert (W0c : S_wake_sent_us Y6 = g_now X) by (transitivity (S_wake_sent_us Y0); [fget G06 | exact V0c]).
  assert (W1a : g_fail_next Y6 = 0) by (transitivity (g_fail_next Y1); [fget G16 | exact V1a]).
  assert (W1b : GOT_e2 Y6 = e + 1) by (transitivity (GOT_e2 Y1); [fget G16 | exact V1b]).
  assert (W5a : S_inflight Y6 = 1) by (transitivity (S_inflight Y5); [fget F6 | exact V5a]).
  assert (W5b : S_inflight_counter Y6 = send) by (transitivity (S_inflight_counter Y5); [fget F6 | exact V5b]).
  assert (W5c : S_inflight_retries Y6 = 0) by (transitivity (S_inflight_retries Y5); [fget F6 | exact V5c]).
  assert (W5d : S_inflight_sent_us Y6 = g_now X) by (transitivity (S_inflight_sent_us Y5); [fget F6 | exact V5d]).
  assert (W4a : S_inflight_len Y6 = 60) by (transitivity (S_inflight_len Y4); [fget G46 | exact V4a]).
  assert (W4b : sub Y6 A_S_inflight_frame 60 = fw).
  { transitivity (sub Y4 A_S_inflight_frame 60); [apply (fr_sub _ _ _ _ _ G46); [wnum | vm_compute; reflexivity]
                                                  | exact V4b]. }
  assert (W2a : M_fly_on Y6 = 1) by (transitivity (M_fly_on Y2); [fget G26 | exact V2a]).
  assert (W2b : M_fly_cmd Y6 = SPEC_CMD_E2) by (transitivity (M_fly_cmd Y2); [fget G26 | exact V2b]).
  assert (W2c : M_fly_counter Y6 = send) by (transitivity (M_fly_counter Y2); [fget G26 | exact V2c]).
  assert (W2d : M_fly_retries Y6 = 0) by (transitivity (M_fly_retries Y2); [fget G26 | exact V2d]).
  assert (W2e : M_fly_sent Y6 = g_now X) by (transitivity (M_fly_sent Y2); [fget G26 | exact V2e]).
  assert (W2f : M_fly_len Y6 = 60) by (transitivity (M_fly_len Y2); [fget G26 | exact V2f]).
  assert (W2g : sub Y6 A_M_fly_frame 60 = fw).
  { transitivity (sub Y2 A_M_fly_frame 60); [apply (fr_sub _ _ _ _ _ G26); [wnum | vm_compute; reflexivity]
                                             | exact V2g]. }
  clear G46 G36 G26 G16 G06 F0 F1 F2 F3 F4 F5 V0a V0b V0c V1a V1b V2a V2b V2c V2d V2e V2f V2g V4a V4b
    V5a V5b V5c V5d.
  assert (L7 : length (rxe0_gset Y6 k DIGINET_S_WAKING S_IDLE DIGINET_R_WAKE) = WN) by (unfold rxe0_gset; wlenl).
  (* the frame of the notice: k concrete for the range list *)
  assert (F7 : wframe (in_rs R_got) Y6 (rxe0_gset Y6 k DIGINET_S_WAKING S_IDLE DIGINET_R_WAKE)).
  { unfold rxe0_gset, R_got. assert (Ek : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
    destruct Ek as [-> | [-> | [-> | [-> | [-> | ->]]]]]; wfrs. }
  split; [exact L7|].
  split; [refine (wframe_rs_incl _ _ _ _ _ (wframe_trans_rs _ _ _ _ _ Gx6 F7)); vm_compute; reflexivity|].
  split.
  { apply (rxe0_tkg_trans _ Y6).
    - apply (rxe0_tkg_le _ _ TRANS_MAX); [exact (rxe0_tkg_fr _ _ _ Gx6 ltac:(vm_compute; reflexivity))
                                         | unfold TRANS_MAX; lia].
    - intros i Hi. unfold rxe0_gset. split; [wgl|]. split; [wgl | wgl]. }
  split; [transitivity (S_e1_named_us Y6); [fget F7 | exact W0a]|].
  split; [transitivity (S_wake_acked Y6); [fget F7 | exact W0b]|].
  split; [transitivity (S_wake_sent_us Y6); [fget F7 | exact W0c]|].
  split; [transitivity (g_fail_next Y6); [fget F7 | exact W1a]|].
  split; [transitivity (GOT_e2 Y6); [fget F7 | exact W1b]|].
  split; [transitivity (S_state Y6); [fget F7 | exact V6]|].
  split; [unfold rxe0_gset; rxe0_consts; wgl|]. split; [unfold rxe0_gset; rxe0_consts; wgl|].
  split; [unfold rxe0_gset; rxe0_consts; wgl|]. split; [unfold rxe0_gset; rxe0_consts; wgl|].
  split; [transitivity (S_inflight Y6); [fget F7 | exact W5a]|].
  split; [transitivity (S_inflight_counter Y6); [fget F7 | exact W5b]|].
  split; [transitivity (S_inflight_retries Y6); [fget F7 | exact W5c]|].
  split; [transitivity (S_inflight_sent_us Y6); [fget F7 | exact W5d]|].
  split; [transitivity (S_inflight_len Y6); [fget F7 | exact W4a]|].
  split; [transitivity (M_fly_on Y6); [fget F7 | exact W2a]|].
  split; [transitivity (M_fly_cmd Y6); [fget F7 | exact W2b]|].
  split; [transitivity (M_fly_counter Y6); [fget F7 | exact W2c]|].
  split; [transitivity (M_fly_retries Y6); [fget F7 | exact W2d]|].
  split; [transitivity (M_fly_sent Y6); [fget F7 | exact W2e]|].
  split; [transitivity (M_fly_len Y6); [fget F7 | exact W2f]|].
  split; [transitivity (sub Y6 A_M_fly_frame 60); [fget F7 | exact W2g]|].
  transitivity (sub Y6 A_S_inflight_frame 60); [fget F7 | exact W4b].
Qed.

(* ---- the prefix of the e0 branch on both sides ---- *)

(* m_rx (FT:315-318) after the desk is named: the model's tail of the e0 branch *)
Definition rxe0_mtail (B5 : list byte) : option (list byte * unit) :=
  let* (B6, _) := if M_state B5 =? S_ONLINE then m_lost_m B5 R_DESK_OFFLINE else Some (B5, tt) in
  if (M_state B6 =? S_IDLE) && truth (Cfg_auto_wake B6) then
    let* (B7, _) := m_wake_m B6 in Some (B7, tt)
  else Some (B6, tt).

(* the world after FT:303-314: OW.desk d (one more than before, FT:308), desk_off -1, desk_p, desk_body, foreign 0 *)
Definition rxe0_ma (B2 : list byte) (d dp addr : Z) : list byte :=
  set_M_foreign (set_OW_desk_body (set_OW_desk_p (set_OW_desk_off (set_OW_desk B2 d) (-1)) dp) (addr + 30)) 0.

Lemma rxe0_ma_desk : forall B2 d dp addr, length B2 = WN -> 0 <= d <= 2 -> OW_desk (rxe0_ma B2 d dp addr) = d.
Proof. intros B2 d dp addr HB Hd. unfold rxe0_ma. wg. Qed.

Definition R_mpre : list (Z * Z) :=
  [(A_OW_desk, 4); (A_OW_desk_off, 4); (A_OW_desk_p, 8); (A_OW_desk_body, 8); (A_M_foreign, 4)].

Lemma rxe0_m_prefix : forall (HL : links) I fr n B2 od, timg_ok I -> 0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  fr_code (rxbuf fr n) = DIGINET_OK -> fr_cmd (rxbuf fr n) = DIGINET_CMD_ANNOUNCE ->
  33 <= fr_body_len (rxbuf fr n) -> OW_desk B2 = od -> 0 <= od <= 1 ->
  exists dp, m_rx_sw I fr n B2 = rxe0_mtail (rxe0_ma B2 (od + 1) dp (tf_addr fr)) /\
    (forall X, option_map snd (desk_named_m I X (skipn 30 (tf_bytes fr))) = Some dp) /\ 0 <= dp < 2 ^ 64.
Proof.
  intros HL I fr n B2 od HI Hn Hc Hcmd Hbl Hd Hodr.
  pose proof (rx_frame_ok HL fr n Hn Hc) as Hf.
  pose proof (rf_blen _ _ Hf) as Hb.
  assert (Lr : SPEC_ANN_MIN <= Z.of_nat (length (skipn 30 (tf_bytes fr))))
    by (rewrite length_skipn; unfold SPEC_ANN_MIN; lia).
  pose proof HL as (_ & _ & _ & _ & HL5 & _).
  pose proof (HL5 I (set_OW_desk_off (set_OW_desk B2 (od + 1)) (-1)) (skipn 30 (tf_bytes fr)) Lr) as H5.
  cbv zeta in H5. destruct H5 as (dp & Hdn & Hp).
  exists dp. split; [|split].
  3: { pose proof (ti_spec_c24_ok I HI). pose proof (ti_spec_pc_ok I HI).
       match type of Hp with context [diginet_personality_from_name ?t] =>
         revert Hp; destruct (diginet_personality_from_name t) as [i|]; intros Hp end.
       - destruct Hp as (pp & d & _ & [(_ & -> & _) | (_ & -> & _)] & _); lia.
       - rewrite Hp. lia. }
  - unfold m_rx_sw. cbv zeta.
    rewrite (rf_cmd _ _ Hf), (rf_body_len _ _ Hf), (rf_body _ _ Hf).
    assert (E0 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E0) = true) by (rewrite Hcmd; reflexivity).
    assert (E1 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E1) = false) by (rewrite Hcmd; reflexivity).
    assert (Bl : (fr_body_len (rxbuf fr n) <? SPEC_ANN_MIN) = false) by (apply Z.ltb_ge; unfold SPEC_ANN_MIN; lia).
    rewrite E0, E1, Bl. cbv beta iota delta [orb].
    rewrite Hd, (rxe0_int_inc od ltac:(lia)). cbv beta iota.
    change (Z.to_nat 30) with 30%nat. rewrite Hdn. cbv beta iota.
    unfold rxe0_mtail, rxe0_ma. cbv beta. wsyn.
  - intros X.
    assert (L33 : (33 <= length (skipn 30 (tf_bytes fr)))%nat) by (unfold SPEC_ANN_MIN in Lr; lia).
    rewrite <- (desk_named_prefix I (set_OW_desk_off (set_OW_desk B2 (od + 1)) (-1)) X _ _ L33 L33 eq_refl).
    rewrite Hdn. reflexivity.
Qed.

(* on_announce (DS:200-206) after the N_DESK notice: the library's tail of the e0 branch *)
Definition rxe0_ltail (I : timg) (F : option tframe) (B : list byte) (now : Z) : option (list byte * unit) :=
  match (if S_state B =? DIGINET_S_ONLINE then session_lost_m I F B DIGINET_R_DESK_OFFLINE else Some (B, tt)) with
  | None => None
  | Some (B, _) =>
      if (S_state B =? DIGINET_S_IDLE) && negb (S_cfg_auto_wake B =? 0) then
        match diginet_session_wake_m I F B now with
        | None => None
        | Some (B, _) => Some (B, tt)
        end
      else Some (B, tt)
  end.

(* od: GOT.desk before the N_DESK notice, one less than OW.desk *)
Lemma rxe0_lib_prefix : forall (HL : links) I fr n W dp now od, timg_ok I ->
  0 <= n <= Z.of_nat (length (tf_bytes fr)) -> 0 < tf_addr fr ->
  fr_code (rxbuf fr n) = DIGINET_OK -> fr_cmd (rxbuf fr n) = DIGINET_CMD_ANNOUNCE ->
  33 <= fr_body_len (rxbuf fr n) ->
  length W = WN -> S_notify W = ti_notice I -> GOT_desk W = od -> 0 <= od <= 1 -> OW_desk W = od + 1 ->
  OW_desk_off W = -1 ->
  OW_desk_p W = dp -> (forall X, option_map snd (desk_named_m I X (skipn 30 (tf_bytes fr))) = Some dp) ->
  OW_desk_body W = tf_addr fr + 30 ->
  exists W2, on_announce_m I (Some fr) W (rxbuf fr n) now = rxe0_ltail I (Some fr) (set_S_foreign W2 0) now /\
    length W2 = WN /\ wframe (in_rs [(A_S_personality, 8); (A_GOT_desk, 4)]) W W2 /\ GOT_desk W2 = od + 1 /\
    (S_personality W2 = S_personality W \/ S_personality W2 = ti_personalities I \/
     S_personality W2 = ti_personalities I + 24).
Proof.
  intros HL I [a bytes] n W dp now od HI Hn Ha Hc Hcmd Hbl HW Hno Hg Hodr Hod Hoff Hdp Hdn Hdb.
  unfold rxbuf in *. cbn [tf_bytes tf_addr] in *.
  assert (Hnn : (Z.to_nat n <= length bytes)%nat) by lia.
  assert (Ea : ann_code (fr_cmd (firstn (Z.to_nat n) bytes)) (fr_body_len (firstn (Z.to_nat n) bytes)) = DIGINET_OK).
  { rewrite Hcmd. unfold ann_code. change (ann_cmd DIGINET_CMD_ANNOUNCE) with true. cbv beta iota delta [negb].
    rewrite (proj2 (Z.ltb_ge _ 33) Hbl). reflexivity. }
  assert (F1 : (fr_cmd (firstn (Z.to_nat n) bytes) =? DIGINET_CMD_ANNOUNCE) = true) by (rewrite Hcmd; reflexivity).
  assert (F2 : (fr_cmd (firstn (Z.to_nat n) bytes) =? DIGINET_CMD_ANNOUNCE_SESSION) = false)
    by (rewrite Hcmd; reflexivity).
  assert (Hann : ann_cmd (fr_cmd (firstn (Z.to_nat n) bytes)) = true) by (rewrite Hcmd; reflexivity).
  pose proof HL as (_ & _ & _ & _ & HL5 & _).
  assert (Lb : SPEC_ANN_MIN <= Z.of_nat (length (fr_body (firstn (Z.to_nat n) bytes)))).
  { rewrite (length_fr_body _ Hc). unfold SPEC_ANN_MIN. lia. }
  pose proof (HL5 I W (fr_body (firstn (Z.to_nat n) bytes)) Lb) as H5. cbv zeta in H5.
  destruct H5 as (dp' & _ & H5). change (Z.to_nat SPEC_ANN_NAME) with 24%nat in H5.
  pose proof (ti_personalities_ok I HI) as Hpers.
  unfold on_announce_m. cbv zeta. rewrite Ea, (Z.eqb_refl DIGINET_OK). change (negb true) with false. cbv beta iota.
  rewrite F2, F1. cbv beta iota.
  match goal with |- context [diginet_personality_from_name ?t] =>
    destruct (diginet_personality_from_name t) as [i|] eqn:Ep end.
  all: cbv beta iota.
  all: match goal with |- context [call_notify _ _ ?W1 (Ntc DIGINET_N_DESK _ _ _ _ _ _ _ _ _ _)] =>
    exists (set_GOT_desk W1 (od + 1));
    assert (L1 : length W1 = WN) by wlen;
    assert (N1 : S_notify W1 = ti_notice I) by (transitivity (S_notify W); [wg | exact Hno]);
    assert (G1 : GOT_desk W1 = od) by (transitivity (GOT_desk W); [wg | exact Hg]);
    assert (K1a : GOT_desk (set_GOT_desk W1 (od + 1)) = od + 1) by wg;
    assert (K1b : OW_desk (set_GOT_desk W1 (od + 1)) = od + 1) by (transitivity (OW_desk W); [wg | exact Hod]);
    assert (K1 : GOT_desk (set_GOT_desk W1 (od + 1)) <= OW_desk (set_GOT_desk W1 (od + 1)))
      by (rewrite K1a, K1b; lia);
    assert (K2 : OW_desk_off (set_GOT_desk W1 (od + 1)) = -1) by (transitivity (OW_desk_off W); [wg | exact Hoff]);
    assert (K3 : OW_desk_p (set_GOT_desk W1 (od + 1)) = dp) by (transitivity (OW_desk_p W); [wg | exact Hdp]);
    assert (K4 : OW_desk_body (set_GOT_desk W1 (od + 1)) = a + 30)
      by (transitivity (OW_desk_body W); [wg | exact Hdb]);
    pose proof (check_state_desk_ok HL I (set_GOT_desk W1 (od + 1)) a bytes (Z.to_nat n) (S_state W1) dp HI Hnn)
      as CK
  end.
  all: cbv zeta in CK; rewrite F2 in CK; try rewrite Ep in CK; cbv beta iota in CK.
  all: specialize (CK Hc Hann Hbl K1 K2 (Hdn _) K3 Ha K4).
  all: match goal with |- context [call_notify ?I' ?F' ?W1 ?N'] =>
    assert (CN : call_notify I' F' W1 N' = Some (set_GOT_desk W1 (od + 1), tt));
    [ unfold call_notify; rewrite N1, (Z.eqb_refl (ti_notice I)); cbv beta iota;
      rewrite (rxe0_notice_desk I' F' W1 N' od eq_refl G1 Hodr); wexact
    | rewrite CN; cbv beta iota ]
  end.
  all: split; [unfold rxe0_ltail; cbv beta; wsyn|].
  all: split; [wlen|]; split; [wfrs|]; split; [wg|].
  - try rewrite Ep in H5. cbv beta iota in H5. destruct H5 as (pp & d & _ & Hi & _).
    destruct Hi as [(-> & _) | (-> & _)]; right; [left | right].
    + transitivity (ti_personalities I + 24 * 0); [wg | ring].
    + transitivity (ti_personalities I + 24 * 1); [wg | ring].
  - left. wg.
Qed.

(* ---- the branch, its context and its leaves ---- *)

Definition cond_e0 (B buf : list byte) : Prop := fr_cmd buf = DIGINET_CMD_ANNOUNCE.

(* rx_branch_g's premises for cond_e0 *)
Record rxe0_ctx (I : timg) (ops : Z) (fr : tframe) (n : Z) (B : list byte) : Prop := {
  cx_n : 0 <= n <= Z.of_nat (length (tf_bytes fr));
  cx_a : 0 < tf_addr fr /\ tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64;
  cx_pre : rx_pre_g I ops B (rxbuf fr n);
  cx_acc : rx_accepts B (rxbuf fr n);
  cx_cmd : fr_cmd (rxbuf fr n) = DIGINET_CMD_ANNOUNCE;
}.

(* rx_branch_g's conclusion *)
Definition rxe0_goal (I : timg) (ops : Z) (fr : tframe) (n : Z) (B : list byte) : Prop :=
  exists Bm, m_rx_sw I fr n (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) = Some (Bm, tt) /\
    m_tick_m Bm = Some (Bm, tt) /\
    (length Bm = length B /\ forall a : nat, ~ in_rs R_mod (Z.of_nat a) -> nth_error Bm a = nth_error B a) /\
    forall W, lib_start Bm W (rxbuf fr n) ->
      exists W', rx_sw I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', tt) /\ rx_post_g I ops B (rxbuf fr n) W W'.

Definition R_ba : list (Z * Z) := (R_learn ++ [(A_M_last_rx, 8)]) ++ R_mpre.

(* the model's world after FT:296-314 *)
Record rxe0_ba (B Ba : list byte) (buf : list byte) (dp addr : Z) : Prop := {
  ba_len : length Ba = WN;
  ba_fr : wframe (in_rs R_ba) B Ba;
  ba_known : M_desk_known Ba = 1;
  ba_desk : M_desk Ba = fr_src buf;
  ba_last_rx : M_last_rx Ba = g_now B;
  ba_foreign : M_foreign Ba = 0;
  ba_owdesk : OW_desk Ba = OW_desk B + 1;
  ba_off : OW_desk_off Ba = -1;
  ba_p : OW_desk_p Ba = dp;
  ba_body : OW_desk_body Ba = addr + 30;
}.

Lemma rxe0_model_pre : forall (HL : links) I ops fr n B, rxe0_ctx I ops fr n B -> 33 <= fr_body_len (rxbuf fr n) ->
  exists dp, m_rx_sw I fr n (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) =
      rxe0_mtail (rxe0_ma (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) (OW_desk B + 1) dp (tf_addr fr)) /\
    (forall X, option_map snd (desk_named_m I X (skipn 30 (tf_bytes fr))) = Some dp) /\
    rxe0_ba B (rxe0_ma (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) (OW_desk B + 1) dp (tf_addr fr))
      (rxbuf fr n) dp (tf_addr fr).
Proof.
  intros HL I ops fr n B [Hn Ha Hpre Hacc Hcmd] Hbl.
  pose proof Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (HB : length B = WN) by exact Hlen.
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  pose proof (rf_blen _ _ Hf) as Hb.
  pose proof (rf_src_len _ _ Hf) as Hsl.
  destruct (learn_M_frame B (rxbuf fr n) HB Hsl) as [Hlf Hll].
  destruct (learn_M_desk B (rxbuf fr n) HB Hsl (b2_desk_known01 _ Hst) (ra_known _ _ Hacc)) as [Lk Ld].
  remember (learn_M B (rxbuf fr n)) as Bk eqn:EBk.
  remember (set_M_last_rx Bk (g_now B)) as B2 eqn:EB2.
  assert (HB2 : length B2 = WN) by (subst B2; wlen).
  assert (Hk2 : wframe (in_rs [(A_M_last_rx, 8)]) Bk B2) by (subst B2; wfrs).
  assert (Od : OW_desk B2 = OW_desk B) by (transitivity (OW_desk Bk); [subst B2; wg | fget Hlf]).
  assert (Hdr : 0 <= OW_desk B <= 1)
    by (pose proof (og_desk_range _ (wr_og _ Hroom)); pose proof (wr_desk _ Hroom); lia).
  destruct (rxe0_m_prefix HL I fr n B2 (OW_desk B) Himg Hn (ra_code _ _ Hacc) Hcmd Hbl Od Hdr)
    as (dp & Em & Hdn & Hdp).
  exists dp. split; [exact Em|]. split; [exact Hdn|].
  assert (Hpa : wframe (in_rs R_mpre) B2 (rxe0_ma B2 (OW_desk B + 1) dp (tf_addr fr))) by (unfold rxe0_ma; wfrs).
  pose proof (wframe_trans_rs _ _ _ _ _ (wframe_trans_rs _ _ _ _ _ Hlf Hk2) Hpa) as Hall.
  assert (Hab : 0 <= tf_addr fr + 30 < 2 ^ 64) by lia.
  constructor.
  - unfold rxe0_ma; wlen.
  - exact Hall.
  - transitivity (M_desk_known B2); [unfold rxe0_ma; wg|].
    transitivity (M_desk_known Bk); [subst B2; wg | exact Lk].
  - transitivity (M_desk B2); [unfold rxe0_ma; wg|].
    transitivity (M_desk Bk); [subst B2; wg | exact Ld].
  - transitivity (M_last_rx B2); [unfold rxe0_ma; wg | subst B2; wg].
  - unfold rxe0_ma; wg.
  - exact (rxe0_ma_desk B2 (OW_desk B + 1) dp (tf_addr fr) HB2 ltac:(lia)).
  - unfold rxe0_ma; wg.
  - unfold rxe0_ma; wg.
  - unfold rxe0_ma; wg.
Qed.

Definition R_lpre : list (Z * Z) := [(A_S_personality, 8); (A_GOT_desk, 4); (A_S_foreign, 4)].
Definition R_mall : list (Z * Z) := R_mlost ++ R_mwake.

(* the library from the switch (DS:298) to the end of on_announce's N_DESK notice and DS:201 *)
Lemma rxe0_lstart : forall (HL : links) I ops fr n B Ba Bm W dp, rxe0_ctx I ops fr n B ->
  33 <= fr_body_len (rxbuf fr n) -> rxe0_ba B Ba (rxbuf fr n) dp (tf_addr fr) ->
  (forall X, option_map snd (desk_named_m I X (skipn 30 (tf_bytes fr))) = Some dp) ->
  wframe (in_rs R_mall) Ba Bm -> lib_start Bm W (rxbuf fr n) ->
  exists W3, rx_sw I (Some fr) W (rxbuf fr n) (g_now B) = rxe0_ltail I (Some fr) W3 (g_now B) /\ length W3 = WN /\
    wframe (in_rs (R_start ++ R_lpre)) Bm W3 /\ wframe (in_rs R_lpre) W W3 /\ S_foreign W3 = 0 /\
    GOT_desk W3 = OW_desk B + 1 /\
    S_desk_known W3 = 1 /\ S_desk_mac W3 = fr_src (rxbuf fr n) /\ S_last_rx_us W3 = g_now Bm /\
    (S_personality W3 = S_personality B \/ S_personality W3 = ti_personalities I \/
     S_personality W3 = ti_personalities I + 24).
Proof.
  intros HL I ops fr n B Ba Bm W dp [Hn Ha Hpre Hacc Hcmd] Hbl Hba Hdn Hmb HW.
  pose proof Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof Hba as [HBa Hfa Ak Ad Alr Af Aod Aoff Ap Ab].
  pose proof HW as (HWf & HWk & HWm & HWl).
  assert (HBm : length Bm = WN) by (eapply wframe_len; [exact Hmb | exact HBa]).
  assert (HWn : length W = WN) by (eapply wframe_len; [exact HWf | exact HBm]).
  pose proof (wframe_trans_rs _ _ _ _ _ Hmb HWf) as Hmw.
  pose proof (wframe_trans_rs _ _ _ _ _ Hfa Hmw) as Hall.
  assert (N0 : S_notify W = ti_notice I) by (transitivity (S_notify B); [fget Hall | exact (a3_notify _ _ Hio)]).
  assert (G0 : GOT_desk W = OW_desk B)
    by (transitivity (GOT_desk B); [fget Hall | exact (og_desk _ (wr_og _ Hroom))]).
  assert (Hdr : 0 <= OW_desk B <= 1)
    by (pose proof (og_desk_range _ (wr_og _ Hroom)); pose proof (wr_desk _ Hroom); lia).
  assert (O1 : OW_desk W = OW_desk B + 1) by (transitivity (OW_desk Ba); [fget Hmw | exact Aod]).
  assert (O2 : OW_desk_off W = -1) by (transitivity (OW_desk_off Ba); [fget Hmw | exact Aoff]).
  assert (O3 : OW_desk_p W = dp) by (transitivity (OW_desk_p Ba); [fget Hmw | exact Ap]).
  assert (O4 : OW_desk_body W = tf_addr fr + 30) by (transitivity (OW_desk_body Ba); [fget Hmw | exact Ab]).
  assert (P0 : S_personality W = S_personality B) by fget Hall.
  destruct (rxe0_lib_prefix HL I fr n W dp (g_now B) (OW_desk B) Himg Hn (proj1 Ha) (ra_code _ _ Hacc) Hcmd Hbl
              HWn N0 G0 Hdr O1 O2 O3 Hdn O4) as (W2 & Ea & HW2 & Hf2 & G2 & P2).
  assert (H3 : wframe (in_rs R_lpre) W (set_S_foreign W2 0)).
  { unfold set_S_foreign. apply (wframe_upd_rs R_lpre W W2).
    - apply (wframe_rs_incl [(A_S_personality, 8); (A_GOT_desk, 4)] R_lpre W W2); [vm_compute; reflexivity | exact Hf2].
    - exact HW2.
    - wnum.
    - wlenput; wnum.
    - wlenput; vm_compute; reflexivity. }
  exists (set_S_foreign W2 0). split.
  { assert (F1 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE) = true) by (rewrite Hcmd; reflexivity).
    unfold rx_sw. cbv zeta. rewrite F1. cbv beta iota delta [orb]. rewrite Ea. exact eq_refl. }
  split; [wlen|].
  split; [exact (wframe_trans_rs _ _ _ _ _ HWf H3)|]. split; [exact H3|].
  split; [wg|].
  split; [transitivity (GOT_desk W2); [wg | exact G2]|].
  split; [transitivity (S_desk_known W); [fget H3 | exact HWk]|].
  split; [transitivity (S_desk_mac W); [fget H3 | exact HWm]|].
  split; [transitivity (S_last_rx_us W); [fget H3 | exact HWl]|].
  assert (P3 : S_personality (set_S_foreign W2 0) = S_personality W2) by wg.
  rewrite P3. rewrite <- P0. exact P2.
Qed.

(* ---- the post-state, from the facts each leaf computes ---- *)

(* the fields no step of the e0 branch writes, on either side *)
Record rxe0_keep (B X : list byte) : Prop := {
  kp_backoff_S : S_backoff_until_us X = S_backoff_until_us B;
  kp_backoff_M : M_backoff_until X = M_backoff_until B;
  kp_raw : g_raw X = g_raw B;
  kp_next_ka_S : S_next_keepalive_us X = S_next_keepalive_us B;
  kp_next_ka_M : M_next_ka X = M_next_ka B;
  kp_disp_S : S_display_sent X = S_display_sent B;
  kp_disp_M : M_display_sent X = M_display_sent B;
  kp_last_disp_S : S_last_display_us X = S_last_display_us B;
  kp_last_disp_M : M_last_display X = M_last_display B;
  kp_counter_S : S_desk_counter X = S_desk_counter B;
  kp_counter_M : M_desk_counter X = M_desk_counter B;
  kp_host_S : S_host_counter X = S_host_counter B;
  kp_host_M : M_host_counter X = M_host_counter B;
  kp_max_retries : Cfg_max_retries X = Cfg_max_retries B;
  kp_sum : Cfg_sum_mode X = Cfg_sum_mode B;
  kp_now : g_now X = g_now B;
  kp_wake_to : Cfg_wake_timeout_ms X = Cfg_wake_timeout_ms B;
  kp_offline : Cfg_offline_ms X = Cfg_offline_ms B;
  kp_ack_to : Cfg_ack_timeout_ms X = Cfg_ack_timeout_ms B;
  kp_e3_G : GOT_e3 X = GOT_e3 B;
  kp_e3_O : OW_e3 X = OW_e3 B;
  kp_acks_G : GOT_acks X = GOT_acks B;
  kp_acks_O : OW_acks X = OW_acks B;
  kp_foreign_G : GOT_foreign X = GOT_foreign B;
  kp_foreign_O : OW_foreign X = OW_foreign B;
  kp_acked_G : GOT_acked X = GOT_acked B;
  kp_acked_O : OW_acked X = OW_acked B;
  kp_ndata_G : GOT_ndata X = GOT_ndata B;
  kp_ndata_O : OW_ndata X = OW_ndata B;
}.

(* m_tick (FT:373) of the model's world: nothing overdue *)
Lemma rxe0_tick : forall I ops B Bm, agree_core I ops B ->
  (M_state Bm = S_WAKING -> M_wake_sent Bm <= g_now B /\ g_now B - M_wake_sent Bm < 1000 * Cfg_wake_timeout_ms B) ->
  M_last_rx Bm = g_now B -> g_now Bm = g_now B -> Cfg_wake_timeout_ms Bm = Cfg_wake_timeout_ms B ->
  Cfg_offline_ms Bm = Cfg_offline_ms B -> m_tick_m Bm = Some (Bm, tt).
Proof.
  intros I ops B Bm Hcore Hw Hlr Hnw Hcw Hco. pose proof Hcore as [_ _ Hcfg _ _ _ _ _ _].
  pose proof (a1_wake_timeout _ Hcfg) as T1. pose proof (a1_offline _ Hcfg) as T2.
  apply m_tick_quiet.
  - rewrite Hnw, Hcw. exact Hw.
  - rewrite Hlr, Hnw, Hco. intros _. split; [apply Z.le_refl | rewrite Z.sub_diag; lia].
  - rewrite Hcw. lia.
  - rewrite Hco. lia.
Qed.

(* no frame in flight on either side *)
Lemma rxe0_fly_off : forall X, M_fly_on X = 0 -> S_inflight X = 0 -> agree_fly X.
Proof.
  intros X Hm Hs.
  constructor; [rewrite Hs, Hm; reflexivity | left; exact Hm | intros H; rewrite Hm in H; discriminate H ..].
Qed.

(* the wake's E2 in flight on both sides (DS:139-142, FT:883-889) *)
Lemma rxe0_fly_wake : forall X dst send mode,
  M_fly_on X = 1 -> S_inflight X = 1 -> M_state X = S_WAKING -> S_inflight_counter X = send ->
  M_fly_counter X = send -> S_host_counter X = send -> S_inflight_retries X = 0 -> M_fly_retries X = 0 ->
  S_inflight_sent_us X = M_fly_sent X -> S_inflight_len X = 60 -> M_fly_len X = 60 -> M_fly_cmd X = SPEC_CMD_E2 ->
  M_desk X = dst -> Cfg_sum_mode X = mode ->
  sub X A_M_fly_frame 60 = lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode ->
  sub X A_S_inflight_frame 60 = lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode ->
  agree_fly X.
Proof.
  intros X dst send mode Hon Hin Hst Hc1 Hc2 Hhc Hr1 Hr2 Hsent Hl1 Hl2 Hcmd Hd Hm Hfm Hfs.
  constructor.
  - rewrite Hin, Hon. reflexivity.
  - right. exact Hon.
  - intros _. left. exact Hst.
  - intros _. rewrite Hc1, Hc2. reflexivity.
  - intros _. rewrite Hc1, Hhc. reflexivity.
  - intros _. rewrite Hr1, Hr2. reflexivity.
  - intros _. rewrite Hr2. unfold Cfg_max_retries. apply u_at_nonneg.
  - intros _. exact Hsent.
  - intros _. rewrite Hl1, Hl2. reflexivity.
  - intros _. left. exact Hcmd.
  - intros _. exists [], 0.
    rewrite Hl2, Hd, Hc2, Hcmd, Hm, Hr2. change (Z.to_nat 60) with 60%nat.
    change SPEC_CMD_E2 with DIGINET_CMD_WAKE.
    split; [cbn; lia|]. split; [vm_compute; reflexivity|]. split; [split; [lia | vm_compute; reflexivity]|].
    split; [vm_compute; reflexivity|]. split; [exact Hfm | exact Hfs].
Qed.

(* ow_got_eq and ow_step from the counts: n, e2 and desk computed, the others as in B *)
Lemma rxe0_og_mk : forall B X nn ec dd, ow_room B -> rxe0_keep B X ->
  GOT_n X = nn -> OW_n X = nn -> OW_n B <= nn <= OW_n B + 2 ->
  (forall i, 0 <= i < nn -> i < TRANS_MAX ->
     GOT_t_state X i = OW_t_state X i /\ GOT_t_old X i = OW_t_old X i /\ GOT_t_reason X i = OW_t_reason X i) ->
  GOT_e2 X = ec -> OW_e2 X = ec -> OW_e2 B <= ec <= OW_e2 B + 1 ->
  GOT_desk X = dd -> OW_desk X = dd -> OW_desk B <= dd <= OW_desk B + 1 ->
  ow_got_eq X /\ ow_step B X.
Proof.
  intros B X nn ec dd Hr Kp Gn On Nn Ht Ge Oe Ee Gd Od Ed.
  destruct Hr as [Hog Rn Re2 Re3 Rac Rd Rf Rak Rnd].
  destruct Hog as [O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 O16 O17].
  destruct Kp as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K20 K21 K22 K23 K24 K25 K26 K27 K28 K29].
  split.
  - constructor.
    + rewrite Gn, On. reflexivity.
    + rewrite On. lia.
    + rewrite On. exact Ht.
    + rewrite Ge, Oe. reflexivity.
    + rewrite Oe. lia.
    + rewrite K20, K21. exact O6.
    + rewrite K21. exact O7.
    + rewrite K22, K23. exact O8.
    + rewrite K23. exact O9.
    + rewrite Gd, Od. reflexivity.
    + rewrite Od. lia.
    + rewrite K24, K25. exact O12.
    + rewrite K25. exact O13.
    + rewrite K26, K27. exact O14.
    + rewrite K27. exact O15.
    + rewrite K28, K29. exact O16.
    + rewrite K29. exact O17.
  - constructor; [rewrite On | rewrite Oe | rewrite K21 | rewrite K23 | rewrite Od | rewrite K25 | rewrite K27
                 | rewrite K29]; lia.
Qed.

(* rx_post_g from the facts each leaf computes; B the world before m_rx, buf the frame *)
Lemma rxe0_post : forall I ops B buf W X st e1 e2 ws vv nn ec dd,
  agree_core I ops B -> ow_room B -> rxe0_keep B X -> wframe R_rx B X ->
  S_state X = st -> M_state X = st -> 0 <= st <= 3 ->
  S_desk_known X = 1 -> M_desk_known X = 1 -> S_desk_mac X = M_desk X ->
  S_foreign X = 0 -> M_foreign X = 0 ->
  S_e1_named_us X = e1 -> M_e1_us X = e1 -> bit01 e1 ->
  S_wake_acked X = e2 -> M_e2_acked X = e2 -> bit01 e2 ->
  S_wake_sent_us X = ws -> M_wake_sent X = ws -> ws <= g_now B ->
  (st = S_WAKING -> g_now B - ws < 1000 * Cfg_wake_timeout_ms B) ->
  S_last_rx_us X = g_now B -> M_last_rx X = g_now B ->
  S_desk_counter_valid X = vv -> M_desk_counter_valid X = vv -> bit01 vv ->
  (vv = 1 -> S_desk_counter B = M_desk_counter B) ->
  (st = S_IDLE \/ st = S_CLOSED -> M_fly_on X = 0) ->
  agree_fly X ->
  (M_fly_on X = 1 -> M_fly_sent X <= g_now B /\ g_now B - M_fly_sent X < 1000 * Cfg_ack_timeout_ms B) ->
  bit01 (g_fail_next X) ->
  (S_personality X = 0 \/ S_personality X = ti_personalities I \/ S_personality X = ti_personalities I + 24) ->
  GOT_n X = nn -> OW_n X = nn -> OW_n B <= nn <= OW_n B + 2 ->
  (forall i, 0 <= i < nn -> i < TRANS_MAX ->
     GOT_t_state X i = OW_t_state X i /\ GOT_t_old X i = OW_t_old X i /\ GOT_t_reason X i = OW_t_reason X i) ->
  GOT_e2 X = ec -> OW_e2 X = ec -> OW_e2 B <= ec <= OW_e2 B + 1 ->
  GOT_desk X = dd -> OW_desk X = dd -> OW_desk B <= dd <= OW_desk B + 1 ->
  g_rx X = g_rx W -> g_rx_len X = g_rx_len W -> g_rx_times X = g_rx_times W -> g_rx_fail X = g_rx_fail W ->
  g_now W = g_now B -> g_rx_send X = g_rx_send W ->
  (rx_wake_buf buf -> M_fail X = g_fail_next X /\ st <> S_ONLINE) ->
  rx_post_g I ops B buf W X.
Proof.
  intros I ops B buf W X st e1 e2 ws vv nn ec dd Hcore Hr Kp Hrx Ss Ms Sr Sk Mk Sdm Sf Mf Se1 Me1 E1 Se2 Me2 E2
    Sws Mws Ws Ww Slr Mlr Sv Mv Vv Vc Vi Hfl Hft Hfn Hpe Gn On Nn Ht Ge Oe Ee Gd Od Ed R1 R2 R3 R4 R5 R6 Hwk.
  destruct (rxe0_og_mk B X nn ec dd Hr Kp Gn On Nn Ht Ge Oe Ee Gd Od Ed) as [Hog Hstep].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly0 Htime Hq Hmisc].
  pose proof Kp as [K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25
    K26 K27 K28 K29].
  constructor; [constructor | exact Hstep | exact R6 | rewrite Ms; exact Hwk].
  - apply (agree_core_rx I ops B X Hcore Hrx).
    + clear R1 R2 R3 R4 R6. constructor; rw_eqs X.
      * reflexivity.
      * exact Sr.
      * reflexivity.
      * right; reflexivity.
      * intros _; reflexivity.
      * reflexivity.
      * left; reflexivity.
      * reflexivity.
      * exact E1.
      * reflexivity.
      * exact E2.
      * reflexivity.
      * reflexivity.
      * exact (b4_backoff _ Hst).
      * exact (b5_next_ka _ Hst).
      * exact (b5_display_sent _ Hst).
      * exact (b5_display_sent01 _ Hst).
      * exact (b5_last_display _ Hst).
      * reflexivity.
      * exact Vv.
      * exact Vc.
      * exact (b7_host_counter _ Hst).
      * exact Vi.
      * intros _; reflexivity.
    + exact Hfl.
    + clear R1 R2 R3 R4 R6. constructor; rw_eqs X.
      * exact (c_now _ _ Htime).
      * apply Z.le_refl.
      * exact Ws.
      * intros H. exact (proj1 (Hft H)).
      * exact (c1_last_display _ _ Htime).
      * exact (c1_backoff _ _ Htime).
      * exact (c1_next_ka _ _ Htime).
      * exact Ww.
      * intros _. rewrite Z.sub_diag. pose proof (a1_offline _ Hcfg). slia.
      * intros H. exact (proj2 (Hft H)).
    + constructor; [exact Hfn | exact Hpe].
  - exact Hog.
  - exact R1.
  - exact R2.
  - exact R3.
  - exact R4.
  - exact (eq_trans K16 (eq_sym R5)).
Qed.

(* ---- leaf 1: neither lost nor wake (WAKING, or IDLE without auto_wake): FT:303-318 and DS:184-206 write only
   the desk naming and foreign ---- *)
Lemma rxe0_leaf_noact : forall (HL : links) I ops fr n B, rxe0_ctx I ops fr n B -> 33 <= fr_body_len (rxbuf fr n) ->
  M_state B <> S_ONLINE -> ((M_state B =? S_IDLE) && truth (Cfg_auto_wake B)) = false -> rxe0_goal I ops fr n B.
Proof.
  intros HL I ops fr n B Cx Hbl Hno Hnw.
  pose proof Cx as [Hn Ha Hpre Hacc Hcmd].
  pose proof Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hroom) as Hog.
  pose proof (Hfail Hacc (conj Hcmd Hbl)) as Hmf.
  destruct (rxe0_model_pre HL I ops fr n B Cx Hbl) as (dp & Em & Hdn & Hba).
  set (Ba := rxe0_ma (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) (OW_desk B + 1) dp (tf_addr fr)) in *.
  pose proof Hba as [HBa Hfa Ak Ad Alr Af Aod Aoff Ap Ab].
  assert (As : M_state Ba = M_state B) by fget Hfa.
  assert (Aaw : Cfg_auto_wake Ba = Cfg_auto_wake B) by fget Hfa.
  assert (Anw : g_now Ba = g_now B) by fget Hfa.
  unfold rxe0_goal. rewrite Em. exists Ba. split; [|split; [|split]].
  - unfold rxe0_mtail. rewrite As, (proj2 (Z.eqb_neq _ _) Hno). cbv beta iota.
    rewrite As, Aaw, Hnw. cbv beta iota. exact eq_refl.
  - apply (rxe0_tick I ops B Ba Hcore).
    + rewrite As. intros Hw. assert (E : M_wake_sent Ba = M_wake_sent B) by fget Hfa. rewrite E.
      exact (conj (c1_wake_sent _ _ Htime) (c2_wake _ _ Htime Hw)).
    + exact Alr.
    + exact Anw.
    + fget Hfa.
    + fget Hfa.
  - apply (wframe_rs_incl R_ba R_mod B Ba); [vm_compute; reflexivity | exact Hfa].
  - intros W HW.
    destruct (rxe0_lstart HL I ops fr n B Ba Ba W dp Cx Hbl Hba Hdn (wframe_refl _ Ba) HW)
      as (W3 & Ew & HW3 & Hf3 & Hw3 & F3 & G3 & K3 & D3 & L3 & P3).
    rewrite Ew. exists W3.
    pose proof HW as (HWf & HWk & HWm & HWl).
    pose proof (wframe_trans_rs _ _ _ _ _ Hfa Hf3) as Hall.
    assert (S3 : S_state W3 = M_state B) by (transitivity (S_state B); [fget Hall | exact (b1_state _ Hst)]).
    assert (A3 : S_cfg_auto_wake W3 = Cfg_auto_wake B)
      by (transitivity (S_cfg_auto_wake B); [fget Hall | exact (a2_auto_wake _ Hcfg)]).
    split.
    + unfold rxe0_ltail. rewrite S3. change DIGINET_S_ONLINE with S_ONLINE.
      rewrite (proj2 (Z.eqb_neq _ _) Hno). cbv beta iota.
      rewrite S3, A3.
      change ((M_state B =? DIGINET_S_IDLE) && negb (Cfg_auto_wake B =? 0)) with
        ((M_state B =? S_IDLE) && truth (Cfg_auto_wake B)).
      rewrite Hnw. cbv beta iota. exact eq_refl.
    + assert (Kp : rxe0_keep B W3) by (constructor; fget Hall).
      assert (Md3 : M_desk W3 = fr_src (rxbuf fr n)) by (transitivity (M_desk Ba); [fget Hf3 | exact Ad]).
      apply (rxe0_post I ops B (rxbuf fr n) W W3 (M_state B) (M_e1_us B) (M_e2_acked B) (M_wake_sent B)
               (M_desk_counter_valid B) (OW_n B) (OW_e2 B) (OW_desk B + 1) Hcore Hroom Kp).
      * refine (wframe_rx _ _ _ _ Hall). vm_compute. reflexivity.
      * exact S3.
      * fget Hall.
      * exact (b1_state_range _ Hst).
      * exact K3.
      * transitivity (M_desk_known Ba); [fget Hf3 | exact Ak].
      * rewrite D3, Md3. reflexivity.
      * exact F3.
      * transitivity (M_foreign Ba); [fget Hf3 | exact Af].
      * transitivity (S_e1_named_us B); [fget Hall | exact (b3_e1 _ Hst)].
      * fget Hall.
      * exact (b3_e1_01 _ Hst).
      * transitivity (S_wake_acked B); [fget Hall | exact (b3_e2 _ Hst)].
      * fget Hall.
      * exact (b3_e2_01 _ Hst).
      * transitivity (S_wake_sent_us B); [fget Hall | exact (b4_wake_sent _ Hst)].
      * fget Hall.
      * exact (c1_wake_sent _ _ Htime).
      * exact (c2_wake _ _ Htime).
      * rewrite L3. exact Anw.
      * transitivity (M_last_rx Ba); [fget Hf3 | exact Alr].
      * transitivity (S_desk_counter_valid B); [fget Hall | exact (b6_valid _ Hst)].
      * fget Hall.
      * exact (b6_valid01 _ Hst).
      * exact (b6_counter _ Hst).
      * intros Hi. transitivity (M_fly_on B); [fget Hall | exact (b9_idle _ Hst Hi)].
      * apply (agree_fly_fr _ B W3 Hall); [vm_compute; reflexivity | vm_compute; reflexivity | fget Hall | fget Hall
          | fget Hall | | exact Hfly].
        intros Hon. split.
        -- rewrite Md3. exact (ra_known _ _ Hacc (b9_known _ Hst (b8_state _ Hfly Hon))).
        -- assert (E : M_state W3 = M_state B) by fget Hall. rewrite E. exact (b8_state _ Hfly Hon).
      * intros Hon. assert (E1 : M_fly_on W3 = M_fly_on B) by fget Hall. rewrite E1 in Hon.
        assert (E2 : M_fly_sent W3 = M_fly_sent B) by fget Hall. rewrite E2.
        exact (conj (c1_fly_sent _ _ Htime Hon) (c2_fly _ _ Htime Hon)).
      * assert (E : g_fail_next W3 = g_fail_next B) by fget Hall. rewrite E. exact (e1_fail_next _ _ Hmisc).
      * destruct P3 as [E|[E|E]]; rewrite E; [exact (e2_personality _ _ Hmisc) | right; left; reflexivity
          | right; right; reflexivity].
      * transitivity (GOT_n B); [fget Hall | exact (og_n _ Hog)].
      * fget Hall.
      * lia.
      * exact (rxe0_t_fr _ B W3 Hog Hall ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
      * transitivity (GOT_e2 B); [fget Hall | exact (og_e2 _ Hog)].
      * fget Hall.
      * lia.
      * exact G3.
      * transitivity (OW_desk Ba); [fget Hf3 | exact Aod].
      * lia.
      * fget Hw3.
      * fget Hw3.
      * fget Hw3.
      * fget Hw3.
      * transitivity (g_now Ba); [fget HWf | exact Anw].
      * fget Hw3.
      * (* neither side writes M.fail or g_fail_next here *)
        intros _. split; [|exact Hno].
        assert (E1 : M_fail W3 = M_fail B) by fget Hall. assert (E2 : g_fail_next W3 = g_fail_next B) by fget Hall.
        rewrite E1, E2. exact Hmf.
Qed.

Lemma rxe0_hc_range : forall B, 0 <= M_host_counter B < 2 ^ 32.
Proof.
  intros B. unfold M_host_counter. pose proof (rw_u_range B A_M_host_counter 4) as H.
  change (8 * Z.of_nat 4) with 32 in H. exact H.
Qed.

(* what diginet_session_wake reads, on the library's world, from its agreement with B *)
Lemma rxe0_lw_mk : forall I ops B Wp (dst : list byte) e, agree_core I ops B -> length Wp = WN ->
  length dst = 6%nat -> 0 <= e <= 1 ->
  M_desk_known Wp = 1 -> M_desk Wp = dst -> Cfg_sum_mode Wp = Cfg_sum_mode B -> M_foreign Wp = 0 ->
  M_host_counter Wp = M_host_counter B -> GOT_e2 Wp = e ->
  S_desk_known Wp = 1 -> S_foreign Wp = 0 -> S_desk_mac Wp = dst -> S_cfg_host_mac Wp = S_cfg_host_mac B ->
  S_host_counter Wp = S_host_counter B -> S_cfg_sum_mode Wp = S_cfg_sum_mode B -> S_io_send Wp = S_io_send B ->
  S_notify Wp = S_notify B -> S_state Wp = S_IDLE ->
  rxe0_lw I Wp dst (M_host_counter B) (Cfg_sum_mode B) e.
Proof.
  intros I ops B Wp dst e Hcore HW Hd Her Mk Md Ms Mf Mh Ge Sk Sf Sd Sh Sc Sm Sio Sno Sst.
  pose proof Hcore as [_ _ Hcfg Hio Hst _ _ _ _].
  constructor; [constructor|..].
  - exact HW.
  - exact Hd.
  - exact (a1_sum_mode _ Hcfg).
  - exact (rxe0_hc_range B).
  - exact Mk.
  - exact Md.
  - exact Ms.
  - exact Mf.
  - exact Mh.
  - exact Ge.
  - exact Her.
  - exact Sk.
  - exact Sf.
  - exact Sd.
  - rewrite Sh. exact (a2_host_mac _ Hcfg).
  - rewrite Sc. exact (b7_host_counter _ Hst).
  - rewrite Sm. exact (a2_sum_mode _ Hcfg).
  - rewrite Sio. exact (a3_io_send _ _ Hio).
  - rewrite Sno. exact (a3_notify _ _ Hio).
  - exact Sst.
Qed.

(* ---- leaf 2: ONLINE without auto_wake: both sides lose the session (R_DESK_OFFLINE) ---- *)
Lemma rxe0_leaf_lost : forall (HL : links) I ops fr n B, rxe0_ctx I ops fr n B -> 33 <= fr_body_len (rxbuf fr n) ->
  M_state B = S_ONLINE -> Cfg_auto_wake B = 0 -> rxe0_goal I ops fr n B.
Proof.
  intros HL I ops fr n B Cx Hbl Hon Haw.
  pose proof Cx as [Hn Ha Hpre Hacc Hcmd].
  pose proof Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hroom) as Hog.
  pose proof (Hfail Hacc (conj Hcmd Hbl)) as Hmf.
  assert (Hnr : 0 <= OW_n B <= 4) by (pose proof (og_n_range _ Hog); pose proof (wr_n _ Hroom); lia).
  destruct (rxe0_model_pre HL I ops fr n B Cx Hbl) as (dp & Em & Hdn & Hba).
  set (Ba := rxe0_ma (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) (OW_desk B + 1) dp (tf_addr fr)) in *.
  pose proof Hba as [HBa Hfa Ak Ad Alr Af Aod Aoff Ap Ab].
  assert (As : M_state Ba = S_ONLINE) by (transitivity (M_state B); [fget Hfa | exact Hon]).
  assert (On0 : OW_n Ba = OW_n B) by fget Hfa.
  assert (Anw : g_now Ba = g_now B) by fget Hfa.
  destruct (rxe0_m_lost Ba (OW_n B) HBa As On0 Hnr)
    as (Bl & El & HBl & Fl & Ltk & Ls & Lf & Lv & Ln & Lt1 & Lt2 & Lt3).
  pose proof (wframe_trans_rs _ _ _ _ _ Hfa Fl) as Hml.
  assert (Law : Cfg_auto_wake Bl = 0) by (transitivity (Cfg_auto_wake B); [fget Hml | exact Haw]).
  assert (Lnw : g_now Bl = g_now B) by (transitivity (g_now Ba); [fget Fl | exact Anw]).
  unfold rxe0_goal. rewrite Em. exists Bl. split; [|split; [|split]].
  - unfold rxe0_mtail. rewrite As, (Z.eqb_refl S_ONLINE). cbv beta iota. rewrite El. cbv beta iota.
    rewrite Ls, Law, (Z.eqb_refl S_IDLE), rxe0_truth0. change (true && false) with false. cbv beta iota.
    exact eq_refl.
  - apply (rxe0_tick I ops B Bl Hcore).
    + rewrite Ls. intros H. exfalso. unfold S_IDLE, S_WAKING in H. discriminate H.
    + transitivity (M_last_rx Ba); [fget Fl | exact Alr].
    + exact Lnw.
    + fget Hml.
    + fget Hml.
  - apply (wframe_rs_incl (R_ba ++ R_mlost) R_mod B Bl); [vm_compute; reflexivity | exact Hml].
  - intros W HW.
    destruct (rxe0_lstart HL I ops fr n B Ba Bl W dp Cx Hbl Hba Hdn
                (wframe_rs_incl R_mlost R_mall Ba Bl ltac:(vm_compute; reflexivity) Fl) HW)
      as (W3 & Ew & HW3 & Hf3 & Hw3 & F3 & G3 & K3 & D3 & L3 & P3).
    rewrite Ew.
    pose proof HW as (HWf & HWk & HWm & HWl).
    pose proof (wframe_trans_rs _ _ _ _ _ Hml Hf3) as Hall3.
    assert (S3 : S_state W3 = S_ONLINE)
      by (transitivity (S_state B); [fget Hall3 | rewrite (b1_state _ Hst); exact Hon]).
    assert (N3 : S_notify W3 = ti_notice I) by (transitivity (S_notify B); [fget Hall3 | exact (a3_notify _ _ Hio)]).
    assert (Gn3 : GOT_n W3 = OW_n B) by (transitivity (GOT_n B); [fget Hall3 | exact (og_n _ Hog)]).
    destruct (rxe0_lib_lost I (Some fr) W3 (OW_n B) HW3 S3 N3 Gn3 Hnr)
      as (Wl & Ewl & HWl' & Fwl & Wtk & Ws & Wi & Wv & Wn & Wt1 & Wt2 & Wt3).
    pose proof (wframe_trans_rs _ _ _ _ _ Hall3 Fwl) as Hall.
    pose proof (wframe_trans_rs _ _ _ _ _ Hf3 Fwl) as Hlw.
    pose proof (wframe_trans_rs _ _ _ _ _ Fl Hlw) as Hbw.
    pose proof (wframe_trans_rs _ _ _ _ _ Hw3 Fwl) as Hww.
    assert (Aw : S_cfg_auto_wake Wl = 0)
      by (transitivity (S_cfg_auto_wake B); [fget Hall | rewrite (a2_auto_wake _ Hcfg); exact Haw]).
    exists Wl. split.
    + unfold rxe0_ltail. rewrite S3. change DIGINET_S_ONLINE with S_ONLINE. rewrite (Z.eqb_refl S_ONLINE).
      cbv beta iota. rewrite Ewl. cbv beta iota. rewrite Ws, Aw.
      change (S_IDLE =? DIGINET_S_IDLE) with true. change (negb (0 =? 0)) with false.
      change (true && false) with false. cbv beta iota. exact eq_refl.
    + assert (Kp : rxe0_keep B Wl) by (constructor; fget Hall).
      assert (Md : M_desk Wl = fr_src (rxbuf fr n)) by (transitivity (M_desk Ba); [fget Hbw | exact Ad]).
      assert (Mf0 : M_fly_on Wl = 0) by (transitivity (M_fly_on Bl); [fget Hlw | exact Lf]).
      (* the transition entries: below OW.n B those of B (ow_got_eq B), at OW.n B the lost on both sides *)
      assert (TG : rxe0_tkg B Wl (OW_n B)).
      { apply (rxe0_tkg_trans _ W3); [|exact Wtk].
        apply (rxe0_tkg_le _ _ TRANS_MAX); [exact (rxe0_tkg_fr _ _ _ Hall3 ltac:(vm_compute; reflexivity))
                                           | unfold TRANS_MAX; lia]. }
      assert (TO : rxe0_tko Bl Wl TRANS_MAX) by exact (rxe0_tko_fr _ _ _ Hlw ltac:(vm_compute; reflexivity)).
      assert (TO' : rxe0_tko B Wl (OW_n B)).
      { apply (rxe0_tko_trans _ Ba).
        - apply (rxe0_tko_le _ _ TRANS_MAX); [exact (rxe0_tko_fr _ _ _ Hfa ltac:(vm_compute; reflexivity))
                                             | unfold TRANS_MAX; lia].
        - apply (rxe0_tko_trans _ Bl); [exact Ltk|].
          apply (rxe0_tko_le _ _ TRANS_MAX); [exact TO | unfold TRANS_MAX; lia]. }
      apply (rxe0_post I ops B (rxbuf fr n) W Wl S_IDLE (M_e1_us B) (M_e2_acked B) (M_wake_sent B) 0
               (OW_n B + 1) (OW_e2 B) (OW_desk B + 1) Hcore Hroom Kp).
      * refine (wframe_rx _ _ _ _ Hall). vm_compute. reflexivity.
      * exact Ws.
      * transitivity (M_state Bl); [fget Hlw | exact Ls].
      * unfold S_IDLE. lia.
      * transitivity (S_desk_known W3); [fget Fwl | exact K3].
      * transitivity (M_desk_known Ba); [fget Hbw | exact Ak].
      * rewrite Md. transitivity (S_desk_mac W3); [fget Fwl | exact D3].
      * transitivity (S_foreign W3); [fget Fwl | exact F3].
      * transitivity (M_foreign Ba); [fget Hbw | exact Af].
      * transitivity (S_e1_named_us B); [fget Hall | exact (b3_e1 _ Hst)].
      * fget Hall.
      * exact (b3_e1_01 _ Hst).
      * transitivity (S_wake_acked B); [fget Hall | exact (b3_e2 _ Hst)].
      * fget Hall.
      * exact (b3_e2_01 _ Hst).
      * transitivity (S_wake_sent_us B); [fget Hall | exact (b4_wake_sent _ Hst)].
      * fget Hall.
      * exact (c1_wake_sent _ _ Htime).
      * intros H. exfalso. unfold S_IDLE, S_WAKING in H. discriminate H.
      * transitivity (S_last_rx_us W3); [fget Fwl | rewrite L3; exact Lnw].
      * transitivity (M_last_rx Ba); [fget Hbw | exact Alr].
      * exact Wv.
      * transitivity (M_desk_counter_valid Bl); [fget Hlw | exact Lv].
      * left. reflexivity.
      * intros H. discriminate H.
      * intros _. exact Mf0.
      * apply rxe0_fly_off; [exact Mf0 | exact Wi].
      * intros H. rewrite Mf0 in H. discriminate H.
      * assert (E : g_fail_next Wl = g_fail_next B) by fget Hall. rewrite E. exact (e1_fail_next _ _ Hmisc).
      * assert (E : S_personality Wl = S_personality W3) by fget Fwl. rewrite E.
        destruct P3 as [E3|[E3|E3]]; rewrite E3; [exact (e2_personality _ _ Hmisc) | right; left; reflexivity
          | right; right; reflexivity].
      * exact Wn.
      * transitivity (OW_n Bl); [fget Hlw | exact Ln].
      * lia.
      * intros i Hi Hi2. destruct (Z.lt_ge_cases i (OW_n B)) as [Hlt | Hge].
        -- exact (rxe0_t_below B Wl Hog TG TO' i (conj (proj1 Hi) Hlt) Hi2).
        -- assert (Ei : i = OW_n B) by lia. subst i.
           destruct (TO (OW_n B) ltac:(unfold TRANS_MAX; lia)) as (O1 & O2 & O3).
           rewrite Wt1, Wt2, Wt3, O1, O2, O3, Lt1, Lt2, Lt3. exact (conj eq_refl (conj eq_refl eq_refl)).
      * transitivity (GOT_e2 B); [fget Hall | exact (og_e2 _ Hog)].
      * fget Hall.
      * lia.
      * transitivity (GOT_desk W3); [fget Fwl | exact G3].
      * transitivity (OW_desk Ba); [fget Hbw | exact Aod].
      * lia.
      * fget Hww.
      * fget Hww.
      * fget Hww.
      * fget Hww.
      * transitivity (g_now Bl); [fget HWf | exact Lnw].
      * fget Hww.
      * (* M.fail and g_fail_next untouched; the session is lost *)
        intros _. split; [|unfold S_IDLE, S_ONLINE; lia].
        assert (E1 : M_fail Wl = M_fail B) by fget Hall. assert (E2 : g_fail_next Wl = g_fail_next B) by fget Hall.
        rewrite E1, E2. exact Hmf.
Qed.

(* ---- leaf 3: IDLE with auto_wake, the E2 send fails (g_fail_next): both start the wake (e1/e2 cleared,
   wake_sent = now, E2 counted) and stay IDLE (FT:229-230, DS:137-138) ---- *)
Lemma rxe0_leaf_idle_fail : forall (HL : links) I ops fr n B, rxe0_ctx I ops fr n B ->
  33 <= fr_body_len (rxbuf fr n) -> M_state B = S_IDLE -> Cfg_auto_wake B = 1 -> g_fail_next B = 1 ->
  rxe0_goal I ops fr n B.
Proof.
  intros HL I ops fr n B Cx Hbl Hid Haw Hfn.
  pose proof Cx as [Hn Ha Hpre Hacc Hcmd].
  pose proof Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hroom) as Hog.
  pose proof (Hfail Hacc (conj Hcmd Hbl)) as Hmf.
  assert (He2r : 0 <= OW_e2 B <= 1) by (pose proof (og_e2_range _ Hog); pose proof (wr_e2 _ Hroom); lia).
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  destruct (rxe0_model_pre HL I ops fr n B Cx Hbl) as (dp & Em & Hdn & Hba).
  set (Ba := rxe0_ma (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) (OW_desk B + 1) dp (tf_addr fr)) in *.
  pose proof Hba as [HBa Hfa Ak Ad Alr Af Aod Aoff Ap Ab].
  assert (As : M_state Ba = S_IDLE) by (transitivity (M_state B); [fget Hfa | exact Hid]).
  assert (Aaw : Cfg_auto_wake Ba = 1) by (transitivity (Cfg_auto_wake B); [fget Hfa | exact Haw]).
  assert (Ae2 : OW_e2 Ba = OW_e2 B) by fget Hfa.
  assert (Afl : M_fail Ba = 1) by (transitivity (M_fail B); [fget Hfa | rewrite Hmf; exact Hfn]).
  assert (Anw : g_now Ba = g_now B) by fget Hfa.
  destruct (rxe0_m_wake_fail Ba (OW_e2 B) HBa Ak Af Ae2 He2r Afl)
    as (Bw & Emw & HBw & Fw & Me2 & Me1 & Mws & Moe & Mfl).
  pose proof (wframe_trans_rs _ _ _ _ _ Hfa Fw) as Hmw.
  unfold rxe0_goal. rewrite Em. exists Bw. split; [|split; [|split]].
  - unfold rxe0_mtail. rewrite As. change (S_IDLE =? S_ONLINE) with false. cbv beta iota.
    rewrite As, Aaw, (Z.eqb_refl S_IDLE), rxe0_truth1. change (true && true) with true. cbv beta iota.
    rewrite Emw. cbv beta iota. exact eq_refl.
  - apply (rxe0_tick I ops B Bw Hcore).
    + assert (E : M_state Bw = S_IDLE) by (transitivity (M_state Ba); [fget Fw | exact As]).
      rewrite E. intros H. exfalso. unfold S_IDLE, S_WAKING in H. discriminate H.
    + transitivity (M_last_rx Ba); [fget Fw | exact Alr].
    + transitivity (g_now Ba); [fget Fw | exact Anw].
    + fget Hmw.
    + fget Hmw.
  - apply (wframe_rs_incl (R_ba ++ R_mwfail) R_mod B Bw); [vm_compute; reflexivity | exact Hmw].
  - intros W HW.
    destruct (rxe0_lstart HL I ops fr n B Ba Bw W dp Cx Hbl Hba Hdn
                (wframe_rs_incl R_mwfail R_mall Ba Bw ltac:(vm_compute; reflexivity) Fw) HW)
      as (W3 & Ew & HW3 & Hf3 & Hw3 & F3 & G3 & K3 & D3 & L3 & P3).
    rewrite Ew.
    pose proof HW as (HWf & HWk & HWm & HWl).
    pose proof (wframe_trans_rs _ _ _ _ _ Hmw Hf3) as Hall3.
    pose proof (wframe_trans_rs _ _ _ _ _ Fw Hf3) as Hb3.
    assert (S3 : S_state W3 = S_IDLE) by (transitivity (S_state B); [fget Hall3 | rewrite (b1_state _ Hst); exact Hid]).
    assert (A3 : S_cfg_auto_wake W3 = 1)
      by (transitivity (S_cfg_auto_wake B); [fget Hall3 | rewrite (a2_auto_wake _ Hcfg); exact Haw]).
    assert (Wnow : g_now W3 = g_now B) by (transitivity (g_now Ba); [fget Hb3 | exact Anw]).
    assert (Lw : rxe0_lw I W3 (fr_src (rxbuf fr n)) (M_host_counter B) (Cfg_sum_mode B) (OW_e2 B)).
    { apply (rxe0_lw_mk I ops B W3 (fr_src (rxbuf fr n)) (OW_e2 B) Hcore HW3 (rf_src_len _ _ Hf) He2r).
      - transitivity (M_desk_known Ba); [fget Hb3 | exact Ak].
      - transitivity (M_desk Ba); [fget Hb3 | exact Ad].
      - fget Hall3.
      - transitivity (M_foreign Ba); [fget Hb3 | exact Af].
      - fget Hall3.
      - transitivity (GOT_e2 B); [fget Hall3 | exact (og_e2 _ Hog)].
      - exact K3.
      - exact F3.
      - exact D3.
      - fget Hall3.
      - fget Hall3.
      - fget Hall3.
      - fget Hall3.
      - fget Hall3.
      - exact S3. }
    assert (Wf1 : g_fail_next W3 = 1) by (transitivity (g_fail_next B); [fget Hall3 | exact Hfn]).
    destruct (rxe0_lib_wake_fail HL I (Some fr) W3 _ _ _ _ (g_now B) Lw Wf1 Wnow)
      as (Ww & Eww & HWw & Fww & We1 & Wack & Wsent & Wfn & We2).
    exists Ww. split.
    + unfold rxe0_ltail. rewrite S3. change (S_IDLE =? DIGINET_S_ONLINE) with false. cbv beta iota.
      rewrite S3, A3. change ((S_IDLE =? DIGINET_S_IDLE) && negb (1 =? 0)) with true. cbv beta iota.
      rewrite Eww. cbv beta iota. exact eq_refl.
    + pose proof (wframe_trans_rs _ _ _ _ _ Hall3 Fww) as Hall.
      pose proof (wframe_trans_rs _ _ _ _ _ Hb3 Fww) as Hbw.
      pose proof (wframe_trans_rs _ _ _ _ _ Hf3 Fww) as Hmw'.
      pose proof (wframe_trans_rs _ _ _ _ _ Hw3 Fww) as Hww.
      assert (Kp : rxe0_keep B Ww) by (constructor; fget Hall).
      assert (Md : M_desk Ww = fr_src (rxbuf fr n)) by (transitivity (M_desk Ba); [fget Hbw | exact Ad]).
      assert (Mf0 : M_fly_on Ww = 0)
        by (transitivity (M_fly_on B); [fget Hall | exact (b9_idle _ Hst (or_introl Hid))]).
      assert (Si0 : S_inflight Ww = 0).
      { transitivity (S_inflight B); [fget Hall|]. rewrite (b8_on _ Hfly). exact (b9_idle _ Hst (or_introl Hid)). }
      apply (rxe0_post I ops B (rxbuf fr n) W Ww S_IDLE 0 0 (g_now B) (M_desk_counter_valid B) (OW_n B)
               (OW_e2 B + 1) (OW_desk B + 1) Hcore Hroom Kp).
      * refine (wframe_rx _ _ _ _ Hall). vm_compute. reflexivity.
      * transitivity (S_state W3); [fget Fww | exact S3].
      * transitivity (M_state B); [fget Hall | exact Hid].
      * unfold S_IDLE. lia.
      * transitivity (S_desk_known W3); [fget Fww | exact K3].
      * transitivity (M_desk_known Ba); [fget Hbw | exact Ak].
      * rewrite Md. transitivity (S_desk_mac W3); [fget Fww | exact D3].
      * transitivity (S_foreign W3); [fget Fww | exact F3].
      * transitivity (M_foreign Ba); [fget Hbw | exact Af].
      * exact We1.
      * transitivity (M_e1_us Bw); [fget Hmw' | exact Me1].
      * left. reflexivity.
      * exact Wack.
      * transitivity (M_e2_acked Bw); [fget Hmw' | exact Me2].
      * left. reflexivity.
      * exact Wsent.
      * transitivity (M_wake_sent Bw); [fget Hmw' | rewrite Mws; exact Anw].
      * apply Z.le_refl.
      * intros H. exfalso. unfold S_IDLE, S_WAKING in H. discriminate H.
      * transitivity (S_last_rx_us W3); [fget Fww | rewrite L3; transitivity (g_now Ba); [fget Fw | exact Anw]].
      * transitivity (M_last_rx Ba); [fget Hbw | exact Alr].
      * transitivity (S_desk_counter_valid B); [fget Hall | exact (b6_valid _ Hst)].
      * fget Hall.
      * exact (b6_valid01 _ Hst).
      * exact (b6_counter _ Hst).
      * intros _. exact Mf0.
      * apply rxe0_fly_off; [exact Mf0 | exact Si0].
      * intros H. rewrite Mf0 in H. discriminate H.
      * rewrite Wfn. left. reflexivity.
      * assert (E : S_personality Ww = S_personality W3) by fget Fww. rewrite E.
        destruct P3 as [E3|[E3|E3]]; rewrite E3; [exact (e2_personality _ _ Hmisc) | right; left; reflexivity
          | right; right; reflexivity].
      * transitivity (GOT_n B); [fget Hall | exact (og_n _ Hog)].
      * fget Hall.
      * lia.
      * exact (rxe0_t_fr _ B Ww Hog Hall ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
      * exact We2.
      * transitivity (OW_e2 Bw); [fget Hmw' | exact Moe].
      * lia.
      * transitivity (GOT_desk W3); [fget Fww | exact G3].
      * transitivity (OW_desk Ba); [fget Hbw | exact Aod].
      * lia.
      * fget Hww.
      * fget Hww.
      * fget Hww.
      * fget Hww.
      * transitivity (g_now Bw); [fget HWf | transitivity (g_now Ba); [fget Fw | exact Anw]].
      * fget Hww.
      * (* both wakes cleared M.fail / g_fail_next (FT:228, :829); the session stays IDLE *)
        intros _. split; [|unfold S_IDLE, S_ONLINE; lia].
        rewrite Wfn. transitivity (M_fail Bw); [fget Hmw' | exact Mfl].
Qed.

(* ---- leaf 4: ONLINE with auto_wake, the E2 send fails: lost (R_DESK_OFFLINE), then the failed wake ---- *)
Lemma rxe0_leaf_on_fail : forall (HL : links) I ops fr n B, rxe0_ctx I ops fr n B ->
  33 <= fr_body_len (rxbuf fr n) -> M_state B = S_ONLINE -> Cfg_auto_wake B = 1 -> g_fail_next B = 1 ->
  rxe0_goal I ops fr n B.
Proof.
  intros HL I ops fr n B Cx Hbl Hon Haw Hfn.
  pose proof Cx as [Hn Ha Hpre Hacc Hcmd].
  pose proof Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hroom) as Hog.
  pose proof (Hfail Hacc (conj Hcmd Hbl)) as Hmf.
  assert (Hnr : 0 <= OW_n B <= 4) by (pose proof (og_n_range _ Hog); pose proof (wr_n _ Hroom); lia).
  assert (He2r : 0 <= OW_e2 B <= 1) by (pose proof (og_e2_range _ Hog); pose proof (wr_e2 _ Hroom); lia).
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  destruct (rxe0_model_pre HL I ops fr n B Cx Hbl) as (dp & Em & Hdn & Hba).
  set (Ba := rxe0_ma (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) (OW_desk B + 1) dp (tf_addr fr)) in *.
  pose proof Hba as [HBa Hfa Ak Ad Alr Af Aod Aoff Ap Ab].
  assert (As : M_state Ba = S_ONLINE) by (transitivity (M_state B); [fget Hfa | exact Hon]).
  assert (On0 : OW_n Ba = OW_n B) by fget Hfa.
  assert (Anw : g_now Ba = g_now B) by fget Hfa.
  destruct (rxe0_m_lost Ba (OW_n B) HBa As On0 Hnr)
    as (Bl & El & HBl & Fl & Ltk & Ls & Lf & Lv & Ln & Lt1 & Lt2 & Lt3).
  pose proof (wframe_trans_rs _ _ _ _ _ Hfa Fl) as Hml.
  assert (Law : Cfg_auto_wake Bl = 1) by (transitivity (Cfg_auto_wake B); [fget Hml | exact Haw]).
  assert (Lnw : g_now Bl = g_now B) by (transitivity (g_now Ba); [fget Fl | exact Anw]).
  assert (Lk : M_desk_known Bl = 1) by (transitivity (M_desk_known Ba); [fget Fl | exact Ak]).
  assert (Lfo : M_foreign Bl = 0) by (transitivity (M_foreign Ba); [fget Fl | exact Af]).
  assert (Le2 : OW_e2 Bl = OW_e2 B) by fget Hml.
  assert (Lfl : M_fail Bl = 1) by (transitivity (M_fail B); [fget Hml | rewrite Hmf; exact Hfn]).
  destruct (rxe0_m_wake_fail Bl (OW_e2 B) HBl Lk Lfo Le2 He2r Lfl)
    as (Bw & Emw & HBw & Fw & Me2 & Me1 & Mws & Moe & Mfl).
  pose proof (wframe_trans_rs _ _ _ _ _ Fl Fw) as Haw2.
  pose proof (wframe_trans_rs _ _ _ _ _ Hfa Haw2) as Hmw.
  unfold rxe0_goal. rewrite Em. exists Bw. split; [|split; [|split]].
  - unfold rxe0_mtail. rewrite As, (Z.eqb_refl S_ONLINE). cbv beta iota. rewrite El. cbv beta iota.
    rewrite Ls, Law, (Z.eqb_refl S_IDLE), rxe0_truth1. change (true && true) with true. cbv beta iota.
    rewrite Emw. cbv beta iota. exact eq_refl.
  - apply (rxe0_tick I ops B Bw Hcore).
    + assert (E : M_state Bw = S_IDLE) by (transitivity (M_state Bl); [fget Fw | exact Ls]).
      rewrite E. intros H. exfalso. unfold S_IDLE, S_WAKING in H. discriminate H.
    + transitivity (M_last_rx Ba); [fget Haw2 | exact Alr].
    + transitivity (g_now Bl); [fget Fw | exact Lnw].
    + fget Hmw.
    + fget Hmw.
  - apply (wframe_rs_incl (R_ba ++ R_mlost ++ R_mwfail) R_mod B Bw); [vm_compute; reflexivity | exact Hmw].
  - intros W HW.
    destruct (rxe0_lstart HL I ops fr n B Ba Bw W dp Cx Hbl Hba Hdn
                (wframe_rs_incl (R_mlost ++ R_mwfail) R_mall Ba Bw ltac:(vm_compute; reflexivity) Haw2) HW)
      as (W3 & Ew & HW3 & Hf3 & Hw3 & F3 & G3 & K3 & D3 & L3 & P3).
    rewrite Ew.
    pose proof HW as (HWf & HWk & HWm & HWl).
    pose proof (wframe_trans_rs _ _ _ _ _ Hmw Hf3) as Hall3.
    assert (S3 : S_state W3 = S_ONLINE)
      by (transitivity (S_state B); [fget Hall3 | rewrite (b1_state _ Hst); exact Hon]).
    assert (N3 : S_notify W3 = ti_notice I) by (transitivity (S_notify B); [fget Hall3 | exact (a3_notify _ _ Hio)]).
    assert (Gn3 : GOT_n W3 = OW_n B) by (transitivity (GOT_n B); [fget Hall3 | exact (og_n _ Hog)]).
    destruct (rxe0_lib_lost I (Some fr) W3 (OW_n B) HW3 S3 N3 Gn3 Hnr)
      as (Wl & Ewl & HWl' & Fwl & Wtk & Ws & Wi & Wv & Wn & Wt1 & Wt2 & Wt3).
    pose proof (wframe_trans_rs _ _ _ _ _ Hall3 Fwl) as Hall4.
    pose proof (wframe_trans_rs _ _ _ _ _ Haw2 (wframe_trans_rs _ _ _ _ _ Hf3 Fwl)) as Hb4.
    assert (A4 : S_cfg_auto_wake Wl = 1)
      by (transitivity (S_cfg_auto_wake B); [fget Hall4 | rewrite (a2_auto_wake _ Hcfg); exact Haw]).
    assert (Wnow : g_now Wl = g_now B) by (transitivity (g_now Ba); [fget Hb4 | exact Anw]).
    assert (Lw : rxe0_lw I Wl (fr_src (rxbuf fr n)) (M_host_counter B) (Cfg_sum_mode B) (OW_e2 B)).
    { apply (rxe0_lw_mk I ops B Wl (fr_src (rxbuf fr n)) (OW_e2 B) Hcore HWl' (rf_src_len _ _ Hf) He2r).
      - transitivity (M_desk_known Ba); [fget Hb4 | exact Ak].
      - transitivity (M_desk Ba); [fget Hb4 | exact Ad].
      - fget Hall4.
      - transitivity (M_foreign Ba); [fget Hb4 | exact Af].
      - fget Hall4.
      - transitivity (GOT_e2 B); [fget Hall4 | exact (og_e2 _ Hog)].
      - transitivity (S_desk_known W3); [fget Fwl | exact K3].
      - transitivity (S_foreign W3); [fget Fwl | exact F3].
      - transitivity (S_desk_mac W3); [fget Fwl | exact D3].
      - fget Hall4.
      - fget Hall4.
      - fget Hall4.
      - fget Hall4.
      - fget Hall4.
      - exact Ws. }
    assert (Wf1 : g_fail_next Wl = 1) by (transitivity (g_fail_next B); [fget Hall4 | exact Hfn]).
    destruct (rxe0_lib_wake_fail HL I (Some fr) Wl _ _ _ _ (g_now B) Lw Wf1 Wnow)
      as (Ww & Eww & HWw & Fww & We1 & Wack & Wsent & Wfn & We2).
    exists Ww. split.
    + unfold rxe0_ltail. rewrite S3. change DIGINET_S_ONLINE with S_ONLINE. rewrite (Z.eqb_refl S_ONLINE).
      cbv beta iota. rewrite Ewl. cbv beta iota. rewrite Ws, A4.
      change ((S_IDLE =? DIGINET_S_IDLE) && negb (1 =? 0)) with true. cbv beta iota.
      rewrite Eww. cbv beta iota. exact eq_refl.
    + pose proof (wframe_trans_rs _ _ _ _ _ Hall4 Fww) as Hall.
      pose proof (wframe_trans_rs _ _ _ _ _ Hb4 Fww) as Hbw.
      pose proof (wframe_trans_rs _ _ _ _ _ Hf3 (wframe_trans_rs _ _ _ _ _ Fwl Fww)) as Hmw'.
      pose proof (wframe_trans_rs _ _ _ _ _ Fw Hmw') as Hlw.
      pose proof (wframe_trans_rs _ _ _ _ _ Hw3 (wframe_trans_rs _ _ _ _ _ Fwl Fww)) as Hww.
      assert (Kp : rxe0_keep B Ww) by (constructor; fget Hall).
      assert (Md : M_desk Ww = fr_src (rxbuf fr n)) by (transitivity (M_desk Ba); [fget Hbw | exact Ad]).
      assert (Mf0 : M_fly_on Ww = 0) by (transitivity (M_fly_on Bl); [fget Hlw | exact Lf]).
      assert (Si0 : S_inflight Ww = 0) by (transitivity (S_inflight Wl); [fget Fww | exact Wi]).
      (* the transition entries: below OW.n B those of B (ow_got_eq B), at OW.n B the lost on both sides *)
      assert (TG : rxe0_tkg B Ww (OW_n B)).
      { apply (rxe0_tkg_trans _ W3).
        - apply (rxe0_tkg_le _ _ TRANS_MAX); [exact (rxe0_tkg_fr _ _ _ Hall3 ltac:(vm_compute; reflexivity))
                                             | unfold TRANS_MAX; lia].
        - apply (rxe0_tkg_trans _ Wl); [exact Wtk|].
          apply (rxe0_tkg_le _ _ TRANS_MAX); [exact (rxe0_tkg_fr _ _ _ Fww ltac:(vm_compute; reflexivity))
                                             | unfold TRANS_MAX; lia]. }
      assert (TO : rxe0_tko Bl Ww TRANS_MAX) by exact (rxe0_tko_fr _ _ _ Hlw ltac:(vm_compute; reflexivity)).
      assert (TO' : rxe0_tko B Ww (OW_n B)).
      { apply (rxe0_tko_trans _ Ba).
        - apply (rxe0_tko_le _ _ TRANS_MAX); [exact (rxe0_tko_fr _ _ _ Hfa ltac:(vm_compute; reflexivity))
                                             | unfold TRANS_MAX; lia].
        - apply (rxe0_tko_trans _ Bl); [exact Ltk|].
          apply (rxe0_tko_le _ _ TRANS_MAX); [exact TO | unfold TRANS_MAX; lia]. }
      apply (rxe0_post I ops B (rxbuf fr n) W Ww S_IDLE 0 0 (g_now B) 0 (OW_n B + 1) (OW_e2 B + 1) (OW_desk B + 1)
               Hcore Hroom Kp).
      * refine (wframe_rx _ _ _ _ Hall). vm_compute. reflexivity.
      * transitivity (S_state Wl); [fget Fww | exact Ws].
      * transitivity (M_state Bl); [fget Hlw | exact Ls].
      * unfold S_IDLE. lia.
      * transitivity (S_desk_known W3); [fget (wframe_trans_rs _ _ _ _ _ Fwl Fww) | exact K3].
      * transitivity (M_desk_known Ba); [fget Hbw | exact Ak].
      * rewrite Md. transitivity (S_desk_mac W3); [fget (wframe_trans_rs _ _ _ _ _ Fwl Fww) | exact D3].
      * transitivity (S_foreign W3); [fget (wframe_trans_rs _ _ _ _ _ Fwl Fww) | exact F3].
      * transitivity (M_foreign Ba); [fget Hbw | exact Af].
      * exact We1.
      * transitivity (M_e1_us Bw); [fget (wframe_trans_rs _ _ _ _ _ Hf3 (wframe_trans_rs _ _ _ _ _ Fwl Fww)) | exact Me1].
      * left. reflexivity.
      * exact Wack.
      * transitivity (M_e2_acked Bw); [fget (wframe_trans_rs _ _ _ _ _ Hf3 (wframe_trans_rs _ _ _ _ _ Fwl Fww)) | exact Me2].
      * left. reflexivity.
      * exact Wsent.
      * transitivity (M_wake_sent Bw); [fget (wframe_trans_rs _ _ _ _ _ Hf3 (wframe_trans_rs _ _ _ _ _ Fwl Fww))
          | rewrite Mws; exact Lnw].
      * apply Z.le_refl.
      * intros H. exfalso. unfold S_IDLE, S_WAKING in H. discriminate H.
      * transitivity (S_last_rx_us W3); [fget (wframe_trans_rs _ _ _ _ _ Fwl Fww)
          | rewrite L3; transitivity (g_now Bl); [fget Fw | exact Lnw]].
      * transitivity (M_last_rx Ba); [fget Hbw | exact Alr].
      * transitivity (S_desk_counter_valid Wl); [fget Fww | exact Wv].
      * transitivity (M_desk_counter_valid Bl); [fget Hlw | exact Lv].
      * left. reflexivity.
      * intros H. discriminate H.
      * intros _. exact Mf0.
      * apply rxe0_fly_off; [exact Mf0 | exact Si0].
      * intros H. rewrite Mf0 in H. discriminate H.
      * rewrite Wfn. left. reflexivity.
      * assert (E : S_personality Ww = S_personality W3) by fget (wframe_trans_rs _ _ _ _ _ Fwl Fww). rewrite E.
        destruct P3 as [E3|[E3|E3]]; rewrite E3; [exact (e2_personality _ _ Hmisc) | right; left; reflexivity
          | right; right; reflexivity].
      * transitivity (GOT_n Wl); [fget Fww | exact Wn].
      * transitivity (OW_n Bl); [fget Hlw | exact Ln].
      * lia.
      * intros i Hi Hi2. destruct (Z.lt_ge_cases i (OW_n B)) as [Hlt | Hge].
        -- exact (rxe0_t_below B Ww Hog TG TO' i (conj (proj1 Hi) Hlt) Hi2).
        -- assert (Ei : i = OW_n B) by lia. subst i.
           destruct (rxe0_tkg_fr _ _ _ Fww ltac:(vm_compute; reflexivity) (OW_n B) ltac:(unfold TRANS_MAX; lia))
             as (Q1 & Q2 & Q3).
           destruct (TO (OW_n B) ltac:(unfold TRANS_MAX; lia)) as (O1 & O2 & O3).
           rewrite Q1, Q2, Q3, Wt1, Wt2, Wt3, O1, O2, O3, Lt1, Lt2, Lt3.
           exact (conj eq_refl (conj eq_refl eq_refl)).
      * exact We2.
      * transitivity (OW_e2 Bw); [fget (wframe_trans_rs _ _ _ _ _ Hf3 (wframe_trans_rs _ _ _ _ _ Fwl Fww)) | exact Moe].
      * lia.
      * transitivity (GOT_desk W3); [fget (wframe_trans_rs _ _ _ _ _ Fwl Fww) | exact G3].
      * transitivity (OW_desk Ba); [fget Hbw | exact Aod].
      * lia.
      * fget Hww.
      * fget Hww.
      * fget Hww.
      * fget Hww.
      * transitivity (g_now Bw); [fget HWf | transitivity (g_now Bl); [fget Fw | exact Lnw]].
      * fget Hww.
      * (* both wakes cleared M.fail / g_fail_next (FT:228, :829); the session stays IDLE *)
        intros _. split; [|unfold S_IDLE, S_ONLINE; lia].
        rewrite Wfn. transitivity (M_fail Bw); [fget Hmw' | exact Mfl].
Qed.

(* ---- leaf 5: IDLE with auto_wake, the E2 goes out: both go WAKING (R_WAKE), the E2 in flight ---- *)
Lemma rxe0_leaf_idle_ok : forall (HL : links) I ops fr n B, rxe0_ctx I ops fr n B ->
  33 <= fr_body_len (rxbuf fr n) -> M_state B = S_IDLE -> Cfg_auto_wake B = 1 -> g_fail_next B = 0 ->
  rxe0_goal I ops fr n B.
Proof.
  intros HL I ops fr n B Cx Hbl Hid Haw Hfn.
  pose proof Cx as [Hn Ha Hpre Hacc Hcmd].
  pose proof Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hroom) as Hog.
  pose proof (Hfail Hacc (conj Hcmd Hbl)) as Hmf.
  assert (Hnr : 0 <= OW_n B <= 4) by (pose proof (og_n_range _ Hog); pose proof (wr_n _ Hroom); lia).
  assert (He2r : 0 <= OW_e2 B <= 1) by (pose proof (og_e2_range _ Hog); pose proof (wr_e2 _ Hroom); lia).
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  destruct (rxe0_model_pre HL I ops fr n B Cx Hbl) as (dp & Em & Hdn & Hba).
  set (Ba := rxe0_ma (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) (OW_desk B + 1) dp (tf_addr fr)) in *.
  pose proof Hba as [HBa Hfa Ak Ad Alr Af Aod Aoff Ap Ab].
  assert (As : M_state Ba = S_IDLE) by (transitivity (M_state B); [fget Hfa | exact Hid]).
  assert (Aaw : Cfg_auto_wake Ba = 1) by (transitivity (Cfg_auto_wake B); [fget Hfa | exact Haw]).
  assert (Ae2 : OW_e2 Ba = OW_e2 B) by fget Hfa.
  assert (Afl : M_fail Ba = 0) by (transitivity (M_fail B); [fget Hfa | rewrite Hmf; exact Hfn]).
  assert (On0 : OW_n Ba = OW_n B) by fget Hfa.
  assert (Anw : g_now Ba = g_now B) by fget Hfa.
  destruct (rxe0_m_wake_ok Ba (OW_e2 B) (OW_n B) HBa Ak Af Ae2 He2r Afl As On0 ltac:(lia))
    as (Bw & Emw & HBw & Fw & Mtk & Me2 & Me1 & Mws & Moe & Mfl & Mst & Mon & Mt1 & Mt2 & Mt3).
  pose proof (wframe_trans_rs _ _ _ _ _ Hfa Fw) as Hmw.
  unfold rxe0_goal. rewrite Em. exists Bw. split; [|split; [|split]].
  - unfold rxe0_mtail. rewrite As. change (S_IDLE =? S_ONLINE) with false. cbv beta iota.
    rewrite As, Aaw, (Z.eqb_refl S_IDLE), rxe0_truth1. change (true && true) with true. cbv beta iota.
    rewrite Emw. cbv beta iota. exact eq_refl.
  - apply (rxe0_tick I ops B Bw Hcore).
    + intros _. rewrite Mws, Anw. pose proof (a1_wake_timeout _ Hcfg).
      split; [apply Z.le_refl | rewrite Z.sub_diag; slia].
    + transitivity (M_last_rx Ba); [fget Fw | exact Alr].
    + transitivity (g_now Ba); [fget Fw | exact Anw].
    + fget Hmw.
    + fget Hmw.
  - apply (wframe_rs_incl (R_ba ++ R_mwake) R_mod B Bw); [vm_compute; reflexivity | exact Hmw].
  - intros W HW.
    destruct (rxe0_lstart HL I ops fr n B Ba Bw W dp Cx Hbl Hba Hdn
                (wframe_rs_incl R_mwake R_mall Ba Bw ltac:(vm_compute; reflexivity) Fw) HW)
      as (W3 & Ew & HW3 & Hf3 & Hw3 & F3 & G3 & K3 & D3 & L3 & P3).
    rewrite Ew.
    pose proof HW as (HWf & HWk & HWm & HWl).
    pose proof (wframe_trans_rs _ _ _ _ _ Hmw Hf3) as Hall3.
    pose proof (wframe_trans_rs _ _ _ _ _ Fw Hf3) as Hb3.
    assert (S3 : S_state W3 = S_IDLE) by (transitivity (S_state B); [fget Hall3 | rewrite (b1_state _ Hst); exact Hid]).
    assert (A3 : S_cfg_auto_wake W3 = 1)
      by (transitivity (S_cfg_auto_wake B); [fget Hall3 | rewrite (a2_auto_wake _ Hcfg); exact Haw]).
    assert (Wnow : g_now W3 = g_now B) by (transitivity (g_now Ba); [fget Hb3 | exact Anw]).
    assert (Lw : rxe0_lw I W3 (fr_src (rxbuf fr n)) (M_host_counter B) (Cfg_sum_mode B) (OW_e2 B)).
    { apply (rxe0_lw_mk I ops B W3 (fr_src (rxbuf fr n)) (OW_e2 B) Hcore HW3 (rf_src_len _ _ Hf) He2r).
      - transitivity (M_desk_known Ba); [fget Hb3 | exact Ak].
      - transitivity (M_desk Ba); [fget Hb3 | exact Ad].
      - fget Hall3.
      - transitivity (M_foreign Ba); [fget Hb3 | exact Af].
      - fget Hall3.
      - transitivity (GOT_e2 B); [fget Hall3 | exact (og_e2 _ Hog)].
      - exact K3.
      - exact F3.
      - exact D3.
      - fget Hall3.
      - fget Hall3.
      - fget Hall3.
      - fget Hall3.
      - fget Hall3.
      - exact S3. }
    assert (Wf0 : g_fail_next W3 = 0) by (transitivity (g_fail_next B); [fget Hall3 | exact Hfn]).
    assert (Gn3 : GOT_n W3 = OW_n B) by (transitivity (GOT_n B); [fget Hall3 | exact (og_n _ Hog)]).
    destruct (rxe0_lib_wake_ok HL I (Some fr) W3 _ _ _ _ (g_now B) (OW_n B) Lw Wf0 Wnow Gn3 ltac:(lia))
      as (Ww & Eww & HWw & Fww & Wtk & We1 & Wack & Wsent & Wfn & We2 & Wst & Wn & Wt1 & Wt2 & Wt3 & Wi & Wic
          & Wir & Wis & Wil & Wfo & Wfc & Wfk & Wfr & Wfs & Wfl & Wfm & Wif).
    exists Ww. split.
    + unfold rxe0_ltail. rewrite S3. change (S_IDLE =? DIGINET_S_ONLINE) with false. cbv beta iota.
      rewrite S3, A3. change ((S_IDLE =? DIGINET_S_IDLE) && negb (1 =? 0)) with true. cbv beta iota.
      rewrite Eww. cbv beta iota. exact eq_refl.
    + pose proof (wframe_trans_rs _ _ _ _ _ Hall3 Fww) as Hall.
      pose proof (wframe_trans_rs _ _ _ _ _ Hb3 Fww) as Hbw.
      pose proof (wframe_trans_rs _ _ _ _ _ Hf3 Fww) as Hmw'.
      pose proof (wframe_trans_rs _ _ _ _ _ Hw3 Fww) as Hww.
      assert (Kp : rxe0_keep B Ww) by (constructor; fget Hall).
      assert (Md : M_desk Ww = fr_src (rxbuf fr n)) by (transitivity (M_desk Ba); [fget Hbw | exact Ad]).
      assert (Ms : M_state Ww = S_WAKING) by (transitivity (M_state Bw); [fget Hmw' | exact Mst]).
      (* the transition entries: below OW.n B those of B (ow_got_eq B), at OW.n B the wake on both sides *)
      assert (TG : rxe0_tkg B Ww (OW_n B)).
      { apply (rxe0_tkg_trans _ W3); [|exact Wtk].
        apply (rxe0_tkg_le _ _ TRANS_MAX); [exact (rxe0_tkg_fr _ _ _ Hall3 ltac:(vm_compute; reflexivity))
                                           | unfold TRANS_MAX; lia]. }
      assert (TO : rxe0_tko Bw Ww TRANS_MAX) by exact (rxe0_tko_fr _ _ _ Hmw' ltac:(vm_compute; reflexivity)).
      assert (TO' : rxe0_tko B Ww (OW_n B)).
      { apply (rxe0_tko_trans _ Ba).
        - apply (rxe0_tko_le _ _ TRANS_MAX); [exact (rxe0_tko_fr _ _ _ Hfa ltac:(vm_compute; reflexivity))
                                             | unfold TRANS_MAX; lia].
        - apply (rxe0_tko_trans _ Bw); [exact Mtk|].
          apply (rxe0_tko_le _ _ TRANS_MAX); [exact TO | unfold TRANS_MAX; lia]. }
      apply (rxe0_post I ops B (rxbuf fr n) W Ww S_WAKING 0 0 (g_now B) (M_desk_counter_valid B) (OW_n B + 1)
               (OW_e2 B + 1) (OW_desk B + 1) Hcore Hroom Kp).
      * refine (wframe_rx _ _ _ _ Hall). vm_compute. reflexivity.
      * exact Wst.
      * exact Ms.
      * unfold S_WAKING. lia.
      * transitivity (S_desk_known W3); [fget Fww | exact K3].
      * transitivity (M_desk_known Ba); [fget Hbw | exact Ak].
      * rewrite Md. transitivity (S_desk_mac W3); [fget Fww | exact D3].
      * transitivity (S_foreign W3); [fget Fww | exact F3].
      * transitivity (M_foreign Ba); [fget Hbw | exact Af].
      * exact We1.
      * transitivity (M_e1_us Bw); [fget Hmw' | exact Me1].
      * left. reflexivity.
      * exact Wack.
      * transitivity (M_e2_acked Bw); [fget Hmw' | exact Me2].
      * left. reflexivity.
      * exact Wsent.
      * transitivity (M_wake_sent Bw); [fget Hmw' | rewrite Mws; exact Anw].
      * apply Z.le_refl.
      * intros _. rewrite Z.sub_diag. pose proof (a1_wake_timeout _ Hcfg). slia.
      * transitivity (S_last_rx_us W3); [fget Fww | rewrite L3; transitivity (g_now Ba); [fget Fw | exact Anw]].
      * transitivity (M_last_rx Ba); [fget Hbw | exact Alr].
      * transitivity (S_desk_counter_valid B); [fget Hall | exact (b6_valid _ Hst)].
      * fget Hall.
      * exact (b6_valid01 _ Hst).
      * exact (b6_counter _ Hst).
      * intros [H|H]; exfalso; unfold S_WAKING, S_IDLE, S_CLOSED in H; discriminate H.
      * refine (rxe0_fly_wake Ww (fr_src (rxbuf fr n)) (M_host_counter B) (Cfg_sum_mode B) Wfo Wi Ms Wic Wfk _
                  Wir Wfr _ Wil Wfl Wfc Md _ Wfm Wif).
        -- transitivity (S_host_counter B); [fget Hall | exact (b7_host_counter _ Hst)].
        -- rewrite Wis, Wfs. reflexivity.
        -- fget Hall.
      * intros _. rewrite Wfs. pose proof (a1_ack_timeout _ Hcfg).
        split; [apply Z.le_refl | rewrite Z.sub_diag; slia].
      * rewrite Wfn. left. reflexivity.
      * assert (E : S_personality Ww = S_personality W3) by fget Fww. rewrite E.
        destruct P3 as [E3|[E3|E3]]; rewrite E3; [exact (e2_personality _ _ Hmisc) | right; left; reflexivity
          | right; right; reflexivity].
      * exact Wn.
      * transitivity (OW_n Bw); [fget Hmw' | exact Mon].
      * lia.
      * intros i Hi Hi2. destruct (Z.lt_ge_cases i (OW_n B)) as [Hlt | Hge].
        -- exact (rxe0_t_below B Ww Hog TG TO' i (conj (proj1 Hi) Hlt) Hi2).
        -- assert (Ei : i = OW_n B) by lia. subst i.
           destruct (TO (OW_n B) ltac:(unfold TRANS_MAX; lia)) as (O1 & O2 & O3).
           rewrite Wt1, Wt2, Wt3, O1, O2, O3, Mt1, Mt2, Mt3. exact (conj eq_refl (conj eq_refl eq_refl)).
      * exact We2.
      * transitivity (OW_e2 Bw); [fget Hmw' | exact Moe].
      * lia.
      * transitivity (GOT_desk W3); [fget Fww | exact G3].
      * transitivity (OW_desk Ba); [fget Hbw | exact Aod].
      * lia.
      * fget Hww.
      * fget Hww.
      * fget Hww.
      * fget Hww.
      * transitivity (g_now Bw); [fget HWf | transitivity (g_now Ba); [fget Fw | exact Anw]].
      * fget Hww.
      * (* both wakes cleared M.fail / g_fail_next (FT:228, :829); the session is WAKING *)
        intros _. split; [|unfold S_WAKING, S_ONLINE; lia].
        rewrite Wfn. transitivity (M_fail Bw); [fget Hmw' | exact Mfl].
Qed.

(* ---- leaf 6: ONLINE with auto_wake, the E2 goes out: lost (R_DESK_OFFLINE), then WAKING (R_WAKE) ---- *)
Lemma rxe0_leaf_on_ok : forall (HL : links) I ops fr n B, rxe0_ctx I ops fr n B ->
  33 <= fr_body_len (rxbuf fr n) -> M_state B = S_ONLINE -> Cfg_auto_wake B = 1 -> g_fail_next B = 0 ->
  rxe0_goal I ops fr n B.
Proof.
  intros HL I ops fr n B Cx Hbl Hon Haw Hfn.
  pose proof Cx as [Hn Ha Hpre Hacc Hcmd].
  pose proof Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hroom) as Hog.
  pose proof (Hfail Hacc (conj Hcmd Hbl)) as Hmf.
  assert (Hnr : 0 <= OW_n B <= 4) by (pose proof (og_n_range _ Hog); pose proof (wr_n _ Hroom); lia).
  assert (He2r : 0 <= OW_e2 B <= 1) by (pose proof (og_e2_range _ Hog); pose proof (wr_e2 _ Hroom); lia).
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  destruct (rxe0_model_pre HL I ops fr n B Cx Hbl) as (dp & Em & Hdn & Hba).
  set (Ba := rxe0_ma (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) (OW_desk B + 1) dp (tf_addr fr)) in *.
  pose proof Hba as [HBa Hfa Ak Ad Alr Af Aod Aoff Ap Ab].
  assert (As : M_state Ba = S_ONLINE) by (transitivity (M_state B); [fget Hfa | exact Hon]).
  assert (On0 : OW_n Ba = OW_n B) by fget Hfa.
  assert (Anw : g_now Ba = g_now B) by fget Hfa.
  destruct (rxe0_m_lost Ba (OW_n B) HBa As On0 Hnr)
    as (Bl & El & HBl & Fl & Ltk & Ls & Lf & Lv & Ln & Lt1 & Lt2 & Lt3).
  pose proof (wframe_trans_rs _ _ _ _ _ Hfa Fl) as Hml.
  assert (Law : Cfg_auto_wake Bl = 1) by (transitivity (Cfg_auto_wake B); [fget Hml | exact Haw]).
  assert (Lnw : g_now Bl = g_now B) by (transitivity (g_now Ba); [fget Fl | exact Anw]).
  assert (Lk : M_desk_known Bl = 1) by (transitivity (M_desk_known Ba); [fget Fl | exact Ak]).
  assert (Lfo : M_foreign Bl = 0) by (transitivity (M_foreign Ba); [fget Fl | exact Af]).
  assert (Le2 : OW_e2 Bl = OW_e2 B) by fget Hml.
  assert (Lfl : M_fail Bl = 0) by (transitivity (M_fail B); [fget Hml | rewrite Hmf; exact Hfn]).
  destruct (rxe0_m_wake_ok Bl (OW_e2 B) (OW_n B + 1) HBl Lk Lfo Le2 He2r Lfl Ls Ln ltac:(lia))
    as (Bw & Emw & HBw & Fw & Mtk & Me2 & Me1 & Mws & Moe & Mfl & Mst & Mon & Mt1 & Mt2 & Mt3).
  pose proof (wframe_trans_rs _ _ _ _ _ Fl Fw) as Haw2.
  pose proof (wframe_trans_rs _ _ _ _ _ Hfa Haw2) as Hmw.
  unfold rxe0_goal. rewrite Em. exists Bw. split; [|split; [|split]].
  - unfold rxe0_mtail. rewrite As, (Z.eqb_refl S_ONLINE). cbv beta iota. rewrite El. cbv beta iota.
    rewrite Ls, Law, (Z.eqb_refl S_IDLE), rxe0_truth1. change (true && true) with true. cbv beta iota.
    rewrite Emw. cbv beta iota. exact eq_refl.
  - apply (rxe0_tick I ops B Bw Hcore).
    + intros _. rewrite Mws, Lnw. pose proof (a1_wake_timeout _ Hcfg).
      split; [apply Z.le_refl | rewrite Z.sub_diag; slia].
    + transitivity (M_last_rx Ba); [fget Haw2 | exact Alr].
    + transitivity (g_now Bl); [fget Fw | exact Lnw].
    + fget Hmw.
    + fget Hmw.
  - apply (wframe_rs_incl (R_ba ++ R_mlost ++ R_mwake) R_mod B Bw); [vm_compute; reflexivity | exact Hmw].
  - intros W HW.
    destruct (rxe0_lstart HL I ops fr n B Ba Bw W dp Cx Hbl Hba Hdn
                (wframe_rs_incl (R_mlost ++ R_mwake) R_mall Ba Bw ltac:(vm_compute; reflexivity) Haw2) HW)
      as (W3 & Ew & HW3 & Hf3 & Hw3 & F3 & G3 & K3 & D3 & L3 & P3).
    rewrite Ew.
    pose proof HW as (HWf & HWk & HWm & HWl).
    pose proof (wframe_trans_rs _ _ _ _ _ Hmw Hf3) as Hall3.
    assert (S3 : S_state W3 = S_ONLINE)
      by (transitivity (S_state B); [fget Hall3 | rewrite (b1_state _ Hst); exact Hon]).
    assert (N3 : S_notify W3 = ti_notice I) by (transitivity (S_notify B); [fget Hall3 | exact (a3_notify _ _ Hio)]).
    assert (Gn3 : GOT_n W3 = OW_n B) by (transitivity (GOT_n B); [fget Hall3 | exact (og_n _ Hog)]).
    destruct (rxe0_lib_lost I (Some fr) W3 (OW_n B) HW3 S3 N3 Gn3 Hnr)
      as (Wl & Ewl & HWl' & Fwl & Wtk & Ws & Wi & Wv & Wn & Wt1 & Wt2 & Wt3).
    pose proof (wframe_trans_rs _ _ _ _ _ Hall3 Fwl) as Hall4.
    pose proof (wframe_trans_rs _ _ _ _ _ Haw2 (wframe_trans_rs _ _ _ _ _ Hf3 Fwl)) as Hb4.
    assert (A4 : S_cfg_auto_wake Wl = 1)
      by (transitivity (S_cfg_auto_wake B); [fget Hall4 | rewrite (a2_auto_wake _ Hcfg); exact Haw]).
    assert (Wnow : g_now Wl = g_now B) by (transitivity (g_now Ba); [fget Hb4 | exact Anw]).
    assert (Lw : rxe0_lw I Wl (fr_src (rxbuf fr n)) (M_host_counter B) (Cfg_sum_mode B) (OW_e2 B)).
    { apply (rxe0_lw_mk I ops B Wl (fr_src (rxbuf fr n)) (OW_e2 B) Hcore HWl' (rf_src_len _ _ Hf) He2r).
      - transitivity (M_desk_known Ba); [fget Hb4 | exact Ak].
      - transitivity (M_desk Ba); [fget Hb4 | exact Ad].
      - fget Hall4.
      - transitivity (M_foreign Ba); [fget Hb4 | exact Af].
      - fget Hall4.
      - transitivity (GOT_e2 B); [fget Hall4 | exact (og_e2 _ Hog)].
      - transitivity (S_desk_known W3); [fget Fwl | exact K3].
      - transitivity (S_foreign W3); [fget Fwl | exact F3].
      - transitivity (S_desk_mac W3); [fget Fwl | exact D3].
      - fget Hall4.
      - fget Hall4.
      - fget Hall4.
      - fget Hall4.
      - fget Hall4.
      - exact Ws. }
    assert (Wf0 : g_fail_next Wl = 0) by (transitivity (g_fail_next B); [fget Hall4 | exact Hfn]).
    destruct (rxe0_lib_wake_ok HL I (Some fr) Wl _ _ _ _ (g_now B) (OW_n B + 1) Lw Wf0 Wnow Wn ltac:(lia))
      as (Ww & Eww & HWw & Fww & Xtk & We1 & Wack & Wsent & Wfn & We2 & Wst & Xn & Xt1 & Xt2 & Xt3 & Wi' & Wic
          & Wir & Wis & Wil & Wfo & Wfc & Wfk & Wfr & Wfs & Wfl & Wfm & Wif).
    exists Ww. split.
    + unfold rxe0_ltail. rewrite S3. change DIGINET_S_ONLINE with S_ONLINE. rewrite (Z.eqb_refl S_ONLINE).
      cbv beta iota. rewrite Ewl. cbv beta iota. rewrite Ws, A4.
      change ((S_IDLE =? DIGINET_S_IDLE) && negb (1 =? 0)) with true. cbv beta iota.
      rewrite Eww. cbv beta iota. exact eq_refl.
    + pose proof (wframe_trans_rs _ _ _ _ _ Hall4 Fww) as Hall.
      pose proof (wframe_trans_rs _ _ _ _ _ Hb4 Fww) as Hbw.
      pose proof (wframe_trans_rs _ _ _ _ _ Fwl Fww) as Hlw'.
      pose proof (wframe_trans_rs _ _ _ _ _ Hf3 Hlw') as Hmw'.
      pose proof (wframe_trans_rs _ _ _ _ _ Fw Hmw') as Hlw.
      pose proof (wframe_trans_rs _ _ _ _ _ Hw3 Hlw') as Hww.
      assert (Kp : rxe0_keep B Ww) by (constructor; fget Hall).
      assert (Md : M_desk Ww = fr_src (rxbuf fr n)) by (transitivity (M_desk Ba); [fget Hbw | exact Ad]).
      assert (Ms : M_state Ww = S_WAKING) by (transitivity (M_state Bw); [fget Hmw' | exact Mst]).
      assert (Bwn : g_now Bw = g_now B) by (transitivity (g_now Bl); [fget Fw | exact Lnw]).
      (* the transition entries: below OW.n B those of B (ow_got_eq B), then the lost and the wake on both
         sides *)
      assert (TG : rxe0_tkg B Ww (OW_n B)).
      { apply (rxe0_tkg_trans _ W3).
        - apply (rxe0_tkg_le _ _ TRANS_MAX); [exact (rxe0_tkg_fr _ _ _ Hall3 ltac:(vm_compute; reflexivity))
                                             | unfold TRANS_MAX; lia].
        - apply (rxe0_tkg_trans _ Wl); [exact Wtk|]. apply (rxe0_tkg_le _ _ (OW_n B + 1)); [exact Xtk | lia]. }
      assert (TO : rxe0_tko Bw Ww TRANS_MAX) by exact (rxe0_tko_fr _ _ _ Hmw' ltac:(vm_compute; reflexivity)).
      assert (TO' : rxe0_tko B Ww (OW_n B)).
      { apply (rxe0_tko_trans _ Ba).
        - apply (rxe0_tko_le _ _ TRANS_MAX); [exact (rxe0_tko_fr _ _ _ Hfa ltac:(vm_compute; reflexivity))
                                             | unfold TRANS_MAX; lia].
        - apply (rxe0_tko_trans _ Bl); [exact Ltk|]. apply (rxe0_tko_trans _ Bw).
          + apply (rxe0_tko_le _ _ (OW_n B + 1)); [exact Mtk | lia].
          + apply (rxe0_tko_le _ _ TRANS_MAX); [exact TO | unfold TRANS_MAX; lia]. }
      apply (rxe0_post I ops B (rxbuf fr n) W Ww S_WAKING 0 0 (g_now B) 0 (OW_n B + 1 + 1) (OW_e2 B + 1)
               (OW_desk B + 1) Hcore Hroom Kp).
      * refine (wframe_rx _ _ _ _ Hall). vm_compute. reflexivity.
      * exact Wst.
      * exact Ms.
      * unfold S_WAKING. lia.
      * transitivity (S_desk_known W3); [fget Hlw' | exact K3].
      * transitivity (M_desk_known Ba); [fget Hbw | exact Ak].
      * rewrite Md. transitivity (S_desk_mac W3); [fget Hlw' | exact D3].
      * transitivity (S_foreign W3); [fget Hlw' | exact F3].
      * transitivity (M_foreign Ba); [fget Hbw | exact Af].
      * exact We1.
      * transitivity (M_e1_us Bw); [fget Hmw' | exact Me1].
      * left. reflexivity.
      * exact Wack.
      * transitivity (M_e2_acked Bw); [fget Hmw' | exact Me2].
      * left. reflexivity.
      * exact Wsent.
      * transitivity (M_wake_sent Bw); [fget Hmw' | rewrite Mws; exact Lnw].
      * apply Z.le_refl.
      * intros _. rewrite Z.sub_diag. pose proof (a1_wake_timeout _ Hcfg). slia.
      * transitivity (S_last_rx_us W3); [fget Hlw' | rewrite L3; exact Bwn].
      * transitivity (M_last_rx Ba); [fget Hbw | exact Alr].
      * transitivity (S_desk_counter_valid Wl); [fget Fww | exact Wv].
      * transitivity (M_desk_counter_valid Bl); [fget Hlw | exact Lv].
      * left. reflexivity.
      * intros H. discriminate H.
      * intros [H|H]; exfalso; unfold S_WAKING, S_IDLE, S_CLOSED in H; discriminate H.
      * refine (rxe0_fly_wake Ww (fr_src (rxbuf fr n)) (M_host_counter B) (Cfg_sum_mode B) Wfo Wi' Ms Wic Wfk _
                  Wir Wfr _ Wil Wfl Wfc Md _ Wfm Wif).
        -- transitivity (S_host_counter B); [fget Hall | exact (b7_host_counter _ Hst)].
        -- rewrite Wis, Wfs. reflexivity.
        -- fget Hall.
      * intros _. rewrite Wfs. pose proof (a1_ack_timeout _ Hcfg).
        split; [apply Z.le_refl | rewrite Z.sub_diag; slia].
      * rewrite Wfn. left. reflexivity.
      * assert (E : S_personality Ww = S_personality W3) by fget Hlw'. rewrite E.
        destruct P3 as [E3|[E3|E3]]; rewrite E3; [exact (e2_personality _ _ Hmisc) | right; left; reflexivity
          | right; right; reflexivity].
      * exact Xn.
      * transitivity (OW_n Bw); [fget Hmw' | exact Mon].
      * lia.
      * intros i Hi Hi2. destruct (Z.lt_ge_cases i (OW_n B)) as [Hlt | Hge].
        { exact (rxe0_t_below B Ww Hog TG TO' i (conj (proj1 Hi) Hlt) Hi2). }
        assert (Ei : i = OW_n B \/ i = OW_n B + 1) by lia. destruct Ei as [-> | ->].
        -- destruct (Xtk (OW_n B) ltac:(lia)) as (Q1 & Q2 & Q3).
           destruct (TO (OW_n B) ltac:(unfold TRANS_MAX; lia)) as (O1 & O2 & O3).
           destruct (Mtk (OW_n B) ltac:(lia)) as (M1 & M2 & M3).
           rewrite Q1, Q2, Q3, Wt1, Wt2, Wt3, O1, O2, O3, M1, M2, M3, Lt1, Lt2, Lt3.
           exact (conj eq_refl (conj eq_refl eq_refl)).
        -- destruct (TO (OW_n B + 1) ltac:(unfold TRANS_MAX; lia)) as (O1 & O2 & O3).
           rewrite Xt1, Xt2, Xt3, O1, O2, O3, Mt1, Mt2, Mt3. exact (conj eq_refl (conj eq_refl eq_refl)).
      * exact We2.
      * transitivity (OW_e2 Bw); [fget Hmw' | exact Moe].
      * lia.
      * transitivity (GOT_desk W3); [fget Hlw' | exact G3].
      * transitivity (OW_desk Ba); [fget Hbw | exact Aod].
      * lia.
      * fget Hww.
      * fget Hww.
      * fget Hww.
      * fget Hww.
      * transitivity (g_now Bw); [fget HWf | exact Bwn].
      * fget Hww.
      * (* both wakes cleared M.fail / g_fail_next (FT:228, :829); the session is WAKING *)
        intros _. split; [|unfold S_WAKING, S_ONLINE; lia].
        rewrite Wfn. transitivity (M_fail Bw); [fget Hmw' | exact Mfl].
Qed.

(* ---- leaf 0: a body under 33 bytes: the model does nothing (FT:304), the library counts the frame ignored
   (DS:187-189) ---- *)
Lemma rxe0_leaf_short : forall (HL : links) I ops fr n B, rxe0_ctx I ops fr n B ->
  fr_body_len (rxbuf fr n) < 33 -> rxe0_goal I ops fr n B.
Proof.
  intros HL I ops fr n B Cx Hs.
  pose proof Cx as [Hn Ha Hpre Hacc Hcmd].
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  destruct Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (HB : length B = WN) by exact Hlen.
  pose proof (rf_cmd _ _ Hf) as Ecmd.
  pose proof (rf_src_len _ _ Hf) as Hsl.
  unfold rxe0_goal.
  destruct (learn_M_frame B (rxbuf fr n) HB Hsl) as [Hlf Hll].
  destruct (learn_M_desk B (rxbuf fr n) HB Hsl (b2_desk_known01 _ Hst) (ra_known _ _ Hacc)) as [Lk Ld].
  remember (learn_M B (rxbuf fr n)) as Bk eqn:EBk.
  assert (E0 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E0) = true) by (rewrite Hcmd; reflexivity).
  assert (Bl : (fr_body_len (rxbuf fr n) <? SPEC_ANN_MIN) = true) by (apply Z.ltb_lt; unfold SPEC_ANN_MIN; exact Hs).
  assert (F1 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE) = true) by (rewrite Hcmd; reflexivity).
  assert (Ea : ann_code (fr_cmd (rxbuf fr n)) (fr_body_len (rxbuf fr n)) = -4).
  { rewrite Hcmd. unfold ann_code. change (ann_cmd DIGINET_CMD_ANNOUNCE) with true. cbv beta iota delta [negb].
    rewrite (proj2 (Z.ltb_lt _ 33) Hs). reflexivity. }
  remember (set_M_last_rx Bk (g_now B)) as Bm eqn:EBm.
  assert (HBm : length Bm = WN) by (subst Bm; wlen).
  assert (Hkm : wframe (in_rs [(A_M_last_rx, 8)]) Bk Bm) by (subst Bm; wfrs).
  assert (Mst : M_state Bm = M_state B) by (transitivity (M_state Bk); [subst Bm; wget | fget Hlf]).
  assert (Mws : M_wake_sent Bm = M_wake_sent B) by (transitivity (M_wake_sent Bk); [subst Bm; wget | fget Hlf]).
  assert (Mnw : g_now Bm = g_now B) by (transitivity (g_now Bk); [subst Bm; wget | fget Hlf]).
  assert (Mlr : M_last_rx Bm = g_now B) by (subst Bm; wget).
  pose proof (wframe_trans_rs _ _ _ _ _ Hlf Hkm) as Hbm.
  exists Bm. split; [|split; [|split]].
  - unfold m_rx_sw. cbv zeta. rewrite Ecmd, E0, (rf_body_len _ _ Hf), Bl. cbv beta iota delta [orb].
    exact eq_refl.
  - apply (rxe0_tick I ops B Bm Hcore).
    + rewrite Mst, Mws. intros Hw. exact (conj (c1_wake_sent _ _ Htime) (c2_wake _ _ Htime Hw)).
    + exact Mlr.
    + exact Mnw.
    + fget Hbm.
    + fget Hbm.
  - apply (wframe_rs_incl (R_learn ++ [(A_M_last_rx, 8)]) R_mod B Bm); [vm_compute; reflexivity | exact Hbm].
  - intros W HW.
    pose proof HW as (HWf & HWk & HWm & HWl).
    assert (HWn : length W = WN) by (eapply wframe_len; [exact HWf | exact HBm]).
    exists (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1))). split.
    + unfold rx_sw. cbv zeta. rewrite F1. cbv beta iota delta [orb]. unfold on_announce_m. cbv zeta.
      rewrite Ea. change (negb (-4 =? DIGINET_OK)) with true. cbv beta iota. exact eq_refl.
    + remember (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1))) as W' eqn:EW'.
      assert (HW' : wframe (in_rs [(A_S_stats_rx_ignored, 8)]) W W') by (subst W'; wfrs).
      pose proof (wframe_trans_rs _ _ _ _ _ HWf HW') as Hmw.
      pose proof (wframe_trans_rs _ _ _ _ _ Hbm Hmw) as Hall.
      assert (W1 : M_desk_known W' = 1) by (rewrite <- Lk; transitivity (M_desk_known Bm); [fget Hmw | subst Bm; wget]).
      assert (W2 : M_desk W' = fr_src (rxbuf fr n)) by (rewrite <- Ld; transitivity (M_desk Bm); [fget Hmw | subst Bm; wget]).
      assert (W3 : M_last_rx W' = g_now B) by (rewrite <- Mlr; fget Hmw).
      assert (W4 : S_desk_known W' = 1) by (rewrite <- HWk; subst W'; wget).
      assert (W5 : S_desk_mac W' = fr_src (rxbuf fr n)) by (rewrite <- HWm; subst W'; wget).
      assert (W6 : S_last_rx_us W' = g_now B) by (rewrite <- Mnw, <- HWl; subst W'; wget).
      assert (W7 : g_rx W' = g_rx W) by (subst W'; wget).
      assert (W8 : g_rx_len W' = g_rx_len W) by (subst W'; wget).
      assert (W9 : g_rx_times W' = g_rx_times W) by (subst W'; wget).
      assert (W10 : g_rx_fail W' = g_rx_fail W) by (subst W'; wget).
      assert (W11 : g_rx_send W' = g_rx_send W) by (subst W'; wget).
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
        - intros _. rewrite Z.sub_diag. pose proof (a1_offline _ Hcfg). slia.
        - exact (c2_fly _ _ Htime). }
      assert (Hmi' : agree_misc I W').
      { constructor; rw_eqs W'; [exact (e1_fail_next _ _ Hmisc) | exact (e2_personality _ _ Hmisc)]. }
      constructor; [constructor | | |].
      * apply (agree_core_rx I ops B W' Hcore); [| exact Hst' | exact Hfl' | exact Hti' | exact Hmi'].
        eapply wframe_rx; [| exact Hall]. vm_compute. reflexivity.
      * (* neither side writes OW or GOT *)
        apply (ow_got_eq_fr _ B W' Hall); [vm_compute; reflexivity | exact (wr_og _ Hroom)].
      * exact W7.
      * exact W8.
      * exact W9.
      * exact W10.
      * rewrite U39, <- Mnw. symmetry. fget HWf.
      * apply (ow_step_fr _ B B W' Hall); [vm_compute; reflexivity | apply ow_step_refl].
      * exact W11.
      * (* a short body cannot wake *)
        unfold rx_wake_buf. intros [_ Hw]. exfalso. exact (Z.lt_irrefl _ (Z.lt_le_trans _ _ _ Hs Hw)).
Qed.

(* ---- the branch, any reception of the operation ---- *)
Lemma rx_e0_g : forall (HL : links), rx_branch_g cond_e0.
Proof.
  intros HL. unfold rx_branch_g. intros I ops fr n B. cbv zeta. intros Hn Ha Hpre Hacc Hc.
  pose proof (Build_rxe0_ctx I ops fr n B Hn Ha Hpre Hacc Hc) as Cx.
  change (rxe0_goal I ops fr n B).
  pose proof Hpre as [Hcore _ _ _ _]. pose proof Hcore as [_ _ Hcfg _ Hst _ _ _ Hmisc].
  destruct (Z.ltb_spec (fr_body_len (rxbuf fr n)) 33) as [Hs|Hl].
  { exact (rxe0_leaf_short HL I ops fr n B Cx Hs). }
  destruct (Z.eq_dec (M_state B) S_ONLINE) as [Hon|Hon].
  - destruct (a1_auto_wake _ Hcfg) as [Aw|Aw].
    + exact (rxe0_leaf_lost HL I ops fr n B Cx Hl Hon Aw).
    + destruct (e1_fail_next _ _ Hmisc) as [F|F].
      * exact (rxe0_leaf_on_ok HL I ops fr n B Cx Hl Hon Aw F).
      * exact (rxe0_leaf_on_fail HL I ops fr n B Cx Hl Hon Aw F).
  - destruct (Z.eq_dec (M_state B) S_IDLE) as [Hid|Hid].
    + destruct (a1_auto_wake _ Hcfg) as [Aw|Aw].
      * apply (rxe0_leaf_noact HL I ops fr n B Cx Hl Hon).
        rewrite Aw, rxe0_truth0. apply Bool.andb_false_r.
      * destruct (e1_fail_next _ _ Hmisc) as [F|F].
        -- exact (rxe0_leaf_idle_ok HL I ops fr n B Cx Hl Hid Aw F).
        -- exact (rxe0_leaf_idle_fail HL I ops fr n B Cx Hl Hid Aw F).
    + apply (rxe0_leaf_noact HL I ops fr n B Cx Hl Hon).
      rewrite (proj2 (Z.eqb_neq _ _) Hid). apply Bool.andb_false_l.
Qed.

(* the first reception of an operation (rx_pre) *)
Lemma rx_e0 : forall (HL : links), rx_branch cond_e0.
Proof. intros HL. exact (rx_branch_of_g cond_e0 (rx_e0_g HL)). Qed.
