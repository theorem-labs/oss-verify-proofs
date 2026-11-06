(* A frame from the desk whose command is e1 (DIGINET_CMD_ANNOUNCE_SESSION): m_rx (FT:303-330) and the
   library's on_announce (DS:184-221). The desk may have been learnt by both (FT:296-297, DS:290-291). A body
   under 33 bytes: the model does nothing (FT:305-306), the library counts the frame ignored (DS:187-189). Else
   both name the desk (OW.desk FT:308-311; N_DESK DS:196-198, which check_state_desk FT:527-557 checks) and look
   for this host's MAC in the announce's unknown field (host_offset FT:256-262, find_mac DS:168-174: the same
   offset). Found (FT:319-322, DS:209-214): both clear foreign, set e1 and go ONLINE when WAKING with the wake
   acked (m_maybe_online FT:237-243, maybe_online DS:176-182). Not found (FT:324-328, DS:215-220): both set
   foreign (OW.foreign; N_FOREIGN FT:967-968) and lose a live session (R_FOREIGN). The reception may follow
   another of the same operation (rx_pre_g, RxBase.v): OW and GOT then agree but need not be zero, the counts go up
   from their values (OW.desk FT:308, OW.foreign FT:326, GOT.desk FT:960, GOT.foreign FT:968) and a transition lands
   at OW.t[OW.n] (m_set FT:200-206) and GOT.t[GOT.n] (notice FT:942-947), the same index on both sides. *)
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

Local Notation "'let*' p ':=' c1 'in' c2" := (match c1 with Some p => c2 | None => None end)
  (at level 200, p pattern, c1 at level 200, c2 at level 200).

Definition cond_e1 (B buf : list byte) : Prop := fr_cmd buf = DIGINET_CMD_ANNOUNCE_SESSION.

(* a read that wget must close *)
Ltac wg := solve [wget].

(* `G Y i = G X i` for a getter G of a transition log, OW.t or GOT.t (TRANS_MAX entries of 12 bytes), given
   H : wframe (in_rs rs) X Y with rs a closed list that misses that log, and 0 <= i < TRANS_MAX in the context
   (only the log getters unfold, so that an index such as OW_n B stays the term the context bounds) *)
Ltac tget H := unfold OW_t_state, OW_t_old, OW_t_reason, GOT_t_state, GOT_t_old, GOT_t_reason;
  lazymatch goal with |- s32_at _ _ = s32_at _ _ => apply (fr_s _ _ _ _ H) end;
  [ wunf_off; slia
  | first [ apply (disj_rs_sub (A_OW_t_state 0) 192); [vm_compute; reflexivity | wunf_off; slia | wunf_off; slia]
          | apply (disj_rs_sub (A_GOT_t_state 0) 192); [vm_compute; reflexivity | wunf_off; slia | wunf_off; slia] ] ].

(* k in 0 .. 4, i in 0 .. 3 (the context bounds them): the concrete indices the write tactics need (wfrs and
   wnum decide offsets on closed numbers) *)
Ltac ann1_k5 k := let E := fresh in assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia;
  destruct E as [-> | [-> | [-> | [-> | ->]]]].
Ltac ann1_i4 i := let E := fresh in assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia;
  destruct E as [-> | [-> | [-> | ->]]].

(* ---- closed facts ---- *)

(* x + 1 in int (int_inc) for a count far below INT_MAX *)
Lemma ann1_int_inc : forall x, 0 <= x <= 16 -> int_inc x = Some (x + 1).
Proof. intros x Hx. unfold int_inc. rewrite (proj2 (Z.eqb_neq x INT_MAX)) by (unfold INT_MAX; lia). reflexivity. Qed.

(* what ow_room (RxBase.v) gives the counts an e1 moves *)
Lemma ann1_room : forall B, ow_room B ->
  0 <= OW_n B <= 4 /\ 0 <= OW_desk B <= 1 /\ 0 <= OW_foreign B <= 1 /\
  GOT_n B = OW_n B /\ GOT_desk B = OW_desk B /\ GOT_foreign B = OW_foreign B.
Proof.
  intros B Hr. pose proof (wr_og _ Hr) as Hog.
  pose proof (og_n_range _ Hog). pose proof (og_desk_range _ Hog). pose proof (og_foreign_range _ Hog).
  pose proof (wr_n _ Hr). pose proof (wr_desk _ Hr). pose proof (wr_foreign _ Hr).
  pose proof (og_n _ Hog). pose proof (og_desk _ Hog). pose proof (og_foreign _ Hog).
  lia.
Qed.

(* an e1 is not the frame whose reception can wake (rx_wake_buf, RxBase.v) *)
Lemma ann1_nowake : forall buf, fr_cmd buf = DIGINET_CMD_ANNOUNCE_SESSION -> ~ rx_wake_buf buf.
Proof. intros buf Hc [Hw _]. rewrite Hc in Hw. vm_compute in Hw. discriminate Hw. Qed.

Lemma ann1_ow : S_ONLINE <> S_WAKING.
Proof. unfold S_ONLINE, S_WAKING. discriminate. Qed.
Lemma ann1_oi : S_ONLINE <> S_IDLE.
Proof. unfold S_ONLINE, S_IDLE. discriminate. Qed.
Lemma ann1_oc : S_ONLINE <> S_CLOSED.
Proof. unfold S_ONLINE, S_CLOSED. discriminate. Qed.
Lemma ann1_iw : S_IDLE <> S_WAKING.
Proof. unfold S_IDLE, S_WAKING. discriminate. Qed.
Lemma ann1_io : S_IDLE <> S_ONLINE.
Proof. unfold S_IDLE, S_ONLINE. discriminate. Qed.

(* ---- find_mac (DS:168-174) answers -1 or an offset below 10 ---- *)

Lemma ann1_find_mac_loop_range : forall u mac fuel i, 0 <= i ->
  -1 <= find_mac_loop u mac i fuel < i + Z.of_nat fuel + 1.
Proof.
  intros u mac fuel. induction fuel as [|f IH]; intros i Hi; cbn [find_mac_loop].
  - lia.
  - destruct (memeq _ _ _); [lia|]. specialize (IH (i + 1) ltac:(lia)). lia.
Qed.

Lemma ann1_find_mac_range : forall u mac, -1 <= find_mac_m u 15 mac < 11.
Proof.
  intros u mac. unfold find_mac_m. change (Z.to_nat (15 - DIGINET_MAC_LEN + 1)) with 10%nat.
  pose proof (ann1_find_mac_loop_range u mac 10 0 (Z.le_refl 0)) as H. lia.
Qed.

(* desk_named (FT:265-273) answers one of the image's two desks or NULL, all 8-byte pointers *)
Lemma ann1_dn_range : forall I X r dp, timg_ok I -> desk_named_m I X r = Some (X, dp) -> 0 <= dp < 2 ^ 64.
Proof.
  intros I X r dp HI. pose proof (ti_spec_c24_ok I HI) as H1. pose proof (ti_spec_pc_ok I HI) as H2.
  unfold desk_named_m. cbv zeta.
  destruct (list_strz_len _) as [k|]; [|intros H; discriminate H].
  destruct (_ && _); [|destruct (_ && _)]; cbv beta iota; intros H; inversion H; subst; lia.
Qed.

(* ---- the worlds the two sides write ---- *)

(* the model at FT:308-311: OW.desk d (OW.desk + 1), desk_off, desk_p, desk_body *)
Definition ann1_mA (B2 : list byte) (d off dp a : Z) : list byte :=
  set_OW_desk_body (set_OW_desk_p (set_OW_desk_off (set_OW_desk B2 d) off) dp) (a + 30).
Definition ann1_RA : list (Z * Z) := [(A_OW_desk, 4); (A_OW_desk_off, 4); (A_OW_desk_p, 8); (A_OW_desk_body, 8)].

Lemma ann1_mA_get : forall B2 d off dp a, length B2 = WN -> 0 <= d <= 2 -> -1 <= off < 11 -> 0 <= dp < 2 ^ 64 ->
  0 <= a + 30 < 2 ^ 64 ->
  length (ann1_mA B2 d off dp a) = WN /\ wframe (in_rs ann1_RA) B2 (ann1_mA B2 d off dp a) /\
  OW_desk (ann1_mA B2 d off dp a) = d /\ OW_desk_off (ann1_mA B2 d off dp a) = off /\
  OW_desk_p (ann1_mA B2 d off dp a) = dp /\ OW_desk_body (ann1_mA B2 d off dp a) = a + 30.
Proof.
  intros B2 d off dp a HB Hd Ho Hdp Ha. unfold ann1_mA, ann1_RA.
  split; [wlen|]. split; [wfrs|]. split; [wg|]. split; [wg|]. split; [wg|]. wg.
Qed.

(* the model at FT:320-321: foreign 0, e1_us 1 *)
Definition ann1_mU (B4 : list byte) : list byte := set_M_e1_us (set_M_foreign B4 0) 1.
Definition ann1_RU : list (Z * Z) := [(A_M_foreign, 4); (A_M_e1_us, 4)].

Lemma ann1_mU_get : forall B4, length B4 = WN ->
  length (ann1_mU B4) = WN /\ wframe (in_rs ann1_RU) B4 (ann1_mU B4) /\
  M_foreign (ann1_mU B4) = 0 /\ M_e1_us (ann1_mU B4) = 1.
Proof.
  intros B4 HB. unfold ann1_mU, ann1_RU. split; [wlen|]. split; [wfrs|]. split; [wg|]. wg.
Qed.

(* m_maybe_online (FT:239-241) going ONLINE from WAKING, the transition at OW.t[k], k = OW.n (m_set FT:200-206).
   The range list names the whole log OW.t, so that it stays closed for every k *)
Definition ann1_mON (X : list byte) (v k : Z) : list byte :=
  set_M_state (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state
    (set_M_next_ka X v) k S_ONLINE) k S_WAKING) k R_ONLINE) (k + 1)) S_ONLINE.
Definition ann1_RON : list (Z * Z) := [(A_M_next_ka, 8); (A_OW_t_state 0, 192); (A_OW_n, 4); (A_M_state, 4)].

Lemma ann1_mON_get : forall X v k, length X = WN -> 0 <= v < 2 ^ 64 -> 0 <= k <= 4 ->
  length (ann1_mON X v k) = WN /\ wframe (in_rs ann1_RON) X (ann1_mON X v k) /\
  M_state (ann1_mON X v k) = S_ONLINE /\ M_next_ka (ann1_mON X v k) = v /\ OW_n (ann1_mON X v k) = k + 1 /\
  OW_t_state (ann1_mON X v k) k = S_ONLINE /\ OW_t_old (ann1_mON X v k) k = S_WAKING /\
  OW_t_reason (ann1_mON X v k) k = R_ONLINE /\
  (forall i, 0 <= i < k -> OW_t_state (ann1_mON X v k) i = OW_t_state X i /\
     OW_t_old (ann1_mON X v k) i = OW_t_old X i /\ OW_t_reason (ann1_mON X v k) i = OW_t_reason X i).
Proof.
  intros X v k HX Hv Hk. unfold ann1_mON, ann1_RON, S_ONLINE, S_WAKING, R_ONLINE. ann1_k5 k.
  all: split; [wlen|]; split; [wfrs|]; split; [wg|]; split; [wg|]; split; [wg|]; split; [wg|]; split; [wg|];
    split; [wg|].
  all: intros i Hi; ann1_i4 i; first [exfalso; lia | split; [wg|]; split; [wg|]; wg].
Qed.

(* the model at FT:325-326: foreign 1, OW.foreign f (OW.foreign + 1) *)
Definition ann1_mF (B4 : list byte) (f : Z) : list byte := set_OW_foreign (set_M_foreign B4 1) f.
Definition ann1_RF : list (Z * Z) := [(A_M_foreign, 4); (A_OW_foreign, 4)].

Lemma ann1_mF_get : forall B4 f, length B4 = WN -> 0 <= f <= 2 ->
  length (ann1_mF B4 f) = WN /\ wframe (in_rs ann1_RF) B4 (ann1_mF B4 f) /\
  M_foreign (ann1_mF B4 f) = 1 /\ OW_foreign (ann1_mF B4 f) = f.
Proof.
  intros B4 f HB Hf. unfold ann1_mF, ann1_RF. split; [wlen|]. split; [wfrs|]. split; [wg|]. wg.
Qed.

(* m_lost (FT:210-215) with R_FOREIGN from a live state, the transition at OW.t[k], k = OW.n *)
Definition ann1_mL (X : list byte) (old k : Z) : list byte :=
  set_M_state (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state
    (set_M_desk_counter_valid (set_M_fly_on X 0) 0) k S_IDLE) k old) k R_FOREIGN) (k + 1)) S_IDLE.
Definition ann1_RL : list (Z * Z) :=
  [(A_M_fly_on, 4); (A_M_desk_counter_valid, 4); (A_OW_t_state 0, 192); (A_OW_n, 4); (A_M_state, 4)].

Lemma ann1_mL_get : forall X old k, length X = WN -> - 2 ^ 31 <= old < 2 ^ 31 -> 0 <= k <= 4 ->
  length (ann1_mL X old k) = WN /\ wframe (in_rs ann1_RL) X (ann1_mL X old k) /\
  M_state (ann1_mL X old k) = S_IDLE /\ M_fly_on (ann1_mL X old k) = 0 /\
  M_desk_counter_valid (ann1_mL X old k) = 0 /\ OW_n (ann1_mL X old k) = k + 1 /\
  OW_t_state (ann1_mL X old k) k = S_IDLE /\ OW_t_old (ann1_mL X old k) k = old /\
  OW_t_reason (ann1_mL X old k) k = R_FOREIGN /\
  (forall i, 0 <= i < k -> OW_t_state (ann1_mL X old k) i = OW_t_state X i /\
     OW_t_old (ann1_mL X old k) i = OW_t_old X i /\ OW_t_reason (ann1_mL X old k) i = OW_t_reason X i).
Proof.
  intros X old k HX Ho Hk. unfold ann1_mL, ann1_RL, S_IDLE, R_FOREIGN. ann1_k5 k.
  all: split; [wlen|]; split; [wfrs|]; split; [wg|]; split; [wg|]; split; [wg|]; split; [wg|]; split; [wg|];
    split; [wg|]; split; [wg|].
  all: intros i Hi; ann1_i4 i; first [exfalso; lia | split; [wg|]; split; [wg|]; wg].
Qed.

(* the library at DS:211-212: foreign 0, e1_named_us 1 *)
Definition ann1_lU (W2 : list byte) : list byte := set_S_e1_named_us (set_S_foreign W2 0) 1.
Definition ann1_RLU : list (Z * Z) := [(A_S_foreign, 4); (A_S_e1_named_us, 4)].

Lemma ann1_lU_get : forall W2, length W2 = WN ->
  length (ann1_lU W2) = WN /\ wframe (in_rs ann1_RLU) W2 (ann1_lU W2) /\
  S_foreign (ann1_lU W2) = 0 /\ S_e1_named_us (ann1_lU W2) = 1.
Proof.
  intros W2 HW. unfold ann1_lU, ann1_RLU. split; [wlen|]. split; [wfrs|]. split; [wg|]. wg.
Qed.

(* maybe_online (DS:179-180) going ONLINE from WAKING, its N_STATE notice logged in GOT.t[k], k = GOT.n
   (FT:942-947); the range list names the whole log GOT.t *)
Definition ann1_lON (Y : list byte) (v k : Z) : list byte :=
  set_GOT_n (set_GOT_t_reason (set_GOT_t_old (set_GOT_t_state (set_S_state (set_S_next_keepalive_us Y v)
    DIGINET_S_ONLINE) k DIGINET_S_ONLINE) k DIGINET_S_WAKING) k DIGINET_R_ONLINE) (k + 1).
Definition ann1_RLON : list (Z * Z) :=
  [(A_S_next_keepalive_us, 8); (A_S_state, 4); (A_GOT_t_state 0, 192); (A_GOT_n, 4)].

Lemma ann1_lON_get : forall Y v k, length Y = WN -> 0 <= v < 2 ^ 64 -> 0 <= k <= 4 ->
  length (ann1_lON Y v k) = WN /\ wframe (in_rs ann1_RLON) Y (ann1_lON Y v k) /\
  S_state (ann1_lON Y v k) = DIGINET_S_ONLINE /\ S_next_keepalive_us (ann1_lON Y v k) = v /\
  GOT_n (ann1_lON Y v k) = k + 1 /\ GOT_t_state (ann1_lON Y v k) k = DIGINET_S_ONLINE /\
  GOT_t_old (ann1_lON Y v k) k = DIGINET_S_WAKING /\ GOT_t_reason (ann1_lON Y v k) k = DIGINET_R_ONLINE /\
  (forall i, 0 <= i < k -> GOT_t_state (ann1_lON Y v k) i = GOT_t_state Y i /\
     GOT_t_old (ann1_lON Y v k) i = GOT_t_old Y i /\ GOT_t_reason (ann1_lON Y v k) i = GOT_t_reason Y i).
Proof.
  intros Y v k HY Hv Hk. unfold ann1_lON, ann1_RLON, DIGINET_S_ONLINE, DIGINET_S_WAKING, DIGINET_R_ONLINE.
  ann1_k5 k.
  all: split; [wlen|]; split; [wfrs|]; split; [wg|]; split; [wg|]; split; [wg|]; split; [wg|]; split; [wg|];
    split; [wg|].
  all: intros i Hi; ann1_i4 i; first [exfalso; lia | split; [wg|]; split; [wg|]; wg].
Qed.

(* the library at DS:216-218: foreign 1, the N_FOREIGN notice counted in GOT.foreign, f = GOT.foreign + 1
   (FT:968) *)
Definition ann1_lF (W2 : list byte) (f : Z) : list byte := set_GOT_foreign (set_S_foreign W2 1) f.
Definition ann1_RLF : list (Z * Z) := [(A_S_foreign, 4); (A_GOT_foreign, 4)].

Lemma ann1_lF_get : forall W2 f, length W2 = WN -> 0 <= f <= 2 ->
  length (ann1_lF W2 f) = WN /\ wframe (in_rs ann1_RLF) W2 (ann1_lF W2 f) /\
  S_foreign (ann1_lF W2 f) = 1 /\ GOT_foreign (ann1_lF W2 f) = f.
Proof.
  intros W2 f HW Hf. unfold ann1_lF, ann1_RLF. split; [wlen|]. split; [wfrs|]. split; [wg|]. wg.
Qed.

(* session_lost (DS:160-165) with R_FOREIGN from a live state, its N_STATE notice logged in GOT.t[k], k = GOT.n *)
Definition ann1_lL (Y : list byte) (old k : Z) : list byte :=
  set_GOT_n (set_GOT_t_reason (set_GOT_t_old (set_GOT_t_state
    (set_S_state (set_S_desk_counter_valid (set_S_inflight Y 0) 0) DIGINET_S_IDLE)
    k DIGINET_S_IDLE) k old) k DIGINET_R_FOREIGN) (k + 1).
Definition ann1_RLL : list (Z * Z) :=
  [(A_S_inflight, 4); (A_S_desk_counter_valid, 4); (A_S_state, 4); (A_GOT_t_state 0, 192); (A_GOT_n, 4)].

Lemma ann1_lL_get : forall Y old k, length Y = WN -> - 2 ^ 31 <= old < 2 ^ 31 -> 0 <= k <= 4 ->
  length (ann1_lL Y old k) = WN /\ wframe (in_rs ann1_RLL) Y (ann1_lL Y old k) /\
  S_state (ann1_lL Y old k) = DIGINET_S_IDLE /\ S_inflight (ann1_lL Y old k) = 0 /\
  S_desk_counter_valid (ann1_lL Y old k) = 0 /\ GOT_n (ann1_lL Y old k) = k + 1 /\
  GOT_t_state (ann1_lL Y old k) k = DIGINET_S_IDLE /\ GOT_t_old (ann1_lL Y old k) k = old /\
  GOT_t_reason (ann1_lL Y old k) k = DIGINET_R_FOREIGN /\
  (forall i, 0 <= i < k -> GOT_t_state (ann1_lL Y old k) i = GOT_t_state Y i /\
     GOT_t_old (ann1_lL Y old k) i = GOT_t_old Y i /\ GOT_t_reason (ann1_lL Y old k) i = GOT_t_reason Y i).
Proof.
  intros Y old k HY Ho Hk. unfold ann1_lL, ann1_RLL, DIGINET_S_IDLE, DIGINET_R_FOREIGN. ann1_k5 k.
  all: split; [wlen|]; split; [wfrs|]; split; [wg|]; split; [wg|]; split; [wg|]; split; [wg|]; split; [wg|];
    split; [wg|]; split; [wg|].
  all: intros i Hi; ann1_i4 i; first [exfalso; lia | split; [wg|]; split; [wg|]; wg].
Qed.

(* ---- the model's steps (TCb m_maybe_online_m, m_lost_m) ---- *)

(* FT:239-241: WAKING, e2 acked, e1 named: ONLINE, the transition at OW.t[k], k = OW.n *)
Lemma ann1_m_online : forall X v k, length X = WN -> M_state X = S_WAKING -> M_e2_acked X = 1 -> M_e1_us X = 1 ->
  OW_n X = k -> 0 <= k <= 4 -> u64 (M_last_rx X + h_ms_m (Cfg_keepalive_ms X)) = v ->
  m_maybe_online_m X = Some (ann1_mON X v k, tt).
Proof.
  intros X v k HX Hs He2 He1 Hn Hk Hv.
  unfold m_maybe_online_m. rewrite Hs, He2, He1.
  change ((S_WAKING =? S_WAKING) && truth 1 && truth 1) with true.
  cbv beta iota zeta. rewrite Hv.
  unfold m_set_m. cbv zeta.
  assert (G7 : M_state (set_M_next_ka X v) = S_WAKING) by (transitivity (M_state X); [wget | exact Hs]).
  assert (G8 : OW_n (set_M_next_ka X v) = k) by (transitivity (OW_n X); [wget | exact Hn]).
  rewrite G7, G8.
  change (S_WAKING =? S_ONLINE) with false.
  rewrite (proj2 (Z.ltb_lt k TRANS_MAX)) by (unfold TRANS_MAX; lia).
  rewrite (proj2 (Z.ltb_ge k 0)) by lia.
  rewrite (ann1_int_inc k) by lia.
  cbv beta iota. unfold ann1_mON. reflexivity.
Qed.

(* FT:239 false: nothing more *)
Lemma ann1_m_stay : forall X, (M_state X <> S_WAKING \/ M_e2_acked X = 0) -> m_maybe_online_m X = Some (X, tt).
Proof.
  intros X H. unfold m_maybe_online_m. destruct H as [H|H].
  - rewrite (proj2 (Z.eqb_neq _ _) H). cbv beta iota delta [andb]. reflexivity.
  - rewrite H. change (truth 0) with false.
    rewrite (andb_false_r (M_state X =? S_WAKING)). cbv beta iota delta [andb]. reflexivity.
Qed.

(* FT:210-215 with R_FOREIGN from a live state, the transition at OW.t[k], k = OW.n *)
Lemma ann1_m_lost : forall X old k, length X = WN -> OW_n X = k -> 0 <= k <= 4 -> M_state X <> S_IDLE ->
  M_state X = old -> m_lost_m X R_FOREIGN = Some (ann1_mL X old k, tt).
Proof.
  intros X old k HX Hn Hk Hs Ho. unfold m_lost_m, m_set_m. cbv zeta.
  assert (E1 : M_state (set_M_desk_counter_valid (set_M_fly_on X 0) 0) = old)
    by (transitivity (M_state X); [wget | exact Ho]).
  assert (E2 : OW_n (set_M_desk_counter_valid (set_M_fly_on X 0) 0) = k)
    by (transitivity (OW_n X); [wget | exact Hn]).
  assert (E3 : (old =? S_IDLE) = false) by (rewrite <- Ho; apply Z.eqb_neq; exact Hs).
  rewrite E1, E2, E3.
  rewrite (proj2 (Z.ltb_lt k TRANS_MAX)) by (unfold TRANS_MAX; lia).
  rewrite (proj2 (Z.ltb_ge k 0)) by lia.
  rewrite (ann1_int_inc k) by lia.
  unfold ann1_mL. reflexivity.
Qed.

(* ---- the library's steps (TSess maybe_online_m, session_lost_m; TCb notice_m) ---- *)

(* DS:178-180 from WAKING with the wake acked and the e1 named: ONLINE, the N_STATE notice (FT:941-949) logged
   at GOT.t[k], k = GOT.n *)
Lemma ann1_l_online : forall I F Y v k, length Y = WN -> S_state Y = DIGINET_S_WAKING -> S_wake_acked Y = 1 ->
  S_e1_named_us Y = 1 -> S_notify Y = ti_notice I -> GOT_n Y = k -> 0 <= k <= 4 -> M_e2_acked Y = 1 ->
  M_e1_us Y = 1 -> 0 <= v < 2 ^ 64 -> u64 (S_last_rx_us Y + ms_m (S_cfg_keepalive_ms Y)) = v ->
  maybe_online_m I F Y = Some (ann1_lON Y v k, tt).
Proof.
  intros I F Y v k HY Hs Hw He Hno Hg Hk Hm2 Hm1 Hvr Hv.
  destruct (ann1_lON_get Y v k HY Hvr Hk) as (_ & Hf & _).
  unfold maybe_online_m. rewrite Hs, Hw, He.
  change ((DIGINET_S_WAKING =? DIGINET_S_WAKING) && negb (1 =? 0) && negb (1 =? 0)) with true.
  cbv beta iota zeta. rewrite Hv.
  unfold set_state_m.
  assert (H4s : S_state (set_S_next_keepalive_us Y v) = DIGINET_S_WAKING)
    by (transitivity (S_state Y); [wget | exact Hs]).
  rewrite H4s. change (DIGINET_S_WAKING =? DIGINET_S_ONLINE) with false. cbv beta iota zeta.
  unfold call_notify.
  assert (H4n : S_notify (set_S_state (set_S_next_keepalive_us Y v) DIGINET_S_ONLINE) = ti_notice I)
    by (transitivity (S_notify Y); [wget | exact Hno]).
  rewrite H4n, (Z.eqb_refl (ti_notice I)). cbv beta iota.
  unfold notice_m. cbv beta zeta. cbn [n_kind n_state n_old n_reason].
  change (DIGINET_N_STATE =? N_STATE) with true. cbv beta iota zeta.
  assert (H4g : GOT_n (set_S_state (set_S_next_keepalive_us Y v) DIGINET_S_ONLINE) = k)
    by (transitivity (GOT_n Y); [wget | exact Hg]).
  rewrite H4g.
  rewrite (proj2 (Z.ltb_lt k TRANS_MAX)) by (unfold TRANS_MAX; lia).
  rewrite (proj2 (Z.ltb_ge k 0)) by lia.
  rewrite (ann1_int_inc k) by lia.
  change (DIGINET_S_ONLINE =? S_ONLINE) with true.
  cbv beta iota.
  assert (HO1 : M_e2_acked (ann1_lON Y v k) = 1) by (transitivity (M_e2_acked Y); [fget Hf | exact Hm2]).
  assert (HO2 : M_e1_us (ann1_lON Y v k) = 1) by (transitivity (M_e1_us Y); [fget Hf | exact Hm1]).
  unfold ann1_lON in HO1, HO2.
  rewrite (check_state_online_ok _ HO1 HO2). unfold ann1_lON. reflexivity.
Qed.

(* DS:178 false: nothing more *)
Lemma ann1_l_stay : forall I F Y, (S_state Y <> DIGINET_S_WAKING \/ S_wake_acked Y = 0) ->
  maybe_online_m I F Y = Some (Y, tt).
Proof.
  intros I F Y H. unfold maybe_online_m. destruct H as [H|H].
  - rewrite (proj2 (Z.eqb_neq _ _) H). cbv beta iota delta [andb]. reflexivity.
  - rewrite H. change (negb (0 =? 0)) with false.
    rewrite (andb_false_r (S_state Y =? DIGINET_S_WAKING)). cbv beta iota delta [andb]. reflexivity.
Qed.

(* DS:160-165 with R_FOREIGN from a live state: set_state IDLE, its N_STATE notice (FT:941-949) at GOT.t[k] *)
Lemma ann1_l_lost : forall I F Y old k, length Y = WN -> S_notify Y = ti_notice I -> GOT_n Y = k -> 0 <= k <= 4 ->
  S_state Y <> DIGINET_S_IDLE -> S_state Y = old ->
  session_lost_m I F Y DIGINET_R_FOREIGN = Some (ann1_lL Y old k, tt).
Proof.
  intros I F Y old k HY Hno Hg Hk Hs Ho. unfold session_lost_m, set_state_m, call_notify, notice_m. cbv zeta.
  assert (E1 : S_state (set_S_desk_counter_valid (set_S_inflight Y 0) 0) = old)
    by (transitivity (S_state Y); [wget | exact Ho]).
  assert (E2 : (old =? DIGINET_S_IDLE) = false) by (rewrite <- Ho; apply Z.eqb_neq; exact Hs).
  assert (E3 : S_notify (set_S_state (set_S_desk_counter_valid (set_S_inflight Y 0) 0) DIGINET_S_IDLE)
                 = ti_notice I) by (transitivity (S_notify Y); [wget | exact Hno]).
  assert (E4 : GOT_n (set_S_state (set_S_desk_counter_valid (set_S_inflight Y 0) 0) DIGINET_S_IDLE) = k)
    by (transitivity (GOT_n Y); [wget | exact Hg]).
  rewrite E1, E2, E3, (Z.eqb_refl (ti_notice I)), E4.
  rewrite (proj2 (Z.ltb_lt k TRANS_MAX)) by (unfold TRANS_MAX; lia).
  rewrite (proj2 (Z.ltb_ge k 0)) by lia.
  rewrite (ann1_int_inc k) by lia.
  unfold ann1_lL. reflexivity.
Qed.

(* notice (FT:959-961) of an N_DESK notice: GOT.desk + 1 *)
Lemma ann1_notice_desk : forall I F X n g, n_kind n = DIGINET_N_DESK -> GOT_desk X = g -> 0 <= g <= 1 ->
  notice_m I F X n = check_state_desk_m I F (set_GOT_desk X (g + 1)) n.
Proof.
  intros I F X n g Hk Hg Hr. unfold notice_m. cbv zeta. rewrite Hk.
  change (DIGINET_N_DESK =? N_STATE) with false. change (DIGINET_N_DESK =? N_ACKED) with false.
  change (DIGINET_N_DESK =? N_ACK_LOST) with false. change (DIGINET_N_DESK =? N_DESK) with true.
  cbv beta iota. rewrite Hg, (ann1_int_inc g) by lia. cbv beta iota. exact eq_refl.
Qed.

(* ---- desk_named (FT:265-273) on the body: one answer for every world ---- *)

Lemma ann1_dn_some : forall I X r dp, option_map snd (desk_named_m I X r) = Some dp ->
  desk_named_m I X r = Some (X, dp).
Proof.
  intros I X r dp. unfold desk_named_m. cbv zeta.
  destruct (list_strz_len _) as [k|]; [|cbn; intros H; discriminate H].
  destruct (_ && _); [|destruct (_ && _)]; cbn; intros H; injection H as <-; reflexivity.
Qed.

Lemma ann1_named : forall (HL : links) I fr n, timg_ok I -> 0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  rx_frame_facts fr n -> 33 <= fr_body_len (rxbuf fr n) ->
  exists dp, (forall X, option_map snd (desk_named_m I X (skipn 30 (tf_bytes fr))) = Some dp) /\ 0 <= dp < 2 ^ 64.
Proof.
  intros HL I fr n HI Hn Hf Hbl.
  pose proof (rf_blen _ _ Hf) as Hb.
  assert (Lr : SPEC_ANN_MIN <= Z.of_nat (length (skipn 30 (tf_bytes fr))))
    by (rewrite length_skipn; unfold SPEC_ANN_MIN; lia).
  pose proof HL as (_ & _ & _ & _ & HL5 & _).
  pose proof (HL5 I [] (skipn 30 (tf_bytes fr)) Lr) as H5.
  cbv zeta in H5. destruct H5 as (dp & Hdn & _).
  exists dp. split.
  - intros X.
    assert (L33 : (33 <= length (skipn 30 (tf_bytes fr)))%nat) by (unfold SPEC_ANN_MIN in Lr; lia).
    rewrite (desk_named_prefix I X [] _ _ L33 L33 eq_refl). rewrite Hdn. reflexivity.
  - exact (ann1_dn_range I [] _ dp HI Hdn).
Qed.

(* ---- the prefix of the e1 branch on both sides ---- *)

(* m_rx (FT:319-328) after the desk is named: the model's tail of the e1 branch *)
Definition ann1_mtail (B4 : list byte) (off : Z) : option (list byte * unit) :=
  if 0 <=? off then m_maybe_online_m (ann1_mU B4)
  else
    let* fo := int_inc (OW_foreign (set_M_foreign B4 1)) in
    if (M_state (set_OW_foreign (set_M_foreign B4 1) fo) =? S_ONLINE) ||
       (M_state (set_OW_foreign (set_M_foreign B4 1) fo) =? S_WAKING)
    then m_lost_m (set_OW_foreign (set_M_foreign B4 1) fo) R_FOREIGN
    else Some (set_OW_foreign (set_M_foreign B4 1) fo, tt).

Lemma ann1_m_prefix : forall (HL : links) I fr n B2 dp off d0, 0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  fr_code (rxbuf fr n) = DIGINET_OK -> fr_cmd (rxbuf fr n) = DIGINET_CMD_ANNOUNCE_SESSION ->
  33 <= fr_body_len (rxbuf fr n) -> OW_desk B2 = d0 -> 0 <= d0 <= 1 ->
  (forall X, option_map snd (desk_named_m I X (skipn 30 (tf_bytes fr))) = Some dp) ->
  off = find_mac_m (ann_unknown (fr_body (rxbuf fr n))) 15 HOST ->
  m_rx_sw I fr n B2 = ann1_mtail (ann1_mA B2 (d0 + 1) off dp (tf_addr fr)) off.
Proof.
  intros HL I fr n B2 dp off d0 Hn Hc Hcmd Hbl Hd Hd0 Hdn Eoff.
  pose proof (rx_frame_ok HL fr n Hn Hc) as Hf.
  pose proof (rf_blen _ _ Hf) as Hb. pose proof (rf_body_length _ _ Hf) as Lb.
  pose proof (rf_body_bytes _ _ Hf) as Eb.
  assert (Hho : host_offset_loop 10 (skipn 30 (tf_bytes fr)) 0 = Some off).
  { rewrite Eoff. apply find_mac_host_offset.
    - rewrite length_skipn. lia.
    - rewrite Lb. lia.
    - rewrite <- Eb, firstn_firstn, Nat.min_l by lia. reflexivity. }
  assert (Hdn0 : desk_named_m I (set_OW_desk_off (set_OW_desk B2 (d0 + 1)) off) (skipn 30 (tf_bytes fr)) =
                 Some (set_OW_desk_off (set_OW_desk B2 (d0 + 1)) off, dp))
    by (apply ann1_dn_some; apply Hdn).
  assert (E0 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E0) = false) by (rewrite Hcmd; reflexivity).
  assert (E1 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E1) = true) by (rewrite Hcmd; reflexivity).
  assert (Bl : (fr_body_len (rxbuf fr n) <? SPEC_ANN_MIN) = false)
    by (apply Z.ltb_ge; unfold SPEC_ANN_MIN; lia).
  unfold m_rx_sw. cbv zeta.
  rewrite (rf_cmd _ _ Hf), (rf_body_len _ _ Hf), (rf_body _ _ Hf).
  rewrite E0, E1, Bl. change (false || true) with true. cbv beta iota.
  change (Z.to_nat 30) with 30%nat. unfold host_offset_m. rewrite Hho. cbv beta iota.
  rewrite Hd, (ann1_int_inc d0) by lia. cbv beta iota.
  rewrite Hdn0. cbv beta iota.
  unfold ann1_mtail, ann1_mA, ann1_mU. cbv beta. wsyn.
Qed.

(* FT:324-328: foreign (OW.foreign + 1), then lose a live session *)
Lemma ann1_mtail_fo : forall B4 off f, length B4 = WN -> off < 0 -> OW_foreign B4 = f -> 0 <= f <= 1 ->
  ann1_mtail B4 off = if (M_state B4 =? S_ONLINE) || (M_state B4 =? S_WAKING)
                      then m_lost_m (ann1_mF B4 (f + 1)) R_FOREIGN else Some (ann1_mF B4 (f + 1), tt).
Proof.
  intros B4 off f HB Ho Hf Hfr. unfold ann1_mtail. cbv beta.
  rewrite (proj2 (Z.leb_gt 0 off) Ho). cbv beta iota.
  assert (E1 : OW_foreign (set_M_foreign B4 1) = f) by (transitivity (OW_foreign B4); [wget | exact Hf]).
  rewrite E1, (ann1_int_inc f) by lia. cbv beta iota.
  assert (E2 : M_state (set_OW_foreign (set_M_foreign B4 1) (f + 1)) = M_state B4) by wget.
  rewrite E2. unfold ann1_mF. reflexivity.
Qed.

(* on_announce (DS:209-220) after the N_DESK notice: the library's tail of the e1 branch *)
Definition ann1_ltail (I : timg) (F : option tframe) (W2 : list byte) (off : Z) (a : tann)
    : option (list byte * unit) :=
  if 0 <=? off then maybe_online_m I F (ann1_lU W2)
  else
    match call_notify I F (set_S_foreign W2 1)
            (Ntc DIGINET_N_FOREIGN (S_state (set_S_foreign W2 1)) 0 0 0 0 0 0 (Some a) [] 0) with
    | None => None
    | Some (B, _) =>
        if (S_state B =? DIGINET_S_ONLINE) || (S_state B =? DIGINET_S_WAKING)
        then session_lost_m I F B DIGINET_R_FOREIGN else Some (B, tt)
    end.

(* DS:215-220: foreign, the N_FOREIGN notice (FT:967-968: GOT.foreign + 1), then lose a live session *)
Lemma ann1_ltail_fo : forall I F W2 off a f, length W2 = WN -> off < 0 -> S_notify W2 = ti_notice I ->
  GOT_foreign W2 = f -> 0 <= f <= 1 ->
  ann1_ltail I F W2 off a = if (S_state W2 =? DIGINET_S_ONLINE) || (S_state W2 =? DIGINET_S_WAKING)
                            then session_lost_m I F (ann1_lF W2 (f + 1)) DIGINET_R_FOREIGN
                            else Some (ann1_lF W2 (f + 1), tt).
Proof.
  intros I F W2 off a f HW Ho Hno Hg Hfr. unfold ann1_ltail. cbv beta.
  rewrite (proj2 (Z.leb_gt 0 off) Ho). cbv beta iota.
  assert (E1 : S_notify (set_S_foreign W2 1) = ti_notice I) by (transitivity (S_notify W2); [wget | exact Hno]).
  assert (E2 : GOT_foreign (set_S_foreign W2 1) = f) by (transitivity (GOT_foreign W2); [wget | exact Hg]).
  assert (E3 : S_state (set_GOT_foreign (set_S_foreign W2 1) (f + 1)) = S_state W2) by wget.
  unfold call_notify. rewrite E1, (Z.eqb_refl (ti_notice I)). cbv beta iota.
  unfold notice_m. cbv zeta. cbn [n_kind].
  change (DIGINET_N_FOREIGN =? N_STATE) with false. change (DIGINET_N_FOREIGN =? N_ACKED) with false.
  change (DIGINET_N_FOREIGN =? N_ACK_LOST) with false. change (DIGINET_N_FOREIGN =? N_DESK) with false.
  change (DIGINET_N_FOREIGN =? N_DATA) with false. change (DIGINET_N_FOREIGN =? N_FOREIGN) with true.
  cbv beta iota. rewrite E2, (ann1_int_inc f) by lia. cbv beta iota.
  rewrite E3. unfold ann1_lF. reflexivity.
Qed.

(* DS:184-198 on an e1 of 33 bytes or more: the personality (DS:191-193), find_mac (DS:194, = OW.desk_off), the
   N_DESK notice (DS:196-198: GOT.desk g to g + 1, OW.desk being g + 1) that check_state_desk (FT:527-557) passes;
   then the tail *)
Lemma ann1_lib_prefix : forall (HL : links) I fr n W dp off now g, timg_ok I ->
  0 <= n <= Z.of_nat (length (tf_bytes fr)) -> 0 < tf_addr fr ->
  fr_code (rxbuf fr n) = DIGINET_OK -> fr_cmd (rxbuf fr n) = DIGINET_CMD_ANNOUNCE_SESSION ->
  33 <= fr_body_len (rxbuf fr n) -> off = find_mac_m (ann_unknown (fr_body (rxbuf fr n))) 15 HOST ->
  length W = WN -> S_cfg_host_mac W = HOST -> S_notify W = ti_notice I -> GOT_desk W = g -> OW_desk W = g + 1 ->
  0 <= g <= 1 -> OW_desk_off W = off -> OW_desk_p W = dp ->
  (forall X, option_map snd (desk_named_m I X (skipn 30 (tf_bytes fr))) = Some dp) ->
  OW_desk_body W = tf_addr fr + 30 ->
  exists W2, rx_sw I (Some fr) W (rxbuf fr n) now =
      ann1_ltail I (Some fr) W2 off
        (TAnn (ann_field (skipn 15 (fr_body (rxbuf fr n)))) (ann_field (skipn 24 (fr_body (rxbuf fr n))))) /\
    length W2 = WN /\ wframe (in_rs [(A_S_personality, 8); (A_GOT_desk, 4)]) W W2 /\ GOT_desk W2 = g + 1 /\
    (S_personality W2 = S_personality W \/ S_personality W2 = ti_personalities I \/
     S_personality W2 = ti_personalities I + 24).
Proof.
  intros HL I [a bytes] n W dp off now g HI Hn Ha Hc Hcmd Hbl Eoff HW Hhm Hno Hg Hod Hgr Hoff Hdp Hdn Hdb.
  unfold rxbuf in *. cbn [tf_bytes tf_addr] in *.

  assert (Hnn : (Z.to_nat n <= length bytes)%nat) by lia.
  assert (Ea : ann_code (fr_cmd (firstn (Z.to_nat n) bytes)) (fr_body_len (firstn (Z.to_nat n) bytes)) = DIGINET_OK).
  { rewrite Hcmd. unfold ann_code. change (ann_cmd DIGINET_CMD_ANNOUNCE_SESSION) with true.
    cbv beta iota delta [negb]. rewrite (proj2 (Z.ltb_ge _ 33) Hbl). reflexivity. }
  assert (F1 : (fr_cmd (firstn (Z.to_nat n) bytes) =? DIGINET_CMD_ANNOUNCE) = false) by (rewrite Hcmd; reflexivity).
  assert (F2 : (fr_cmd (firstn (Z.to_nat n) bytes) =? DIGINET_CMD_ANNOUNCE_SESSION) = true)
    by (rewrite Hcmd; reflexivity).
  assert (Hann : ann_cmd (fr_cmd (firstn (Z.to_nat n) bytes)) = true) by (rewrite Hcmd; reflexivity).
  pose proof HL as (_ & _ & _ & _ & HL5 & _).
  assert (Lb : SPEC_ANN_MIN <= Z.of_nat (length (fr_body (firstn (Z.to_nat n) bytes)))).
  { rewrite (length_fr_body _ Hc). unfold SPEC_ANN_MIN. lia. }
  pose proof (HL5 I W (fr_body (firstn (Z.to_nat n) bytes)) Lb) as H5. cbv zeta in H5.
  destruct H5 as (dp' & _ & H5). change (Z.to_nat SPEC_ANN_NAME) with 24%nat in H5.
  pose proof (ti_personalities_ok I HI) as Hpers.
  unfold rx_sw. cbv zeta. rewrite F1, F2. change (false || true) with true. cbv beta iota.
  unfold on_announce_m. cbv zeta. rewrite Ea, (Z.eqb_refl DIGINET_OK). change (negb true) with false.
  cbv beta iota.
  rewrite F2, F1. cbv beta iota.
  match goal with |- context [diginet_personality_from_name ?t] =>
    destruct (diginet_personality_from_name t) as [i|] eqn:Ep end.
  all: cbv beta iota.
  all: match goal with |- context [call_notify _ _ ?W1 (Ntc DIGINET_N_DESK _ _ _ _ _ _ _ _ _ _)] =>
    assert (L1 : length W1 = WN) by wlen;
    assert (M1 : S_cfg_host_mac W1 = HOST) by (transitivity (S_cfg_host_mac W); [wg | exact Hhm]);
    rewrite M1, <- Eoff;
    exists (set_GOT_desk W1 (g + 1));
    assert (N1 : S_notify W1 = ti_notice I) by (transitivity (S_notify W); [wg | exact Hno]);
    assert (G1 : GOT_desk W1 = g) by (transitivity (GOT_desk W); [wg | exact Hg]);
    assert (K1a : GOT_desk (set_GOT_desk W1 (g + 1)) = g + 1) by wg;
    assert (K1b : OW_desk (set_GOT_desk W1 (g + 1)) = g + 1) by (transitivity (OW_desk W); [wg | exact Hod]);
    assert (K1 : GOT_desk (set_GOT_desk W1 (g + 1)) <= OW_desk (set_GOT_desk W1 (g + 1))) by (rewrite K1a, K1b; lia);
    assert (K2 : OW_desk_off (set_GOT_desk W1 (g + 1)) = off) by (transitivity (OW_desk_off W); [wg | exact Hoff]);
    assert (K3 : OW_desk_p (set_GOT_desk W1 (g + 1)) = dp) by (transitivity (OW_desk_p W); [wg | exact Hdp]);
    assert (K4 : OW_desk_body (set_GOT_desk W1 (g + 1)) = a + 30)
      by (transitivity (OW_desk_body W); [wg | exact Hdb]);
    pose proof (check_state_desk_ok HL I (set_GOT_desk W1 (g + 1)) a bytes (Z.to_nat n) (S_state W1) dp HI Hnn) as CK
  end.
  all: cbv zeta in CK; rewrite F2 in CK; try rewrite Ep in CK; cbv beta iota in CK; rewrite <- Eoff in CK.
  all: specialize (CK Hc Hann Hbl K1 K2 (Hdn _) K3 Ha K4).
  all: match goal with |- context [call_notify ?I' ?F' ?W1 (Ntc DIGINET_N_DESK ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10)] =>
    assert (CN : call_notify I' F' W1 (Ntc DIGINET_N_DESK a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) =
                 Some (set_GOT_desk W1 (g + 1), tt));
    [ unfold call_notify; rewrite N1, (Z.eqb_refl (ti_notice I)); cbv beta iota;
      rewrite (ann1_notice_desk I' F' W1 (Ntc DIGINET_N_DESK a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) g eq_refl G1 Hgr); wexact
    | rewrite CN; cbv beta iota ]
  end.
  all: split; [unfold ann1_ltail, ann1_lU; cbv beta; wsyn|].
  all: split; [wlen|]; split; [wfrs|]; split; [wg|].
  - try rewrite Ep in H5. cbv beta iota in H5. destruct H5 as (pp & d & _ & Hi & _).
    destruct Hi as [(-> & _) | (-> & _)]; right; [left | right].
    + transitivity (ti_personalities I + 24 * 0); [wg | ring].
    + transitivity (ti_personalities I + 24 * 1); [wg | ring].
  - left. wg.
Qed.

(* ---- after the switch ---- *)

(* the keepalive deadline ONLINE sets (FT:240 / DS:179): now < 2^47, ka <= 65536, so no u64 wraps *)
Definition ann1_kv (B : list byte) : Z := g_now B + Cfg_keepalive_ms B * 1000.

Lemma ann1_kv_facts : forall I ops B, agree_core I ops B ->
  0 <= ann1_kv B < 2 ^ 64 /\ ann1_kv B <= g_now B + 65536000 /\
  u64 (g_now B + h_ms_m (Cfg_keepalive_ms B)) = ann1_kv B /\
  u64 (g_now B + ms_m (Cfg_keepalive_ms B)) = ann1_kv B.
Proof.
  intros I ops B Hcore. pose proof Hcore as [_ _ Hcfg _ _ _ Htime Hq _].
  pose proof (a1_keepalive _ Hcfg) as Hk. pose proof (c_now _ _ Htime) as Hc. pose proof (d3_ops _ _ Hq) as Ho.
  assert (H0 : 0 <= g_now B) by (unfold g_now; apply u_at_nonneg).
  unfold OPS_MAX in Ho. unfold ann1_kv, h_ms_m, ms_m, u64.
  clear - Hk Hc Ho H0.
  assert (Hn : g_now B <= 1000000 + 1024 * 65535000000) by lia.
  rewrite (Z.mod_small (Cfg_keepalive_ms B * 1000) (2 ^ 64)) by lia.
  rewrite (Z.mod_small (g_now B + Cfg_keepalive_ms B * 1000) (2 ^ 64)) by lia.
  lia.
Qed.

(* m_tick (FT:246-252) after the switch: nothing overdue (the state is B's, ONLINE with last_rx = now, or IDLE) *)
Lemma ann1_tick : forall ops B Bm, agree_cfg B -> agree_time ops B ->
  (M_state Bm = M_state B \/ M_state Bm = S_ONLINE \/ M_state Bm = S_IDLE) ->
  M_last_rx Bm = g_now B -> M_wake_sent Bm = M_wake_sent B -> g_now Bm = g_now B ->
  Cfg_wake_timeout_ms Bm = Cfg_wake_timeout_ms B -> Cfg_offline_ms Bm = Cfg_offline_ms B ->
  m_tick_m Bm = Some (Bm, tt).
Proof.
  intros ops B Bm Hcfg Htime Hs Hlr Hws Hnw Hcw Hco. apply m_tick_quiet.
  - intros Hw. rewrite Hws, Hnw, Hcw.
    assert (Hb : M_state B = S_WAKING).
    { destruct Hs as [E | [E | E]]; rewrite E in Hw; [exact Hw | destruct (ann1_ow Hw) | destruct (ann1_iw Hw)]. }
    split; [exact (c1_wake_sent _ _ Htime) | exact (c2_wake _ _ Htime Hb)].
  - intros _. rewrite Hlr, Hnw, Hco, (Z.sub_diag (g_now B)). pose proof (a1_offline _ Hcfg) as Ho.
    split; [apply Z.le_refl | clear - Ho; lia].
  - rewrite Hcw. exact (proj2 (a1_wake_timeout _ Hcfg)).
  - rewrite Hco. exact (proj2 (a1_offline _ Hcfg)).
Qed.

(* every range an e1 reception writes, on either side, with the prologue's *)
Definition ann1_R : list (Z * Z) :=
  ((R_learn ++ [(A_M_last_rx, 8)]) ++ ann1_RA ++ ann1_RU ++ ann1_RON ++ ann1_RF ++ ann1_RL) ++
  (R_start ++ [(A_S_personality, 8); (A_GOT_desk, 4)] ++ ann1_RLU ++ ann1_RLON ++ ann1_RLF ++ ann1_RLL ++
   [(A_S_stats_rx_ignored, 8)]).

(* the transition logs after an e1 reception: below k = OW.n B (= GOT.n B) both are B's, and a transition
   logged by the reception lands at index k on both sides *)
Lemma ann1_og_t : forall B W' k, ow_got_eq B -> OW_n B = k ->
  (forall i, 0 <= i < k ->
     GOT_t_state W' i = GOT_t_state B i /\ GOT_t_old W' i = GOT_t_old B i /\ GOT_t_reason W' i = GOT_t_reason B i /\
     OW_t_state W' i = OW_t_state B i /\ OW_t_old W' i = OW_t_old B i /\ OW_t_reason W' i = OW_t_reason B i) ->
  (OW_n W' = k \/ (OW_n W' = k + 1 /\ GOT_t_state W' k = OW_t_state W' k /\ GOT_t_old W' k = OW_t_old W' k /\
                   GOT_t_reason W' k = OW_t_reason W' k)) ->
  forall i, 0 <= i < OW_n W' -> i < TRANS_MAX ->
    GOT_t_state W' i = OW_t_state W' i /\ GOT_t_old W' i = OW_t_old W' i /\ GOT_t_reason W' i = OW_t_reason W' i.
Proof.
  intros B W' k Hog Hk Hbelow Hnew i Hi Ht.
  assert (Hc : i < k \/ (i = k /\ OW_n W' = k + 1)) by (destruct Hnew as [E | (E & _)]; lia).
  destruct Hc as [Hlt | (Ei & _)].
  - destruct (Hbelow i ltac:(lia)) as (T1 & T2 & T3 & T4 & T5 & T6). rewrite T1, T2, T3, T4, T5, T6.
    apply (og_t _ Hog); lia.
  - subst i. destruct Hnew as [E | (_ & N1 & N2 & N3)]; [lia | exact (conj N1 (conj N2 N3))].
Qed.

(* agree_core, the OW / GOT counts and the step from B after an e1 reception, from the fields it moves *)
Lemma ann1_post : forall I ops B W',
  agree_core I ops B -> ow_room B -> wframe (in_rs ann1_R) B W' -> agree_fly W' ->
  M_desk_known W' = 1 -> S_desk_known W' = 1 -> S_desk_mac W' = M_desk W' ->
  M_last_rx W' = g_now B -> S_last_rx_us W' = g_now B ->
  S_state W' = M_state W' -> 0 <= M_state W' <= 3 -> (M_state W' = S_WAKING -> M_state B = S_WAKING) ->
  (M_state W' = S_IDLE \/ M_state W' = S_CLOSED -> M_fly_on W' = 0) ->
  (M_fly_on W' = 1 -> M_fly_on B = 1) ->
  S_foreign W' = M_foreign W' -> bit01 (M_foreign W') ->
  S_e1_named_us W' = M_e1_us W' -> bit01 (M_e1_us W') ->
  (g_raw B = 0 -> S_next_keepalive_us W' = M_next_ka W' /\ M_next_ka W' <= g_now B + 65536000) ->
  S_desk_counter_valid W' = M_desk_counter_valid W' -> bit01 (M_desk_counter_valid W') ->
  (M_desk_counter_valid W' = 1 -> M_desk_counter_valid B = 1) ->
  (S_personality W' = 0 \/ S_personality W' = ti_personalities I \/ S_personality W' = ti_personalities I + 24) ->
  GOT_n W' = OW_n W' -> OW_n B <= OW_n W' <= OW_n B + 1 ->
  (forall i, 0 <= i < OW_n W' -> i < TRANS_MAX ->
     GOT_t_state W' i = OW_t_state W' i /\ GOT_t_old W' i = OW_t_old W' i /\ GOT_t_reason W' i = OW_t_reason W' i) ->
  GOT_desk W' = OW_desk W' -> OW_desk B <= OW_desk W' <= OW_desk B + 1 ->
  GOT_foreign W' = OW_foreign W' -> OW_foreign B <= OW_foreign W' <= OW_foreign B + 1 ->
  agree_core I ops W' /\ ow_got_eq W' /\ ow_step B W'.
Proof.
  intros I ops B W' Hcore Hrm Hall Hfl' Wdk Wsk Wdm Wlr Wsl Wss Wrg Wwk Wb9 Wf1 Wfs Wf01 Wes We01 Wka Wvs Wv01 Wv1
    Wpe Wgn Wn Wt Wgd Wodr Wgf Wofr.
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof Hrm as [Hog Rn Re2 Re3 Rac Rd Rf Rak Rnd].
  pose proof Hog as [Gn Gnr Gt Ge2 Ge2r Ge3 Ge3r Gac Gacr Gd Gdr Gf Gfr Gak Gakr Gnd Gndr].
  (* the fields nobody wrote *)
  assert (U7 : S_wake_acked W' = S_wake_acked B) by fget Hall.
  assert (U8 : M_e2_acked W' = M_e2_acked B) by fget Hall.
  assert (U9 : S_wake_sent_us W' = S_wake_sent_us B) by fget Hall.
  assert (U10 : M_wake_sent W' = M_wake_sent B) by fget Hall.
  assert (U11 : S_backoff_until_us W' = S_backoff_until_us B) by fget Hall.
  assert (U12 : M_backoff_until W' = M_backoff_until B) by fget Hall.
  assert (U13 : g_raw W' = g_raw B) by fget Hall.
  assert (U16 : S_display_sent W' = S_display_sent B) by fget Hall.
  assert (U17 : M_display_sent W' = M_display_sent B) by fget Hall.
  assert (U18 : S_last_display_us W' = S_last_display_us B) by fget Hall.
  assert (U19 : M_last_display W' = M_last_display B) by fget Hall.
  assert (U22 : S_desk_counter W' = S_desk_counter B) by fget Hall.
  assert (U23 : M_desk_counter W' = M_desk_counter B) by fget Hall.
  assert (U24 : S_host_counter W' = S_host_counter B) by fget Hall.
  assert (U25 : M_host_counter W' = M_host_counter B) by fget Hall.
  assert (U33 : M_fly_sent W' = M_fly_sent B) by fget Hall.
  assert (U39 : g_now W' = g_now B) by fget Hall.
  assert (U40 : Cfg_wake_timeout_ms W' = Cfg_wake_timeout_ms B) by fget Hall.
  assert (U41 : Cfg_offline_ms W' = Cfg_offline_ms B) by fget Hall.
  assert (U42 : Cfg_ack_timeout_ms W' = Cfg_ack_timeout_ms B) by fget Hall.
  assert (U43 : g_fail_next W' = g_fail_next B) by fget Hall.
  (* the counts nobody moved *)
  assert (O2 : OW_e2 W' = OW_e2 B) by fget Hall.
  assert (O3 : OW_e3 W' = OW_e3 B) by fget Hall.
  assert (O4 : OW_acks W' = OW_acks B) by fget Hall.
  assert (O6 : OW_acked W' = OW_acked B) by fget Hall.
  assert (O7 : OW_ndata W' = OW_ndata B) by fget Hall.
  assert (G2 : GOT_e2 W' = GOT_e2 B) by fget Hall.
  assert (G3 : GOT_e3 W' = GOT_e3 B) by fget Hall.
  assert (G4 : GOT_acks W' = GOT_acks B) by fget Hall.
  assert (G6 : GOT_acked W' = GOT_acked B) by fget Hall.
  assert (G7 : GOT_ndata W' = GOT_ndata B) by fget Hall.
  assert (Hst' : agree_st W').
  { constructor; rw_eqs W'.
    - reflexivity.
    - exact Wrg.
    - reflexivity.
    - right; reflexivity.
    - intros _; reflexivity.
    - reflexivity.
    - exact Wf01.
    - reflexivity.
    - exact We01.
    - exact (b3_e2 _ Hst).
    - exact (b3_e2_01 _ Hst).
    - exact (b4_wake_sent _ Hst).
    - reflexivity.
    - exact (b4_backoff _ Hst).
    - intros Hr. exact (proj1 (Wka Hr)).
    - exact (b5_display_sent _ Hst).
    - exact (b5_display_sent01 _ Hst).
    - exact (b5_last_display _ Hst).
    - reflexivity.
    - exact Wv01.
    - intros H. exact (b6_counter _ Hst (Wv1 H)).
    - exact (b7_host_counter _ Hst).
    - exact Wb9.
    - intros _; reflexivity. }
  assert (Hti' : agree_time ops W').
  { constructor; rw_eqs W'.
    - exact (c_now _ _ Htime).
    - apply Z.le_refl.
    - exact (c1_wake_sent _ _ Htime).
    - intros H. exact (c1_fly_sent _ _ Htime (Wf1 H)).
    - exact (c1_last_display _ _ Htime).
    - exact (c1_backoff _ _ Htime).
    - intros Hr. exact (proj2 (Wka Hr)).
    - intros H. exact (c2_wake _ _ Htime (Wwk H)).
    - intros _. rewrite (Z.sub_diag (g_now B)). pose proof (a1_offline _ Hcfg) as Ho. clear - Ho. lia.
    - intros H. exact (c2_fly _ _ Htime (Wf1 H)). }
  assert (Hmi' : agree_misc I W').
  { constructor; rw_eqs W'; [exact (e1_fail_next _ _ Hmisc) | exact Wpe]. }
  split; [|split].
  - apply (agree_core_rx I ops B W' Hcore); [| exact Hst' | exact Hfl' | exact Hti' | exact Hmi'].
    eapply wframe_rx; [| exact Hall]. vm_compute. reflexivity.
  - constructor.
    + exact Wgn.
    + clear - Gnr Rn Wn. lia.
    + exact Wt.
    + rewrite G2, O2. exact Ge2.
    + rewrite O2. exact Ge2r.
    + rewrite G3, O3. exact Ge3.
    + rewrite O3. exact Ge3r.
    + rewrite G4, O4. exact Gac.
    + rewrite O4. exact Gacr.
    + exact Wgd.
    + clear - Gdr Rd Wodr. lia.
    + exact Wgf.
    + clear - Gfr Rf Wofr. lia.
    + rewrite G6, O6. exact Gak.
    + rewrite O6. exact Gakr.
    + rewrite G7, O7. exact Gnd.
    + rewrite O7. exact Gndr.
  - constructor.
    + clear - Wn. lia.
    + rewrite O2. slia.
    + rewrite O3. slia.
    + rewrite O4. slia.
    + clear - Wodr. lia.
    + clear - Wofr. lia.
    + rewrite O6. slia.
    + rewrite O7. slia.
Qed.

(* ---- the long body: the facts both sides share ---- *)

Record ann1_ctx (I : timg) (ops : Z) (fr : tframe) (n : Z) (B B2 : list byte) (off dp : Z) : Prop := {
  cx_core : agree_core I ops B;
  cx_room : ow_room B;
  cx_acc : rx_accepts B (rxbuf fr n);
  cx_cmd : fr_cmd (rxbuf fr n) = DIGINET_CMD_ANNOUNCE_SESSION;
  cx_n : 0 <= n <= Z.of_nat (length (tf_bytes fr));
  cx_addr : 0 < tf_addr fr /\ tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64;
  cx_blen : 33 <= fr_body_len (rxbuf fr n);
  cx_len2 : length B2 = WN;
  cx_fr2 : wframe (in_rs (R_learn ++ [(A_M_last_rx, 8)])) B B2;
  cx_dk : M_desk_known B2 = 1;
  cx_dm : M_desk B2 = fr_src (rxbuf fr n);
  cx_lr : M_last_rx B2 = g_now B;
  cx_off : off = find_mac_m (ann_unknown (fr_body (rxbuf fr n))) 15 HOST;
  cx_offr : -1 <= off < 11;
  cx_dn : forall X, option_map snd (desk_named_m I X (skipn 30 (tf_bytes fr))) = Some dp;
  cx_dpr : 0 <= dp < 2 ^ 64;
}.

(* what rx_branch_g asks of the model's world after FT:301 (B2 = set_M_last_rx (learn_M B buf) now) *)
Definition ann1_concl (I : timg) (ops : Z) (fr : tframe) (n : Z) (B B2 : list byte) : Prop :=
  exists Bm, m_rx_sw I fr n B2 = Some (Bm, tt) /\ m_tick_m Bm = Some (Bm, tt) /\
    (length Bm = length B /\ forall a : nat, ~ in_rs R_mod (Z.of_nat a) -> nth_error Bm a = nth_error B a) /\
    forall W, lib_start Bm W (rxbuf fr n) ->
      exists W', rx_sw I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', tt) /\ rx_post_g I ops B (rxbuf fr n) W W'.

Lemma ann1_ctx_a30 : forall (HL : links) I ops fr n B B2 off dp, ann1_ctx I ops fr n B B2 off dp ->
  0 <= tf_addr fr + 30 < 2 ^ 64.
Proof.
  intros HL I ops fr n B B2 off dp Hx.
  destruct Hx as [_ _ Hacc _ Hn Ha _ _ _ _ _ _ _ _ _ _].
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  pose proof (rf_blen _ _ Hf) as Hb. clear - Hb Hn Ha. lia.
Qed.

(* FT:303-312: the model names the desk, OW.desk + 1 *)
Lemma ann1_ctx_sw : forall (HL : links) I ops fr n B B2 off dp, ann1_ctx I ops fr n B B2 off dp ->
  m_rx_sw I fr n B2 = ann1_mtail (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) off.
Proof.
  intros HL I ops fr n B B2 off dp Hx.
  destruct Hx as [Hcore Hrm Hacc Hc Hn Ha Hbl HB2 H02 Lk Ld Mlr Eoff Hoffr Hdn Hdpr].
  destruct (ann1_room B Hrm) as (_ & Rd & _).
  apply (ann1_m_prefix HL I fr n B2 dp off (OW_desk B) Hn (ra_code _ _ Hacc) Hc Hbl);
    [fget H02 | exact Rd | exact Hdn | exact Eoff].
Qed.

(* every range the model's tails write after FT:311 *)
Definition ann1_Rm : list (Z * Z) := ann1_RU ++ ann1_RON ++ ann1_RF ++ ann1_RL.

(* the library's world at its switch (lib_start of the model's), as on_announce reads it *)
Lemma ann1_wpre : forall (HL : links) I ops fr n B B2 off dp Bm W, ann1_ctx I ops fr n B B2 off dp ->
  wframe (in_rs ann1_Rm) (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) Bm -> length Bm = WN ->
  lib_start Bm W (rxbuf fr n) ->
  length W = WN /\ S_cfg_host_mac W = HOST /\ S_notify W = ti_notice I /\ GOT_desk W = OW_desk B /\
  OW_desk W = OW_desk B + 1 /\ OW_desk_off W = off /\ OW_desk_p W = dp /\ OW_desk_body W = tf_addr fr + 30 /\
  GOT_n W = OW_n B /\ GOT_foreign W = OW_foreign B /\ S_state W = M_state B /\ S_wake_acked W = M_e2_acked B /\
  S_last_rx_us W = g_now B /\ S_cfg_keepalive_ms W = Cfg_keepalive_ms B /\ M_e2_acked W = M_e2_acked B.
Proof.
  intros HL I ops fr n B B2 off dp Bm W Hx H4m HBm HW.
  pose proof (ann1_ctx_a30 HL _ _ _ _ _ _ _ _ Hx) as Ha30.
  destruct Hx as [Hcore Hrm Hacc Hc Hn Ha Hbl HB2 H02 Lk Ld Mlr Eoff Hoffr Hdn Hdpr].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  destruct (ann1_room B Hrm) as (Rn & Rd & Rf & Gn & Gd & Gf).
  destruct (ann1_mA_get B2 (OW_desk B + 1) off dp (tf_addr fr) HB2 ltac:(clear - Rd; lia) Hoffr Hdpr Ha30)
    as (HB4 & H24 & A1 & A2 & A3 & A4).
  remember (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) as B4 eqn:EB4.
  pose proof HW as (HWf & HWk & HWm & HWl).
  pose proof (wframe_trans_rs _ _ _ _ _ H4m HWf) as H4w.
  pose proof (wframe_trans_rs _ _ _ _ _ (wframe_trans_rs _ _ _ _ _ H02 H24) H4m) as H0m.
  pose proof (wframe_trans_rs _ _ _ _ _ H0m HWf) as H0w.
  split; [eapply wframe_len; [exact HWf | exact HBm]|].
  split; [transitivity (S_cfg_host_mac B); [fget H0w | exact (a2_host_mac _ Hcfg)]|].
  split; [transitivity (S_notify B); [fget H0w | exact (a3_notify _ _ Hio)]|].
  split; [transitivity (GOT_desk B); [fget H0w | exact Gd]|].
  split; [transitivity (OW_desk B4); [fget H4w | exact A1]|].
  split; [transitivity (OW_desk_off B4); [fget H4w | exact A2]|].
  split; [transitivity (OW_desk_p B4); [fget H4w | exact A3]|].
  split; [transitivity (OW_desk_body B4); [fget H4w | exact A4]|].
  split; [transitivity (GOT_n B); [fget H0w | exact Gn]|].
  split; [transitivity (GOT_foreign B); [fget H0w | exact Gf]|].
  split; [transitivity (S_state B); [fget H0w | exact (b1_state _ Hst)]|].
  split; [transitivity (S_wake_acked B); [fget H0w | exact (b3_e2 _ Hst)]|].
  split; [rewrite HWl; fget H0m|].
  split; [transitivity (S_cfg_keepalive_ms B); [fget H0w | exact (a2_keepalive _ Hcfg)]|].
  fget H0w.
Qed.

(* ---- the e1 names this host (FT:319-322, DS:209-214) ---- *)

(* WAKING with the wake acked: both go ONLINE (the library's tick-free part) *)
Lemma ann1_lib_us_on : forall (HL : links) I ops fr n B B2 off dp W, ann1_ctx I ops fr n B B2 off dp ->
  0 <= off -> M_state B = S_WAKING -> M_e2_acked B = 1 ->
  lib_start (ann1_mON (ann1_mU (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr))) (ann1_kv B) (OW_n B)) W
    (rxbuf fr n) ->
  exists W', rx_sw I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', tt) /\ rx_post_g I ops B (rxbuf fr n) W W'.
Proof.
  intros HL I ops fr n B B2 off dp W Hx Hoff Hw He HW.
  pose proof (ann1_ctx_a30 HL _ _ _ _ _ _ _ _ Hx) as Ha30.
  pose proof Hx as [Hcore Hrm Hacc Hc Hn Ha Hbl HB2 H02 Lk Ld Mlr Eoff Hoffr Hdn Hdpr].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hrm) as Hog.
  destruct (ann1_room B Hrm) as (Rn & Rd & Rf & Gn & Gd & Gf).
  destruct (ann1_kv_facts I ops B Hcore) as (Hkvr & Hkvle & _ & Hkvl).
  destruct (ann1_mA_get B2 (OW_desk B + 1) off dp (tf_addr fr) HB2 ltac:(clear - Rd; lia) Hoffr Hdpr Ha30)
    as (HB4 & H24 & A1 & A2 & A3 & A4).
  remember (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) as B4 eqn:EB4.
  destruct (ann1_mU_get B4 HB4) as (HX & H4x & U1 & U2).
  remember (ann1_mU B4) as X eqn:EX.
  destruct (ann1_mON_get X (ann1_kv B) (OW_n B) HX Hkvr Rn) as (HBm & Hxm & M1 & M2 & M3 & M4 & M5 & M6 & M7).
  remember (ann1_mON X (ann1_kv B) (OW_n B)) as Bm eqn:EBm.
  assert (H4m : wframe (in_rs ann1_Rm) B4 Bm).
  { refine (wframe_rs_incl _ ann1_Rm B4 Bm _ (wframe_trans_rs _ _ _ _ _ H4x Hxm)). vm_compute. reflexivity. }
  destruct (ann1_wpre HL I ops fr n B B2 off dp Bm W Hx ltac:(rewrite <- EB4; exact H4m) HBm HW)
    as (HWn & Whm & Wno & Wgd & Wod & Woo & Wop & Wob & Wgn & Wgf & Wss & Wwa & Wlr & Wka & We2).
  destruct (ann1_lib_prefix HL I fr n W dp off (g_now B) (OW_desk B) Himg Hn (proj1 Ha) (ra_code _ _ Hacc) Hc Hbl
              Eoff HWn Whm Wno Wgd Wod Rd Woo Wop Hdn Wob) as (W2 & Epre & HW2n & HW2f & HW2g & HW2p).
  destruct (ann1_lU_get W2 HW2n) as (HYn & H2y & Y1 & Y2).
  remember (ann1_lU W2) as Y eqn:EY.
  pose proof HW as (HWf & HWk & HWm & HWl).
  pose proof (wframe_trans_rs _ _ _ _ _ HW2f H2y) as Hwy.
  assert (Ys : S_state Y = DIGINET_S_WAKING) by (transitivity (S_state W); [fget Hwy | rewrite Wss; exact Hw]).
  assert (Ywa : S_wake_acked Y = 1) by (transitivity (S_wake_acked W); [fget Hwy | rewrite Wwa; exact He]).
  assert (Yno : S_notify Y = ti_notice I) by (transitivity (S_notify W); [fget Hwy | exact Wno]).
  assert (Ygn : GOT_n Y = OW_n B) by (transitivity (GOT_n W); [fget Hwy | exact Wgn]).
  assert (Ym2 : M_e2_acked Y = 1) by (transitivity (M_e2_acked W); [fget Hwy | rewrite We2; exact He]).
  assert (Ym1 : M_e1_us Y = 1)
    by (transitivity (M_e1_us X); [fget (wframe_trans_rs _ _ _ _ _ Hxm (wframe_trans_rs _ _ _ _ _ HWf Hwy))
                                   | exact U2]).
  assert (Ekl : u64 (S_last_rx_us Y + ms_m (S_cfg_keepalive_ms Y)) = ann1_kv B).
  { assert (Ylr : S_last_rx_us Y = g_now B) by (transitivity (S_last_rx_us W); [fget Hwy | exact Wlr]).
    assert (Ykm : S_cfg_keepalive_ms Y = Cfg_keepalive_ms B)
      by (transitivity (S_cfg_keepalive_ms W); [fget Hwy | exact Wka]).
    rewrite Ylr, Ykm. exact Hkvl. }
  pose proof (ann1_l_online I (Some fr) Y (ann1_kv B) (OW_n B) HYn Ys Ywa Y2 Yno Ygn Rn Ym2 Ym1 Hkvr Ekl) as Elo.
  destruct (ann1_lON_get Y (ann1_kv B) (OW_n B) HYn Hkvr Rn) as (HW'n & Hyw & L1 & L2 & L3 & L4 & L5 & L6 & L7).
  remember (ann1_lON Y (ann1_kv B) (OW_n B)) as W' eqn:EW'.
  exists W'. split.
  { rewrite Epre. unfold ann1_ltail. cbv beta. rewrite (proj2 (Z.leb_le 0 off) Hoff). cbv beta iota.
    rewrite <- EY. exact Elo. }
  pose proof (wframe_trans_rs _ _ _ _ _ Hwy Hyw) as Hww.
  pose proof (wframe_trans_rs _ _ _ _ _ HWf Hww) as Hmw.
  pose proof (wframe_trans_rs _ _ _ _ _ Hxm Hmw) as Hxw.
  pose proof (wframe_trans_rs _ _ _ _ _ H4x Hxw) as H4w.
  pose proof (wframe_trans_rs _ _ _ _ _ H24 H4w) as H2w.
  pose proof (wframe_trans_rs _ _ _ _ _ H02 H2w) as Hall.
  pose proof (wframe_trans_rs _ _ _ _ _ H2y Hyw) as H2'w.
  pose proof (wframe_trans_rs _ _ _ _ _ H02 (wframe_trans_rs _ _ _ _ _ H24 H4x)) as H0x.
  pose proof (wframe_trans_rs _ _ _ _ _ H0x Hxm) as H0m.
  pose proof (wframe_trans_rs _ _ _ _ _ H0m (wframe_trans_rs _ _ _ _ _ HWf Hwy)) as H0y.
  assert (Wdk : M_desk_known W' = 1) by (transitivity (M_desk_known B2); [fget H2w | exact Lk]).
  assert (D1 : S_desk_mac W' = fr_src (rxbuf fr n)) by (transitivity (S_desk_mac W); [fget Hww | exact HWm]).
  assert (D2 : M_desk W' = fr_src (rxbuf fr n)) by (transitivity (M_desk B2); [fget H2w | exact Ld]).
  assert (Wsk : S_desk_known W' = 1) by (transitivity (S_desk_known W); [fget Hww | exact HWk]).
  assert (Wlr' : M_last_rx W' = g_now B) by (transitivity (M_last_rx B2); [fget H2w | exact Mlr]).
  assert (Wsl : S_last_rx_us W' = g_now B) by (transitivity (S_last_rx_us W); [fget Hww | exact Wlr]).
  assert (Wms : M_state W' = S_ONLINE) by (transitivity (M_state Bm); [fget Hmw | exact M1]).
  assert (Wmf : M_foreign W' = 0) by (transitivity (M_foreign X); [fget Hxw | exact U1]).
  assert (Wsf : S_foreign W' = 0) by (transitivity (S_foreign Y); [fget Hyw | exact Y1]).
  assert (Wme : M_e1_us W' = 1) by (transitivity (M_e1_us X); [fget Hxw | exact U2]).
  assert (Wse : S_e1_named_us W' = 1) by (transitivity (S_e1_named_us Y); [fget Hyw | exact Y2]).
  assert (Wmk : M_next_ka W' = ann1_kv B) by (transitivity (M_next_ka Bm); [fget Hmw | exact M2]).
  assert (Wfo : M_fly_on W' = M_fly_on B) by fget Hall.
  assert (Wsv : S_desk_counter_valid W' = S_desk_counter_valid B) by fget Hall.
  assert (Wmv : M_desk_counter_valid W' = M_desk_counter_valid B) by fget Hall.
  assert (Wsp : S_personality W' = S_personality W2) by fget H2'w.
  assert (Wsp0 : S_personality W = S_personality B) by (transitivity (S_personality Bm); [fget HWf | fget H0m]).
  assert (Won : OW_n W' = OW_n B + 1) by (transitivity (OW_n Bm); [fget Hmw | exact M3]).
  assert (Wot : OW_t_state W' (OW_n B) = S_ONLINE)
    by (transitivity (OW_t_state Bm (OW_n B)); [tget Hmw | exact M4]).
  assert (Woo' : OW_t_old W' (OW_n B) = S_WAKING) by (transitivity (OW_t_old Bm (OW_n B)); [tget Hmw | exact M5]).
  assert (Wor : OW_t_reason W' (OW_n B) = R_ONLINE)
    by (transitivity (OW_t_reason Bm (OW_n B)); [tget Hmw | exact M6]).
  assert (Wgd' : GOT_desk W' = OW_desk B + 1) by (transitivity (GOT_desk W2); [fget H2'w | exact HW2g]).
  assert (Wod' : OW_desk W' = OW_desk B + 1) by (transitivity (OW_desk B4); [fget H4w | exact A1]).
  assert (Wgf' : GOT_foreign W' = OW_foreign B) by (transitivity (GOT_foreign B); [fget Hall | exact Gf]).
  assert (Wof' : OW_foreign W' = OW_foreign B) by fget Hall.
  (* below OW.n B: GOT.t through ON's notice (GOT.t[OW.n B] only) and frames, OW.t through m_set likewise *)
  assert (Hbelow : forall i, 0 <= i < OW_n B ->
    GOT_t_state W' i = GOT_t_state B i /\ GOT_t_old W' i = GOT_t_old B i /\ GOT_t_reason W' i = GOT_t_reason B i /\
    OW_t_state W' i = OW_t_state B i /\ OW_t_old W' i = OW_t_old B i /\ OW_t_reason W' i = OW_t_reason B i).
  { intros i Hi. destruct (L7 i Hi) as (P1 & P2 & P3). destruct (M7 i Hi) as (Q1 & Q2 & Q3).
    assert (E1 : GOT_t_state Y i = GOT_t_state B i) by tget H0y.
    assert (E2 : GOT_t_old Y i = GOT_t_old B i) by tget H0y.
    assert (E3 : GOT_t_reason Y i = GOT_t_reason B i) by tget H0y.
    assert (E4 : OW_t_state W' i = OW_t_state Bm i) by tget Hmw.
    assert (E5 : OW_t_old W' i = OW_t_old Bm i) by tget Hmw.
    assert (E6 : OW_t_reason W' i = OW_t_reason Bm i) by tget Hmw.
    assert (E7 : OW_t_state X i = OW_t_state B i) by tget H0x.
    assert (E8 : OW_t_old X i = OW_t_old B i) by tget H0x.
    assert (E9 : OW_t_reason X i = OW_t_reason B i) by tget H0x.
    rewrite P1, P2, P3, E1, E2, E3, E4, E5, E6, Q1, Q2, Q3, E7, E8, E9.
    exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))). }
  assert (Hfl' : agree_fly W').
  { apply (agree_fly_fr _ B W' Hall); [vm_compute; reflexivity | vm_compute; reflexivity | fget Hall | fget Hall
      | fget Hall | | exact Hfly].
    intros Hon. split.
    - rewrite D2. apply (ra_known _ _ Hacc). apply (b9_known _ Hst). exact (b8_state _ Hfly Hon).
    - rewrite Wms. right. reflexivity. }
  assert (Hpost : agree_core I ops W' /\ ow_got_eq W' /\ ow_step B W').
  { apply (ann1_post I ops B W' Hcore Hrm).
    - refine (wframe_rs_incl _ ann1_R B W' _ Hall). vm_compute. reflexivity.
    - exact Hfl'.
    - exact Wdk.
    - exact Wsk.
    - rewrite D1, D2. reflexivity.
    - exact Wlr'.
    - exact Wsl.
    - rewrite L1, Wms. reflexivity.
    - rewrite Wms. wcl.
    - rewrite Wms. intros H. destruct (ann1_ow H).
    - rewrite Wms. intros [H|H]; [destruct (ann1_oi H) | destruct (ann1_oc H)].
    - rewrite Wfo. exact (fun H => H).
    - rewrite Wsf, Wmf. reflexivity.
    - rewrite Wmf. left. reflexivity.
    - rewrite Wse, Wme. reflexivity.
    - rewrite Wme. right. reflexivity.
    - intros _. rewrite L2, Wmk. split; [reflexivity | exact Hkvle].
    - rewrite Wsv, Wmv. exact (b6_valid _ Hst).
    - rewrite Wmv. exact (b6_valid01 _ Hst).
    - rewrite Wmv. exact (fun H => H).
    - rewrite Wsp. destruct HW2p as [E|E]; [rewrite E, Wsp0; exact (e2_personality _ _ Hmisc) | right; exact E].
    - rewrite L3, Won. reflexivity.
    - rewrite Won. slia.
    - refine (ann1_og_t B W' (OW_n B) Hog eq_refl Hbelow _). right. split; [exact Won|].
      rewrite L4, Wot, L5, Woo', L6, Wor. split; [reflexivity | split; reflexivity].
    - rewrite Wgd', Wod'. reflexivity.
    - rewrite Wod'. slia.
    - rewrite Wgf', Wof'. reflexivity.
    - rewrite Wof'. slia. }
  destruct Hpost as (Hc' & Hog' & Hstep).
  constructor; [constructor; [exact Hc' | exact Hog' | fget Hww | fget Hww | fget Hww | fget Hww | fget Hww]
               | exact Hstep | fget Hww | intros Hwb; exfalso; exact (ann1_nowake _ Hc Hwb)].
Qed.

(* WAKING with the wake acked: the model goes ONLINE (FT:239-241) *)
Lemma ann1_us_on : forall (HL : links) I ops fr n B B2 off dp, ann1_ctx I ops fr n B B2 off dp ->
  0 <= off -> M_state B = S_WAKING -> M_e2_acked B = 1 -> ann1_concl I ops fr n B B2.
Proof.
  intros HL I ops fr n B B2 off dp Hx Hoff Hw He.
  pose proof (ann1_ctx_sw HL _ _ _ _ _ _ _ _ Hx) as Esw.
  pose proof (ann1_ctx_a30 HL _ _ _ _ _ _ _ _ Hx) as Ha30.
  pose proof Hx as [Hcore Hrm Hacc Hc Hn Ha Hbl HB2 H02 Lk Ld Mlr Eoff Hoffr Hdn Hdpr].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  destruct (ann1_room B Hrm) as (Rn & Rd & _).
  destruct (ann1_kv_facts I ops B Hcore) as (Hkvr & _ & Hkvm & _).
  destruct (ann1_mA_get B2 (OW_desk B + 1) off dp (tf_addr fr) HB2 ltac:(clear - Rd; lia) Hoffr Hdpr Ha30)
    as (HB4 & H24 & _ & _ & _ & _).
  destruct (ann1_mU_get (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) HB4) as (HX & H4x & _ & U2).
  remember (ann1_mU (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr))) as X eqn:EX.
  pose proof (wframe_trans_rs _ _ _ _ _ (wframe_trans_rs _ _ _ _ _ H02 H24) H4x) as H0x.
  pose proof (wframe_trans_rs _ _ _ _ _ H24 H4x) as H2x.
  assert (Xs : M_state X = S_WAKING) by (transitivity (M_state B); [fget H0x | exact Hw]).
  assert (Xe : M_e2_acked X = 1) by (transitivity (M_e2_acked B); [fget H0x | exact He]).
  assert (Xn : OW_n X = OW_n B) by fget H0x.
  assert (Ekv : u64 (M_last_rx X + h_ms_m (Cfg_keepalive_ms X)) = ann1_kv B).
  { assert (Xlr : M_last_rx X = g_now B) by (transitivity (M_last_rx B2); [fget H2x | exact Mlr]).
    assert (Xka : Cfg_keepalive_ms X = Cfg_keepalive_ms B) by fget H0x.
    rewrite Xlr, Xka. exact Hkvm. }
  pose proof (ann1_m_online X (ann1_kv B) (OW_n B) HX Xs Xe U2 Xn Rn Ekv) as Emo.
  destruct (ann1_mON_get X (ann1_kv B) (OW_n B) HX Hkvr Rn) as (HBm & Hxm & M1 & _).
  pose proof (wframe_trans_rs _ _ _ _ _ H0x Hxm) as H0m.
  pose proof (wframe_trans_rs _ _ _ _ _ H2x Hxm) as H2m.
  exists (ann1_mON X (ann1_kv B) (OW_n B)). split; [|split; [|split]].
  - rewrite Esw. unfold ann1_mtail. cbv beta. rewrite (proj2 (Z.leb_le 0 off) Hoff). cbv beta iota.
    rewrite <- EX. exact Emo.
  - apply (ann1_tick ops B _ Hcfg Htime).
    + right; left; exact M1.
    + transitivity (M_last_rx B2); [fget H2m | exact Mlr].
    + fget H0m.
    + fget H0m.
    + fget H0m.
    + fget H0m.
  - refine (wframe_rs_incl _ R_mod B _ _ H0m). vm_compute. reflexivity.
  - intros W HW. subst X. exact (ann1_lib_us_on HL I ops fr n B B2 off dp W Hx Hoff Hw He HW).
Qed.

(* not WAKING, or the wake not acked: e1 named, foreign cleared, nothing more (the library's part) *)
Lemma ann1_lib_us_stay : forall (HL : links) I ops fr n B B2 off dp W, ann1_ctx I ops fr n B B2 off dp ->
  0 <= off -> (M_state B <> S_WAKING \/ M_e2_acked B = 0) ->
  lib_start (ann1_mU (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr))) W (rxbuf fr n) ->
  exists W', rx_sw I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', tt) /\ rx_post_g I ops B (rxbuf fr n) W W'.
Proof.
  intros HL I ops fr n B B2 off dp W Hx Hoff Hno HW.
  pose proof (ann1_ctx_a30 HL _ _ _ _ _ _ _ _ Hx) as Ha30.
  pose proof Hx as [Hcore Hrm Hacc Hc Hn Ha Hbl HB2 H02 Lk Ld Mlr Eoff Hoffr Hdn Hdpr].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hrm) as Hog.
  destruct (ann1_room B Hrm) as (Rn & Rd & Rf & Gn & Gd & Gf).
  destruct (ann1_mA_get B2 (OW_desk B + 1) off dp (tf_addr fr) HB2 ltac:(clear - Rd; lia) Hoffr Hdpr Ha30)
    as (HB4 & H24 & A1 & A2 & A3 & A4).
  remember (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) as B4 eqn:EB4.
  destruct (ann1_mU_get B4 HB4) as (HBm & H4m0 & U1 & U2).
  remember (ann1_mU B4) as Bm eqn:EBm.
  assert (H4m : wframe (in_rs ann1_Rm) B4 Bm).
  { refine (wframe_rs_incl _ ann1_Rm B4 Bm _ H4m0). vm_compute. reflexivity. }
  destruct (ann1_wpre HL I ops fr n B B2 off dp Bm W Hx ltac:(rewrite <- EB4; exact H4m) HBm HW)
    as (HWn & Whm & Wno & Wgd & Wod & Woo & Wop & Wob & Wgn & Wgf & Wss & Wwa & Wlr & Wka & We2).
  destruct (ann1_lib_prefix HL I fr n W dp off (g_now B) (OW_desk B) Himg Hn (proj1 Ha) (ra_code _ _ Hacc) Hc Hbl
              Eoff HWn Whm Wno Wgd Wod Rd Woo Wop Hdn Wob) as (W2 & Epre & HW2n & HW2f & HW2g & HW2p).
  destruct (ann1_lU_get W2 HW2n) as (HW'n & H2w & Y1 & Y2).
  remember (ann1_lU W2) as W' eqn:EW'.
  pose proof HW as (HWf & HWk & HWm & HWl).
  pose proof (wframe_trans_rs _ _ _ _ _ HW2f H2w) as Hww.
  assert (Ys : S_state W' = M_state B) by (transitivity (S_state W); [fget Hww | exact Wss]).
  assert (Ywa : S_wake_acked W' = M_e2_acked B) by (transitivity (S_wake_acked W); [fget Hww | exact Wwa]).
  exists W'. split.
  { rewrite Epre. unfold ann1_ltail. cbv beta. rewrite (proj2 (Z.leb_le 0 off) Hoff). cbv beta iota.
    rewrite <- EW'. apply ann1_l_stay.
    destruct Hno as [H|H]; [left; rewrite Ys; exact H | right; rewrite Ywa; exact H]. }
  pose proof (wframe_trans_rs _ _ _ _ _ HWf Hww) as Hmw.
  pose proof (wframe_trans_rs _ _ _ _ _ H4m0 Hmw) as H4w.
  pose proof (wframe_trans_rs _ _ _ _ _ H24 H4w) as H2w'.
  pose proof (wframe_trans_rs _ _ _ _ _ H02 H2w') as Hall.
  pose proof (wframe_trans_rs _ _ _ _ _ H02 (wframe_trans_rs _ _ _ _ _ H24 H4m0)) as H0m.
  assert (Wdk : M_desk_known W' = 1) by (transitivity (M_desk_known B2); [fget H2w' | exact Lk]).
  assert (D1 : S_desk_mac W' = fr_src (rxbuf fr n)) by (transitivity (S_desk_mac W); [fget Hww | exact HWm]).
  assert (D2 : M_desk W' = fr_src (rxbuf fr n)) by (transitivity (M_desk B2); [fget H2w' | exact Ld]).
  assert (Wsk : S_desk_known W' = 1) by (transitivity (S_desk_known W); [fget Hww | exact HWk]).
  assert (Wlr' : M_last_rx W' = g_now B) by (transitivity (M_last_rx B2); [fget H2w' | exact Mlr]).
  assert (Wsl : S_last_rx_us W' = g_now B) by (transitivity (S_last_rx_us W); [fget Hww | exact Wlr]).
  assert (Wms : M_state W' = M_state B) by fget Hall.
  assert (Wmf : M_foreign W' = 0) by (transitivity (M_foreign Bm); [fget Hmw | exact U1]).
  assert (Wme : M_e1_us W' = 1) by (transitivity (M_e1_us Bm); [fget Hmw | exact U2]).
  assert (Wsk1 : S_next_keepalive_us W' = S_next_keepalive_us B) by fget Hall.
  assert (Wmk : M_next_ka W' = M_next_ka B) by fget Hall.
  assert (Wfo : M_fly_on W' = M_fly_on B) by fget Hall.
  assert (Wsv : S_desk_counter_valid W' = S_desk_counter_valid B) by fget Hall.
  assert (Wmv : M_desk_counter_valid W' = M_desk_counter_valid B) by fget Hall.
  assert (Wsp : S_personality W' = S_personality W2) by fget H2w.
  assert (Wsp0 : S_personality W = S_personality B) by (transitivity (S_personality Bm); [fget HWf | fget H0m]).
  assert (Won : OW_n W' = OW_n B) by fget Hall.
  assert (Wgn' : GOT_n W' = OW_n B) by (transitivity (GOT_n B); [fget Hall | exact Gn]).
  assert (Wgd' : GOT_desk W' = OW_desk B + 1) by (transitivity (GOT_desk W2); [fget H2w | exact HW2g]).
  assert (Wod' : OW_desk W' = OW_desk B + 1) by (transitivity (OW_desk B4); [fget H4w | exact A1]).
  assert (Wgf' : GOT_foreign W' = OW_foreign B) by (transitivity (GOT_foreign B); [fget Hall | exact Gf]).
  assert (Wof' : OW_foreign W' = OW_foreign B) by fget Hall.
  (* no transition: both logs are B's *)
  assert (Hbelow : forall i, 0 <= i < OW_n B ->
    GOT_t_state W' i = GOT_t_state B i /\ GOT_t_old W' i = GOT_t_old B i /\ GOT_t_reason W' i = GOT_t_reason B i /\
    OW_t_state W' i = OW_t_state B i /\ OW_t_old W' i = OW_t_old B i /\ OW_t_reason W' i = OW_t_reason B i).
  { intros i Hi. split; [tget Hall|]. split; [tget Hall|]. split; [tget Hall|].
    split; [tget Hall|]. split; [tget Hall | tget Hall]. }
  assert (Hfl' : agree_fly W').
  { apply (agree_fly_fr _ B W' Hall); [vm_compute; reflexivity | vm_compute; reflexivity | fget Hall | fget Hall
      | fget Hall | | exact Hfly].
    intros Hon. split.
    - rewrite D2. apply (ra_known _ _ Hacc). apply (b9_known _ Hst). exact (b8_state _ Hfly Hon).
    - rewrite Wms. exact (b8_state _ Hfly Hon). }
  assert (Hpost : agree_core I ops W' /\ ow_got_eq W' /\ ow_step B W').
  { apply (ann1_post I ops B W' Hcore Hrm).
    - refine (wframe_rs_incl _ ann1_R B W' _ Hall). vm_compute. reflexivity.
    - exact Hfl'.
    - exact Wdk.
    - exact Wsk.
    - rewrite D1, D2. reflexivity.
    - exact Wlr'.
    - exact Wsl.
    - rewrite Ys, Wms. reflexivity.
    - rewrite Wms. exact (b1_state_range _ Hst).
    - rewrite Wms. exact (fun H => H).
    - rewrite Wms, Wfo. exact (b9_idle _ Hst).
    - rewrite Wfo. exact (fun H => H).
    - rewrite Y1, Wmf. reflexivity.
    - rewrite Wmf. left. reflexivity.
    - rewrite Y2, Wme. reflexivity.
    - rewrite Wme. right. reflexivity.
    - intros Hr. rewrite Wsk1, Wmk. exact (conj (b5_next_ka _ Hst Hr) (c1_next_ka _ _ Htime Hr)).
    - rewrite Wsv, Wmv. exact (b6_valid _ Hst).
    - rewrite Wmv. exact (b6_valid01 _ Hst).
    - rewrite Wmv. exact (fun H => H).
    - rewrite Wsp. destruct HW2p as [E|E]; [rewrite E, Wsp0; exact (e2_personality _ _ Hmisc) | right; exact E].
    - rewrite Wgn', Won. reflexivity.
    - rewrite Won. slia.
    - refine (ann1_og_t B W' (OW_n B) Hog eq_refl Hbelow _). left. exact Won.
    - rewrite Wgd', Wod'. reflexivity.
    - rewrite Wod'. slia.
    - rewrite Wgf', Wof'. reflexivity.
    - rewrite Wof'. slia. }
  destruct Hpost as (Hc' & Hog' & Hstep).
  constructor; [constructor; [exact Hc' | exact Hog' | fget Hww | fget Hww | fget Hww | fget Hww | fget Hww]
               | exact Hstep | fget Hww | intros Hwb; exfalso; exact (ann1_nowake _ Hc Hwb)].
Qed.

(* not WAKING, or the wake not acked: the model names e1 and clears foreign only (FT:239 false) *)
Lemma ann1_us_stay : forall (HL : links) I ops fr n B B2 off dp, ann1_ctx I ops fr n B B2 off dp ->
  0 <= off -> (M_state B <> S_WAKING \/ M_e2_acked B = 0) -> ann1_concl I ops fr n B B2.
Proof.
  intros HL I ops fr n B B2 off dp Hx Hoff Hno.
  pose proof (ann1_ctx_sw HL _ _ _ _ _ _ _ _ Hx) as Esw.
  pose proof (ann1_ctx_a30 HL _ _ _ _ _ _ _ _ Hx) as Ha30.
  pose proof Hx as [Hcore Hrm Hacc Hc Hn Ha Hbl HB2 H02 Lk Ld Mlr Eoff Hoffr Hdn Hdpr].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  destruct (ann1_room B Hrm) as (_ & Rd & _).
  destruct (ann1_mA_get B2 (OW_desk B + 1) off dp (tf_addr fr) HB2 ltac:(clear - Rd; lia) Hoffr Hdpr Ha30)
    as (HB4 & H24 & _ & _ & _ & _).
  destruct (ann1_mU_get (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) HB4) as (HX & H4x & _ & _).
  pose proof (wframe_trans_rs _ _ _ _ _ (wframe_trans_rs _ _ _ _ _ H02 H24) H4x) as H0m.
  pose proof (wframe_trans_rs _ _ _ _ _ H24 H4x) as H2m.
  remember (ann1_mU (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr))) as X eqn:EX.
  assert (Xs : M_state X = M_state B) by fget H0m.
  assert (Xe : M_e2_acked X = M_e2_acked B) by fget H0m.
  exists X. split; [|split; [|split]].
  - rewrite Esw. unfold ann1_mtail. cbv beta. rewrite (proj2 (Z.leb_le 0 off) Hoff). cbv beta iota.
    rewrite <- EX. apply ann1_m_stay. destruct Hno as [H|H]; [left; rewrite Xs; exact H | right; rewrite Xe; exact H].
  - apply (ann1_tick ops B _ Hcfg Htime).
    + left; exact Xs.
    + transitivity (M_last_rx B2); [fget H2m | exact Mlr].
    + fget H0m.
    + fget H0m.
    + fget H0m.
    + fget H0m.
  - refine (wframe_rs_incl _ R_mod B _ _ H0m). vm_compute. reflexivity.
  - intros W HW. subst X. exact (ann1_lib_us_stay HL I ops fr n B B2 off dp W Hx Hoff Hno HW).
Qed.

(* ---- the e1 names another host (FT:324-328, DS:215-220) ---- *)

(* ONLINE or WAKING: both set foreign and lose the session (the library's part) *)
Lemma ann1_lib_fo_lost : forall (HL : links) I ops fr n B B2 off dp W, ann1_ctx I ops fr n B B2 off dp ->
  off < 0 -> (M_state B = S_ONLINE \/ M_state B = S_WAKING) ->
  lib_start (ann1_mL (ann1_mF (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) (OW_foreign B + 1)) (M_state B) (OW_n B))
    W (rxbuf fr n) ->
  exists W', rx_sw I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', tt) /\ rx_post_g I ops B (rxbuf fr n) W W'.
Proof.
  intros HL I ops fr n B B2 off dp W Hx Hoff Hlive HW.
  pose proof (ann1_ctx_a30 HL _ _ _ _ _ _ _ _ Hx) as Ha30.
  pose proof Hx as [Hcore Hrm Hacc Hc Hn Ha Hbl HB2 H02 Lk Ld Mlr Eoff Hoffr Hdn Hdpr].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hrm) as Hog.
  destruct (ann1_room B Hrm) as (Rn & Rd & Rf & Gn & Gd & Gf).
  assert (Hsr : - 2 ^ 31 <= M_state B < 2 ^ 31) by (pose proof (b1_state_range _ Hst) as R; clear - R; lia).
  destruct (ann1_mA_get B2 (OW_desk B + 1) off dp (tf_addr fr) HB2 ltac:(clear - Rd; lia) Hoffr Hdpr Ha30)
    as (HB4 & H24 & A1 & A2 & A3 & A4).
  remember (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) as B4 eqn:EB4.
  destruct (ann1_mF_get B4 (OW_foreign B + 1) HB4 ltac:(clear - Rf; lia)) as (HX & H4x & F1 & F2).
  remember (ann1_mF B4 (OW_foreign B + 1)) as X eqn:EX.
  destruct (ann1_mL_get X (M_state B) (OW_n B) HX Hsr Rn) as (HBm & Hxm & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  remember (ann1_mL X (M_state B) (OW_n B)) as Bm eqn:EBm.
  assert (H4m : wframe (in_rs ann1_Rm) B4 Bm).
  { refine (wframe_rs_incl _ ann1_Rm B4 Bm _ (wframe_trans_rs _ _ _ _ _ H4x Hxm)). vm_compute. reflexivity. }
  destruct (ann1_wpre HL I ops fr n B B2 off dp Bm W Hx ltac:(rewrite <- EB4; exact H4m) HBm HW)
    as (HWn & Whm & Wno & Wgd & Wod & Woo & Wop & Wob & Wgn & Wgf & Wss & Wwa & Wlr & Wka & We2).
  destruct (ann1_lib_prefix HL I fr n W dp off (g_now B) (OW_desk B) Himg Hn (proj1 Ha) (ra_code _ _ Hacc) Hc Hbl
              Eoff HWn Whm Wno Wgd Wod Rd Woo Wop Hdn Wob) as (W2 & Epre & HW2n & HW2f & HW2g & HW2p).
  pose proof HW as (HWf & HWk & HWm & HWl).
  assert (W2no : S_notify W2 = ti_notice I) by (transitivity (S_notify W); [fget HW2f | exact Wno]).
  assert (W2gf : GOT_foreign W2 = OW_foreign B) by (transitivity (GOT_foreign W); [fget HW2f | exact Wgf]).
  assert (W2ss : S_state W2 = M_state B) by (transitivity (S_state W); [fget HW2f | exact Wss]).
  assert (Lst : ((S_state W2 =? DIGINET_S_ONLINE) || (S_state W2 =? DIGINET_S_WAKING)) = true)
    by (rewrite W2ss; destruct Hlive as [T|T]; rewrite T; reflexivity).
  destruct (ann1_lF_get W2 (OW_foreign B + 1) HW2n ltac:(clear - Rf; lia)) as (HYn & H2y & Y1 & Y2).
  remember (ann1_lF W2 (OW_foreign B + 1)) as Y eqn:EY.
  pose proof (wframe_trans_rs _ _ _ _ _ HW2f H2y) as Hwy.
  assert (Yno : S_notify Y = ti_notice I) by (transitivity (S_notify W2); [fget H2y | exact W2no]).
  assert (Ygn : GOT_n Y = OW_n B) by (transitivity (GOT_n W); [fget Hwy | exact Wgn]).
  assert (Ys : S_state Y = M_state B) by (transitivity (S_state W2); [fget H2y | exact W2ss]).
  assert (Yi : S_state Y <> DIGINET_S_IDLE)
    by (rewrite Ys; clear - Hlive; unfold S_ONLINE, S_WAKING, DIGINET_S_IDLE in *; lia).
  pose proof (ann1_l_lost I (Some fr) Y (M_state B) (OW_n B) HYn Yno Ygn Rn Yi Ys) as Ell.
  destruct (ann1_lL_get Y (M_state B) (OW_n B) HYn Hsr Rn)
    as (HW'n & Hyw & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  remember (ann1_lL Y (M_state B) (OW_n B)) as W' eqn:EW'.
  exists W'. split.
  { rewrite Epre, (ann1_ltail_fo I (Some fr) W2 off _ (OW_foreign B) HW2n Hoff W2no W2gf Rf), Lst. cbv beta iota.
    rewrite <- EY. exact Ell. }
  pose proof (wframe_trans_rs _ _ _ _ _ H2y Hyw) as H2'w.
  pose proof (wframe_trans_rs _ _ _ _ _ HW2f H2'w) as Hww.
  pose proof (wframe_trans_rs _ _ _ _ _ HWf Hww) as Hmw.
  pose proof (wframe_trans_rs _ _ _ _ _ Hxm Hmw) as Hxw.
  pose proof (wframe_trans_rs _ _ _ _ _ H4x Hxw) as H4w.
  pose proof (wframe_trans_rs _ _ _ _ _ H24 H4w) as H2w.
  pose proof (wframe_trans_rs _ _ _ _ _ H02 H2w) as Hall.
  pose proof (wframe_trans_rs _ _ _ _ _ H02 (wframe_trans_rs _ _ _ _ _ H24 H4x)) as H0x.
  pose proof (wframe_trans_rs _ _ _ _ _ H0x Hxm) as H0m.
  pose proof (wframe_trans_rs _ _ _ _ _ H0m (wframe_trans_rs _ _ _ _ _ HWf Hwy)) as H0y.
  assert (Wdk : M_desk_known W' = 1) by (transitivity (M_desk_known B2); [fget H2w | exact Lk]).
  assert (D1 : S_desk_mac W' = fr_src (rxbuf fr n)) by (transitivity (S_desk_mac W); [fget Hww | exact HWm]).
  assert (D2 : M_desk W' = fr_src (rxbuf fr n)) by (transitivity (M_desk B2); [fget H2w | exact Ld]).
  assert (Wsk : S_desk_known W' = 1) by (transitivity (S_desk_known W); [fget Hww | exact HWk]).
  assert (Wlr' : M_last_rx W' = g_now B) by (transitivity (M_last_rx B2); [fget H2w | exact Mlr]).
  assert (Wsl : S_last_rx_us W' = g_now B) by (transitivity (S_last_rx_us W); [fget Hww | exact Wlr]).
  assert (Wms : M_state W' = S_IDLE) by (transitivity (M_state Bm); [fget Hmw | exact M1]).
  assert (Wmfl : M_fly_on W' = 0) by (transitivity (M_fly_on Bm); [fget Hmw | exact M2]).
  assert (Wmv : M_desk_counter_valid W' = 0) by (transitivity (M_desk_counter_valid Bm); [fget Hmw | exact M3]).
  assert (Won : OW_n W' = OW_n B + 1) by (transitivity (OW_n Bm); [fget Hmw | exact M4]).
  assert (Wot : OW_t_state W' (OW_n B) = S_IDLE) by (transitivity (OW_t_state Bm (OW_n B)); [tget Hmw | exact M5]).
  assert (Woo' : OW_t_old W' (OW_n B) = M_state B)
    by (transitivity (OW_t_old Bm (OW_n B)); [tget Hmw | exact M6]).
  assert (Wor : OW_t_reason W' (OW_n B) = R_FOREIGN)
    by (transitivity (OW_t_reason Bm (OW_n B)); [tget Hmw | exact M7]).
  assert (Wmf : M_foreign W' = 1) by (transitivity (M_foreign X); [fget Hxw | exact F1]).
  assert (Wof' : OW_foreign W' = OW_foreign B + 1) by (transitivity (OW_foreign X); [fget Hxw | exact F2]).
  assert (Wsf : S_foreign W' = 1) by (transitivity (S_foreign Y); [fget Hyw | exact Y1]).
  assert (Wgf' : GOT_foreign W' = OW_foreign B + 1) by (transitivity (GOT_foreign Y); [fget Hyw | exact Y2]).
  assert (Wse : S_e1_named_us W' = S_e1_named_us B) by fget Hall.
  assert (Wme : M_e1_us W' = M_e1_us B) by fget Hall.
  assert (Wsk1 : S_next_keepalive_us W' = S_next_keepalive_us B) by fget Hall.
  assert (Wmk : M_next_ka W' = M_next_ka B) by fget Hall.
  assert (Wsp : S_personality W' = S_personality W2) by fget H2'w.
  assert (Wsp0 : S_personality W = S_personality B) by (transitivity (S_personality Bm); [fget HWf | fget H0m]).
  assert (Wgd' : GOT_desk W' = OW_desk B + 1) by (transitivity (GOT_desk W2); [fget H2'w | exact HW2g]).
  assert (Wod' : OW_desk W' = OW_desk B + 1) by (transitivity (OW_desk B4); [fget H4w | exact A1]).
  (* below OW.n B: GOT.t through the lost notice (GOT.t[OW.n B] only) and frames, OW.t through m_set likewise *)
  assert (Hbelow : forall i, 0 <= i < OW_n B ->
    GOT_t_state W' i = GOT_t_state B i /\ GOT_t_old W' i = GOT_t_old B i /\ GOT_t_reason W' i = GOT_t_reason B i /\
    OW_t_state W' i = OW_t_state B i /\ OW_t_old W' i = OW_t_old B i /\ OW_t_reason W' i = OW_t_reason B i).
  { intros i Hi. destruct (L8 i Hi) as (P1 & P2 & P3). destruct (M8 i Hi) as (Q1 & Q2 & Q3).
    assert (E1 : GOT_t_state Y i = GOT_t_state B i) by tget H0y.
    assert (E2 : GOT_t_old Y i = GOT_t_old B i) by tget H0y.
    assert (E3 : GOT_t_reason Y i = GOT_t_reason B i) by tget H0y.
    assert (E4 : OW_t_state W' i = OW_t_state Bm i) by tget Hmw.
    assert (E5 : OW_t_old W' i = OW_t_old Bm i) by tget Hmw.
    assert (E6 : OW_t_reason W' i = OW_t_reason Bm i) by tget Hmw.
    assert (E7 : OW_t_state X i = OW_t_state B i) by tget H0x.
    assert (E8 : OW_t_old X i = OW_t_old B i) by tget H0x.
    assert (E9 : OW_t_reason X i = OW_t_reason B i) by tget H0x.
    rewrite P1, P2, P3, E1, E2, E3, E4, E5, E6, Q1, Q2, Q3, E7, E8, E9.
    exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))). }
  assert (Hfl' : agree_fly W').
  { constructor; rw_eqs W'; [reflexivity | left; reflexivity | intros H; discriminate H ..]. }
  assert (Hpost : agree_core I ops W' /\ ow_got_eq W' /\ ow_step B W').
  { apply (ann1_post I ops B W' Hcore Hrm).
    - refine (wframe_rs_incl _ ann1_R B W' _ Hall). vm_compute. reflexivity.
    - exact Hfl'.
    - exact Wdk.
    - exact Wsk.
    - rewrite D1, D2. reflexivity.
    - exact Wlr'.
    - exact Wsl.
    - rewrite L1, Wms. reflexivity.
    - rewrite Wms. wcl.
    - rewrite Wms. intros H. destruct (ann1_iw H).
    - intros _. exact Wmfl.
    - rewrite Wmfl. intros H. discriminate H.
    - rewrite Wsf, Wmf. reflexivity.
    - rewrite Wmf. right. reflexivity.
    - rewrite Wse, Wme. exact (b3_e1 _ Hst).
    - rewrite Wme. exact (b3_e1_01 _ Hst).
    - intros Hr. rewrite Wsk1, Wmk. exact (conj (b5_next_ka _ Hst Hr) (c1_next_ka _ _ Htime Hr)).
    - rewrite L3, Wmv. reflexivity.
    - rewrite Wmv. left. reflexivity.
    - rewrite Wmv. intros H. discriminate H.
    - rewrite Wsp. destruct HW2p as [E|E]; [rewrite E, Wsp0; exact (e2_personality _ _ Hmisc) | right; exact E].
    - rewrite L4, Won. reflexivity.
    - rewrite Won. slia.
    - refine (ann1_og_t B W' (OW_n B) Hog eq_refl Hbelow _). right. split; [exact Won|].
      rewrite L5, Wot, L6, Woo', L7, Wor. split; [reflexivity | split; reflexivity].
    - rewrite Wgd', Wod'. reflexivity.
    - rewrite Wod'. slia.
    - rewrite Wgf', Wof'. reflexivity.
    - rewrite Wof'. slia. }
  destruct Hpost as (Hc' & Hog' & Hstep).
  constructor; [constructor; [exact Hc' | exact Hog' | fget Hww | fget Hww | fget Hww | fget Hww | fget Hww]
               | exact Hstep | fget Hww | intros Hwb; exfalso; exact (ann1_nowake _ Hc Hwb)].
Qed.

(* ONLINE or WAKING: the model sets foreign and loses the session (FT:325-328) *)
Lemma ann1_fo_lost : forall (HL : links) I ops fr n B B2 off dp, ann1_ctx I ops fr n B B2 off dp ->
  off < 0 -> (M_state B = S_ONLINE \/ M_state B = S_WAKING) -> ann1_concl I ops fr n B B2.
Proof.
  intros HL I ops fr n B B2 off dp Hx Hoff Hlive.
  pose proof (ann1_ctx_sw HL _ _ _ _ _ _ _ _ Hx) as Esw.
  pose proof (ann1_ctx_a30 HL _ _ _ _ _ _ _ _ Hx) as Ha30.
  pose proof Hx as [Hcore Hrm Hacc Hc Hn Ha Hbl HB2 H02 Lk Ld Mlr Eoff Hoffr Hdn Hdpr].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  destruct (ann1_room B Hrm) as (Rn & Rd & Rf & _).
  assert (Hsr : - 2 ^ 31 <= M_state B < 2 ^ 31) by (pose proof (b1_state_range _ Hst) as R; clear - R; lia).
  destruct (ann1_mA_get B2 (OW_desk B + 1) off dp (tf_addr fr) HB2 ltac:(clear - Rd; lia) Hoffr Hdpr Ha30)
    as (HB4 & H24 & _ & _ & _ & _).
  remember (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) as B4 eqn:EB4.
  pose proof (wframe_trans_rs _ _ _ _ _ H02 H24) as H04.
  assert (O4 : OW_foreign B4 = OW_foreign B) by fget H04.
  assert (S4 : M_state B4 = M_state B) by fget H04.
  assert (Tst : ((M_state B4 =? S_ONLINE) || (M_state B4 =? S_WAKING)) = true)
    by (rewrite S4; destruct Hlive as [T|T]; rewrite T; reflexivity).
  destruct (ann1_mF_get B4 (OW_foreign B + 1) HB4 ltac:(clear - Rf; lia)) as (HX & H4x & _ & _).
  remember (ann1_mF B4 (OW_foreign B + 1)) as X eqn:EX.
  pose proof (wframe_trans_rs _ _ _ _ _ H04 H4x) as H0x.
  assert (Xs : M_state X = M_state B) by fget H0x.
  assert (Xn : OW_n X = OW_n B) by fget H0x.
  assert (Xi : M_state X <> S_IDLE) by (rewrite Xs; clear - Hlive; unfold S_ONLINE, S_WAKING, S_IDLE in *; lia).
  pose proof (ann1_m_lost X (M_state B) (OW_n B) HX Xn Rn Xi Xs) as Elost.
  destruct (ann1_mL_get X (M_state B) (OW_n B) HX Hsr Rn) as (HBm & Hxm & M1 & _).
  pose proof (wframe_trans_rs _ _ _ _ _ H0x Hxm) as H0m.
  pose proof (wframe_trans_rs _ _ _ _ _ (wframe_trans_rs _ _ _ _ _ H24 H4x) Hxm) as H2m.
  exists (ann1_mL X (M_state B) (OW_n B)). split; [|split; [|split]].
  - rewrite Esw, (ann1_mtail_fo B4 off (OW_foreign B) HB4 Hoff O4 Rf), Tst. cbv beta iota. rewrite <- EX. exact Elost.
  - apply (ann1_tick ops B _ Hcfg Htime).
    + right; right; exact M1.
    + transitivity (M_last_rx B2); [fget H2m | exact Mlr].
    + fget H0m.
    + fget H0m.
    + fget H0m.
    + fget H0m.
  - refine (wframe_rs_incl _ R_mod B _ _ H0m). vm_compute. reflexivity.
  - intros W HW. subst X B4. exact (ann1_lib_fo_lost HL I ops fr n B B2 off dp W Hx Hoff Hlive HW).
Qed.

(* IDLE (CLOSED is refused before the switch): both set foreign only (the library's part) *)
Lemma ann1_lib_fo_stay : forall (HL : links) I ops fr n B B2 off dp W, ann1_ctx I ops fr n B B2 off dp ->
  off < 0 -> M_state B = S_IDLE ->
  lib_start (ann1_mF (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) (OW_foreign B + 1)) W (rxbuf fr n) ->
  exists W', rx_sw I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', tt) /\ rx_post_g I ops B (rxbuf fr n) W W'.
Proof.
  intros HL I ops fr n B B2 off dp W Hx Hoff Hidle HW.
  pose proof (ann1_ctx_a30 HL _ _ _ _ _ _ _ _ Hx) as Ha30.
  pose proof Hx as [Hcore Hrm Hacc Hc Hn Ha Hbl HB2 H02 Lk Ld Mlr Eoff Hoffr Hdn Hdpr].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hrm) as Hog.
  destruct (ann1_room B Hrm) as (Rn & Rd & Rf & Gn & Gd & Gf).
  destruct (ann1_mA_get B2 (OW_desk B + 1) off dp (tf_addr fr) HB2 ltac:(clear - Rd; lia) Hoffr Hdpr Ha30)
    as (HB4 & H24 & A1 & A2 & A3 & A4).
  remember (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) as B4 eqn:EB4.
  destruct (ann1_mF_get B4 (OW_foreign B + 1) HB4 ltac:(clear - Rf; lia)) as (HBm & H4m0 & F1 & F2).
  remember (ann1_mF B4 (OW_foreign B + 1)) as Bm eqn:EBm.
  assert (H4m : wframe (in_rs ann1_Rm) B4 Bm).
  { refine (wframe_rs_incl _ ann1_Rm B4 Bm _ H4m0). vm_compute. reflexivity. }
  destruct (ann1_wpre HL I ops fr n B B2 off dp Bm W Hx ltac:(rewrite <- EB4; exact H4m) HBm HW)
    as (HWn & Whm & Wno & Wgd & Wod & Woo & Wop & Wob & Wgn & Wgf & Wss & Wwa & Wlr & Wka & We2).
  destruct (ann1_lib_prefix HL I fr n W dp off (g_now B) (OW_desk B) Himg Hn (proj1 Ha) (ra_code _ _ Hacc) Hc Hbl
              Eoff HWn Whm Wno Wgd Wod Rd Woo Wop Hdn Wob) as (W2 & Epre & HW2n & HW2f & HW2g & HW2p).
  pose proof HW as (HWf & HWk & HWm & HWl).
  assert (W2no : S_notify W2 = ti_notice I) by (transitivity (S_notify W); [fget HW2f | exact Wno]).
  assert (W2gf : GOT_foreign W2 = OW_foreign B) by (transitivity (GOT_foreign W); [fget HW2f | exact Wgf]).
  assert (W2ss : S_state W2 = M_state B) by (transitivity (S_state W); [fget HW2f | exact Wss]).
  assert (Lst : ((S_state W2 =? DIGINET_S_ONLINE) || (S_state W2 =? DIGINET_S_WAKING)) = false)
    by (rewrite W2ss, Hidle; reflexivity).
  destruct (ann1_lF_get W2 (OW_foreign B + 1) HW2n ltac:(clear - Rf; lia)) as (HW'n & H2w & Y1 & Y2).
  remember (ann1_lF W2 (OW_foreign B + 1)) as W' eqn:EW'.
  exists W'. split.
  { rewrite Epre, (ann1_ltail_fo I (Some fr) W2 off _ (OW_foreign B) HW2n Hoff W2no W2gf Rf), Lst.
    rewrite <- EW'. reflexivity. }
  pose proof (wframe_trans_rs _ _ _ _ _ HW2f H2w) as Hww.
  pose proof (wframe_trans_rs _ _ _ _ _ HWf Hww) as Hmw.
  pose proof (wframe_trans_rs _ _ _ _ _ H4m0 Hmw) as H4w.
  pose proof (wframe_trans_rs _ _ _ _ _ H24 H4w) as H2w'.
  pose proof (wframe_trans_rs _ _ _ _ _ H02 H2w') as Hall.
  pose proof (wframe_trans_rs _ _ _ _ _ H02 (wframe_trans_rs _ _ _ _ _ H24 H4m0)) as H0m.
  assert (Wdk : M_desk_known W' = 1) by (transitivity (M_desk_known B2); [fget H2w' | exact Lk]).
  assert (D1 : S_desk_mac W' = fr_src (rxbuf fr n)) by (transitivity (S_desk_mac W); [fget Hww | exact HWm]).
  assert (D2 : M_desk W' = fr_src (rxbuf fr n)) by (transitivity (M_desk B2); [fget H2w' | exact Ld]).
  assert (Wsk : S_desk_known W' = 1) by (transitivity (S_desk_known W); [fget Hww | exact HWk]).
  assert (Wlr' : M_last_rx W' = g_now B) by (transitivity (M_last_rx B2); [fget H2w' | exact Mlr]).
  assert (Wsl : S_last_rx_us W' = g_now B) by (transitivity (S_last_rx_us W); [fget Hww | exact Wlr]).
  assert (Wms : M_state W' = M_state B) by fget Hall.
  assert (Ws : S_state W' = M_state B) by (transitivity (S_state W2); [fget H2w | exact W2ss]).
  assert (Wmf : M_foreign W' = 1) by (transitivity (M_foreign Bm); [fget Hmw | exact F1]).
  assert (Wof' : OW_foreign W' = OW_foreign B + 1) by (transitivity (OW_foreign Bm); [fget Hmw | exact F2]).
  assert (Wse : S_e1_named_us W' = S_e1_named_us B) by fget Hall.
  assert (Wme : M_e1_us W' = M_e1_us B) by fget Hall.
  assert (Wsk1 : S_next_keepalive_us W' = S_next_keepalive_us B) by fget Hall.
  assert (Wmk : M_next_ka W' = M_next_ka B) by fget Hall.
  assert (Wfo : M_fly_on W' = M_fly_on B) by fget Hall.
  assert (Wsv : S_desk_counter_valid W' = S_desk_counter_valid B) by fget Hall.
  assert (Wmv : M_desk_counter_valid W' = M_desk_counter_valid B) by fget Hall.
  assert (Wsp : S_personality W' = S_personality W2) by fget H2w.
  assert (Wsp0 : S_personality W = S_personality B) by (transitivity (S_personality Bm); [fget HWf | fget H0m]).
  assert (Won : OW_n W' = OW_n B) by fget Hall.
  assert (Wgn' : GOT_n W' = OW_n B) by (transitivity (GOT_n B); [fget Hall | exact Gn]).
  assert (Wgd' : GOT_desk W' = OW_desk B + 1) by (transitivity (GOT_desk W2); [fget H2w | exact HW2g]).
  assert (Wod' : OW_desk W' = OW_desk B + 1) by (transitivity (OW_desk B4); [fget H4w | exact A1]).
  (* no transition: both logs are B's *)
  assert (Hbelow : forall i, 0 <= i < OW_n B ->
    GOT_t_state W' i = GOT_t_state B i /\ GOT_t_old W' i = GOT_t_old B i /\ GOT_t_reason W' i = GOT_t_reason B i /\
    OW_t_state W' i = OW_t_state B i /\ OW_t_old W' i = OW_t_old B i /\ OW_t_reason W' i = OW_t_reason B i).
  { intros i Hi. split; [tget Hall|]. split; [tget Hall|]. split; [tget Hall|].
    split; [tget Hall|]. split; [tget Hall | tget Hall]. }
  assert (Hfl' : agree_fly W').
  { apply (agree_fly_fr _ B W' Hall); [vm_compute; reflexivity | vm_compute; reflexivity | fget Hall | fget Hall
      | fget Hall | | exact Hfly].
    intros Hon. split.
    - rewrite D2. apply (ra_known _ _ Hacc). apply (b9_known _ Hst). exact (b8_state _ Hfly Hon).
    - rewrite Wms. exact (b8_state _ Hfly Hon). }
  assert (Hpost : agree_core I ops W' /\ ow_got_eq W' /\ ow_step B W').
  { apply (ann1_post I ops B W' Hcore Hrm).
    - refine (wframe_rs_incl _ ann1_R B W' _ Hall). vm_compute. reflexivity.
    - exact Hfl'.
    - exact Wdk.
    - exact Wsk.
    - rewrite D1, D2. reflexivity.
    - exact Wlr'.
    - exact Wsl.
    - rewrite Ws, Wms. reflexivity.
    - rewrite Wms. exact (b1_state_range _ Hst).
    - rewrite Wms. exact (fun H => H).
    - rewrite Wms, Wfo. exact (b9_idle _ Hst).
    - rewrite Wfo. exact (fun H => H).
    - rewrite Y1, Wmf. reflexivity.
    - rewrite Wmf. right. reflexivity.
    - rewrite Wse, Wme. exact (b3_e1 _ Hst).
    - rewrite Wme. exact (b3_e1_01 _ Hst).
    - intros Hr. rewrite Wsk1, Wmk. exact (conj (b5_next_ka _ Hst Hr) (c1_next_ka _ _ Htime Hr)).
    - rewrite Wsv, Wmv. exact (b6_valid _ Hst).
    - rewrite Wmv. exact (b6_valid01 _ Hst).
    - rewrite Wmv. exact (fun H => H).
    - rewrite Wsp. destruct HW2p as [E|E]; [rewrite E, Wsp0; exact (e2_personality _ _ Hmisc) | right; exact E].
    - rewrite Wgn', Won. reflexivity.
    - rewrite Won. slia.
    - refine (ann1_og_t B W' (OW_n B) Hog eq_refl Hbelow _). left. exact Won.
    - rewrite Wgd', Wod'. reflexivity.
    - rewrite Wod'. slia.
    - rewrite Y2, Wof'. reflexivity.
    - rewrite Wof'. slia. }
  destruct Hpost as (Hc' & Hog' & Hstep).
  constructor; [constructor; [exact Hc' | exact Hog' | fget Hww | fget Hww | fget Hww | fget Hww | fget Hww]
               | exact Hstep | fget Hww | intros Hwb; exfalso; exact (ann1_nowake _ Hc Hwb)].
Qed.

(* IDLE: the model sets foreign only (FT:325-326, :327 false) *)
Lemma ann1_fo_stay : forall (HL : links) I ops fr n B B2 off dp, ann1_ctx I ops fr n B B2 off dp ->
  off < 0 -> M_state B = S_IDLE -> ann1_concl I ops fr n B B2.
Proof.
  intros HL I ops fr n B B2 off dp Hx Hoff Hidle.
  pose proof (ann1_ctx_sw HL _ _ _ _ _ _ _ _ Hx) as Esw.
  pose proof (ann1_ctx_a30 HL _ _ _ _ _ _ _ _ Hx) as Ha30.
  pose proof Hx as [Hcore Hrm Hacc Hc Hn Ha Hbl HB2 H02 Lk Ld Mlr Eoff Hoffr Hdn Hdpr].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  destruct (ann1_room B Hrm) as (_ & Rd & Rf & _).
  destruct (ann1_mA_get B2 (OW_desk B + 1) off dp (tf_addr fr) HB2 ltac:(clear - Rd; lia) Hoffr Hdpr Ha30)
    as (HB4 & H24 & _ & _ & _ & _).
  remember (ann1_mA B2 (OW_desk B + 1) off dp (tf_addr fr)) as B4 eqn:EB4.
  pose proof (wframe_trans_rs _ _ _ _ _ H02 H24) as H04.
  assert (O4 : OW_foreign B4 = OW_foreign B) by fget H04.
  assert (S4 : M_state B4 = M_state B) by fget H04.
  assert (Tst : ((M_state B4 =? S_ONLINE) || (M_state B4 =? S_WAKING)) = false)
    by (rewrite S4, Hidle; reflexivity).
  destruct (ann1_mF_get B4 (OW_foreign B + 1) HB4 ltac:(clear - Rf; lia)) as (HX & H4x & _ & _).
  pose proof (wframe_trans_rs _ _ _ _ _ H04 H4x) as H0m.
  pose proof (wframe_trans_rs _ _ _ _ _ H24 H4x) as H2m.
  exists (ann1_mF B4 (OW_foreign B + 1)). split; [|split; [|split]].
  - rewrite Esw, (ann1_mtail_fo B4 off (OW_foreign B) HB4 Hoff O4 Rf), Tst. reflexivity.
  - apply (ann1_tick ops B _ Hcfg Htime).
    + left. fget H0m.
    + transitivity (M_last_rx B2); [fget H2m | exact Mlr].
    + fget H0m.
    + fget H0m.
    + fget H0m.
    + fget H0m.
  - refine (wframe_rs_incl _ R_mod B _ _ H0m). vm_compute. reflexivity.
  - intros W HW. subst B4. exact (ann1_lib_fo_stay HL I ops fr n B B2 off dp W Hx Hoff Hidle HW).
Qed.

(* ---- a body under 33 bytes: the model does nothing (FT:305-306), the library counts it ignored (DS:187-189) ---- *)

Lemma ann1_short : forall (HL : links) I ops fr n B B2, agree_core I ops B -> ow_room B -> rx_accepts B (rxbuf fr n) ->
  fr_cmd (rxbuf fr n) = DIGINET_CMD_ANNOUNCE_SESSION -> 0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  fr_body_len (rxbuf fr n) < 33 -> length B2 = WN -> wframe (in_rs (R_learn ++ [(A_M_last_rx, 8)])) B B2 ->
  M_desk_known B2 = 1 -> M_desk B2 = fr_src (rxbuf fr n) -> M_last_rx B2 = g_now B ->
  ann1_concl I ops fr n B B2.
Proof.
  intros HL I ops fr n B B2 Hcore Hrm Hacc Hc Hn Hbl HB2 H02 Lk Ld Mlr.
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  pose proof (wr_og _ Hrm) as Hog.
  destruct (ann1_room B Hrm) as (Rn & Rd & Rf & Gn & Gd & Gf).
  exists B2. split; [|split; [|split]].
  - assert (E0 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E0) = false) by (rewrite Hc; reflexivity).
    assert (E1 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E1) = true) by (rewrite Hc; reflexivity).
    assert (Bl : (fr_body_len (rxbuf fr n) <? SPEC_ANN_MIN) = true)
      by (apply Z.ltb_lt; unfold SPEC_ANN_MIN; exact Hbl).
    unfold m_rx_sw. cbv zeta. rewrite (rf_cmd _ _ Hf), (rf_body_len _ _ Hf), E0, E1, Bl. reflexivity.
  - apply (ann1_tick ops B B2 Hcfg Htime).
    + left. fget H02.
    + exact Mlr.
    + fget H02.
    + fget H02.
    + fget H02.
    + fget H02.
  - refine (wframe_rs_incl _ R_mod B B2 _ H02). vm_compute. reflexivity.
  - intros W HW. pose proof HW as (HWf & HWk & HWm & HWl).
    assert (F1 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE) = false) by (rewrite Hc; reflexivity).
    assert (F2 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE_SESSION) = true) by (rewrite Hc; reflexivity).
    assert (Ea : (ann_code (fr_cmd (rxbuf fr n)) (fr_body_len (rxbuf fr n)) =? DIGINET_OK) = false).
    { rewrite Hc. unfold ann_code. change (ann_cmd DIGINET_CMD_ANNOUNCE_SESSION) with true.
      cbv beta iota delta [negb]. rewrite (proj2 (Z.ltb_lt _ 33) Hbl). reflexivity. }
    exists (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1))). split.
    + unfold rx_sw. cbv zeta. rewrite F1, F2. change (false || true) with true. cbv beta iota.
      unfold on_announce_m. cbv zeta. rewrite Ea. reflexivity.
    + remember (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1))) as W' eqn:EW'.
      assert (HWn : length W = WN) by (eapply wframe_len; [exact HWf | exact HB2]).
      assert (HW' : wframe (in_rs [(A_S_stats_rx_ignored, 8)]) W W') by (subst W'; wfrs).
      pose proof (wframe_trans_rs _ _ _ _ _ HWf HW') as Hmw.
      pose proof (wframe_trans_rs _ _ _ _ _ H02 Hmw) as Hall.
      assert (Wdk : M_desk_known W' = 1) by (transitivity (M_desk_known B2); [fget Hmw | exact Lk]).
      assert (D1 : S_desk_mac W' = fr_src (rxbuf fr n)) by (transitivity (S_desk_mac W); [fget HW' | exact HWm]).
      assert (D2 : M_desk W' = fr_src (rxbuf fr n)) by (transitivity (M_desk B2); [fget Hmw | exact Ld]).
      assert (Wsk : S_desk_known W' = 1) by (transitivity (S_desk_known W); [fget HW' | exact HWk]).
      assert (Wlr' : M_last_rx W' = g_now B) by (transitivity (M_last_rx B2); [fget Hmw | exact Mlr]).
      assert (Wsl : S_last_rx_us W' = g_now B)
        by (transitivity (S_last_rx_us W); [fget HW' | rewrite HWl; fget H02]).
      assert (Wms : M_state W' = M_state B) by fget Hall.
      assert (Wss : S_state W' = S_state B) by fget Hall.
      assert (Wsf : S_foreign W' = S_foreign B) by fget Hall.
      assert (Wmf : M_foreign W' = M_foreign B) by fget Hall.
      assert (Wse : S_e1_named_us W' = S_e1_named_us B) by fget Hall.
      assert (Wme : M_e1_us W' = M_e1_us B) by fget Hall.
      assert (Wsk1 : S_next_keepalive_us W' = S_next_keepalive_us B) by fget Hall.
      assert (Wmk : M_next_ka W' = M_next_ka B) by fget Hall.
      assert (Wfo : M_fly_on W' = M_fly_on B) by fget Hall.
      assert (Wsv : S_desk_counter_valid W' = S_desk_counter_valid B) by fget Hall.
      assert (Wmv : M_desk_counter_valid W' = M_desk_counter_valid B) by fget Hall.
      assert (Wsp : S_personality W' = S_personality B) by fget Hall.
      assert (Won : OW_n W' = OW_n B) by fget Hall.
      assert (Wgn : GOT_n W' = OW_n B) by (transitivity (GOT_n B); [fget Hall | exact Gn]).
      assert (Wod : OW_desk W' = OW_desk B) by fget Hall.
      assert (Wgd : GOT_desk W' = OW_desk B) by (transitivity (GOT_desk B); [fget Hall | exact Gd]).
      assert (Wof : OW_foreign W' = OW_foreign B) by fget Hall.
      assert (Wgf : GOT_foreign W' = OW_foreign B) by (transitivity (GOT_foreign B); [fget Hall | exact Gf]).
      (* nothing logged: both logs are B's *)
      assert (Hbelow : forall i, 0 <= i < OW_n B ->
        GOT_t_state W' i = GOT_t_state B i /\ GOT_t_old W' i = GOT_t_old B i /\
        GOT_t_reason W' i = GOT_t_reason B i /\
        OW_t_state W' i = OW_t_state B i /\ OW_t_old W' i = OW_t_old B i /\ OW_t_reason W' i = OW_t_reason B i).
      { intros i Hi. split; [tget Hall|]. split; [tget Hall|]. split; [tget Hall|].
        split; [tget Hall|]. split; [tget Hall | tget Hall]. }
      assert (Hfl' : agree_fly W').
      { apply (agree_fly_fr _ B W' Hall); [vm_compute; reflexivity | vm_compute; reflexivity | fget Hall | fget Hall
          | fget Hall | | exact Hfly].
        intros Hon. split.
        - rewrite D2. apply (ra_known _ _ Hacc). apply (b9_known _ Hst). exact (b8_state _ Hfly Hon).
        - rewrite Wms. exact (b8_state _ Hfly Hon). }
      assert (Hpost : agree_core I ops W' /\ ow_got_eq W' /\ ow_step B W').
      { apply (ann1_post I ops B W' Hcore Hrm).
        - refine (wframe_rs_incl _ ann1_R B W' _ Hall). vm_compute. reflexivity.
        - exact Hfl'.
        - exact Wdk.
        - exact Wsk.
        - rewrite D1, D2. reflexivity.
        - exact Wlr'.
        - exact Wsl.
        - rewrite Wss, Wms. exact (b1_state _ Hst).
        - rewrite Wms. exact (b1_state_range _ Hst).
        - rewrite Wms. exact (fun H => H).
        - rewrite Wms, Wfo. exact (b9_idle _ Hst).
        - rewrite Wfo. exact (fun H => H).
        - rewrite Wsf, Wmf. exact (b3_foreign _ Hst).
        - rewrite Wmf. exact (b3_foreign01 _ Hst).
        - rewrite Wse, Wme. exact (b3_e1 _ Hst).
        - rewrite Wme. exact (b3_e1_01 _ Hst).
        - intros Hr. rewrite Wsk1, Wmk. exact (conj (b5_next_ka _ Hst Hr) (c1_next_ka _ _ Htime Hr)).
        - rewrite Wsv, Wmv. exact (b6_valid _ Hst).
        - rewrite Wmv. exact (b6_valid01 _ Hst).
        - rewrite Wmv. exact (fun H => H).
        - rewrite Wsp. exact (e2_personality _ _ Hmisc).
        - rewrite Wgn, Won. reflexivity.
        - rewrite Won. slia.
        - refine (ann1_og_t B W' (OW_n B) Hog eq_refl Hbelow _). left. exact Won.
        - rewrite Wgd, Wod. reflexivity.
        - rewrite Wod. slia.
        - rewrite Wgf, Wof. reflexivity.
        - rewrite Wof. slia. }
      destruct Hpost as (Hc' & Hog' & Hstep).
      constructor; [constructor; [exact Hc' | exact Hog' | fget HW' | fget HW' | fget HW' | fget HW' | fget HW']
                   | exact Hstep | fget HW' | intros Hwb; exfalso; exact (ann1_nowake _ Hc Hwb)].
Qed.

(* ---- the branch ---- *)

Lemma rx_e1_g : forall (HL : links), rx_branch_g cond_e1.
Proof.
  intros HL. unfold rx_branch_g. intros I ops fr n B. cbv zeta. intros Hn Ha Hpre Hacc Hc.
  unfold cond_e1 in Hc.
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  destruct Hpre as [Hcore Hka Hrm Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (HB : length B = WN) by exact Hlen.
  pose proof (rf_src_len _ _ Hf) as Hsl.
  destruct (learn_M_frame B (rxbuf fr n) HB Hsl) as [Hlf Hll].
  destruct (learn_M_desk B (rxbuf fr n) HB Hsl (b2_desk_known01 _ Hst) (ra_known _ _ Hacc)) as [Lk Ld].
  remember (learn_M B (rxbuf fr n)) as Bk eqn:EBk.
  remember (set_M_last_rx Bk (g_now B)) as B2 eqn:EB2.
  assert (HB2 : length B2 = WN) by (subst B2; wlen).
  assert (Hk2 : wframe (in_rs [(A_M_last_rx, 8)]) Bk B2) by (subst B2; wfrs).
  pose proof (wframe_trans_rs _ _ _ _ _ Hlf Hk2) as H02.
  assert (Lk2 : M_desk_known B2 = 1) by (transitivity (M_desk_known Bk); [fget Hk2 | exact Lk]).
  assert (Ld2 : M_desk B2 = fr_src (rxbuf fr n)) by (transitivity (M_desk Bk); [fget Hk2 | exact Ld]).
  assert (Mlr : M_last_rx B2 = g_now B) by (subst B2; wget).
  change (ann1_concl I ops fr n B B2).
  destruct (Z.ltb_spec (fr_body_len (rxbuf fr n)) 33) as [Hshort | Hlong].
  { exact (ann1_short HL I ops fr n B B2 Hcore Hrm Hacc Hc Hn Hshort HB2 H02 Lk2 Ld2 Mlr). }
  pose proof (ann1_find_mac_range (ann_unknown (fr_body (rxbuf fr n))) HOST) as Hoffr.
  remember (find_mac_m (ann_unknown (fr_body (rxbuf fr n))) 15 HOST) as off eqn:Eoff.
  destruct (ann1_named HL I fr n Himg Hn Hf Hlong) as (dp & Hdn & Hdpr).
  pose proof (Build_ann1_ctx I ops fr n B B2 off dp Hcore Hrm Hacc Hc Hn Ha Hlong HB2 H02 Lk2 Ld2 Mlr Eoff Hoffr
                Hdn Hdpr) as Hx.
  destruct (Z.leb_spec 0 off) as [Hoff | Hoff].
  - destruct (Z.eq_dec (M_state B) S_WAKING) as [Hw | Hw].
    + destruct (b3_e2_01 _ Hst) as [He | He].
      * exact (ann1_us_stay HL I ops fr n B B2 off dp Hx Hoff (or_intror He)).
      * exact (ann1_us_on HL I ops fr n B B2 off dp Hx Hoff Hw He).
    + exact (ann1_us_stay HL I ops fr n B B2 off dp Hx Hoff (or_introl Hw)).
  - assert (Tcase : (M_state B = S_ONLINE \/ M_state B = S_WAKING) \/ M_state B = S_IDLE).
    { pose proof (b1_state_range _ Hst) as R1. pose proof (ra_open _ _ Hacc) as R2. clear - R1 R2.
      unfold S_ONLINE, S_WAKING, S_IDLE, S_CLOSED in *. lia. }
    destruct Tcase as [Hlive | Hidle].
    + exact (ann1_fo_lost HL I ops fr n B B2 off dp Hx Hoff Hlive).
    + exact (ann1_fo_stay HL I ops fr n B B2 off dp Hx Hoff Hidle).
Qed.

Lemma rx_e1 : forall (HL : links), rx_branch cond_e1.
Proof. intros HL. exact (rx_branch_of_g cond_e1 (rx_e1_g HL)). Qed.
