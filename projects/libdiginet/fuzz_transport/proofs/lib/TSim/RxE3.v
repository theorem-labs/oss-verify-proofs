(* A frame from the desk whose command is e3 (DISCONNECT). After `M.last_rx = g_now` (FT:301) the model loses
   the session when it is ONLINE or WAKING (FT:366-369: m_lost, FT:210-215, and m_set, FT:196-207, which logs
   the transition in OW.t[OW.n]); the library, after its rx_frames / last_rx_us (DS:296-297), does the same
   (DS:309-312: session_lost, DS:160-165, and set_state, DS:79-86, whose notice, FT:937-949, logs it in
   GOT.t[GOT.n]). Both sides write IDLE, the flight off and the desk counter invalid; the two logs hold the same
   one transition. In any other state neither side moves. An unknown desk only passes the filters with e0 / e1
   (FT:292-293, DS:284-285), so here the desk is known on both sides. *)
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

Definition cond_e3 (B buf : list byte) : Prop := fr_cmd buf = DIGINET_CMD_DISCONNECT.

Lemma rxe3_iw : S_IDLE <> S_WAKING.
Proof. unfold S_IDLE, S_WAKING. discriminate. Qed.

Lemma rxe3_io : S_IDLE <> S_ONLINE.
Proof. unfold S_IDLE, S_ONLINE. discriminate. Qed.

(* the index k of the next transition: inside the log (FT:200, :942-943) and below INT_MAX (FT:205, :947) *)
Lemma rxe3_idx : forall k, 0 <= k < TRANS_MAX ->
  (k <? TRANS_MAX) = true /\ (k <? 0) = false /\ int_inc k = Some (k + 1).
Proof.
  intros k Hk. split; [apply Z.ltb_lt; lia | split; [apply Z.ltb_ge; lia |]].
  unfold int_inc. rewrite (proj2 (Z.eqb_neq k INT_MAX)) by (unfold TRANS_MAX, INT_MAX in *; lia). reflexivity.
Qed.

(* ---- the model: m_lost (FT:210-215) from a live state, OW.n = k ---- *)

Definition rxe3_mB (X : list byte) (k : Z) : list byte :=
  set_M_state (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state
    (set_M_desk_counter_valid (set_M_fly_on X 0) 0) k S_IDLE) k (M_state X)) k R_DESK_DISCONNECT) (k + 1)) S_IDLE.

(* the whole of OW.t, so that the list stays closed for any k *)
Definition rxe3_RM : list (Z * Z) :=
  [(A_M_fly_on, 4); (A_M_desk_counter_valid, 4); (A_OW_t_state 0, 12 * TRANS_MAX); (A_OW_n, 4); (A_M_state, 4)].

Lemma rxe3_m_lost : forall X k, length X = WN -> OW_n X = k -> 0 <= k < TRANS_MAX -> M_state X <> S_IDLE ->
  m_lost_m X R_DESK_DISCONNECT = Some (rxe3_mB X k, tt).
Proof.
  intros X k HX Hn Hk Hs. unfold m_lost_m, m_set_m. cbv zeta.
  assert (E1 : M_state (set_M_desk_counter_valid (set_M_fly_on X 0) 0) = M_state X) by wget.
  assert (E2 : OW_n (set_M_desk_counter_valid (set_M_fly_on X 0) 0) = k)
    by (transitivity (OW_n X); [wget | exact Hn]).
  assert (E3 : (M_state X =? S_IDLE) = false) by (apply Z.eqb_neq; exact Hs).
  destruct (rxe3_idx k Hk) as (J1 & J2 & J3).
  rewrite E1, E2, E3, J1, J2, J3. unfold rxe3_mB. reflexivity.
Qed.

(* the kit's reads and frames (wget, wfrs, wlen) decide offsets by computation, and are slow on a symbolic
   index: the lemmas below split k (and i) into their values first *)
Lemma rxe3_mB_frame : forall X k, length X = WN -> 0 <= k <= 4 ->
  wframe (in_rs rxe3_RM) X (rxe3_mB X k) /\ length (rxe3_mB X k) = WN.
Proof.
  intros X k HX Hk. assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia. clear Hk.
  unfold rxe3_mB. destruct Hc as [-> | [-> | [-> | [-> | ->]]]]; (split; [unfold rxe3_RM; wfrs | wlen]).
Qed.

Lemma rxe3_mB_get : forall X k, length X = WN -> 0 <= k <= 4 ->
  M_state (rxe3_mB X k) = S_IDLE /\ M_fly_on (rxe3_mB X k) = 0 /\ M_desk_counter_valid (rxe3_mB X k) = 0 /\
  OW_n (rxe3_mB X k) = k + 1 /\ OW_t_state (rxe3_mB X k) k = S_IDLE /\ OW_t_old (rxe3_mB X k) k = M_state X /\
  OW_t_reason (rxe3_mB X k) k = R_DESK_DISCONNECT.
Proof.
  intros X k HX Hk. assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia. clear Hk.
  unfold rxe3_mB, S_IDLE, R_DESK_DISCONNECT.
  destruct Hc as [-> | [-> | [-> | [-> | ->]]]];
    (refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
     [ solve [wget] | solve [wget] | solve [wget] | solve [wget] | solve [wget]
     | wget; apply rw_swrap_id; apply rw_s_range | solve [wget] ]).
Qed.

(* the entries below k: the model's writes miss them *)
Lemma rxe3_mB_below : forall X k i, length X = WN -> 0 <= i < k -> k <= 4 ->
  GOT_t_state (rxe3_mB X k) i = GOT_t_state X i /\ GOT_t_old (rxe3_mB X k) i = GOT_t_old X i /\
  GOT_t_reason (rxe3_mB X k) i = GOT_t_reason X i /\ OW_t_state (rxe3_mB X k) i = OW_t_state X i /\
  OW_t_old (rxe3_mB X k) i = OW_t_old X i /\ OW_t_reason (rxe3_mB X k) i = OW_t_reason X i.
Proof.
  intros X k i HX Hi Hk.
  assert (Hc : (k = 1 /\ i = 0) \/ (k = 2 /\ i = 0) \/ (k = 2 /\ i = 1) \/ (k = 3 /\ i = 0) \/ (k = 3 /\ i = 1) \/
    (k = 3 /\ i = 2) \/ (k = 4 /\ i = 0) \/ (k = 4 /\ i = 1) \/ (k = 4 /\ i = 2) \/ (k = 4 /\ i = 3)) by lia.
  clear Hi Hk. unfold rxe3_mB.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [Hc | Hc] end.
  all: destruct Hc as [-> ->]; refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); solve [wget].
Qed.

(* ---- the library: session_lost (DS:160-165) from a live state, GOT.n = k ---- *)

Definition rxe3_sW (W : list byte) (k : Z) : list byte :=
  set_GOT_n (set_GOT_t_reason (set_GOT_t_old (set_GOT_t_state
    (set_S_state (set_S_desk_counter_valid (set_S_inflight W 0) 0) DIGINET_S_IDLE)
    k DIGINET_S_IDLE) k (S_state W)) k DIGINET_R_DESK_DISCONNECT) (k + 1).

(* the whole of GOT.t, so that the list stays closed for any k *)
Definition rxe3_RS : list (Z * Z) :=
  [(A_S_inflight, 4); (A_S_desk_counter_valid, 4); (A_S_state, 4); (A_GOT_t_state 0, 12 * TRANS_MAX);
   (A_GOT_n, 4)].

(* set_state's notice (DS:83-85) reaches the harness's notice (FT:937): N_STATE, IDLE is not ONLINE (FT:948) *)
Lemma rxe3_s_lost : forall I F W k, length W = WN -> S_notify W = ti_notice I -> GOT_n W = k ->
  0 <= k < TRANS_MAX -> S_state W <> DIGINET_S_IDLE ->
  session_lost_m I F W DIGINET_R_DESK_DISCONNECT = Some (rxe3_sW W k, tt).
Proof.
  intros I F W k HW Hno Hg Hk Hs. unfold session_lost_m, set_state_m, call_notify, notice_m. cbv zeta.
  assert (E1 : S_state (set_S_desk_counter_valid (set_S_inflight W 0) 0) = S_state W) by wget.
  assert (E2 : (S_state W =? DIGINET_S_IDLE) = false) by (apply Z.eqb_neq; exact Hs).
  assert (E3 : S_notify (set_S_state (set_S_desk_counter_valid (set_S_inflight W 0) 0) DIGINET_S_IDLE)
                 = ti_notice I) by (transitivity (S_notify W); [wget | exact Hno]).
  assert (E4 : GOT_n (set_S_state (set_S_desk_counter_valid (set_S_inflight W 0) 0) DIGINET_S_IDLE) = k)
    by (transitivity (GOT_n W); [wget | exact Hg]).
  destruct (rxe3_idx k Hk) as (J1 & J2 & J3).
  rewrite E1, E2, E3, (Z.eqb_refl (ti_notice I)), E4, J1, J2, J3. unfold rxe3_sW. reflexivity.
Qed.

Lemma rxe3_sW_frame : forall W k, length W = WN -> 0 <= k <= 4 ->
  wframe (in_rs rxe3_RS) W (rxe3_sW W k) /\ length (rxe3_sW W k) = WN.
Proof.
  intros W k HW Hk. assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia. clear Hk.
  unfold rxe3_sW. destruct Hc as [-> | [-> | [-> | [-> | ->]]]]; (split; [unfold rxe3_RS; wfrs | wlen]).
Qed.

Lemma rxe3_sW_get : forall W k, length W = WN -> 0 <= k <= 4 ->
  S_state (rxe3_sW W k) = DIGINET_S_IDLE /\ S_inflight (rxe3_sW W k) = 0 /\
  S_desk_counter_valid (rxe3_sW W k) = 0 /\ GOT_n (rxe3_sW W k) = k + 1 /\
  GOT_t_state (rxe3_sW W k) k = DIGINET_S_IDLE /\ GOT_t_old (rxe3_sW W k) k = S_state W /\
  GOT_t_reason (rxe3_sW W k) k = DIGINET_R_DESK_DISCONNECT.
Proof.
  intros W k HW Hk. assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia. clear Hk.
  unfold rxe3_sW, DIGINET_S_IDLE, DIGINET_R_DESK_DISCONNECT.
  destruct Hc as [-> | [-> | [-> | [-> | ->]]]];
    (refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
     [ solve [wget] | solve [wget] | solve [wget] | solve [wget] | solve [wget]
     | wget; apply rw_swrap_id; apply rw_s_range | solve [wget] ]).
Qed.

(* the entries below k: the library's writes miss them *)
Lemma rxe3_sW_below : forall W k i, length W = WN -> 0 <= i < k -> k <= 4 ->
  GOT_t_state (rxe3_sW W k) i = GOT_t_state W i /\ GOT_t_old (rxe3_sW W k) i = GOT_t_old W i /\
  GOT_t_reason (rxe3_sW W k) i = GOT_t_reason W i /\ OW_t_state (rxe3_sW W k) i = OW_t_state W i /\
  OW_t_old (rxe3_sW W k) i = OW_t_old W i /\ OW_t_reason (rxe3_sW W k) i = OW_t_reason W i.
Proof.
  intros W k i HW Hi Hk.
  assert (Hc : (k = 1 /\ i = 0) \/ (k = 2 /\ i = 0) \/ (k = 2 /\ i = 1) \/ (k = 3 /\ i = 0) \/ (k = 3 /\ i = 1) \/
    (k = 3 /\ i = 2) \/ (k = 4 /\ i = 0) \/ (k = 4 /\ i = 1) \/ (k = 4 /\ i = 2) \/ (k = 4 /\ i = 3)) by lia.
  clear Hi Hk. unfold rxe3_sW.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [Hc | Hc] end.
  all: destruct Hc as [-> ->]; refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); solve [wget].
Qed.

(* the model's entry k: the library writes only GOT *)
Lemma rxe3_sW_ow : forall W k, length W = WN -> 0 <= k <= 4 ->
  OW_t_state (rxe3_sW W k) k = OW_t_state W k /\ OW_t_old (rxe3_sW W k) k = OW_t_old W k /\
  OW_t_reason (rxe3_sW W k) k = OW_t_reason W k.
Proof.
  intros W k HW Hk. assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia. clear Hk.
  unfold rxe3_sW. destruct Hc as [-> | [-> | [-> | [-> | ->]]]]; (refine (conj _ (conj _ _)); solve [wget]).
Qed.

(* the log entries across a frame that misses OW and GOT, at a symbolic index (read with lia) *)
Lemma rxe3_log_fr : forall rs X Y i, wframe (in_rs rs) X Y ->
  disj_rs OFF_GOT (OFF_OW + SZ_OW - OFF_GOT) rs = true -> 0 <= i < TRANS_MAX ->
  GOT_t_state Y i = GOT_t_state X i /\ GOT_t_old Y i = GOT_t_old X i /\ GOT_t_reason Y i = GOT_t_reason X i /\
  OW_t_state Y i = OW_t_state X i /\ OW_t_old Y i = OW_t_old X i /\ OW_t_reason Y i = OW_t_reason X i.
Proof.
  intros rs X Y i H Hd Hi. pose proof (ow_rs_miss rs Hd) as HR. unfold TRANS_MAX in Hi.
  unfold GOT_t_state, GOT_t_old, GOT_t_reason, OW_t_state, OW_t_old, OW_t_reason.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); (apply (wframe_s32_at _ _ _ _ H);
    [ wunf_off; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HR; revert Ha; wunf_off; intros; lia ]).
Qed.

(* OW and GOT agree in X, k = OW.n X; the model appends its transition at OW.t[k] (rxe3_mB, FT:200-206), the
   library, from a W that is the model's world outside R_start, the same one at GOT.t[k] (rxe3_sW, FT:942-947);
   every other count stays X's *)
Lemma rxe3_og : forall X W k, length X = WN -> length W = WN -> ow_got_eq X -> OW_n X = k -> 0 <= k <= 4 ->
  wframe (in_rs R_start) (rxe3_mB X k) W -> S_state W = M_state X -> ow_got_eq (rxe3_sW W k).
Proof.
  intros X W k HX HW Hog Hn Hk Hf Hs.
  destruct (rxe3_mB_frame X k HX Hk) as [F1 _].
  destruct (rxe3_sW_frame W k HW Hk) as [F2 _].
  pose proof (wframe_trans_rs _ _ _ _ _ Hf F2) as F3.
  pose proof (wframe_trans_rs _ _ _ _ _ F1 F3) as Fa.
  assert (Hd : disj_rs OFF_GOT (OFF_OW + SZ_OW - OFF_GOT) R_start = true) by (vm_compute; reflexivity).
  destruct (rxe3_mB_get X k HX Hk) as (_ & _ & _ & Mn & Mts & Mto & Mtr).
  destruct (rxe3_sW_get W k HW Hk) as (_ & _ & _ & Gn & Gts & Gto & Gtr).
  (* entries below k: X's, through the model's writes, the frame and the library's writes *)
  assert (ET : forall i, 0 <= i < k ->
    GOT_t_state (rxe3_sW W k) i = GOT_t_state X i /\ GOT_t_old (rxe3_sW W k) i = GOT_t_old X i /\
    GOT_t_reason (rxe3_sW W k) i = GOT_t_reason X i /\ OW_t_state (rxe3_sW W k) i = OW_t_state X i /\
    OW_t_old (rxe3_sW W k) i = OW_t_old X i /\ OW_t_reason (rxe3_sW W k) i = OW_t_reason X i).
  { intros i Hi.
    destruct (rxe3_sW_below W k i HW Hi (proj2 Hk)) as (S1 & S2 & S3 & S4 & S5 & S6).
    destruct (rxe3_log_fr _ _ _ i Hf Hd ltac:(unfold TRANS_MAX; lia)) as (R1 & R2 & R3 & R4 & R5 & R6).
    destruct (rxe3_mB_below X k i HX Hi (proj2 Hk)) as (M1 & M2 & M3 & M4 & M5 & M6).
    exact (conj (eq_trans S1 (eq_trans R1 M1)) (conj (eq_trans S2 (eq_trans R2 M2))
      (conj (eq_trans S3 (eq_trans R3 M3)) (conj (eq_trans S4 (eq_trans R4 M4))
      (conj (eq_trans S5 (eq_trans R5 M5)) (eq_trans S6 (eq_trans R6 M6))))))). }
  (* the model's entry k, through the frame and the library's writes *)
  destruct (rxe3_sW_ow W k HW Hk) as (K1 & K2 & K3).
  destruct (rxe3_log_fr _ _ _ k Hf Hd ltac:(unfold TRANS_MAX; lia)) as (_ & _ & _ & R4 & R5 & R6).
  pose proof (eq_trans K1 (eq_trans R4 Mts)) as Kts.
  pose proof (eq_trans K2 (eq_trans R5 Mto)) as Kto.
  pose proof (eq_trans K3 (eq_trans R6 Mtr)) as Ktr.
  assert (On : OW_n (rxe3_sW W k) = k + 1) by (transitivity (OW_n (rxe3_mB X k)); [fget F3 | exact Mn]).
  assert (C1 : GOT_e2 (rxe3_sW W k) = GOT_e2 X) by fget Fa.
  assert (C2 : OW_e2 (rxe3_sW W k) = OW_e2 X) by fget Fa.
  assert (C3 : GOT_e3 (rxe3_sW W k) = GOT_e3 X) by fget Fa.
  assert (C4 : OW_e3 (rxe3_sW W k) = OW_e3 X) by fget Fa.
  assert (C5 : GOT_acks (rxe3_sW W k) = GOT_acks X) by fget Fa.
  assert (C6 : OW_acks (rxe3_sW W k) = OW_acks X) by fget Fa.
  assert (C7 : GOT_desk (rxe3_sW W k) = GOT_desk X) by fget Fa.
  assert (C8 : OW_desk (rxe3_sW W k) = OW_desk X) by fget Fa.
  assert (C9 : GOT_foreign (rxe3_sW W k) = GOT_foreign X) by fget Fa.
  assert (C10 : OW_foreign (rxe3_sW W k) = OW_foreign X) by fget Fa.
  assert (C11 : GOT_acked (rxe3_sW W k) = GOT_acked X) by fget Fa.
  assert (C12 : OW_acked (rxe3_sW W k) = OW_acked X) by fget Fa.
  assert (C13 : GOT_ndata (rxe3_sW W k) = GOT_ndata X) by fget Fa.
  assert (C14 : OW_ndata (rxe3_sW W k) = OW_ndata X) by fget Fa.
  destruct Hog as [O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 O16 O17].
  constructor.
  - rewrite Gn, On. reflexivity.
  - rewrite On. lia.
  - intros i Hi Hi2. rewrite On in Hi.
    destruct (Z.lt_ge_cases i k) as [Hlt | Hge].
    + destruct (ET i (conj (proj1 Hi) Hlt)) as (T1 & T2 & T3 & T4 & T5 & T6).
      rewrite T1, T2, T3, T4, T5, T6. apply O3; [rewrite Hn; exact (conj (proj1 Hi) Hlt) | exact Hi2].
    + assert (E : i = k) by lia. subst i.
      rewrite Gts, Gto, Gtr, Kts, Kto, Ktr, Hs. split; [reflexivity | split; reflexivity].
  - rewrite C1, C2. exact O4.
  - rewrite C2. exact O5.
  - rewrite C3, C4. exact O6.
  - rewrite C4. exact O7.
  - rewrite C5, C6. exact O8.
  - rewrite C6. exact O9.
  - rewrite C7, C8. exact O10.
  - rewrite C8. exact O11.
  - rewrite C9, C10. exact O12.
  - rewrite C10. exact O13.
  - rewrite C11, C12. exact O14.
  - rewrite C12. exact O15.
  - rewrite C13, C14. exact O16.
  - rewrite C14. exact O17.
Qed.

Lemma rx_e3_g : forall (HL : links), rx_branch_g cond_e3.
Proof.
  intros HL. unfold rx_branch_g. intros I ops fr n B. cbv zeta. intros Hn Ha Hpre Hacc Hc.
  unfold cond_e3 in Hc.
  pose proof (rx_frame_ok HL fr n Hn (ra_code _ _ Hacc)) as Hf.
  destruct Hpre as [Hcore Hka Hroom Hfail Hsend].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (HB : length B = WN) by exact Hlen.
  (* OW and GOT agree; a transition goes in at k = OW.n = GOT.n *)
  pose proof (wr_og _ Hroom) as Hog0.
  assert (Hkr : 0 <= OW_n B <= 4) by exact (conj (proj1 (og_n_range _ Hog0)) (wr_n _ Hroom)).
  remember (OW_n B) as k eqn:Ek.
  pose proof (rf_cmd _ _ Hf) as Ecmd.
  pose proof (rf_src_len _ _ Hf) as Hsl.
  destruct (learn_M_frame B (rxbuf fr n) HB Hsl) as [Hlf Hll].
  destruct (learn_M_desk B (rxbuf fr n) HB Hsl (b2_desk_known01 _ Hst) (ra_known _ _ Hacc)) as [Lk Ld].
  remember (learn_M B (rxbuf fr n)) as Bk eqn:EBk.
  assert (E1 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E0) = false) by (rewrite Hc; reflexivity).
  assert (E2 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E1) = false) by (rewrite Hc; reflexivity).
  assert (E3 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_ACK) = false) by (rewrite Hc; reflexivity).
  assert (E4 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_DATA) = false) by (rewrite Hc; reflexivity).
  assert (E5 : (fr_cmd (rxbuf fr n) =? SPEC_CMD_E3) = true) by (rewrite Hc; reflexivity).
  assert (F1 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE) = false) by (rewrite Hc; reflexivity).
  assert (F2 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ANNOUNCE_SESSION) = false) by (rewrite Hc; reflexivity).
  assert (F3 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_ACK) = false) by (rewrite Hc; reflexivity).
  assert (F4 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_DATA) = false) by (rewrite Hc; reflexivity).
  assert (F5 : (fr_cmd (rxbuf fr n) =? DIGINET_CMD_DISCONNECT) = true) by (rewrite Hc; reflexivity).
  (* the model's world at its switch (FT:301) *)
  remember (set_M_last_rx Bk (g_now B)) as X0 eqn:EX0.
  assert (HX0 : length X0 = WN) by (subst X0; wlen).
  assert (Hk0 : wframe (in_rs [(A_M_last_rx, 8)]) Bk X0) by (subst X0; wfrs).
  pose proof (wframe_trans_rs _ _ _ _ _ Hlf Hk0) as HB0.
  assert (Mst0 : M_state X0 = M_state B) by fget HB0.
  assert (Mlr0 : M_last_rx X0 = g_now B) by (subst X0; wget).
  assert (Tcase : (M_state B = S_ONLINE \/ M_state B = S_WAKING) \/ M_state B = S_IDLE).
  { pose proof (b1_state_range _ Hst) as R1. pose proof (ra_open _ _ Hacc) as R2. clear - R1 R2.
    unfold S_ONLINE, S_WAKING, S_IDLE, S_CLOSED in *. lia. }
  destruct Tcase as [Hlive | Hidle].
  - (* ONLINE or WAKING: both sides lose the session (FT:367-368, DS:309-311) *)
    assert (Tst : ((M_state X0 =? S_ONLINE) || (M_state X0 =? S_WAKING)) = true)
      by (rewrite Mst0; destruct Hlive as [T|T]; rewrite T; reflexivity).
    assert (Hn0 : OW_n X0 = k) by (transitivity (OW_n B); [fget HB0 | symmetry; exact Ek]).
    assert (Hkt : 0 <= k < TRANS_MAX) by (clear - Hkr; unfold TRANS_MAX; lia).
    assert (HogX0 : ow_got_eq X0)
      by (apply (ow_got_eq_fr _ B X0 HB0); [vm_compute; reflexivity | exact Hog0]).
    assert (Hs0 : M_state X0 <> S_IDLE)
      by (rewrite Mst0; clear - Hlive; unfold S_ONLINE, S_WAKING, S_IDLE in *; lia).
    pose proof (rxe3_m_lost X0 k HX0 Hn0 Hkt Hs0) as Elost.
    destruct (rxe3_mB_frame X0 k HX0 Hkr) as [H0m HBm].
    destruct (rxe3_mB_get X0 k HX0 Hkr) as (Bs & Bf & Bv & Bn & _ & _ & _).
    remember (rxe3_mB X0 k) as Bm eqn:EBm.
    pose proof (wframe_trans_rs _ _ _ _ _ HB0 H0m) as HBm'.
    assert (Mcw : Cfg_wake_timeout_ms Bm = Cfg_wake_timeout_ms B) by fget HBm'.
    assert (Mco : Cfg_offline_ms Bm = Cfg_offline_ms B) by fget HBm'.
    exists Bm. split; [|split; [|split]].
    + (* FT:366-368 *)
      unfold m_rx_sw. cbv zeta. rewrite Ecmd, E1, E2, E3, E4, E5, Tst, Elost. reflexivity.
    + (* FT:373: IDLE, nothing to time out *)
      apply m_tick_quiet.
      * rewrite Bs. intros H. destruct (rxe3_iw H).
      * rewrite Bs. intros H. destruct (rxe3_io H).
      * rewrite Mcw. exact (proj2 (a1_wake_timeout _ Hcfg)).
      * rewrite Mco. exact (proj2 (a1_offline _ Hcfg)).
    + (* the model wrote only M and OW *)
      apply (wframe_rs_incl ((R_learn ++ [(A_M_last_rx, 8)]) ++ rxe3_RM) R_mod B Bm);
        [vm_compute; reflexivity | exact HBm'].
    + intros W HW.
      pose proof HW as (HWf & HWk & HWm & HWl).
      assert (HWn : length W = WN) by (eapply wframe_len; [exact HWf | exact HBm]).
      assert (SsW : S_state W = M_state B)
        by (transitivity (S_state Bm); [fget HWf | transitivity (S_state B); [fget HBm' | exact (b1_state _ Hst)]]).
      assert (NoW : S_notify W = ti_notice I)
        by (transitivity (S_notify Bm); [fget HWf | transitivity (S_notify B); [fget HBm' | exact (a3_notify _ _ Hio)]]).
      assert (GnW : GOT_n W = k)
        by (transitivity (GOT_n Bm); [fget HWf | transitivity (GOT_n B);
              [fget HBm' | rewrite (og_n _ Hog0); symmetry; exact Ek]]).
      assert (SsW' : S_state W <> DIGINET_S_IDLE)
        by (rewrite SsW; clear - Hlive; unfold S_ONLINE, S_WAKING, DIGINET_S_IDLE in *; lia).
      assert (Lst : ((S_state W =? DIGINET_S_ONLINE) || (S_state W =? DIGINET_S_WAKING)) = true)
        by (rewrite SsW; destruct Hlive as [T|T]; rewrite T; reflexivity).
      pose proof (rxe3_s_lost I (Some fr) W k HWn NoW GnW Hkt SsW') as Elib.
      destruct (rxe3_sW_frame W k HWn Hkr) as [HW' HW'n].
      destruct (rxe3_sW_get W k HWn Hkr) as (Ss & Si & Sv & _ & _ & _ & _).
      assert (Hog : ow_got_eq (rxe3_sW W k)).
      { apply (rxe3_og X0 W k HX0 HWn HogX0 Hn0 Hkr).
        - rewrite <- EBm. exact HWf.
        - rewrite SsW. symmetry. exact Mst0. }
      remember (rxe3_sW W k) as W' eqn:EW'.
      exists W'. split.
      * (* DS:309-311 *)
        unfold rx_sw. cbv zeta. rewrite F1, F2, F3, F4, F5, Lst, Elib. reflexivity.
      * pose proof (wframe_trans_rs _ _ _ _ _ HWf HW') as Hmw.
        pose proof (wframe_trans_rs _ _ _ _ _ HBm' Hmw) as Hall.
        pose proof (wframe_trans_rs _ _ _ _ _ H0m Hmw) as H0w.
        pose proof (wframe_trans_rs _ _ _ _ _ Hk0 H0w) as Hkw.
        (* the written fields *)
        assert (W1 : M_desk_known W' = 1) by (transitivity (M_desk_known Bk); [fget Hkw | exact Lk]).
        assert (W2 : M_desk W' = fr_src (rxbuf fr n)) by (transitivity (M_desk Bk); [fget Hkw | exact Ld]).
        assert (W3 : M_last_rx W' = g_now B) by (transitivity (M_last_rx X0); [fget H0w | exact Mlr0]).
        assert (W4 : S_desk_known W' = 1) by (transitivity (S_desk_known W); [fget HW' | exact HWk]).
        assert (W5 : S_desk_mac W' = fr_src (rxbuf fr n))
          by (transitivity (S_desk_mac W); [fget HW' | exact HWm]).
        assert (W6 : S_last_rx_us W' = g_now B)
          by (transitivity (S_last_rx_us W); [fget HW' | rewrite HWl; fget HBm']).
        assert (W7 : g_rx W' = g_rx W) by fget HW'.
        assert (W8 : g_rx_len W' = g_rx_len W) by fget HW'.
        assert (W9 : g_rx_times W' = g_rx_times W) by fget HW'.
        assert (W10 : g_rx_fail W' = g_rx_fail W) by fget HW'.
        assert (Wms : M_state W' = S_IDLE) by (transitivity (M_state Bm); [fget Hmw | exact Bs]).
        assert (Wmf : M_fly_on W' = 0) by (transitivity (M_fly_on Bm); [fget Hmw | exact Bf]).
        assert (Wmv : M_desk_counter_valid W' = 0)
          by (transitivity (M_desk_counter_valid Bm); [fget Hmw | exact Bv]).
        (* the fields nobody wrote *)
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
        assert (U24 : S_host_counter W' = S_host_counter B) by fget Hall.
        assert (U25 : M_host_counter W' = M_host_counter B) by fget Hall.
        assert (U39 : g_now W' = g_now B) by fget Hall.
        assert (U43 : g_fail_next W' = g_fail_next B) by fget Hall.
        assert (U44 : S_personality W' = S_personality B) by fget Hall.
        assert (Hst' : agree_st W').
        { constructor; rw_eqs W'.
          - reflexivity.
          - wcl.
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
          - reflexivity.
          - left; reflexivity.
          - intros H; discriminate H.
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
          - exact (c1_next_ka _ _ Htime).
          - intros H; destruct (rxe3_iw H).
          - intros H; destruct (rxe3_io H).
          - intros H; discriminate H. }
        assert (Hmi' : agree_misc I W').
        { constructor; rw_eqs W'; [exact (e1_fail_next _ _ Hmisc) | exact (e2_personality _ _ Hmisc)]. }
        (* the two logs gained one transition each (FT:201-206, FT:942-947); no other count moved *)
        assert (Hstep : ow_step B W').
        { assert (On : OW_n W' = k + 1) by (transitivity (OW_n Bm); [fget Hmw | exact Bn]).
          assert (C1 : OW_e2 W' = OW_e2 B) by fget Hall.
          assert (C2 : OW_e3 W' = OW_e3 B) by fget Hall.
          assert (C3 : OW_acks W' = OW_acks B) by fget Hall.
          assert (C4 : OW_desk W' = OW_desk B) by fget Hall.
          assert (C5 : OW_foreign W' = OW_foreign B) by fget Hall.
          assert (C6 : OW_acked W' = OW_acked B) by fget Hall.
          assert (C7 : OW_ndata W' = OW_ndata B) by fget Hall.
          clear - Ek On C1 C2 C3 C4 C5 C6 C7. constructor; lia. }
        constructor.
        -- constructor.
           ++ apply (agree_core_rx I ops B W' Hcore); [| exact Hst' | exact Hfl' | exact Hti' | exact Hmi'].
              eapply wframe_rx; [| exact Hall]. vm_compute. reflexivity.
           ++ exact Hog.
           ++ exact W7.
           ++ exact W8.
           ++ exact W9.
           ++ exact W10.
           ++ fget HW'.
        -- exact Hstep.
        -- fget HW'.
        -- (* only an e0 wakes *)
           unfold rx_wake_buf. intros [Hw _]. rewrite Hw, Z.eqb_refl in F1. discriminate F1.
  - (* IDLE (CLOSED is refused before the switch): neither side moves (FT:369, DS:312) *)
    assert (Tst : ((M_state X0 =? S_ONLINE) || (M_state X0 =? S_WAKING)) = false)
      by (rewrite Mst0, Hidle; reflexivity).
    assert (Ms0 : M_state X0 = S_IDLE) by (rewrite Mst0; exact Hidle).
    assert (Mcw : Cfg_wake_timeout_ms X0 = Cfg_wake_timeout_ms B) by fget HB0.
    assert (Mco : Cfg_offline_ms X0 = Cfg_offline_ms B) by fget HB0.
    exists X0. split; [|split; [|split]].
    + (* FT:366, :369 *)
      unfold m_rx_sw. cbv zeta. rewrite Ecmd, E1, E2, E3, E4, E5, Tst. reflexivity.
    + (* FT:373 *)
      apply m_tick_quiet.
      * rewrite Ms0. intros H. destruct (rxe3_iw H).
      * rewrite Ms0. intros H. destruct (rxe3_io H).
      * rewrite Mcw. exact (proj2 (a1_wake_timeout _ Hcfg)).
      * rewrite Mco. exact (proj2 (a1_offline _ Hcfg)).
    + (* the model wrote only M *)
      apply (wframe_rs_incl (R_learn ++ [(A_M_last_rx, 8)]) R_mod B X0); [vm_compute; reflexivity | exact HB0].
    + intros W HW.
      pose proof HW as (HWf & HWk & HWm & HWl).
      assert (HWn : length W = WN) by (eapply wframe_len; [exact HWf | exact HX0]).
      assert (SsW : S_state W = M_state B)
        by (transitivity (S_state X0); [fget HWf | transitivity (S_state B); [fget HB0 | exact (b1_state _ Hst)]]).
      assert (Lst : ((S_state W =? DIGINET_S_ONLINE) || (S_state W =? DIGINET_S_WAKING)) = false)
        by (rewrite SsW, Hidle; reflexivity).
      exists W. split.
      * (* DS:309, :312 *)
        unfold rx_sw. cbv zeta. rewrite F1, F2, F3, F4, F5, Lst. reflexivity.
      * pose proof (wframe_trans_rs _ _ _ _ _ HB0 HWf) as Hall.
        pose proof (wframe_trans_rs _ _ _ _ _ Hk0 HWf) as Hkw.
        (* the written fields *)
        assert (W1 : M_desk_known W = 1) by (transitivity (M_desk_known Bk); [fget Hkw | exact Lk]).
        assert (W2 : M_desk W = fr_src (rxbuf fr n)) by (transitivity (M_desk Bk); [fget Hkw | exact Ld]).
        assert (W3 : M_last_rx W = g_now B) by (transitivity (M_last_rx X0); [fget HWf | exact Mlr0]).
        assert (W6 : S_last_rx_us W = g_now B) by (rewrite HWl; fget HB0).
        clear HWl.
        (* the fields nobody wrote *)
        assert (U2 : M_state W = M_state B) by fget Hall.
        assert (U3 : S_foreign W = S_foreign B) by fget Hall.
        assert (U4 : M_foreign W = M_foreign B) by fget Hall.
        assert (U5 : S_e1_named_us W = S_e1_named_us B) by fget Hall.
        assert (U6 : M_e1_us W = M_e1_us B) by fget Hall.
        assert (U7 : S_wake_acked W = S_wake_acked B) by fget Hall.
        assert (U8 : M_e2_acked W = M_e2_acked B) by fget Hall.
        assert (U9 : S_wake_sent_us W = S_wake_sent_us B) by fget Hall.
        assert (U10 : M_wake_sent W = M_wake_sent B) by fget Hall.
        assert (U11 : S_backoff_until_us W = S_backoff_until_us B) by fget Hall.
        assert (U12 : M_backoff_until W = M_backoff_until B) by fget Hall.
        assert (U13 : g_raw W = g_raw B) by fget Hall.
        assert (U14 : S_next_keepalive_us W = S_next_keepalive_us B) by fget Hall.
        assert (U15 : M_next_ka W = M_next_ka B) by fget Hall.
        assert (U16 : S_display_sent W = S_display_sent B) by fget Hall.
        assert (U17 : M_display_sent W = M_display_sent B) by fget Hall.
        assert (U18 : S_last_display_us W = S_last_display_us B) by fget Hall.
        assert (U19 : M_last_display W = M_last_display B) by fget Hall.
        assert (U20 : S_desk_counter_valid W = S_desk_counter_valid B) by fget Hall.
        assert (U21 : M_desk_counter_valid W = M_desk_counter_valid B) by fget Hall.
        assert (U22 : S_desk_counter W = S_desk_counter B) by fget Hall.
        assert (U23 : M_desk_counter W = M_desk_counter B) by fget Hall.
        assert (U24 : S_host_counter W = S_host_counter B) by fget Hall.
        assert (U25 : M_host_counter W = M_host_counter B) by fget Hall.
        assert (U26 : M_fly_on W = M_fly_on B) by fget Hall.
        assert (U33 : M_fly_sent W = M_fly_sent B) by fget Hall.
        assert (U37 : Cfg_max_retries W = Cfg_max_retries B) by fget Hall.
        assert (U38 : Cfg_sum_mode W = Cfg_sum_mode B) by fget Hall.
        assert (U39 : g_now W = g_now B) by fget Hall.
        assert (U40 : Cfg_wake_timeout_ms W = Cfg_wake_timeout_ms B) by fget Hall.
        assert (U41 : Cfg_offline_ms W = Cfg_offline_ms B) by fget Hall.
        assert (U42 : Cfg_ack_timeout_ms W = Cfg_ack_timeout_ms B) by fget Hall.
        assert (U43 : g_fail_next W = g_fail_next B) by fget Hall.
        assert (U44 : S_personality W = S_personality B) by fget Hall.
        assert (Hst' : agree_st W).
        { constructor; rw_eqs W.
          - reflexivity.
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
        assert (Hfl' : agree_fly W).
        { apply (agree_fly_fr _ B W Hall); [vm_compute; reflexivity | vm_compute; reflexivity | exact U24
            | exact U37 | exact U38 | | exact Hfly].
          intros Hon. split.
          - rewrite W2. apply (ra_known _ _ Hacc). apply (b9_known _ Hst). exact (b8_state _ Hfly Hon).
          - rewrite U2. exact (b8_state _ Hfly Hon). }
        assert (Hti' : agree_time ops W).
        { constructor; rw_eqs W.
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
        assert (Hmi' : agree_misc I W).
        { constructor; rw_eqs W; [exact (e1_fail_next _ _ Hmisc) | exact (e2_personality _ _ Hmisc)]. }
        constructor.
        -- constructor.
           ++ apply (agree_core_rx I ops B W Hcore); [| exact Hst' | exact Hfl' | exact Hti' | exact Hmi'].
              eapply wframe_rx; [| exact Hall]. vm_compute. reflexivity.
           ++ apply (ow_got_eq_fr _ B W Hall); [vm_compute; reflexivity | exact Hog0].
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
        -- apply (ow_step_fr _ B B W Hall); [vm_compute; reflexivity | apply ow_step_refl].
        -- reflexivity.
        -- (* only an e0 wakes *)
           unfold rx_wake_buf. intros [Hw _]. rewrite Hw, Z.eqb_refl in F1. discriminate F1.
Qed.

Lemma rx_e3 : forall (HL : links), rx_branch cond_e3.
Proof. intros HL. exact (rx_branch_of_g cond_e3 (rx_e3_g HL)). Qed.
