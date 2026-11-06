(* The filters of one reception: m_rx (fuzz_transport.c:283-300, FT) and diginet_session_rx (diginet_session.c
   :268-294, DS) parse the same bytes (L1) and compare them with the same values (A2: s->cfg.host_mac = HOST;
   B2: desk_known and the desk's MAC), so they refuse a frame together or pass it together (RxFlt_filters).
   - rx_reject_g: a refused frame, or one that reaches a closed session (FT:299-300, DS:293-294), makes the model
     return 0 with M at most learnt, and the library count it ignored or learn the desk: rx_done_g, from any
     reception of the operation (rx_pre_g); rx_reject is its case rx_pre.
   - rx_accept_path_g: a frame that passes reaches m_rx's switch through k (FT:299-301) and the library's switch
     through accept (DS:293-298), from a world lib_start relates to the model's; rx_accept_path is its case
     rx_pre. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb
  TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SimLib QueueFacts SettleOk
  RxDefs RxBase RxList RxFrame RxW RxCore.
Import ListNotations.
Open Scope Z_scope.

(* the world functions stay folded for the unifier (RxW.v header); the getters unfold to them *)
Local Opaque sub upd u_at s32_at put.

(* the three tests both filters make, in the model's words (FT:285-297; DS:273-291 after RxFrame's bridges) *)
Local Abbreviation rxf_mac buf :=
  (beq_bytes (fr_src buf) HOST || (negb (beq_bytes (fr_dst buf) HOST) && negb (beq_bytes (fr_dst buf) SPEC_BCAST))).
Local Abbreviation rxf_ann buf := ((fr_cmd buf =? SPEC_CMD_E0) || (fr_cmd buf =? SPEC_CMD_E1)).
Local Abbreviation rxf_oui buf := (beq_bytes (firstn 3 (fr_src buf)) SPEC_OUI).

(* ---- small facts ---- *)

Lemma RxFlt_bool : forall b : bool, b = true \/ b = false.
Proof. intros [|]; [left | right]; reflexivity. Qed.

Lemma RxFlt_nt : negb true = false. Proof. reflexivity. Qed.
Lemma RxFlt_nf : negb false = true. Proof. reflexivity. Qed.
Lemma RxFlt_t0 : truth 0 = false. Proof. reflexivity. Qed.
Lemma RxFlt_t1 : truth 1 = true. Proof. reflexivity. Qed.
Lemma RxFlt_n0 : negb (0 =? 0) = false. Proof. reflexivity. Qed.
Lemma RxFlt_n1 : negb (1 =? 0) = true. Proof. reflexivity. Qed.
Lemma RxFlt_e10 : (1 =? 0) = false. Proof. reflexivity. Qed.
Lemma RxFlt_ok_spec : (SPEC_OK =? SPEC_OK) = true. Proof. reflexivity. Qed.
Lemma RxFlt_ok_lib : (DIGINET_OK =? DIGINET_OK) = true. Proof. reflexivity. Qed.
Lemma RxFlt_cmd0 : DIGINET_CMD_ANNOUNCE = SPEC_CMD_E0. Proof. reflexivity. Qed.
Lemma RxFlt_cmd1 : DIGINET_CMD_ANNOUNCE_SESSION = SPEC_CMD_E1. Proof. reflexivity. Qed.

Lemma RxFlt_beq_eq : forall a b, beq_bytes a b = true -> a = b.
Proof.
  intros a b H. unfold beq_bytes in H.
  destruct (list_eq_dec Z.eq_dec (zs a) (zs b)) as [E|E]; [|discriminate H].
  unfold zs in E. revert b E. induction a as [|x a IH]; intros [|y b] E; cbn in E; try discriminate E.
  - reflexivity.
  - injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | exact (IH b E2)].
Qed.

Lemma RxFlt_beq_neq : forall a b, beq_bytes a b = false -> a <> b.
Proof. intros a b H E. rewrite E in H. rewrite (rx_beq_bytes_refl b) in H. discriminate H. Qed.

(* m_rx_m's bounds on n: the read of FT:283 stays inside the heap frame *)
Lemma RxFlt_mod_flt : forall I fr B n, 0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
  m_rx_m I (Some fr) B n = m_rx_flt I fr B n.
Proof.
  intros I fr B n Hn. rewrite (m_rx_m_eq I fr B n).
  assert (E : (n <? 0) || (Z.of_nat (length (tf_bytes fr)) <? n) = false).
  { apply orb_false_intro; apply Z.ltb_ge; lia. }
  rewrite E. reflexivity.
Qed.

(* ---- the desk learnt (FT:296-297, DS:290-291) ---- *)

Lemma RxFlt_learnM_0 : forall B buf, M_desk_known B = 0 ->
  learn_M B buf = set_M_desk_known (set_M_desk B (fr_src buf)) 1.
Proof. intros B buf K. unfold learn_M. rewrite K, (Z.eqb_refl 0). reflexivity. Qed.

Lemma RxFlt_learnM_1 : forall B buf, M_desk_known B = 1 -> learn_M B buf = B.
Proof. intros B buf K. unfold learn_M. rewrite K, RxFlt_e10. reflexivity. Qed.

Lemma RxFlt_learnS_0 : forall W buf, S_desk_known W = 0 ->
  learn_S W buf = set_S_desk_known (set_S_desk_mac W (fr_src buf)) 1.
Proof. intros W buf K. unfold learn_S. rewrite K, (Z.eqb_refl 0). reflexivity. Qed.

Lemma RxFlt_learnS_1 : forall W buf, S_desk_known W = 1 -> learn_S W buf = W.
Proof. intros W buf K. unfold learn_S. rewrite K, RxFlt_e10. reflexivity. Qed.

Definition RxFlt_R_learnS : list (Z * Z) := [(A_S_desk_known, 4); (A_S_desk_mac, 6)].

Lemma RxFlt_learnS_frame : forall W buf, length W = WN -> length (fr_src buf) = 6%nat ->
  wframe (in_rs RxFlt_R_learnS) W (learn_S W buf) /\ length (learn_S W buf) = WN.
Proof.
  intros W buf HW Hs. unfold learn_S. destruct (S_desk_known W =? 0).
  - split; [wfrs | wlen].
  - split; [apply wframe_refl | exact HW].
Qed.

Lemma RxFlt_learnS_desk : forall W buf, length W = WN -> length (fr_src buf) = 6%nat ->
  (S_desk_known W = 0 \/ S_desk_known W = 1) -> (S_desk_known W = 1 -> fr_src buf = S_desk_mac W) ->
  S_desk_known (learn_S W buf) = 1 /\ S_desk_mac (learn_S W buf) = fr_src buf.
Proof.
  intros W buf HW Hs H01 Hk. unfold learn_S. destruct (Z.eqb_spec (S_desk_known W) 0) as [E|E].
  - split; wget.
  - destruct H01 as [H0|H1]; [exact (False_ind _ (E H0))|]. split; [exact H1 | symmetry; exact (Hk H1)].
Qed.

(* the library's prologue writes (DS:296-297) *)
Lemma RxFlt_pro_frame : forall X now, length X = WN ->
  wframe (in_rs [(A_S_stats_rx_frames, 8); (A_S_last_rx_us, 8)]) X
    (set_S_last_rx_us (set_S_stats_rx_frames X (u64 (S_stats_rx_frames X + 1))) now).
Proof. intros X now HX. wfrs. Qed.

(* ---- m_tick after a refusal: nothing is overdue (C2 at B) ---- *)

Lemma RxFlt_tick : forall I ops B X, agree_core I ops B -> wframe (in_rs R_learn) B X -> m_tick_m X = Some (X, tt).
Proof.
  intros I ops B X Hcore HX.
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (E1 : M_state X = M_state B) by fget HX.
  assert (E2 : M_wake_sent X = M_wake_sent B) by fget HX.
  assert (E3 : g_now X = g_now B) by fget HX.
  assert (E4 : M_last_rx X = M_last_rx B) by fget HX.
  assert (E5 : Cfg_wake_timeout_ms X = Cfg_wake_timeout_ms B) by fget HX.
  assert (E6 : Cfg_offline_ms X = Cfg_offline_ms B) by fget HX.
  apply m_tick_quiet.
  - rewrite E1, E2, E3, E5. intros Hw. split; [exact (c1_wake_sent _ _ Htime) | exact (c2_wake _ _ Htime Hw)].
  - rewrite E1, E3, E4, E6. intros Ho. split; [exact (c1_last_rx _ _ Htime) | exact (c2_online _ _ Htime Ho)].
  - rewrite E5. exact (proj2 (a1_wake_timeout _ Hcfg)).
  - rewrite E6. exact (proj2 (a1_offline _ Hcfg)).
Qed.

(* ---- rx_done_g when the library only counted, learnt, or did nothing ---- *)

Definition RxFlt_rs : list (Z * Z) := R_learn ++ R_poll ++ RxFlt_R_learnS ++ [(A_S_stats_rx_ignored, 8)].
Definition RxFlt_rq : list (Z * Z) := R_poll ++ [(A_S_stats_rx_ignored, 8)].

Lemma RxFlt_done : forall I ops B W W', agree_core I ops B -> c2_keepalive B -> ow_got_eq B ->
  wframe (in_rs RxFlt_rs) B W' -> wframe (in_rs (R_learn ++ R_poll)) B W ->
  S_desk_known W' = M_desk_known W' -> bit01 (M_desk_known W') ->
  (M_desk_known W' = 1 -> S_desk_mac W' = M_desk W') ->
  (M_state B = S_WAKING \/ M_state B = S_ONLINE -> M_desk_known W' = 1) ->
  (M_fly_on B = 1 -> M_desk W' = M_desk B) ->
  g_rx W' = g_rx W -> g_rx_len W' = g_rx_len W -> g_rx_times W' = g_rx_times W -> g_rx_fail W' = g_rx_fail W ->
  rx_done I ops 0 W W'.
Proof.
  intros I ops B W W' Hcore Hka Hog Hall HW D1 D2 D3 D4 D5 R1 R2 R3 R4.
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
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
  assert (U27 : S_last_rx_us W' = S_last_rx_us B) by fget Hall.
  assert (U28 : M_last_rx W' = M_last_rx B) by fget Hall.
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
    - exact D2.
    - exact D3.
    - exact (b3_foreign _ Hst).
    - exact (b3_foreign01 _ Hst).
    - exact (b3_e1 _ Hst).
    - exact (b3_e1_01 _ Hst).
    - exact (b3_e2 _ Hst).
    - exact (b3_e2_01 _ Hst).
    - exact (b4_wake_sent _ Hst).
    - exact (b4_last_rx _ Hst).
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
    - exact D4. }
  assert (Hfl' : agree_fly W').
  { apply (agree_fly_fr _ B W' Hall); [vm_compute; reflexivity | vm_compute; reflexivity | exact U24
      | exact U37 | exact U38 | | exact Hfly].
    intros Hon. split; [exact (D5 Hon) | rewrite U2; exact (b8_state _ Hfly Hon)]. }
  assert (Hti' : agree_time ops W').
  { constructor; rw_eqs W'.
    - exact (c_now _ _ Htime).
    - exact (c1_last_rx _ _ Htime).
    - exact (c1_wake_sent _ _ Htime).
    - exact (c1_fly_sent _ _ Htime).
    - exact (c1_last_display _ _ Htime).
    - exact (c1_backoff _ _ Htime).
    - exact (c1_next_ka _ _ Htime).
    - exact (c2_wake _ _ Htime).
    - exact (c2_online _ _ Htime).
    - exact (c2_fly _ _ Htime). }
  assert (Hmi' : agree_misc I W').
  { constructor; rw_eqs W'; [exact (e1_fail_next _ _ Hmisc) | exact (e2_personality _ _ Hmisc)]. }
  constructor.
  - apply (agree_core_rx I ops B W' Hcore); [| exact Hst' | exact Hfl' | exact Hti' | exact Hmi'].
    eapply wframe_rx; [| exact Hall]. vm_compute. reflexivity.
  - unfold c2_keepalive in Hka |- *. rw_eqs W'. exact Hka.
  - apply (ow_got_eq_fr _ B W' Hall); [vm_compute; reflexivity | exact Hog].
  - intros H. discriminate H.
  - exact R1.
  - exact R2.
  - exact R3.
  - exact R4.
  - rewrite U39. symmetry. fget HW.
Qed.

(* drain_fact (SettleOk.v) reads g_raw, M.state, M.fly_on, M.backoff_until, g_now, g_nq, g_q, the commands'
   display flags, M.display_sent, M.last_display and cfg.display_gap_us: RxFlt_rs holds none of them *)
Lemma RxFlt_drain : forall ops X Y, agree_q ops X -> wframe (in_rs RxFlt_rs) X Y -> drain_fact X -> drain_fact Y.
Proof.
  intros ops X Y HQ H HD.
  assert (Hdq : disj_rs OFF_g_q 4096 RxFlt_rs = true) by (vm_compute; reflexivity).
  assert (Hdc : disj_rs OFF_g_cmd 40960 RxFlt_rs = true) by (vm_compute; reflexivity).
  assert (Eq : forall j, 0 <= j < 1024 -> Q_at Y j = Q_at X j) by (intros j Hj; fget_in H Hdq).
  assert (Ec : forall k, 0 <= k < 1024 -> Cmd_display Y k = Cmd_display X k) by (intros k Hk; fget_in H Hdc).
  assert (E1 : g_raw Y = g_raw X) by fget H.
  assert (E2 : M_state Y = M_state X) by fget H.
  assert (E3 : M_fly_on Y = M_fly_on X) by fget H.
  assert (E4 : M_backoff_until Y = M_backoff_until X) by fget H.
  assert (E5 : g_now Y = g_now X) by fget H.
  assert (E6 : g_nq Y = g_nq X) by fget H.
  assert (E7 : M_display_sent Y = M_display_sent X) by fget H.
  assert (E8 : M_last_display Y = M_last_display X) by fget H.
  assert (E9 : Cfg_display_gap_us Y = Cfg_display_gap_us X) by fget H.
  unfold drain_fact, drain_allow in *. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9.
  intros Hr Hs Hf Hb i Hi.
  pose proof (d1_nq _ _ HQ Hr) as Hnq. destruct (d1_entry _ _ HQ Hr i Hi) as [Hqi _].
  pose proof (d3_ncmd _ _ HQ) as Hn3. pose proof (d3_ops _ _ HQ) as Hops.
  unfold QUEUE_MAX, OPS_MAX in *.
  rewrite (Eq i) by slia. rewrite (Ec (Q_at X i)) by slia.
  exact (HD Hr Hs Hf Hb i Hi).
Qed.

(* a refused reception that wrote no more than RxFlt_rs: OW / GOT, g_rx_send and the drain fact untouched *)
Lemma RxFlt_done_g : forall I ops B buf W W', agree_core I ops B ->
  wframe (in_rs RxFlt_rs) B W' -> wframe (in_rs (R_learn ++ R_poll)) B W -> rx_done I ops 0 W W' ->
  ~ rx_accepts B buf -> (rx_accepts W' buf -> rx_accepts B buf) -> rx_done_g I ops 0 B buf W W'.
Proof.
  intros I ops B buf W W' Hcore Hall HW Hd Hrej Hacc.
  constructor.
  - exact Hd.
  - apply (ow_step_fr _ B B W' Hall); [vm_compute; reflexivity | apply ow_step_refl].
  - transitivity (g_rx_send B); [fget Hall | symmetry; fget HW].
  - intros _. exact (RxFlt_drain ops B W' (ac_q _ _ _ Hcore) Hall).
  - intros Ha. exact (False_ind _ (Hrej Ha)).
  - exact Hacc.
Qed.

(* the library changed at most its rx_ignored count (DS:270, :275, :280, :287) *)
Lemma RxFlt_done_q : forall I ops B buf W W', agree_core I ops B -> c2_keepalive B -> ow_got_eq B ->
  ~ rx_accepts B buf -> wframe (in_rs RxFlt_rq) B W' -> wframe (in_rs R_poll) B W ->
  g_rx W' = g_rx W -> g_rx_len W' = g_rx_len W -> g_rx_times W' = g_rx_times W -> g_rx_fail W' = g_rx_fail W ->
  rx_done_g I ops 0 B buf W W'.
Proof.
  intros I ops B buf W W' Hcore Hka Hog Hrej Hq HW R1 R2 R3 R4.
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hqq Hmisc].
  assert (E1 : S_desk_known W' = S_desk_known B) by fget Hq.
  assert (E2 : M_desk_known W' = M_desk_known B) by fget Hq.
  assert (E3 : S_desk_mac W' = S_desk_mac B) by fget Hq.
  assert (E4 : M_desk W' = M_desk B) by fget Hq.
  assert (E5 : M_state W' = M_state B) by fget Hq.
  assert (Hall : wframe (in_rs RxFlt_rs) B W').
  { apply (wframe_rs_incl RxFlt_rq RxFlt_rs); [vm_compute; reflexivity | exact Hq]. }
  pose proof (wframe_app_r R_learn R_poll B W HW) as HW2.
  apply (RxFlt_done_g I ops B buf W W' Hcore Hall HW2); [| exact Hrej |].
  - apply (RxFlt_done I ops B W W' Hcore Hka Hog Hall HW2).
    + rewrite E1, E2. exact (b2_desk_known _ Hst).
    + rewrite E2. exact (b2_desk_known01 _ Hst).
    + rewrite E2, E3, E4. exact (b2_desk_mac _ Hst).
    + rewrite E2. exact (b9_known _ Hst).
    + intros _. exact E4.
    + exact R1.
    + exact R2.
    + exact R3.
    + exact R4.
  - (* the filters and the closed test read only M.desk_known, M.desk and M.state, which W' keeps *)
    intros Ha. exact (rx_accepts_same W' B buf Ha (eq_sym E2) (eq_sym E4) (eq_sym E5)).
Qed.

Lemma RxFlt_done_same : forall I ops B buf W, agree_core I ops B -> c2_keepalive B -> ow_got_eq B ->
  ~ rx_accepts B buf -> wframe (in_rs R_poll) B W -> rx_done_g I ops 0 B buf W W.
Proof.
  intros I ops B buf W Hc Hk Hog Hrej HW.
  apply (RxFlt_done_q I ops B buf W W Hc Hk Hog Hrej);
    [exact (wframe_app_l R_poll [(A_S_stats_rx_ignored, 8)] B W HW)
    | exact HW | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

Lemma RxFlt_done_ign : forall I ops B buf W, agree_core I ops B -> c2_keepalive B -> ow_got_eq B ->
  ~ rx_accepts B buf -> wframe (in_rs R_poll) B W ->
  rx_done_g I ops 0 B buf W (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1))).
Proof.
  intros I ops B buf W Hc Hk Hog Hrej HW.
  assert (HB : length B = WN) by exact (ac_len _ _ _ Hc).
  assert (HWn : length W = WN) by (eapply wframe_len; [exact HW | exact HB]).
  assert (H1 : wframe (in_rs [(A_S_stats_rx_ignored, 8)]) W
                 (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1)))) by wfrs.
  apply (RxFlt_done_q I ops B buf W _ Hc Hk Hog Hrej (wframe_trans_rs _ _ _ _ _ HW H1) HW); wget.
Qed.

(* ---- the filters, both sides ---- *)

(* the frame passes the source, destination and desk filters (FT:285-297, DS:273-291) *)
Record RxFlt_pass (B buf : list byte) : Prop := {
  fp_src : beq_bytes (fr_src buf) HOST = false;
  fp_dst : beq_bytes (fr_dst buf) HOST = true \/ beq_bytes (fr_dst buf) SPEC_BCAST = true;
  fp_known : M_desk_known B = 1 -> fr_src buf = M_desk B;
  fp_unknown : M_desk_known B = 0 -> ann_cmd (fr_cmd buf) = true /\ oui_of (fr_src buf) = true;
}.

(* a parsed frame: both sides refuse it (the model returns 0 unchanged, the library returns OK, counting it
   ignored or not), or both pass it to their closed test, the model to k with the desk learnt (FT:296-299), the
   library to accept with the desk learnt (DS:290-293) *)
Lemma RxFlt_filters : forall (HL : links) I ops fr n B,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) -> agree_core I ops B -> fr_code (rxbuf fr n) = DIGINET_OK ->
  (~ RxFlt_pass B (rxbuf fr n) /\ m_rx_m I (Some fr) B n = Some (B, 0) /\
   forall W now, wframe (in_rs (R_mod ++ R_poll)) B W ->
     diginet_session_rx_m I (Some fr) W (rxbuf fr n) now = Some (W, DIGINET_OK) \/
     diginet_session_rx_m I (Some fr) W (rxbuf fr n) now = rx_ignored W) \/
  (RxFlt_pass B (rxbuf fr n) /\ m_rx_m I (Some fr) B n = m_rx_k I fr n (learn_M B (rxbuf fr n)) /\
   forall W now, wframe (in_rs (R_mod ++ R_poll)) B W ->
     diginet_session_rx_m I (Some fr) W (rxbuf fr n) now =
       rx_accept I (Some fr) (learn_S W (rxbuf fr n)) (rxbuf fr n) now).
Proof.
  intros HL I ops fr n B Hn Hcore Hc.
  pose proof (rx_frame_ok HL fr n Hn Hc) as Hf.
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (HB : length B = WN) by exact Hlen.
  assert (LH : length HOST = 6%nat) by reflexivity.
  assert (LS : length SPEC_BCAST = 6%nat) by reflexivity.
  assert (LM : length (S_desk_mac B) = 6%nat).
  { unfold S_desk_mac. apply length_sub; [wnum | rewrite HB; wnum]. }
  (* the model's filters (FT:283-297) *)
  assert (EM : m_rx_m I (Some fr) B n =
    if rxf_mac (rxbuf fr n) then Some (B, 0)
    else if truth (M_desk_known B) then
      (if beq_bytes (fr_src (rxbuf fr n)) (M_desk B) then m_rx_k I fr n B else Some (B, 0))
    else if negb (rxf_ann (rxbuf fr n)) then Some (B, 0)
    else if negb (rxf_oui (rxbuf fr n)) then Some (B, 0)
    else m_rx_k I fr n (set_M_desk_known (set_M_desk B (fr_src (rxbuf fr n))) 1)).
  { rewrite (RxFlt_mod_flt I fr B n Hn). unfold m_rx_flt. cbv zeta.
    rewrite (rf_code _ _ Hf), (rf_src _ _ Hf), (rf_dst _ _ Hf), (rf_cmd _ _ Hf), (rf_src_bytes _ _ Hf),
      (rf_dst_bytes _ _ Hf), RxFlt_ok_spec, RxFlt_nt.
    cbv iota. reflexivity. }
  (* the library's filters (DS:268-291) on any world that is B outside M, OW, GOT and the poll's fields *)
  assert (EL : forall W now, wframe (in_rs (R_mod ++ R_poll)) B W ->
    diginet_session_rx_m I (Some fr) W (rxbuf fr n) now =
    if rxf_mac (rxbuf fr n) then rx_ignored W
    else if negb (M_desk_known B =? 0) then
      (if negb (beq_bytes (fr_src (rxbuf fr n)) (S_desk_mac B)) then rx_ignored W
       else rx_accept I (Some fr) W (rxbuf fr n) now)
    else if negb (rxf_ann (rxbuf fr n)) then Some (W, DIGINET_OK)
    else if negb (rxf_oui (rxbuf fr n)) then rx_ignored W
    else rx_accept I (Some fr) (set_S_desk_known (set_S_desk_mac W (fr_src (rxbuf fr n))) 1) (rxbuf fr n) now).
  { intros W now HW.
    assert (Wh : S_cfg_host_mac W = HOST).
    { transitivity (S_cfg_host_mac B); [fget HW | exact (a2_host_mac _ Hcfg)]. }
    assert (Wk : S_desk_known W = M_desk_known B).
    { transitivity (S_desk_known B); [fget HW | exact (b2_desk_known _ Hst)]. }
    assert (Wm : S_desk_mac W = S_desk_mac B) by fget HW.
    rewrite (diginet_session_rx_m_eq I (Some fr) W (rxbuf fr n) now). cbv zeta.
    rewrite Wh, Wk, Wm, Hc, RxFlt_ok_lib, RxFlt_nt. cbv iota.
    rewrite (rx_memeq_src fr n (S_desk_mac B) Hn Hc LM), (rx_memeq_src fr n HOST Hn Hc LH),
      (rx_memeq_dst fr n HOST Hn Hc LH), rx_broadcast, (rx_memeq_dst fr n SPEC_BCAST Hn Hc LS), RxFlt_cmd0,
      RxFlt_cmd1, (rx_oui HL fr n Hn Hc).
    reflexivity. }
  destruct (RxFlt_bool (rxf_mac (rxbuf fr n))) as [T1|T1].
  - (* our own frame, or not to us (FT:285-287, DS:273-277) *)
    left. split; [|split].
    + intros [P1 P2 _ _]. destruct (proj1 (orb_true_iff _ _) T1) as [E|E].
      * rewrite P1 in E. discriminate E.
      * destruct (proj1 (andb_true_iff _ _) E) as [Ea Eb].
        destruct P2 as [P2|P2]; [rewrite P2 in Ea; discriminate Ea | rewrite P2 in Eb; discriminate Eb].
    + rewrite EM, T1. cbv iota. reflexivity.
    + intros W now HW. right. rewrite (EL W now HW), T1. cbv iota. reflexivity.
  - destruct (proj1 (orb_false_iff _ _) T1) as [P1 T1x].
    assert (P2 : beq_bytes (fr_dst (rxbuf fr n)) HOST = true \/ beq_bytes (fr_dst (rxbuf fr n)) SPEC_BCAST = true).
    { destruct (proj1 (andb_false_iff _ _) T1x) as [E|E]; [left | right]; apply negb_false_iff; exact E. }
    destruct (b2_desk_known01 _ Hst) as [K|K].
    + (* the desk unknown: an announce from a Digidesign MAC is learnt (FT:291-298, DS:283-292) *)
      destruct (RxFlt_bool (rxf_ann (rxbuf fr n))) as [Tc|Tc].
      * destruct (RxFlt_bool (rxf_oui (rxbuf fr n))) as [To|To].
        -- right. split; [|split].
           ++ refine (Build_RxFlt_pass B (rxbuf fr n) P1 P2 _ _).
              ** intros K1. rewrite K in K1. discriminate K1.
              ** intros _. split.
                 --- unfold ann_cmd. unfold SPEC_CMD_E0, SPEC_CMD_E1 in Tc. exact Tc.
                 --- rewrite (rx_oui HL fr n Hn Hc). exact To.
           ++ rewrite EM, T1, K, RxFlt_t0, Tc, To, RxFlt_nt, (RxFlt_learnM_0 B (rxbuf fr n) K).
              cbv iota. reflexivity.
           ++ intros W now HW.
              assert (Wk : S_desk_known W = 0).
              { transitivity (M_desk_known B); [| exact K].
                transitivity (S_desk_known B); [fget HW | exact (b2_desk_known _ Hst)]. }
              rewrite (EL W now HW), T1, K, RxFlt_n0, Tc, To, RxFlt_nt, (RxFlt_learnS_0 W (rxbuf fr n) Wk).
              cbv iota. reflexivity.
        -- left. split; [|split].
           ++ intros [_ _ _ P4]. destruct (P4 K) as [_ Po]. rewrite (rx_oui HL fr n Hn Hc), To in Po.
              discriminate Po.
           ++ rewrite EM, T1, K, RxFlt_t0, Tc, To, RxFlt_nt, RxFlt_nf. cbv iota. reflexivity.
           ++ intros W now HW. right. rewrite (EL W now HW), T1, K, RxFlt_n0, Tc, To, RxFlt_nt, RxFlt_nf.
              cbv iota. reflexivity.
      * left. split; [|split].
        -- intros [_ _ _ P4]. destruct (P4 K) as [Pa _]. unfold ann_cmd in Pa.
           unfold SPEC_CMD_E0, SPEC_CMD_E1 in Tc. rewrite Tc in Pa. discriminate Pa.
        -- rewrite EM, T1, K, RxFlt_t0, Tc, RxFlt_nf. cbv iota. reflexivity.
        -- intros W now HW. left. rewrite (EL W now HW), T1, K, RxFlt_n0, Tc, RxFlt_nf. cbv iota. reflexivity.
    + (* the desk known: only its frames pass (FT:288-290, DS:278-282) *)
      destruct (RxFlt_bool (beq_bytes (fr_src (rxbuf fr n)) (M_desk B))) as [Td|Td].
      * right. split; [|split].
        -- refine (Build_RxFlt_pass B (rxbuf fr n) P1 P2 _ _).
           ++ intros _. exact (RxFlt_beq_eq _ _ Td).
           ++ intros K0. rewrite K in K0. discriminate K0.
        -- rewrite EM, T1, K, RxFlt_t1, Td, (RxFlt_learnM_1 B (rxbuf fr n) K). cbv iota. reflexivity.
        -- intros W now HW.
           assert (Wk : S_desk_known W = 1).
           { transitivity (M_desk_known B); [| exact K].
             transitivity (S_desk_known B); [fget HW | exact (b2_desk_known _ Hst)]. }
           rewrite (EL W now HW), T1, K, RxFlt_n1, (b2_desk_mac _ Hst K), Td, RxFlt_nt,
             (RxFlt_learnS_1 W (rxbuf fr n) Wk).
           cbv iota. reflexivity.
      * left. split; [|split].
        -- intros [_ _ P3 _]. rewrite (P3 K), (rx_beq_bytes_refl (M_desk B)) in Td. discriminate Td.
        -- rewrite EM, T1, K, RxFlt_t1, Td. cbv iota. reflexivity.
        -- intros W now HW. right.
           rewrite (EL W now HW), T1, K, RxFlt_n1, (b2_desk_mac _ Hst K), Td, RxFlt_nf. cbv iota. reflexivity.
Qed.

(* ---- the three statements ---- *)

Lemma rx_accepts_dec : forall B buf, rx_accepts B buf \/ ~ rx_accepts B buf.
Proof.
  intros B buf.
  destruct (Z.eq_dec (fr_code buf) DIGINET_OK) as [H1|H1]; [| right; intros H; exact (H1 (ra_code _ _ H))].
  destruct (beq_bytes (fr_src buf) HOST) eqn:H2;
    [right; intros H; rewrite (ra_src _ _ H) in H2; discriminate H2 |].
  assert (H3 : (beq_bytes (fr_dst buf) HOST = true \/ beq_bytes (fr_dst buf) SPEC_BCAST = true) \/
               ~ (beq_bytes (fr_dst buf) HOST = true \/ beq_bytes (fr_dst buf) SPEC_BCAST = true)).
  { destruct (beq_bytes (fr_dst buf) HOST); [left; left; reflexivity |].
    destruct (beq_bytes (fr_dst buf) SPEC_BCAST); [left; right; reflexivity |].
    right; intros [E|E]; discriminate E. }
  destruct H3 as [H3|H3]; [| right; intros H; exact (H3 (ra_dst _ _ H))].
  assert (H4 : (M_desk_known B = 1 -> fr_src buf = M_desk B) \/ ~ (M_desk_known B = 1 -> fr_src buf = M_desk B)).
  { destruct (Z.eq_dec (M_desk_known B) 1) as [K|K]; [| left; intros K'; exact (False_ind _ (K K'))].
    destruct (RxFlt_bool (beq_bytes (fr_src buf) (M_desk B))) as [E|E].
    - left; intros _; exact (RxFlt_beq_eq _ _ E).
    - right; intros H; exact (RxFlt_beq_neq _ _ E (H K)). }
  destruct H4 as [H4|H4]; [| right; intros H; exact (H4 (ra_known _ _ H))].
  assert (H5 : (M_desk_known B = 0 -> ann_cmd (fr_cmd buf) = true /\ oui_of (fr_src buf) = true) \/
               ~ (M_desk_known B = 0 -> ann_cmd (fr_cmd buf) = true /\ oui_of (fr_src buf) = true)).
  { destruct (Z.eq_dec (M_desk_known B) 0) as [K|K]; [| left; intros K'; exact (False_ind _ (K K'))].
    destruct (ann_cmd (fr_cmd buf)); [| right; intros H; destruct (H K) as [E _]; discriminate E].
    destruct (oui_of (fr_src buf)); [left; intros _; split; reflexivity |].
    right; intros H; destruct (H K) as [_ E]; discriminate E. }
  destruct H5 as [H5|H5]; [| right; intros H; exact (H5 (ra_unknown _ _ H))].
  destruct (Z.eq_dec (M_state B) S_CLOSED) as [H6|H6]; [right; intros H; exact (ra_open _ _ H H6) |].
  left. exact (Build_rx_accepts B buf H1 H2 H3 H4 H5 H6).
Qed.

(* the frame is refused by the filters, or the session is closed: neither side does more than count or learn;
   any reception of the operation (rx_pre_g: OW and GOT agree, not necessarily zero) *)
Lemma rx_reject_g : forall (HL : links) I ops fr n B,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) -> rx_pre_g I ops B (rxbuf fr n) -> ~ rx_accepts B (rxbuf fr n) ->
  exists Bx, m_rx_m I (Some fr) B n = Some (Bx, 0) /\ m_tick_m Bx = Some (Bx, tt) /\ wframe (in_rs R_mod) B Bx /\
    forall W, wframe (in_rs R_poll) Bx W ->
      exists W' r, diginet_session_rx_m I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', r) /\
        rx_done_g I ops 0 B (rxbuf fr n) W W'.
Proof.
  intros HL I ops fr n B Hn Hpre Hacc.
  destruct Hpre as [Hcore Hka Hroom _ _].
  pose proof (wr_og _ Hroom) as Hog.
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (HB : length B = WN) by exact Hlen.
  pose proof (RxFlt_tick I ops B B Hcore (wframe_refl _ B)) as Htk.
  destruct (Z.eq_dec (fr_code (rxbuf fr n)) DIGINET_OK) as [Hc|Hc].
  2:{ (* the parse refused (FT:283-284, DS:268-272) *)
    exists B. split; [|split; [exact Htk | split; [apply wframe_refl |]]].
    - rewrite (RxFlt_mod_flt I fr B n Hn). unfold m_rx_flt. cbv zeta.
      assert (E : (sf_code (spec_read_frame (zs (tf_bytes fr)) n) =? SPEC_OK) = false).
      { apply Z.eqb_neq. exact (rx_frame_bad HL fr n Hn Hc). }
      rewrite E, RxFlt_nf. cbv iota. reflexivity.
    - intros W HW. exists (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1))), (fr_code (rxbuf fr n)).
      split.
      + rewrite (diginet_session_rx_m_eq I (Some fr) W (rxbuf fr n) (g_now B)).
        assert (E : (fr_code (rxbuf fr n) =? DIGINET_OK) = false) by (apply Z.eqb_neq; exact Hc).
        rewrite E, RxFlt_nf. cbv iota. reflexivity.
      + exact (RxFlt_done_ign I ops B (rxbuf fr n) W Hcore Hka Hog Hacc HW). }
  pose proof (rx_frame_ok HL fr n Hn Hc) as Hf.
  pose proof (rf_src_len _ _ Hf) as Hsl.
  destruct (RxFlt_filters HL I ops fr n B Hn Hcore Hc) as [(Hnp & Em & El) | (Hp & Em & El)].
  - (* refused by a filter *)
    exists B. split; [exact Em|]. split; [exact Htk|]. split; [apply wframe_refl|].
    intros W HW.
    pose proof (wframe_app_r R_mod R_poll B W HW) as HW2.
    destruct (El W (g_now B) HW2) as [E|E].
    + exists W, DIGINET_OK.
      split; [exact E | exact (RxFlt_done_same I ops B (rxbuf fr n) W Hcore Hka Hog Hacc HW)].
    + exists (set_S_stats_rx_ignored W (u64 (S_stats_rx_ignored W + 1))), DIGINET_OK.
      split; [exact E | exact (RxFlt_done_ign I ops B (rxbuf fr n) W Hcore Hka Hog Hacc HW)].
  - (* passed: the session is closed (FT:299-300, DS:293-294) *)
    destruct Hp as [P1 P2 P3 P4].
    assert (Hcl : M_state B = S_CLOSED).
    { destruct (Z.eq_dec (M_state B) S_CLOSED) as [H|H]; [exact H|].
      exfalso. apply Hacc. exact (Build_rx_accepts B (rxbuf fr n) Hc P1 P2 P3 P4 H). }
    destruct (learn_M_frame B (rxbuf fr n) HB Hsl) as [Hlf Hll].
    destruct (learn_M_desk B (rxbuf fr n) HB Hsl (b2_desk_known01 _ Hst) P3) as [Lk Ld].
    exists (learn_M B (rxbuf fr n)). split; [|split; [|split]].
    + rewrite Em. unfold m_rx_k.
      assert (E : (M_state (learn_M B (rxbuf fr n)) =? S_CLOSED) = true).
      { apply Z.eqb_eq. transitivity (M_state B); [fget Hlf | exact Hcl]. }
      rewrite E. cbv iota. reflexivity.
    + exact (RxFlt_tick I ops B _ Hcore Hlf).
    + apply (wframe_rs_incl R_learn R_mod); [vm_compute; reflexivity | exact Hlf].
    + intros W HW.
      pose proof (wframe_trans_rs _ _ _ _ _ Hlf HW) as HBW.
      assert (HBW2 : wframe (in_rs (R_mod ++ R_poll)) B W).
      { apply (wframe_rs_incl (R_learn ++ R_poll)); [vm_compute; reflexivity | exact HBW]. }
      assert (HWn : length W = WN) by (eapply wframe_len; [exact HW | exact Hll]).
      destruct (RxFlt_learnS_frame W (rxbuf fr n) HWn Hsl) as [HlS HlSn].
      assert (Wk : S_desk_known W = M_desk_known B).
      { transitivity (S_desk_known B); [fget HBW | exact (b2_desk_known _ Hst)]. }
      assert (W01 : S_desk_known W = 0 \/ S_desk_known W = 1).
      { rewrite Wk. exact (b2_desk_known01 _ Hst). }
      assert (Wm : S_desk_known W = 1 -> fr_src (rxbuf fr n) = S_desk_mac W).
      { intros K. rewrite Wk in K. assert (E : S_desk_mac W = S_desk_mac B) by fget HBW.
        rewrite E, (b2_desk_mac _ Hst K). exact (P3 K). }
      destruct (RxFlt_learnS_desk W (rxbuf fr n) HWn Hsl W01 Wm) as [Sk Sm].
      exists (learn_S W (rxbuf fr n)), DIGINET_OK. split.
      * rewrite (El W (g_now B) HBW2). unfold rx_accept.
        assert (E : (S_state (learn_S W (rxbuf fr n)) =? DIGINET_S_CLOSED) = true).
        { apply Z.eqb_eq. transitivity (S_state W); [fget HlS |]. transitivity (S_state B); [fget HBW |].
          rewrite (b1_state _ Hst). exact Hcl. }
        rewrite E. cbv iota. reflexivity.
      * assert (HSW : wframe (in_rs RxFlt_rs) B (learn_S W (rxbuf fr n))).
        { apply (wframe_rs_incl ((R_learn ++ R_poll) ++ RxFlt_R_learnS)); [vm_compute; reflexivity |].
          exact (wframe_trans_rs _ _ _ _ _ HBW HlS). }
        assert (Mk : M_desk_known (learn_S W (rxbuf fr n)) = 1).
        { transitivity (M_desk_known (learn_M B (rxbuf fr n))); [| exact Lk].
          transitivity (M_desk_known W); [fget HlS | fget HW]. }
        assert (Md : M_desk (learn_S W (rxbuf fr n)) = fr_src (rxbuf fr n)).
        { transitivity (M_desk (learn_M B (rxbuf fr n))); [| exact Ld].
          transitivity (M_desk W); [fget HlS | fget HW]. }
        apply (RxFlt_done_g I ops B (rxbuf fr n) W _ Hcore HSW HBW); [| exact Hacc |].
        -- apply (RxFlt_done I ops B W _ Hcore Hka Hog HSW HBW).
           ++ rewrite Sk, Mk. reflexivity.
           ++ rewrite Mk. right. reflexivity.
           ++ intros _. rewrite Sm, Md. reflexivity.
           ++ intros _. exact Mk.
           ++ intros Hon. rewrite (b9_idle _ Hst (or_intror Hcl)) in Hon. discriminate Hon.
           ++ fget HlS.
           ++ fget HlS.
           ++ fget HlS.
           ++ fget HlS.
        -- (* the session stays closed (DS:293-294): W' accepts nothing *)
           intros Ha. exfalso. apply (ra_open _ _ Ha).
           transitivity (M_state W); [fget HlS |]. transitivity (M_state B); [fget HBW | exact Hcl].
Qed.

Lemma rx_reject : forall (HL : links) I ops fr n B,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) -> rx_pre I ops B (rxbuf fr n) -> ~ rx_accepts B (rxbuf fr n) ->
  exists Bx, m_rx_m I (Some fr) B n = Some (Bx, 0) /\ m_tick_m Bx = Some (Bx, tt) /\ wframe (in_rs R_mod) B Bx /\
    forall W, wframe (in_rs R_poll) Bx W ->
      exists W' r, diginet_session_rx_m I (Some fr) W (rxbuf fr n) (g_now B) = Some (W', r) /\ rx_done I ops 0 W W'.
Proof.
  intros HL I ops fr n B Hn Hpre Hacc.
  destruct (rx_reject_g HL I ops fr n B Hn (rx_pre_g_of _ _ _ _ Hpre) Hacc) as (Bx & E1 & E2 & E3 & Hl).
  exists Bx. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
  intros W HW. destruct (Hl W HW) as (W' & r & Es & Hd). exists W', r.
  exact (conj Es (rk_done _ _ _ _ _ _ _ Hd)).
Qed.

(* accepted: the model reaches its switch through k (FT:299-301), the library its switch through accept (DS:293-298);
   any reception of the operation, and the prologue leaves g_rx_send alone *)
Lemma rx_accept_path_g : forall (HL : links) I ops fr n B,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) -> rx_pre_g I ops B (rxbuf fr n) -> rx_accepts B (rxbuf fr n) ->
  m_rx_m I (Some fr) B n =
    match m_rx_sw I fr n (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) with
    | Some (B3, _) => match m_tick_m B3 with Some (B4, _) => Some (B4, 1) | None => None end
    | None => None
    end /\
  forall Bm W, wframe (in_rs R_mod) B Bm -> wframe (in_rs R_poll) Bm W ->
    exists W1, lib_start Bm W1 (rxbuf fr n) /\
      g_rx W1 = g_rx W /\ g_rx_len W1 = g_rx_len W /\ g_rx_times W1 = g_rx_times W /\ g_rx_fail W1 = g_rx_fail W /\
      g_now W1 = g_now B /\ g_rx_send W1 = g_rx_send W /\
      diginet_session_rx_m I (Some fr) W (rxbuf fr n) (g_now B) =
      match rx_sw I (Some fr) W1 (rxbuf fr n) (g_now B) with
      | Some (W2, _) => diginet_session_tick_m I (Some fr) W2 (g_now B)
      | None => None
      end.
Proof.
  intros HL I ops fr n B Hn Hpre Hacc.
  destruct Hpre as [Hcore _ _ _ _].
  pose proof Hcore as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  assert (HB : length B = WN) by exact Hlen.
  pose proof (ra_code _ _ Hacc) as Hc.
  pose proof (rx_frame_ok HL fr n Hn Hc) as Hf.
  pose proof (rf_src_len _ _ Hf) as Hsl.
  destruct (RxFlt_filters HL I ops fr n B Hn Hcore Hc) as [(Hnp & _ & _) | (Hp & Em & El)].
  { exfalso. apply Hnp.
    exact (Build_RxFlt_pass B (rxbuf fr n) (ra_src _ _ Hacc) (ra_dst _ _ Hacc) (ra_known _ _ Hacc)
             (ra_unknown _ _ Hacc)). }
  destruct (learn_M_frame B (rxbuf fr n) HB Hsl) as [Hlf Hll].
  split.
  - (* FT:299-301, :373-374 *)
    rewrite Em. unfold m_rx_k.
    assert (E1 : M_state (learn_M B (rxbuf fr n)) = M_state B) by fget Hlf.
    assert (E2 : g_now (learn_M B (rxbuf fr n)) = g_now B) by fget Hlf.
    assert (Hop : (M_state B =? S_CLOSED) = false) by (apply Z.eqb_neq; exact (ra_open _ _ Hacc)).
    rewrite E1, E2, Hop. cbv iota. reflexivity.
  - (* DS:293-298 *)
    intros Bm W HBm HW.
    assert (HBmn : length Bm = WN) by (eapply wframe_len; [exact HBm | exact HB]).
    assert (HWn : length W = WN) by (eapply wframe_len; [exact HW | exact HBmn]).
    pose proof (wframe_trans_rs _ _ _ _ _ HBm HW) as HBW.
    destruct (RxFlt_learnS_frame W (rxbuf fr n) HWn Hsl) as [HlS HlSn].
    assert (Wk : S_desk_known W = M_desk_known B).
    { transitivity (S_desk_known B); [fget HBW | exact (b2_desk_known _ Hst)]. }
    assert (W01 : S_desk_known W = 0 \/ S_desk_known W = 1).
    { rewrite Wk. exact (b2_desk_known01 _ Hst). }
    assert (Wm : S_desk_known W = 1 -> fr_src (rxbuf fr n) = S_desk_mac W).
    { intros K. rewrite Wk in K. assert (E : S_desk_mac W = S_desk_mac B) by fget HBW.
      rewrite E, (b2_desk_mac _ Hst K). exact (ra_known _ _ Hacc K). }
    destruct (RxFlt_learnS_desk W (rxbuf fr n) HWn Hsl W01 Wm) as [Sk Sm].
    pose proof (RxFlt_pro_frame (learn_S W (rxbuf fr n)) (g_now B) HlSn) as Hpf.
    exists (set_S_last_rx_us (set_S_stats_rx_frames (learn_S W (rxbuf fr n))
              (u64 (S_stats_rx_frames (learn_S W (rxbuf fr n)) + 1))) (g_now B)).
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + (* lib_start *)
      split; [|split; [|split]].
      * apply (wframe_rs_incl ((R_poll ++ RxFlt_R_learnS) ++ [(A_S_stats_rx_frames, 8); (A_S_last_rx_us, 8)]));
          [vm_compute; reflexivity |].
        exact (wframe_trans_rs _ _ _ _ _ (wframe_trans_rs _ _ _ _ _ HW HlS) Hpf).
      * transitivity (S_desk_known (learn_S W (rxbuf fr n))); [wget | exact Sk].
      * transitivity (S_desk_mac (learn_S W (rxbuf fr n))); [wget | exact Sm].
      * transitivity (g_now B); [wget | symmetry; fget HBm].
    + transitivity (g_rx (learn_S W (rxbuf fr n))); [wget | fget HlS].
    + transitivity (g_rx_len (learn_S W (rxbuf fr n))); [wget | fget HlS].
    + transitivity (g_rx_times (learn_S W (rxbuf fr n))); [wget | fget HlS].
    + transitivity (g_rx_fail (learn_S W (rxbuf fr n))); [wget | fget HlS].
    + transitivity (g_now (learn_S W (rxbuf fr n))); [wget |].
      transitivity (g_now W); [fget HlS |]. transitivity (g_now Bm); [fget HW | fget HBm].
    + transitivity (g_rx_send (learn_S W (rxbuf fr n))); [wget | fget HlS].
    + rewrite (El W (g_now B) HBW). unfold rx_accept. cbv zeta.
      assert (Sst : S_state (learn_S W (rxbuf fr n)) = M_state B).
      { transitivity (S_state W); [fget HlS |]. transitivity (S_state B); [fget HBW | exact (b1_state _ Hst)]. }
      assert (Hop : (M_state B =? DIGINET_S_CLOSED) = false) by (apply Z.eqb_neq; exact (ra_open _ _ Hacc)).
      rewrite Sst, Hop. cbv iota. reflexivity.
Qed.

Lemma rx_accept_path : forall (HL : links) I ops fr n B,
  0 <= n <= Z.of_nat (length (tf_bytes fr)) -> rx_pre I ops B (rxbuf fr n) -> rx_accepts B (rxbuf fr n) ->
  m_rx_m I (Some fr) B n =
    match m_rx_sw I fr n (set_M_last_rx (learn_M B (rxbuf fr n)) (g_now B)) with
    | Some (B3, _) => match m_tick_m B3 with Some (B4, _) => Some (B4, 1) | None => None end
    | None => None
    end /\
  forall Bm W, wframe (in_rs R_mod) B Bm -> wframe (in_rs R_poll) Bm W ->
    exists W1, lib_start Bm W1 (rxbuf fr n) /\
      g_rx W1 = g_rx W /\ g_rx_len W1 = g_rx_len W /\ g_rx_times W1 = g_rx_times W /\ g_rx_fail W1 = g_rx_fail W /\
      g_now W1 = g_now B /\
      diginet_session_rx_m I (Some fr) W (rxbuf fr n) (g_now B) =
      match rx_sw I (Some fr) W1 (rxbuf fr n) (g_now B) with
      | Some (W2, _) => diginet_session_tick_m I (Some fr) W2 (g_now B)
      | None => None
      end.
Proof.
  intros HL I ops fr n B Hn Hpre Hacc.
  destruct (rx_accept_path_g HL I ops fr n B Hn (rx_pre_g_of _ _ _ _ Hpre) Hacc) as [Em Hl].
  split; [exact Em|]. intros Bm W HBm HW.
  destruct (Hl Bm W HBm HW) as (W1 & L & E1 & E2 & E3 & E4 & E5 & _ & E7).
  exists W1. exact (conj L (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 E7)))))).
Qed.
