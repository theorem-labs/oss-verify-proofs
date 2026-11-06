(* Modified by Theorem Labs, 2026-10: new file, operations 5 (wake), 6 (close) and 7 (fail-next) of the fuzz_transport harness keep the simulation invariant (a Theorem Labs lane). *)
(* fuzz_transport.c (FT):1193-1208 and the library calls they make, diginet_session.c (DS):97-158.
   Part A: io_send (FT:823-899) on the two control frames only these operations send through send_control
   (DS:97-109): the wake's E2 and the close's E3. Each is stated over the world facts io_send reads, for any
   world Bc: at the callback the harness model has already run ahead of the library. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SendOk SimLib.
Import ListNotations.
Open Scope Z_scope.

Ltac synrefl := match goal with |- ?a = ?b => wis a b; exact eq_refl end.

(* a read of a world a few writes away from its base, equal to the same read of the base *)
(* SimLib's read rewriting without its closing eq_refl (which compares by conversion) *)
Ltac wsimpq := wunfold_set; wsimp_go.
Ltac wfr := wsimpq; synrefl.

(* decide the comparisons of closed constants (no world in them) by computation *)
Ltac kclosed t :=
  lazymatch t with
  | Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac
  | DIGINET_CMD_WAKE => idtac | DIGINET_CMD_DISCONNECT => idtac | SPEC_CMD_ACK => idtac
  | SPEC_CMD_E2 => idtac | SPEC_CMD_DATA => idtac | SPEC_CMD_E3 => idtac | SPEC_MAX_FRAME => idtac
  | INT_MAX => idtac | SPEC_OK => idtac | DIGINET_OK => idtac | DIGINET_E_ARG => idtac
  | DIGINET_E_REFUSED => idtac | SPEC_E_ARG => idtac | SPEC_E_REFUSED => idtac | EIO => idtac
  | DIGINET_N_STATE => idtac | N_STATE => idtac | N_ACKED => idtac | N_ACK_LOST => idtac | N_DESK => idtac
  | N_DATA => idtac | N_FOREIGN => idtac | DIGINET_MIN_FRAME_LEN => idtac
  | DIGINET_R_WAKE => idtac | DIGINET_R_CLOSED => idtac | R_WAKE => idtac | R_CLOSED => idtac
  | DIGINET_S_IDLE => idtac | DIGINET_S_WAKING => idtac | DIGINET_S_ONLINE => idtac | DIGINET_S_CLOSED => idtac
  | S_IDLE => idtac | S_WAKING => idtac | S_ONLINE => idtac | S_CLOSED => idtac | TRANS_MAX => idtac
  | - ?a => kclosed a
  end.

Ltac kdec1 :=
  match goal with
  | |- context [?a =? ?b] => kclosed a; kclosed b; let v := eval vm_compute in (a =? b) in change (a =? b) with v
  | |- context [?a <? ?b] => kclosed a; kclosed b; let v := eval vm_compute in (a <? b) in change (a <? b) with v
  end.

Ltac kdec :=
  try unfold truth;
  repeat (first [ kdec1 | progress cbv beta iota delta [orb andb negb] ]).

(* decide the integer comparisons lia can *)
Ltac zdec :=
  repeat match goal with
  | |- context [?a =? ?b] =>
      first [ rewrite (proj2 (Z.eqb_neq a b)) by lia | rewrite (proj2 (Z.eqb_eq a b)) by lia ]
  | |- context [?a <? ?b] =>
      first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  end;
  cbv beta iota delta [orb andb negb].

(* ---- the two control frames (DS:99-101: no body, ncmds 0, retry 0, ack 0) ---- *)
Definition wake_frame (dst : list byte) (send mode : Z) : list byte :=
  lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode.
Definition close_frame (dst : list byte) (send mode : Z) : list byte :=
  lib_frame dst HOST send 0 0 DIGINET_CMD_DISCONNECT 0 [] mode.

Lemma u8_range : forall c, 0 <= c < 256 -> 0 <= c < 2 ^ 8.
Proof. intros c H. change (2 ^ 8) with 256. exact H. Qed.

Lemma zero_u32 : 0 <= 0 < 2 ^ 32.
Proof. split; [apply Z.le_refl | apply Z.ltb_lt; reflexivity]. Qed.

(* ---- io_send of the E2 (FT:838-852, :883-889) ----
   g_fail_next cleared (:829); GOT.e2 + 1 and g_last_counter = the counter (:849-850); then, when the send
   does not fail, the model's frame in flight is the E2 (:883-889, len 60 < 1514). *)
Definition io_e2_w (Bc : list byte) (f : list byte) (send : Z) : list byte :=
  let B5 := set_g_last_counter (set_GOT_e2 (set_g_fail_next Bc 0) (GOT_e2 Bc + 1)) send in
  if g_fail_next Bc =? 0 then
    set_M_fly_frame
      (set_M_fly_len
         (set_M_fly_sent
            (set_M_fly_retries (set_M_fly_counter (set_M_fly_cmd (set_M_fly_on B5 1) DIGINET_CMD_WAKE) send) 0)
            (g_now Bc)) 60) f
  else B5.

Lemma io_send_e2_ok : forall (HL : links) (I : timg) (Bc dst : list byte) (send mode : Z),
  length Bc = Z.to_nat W_LEN -> length dst = 6%nat -> (mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO) ->
  0 <= send < 2 ^ 32 ->
  M_desk_known Bc = 1 -> M_desk Bc = dst -> Cfg_sum_mode Bc = mode -> M_foreign Bc = 0 ->
  M_host_counter Bc = send -> 0 <= GOT_e2 Bc < INT_MAX -> bit01 (g_fail_next Bc) ->
  io_send_m I Bc (wake_frame dst send mode) =
    Some (io_e2_w Bc (wake_frame dst send mode) send, if g_fail_next Bc =? 0 then 0 else - EIO).
Proof.
  intros HL I Bc dst send mode HB Hd Hm Hs Hk Hdesk Hmode Hfor Hhc He2 Hf.
  assert (Hok : build_ok dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode).
  { apply control_build_ok; [exact Hd | reflexivity | exact Hm | exact Hs | exact zero_u32 |].
    apply u8_range. unfold DIGINET_CMD_WAKE. lia. }
  pose proof (rf_lib_frame HL dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode Hok) as R. cbv zeta in R.
  destruct R as (Hlen & _ & _ & _ & _ & Hcmd & Hsend & _ & Hretry & _).
  assert (Hl60 : length (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode) = 60%nat)
    by (unfold frame_len in Hlen; cbn [length] in Hlen; lia).
  (* the world io_send works on after :829 *)
  assert (E1 : M_desk_known (set_g_fail_next Bc 0) = 1) by (transitivity (M_desk_known Bc); [wfr | exact Hk]).
  assert (E2 : M_desk (set_g_fail_next Bc 0) = dst) by (transitivity (M_desk Bc); [wfr | exact Hdesk]).
  assert (E3 : Cfg_sum_mode (set_g_fail_next Bc 0) = mode) by (transitivity (Cfg_sum_mode Bc); [wfr | exact Hmode]).
  assert (E4 : M_foreign (set_g_fail_next Bc 0) = 0) by (transitivity (M_foreign Bc); [wfr | exact Hfor]).
  assert (E5 : send = M_host_counter (set_g_fail_next Bc 0)) by (transitivity (M_host_counter Bc); [symmetry; exact Hhc | symmetry; wfr]).
  assert (E6 : GOT_e2 (set_g_fail_next Bc 0) = GOT_e2 Bc) by wfr.
  unfold wake_frame, io_e2_w, io_send_m. cbv beta zeta.
  rewrite (sent_frame_ok HL (set_g_fail_next Bc 0) dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode Hok eq_refl E1 E2 E3).
  cbv beta iota.
  rewrite Hcmd, Hretry, Hsend. kdec.
  unfold check_state_wake_m. rewrite E4. kdec.
  rewrite (latest_control_ok HL (set_g_fail_next Bc 0) dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode Hok E5).
  cbv beta iota.
  unfold int_inc. rewrite E6. zdec. cbv beta iota.
  assert (E7 : g_now (set_g_last_counter (set_GOT_e2 (set_g_fail_next Bc 0) (GOT_e2 Bc + 1)) send) = g_now Bc) by wfr.
  rewrite E7, Hlen.
  replace (frame_len (length (@nil byte))) with 60 by reflexivity.
  kdec.
  replace (Z.to_nat 60) with 60%nat by reflexivity.
  rewrite (firstn_all2 (n := 60%nat) (lib_frame dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode)) by lia.
  destruct Hf as [Hf|Hf]; rewrite Hf; kdec; synrefl.
Qed.

(* ---- io_send of the E3 (FT:891-893): g_fail_next cleared, GOT.e3 + 1, the counter checked ---- *)
Definition io_e3_w (Bc : list byte) : list byte :=
  set_GOT_e3 (set_g_fail_next Bc 0) (GOT_e3 Bc + 1).

Lemma io_send_e3_ok : forall (HL : links) (I : timg) (Bc dst : list byte) (send mode : Z),
  length Bc = Z.to_nat W_LEN -> length dst = 6%nat -> (mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO) ->
  0 <= send < 2 ^ 32 ->
  M_desk_known Bc = 1 -> M_desk Bc = dst -> Cfg_sum_mode Bc = mode ->
  M_host_counter Bc = send -> 0 <= GOT_e3 Bc < INT_MAX -> bit01 (g_fail_next Bc) ->
  io_send_m I Bc (close_frame dst send mode) =
    Some (io_e3_w Bc, if g_fail_next Bc =? 0 then 0 else - EIO).
Proof.
  intros HL I Bc dst send mode HB Hd Hm Hs Hk Hdesk Hmode Hhc He3 Hf.
  assert (Hok : build_ok dst HOST send 0 0 DIGINET_CMD_DISCONNECT 0 [] mode).
  { apply control_build_ok; [exact Hd | reflexivity | exact Hm | exact Hs | exact zero_u32 |].
    apply u8_range. unfold DIGINET_CMD_DISCONNECT. lia. }
  pose proof (rf_lib_frame HL dst HOST send 0 0 DIGINET_CMD_DISCONNECT 0 [] mode Hok) as R. cbv zeta in R.
  destruct R as (Hlen & _ & _ & _ & _ & Hcmd & Hsend & _ & Hretry & _).
  assert (E1 : M_desk_known (set_g_fail_next Bc 0) = 1) by (transitivity (M_desk_known Bc); [wfr | exact Hk]).
  assert (E2 : M_desk (set_g_fail_next Bc 0) = dst) by (transitivity (M_desk Bc); [wfr | exact Hdesk]).
  assert (E3 : Cfg_sum_mode (set_g_fail_next Bc 0) = mode) by (transitivity (Cfg_sum_mode Bc); [wfr | exact Hmode]).
  assert (E6 : GOT_e3 (set_g_fail_next Bc 0) = GOT_e3 Bc) by wfr.
  assert (E5 : send = M_host_counter (set_GOT_e3 (set_g_fail_next Bc 0) (GOT_e3 Bc + 1)))
    by (transitivity (M_host_counter Bc); [symmetry; exact Hhc | symmetry; wfr]).
  unfold close_frame, io_e3_w, io_send_m. cbv beta zeta.
  rewrite (sent_frame_ok HL (set_g_fail_next Bc 0) dst HOST send 0 0 DIGINET_CMD_DISCONNECT 0 [] mode Hok eq_refl E1 E2 E3).
  cbv beta iota.
  rewrite Hcmd. kdec.
  unfold int_inc. rewrite E6. zdec. cbv beta iota.
  rewrite (latest_control_ok HL (set_GOT_e3 (set_g_fail_next Bc 0) (GOT_e3 Bc + 1)) dst HOST send 0 0
             DIGINET_CMD_DISCONNECT 0 [] mode Hok E5).
  cbv beta iota.
  destruct Hf as [Hf|Hf]; rewrite Hf; kdec; synrefl.
Qed.

(* ================================================================ Part B: the harness model and the session's
   state change, as explicit worlds *)

(* m_set (FT:196-207) *)
Definition m_set_w (B : list byte) (st why : Z) : list byte :=
  if M_state B =? st then B
  else
    set_M_state
      (set_OW_n
         (if OW_n B <? TRANS_MAX
          then set_OW_t_reason (set_OW_t_old (set_OW_t_state B (OW_n B) st) (OW_n B) (M_state B)) (OW_n B) why
          else B)
         (OW_n B + 1))
      st.

Lemma m_set_ok : forall B st why, 0 <= OW_n B < INT_MAX -> m_set_m B st why = Some (m_set_w B st why, tt).
Proof.
  intros B st why Hn. unfold m_set_m, m_set_w.
  destruct (Z.eqb_spec (M_state B) st) as [_|_]; [reflexivity|].
  cbv zeta. unfold int_inc.
  destruct (Z.eqb_spec (OW_n B) INT_MAX) as [Hm|_]; [lia|].
  destruct (Z.ltb_spec (OW_n B) TRANS_MAX) as [_|_].
  - destruct (Z.ltb_spec (OW_n B) 0) as [H0|_]; [lia|]. cbv beta iota. synrefl.
  - cbv beta iota. synrefl.
Qed.

(* m_wake (FT:218-233) when the desk is known and not foreign: the flags, wake_sent, OW.e2 + 1, M.fail
   consumed; then WAKING unless the wake fails *)
Definition m_wake_pre (B : list byte) : list byte :=
  set_M_fail (set_OW_e2 (set_M_wake_sent (set_M_e1_us (set_M_e2_acked B 0) 0) (g_now B)) (OW_e2 B + 1)) 0.
Definition m_wake_w (B : list byte) : list byte :=
  if M_fail B =? 0 then m_set_w (m_wake_pre B) S_WAKING R_WAKE else m_wake_pre B.

Lemma m_wake_ok : forall B, length B = Z.to_nat W_LEN -> M_desk_known B <> 0 -> M_foreign B = 0 ->
  0 <= OW_e2 B < INT_MAX -> 0 <= OW_n B < INT_MAX ->
  m_wake_m B = Some (m_wake_w B, if M_fail B =? 0 then SPEC_OK else - EIO).
Proof.
  intros B HB Hk Hf He Hn.
  assert (E1 : g_now (set_M_e1_us (set_M_e2_acked B 0) 0) = g_now B) by wfr.
  assert (E2 : OW_e2 (set_M_wake_sent (set_M_e1_us (set_M_e2_acked B 0) 0) (g_now B)) = OW_e2 B) by wfr.
  assert (E3 : M_fail (set_OW_e2 (set_M_wake_sent (set_M_e1_us (set_M_e2_acked B 0) 0) (g_now B)) (OW_e2 B + 1))
               = M_fail B) by wfr.
  assert (E4 : OW_n (m_wake_pre B) = OW_n B) by (unfold m_wake_pre; wfr).
  unfold m_wake_m, m_wake_w. unfold truth at 1 2.
  destruct (Z.eqb_spec (M_desk_known B) 0) as [Hk0|_]; [contradiction|].
  rewrite Hf. kdec. cbv zeta.
  rewrite E1. unfold int_inc. rewrite E2.
  destruct (Z.eqb_spec (OW_e2 B) INT_MAX) as [Hm|_]; [lia|]. cbv beta iota.
  rewrite E3. unfold truth.
  destruct (Z.eqb_spec (M_fail B) 0) as [_|_]; cbv beta iota delta [negb].
  - fold (m_wake_pre B). rewrite (m_set_ok (m_wake_pre B) S_WAKING R_WAKE) by (rewrite E4; exact Hn).
    cbv beta iota. synrefl.
  - fold (m_wake_pre B). synrefl.
Qed.

(* m_close (FT:378-386) *)
Definition m_close_w (B : list byte) : list byte :=
  let B1 := if truth (M_desk_known B) && negb (truth (M_foreign B)) && negb (M_state B =? S_CLOSED)
            then set_M_fail (set_OW_e3 B (OW_e3 B + 1)) 0 else B in
  m_set_w (set_M_fly_on B1 0) S_CLOSED R_CLOSED.

Lemma m_close_ok : forall B, length B = Z.to_nat W_LEN -> 0 <= OW_e3 B < INT_MAX -> 0 <= OW_n B < INT_MAX ->
  m_close_m B = Some (m_close_w B, tt).
Proof.
  intros B HB He Hn. unfold m_close_m, m_close_w. cbv zeta.
  destruct (truth (M_desk_known B) && negb (truth (M_foreign B)) && negb (M_state B =? S_CLOSED)).
  - unfold int_inc. destruct (Z.eqb_spec (OW_e3 B) INT_MAX) as [Hm|_]; [lia|]. cbv beta iota.
    assert (E : OW_n (set_M_fly_on (set_M_fail (set_OW_e3 B (OW_e3 B + 1)) 0) 0) = OW_n B) by wfr.
    rewrite (m_set_ok (set_M_fly_on (set_M_fail (set_OW_e3 B (OW_e3 B + 1)) 0) 0) S_CLOSED R_CLOSED)
      by (rewrite E; exact Hn).
    synrefl.
  - cbv beta iota.
    assert (E : OW_n (set_M_fly_on B 0) = OW_n B) by wfr.
    rewrite (m_set_ok (set_M_fly_on B 0) S_CLOSED R_CLOSED) by (rewrite E; exact Hn).
    synrefl.
Qed.

(* the session's set_state (DS:79-86) with the harness's notice (FT:937-949) inline: GOT records the
   transition; no check runs for a state other than ONLINE *)
Definition got_set_w (B : list byte) (st old why : Z) : list byte :=
  set_GOT_n
    (if GOT_n B <? TRANS_MAX
     then set_GOT_t_reason (set_GOT_t_old (set_GOT_t_state B (GOT_n B) st) (GOT_n B) old) (GOT_n B) why
     else B)
    (GOT_n B + 1).
Definition set_state_w (B : list byte) (st why : Z) : list byte :=
  if S_state B =? st then B else got_set_w (set_S_state B st) st (S_state B) why.

Lemma set_state_ok : forall I F B st why, length B = Z.to_nat W_LEN -> S_notify B = ti_notice I ->
  0 <= GOT_n B < INT_MAX -> st <> S_ONLINE ->
  set_state_m I F B st why = Some (set_state_w B st why, tt).
Proof.
  intros I F B st why HB Hno Hg Hst. unfold set_state_m, set_state_w.
  destruct (Z.eqb_spec (S_state B) st) as [_|_]; [reflexivity|].
  assert (E1 : S_notify (set_S_state B st) = S_notify B) by wfr.
  assert (E2 : GOT_n (set_S_state B st) = GOT_n B) by wfr.
  unfold call_notify, got_set_w. rewrite E1, Hno, (Z.eqb_refl (ti_notice I)).
  unfold notice_m. cbn [n_kind n_state n_old n_reason]. kdec.
  unfold int_inc.
  destruct (Z.eqb_spec (GOT_n (set_S_state B st)) INT_MAX) as [Hm|_]; [lia|].
  destruct (Z.eqb_spec st S_ONLINE) as [Ho|_]; [contradiction|].
  destruct (Z.ltb_spec (GOT_n (set_S_state B st)) TRANS_MAX) as [_|_].
  - destruct (Z.ltb_spec (GOT_n (set_S_state B st)) 0) as [H0|_]; [lia|]. cbv beta iota. synrefl.
  - cbv beta iota. synrefl.
Qed.

(* ================================================================ Part C: the session's wake and close *)

(* S_host_counter is a uint32_t *)
Lemma host_counter_range : forall B, 0 <= S_host_counter B < 2 ^ 32.
Proof. intros B. exact (u_at_range B A_S_host_counter 4). Qed.

Lemma wake_frame_len : forall (HL : links) dst send mode, length dst = 6%nat ->
  (mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO) -> 0 <= send < 2 ^ 32 ->
  length (wake_frame dst send mode) = 60%nat.
Proof.
  intros HL dst send mode Hd Hm Hs.
  assert (Hok : build_ok dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode).
  { apply control_build_ok; [exact Hd | reflexivity | exact Hm | exact Hs | exact zero_u32 |].
    apply u8_range. unfold DIGINET_CMD_WAKE. lia. }
  destruct (control_frame_ok HL [] dst HOST send 0 DIGINET_CMD_WAKE mode Hok) as (_ & Hlen & _).
  exact Hlen.
Qed.

(* diginet_session_wake (DS:119-145), desk known and not foreign: the flags and wake_sent (:129-131), the E2
   through send_control / send_raw / io_send (:134-136), and on success the frame in flight (:139-142) and the
   state WAKING (:143) *)
Definition lw_pre (B : list byte) (now : Z) : list byte :=
  set_S_wake_sent_us (set_S_wake_acked (set_S_e1_named_us B 0) 0) now.
Definition lw_sent (B : list byte) (f : list byte) (send : Z) : list byte :=
  let Bi := io_e2_w B f send in set_S_stats_tx_frames Bi (u64 (S_stats_tx_frames Bi + 1)).
Definition lw_done (B : list byte) (f : list byte) (now : Z) : list byte :=
  let B1 := set_S_inflight_len (set_S_inflight_frame B f) (Z.of_nat (length f)) in
  let B2 := set_S_stats_tx_wakes B1 (u64 (S_stats_tx_wakes B1 + 1)) in
  let B3 := set_S_inflight_sent_us (set_S_inflight_retries (set_S_inflight_counter (set_S_inflight B2 1)
              (S_host_counter B2)) 0) now in
  set_state_w B3 DIGINET_S_WAKING DIGINET_R_WAKE.

Lemma lib_wake_ok : forall (HL : links) (I : timg) (F : option tframe) (B : list byte) (now : Z)
    (dst : list byte) (send mode : Z),
  length B = Z.to_nat W_LEN -> S_desk_known B <> 0 -> S_foreign B = 0 ->
  S_desk_mac B = dst -> S_cfg_host_mac B = HOST -> S_host_counter B = send -> S_cfg_sum_mode B = mode ->
  length dst = 6%nat -> (mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO) ->
  S_io_send B = ti_io_send I -> S_notify B = ti_notice I ->
  M_desk_known B = 1 -> M_desk B = dst -> Cfg_sum_mode B = mode -> M_foreign B = 0 -> M_host_counter B = send ->
  0 <= GOT_e2 B < INT_MAX -> 0 <= GOT_n B < INT_MAX -> bit01 (g_fail_next B) ->
  diginet_session_wake_m I F B now =
    if g_fail_next B =? 0
    then Some (lw_done (lw_sent (lw_pre B now) (wake_frame dst send mode) send) (wake_frame dst send mode) now,
               DIGINET_OK)
    else Some (io_e2_w (lw_pre B now) (wake_frame dst send mode) send, - EIO).
Proof.
  intros HL I F B now dst send mode HB Hk Hf Hdm Hhm Hhc Hsm Hd Hm Hio Hno Mk Md Mm Mf Mh He2 Hn Hfn.
  assert (Hs : 0 <= send < 2 ^ 32) by (rewrite <- Hhc; apply host_counter_range).
  pose proof (wake_frame_len HL dst send mode Hd Hm Hs) as Hlf.
  assert (La : length (lw_pre B now) = Z.to_nat W_LEN) by (unfold lw_pre; wlen).
  assert (Adm : S_desk_mac (lw_pre B now) = dst) by (rewrite <- Hdm; unfold lw_pre; wfr).
  assert (Ahm : S_cfg_host_mac (lw_pre B now) = HOST) by (rewrite <- Hhm; unfold lw_pre; wfr).
  assert (Ahc : S_host_counter (lw_pre B now) = send) by (rewrite <- Hhc; unfold lw_pre; wfr).
  assert (Asm : S_cfg_sum_mode (lw_pre B now) = mode) by (rewrite <- Hsm; unfold lw_pre; wfr).
  assert (Aio : S_io_send (lw_pre B now) = ti_io_send I) by (rewrite <- Hio; unfold lw_pre; wfr).
  assert (AMk : M_desk_known (lw_pre B now) = 1) by (rewrite <- Mk; unfold lw_pre; wfr).
  assert (AMd : M_desk (lw_pre B now) = dst) by (rewrite <- Md; unfold lw_pre; wfr).
  assert (AMm : Cfg_sum_mode (lw_pre B now) = mode) by (rewrite <- Mm; unfold lw_pre; wfr).
  assert (AMf : M_foreign (lw_pre B now) = 0) by (rewrite <- Mf; unfold lw_pre; wfr).
  assert (AMh : M_host_counter (lw_pre B now) = send) by (rewrite <- Mh; unfold lw_pre; wfr).
  assert (AGe : GOT_e2 (lw_pre B now) = GOT_e2 B) by (unfold lw_pre; wfr).
  assert (Afn : g_fail_next (lw_pre B now) = g_fail_next B) by (unfold lw_pre; wfr).
  assert (Hok : build_ok dst HOST send 0 0 DIGINET_CMD_WAKE 0 [] mode).
  { apply control_build_ok; [exact Hd | reflexivity | exact Hm | exact Hs | exact zero_u32 |].
    apply u8_range. unfold DIGINET_CMD_WAKE. lia. }
  destruct (control_frame_ok HL (lw_pre B now) dst HOST send 0 DIGINET_CMD_WAKE mode Hok) as (Hcode & _ & _).
  unfold diginet_session_wake_m.
  destruct (Z.eqb_spec (S_desk_known B) 0) as [E|_]; [contradiction|].
  rewrite Hf. kdec. cbv zeta.
  change (set_S_wake_sent_us (set_S_wake_acked (set_S_e1_named_us B 0) 0) now) with (lw_pre B now).
  unfold send_control_m. cbv zeta.
  rewrite Asm, Adm, Ahm, Ahc, Hcode. kdec. cbv beta iota.
  unfold send_raw_m, call_send. rewrite Aio, (Z.eqb_refl (ti_io_send I)).
  fold (wake_frame dst send mode).
  rewrite (io_send_e2_ok HL I (lw_pre B now) dst send mode La Hd Hm Hs AMk AMd AMm AMf AMh
             ltac:(rewrite AGe; exact He2) ltac:(rewrite Afn; exact Hfn)).
  rewrite Afn.
  destruct Hfn as [Z0|Z1].
  - rewrite Z0. kdec. cbv beta iota.
    unfold inflight_start_m. cbv beta iota zeta.
    unfold lw_done, lw_sent, io_e2_w. rewrite Afn, Z0. kdec. cbv beta iota zeta.
    match goal with |- context [set_state_m I F ?X DIGINET_S_WAKING DIGINET_R_WAKE] =>
      assert (LX : length X = Z.to_nat W_LEN) by (unfold lw_pre; wlen);
      assert (NX : S_notify X = ti_notice I) by (rewrite <- Hno; unfold lw_pre; wfr);
      assert (GX : GOT_n X = GOT_n B) by (unfold lw_pre; wfr);
      rewrite (set_state_ok I F X DIGINET_S_WAKING DIGINET_R_WAKE LX NX ltac:(rewrite GX; exact Hn)
                 ltac:(unfold DIGINET_S_WAKING, S_ONLINE; discriminate))
    end.
    cbv beta iota. kdec. synrefl.
  - rewrite Z1. kdec. cbv beta iota. synrefl.
Qed.

(* diginet_session_close (DS:147-158): the E3 when the desk is known, not foreign and the session not
   closed (:153-154), then nothing in flight and CLOSED (:155-156) *)
Definition lc_sent (B : list byte) : list byte :=
  let Bi := io_e3_w B in if g_fail_next B =? 0 then set_S_stats_tx_frames Bi (u64 (S_stats_tx_frames Bi + 1)) else Bi.

Lemma lib_close_send_ok : forall (HL : links) (I : timg) (F : option tframe) (B : list byte) (now : Z)
    (dst : list byte) (send mode : Z),
  length B = Z.to_nat W_LEN -> S_desk_known B <> 0 -> S_foreign B = 0 -> S_state B <> DIGINET_S_CLOSED ->
  S_desk_mac B = dst -> S_cfg_host_mac B = HOST -> S_host_counter B = send -> S_cfg_sum_mode B = mode ->
  length dst = 6%nat -> (mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO) ->
  S_io_send B = ti_io_send I -> S_notify B = ti_notice I ->
  M_desk_known B = 1 -> M_desk B = dst -> Cfg_sum_mode B = mode -> M_host_counter B = send ->
  0 <= GOT_e3 B < INT_MAX -> 0 <= GOT_n B < INT_MAX -> bit01 (g_fail_next B) ->
  diginet_session_close_m I F B now =
    Some (set_state_w (set_S_inflight (lc_sent B) 0) DIGINET_S_CLOSED DIGINET_R_CLOSED,
          if g_fail_next B =? 0 then 0 else - EIO).
Proof.
  intros HL I F B now dst send mode HB Hk Hf Hc Hdm Hhm Hhc Hsm Hd Hm Hio Hno Mk Md Mm Mh He3 Hn Hfn.
  assert (Hs : 0 <= send < 2 ^ 32) by (rewrite <- Hhc; apply host_counter_range).
  assert (Hok : build_ok dst HOST send 0 0 DIGINET_CMD_DISCONNECT 0 [] mode).
  { apply control_build_ok; [exact Hd | reflexivity | exact Hm | exact Hs | exact zero_u32 |].
    apply u8_range. unfold DIGINET_CMD_DISCONNECT. lia. }
  destruct (control_frame_ok HL B dst HOST send 0 DIGINET_CMD_DISCONNECT mode Hok) as (Hcode & _ & _).
  unfold diginet_session_close_m. cbv zeta.
  destruct (Z.eqb_spec (S_desk_known B) 0) as [E|_]; [contradiction|].
  destruct (Z.eqb_spec (S_state B) DIGINET_S_CLOSED) as [E|_]; [contradiction|].
  rewrite Hf. kdec. cbv beta iota.
  unfold send_control_m. cbv zeta.
  rewrite Hsm, Hdm, Hhm, Hhc, Hcode. kdec. cbv beta iota.
  unfold send_raw_m, call_send. rewrite Hio, (Z.eqb_refl (ti_io_send I)).
  fold (close_frame dst send mode).
  rewrite (io_send_e3_ok HL I B dst send mode HB Hd Hm Hs Mk Md Mm Mh He3 Hfn).
  unfold lc_sent.
  destruct Hfn as [Z0|Z1]; [rewrite Z0 | rewrite Z1]; kdec; cbv beta iota zeta;
  match goal with |- context [set_state_m I F ?X DIGINET_S_CLOSED DIGINET_R_CLOSED] =>
    assert (LX : length X = Z.to_nat W_LEN) by (unfold io_e3_w; wlen);
    assert (NX : S_notify X = ti_notice I) by (rewrite <- Hno; unfold io_e3_w; wfr);
    assert (GX : GOT_n X = GOT_n B) by (unfold io_e3_w; wfr);
    rewrite (set_state_ok I F X DIGINET_S_CLOSED DIGINET_R_CLOSED LX NX ltac:(rewrite GX; exact Hn)
               ltac:(unfold DIGINET_S_CLOSED, S_ONLINE; discriminate))
  end;
  cbv beta iota; synrefl.
Qed.

Lemma lib_close_nosend_ok : forall (I : timg) (F : option tframe) (B : list byte) (now : Z),
  length B = Z.to_nat W_LEN ->
  (S_desk_known B = 0 \/ S_foreign B <> 0 \/ S_state B = DIGINET_S_CLOSED) ->
  S_notify B = ti_notice I -> 0 <= GOT_n B < INT_MAX ->
  diginet_session_close_m I F B now =
    Some (set_state_w (set_S_inflight B 0) DIGINET_S_CLOSED DIGINET_R_CLOSED, 0).
Proof.
  intros I F B now HB Hc Hno Hn.
  assert (E : (negb (S_desk_known B =? 0) && (S_foreign B =? 0) && negb (S_state B =? DIGINET_S_CLOSED)) = false).
  { destruct (Z.eqb_spec (S_desk_known B) 0); destruct (Z.eqb_spec (S_foreign B) 0);
      destruct (Z.eqb_spec (S_state B) DIGINET_S_CLOSED); cbv [andb negb];
      first [ exact eq_refl | exfalso; tauto ]. }
  unfold diginet_session_close_m. cbv zeta. rewrite E. cbv beta iota.
  assert (LX : length (set_S_inflight B 0) = Z.to_nat W_LEN) by wlen.
  assert (NX : S_notify (set_S_inflight B 0) = ti_notice I) by (rewrite <- Hno; wfr).
  assert (GX : GOT_n (set_S_inflight B 0) = GOT_n B) by wfr.
  rewrite (set_state_ok I F (set_S_inflight B 0) DIGINET_S_CLOSED DIGINET_R_CLOSED LX NX
             ltac:(rewrite GX; exact Hn) ltac:(unfold DIGINET_S_CLOSED, S_ONLINE; discriminate)).
  synrefl.
Qed.

(* ================================================================ Part D: the operations *)

(* operation 7 (FT:1206-1208): g_fail_next = 1, nothing else; agree holds after (SimLib agree_fail_next) *)
Theorem op7_step : forall (I : timg) (ops : Z) (B : list byte) (A : nat -> Z) (D : list byte) (c : fuzz_in) (k : nat),
  agree I ops B -> 0 <= ops < OPS_MAX -> snd (fuzz_u8_m D c) mod 9 = 7 ->
  LLVMFuzzerTestOneInput_op_m I B A D c k = Some (set_g_fail_next B 1, (fst (fuzz_u8_m D c), k)) /\
  agree I (ops + 1) (set_g_fail_next B 1).
Proof.
  intros I ops B A D c k HA Ho Hop. split.
  - unfold LLVMFuzzerTestOneInput_op_m. destruct (fuzz_u8_m D c) as [c1 opb]. cbn [fst snd] in *.
    cbv beta iota zeta. rewrite Hop. kdec. cbv beta iota. synrefl.
  - apply (agree_mono I ops (ops + 1) (set_g_fail_next B 1) (agree_fail_next I ops B HA)). lia.
Qed.
