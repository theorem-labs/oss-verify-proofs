(* What SubmitTag.v, SubmitRaw.v and SubmitOk.v share: the addresses op 4 writes (R_ob for op_begin, FT:388-394;
   R4q for the rest of fuzz_transport.c:1068-1122 op_submit and diginet_session.c:328-349 diginet_session_submit),
   tactics that read a world through a chain of writes of known length (woffs, wlen, rd1, wunfold, wfr), and the
   op_begin stage with the OW / GOT state settle(0) reads (ow_got_zero). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SimLib QueueFacts.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the addresses op 4 writes *)

(* OW, GOT and M.fail (op_begin, FT:388-394); the tail of g_s from s->queue on (queue[512], queued, stats:
   DS:333, :339-341, :347-348); g_cmd and g_q (FT:1087, :1108-1118); g_nq and g_ncmd (FT:1117, :1120) *)
Definition R_ob (a : Z) : Prop :=
  (OFF_OW <= a < OFF_OW + SZ_OW) \/ (OFF_GOT <= a < OFF_GOT + SZ_GOT) \/ (A_M_fail <= a < A_M_fail + 4).
(* what op 4 writes after op_begin *)
Definition R4q (a : Z) : Prop :=
  (OFF_g_s + 1760 <= a < OFF_g_s + SZ_g_s) \/ (OFF_g_cmd <= a < OFF_g_q + SZ_g_q) \/
  (OFF_g_nq <= a < OFF_g_ncmd + 4).
Definition R4 (a : Z) : Prop := R_ob a \/ R4q a.

(* ---------------------------------------------------------------- reading a world after writes *)
(* offset arithmetic: derived addresses first, then the bases they name. woffs unfolds the offsets everywhere but
   rewrites lengths in the goal only (a `rewrite ?H in *` round that finds no LHS falls back to conversion and can
   unfold getters); woffs_in also rewrites lengths in the hypotheses, for small contexts. *)
Ltac woffs_unfold := unfold R4, R_ob, R4q, A_S_queue_bytes, A_S_queue_len, A_S_queue_display, A_S_queue_key,
  A_S_queued, A_S_stats_refused, A_S_stats_coalesced, A_Cmd_st, A_Cmd_key, A_Cmd_display, A_Cmd_bytes, A_Cmd_len,
  A_OW_desk_off, A_OW_n, A_OW_e2, A_OW_e3, A_OW_acks, A_OW_desk, A_OW_foreign, A_OW_acked, A_OW_ndata,
  A_GOT_n, A_GOT_e2, A_GOT_e3, A_GOT_acks, A_GOT_desk, A_GOT_foreign, A_GOT_acked, A_GOT_ndata, A_M_fail,
  WN, W_LEN, OFF_M, OFF_OW, SZ_OW, OFF_GOT, SZ_GOT, OFF_g_s, SZ_g_s, OFF_g_cmd, SZ_g_cmd, OFF_g_q, SZ_g_q,
  OFF_g_nq, OFF_g_ncmd, OFF_g_raw, OFF_g_fail_next, S_queue_N, CMDS_MAX, QUEUE_MAX, Cmd_ESZ in *.
Ltac woffs := woffs_unfold; rewrite ?length_put, ?repeat_length, ?length_firstn; lia.
Ltac woffs_in := unfold R4, R_ob, R4q, A_S_queue_bytes, A_S_queue_len, A_S_queue_display, A_S_queue_key,
  A_S_queued, A_S_stats_refused, A_S_stats_coalesced, A_Cmd_st, A_Cmd_key, A_Cmd_display, A_Cmd_bytes, A_Cmd_len,
  A_OW_desk_off, A_OW_n, A_OW_e2, A_OW_e3, A_OW_acks, A_OW_desk, A_OW_foreign, A_OW_acked, A_OW_ndata,
  A_GOT_n, A_GOT_e2, A_GOT_e3, A_GOT_acks, A_GOT_desk, A_GOT_foreign, A_GOT_acked, A_GOT_ndata, A_M_fail,
  WN, W_LEN, OFF_M, OFF_OW, SZ_OW, OFF_GOT, SZ_GOT, OFF_g_s, SZ_g_s, OFF_g_cmd, SZ_g_cmd, OFF_g_q, SZ_g_q,
  OFF_g_nq, OFF_g_ncmd, OFF_g_raw, OFF_g_fail_next, S_queue_N, CMDS_MAX, QUEUE_MAX, Cmd_ESZ in *;
  rewrite ?length_put, ?repeat_length, ?length_firstn in *; lia.

Lemma rd_len : forall B k v, length B = WN -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  length (upd B k v) = WN.
Proof. intros B k v HB Hk Hv. rewrite length_upd; [exact HB | exact Hk | rewrite HB; unfold WN; lia]. Qed.

Ltac wlen := lazymatch goal with
  | |- length ?X = WN => first [ apply rd_len; [wlen | woffs | woffs] | assumption ]
  end.

Lemma rd_disj : forall B k v j n, length B = WN -> 0 <= k -> 0 <= j -> k + Z.of_nat (length v) <= W_LEN ->
  (j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j) -> sub (upd B k v) j n = sub B j n.
Proof. intros B k v j n HB Hk Hj Hv Hd. apply sub_upd_out; [exact Hk | exact Hj | exact Hd | rewrite HB; unfold WN; lia]. Qed.

Lemma rd_put : forall B k n v, length B = WN -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  sub (upd B k (put n v)) k n = put n v.
Proof.
  intros B k n v HB Hk Hn.
  apply sub_upd_eq; [exact Hk | apply length_put | rewrite length_put, HB; unfold WN; lia].
Qed.

Lemma rd_zero : forall B k m j n, length B = WN -> 0 <= k -> k <= j -> j + Z.of_nat n <= k + Z.of_nat m ->
  k + Z.of_nat m <= W_LEN -> sub (upd B k (repeat (b8 0) m)) j n = repeat (b8 0) n.
Proof.
  intros B k m j n HB Hk Hj Hn Hm.
  apply wr_sub_upd_zero; [exact Hk | rewrite HB; unfold WN; lia | apply andb_true_iff; split; apply Z.leb_le; lia].
Qed.

Lemma bytes_put_small : forall n v, 0 <= v < 2 ^ (8 * Z.of_nat n) -> bytes_le_to_Z (put n v) = v.
Proof. intros n v Hv. rewrite bytes_le_to_Z_put. apply Z.mod_small. exact Hv. Qed.

(* one layer: a read the write misses, or the write of a put / of zeros read back *)
Ltac rd1 := first
  [ rewrite rd_disj by (first [wlen | woffs])
  | rewrite rd_put by (first [wlen | woffs])
  | rewrite rd_zero by (first [wlen | woffs]) ].

Ltac wunfold := unfold set_M_fail, set_OW_desk_off, set_Cmd_st, set_Cmd_key, set_Cmd_display, set_Cmd_len,
  set_Cmd_bytes, set_Q_at, set_g_nq, set_g_ncmd, set_S_queued, set_S_stats_refused, set_S_stats_coalesced in *.

(* ---------------------------------------------------------------- op_begin (FT:388-394) *)

(* a frame through a chain of writes, the last write first *)
Lemma wframe_upd_r : forall (R : Z -> Prop) B X k v, wframe R B X -> length X = WN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> (forall a, k <= a < k + Z.of_nat (length v) -> R a) ->
  wframe R B (upd X k v).
Proof.
  intros R B X k v H HX Hk Hv HR. eapply wframe_trans; [exact H|].
  apply wframe_upd; [exact Hk | rewrite HX; unfold WN; lia | exact HR].
Qed.

Ltac wfr := lazymatch goal with
  | |- wframe _ ?B ?B => apply wframe_refl
  | |- wframe _ _ _ => apply wframe_upd_r;
      [wfr | wlen | woffs | woffs | let a := fresh "a" in let H := fresh "H" in intros a H; revert H; woffs]
  end.

(* OW and GOT as op_begin leaves them (FT:390-391): no transition owed or got, no notice, nothing acked *)
Definition ow_got_zero (B : list byte) : Prop :=
  OW_n B = 0 /\ OW_e2 B = 0 /\ OW_e3 B = 0 /\ OW_acks B = 0 /\ OW_desk B = 0 /\ OW_foreign B = 0 /\
  OW_acked B = 0 /\ OW_ndata B = 0 /\
  GOT_n B = 0 /\ GOT_e2 B = 0 /\ GOT_e3 B = 0 /\ GOT_acks B = 0 /\ GOT_desk B = 0 /\
  GOT_foreign B = 0 /\ GOT_acked B = 0 /\ GOT_ndata B = 0.

Lemma op_begin_stage : forall B, length B = WN ->
  exists B1, op_begin_m B = Some (B1, tt) /\ wframe R_ob B B1 /\ ow_got_zero B1 /\ M_fail B1 = g_fail_next B.
Proof.
  intros B HB. unfold op_begin_m. eexists. split; [reflexivity|].
  assert (Hg : g_fail_next (set_OW_desk_off (upd (upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW))) OFF_GOT
                 (repeat (b8 0) (Z.to_nat SZ_GOT))) (-1)) = g_fail_next B).
  { unfold g_fail_next, u_at. wunfold. do 3 rd1. reflexivity. }
  rewrite Hg. split; [|unfold ow_got_zero].
  - wunfold. wfr.
  - unfold OW_n, OW_e2, OW_e3, OW_acks, OW_desk, OW_foreign, OW_acked, OW_ndata,
      GOT_n, GOT_e2, GOT_e3, GOT_acks, GOT_desk, GOT_foreign, GOT_acked, GOT_ndata, M_fail, s32_at, u_at.
    wunfold. repeat split; [repeat rd1; rewrite w_bytes_zero; reflexivity .. |].
    rewrite rd_put by (first [wlen | woffs]). apply w_s32_put.
    pose proof (u_at_nonneg B OFF_g_fail_next 1). pose proof (u_at_bound B OFF_g_fail_next 1).
    unfold g_fail_next. change (8 * Z.of_nat 1) with 8 in *. lia.
Qed.

Lemma ow_got_zero_frame : forall B B', wframe R4q B B' -> ow_got_zero B -> ow_got_zero B'.
Proof.
  intros B B' H Z. unfold ow_got_zero, OW_n, OW_e2, OW_e3, OW_acks, OW_desk, OW_foreign, OW_acked, OW_ndata,
    GOT_n, GOT_e2, GOT_e3, GOT_acks, GOT_desk, GOT_foreign, GOT_acked, GOT_ndata in *.
  assert (E : forall j, OFF_GOT <= j -> j + 4 <= OFF_OW + SZ_OW -> s32_at B' j = s32_at B j).
  { intros j Hj1 Hj2. apply (wframe_s32_at R4q B B' j H); [woffs | intros a Ha HR; woffs]. }
  rewrite !E by woffs. exact Z.
Qed.

Lemma wframe_R4 : forall B B1 B7, wframe R_ob B B1 -> wframe R4q B1 B7 -> wframe R4 B B7.
Proof.
  intros B B1 B7 H1 H2. eapply wframe_trans.
  - eapply wframe_weaken; [|exact H1]. intros a Ha. left. exact Ha.
  - eapply wframe_weaken; [|exact H2]. intros a Ha. right. exact Ha.
Qed.
