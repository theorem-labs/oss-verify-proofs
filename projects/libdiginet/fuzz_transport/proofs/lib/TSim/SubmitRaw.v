(* fuzz_transport.c:1068-1083 op_submit (FT) with g_raw != 0, TOps.v op_submit_m's raw branch: the command is
   (uint8_t)fuzz_take(in, fuzz_u16(in) % 25, &p) bytes of the input (FT:1079-1080), diginet_session_submit
   (diginet_session.c:328-349, DS; QueueFacts.v submit_spec) queues it, coalesces it, refuses it or answers
   E_ARG / E_SPACE, and check_refusal_submit (FT:656-665) holds by L3. The world after both is B7 of the
   contract: the session writes only the tail of g_s from s->queue on (R_sq), and D4 (agree_q) holds of it. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SimLib QueueFacts SubmitLib.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the session's queue in raw mode *)

(* the tail of g_s from s->queue[0] on (queue[512], queued, stats): what diginet_session_submit writes *)
Definition R_sq (a : Z) : Prop := OFF_g_s + 1760 <= a < OFF_g_s + SZ_g_s.

(* a frame through writes in R_sq (wfr with R_sq unfolded) *)
Ltac wfr_sq := lazymatch goal with
  | |- wframe _ ?B ?B => apply wframe_refl
  | |- wframe _ _ _ => apply wframe_upd_r;
      [wfr_sq | wlen | woffs | woffs | let a := fresh "a" in let H := fresh "H" in intros a H; revert H; unfold R_sq; woffs]
  end.

(* D4's entry, over the 32 bytes of s->queue[i] *)
Definition ent_ok (e : list byte) : Prop :=
  1 <= cmd_len_of e <= 24 /\ system_at (firstn (Z.to_nat (cmd_len_of e)) (firstn 24 e)) = false.
(* D4 *)
Definition q_ok (B : list byte) : Prop :=
  S_queued B <= QUEUE_MAX /\ forall i, 0 <= i < S_queued B -> ent_ok (sq_ent B i).

Lemma S_queued_nonneg : forall X, 0 <= S_queued X.
Proof. intros X. apply u_at_nonneg. Qed.

Lemma cmd_len_nonneg : forall c, 0 <= cmd_len_of c.
Proof. intros c. apply u_at_nonneg. Qed.

(* the writes of DS:333, :339-341, :347-348, read back *)
Lemma S_queued_refused : forall X v, length X = WN -> S_queued (set_S_stats_refused X v) = S_queued X.
Proof. intros X v HX. unfold S_queued, u_at, set_S_stats_refused. rd1. reflexivity. Qed.

Lemma S_queued_coal : forall X v, length X = WN -> S_queued (set_S_stats_coalesced X v) = S_queued X.
Proof. intros X v HX. unfold S_queued, u_at, set_S_stats_coalesced. rd1. reflexivity. Qed.

Lemma S_queued_upd_ent : forall X i e, length X = WN -> 0 <= i < S_queue_N -> length e = 32%nat ->
  S_queued (upd X (A_S_queue_bytes i) e) = S_queued X.
Proof. intros X i e HX Hi He. unfold S_queued, u_at. rd1. reflexivity. Qed.

Lemma S_queued_set : forall X v, length X = WN -> 0 <= v < 2 ^ 32 -> S_queued (set_S_queued X v) = v.
Proof.
  intros X v HX Hv. unfold S_queued, set_S_queued, u_at. rewrite rd_put by (first [wlen | woffs]).
  apply bytes_put_small. change (8 * Z.of_nat 4) with 32. exact Hv.
Qed.

Lemma sq_ent_refused : forall X v j, length X = WN -> 0 <= j < S_queue_N ->
  sq_ent (set_S_stats_refused X v) j = sq_ent X j.
Proof. intros X v j HX Hj. unfold sq_ent, set_S_stats_refused. rd1. reflexivity. Qed.

Lemma sq_ent_coal : forall X v j, length X = WN -> 0 <= j < S_queue_N ->
  sq_ent (set_S_stats_coalesced X v) j = sq_ent X j.
Proof. intros X v j HX Hj. unfold sq_ent, set_S_stats_coalesced. rd1. reflexivity. Qed.

Lemma sq_ent_queued : forall X v j, length X = WN -> 0 <= j < S_queue_N ->
  sq_ent (set_S_queued X v) j = sq_ent X j.
Proof. intros X v j HX Hj. unfold sq_ent, set_S_queued. rd1. reflexivity. Qed.

(* D4 through each branch of DS:328-349 *)
Lemma q_ok_refused : forall X v, length X = WN -> q_ok X -> q_ok (set_S_stats_refused X v).
Proof.
  intros X v HX [Hq He]. split.
  - rewrite (S_queued_refused X v HX). exact Hq.
  - intros j Hj. rewrite (S_queued_refused X v HX) in Hj.
    rewrite (sq_ent_refused X v j HX) by (unfold S_queue_N, QUEUE_MAX in *; lia). apply He. exact Hj.
Qed.

Lemma q_ok_coalesce : forall X i e v, length X = WN -> length e = 32%nat -> q_ok X -> 0 <= i < S_queued X ->
  ent_ok e -> q_ok (set_S_stats_coalesced (upd X (A_S_queue_bytes i) e) v).
Proof.
  intros X i e v HX He [Hq Hen] Hi Hok.
  assert (Hi' : 0 <= i < S_queue_N) by (unfold S_queue_N, QUEUE_MAX in *; lia).
  assert (HX1 : length (upd X (A_S_queue_bytes i) e) = WN) by wlen.
  assert (EQ : S_queued (set_S_stats_coalesced (upd X (A_S_queue_bytes i) e) v) = S_queued X).
  { rewrite (S_queued_coal _ v HX1). exact (S_queued_upd_ent X i e HX Hi' He). }
  split.
  - rewrite EQ. exact Hq.
  - intros j Hj. rewrite EQ in Hj.
    assert (Hj' : 0 <= j < S_queue_N) by (unfold S_queue_N, QUEUE_MAX in *; lia).
    rewrite (sq_ent_coal _ v j HX1 Hj'), (sq_ent_upd X i j e HX Hi' Hj' He).
    destruct (Z.eqb_spec i j); [exact Hok | apply Hen; exact Hj].
Qed.

Lemma q_ok_append : forall X e, length X = WN -> length e = 32%nat -> q_ok X -> S_queued X < QUEUE_MAX ->
  ent_ok e -> q_ok (set_S_queued (upd X (A_S_queue_bytes (S_queued X)) e) (u32 (S_queued X + 1))).
Proof.
  intros X e HX He [Hq Hen] Hlt Hok.
  pose proof (S_queued_nonneg X) as Hq0.
  assert (Hi' : 0 <= S_queued X < S_queue_N) by (unfold S_queue_N, QUEUE_MAX in *; lia).
  assert (HX1 : length (upd X (A_S_queue_bytes (S_queued X)) e) = WN) by wlen.
  assert (EQ : S_queued (set_S_queued (upd X (A_S_queue_bytes (S_queued X)) e) (u32 (S_queued X + 1))) =
               S_queued X + 1).
  { rewrite (S_queued_set _ (u32 (S_queued X + 1)) HX1) by (unfold u32; apply Z.mod_pos_bound; lia).
    unfold u32. apply Z.mod_small. unfold QUEUE_MAX in Hlt. lia. }
  split.
  - rewrite EQ. unfold QUEUE_MAX in *. lia.
  - intros j Hj. rewrite EQ in Hj.
    assert (Hj' : 0 <= j < S_queue_N) by (unfold S_queue_N, QUEUE_MAX in *; lia).
    rewrite (sq_ent_queued _ _ j HX1 Hj'), (sq_ent_upd X (S_queued X) j e HX Hi' Hj' He).
    destruct (Z.eqb_spec (S_queued X) j); [exact Hok | apply Hen; lia].
Qed.

(* a command the body check accepts, of 1 to 24 bytes, is a D4 entry *)
Lemma ent_ok_cs : forall cs, 1 <= cmd_len_of cs <= 24 ->
  body_check (firstn (Z.to_nat (cmd_len_of cs)) cs) = DIGINET_OK -> ent_ok cs.
Proof.
  intros cs Hl Hok. unfold ent_ok. split; [exact Hl|].
  rewrite firstn_firstn, (Nat.min_l _ 24) by lia.
  destruct (system_at (firstn (Z.to_nat (cmd_len_of cs)) cs)) eqn:Es; [|reflexivity].
  exfalso. apply (proj2 (body_check_refused _)) in Es. rewrite Hok in Es. unfold DIGINET_OK in Es. discriminate Es.
Qed.

(* diginet_session_submit (DS:328-349) in raw mode: the writes stay in R_sq, D4 holds after, and the answer
   is E_ARG (len 0), E_REFUSED (the body check refuses; the queue unchanged), or not E_REFUSED (accepted) *)
Lemma submit_spec_raw : forall B1 cs, length B1 = WN -> length cs = 32%nat -> 0 <= cmd_len_of cs <= 24 ->
  q_ok B1 ->
  let '(B3, rc) := submit_spec B1 cs in
  wframe R_sq B1 B3 /\ q_ok B3 /\
  ((cmd_len_of cs = 0 /\ rc = DIGINET_E_ARG) \/
   (body_check (firstn (Z.to_nat (cmd_len_of cs)) cs) <> DIGINET_OK /\ rc = DIGINET_E_REFUSED /\
    S_queued B3 = S_queued B1) \/
   (body_check (firstn (Z.to_nat (cmd_len_of cs)) cs) = DIGINET_OK /\ rc <> DIGINET_E_REFUSED)).
Proof.
  intros B1 cs HB Hcs Hle Hq1.
  pose proof (S_queued_nonneg B1) as Hq0. pose proof (proj1 Hq1) as Hqm.
  unfold submit_spec. cbv zeta.
  destruct (Z.eqb_spec (cmd_len_of cs) 0) as [E0|E0]; cbn [orb].
  { split; [apply wframe_refl|]. split; [exact Hq1|]. left. split; [exact E0 | reflexivity]. }
  destruct (Z.ltb_spec DIGINET_CMD_MAX_LEN (cmd_len_of cs)) as [E1|E1];
    [exfalso; unfold DIGINET_CMD_MAX_LEN in E1; lia|].
  cbn [orb].
  destruct (Z.eqb_spec (body_check (firstn (Z.to_nat (cmd_len_of cs)) cs)) DIGINET_OK) as [Hok|Hno];
    cbn [negb].
  2: { split; [unfold set_S_stats_refused; wfr_sq|]. split; [exact (q_ok_refused B1 _ HB Hq1)|].
       right; left. split; [exact Hno|]. split; [reflexivity | exact (S_queued_refused B1 _ HB)]. }
  assert (Hent : ent_ok cs) by (apply ent_ok_cs; [lia | exact Hok]).
  remember (if coalescable_m (cmd_key_of cs) =? 0 then None
            else first_idx (fun j => S_queue_key B1 j =? cmd_key_of cs) 0 (Z.to_nat (S_queued B1)))
    as found eqn:Ef.
  destruct found as [i|]; cbn [orb].
  - assert (Hi : 0 <= i < S_queued B1).
    { revert Ef. destruct (coalescable_m (cmd_key_of cs) =? 0); intros Ef; [discriminate Ef|].
      cbn [orb] in Ef. symmetry in Ef. apply first_idx_some in Ef. destruct Ef as (Ei & _ & _). lia. }
    split; [unfold set_S_stats_coalesced; wfr_sq|]. split.
    + exact (q_ok_coalesce B1 i cs _ HB Hcs Hq1 Hi Hent).
    + right; right. split; [exact Hok | unfold DIGINET_OK, DIGINET_E_REFUSED; lia].
  - destruct (Z.eqb_spec (S_queued B1) DIGINET_QUEUE_MAX) as [Eqm|Eqm]; cbn [orb].
    + split; [apply wframe_refl|]. split; [exact Hq1|]. right; right.
      split; [exact Hok | unfold DIGINET_E_SPACE, DIGINET_E_REFUSED; lia].
    + assert (Hlt : S_queued B1 < QUEUE_MAX)
        by (destruct Hq1 as [Hq _]; unfold QUEUE_MAX, DIGINET_QUEUE_MAX in *; lia).
      split; [unfold set_S_queued; wfr_sq|]. split; [exact (q_ok_append B1 cs HB Hcs Hq1 Hlt Hent)|].
      right; right. split; [exact Hok | unfold DIGINET_OK, DIGINET_E_REFUSED; lia].
Qed.

Lemma body_check_nil : body_check [] = DIGINET_OK.
Proof. rewrite body_check_spec. reflexivity. Qed.

Lemma refused_eqb : (DIGINET_E_REFUSED =? SPEC_E_REFUSED) = true.
Proof. reflexivity. Qed.

(* check_refusal_submit (FT:656-665) after the session's answer, by L3 *)
Lemma refusal_raw : forall B3 cs rc before, L3_stmt -> length cs = 32%nat -> 0 <= cmd_len_of cs <= 24 ->
  at8 cs 24 = cmd_len_of cs ->
  ((cmd_len_of cs = 0 /\ rc = DIGINET_E_ARG) \/
   (body_check (firstn (Z.to_nat (cmd_len_of cs)) cs) <> DIGINET_OK /\ rc = DIGINET_E_REFUSED /\
    S_queued B3 = before) \/
   (body_check (firstn (Z.to_nat (cmd_len_of cs)) cs) = DIGINET_OK /\ rc <> DIGINET_E_REFUSED)) ->
  check_refusal_submit_m B3 cs rc before = Some (B3, tt).
Proof.
  intros B3 cs rc before L3 Hcs Hle Hat Hcase.
  destruct (L3 cs (cmd_len_of cs) ltac:(rewrite Hcs; lia)) as (L3a & _ & _).
  unfold check_refusal_submit_m. cbv zeta. rewrite Hat.
  destruct (Nat.ltb_spec (length cs) 25) as [X|_]; [lia|].
  destruct (Z.ltb_spec (Z.of_nat (length cs)) (cmd_len_of cs)) as [X|_]; [lia|].
  cbn [orb].
  destruct (Z.leb_spec 0 (spec_system_at (zs cs) (cmd_len_of cs))) as [Hs|Hs].
  - assert (Hno : body_check (firstn (Z.to_nat (cmd_len_of cs)) cs) <> DIGINET_OK)
      by (intros H; apply L3a in H; lia).
    destruct Hcase as [(E0 & _) | [(_ & Erc & Ebf) | (Hok & _)]].
    + exfalso. apply Hno. rewrite E0. exact body_check_nil.
    + subst rc. rewrite Ebf, (Z.eqb_refl before), refused_eqb. reflexivity.
    + exfalso. exact (Hno Hok).
  - assert (Hok : body_check (firstn (Z.to_nat (cmd_len_of cs)) cs) = DIGINET_OK) by (apply L3a; exact Hs).
    destruct Hcase as [(_ & Erc) | [(Hno & _ & _) | (_ & Hrc)]].
    + subst rc. reflexivity.
    + exfalso. exact (Hno Hok).
    + destruct (Z.eqb_spec rc SPEC_E_REFUSED) as [X|_]; [|reflexivity].
      exfalso. apply Hrc. rewrite X. reflexivity.
Qed.

(* the session, then the check: the B3 of op_submit_m's raw branch *)
Lemma submit_raw_session : forall B1 cs before, links -> length B1 = WN -> length cs = 32%nat ->
  0 <= cmd_len_of cs <= 24 -> at8 cs 24 = cmd_len_of cs -> q_ok B1 -> S_queued B1 = before ->
  exists B3 rc, diginet_session_submit_m B1 cs = Some (B3, rc) /\
    check_refusal_submit_m B3 cs rc before = Some (B3, tt) /\ wframe R_sq B1 B3 /\ q_ok B3.
Proof.
  intros B1 cs before HL HB Hcs Hle Hat Hq1 Hbef.
  destruct HL as (_ & _ & L3 & _).
  rewrite submit_m_spec by (destruct Hq1 as [Hq _]; unfold S_queue_N; unfold QUEUE_MAX in Hq; lia).
  pose proof (submit_spec_raw B1 cs HB Hcs Hle Hq1) as H. revert H.
  destruct (submit_spec B1 cs) as [B3 rc]. intros H. cbv beta iota in H. destruct H as (Hfr & Hq3 & Hcase).
  exists B3, rc. split; [reflexivity|]. split; [|split; [exact Hfr | exact Hq3]].
  apply (refusal_raw B3 cs rc before L3 Hcs Hle Hat).
  destruct Hcase as [C | [(C1 & C2 & C3) | C]]; [left; exact C | right; left | right; right; exact C].
  split; [exact C1|]. split; [exact C2|]. rewrite C3. exact Hbef.
Qed.

(* ---------------------------------------------------------------- the command op_submit builds (FT:1079-1080) *)

Lemma cs_raw_facts : forall D off t d k cs, 0 <= off -> 0 <= t <= 24 -> off + t <= Z.of_nat (length D) ->
  cs = cmd_struct (sub D off (Z.to_nat t) ++ repeat (b8 0) (Z.to_nat (24 - t))) t d k ->
  length cs = 32%nat /\ cmd_len_of cs = t /\ at8 cs 24 = t.
Proof.
  intros D off t d k cs H0 Ht HD Ecs.
  assert (Hb : length (sub D off (Z.to_nat t) ++ repeat (b8 0) (Z.to_nat (24 - t))) = 24%nat).
  { rewrite length_app, (length_sub_D D off t H0 (proj1 Ht) HD), repeat_length. lia. }
  subst cs. revert Hb. generalize (sub D off (Z.to_nat t) ++ repeat (b8 0) (Z.to_nat (24 - t))) as cb.
  intros cb Hb. unfold cmd_struct.
  assert (Ht8 : 0 <= t < 2 ^ 8) by lia.
  split; [|split].
  - rewrite !length_app, length_put, Hb. reflexivity.
  - unfold cmd_len_of, u_at, sub. change (Z.to_nat 24) with 24%nat.
    rewrite skipn_app. replace (skipn 24 cb) with (@nil byte) by (symmetry; apply skipn_all2; lia).
    rewrite Hb, Nat.sub_diag. cbn [app skipn firstn bytes_le_to_Z].
    rewrite Z.shiftl_0_l, Z.lor_0_r. exact (bz_b8 t Ht8).
  - unfold at8. rewrite app_nth2 by lia. rewrite Hb, Nat.sub_diag. cbn [app nth]. exact (bz_b8 t Ht8).
Qed.

(* ---------------------------------------------------------------- agree_q after the raw submit *)

Lemma raw_frame : forall (R : Z -> Prop) B B', wframe R B B' ->
  (forall a, OFF_g_raw <= a < OFF_g_raw + 4 -> ~ R a) -> g_raw B' = g_raw B.
Proof. intros R B B' Hf HR. unfold g_raw. apply (wframe_s32_at R B B' OFF_g_raw Hf); [unfold OFF_g_raw; lia | exact HR]. Qed.

Lemma q_ok_frame : forall (R : Z -> Prop) B B', wframe R B B' ->
  (forall a, OFF_g_s + 1760 <= a < OFF_g_s + 18148 -> ~ R a) -> q_ok B -> q_ok B'.
Proof.
  intros R B B' Hf HR [Hq He].
  assert (EQ : S_queued B' = S_queued B).
  { unfold S_queued. apply (wframe_u_at R B B' A_S_queued 4 Hf); [unfold A_S_queued, OFF_g_s; lia|].
    intros a Ha. apply HR. unfold A_S_queued in Ha. lia. }
  split; [rewrite EQ; exact Hq|].
  intros i Hi. rewrite EQ in Hi.
  assert (E : sq_ent B' i = sq_ent B i).
  { unfold sq_ent. apply (wframe_sub R B B' _ 32 Hf); [unfold A_S_queue_bytes, OFF_g_s; lia|].
    intros a Ha. apply HR. unfold QUEUE_MAX, A_S_queue_bytes in *. lia. }
  rewrite E. apply He. exact Hi.
Qed.

Lemma q_ok_of_agree : forall ops B, agree_q ops B -> g_raw B <> 0 -> q_ok B.
Proof.
  intros ops B HQ Hraw. split; [exact (d4_queued _ _ HQ Hraw)|].
  intros i Hi. destruct (d4_entry _ _ HQ Hraw i Hi) as [H1 H2].
  rewrite (S_queue_len_ent B i (proj1 Hi)) in H1, H2. rewrite (S_queue_bytes_ent B i (proj1 Hi)) in H2.
  split; [exact H1 | exact H2].
Qed.

(* D1-D4 after op_begin (R_ob) and the session (R_sq): D1 is vacuous (raw), D2 and D3 read g_cmd and g_ncmd,
   which neither writes; D4 is q_ok *)
Lemma agree_q_raw : forall ops B B7, agree_q ops B -> g_raw B <> 0 -> ops < OPS_MAX ->
  wframe (fun a => R_ob a \/ R_sq a) B B7 -> q_ok B7 -> agree_q (ops + 1) B7.
Proof.
  intros ops B B7 HQ Hraw Hops Hf [Hq He].
  assert (Er : g_raw B7 = g_raw B).
  { apply (raw_frame _ B B7 Hf). intros a Ha. cbv beta. unfold R_sq. woffs. }
  assert (En : g_ncmd B7 = g_ncmd B).
  { unfold g_ncmd. apply (wframe_u_at _ B B7 OFF_g_ncmd 4 Hf); [unfold OFF_g_ncmd; lia|].
    intros a Ha. cbv beta. unfold R_sq. woffs. }
  assert (Ec : forall k, 0 <= k < CMDS_MAX -> Cmd_st B7 k = Cmd_st B k /\ Cmd_bytes B7 k = Cmd_bytes B k /\
                 Cmd_len B7 k = Cmd_len B k /\ Cmd_display B7 k = Cmd_display B k).
  { intros k Hk. unfold Cmd_st, Cmd_bytes, Cmd_len, Cmd_display. split; [|split; [|split]].
    - apply (wframe_s32_at _ B B7 _ Hf); [unfold A_Cmd_st, OFF_g_cmd, CMDS_MAX in *; lia|].
      intros a Ha. cbv beta. unfold R_sq. woffs.
    - apply (wframe_sub _ B B7 _ _ Hf); [unfold A_Cmd_bytes, OFF_g_cmd, CMDS_MAX in *; lia|].
      intros a Ha. cbv beta. unfold R_sq. woffs.
    - apply (wframe_u_at _ B B7 _ _ Hf); [unfold A_Cmd_len, OFF_g_cmd, CMDS_MAX in *; lia|].
      intros a Ha. cbv beta. unfold R_sq. woffs.
    - apply (wframe_s32_at _ B B7 _ Hf); [unfold A_Cmd_display, OFF_g_cmd, CMDS_MAX in *; lia|].
      intros a Ha. cbv beta. unfold R_sq. woffs. }
  constructor.
  1-5: intros H; rewrite Er in H; exfalso; exact (Hraw H).
  - intros k Hk Hst. rewrite En in Hk. pose proof (d3_ncmd _ _ HQ) as Hn.
    assert (Hk' : 0 <= k < CMDS_MAX) by (unfold CMDS_MAX, OPS_MAX in *; lia).
    destruct (Ec k Hk') as (E1 & E2 & E3 & E4). rewrite E1 in Hst. rewrite E2, E3, E4.
    exact (d2_cmd _ _ HQ k Hk Hst).
  - rewrite En. pose proof (d3_ncmd _ _ HQ). lia.
  - pose proof (d3_ops _ _ HQ). unfold OPS_MAX in *. lia.
  - intros _. exact Hq.
  - intros _ i Hi. destruct (He i Hi) as [H1 H2].
    rewrite (S_queue_len_ent B7 i (proj1 Hi)), (S_queue_bytes_ent B7 i (proj1 Hi)).
    split; [exact H1 | exact H2].
Qed.

(* ---------------------------------------------------------------- op 4, raw mode, up to settle(0) (FT:1083) *)

Lemma submit_raw_pre : forall I ops B D c, links -> agree I ops B -> ops < OPS_MAX -> g_raw B <> 0 -> fuzz_in_ok D c ->
  exists B1 B7 c5, op_begin_m B = Some (B1, tt) /\ wframe R4q B1 B7 /\ agree_q (ops + 1) B7 /\ fuzz_in_ok D c5 /\
    op_submit_m B D c = match settle_m B7 0 with Some (B8, _) => Some (B8, c5) | None => None end.
Proof.
  intros I ops B D c HL HA Hops Hraw Hc.
  assert (HB : length B = WN) by exact (ac_len _ _ _ (ag_core _ _ _ HA)).
  pose proof (ac_q _ _ _ (ag_core _ _ _ HA)) as HQ. clear HA.
  (* op_begin (FT:1074) *)
  destruct (op_begin_stage B HB) as (B1 & Hob & Hf1 & _ & _).
  assert (HB1 : length B1 = WN) by (rewrite (proj1 Hf1); exact HB).
  assert (Er1 : g_raw B1 = g_raw B) by (apply (raw_frame R_ob B B1 Hf1); intros a Ha; woffs).
  assert (Eq1 : S_queued B1 = S_queued B).
  { unfold S_queued. apply (wframe_u_at R_ob B B1 A_S_queued 4 Hf1); [unfold A_S_queued, OFF_g_s; lia|].
    intros a Ha. woffs. }
  assert (Hq1 : q_ok B1).
  { apply (q_ok_frame R_ob B B1 Hf1); [intros a Ha; woffs | exact (q_ok_of_agree ops B HQ Hraw)]. }
  (* the cursor (FT:1076-1079) *)
  destruct (fuzz_u8_ok D c Hc) as (c1 & kb & E1 & Hc1 & _).
  destruct (fuzz_u8_ok D c1 Hc1) as (c2 & ab & E2 & Hc2 & _).
  destruct (fuzz_u8_ok D c2 Hc2) as (c3 & db & E3 & Hc3 & _).
  destruct (fuzz_u16_ok D c3 Hc3) as (c4 & w & E4 & Hc4 & _).
  pose proof (Z.mod_pos_bound w (SPEC_CMD_MAX + 1) ltac:(unfold SPEC_CMD_MAX; lia)) as Hw.
  destruct (fuzz_take_ok D c4 (w mod (SPEC_CMD_MAX + 1)) Hc4 (proj1 Hw))
    as (c5 & off & t & E5 & Hc5 & Ht & Hoff & HtD & _).
  assert (Ht24 : 0 <= t <= 24) by (unfold SPEC_CMD_MAX in Hw, Ht; lia).
  assert (Etm : t mod 2 ^ 8 = t) by (apply Z.mod_small; lia).
  (* the command (FT:1079-1080) *)
  remember (cmd_struct (sub D off (Z.to_nat t) ++ repeat (b8 0) (Z.to_nat (24 - t))) t (Z.land db 1)
              (KEY (kb mod 9 + 1) ab)) as cs eqn:Ecs.
  destruct (cs_raw_facts D off t (Z.land db 1) (KEY (kb mod 9 + 1) ab) cs Hoff Ht24 HtD Ecs)
    as (Hcs & Hlen & Hat).
  (* the session and check_refusal_submit (FT:1081-1082) *)
  destruct (submit_raw_session B1 cs (S_queued B) HL HB1 Hcs ltac:(rewrite Hlen; lia)
              ltac:(rewrite Hat, Hlen; reflexivity) Hq1 Eq1) as (B3 & rc & Esub & Eref & Hfr & Hq3).
  assert (Hf : wframe (fun a => R_ob a \/ R_sq a) B B3).
  { apply (wframe_trans _ B B1 B3).
    - apply (wframe_weaken R_ob); [intros a Ha; left; exact Ha | exact Hf1].
    - apply (wframe_weaken R_sq); [intros a Ha; right; exact Ha | exact Hfr]. }
  exists B1, B3, c5. split; [exact Hob|]. split.
  { apply (wframe_weaken R_sq); [intros a Ha; left; exact Ha | exact Hfr]. }
  split; [exact (agree_q_raw ops B B3 HQ Hraw Hops Hf Hq3)|].
  split; [exact Hc5|].
  (* op_submit_m's raw branch, step by step *)
  unfold op_submit_m. rewrite Hob. cbv beta iota zeta.
  rewrite E1. cbv beta iota. rewrite E2. cbv beta iota. rewrite E3. cbv beta iota.
  rewrite Er1. destruct (Z.eqb_spec (g_raw B) 0) as [X|_]; [exfalso; exact (Hraw X)|]. cbn [negb].
  rewrite E4. cbv beta iota. rewrite E5. cbv beta iota. rewrite Etm. rewrite <- Ecs.
  rewrite Esub. cbv beta iota. rewrite Eref. cbv beta iota. reflexivity.
Qed.
