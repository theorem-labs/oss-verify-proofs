(* fuzz_transport.c:1068-1122 op_submit (FT) with g_raw == 0, TOps.v op_submit_m, against diginet_session.c:328-349
   diginet_session_submit (DS; QueueFacts.v submit_spec). submit_tagged_pre: after op_begin (FT:1074) the harness
   reads the key, display and length bytes (FT:1076-1092), zeroes g_cmd[serial] (FT:1087), finds the place `at`
   (FT:1097-1101), calls the session's submit (FT:1103), runs check_refusal_submit (FT:1104, by L3) and
   check_latest_submit (FT:1106), records the command (FT:1107-1119) and counts it (FT:1120). The world B7 then
   holds agree_q (ops + 1), differs from op_begin's world only in R4q, and op 4 is settle(0) of B7.
   Outcomes: refused (the body holds a system message), E_SPACE (512 pending, no place), coalesced at `at`,
   appended. Each stage is a lemma over abstract worlds; aq_noop / aq_coalesce / aq_append close agree_q from the
   stage facts, and aq_transfer carries agree_q across op_begin. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SimLib QueueFacts SubmitLib.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- agree_q after the op, from the getters
   (pure logic: every getter application is an atom) *)

(* g_cmd[k] other than its st: the same in X and Y *)
Definition cmd_same (X Y : list byte) (k : Z) : Prop :=
  Cmd_key Y k = Cmd_key X k /\ Cmd_display Y k = Cmd_display X k /\ Cmd_len Y k = Cmd_len X k /\
  Cmd_bytes Y k = Cmd_bytes X k.

(* the new command g_cmd[s] the harness records (fuzz_transport.c:1089-1096, :1108-1112) *)
Definition new_cmd_ok (s key disp len : Z) (cb : list byte) : Prop :=
  at8 cb 0 = TAG /\ at8 cb 1 = Z.land s 0x7f /\ at8 cb 2 = Z.land (Z.shiftr s 7) 0x7f /\ 3 <= len <= 24 /\
  bit01 disp /\ system_at (firstn (Z.to_nat len) cb) = false.

(* the 32-byte struct diginet_cmd the session stored (diginet_session.c:339, :347) *)
Definition new_ent_ok (e : list byte) (key disp len : Z) (cb : list byte) : Prop :=
  firstn 24 e = cb /\ cmd_len_of e = len /\ cmd_key_of e = key /\ cmd_display_of e = disp.

(* index bounds (pure arithmetic over atoms) *)
Lemma sqt_kb : forall ops nc k, nc <= ops -> 0 <= ops <= OPS_MAX -> 0 <= k < nc -> 0 <= k < CMDS_MAX.
Proof. intros ops nc k H1 H2 H3. unfold OPS_MAX, CMDS_MAX in *. lia. Qed.

Lemma sqt_qb : forall n i, n <= QUEUE_MAX -> 0 <= i < n -> 0 <= i < QUEUE_MAX.
Proof. intros n i H1 H2. lia. Qed.

Lemma sqt_qb1 : forall n i, n < QUEUE_MAX -> 0 <= i < n + 1 -> 0 <= i < QUEUE_MAX.
Proof. intros n i H1 H2. lia. Qed.

Lemma sqt_lt : forall n i, 0 <= i < n + 1 -> i <> n -> 0 <= i < n.
Proof. intros n i H1 H2. lia. Qed.

(* agree_q reads only these getters: equal getters, equal agree_q *)
Lemma aq_transfer : forall ops X Y, agree_q ops X ->
  g_raw Y = g_raw X -> S_queued Y = S_queued X -> g_nq Y = g_nq X -> g_ncmd Y = g_ncmd X ->
  (forall j, 0 <= j < QUEUE_MAX -> Q_at Y j = Q_at X j) ->
  (forall k, 0 <= k < CMDS_MAX -> Cmd_st Y k = Cmd_st X k /\ cmd_same X Y k) ->
  (forall i, 0 <= i < QUEUE_MAX -> sq_ent Y i = sq_ent X i) ->
  agree_q ops Y.
Proof.
  intros ops X Y HX Hraw Hsq Hnq Hnc HQ HC HE.
  destruct HX as [Q1 N1 E1 ND1 P1 C2 N3 O3 Q4 E4].
  constructor.
  - intros Hr. rewrite Hraw in Hr. rewrite Hsq, Hnq. exact (Q1 Hr).
  - intros Hr. rewrite Hraw in Hr. rewrite Hnq. exact (N1 Hr).
  - intros Hr i Hi. rewrite Hraw in Hr. rewrite Hnq in Hi.
    pose proof (sqt_qb _ _ (N1 Hr) Hi) as Hi'.
    rewrite (HQ i Hi'), Hnc.
    destruct (E1 Hr i Hi) as [Hb _].
    pose proof (sqt_kb _ _ _ N3 O3 Hb) as Hq.
    destruct (HC (Q_at X i) Hq) as [Hst Hsm]. unfold cmd_same in Hsm. destruct Hsm as (Hk1 & Hd1 & Hl1 & Hb1).
    rewrite Hst, Hk1, Hd1, Hl1, Hb1.
    rewrite (S_queue_bytes_ent Y i (proj1 Hi)), (S_queue_len_ent Y i (proj1 Hi)),
      (S_queue_key_ent Y i (proj1 Hi)), (S_queue_display_ent Y i (proj1 Hi)), (HE i Hi'),
      <- (S_queue_bytes_ent X i (proj1 Hi)), <- (S_queue_len_ent X i (proj1 Hi)),
      <- (S_queue_key_ent X i (proj1 Hi)), <- (S_queue_display_ent X i (proj1 Hi)).
    exact (E1 Hr i Hi).
  - intros Hr i j Hi Hj Hij. rewrite Hraw in Hr. rewrite Hnq in Hi, Hj.
    pose proof (sqt_qb _ _ (N1 Hr) Hi) as Hi'. pose proof (sqt_qb _ _ (N1 Hr) Hj) as Hj'.
    exact (ND1 Hr i j Hi Hj (eq_trans (eq_sym (HQ i Hi')) (eq_trans Hij (HQ j Hj')))).
  - intros Hr k Hk. rewrite Hraw in Hr. rewrite Hnc in Hk.
    pose proof (sqt_kb _ _ _ N3 O3 Hk) as Hk'.
    destruct (HC k Hk') as [Hst _]. rewrite Hst. split.
    + intros H. destruct (proj1 (P1 Hr k Hk) H) as [i [Hi Hqi]].
      exists i. rewrite Hnq. split; [exact Hi|].
      rewrite (HQ i (sqt_qb _ _ (N1 Hr) Hi)). exact Hqi.
    + intros [i [Hi Hqi]]. rewrite Hnq in Hi. apply (proj2 (P1 Hr k Hk)).
      exists i. split; [exact Hi|]. exact (eq_trans (eq_sym (HQ i (sqt_qb _ _ (N1 Hr) Hi))) Hqi).
  - intros k Hk Hst. rewrite Hnc in Hk.
    pose proof (sqt_kb _ _ _ N3 O3 Hk) as Hk'.
    destruct (HC k Hk') as [Hst1 Hsm]. unfold cmd_same in Hsm. destruct Hsm as (Hk1 & Hd1 & Hl1 & Hb1).
    rewrite Hst1 in Hst. rewrite Hb1, Hl1, Hd1. exact (C2 k Hk Hst).
  - rewrite Hnc. exact N3.
  - exact O3.
  - intros Hr. rewrite Hraw in Hr. rewrite Hsq. exact (Q4 Hr).
  - intros Hr i Hi. rewrite Hraw in Hr. rewrite Hsq in Hi.
    pose proof (sqt_qb _ _ (Q4 Hr) Hi) as Hi'.
    rewrite (S_queue_len_ent Y i (proj1 Hi)), (S_queue_bytes_ent Y i (proj1 Hi)), (HE i Hi'),
      <- (S_queue_len_ent X i (proj1 Hi)), <- (S_queue_bytes_ent X i (proj1 Hi)).
    exact (E4 Hr i Hi).
Qed.

(* refused or E_SPACE: g_cmd[s] zeroed (st 0), g_ncmd + 1, the queues unchanged *)
Lemma aq_noop : forall ops X Y s, agree_q ops X -> g_raw X = 0 -> ops < OPS_MAX -> s = g_ncmd X ->
  g_raw Y = 0 -> S_queued Y = S_queued X -> g_nq Y = g_nq X -> g_ncmd Y = s + 1 ->
  (forall j, 0 <= j < QUEUE_MAX -> Q_at Y j = Q_at X j) ->
  Cmd_st Y s = 0 ->
  (forall k, 0 <= k < CMDS_MAX -> k <> s -> Cmd_st Y k = Cmd_st X k /\ cmd_same X Y k) ->
  (forall i, 0 <= i < QUEUE_MAX -> sq_ent Y i = sq_ent X i) ->
  agree_q (ops + 1) Y.
Proof.
  intros ops X Y s HX Hr0 Hops Hs HrY Hsq Hnq Hnc HQ Hst0 HC HE.
  destruct HX as [Q1 N1 E1 ND1 P1 C2 N3 O3 Q4 E4].
  constructor.
  - intros _. rewrite Hsq, Hnq. exact (Q1 Hr0).
  - intros _. rewrite Hnq. exact (N1 Hr0).
  - intros _ i Hi. rewrite Hnq in Hi.
    pose proof (sqt_qb _ _ (N1 Hr0) Hi) as Hi'.
    rewrite (HQ i Hi'), Hnc.
    destruct (E1 Hr0 i Hi) as [Hb _].
    pose proof (sqt_kb _ _ _ N3 O3 Hb) as Hq.
    assert (Hqs : Q_at X i <> s) by (clear - Hb Hs; lia).
    destruct (HC (Q_at X i) Hq Hqs) as [Hst Hsm]. unfold cmd_same in Hsm. destruct Hsm as (Hk1 & Hd1 & Hl1 & Hb1).
    split; [clear - Hb Hs; lia|].
    rewrite Hst, Hk1, Hd1, Hl1, Hb1.
    rewrite (S_queue_bytes_ent Y i (proj1 Hi)), (S_queue_len_ent Y i (proj1 Hi)),
      (S_queue_key_ent Y i (proj1 Hi)), (S_queue_display_ent Y i (proj1 Hi)), (HE i Hi'),
      <- (S_queue_bytes_ent X i (proj1 Hi)), <- (S_queue_len_ent X i (proj1 Hi)),
      <- (S_queue_key_ent X i (proj1 Hi)), <- (S_queue_display_ent X i (proj1 Hi)).
    exact (proj2 (E1 Hr0 i Hi)).
  - intros _ i j Hi Hj Hij. rewrite Hnq in Hi, Hj.
    pose proof (sqt_qb _ _ (N1 Hr0) Hi) as Hi'. pose proof (sqt_qb _ _ (N1 Hr0) Hj) as Hj'.
    exact (ND1 Hr0 i j Hi Hj (eq_trans (eq_sym (HQ i Hi')) (eq_trans Hij (HQ j Hj')))).
  - intros _ k Hk. rewrite Hnc in Hk.
    destruct (Z.eq_dec k s) as [Hks|Hks].
    + subst k. rewrite Hst0. split.
      * intros H. exfalso. clear - H. unfold PENDING in H. lia.
      * intros [i [Hi Hqi]]. exfalso. rewrite Hnq in Hi.
        pose proof (sqt_qb _ _ (N1 Hr0) Hi) as Hi'.
        destruct (E1 Hr0 i Hi) as [Hb _].
        pose proof (eq_trans (eq_sym (HQ i Hi')) Hqi) as Hx.
        clear - Hb Hx Hs. lia.
    + assert (Hkx : 0 <= k < g_ncmd X) by (clear - Hk Hks Hs; lia).
      pose proof (sqt_kb _ _ _ N3 O3 Hkx) as Hk'.
      destruct (HC k Hk' Hks) as [Hst _]. rewrite Hst. split.
      * intros H. destruct (proj1 (P1 Hr0 k Hkx) H) as [i [Hi Hqi]].
        exists i. rewrite Hnq. split; [exact Hi|].
        rewrite (HQ i (sqt_qb _ _ (N1 Hr0) Hi)). exact Hqi.
      * intros [i [Hi Hqi]]. rewrite Hnq in Hi. apply (proj2 (P1 Hr0 k Hkx)).
        exists i. split; [exact Hi|]. exact (eq_trans (eq_sym (HQ i (sqt_qb _ _ (N1 Hr0) Hi))) Hqi).
  - intros k Hk Hst. rewrite Hnc in Hk.
    destruct (Z.eq_dec k s) as [Hks|Hks].
    + subst k. rewrite Hst0 in Hst. exfalso. exact (Hst eq_refl).
    + assert (Hkx : 0 <= k < g_ncmd X) by (clear - Hk Hks Hs; lia).
      pose proof (sqt_kb _ _ _ N3 O3 Hkx) as Hk'.
      destruct (HC k Hk' Hks) as [Hst1 Hsm]. unfold cmd_same in Hsm. destruct Hsm as (Hk1 & Hd1 & Hl1 & Hb1).
      rewrite Hst1 in Hst. rewrite Hb1, Hl1, Hd1. exact (C2 k Hkx Hst).
  - rewrite Hnc. clear - N3 Hs. lia.
  - clear - O3 Hops. lia.
  - intros H. exfalso. exact (H HrY).
  - intros H. exfalso. exact (H HrY).
Qed.

(* coalesced at a: g_q[a] := s, g_cmd[g_q[a]].st := REPLACED, s->queue[a] := the new entry *)
Lemma aq_coalesce : forall ops X Y s a key disp len cb e,
  agree_q ops X -> g_raw X = 0 -> ops < OPS_MAX -> s = g_ncmd X -> 0 <= a < g_nq X ->
  g_raw Y = 0 -> S_queued Y = S_queued X -> g_nq Y = g_nq X -> g_ncmd Y = s + 1 ->
  (forall j, 0 <= j < QUEUE_MAX -> j <> a -> Q_at Y j = Q_at X j) -> Q_at Y a = s ->
  Cmd_st Y s = PENDING -> Cmd_st Y (Q_at X a) = REPLACED ->
  (forall k, 0 <= k < CMDS_MAX -> k <> s -> k <> Q_at X a -> Cmd_st Y k = Cmd_st X k) ->
  (forall k, 0 <= k < CMDS_MAX -> k <> s -> cmd_same X Y k) ->
  Cmd_key Y s = key -> Cmd_display Y s = disp -> Cmd_len Y s = len -> Cmd_bytes Y s = cb ->
  (forall i, 0 <= i < QUEUE_MAX -> i <> a -> sq_ent Y i = sq_ent X i) -> sq_ent Y a = e ->
  new_ent_ok e key disp len cb -> new_cmd_ok s key disp len cb ->
  agree_q (ops + 1) Y.
Proof.
  intros ops X Y s a key disp len cb e HX Hr0 Hops Hs Ha HrY Hsq Hnq Hnc HQ HQa HstS HstQ HC HCs
    Hkey Hdisp Hlen Hcb HE HEa Hent Hcmd.
  destruct HX as [Q1 N1 E1 ND1 P1 C2 N3 O3 Q4 E4].
  destruct (E1 Hr0 a Ha) as [Hqa [HPa _]].
  constructor.
  - intros _. rewrite Hsq, Hnq. exact (Q1 Hr0).
  - intros _. rewrite Hnq. exact (N1 Hr0).
  - intros _ i Hi. rewrite Hnq in Hi.
    pose proof (sqt_qb _ _ (N1 Hr0) Hi) as Hi'.
    rewrite Hnc.
    destruct (Z.eq_dec i a) as [Hia|Hia].
    + subst i. rewrite HQa, HstS, Hkey, Hdisp, Hlen, Hcb.
      rewrite (S_queue_bytes_ent Y a (proj1 Ha)), (S_queue_len_ent Y a (proj1 Ha)),
        (S_queue_key_ent Y a (proj1 Ha)), (S_queue_display_ent Y a (proj1 Ha)), HEa.
      unfold new_ent_ok in Hent. destruct Hent as (H1 & H2 & H3 & H4).
      rewrite H1, H2, H3, H4.
      split; [clear - Hqa Hs; lia|].
      exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
    + rewrite (HQ i Hi' Hia).
      destruct (E1 Hr0 i Hi) as [Hb _].
      pose proof (sqt_kb _ _ _ N3 O3 Hb) as Hq.
      assert (Hqis : Q_at X i <> s) by (clear - Hb Hs; lia).
      assert (Hqiq : Q_at X i <> Q_at X a) by (intros Heq; exact (Hia (ND1 Hr0 i a Hi Ha Heq))).
      pose proof (HC (Q_at X i) Hq Hqis Hqiq) as Hst.
      pose proof (HCs (Q_at X i) Hq Hqis) as Hsm. unfold cmd_same in Hsm. destruct Hsm as (Hk1 & Hd1 & Hl1 & Hb1).
      split; [clear - Hb Hs; lia|].
      rewrite Hst, Hk1, Hd1, Hl1, Hb1.
      rewrite (S_queue_bytes_ent Y i (proj1 Hi)), (S_queue_len_ent Y i (proj1 Hi)),
        (S_queue_key_ent Y i (proj1 Hi)), (S_queue_display_ent Y i (proj1 Hi)), (HE i Hi' Hia),
        <- (S_queue_bytes_ent X i (proj1 Hi)), <- (S_queue_len_ent X i (proj1 Hi)),
        <- (S_queue_key_ent X i (proj1 Hi)), <- (S_queue_display_ent X i (proj1 Hi)).
      exact (proj2 (E1 Hr0 i Hi)).
  - intros _ i j Hi Hj Hij. rewrite Hnq in Hi, Hj.
    pose proof (sqt_qb _ _ (N1 Hr0) Hi) as Hi'. pose proof (sqt_qb _ _ (N1 Hr0) Hj) as Hj'.
    destruct (Z.eq_dec i a) as [Hia|Hia]; destruct (Z.eq_dec j a) as [Hja|Hja].
    + exact (eq_trans Hia (eq_sym Hja)).
    + exfalso. subst i.
      pose proof (eq_trans (eq_sym HQa) (eq_trans Hij (HQ j Hj' Hja))) as Hx.
      destruct (E1 Hr0 j Hj) as [Hb _]. clear - Hb Hx Hs. lia.
    + exfalso. subst j.
      pose proof (eq_trans (eq_sym HQa) (eq_trans (eq_sym Hij) (HQ i Hi' Hia))) as Hx.
      destruct (E1 Hr0 i Hi) as [Hb _]. clear - Hb Hx Hs. lia.
    + exact (ND1 Hr0 i j Hi Hj (eq_trans (eq_sym (HQ i Hi' Hia)) (eq_trans Hij (HQ j Hj' Hja)))).
  - intros _ k Hk. rewrite Hnc in Hk.
    destruct (Z.eq_dec k s) as [Hks|Hks].
    + subst k. rewrite HstS. split.
      * intros _. exists a. rewrite Hnq. split; [exact Ha | exact HQa].
      * intros _. reflexivity.
    + destruct (Z.eq_dec k (Q_at X a)) as [Hkq|Hkq].
      * subst k. rewrite HstQ. split.
        -- intros H. exfalso. clear - H. unfold REPLACED, PENDING in H. lia.
        -- intros [i [Hi Hqi]]. exfalso. rewrite Hnq in Hi.
           destruct (Z.eq_dec i a) as [Hia|Hia].
           ++ subst i. pose proof (eq_trans (eq_sym HQa) Hqi) as Hx. exact (Hks (eq_sym Hx)).
           ++ pose proof (eq_trans (eq_sym (HQ i (sqt_qb _ _ (N1 Hr0) Hi) Hia)) Hqi) as Hx.
              exact (Hia (ND1 Hr0 i a Hi Ha Hx)).
      * assert (Hkx : 0 <= k < g_ncmd X) by (clear - Hk Hks Hs; lia).
        pose proof (sqt_kb _ _ _ N3 O3 Hkx) as Hk'.
        rewrite (HC k Hk' Hks Hkq). split.
        -- intros H. destruct (proj1 (P1 Hr0 k Hkx) H) as [i [Hi Hqi]].
           exists i. rewrite Hnq. split; [exact Hi|].
           destruct (Z.eq_dec i a) as [Hia|Hia].
           ++ subst i. exfalso. exact (Hkq (eq_sym Hqi)).
           ++ rewrite (HQ i (sqt_qb _ _ (N1 Hr0) Hi) Hia). exact Hqi.
        -- intros [i [Hi Hqi]]. rewrite Hnq in Hi. apply (proj2 (P1 Hr0 k Hkx)).
           destruct (Z.eq_dec i a) as [Hia|Hia].
           ++ subst i. exfalso. exact (Hks (eq_trans (eq_sym Hqi) HQa)).
           ++ exists i. split; [exact Hi|].
              exact (eq_trans (eq_sym (HQ i (sqt_qb _ _ (N1 Hr0) Hi) Hia)) Hqi).
  - intros k Hk Hst. rewrite Hnc in Hk.
    destruct (Z.eq_dec k s) as [Hks|Hks].
    + subst k. rewrite Hcb, Hlen, Hdisp. unfold new_cmd_ok in Hcmd. exact Hcmd.
    + assert (Hkx : 0 <= k < g_ncmd X) by (clear - Hk Hks Hs; lia).
      pose proof (sqt_kb _ _ _ N3 O3 Hkx) as Hk'.
      pose proof (HCs k Hk' Hks) as Hsm. unfold cmd_same in Hsm. destruct Hsm as (Hk1 & Hd1 & Hl1 & Hb1).
      rewrite Hb1, Hl1, Hd1.
      destruct (Z.eq_dec k (Q_at X a)) as [Hkq|Hkq].
      * subst k. assert (HX0 : Cmd_st X (Q_at X a) <> 0) by (rewrite HPa; unfold PENDING; lia).
        exact (C2 (Q_at X a) Hkx HX0).
      * rewrite (HC k Hk' Hks Hkq) in Hst. exact (C2 k Hkx Hst).
  - rewrite Hnc. clear - N3 Hs. lia.
  - clear - O3 Hops. lia.
  - intros H. exfalso. exact (H HrY).
  - intros H. exfalso. exact (H HrY).
Qed.

(* appended: g_q[g_nq] := s, g_nq + 1, s->queue[queued] := the new entry, queued + 1 *)
Lemma aq_append : forall ops X Y s key disp len cb e,
  agree_q ops X -> g_raw X = 0 -> ops < OPS_MAX -> s = g_ncmd X -> g_nq X < QUEUE_MAX ->
  g_raw Y = 0 -> S_queued Y = S_queued X + 1 -> g_nq Y = g_nq X + 1 -> g_ncmd Y = s + 1 ->
  (forall j, 0 <= j < QUEUE_MAX -> j <> g_nq X -> Q_at Y j = Q_at X j) -> Q_at Y (g_nq X) = s ->
  Cmd_st Y s = PENDING ->
  (forall k, 0 <= k < CMDS_MAX -> k <> s -> Cmd_st Y k = Cmd_st X k /\ cmd_same X Y k) ->
  Cmd_key Y s = key -> Cmd_display Y s = disp -> Cmd_len Y s = len -> Cmd_bytes Y s = cb ->
  (forall i, 0 <= i < QUEUE_MAX -> i <> g_nq X -> sq_ent Y i = sq_ent X i) -> sq_ent Y (g_nq X) = e ->
  new_ent_ok e key disp len cb -> new_cmd_ok s key disp len cb ->
  agree_q (ops + 1) Y.
Proof.
  intros ops X Y s key disp len cb e HX Hr0 Hops Hs Hn HrY Hsq Hnq Hnc HQ HQn HstS HC
    Hkey Hdisp Hlen Hcb HE HEn Hent Hcmd.
  destruct HX as [Q1 N1 E1 ND1 P1 C2 N3 O3 Q4 E4].
  assert (Hn0 : 0 <= g_nq X) by (unfold g_nq; apply u_at_nonneg).
  assert (Hs0 : 0 <= g_ncmd X) by (unfold g_ncmd; apply u_at_nonneg).
  constructor.
  - intros _. rewrite Hsq, Hnq. pose proof (Q1 Hr0) as Hq1. clear - Hq1. lia.
  - intros _. rewrite Hnq. clear - Hn. lia.
  - intros _ i Hi. rewrite Hnq in Hi. rewrite Hnc.
    pose proof (sqt_qb1 _ _ Hn Hi) as Hi'.
    destruct (Z.eq_dec i (g_nq X)) as [Hin|Hin].
    + subst i. rewrite HQn, HstS, Hkey, Hdisp, Hlen, Hcb.
      rewrite (S_queue_bytes_ent Y (g_nq X) Hn0), (S_queue_len_ent Y (g_nq X) Hn0),
        (S_queue_key_ent Y (g_nq X) Hn0), (S_queue_display_ent Y (g_nq X) Hn0), HEn.
      unfold new_ent_ok in Hent. destruct Hent as (H1 & H2 & H3 & H4).
      rewrite H1, H2, H3, H4.
      split; [clear - Hs0 Hs; lia|].
      exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
    + pose proof (sqt_lt _ _ Hi Hin) as Hi0.
      rewrite (HQ i Hi' Hin).
      destruct (E1 Hr0 i Hi0) as [Hb _].
      pose proof (sqt_kb _ _ _ N3 O3 Hb) as Hq.
      assert (Hqis : Q_at X i <> s) by (clear - Hb Hs; lia).
      destruct (HC (Q_at X i) Hq Hqis) as [Hst Hsm]. unfold cmd_same in Hsm. destruct Hsm as (Hk1 & Hd1 & Hl1 & Hb1).
      split; [clear - Hb Hs; lia|].
      rewrite Hst, Hk1, Hd1, Hl1, Hb1.
      rewrite (S_queue_bytes_ent Y i (proj1 Hi)), (S_queue_len_ent Y i (proj1 Hi)),
        (S_queue_key_ent Y i (proj1 Hi)), (S_queue_display_ent Y i (proj1 Hi)), (HE i Hi' Hin),
        <- (S_queue_bytes_ent X i (proj1 Hi)), <- (S_queue_len_ent X i (proj1 Hi)),
        <- (S_queue_key_ent X i (proj1 Hi)), <- (S_queue_display_ent X i (proj1 Hi)).
      exact (proj2 (E1 Hr0 i Hi0)).
  - intros _ i j Hi Hj Hij. rewrite Hnq in Hi, Hj.
    pose proof (sqt_qb1 _ _ Hn Hi) as Hi'. pose proof (sqt_qb1 _ _ Hn Hj) as Hj'.
    destruct (Z.eq_dec i (g_nq X)) as [Hin|Hin]; destruct (Z.eq_dec j (g_nq X)) as [Hjn|Hjn].
    + exact (eq_trans Hin (eq_sym Hjn)).
    + exfalso. subst i. pose proof (sqt_lt _ _ Hj Hjn) as Hj0.
      pose proof (eq_trans (eq_sym HQn) (eq_trans Hij (HQ j Hj' Hjn))) as Hx.
      destruct (E1 Hr0 j Hj0) as [Hb _]. clear - Hb Hx Hs. lia.
    + exfalso. subst j. pose proof (sqt_lt _ _ Hi Hin) as Hi0.
      pose proof (eq_trans (eq_sym HQn) (eq_trans (eq_sym Hij) (HQ i Hi' Hin))) as Hx.
      destruct (E1 Hr0 i Hi0) as [Hb _]. clear - Hb Hx Hs. lia.
    + exact (ND1 Hr0 i j (sqt_lt _ _ Hi Hin) (sqt_lt _ _ Hj Hjn)
        (eq_trans (eq_sym (HQ i Hi' Hin)) (eq_trans Hij (HQ j Hj' Hjn)))).
  - intros _ k Hk. rewrite Hnc in Hk.
    destruct (Z.eq_dec k s) as [Hks|Hks].
    + subst k. rewrite HstS. split.
      * intros _. exists (g_nq X). rewrite Hnq. split; [clear - Hn0; lia | exact HQn].
      * intros _. reflexivity.
    + assert (Hkx : 0 <= k < g_ncmd X) by (clear - Hk Hks Hs; lia).
      pose proof (sqt_kb _ _ _ N3 O3 Hkx) as Hk'.
      destruct (HC k Hk' Hks) as [Hst _]. rewrite Hst. split.
      * intros H. destruct (proj1 (P1 Hr0 k Hkx) H) as [i [Hi Hqi]].
        exists i. rewrite Hnq. split; [clear - Hi; lia|].
        assert (Hin : i <> g_nq X) by (clear - Hi; lia).
        rewrite (HQ i (sqt_qb _ _ (N1 Hr0) Hi) Hin). exact Hqi.
      * intros [i [Hi Hqi]]. rewrite Hnq in Hi. apply (proj2 (P1 Hr0 k Hkx)).
        destruct (Z.eq_dec i (g_nq X)) as [Hin|Hin].
        -- subst i. exfalso. exact (Hks (eq_trans (eq_sym Hqi) HQn)).
        -- exists i. split; [exact (sqt_lt _ _ Hi Hin)|].
           exact (eq_trans (eq_sym (HQ i (sqt_qb1 _ _ Hn Hi) Hin)) Hqi).
  - intros k Hk Hst. rewrite Hnc in Hk.
    destruct (Z.eq_dec k s) as [Hks|Hks].
    + subst k. rewrite Hcb, Hlen, Hdisp. unfold new_cmd_ok in Hcmd. exact Hcmd.
    + assert (Hkx : 0 <= k < g_ncmd X) by (clear - Hk Hks Hs; lia).
      pose proof (sqt_kb _ _ _ N3 O3 Hkx) as Hk'.
      destruct (HC k Hk' Hks) as [Hst1 Hsm]. unfold cmd_same in Hsm. destruct Hsm as (Hk1 & Hd1 & Hl1 & Hb1).
      rewrite Hst1 in Hst. rewrite Hb1, Hl1, Hd1. exact (C2 k Hkx Hst).
  - rewrite Hnc. clear - N3 Hs. lia.
  - clear - O3 Hops. lia.
  - intros H. exfalso. exact (H HrY).
  - intros H. exfalso. exact (H HrY).
Qed.

(* ---------------------------------------------------------------- the regions the stages write *)

Definition RCmd (s x : Z) : Prop := A_Cmd_st s <= x < A_Cmd_st s + Cmd_ESZ.          (* g_cmd[s], FT:1087 *)
Definition RQent (p x : Z) : Prop := A_S_queue_bytes p <= x < A_S_queue_bytes p + 32. (* s->queue[p], DS:339, :347 *)
Definition RStat (x : Z) : Prop := OFF_g_s + 18152 <= x < OFF_g_s + SZ_g_s.          (* s->stats, DS:333, :340 *)
Definition RQd (x : Z) : Prop := A_S_queued <= x < A_S_queued + 4.                    (* s->queued, DS:347 *)
Definition RCst (q x : Z) : Prop := A_Cmd_st q <= x < A_Cmd_st q + 4.                 (* g_cmd[q].st, FT:1114 *)
Definition RQ (p x : Z) : Prop := OFF_g_q + 4 * p <= x < OFF_g_q + 4 * p + 4.         (* g_q[p], FT:1115, :1117 *)
Definition RNq (x : Z) : Prop := OFF_g_nq <= x < OFF_g_nq + 4.                        (* g_nq, FT:1117 *)
Definition RNc (x : Z) : Prop := OFF_g_ncmd <= x < OFF_g_ncmd + 4.                    (* g_ncmd, FT:1120 *)
Definition Ror (R1 R2 : Z -> Prop) (x : Z) : Prop := R1 x \/ R2 x.
(* the whole op, by outcome *)
Definition Rnoop (s x : Z) : Prop := RCmd s x \/ RStat x \/ RNc x.
Definition Rcoal (s a q x : Z) : Prop := RCmd s x \/ RQent a x \/ RStat x \/ RCst q x \/ RQ a x \/ RNc x.
Definition Rapp (s p x : Z) : Prop := RCmd s x \/ RQent p x \/ RQd x \/ RQ p x \/ RNq x \/ RNc x.

Ltac runf := unfold Rnoop, Rcoal, Rapp, Ror, RCmd, RQent, RStat, RQd, RCst, RQ, RNq, RNc in *.

(* wframe of a chain of writes into one of the regions above *)
Ltac wfr2 := lazymatch goal with
  | |- wframe _ ?B ?B => apply wframe_refl
  | |- wframe _ _ _ => apply wframe_upd_r;
      [wfr2 | wlen | woffs | woffs | let a := fresh "a" in let H := fresh "H" in intros a H; revert H; runf; woffs]
  end.

(* a getter the frame H misses reads the same: goal `g Later args = g Earlier args` *)
Ltac wkeep_unf :=
  lazymatch goal with
  | |- g_nq _ = _ => unfold g_nq
  | |- g_ncmd _ = _ => unfold g_ncmd
  | |- g_raw _ = _ => unfold g_raw
  | |- S_queued _ = _ => unfold S_queued
  | |- Q_at _ _ = _ => unfold Q_at
  | |- Cmd_st _ _ = _ => unfold Cmd_st
  | |- Cmd_key _ _ = _ => unfold Cmd_key
  | |- Cmd_display _ _ = _ => unfold Cmd_display
  | |- Cmd_len _ _ = _ => unfold Cmd_len
  | |- Cmd_bytes _ _ = _ => unfold Cmd_bytes
  | |- sq_ent _ _ = _ => unfold sq_ent
  | |- S_queue_key _ _ = _ => unfold S_queue_key
  | |- sub _ _ _ = _ => idtac
  end.
Ltac wkeep H := wkeep_unf;
  lazymatch goal with
  | |- s32_at _ _ = s32_at _ _ => apply (wframe_s32_at _ _ _ _ H)
  | |- u_at _ _ _ = u_at _ _ _ => apply (wframe_u_at _ _ _ _ _ H)
  | |- sub _ _ _ = sub _ _ _ => apply (wframe_sub _ _ _ _ _ H)
  end;
  [ woffs | let x := fresh "x" in let Hx := fresh "Hx" in let HR := fresh "HR" in intros x Hx HR; runf; woffs ].

Lemma wframe_w : forall (R R' : Z -> Prop) X Y W, wframe R' X Y -> (forall x, R' x -> R x) -> wframe R Y W ->
  wframe R X W.
Proof. intros R R' X Y W H1 HR H2. eapply wframe_trans; [|exact H2]. eapply wframe_weaken; [exact HR|exact H1]. Qed.

(* reading from the start of a write on past its end *)
Lemma rd_cover : forall B k v n, length B = WN -> 0 <= k -> (length v <= n)%nat -> k + Z.of_nat n <= W_LEN ->
  sub (upd B k v) k n = v ++ sub B (k + Z.of_nat (length v)) (n - length v).
Proof. intros B k v n HB Hk Hv Hn. apply w_sub_upd_cover; try assumption. rewrite HB. unfold WN. lia. Qed.

(* ---------------------------------------------------------------- the command's bytes (FT:1075-1093) *)

Lemma firstn_repeat' : forall {A} (x : A) a m, firstn a (repeat x m) = repeat x (Nat.min a m).
Proof. intros A x a. induction a as [|a IH]; intros [|m]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma repeat_add' : forall {A} (x : A) n m, repeat x n ++ repeat x m = repeat x (n + m).
Proof. intros A x n. induction n as [|n IH]; intros m; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* c.bytes past c.len are memset's zeros *)
Lemma cb_tail : forall (l3 p : list byte) (k m : nat), length l3 = 3%nat -> (3 + length p + k = 24)%nat ->
  (3 + length p <= m <= 24)%nat ->
  firstn m (l3 ++ p ++ repeat (b8 0) k) ++ repeat (b8 0) (24 - m) = l3 ++ p ++ repeat (b8 0) k.
Proof.
  intros l3 p k m H3 Hk Hm.
  rewrite firstn_app, H3.
  assert (E1 : firstn m l3 = l3) by (apply firstn_all2; lia). rewrite E1.
  rewrite firstn_app.
  assert (E2 : firstn (m - 3) p = p) by (apply firstn_all2; lia). rewrite E2.
  rewrite firstn_repeat'. rewrite <- !app_assoc. rewrite repeat_add'.
  replace (Nat.min (m - 3 - length p) k + (24 - m))%nat with k by lia. reflexivity.
Qed.

Lemma land_7f : forall x, 0 <= Z.land x 0x7f < 2 ^ 8.
Proof.
  intros x. change 0x7f with (Z.ones 7). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 7) ltac:(lia)). lia.
Qed.

(* cbytes of FT:1089-1093: TAG, the serial's two 7-bit halves, the n bytes taken, zeros *)
Lemma cb_facts : forall s p n cb, length p = Z.to_nat n -> 0 <= n <= 21 ->
  cb = [b8 TAG; b8 (Z.land s 0x7f); b8 (Z.land (Z.shiftr s 7) 0x7f)] ++ p ++ repeat (b8 0) (Z.to_nat (21 - n)) ->
  length cb = 24%nat /\ at8 cb 0 = TAG /\ at8 cb 1 = Z.land s 0x7f /\ at8 cb 2 = Z.land (Z.shiftr s 7) 0x7f /\
  (forall len, 3 + n <= len <= 24 -> firstn (Z.to_nat len) cb ++ repeat (b8 0) (24 - Z.to_nat len) = cb).
Proof.
  intros s p n cb Hp Hn Ecb. subst cb.
  split; [|split; [|split; [|split]]].
  - rewrite !length_app, Hp, repeat_length. cbn [length]. lia.
  - unfold at8. cbn [nth app]. apply bz_b8. unfold TAG. lia.
  - unfold at8. cbn [nth app]. apply bz_b8. apply land_7f.
  - unfold at8. cbn [nth app]. apply bz_b8. apply land_7f.
  - intros len Hl. apply cb_tail; [reflexivity | rewrite Hp; lia | rewrite Hp; lia].
Qed.

Lemma sub_after : forall (cb rest : list byte) k n, length cb = 24%nat -> 24 <= k ->
  sub (cb ++ rest) k n = sub rest (k - 24) n.
Proof.
  intros cb rest k n Hcb Hk. unfold sub. rewrite skipn_app.
  assert (E : skipn (Z.to_nat k) cb = []) by (apply skipn_all2; lia). rewrite E, app_nil_l, Hcb.
  replace (Z.to_nat k - 24)%nat with (Z.to_nat (k - 24)) by lia. reflexivity.
Qed.

Lemma bytes_one : forall b : byte, bytes_le_to_Z [b] = bz b.
Proof. intros b. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. Qed.

(* the struct diginet_cmd c the harness passes (TOps.v cmd_struct) *)
Lemma cs_facts : forall cb len disp key cs, length cb = 24%nat -> 0 <= len < 2 ^ 8 -> 0 <= disp < 2 ^ 8 ->
  0 <= key < 2 ^ 32 -> cs = cmd_struct cb len disp key ->
  length cs = 32%nat /\ cmd_len_of cs = len /\ cmd_display_of cs = disp /\ cmd_key_of cs = key /\
  firstn 24 cs = cb /\ at8 cs 24 = len /\ (forall m, (m <= 24)%nat -> firstn m cs = firstn m cb).
Proof.
  intros cb len disp key cs Hcb Hl Hd Hk Ecs. subst cs. unfold cmd_struct.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - rewrite !length_app, length_put, Hcb. cbn [length]. lia.
  - unfold cmd_len_of, u_at. rewrite (sub_after cb _ 24 1 Hcb ltac:(lia)).
    change (sub ([b8 len; b8 disp; b8 0; b8 0] ++ put 4 key) (24 - 24) 1) with [b8 len].
    rewrite bytes_one. apply bz_b8. exact Hl.
  - unfold cmd_display_of, u_at. rewrite (sub_after cb _ 25 1 Hcb ltac:(lia)).
    change (sub ([b8 len; b8 disp; b8 0; b8 0] ++ put 4 key) (25 - 24) 1) with [b8 disp].
    rewrite bytes_one. apply bz_b8. exact Hd.
  - unfold cmd_key_of, u_at. rewrite (sub_after cb _ 28 4 Hcb ltac:(lia)).
    change (sub ([b8 len; b8 disp; b8 0; b8 0] ++ put 4 key) (28 - 24) 4) with (firstn 4 (put 4 key)).
    rewrite firstn_all2 by (rewrite length_put; lia).
    apply bytes_put_small. change (8 * Z.of_nat 4) with 32. exact Hk.
  - rewrite firstn_app, Hcb, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. apply firstn_all2. lia.
  - unfold at8. rewrite app_nth2 by lia. rewrite Hcb. cbn [Nat.sub nth app]. apply bz_b8. exact Hl.
  - intros m Hm. rewrite firstn_app. replace (m - length cb)%nat with 0%nat by lia. cbn [firstn].
    apply app_nil_r.
Qed.

Lemma lor_lt32 : forall x y, 0 < x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> 0 <= Z.lor x y < 2 ^ 32.
Proof.
  intros x y Hx Hy.
  assert (H0 : 0 <= Z.lor x y) by (apply Z.lor_nonneg; lia).
  split; [exact H0|].
  destruct (Z.eq_dec (Z.lor x y) 0) as [E|E]; [rewrite E; lia|].
  apply (proj2 (Z.log2_lt_pow2 (Z.lor x y) 32 ltac:(lia))).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - apply (proj1 (Z.log2_lt_pow2 x 32 ltac:(lia))). lia.
  - destruct (Z.eq_dec y 0) as [E0|E0].
    + rewrite E0. change (Z.log2 0) with 0. lia.
    + apply (proj1 (Z.log2_lt_pow2 y 32 ltac:(lia))). lia.
Qed.

(* SPEC_KEY (kind, addr) with kind <= 9 and an address byte: a u32 *)
Lemma key_range : forall kb ab, 0 <= kb < 256 -> 0 <= ab < 256 -> 0 <= KEY (kb mod 9 + 1) ab < 2 ^ 32.
Proof.
  intros kb ab Hk Ha. unfold KEY. apply lor_lt32.
  - pose proof (Z.mod_pos_bound kb 9 ltac:(lia)). lia.
  - change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound ab (2 ^ 16) ltac:(lia)). lia.
Qed.

Lemma land1_bit : forall x, 0 <= Z.land x 1 <= 1 /\ bit01 (Z.land x 1).
Proof.
  intros x. assert (E : Z.land x 1 = x mod 2).
  { change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia. reflexivity. }
  rewrite E. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). unfold bit01. lia.
Qed.

(* the session's coalescable (DS:322-326) is the harness's (FT:188-194) *)
Lemma coal_eq : forall key, coalescable_m key = h_coalescable_m key.
Proof.
  intros key. unfold coalescable_m, h_coalescable_m, u8, int_of_bool, b2z, DIGINET_KEY_INPUT,
    DIGINET_KEY_KEEPALIVE, SPEC_KEY_INPUT, SPEC_KEY_KEEPALIVE.
  change (2 ^ 8) with 256. reflexivity.
Qed.

(* ---------------------------------------------------------------- op_begin keeps agree_q *)

Lemma ob_keep : forall ops B B1, wframe R_ob B B1 -> agree_q ops B ->
  agree_q ops B1 /\ g_raw B1 = g_raw B /\ S_queued B1 = S_queued B.
Proof.
  intros ops B B1 F HQ.
  assert (Kr : g_raw B1 = g_raw B) by (wkeep F).
  assert (Kq : S_queued B1 = S_queued B) by (wkeep F).
  split; [|split; assumption].
  apply (aq_transfer ops B B1 HQ Kr Kq).
  - wkeep F.
  - wkeep F.
  - intros j Hj. wkeep F.
  - intros k Hk. split; [wkeep F|]. unfold cmd_same. split; [wkeep F|]. split; [wkeep F|]. split; wkeep F.
  - intros i Hi. wkeep F.
Qed.

(* ---------------------------------------------------------------- the stages *)

(* FT:1087 memset (&g_cmd[serial], 0, 40) *)
Lemma B2_facts : forall B1 B2 s, length B1 = WN -> 0 <= s < CMDS_MAX ->
  B2 = upd B1 (A_Cmd_st s) (repeat (b8 0) (Z.to_nat Cmd_ESZ)) ->
  length B2 = WN /\ wframe (RCmd s) B1 B2 /\
  g_nq B2 = g_nq B1 /\ S_queued B2 = S_queued B1 /\ g_ncmd B2 = g_ncmd B1 /\
  (forall j, 0 <= j < CMDS_MAX -> Q_at B2 j = Q_at B1 j) /\
  (forall k, 0 <= k < CMDS_MAX -> k <> s -> Cmd_key B2 k = Cmd_key B1 k) /\
  (forall j, 0 <= j < S_queue_N -> S_queue_key B2 j = S_queue_key B1 j) /\
  Cmd_st B2 s = 0 /\
  (forall j m, A_Cmd_st s <= j -> j + Z.of_nat m <= A_Cmd_st s + Cmd_ESZ -> sub B2 j m = repeat (b8 0) m).
Proof.
  intros B1 B2 s HB Hs E.
  assert (L : length B2 = WN) by (subst B2; wlen).
  assert (F : wframe (RCmd s) B1 B2) by (subst B2; wfr2).
  assert (Zr : forall j m, A_Cmd_st s <= j -> j + Z.of_nat m <= A_Cmd_st s + Cmd_ESZ ->
                 sub B2 j m = repeat (b8 0) m).
  { intros j m Hj Hm. subst B2. apply rd_zero; [exact HB | woffs | exact Hj | woffs | woffs]. }
  split; [exact L|]. split; [exact F|].
  split; [wkeep F|]. split; [wkeep F|]. split; [wkeep F|].
  split; [intros j Hj; wkeep F|]. split; [intros k Hk Hks; wkeep F|]. split; [intros j Hj; wkeep F|].
  split; [|exact Zr].
  unfold Cmd_st, s32_at, u_at. rewrite (Zr (A_Cmd_st s) 4%nat) by (unfold Cmd_ESZ; lia).
  rewrite w_bytes_zero. reflexivity.
Qed.

(* DS:333 s->stats.refused++ *)
Lemma W3_ref : forall B2 B3, length B2 = WN ->
  B3 = set_S_stats_refused B2 (u64 (S_stats_refused B2 + 1)) ->
  length B3 = WN /\ wframe RStat B2 B3.
Proof. intros B2 B3 HB E. subst B3. wunfold. split; [wlen | wfr2]. Qed.

(* DS:339-340 s->queue[i] = *c; s->stats.coalesced++ *)
Lemma W3_coal : forall B2 B3 a cs, length B2 = WN -> 0 <= a < S_queue_N -> length cs = 32%nat ->
  B3 = set_S_stats_coalesced (upd B2 (A_S_queue_bytes a) cs)
         (u64 (S_stats_coalesced (upd B2 (A_S_queue_bytes a) cs) + 1)) ->
  length B3 = WN /\ wframe (Ror (RQent a) RStat) B2 B3 /\ sq_ent B3 a = cs.
Proof.
  intros B2 B3 a cs HB Ha Hcs E. subst B3. wunfold. split; [wlen|]. split; [wfr2|].
  unfold sq_ent. rd1.
  apply (sub_upd_eq B2 cs (A_S_queue_bytes a) 32); [woffs | exact Hcs | rewrite HB; woffs].
Qed.

(* DS:347 s->queue[s->queued++] = *c *)
Lemma W3_app : forall B2 B3 p cs, length B2 = WN -> 0 <= p < S_queue_N -> length cs = 32%nat ->
  B3 = set_S_queued (upd B2 (A_S_queue_bytes p) cs) (u32 (p + 1)) ->
  length B3 = WN /\ wframe (Ror (RQent p) RQd) B2 B3 /\ sq_ent B3 p = cs /\ S_queued B3 = p + 1.
Proof.
  intros B2 B3 p cs HB Hp Hcs E. subst B3. wunfold. split; [wlen|]. split; [wfr2|]. split.
  - unfold sq_ent. rd1.
    apply (sub_upd_eq B2 cs (A_S_queue_bytes p) 32); [woffs | exact Hcs | rewrite HB; woffs].
  - unfold S_queued, u_at. rewrite rd_put by (first [wlen | woffs]). rewrite bytes_le_to_Z_put.
    change (8 * Z.of_nat 4) with 32. unfold u32. rewrite Z.mod_mod by lia. apply Z.mod_small.
    unfold S_queue_N in Hp. lia.
Qed.

(* FT:1108-1112 g_cmd[serial] := { PENDING, key, display, len, the first len bytes } *)
Lemma Wtag : forall B3 Bw s key disp len cb, length B3 = WN -> 0 <= s < CMDS_MAX -> length cb = 24%nat ->
  3 <= len <= 24 -> 0 <= key < 2 ^ 32 -> 0 <= disp <= 1 ->
  Bw = set_Cmd_bytes (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B3 s PENDING) s key) s disp) s len)
         s (firstn (Z.to_nat len) cb) ->
  length Bw = WN /\ wframe (RCmd s) B3 Bw /\
  Cmd_st Bw s = PENDING /\ Cmd_key Bw s = key /\ Cmd_display Bw s = disp /\ Cmd_len Bw s = len /\
  Cmd_bytes Bw s = firstn (Z.to_nat len) cb ++ sub B3 (A_Cmd_bytes s + len) (24 - Z.to_nat len).
Proof.
  intros B3 Bw s key disp len cb HB Hs Hcb Hl Hk Hd E. subst Bw. wunfold.
  split; [wlen|]. split; [wfr2|].
  split; [|split; [|split; [|split]]].
  - unfold Cmd_st, s32_at, u_at. repeat rd1. apply w_s32_put. unfold PENDING. lia.
  - unfold Cmd_key, u_at. repeat rd1. apply bytes_put_small. change (8 * Z.of_nat 4) with 32. exact Hk.
  - unfold Cmd_display, s32_at, u_at. repeat rd1. apply w_s32_put. lia.
  - unfold Cmd_len, u_at. repeat rd1. apply bytes_put_small. change (8 * Z.of_nat 1) with 8. lia.
  - unfold Cmd_bytes. rewrite rd_cover by (first [wlen | woffs]).
    rewrite length_firstn, Hcb. replace (Nat.min (Z.to_nat len) 24) with (Z.to_nat len) by lia.
    rewrite Z2Nat.id by lia. repeat rd1. reflexivity.
Qed.

(* FT:1114-1115 g_cmd[g_q[at]].st = REPLACED; g_q[at] = serial *)
Lemma W6_coal : forall Bw B6 a q s, length Bw = WN -> 0 <= a < QUEUE_MAX -> 0 <= q < CMDS_MAX -> 0 <= s < 2 ^ 32 ->
  B6 = set_Q_at (set_Cmd_st Bw q REPLACED) a s ->
  length B6 = WN /\ wframe (Ror (RCst q) (RQ a)) Bw B6 /\ Q_at B6 a = s /\ Cmd_st B6 q = REPLACED.
Proof.
  intros Bw B6 a q s HB Ha Hq Hs E. subst B6. wunfold. split; [wlen|]. split; [wfr2|]. split.
  - unfold Q_at, u_at. rewrite rd_put by (first [wlen | woffs]). apply bytes_put_small.
    change (8 * Z.of_nat 4) with 32. exact Hs.
  - unfold Cmd_st, s32_at, u_at. rd1. rewrite rd_put by (first [wlen | woffs]). apply w_s32_put.
    unfold REPLACED. lia.
Qed.

(* FT:1117 g_q[g_nq++] = serial *)
Lemma W6_app : forall Bw B6 p s, length Bw = WN -> 0 <= p < QUEUE_MAX -> 0 <= s < 2 ^ 32 ->
  B6 = set_g_nq (set_Q_at Bw p s) ((p + 1) mod 2 ^ 32) ->
  length B6 = WN /\ wframe (Ror (RQ p) RNq) Bw B6 /\ Q_at B6 p = s /\ g_nq B6 = p + 1.
Proof.
  intros Bw B6 p s HB Hp Hs E. subst B6. wunfold. split; [wlen|]. split; [wfr2|]. split.
  - unfold Q_at, u_at. rd1. rewrite rd_put by (first [wlen | woffs]). apply bytes_put_small.
    change (8 * Z.of_nat 4) with 32. exact Hs.
  - unfold g_nq, u_at. rewrite rd_put by (first [wlen | woffs]). rewrite bytes_le_to_Z_put.
    change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by lia. apply Z.mod_small. unfold QUEUE_MAX in Hp. lia.
Qed.

(* FT:1120 g_ncmd++ *)
Lemma W7 : forall B6 B7 v, length B6 = WN -> 0 <= v < 2 ^ 32 -> B7 = set_g_ncmd B6 v ->
  length B7 = WN /\ wframe RNc B6 B7 /\ g_ncmd B7 = v.
Proof.
  intros B6 B7 v HB Hv E. subst B7. wunfold. split; [wlen|]. split; [wfr2|].
  unfold g_ncmd, u_at. rewrite rd_put by (first [wlen | woffs]). apply bytes_put_small.
  change (8 * Z.of_nat 4) with 32. exact Hv.
Qed.

(* ---------------------------------------------------------------- the two scans for the key *)

(* FT:1097-1101 on the world after the memset: the first place, in op_begin's world, of a pending command with
   this key, or -1 *)
Lemma harness_at : forall B1 B2 s key, g_nq B2 = g_nq B1 -> 0 <= s < CMDS_MAX ->
  (forall j, 0 <= j < CMDS_MAX -> Q_at B2 j = Q_at B1 j) ->
  (forall k, 0 <= k < CMDS_MAX -> k <> s -> Cmd_key B2 k = Cmd_key B1 k) ->
  g_nq B1 <= QUEUE_MAX -> (forall j, 0 <= j < g_nq B1 -> 0 <= Q_at B1 j < s) ->
  (if negb (h_coalescable_m key =? 0) then submit_find_at (S (Z.to_nat CMDS_MAX)) B2 key 0 else Some (-1)) =
  Some (match (if h_coalescable_m key =? 0 then None
               else first_idx (fun j => Cmd_key B1 (Q_at B1 j) =? key) 0 (Z.to_nat (g_nq B1))) with
        | Some j => j | None => -1 end).
Proof.
  intros B1 B2 s key Hnq Hs HQ HK Hnq1 HQ1.
  pose proof (u_at_nonneg B1 OFF_g_nq 4) as H0. fold (g_nq B1) in H0.
  destruct (h_coalescable_m key =? 0); cbn [negb]; [reflexivity|].
  rewrite (submit_find_at_first B2 key (S (Z.to_nat CMDS_MAX)) 0).
  - rewrite Hnq, Z.sub_0_r.
    assert (Hext : forall j, 0 <= j < 0 + Z.of_nat (Z.to_nat (g_nq B1)) ->
                     (Cmd_key B2 (Q_at B2 j) =? key) = (Cmd_key B1 (Q_at B1 j) =? key)).
    { intros j Hj. specialize (HQ1 j ltac:(lia)).
      rewrite (HQ j) by (unfold CMDS_MAX, QUEUE_MAX in *; lia).
      rewrite (HK (Q_at B1 j)) by (unfold CMDS_MAX in *; lia). reflexivity. }
    rewrite (first_idx_ext (fun j => Cmd_key B2 (Q_at B2 j) =? key) (fun j => Cmd_key B1 (Q_at B1 j) =? key)
               (Z.to_nat (g_nq B1)) 0 Hext).
    reflexivity.
  - rewrite Hnq. lia.
  - rewrite Hnq. unfold CMDS_MAX, QUEUE_MAX in *. lia.
  - rewrite Hnq. unfold CMDS_MAX, QUEUE_MAX in *. lia.
  - intros j Hj. rewrite Hnq in Hj. specialize (HQ1 j Hj).
    rewrite (HQ j) by (unfold CMDS_MAX, QUEUE_MAX in *; lia). lia.
Qed.

(* DS:336-343 on the same world: the same place (D1: s->queue mirrors g_q) *)
Lemma session_fi : forall B1 B2 cs key, cmd_key_of cs = key -> S_queued B2 = g_nq B1 ->
  (forall j, 0 <= j < g_nq B1 -> S_queue_key B2 j = Cmd_key B1 (Q_at B1 j)) ->
  (if coalescable_m (cmd_key_of cs) =? 0 then None
   else first_idx (fun j => S_queue_key B2 j =? cmd_key_of cs) 0 (Z.to_nat (S_queued B2))) =
  (if h_coalescable_m key =? 0 then None
   else first_idx (fun j => Cmd_key B1 (Q_at B1 j) =? key) 0 (Z.to_nat (g_nq B1))).
Proof.
  intros B1 B2 cs key Hk Hq HS. rewrite Hk, coal_eq, Hq.
  destruct (h_coalescable_m key =? 0); [reflexivity|].
  apply first_idx_ext. intros j Hj. cbv beta. rewrite (HS j) by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------- diginet_session_submit, by outcome *)

Lemma spec_len : forall c, 1 <= cmd_len_of c <= 24 ->
  ((cmd_len_of c =? 0) || (DIGINET_CMD_MAX_LEN <? cmd_len_of c)) = false.
Proof.
  intros c H. unfold DIGINET_CMD_MAX_LEN.
  destruct (Z.eqb_spec (cmd_len_of c) 0); [lia|]. destruct (Z.ltb_spec 24 (cmd_len_of c)); [lia|]. reflexivity.
Qed.

Lemma spec_refused : forall B c, 1 <= cmd_len_of c <= 24 ->
  body_check (firstn (Z.to_nat (cmd_len_of c)) c) <> DIGINET_OK ->
  submit_spec B c = (set_S_stats_refused B (u64 (S_stats_refused B + 1)), DIGINET_E_REFUSED).
Proof.
  intros B c Hl Hb. unfold submit_spec. cbv zeta. rewrite (spec_len c Hl).
  destruct (Z.eqb_spec (body_check (firstn (Z.to_nat (cmd_len_of c)) c)) DIGINET_OK) as [E|E]; [contradiction|].
  reflexivity.
Qed.

Lemma spec_found : forall B c i, 1 <= cmd_len_of c <= 24 ->
  body_check (firstn (Z.to_nat (cmd_len_of c)) c) = DIGINET_OK ->
  (if coalescable_m (cmd_key_of c) =? 0 then None
   else first_idx (fun j => S_queue_key B j =? cmd_key_of c) 0 (Z.to_nat (S_queued B))) = Some i ->
  submit_spec B c = (set_S_stats_coalesced (upd B (A_S_queue_bytes i) c)
                       (u64 (S_stats_coalesced (upd B (A_S_queue_bytes i) c) + 1)), DIGINET_OK).
Proof.
  intros B c i Hl Hb Hf. unfold submit_spec. cbv zeta.
  rewrite (spec_len c Hl), Hb, (Z.eqb_refl DIGINET_OK). cbn [negb]. rewrite Hf. reflexivity.
Qed.

Lemma spec_none : forall B c, 1 <= cmd_len_of c <= 24 ->
  body_check (firstn (Z.to_nat (cmd_len_of c)) c) = DIGINET_OK ->
  (if coalescable_m (cmd_key_of c) =? 0 then None
   else first_idx (fun j => S_queue_key B j =? cmd_key_of c) 0 (Z.to_nat (S_queued B))) = None ->
  submit_spec B c = if S_queued B =? DIGINET_QUEUE_MAX then (B, DIGINET_E_SPACE)
                    else (set_S_queued (upd B (A_S_queue_bytes (S_queued B)) c) (u32 (S_queued B + 1)), DIGINET_OK).
Proof.
  intros B c Hl Hb Hf. unfold submit_spec. cbv zeta.
  rewrite (spec_len c Hl), Hb, (Z.eqb_refl DIGINET_OK). cbn [negb]. rewrite Hf. reflexivity.
Qed.

(* ---------------------------------------------------------------- the two checks (FT:656-676) *)

Lemma refusal_ok : forall X c rc before len, L3_stmt -> length c = 32%nat -> at8 c 24 = len -> 0 <= len <= 24 ->
  (body_check (firstn (Z.to_nat len) c) = DIGINET_OK -> rc <> SPEC_E_REFUSED) ->
  (body_check (firstn (Z.to_nat len) c) <> DIGINET_OK -> rc = SPEC_E_REFUSED /\ S_queued X = before) ->
  check_refusal_submit_m X c rc before = Some (X, tt).
Proof.
  intros X c rc before len L3 Hc Hat Hl Hok Hno. unfold check_refusal_submit_m. cbv zeta. rewrite Hat, Hc.
  replace ((32 <? 25)%nat || (Z.of_nat 32 <? len)) with false
    by (destruct (Z.ltb_spec (Z.of_nat 32) len); [lia | reflexivity]).
  destruct (L3 c len ltac:(rewrite Hc; lia)) as (Hiff & _ & _).
  destruct (Z.leb_spec 0 (spec_system_at (zs c) len)) as [Hge|Hlt].
  - assert (Hne : body_check (firstn (Z.to_nat len) c) <> DIGINET_OK) by (intros E; apply Hiff in E; lia).
    destruct (Hno Hne) as (Er & Eb). rewrite Er, Eb, (Z.eqb_refl SPEC_E_REFUSED), (Z.eqb_refl before).
    reflexivity.
  - assert (E : body_check (firstn (Z.to_nat len) c) = DIGINET_OK) by (apply Hiff; exact Hlt).
    specialize (Hok E). destruct (Z.eqb_spec rc SPEC_E_REFUSED); [contradiction|]. reflexivity.
Qed.

Lemma latest_ok : forall X rc want, rc = want -> check_latest_submit_m X rc want = Some (X, tt).
Proof. intros X rc want E. subst rc. unfold check_latest_submit_m. rewrite (Z.eqb_refl want). reflexivity. Qed.

(* ---------------------------------------------------------------- the four outcomes *)

(* the place g_q[at] the coalesced command leaves, read after the session's write and the record *)
Lemma coal_qBw : forall B1 B2 B3 Bw s a key disp len cb cs, length B1 = WN -> 0 <= s < CMDS_MAX ->
  0 <= a < QUEUE_MAX -> length cs = 32%nat -> length cb = 24%nat -> 3 <= len <= 24 -> 0 <= key < 2 ^ 32 ->
  0 <= disp <= 1 ->
  B2 = upd B1 (A_Cmd_st s) (repeat (b8 0) (Z.to_nat Cmd_ESZ)) ->
  B3 = set_S_stats_coalesced (upd B2 (A_S_queue_bytes a) cs)
         (u64 (S_stats_coalesced (upd B2 (A_S_queue_bytes a) cs) + 1)) ->
  Bw = set_Cmd_bytes (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B3 s PENDING) s key) s disp) s len)
         s (firstn (Z.to_nat len) cb) ->
  Q_at Bw a = Q_at B1 a.
Proof.
  intros B1 B2 B3 Bw s a key disp len cb cs HB Hs Ha Hcs Hcb Hl Hk Hd E2 E3 Ew.
  destruct (B2_facts B1 B2 s HB Hs E2) as (L2 & F2 & _).
  destruct (W3_coal B2 B3 a cs L2 ltac:(unfold S_queue_N, QUEUE_MAX in *; lia) Hcs E3) as (L3 & F3 & _).
  destruct (Wtag B3 Bw s key disp len cb L3 Hs Hcb Hl Hk Hd Ew) as (Lw & Fw & _).
  assert (K1 : Q_at Bw a = Q_at B3 a) by (wkeep Fw).
  assert (K2 : Q_at B3 a = Q_at B2 a) by (wkeep F3).
  assert (K3 : Q_at B2 a = Q_at B1 a) by (wkeep F2).
  rewrite K1, K2, K3. reflexivity.
Qed.

(* g_nq before the record of an appended command *)
Lemma app_nqBw : forall B1 B2 B3 Bw s p key disp len cb cs, length B1 = WN -> 0 <= s < CMDS_MAX ->
  0 <= p < QUEUE_MAX -> length cs = 32%nat -> length cb = 24%nat -> 3 <= len <= 24 -> 0 <= key < 2 ^ 32 ->
  0 <= disp <= 1 ->
  B2 = upd B1 (A_Cmd_st s) (repeat (b8 0) (Z.to_nat Cmd_ESZ)) ->
  B3 = set_S_queued (upd B2 (A_S_queue_bytes p) cs) (u32 (p + 1)) ->
  Bw = set_Cmd_bytes (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B3 s PENDING) s key) s disp) s len)
         s (firstn (Z.to_nat len) cb) ->
  g_nq Bw = g_nq B1.
Proof.
  intros B1 B2 B3 Bw s p key disp len cb cs HB Hs Hp Hcs Hcb Hl Hk Hd E2 E3 Ew.
  destruct (B2_facts B1 B2 s HB Hs E2) as (L2 & F2 & Nq2 & _).
  destruct (W3_app B2 B3 p cs L2 ltac:(unfold S_queue_N, QUEUE_MAX in *; lia) Hcs E3) as (L3 & F3 & _).
  destruct (Wtag B3 Bw s key disp len cb L3 Hs Hcb Hl Hk Hd Ew) as (Lw & Fw & _).
  assert (K1 : g_nq Bw = g_nq B3) by (wkeep Fw).
  assert (K2 : g_nq B3 = g_nq B2) by (wkeep F3).
  rewrite K1, K2, Nq2. reflexivity.
Qed.

(* refused (B3 = the stats write) or E_SPACE (B3 = B2): g_cmd[serial] zeroed, g_ncmd + 1 *)
Lemma case_noop : forall ops B1 B2 B3 B7 s, length B1 = WN -> agree_q ops B1 -> g_raw B1 = 0 -> ops < OPS_MAX ->
  s = g_ncmd B1 -> B2 = upd B1 (A_Cmd_st s) (repeat (b8 0) (Z.to_nat Cmd_ESZ)) ->
  length B3 = WN -> wframe RStat B2 B3 -> B7 = set_g_ncmd B3 ((g_ncmd B3 + 1) mod 2 ^ 32) ->
  wframe R4q B1 B7 /\ agree_q (ops + 1) B7.
Proof.
  intros ops B1 B2 B3 B7 s HB HQ Hr Hops Hs EB2 L3 F3 EB7.
  pose proof (d3_ncmd _ _ HQ) as Hn. pose proof (d3_ops _ _ HQ) as Ho.
  pose proof (u_at_nonneg B1 OFF_g_ncmd 4) as Hs0. fold (g_ncmd B1) in Hs0.
  assert (Hsr : 0 <= s < CMDS_MAX) by (unfold CMDS_MAX, OPS_MAX in *; lia).
  destruct (B2_facts B1 B2 s HB Hsr EB2) as (L2 & F2 & _ & _ & Nc2 & _ & _ & _ & St2 & _).
  assert (Nc3 : g_ncmd B3 = g_ncmd B2) by (wkeep F3).
  assert (Hv : 0 <= (g_ncmd B3 + 1) mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  destruct (W7 B3 B7 _ L3 Hv EB7) as (L7 & F7 & Nc7).
  assert (F : wframe (Rnoop s) B1 B7).
  { apply (wframe_w _ _ _ _ _ F2); [intros x Hx; runf; lia|].
    apply (wframe_w _ _ _ _ _ F3); [intros x Hx; runf; lia|].
    eapply wframe_weaken; [|exact F7]. intros x Hx. runf. lia. }
  split.
  - eapply wframe_weaken; [|exact F]. intros x Hx. runf. woffs.
  - apply (aq_noop ops B1 B7 s HQ Hr Hops Hs).
    + assert (E : g_raw B7 = g_raw B1) by (wkeep F). rewrite E. exact Hr.
    + wkeep F.
    + wkeep F.
    + rewrite Nc7, Nc3, Nc2, <- Hs. apply Z.mod_small. unfold CMDS_MAX in Hsr. lia.
    + intros j Hj. wkeep F.
    + assert (E1 : Cmd_st B7 s = Cmd_st B3 s) by (wkeep F7).
      assert (E2 : Cmd_st B3 s = Cmd_st B2 s) by (wkeep F3).
      rewrite E1, E2. exact St2.
    + intros k Hk Hks. split; [wkeep F|]. unfold cmd_same. split; [wkeep F|]. split; [wkeep F|]. split; wkeep F.
    + intros i Hi. wkeep F.
Qed.

(* coalesced at a *)
Lemma case_coal : forall ops B1 B2 B3 Bw B6 B7 s a key disp len cb cs,
  length B1 = WN -> agree_q ops B1 -> g_raw B1 = 0 -> ops < OPS_MAX -> s = g_ncmd B1 -> 0 <= a < g_nq B1 ->
  length cb = 24%nat -> length cs = 32%nat -> new_ent_ok cs key disp len cb -> new_cmd_ok s key disp len cb ->
  0 <= key < 2 ^ 32 -> firstn (Z.to_nat len) cb ++ repeat (b8 0) (24 - Z.to_nat len) = cb ->
  B2 = upd B1 (A_Cmd_st s) (repeat (b8 0) (Z.to_nat Cmd_ESZ)) ->
  B3 = set_S_stats_coalesced (upd B2 (A_S_queue_bytes a) cs)
         (u64 (S_stats_coalesced (upd B2 (A_S_queue_bytes a) cs) + 1)) ->
  Bw = set_Cmd_bytes (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B3 s PENDING) s key) s disp) s len)
         s (firstn (Z.to_nat len) cb) ->
  B6 = set_Q_at (set_Cmd_st Bw (Q_at B1 a) REPLACED) a s ->
  B7 = set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32) ->
  wframe R4q B1 B7 /\ agree_q (ops + 1) B7.
Proof.
  intros ops B1 B2 B3 Bw B6 B7 s a key disp len cb cs HB HQ Hr Hops Hs Ha Lcb Lcs Hent Hnew Hkey Htail
    EB2 EB3 EBw EB6 EB7.
  pose proof (d3_ncmd _ _ HQ) as Hn. pose proof (d3_ops _ _ HQ) as Ho. pose proof (d1_nq _ _ HQ Hr) as Hnq.
  pose proof (u_at_nonneg B1 OFF_g_ncmd 4) as Hs0. fold (g_ncmd B1) in Hs0.
  assert (Hsr : 0 <= s < CMDS_MAX) by (unfold CMDS_MAX, OPS_MAX in *; lia).
  destruct (d1_entry _ _ HQ Hr a Ha) as (Hqa & _).
  assert (Hqr : 0 <= Q_at B1 a < CMDS_MAX) by (unfold CMDS_MAX, OPS_MAX in *; lia).
  assert (Hqs : Q_at B1 a <> s) by lia.
  assert (Har : 0 <= a < QUEUE_MAX) by lia.
  pose proof Hnew as Hnew'. destruct Hnew' as (_ & _ & _ & Hlen & Hd & _).
  assert (Hdr : 0 <= disp <= 1) by (destruct Hd; lia).
  destruct (B2_facts B1 B2 s HB Hsr EB2) as (L2 & F2 & _ & _ & Nc2 & _ & _ & _ & _ & Z2).
  destruct (W3_coal B2 B3 a cs L2 ltac:(unfold S_queue_N, QUEUE_MAX in *; lia) Lcs EB3) as (L3 & F3 & Sq3).
  destruct (Wtag B3 Bw s key disp len cb L3 Hsr Lcb Hlen Hkey Hdr EBw) as (Lw & Fw & Stw & Kw & Dw & Lnw & Bw_).
  destruct (W6_coal Bw B6 a (Q_at B1 a) s Lw Har Hqr ltac:(unfold CMDS_MAX in *; lia) EB6) as (L6 & F6 & Q6 & St6).
  assert (Nc6 : g_ncmd B6 = s).
  { assert (E6 : g_ncmd B6 = g_ncmd Bw) by (wkeep F6). assert (Ew : g_ncmd Bw = g_ncmd B3) by (wkeep Fw).
    assert (E3 : g_ncmd B3 = g_ncmd B2) by (wkeep F3). rewrite E6, Ew, E3, Nc2. symmetry. exact Hs. }
  assert (Hv : 0 <= (g_ncmd B6 + 1) mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  destruct (W7 B6 B7 _ L6 Hv EB7) as (L7 & F7 & Nc7).
  assert (F : wframe (Rcoal s a (Q_at B1 a)) B1 B7).
  { apply (wframe_w _ _ _ _ _ F2); [intros x Hx; runf; lia|].
    apply (wframe_w _ _ _ _ _ F3); [intros x Hx; runf; lia|].
    apply (wframe_w _ _ _ _ _ Fw); [intros x Hx; runf; lia|].
    apply (wframe_w _ _ _ _ _ F6); [intros x Hx; runf; lia|].
    eapply wframe_weaken; [|exact F7]. intros x Hx. runf. lia. }
  (* g_cmd[serial] after the record: unchanged by the two writes after it *)
  assert (C7 : forall (P : list byte -> Z -> Z), (forall X Y, wframe RNc X Y -> P Y s = P X s) ->
                 (forall X Y, wframe (Ror (RCst (Q_at B1 a)) (RQ a)) X Y -> P Y s = P X s) -> P B7 s = P Bw s).
  { intros P H7 H6. rewrite (H7 B6 B7 F7). apply (H6 Bw B6 F6). }
  split.
  - eapply wframe_weaken; [|exact F]. intros x Hx. runf. woffs.
  - apply (aq_coalesce ops B1 B7 s a key disp len cb cs HQ Hr Hops Hs Ha).
    + assert (E : g_raw B7 = g_raw B1) by (wkeep F). rewrite E. exact Hr.
    + wkeep F.
    + wkeep F.
    + rewrite Nc7, Nc6. apply Z.mod_small. unfold CMDS_MAX in Hsr. lia.
    + intros j Hj Hja. wkeep F.
    + assert (E : Q_at B7 a = Q_at B6 a) by (wkeep F7). rewrite E. exact Q6.
    + rewrite <- Stw. apply (C7 (fun X k => Cmd_st X k)); intros X Y H; cbv beta; wkeep H.
    + assert (E : Cmd_st B7 (Q_at B1 a) = Cmd_st B6 (Q_at B1 a)) by (wkeep F7). rewrite E. exact St6.
    + intros k Hk Hks Hkq. wkeep F.
    + intros k Hk Hks. unfold cmd_same. split; [wkeep F|]. split; [wkeep F|]. split; wkeep F.
    + rewrite <- Kw. apply (C7 (fun X k => Cmd_key X k)); intros X Y H; cbv beta; wkeep H.
    + rewrite <- Dw. apply (C7 (fun X k => Cmd_display X k)); intros X Y H; cbv beta; wkeep H.
    + rewrite <- Lnw. apply (C7 (fun X k => Cmd_len X k)); intros X Y H; cbv beta; wkeep H.
    + assert (E7 : Cmd_bytes B7 s = Cmd_bytes B6 s) by (wkeep F7).
      assert (E6 : Cmd_bytes B6 s = Cmd_bytes Bw s) by (wkeep F6).
      assert (E3 : sub B3 (A_Cmd_bytes s + len) (24 - Z.to_nat len) =
                   sub B2 (A_Cmd_bytes s + len) (24 - Z.to_nat len)) by (wkeep F3).
      rewrite E7, E6, Bw_, E3, Z2 by (unfold A_Cmd_bytes, A_Cmd_st, Cmd_ESZ; lia). exact Htail.
    + intros i Hi Hia. wkeep F.
    + assert (E7 : sq_ent B7 a = sq_ent B6 a) by (wkeep F7).
      assert (E6 : sq_ent B6 a = sq_ent Bw a) by (wkeep F6).
      assert (Ew : sq_ent Bw a = sq_ent B3 a) by (wkeep Fw).
      rewrite E7, E6, Ew. exact Sq3.
    + exact Hent.
    + exact Hnew.
Qed.

(* appended at g_nq *)
Lemma case_app : forall ops B1 B2 B3 Bw B6 B7 s key disp len cb cs,
  length B1 = WN -> agree_q ops B1 -> g_raw B1 = 0 -> ops < OPS_MAX -> s = g_ncmd B1 -> g_nq B1 < QUEUE_MAX ->
  length cb = 24%nat -> length cs = 32%nat -> new_ent_ok cs key disp len cb -> new_cmd_ok s key disp len cb ->
  0 <= key < 2 ^ 32 -> firstn (Z.to_nat len) cb ++ repeat (b8 0) (24 - Z.to_nat len) = cb ->
  B2 = upd B1 (A_Cmd_st s) (repeat (b8 0) (Z.to_nat Cmd_ESZ)) ->
  B3 = set_S_queued (upd B2 (A_S_queue_bytes (g_nq B1)) cs) (u32 (g_nq B1 + 1)) ->
  Bw = set_Cmd_bytes (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B3 s PENDING) s key) s disp) s len)
         s (firstn (Z.to_nat len) cb) ->
  B6 = set_g_nq (set_Q_at Bw (g_nq B1) s) ((g_nq B1 + 1) mod 2 ^ 32) ->
  B7 = set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32) ->
  wframe R4q B1 B7 /\ agree_q (ops + 1) B7.
Proof.
  intros ops B1 B2 B3 Bw B6 B7 s key disp len cb cs HB HQ Hr Hops Hs Hnq Lcb Lcs Hent Hnew Hkey Htail
    EB2 EB3 EBw EB6 EB7.
  pose proof (d3_ncmd _ _ HQ) as Hn. pose proof (d3_ops _ _ HQ) as Ho. pose proof (d1_queued _ _ HQ Hr) as Hqd.
  pose proof (u_at_nonneg B1 OFF_g_ncmd 4) as Hs0. fold (g_ncmd B1) in Hs0.
  pose proof (u_at_nonneg B1 OFF_g_nq 4) as Hp0. fold (g_nq B1) in Hp0.
  assert (Hsr : 0 <= s < CMDS_MAX) by (unfold CMDS_MAX, OPS_MAX in *; lia).
  assert (Hpr : 0 <= g_nq B1 < QUEUE_MAX) by lia.
  pose proof Hnew as Hnew'. destruct Hnew' as (_ & _ & _ & Hlen & Hd & _).
  assert (Hdr : 0 <= disp <= 1) by (destruct Hd; lia).
  destruct (B2_facts B1 B2 s HB Hsr EB2) as (L2 & F2 & Nq2 & _ & Nc2 & _ & _ & _ & _ & Z2).
  destruct (W3_app B2 B3 (g_nq B1) cs L2 ltac:(unfold S_queue_N, QUEUE_MAX in *; lia) Lcs EB3)
    as (L3 & F3 & Sq3 & Qd3).
  destruct (Wtag B3 Bw s key disp len cb L3 Hsr Lcb Hlen Hkey Hdr EBw) as (Lw & Fw & Stw & Kw & Dw & Lnw & Bw_).
  destruct (W6_app Bw B6 (g_nq B1) s Lw Hpr ltac:(unfold CMDS_MAX in *; lia) EB6) as (L6 & F6 & Q6 & Nq6).
  assert (Nc6 : g_ncmd B6 = s).
  { assert (E6 : g_ncmd B6 = g_ncmd Bw) by (wkeep F6). assert (Ew : g_ncmd Bw = g_ncmd B3) by (wkeep Fw).
    assert (E3 : g_ncmd B3 = g_ncmd B2) by (wkeep F3). rewrite E6, Ew, E3, Nc2. symmetry. exact Hs. }
  assert (Hv : 0 <= (g_ncmd B6 + 1) mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  destruct (W7 B6 B7 _ L6 Hv EB7) as (L7 & F7 & Nc7).
  assert (F : wframe (Rapp s (g_nq B1)) B1 B7).
  { apply (wframe_w _ _ _ _ _ F2); [intros x Hx; runf; lia|].
    apply (wframe_w _ _ _ _ _ F3); [intros x Hx; runf; lia|].
    apply (wframe_w _ _ _ _ _ Fw); [intros x Hx; runf; lia|].
    apply (wframe_w _ _ _ _ _ F6); [intros x Hx; runf; lia|].
    eapply wframe_weaken; [|exact F7]. intros x Hx. runf. lia. }
  assert (C7 : forall (P : list byte -> Z -> Z), (forall X Y, wframe RNc X Y -> P Y s = P X s) ->
                 (forall X Y, wframe (Ror (RQ (g_nq B1)) RNq) X Y -> P Y s = P X s) -> P B7 s = P Bw s).
  { intros P H7 H6. rewrite (H7 B6 B7 F7). apply (H6 Bw B6 F6). }
  split.
  - eapply wframe_weaken; [|exact F]. intros x Hx. runf. woffs.
  - apply (aq_append ops B1 B7 s key disp len cb cs HQ Hr Hops Hs Hnq).
    + assert (E : g_raw B7 = g_raw B1) by (wkeep F). rewrite E. exact Hr.
    + assert (E7 : S_queued B7 = S_queued B6) by (wkeep F7).
      assert (E6 : S_queued B6 = S_queued Bw) by (wkeep F6).
      assert (Ew : S_queued Bw = S_queued B3) by (wkeep Fw).
      rewrite E7, E6, Ew, Qd3, Hqd. reflexivity.
    + assert (E7 : g_nq B7 = g_nq B6) by (wkeep F7). rewrite E7. exact Nq6.
    + rewrite Nc7, Nc6. apply Z.mod_small. unfold CMDS_MAX in Hsr. lia.
    + intros j Hj Hja. wkeep F.
    + assert (E : Q_at B7 (g_nq B1) = Q_at B6 (g_nq B1)) by (wkeep F7). rewrite E. exact Q6.
    + rewrite <- Stw. apply (C7 (fun X k => Cmd_st X k)); intros X Y H; cbv beta; wkeep H.
    + intros k Hk Hks. split; [wkeep F|]. unfold cmd_same. split; [wkeep F|]. split; [wkeep F|]. split; wkeep F.
    + rewrite <- Kw. apply (C7 (fun X k => Cmd_key X k)); intros X Y H; cbv beta; wkeep H.
    + rewrite <- Dw. apply (C7 (fun X k => Cmd_display X k)); intros X Y H; cbv beta; wkeep H.
    + rewrite <- Lnw. apply (C7 (fun X k => Cmd_len X k)); intros X Y H; cbv beta; wkeep H.
    + assert (E7 : Cmd_bytes B7 s = Cmd_bytes B6 s) by (wkeep F7).
      assert (E6 : Cmd_bytes B6 s = Cmd_bytes Bw s) by (wkeep F6).
      assert (E3 : sub B3 (A_Cmd_bytes s + len) (24 - Z.to_nat len) =
                   sub B2 (A_Cmd_bytes s + len) (24 - Z.to_nat len)) by (wkeep F3).
      rewrite E7, E6, Bw_, E3, Z2 by (unfold A_Cmd_bytes, A_Cmd_st, Cmd_ESZ; lia). exact Htail.
    + intros i Hi Hia. wkeep F.
    + assert (E7 : sq_ent B7 (g_nq B1) = sq_ent B6 (g_nq B1)) by (wkeep F7).
      assert (E6 : sq_ent B6 (g_nq B1) = sq_ent Bw (g_nq B1)) by (wkeep F6).
      assert (Ew : sq_ent Bw (g_nq B1) = sq_ent B3 (g_nq B1)) by (wkeep Fw).
      rewrite E7, E6, Ew. exact Sq3.
    + exact Hent.
    + exact Hnew.
Qed.

(* ---------------------------------------------------------------- op 4, tagged mode *)

Lemma submit_tagged_pre : forall I ops B D c, links -> agree I ops B -> ops < OPS_MAX -> g_raw B = 0 -> fuzz_in_ok D c ->
  exists B1 B7 c5, op_begin_m B = Some (B1, tt) /\ wframe R4q B1 B7 /\ agree_q (ops + 1) B7 /\ fuzz_in_ok D c5 /\
    op_submit_m B D c = match settle_m B7 0 with Some (B8, _) => Some (B8, c5) | None => None end.
Proof.
  intros I ops B D c HL HA Hops Hraw Hc.
  destruct HL as (_ & _ & L3 & _).
  assert (HB : length B = WN) by exact (ac_len _ _ _ (ag_core _ _ _ HA)).
  pose proof (ac_q _ _ _ (ag_core _ _ _ HA)) as HQ0. clear HA.
  destruct (op_begin_stage B HB) as (B1 & Hob & Hfr & _ & _).
  assert (HB1 : length B1 = WN) by (destruct Hfr as [Lf _]; rewrite Lf; exact HB).
  destruct (ob_keep ops B B1 Hfr HQ0) as (HQ & Hr1 & Hbefore). rewrite Hraw in Hr1.
  clear HQ0 Hfr.
  pose proof (d3_ncmd _ _ HQ) as Hn. pose proof (d3_ops _ _ HQ) as Ho. pose proof (d1_nq _ _ HQ Hr1) as Hnq.
  pose proof (d1_queued _ _ HQ Hr1) as Hqd.
  pose proof (u_at_nonneg B1 OFF_g_ncmd 4) as Hs0. fold (g_ncmd B1) in Hs0.
  pose proof (u_at_nonneg B1 OFF_g_nq 4) as Hnq0. fold (g_nq B1) in Hnq0.
  (* the cursor (FT:1076-1092) *)
  destruct (fuzz_u8_ok D c Hc) as (c1 & kb & E1 & Hc1 & Hkb).
  destruct (fuzz_u8_ok D c1 Hc1) as (c2 & ab & E2 & Hc2 & Hab).
  destruct (fuzz_u8_ok D c2 Hc2) as (c3 & db & E3 & Hc3 & Hdb).
  destruct (fuzz_u8_ok D c3 Hc3) as (c4 & lb & E4 & Hc4 & Hlb).
  pose proof (Z.mod_pos_bound lb 22 ltac:(lia)) as Hlm.
  destruct (fuzz_take_ok D c4 (lb mod 22 + 3 - 3) Hc4 ltac:(lia)) as (c5 & off & n & E5 & Hc5 & Hn5 & Hoff & Hend & _).
  exists B1.
  enough (G : exists B7, wframe R4q B1 B7 /\ agree_q (ops + 1) B7 /\
    op_submit_m B D c = match settle_m B7 0 with Some (B8, _) => Some (B8, c5) | None => None end).
  { destruct G as (B7 & G1 & G2 & G3). exists B7, c5.
    split; [exact Hob|]. split; [exact G1|]. split; [exact G2|]. split; [exact Hc5|exact G3]. }
  unfold op_submit_m. cbn beta iota zeta. rewrite Hob. cbn beta iota zeta.
  rewrite E1. cbn beta iota zeta. rewrite E2. cbn beta iota zeta. rewrite E3. cbn beta iota zeta.
  assert (Er : negb (g_raw B1 =? 0) = false) by (rewrite Hr1; reflexivity). rewrite Er. cbn beta iota zeta.
  remember (g_ncmd B1) as s eqn:Es.
  assert (Hsr : 0 <= s < CMDS_MAX) by (unfold CMDS_MAX, OPS_MAX in *; lia).
  assert (Ecm : (CMDS_MAX <=? s) = false) by (apply Z.leb_gt; lia). rewrite Ecm. cbn beta iota zeta.
  remember (upd B1 (A_Cmd_st s) (repeat (b8 0) (Z.to_nat Cmd_ESZ))) as B2 eqn:EB2.
  destruct (B2_facts B1 B2 s HB1 Hsr EB2) as (L2 & F2 & Nq2 & Sq2 & Nc2 & Q2 & K2 & SK2 & _ & _).
  rewrite E4. cbn beta iota zeta. rewrite E5. cbn beta iota zeta.
  remember (KEY (kb mod 9 + 1) ab) as key eqn:Ekey.
  remember (Z.land db 1) as disp eqn:Edisp.
  remember (lb mod 22 + 3) as len eqn:Elen.
  remember ([b8 TAG; b8 (Z.land s 0x7f); b8 (Z.land (Z.shiftr s 7) 0x7f)] ++ sub D off (Z.to_nat n)
              ++ repeat (b8 0) (Z.to_nat (21 - n))) as cb eqn:Ecb.
  remember (cmd_struct cb len disp key) as cs eqn:Ecs.
  (* the command *)
  assert (Lp : length (sub D off (Z.to_nat n)) = Z.to_nat n) by (apply length_sub_D; lia).
  destruct (cb_facts s (sub D off (Z.to_nat n)) n cb Lp ltac:(lia) Ecb) as (Lcb & C0 & C1 & C2 & Ctail).
  assert (Hkey : 0 <= key < 2 ^ 32) by (rewrite Ekey; apply key_range; lia).
  destruct (land1_bit db) as (Hdr & Hd). rewrite <- Edisp in Hdr, Hd.
  assert (Hlen : 3 <= len <= 24) by lia.
  destruct (cs_facts cb len disp key cs Lcb ltac:(lia) ltac:(lia) Hkey Ecs)
    as (Lcs & Clen & Cdisp & Ckey & C24 & Cat & Cfirst).
  assert (Htail : firstn (Z.to_nat len) cb ++ repeat (b8 0) (24 - Z.to_nat len) = cb) by (apply Ctail; lia).
  assert (Hent : new_ent_ok cs key disp len cb) by (unfold new_ent_ok; exact (conj C24 (conj Clen (conj Ckey Cdisp)))).
  assert (Hbc : body_check (firstn (Z.to_nat len) cs) = if system_at (firstn (Z.to_nat len) cb) then -10 else 0).
  { rewrite (Cfirst (Z.to_nat len)) by lia. apply body_check_spec. }
  assert (Hl1 : 1 <= cmd_len_of cs <= 24) by (rewrite Clen; lia).
  (* the queues of B1 (D1) *)
  assert (HQs : forall j, 0 <= j < g_nq B1 -> 0 <= Q_at B1 j < s).
  { intros j Hj. destruct (d1_entry _ _ HQ Hr1 j Hj) as (Hq & _). lia. }
  assert (HSK : forall j, 0 <= j < g_nq B1 -> S_queue_key B2 j = Cmd_key B1 (Q_at B1 j)).
  { intros j Hj. destruct (d1_entry _ _ HQ Hr1 j Hj) as (_ & _ & _ & _ & Hk & _).
    rewrite (SK2 j) by (unfold S_queue_N, QUEUE_MAX in *; lia). exact Hk. }
  assert (HSq2 : S_queued B2 = g_nq B1) by (rewrite Sq2; exact Hqd).
  assert (Hq2 : S_queued B2 <= S_queue_N) by (rewrite HSq2; unfold S_queue_N, QUEUE_MAX in *; lia).
  (* at (FT:1097-1101) *)
  rewrite (harness_at B1 B2 s key Nq2 Hsr Q2 K2 Hnq HQs). cbn beta iota zeta.
  rewrite (submit_m_spec B2 cs Hq2).
  rewrite Nq2.
  destruct (system_at (firstn (Z.to_nat len) cb)) eqn:Esys.
  - (* refused: the body holds F0 13 xx 70 *)
    cbn beta iota zeta.
    rewrite (spec_refused B2 cs Hl1 ltac:(intros E; rewrite Clen, Hbc in E; try rewrite Esys in E; cbn in E;
                                          discriminate E)). cbn beta iota zeta.
    remember (set_S_stats_refused B2 (u64 (S_stats_refused B2 + 1))) as B3 eqn:EB3.
    destruct (W3_ref B2 B3 L2 EB3) as (L3' & F3).
    assert (Sq3 : S_queued B3 = S_queued B2) by (wkeep F3).
    rewrite (refusal_ok B3 cs DIGINET_E_REFUSED (S_queued B) len L3 Lcs Cat ltac:(lia)).
    2: { intros E. rewrite Hbc in E. try rewrite Esys in E. cbn in E. discriminate E. }
    2: { intros _. split; [reflexivity|]. rewrite Sq3, Sq2. exact Hbefore. }
    cbn beta iota zeta.
    assert (Ew : (SPEC_E_REFUSED =? SPEC_OK) = false) by reflexivity. rewrite Ew. cbn beta iota zeta.
    remember (set_g_ncmd B3 ((g_ncmd B3 + 1) mod 2 ^ 32)) as B7 eqn:EB7.
    exists B7. split; [|split].
    + exact (proj1 (case_noop ops B1 B2 B3 B7 s HB1 HQ Hr1 Hops Es EB2 L3' F3 EB7)).
    + exact (proj2 (case_noop ops B1 B2 B3 B7 s HB1 HQ Hr1 Hops Es EB2 L3' F3 EB7)).
    + reflexivity.
  - cbn beta iota zeta.
    assert (Hb0 : body_check (firstn (Z.to_nat (cmd_len_of cs)) cs) = DIGINET_OK)
      by (rewrite Clen, Hbc; try rewrite Esys; reflexivity).
    assert (Hok : body_check (firstn (Z.to_nat len) cs) = DIGINET_OK) by (rewrite Hbc; try rewrite Esys; reflexivity).
    destruct (if h_coalescable_m key =? 0 then None
              else first_idx (fun j => Cmd_key B1 (Q_at B1 j) =? key) 0 (Z.to_nat (g_nq B1))) as [a|] eqn:EF.
    + (* coalesced at a *)
      assert (Ha : 0 <= a < g_nq B1).
      { revert EF. destruct (h_coalescable_m key =? 0); intros EF; [discriminate EF|].
        apply first_idx_some in EF. lia. }
      cbn beta iota zeta.
      rewrite (spec_found B2 cs a Hl1 Hb0 (eq_trans (session_fi B1 B2 cs key Ckey HSq2 HSK) EF)).
      cbn beta iota zeta.
      remember (set_S_stats_coalesced (upd B2 (A_S_queue_bytes a) cs)
                  (u64 (S_stats_coalesced (upd B2 (A_S_queue_bytes a) cs) + 1))) as B3 eqn:EB3.
      rewrite (refusal_ok B3 cs DIGINET_OK (S_queued B) len L3 Lcs Cat ltac:(lia)).
      2: { intros _. unfold DIGINET_OK, SPEC_E_REFUSED. discriminate. }
      2: { intros Hne. exfalso. exact (Hne Hok). }
      cbn beta iota zeta.
      assert (Ea : (a <? 0) = false) by (apply Z.ltb_ge; lia). rewrite Ea, Bool.andb_false_l. cbn beta iota zeta.
      rewrite (latest_ok B3 DIGINET_OK SPEC_OK eq_refl). cbn beta iota zeta.
      rewrite (Z.eqb_refl SPEC_OK). cbn beta iota zeta.
      remember (set_Cmd_bytes (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B3 s PENDING) s key) s disp)
                  s len) s (firstn (Z.to_nat len) cb)) as Bw eqn:EBw.
      assert (Ea0 : (0 <=? a) = true) by (apply Z.leb_le; lia). rewrite Ea0. cbn beta iota zeta.
      rewrite (coal_qBw B1 B2 B3 Bw s a key disp len cb cs HB1 Hsr ltac:(unfold QUEUE_MAX in *; lia) Lcs Lcb Hlen
                 Hkey Hdr EB2 EB3 EBw).
      assert (Eq : (CMDS_MAX <=? Q_at B1 a) = false) by (apply Z.leb_gt; specialize (HQs a Ha); lia).
      rewrite Eq. cbn beta iota zeta.
      remember (set_Q_at (set_Cmd_st Bw (Q_at B1 a) REPLACED) a s) as B6 eqn:EB6.
      remember (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) as B7 eqn:EB7.
      assert (Hnew : new_cmd_ok s key disp len cb)
        by (unfold new_cmd_ok; exact (conj C0 (conj C1 (conj C2 (conj Hlen (conj Hd Esys)))))).
      exists B7. split; [|split].
      * exact (proj1 (case_coal ops B1 B2 B3 Bw B6 B7 s a key disp len cb cs HB1 HQ Hr1 Hops Es Ha Lcb Lcs Hent Hnew
                       Hkey Htail EB2 EB3 EBw EB6 EB7)).
      * exact (proj2 (case_coal ops B1 B2 B3 Bw B6 B7 s a key disp len cb cs HB1 HQ Hr1 Hops Es Ha Lcb Lcs Hent Hnew
                       Hkey Htail EB2 EB3 EBw EB6 EB7)).
      * reflexivity.
    + (* no place: E_SPACE when 512 are pending, else appended *)
      cbn beta iota zeta.
      rewrite (spec_none B2 cs Hl1 Hb0 (eq_trans (session_fi B1 B2 cs key Ckey HSq2 HSK) EF)).
      assert (Em : (-1 <? 0) = true) by reflexivity. rewrite Em, Bool.andb_true_l.
      rewrite HSq2.
      destruct (Z.eqb_spec (g_nq B1) QUEUE_MAX) as [Efull|Enfull].
      * (* E_SPACE *)
        assert (Ef1 : (g_nq B1 =? DIGINET_QUEUE_MAX) = true) by (rewrite Efull; reflexivity).
        rewrite Ef1. cbn beta iota zeta.
        rewrite (refusal_ok B2 cs DIGINET_E_SPACE (S_queued B) len L3 Lcs Cat ltac:(lia)).
        2: { intros _. unfold DIGINET_E_SPACE, SPEC_E_REFUSED. discriminate. }
        2: { intros Hne. exfalso. exact (Hne Hok). }
        cbn beta iota zeta.
        rewrite (latest_ok B2 DIGINET_E_SPACE SPEC_E_SPACE eq_refl). cbn beta iota zeta.
        assert (Ew : (SPEC_E_SPACE =? SPEC_OK) = false) by reflexivity. rewrite Ew. cbn beta iota zeta.
        remember (set_g_ncmd B2 ((g_ncmd B2 + 1) mod 2 ^ 32)) as B7 eqn:EB7.
        exists B7. split; [|split].
        -- exact (proj1 (case_noop ops B1 B2 B2 B7 s HB1 HQ Hr1 Hops Es EB2 L2 (wframe_refl _ _) EB7)).
        -- exact (proj2 (case_noop ops B1 B2 B2 B7 s HB1 HQ Hr1 Hops Es EB2 L2 (wframe_refl _ _) EB7)).
        -- reflexivity.
      * (* appended *)
        assert (Ef1 : (g_nq B1 =? DIGINET_QUEUE_MAX) = false)
          by (apply Z.eqb_neq; unfold DIGINET_QUEUE_MAX; unfold QUEUE_MAX in Enfull; exact Enfull).
        assert (Hnq' : g_nq B1 < QUEUE_MAX) by lia.
        rewrite Ef1. cbn beta iota zeta.
        remember (set_S_queued (upd B2 (A_S_queue_bytes (g_nq B1)) cs) (u32 (g_nq B1 + 1))) as B3 eqn:EB3.
        rewrite (refusal_ok B3 cs DIGINET_OK (S_queued B) len L3 Lcs Cat ltac:(lia)).
        2: { intros _. unfold DIGINET_OK, SPEC_E_REFUSED. discriminate. }
        2: { intros Hne. exfalso. exact (Hne Hok). }
        cbn beta iota zeta.
        rewrite (latest_ok B3 DIGINET_OK SPEC_OK eq_refl). cbn beta iota zeta.
        rewrite (Z.eqb_refl SPEC_OK). cbn beta iota zeta.
        remember (set_Cmd_bytes (set_Cmd_len (set_Cmd_display (set_Cmd_key (set_Cmd_st B3 s PENDING) s key) s disp)
                    s len) s (firstn (Z.to_nat len) cb)) as Bw eqn:EBw.
        assert (Em0 : (0 <=? -1) = false) by reflexivity. rewrite Em0. cbn beta iota zeta.
        rewrite (app_nqBw B1 B2 B3 Bw s (g_nq B1) key disp len cb cs HB1 Hsr ltac:(lia) Lcs Lcb Hlen Hkey Hdr
                   EB2 EB3 EBw).
        assert (Eq : (CMDS_MAX <=? g_nq B1) = false) by (apply Z.leb_gt; unfold CMDS_MAX, QUEUE_MAX in *; lia).
        rewrite Eq. cbn beta iota zeta.
        remember (set_g_nq (set_Q_at Bw (g_nq B1) s) ((g_nq B1 + 1) mod 2 ^ 32)) as B6 eqn:EB6.
        remember (set_g_ncmd B6 ((g_ncmd B6 + 1) mod 2 ^ 32)) as B7 eqn:EB7.
        assert (Hnew : new_cmd_ok s key disp len cb)
          by (unfold new_cmd_ok; exact (conj C0 (conj C1 (conj C2 (conj Hlen (conj Hd Esys)))))).
        exists B7. split; [|split].
        -- exact (proj1 (case_app ops B1 B2 B3 Bw B6 B7 s key disp len cb cs HB1 HQ Hr1 Hops Es Hnq' Lcb Lcs Hent
                          Hnew Hkey Htail EB2 EB3 EBw EB6 EB7)).
        -- exact (proj2 (case_app ops B1 B2 B3 Bw B6 B7 s key disp len cb cs HB1 HQ Hr1 Hops Es Hnq' Lcb Lcs Hent
                          Hnew Hkey Htail EB2 EB3 EBw EB6 EB7)).
        -- reflexivity.
Qed.
