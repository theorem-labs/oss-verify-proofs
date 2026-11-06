(* Pure facts about the Gallina model (TSess0.v, TCb.v) that the walk of diginet_session_tick uses:
   the ranges of take's results, and that notice leaves g_fail_next unchanged. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess.
Import ListNotations.
Open Scope Z_scope.

(* ==== take ==== *)

Lemma tsf_qlen : forall B i, 0 <= S_queue_len B i < 256.
Proof. intros B i. exact (u_at_range B (A_S_queue_len i) 1). Qed.

Lemma tsf_qdisp : forall B i, 0 <= S_queue_display B i < 256.
Proof. intros B i. exact (u_at_range B (A_S_queue_display i) 1). Qed.

Lemma tsf_log2_byte : forall a, 0 <= a < 256 -> Z.log2 a < 8.
Proof.
  intros a Ha. destruct (Z.eq_dec a 0) as [->|E]; [cbn; lia|].
  apply (proj1 (Z.log2_lt_pow2 a 8 ltac:(lia))). change (2 ^ 8) with 256. lia.
Qed.

(* the OR of two byte values is a byte value *)
Lemma tsf_lor_byte : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros a b Ha Hb. assert (P : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  split; [exact P|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [lia|].
  assert (L : Z.log2 (Z.lor a b) < 8).
  { rewrite Z.log2_lor by lia. pose proof (tsf_log2_byte a Ha). pose proof (tsf_log2_byte b Hb). lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) 8 ltac:(lia))) in L. change (2 ^ 8) with 256 in L. lia.
Qed.

(* take's loop: each turn adds at most one to taken, keeps len <= 1484 (the turn that would pass it is None)
   and ORs a byte into has_display *)
Lemma tsf_take_loop : forall fuel B allow i taken kept len hd body B' body' len' hd' taken' kept' Q,
  take_loop_m B allow i taken kept len hd body fuel = Some (B', (body', len', hd', taken', kept')) ->
  0 <= taken -> taken + Z.of_nat fuel <= Q -> 0 <= len <= 1484 -> 0 <= hd < 256 ->
  0 <= taken' <= Q /\ 0 <= len' <= 1484 /\ 0 <= hd' < 256.
Proof.
  induction fuel as [|f IH];
    intros B allow i taken kept len hd body B' body' len' hd' taken' kept' Q H Ht HQ Hl Hh.
  - cbn [take_loop_m] in H. injection H; intros; subst. lia.
  - cbn [take_loop_m] in H.
    pose proof (tsf_qlen B i) as Rc. pose proof (tsf_qdisp B i) as Rd.
    destruct (S_queue_N <=? i); [discriminate|].
    match type of H with context [?f0 && (DIGINET_MAX_BODY_LEN <? ?s)] =>
      destruct (f0 && (DIGINET_MAX_BODY_LEN <? s)) eqn:Ebig; [discriminate|] end.
    match type of H with context [?f0 && (body_check ?cnd =? DIGINET_OK)] =>
      destruct (f0 && (body_check cnd =? DIGINET_OK)) eqn:Efit end.
    + apply andb_prop in Efit as [Hf0 _]. rewrite Hf0, andb_true_l in Ebig. apply Z.ltb_ge in Ebig.
      unfold DIGINET_MAX_BODY_LEN in Ebig. cbn beta iota in H.
      match type of H with (if ?c then _ else _) = _ => destruct c end.
      * match type of H with (match ?x with _ => _ end) = _ => destruct x as [[B2 k2]|] end;
          cbn beta iota in H; [|discriminate].
        injection H; intros; subst. split; [lia|]. split; [lia|]. apply tsf_lor_byte; assumption.
      * eapply IH; [exact H | lia | lia | lia | apply tsf_lor_byte; assumption].
    + cbn beta iota in H.
      match type of H with (if ?c then _ else _) = _ => destruct c end.
      * match type of H with (match ?x with _ => _ end) = _ => destruct x as [[B2 k2]|] end;
          cbn beta iota in H; [|discriminate].
        injection H; intros; subst. lia.
      * eapply IH; [exact H | lia | lia | lia | assumption].
Qed.

(* take's results as tick uses them: the count it returns is an unsigned (<= s->queued), the body length fits
   tick's body[1484], *has_display is an OR of uint8_t display flags. *)
Lemma take_m_out : forall B allow B' body len hd taken,
  take_m B allow = Some (B', (body, len, hd, taken)) ->
  0 <= taken < 2^32 /\ 0 <= len <= 1484 /\ 0 <= hd < 256.
Proof.
  intros B allow B' body len hd taken H. unfold take_m in H.
  destruct (take_loop_m B allow 0 0 0 0 0 [] (Z.to_nat (S_queued B)))
    as [[B1 [[[[body1 len1] hd1] taken1] kept1]]|] eqn:E; [|discriminate].
  injection H; intros; subst.
  assert (RQ : 0 <= S_queued B < 2 ^ 32) by exact (u_at_range B A_S_queued 4).
  destruct (tsf_take_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S_queued B) E) as (R1 & R2 & R3);
    [lia | rewrite Z2Nat.id by lia; lia | lia | lia |].
  lia.
Qed.

(* ==== worlds that keep g_fail_next ==== *)

(* B is a whole world and its g_fail_next byte holds v *)
Definition tsf_gf (v : Z) (B : list byte) : Prop := length B = Z.to_nat W_LEN /\ g_fail_next B = v.

Lemma tsf_len : forall B : list byte, length B = Z.to_nat W_LEN -> Z.of_nat (length B) = W_LEN.
Proof. intros B H. rewrite H. apply Z2Nat.id. unfold W_LEN. lia. Qed.

(* a write inside the world that misses the g_fail_next byte keeps it *)
Lemma tsf_gf_upd : forall v B k w, tsf_gf v B -> 0 <= k -> k + Z.of_nat (length w) <= W_LEN ->
  (k + Z.of_nat (length w) <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) -> tsf_gf v (upd B k w).
Proof.
  intros v B k w [HL HG] Hk Hl Hd. pose proof (tsf_len B HL) as HZ. split.
  - rewrite length_upd by lia. exact HL.
  - unfold g_fail_next in *. rewrite u_at_upd_out; [exact HG | lia | unfold OFF_g_fail_next; lia | | lia].
    unfold OFF_g_fail_next in *. lia.
Qed.

Lemma tsf_gf_put : forall v B k n x, tsf_gf v B -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  (k + Z.of_nat n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k) -> tsf_gf v (upd B k (put n x)).
Proof. intros. apply tsf_gf_upd; rewrite ?length_put; assumption. Qed.

Ltac tsf_num :=
  cbv [W_LEN OFF_g_fail_next OFF_M OFF_GOT A_M_fly_on
       A_GOT_n A_GOT_desk A_GOT_foreign A_GOT_acked A_GOT_ndata
       A_GOT_t_state A_GOT_t_old A_GOT_t_reason TRANS_MAX] in *; lia.

Ltac tsf_put := intros; apply tsf_gf_put; [assumption | tsf_num ..].

(* the writes notice makes; each misses 0xfdc8 *)
Lemma gf_set_M_fly_on : forall v B x, tsf_gf v B -> tsf_gf v (set_M_fly_on B x).
Proof. unfold set_M_fly_on. tsf_put. Qed.
Lemma gf_set_GOT_n : forall v B x, tsf_gf v B -> tsf_gf v (set_GOT_n B x).
Proof. unfold set_GOT_n. tsf_put. Qed.
Lemma gf_set_GOT_desk : forall v B x, tsf_gf v B -> tsf_gf v (set_GOT_desk B x).
Proof. unfold set_GOT_desk. tsf_put. Qed.
Lemma gf_set_GOT_foreign : forall v B x, tsf_gf v B -> tsf_gf v (set_GOT_foreign B x).
Proof. unfold set_GOT_foreign. tsf_put. Qed.
Lemma gf_set_GOT_acked : forall v B x, tsf_gf v B -> tsf_gf v (set_GOT_acked B x).
Proof. unfold set_GOT_acked. tsf_put. Qed.
Lemma gf_set_GOT_ndata : forall v B x, tsf_gf v B -> tsf_gf v (set_GOT_ndata B x).
Proof. unfold set_GOT_ndata. tsf_put. Qed.
Lemma gf_set_GOT_t_state : forall v B g x, tsf_gf v B -> 0 <= g < 16 -> tsf_gf v (set_GOT_t_state B g x).
Proof. unfold set_GOT_t_state. tsf_put. Qed.
Lemma gf_set_GOT_t_old : forall v B g x, tsf_gf v B -> 0 <= g < 16 -> tsf_gf v (set_GOT_t_old B g x).
Proof. unfold set_GOT_t_old. tsf_put. Qed.
Lemma gf_set_GOT_t_reason : forall v B g x, tsf_gf v B -> 0 <= g < 16 -> tsf_gf v (set_GOT_t_reason B g x).
Proof. unfold set_GOT_t_reason. tsf_put. Qed.

Ltac gf1 :=
  match goal with
  | |- tsf_gf _ (set_M_fly_on _ _) => apply gf_set_M_fly_on
  | |- tsf_gf _ (set_GOT_n _ _) => apply gf_set_GOT_n
  | |- tsf_gf _ (set_GOT_desk _ _) => apply gf_set_GOT_desk
  | |- tsf_gf _ (set_GOT_foreign _ _) => apply gf_set_GOT_foreign
  | |- tsf_gf _ (set_GOT_acked _ _) => apply gf_set_GOT_acked
  | |- tsf_gf _ (set_GOT_ndata _ _) => apply gf_set_GOT_ndata
  | |- tsf_gf _ (set_GOT_t_state _ _ _) => apply gf_set_GOT_t_state
  | |- tsf_gf _ (set_GOT_t_old _ _ _) => apply gf_set_GOT_t_old
  | |- tsf_gf _ (set_GOT_t_reason _ _ _) => apply gf_set_GOT_t_reason
  end.

Ltac tsf_bools :=
  repeat match goal with
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  end.

Ltac tsf_gf_solve := repeat (first [assumption | gf1]); try (tsf_bools; tsf_num).

(* ---- one step of the case analysis of a hypothesis `model = Some _` ---- *)
Ltac tsf_step :=
  match goal with
  | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
  | H : None = Some _ |- _ => discriminate H
  | H : match ?x with _ => _ end = Some _ |- _ =>
      first [ is_var x; destruct x | let E := fresh "E" in destruct x eqn:E ]; cbn beta iota in H
  end.

(* ---- the checks notice calls return the world they were given ---- *)
Ltac tsf_same := intros; match goal with H : _ = Some _ |- _ => cbv beta zeta in H end; repeat tsf_step; reflexivity.

Lemma ck_state_online : forall B B' u, check_state_online_m B = Some (B', u) -> B' = B.
Proof. unfold check_state_online_m. tsf_same. Qed.
Lemma ck_inflight_acked : forall B n B' u, check_inflight_acked_m B n = Some (B', u) -> B' = B.
Proof. unfold check_inflight_acked_m. tsf_same. Qed.
Lemma ck_inflight_lost : forall B n B' u, check_inflight_lost_m B n = Some (B', u) -> B' = B.
Proof. unfold check_inflight_lost_m. tsf_same. Qed.
Lemma ck_state_desk : forall I F B n B' u, check_state_desk_m I F B n = Some (B', u) -> B' = B.
Proof. unfold check_state_desk_m. tsf_same. Qed.
Lemma ck_state_data : forall F B n B' u, check_state_data_m F B n = Some (B', u) -> B' = B.
Proof. unfold check_state_data_m. tsf_same. Qed.

(* ---- the walk through notice ---- *)
Ltac tsf_walk :=
  repeat match goal with
  | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
  | H : None = Some _ |- _ => discriminate H
  | H : check_state_online_m _ = Some (_, _) |- _ => apply ck_state_online in H; subst
  | H : check_inflight_acked_m _ _ = Some (_, _) |- _ => apply ck_inflight_acked in H; subst
  | H : check_inflight_lost_m _ _ = Some (_, _) |- _ => apply ck_inflight_lost in H; subst
  | H : check_state_desk_m _ _ _ _ = Some (_, _) |- _ => apply ck_state_desk in H; subst
  | H : check_state_data_m _ _ _ = Some (_, _) |- _ => apply ck_state_data in H; subst
  | H : match ?x with _ => _ end = Some _ |- _ =>
      first [ is_var x; destruct x | let E := fresh "E" in destruct x eqn:E ]; cbn beta iota in H
  end.

(* notice writes GOT and M.fly.on, never g_fail_next. *)
Lemma notice_m_fail_next : forall I F B n B',
  length B = Z.to_nat W_LEN ->
  notice_m I F B n = Some (B', tt) ->
  g_fail_next B' = g_fail_next B.
Proof.
  intros I F B n B' HL H.
  assert (G : tsf_gf (g_fail_next B) B) by (split; [exact HL | reflexivity]).
  enough (R : tsf_gf (g_fail_next B) B') by (destruct R as [_ R]; exact R).
  unfold notice_m in H. cbv beta zeta in H.
  set (v := g_fail_next B) in G |- *. clearbody v.
  tsf_walk.
  all: tsf_gf_solve.
Qed.
