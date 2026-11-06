From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree SimLib.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- the queue views *)

(* the world's length (TWorld.v: the .bss region of W_LEN bytes) *)
Definition WN : nat := Z.to_nat W_LEN.

(* zseq n = 0, 1, ..., n - 1 is DgnSpec.v's (n : nat) *)

(* s->queue[i], the 32 bytes of the struct diginet_cmd (TSess0.v: bytes[24] at 0, len at 24, display at 25, key at
   28; cmd_len_of, cmd_display_of, cmd_key_of read them) *)
Definition sq_ent (B : list byte) (i : Z) : list byte := sub B (A_S_queue_bytes i) 32.
(* the session's queue s->queue[0 .. s->queued) *)
Definition sq (B : list byte) : list (list byte) := map (sq_ent B) (zseq (Z.to_nat (S_queued B))).
(* the harness's queue g_q[0 .. g_nq): serials into g_cmd *)
Definition hq (B : list byte) : list Z := map (Q_at B) (zseq (Z.to_nat (g_nq B))).

Lemma in_zseq : forall n i, In i (zseq n) <-> 0 <= i < Z.of_nat n.
Proof.
  intros n i. unfold zseq. rewrite in_map_iff. split.
  - intros [t [<- Ht]]. apply in_seq in Ht. lia.
  - intros Hi. exists (Z.to_nat i). split; [lia|]. apply in_seq. lia.
Qed.

Lemma length_zseq : forall n, length (zseq n) = n.
Proof. intros n. unfold zseq. rewrite length_map, length_seq. reflexivity. Qed.

Lemma nth_zseq : forall n t d, (t < n)%nat -> nth t (zseq n) d = Z.of_nat t.
Proof.
  intros n t d Ht. unfold zseq. rewrite nth_indep with (d' := Z.of_nat 0) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by exact Ht. reflexivity.
Qed.

Lemma zseq_succ : forall n, zseq (S n) = zseq n ++ [Z.of_nat n].
Proof. intros n. unfold zseq. rewrite seq_S, map_app. reflexivity. Qed.

Lemma NoDup_zseq : forall n, List.NoDup (zseq n).
Proof. intros n. unfold zseq. apply List.NoDup_map_inv with (f := Z.to_nat). rewrite map_map.
  rewrite (map_ext_in _ (fun x => x)) by (intros; lia). rewrite map_id. apply List.seq_NoDup. Qed.

(* the session's queue entry, field by field *)
Lemma S_queue_bytes_ent : forall B i, 0 <= i -> S_queue_bytes B i = firstn 24 (sq_ent B i).
Proof. intros B i Hi. unfold S_queue_bytes, sq_ent, sub. rewrite firstn_firstn. reflexivity. Qed.

Lemma S_queue_len_ent : forall B i, 0 <= i -> S_queue_len B i = cmd_len_of (sq_ent B i).
Proof.
  intros B i Hi. unfold S_queue_len, cmd_len_of, sq_ent, u_at. rewrite sub_sub by (unfold A_S_queue_bytes, OFF_g_s; lia).
  unfold A_S_queue_len, A_S_queue_bytes. do 2 f_equal. lia.
Qed.

Lemma S_queue_display_ent : forall B i, 0 <= i -> S_queue_display B i = cmd_display_of (sq_ent B i).
Proof.
  intros B i Hi. unfold S_queue_display, cmd_display_of, sq_ent, u_at.
  rewrite sub_sub by (unfold A_S_queue_bytes, OFF_g_s; lia).
  unfold A_S_queue_display, A_S_queue_bytes. do 2 f_equal. lia.
Qed.

Lemma S_queue_key_ent : forall B i, 0 <= i -> S_queue_key B i = cmd_key_of (sq_ent B i).
Proof.
  intros B i Hi. unfold S_queue_key, cmd_key_of, sq_ent, u_at.
  rewrite sub_sub by (unfold A_S_queue_bytes, OFF_g_s; lia).
  unfold A_S_queue_key, A_S_queue_bytes. do 2 f_equal. lia.
Qed.

(* one entry written: the others read as before *)
Lemma sq_ent_upd : forall B i j e, length B = WN -> 0 <= i < S_queue_N -> 0 <= j < S_queue_N -> length e = 32%nat ->
  sq_ent (upd B (A_S_queue_bytes i) e) j = if i =? j then e else sq_ent B j.
Proof.
  intros B i j e HB Hi Hj He. unfold sq_ent.
  assert (Hl : A_S_queue_bytes i + Z.of_nat (length e) <= Z.of_nat (length B))
    by (rewrite HB, He; unfold WN, W_LEN, A_S_queue_bytes, OFF_g_s, S_queue_N in *; lia).
  destruct (Z.eqb_spec i j) as [<-|Hij].
  - apply sub_upd_eq; [unfold A_S_queue_bytes, OFF_g_s; lia | exact He | exact Hl].
  - apply sub_upd_out; [unfold A_S_queue_bytes, OFF_g_s; lia .. | | exact Hl].
    rewrite He. unfold A_S_queue_bytes. lia.
Qed.

Lemma u_at_nonneg : forall B k n, 0 <= u_at B k n.
Proof. intros B k n. exact (proj1 (u_at_range B k n)). Qed.

Lemma u_at_bound : forall B k n, u_at B k n < 2 ^ (8 * Z.of_nat n).
Proof. intros B k n. exact (proj2 (u_at_range B k n)). Qed.

(* ---------------------------------------------------------------- the first index a test holds at *)

Fixpoint first_idx (p : Z -> bool) (i : Z) (fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S f => if p i then Some i else first_idx p (i + 1) f
  end.

Lemma first_idx_some : forall p fuel i j, first_idx p i fuel = Some j ->
  i <= j < i + Z.of_nat fuel /\ p j = true /\ forall j', i <= j' < j -> p j' = false.
Proof.
  intros p fuel. induction fuel as [|f IH]; intros i j H; cbn [first_idx] in H; [discriminate|].
  destruct (p i) eqn:E.
  - injection H as <-. split; [lia|]. split; [exact E|]. intros; lia.
  - apply IH in H as (H1 & H2 & H3). split; [lia|]. split; [exact H2|].
    intros j' Hj'. destruct (Z.eq_dec j' i) as [->|Hne]; [exact E|]. apply H3. lia.
Qed.

Lemma first_idx_none : forall p fuel i, first_idx p i fuel = None ->
  forall j, i <= j < i + Z.of_nat fuel -> p j = false.
Proof.
  intros p fuel. induction fuel as [|f IH]; intros i H j Hj; cbn [first_idx] in H; [lia|].
  destruct (p i) eqn:E; [discriminate|].
  destruct (Z.eq_dec j i) as [->|Hne]; [exact E|]. apply (IH (i + 1)); [exact H|lia].
Qed.

Lemma first_idx_ext : forall p q fuel i, (forall j, i <= j < i + Z.of_nat fuel -> p j = q j) ->
  first_idx p i fuel = first_idx q i fuel.
Proof.
  intros p q fuel. induction fuel as [|f IH]; intros i H; cbn [first_idx]; [reflexivity|].
  rewrite (H i) by lia. destruct (q i); [reflexivity|]. apply IH. intros j Hj. apply H. lia.
Qed.

(* ---------------------------------------------------------------- the two scans for a command's key *)

(* the session's, diginet_session.c:337-343 *)
Lemma submit_find_m_first : forall B key fuel i, 0 <= i -> i + Z.of_nat fuel <= S_queue_N ->
  submit_find_m B key i fuel = Some (first_idx (fun j => S_queue_key B j =? key) i fuel).
Proof.
  intros B key fuel. induction fuel as [|f IH]; intros i Hi Hf; cbn [submit_find_m first_idx]; [reflexivity|].
  destruct (Z.leb_spec S_queue_N i); [lia|].
  destruct (S_queue_key B i =? key); [reflexivity|]. apply IH; lia.
Qed.

(* the harness's, fuzz_transport.c:1097-1101: the first place at, or -1 *)
Lemma submit_find_at_first : forall B key fuel i, 0 <= i <= g_nq B -> g_nq B <= CMDS_MAX ->
  (Z.to_nat (g_nq B - i) < fuel)%nat ->
  (forall j, i <= j < g_nq B -> Q_at B j < CMDS_MAX) ->
  submit_find_at fuel B key i =
    Some (match first_idx (fun j => Cmd_key B (Q_at B j) =? key) i (Z.to_nat (g_nq B - i)) with
          | Some j => j | None => -1 end).
Proof.
  intros B key fuel. induction fuel as [|f IH]; intros i Hi Hn Hf HQ; [lia|].
  cbn [submit_find_at].
  destruct (Z.ltb_spec i (g_nq B)) as [Hlt|Hge].
  - destruct (Z.leb_spec CMDS_MAX i); [lia|].
    destruct (Z.leb_spec CMDS_MAX (Q_at B i)); [specialize (HQ i); lia|].
    replace (Z.to_nat (g_nq B - i)) with (S (Z.to_nat (g_nq B - (i + 1)))) by lia.
    cbn [first_idx]. destruct (Cmd_key B (Q_at B i) =? key); [reflexivity|].
    apply IH; try lia. intros j Hj; apply HQ; lia.
  - replace (Z.to_nat (g_nq B - i)) with 0%nat by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------- diginet_session_submit (diginet_session.c:328-349) *)

(* diginet_session_submit_m with the scan of :337-343 as first_idx; its None branches (an index >= 512) are gone,
   which needs s->queued <= 512 (D1, D4) *)
Definition submit_spec (B : list byte) (c : list byte) : list byte * Z :=
  let len := cmd_len_of c in
  if (len =? 0) || (DIGINET_CMD_MAX_LEN <? len) then (B, DIGINET_E_ARG)
  else if negb (body_check (firstn (Z.to_nat len) c) =? DIGINET_OK) then
    (set_S_stats_refused B (u64 (S_stats_refused B + 1)), DIGINET_E_REFUSED)
  else
    match (if coalescable_m (cmd_key_of c) =? 0 then None
           else first_idx (fun j => S_queue_key B j =? cmd_key_of c) 0 (Z.to_nat (S_queued B))) with
    | Some i =>
        let B1 := upd B (A_S_queue_bytes i) c in
        (set_S_stats_coalesced B1 (u64 (S_stats_coalesced B1 + 1)), DIGINET_OK)
    | None =>
        let q := S_queued B in
        if q =? DIGINET_QUEUE_MAX then (B, DIGINET_E_SPACE)
        else (set_S_queued (upd B (A_S_queue_bytes q) c) (u32 (q + 1)), DIGINET_OK)
    end.

Lemma submit_m_spec : forall B c, S_queued B <= S_queue_N ->
  diginet_session_submit_m B c = Some (submit_spec B c).
Proof.
  intros B c Hq. pose proof (u_at_nonneg B A_S_queued 4) as Hq0. fold (S_queued B) in Hq0.
  unfold diginet_session_submit_m, submit_spec.
  destruct (_ || _); [reflexivity|]. destruct (negb _); [reflexivity|].
  destruct (coalescable_m (cmd_key_of c) =? 0).
  - destruct (Z.eqb_spec (S_queued B) DIGINET_QUEUE_MAX); [reflexivity|].
    destruct (Z.leb_spec S_queue_N (S_queued B)); [unfold S_queue_N, DIGINET_QUEUE_MAX in *; lia|]. reflexivity.
  - rewrite submit_find_m_first by lia.
    destruct (first_idx _ _ _); [reflexivity|].
    destruct (Z.eqb_spec (S_queued B) DIGINET_QUEUE_MAX); [reflexivity|].
    destruct (Z.leb_spec S_queue_N (S_queued B)); [unfold S_queue_N, DIGINET_QUEUE_MAX in *; lia|]. reflexivity.
Qed.

(* ---------------------------------------------------------------- the input cursor (fuzz.h:29-76, TOps.v) *)

(* the cursor { p, n } over the size bytes of D: p = D + fi_off, and p + n is the end of D *)
Definition fuzz_in_ok (D : list byte) (c : fuzz_in) : Prop :=
  0 <= fi_off c /\ 0 <= fi_n c /\ fi_off c + fi_n c = Z.of_nat (length D).

Lemma fuzz_in_m_ok : forall D, fuzz_in_ok D (fuzz_in_m (Z.of_nat (length D))).
Proof. intros D. unfold fuzz_in_ok, fuzz_in_m. cbn. lia. Qed.

Lemma fuzz_u8_ok : forall D c, fuzz_in_ok D c ->
  exists c' v, fuzz_u8_m D c = (c', v) /\ fuzz_in_ok D c' /\ 0 <= v < 256.
Proof.
  intros D c (H0 & H1 & H2). unfold fuzz_u8_m.
  destruct (Z.eqb_spec (fi_n c) 0).
  - exists c, 0. split; [reflexivity|]. split; [unfold fuzz_in_ok; lia | lia].
  - eexists _, _. split; [reflexivity|]. split; [unfold fuzz_in_ok; cbn; lia|].
    unfold at8. pose proof (bz_range (nth (Z.to_nat (fi_off c)) D (b8 0))). lia.
Qed.

Lemma fuzz_u16_ok : forall D c, fuzz_in_ok D c ->
  exists c' v, fuzz_u16_m D c = (c', v) /\ fuzz_in_ok D c' /\ 0 <= v < 65536.
Proof.
  intros D c Hc. unfold fuzz_u16_m.
  destruct (fuzz_u8_ok D c Hc) as (c1 & lo & E1 & Hc1 & _). rewrite E1.
  destruct (fuzz_u8_ok D c1 Hc1) as (c2 & hi & E2 & Hc2 & _). rewrite E2.
  eexists _, _. split; [reflexivity|]. split; [exact Hc2|]. apply Z.mod_pos_bound. lia.
Qed.

(* fuzz_take: the bytes handed out are the n bytes at off, all inside D *)
Lemma fuzz_take_ok : forall D c want, fuzz_in_ok D c -> 0 <= want ->
  exists c' off n, fuzz_take_m c want = (c', off, n) /\ fuzz_in_ok D c' /\
    0 <= n <= want /\ 0 <= off /\ off + n <= Z.of_nat (length D) /\ (n < want -> c' = FuzzIn (Z.of_nat (length D)) 0).
Proof.
  intros D c want (H0 & H1 & H2) Hw. unfold fuzz_take_m.
  eexists _, _, _. split; [reflexivity|].
  destruct (Z.ltb_spec want (fi_n c)); (split; [unfold fuzz_in_ok; cbn; lia|]); repeat split; try lia.
  intros Hn. f_equal; lia.
Qed.

Lemma length_sub_D : forall D off n, 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length D) ->
  length (sub D off (Z.to_nat n)) = Z.to_nat n.
Proof. intros D off n H0 H1 H2. apply length_sub; lia. Qed.

(* ---------------------------------------------------------------- check_latest_queue (fuzz_transport.c:804-819) *)

Lemma sub_firstn : forall B k m n, (m <= n)%nat -> firstn m (sub B k n) = sub B k m.
Proof. intros B k m n H. unfold sub. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma beq_bytes_refl : forall a, beq_bytes a a = true.
Proof. intros a. unfold beq_bytes. destruct (list_eq_dec Z.eq_dec (zs a) (zs a)); [reflexivity|congruence]. Qed.

(* D1's entry: the session's bytes over the command's length are the model's *)
Lemma d1_bytes_len : forall B i k, S_queue_bytes B i = Cmd_bytes B k -> 0 <= Cmd_len B k <= 24 ->
  sub B (A_S_queue_bytes i) (Z.to_nat (Cmd_len B k)) = sub B (A_Cmd_bytes k) (Z.to_nat (Cmd_len B k)).
Proof.
  intros B i k Hb Hl. unfold S_queue_bytes, Cmd_bytes in Hb.
  rewrite <- (sub_firstn B (A_S_queue_bytes i) _ 24) by lia. rewrite Hb. apply sub_firstn. lia.
Qed.

Lemma queue_loop_ok : forall ops B, agree_q ops B -> g_raw B = 0 ->
  forall fuel i, 0 <= i <= g_nq B -> (Z.to_nat (g_nq B - i) < fuel)%nat ->
  queue_loop fuel B i true = Some true.
Proof.
  intros ops B HQ Hr fuel. induction fuel as [|f IH]; intros i Hi Hf; [lia|].
  pose proof (d1_nq _ _ HQ Hr) as Hnq. pose proof (d3_ncmd _ _ HQ). pose proof (d3_ops _ _ HQ).
  cbn [queue_loop andb]. destruct (Z.ltb_spec i (g_nq B)) as [Hlt|Hge]; [|reflexivity].
  destruct (d1_entry _ _ HQ Hr i ltac:(lia)) as (Hk & Hst & Hby & Hlen & _ & _).
  destruct (Z.leb_spec CMDS_MAX i); [unfold CMDS_MAX, QUEUE_MAX in *; lia|].
  destruct (Z.leb_spec CMDS_MAX (Q_at B i)); [unfold CMDS_MAX, OPS_MAX in *; lia|].
  destruct (Z.leb_spec QUEUE_MAX i); [unfold QUEUE_MAX in *; lia|].
  destruct (d2_cmd _ _ HQ (Q_at B i) Hk ltac:(rewrite Hst; unfold PENDING; lia)) as (_ & _ & _ & Hl & _).
  rewrite Hlen, Z.eqb_refl, d1_bytes_len by (assumption || lia). rewrite beq_bytes_refl. cbn [andb].
  apply IH; lia.
Qed.

Lemma latest_queue_ok : forall ops B, agree_q ops B -> g_raw B = 0 -> check_latest_queue_m B = Some (B, tt).
Proof.
  intros ops B HQ Hr. unfold check_latest_queue_m. rewrite (d1_queued _ _ HQ Hr), Z.eqb_refl.
  pose proof (d1_nq _ _ HQ Hr). pose proof (u_at_nonneg B OFF_g_nq 4). fold (g_nq B) in *.
  rewrite (queue_loop_ok ops B HQ Hr) by (unfold QUEUE_MAX in *; lia). reflexivity.
Qed.
