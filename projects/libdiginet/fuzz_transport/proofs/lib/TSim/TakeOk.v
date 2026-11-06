(* The queue part of diginet_session_tick (diginet_session.c:458-471) and the harness checks it meets:
   take (DS:353-386, TSess0.take_m), the harness's io_send DATA path (fuzz_transport.c:858-862 the command count
   loop, TCb.cmds_loop; :626-644 check_latest_sent with q_remove :617-624) and settle's check_latest_drain
   (:785-802, TCb.drain_loop).
   The queue is a list of 32-byte entries (QueueFacts.sq); take is a mask over it (take_mask, true = taken):
   the body take builds is the in-order concatenation of the taken entries' bytes (P1-P4, T1), the queue it
   leaves is the entries not taken, in order (T1), the first ready entry is always taken (P5).
   No lemma here assumes agree: each takes explicit hypotheses (agree's D1, D2, D4 give them). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import QueueFacts SimLib.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- definitions *)

(* a queue entry's fields (TSess0: len at 24, display at 25) and the bytes take copies (c->bytes, c->len) *)
Definition e_len (e : list byte) : Z := cmd_len_of e.
Definition e_disp (e : list byte) : Z := cmd_display_of e.
Definition e_bytes (e : list byte) : list byte := firstn (Z.to_nat (e_len e)) e.

(* the elements whose flag is true, in order *)
Fixpoint pick {A} (m : list bool) (l : list A) : list A :=
  match m, l with
  | b :: m', x :: l' => if b then x :: pick m' l' else pick m' l'
  | _, _ => []
  end.
Definition unpick {A} (m : list bool) (l : list A) : list A := pick (map negb m) l.

(* take (DS:353-386) on the queue as a list of 32-byte entries; flags, true = taken *)
Fixpoint take_mask (maxc maxb allow taken len : Z) (body : list byte) (q : list (list byte)) : list bool :=
  match q with
  | [] => []
  | e :: q' =>
      let fits := (taken <? maxc) && (len + e_len e <=? maxb) && (negb (allow =? 0) || (e_disp e =? 0))
                  && (body_check (body ++ e_bytes e) =? 0) in
      let '(t1, l1, b1) := if fits then (taken + 1, len + e_len e, body ++ e_bytes e) else (taken, len, body) in
      fits :: (if (t1 =? maxc) || (l1 =? maxb) then repeat false (length q') else take_mask maxc maxb allow t1 l1 b1 q')
  end.

Definition take_res (maxc maxb allow : Z) (q : list (list byte)) : list byte * Z * Z * Z :=
  let T := pick (take_mask maxc maxb allow 0 0 [] q) q in
  (concat (map e_bytes T), Z.of_nat (length (concat (map e_bytes T))), fold_left Z.lor (map e_disp T) 0, Z.of_nat (length T)).

(* g_cmd[k]'s bytes over its length, what the harness compares a sent command with (FT:637) *)
Definition cmd_body (B : list byte) (k : Z) : list byte := sub B (A_Cmd_bytes k) (Z.to_nat (Cmd_len B k)).

(* a queued serial k: a PENDING command of the model with the harness's tag and k's 14 bits in bytes 0-2
   (FT:1089-1094; agree's d1_entry, d2_cmd) *)
Definition tagged_ok (B : list byte) (k : Z) : Prop :=
  0 <= k < g_ncmd B /\ g_ncmd B <= CMDS_MAX /\ Cmd_st B k = PENDING /\ 3 <= Cmd_len B k <= 24 /\
  at8 (Cmd_bytes B k) 0 = TAG /\ at8 (Cmd_bytes B k) 1 = Z.land k 127 /\ at8 (Cmd_bytes B k) 2 = Z.land (Z.shiftr k 7) 127.

(* ---------------------------------------------------------------- pick and unpick *)

Lemma pick_repeat_false : forall {A} n (l : list A), pick (repeat false n) l = [].
Proof. intros A n; induction n as [|n IH]; intros [|x l]; cbn; auto. Qed.

Lemma unpick_repeat_false : forall {A} (l : list A), unpick (repeat false (length l)) l = l.
Proof. intros A l; unfold unpick; induction l as [|x l IH]; cbn; [reflexivity|]. f_equal. exact IH. Qed.

Lemma pick_Forall2 : forall {A B} (R : A -> B -> Prop) (m : list bool) l1 l2,
  Forall2 R l1 l2 -> Forall2 R (pick m l1) (pick m l2).
Proof.
  intros A B R m l1 l2 H. revert m.
  induction H as [|x y l1 l2 Hxy H IH]; intros [|b m]; cbn.
  - constructor.
  - constructor.
  - constructor.
  - destruct b; [constructor; [exact Hxy | apply IH] | apply IH].
Qed.

Lemma unpick_Forall2 : forall {A B} (R : A -> B -> Prop) (m : list bool) l1 l2,
  Forall2 R l1 l2 -> Forall2 R (unpick m l1) (unpick m l2).
Proof. intros. unfold unpick. apply pick_Forall2. assumption. Qed.

Lemma pick_unpick_length : forall {A} (m : list bool) (l : list A),
  length m = length l -> (length (pick m l) + length (unpick m l))%nat = length l.
Proof.
  intros A m l; revert m. unfold unpick.
  induction l as [|x l IH]; intros [|b m] Hlen; cbn in *; try discriminate; [reflexivity|].
  assert (H : length m = length l) by lia.
  specialize (IH m H). destruct b; cbn; lia.
Qed.

Lemma pick_nil_unpick : forall {A} (m : list bool) (l : list A),
  length m = length l -> pick m l = [] -> unpick m l = l.
Proof.
  intros A m l; revert m; unfold unpick.
  induction l as [|x l IH]; intros [|b m] Hlen Hp; cbn in *; try discriminate; [reflexivity|].
  destruct b; cbn in *; [discriminate|].
  f_equal. apply IH; [lia | exact Hp].
Qed.

Lemma Forall_pick : forall {A} (P : A -> Prop) (m : list bool) l, Forall P l -> Forall P (pick m l).
Proof.
  intros A P m l H. revert m.
  induction H as [|x l Hx H IH]; intros [|b m]; cbn.
  - constructor.
  - constructor.
  - constructor.
  - destruct b; [constructor; [exact Hx | apply IH] | apply IH].
Qed.

Lemma in_pick : forall {A} (m : list bool) (l : list A) x, In x (pick m l) -> In x l.
Proof.
  intros A m l; revert m. induction l as [|y l IH]; intros [|b m] x Hx; cbn in Hx; try contradiction.
  destruct b; [destruct Hx as [<-|Hx]; [left; reflexivity | right; eapply IH; exact Hx] | right; eapply IH; exact Hx].
Qed.

Lemma in_unpick : forall {A} (m : list bool) (l : list A) x, In x (unpick m l) -> In x l.
Proof. intros A m l x. unfold unpick. apply in_pick. Qed.

(* ---------------------------------------------------------------- take_mask, one step *)

Definition fits_of (maxc maxb allow taken len : Z) (body e : list byte) : bool :=
  (taken <? maxc) && (len + e_len e <=? maxb) && (negb (allow =? 0) || (e_disp e =? 0))
  && (body_check (body ++ e_bytes e) =? 0).

Lemma take_mask_cons_t : forall maxc maxb allow taken len body e q,
  fits_of maxc maxb allow taken len body e = true ->
  take_mask maxc maxb allow taken len body (e :: q) =
  true :: (if (taken + 1 =? maxc) || (len + e_len e =? maxb) then repeat false (length q)
           else take_mask maxc maxb allow (taken + 1) (len + e_len e) (body ++ e_bytes e) q).
Proof. intros * H. unfold fits_of in H. cbn [take_mask]. rewrite H. reflexivity. Qed.

Lemma take_mask_cons_f : forall maxc maxb allow taken len body e q,
  fits_of maxc maxb allow taken len body e = false ->
  take_mask maxc maxb allow taken len body (e :: q) =
  false :: (if (taken =? maxc) || (len =? maxb) then repeat false (length q)
            else take_mask maxc maxb allow taken len body q).
Proof. intros * H. unfold fits_of in H. cbn [take_mask]. rewrite H. reflexivity. Qed.

Ltac split_if := match goal with |- context [if ?c then _ else _] => destruct c end.

Ltac take_step maxc maxb allow taken len body e F :=
  destruct (fits_of maxc maxb allow taken len body e) eqn:F;
  [rewrite (take_mask_cons_t maxc maxb allow taken len body e _ F)
  |rewrite (take_mask_cons_f maxc maxb allow taken len body e _ F)].

Lemma fits_of_true : forall maxc maxb allow taken len body e, fits_of maxc maxb allow taken len body e = true ->
  taken < maxc /\ len + e_len e <= maxb /\ (allow <> 0 \/ e_disp e = 0) /\ body_check (body ++ e_bytes e) = 0.
Proof.
  intros * H. unfold fits_of in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H4.
  apply orb_prop in H3. split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
  destruct H3 as [H3|H3]; [left; apply negb_true_iff, Z.eqb_neq in H3; exact H3 | right; apply Z.eqb_eq; exact H3].
Qed.

(* ---------------------------------------------------------------- P0 - P6 *)

(* P0 *)
Lemma take_mask_length : forall maxc maxb allow taken len body q,
  length (take_mask maxc maxb allow taken len body q) = length q.
Proof.
  intros maxc maxb allow taken len body q. revert taken len body.
  induction q as [|e q IH]; intros taken len body; [reflexivity|].
  take_step maxc maxb allow taken len body e F; cbn [length]; f_equal; split_if;
    rewrite ?repeat_length; auto.
Qed.

Lemma body_check_nil : body_check [] = 0.
Proof. reflexivity. Qed.

Lemma take_body_ok_gen : forall maxc maxb allow q taken len body,
  body_check body = 0 ->
  body_check (body ++ concat (map e_bytes (pick (take_mask maxc maxb allow taken len body q) q))) = 0.
Proof.
  intros maxc maxb allow q. induction q as [|e q IH]; intros taken len body Hb.
  - cbn [take_mask pick map concat]. rewrite app_nil_r. exact Hb.
  - take_step maxc maxb allow taken len body e F.
    + apply fits_of_true in F as (_ & _ & _ & Hb').
      cbn [pick map concat]. rewrite app_assoc. split_if.
      * rewrite pick_repeat_false. cbn [map concat]. rewrite app_nil_r. exact Hb'.
      * apply IH. exact Hb'.
    + cbn [pick]. split_if.
      * rewrite pick_repeat_false. cbn [map concat]. rewrite app_nil_r. exact Hb.
      * apply IH. exact Hb.
Qed.

(* P1 *)
Lemma take_body_ok : forall maxc maxb allow q,
  body_check (concat (map e_bytes (pick (take_mask maxc maxb allow 0 0 [] q) q))) = 0.
Proof.
  intros. pose proof (take_body_ok_gen maxc maxb allow q 0 0 [] body_check_nil) as H.
  cbn [app] in H. exact H.
Qed.

Lemma e_len_nonneg : forall e, 0 <= e_len e.
Proof. intros e. unfold e_len, cmd_len_of. exact (proj1 (u_at_range e 24 1)). Qed.

Lemma e_bytes_length : forall e, length e = 32%nat -> e_len e <= 24 -> Z.of_nat (length (e_bytes e)) = e_len e.
Proof.
  intros e Hl Hle. pose proof (e_len_nonneg e). unfold e_bytes. rewrite length_firstn, Hl. lia.
Qed.

Lemma concat_e_bytes_length : forall T, Forall (fun e => length e = 32%nat /\ e_len e <= 24) T ->
  Z.of_nat (length (concat (map e_bytes T))) = fold_right Z.add 0 (map e_len T).
Proof.
  induction T as [|e T IH]; intros H; [reflexivity|].
  apply Forall_cons_iff in H as [[Hl Hle] HT].
  cbn [map concat fold_right]. rewrite length_app, Nat2Z.inj_add, e_bytes_length by assumption.
  rewrite IH by exact HT. reflexivity.
Qed.

Lemma take_len_le_gen : forall maxc maxb allow q taken len body, len <= maxb ->
  len + fold_right Z.add 0 (map e_len (pick (take_mask maxc maxb allow taken len body q) q)) <= maxb.
Proof.
  intros maxc maxb allow q. induction q as [|e q IH]; intros taken len body Hl.
  - cbn. lia.
  - take_step maxc maxb allow taken len body e F.
    + apply fits_of_true in F as (_ & Hle & _ & _).
      cbn [pick map fold_right]. split_if.
      * rewrite pick_repeat_false. cbn. lia.
      * specialize (IH (taken + 1) (len + e_len e) (body ++ e_bytes e) Hle). lia.
    + cbn [pick]. split_if.
      * rewrite pick_repeat_false. cbn. lia.
      * apply IH. exact Hl.
Qed.

(* P2 *)
Lemma take_len_le : forall maxc maxb allow q, 0 <= maxb ->
  Forall (fun e => length e = 32%nat /\ e_len e <= 24) q ->
  Z.of_nat (length (concat (map e_bytes (pick (take_mask maxc maxb allow 0 0 [] q) q)))) =
    fold_right Z.add 0 (map e_len (pick (take_mask maxc maxb allow 0 0 [] q) q)) /\
  Z.of_nat (length (concat (map e_bytes (pick (take_mask maxc maxb allow 0 0 [] q) q)))) <= maxb.
Proof.
  intros maxc maxb allow q Hb Hq.
  rewrite concat_e_bytes_length by (apply Forall_pick; exact Hq).
  split; [reflexivity|]. pose proof (take_len_le_gen maxc maxb allow q 0 0 [] Hb). lia.
Qed.

Lemma take_n_le_gen : forall maxc maxb allow q taken len body, taken <= maxc ->
  taken + Z.of_nat (length (pick (take_mask maxc maxb allow taken len body q) q)) <= maxc.
Proof.
  intros maxc maxb allow q. induction q as [|e q IH]; intros taken len body Ht.
  - cbn. lia.
  - take_step maxc maxb allow taken len body e F.
    + apply fits_of_true in F as (Hlt & _ & _ & _).
      cbn [pick length]. split_if.
      * rewrite pick_repeat_false. cbn. lia.
      * specialize (IH (taken + 1) (len + e_len e) (body ++ e_bytes e) ltac:(lia)). lia.
    + cbn [pick]. split_if.
      * rewrite pick_repeat_false. cbn. lia.
      * apply IH. exact Ht.
Qed.

(* P3 *)
Lemma take_n_le : forall maxc maxb allow q, 0 <= maxc ->
  Z.of_nat (length (pick (take_mask maxc maxb allow 0 0 [] q) q)) <= maxc.
Proof. intros. pose proof (take_n_le_gen maxc maxb allow q 0 0 [] H). lia. Qed.

Lemma take_disp_gen : forall maxc maxb q taken len body,
  Forall (fun e => e_disp e = 0) (pick (take_mask maxc maxb 0 taken len body q) q).
Proof.
  intros maxc maxb q. induction q as [|e q IH]; intros taken len body.
  - constructor.
  - take_step maxc maxb 0 taken len body e F.
    + apply fits_of_true in F as (_ & _ & Hd & _).
      cbn [pick]. constructor; [destruct Hd as [Hd|Hd]; [exfalso; apply Hd; reflexivity | exact Hd]|].
      split_if; [rewrite pick_repeat_false; constructor | apply IH].
    + cbn [pick]. split_if; [rewrite pick_repeat_false; constructor | apply IH].
Qed.

Lemma fold_lor_zeros : forall l, Forall (fun x => x = 0) l -> fold_left Z.lor l 0 = 0.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  apply Forall_cons_iff in H as [-> H]. cbn [fold_left]. change (Z.lor 0 0) with 0. apply IH, H.
Qed.

(* P4 *)
Lemma take_disp : forall maxc maxb allow q, allow = 0 ->
  fold_left Z.lor (map e_disp (pick (take_mask maxc maxb allow 0 0 [] q) q)) 0 = 0.
Proof.
  intros maxc maxb allow q ->. apply fold_lor_zeros. apply Forall_map.
  apply take_disp_gen.
Qed.

Lemma fits_of_first : forall maxc maxb allow e, 1 <= maxc -> 24 <= maxb -> e_len e <= 24 ->
  body_check (e_bytes e) = 0 -> (allow <> 0 \/ e_disp e = 0) -> fits_of maxc maxb allow 0 0 [] e = true.
Proof.
  intros maxc maxb allow e Hc Hb Hl Hbc Hr. unfold fits_of. cbn [app]. rewrite Hbc, Z.eqb_refl.
  destruct (Z.ltb_spec 0 maxc); [|lia]. destruct (Z.leb_spec (0 + e_len e) maxb); [|lia]. cbn [andb].
  destruct Hr as [Hr|Hr]; [apply Z.eqb_neq in Hr; rewrite Hr; reflexivity | rewrite Hr, orb_true_r; reflexivity].
Qed.

(* P5: the first ready entry is taken, so something is *)
Lemma take_first : forall maxc maxb allow q, 1 <= maxc -> 24 <= maxb ->
  Forall (fun e => length e = 32%nat /\ 1 <= e_len e <= 24 /\ body_check (e_bytes e) = 0) q ->
  (exists e, In e q /\ (allow <> 0 \/ e_disp e = 0)) ->
  pick (take_mask maxc maxb allow 0 0 [] q) q <> [].
Proof.
  intros maxc maxb allow q Hc Hb. induction q as [|e q IH]; intros Hq [e0 [Hin Hr]]; [destruct Hin|].
  apply Forall_cons_iff in Hq as [(Hl & Hle & Hbc) Hq'].
  take_step maxc maxb allow 0 0 (@nil byte) e F.
  - cbn [pick]. discriminate.
  - cbn [pick]. destruct (Z.eqb_spec 0 maxc); [lia|]. destruct (Z.eqb_spec 0 maxb); [lia|]. cbn [orb].
    apply IH; [exact Hq'|]. destruct Hin as [He|Hin]; [|exists e0; split; assumption].
    subst e0. exfalso. rewrite (fits_of_first maxc maxb allow e Hc Hb ltac:(lia) Hbc Hr) in F. discriminate.
Qed.

(* P6 *)
Lemma take_none : forall maxc maxb allow q,
  pick (take_mask maxc maxb allow 0 0 [] q) q = [] -> unpick (take_mask maxc maxb allow 0 0 [] q) q = q.
Proof. intros. apply pick_nil_unpick; [apply take_mask_length | assumption]. Qed.

(* ---------------------------------------------------------------- T1: take_m on the world *)

Lemma pick_true : forall {A} (m : list bool) (x : A) l, pick (true :: m) (x :: l) = x :: pick m l.
Proof. reflexivity. Qed.
Lemma pick_false : forall {A} (m : list bool) (x : A) l, pick (false :: m) (x :: l) = pick m l.
Proof. reflexivity. Qed.
Lemma unpick_true : forall {A} (m : list bool) (x : A) l, unpick (true :: m) (x :: l) = unpick m l.
Proof. reflexivity. Qed.
Lemma unpick_false : forall {A} (m : list bool) (x : A) l, unpick (false :: m) (x :: l) = x :: unpick m l.
Proof. reflexivity. Qed.

(* i, i + 1, ..., i + k - 1 *)
Fixpoint zr (i : Z) (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => i :: zr (i + 1) k'
  end.

Lemma length_zr : forall k i, length (zr i k) = k.
Proof. induction k as [|k IH]; intros i; cbn [zr length]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma zr_zseq : forall n, zseq n = zr 0 n.
Proof.
  assert (G : forall n s, map Z.of_nat (seq s n) = zr (Z.of_nat s) n).
  { induction n as [|n IH]; intros s; [reflexivity|]. cbn [seq map zr]. rewrite IH.
    replace (Z.of_nat (S s)) with (Z.of_nat s + 1) by lia. reflexivity. }
  intros n. unfold zseq. exact (G n 0%nat).
Qed.

(* the queue array s->queue[0 .. 512): what take's loop writes *)
Definition Rq (a : Z) : Prop := A_S_queue_bytes 0 <= a < A_S_queue_bytes S_queue_N.
(* what take writes: the queue array and s->queued (DS:385) *)
Definition take_rs (a : Z) : Prop :=
  (A_S_queue_bytes 0 <= a < A_S_queue_bytes S_queue_N) \/ (A_S_queued <= a < A_S_queued + 4).

Lemma rq_getters : forall B B', wframe Rq B B' ->
  S_cfg_max_cmds B' = S_cfg_max_cmds B /\ S_cfg_max_body B' = S_cfg_max_body B /\ S_queued B' = S_queued B.
Proof.
  intros B B' H.
  assert (G : forall j n, 0 <= j -> (j + Z.of_nat n <= A_S_queue_bytes 0 \/ A_S_queue_bytes S_queue_N <= j) ->
              u_at B' j n = u_at B j n).
  { intros j n Hj Hd. apply (wframe_u_at Rq B B' j n H Hj). intros a Ha HR. unfold Rq in HR. lia. }
  unfold S_cfg_max_cmds, S_cfg_max_body, S_queued.
  split; [|split]; apply G; unfold A_S_cfg_max_cmds, A_S_cfg_max_body, A_S_queued, A_S_queue_bytes, S_queue_N, OFF_g_s; lia.
Qed.

Lemma sq_ent_length : forall B i, length B = WN -> 0 <= i < S_queue_N -> length (sq_ent B i) = 32%nat.
Proof.
  intros B i HB Hi. unfold sq_ent. apply length_sub; [unfold A_S_queue_bytes, OFF_g_s; lia|]. rewrite HB.
  unfold WN, W_LEN, A_S_queue_bytes, OFF_g_s, S_queue_N in *. lia.
Qed.

Lemma Rq_upd : forall Bc k v, length Bc = WN -> 0 <= k < S_queue_N -> length v = 32%nat ->
  wframe Rq Bc (upd Bc (A_S_queue_bytes k) v).
Proof.
  intros Bc k v HB Hk Hv. apply wframe_upd.
  - unfold A_S_queue_bytes, OFF_g_s. lia.
  - rewrite HB, Hv. unfold WN, W_LEN, A_S_queue_bytes, OFF_g_s, S_queue_N in *. lia.
  - intros a Ha. rewrite Hv in Ha. unfold Rq, A_S_queue_bytes, OFF_g_s, S_queue_N in *. lia.
Qed.

Lemma map_sq_succ : forall Bc kept, 0 <= kept ->
  map (sq_ent Bc) (zseq (Z.to_nat (kept + 1))) = map (sq_ent Bc) (zseq (Z.to_nat kept)) ++ [sq_ent Bc kept].
Proof.
  intros Bc kept H. replace (Z.to_nat (kept + 1)) with (S (Z.to_nat kept)) by lia.
  rewrite zseq_succ, map_app. cbn [map]. rewrite (Z2Nat.id kept H). reflexivity.
Qed.

Lemma map_sq_upd_prefix : forall Bc kept v, length Bc = WN -> 0 <= kept < S_queue_N -> length v = 32%nat ->
  map (sq_ent (upd Bc (A_S_queue_bytes kept) v)) (zseq (Z.to_nat (kept + 1))) =
    map (sq_ent Bc) (zseq (Z.to_nat kept)) ++ [v].
Proof.
  intros Bc kept v HB Hk Hv. rewrite (map_sq_succ (upd Bc (A_S_queue_bytes kept) v) kept ltac:(lia)). f_equal.
  - apply map_ext_in. intros x Hx. apply in_zseq in Hx.
    rewrite (sq_ent_upd Bc kept x v HB Hk ltac:(lia) Hv).
    destruct (Z.eqb_spec kept x); [lia | reflexivity].
  - rewrite (sq_ent_upd Bc kept kept v HB Hk Hk Hv).
    destruct (Z.eqb_spec kept kept); [reflexivity | lia].
Qed.

Lemma sql_e : forall Bc i e, 0 <= i -> sq_ent Bc i = e -> S_queue_len Bc i = e_len e.
Proof. intros Bc i e Hi He. rewrite (S_queue_len_ent Bc i Hi), He. unfold e_len. reflexivity. Qed.

Lemma sqd_e : forall Bc i e, 0 <= i -> sq_ent Bc i = e -> S_queue_display Bc i = e_disp e.
Proof. intros Bc i e Hi He. rewrite (S_queue_display_ent Bc i Hi), He. unfold e_disp. reflexivity. Qed.

Lemma sqb_e : forall Bc i e, sq_ent Bc i = e -> e_len e <= 24 ->
  sub Bc (A_S_queue_bytes i) (Z.to_nat (e_len e)) = e_bytes e.
Proof.
  intros Bc i e He H24. pose proof (e_len_nonneg e).
  transitivity (firstn (Z.to_nat (e_len e)) (sq_ent Bc i)).
  - unfold sq_ent. symmetry. apply sub_firstn. lia.
  - rewrite He. unfold e_bytes. reflexivity.
Qed.

(* DS:378-379, the tail copy after the break *)
Lemma take_tail_ok : forall B, length B = WN -> S_queued B <= S_queue_N ->
  forall fuel Bc kept j, 0 <= kept <= j -> j + Z.of_nat fuel = S_queued B ->
  wframe Rq B Bc -> (forall x, j <= x < S_queued B -> sq_ent Bc x = sq_ent B x) ->
  exists Bf, take_tail_m Bc kept j fuel = Some (Bf, kept + Z.of_nat fuel) /\ wframe Rq B Bf /\
    map (sq_ent Bf) (zseq (Z.to_nat (kept + Z.of_nat fuel))) =
      map (sq_ent Bc) (zseq (Z.to_nat kept)) ++ map (sq_ent B) (zr j fuel).
Proof.
  intros B HB Hn fuel. induction fuel as [|f IH]; intros Bc kept j Hk Hj Hfr Hs.
  - exists Bc. cbn [take_tail_m zr map]. change (Z.of_nat 0) with 0. rewrite (Z.add_0_r kept).
    rewrite (app_nil_r (map (sq_ent Bc) (zseq (Z.to_nat kept)))).
    split; [reflexivity|]. split; [exact Hfr | reflexivity].
  - assert (HBc : length Bc = WN) by (rewrite (proj1 Hfr); exact HB).
    cbn [take_tail_m].
    destruct (Z.leb_spec S_queue_N j) as [Hx|_]; [lia|].
    destruct (Z.leb_spec S_queue_N kept) as [Hx|_]; [lia|].
    cbn [orb].
    change (sub Bc (A_S_queue_bytes j) 32) with (sq_ent Bc j).
    rewrite (Hs j ltac:(lia)).
    assert (Hel : length (sq_ent B j) = 32%nat) by (apply sq_ent_length; [exact HB | lia]).
    assert (Hfr' : wframe Rq B (upd Bc (A_S_queue_bytes kept) (sq_ent B j)))
      by exact (wframe_trans _ _ _ _ Hfr (Rq_upd Bc kept _ HBc ltac:(lia) Hel)).
    assert (Hs' : forall x, j + 1 <= x < S_queued B ->
                  sq_ent (upd Bc (A_S_queue_bytes kept) (sq_ent B j)) x = sq_ent B x).
    { intros x Hx. rewrite (sq_ent_upd Bc kept x (sq_ent B j) HBc ltac:(lia) ltac:(lia) Hel).
      destruct (Z.eqb_spec kept x); [lia|]. apply Hs. lia. }
    destruct (IH (upd Bc (A_S_queue_bytes kept) (sq_ent B j)) (kept + 1) (j + 1) ltac:(lia) ltac:(lia) Hfr' Hs')
      as (Bf & Hrun & HfrF & Hmap).
    exists Bf. rewrite Hrun.
    replace (kept + Z.of_nat (S f)) with (kept + 1 + Z.of_nat f) by lia.
    split; [reflexivity|]. split; [exact HfrF|].
    rewrite Hmap, (map_sq_upd_prefix Bc kept (sq_ent B j) HBc ltac:(lia) Hel).
    cbn [zr map]. rewrite <- app_assoc. reflexivity.
Qed.

(* one turn of take's loop (DS:358-382) with the entry's fields read as e's *)
Lemma take_loop_step : forall Bc allow i taken kept len hd body f e maxc maxb,
  0 <= i < S_queue_N ->
  S_queue_len Bc i = e_len e -> S_queue_display Bc i = e_disp e ->
  sub Bc (A_S_queue_bytes i) (Z.to_nat (e_len e)) = e_bytes e -> sub Bc (A_S_queue_bytes i) 32 = e ->
  S_cfg_max_cmds Bc = maxc -> S_cfg_max_body Bc = maxb -> maxb <= DIGINET_MAX_BODY_LEN ->
  take_loop_m Bc allow i taken kept len hd body (S f) =
  if fits_of maxc maxb allow taken len body e then
    (if (taken + 1 =? maxc) || (len + e_len e =? maxb) then
       match take_tail_m Bc kept (i + 1) (Z.to_nat (S_queued Bc - (i + 1))) with
       | None => None
       | Some (B2, kept2) => Some (B2, (body ++ e_bytes e, len + e_len e, Z.lor hd (e_disp e), taken + 1, kept2))
       end
     else take_loop_m Bc allow (i + 1) (taken + 1) kept (len + e_len e) (Z.lor hd (e_disp e)) (body ++ e_bytes e) f)
  else
    let B1 := if kept =? i then Bc else upd Bc (A_S_queue_bytes kept) e in
    (if (taken =? S_cfg_max_cmds B1) || (len =? S_cfg_max_body B1) then
       match take_tail_m B1 (kept + 1) (i + 1) (Z.to_nat (S_queued B1 - (i + 1))) with
       | None => None
       | Some (B2, kept2) => Some (B2, (body, len, hd, taken, kept2))
       end
     else take_loop_m B1 allow (i + 1) taken (kept + 1) len hd body f).
Proof.
  intros Bc allow i taken kept len hd body f e maxc maxb Hi HL HD HBy HE Hc Hb Hmax.
  cbn [take_loop_m]. cbv zeta.
  destruct (Z.leb_spec S_queue_N i) as [Hx|_]; [lia|].
  rewrite HL. rewrite HD. rewrite HBy. rewrite HE. rewrite Hc. rewrite Hb.
  unfold fits_of, DIGINET_OK.
  destruct ((taken <? maxc) && (len + e_len e <=? maxb) && (negb (allow =? 0) || (e_disp e =? 0))) eqn:F0.
  - assert (Hl : len + e_len e <= maxb).
    { apply andb_prop in F0 as [F0 _]. apply andb_prop in F0 as [_ F0]. apply Z.leb_le. exact F0. }
    destruct (Z.ltb_spec DIGINET_MAX_BODY_LEN (len + e_len e)) as [Hx|_]; [lia|].
    cbn [andb].
    destruct (body_check (body ++ e_bytes e) =? 0); cbv beta iota zeta.
    + rewrite Hc. rewrite Hb. reflexivity.
    + reflexivity.
  - cbn [andb]. cbv beta iota zeta. reflexivity.
Qed.

(* what take's loop from i returns, for the entries rest (= s->queue[i ..)) and the mask M over them *)
Definition loop_post (B Bc : list byte) (kept len hd taken : Z) (body : list byte) (M : list bool)
    (rest : list (list byte)) (r : option (list byte * (list byte * Z * Z * Z * Z))) : Prop :=
  exists Bf b l h t kf, r = Some (Bf, (b, l, h, t, kf)) /\
    b = body ++ concat (map e_bytes (pick M rest)) /\
    l = len + fold_right Z.add 0 (map e_len (pick M rest)) /\
    h = fold_left Z.lor (map e_disp (pick M rest)) hd /\
    t = taken + Z.of_nat (length (pick M rest)) /\
    kf = kept + Z.of_nat (length (unpick M rest)) /\
    wframe Rq B Bf /\
    map (sq_ent Bf) (zseq (Z.to_nat kf)) = map (sq_ent Bc) (zseq (Z.to_nat kept)) ++ unpick M rest.

(* the invariant of take_loop_m: entries >= i untouched, entries [0, kept) the kept ones so far *)
Lemma take_loop_ok : forall B allow maxc maxb, length B = WN -> S_cfg_max_cmds B = maxc -> S_cfg_max_body B = maxb ->
  maxb <= DIGINET_MAX_BODY_LEN -> S_queued B <= S_queue_N ->
  (forall j, 0 <= j < S_queued B -> e_len (sq_ent B j) <= 24) ->
  forall fuel Bc i taken kept len hd body, 0 <= kept <= i -> i + Z.of_nat fuel = S_queued B ->
  wframe Rq B Bc -> (forall j, i <= j < S_queued B -> sq_ent Bc j = sq_ent B j) ->
  loop_post B Bc kept len hd taken body (take_mask maxc maxb allow taken len body (map (sq_ent B) (zr i fuel)))
    (map (sq_ent B) (zr i fuel)) (take_loop_m Bc allow i taken kept len hd body fuel).
Proof.
  intros B allow maxc maxb HB Hc Hb H1484 Hn H24 fuel.
  induction fuel as [|f IH]; intros Bc i taken kept len hd body Hk Hi Hfr Hs.
  - cbn [take_loop_m zr map take_mask]. unfold loop_post.
    exists Bc, body, len, hd, taken, kept. cbn [pick unpick map concat fold_right fold_left length].
    refine (conj eq_refl (conj _ (conj _ (conj eq_refl (conj _ (conj _ (conj Hfr _))))))).
    + symmetry. apply app_nil_r.
    + lia.
    + lia.
    + lia.
    + symmetry. apply app_nil_r.
  - assert (HBc : length Bc = WN) by (rewrite (proj1 Hfr); exact HB).
    assert (Hin : 0 <= i < S_queue_N) by lia.
    destruct (rq_getters B Bc Hfr) as (Hc' & Hb' & Hq').
    cbn [zr map].
    remember (sq_ent B i) as e eqn:Ee.
    assert (He : sq_ent Bc i = e) by (rewrite Ee; apply Hs; lia).
    assert (He24 : e_len e <= 24) by (rewrite Ee; apply H24; lia).
    assert (Hel : length e = 32%nat) by (rewrite Ee; apply sq_ent_length; [exact HB | exact Hin]).
    rewrite (take_loop_step Bc allow i taken kept len hd body f e maxc maxb Hin
               (sql_e Bc i e ltac:(lia) He) (sqd_e Bc i e ltac:(lia) He) (sqb_e Bc i e He He24) He
               (eq_trans Hc' Hc) (eq_trans Hb' Hb) H1484).
    destruct (fits_of maxc maxb allow taken len body e) eqn:F.
    + rewrite (take_mask_cons_t maxc maxb allow taken len body e _ F).
      destruct ((taken + 1 =? maxc) || (len + e_len e =? maxb)) eqn:C.
      * rewrite Hq'. replace (Z.to_nat (S_queued B - (i + 1))) with f by lia.
        destruct (take_tail_ok B HB Hn f Bc kept (i + 1) ltac:(lia) ltac:(lia) Hfr (fun x Hx => Hs x ltac:(lia)))
          as (Bf & Hrun & HfrF & Hmap).
        rewrite Hrun. unfold loop_post.
        exists Bf, (body ++ e_bytes e), (len + e_len e), (Z.lor hd (e_disp e)), (taken + 1), (kept + Z.of_nat f).
        rewrite pick_true. rewrite unpick_true. rewrite pick_repeat_false. rewrite unpick_repeat_false.
        split; [reflexivity|].
        split; [cbn [map concat]; rewrite (app_nil_r (e_bytes e)); reflexivity|].
        split; [cbn [map fold_right]; lia|].
        split; [cbn [map fold_left]; reflexivity|].
        split; [cbn [length]; lia|].
        split; [rewrite length_map, length_zr; reflexivity|].
        split; [exact HfrF|].
        exact Hmap.
      * pose proof (IH Bc (i + 1) (taken + 1) kept (len + e_len e) (Z.lor hd (e_disp e)) (body ++ e_bytes e)
                      ltac:(lia) ltac:(lia) Hfr (fun x Hx => Hs x ltac:(lia))) as IH'.
        unfold loop_post in IH' |- *.
        destruct IH' as (Bf & b & l & h & t & kf & Hr & Eb & El & Eh & Et & Ek & HfrF & Hmap).
        exists Bf, b, l, h, t, kf. rewrite pick_true. rewrite unpick_true.
        split; [exact Hr|].
        split; [rewrite Eb; cbn [map concat]; rewrite app_assoc; reflexivity|].
        split; [rewrite El; cbn [map fold_right]; lia|].
        split; [rewrite Eh; cbn [map fold_left]; reflexivity|].
        split; [rewrite Et; cbn [length]; lia|].
        split; [exact Ek|].
        split; [exact HfrF|].
        exact Hmap.
    + rewrite (take_mask_cons_f maxc maxb allow taken len body e _ F).
      cbv zeta.
      remember (if kept =? i then Bc else upd Bc (A_S_queue_bytes kept) e) as B1 eqn:EB1.
      assert (HB1 : wframe Rq B B1 /\ (forall x, i + 1 <= x < S_queued B -> sq_ent B1 x = sq_ent B x) /\
                    map (sq_ent B1) (zseq (Z.to_nat (kept + 1))) = map (sq_ent Bc) (zseq (Z.to_nat kept)) ++ [e]).
      { subst B1. destruct (Z.eqb_spec kept i) as [Eki|Hne]; cbv beta iota.
        - subst kept. split; [exact Hfr|]. split; [intros x Hx; apply Hs; lia|].
          rewrite (map_sq_succ Bc i ltac:(lia)). rewrite He. reflexivity.
        - split; [exact (wframe_trans _ _ _ _ Hfr (Rq_upd Bc kept e HBc ltac:(lia) Hel))|].
          split.
          + intros x Hx. rewrite (sq_ent_upd Bc kept x e HBc ltac:(lia) ltac:(lia) Hel).
            destruct (Z.eqb_spec kept x); [lia|]. apply Hs. lia.
          + exact (map_sq_upd_prefix Bc kept e HBc ltac:(lia) Hel). }
      destruct HB1 as (HB1fr & HB1s & HB1map).
      destruct (rq_getters B B1 HB1fr) as (Hc1 & Hb1 & Hq1).
      rewrite Hc1. rewrite Hb1. rewrite Hq1. rewrite Hc. rewrite Hb.
      destruct ((taken =? maxc) || (len =? maxb)) eqn:C.
      * replace (Z.to_nat (S_queued B - (i + 1))) with f by lia.
        destruct (take_tail_ok B HB Hn f B1 (kept + 1) (i + 1) ltac:(lia) ltac:(lia) HB1fr HB1s)
          as (Bf & Hrun & HfrF & Hmap).
        rewrite Hrun. unfold loop_post.
        exists Bf, body, len, hd, taken, (kept + 1 + Z.of_nat f).
        rewrite pick_false. rewrite unpick_false. rewrite pick_repeat_false. rewrite unpick_repeat_false.
        split; [reflexivity|].
        split; [cbn [map concat]; rewrite (app_nil_r body); reflexivity|].
        split; [cbn [map fold_right]; lia|].
        split; [cbn [map fold_left]; reflexivity|].
        split; [cbn [length]; lia|].
        split; [cbn [length]; rewrite length_map, length_zr; lia|].
        split; [exact HfrF|].
        rewrite Hmap. rewrite HB1map. rewrite <- app_assoc. reflexivity.
      * pose proof (IH B1 (i + 1) taken (kept + 1) len hd body ltac:(lia) ltac:(lia) HB1fr HB1s) as IH'.
        unfold loop_post in IH' |- *.
        destruct IH' as (Bf & b & l & h & t & kf & Hr & Eb & El & Eh & Et & Ek & HfrF & Hmap).
        exists Bf, b, l, h, t, kf. rewrite pick_false. rewrite unpick_false.
        split; [exact Hr|].
        split; [exact Eb|].
        split; [exact El|].
        split; [exact Eh|].
        split; [exact Et|].
        split; [rewrite Ek; cbn [length]; lia|].
        split; [exact HfrF|].
        rewrite Hmap. rewrite HB1map. rewrite <- app_assoc. reflexivity.
Qed.

(* T1: take (DS:353-386) is take_res on the queue; it leaves the entries not taken, in order *)
Lemma take_m_ok : forall B allow, length B = Z.to_nat W_LEN -> 0 <= S_queued B <= 512 -> S_cfg_max_body B <= 1484 ->
  Forall (fun e => e_len e <= 24) (sq B) ->
  let maxc := S_cfg_max_cmds B in let maxb := S_cfg_max_body B in
  exists B', take_m B allow = Some (B', take_res maxc maxb allow (sq B)) /\
    sq B' = unpick (take_mask maxc maxb allow 0 0 [] (sq B)) (sq B) /\
    S_queued B' = Z.of_nat (length (unpick (take_mask maxc maxb allow 0 0 [] (sq B)) (sq B))) /\
    wframe take_rs B B'.
Proof.
  intros B allow HB Hn Hmb H24. cbv zeta.
  assert (H24' : forall j, 0 <= j < S_queued B -> e_len (sq_ent B j) <= 24).
  { intros j Hj. rewrite Forall_forall in H24. apply H24. unfold sq. apply in_map. apply in_zseq. lia. }
  assert (Hq32 : Forall (fun e => length e = 32%nat /\ e_len e <= 24) (sq B)).
  { apply Forall_forall. intros e He. unfold sq in He. apply in_map_iff in He as [j [<- Hj]].
    apply in_zseq in Hj. split; [apply sq_ent_length; [exact HB | unfold S_queue_N; lia] | apply H24'; lia]. }
  assert (Hsq : sq B = map (sq_ent B) (zr 0 (Z.to_nat (S_queued B)))).
  { unfold sq. rewrite (zr_zseq (Z.to_nat (S_queued B))). reflexivity. }
  assert (Hls : length (sq B) = Z.to_nat (S_queued B)).
  { unfold sq. rewrite length_map. apply length_zseq. }
  pose proof (take_loop_ok B allow (S_cfg_max_cmds B) (S_cfg_max_body B) HB eq_refl eq_refl Hmb
               ltac:(unfold S_queue_N; lia) H24' (Z.to_nat (S_queued B)) B 0 0 0 0 0 []
               ltac:(lia) ltac:(lia) (wframe_refl Rq B) (fun j _ => eq_refl)) as HL.
  rewrite <- Hsq in HL.
  set (M := take_mask (S_cfg_max_cmds B) (S_cfg_max_body B) allow 0 0 [] (sq B)) in *.
  unfold loop_post in HL.
  destruct HL as (Bf & b & l & h & t & kf & Hr & Eb & El & Eh & Et & Ek & HfrF & Hmap).
  assert (HBf : length Bf = WN) by (rewrite (proj1 HfrF); exact HB).
  assert (Hkf : 0 <= kf <= 512).
  { pose proof (pick_unpick_length M (sq B) (take_mask_length _ _ _ _ _ _ _)) as Hpu. lia. }
  set (B' := set_S_queued Bf kf).
  assert (HqB' : S_queued B' = kf).
  { unfold B', S_queued, set_S_queued.
    refine (wr_u_upd_same_id Bf A_S_queued 4 kf A_S_queued 4 eq_refl eq_refl _ _ _).
    - unfold A_S_queued, OFF_g_s. lia.
    - rewrite HBf. unfold WN, W_LEN, A_S_queued, OFF_g_s. lia.
    - split; [lia|]. apply (Z.le_lt_trans _ 512); [lia | reflexivity]. }
  assert (Hent : forall x, 0 <= x < S_queue_N -> sq_ent B' x = sq_ent Bf x).
  { intros x Hx. unfold B', sq_ent, set_S_queued. apply sub_upd_out.
    - unfold A_S_queued, OFF_g_s. lia.
    - unfold A_S_queue_bytes, OFF_g_s. lia.
    - left. unfold A_S_queue_bytes, A_S_queued, OFF_g_s, S_queue_N in *. lia.
    - rewrite HBf, length_put. unfold WN, W_LEN, A_S_queued, OFF_g_s. lia. }
  assert (Eb' : b = concat (map e_bytes (pick M (sq B)))) by exact Eb.
  assert (El' : l = Z.of_nat (length (concat (map e_bytes (pick M (sq B)))))).
  { rewrite El. rewrite (concat_e_bytes_length (pick M (sq B)) (Forall_pick _ M _ Hq32)). apply Z.add_0_l. }
  assert (Et' : t = Z.of_nat (length (pick M (sq B)))) by (rewrite Et; apply Z.add_0_l).
  exists B'. split; [|split; [|split]].
  - unfold take_m. rewrite Hr. unfold take_res. fold M. cbv beta iota zeta.
    rewrite Eb'. rewrite El'. rewrite Eh. rewrite Et'. reflexivity.
  - unfold sq at 1. rewrite HqB'.
    rewrite (map_ext_in (sq_ent B') (sq_ent Bf) (zseq (Z.to_nat kf))).
    + rewrite Hmap. change (zseq (Z.to_nat 0)) with (@nil Z). cbn [map app]. reflexivity.
    + intros x Hx. apply in_zseq in Hx. apply Hent. unfold S_queue_N. lia.
  - rewrite HqB'. rewrite Ek. apply Z.add_0_l.
  - apply (wframe_trans take_rs B Bf B').
    + apply (wframe_weaken Rq take_rs B Bf); [|exact HfrF]. intros a Ha. left. exact Ha.
    + unfold B', set_S_queued. apply wframe_upd.
      * unfold A_S_queued, OFF_g_s. lia.
      * rewrite HBf, length_put. unfold WN, W_LEN, A_S_queued, OFF_g_s. lia.
      * intros a Ha. rewrite (length_put 4 kf) in Ha. right. lia.
Qed.

(* the views' lengths are the counters *)
Lemma hq_g_nq : forall B, g_nq B = Z.of_nat (length (hq B)).
Proof.
  intros B. unfold hq. rewrite length_map, length_zseq.
  rewrite (Z2Nat.id (g_nq B) (proj1 (u_at_range B OFF_g_nq 4))). reflexivity.
Qed.

Lemma sq_S_queued : forall B, S_queued B = Z.of_nat (length (sq B)).
Proof.
  intros B. unfold sq. rewrite length_map, length_zseq.
  rewrite (Z2Nat.id (S_queued B) (proj1 (u_at_range B A_S_queued 4))). reflexivity.
Qed.

(* ================================================================ T2, T3
   fuzz_transport.c:609-644 (tagged_of, q_remove, check_latest_sent: TCb.tagged_of_m, q_remove_m, latest_sent_loop,
   check_latest_sent_m) and :858-862 (io_send's command count loop, TCb.cmds_loop) on the body take builds: the
   in-order concatenation of the bytes of the taken serials Ts = pick m (hq B). Helpers are named ls_. *)

(* the addresses check_latest_sent writes: g_q, g_nq (q_remove) and the st cell of each sent command *)
Definition sent_rs (Ts : list Z) (a : Z) : Prop :=
  (OFF_g_q <= a < OFF_g_q + SZ_g_q) \/ (OFF_g_nq <= a < OFF_g_nq + SZ_g_nq) \/
  (exists k, In k Ts /\ A_Cmd_st k <= a < A_Cmd_st k + 4).

(* ---------------------------------------------------------------- numbers and lists *)

Lemma ls_p31 : 2 ^ 31 = 2147483648.
Proof. reflexivity. Qed.

Lemma ls_p32 : 2 ^ 32 = 4294967296.
Proof. reflexivity. Qed.

(* the serial tagged_of reads back from bytes 1-2 (FT:613) *)
Lemma ls_serial : forall k, 0 <= k < 16384 ->
  Z.lor (Z.land k 127) (Z.shiftl (Z.land (Z.shiftr k 7) 127) 7) = k.
Proof.
  intros k Hk.
  assert (E : forall x, Z.land x 127 = x mod 128).
  { intros x. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. }
  rewrite (E k), (E (Z.shiftr k 7)).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 7) with 128.
  rewrite (Z.mod_small (k / 128) 128) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (H0 : Z.land (k mod 128) (k / 128 * 128) = 0).
  { rewrite <- (E k). rewrite <- Z.land_assoc. rewrite (Z.land_comm 127 (k / 128 * 128)).
    rewrite (E (k / 128 * 128)). rewrite Z.mod_mul by lia. apply Z.land_0_r. }
  rewrite <- Z.lxor_lor by exact H0. rewrite <- Z.add_nocarry_lxor by exact H0.
  pose proof (Z.div_mod k 128 ltac:(lia)). lia.
Qed.

Lemma ls_len3 : forall {A} (a b c : list A),
  Z.of_nat (length (a ++ b ++ c)) = Z.of_nat (length a) + Z.of_nat (length b) + Z.of_nat (length c).
Proof. intros A a b c. rewrite !length_app. lia. Qed.

Lemma ls_len_pc : forall {A} (a b c : list A),
  Z.of_nat (length ((a ++ b) ++ c)) = Z.of_nat (length a) + Z.of_nat (length b) + Z.of_nat (length c).
Proof. intros A a b c. rewrite !length_app. lia. Qed.

Lemma ls_skipn_app : forall {A} (l1 l2 : list A), skipn (length l1) (l1 ++ l2) = l2.
Proof. intros A l1 l2. induction l1 as [|x l1 IH]; cbn [length skipn app]; [reflexivity | exact IH]. Qed.

Lemma ls_firstn_app : forall {A} (l1 l2 : list A) n, n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof.
  intros A l1 l2 n ->. induction l1 as [|x l1 IH]; cbn [length firstn app]; [reflexivity|].
  f_equal. exact IH.
Qed.

Lemma ls_nth_firstn : forall {A} (l : list A) m i d, (i < m)%nat -> nth i (firstn m l) d = nth i l d.
Proof.
  intros A l. induction l as [|x l IH]; intros [|m] [|i] d H; cbn [firstn nth]; try reflexivity;
    try (exfalso; lia).
  apply IH. lia.
Qed.

Lemma ls_at8_app : forall l1 l2 i, (i < length l1)%nat -> at8 (l1 ++ l2) i = at8 l1 i.
Proof. intros l1 l2 i H. unfold at8. rewrite List.app_nth1 by exact H. reflexivity. Qed.

(* BvBase exports stdpp, whose filter, NoDup and Forall_forall shadow Stdlib's: the helpers name Stdlib's *)
Lemma ls_filter_ext_in : forall {A} (f g : A -> bool) l, (forall x, In x l -> f x = g x) ->
  List.filter f l = List.filter g l.
Proof.
  intros A f g l H. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter].
  rewrite (H x (or_introl eq_refl)). rewrite IH; [reflexivity|].
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma ls_existsb_notin : forall x l, ~ In x l -> existsb (Z.eqb x) l = false.
Proof.
  intros x l Hx. destruct (existsb (Z.eqb x) l) eqn:E; [|reflexivity].
  apply List.existsb_exists in E as (y & Hy & Hxy). apply Z.eqb_eq in Hxy. subst y. exact (False_ind _ (Hx Hy)).
Qed.

Lemma ls_filter_nil : forall l, List.filter (fun x => negb (existsb (Z.eqb x) [])) l = l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter existsb negb]. f_equal. exact IH. Qed.

Lemma ls_filter_step : forall k L l,
  List.filter (fun x => negb (existsb (Z.eqb x) L)) (List.filter (fun x => negb (x =? k)) l) =
  List.filter (fun x => negb (existsb (Z.eqb x) (k :: L))) l.
Proof.
  intros k L l. induction l as [|x l IH]; [reflexivity|].
  cbn [List.filter existsb]. destruct (x =? k); cbn [negb orb List.filter].
  - exact IH.
  - destruct (existsb (Z.eqb x) L); cbn [negb]; [exact IH | f_equal; exact IH].
Qed.

Lemma ls_NoDup_pick : forall {A} (m : list bool) (l : list A), List.NoDup l -> List.NoDup (pick m l).
Proof.
  intros A m l. revert m. induction l as [|x l IH]; intros [|b m] H; cbn [pick]; try constructor.
  apply List.NoDup_cons_iff in H as [Hx H]. destruct b; cbv beta iota.
  - constructor; [|apply IH; exact H]. intro Hin. apply Hx. eapply in_pick. exact Hin.
  - apply IH. exact H.
Qed.

(* q_remove's queue is the queue less the serials removed; with no repeated serial, that is unpick *)
Lemma ls_filter_unpick : forall (m : list bool) (l : list Z), List.NoDup l -> length m = length l ->
  List.filter (fun x => negb (existsb (Z.eqb x) (pick m l))) l = unpick m l.
Proof.
  intros m l. revert m. induction l as [|x l IH]; intros [|b m] Hnd Hlen; cbn [length] in Hlen; try discriminate.
  - reflexivity.
  - apply List.NoDup_cons_iff in Hnd as [Hx Hnd]. injection Hlen as Hlen.
    unfold unpick. cbn [pick map]. fold (unpick m l).
    destruct b; cbn [negb List.filter].
    + cbn [existsb]. rewrite (Z.eqb_refl x). cbn [orb negb].
      rewrite <- (IH m Hnd Hlen). apply ls_filter_ext_in. intros y Hy. cbn [existsb].
      destruct (Z.eqb_spec y x) as [->|_]; [exact (False_ind _ (Hx Hy)) | reflexivity].
    + rewrite (ls_existsb_notin x (pick m l)) by (intro Hin; apply Hx; eapply in_pick; exact Hin).
      cbn [negb]. f_equal. apply IH; assumption.
Qed.

(* ---------------------------------------------------------------- 4-byte writes *)

Lemma ls_u_at_put4 : forall B k v, 0 <= k -> (Z.to_nat k + 4 <= length B)%nat -> 0 <= v < 2 ^ 32 ->
  u_at (upd B k (put 4 v)) k 4 = v.
Proof.
  intros B k v Hk Hl Hv. rewrite (u_at_upd_put B k 4 v Hk ltac:(lia)).
  change (8 * Z.of_nat 4) with 32. apply Z.mod_small. exact Hv.
Qed.

Lemma ls_Q_at_set : forall B i j v, length B = WN -> 0 <= i < CMDS_MAX -> 0 <= j -> 0 <= v < 2 ^ 32 ->
  Q_at (set_Q_at B i v) j = if i =? j then v else Q_at B j.
Proof.
  intros B i j v HB Hi Hj Hv. unfold Q_at, set_Q_at.
  assert (Hl : (Z.to_nat (OFF_g_q + 4 * i) + 4 <= length B)%nat)
    by (rewrite HB; unfold WN, W_LEN, OFF_g_q, CMDS_MAX in *; lia).
  destruct (Z.eqb_spec i j) as [<-|Hne]; cbv beta iota.
  - apply ls_u_at_put4; [unfold OFF_g_q; lia | exact Hl | exact Hv].
  - apply u_at_upd_out; first [unfold OFF_g_q; lia | rewrite length_put; unfold OFF_g_q in *; lia].
Qed.

(* ---------------------------------------------------------------- q_remove (FT:617-624) *)

Lemma ls_qrl : forall B s nq fuel Bc i k,
  length B = WN -> nq <= QUEUE_MAX -> 0 <= k <= i -> i <= nq -> (Z.to_nat (nq - i) < fuel)%nat ->
  wframe (fun a => OFF_g_q <= a < OFF_g_q + SZ_g_q) B Bc ->
  (forall j, i <= j -> Q_at Bc j = Q_at B j) ->
  map (Q_at Bc) (zseq (Z.to_nat k)) = List.filter (fun x => negb (x =? s)) (map (Q_at B) (zseq (Z.to_nat i))) ->
  exists B1 k1, q_remove_loop fuel Bc s nq i k = Some (B1, k1) /\ 0 <= k1 <= nq /\
    wframe (fun a => OFF_g_q <= a < OFF_g_q + SZ_g_q) B B1 /\
    map (Q_at B1) (zseq (Z.to_nat k1)) = List.filter (fun x => negb (x =? s)) (map (Q_at B) (zseq (Z.to_nat nq))).
Proof.
  intros B s nq fuel. induction fuel as [|f IH]; intros Bc i k HB Hnq Hk Hi Hf Hw HQ Hmap; [lia|].
  cbn [q_remove_loop].
  destruct (Z.ltb_spec i nq) as [Hlt|Hge].
  2: { cbv beta iota. assert (Heq : i = nq) by lia. subst nq.
       exists Bc, k. split; [reflexivity|]. split; [lia|]. split; [exact Hw | exact Hmap]. }
  destruct (Z.leb_spec CMDS_MAX i) as [Hc|_]; [unfold CMDS_MAX, QUEUE_MAX in *; lia|].
  assert (HBc : length Bc = WN) by (destruct Hw as [L _]; rewrite L; exact HB).
  assert (Hzi : zseq (Z.to_nat (i + 1)) = zseq (Z.to_nat i) ++ [i]).
  { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite zseq_succ. rewrite Z2Nat.id by lia.
    reflexivity. }
  destruct (Z.eqb_spec (Q_at Bc i) s) as [Heq|Hne]; cbv beta iota.
  - assert (HQ' : forall j, i + 1 <= j -> Q_at Bc j = Q_at B j) by (intros j Hj; apply HQ; lia).
    assert (Hm' : map (Q_at Bc) (zseq (Z.to_nat k)) =
                  List.filter (fun x => negb (x =? s)) (map (Q_at B) (zseq (Z.to_nat (i + 1))))).
    { rewrite Hzi. rewrite List.map_app. rewrite List.filter_app. rewrite <- Hmap. cbn [map List.filter].
      rewrite <- (HQ i (Z.le_refl i)). rewrite Heq. rewrite (Z.eqb_refl s). cbn [negb].
      rewrite List.app_nil_r. reflexivity. }
    destruct (IH Bc (i + 1) k HB Hnq ltac:(lia) ltac:(lia) ltac:(lia) Hw HQ' Hm')
      as (B1 & k1 & E & Hk1 & Hw1 & Hm1).
    exists B1, k1. exact (conj E (conj Hk1 (conj Hw1 Hm1))).
  - assert (Hk' : 0 <= k < CMDS_MAX) by (unfold CMDS_MAX, QUEUE_MAX in *; lia).
    pose proof (u_at_range Bc (OFF_g_q + 4 * i) 4) as Hv1. change (8 * Z.of_nat 4) with 32 in Hv1.
    assert (Hv : 0 <= Q_at Bc i < 2 ^ 32) by (unfold Q_at; lia).
    assert (Hset : forall j, 0 <= j ->
      Q_at (set_Q_at Bc k (Q_at Bc i)) j = if k =? j then Q_at Bc i else Q_at Bc j)
      by (intros j Hj; apply ls_Q_at_set; [exact HBc | exact Hk' | exact Hj | exact Hv]).
    assert (Hw' : wframe (fun a => OFF_g_q <= a < OFF_g_q + SZ_g_q) B (set_Q_at Bc k (Q_at Bc i))).
    { apply (wframe_trans _ B Bc); [exact Hw|]. unfold set_Q_at.
      apply wframe_upd;
        [unfold OFF_g_q; lia | rewrite length_put, HBc; unfold WN, W_LEN, OFF_g_q, CMDS_MAX in *; lia |].
      intros a Ha. rewrite length_put in Ha. cbv beta. unfold SZ_g_q, CMDS_MAX in *. lia. }
    assert (HQ' : forall j, i + 1 <= j -> Q_at (set_Q_at Bc k (Q_at Bc i)) j = Q_at B j).
    { intros j Hj. rewrite (Hset j) by lia. destruct (Z.eqb_spec k j) as [Hx|_]; [lia|]. cbv beta iota.
      apply HQ. lia. }
    assert (Hzk : zseq (Z.to_nat (k + 1)) = zseq (Z.to_nat k) ++ [k]).
    { replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia. rewrite zseq_succ. rewrite Z2Nat.id by lia.
      reflexivity. }
    assert (Hm' : map (Q_at (set_Q_at Bc k (Q_at Bc i))) (zseq (Z.to_nat (k + 1))) =
                  List.filter (fun x => negb (x =? s)) (map (Q_at B) (zseq (Z.to_nat (i + 1))))).
    { rewrite Hzk. rewrite Hzi. rewrite List.map_app. rewrite List.map_app. rewrite List.filter_app.
      rewrite <- Hmap. cbn [map List.filter]. rewrite <- (HQ i (Z.le_refl i)).
      destruct (Z.eqb_spec (Q_at Bc i) s) as [Hx|_]; [exact (False_ind _ (Hne Hx))|]. cbn [negb].
      f_equal.
      - apply List.map_ext_in. intros j Hj. apply in_zseq in Hj. rewrite (Hset j) by lia.
        destruct (Z.eqb_spec k j) as [Hx|_]; [lia|]. cbv beta iota. reflexivity.
      - rewrite (Hset k) by lia. rewrite (Z.eqb_refl k). cbv beta iota. reflexivity. }
    destruct (IH (set_Q_at Bc k (Q_at Bc i)) (i + 1) (k + 1) HB Hnq ltac:(lia) ltac:(lia) ltac:(lia) Hw' HQ' Hm')
      as (B1 & k1 & E & Hk1 & Hw1 & Hm1).
    exists B1, k1. exact (conj E (conj Hk1 (conj Hw1 Hm1))).
Qed.

Lemma ls_q_remove : forall B s, length B = WN -> 0 <= g_nq B <= QUEUE_MAX ->
  exists B', q_remove_m B s = Some (B', tt) /\ hq B' = List.filter (fun x => negb (x =? s)) (hq B) /\
    wframe (fun a => (OFF_g_q <= a < OFF_g_q + SZ_g_q) \/ (OFF_g_nq <= a < OFF_g_nq + SZ_g_nq)) B B' /\
    g_nq B' <= g_nq B.
Proof.
  intros B s HB Hnq. unfold q_remove_m.
  destruct (ls_qrl B s (g_nq B) (S (Z.to_nat CMDS_MAX)) B 0 0 HB ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold CMDS_MAX, QUEUE_MAX in *; lia) (wframe_refl _ _) (fun j _ => eq_refl) eq_refl)
    as (B1 & k1 & E & Hk1 & Hw1 & Hm1).
  rewrite E. cbv beta iota.
  assert (HB1 : length B1 = WN) by (destruct Hw1 as [L _]; rewrite L; exact HB).
  assert (Hg : g_nq (set_g_nq B1 k1) = k1).
  { unfold g_nq, set_g_nq.
    apply ls_u_at_put4; [unfold OFF_g_nq; lia | rewrite HB1; unfold WN, W_LEN, OFF_g_nq; lia |].
    rewrite ls_p32. unfold QUEUE_MAX in *. lia. }
  assert (Hw2 : wframe (fun a => OFF_g_nq <= a < OFF_g_nq + 4) B1 (set_g_nq B1 k1)).
  { unfold set_g_nq.
    apply wframe_upd; [unfold OFF_g_nq; lia | rewrite length_put, HB1; unfold WN, W_LEN, OFF_g_nq; lia |].
    intros a Ha. rewrite length_put in Ha. cbv beta. lia. }
  exists (set_g_nq B1 k1). split; [reflexivity|]. split.
  { unfold hq at 1. rewrite Hg.
    transitivity (map (Q_at B1) (zseq (Z.to_nat k1))).
    - apply List.map_ext_in. intros j Hj. apply in_zseq in Hj. unfold Q_at.
      eapply wframe_u_at; [exact Hw2 | unfold OFF_g_q; lia |].
      intros a Ha Hc. cbv beta in Hc. unfold OFF_g_q, OFF_g_nq, QUEUE_MAX in *. lia.
    - unfold hq. exact Hm1. }
  split.
  { apply (wframe_trans _ B B1 (set_g_nq B1 k1)).
    - eapply wframe_weaken; [|exact Hw1]. intros a Ha. cbv beta in *. left. exact Ha.
    - eapply wframe_weaken; [|exact Hw2]. intros a Ha. cbv beta in *. right. unfold SZ_g_nq. exact Ha. }
  rewrite Hg. lia.
Qed.

Lemma q_remove_ok : forall B s, length B = Z.to_nat W_LEN -> 0 <= g_nq B <= QUEUE_MAX ->
  exists B', q_remove_m B s = Some (B', tt) /\ hq B' = List.filter (fun x => negb (x =? s)) (hq B) /\
    wframe (fun a => (OFF_g_q <= a < OFF_g_q + SZ_g_q) \/ (OFF_g_nq <= a < OFF_g_nq + SZ_g_nq)) B B'.
Proof.
  intros B s HB Hnq. destruct (ls_q_remove B s HB Hnq) as (B' & E & Hq & Hw & _).
  exists B'. split; [exact E|]. split; [|exact Hw].
  exact Hq.
Qed.

(* ---------------------------------------------------------------- what a sent_rs frame keeps *)

Lemma ls_rs_mono : forall L1 L2 a, (forall x, In x L1 -> In x L2) -> sent_rs L1 a -> sent_rs L2 a.
Proof.
  intros L1 L2 a Hi [H|[H|(k & Hk & H)]]; unfold sent_rs.
  - left. exact H.
  - right. left. exact H.
  - right. right. exists k. split; [apply Hi; exact Hk | exact H].
Qed.

(* bytes 4-39 of g_cmd[k]: key, display, bytes, len *)
Lemma ls_rs_cmd : forall L k a, 0 <= k < CMDS_MAX -> A_Cmd_st k + 4 <= a < A_Cmd_st k + 40 -> ~ sent_rs L a.
Proof.
  intros L k a Hk Ha [H|[H|(k' & _ & H)]];
    unfold OFF_g_q, SZ_g_q, OFF_g_nq, SZ_g_nq, A_Cmd_st, OFF_g_cmd, CMDS_MAX in *; lia.
Qed.

Lemma ls_rs_st : forall L k a, 0 <= k < CMDS_MAX -> ~ In k L -> A_Cmd_st k <= a < A_Cmd_st k + 4 -> ~ sent_rs L a.
Proof.
  intros L k a Hk Hn Ha [H|[H|(k' & Hin & H)]].
  - unfold OFF_g_q, SZ_g_q, A_Cmd_st, OFF_g_cmd, CMDS_MAX in *. lia.
  - unfold OFF_g_nq, SZ_g_nq, A_Cmd_st, OFF_g_cmd, CMDS_MAX in *. lia.
  - assert (Hkk : k' = k) by (unfold A_Cmd_st, OFF_g_cmd in *; lia). subst k'. exact (Hn Hin).
Qed.

Lemma ls_wf_ncmd : forall L B B', wframe (sent_rs L) B B' -> g_ncmd B' = g_ncmd B.
Proof.
  intros L B B' Hw. unfold g_ncmd. eapply wframe_u_at; [exact Hw | unfold OFF_g_ncmd; lia |].
  intros a Ha [H|[H|(k & _ & H)]];
    unfold OFF_g_ncmd, OFF_g_q, SZ_g_q, OFF_g_nq, SZ_g_nq, A_Cmd_st, OFF_g_cmd in *; lia.
Qed.

Lemma ls_wf_len : forall L B B' k, wframe (sent_rs L) B B' -> 0 <= k < CMDS_MAX -> Cmd_len B' k = Cmd_len B k.
Proof.
  intros L B B' k Hw Hk. unfold Cmd_len. eapply wframe_u_at; [exact Hw | unfold A_Cmd_len, OFF_g_cmd; lia |].
  intros a Ha. apply (ls_rs_cmd L k a Hk). unfold A_Cmd_len, A_Cmd_st in *. lia.
Qed.

Lemma ls_wf_bytes : forall L B B' k, wframe (sent_rs L) B B' -> 0 <= k < CMDS_MAX -> Cmd_bytes B' k = Cmd_bytes B k.
Proof.
  intros L B B' k Hw Hk. unfold Cmd_bytes. eapply wframe_sub; [exact Hw | unfold A_Cmd_bytes, OFF_g_cmd; lia |].
  intros a Ha. apply (ls_rs_cmd L k a Hk). unfold A_Cmd_bytes, A_Cmd_st in *. lia.
Qed.

Lemma ls_wf_disp : forall L B B' k, wframe (sent_rs L) B B' -> 0 <= k < CMDS_MAX ->
  Cmd_display B' k = Cmd_display B k.
Proof.
  intros L B B' k Hw Hk. unfold Cmd_display.
  eapply wframe_s32_at; [exact Hw | unfold A_Cmd_display, OFF_g_cmd; lia |].
  intros a Ha. apply (ls_rs_cmd L k a Hk). unfold A_Cmd_display, A_Cmd_st in *. lia.
Qed.

Lemma ls_wf_st : forall L B B' k, wframe (sent_rs L) B B' -> 0 <= k < CMDS_MAX -> ~ In k L ->
  Cmd_st B' k = Cmd_st B k.
Proof.
  intros L B B' k Hw Hk Hn. unfold Cmd_st. eapply wframe_s32_at; [exact Hw | unfold A_Cmd_st, OFF_g_cmd; lia |].
  intros a Ha. exact (ls_rs_st L k a Hk Hn Ha).
Qed.

Lemma ls_wf_body : forall L B B' k, wframe (sent_rs L) B B' -> 0 <= k < CMDS_MAX -> 0 <= Cmd_len B k <= 24 ->
  cmd_body B' k = cmd_body B k.
Proof.
  intros L B B' k Hw Hk Hl. unfold cmd_body. rewrite (ls_wf_len L B B' k Hw Hk).
  eapply wframe_sub; [exact Hw | unfold A_Cmd_bytes, OFF_g_cmd; lia |].
  intros a Ha. apply (ls_rs_cmd L k a Hk). unfold A_Cmd_bytes, A_Cmd_st in *. lia.
Qed.

Lemma ls_wf_tagged : forall L B B' k, wframe (sent_rs L) B B' -> ~ In k L -> tagged_ok B k -> tagged_ok B' k.
Proof.
  intros L B B' k Hw Hn (Hk & Hnc & Hst & Hl & H0 & H1 & H2).
  assert (Hk' : 0 <= k < CMDS_MAX) by lia.
  unfold tagged_ok. rewrite (ls_wf_ncmd L B B' Hw). rewrite (ls_wf_st L B B' k Hw Hk' Hn).
  rewrite (ls_wf_len L B B' k Hw Hk'). rewrite (ls_wf_bytes L B B' k Hw Hk').
  exact (conj Hk (conj Hnc (conj Hst (conj Hl (conj H0 (conj H1 H2)))))).
Qed.

(* hq reads only addresses from g_q on *)
Lemma ls_hq_frame : forall (R : Z -> Prop) B B', wframe R B B' -> (forall a, OFF_g_q <= a -> ~ R a) -> hq B' = hq B.
Proof.
  intros R B B' Hw HR. unfold hq.
  assert (Hn : g_nq B' = g_nq B).
  { unfold g_nq. eapply wframe_u_at; [exact Hw | unfold OFF_g_nq; lia |].
    intros a Ha. apply HR. unfold OFF_g_nq, OFF_g_q in *. lia. }
  rewrite Hn. apply map_ext_in. intros j Hj. apply in_zseq in Hj. unfold Q_at.
  eapply wframe_u_at; [exact Hw | unfold OFF_g_q; lia |]. intros a Ha. apply HR. lia.
Qed.

(* t->st = SENT (FT:639) *)
Lemma ls_st_set : forall Bc k, length Bc = WN -> 0 <= k < CMDS_MAX ->
  length (set_Cmd_st Bc k SENT) = WN /\ Cmd_st (set_Cmd_st Bc k SENT) k = SENT /\
  wframe (sent_rs [k]) Bc (set_Cmd_st Bc k SENT) /\ hq (set_Cmd_st Bc k SENT) = hq Bc /\
  g_nq (set_Cmd_st Bc k SENT) = g_nq Bc.
Proof.
  intros Bc k HB Hk.
  assert (H0 : 0 <= A_Cmd_st k) by (unfold A_Cmd_st, OFF_g_cmd; lia).
  assert (Hl : (Z.to_nat (A_Cmd_st k) + 4 <= length Bc)%nat)
    by (rewrite HB; unfold WN, W_LEN, A_Cmd_st, OFF_g_cmd, CMDS_MAX in *; lia).
  assert (Hw : wframe (fun a => A_Cmd_st k <= a < A_Cmd_st k + 4) Bc (set_Cmd_st Bc k SENT)).
  { unfold set_Cmd_st. apply wframe_upd; [exact H0 | rewrite length_put; exact Hl |].
    intros a Ha. rewrite length_put in Ha. cbv beta. lia. }
  split; [destruct Hw as [L _]; rewrite L; exact HB|].
  split.
  { unfold Cmd_st, set_Cmd_st. apply s32_at_upd_same; [exact H0 | lia | unfold SENT; rewrite ls_p31; lia]. }
  split.
  { apply (wframe_weaken (fun a => A_Cmd_st k <= a < A_Cmd_st k + 4)); [|exact Hw].
    intros a Ha. cbv beta in Ha. unfold sent_rs. right. right. exists k. split; [left; reflexivity | exact Ha]. }
  split.
  { apply (ls_hq_frame _ _ _ Hw). intros a Ha Hc. cbv beta in Hc.
    unfold A_Cmd_st, OFF_g_cmd, OFF_g_q, CMDS_MAX in *. lia. }
  unfold g_nq. eapply wframe_u_at; [exact Hw | unfold OFF_g_nq; lia |].
  intros a Ha Hc. cbv beta in Hc. unfold A_Cmd_st, OFF_g_cmd, OFF_g_nq, CMDS_MAX in *. lia.
Qed.

(* ---------------------------------------------------------------- a queued command's bytes *)

Lemma ls_body_length : forall B k, length B = WN -> 0 <= k < CMDS_MAX -> 0 <= Cmd_len B k <= 24 ->
  length (cmd_body B k) = Z.to_nat (Cmd_len B k).
Proof.
  intros B k HB Hk Hl. unfold cmd_body.
  apply length_sub; [unfold A_Cmd_bytes, OFF_g_cmd in *; lia |].
  rewrite HB. unfold WN, W_LEN, A_Cmd_bytes, OFF_g_cmd, CMDS_MAX in *. lia.
Qed.

Lemma ls_body_firstn : forall B k, 0 <= Cmd_len B k <= 24 ->
  cmd_body B k = firstn (Z.to_nat (Cmd_len B k)) (Cmd_bytes B k).
Proof. intros B k Hl. unfold cmd_body, Cmd_bytes. symmetry. apply sub_firstn. lia. Qed.

Lemma ls_at8_body : forall B k i, 0 <= Cmd_len B k <= 24 -> (i < Z.to_nat (Cmd_len B k))%nat ->
  at8 (cmd_body B k) i = at8 (Cmd_bytes B k) i.
Proof.
  intros B k i Hl Hi. rewrite (ls_body_firstn B k Hl). unfold at8.
  rewrite (ls_nth_firstn (Cmd_bytes B k) (Z.to_nat (Cmd_len B k)) i (b8 0) Hi). reflexivity.
Qed.

(* tagged_of (FT:609-615) on bytes with the tag and a serial below g_ncmd *)
Lemma ls_tagged_of_gen : forall B b n, 3 <= n -> (3 <= length b)%nat -> at8 b 0 = TAG ->
  0 <= Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7) < g_ncmd B -> g_ncmd B <= CMDS_MAX ->
  tagged_of_m B b n = Some (B, Some (Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7))).
Proof.
  intros B b n Hn Hb H0 Hs Hc. unfold tagged_of_m. cbv zeta.
  destruct (Z.ltb_spec n 3) as [Hx|_]; [lia|].
  destruct (Nat.ltb_spec (length b) 1) as [Hx|_]; [lia|].
  rewrite H0. rewrite (Z.eqb_refl TAG). cbn [negb].
  destruct (Nat.ltb_spec (length b) 3) as [Hx|_]; [lia|].
  destruct (Z.ltb_spec (Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7)) (g_ncmd B)) as [_|Hx]; [|lia].
  destruct (Z.leb_spec CMDS_MAX (Z.lor (at8 b 1) (Z.shiftl (at8 b 2) 7))) as [Hx|_]; [lia|].
  cbv beta iota. reflexivity.
Qed.

Lemma ls_tagged_of : forall B k R n, length B = WN -> tagged_ok B k -> Cmd_len B k <= n ->
  tagged_of_m B (cmd_body B k ++ R) n = Some (B, Some k).
Proof.
  intros B k R n HB Htk Hn. pose proof Htk as (Hk & Hnc & _ & Hl & H0 & H1 & H2).
  assert (Hk' : 0 <= k < CMDS_MAX) by lia.
  pose proof (ls_body_length B k HB Hk' ltac:(lia)) as Hlen.
  assert (Hb : forall i, (i < 3)%nat -> at8 (cmd_body B k ++ R) i = at8 (Cmd_bytes B k) i).
  { intros i Hi. rewrite (ls_at8_app (cmd_body B k) R i) by lia. apply ls_at8_body; lia. }
  assert (Hs : Z.lor (at8 (cmd_body B k ++ R) 1) (Z.shiftl (at8 (cmd_body B k ++ R) 2) 7) = k).
  { rewrite (Hb 1%nat) by lia. rewrite (Hb 2%nat) by lia. rewrite H1. rewrite H2.
    apply ls_serial. unfold CMDS_MAX in Hk'. lia. }
  pose proof (ls_tagged_of_gen B (cmd_body B k ++ R) n) as G.
  rewrite Hs in G. apply G.
  - lia.
  - rewrite length_app. lia.
  - rewrite (Hb 0%nat) by lia. exact H0.
  - lia.
  - exact Hnc.
Qed.

Lemma ls_body_concat_length : forall B L, length B = WN -> Forall (tagged_ok B) L ->
  (length L <= length (concat (map (cmd_body B) L)))%nat.
Proof.
  intros B L HB H. induction H as [|k L Hk H IH]; [cbn [length map concat]; lia|].
  cbn [map concat length]. rewrite length_app.
  destruct Hk as (Hk & Hnc & _ & Hl & _).
  pose proof (ls_body_length B k HB ltac:(lia) ltac:(lia)). lia.
Qed.

(* ---------------------------------------------------------------- check_latest_sent (FT:626-644) *)

Lemma ls_loop : forall L fuel Bc pre disp body,
  length Bc = WN -> 0 <= g_nq Bc <= QUEUE_MAX -> List.NoDup L -> Forall (tagged_ok Bc) L ->
  body = pre ++ concat (map (cmd_body Bc) L) -> (length L < fuel)%nat ->
  exists Bf, latest_sent_loop fuel Bc body (Z.of_nat (length body)) (Z.of_nat (length pre)) disp =
      Some (Bf, fold_left Z.lor (map (Cmd_display Bc) L) disp) /\
    hq Bf = List.filter (fun x => negb (existsb (Z.eqb x) L)) (hq Bc) /\
    (forall k, 0 <= k < CMDS_MAX -> Cmd_st Bf k = if existsb (Z.eqb k) L then SENT else Cmd_st Bc k) /\
    wframe (sent_rs L) Bc Bf.
Proof.
  induction L as [|k L IH]; intros fuel Bc pre disp body HB Hnq Hnd Hall Hbody Hf.
  - destruct fuel as [|f]; [lia|].
    cbn [map concat] in Hbody. rewrite List.app_nil_r in Hbody. subst body.
    exists Bc. cbn [latest_sent_loop]. rewrite (Z.ltb_irrefl (Z.of_nat (length pre))). cbn [fold_left map].
    split; [reflexivity|]. split; [symmetry; apply ls_filter_nil|].
    split; [intros k0 _; cbn [existsb]; reflexivity | apply wframe_refl].
  - destruct fuel as [|f]; [lia|].
    apply List.NoDup_cons_iff in Hnd as [Hnin Hnd].
    apply Forall_cons_iff in Hall as [Htk Hall].
    pose proof Hall as HallL. rewrite List.Forall_forall in HallL.
    pose proof Htk as (Hk & Hnc & Hst & Hl & _ & _ & _).
    assert (Hk' : 0 <= k < CMDS_MAX) by lia.
    pose proof (ls_body_length Bc k HB Hk' ltac:(lia)) as Hlen.
    cbn [map concat] in Hbody.
    assert (Hbl : Z.of_nat (length body) =
                  Z.of_nat (length pre) + Cmd_len Bc k + Z.of_nat (length (concat (map (cmd_body Bc) L)))).
    { rewrite Hbody. rewrite ls_len3. lia. }
    cbn [latest_sent_loop].
    destruct (Z.ltb_spec (Z.of_nat (length pre)) (Z.of_nat (length body))) as [_|Hge]; [|lia].
    assert (Hrest : skipn (Z.to_nat (Z.of_nat (length pre))) body = cmd_body Bc k ++ concat (map (cmd_body Bc) L)).
    { rewrite Nat2Z.id. rewrite Hbody. apply ls_skipn_app. }
    rewrite Hrest.
    rewrite (ls_tagged_of Bc k (concat (map (cmd_body Bc) L)) _ HB Htk) by lia.
    cbv beta iota zeta.
    destruct (Z.eqb_spec (Cmd_st Bc k) PENDING) as [_|Hx]; [|exact (False_ind _ (Hx Hst))].
    destruct (Z.ltb_spec (Z.of_nat (length body) - Z.of_nat (length pre)) (Cmd_len Bc k)) as [Hc|_]; [lia|].
    rewrite (ls_firstn_app (cmd_body Bc k)) by lia.
    change (sub Bc (A_Cmd_bytes k) (Z.to_nat (Cmd_len Bc k))) with (cmd_body Bc k).
    rewrite beq_bytes_refl. cbn [negb orb].
    destruct (ls_st_set Bc k HB Hk') as (HB1 & Hst1 & Hw1 & Hq1 & Hg1).
    destruct (ls_q_remove (set_Cmd_st Bc k SENT) k HB1 ltac:(rewrite Hg1; exact Hnq)) as (B2 & EQ & Hq2 & Hw2 & Hn2).
    rewrite EQ. cbv beta iota.
    assert (Hw12 : wframe (sent_rs [k]) Bc B2).
    { apply (wframe_trans _ Bc (set_Cmd_st Bc k SENT) B2); [exact Hw1|].
      eapply wframe_weaken; [|exact Hw2]. intros a Ha. cbv beta in Ha. unfold sent_rs.
      destruct Ha as [Ha|Ha]; [left; exact Ha | right; left; exact Ha]. }
    assert (HB2 : length B2 = WN) by (destruct Hw12 as [L2 _]; rewrite L2; exact HB).
    assert (Hnq2 : 0 <= g_nq B2 <= QUEUE_MAX).
    { pose proof (u_at_range B2 OFF_g_nq 4) as Hr. change (8 * Z.of_nat 4) with 32 in Hr.
      fold (g_nq B2) in Hr. lia. }
    assert (Hin : forall k', In k' L -> ~ In k' [k]).
    { intros k' Hk1 [Heq|[]]. subst k'. exact (Hnin Hk1). }
    assert (HrL : forall k', In k' L -> 0 <= k' < CMDS_MAX /\ 0 <= Cmd_len Bc k' <= 24).
    { intros k' Hk1. destruct (HallL k' Hk1) as (Ha & Hb & _ & Hc & _). lia. }
    assert (Hall2 : Forall (tagged_ok B2) L).
    { apply List.Forall_forall. intros k' Hk1. apply (ls_wf_tagged [k] Bc B2 k' Hw12 (Hin k' Hk1)).
      exact (HallL k' Hk1). }
    assert (Hm : map (cmd_body Bc) L = map (cmd_body B2) L).
    { apply List.map_ext_in. intros k' Hk1. destruct (HrL k' Hk1) as [Ha Hb].
      symmetry. exact (ls_wf_body [k] Bc B2 k' Hw12 Ha Hb). }
    assert (Hbody2 : body = (pre ++ cmd_body Bc k) ++ concat (map (cmd_body B2) L)).
    { rewrite Hbody. rewrite <- (List.app_assoc pre (cmd_body Bc k)). rewrite Hm. reflexivity. }
    assert (Hpos : Z.of_nat (length pre) + Cmd_len Bc k = Z.of_nat (length (pre ++ cmd_body Bc k)))
      by (rewrite length_app; lia).
    rewrite Hpos.
    destruct (IH f B2 (pre ++ cmd_body Bc k) (Z.lor disp (Cmd_display B2 k)) body HB2 Hnq2 Hnd Hall2 Hbody2
      ltac:(cbn [length] in Hf; lia)) as (Bf & E & Hhq & Hstf & Hwf).
    exists Bf. split.
    { rewrite E. cbn [map fold_left]. rewrite (ls_wf_disp [k] Bc B2 k Hw12 Hk').
      rewrite (List.map_ext_in (Cmd_display B2) (Cmd_display Bc) L); [reflexivity|].
      intros k' Hk1. exact (ls_wf_disp [k] Bc B2 k' Hw12 (proj1 (HrL k' Hk1))). }
    split. { rewrite Hhq. rewrite Hq2. rewrite Hq1. apply ls_filter_step. }
    split.
    { intros k0 Hk0. rewrite (Hstf k0 Hk0). cbn [existsb].
      destruct (existsb (Z.eqb k0) L).
      - rewrite orb_true_r. cbv beta iota. reflexivity.
      - rewrite orb_false_r. cbv beta iota.
        destruct (Z.eqb_spec k0 k) as [->|Hne]; cbv beta iota.
        + transitivity (Cmd_st (set_Cmd_st Bc k SENT) k); [|exact Hst1].
          unfold Cmd_st. eapply wframe_s32_at; [exact Hw2 | unfold A_Cmd_st, OFF_g_cmd; lia |].
          intros a Ha Hc. cbv beta in Hc.
          unfold A_Cmd_st, OFF_g_cmd, OFF_g_q, SZ_g_q, OFF_g_nq, SZ_g_nq, CMDS_MAX in *. lia.
        + apply (ls_wf_st [k] Bc B2 k0 Hw12 Hk0). intros [Heq|[]]. apply Hne. symmetry. exact Heq. }
    apply (wframe_trans _ Bc B2 Bf).
    + eapply wframe_weaken; [|exact Hw12]. intros a Ha. apply (ls_rs_mono [k]); [|exact Ha].
      intros x [<-|[]]. left. reflexivity.
    + eapply wframe_weaken; [|exact Hwf]. intros a Ha. apply (ls_rs_mono L); [|exact Ha].
      intros x Hx. right. exact Hx.
Qed.

Lemma latest_sent_ok : forall B m, length B = Z.to_nat W_LEN -> 0 <= g_nq B <= QUEUE_MAX ->
  length m = length (hq B) -> List.NoDup (hq B) -> Forall (tagged_ok B) (hq B) ->
  let Ts := pick m (hq B) in
  let body := concat (map (cmd_body B) Ts) in
  exists B', check_latest_sent_m B body (Z.of_nat (length body)) = Some (B', fold_left Z.lor (map (Cmd_display B) Ts) 0) /\
    hq B' = unpick m (hq B) /\
    (forall k, 0 <= k < CMDS_MAX -> Cmd_st B' k = if existsb (Z.eqb k) Ts then SENT else Cmd_st B k) /\
    wframe (sent_rs Ts) B B'.
Proof.
  intros B m HB Hnq Hm Hnd Hall Ts body.
  assert (HTs : Ts = pick m (hq B)) by reflexivity.
  assert (Hbd : body = concat (map (cmd_body B) Ts)) by reflexivity.
  clearbody body. clearbody Ts.
  pose proof Hnd as HndL.
  assert (HndT : List.NoDup Ts) by (rewrite HTs; exact (ls_NoDup_pick m (hq B) HndL)).
  assert (HallT : Forall (tagged_ok B) Ts) by (rewrite HTs; exact (Forall_pick (tagged_ok B) m (hq B) Hall)).
  pose proof (ls_body_concat_length B Ts HB HallT) as Hbl. rewrite <- Hbd in Hbl.
  assert (Hb0 : body = [] ++ concat (map (cmd_body B) Ts)) by (rewrite Hbd; symmetry; apply List.app_nil_l).
  destruct (ls_loop Ts (S (Z.to_nat (Z.of_nat (length body)))) B [] 0 body HB Hnq HndT HallT Hb0
    ltac:(rewrite Nat2Z.id; lia)) as (Bf & E & Hhq & Hst & Hw).
  change (Z.of_nat (length (@nil byte))) with 0 in E.
  exists Bf. split; [unfold check_latest_sent_m; exact E|].
  split; [|split; [exact Hst | exact Hw]].
  rewrite Hhq. rewrite HTs. exact (ls_filter_unpick m (hq B) HndL Hm).
Qed.

(* with g_nq B' (hq_g_nq) *)
Lemma latest_sent_nq : forall B m, length B = Z.to_nat W_LEN -> 0 <= g_nq B <= QUEUE_MAX ->
  length m = length (hq B) -> List.NoDup (hq B) -> Forall (tagged_ok B) (hq B) ->
  let Ts := pick m (hq B) in
  let body := concat (map (cmd_body B) Ts) in
  exists B', check_latest_sent_m B body (Z.of_nat (length body)) = Some (B', fold_left Z.lor (map (Cmd_display B) Ts) 0) /\
    hq B' = unpick m (hq B) /\ g_nq B' = Z.of_nat (length (unpick m (hq B))) /\
    (forall k, 0 <= k < CMDS_MAX -> Cmd_st B' k = if existsb (Z.eqb k) Ts then SENT else Cmd_st B k) /\
    wframe (sent_rs Ts) B B'.
Proof.
  intros B m HB Hnq Hm Hnd Hall Ts body.
  destruct (latest_sent_ok B m HB Hnq Hm Hnd Hall) as (B' & E & Hq & Hst & Hw).
  exists B'. split; [exact E|]. split; [exact Hq|]. split; [|split; [exact Hst | exact Hw]].
  rewrite (hq_g_nq B'). rewrite Hq. reflexivity.
Qed.

(* ---------------------------------------------------------------- the command count loop (FT:858-862) *)

Lemma ls_cmds : forall B L, length B = WN -> Forall (tagged_ok B) L ->
  forall fuel pre tl cmds, (length L < fuel)%nat -> 0 <= cmds -> cmds + Z.of_nat (length L) < 2 ^ 32 ->
  cmds_loop fuel B (pre ++ concat (map (cmd_body B) L) ++ tl) (Z.of_nat (length (pre ++ concat (map (cmd_body B) L))))
    (Z.of_nat (length pre)) cmds = Some (cmds + Z.of_nat (length L)).
Proof.
  intros B L HB HL. induction HL as [|k L Htk HL IH]; intros fuel pre tl cmds Hf Hc Hb.
  - destruct fuel as [|f]; [lia|].
    cbn [cmds_loop map concat]. rewrite (List.app_nil_r pre). rewrite (Z.ltb_irrefl (Z.of_nat (length pre))).
    cbn [length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - destruct fuel as [|f]; [lia|].
    pose proof Htk as (Hk & Hnc & _ & Hl & _).
    assert (Hk' : 0 <= k < CMDS_MAX) by lia.
    pose proof (ls_body_length B k HB Hk' ltac:(lia)) as Hlen.
    cbn [map concat].
    rewrite (List.app_assoc pre (cmd_body B k) (concat (map (cmd_body B) L))).
    rewrite <- (List.app_assoc (cmd_body B k) (concat (map (cmd_body B) L)) tl).
    rewrite (List.app_assoc pre (cmd_body B k) (concat (map (cmd_body B) L) ++ tl)).
    assert (Hbl : Z.of_nat (length ((pre ++ cmd_body B k) ++ concat (map (cmd_body B) L))) =
                  Z.of_nat (length pre) + Cmd_len B k + Z.of_nat (length (concat (map (cmd_body B) L)))).
    { rewrite ls_len_pc. lia. }
    cbn [cmds_loop].
    destruct (Z.ltb_spec (Z.of_nat (length pre))
      (Z.of_nat (length ((pre ++ cmd_body B k) ++ concat (map (cmd_body B) L))))) as [_|Hge]; [|lia].
    assert (Hs : skipn (Z.to_nat (Z.of_nat (length pre))) ((pre ++ cmd_body B k) ++ concat (map (cmd_body B) L) ++ tl)
                 = cmd_body B k ++ concat (map (cmd_body B) L) ++ tl).
    { rewrite Nat2Z.id. rewrite <- (List.app_assoc pre (cmd_body B k)). apply ls_skipn_app. }
    rewrite Hs.
    rewrite (ls_tagged_of B k (concat (map (cmd_body B) L) ++ tl) _ HB Htk) by lia.
    cbv beta iota zeta.
    destruct (Z.eqb_spec (Cmd_len B k) 0) as [Hz|_]; [lia|].
    unfold u32. rewrite (Z.mod_small (cmds + 1) (2 ^ 32)) by (cbn [length] in Hb; lia).
    assert (Hpos : Z.of_nat (length pre) + Cmd_len B k = Z.of_nat (length (pre ++ cmd_body B k)))
      by (rewrite length_app; lia).
    rewrite Hpos.
    rewrite (IH f (pre ++ cmd_body B k) tl (cmds + 1)) by (cbn [length] in *; lia).
    cbn [length]. f_equal. lia.
Qed.

Lemma cmds_loop_ok : forall B m, length B = Z.to_nat W_LEN -> 0 <= g_nq B <= QUEUE_MAX ->
  length m = length (hq B) -> List.NoDup (hq B) -> Forall (tagged_ok B) (hq B) ->
  let Ts := pick m (hq B) in
  let body := concat (map (cmd_body B) Ts) in
  forall tl, cmds_loop (S (Z.to_nat (Z.of_nat (length body)))) B (body ++ tl) (Z.of_nat (length body)) 0 0 = Some (Z.of_nat (length Ts)).
Proof.
  intros B m HB Hnq Hm Hnd Hall Ts body tl.
  assert (HTs : Ts = pick m (hq B)) by reflexivity.
  assert (Hbd : body = concat (map (cmd_body B) Ts)) by reflexivity.
  clearbody body. clearbody Ts.
  assert (HallT : Forall (tagged_ok B) Ts) by (rewrite HTs; exact (Forall_pick (tagged_ok B) m (hq B) Hall)).
  pose proof (ls_body_concat_length B Ts HB HallT) as Hbl. rewrite <- Hbd in Hbl.
  pose proof (pick_unpick_length m (hq B) Hm) as Hpl. rewrite <- HTs in Hpl.
  assert (Hhq : length (hq B) = Z.to_nat (g_nq B)).
  { unfold hq. rewrite length_map. rewrite length_zseq. reflexivity. }
  pose proof (ls_cmds B Ts HB HallT (S (Z.to_nat (Z.of_nat (length body)))) [] tl 0) as H.
  rewrite <- Hbd in H. rewrite List.app_nil_l in H. rewrite List.app_nil_l in H.
  change (Z.of_nat (length (@nil byte))) with 0 in H. rewrite Z.add_0_l in H.
  apply H.
  - rewrite Nat2Z.id. lia.
  - lia.
  - rewrite ls_p32. unfold QUEUE_MAX in Hnq. lia.
Qed.
