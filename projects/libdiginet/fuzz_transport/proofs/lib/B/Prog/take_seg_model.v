(* take_seg_model: the facts of the model of take (lib/TModel/TSess0.v take_m, take_loop_m, take_tail_m) that the
   image-B machine walk lib/B/Prog/take_cgW.v reads off it. Nothing here mentions a machine state, a memory or the
   ASan runtime: every lemma is about the world byte list of lib/TModel/TWorld.v (image A's walk reads the same
   lemmas, lib/A/Prog/take_seg_model.v).

   The invariant of the loop (:358-382) is `taken + kept = i`: every turn raises exactly one of the two counters,
   and the tail (:378-380) raises kept once per turn. With the fuel `s->queued - i` that gives
   `takenF + keptF = S_queued B` at the end, hence both counters are bounded by s->queued, which is itself at most
   512 whenever the model answers Some (a turn at an index >= 512 is None). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TSess0 TTake.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnLib.
Import ListNotations.
Open Scope Z_scope.

(* The world's length: the hypothesis every lemma below carries. *)
Definition tkm_wf (B : list byte) : Prop := Z.of_nat (length B) = W_LEN.

(* The layout constants, unfolded for lia. *)
Ltac tkm_lia :=
  unfold tkm_wf, A_S_queue_bytes, A_S_queue_len, A_S_queue_display, A_S_queued, A_S_cfg_max_cmds,
    A_S_cfg_max_body, OFF_g_fail_next, OFF_g_s, SZ_g_s, S_queue_N, W_LEN in *; lia.

Lemma tkm_u_at_1 : forall B k, 0 <= u_at B k 1 < 256.
Proof. intros B k. exact (u_at_range B k 1). Qed.

Lemma tkm_u_at_4 : forall B k, 0 <= u_at B k 4 < 2 ^ 32.
Proof. intros B k. exact (u_at_range B k 4). Qed.

Lemma tkm_q_ranges : forall B i, 0 <= S_queue_len B i < 256 /\ 0 <= S_queue_display B i < 256.
Proof. intros B i. unfold S_queue_len, S_queue_display. split; apply tkm_u_at_1. Qed.

Lemma tkm_queued_range : forall B, 0 <= S_queued B < 2 ^ 32.
Proof. intros B. unfold S_queued. apply tkm_u_at_4. Qed.

(* ---- a write of one queue entry leaves every other field the walk reads alone ---- *)

Lemma tkm_upd_q_wf : forall (B v : list byte) q, tkm_wf B -> 0 <= q < S_queue_N -> length v = 32%nat ->
  tkm_wf (upd B (A_S_queue_bytes q) v).
Proof.
  intros B v q HB Hq Lv. unfold tkm_wf in *.
  rewrite length_upd by tkm_lia. exact HB.
Qed.

Lemma tkm_upd_q_fields : forall (B v : list byte) q, tkm_wf B -> 0 <= q < S_queue_N -> length v = 32%nat ->
  S_queued (upd B (A_S_queue_bytes q) v) = S_queued B /\
  g_fail_next (upd B (A_S_queue_bytes q) v) = g_fail_next B /\
  S_cfg_max_cmds (upd B (A_S_queue_bytes q) v) = S_cfg_max_cmds B /\
  S_cfg_max_body (upd B (A_S_queue_bytes q) v) = S_cfg_max_body B.
Proof.
  intros B v q HB Hq Lv. unfold S_queued, g_fail_next, S_cfg_max_cmds, S_cfg_max_body.
  rewrite !u_at_upd_out by tkm_lia. repeat split; reflexivity.
Qed.

Lemma tkm_upd_q_other : forall (B v : list byte) q i, tkm_wf B -> 0 <= q < S_queue_N -> 0 <= i < S_queue_N ->
  q <> i -> length v = 32%nat ->
  sub (upd B (A_S_queue_bytes q) v) (A_S_queue_bytes i) 32 = sub B (A_S_queue_bytes i) 32 /\
  S_queue_len (upd B (A_S_queue_bytes q) v) i = S_queue_len B i /\
  S_queue_display (upd B (A_S_queue_bytes q) v) i = S_queue_display B i.
Proof.
  intros B v q i HB Hq Hi Hne Lv. unfold S_queue_len, S_queue_display.
  rewrite sub_upd_out, !u_at_upd_out by tkm_lia. repeat split; reflexivity.
Qed.

(* The bytes the copy of :365 moves are a prefix of the entry's 32 bytes (the copy reads c->bytes, the entry's
   first 24 bytes, and c->len is at most 24). *)
Lemma tkm_sub_prefix : forall (B : list byte) i (n : nat), tkm_wf B -> 0 <= i < S_queue_N -> (n <= 32)%nat ->
  sub B (A_S_queue_bytes i) n = firstn n (sub B (A_S_queue_bytes i) 32).
Proof.
  intros B i n _ _ Hn. unfold sub. rewrite firstn_firstn. f_equal. lia.
Qed.

(* A queue entry lies inside g_s's payload. *)
Lemma tkm_entry_in_g_s : forall i, 0 <= i < S_queue_N ->
  OFF_g_s <= A_S_queue_bytes i /\ A_S_queue_bytes i + 32 <= OFF_g_s + SZ_g_s.
Proof. intros i Hi. tkm_lia. Qed.

(* ---- the tail loop (:378-380) ---- *)

Lemma tkm_tail_facts : forall (n : nat) B kept j B2 kept2,
  tkm_wf B -> 0 <= kept -> 0 <= j ->
  take_tail_m B kept j n = Some (B2, kept2) ->
  tkm_wf B2 /\ kept2 = kept + Z.of_nat n /\
  S_queued B2 = S_queued B /\ g_fail_next B2 = g_fail_next B /\
  S_cfg_max_cmds B2 = S_cfg_max_cmds B /\ S_cfg_max_body B2 = S_cfg_max_body B /\
  ((0 < n)%nat -> j + Z.of_nat n <= S_queue_N /\ kept + Z.of_nat n <= S_queue_N).
Proof.
  induction n as [|n IH]; intros B kept j B2 kept2 HB Hk Hj H.
  - cbn [take_tail_m] in H. injection H as <- <-.
    split; [exact HB|]. split; [lia|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros Hc. lia.
  - rewrite tk_tail_S in H.
    destruct ((S_queue_N <=? j) || (S_queue_N <=? kept)) eqn:Ec; [discriminate H|].
    apply orb_false_iff in Ec. destruct Ec as [Ej Ek]. apply Z.leb_gt in Ej, Ek.
    assert (L : length (sub B (A_S_queue_bytes j) 32) = 32%nat) by (apply length_sub; tkm_lia).
    pose proof (tkm_upd_q_wf B (sub B (A_S_queue_bytes j) 32) kept HB ltac:(lia) L) as W1.
    destruct (tkm_upd_q_fields B (sub B (A_S_queue_bytes j) 32) kept HB ltac:(lia) L) as (F1 & F2 & F3 & F4).
    destruct (IH (upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes j) 32)) (kept + 1) (j + 1) B2 kept2
                W1 ltac:(lia) ltac:(lia) H) as (W2 & K2 & G1 & G2 & G3 & G4 & R).
    split; [exact W2|]. split; [lia|].
    split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros _. destruct n as [|n'].
    + lia.
    + destruct (R ltac:(lia)) as [R1 R2]. lia.
Qed.

(* The world after a turn that keeps the command at i (:373-374): the entry copied down to kept. *)
Definition tkm_keep (B : list byte) (kept i : Z) : list byte :=
  if kept =? i then B else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32).

Lemma tkm_keep_facts : forall B kept i, tkm_wf B -> 0 <= kept <= i -> i < S_queue_N ->
  tkm_wf (tkm_keep B kept i) /\ S_queued (tkm_keep B kept i) = S_queued B /\
  g_fail_next (tkm_keep B kept i) = g_fail_next B /\
  S_cfg_max_cmds (tkm_keep B kept i) = S_cfg_max_cmds B /\
  S_cfg_max_body (tkm_keep B kept i) = S_cfg_max_body B.
Proof.
  intros B kept i HB Hk Hi. unfold tkm_keep. destruct (kept =? i); cbv iota.
  - split; [exact HB|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - assert (L : length (sub B (A_S_queue_bytes i) 32) = 32%nat) by (apply length_sub; tkm_lia).
    split; [apply tkm_upd_q_wf; [exact HB | lia | exact L]|].
    apply tkm_upd_q_fields; [exact HB | lia | exact L].
Qed.

(* ---- the main loop (:358-382) ---- *)

Lemma tkm_loop_facts : forall (n : nat) B allow i taken kept len hd body B2 bodyF lenF hdF takenF keptF,
  tkm_wf B -> 0 <= i -> 0 <= taken -> 0 <= kept -> taken + kept = i ->
  0 <= len <= DIGINET_MAX_BODY_LEN -> Z.of_nat (length body) = len -> 0 <= hd < 256 ->
  i + Z.of_nat n = S_queued B ->
  take_loop_m B allow i taken kept len hd body n = Some (B2, (bodyF, lenF, hdF, takenF, keptF)) ->
  tkm_wf B2 /\ 0 <= lenF <= DIGINET_MAX_BODY_LEN /\ Z.of_nat (length bodyF) = lenF /\ 0 <= hdF < 256 /\
  0 <= takenF /\ 0 <= keptF /\ takenF + keptF = S_queued B /\
  S_queued B2 = S_queued B /\ g_fail_next B2 = g_fail_next B /\
  S_cfg_max_cmds B2 = S_cfg_max_cmds B /\ S_cfg_max_body B2 = S_cfg_max_body B /\
  ((0 < n)%nat -> S_queued B <= S_queue_N).
Proof.
  induction n as [|n IH]; intros B allow i taken kept len hd body B2 bodyF lenF hdF takenF keptF
    HB Hi Ht Hk Htk Hlen Hbody Hhd Hn H.
  - cbn [take_loop_m] in H. injection H as <- <- <- <- <- <-.
    split; [exact HB|]. split; [exact Hlen|]. split; [exact Hbody|]. split; [exact Hhd|].
    split; [exact Ht|]. split; [exact Hk|]. split; [lia|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros Hc. lia.
  - destruct (Z_lt_le_dec i S_queue_N) as [Hi5|Hi5].
    2: { rewrite tk_loop_S in H.
         replace (S_queue_N <=? i) with true in H by (symmetry; apply Z.leb_le; lia).
         discriminate H. }
    (* the end of the turn: the test of :377, then the tail (:378-380) or the next turn *)
    assert (NEXT : forall B1 body1 len1 taken1 hd1 kept1,
      tkm_wf B1 -> 0 <= taken1 -> 0 <= kept1 -> taken1 + kept1 = i + 1 ->
      0 <= len1 <= DIGINET_MAX_BODY_LEN -> Z.of_nat (length body1) = len1 -> 0 <= hd1 < 256 ->
      S_queued B1 = S_queued B -> g_fail_next B1 = g_fail_next B ->
      S_cfg_max_cmds B1 = S_cfg_max_cmds B -> S_cfg_max_body B1 = S_cfg_max_body B ->
      (if (taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1) then
         match take_tail_m B1 kept1 (i + 1) (Z.to_nat (S_queued B1 - (i + 1))) with
         | None => None
         | Some (B3, kept2) => Some (B3, (body1, len1, hd1, taken1, kept2))
         end
       else take_loop_m B1 allow (i + 1) taken1 kept1 len1 hd1 body1 n)
      = Some (B2, (bodyF, lenF, hdF, takenF, keptF)) ->
      tkm_wf B2 /\ 0 <= lenF <= DIGINET_MAX_BODY_LEN /\ Z.of_nat (length bodyF) = lenF /\ 0 <= hdF < 256 /\
      0 <= takenF /\ 0 <= keptF /\ takenF + keptF = S_queued B /\
      S_queued B2 = S_queued B /\ g_fail_next B2 = g_fail_next B /\
      S_cfg_max_cmds B2 = S_cfg_max_cmds B /\ S_cfg_max_body B2 = S_cfg_max_body B /\
      ((0 < S n)%nat -> S_queued B <= S_queue_N)).
    { intros B1 body1 len1 taken1 hd1 kept1 W1 T1 K1 TK1 L1 BL1 HD1 Q1 G1 C1 M1 H1.
      destruct ((taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1)) eqn:BRK.
      - (* break: the tail moves the entries i + 1 .. s->queued - 1 down *)
        replace (Z.to_nat (S_queued B1 - (i + 1))) with n in H1 by lia.
        destruct (take_tail_m B1 kept1 (i + 1) n) as [[B3 kept2]|] eqn:ET; [|discriminate H1].
        cbv iota in H1. injection H1 as <- <- <- <- <- <-.
        destruct (tkm_tail_facts n B1 kept1 (i + 1) B3 kept2 W1 K1 ltac:(lia) ET)
          as (W3 & K3 & Q3 & G3 & C3 & M3 & R3).
        split; [exact W3|]. split; [exact L1|]. split; [exact BL1|]. split; [exact HD1|].
        split; [exact T1|]. split; [lia|]. split; [lia|].
        split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
        intros _. destruct n as [|n'].
        + lia.
        + destruct (R3 ltac:(lia)) as [R4 _]. lia.
      - (* the next turn *)
        destruct (IH B1 allow (i + 1) taken1 kept1 len1 hd1 body1 B2 bodyF lenF hdF takenF keptF
                    W1 ltac:(lia) T1 K1 TK1 L1 BL1 HD1 ltac:(lia) H1)
          as (W2 & L2 & BL2 & HD2 & T2 & K2 & TK2 & Q2 & G2 & C2 & M2 & R2).
        split; [exact W2|]. split; [exact L2|]. split; [exact BL2|]. split; [exact HD2|].
        split; [exact T2|]. split; [exact K2|]. split; [lia|].
        split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
        intros _. destruct n as [|n'].
        + lia.
        + specialize (R2 ltac:(lia)). lia. }
    rewrite tk_loop_S in H. replace (S_queue_N <=? i) with false in H by (symmetry; apply Z.leb_gt; lia).
    cbv iota zeta in H.
    destruct (tkm_q_ranges B i) as [RCL RDS].
    destruct ((taken <? S_cfg_max_cmds B) && (len + S_queue_len B i <=? S_cfg_max_body B) &&
              (negb (allow =? 0) || (S_queue_display B i =? 0))) eqn:F0; cbn [andb] in H.
    + (* the command fits max_cmds, max_body and the display pacing: the memcpy of :365 *)
      destruct (DIGINET_MAX_BODY_LEN <? len + S_queue_len B i) eqn:FM; [discriminate H|].
      apply Z.ltb_ge in FM.
      assert (LC : length (sub B (A_S_queue_bytes i) (Z.to_nat (S_queue_len B i))) = Z.to_nat (S_queue_len B i))
        by (apply length_sub; tkm_lia).
      destruct (body_check (body ++ sub B (A_S_queue_bytes i) (Z.to_nat (S_queue_len B i))) =? DIGINET_OK)
        eqn:FB.
      * (* taken (:368-371) *)
        apply (NEXT B (body ++ sub B (A_S_queue_bytes i) (Z.to_nat (S_queue_len B i))) (len + S_queue_len B i)
                 (taken + 1) (Z.lor hd (S_queue_display B i)) kept);
          [ exact HB | lia | lia | lia | lia | (rewrite length_app, LC; lia) | (apply tk_lor_256; lia)
          | reflexivity | reflexivity | reflexivity | reflexivity | exact H ].
      * (* refused by the body check: kept (:373-375) *)
        destruct (tkm_keep_facts B kept i HB ltac:(lia) Hi5) as (WK & QK & GK & CK & MK).
        apply (NEXT (tkm_keep B kept i) body len taken hd (kept + 1));
          [ exact WK | lia | lia | lia | exact Hlen | exact Hbody | exact Hhd
          | exact QK | exact GK | exact CK | exact MK | exact H ].
    + (* kept (:373-375) *)
      destruct (tkm_keep_facts B kept i HB ltac:(lia) Hi5) as (WK & QK & GK & CK & MK).
      apply (NEXT (tkm_keep B kept i) body len taken hd (kept + 1));
        [ exact WK | lia | lia | lia | exact Hlen | exact Hbody | exact Hhd
        | exact QK | exact GK | exact CK | exact MK | exact H ].
Qed.

(* ---- the top level (:353-386) ---- *)

Lemma tkm_take_m : forall B allow B' body len hd taken, tkm_wf B ->
  take_m B allow = Some (B', (body, len, hd, taken)) ->
  exists B1 kept,
    take_loop_m B allow 0 0 0 0 0 [] (Z.to_nat (S_queued B)) = Some (B1, (body, len, hd, taken, kept)) /\
    B' = set_S_queued B1 kept /\
    tkm_wf B1 /\ tkm_wf B' /\
    S_queued B1 = S_queued B /\ g_fail_next B1 = g_fail_next B /\ g_fail_next B' = g_fail_next B /\
    S_queued B' = kept /\
    0 <= taken /\ 0 <= kept /\ taken + kept = S_queued B /\ 0 <= S_queued B <= S_queue_N /\
    0 <= len <= DIGINET_MAX_BODY_LEN /\ Z.of_nat (length body) = len /\ 0 <= hd < 256.
Proof.
  intros B allow B' body len hd taken HB H. unfold take_m in H.
  destruct (take_loop_m B allow 0 0 0 0 0 [] (Z.to_nat (S_queued B)))
    as [[B1 [[[[bodyF lenF] hdF] takenF] keptF]]|] eqn:EL; [|discriminate H].
  injection H as <- <- <- <- <-.
  pose proof (tkm_queued_range B) as RQ.
  destruct (tkm_loop_facts (Z.to_nat (S_queued B)) B allow 0 0 0 0 0 [] B1 bodyF lenF hdF takenF keptF
              HB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold DIGINET_MAX_BODY_LEN; lia)
              eq_refl ltac:(lia) ltac:(lia) EL)
    as (W1 & L1 & BL1 & HD1 & T1 & K1 & TK1 & Q1 & G1 & C1 & M1 & R1).
  assert (W' : tkm_wf (set_S_queued B1 keptF))
    by (unfold tkm_wf, set_S_queued in *; rewrite length_upd_put by tkm_lia; exact W1).
  assert (QK : S_queued (set_S_queued B1 keptF) = keptF).
  { unfold S_queued, set_S_queued. rewrite u_at_upd_put by tkm_lia.
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). apply Z.mod_small. lia. }
  assert (GK : g_fail_next (set_S_queued B1 keptF) = g_fail_next B1).
  { unfold g_fail_next, set_S_queued. apply u_at_upd_out; rewrite ?length_put; tkm_lia. }
  exists B1, keptF.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact W1|]. split; [exact W'|].
  split; [exact Q1|]. split; [exact G1|]. split; [congruence|]. split; [exact QK|].
  split; [exact T1|]. split; [exact K1|]. split; [exact TK1|].
  split.
  { destruct (Z.eq_dec (S_queued B) 0) as [E0|E0].
    - unfold S_queue_N. lia.
    - split; [lia|]. apply R1. lia. }
  split; [exact L1|]. split; [exact BL1|]. exact HD1.
Qed.

(* ---- one turn, with the index test discharged (0 <= i < 512) ---- *)

Lemma tkm_loop_S : forall B allow i taken kept len hd body (n : nat), 0 <= i < S_queue_N ->
  take_loop_m B allow i taken kept len hd body (S n) =
  (let clen := S_queue_len B i in
   let fits0 := (taken <? S_cfg_max_cmds B) && (len + clen <=? S_cfg_max_body B) &&
                (negb (allow =? 0) || (S_queue_display B i =? 0)) in
   if fits0 && (DIGINET_MAX_BODY_LEN <? len + clen) then None
   else
   let cand := body ++ sub B (A_S_queue_bytes i) (Z.to_nat clen) in
   let fits := fits0 && (body_check cand =? DIGINET_OK) in
   let '(B1, body1, len1, taken1, hd1, kept1) :=
     if fits then (B, cand, len + clen, taken + 1, Z.lor hd (S_queue_display B i), kept)
     else ((if kept =? i then B else upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes i) 32)),
           body, len, taken, hd, kept + 1) in
   if (taken1 =? S_cfg_max_cmds B1) || (len1 =? S_cfg_max_body B1) then
     match take_tail_m B1 kept1 (i + 1) (Z.to_nat (S_queued B1 - (i + 1))) with
     | None => None
     | Some (B2, kept2) => Some (B2, (body1, len1, hd1, taken1, kept2))
     end
   else take_loop_m B1 allow (i + 1) taken1 kept1 len1 hd1 body1 n).
Proof.
  intros B allow i taken kept len hd body n Hi. rewrite tk_loop_S.
  replace (S_queue_N <=? i) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma tkm_tail_S : forall B kept j (n : nat), 0 <= j < S_queue_N -> 0 <= kept < S_queue_N ->
  take_tail_m B kept j (S n) =
  take_tail_m (upd B (A_S_queue_bytes kept) (sub B (A_S_queue_bytes j) 32)) (kept + 1) (j + 1) n.
Proof.
  intros B kept j n Hj Hk. rewrite tk_tail_S.
  replace ((S_queue_N <=? j) || (S_queue_N <=? kept)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.leb_gt; lia).
  reflexivity.
Qed.

(* ---- the ranges of the three 1-byte and 4-byte fields the code loads ---- *)

Lemma tkm_field_ranges : forall B i,
  0 <= S_queue_len B i < 256 /\ 0 <= S_queue_display B i < 256 /\
  0 <= S_cfg_max_cmds B < 2 ^ 32 /\ 0 <= S_cfg_max_body B < 2 ^ 32 /\ 0 <= S_queued B < 2 ^ 32.
Proof.
  intros B i. unfold S_queue_len, S_queue_display, S_cfg_max_cmds, S_cfg_max_body, S_queued.
  split; [apply tkm_u_at_1|]. split; [apply tkm_u_at_1|].
  split; [apply tkm_u_at_4|]. split; [apply tkm_u_at_4|]. apply tkm_u_at_4.
Qed.

(* `or` of two bytes is a byte (the store of *has_display | c->display at :370). *)
Lemma tkm_lor_byte : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> 0 <= Z.lor x y < 256.
Proof. exact tk_lor_256. Qed.
