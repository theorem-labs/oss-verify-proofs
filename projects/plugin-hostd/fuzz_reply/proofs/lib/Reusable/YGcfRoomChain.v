(* THE LONG-INPUT ROOM CHAIN (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (g)2; ROOM round piece #7, ROOM-PIECES.md (sha256 6c9d89de0d5a; internal record)).
   The room round's allocator rules need, at each allocator call's OWN pre state S: the room invariant
   room_live_cf S and the live counts (rl_sec_ok Lsec S, ccnt24 S <= L24, rl_b24_ok (L24 + 1) S, and the
   per-class lines).  The summed forms failed exactly on long inputs (a relay held array that grows once per begin,
   72,687 begins): this file shows, at the ALLOCATOR MODEL, that the per-call form does not.
   The chain: allocator states S 0 .. S N, where every step is a model realloc (a path of realloc_tree_with malloc_cf
   free_cf, the step room_live_call_keep's rl_call quantifies over) of ONE live block, the held block h k (the relay's
   held array, regrown per begin), and nothing else changes the live blocks.  From the start state
     - room_live_cf (S 0), and blocks (S 0) = rest ++ [h 0] up to order,
     - the counts of rest leave one unit of margin under the bounds (the held block may change class as it grows),
   and, at each step, Wf_cf and qtight at its pre state (what the rule's ARcf and its journal carry at each call) and
   the model realloc path with its side conditions, chain_inv proves at EVERY state S k, k <= N: room_live_cf (S k)
   (by room_live_call_keep, YGcfRoomLive.v:1410, at each step), blocks (S k) = rest ++ [h k] up to order (the
   allocator's own realloc post YGcfAmx2.amx_realloc_cf gives the block effect), and the counts, so every call's full
   count premise holds.  Each live count differs from rest's by the held block's class membership only: at most + 1.
   Generic in N (chain_inv), with the instance N := 72,687 (chain_inv_long).
   SCOPE: this is a satisfiability witness at the allocator model, not a walk lemma: the model path of each call exists
   inside the cf realloc site's proof (arealloc_realizes_cf), one call at a time, and the room kit's realloc rule does
   not export it.  The chain changes only the held block, as (g)2 states it (the real input also mallocs other blocks
   between reallocs; their counts are LS's cut bounds, ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c)).
   The count of the requests satisfying P is bcnt P, the body of W_journal_x.v:625's acnt over the blocks. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11 YM05 YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG02 YG04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfPath YGcfAmx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre YGcfRoomKeep YGcfRoomStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YG0dcf ReallocP YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfSecBound YG02cf YG03cf YG07cf YGcfApath.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomLive YGcfAmx2.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the live count of the requests satisfying P ---- *)
Definition bcnt (P : Z -> bool) (l : list (sptr * Z)) : nat := length (filter P (map snd l)).

Lemma bcnt_app : forall P l1 l2, bcnt P (l1 ++ l2) = (bcnt P l1 + bcnt P l2)%nat.
Proof. intros P l1 l2. unfold bcnt. rewrite map_app, filter_app, length_app. reflexivity. Qed.

Lemma bcnt_one : forall P b, (bcnt P [b] <= 1)%nat.
Proof. intros P b. unfold bcnt. cbn. destruct (P (snd b)); cbn; lia. Qed.

Lemma bcnt_perm : forall P l l', Permutation l l' -> bcnt P l = bcnt P l'.
Proof.
  intros P l l' H. unfold bcnt.
  induction H as [|b l l' _ IH|b1 b2 l|l l' l'' _ IH1 _ IH2]; cbn [map filter].
  - reflexivity.
  - destruct (P (snd b)); cbn [length]; rewrite IH; reflexivity.
  - destruct (P (snd b1)), (P (snd b2)); reflexivity.
  - congruence.
Qed.

(* the held-block shape bounds every count by rest's plus one *)
Lemma bcnt_shape : forall P l rest b, Permutation l (rest ++ [b]) -> (bcnt P l <= bcnt P rest + 1)%nat.
Proof.
  intros P l rest b H. rewrite (bcnt_perm P _ _ H), bcnt_app. pose proof (bcnt_one P b). lia.
Qed.

(* the room counts of YGcfRoomLive.v are bcnt counts *)
Lemma sec_cnt_bcnt : forall s, sec_cnt s = Z.of_nat (bcnt rl_sec_req (blocks s)).
Proof. intros s. reflexivity. Qed.

Lemma ccnt24_bcnt : forall s, ccnt24 s = Z.of_nat (bcnt (PresetRoom.in_cls kBatchClass) (blocks s)).
Proof. intros s. reflexivity. Qed.

(* realloc's effect on the shape: the held block is replaced on success and kept on failure *)
Lemma shape_realloc : forall s s' rest b n q,
  Permutation (blocks s) (rest ++ [b]) -> realloc_post_cf s (fst b) (snd b) n (q, s') ->
  (q = PNull -> Permutation (blocks s') (rest ++ [b])) /\
  (q <> PNull -> Permutation (blocks s') (rest ++ [(q, n)])).
Proof.
  intros s s' rest [p m] n q H (_ & _ & _ & HN & HS). cbn [fst snd] in *. split.
  - intros Hq. rewrite (HN Hq). exact H.
  - intros Hq. destruct (HS Hq) as (l1 & l2 & E1 & E2). rewrite E2.
    rewrite E1 in H.
    assert (HP : Permutation (l1 ++ l2) (rest ++ [])) by (exact (Permutation_app_inv l1 l2 rest [] (p, m) H)).
    rewrite app_nil_r in HP. rewrite app_assoc. apply Permutation_app_tail. exact HP.
Qed.

Section chain.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : YG0f.asyms.
Local Notation U := (YG0f.as_universe B).
(* the count bounds of room_live_call_keep (the ruled values are Lsec = 1,024, L24 = 2 ^ 15) *)
Variables Lsec L24 : Z.
Hypothesis HLsec : Lsec + QSEC_MAX + 3 < cf_sec_live_max.
Hypothesis HL24 : kBatchBytes * (L24 + 1 + N24Q + 1) + 4 * kUserMapSize <= kFreeArrayOffset.
Variable N : nat.
Variable S : nat -> astate.
(* the held block at each state, and the live blocks no call of the chain touches *)
Variable h : nat -> sptr * Z.
Variable rest : list (sptr * Z).

(* the start state *)
Hypothesis S0_shape : Permutation (blocks (S 0%nat)) (rest ++ [h 0%nat]).
Hypothesis S0_room : room_live_cf (S 0%nat).
Hypothesis S0_sec : Z.of_nat (bcnt rl_sec_req rest) + 1 <= Lsec.
Hypothesis S0_24 : Z.of_nat (bcnt (PresetRoom.in_cls kBatchClass) rest) + 1 <= L24.

(* one step of the chain at its pre state S k: the allocator's state invariant and qtight there, the model realloc
   path of the held block to a new size n >= 1 with rl_call's side conditions, and the held block after it (the new
   block on success, the old one on failure) *)
Definition chain_step (k : nat) : Prop :=
  Wf_cf U (S k) /\ qtight (S k) /\
  exists n tr trc q, universe_ok U /\ In tr U /\ 1 <= n < cf_malloc_max /\ blocks_bytes (S k) + n <= LIVE_MAX /\
    apath (realloc_tree_with malloc_cf free_cf (fst (h k)) n tr (S k)) trc (q, S (Datatypes.S k)) /\
    ((q = PNull /\ h (Datatypes.S k) = h k) \/ (q <> PNull /\ h (Datatypes.S k) = (q, n))).
Hypothesis STEP : forall k, (k < N)%nat -> chain_step k.

(* the counts at a state of the held-block shape: every room_live_call_keep count premise *)
Lemma chain_counts_of_shape : forall s b, Permutation (blocks s) (rest ++ [b]) ->
  rl_sec_ok Lsec s /\ ccnt24 s <= L24 /\ rl_b24_ok (L24 + 1) s.
Proof.
  intros s b H. pose proof (bcnt_shape rl_sec_req _ _ _ H) as Hs.
  pose proof (bcnt_shape (PresetRoom.in_cls kBatchClass) _ _ _ H) as H4.
  assert (Hs' : sec_cnt s <= Lsec) by (rewrite sec_cnt_bcnt; lia).
  assert (H4' : ccnt24 s <= L24) by (rewrite ccnt24_bcnt; lia).
  unfold rl_sec_ok, rl_b24_ok. split; [split; lia|]. split; [exact H4'|]. split; [lia | exact HL24].
Qed.

Theorem chain_inv : forall k, (k <= N)%nat ->
  room_live_cf (S k) /\ Permutation (blocks (S k)) (rest ++ [h k]).
Proof.
  induction k as [|k IH]; intros Hk.
  - split; [exact S0_room | exact S0_shape].
  - destruct (IH ltac:(lia)) as [HR HP].
    destruct (STEP k ltac:(lia)) as (HW & HT & n & tr & trc & q & HU & Htr & Hn & Hlive & Hpath & Hh).
    destruct (chain_counts_of_shape (S k) (h k) HP) as (Hsec & H24 & Hb24).
    (* the allocator's realloc post on this path (amx_realloc_cf at headroom 0: ROOM_cf_k S RK_realloc from room_live_cf) *)
    assert (Hin : In (fst (h k), snd (h k)) (blocks (S k))).
    { rewrite <- surjective_pairing. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. left. reflexivity. }
    assert (HRk : ROOM_cf_k (S k) (RK_realloc + 0)) by (rewrite Nat.add_0_r; exact (room_live_room_k (S k) HR)).
    destruct (amx_realloc_cf B (S k) (fst (h k)) (snd (h k)) n tr 0 HU HW HT HRk Hin Hn Hlive (admits_fix _ _ (S k) HU Htr))
      as (_ & _ & _ & HPOST).
    pose proof (HPOST trc (q, S (Datatypes.S k)) Hpath) as Hpost.
    split.
    + apply (room_live_call_keep U Lsec L24 (S k) (S (Datatypes.S k)) HW HT Hsec H24 Hb24 HR).
      assert (Hn0 : 0 <= n < cf_malloc_max) by lia.
      right. right. left. exists (fst (h k)), n, tr, trc, q.
      exact (conj HU (conj (admits_fix _ _ (S k) HU Htr) (conj Hn0 (conj Hlive Hpath)))).
    + destruct (shape_realloc (S k) (S (Datatypes.S k)) rest (h k) n q HP Hpost) as [Hnull Hsome].
      destruct Hh as [(Hq & ->) | (Hq & ->)]; [exact (Hnull Hq) | exact (Hsome Hq)].
Qed.

(* at every state of the chain: the room invariant and every count premise of the room round's allocator rules *)
Corollary chain_room_counts : forall k, (k <= N)%nat ->
  room_live_cf (S k) /\ rl_sec_ok Lsec (S k) /\ ccnt24 (S k) <= L24 /\ rl_b24_ok (L24 + 1) (S k).
Proof.
  intros k Hk. destruct (chain_inv k Hk) as [HR HP]. split; [exact HR|].
  exact (chain_counts_of_shape (S k) (h k) HP).
Qed.

(* every other live count (the per-class lines of the count block) stays within rest's plus one *)
Corollary chain_bcnt : forall k P, (k <= N)%nat -> (bcnt P (blocks (S k)) <= bcnt P rest + 1)%nat.
Proof. intros k P Hk. destruct (chain_inv k Hk) as [_ HP]. exact (bcnt_shape P _ _ _ HP). Qed.
End chain.

(* THE INSTANCE: N := 72,687 replace-reallocs (the long acceptance input, ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (g)) *)
Definition N_LONG : nat := 72687%nat.

Corollary chain_inv_long : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} B Lsec L24 S h rest,
  Lsec + QSEC_MAX + 3 < cf_sec_live_max ->
  kBatchBytes * (L24 + 1 + N24Q + 1) + 4 * kUserMapSize <= kFreeArrayOffset ->
  Permutation (blocks (S 0%nat)) (rest ++ [h 0%nat]) -> room_live_cf (S 0%nat) ->
  Z.of_nat (bcnt rl_sec_req rest) + 1 <= Lsec ->
  Z.of_nat (bcnt (PresetRoom.in_cls kBatchClass) rest) + 1 <= L24 ->
  (forall k, (k < N_LONG)%nat -> chain_step B S h k) ->
  forall k, (k <= N_LONG)%nat ->
  room_live_cf (S k) /\ rl_sec_ok Lsec (S k) /\ ccnt24 (S k) <= L24 /\ rl_b24_ok (L24 + 1) (S k).
Proof.
  intros fx rc ci cp B Lsec L24 S h rest H1 H2 H3 H4 H5 H6 H7 k Hk.
  exact (chain_room_counts B Lsec L24 H1 H2 N_LONG S h rest H3 H4 H5 H6 H7 k Hk).
Qed.

Print Assumptions chain_inv.
Print Assumptions chain_inv_long.
