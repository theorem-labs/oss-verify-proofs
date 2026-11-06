(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO03 YO0n YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a YI2k.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Ltac anums := cbv [rb_le rb_acc rb_malloc rb_free flush_rb af_rb AF_K FLUSH_K RAWADD_K LZW_K MMAX PGSZ PALSLACK PALMAX rb_bytes rb_cnt rb_hand rb_brk] in *.
Lemma af_room_flush : forall b N, 0 <= N -> af_room b N -> flush_room b N.
Proof.
intros b N HN HR. unfold af_room in HR. unfold flush_room.
pose proof (prN_nonneg N HN). pose proof (flush_peak_nonneg := rawadd_peak_nonneg N HN).
apply (room_mono _ (rb_acc b AF_K (prN N + PALSLACK + flush_peak N)) _ (flush_maxreq N)); [| pose proof (room_size _ _ HR); lia | exact HR].
unfold flush_peak in *. anums. lia.
Qed.
Lemma af_room_copies : forall b bc N nlp, 1 <= N -> 0 <= nlp -> 3 * nlp <= PALMAX -> af_room b N -> rb_le bc (flush_rb b) ->
room bc 40 /\ room (rb_malloc bc 40) N /\ room (rb_malloc (rb_malloc bc 40) N) (3 * nlp).
Proof.
intros b bc N nlp HN Hnlp Hpal HR Hle. unfold af_room in HR.
pose proof (prN_nonneg N ltac:(lia)) as P0. pose proof (rawadd_peak_nonneg N ltac:(lia)) as Q0.
pose proof (mdelta_le N ltac:(lia)) as M1. pose proof (mdelta_nonneg N ltac:(lia)) as M0.
assert (M40 : mdelta 40 = MMAX) by reflexivity.
assert (HMX : 40 <= flush_maxreq N /\ N <= flush_maxreq N /\ 3 * nlp <= flush_maxreq N) by (unfold flush_maxreq, rawadd_maxreq, lzw_maxreq; anums; lia).
split; [| split].
- apply (room_mono _ (rb_acc b AF_K (prN N + PALSLACK + flush_peak N)) _ (flush_maxreq N)); [| lia | exact HR]. unfold flush_peak. anums. lia.
- apply (room_mono _ (rb_acc b AF_K (prN N + PALSLACK + flush_peak N)) _ (flush_maxreq N)); [| lia | exact HR]. unfold flush_peak. anums. rewrite ?M40 in *. lia.
- apply (room_mono _ (rb_acc b AF_K (prN N + PALSLACK + flush_peak N)) _ (flush_maxreq N)); [| lia | exact HR]. unfold flush_peak. anums. rewrite ?M40 in *. lia.
Qed.
Lemma af_rb_copies : forall b bc N nlp dq (e : Z) (lct : bool), 0 <= N -> 0 <= nlp -> 3 * nlp <= PALMAX ->
rb_le bc (RB (rb_bytes b + FLUSH_K * MMAX - e) (rb_cnt b + FLUSH_K) (rb_hand b + 65 * FLUSH_K) (rb_brk b + 2 * PGSZ * FLUSH_K)) ->
prN N <= e + dq * prN N ->
rb_le (if lct then rb_malloc (rb_malloc (rb_malloc bc 40) N) (3 * nlp) else rb_malloc (rb_malloc bc 40) N) (rb_acc b AF_K (dq * prN N + PALSLACK)).
Proof.
intros b bc N nlp dq e lct HN Hnlp Hpal Hle He.
pose proof (prN_nonneg N HN) as P0. pose proof (mdelta_le N HN) as M1. pose proof (mdelta_nonneg N HN) as M0.
pose proof (mdelta_le (3 * nlp) ltac:(lia)) as M3. pose proof (mdelta_nonneg (3 * nlp) ltac:(lia)) as M30.
assert (M40 : mdelta 40 = MMAX) by reflexivity.
assert (P3 : prN (3 * nlp) <= PALSLACK).
{ unfold prN. destruct (MMAP_THRESHOLD <? 3 * nlp); [| anums; lia]. pose proof (page_round_bounds (3 * nlp + IB + UNIT) ltac:(unfold IB, UNIT; lia)). unfold IB, UNIT, PALMAX, PALSLACK in *. lia. }
set (T := dq * prN N) in *. destruct b as [bb bcn bh bk], bc as [cb cc ch ck]. destruct lct; anums; rewrite ?M40 in *; lia.
Qed.
Lemma af_nums_noflush : forall b N nlp q, 1 <= N -> 0 <= nlp -> 3 * nlp <= PALMAX -> af_room b N ->
room b 40 /\ room (rb_malloc b 40) N /\ room (rb_malloc (rb_malloc b 40) N) (3 * nlp) /\
forall lct : bool, rb_le (if lct then rb_malloc (rb_malloc (rb_malloc b 40) N) (3 * nlp) else rb_malloc (rb_malloc b 40) N) (af_rb b N q (q + 1)).
Proof.
intros b N nlp q HN Hnlp Hpal HR. destruct (af_room_copies b b N nlp HN Hnlp Hpal HR ltac:(destruct b; anums; lia)) as (R1 & R2 & R3).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. intros lct. unfold af_rb.
apply (af_rb_copies b b N nlp (q + 1 - q) 0 lct); [lia | lia | lia | destruct b; anums; lia | pose proof (prN_nonneg N ltac:(lia)); nia].
Qed.
Lemma af_nums_flushed : forall b N nlp q, 1 <= N -> 0 <= nlp -> 3 * nlp <= PALMAX -> af_room b N ->
let bc := flush_rb b in
room bc 40 /\ room (rb_malloc bc 40) N /\ room (rb_malloc (rb_malloc bc 40) N) (3 * nlp) /\
forall lct : bool, rb_le (if lct then rb_malloc (rb_malloc (rb_malloc bc 40) N) (3 * nlp) else rb_malloc (rb_malloc bc 40) N) (af_rb b N q (q + 1)).
Proof.
intros b N nlp q HN Hnlp Hpal HR. cbv zeta. destruct (af_room_copies b (flush_rb b) N nlp HN Hnlp Hpal HR (rb_le_refl _)) as (R1 & R2 & R3).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. intros lct. unfold af_rb.
apply (af_rb_copies b (flush_rb b) N nlp (q + 1 - q) 0 lct); [lia | lia | lia | destruct b; anums; lia | pose proof (prN_nonneg N ltac:(lia)); nia].
Qed.
Lemma af_nums_evicted : forall b N nlp q, 1 <= N -> 0 <= nlp -> 3 * nlp <= PALMAX -> af_room b N ->
let bc := rb_free (flush_rb b) N in
room bc 40 /\ room (rb_malloc bc 40) N /\ room (rb_malloc (rb_malloc bc 40) N) (3 * nlp) /\
forall lct : bool, rb_le (if lct then rb_malloc (rb_malloc (rb_malloc bc 40) N) (3 * nlp) else rb_malloc (rb_malloc bc 40) N) (af_rb b N q q).
Proof.
intros b N nlp q HN Hnlp Hpal HR. cbv zeta. destruct (af_room_copies b (rb_free (flush_rb b) N) N nlp HN Hnlp Hpal HR (rb_free_le _ _)) as (R1 & R2 & R3).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. intros lct. unfold af_rb.
apply (af_rb_copies b (rb_free (flush_rb b) N) N nlp (q - q) (prN N) lct); [lia | lia | lia | | pose proof (prN_nonneg N ltac:(lia)); nia].
unfold rb_free, prN. destruct b; destruct (MMAP_THRESHOLD <? N); anums; lia.
Qed.
Lemma af_rb_failed_evicted : forall b N q, 0 <= N -> rb_le (rb_free (flush_rb b) N) (af_rb b N q (q - 1)).
Proof. intros b N q HN. unfold af_rb, rb_free. unfold prN. destruct b; destruct (MMAP_THRESHOLD <? N); anums; nia. Qed.
Lemma af_rb_flushed_same : forall b N q, 0 <= N -> rb_le (flush_rb b) (af_rb b N q q).
Proof. intros b N q HN. pose proof (prN_nonneg N HN). unfold af_rb. destruct b; anums; nia. Qed.
Lemma af_rb_same : forall b N q, 0 <= N -> rb_le b (af_rb b N q q).
Proof. intros b N q HN. pose proof (prN_nonneg N HN). unfold af_rb. destruct b; anums; nia. Qed.
Lemma af_rb_mono_free : forall b b' n, rb_le b b' -> rb_le (rb_free b n) b'.
Proof. intros b b' n H. eapply rb_le_trans; [apply rb_free_le | exact H]. Qed.
