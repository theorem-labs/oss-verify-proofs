(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO03 YO0n YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Lemma prN_mono : forall n m, 0 <= n <= m -> prN n <= prN m.
Proof.
intros n m H. unfold prN. destruct (Z.ltb_spec MMAP_THRESHOLD n), (Z.ltb_spec MMAP_THRESHOLD m); try lia.
- apply page_round_mono. lia.
- pose proof (page_round_bounds (m + IB + UNIT) ltac:(unfold IB, UNIT; lia)). unfold IB, UNIT in *. lia.
Qed.
Lemma lzw_peak_mono : forall n m, 0 <= n <= m -> lzw_peak n <= lzw_peak m.
Proof. intros n m H. unfold lzw_peak. pose proof (page_round_mono (2 * n + 2 ^ 16) (2 * m + 2 ^ 16) ltac:(lia)). lia. Qed.
Lemma rawadd_peak_mono : forall n m, 0 <= n <= m -> rawadd_peak n <= rawadd_peak m.
Proof. intros n m H. unfold rawadd_peak. pose proof (prN_mono n m H). pose proof (lzw_peak_mono n m H). lia. Qed.
Lemma rawadd_peak_nonneg : forall n, 0 <= n -> 0 <= rawadd_peak n.
Proof. intros n H. unfold rawadd_peak, lzw_peak. pose proof (prN_nonneg n H). pose proof (page_round_bounds (2 * n + 2 ^ 16) ltac:(lia)). lia. Qed.
Ltac fnums := cbv [rb_le rb_acc rb_malloc flush_rb rawadd_rb FLUSH_K RAWADD_K LZW_K MMAX PGSZ rb_bytes rb_cnt rb_hand rb_brk] in *.
Lemma flush_room_tmp : forall b N n, 0 <= N -> 0 < n <= N -> flush_room b N ->
room b n /\ rawadd_room (rb_malloc b n) n /\ rb_le (rb_free (rawadd_rb (rb_malloc b n)) n) (flush_rb b).
Proof.
intros b N n HN Hn HR. unfold flush_room in HR.
pose proof (prN_nonneg N HN) as P0. pose proof (prN_mono n N ltac:(lia)) as P1. pose proof (prN_nonneg n ltac:(lia)) as P2.
pose proof (rawadd_peak_nonneg n ltac:(lia)) as Q0. pose proof (rawadd_peak_mono n N ltac:(lia)) as Q1.
pose proof (mdelta_le n ltac:(lia)) as M1. pose proof (mdelta_nonneg n ltac:(lia)) as M0.
split; [| split].
- apply (room_mono b (rb_acc b FLUSH_K (flush_peak N)) n (flush_maxreq N)); [| unfold flush_maxreq, rawadd_maxreq, lzw_maxreq; lia | exact HR].
apply rb_acc_le; [unfold FLUSH_K, RAWADD_K, LZW_K; lia | unfold flush_peak; lia].
- unfold rawadd_room. apply (room_mono _ (rb_acc b FLUSH_K (flush_peak N)) _ (flush_maxreq N)); [| unfold flush_maxreq, rawadd_maxreq, lzw_maxreq; lia | exact HR].
unfold flush_peak. fnums. lia.
- unfold rawadd_rb, rb_free, prN in *. destruct (MMAP_THRESHOLD <? n); fnums; lia.
Qed.
Lemma flush_room_notmp : forall b N, 0 <= N -> flush_room b N -> rawadd_room b N /\ rb_le (rawadd_rb b) (flush_rb b).
Proof.
intros b N HN HR. unfold flush_room in HR. pose proof (prN_nonneg N HN) as P0. pose proof (rawadd_peak_nonneg N HN) as Q0.
split.
- unfold rawadd_room. apply (room_mono _ (rb_acc b FLUSH_K (flush_peak N)) _ (flush_maxreq N)); [| unfold flush_maxreq; pose proof (room_size _ _ HR); unfold flush_maxreq, rawadd_maxreq, lzw_maxreq in *; lia | exact HR].
unfold flush_peak. fnums. lia.
- fnums. lia.
Qed.
