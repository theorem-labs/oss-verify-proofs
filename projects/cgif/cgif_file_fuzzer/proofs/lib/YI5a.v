(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition prN (n : Z) : Z := if MMAP_THRESHOLD <? n then page_round (n + IB + UNIT) else 0.
Definition rb_acc (b : rbound) (k extra : Z) : rbound :=
RB (rb_bytes b + k * MMAX + extra) (rb_cnt b + k) (rb_hand b + 65 * k) (rb_brk b + 2 * PGSZ * k).
Definition PALMAX : Z := 196605.
Definition PALSLACK : Z := 2 ^ 18.
Definition rfc_rb_ok (b : rbound) (fattr nlp N : Z) : rbound :=
rb_malloc (if Z.land fattr 1 =? 0 then b else rb_malloc b (3 * nlp)) N.
Definition rfc_rb_fail (b : rbound) : rbound := rb_acc b 2 0.
Definition rfc_room (b : rbound) (N : Z) : Prop := room (rb_acc b 1 PALSLACK) (Z.max N PALMAX).
Definition NEWGIF_K : Z := 4.
Definition newgif_rb (b : rbound) : rbound := rb_acc b NEWGIF_K PALSLACK.
Definition newgif_room (b : rbound) : Prop := room (rb_acc b NEWGIF_K PALSLACK) PALMAX.
Definition LZW_K : Z := 9.
Definition lzw_peak (N : Z) : Z := 2 * page_round (2 * N + 2 ^ 16) + 2 ^ 21.
Definition lzw_maxreq (N : Z) : Z := Z.max (2 ^ 21) (2 * N + 2 ^ 16).
Definition lzw_room (b : rbound) (N : Z) : Prop := room (rb_acc b LZW_K (lzw_peak N)) (lzw_maxreq N).
Definition lzw_rb (b : rbound) (x : Z) : rbound := rb_acc b LZW_K x.
Definition RAWADD_K : Z := 2 + LZW_K.
Definition rawadd_peak (N : Z) : Z := prN N + lzw_peak N.
Definition rawadd_maxreq (N : Z) : Z := lzw_maxreq N.
Definition rawadd_room (b : rbound) (N : Z) : Prop := room (rb_acc b RAWADD_K (rawadd_peak N)) (rawadd_maxreq N).
Definition rawadd_rb (b : rbound) : rbound := rb_acc b RAWADD_K 0.
Definition FLUSH_K : Z := 2 + RAWADD_K.
Definition flush_peak (N : Z) : Z := 2 * prN N + rawadd_peak N.
Definition flush_maxreq (N : Z) : Z := rawadd_maxreq N.
Definition flush_room (b : rbound) (N : Z) : Prop := room (rb_acc b FLUSH_K (flush_peak N)) (flush_maxreq N).
Definition flush_rb (b : rbound) : rbound := rb_acc b FLUSH_K 0.
Definition AF_K : Z := 3 + FLUSH_K.
Definition af_rb (b : rbound) (N q q' : Z) : rbound := rb_acc b AF_K ((q' - q) * prN N + PALSLACK).
Definition af_room (b : rbound) (N : Z) : Prop := room (rb_acc b AF_K (prN N + PALSLACK + flush_peak N)) (flush_maxreq N).
Definition CLOSE_K : Z := 2 * FLUSH_K.
Definition close_rb (b : rbound) (N q : Z) : rbound := rb_acc b CLOSE_K (- (q * prN N)).
Definition close_room (b : rbound) (N : Z) : Prop := room (rb_acc b CLOSE_K (flush_peak N)) (flush_maxreq N).
Lemma rb_acc_le : forall b k x, 0 <= k -> 0 <= x -> rb_le b (rb_acc b k x).
Proof. intros b k x Hk Hx. unfold rb_le, rb_acc, PGSZ, MMAX. cbn. lia. Qed.
Lemma rb_acc_mono : forall b b' k x k' x', rb_le b b' -> 0 <= k <= k' -> x <= x' -> rb_le (rb_acc b k x) (rb_acc b' k' x').
Proof. intros b b' k x k' x' (L1 & L2 & L3 & L4) Hk Hx. unfold rb_le, rb_acc, PGSZ, MMAX in *. cbn. lia. Qed.
Lemma rb_acc_acc : forall b k x k' x', rb_acc (rb_acc b k x) k' x' = rb_acc b (k + k') (x + x').
Proof. intros b k x k' x'. unfold rb_acc. cbn. f_equal; lia. Qed.
Lemma prN_nonneg : forall n, 0 <= n -> 0 <= prN n.
Proof. intros n Hn. unfold prN. destruct (MMAP_THRESHOLD <? n); [|lia]. pose proof (page_round_bounds (n + IB + UNIT)). unfold IB, UNIT in *. lia. Qed.
Lemma mdelta_le : forall n, 0 <= n -> mdelta n <= MMAX + prN n.
Proof.
intros n Hn. unfold mdelta, prN. pose proof (page_round_bounds (n + IB + UNIT)).
destruct (Z.leb_spec MMAP_THRESHOLD n); destruct (Z.ltb_spec MMAP_THRESHOLD n); unfold MMAX, IB, UNIT, MMAP_THRESHOLD in *; try lia.
Qed.
Lemma rb_malloc_acc : forall b n, 0 <= n -> rb_le (rb_malloc b n) (rb_acc b 1 (prN n)).
Proof. intros b n Hn. pose proof (mdelta_le n Hn). unfold rb_le, rb_malloc, rb_acc, PGSZ in *. cbn. lia. Qed.
Lemma rb_free_acc : forall b n k x, rb_le (rb_free (rb_acc b k x) n) (rb_acc b k (x - prN n)).
Proof.
intros b n k x. unfold rb_free, rb_acc, prN, rb_le. destruct (MMAP_THRESHOLD <? n); cbn; lia.
Qed.
Lemma rb_free_mono : forall b b' n, rb_le b b' -> rb_le (rb_free b n) (rb_free b' n).
Proof. intros b b' n (L1 & L2 & L3 & L4). unfold rb_le, rb_free in *. destruct (MMAP_THRESHOLD <? n); cbn; lia. Qed.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK15 YI16 YI17 YO09 YO08 YI0a.
Definition ITK : Z := 2 + AF_K.
Definition loop_bud (b0 : rbound) (N k q : Z) : rbound :=
rb_acc b0 (7 + (16 - k) * ITK) (q * prN N + prN N + (3 + 2 * (16 - k)) * PALSLACK).
Definition loop_bud3 (b0 : rbound) (N k q1 : Z) : rbound :=
rb_acc b0 (7 + (16 - k) * ITK + AF_K) (q1 * prN N + (4 + 2 * (16 - k)) * PALSLACK).
Lemma prN_le : forall N, 0 <= N <= 100000000 -> 0 <= prN N <= 100012032.
Proof.
intros N HN. unfold prN. destruct (MMAP_THRESHOLD <? N); [|lia].
pose proof (page_round_bounds (N + IB + UNIT) ltac:(unfold IB, UNIT; lia)). unfold IB, UNIT in *. lia.
Qed.
Lemma prN_pal : forall m, 0 <= m <= PALMAX -> 0 <= prN m <= PALSLACK.
Proof.
intros m Hm. unfold prN, PALSLACK. destruct (MMAP_THRESHOLD <? m); [|lia].
pose proof (page_round_bounds (m + IB + UNIT) ltac:(unfold IB, UNIT; lia)).
pose proof (page_round_mono (m + IB + UNIT) (PALMAX + IB + UNIT) ltac:(lia)).
assert (page_round (PALMAX + IB + UNIT) = 200704) by reflexivity. unfold IB, UNIT, PALMAX in *. lia.
Qed.
Lemma lzw_peak_le : forall N, 0 <= N <= 100000000 -> 0 <= lzw_peak N <= 402300000.
Proof. intros N HN. unfold lzw_peak. pose proof (page_round_bounds (2 * N + 2 ^ 16) ltac:(lia)). lia. Qed.
Lemma flush_peak_le : forall N, 0 <= N <= 100000000 -> 0 <= flush_peak N <= 702400000.
Proof. intros N HN. unfold flush_peak, rawadd_peak. pose proof (lzw_peak_le N HN). pose proof (prN_le N HN). lia. Qed.
Lemma rb_free_le_trans : forall b b' n, rb_le b b' -> rb_le (rb_free b n) b'.
Proof. intros b b' n H. eapply rb_le_trans; [apply rb_free_le | exact H]. Qed.
Section a.
Variable b0 : rbound.
Variable plen N : Z.
Hypothesis HROOM : ff_room b0 plen.
Hypothesis HN : 1 <= N <= 100000000.
Lemma site_room : forall b n, rb_le b (ff_peak b0) -> 0 <= n <= FF_MAXREQ -> room b n.
Proof. intros b n Hb Hn. exact (room_mono b (ff_peak b0) n FF_MAXREQ Hb Hn HROOM). Qed.
Lemma ff_peak_acc : ff_peak b0 = rb_acc b0 FF_CALLS (3 * 2 ^ 29).
Proof. unfold ff_peak, rb_acc, FF_PEAK. f_equal; lia. Qed.
Ltac nums := cbv [rb_le rb_acc loop_bud loop_bud3 af_rb close_rb rfc_rb_fail newgif_rb ff_delta ITK NEWGIF_K AF_K CLOSE_K FLUSH_K RAWADD_K LZW_K PALSLACK FF_CALLS MMAX PGSZ
rb_bytes rb_cnt rb_hand rb_brk] in *.
Lemma loop_af_room : forall bc k q, 1 <= k <= 16 -> 0 <= q <= 3 -> rb_le bc (loop_bud b0 N k q) -> af_room bc N.
Proof.
intros bc k q Hk Hq Hle. pose proof (prN_le N ltac:(lia)) as P. pose proof (flush_peak_le N ltac:(lia)) as F.
unfold af_room. apply site_room; [| unfold flush_maxreq, rawadd_maxreq, lzw_maxreq, FF_MAXREQ, PALMAX; lia].
rewrite ff_peak_acc. destruct Hle as (L1 & L2 & L3 & L4). nums. nia.
Qed.
Lemma loop_to_bud3 : forall bc k q q1, 0 <= q <= 3 -> 0 <= q1 <= 3 -> rb_le bc (loop_bud b0 N k q) ->
rb_le (rb_free (af_rb bc N q q1) N) (loop_bud3 b0 N k q1).
Proof.
intros bc k q q1 Hq Hq1 Hle. pose proof (prN_le N ltac:(lia)) as P.
eapply rb_le_trans; [apply rb_free_acc|]. destruct Hle as (L1 & L2 & L3 & L4). nums. nia.
Qed.
Lemma bud3_close_room : forall bc3 k q1, 1 <= k <= 16 -> 0 <= q1 <= 3 -> rb_le bc3 (loop_bud3 b0 N k q1) -> close_room bc3 N.
Proof.
intros bc3 k q1 Hk Hq Hle. pose proof (prN_le N ltac:(lia)) as P. pose proof (flush_peak_le N ltac:(lia)) as F.
unfold close_room. apply site_room; [| unfold flush_maxreq, rawadd_maxreq, lzw_maxreq, FF_MAXREQ, PALMAX; lia].
rewrite ff_peak_acc. destruct Hle as (L1 & L2 & L3 & L4). nums. nia.
Qed.
Lemma bud3_close_fin : forall bc3 k q1, 1 <= k <= 16 -> 0 <= q1 <= 3 -> rb_le bc3 (loop_bud3 b0 N k q1) ->
rb_le (close_rb bc3 N q1) (ff_delta plen b0).
Proof.
intros bc3 k q1 Hk Hq Hle. pose proof (prN_le N ltac:(lia)) as P. destruct Hle as (L1 & L2 & L3 & L4). nums. nia.
Qed.
Lemma bud3_rfc_room : forall bc3 k q1, 1 <= k <= 16 -> 0 <= q1 <= 3 -> rb_le bc3 (loop_bud3 b0 N k q1) -> rfc_room bc3 N.
Proof.
intros bc3 k q1 Hk Hq Hle. pose proof (prN_le N ltac:(lia)) as P.
unfold rfc_room. apply site_room; [| unfold FF_MAXREQ, PALMAX; lia].
rewrite ff_peak_acc. destruct Hle as (L1 & L2 & L3 & L4). nums. nia.
Qed.
Lemma bud3_rfc_fail : forall bc3 k q1, 1 <= k <= 16 -> 0 <= q1 <= 3 -> rb_le bc3 (loop_bud3 b0 N k q1) ->
close_room (rfc_rb_fail bc3) N /\ rb_le (close_rb (rfc_rb_fail bc3) N q1) (ff_delta plen b0).
Proof.
intros bc3 k q1 Hk Hq Hle. pose proof (prN_le N ltac:(lia)) as P. pose proof (flush_peak_le N ltac:(lia)) as F. split.
- unfold close_room. apply site_room; [| unfold flush_maxreq, rawadd_maxreq, lzw_maxreq, FF_MAXREQ, PALMAX; lia].
rewrite ff_peak_acc. destruct Hle as (L1 & L2 & L3 & L4). nums. nia.
- destruct Hle as (L1 & L2 & L3 & L4). nums. nia.
Qed.
Lemma bud3_rfc_ok : forall bc3 k q1 fattr nlp, 2 <= k <= 16 -> 0 <= q1 <= 3 -> 0 <= nlp <= 65535 -> rb_le bc3 (loop_bud3 b0 N k q1) ->
rb_le (rfc_rb_ok bc3 fattr nlp N) (loop_bud b0 N (k - 1) q1).
Proof.
intros bc3 k q1 fattr nlp Hk Hq Hn Hle. pose proof (prN_le N ltac:(lia)) as P. pose proof (prN_pal (3 * nlp) ltac:(unfold PALMAX; lia)) as Q.
unfold rfc_rb_ok. eapply rb_le_trans; [apply rb_malloc_acc; lia|].
assert (Hin : rb_le (if Z.land fattr 1 =? 0 then bc3 else rb_malloc bc3 (3 * nlp)) (rb_acc bc3 1 PALSLACK)).
{ destruct (Z.land fattr 1 =? 0).
- apply rb_acc_le; unfold PALSLACK; lia.
- eapply rb_le_trans; [apply rb_malloc_acc; lia|]. apply rb_acc_mono; [apply rb_le_refl | lia | lia]. }
destruct Hle as (L1 & L2 & L3 & L4). destruct Hin as (M1 & M2 & M3 & M4). nums. nia.
Qed.
End a.
Definition main_bud (b0 : rbound) : rbound := rb_acc b0 1 PALSLACK.
Definition main_bud2 (b0 : rbound) : rbound := rb_acc b0 (1 + NEWGIF_K) (2 * PALSLACK).
Section c.
Variable b0 : rbound.
Variable plen : Z.
Hypothesis HROOM : ff_room b0 plen.
Ltac nums := cbv [rb_le rb_acc loop_bud loop_bud3 main_bud main_bud2 af_rb close_rb rfc_rb_fail newgif_rb ff_delta ITK NEWGIF_K AF_K CLOSE_K FLUSH_K RAWADD_K LZW_K PALSLACK FF_CALLS MMAX PGSZ
rb_bytes rb_cnt rb_hand rb_brk] in *.
Lemma hdr_pal_room : forall m, 0 <= m <= PALMAX -> room b0 m.
Proof.
intros m Hm. apply (site_room b0 plen HROOM); [| unfold FF_MAXREQ, PALMAX in *; lia].
rewrite ff_peak_acc. pose proof (rb_le_refl b0) as (L1 & L2 & L3 & L4). nums. lia.
Qed.
Lemma hdr_pal_bud : forall m, 0 <= m <= PALMAX -> rb_le (rb_malloc b0 m) (main_bud b0).
Proof.
intros m Hm. pose proof (prN_pal m Hm) as Q. eapply rb_le_trans; [apply rb_malloc_acc; lia|]. unfold main_bud. apply rb_acc_mono; [apply rb_le_refl | lia | lia].
Qed.
Lemma hdr_nopal_bud : rb_le b0 (main_bud b0).
Proof. unfold main_bud. apply rb_acc_le; unfold PALSLACK; lia. Qed.
Lemma main_bud_fin : forall bc, rb_le bc (main_bud b0) -> rb_le bc (ff_delta plen b0).
Proof. intros bc (L1 & L2 & L3 & L4). nums. lia. Qed.
Lemma b0_fin : rb_le b0 (ff_delta plen b0).
Proof. exact (main_bud_fin b0 hdr_nopal_bud). Qed.
Lemma main_newgif_room : forall bc, rb_le bc (main_bud b0) -> newgif_room bc.
Proof.
intros bc Hle. unfold newgif_room. apply (site_room b0 plen HROOM); [| unfold FF_MAXREQ, PALMAX; lia].
rewrite ff_peak_acc. destruct Hle as (L1 & L2 & L3 & L4). nums. lia.
Qed.
Lemma main_to_bud2 : forall bc, rb_le bc (main_bud b0) -> rb_le (newgif_rb bc) (main_bud2 b0).
Proof. intros bc (L1 & L2 & L3 & L4). nums. lia. Qed.
Lemma main_to_bud2_free : forall bc n, rb_le bc (main_bud b0) -> rb_le (rb_free (newgif_rb bc) n) (main_bud2 b0).
Proof. intros bc n Hle. apply rb_free_le_trans. apply main_to_bud2. exact Hle. Qed.
Lemma main_bud2_fin : forall bc2, rb_le bc2 (main_bud2 b0) -> rb_le bc2 (ff_delta plen b0).
Proof. intros bc2 (L1 & L2 & L3 & L4). nums. lia. Qed.
Variable N : Z.
Hypothesis HN : 1 <= N <= 100000000.
Lemma main_rfc_room : forall bc2, rb_le bc2 (main_bud2 b0) -> rfc_room bc2 N.
Proof.
intros bc2 Hle. pose proof (prN_le N ltac:(lia)) as P.
unfold rfc_room. apply (site_room b0 plen HROOM); [| unfold FF_MAXREQ, PALMAX; lia].
rewrite ff_peak_acc. destruct Hle as (L1 & L2 & L3 & L4). nums. nia.
Qed.
Lemma main_rfc_fail : forall bc2, rb_le bc2 (main_bud2 b0) ->
close_room (rfc_rb_fail bc2) N /\ rb_le (close_rb (rfc_rb_fail bc2) N 0) (ff_delta plen b0).
Proof.
intros bc2 Hle. pose proof (prN_le N ltac:(lia)) as P. pose proof (flush_peak_le N ltac:(lia)) as F. split.
- unfold close_room. apply (site_room b0 plen HROOM); [| unfold flush_maxreq, rawadd_maxreq, lzw_maxreq, FF_MAXREQ, PALMAX; lia].
rewrite ff_peak_acc. destruct Hle as (L1 & L2 & L3 & L4). nums. nia.
- destruct Hle as (L1 & L2 & L3 & L4). nums. nia.
Qed.
Lemma main_rfc_ok : forall bc2 fattr nlp, rb_le bc2 (main_bud2 b0) -> 0 <= nlp <= 65535 ->
rb_le (rfc_rb_ok bc2 fattr nlp N) (loop_bud b0 N 16 0).
Proof.
intros bc2 fattr nlp Hle Hn. pose proof (prN_le N ltac:(lia)) as P. pose proof (prN_pal (3 * nlp) ltac:(unfold PALMAX; lia)) as Q.
unfold rfc_rb_ok. eapply rb_le_trans; [apply rb_malloc_acc; lia|].
assert (Hin : rb_le (if Z.land fattr 1 =? 0 then bc2 else rb_malloc bc2 (3 * nlp)) (rb_acc bc2 1 PALSLACK)).
{ destruct (Z.land fattr 1 =? 0).
- apply rb_acc_le; unfold PALSLACK; lia.
- eapply rb_le_trans; [apply rb_malloc_acc; lia|]. apply rb_acc_mono; [apply rb_le_refl | lia | lia]. }
destruct Hle as (L1 & L2 & L3 & L4). destruct Hin as (M1 & M2 & M3 & M4). nums. nia.
Qed.
End c.
