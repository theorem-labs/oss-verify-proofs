(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Lemma f32_split3 : forall segs m A ws (n k : nat), (n + k <= length ws)%nat -> rw_cells segs m A (f32 ws) ->
rw_cells segs m A (f32 (firstn n ws))
/\ rw_cells segs m (A + 4 * Z.of_nat n) (f32 (firstn k (skipn n ws)))
/\ rw_cells segs m (A + 4 * Z.of_nat n + 4 * Z.of_nat k) (f32 (skipn (n + k) ws))
/\ length (firstn n ws) = n /\ length (firstn k (skipn n ws)) = k /\ length (skipn (n + k) ws) = (length ws - n - k)%nat.
Proof.
intros segs m A ws n k Hnk H.
destruct (f32_split segs m A ws n ltac:(lia) H) as [H1 H2].
destruct (f32_split segs m _ (skipn n ws) k ltac:(rewrite length_skipn; lia) H2) as [H3 H4].
rewrite skipn_skipn in H4. replace (k + n)%nat with (n + k)%nat in H4 by lia.
split; [exact H1|]. split; [exact H3|]. split; [exact H4|].
rewrite !length_firstn, !length_skipn. lia.
Qed.

Lemma f32_join3 : forall segs m A a b c,
rw_cells segs m A (f32 a) -> rw_cells segs m (A + 4 * Z.of_nat (length a)) (f32 b) ->
rw_cells segs m (A + 4 * Z.of_nat (length a) + 4 * Z.of_nat (length b)) (f32 c) ->
rw_cells segs m A (f32 (a ++ b ++ c)) /\ length (a ++ b ++ c) = (length a + length b + length c)%nat.
Proof.
intros segs m A a b c Ha Hb Hc. split; [| rewrite !length_app; lia].
apply f32_join; [exact Ha|]. apply f32_join; [exact Hb| exact Hc].
Qed.

Lemma f32_split_at : forall segs m A ws (i : nat), (i < length ws)%nat -> rw_cells segs m A (f32 ws) ->
exists x, nth_error ws i = Some x /\
rw_cells segs m A (f32 (firstn i ws)) /\ rw_cells segs m (A + 4 * Z.of_nat i) [C4 x]
/\ rw_cells segs m (A + 4 * Z.of_nat i + 4) (f32 (skipn (S i) ws)) /\ length (firstn i ws) = i.
Proof.
intros segs m A ws i Hi H.
first [ pose proof (f32_split3 segs m A ws i 1 ltac:(lia) H) as sfP_; sf_destruct 6%nat sfP_ as H1 H2 H3 L1 L2 L3 | sf_fb; destruct (f32_split3 segs m A ws i 1 ltac:(lia) H) as (H1 & H2 & H3 & L1 & L2 & L3) ].
destruct (skipn i ws) as [|x rest] eqn:E.
{ exfalso. pose proof (f_equal (@length _) E) as LE. rewrite length_skipn in LE. cbn in LE. lia. }
exists x. cbn [firstn] in H2. rewrite f32_cons, ?f32_nil in H2. change (f32 []) with (@nil cell) in H2.
split.
- rewrite <- (firstn_skipn i ws), E. rewrite nth_error_app2 by (rewrite length_firstn; lia).
rewrite length_firstn. replace (i - Nat.min i (length ws))%nat with 0%nat by lia. reflexivity.
- split; [exact H1|]. split; [exact H2|]. split; [| exact L1].
replace (4 * Z.of_nat 1) with 4 in H3 by lia. replace (i + 1)%nat with (S i) in H3 by lia. exact H3.
Qed.
Lemma f32_join_at : forall segs m A pre x post,
rw_cells segs m A (f32 pre) -> rw_cells segs m (A + 4 * Z.of_nat (length pre)) [C4 x] ->
rw_cells segs m (A + 4 * Z.of_nat (length pre) + 4) (f32 post) ->
rw_cells segs m A (f32 (pre ++ x :: post)) /\ length (pre ++ x :: post) = S (length pre + length post).
Proof.
intros segs m A pre x post H1 H2 H3. split; [| rewrite length_app; cbn; lia].
apply f32_join; [exact H1|]. rewrite f32_cons. change (C4 x :: f32 post) with ([C4 x] ++ f32 post).
apply rw_cells_join; [exact H2|]. cbn [cells_size csize Nat.add].
replace (A + 4 * Z.of_nat (length pre) + Z.of_nat 4) with (A + 4 * Z.of_nat (length pre) + 4) by lia. exact H3.
Qed.
