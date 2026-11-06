(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sd_draws (pl : list Z) (n : Z) : Z * Z * Z :=
  let '(rem, eff) := reserve_data_prefix pl n in
  let '(buf, eff') := uint32Range (skipn (Z.to_nat rem) pl) eff 0 (10 * rem) in
  (rem, buf, eff').

(* [comment removed for export] *)
Definition sd_src_size (pl : list Z) : Z := let '(rem, _, _) := sd_draws pl (Zlength pl) in rem.
(* [comment removed for export] *)
Definition sd_buf_size (pl : list Z) : Z := let '(_, buf, _) := sd_draws pl (Zlength pl) in buf.

Lemma sd_draws_range pl n : 0 <= n <= 2^26 ->
  let '(rem, buf, eff') := sd_draws pl n in 0 <= rem <= n /\ 0 <= buf <= 10 * rem /\ 0 <= eff' <= n - rem.
Proof.
  intros H. unfold sd_draws.
  pose proof (reserve_data_prefix_range pl n ltac:(change (2^32) with 4294967296; change (2^26) with 67108864 in H; lia)) as R.
  destruct (reserve_data_prefix pl n) as [rem eff]. destruct R as (R1 & R2 & R3).
  change (2^26) with 67108864 in H.
  pose proof (uint32Range_range (skipn (Z.to_nat rem) pl) eff 0 (10 * rem) R2 ltac:(lia)
                ltac:(change (2^32) with 4294967296; lia) ltac:(change (2^32) with 4294967296; lia)) as U.
  destruct (uint32Range (skipn (Z.to_nat rem) pl) eff 0 (10 * rem)) as [buf eff']. lia.
Qed.

Lemma sd_buf_size_range pl : Zlength pl <= 2^26 -> 0 <= sd_buf_size pl <= 10 * 2^26.
Proof.
  intros H. unfold sd_buf_size. pose proof (sd_draws_range pl (Zlength pl) ltac:(unfold Zlength in *; lia)) as R.
  destruct (sd_draws pl (Zlength pl)) as [[rem buf] eff']. lia.
Qed.

Lemma sd_src_size_range pl : Zlength pl <= 2^26 -> 0 <= sd_src_size pl <= Zlength pl.
Proof.
  intros H. unfold sd_src_size. pose proof (sd_draws_range pl (Zlength pl) ltac:(unfold Zlength in *; lia)) as R.
  destruct (sd_draws pl (Zlength pl)) as [[rem buf] eff']. lia.
Qed.

Lemma sd_buf_le_src pl : Zlength pl <= 2^26 -> sd_buf_size pl <= 10 * sd_src_size pl.
Proof.
  intros H. unfold sd_buf_size, sd_src_size. pose proof (sd_draws_range pl (Zlength pl) ltac:(unfold Zlength in *; lia)) as R.
  destruct (sd_draws pl (Zlength pl)) as [[rem buf] eff']. lia.
Qed.
