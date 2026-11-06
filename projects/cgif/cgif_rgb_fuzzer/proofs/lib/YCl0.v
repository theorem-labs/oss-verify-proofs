(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14 YP15.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Lemma g_ts_rank_next : forall T, In T ts_chain -> T < MAX_TABLE_SIZE -> g_ts_rank (getNextPrimePower2 T) = g_ts_rank T + 1.
Proof.
intros T HT Hlt. cbv [ts_chain In] in HT.
repeat (destruct HT as [<-|HT]; [first [ vm_compute; reflexivity | exfalso; revert Hlt; vm_compute; discriminate ]|]). destruct HT.
Qed.
Lemma g_rehash_zsum : forall H ent, ht_inv H ent -> zsum (map snd (ents_below H (ht_T H))) = zsum (map snd ent).
Proof. intros H ent Hinv. symmetry. apply perm_zsum. exact (rehash_done H ent Hinv). Qed.
