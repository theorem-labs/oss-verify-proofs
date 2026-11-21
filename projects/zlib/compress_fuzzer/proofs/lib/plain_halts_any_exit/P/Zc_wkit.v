(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep RMalloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Stdio ZApi ZHarness.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Zlib_iface Zh_kit Z_deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rev_append_rev' : forall (l l' : list Z), rev_append l l' = rev l ++ l'.
Proof. induction l as [|a l IH]; intros l'; cbn; [reflexivity|]. rewrite IH, <- app_assoc. reflexivity. Qed.
Lemma zlength_app' : forall (l1 l2 : list Z), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_rev' : forall (l : list Z), zlength (rev l) = zlength l.
Proof. intros. unfold zlength. rewrite length_rev. reflexivity. Qed.
Lemma to_bytes_app : forall l1 l2, to_bytes (l1 ++ l2) = to_bytes l1 ++ to_bytes l2.
Proof. intros. unfold to_bytes. apply map_app. Qed.
Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros. unfold to_bytes. symmetry. apply skipn_map. Qed.

Lemma Forall_skipn_ : forall (P : Z -> Prop) n (l : list Z), Forall P l -> Forall P (skipn n l).
Proof. intros P n l H. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. tauto. Qed.
Lemma zlength_zdrop' : forall (l : list Z) k, 0 <= k <= zlength l -> zlength (zdrop k l) = zlength l - k.
Proof. intros l k Hk. unfold zdrop, zlength in *. rewrite length_skipn. lia. Qed.

Lemma zstore0_app : forall (bs old : list Z), (length bs <= length old)%nat -> zstore old 0 bs = bs ++ skipn (length bs) old.
Proof.
  intros bs old HL. pose proof (Z_deflate.zstore_split bs [] old HL) as E. cbn [app length Z.of_nat] in E. exact E.
Qed.
Lemma outside_app : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[l h] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto. Qed.
Lemma outside_blocks : forall (L : list block) a, (forall b, In b L -> ~ (blk_addr b <= a < blk_addr b + blk_size b)) ->
  outside (map (fun b => (blk_addr b, blk_addr b + blk_size b)) L) a.
Proof.
  intros L a Hb. induction L as [|b L IH]; cbn [map outside]; [exact I|]. split.
  - pose proof (Hb b (or_introl eq_refl)). lia.
  - apply IH. intros b' Hb'. apply Hb. right. exact Hb'.
Qed.

Lemma swrap32_id' : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap. rewrite bv_wrap_small; [lia|].
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N (32 - 1)%N) with (2^31). change (2 ^ Z.of_N 32) with (2^32). lia.
Qed.
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply swrap32_id'. exact Hz. Qed.

Lemma wint_of_word : forall v : word, wint (bv_unsigned v) = v.
Proof.
  intros v. unfold wint, MallocRep.wz. pose proof (bv_unsigned_in_range 64 v) as Rv. change (bv_modulus 64) with (2^64) in Rv.
  rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.
