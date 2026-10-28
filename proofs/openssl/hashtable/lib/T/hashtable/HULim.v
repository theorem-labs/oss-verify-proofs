(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Definition LIM : Z := 2 ^ 31.
Lemma LIM_ge : (2 ^ 31 <= LIM)%Z.
Proof. apply Z.le_refl. Qed.
Lemma LIM_val : LIM = 2147483648%Z.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma LIM_le_source : (LIM <= target_alloc_limit)%Z.
Proof. unfold LIM, target_alloc_limit. apply Z.leb_le. reflexivity. Qed.
Lemma LIM_le_target : (LIM <= target_alloc_limit)%Z.
Proof. unfold LIM, target_alloc_limit. apply Z.leb_le. reflexivity. Qed.
Lemma LIM_le_2g : (LIM <= 2 ^ 31)%Z.
Proof. apply Z.le_refl. Qed.
