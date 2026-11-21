(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_tr_emit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma wrap16_eqm16 : forall V V', V' mod 2^16 = V mod 2^16 -> wrap16 V' = wrap16 V.
Proof. intros V V' H. rewrite !wrap16_mod. exact H. Qed.

Lemma nbv_eqm : forall BB k V V', V' mod 2^16 = V mod 2^16 -> nbv BB k V' = nbv BB k V.
Proof. intros BB k V V' H. unfold nbv. rewrite (wrap16_eqm16 V V' H). reflexivity. Qed.

Lemma cnt_eqm : forall c k, (c + 65535 - k) mod 2^16 = (c - (k + 1)) mod 2^16.
Proof.
  intros c k. replace (c + 65535 - k) with (c - (k + 1) + 1 * 2^16) by lia. apply Z.mod_add. lia.
Qed.
