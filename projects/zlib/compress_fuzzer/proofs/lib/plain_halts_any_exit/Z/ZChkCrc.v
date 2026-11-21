(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkArith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BvAux.

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

Definition CF (c : Z) (d : list byte) (k : nat) : Z := crc_fold c (firstn k (bZ d)).

Lemma split8 : forall u, Z.lxor (Z.land u 255) (Z.shiftl (Z.shiftr u 8) 8) = u.
Proof.
  intro u. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec, Z.land_spec, Z.shiftl_spec by lia.
  replace 255 with (Z.ones 8) by reflexivity.
  destruct (Z.lt_ge_cases n 8) as [Hlt|Hge].
  - rewrite (Z.ones_spec_low 8 n) by lia.
    rewrite (Z.testbit_neg_r (Z.shiftr u 8) (n - 8)) by lia.
    destruct (Z.testbit u n); reflexivity.
  - rewrite (Z.ones_spec_high 8 n) by lia.
    rewrite Z.shiftr_spec by lia.
    replace (n - 8 + 8) with n by lia.
    destruct (Z.testbit u n); reflexivity.
Qed.

Definition ctidx (c b : Z) : Z := Z.land (Z.lxor c b) 255.

Definition ctabbyte (f : Z -> Z) (j : Z) : byte :=
  Z_to_bv 8 ((f (j / 4) / 2 ^ (8 * (j mod 4))) mod 256).

Definition ctabword (f : Z -> Z) (i : Z) : list byte :=
  [ctabbyte f (4 * i); ctabbyte f (4 * i + 1);
   ctabbyte f (4 * i + 2); ctabbyte f (4 * i + 3)].

