(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Export LiaTuning.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Class MSEC : Type := {
  msecret : Z ;                          (* [comment removed for export] *)
  msecret_range : 0 <= msecret < 2^64 ;
  mcanary : bv 64                        (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Ltac msec_facts :=
  lazymatch goal with
  | X : MSEC |- _ => first [ pose proof (@msecret_range X) as MSECR__ | idtac ]
  | |- _ => idtac
  end.

(* [comment removed for export] *)
Definition msec_of_words (secretw canaryw : bv 64) : MSEC :=
  {| msecret := bv_unsigned secretw ;
     msecret_range := bv_unsigned_in_range 64 secretw ;
     mcanary := canaryw |}.

Lemma msecret_of_words : forall w c, @msecret (msec_of_words w c) = bv_unsigned w.
Proof. reflexivity. Qed.
Lemma mcanary_of_words : forall w c, @mcanary (msec_of_words w c) = c.
Proof. reflexivity. Qed.
