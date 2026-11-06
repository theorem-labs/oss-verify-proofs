(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep Asn1Aux.
Import ListNotations.
Open Scope Z_scope.

Lemma statics_ok_heap_presx : forall segs L LB SP X m m',
  statics_ok segs L m -> heap_presx segs L LB SP X m m' ->
  (forall a, hl_static L a -> hl_written L a) ->
  (forall a, hl_data_lo L <= a < hl_data_hi L -> ~ hl_written L a -> outside X a) ->
  statics_ok segs L m'.
Proof.
  intros segs L LB SP X m m' (H0 & H1 & HP) PR SW HX. split; [exact H0|]. split; [exact H1|]. intros a Ha HE.
  destruct (PR a ltac:(lia) ltac:(right; left; split; [exact Ha| intros HS; exact (HE (SW _ HS))]) (HX a Ha HE)) as [E _].
  rewrite E. exact (HP a Ha HE).
Qed.
