(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxSemB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma bytes_at_rd : forall m0 A bs i, bytes_at BSEGS m0 A bs -> 0 <= i < Z.of_nat (length bs) -> mrd BSEGS m0 (wa (A + i)) <> None.
Proof.
  intros m0 A bs i (B1 & B2 & B3) Hi. pose proof (B3 (Z.to_nat i) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia. rewrite X.
  apply nth_error_Some. lia.
Qed.

Lemma digp_extend : forall m0 a x p T bs,
  digp m0 a x -> bytes_at BSEGS m0 T bs -> T <= x -> x <= p -> p <= T + Z.of_nat (length bs) -> digs bs (x - T) (p - T) ->
  digp m0 a p.
Proof.
  intros m0 a x p T bs (Td & bsd & HBd & (Ha1 & Ha2) & Hb & HDd) HB HT Hxp Hp HD.
  pose proof HBd as (D1 & D2 & _). pose proof HB as (C1 & C2 & _).
  destruct (bytes_exist BSEGS m0 Td (Z.to_nat (p - Td)) D1 ltac:(rewrite Z2Nat.id by lia; lia)) as (bu & HBu & Hlu).
  { intros i Hi. destruct (Z_lt_ge_dec (Td + Z.of_nat i) (Td + Z.of_nat (length bsd))) as [H1|H1].
    - apply (bytes_at_rd m0 Td bsd (Z.of_nat i) HBd). lia.
    - replace (Td + Z.of_nat i) with (T + (Td + Z.of_nat i - T)) by ring. apply (bytes_at_rd m0 T bs _ HB). lia. }
  assert (Hlu' : Z.of_nat (length bu) = p - Td) by (rewrite Hlu, Z2Nat.id by lia; reflexivity).
  exists Td, bu. split; [exact HBu|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_ge_dec (Td + i) x) as [H1|H1].
  - pose proof (tx_transport m0 Td bu Td bsd (Td + i) HBu HBd ltac:(lia) ltac:(lia)) as X.
    replace (Td + i - Td) with i in X by ring. unfold isdig. rewrite X. apply HDd. lia.
  - pose proof (tx_transport m0 Td bu T bs (Td + i) HBu HB ltac:(lia) ltac:(lia)) as X.
    replace (Td + i - Td) with i in X by ring. unfold isdig. rewrite X. apply HD. lia.
Qed.
