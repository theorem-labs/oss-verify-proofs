(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Definition digp (m0 : word -> option byte) (a b : Z) : Prop :=
  exists T bs, bytes_at BSEGS m0 T bs /\ T <= a <= b /\ b <= T + Z.of_nat (length bs) /\ digs bs (a - T) (b - T).
(* [comment removed for export] *)
Definition dotp (m0 : word -> option byte) (ie : Z) : Prop :=
  exists T bs, bytes_at BSEGS m0 T bs /\ T <= ie < T + Z.of_nat (length bs) /\ tx bs (ie - T) = 46.
(* [comment removed for export] *)
Definition spansp (m0 : word -> option byte) (ie fp fl pend : Z) : Prop :=
  (fp = 0 /\ fl = 0) \/
  (fp = ie + 1 /\ ie + 1 + fl <= pend /\
   exists T bs, bytes_at BSEGS m0 T bs /\ T <= ie /\ ie + 1 + fl <= T + Z.of_nat (length bs) /\
                tx bs (ie - T) = 46 /\ digs bs (ie + 1 - T) (ie + 1 + fl - T)).
Definition xok_spd (tag : nat) (args : list word) (m0 : word -> option byte) : Prop :=
  match tag, args with
  | 0%nat, [a; b] => digp m0 (bv_unsigned a) (bv_unsigned b)
  | 1%nat, [ie; fp; fl; pend] => spansp m0 (bv_unsigned ie) (bv_unsigned fp) (bv_unsigned fl) (bv_unsigned pend)
  | 2%nat, [ie] => dotp m0 (bv_unsigned ie)
  | _, _ => True
  end.

(* [comment removed for export] *)
Lemma tx_transport : forall m0 T bs T' bs' k, bytes_at BSEGS m0 T bs -> bytes_at BSEGS m0 T' bs' ->
  T <= k < T + Z.of_nat (length bs) -> T' <= k < T' + Z.of_nat (length bs') -> tx bs (k - T) = tx bs' (k - T').
Proof.
  intros m0 T bs T' bs' k (B1 & B2 & B3) (C1 & C2 & C3) Hk Hk'.
  pose proof (B3 (Z.to_nat (k - T)) ltac:(lia)) as X. pose proof (C3 (Z.to_nat (k - T')) ltac:(lia)) as Y.
  rewrite Z2Nat.id in X, Y by lia. replace (T + (k - T)) with k in X by lia. replace (T' + (k - T')) with k in Y by lia.
  rewrite X in Y. unfold tx. rewrite <- (Z2Nat.id (k - T)) at 1 by lia. rewrite <- (Z2Nat.id (k - T')) at 1 by lia.
  rewrite !Nat2Z.id. rewrite (nth_error_nth' bs (Z_to_bv 8 0) (n := Z.to_nat (k - T))) in Y by lia.
  rewrite (nth_error_nth' bs' (Z_to_bv 8 0) (n := Z.to_nat (k - T'))) in Y by lia. injection Y as Y. rewrite Y. reflexivity.
Qed.
Lemma digs_transport : forall m0 T bs T' bs' a b, bytes_at BSEGS m0 T bs -> bytes_at BSEGS m0 T' bs' ->
  T <= a -> b <= T + Z.of_nat (length bs) -> T' <= a -> b <= T' + Z.of_nat (length bs') ->
  digs bs' (a - T') (b - T') -> digs bs (a - T) (b - T).
Proof.
  intros m0 T bs T' bs' a b HB HB' H1 H2 H3 H4 HD k Hk.
  pose proof (tx_transport m0 T bs T' bs' (T + k) HB HB' ltac:(lia) ltac:(lia)) as X.
  replace (T + k - T) with k in X by lia.
  unfold isdig. rewrite X. replace (T + k - T') with (k + T - T') by lia. apply HD. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_transport : forall m m0 T bs, bytes_at BSEGS m T bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m (wa (T + i)) = m0 (wa (T + i))) -> bytes_at BSEGS m0 T bs.
Proof.
  intros m m0 T bs (B1 & B2 & B3) Hm. split; [exact B1|]. split; [exact B2|]. intros i Hi.
  pose proof (B3 i Hi) as X. unfold mrd in *. rewrite <- (Hm (Z.of_nat i)) by lia. exact X.
Qed.
