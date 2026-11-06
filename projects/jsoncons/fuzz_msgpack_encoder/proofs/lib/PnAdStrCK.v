(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQASCK.
Section Facts.
Variable segs : list Segment.

Lemma bytes_ok_app a b : NEM.bytes_ok a -> NEM.bytes_ok b -> NEM.bytes_ok (a ++ b).
Proof. intros Ha Hb. unfold NEM.bytes_ok in *. apply Forall_app. split; assumption. Qed.
Lemma ascii_bytes_ok bs : NEM.ascii bs -> NEM.bytes_ok bs.
Proof. unfold NEM.ascii, NEM.bytes_ok. intros H. eapply Forall_impl; [|exact H]. intros a Ha. cbn in Ha. lia. Qed.
Lemma ascii_app a b : NEM.ascii a -> NEM.ascii b -> NEM.ascii (a ++ b).
Proof. intros Ha Hb. unfold NEM.ascii in *. apply Forall_app. split; assumption. Qed.
(* [comment removed for export] *)
Lemma bytes_at_app M p a b :
  L5.bytes_at segs M p a -> L5.bytes_at segs M (p + Z.of_nat (length a)) b -> L5.bytes_at segs M p (a ++ b).
Proof.
  intros Ha Hb i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length a)) as [Hl|Hr].
  - rewrite app_nth1 by lia. apply Ha. exact Hl.
  - rewrite app_nth2 by lia. replace (p + Z.of_nat i) with (p + Z.of_nat (length a) + Z.of_nat (i - length a)) by lia. apply Hb. lia.
Qed.
Lemma bytes_at_snoc M p a c :
  L5.bytes_at segs M p a -> L5.u8_at segs M (p + Z.of_nat (length a)) c -> L5.bytes_at segs M p (a ++ [c]).
Proof. intros Ha Hc. apply bytes_at_app; [exact Ha|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth]. rewrite Z.add_0_r. exact Hc. Qed.
Lemma bytes_at_split M p a b :
  L5.bytes_at segs M p (a ++ b) -> L5.bytes_at segs M p a /\ L5.bytes_at segs M (p + Z.of_nat (length a)) b.
Proof.
  intros H. split; intros i Hi.
  - pose proof (H i ltac:(rewrite length_app; lia)) as X. rewrite app_nth1 in X by lia. exact X.
  - pose proof (H (length a + i)%nat ltac:(rewrite length_app; lia)) as X. rewrite app_nth2 in X by lia.
    replace (length a + i - length a)%nat with i in X by lia. replace (p + Z.of_nat (length a + i)) with (p + Z.of_nat (length a) + Z.of_nat i) in X by lia. exact X.
Qed.
(* [comment removed for export] *)
Lemma bytes_at_of_rdn M (bs : list byte) p : 0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 p) (length bs) = Some bs -> L5.bytes_at segs M p (map bv_unsigned bs) /\ NEM.bytes_ok (map bv_unsigned bs).
Proof.
  intros Hp Hn RD. split; [apply (L5C.rdn_bytes_at segs M bs p Hp Hn RD)|].
  unfold NEM.bytes_ok. apply Forall_forall. intros z Hz. apply in_map_iff in Hz. destruct Hz as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as X. cbn in X. unfold bv_modulus in X. cbn in X. lia.
Qed.
End Facts.
End PQASCK.
