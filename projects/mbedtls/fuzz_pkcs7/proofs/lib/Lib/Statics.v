(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition pristine (lo hi : Z) (E : Z -> Prop) (m : mem) : Prop :=
  0 <= lo /\ hi <= 2^64 /\ forall a, lo <= a < hi -> ~ E a -> m (wa a) = None.

(* [comment removed for export] *)
Fixpoint img_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom segs (wa A) with
      | Some b' => bv_eqb b b' && img_bytes_b (A + 1) bs'
      | None => false
      end
  end.

#[using="Type"] Lemma pristine_bytes_at : forall lo hi E m A bs,
  pristine lo hi E m -> img_bytes_b A bs = true ->
  lo <= A -> A + Z.of_nat (length bs) <= hi ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> ~ E a) ->
  bytes_at segs m A bs.
Proof.
  intros lo hi E m A bs (Hlo & Hhi & HP) Hb HA Hl HE.
  split; [lia|]. split; [lia|].
  revert A Hb HA Hl HE. induction bs as [|b bs IH]; intros A Hb HA Hl HE i Hi; cbn in Hi; [lia|].
  cbn in Hb. destruct (seg_rom segs (wa A)) as [b'|] eqn:ER; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. unfold bv_eqb in Hb1. apply Z.eqb_eq in Hb1. apply bv_eq in Hb1. subst b'.
  destruct i as [|i].
  - cbn. rewrite Z.add_0_r. unfold mrd. rewrite (HP A) by (cbn in Hl; try lia; apply HE; cbn; lia). exact ER.
  - cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia.
    apply (IH (A + 1)); try assumption; cbn in Hl |- *; try lia.
    intros a Ha. apply HE. cbn. lia.
Qed.

#[using="Type"] Lemma pristine_cells : forall lo hi E m A bs,
  pristine lo hi E m -> img_bytes_b A bs = true ->
  lo <= A -> A + Z.of_nat (length bs) <= hi ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> ~ E a) ->
  ro_cells segs m A [CB (length bs) bs].
Proof.
  intros lo hi E m A bs HP Hb HA Hl HE. split.
  - cbn. split; [reflexivity|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. eapply pristine_bytes_at; eauto.
Qed.

#[using="Type"] Lemma pristine_write : forall lo hi E m (a : Z) (bs : list byte),
  pristine lo hi E m -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> a + i < lo \/ hi <= a + i \/ E (a + i)) ->
  pristine lo hi E (write_to_mem m (wa a) bs).
Proof.
  intros lo hi E m a bs (Hlo & Hhi & HP) Ha Hl HO. split; [lia|]. split; [lia|].
  intros x Hx HEx.
  rewrite (write_to_mem_spec bs m a (wa x)) by lia.
  rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb];
    try (apply HP; assumption).
  exfalso. destruct (HO (x - a) ltac:(lia)) as [?|[?|?]]; try lia.
  replace (a + (x - a)) with x in * by lia. contradiction.
Qed.

End WithSegs.

(* [comment removed for export] *)
