(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Cells Step.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section S.
Variable segs : list Segment.

Lemma rdn_bytes_at : forall n m a bs, rdn segs m (wa a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2^64 -> bytes_at segs m a bs.
Proof.
  induction n as [|n IH]; intros m a bs H Ha Hn.
  - cbn in H. inversion H; subst. split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
  - rewrite rdn_unfold in H. destruct (mrd segs m (wa a)) as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs m (wa a + 1) n) as [r|] eqn:Er; [|discriminate]. inversion H; subst bs; clear H.
    rewrite wa_succ in Er. specialize (IH m (a + 1) r Er ltac:(lia) ltac:(lia)) as (B0 & B1 & B2).
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i].
    + cbn [nth_error]. rewrite Z.add_0_r. exact Eb.
    + cbn [nth_error length] in *. rewrite <- (B2 i ltac:(lia)). f_equal. f_equal. lia.
Qed.

Lemma ro8_of_rdn : forall m A (v : word), rdn segs m (Z_to_bv 64 A) 8%nat = Some (word_to_le_bytes 8 v) -> 0 <= A -> A + 8 <= 2^64 ->
  ro_cells segs m A [C8 v].
Proof.
  intros m A v H HA HB. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply (rdn_bytes_at 8 m A); [exact H | lia | cbn; lia].
Qed.

Lemma ro1_of_rdn : forall m A (b : byte), rdn segs m (Z_to_bv 64 A) 1%nat = Some [b] -> 0 <= A -> A + 1 <= 2^64 ->
  ro_cells segs m A [C1 b].
Proof.
  intros m A b H HA HB. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply (rdn_bytes_at 1 m A); [exact H | lia | cbn; lia].
Qed.
End S.

