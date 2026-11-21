(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import FillWinModel BitsModel SendModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition vsize (s : deflate_state) : Z := 8 * ds_pending s + ds_bi_valid s.

Lemma send_bits_size : forall s v l, vsize (send_bits s v l) = vsize s + l.
Proof.
  intros s v l. unfold vsize, send_bits, Buf_size, put_short, put_byte.
  destruct (Z.ltb_spec (16 - l) (ds_bi_valid s)); dsred; lia.
Qed.


Fixpoint sumlen (cs : list (Z * Z)) : Z :=
  match cs with [] => 0 | (_, l) :: r => l + sumlen r end.

Lemma sumlen_app : forall a b, sumlen (a ++ b) = sumlen a + sumlen b.
Proof. induction a as [|[v l] a IH]; intros b; cbn; [reflexivity|]. rewrite IH. lia. Qed.

Lemma sbs_size : forall cs s, vsize (sbs_run s cs) = vsize s + sumlen cs.
Proof. induction cs as [|[v l] cs IH]; intros s; cbn; [lia|]. rewrite IH, send_bits_size. lia. Qed.


Definition lens_ok (cs : list (Z * Z)) : Prop := Forall (fun vl => 0 <= snd vl <= 16) cs.

Lemma sumlen_nonneg : forall cs, lens_ok cs -> 0 <= sumlen cs.
Proof. induction cs as [|[v l] cs IH]; intros H; cbn; [lia|]. inversion H; subst. cbn in *. specialize (IH H3). lia. Qed.

Lemma sbs_ok_of_total : forall PBL cs s,
  BINV PBL s -> lens_ok cs -> vsize s + sumlen cs <= 8 * PBL -> sbs_ok PBL s cs.
Proof.
  intros PBL cs. induction cs as [|[v l] cs IH]; intros s HB HL HT; cbn; [exact I|].
  inversion HL; subst. cbn in H1. cbn in HT.
  pose proof (sumlen_nonneg cs H2) as SN.
  assert (R : sb_room PBL s l).
  { unfold sb_room, Buf_size. intros C. unfold vsize in HT. destruct HB as (B1 & B2 & B3). lia. }
  split; [exact H1|]. split; [exact R|].
  apply IH; [apply send_bits_BINV; assumption | exact H2 |]. rewrite send_bits_size. lia.
Qed.

Lemma sbs_BINV_total : forall PBL cs s,
  BINV PBL s -> lens_ok cs -> vsize s + sumlen cs <= 8 * PBL ->
  BINV PBL (sbs_run s cs) /\ vsize (sbs_run s cs) = vsize s + sumlen cs.
Proof.
  intros PBL cs s HB HL HT. split; [apply sbs_BINV; [exact HB | apply sbs_ok_of_total; assumption] | apply sbs_size].
Qed.
