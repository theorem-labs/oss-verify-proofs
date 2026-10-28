(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_numkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition crs (t : list Z) : list Z := t ++ repeat 32%Z 64.

Lemma crs_blen : forall t, Z.of_nat (length (zbytes (crs t))) = (blen t + 64)%Z.
Proof. intros t. rewrite zbytes_length. unfold crs, blen. rewrite length_app, repeat_length. lia. Qed.

Lemma crs_bytes_ok : forall t, bytes_ok t -> bytes_ok (crs t).
Proof.
  intros t H. unfold bytes_ok, crs in *. apply Forall_app. split; [exact H|].
  apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. lia.
Qed.

Lemma Bc_lt : forall t q, (B (crs t) q <> 0)%Z -> (B (crs t) q <> 32)%Z -> (0 <= q)%Z -> (q < blen t)%Z.
Proof.
  intros t q H0 H32 Hq. destruct (Z_lt_dec q (blen t)) as [L|L]; [exact L|]. exfalso.
  unfold B, crs, blen in *.
  destruct (Nat.lt_ge_cases (Z.to_nat q) (length t + 64)) as [L2|L2].
  - rewrite app_nth2 in H32 by lia. apply H32. apply nth_repeat_lt. lia.
  - apply H0. apply nth_overflow. rewrite length_app, repeat_length. exact L2.
Qed.

Lemma cp_read_at : forall (m : mem) A l i a,
  bytes_at usegs m A (zbytes l) -> (0 <= i < Z.of_nat (length l))%Z -> a = wa (A + i) ->
  ov_read_bytes usegs m a 1 = Some [Z_to_bv 8 (B l i)].
Proof.
  intros m A l i a H Hi ->.
  eapply (u8ro_read usegs m A (zbytes l) i); [exact H | | lia | reflexivity].
  unfold B. apply nth_error_zbytes. lia.
Qed.

Ltac s2_load_cp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 1] =>
      lazymatch goal with
      | H : bytes_at segs m ?A (zbytes ?l) |- _ =>
          let Ea := addr_expr a in
          let idx := strip_base Ea A in
          rewrite (cp_read_at m A l idx a H ltac:(lia) ltac:(unfold wa; f_equal; lia))
      end
  end;
  load_post.
