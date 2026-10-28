(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W3_gnlem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import I_strncmpw Fz_W3_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma strncmp_sz_bounds : forall n b1 b2, 0 < n -> 1 <= strncmp_sz n b1 b2 <= n.
Proof.
  intros n b1 b2 Hn. unfold strncmp_sz, strncmp_idx. pose proof (idx_aux_le (Z.to_nat n) b1 b2). lia.
Qed.

Lemma strncmp_res_range : forall n b1 b2, strncmp_res n b1 b2 = 0 \/ strncmp_res n b1 b2 = 1 \/ strncmp_res n b1 b2 = -1.
Proof.
  intros n b1 b2. unfold strncmp_res. destruct (strncmp_idx n b1 b2 =? n); [left; reflexivity|].
  destruct (nth_error b1 _); [| left; reflexivity]. destruct (nth_error b2 _); [| left; reflexivity].
  destruct (_ <? _); [right; right; reflexivity|]. destruct (_ <? _); [right; left; reflexivity| left; reflexivity].
Qed.
(* [comment removed for export] *)
Lemma strncmp_reg : forall n b1 b2, bv_unsigned (Z_to_bv 64 (strncmp_res n b1 b2)) = 0 <-> strncmp_res n b1 b2 = 0.
Proof.
  intros n b1 b2. destruct (strncmp_res_range n b1 b2) as [E|[E|E]]; rewrite E; cbn; split; intros H; try reflexivity; try discriminate; exact H.
Qed.

Lemma nth_error_firstn_lt' : forall (l : list byte) j i, (i < j)%nat -> nth_error (firstn j l) i = nth_error l i.
Proof.
  induction l as [|a l IH]; intros [|j] [|i] H; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

(* [comment removed for export] *)
Lemma first_diff : forall (l1 l2 : list byte), length l1 = length l2 -> l1 <> l2 ->
  exists k x y, nth_error l1 k = Some x /\ nth_error l2 k = Some y /\ x <> y /\ (forall j, (j < k)%nat -> nth_error l1 j = nth_error l2 j).
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] LEN NE; cbn in LEN; try discriminate; [exfalso; exact (NE eq_refl)|].
  destruct (decide (a = b)) as [->|NE1].
  - destruct (IH l2 ltac:(lia) ltac:(intros E; apply NE; rewrite E; reflexivity)) as (k & x & y & H1 & H2 & H3 & H4).
    exists (S k), x, y. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. intros [|j] Hj; [reflexivity| apply H4; lia].
  - exists 0%nat, a, b. split; [reflexivity|]. split; [reflexivity|]. split; [exact NE1|]. intros j Hj. lia.
Qed.

(* [comment removed for export] *)
Lemma sc_lit_zero : forall (lit b1 rest : list byte),
  (forall j z, nth_error lit j = Some z -> bv_unsigned z <> 0) -> (length lit <= length b1)%nat ->
  strncmp_res (Z.of_nat (length lit)) b1 (lit ++ Z_to_bv 8 0 :: rest) = 0 -> firstn (length lit) b1 = lit.
Proof.
  intros lit b1 rest NZ LEN RES. set (n := length lit) in *.
  destruct (decide (firstn n b1 = lit)) as [E|NE]; [exact E| exfalso].
  destruct (first_diff (firstn n b1) lit ltac:(rewrite firstn_length_le; [reflexivity| exact LEN]) NE) as (k & x & y & H1 & H2 & H3 & H4).
  assert (HK : (k < n)%nat) by (apply (proj1 (nth_error_Some lit k)); rewrite H2; discriminate).
  rewrite nth_error_firstn_lt' in H1 by exact HK.
  assert (PRE : sc_pre b1 (lit ++ Z_to_bv 8 0 :: rest) k).
  { intros j Hj. pose proof (H4 j Hj) as E. rewrite nth_error_firstn_lt' in E by lia.
    destruct (nth_error lit j) as [z|] eqn:EZ; [| apply nth_error_None in EZ; lia].
    exists z. split; [exact E|]. split; [rewrite nth_error_app1 by lia; exact EZ| exact (NZ j z EZ)]. }
  assert (H2' : nth_error (lit ++ Z_to_bv 8 0 :: rest) k = Some y) by (rewrite nth_error_app1 by lia; exact H2).
  assert (NXY : bv_unsigned x <> bv_unsigned y) by (intros E; apply H3; apply bv_eq; exact E).
  destruct (res_break (Z.of_nat n) b1 (lit ++ Z_to_bv 8 0 :: rest) k x y ltac:(lia) ltac:(rewrite Nat2Z.id; exact HK) PRE H1 H2' (or_introl NXY)) as [_ R].
  rewrite RES in R. unfold cmpx in R. destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); [discriminate|].
  destruct (Z.ltb_spec (bv_unsigned y) (bv_unsigned x)); [discriminate| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pem_begin_strA : list byte := Eval vm_compute in (match image_bytes asegs LIT_BEGIN 11 with Some bs => bs | None => [] end).
Definition pem_tail6_strA : list byte := Eval vm_compute in (match image_bytes asegs LIT_TAIL 6 with Some bs => bs | None => [] end).
Lemma pem_begin_AP : pem_begin_strA = pem_begin_str. Proof. reflexivity. Qed.
Lemma pem_tail6_AP : pem_tail6_strA = pem_tail6_str. Proof. reflexivity. Qed.
Lemma pem_begin_roA : ro_bytes asegs LIT_BEGIN (pem_begin_str ++ [Z_to_bv 8 0]).
Proof. rewrite <- pem_begin_AP. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_tail6_roA : ro_bytes asegs LIT_TAIL (pem_tail6_str ++ [Z_to_bv 8 0]).
Proof. rewrite <- pem_tail6_AP. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_begin_bytes : forall m : word -> option byte, mem_inv asegs m -> bytes_at asegs m LIT_BEGIN (pem_begin_str ++ [Z_to_bv 8 0]).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold LIT_BEGIN; lia| rewrite app_length, pem_begin_len; unfold LIT_BEGIN; cbn; lia| exact pem_begin_roA]. Qed.
Lemma pem_tail6_bytes : forall m : word -> option byte, mem_inv asegs m -> bytes_at asegs m LIT_TAIL (pem_tail6_str ++ [Z_to_bv 8 0]).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold LIT_TAIL; lia| rewrite app_length, pem_tail6_len; unfold LIT_TAIL; cbn; lia| exact pem_tail6_roA]. Qed.
Lemma pem_begin_nonul' : forall j z, nth_error pem_begin_str j = Some z -> bv_unsigned z <> 0.
Proof. intros j z Hz. apply (pem_begin_nonul j z); [| exact Hz]. rewrite <- pem_begin_len. apply (proj1 (nth_error_Some _ j)). rewrite Hz. discriminate. Qed.
Lemma pem_tail6_nonul' : forall j z, nth_error pem_tail6_str j = Some z -> bv_unsigned z <> 0.
Proof. intros j z Hz. apply (pem_tail6_nonul j z); [| exact Hz]. rewrite <- pem_tail6_len. apply (proj1 (nth_error_Some _ j)). rewrite Hz. discriminate. Qed.

(* [comment removed for export] *)
Lemma gn_begin_prefix : forall (bs : list byte) rest,
  (11 <= length bs)%nat -> strncmp_res 11 bs (pem_begin_str ++ Z_to_bv 8 0 :: rest) = 0 -> firstn 11 bs = pem_begin_str.
Proof.
  intros bs rest LEN RES. rewrite <- pem_begin_len. apply (sc_lit_zero pem_begin_str bs rest pem_begin_nonul'); rewrite pem_begin_len; [exact LEN| exact RES].
Qed.
Lemma gn_tail_prefix : forall (bs : list byte) rest,
  (6 <= length bs)%nat -> strncmp_res 6 bs (pem_tail6_str ++ Z_to_bv 8 0 :: rest) = 0 -> firstn 6 bs = pem_tail6_str.
Proof.
  intros bs rest LEN RES. rewrite <- pem_tail6_len. apply (sc_lit_zero pem_tail6_str bs rest pem_tail6_nonul'); rewrite pem_tail6_len; [exact LEN| exact RES].
Qed.
