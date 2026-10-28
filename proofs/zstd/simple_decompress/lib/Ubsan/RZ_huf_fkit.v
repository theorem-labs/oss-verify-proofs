(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma div5_magic : forall x, 0 <= x < 2^64 -> x * 14757395258967641293 / 2^64 / 4 = x / 5.
Proof. intros x Hx. Z.div_mod_to_equations; lia. Qed.

Lemma div7_magic : forall x, 0 <= x < 2^64 ->
  ((x - x * 2635249153387078803 / 2^64) / 2 + x * 2635249153387078803 / 2^64) / 4 = x / 7.
Proof. intros x Hx. Z.div_mod_to_equations; lia. Qed.

(* [comment removed for export] *)
Definition HUF_CTZ_TBL : Z := 0x110b8.
Lemma huf_ctz_tbl : forall m, mem_inv usegs m -> tbl_in usegs m HUF_CTZ_TBL 64 1 0 0 63.
Proof.
  intros m MI. unfold HUF_CTZ_TBL.
  destruct (image_bytes usegs 0x110b8 64) as [bs|] eqn:EB; [|vm_compute in EB; discriminate EB].
  assert (LB : length bs = 64%nat) by exact (image_bytes_length usegs 64 _ _ EB).
  assert (HB : bytes_at usegs m 0x110b8 bs).
  { apply ro_bytes_at; [exact MI | lia | rewrite LB; lia |]. apply ro_bytes_b_sound.
    vm_compute in EB. injection EB as <-. vm_compute. reflexivity. }
  pose proof (tbl_in_bytes_at usegs m 0x110b8 bs 1 0 0 63 HB ltac:(lia) ltac:(lia)) as T. rewrite LB in T. apply T.
  intros i Hi Hs. vm_compute in EB. injection EB as <-.
  assert (Hn : (Z.to_nat (1 * i + 0) < 64)%nat) by lia.
  remember (Z.to_nat (1 * i + 0)) as k eqn:Ek. clear - Hn.
  do 64 (destruct k as [|k]; [eexists; split; [reflexivity | vm_compute; split; discriminate]|]). lia.
Qed.

(* [comment removed for export] *)
Fixpoint c8s_of (k : nat) (bs : list byte) : list cell :=
  match k with O => [] | S k' => C8 (le_bytes_to_word (firstn 8 bs)) :: c8s_of k' (skipn 8 bs) end.

Lemma c8s_of_props : forall k bs, length bs = (8 * k)%nat ->
  cells_wf (c8s_of k bs) /\ cells_bytes (c8s_of k bs) = bs /\ cells_size (c8s_of k bs) = (8 * k)%nat.
Proof.
  induction k as [|k IH]; intros bs HL.
  - destruct bs; [|discriminate]. cbn. repeat split; try constructor.
  - cbn [c8s_of]. assert (L2 : length (skipn 8 bs) = (8 * k)%nat) by (rewrite skipn_length; lia).
    destruct (IH _ L2) as (W & B & S'). split; [|split].
    + split; [exact I | exact W].
    + cbn [cells_bytes cbytes]. rewrite B, le8_of_bytes by (rewrite firstn_length; lia). apply firstn_skipn.
    + cbn [cells_size csize]. rewrite S'. lia.
Qed.

Lemma cb_as_c8s : forall m A (k : nat) bs, rw_cells usegs m A [CB (8 * k) bs] -> rw_cells usegs m A (c8s_of k bs).
Proof.
  intros m A k bs H. assert (HL : length bs = (8 * k)%nat).
  { destruct H as [[W _] _]. exact (proj1 W). }
  destruct (c8s_of_props k bs HL) as (W & B & S').
  apply (rw_cells_recast usegs m A _ _ H W).
  - rewrite B. cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - rewrite S'. cbn [cells_size csize]. lia.
Qed.

Lemma cb160_as_c8s : forall m A bs, rw_cells usegs m A [CB 160 bs] ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : word,
    rw_cells usegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                        C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19].
Proof.
  intros m A bs H. pose proof (cb_as_c8s m A 20 bs H) as H2. cbn [c8s_of] in H2.
  do 20 eexists. exact H2.
Qed.
