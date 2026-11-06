(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ctab (c : Z) : Z :=
  (if is_space c then 1 else 0) + (if is_op c then 2 else 0)
  + (if (c <? 32) || (c =? 34) || (c =? 92) then 4 else 0) + (if 128 <=? c then 8 else 0).
Definition ctab_bytes : list byte := map (fun k => Z_to_bv 8 (ctab (Z.of_nat k))) (seq 0 256).



Lemma ctab_range : forall c, 0 <= ctab c <= 15.
Proof. intros c. unfold ctab. destruct (is_space c), (is_op c), ((c <? 32) || (c =? 34) || (c =? 92)), (128 <=? c); vm_compute; split; discriminate. Qed.

Lemma ctab_space : forall c, Z.land (ctab c) 1 = if is_space c then 1 else 0.
Proof. intros c. unfold ctab. destruct (is_space c), (is_op c), ((c <? 32) || (c =? 34) || (c =? 92)), (128 <=? c); reflexivity. Qed.
Lemma ctab_op : forall c, Z.land (ctab c) 2 = if is_op c then 2 else 0.
Proof. intros c. unfold ctab. destruct (is_space c), (is_op c), ((c <? 32) || (c =? 34) || (c =? 92)), (128 <=? c); reflexivity. Qed.
Lemma ctab_spop : forall c, Z.land (ctab c) 3 = 0 <-> (is_space c || is_op c) = false.
Proof. intros c. unfold ctab. destruct (is_space c), (is_op c), ((c <? 32) || (c =? 34) || (c =? 92)), (128 <=? c); vm_compute; split; congruence. Qed.
Lemma ctab_stop : forall c, Z.land (ctab c) 12 = 0 <-> is_ascii_stop c = false.
Proof.
  intros c. unfold ctab, is_ascii_stop. destruct (is_space c), (is_op c), ((c <? 32) || (c =? 34) || (c =? 92)), (128 <=? c); vm_compute; split; congruence.
Qed.

Lemma nth_ctab_bytes : forall c, 0 <= c < 256 -> nth_error ctab_bytes (Z.to_nat c) = Some (Z_to_bv 8 (ctab c)).
Proof.
  intros c Hc. unfold ctab_bytes. rewrite nth_error_map, nth_error_seq.
  replace (Z.to_nat c <? 256)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn [option_map]. rewrite Nat.add_0_l, Z2Nat.id by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition s1buf (d : list Z) : list byte := map (Z_to_bv 8) (d ++ repeat 0 64).

Lemma byte_at_app_zeros : forall d i, 0 <= i -> nth (Z.to_nat i) (d ++ repeat 0 64) 0 = byte_at d i.
Proof.
  intros d i Hi. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat i) (length d)) as [L|G].
  - rewrite app_nth1 by exact L. reflexivity.
  - rewrite app_nth2 by exact G. rewrite (nth_overflow d 0 G).
    destruct (Nat.lt_ge_cases (Z.to_nat i - length d) 64) as [L2|G2].
    + rewrite nth_repeat. reflexivity.
    + apply nth_overflow. rewrite repeat_length. exact G2.
Qed.



Lemma byte_at_range : forall d i, Forall (fun c => 0 <= c < 256) d -> 0 <= byte_at d i < 256.
Proof.
  intros d i H. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat i) (length d)) as [L|G].
  - rewrite Forall_forall in H. apply H. apply nth_In. exact L.
  - rewrite nth_overflow by exact G. lia.
Qed.




(* [comment removed for export] *)
Lemma byte_check : forall (p : Z -> bool), forallb p (map Z.of_nat (seq 0 256)) = true -> forall c, 0 <= c < 256 -> p c = true.
Proof.
  intros p H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma cont_signed : forall c, 0 <= c < 256 -> (bv_signed (Z_to_bv 8 c) <=? -65) = is_cont c.
Proof.
  intros c Hc. apply Bool.eqb_prop.
  exact (byte_check (fun c => Bool.eqb (bv_signed (Z_to_bv 8 c) <=? -65) (is_cont c)) ltac:(vm_compute; reflexivity) c Hc).
Qed.
Lemma cont_signed64 : forall c, 0 <= c < 256 -> (-64 <=? bv_signed (Z_to_bv 8 c)) = negb (is_cont c).
Proof.
  intros c Hc. apply Bool.eqb_prop.
  exact (byte_check (fun c => Bool.eqb (-64 <=? bv_signed (Z_to_bv 8 c)) (negb (is_cont c))) ltac:(vm_compute; reflexivity) c Hc).
Qed.
Lemma signed_byte_range : forall c, 0 <= c < 256 -> -128 <= bv_signed (Z_to_bv 8 c) < 128.
Proof.
  intros c Hc. pose proof (byte_check (fun c => (-128 <=? bv_signed (Z_to_bv 8 c)) && (bv_signed (Z_to_bv 8 c) <? 128)) ltac:(vm_compute; reflexivity) c Hc) as H.
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma unsigned_byte : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hc. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mbytes (M : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  forall i, 0 <= i < Z.of_nat (length bs) -> M (Z_to_bv 64 (a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).

Fixpoint u32bytes (l : list Z) : list byte :=
  match l with [] => [] | x :: r => word_to_le_bytes 4 (Z_to_bv 64 x) ++ u32bytes r end.

Lemma u32bytes_length : forall l, length (u32bytes l) = (4 * length l)%nat.
Proof. induction l as [|x l IH]; cbn [u32bytes length]; [reflexivity|]. rewrite length_app, IH. unfold word_to_le_bytes.
  rewrite length_Z_to_le_bytes. lia. Qed.

Lemma u32bytes_app : forall a b, u32bytes (a ++ b) = u32bytes a ++ u32bytes b.
Proof. induction a as [|x a IH]; intros b; cbn [u32bytes app]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma mbytes_frame : forall M M' a bs, (forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> M' x = M x) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> mbytes M a bs -> mbytes M' a bs.
Proof.
  intros M M' a bs HF H0 H1 H i Hi. rewrite HF; [exact (H i Hi)|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia. lia.
Qed.


