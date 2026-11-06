(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec StreamSim StoreOk.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import Reloc.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive cval :=
| CV_lit (z : Z)                    (* [comment removed for export] *)
| CV_rl (X : positive) (t : Z)      (* [comment removed for export] *)
| CV_rel (X : positive) (t : Z) (Y : positive) (u : Z)
                                    (* [comment removed for export] *)
| CV_bytes (bs : list Z).           (* [comment removed for export] *)

Record ccell := mkCell { ce_blk : positive; ce_addr : Z; ce_n : nat; ce_val : cval }.

Section Cells.
Context {RL : Reloc}.

Definition cell_bytes (n : nat) (v : cval) : list byte :=
  match v with
  | CV_lit z => word_to_le_bytes n (Z_to_bv 64 z)
  | CV_rl X t => word_to_le_bytes n (rl (rl_delta X) t)
  | CV_rel X t Y u => word_to_le_bytes n (Z_to_bv 64 ((t + rl_delta X) - (u + rl_delta Y)))
  | CV_bytes bs => map (Z_to_bv 8) bs
  end.

Definition bytes_eqb (l1 l2 : list byte) : bool :=
  (Nat.eqb (length l1) (length l2)) && forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p))) (combine l1 l2).

Lemma bytes_eqb_true : forall l1 l2, bytes_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; try reflexivity;
    unfold bytes_eqb in H; cbn [length Nat.eqb andb] in H; try discriminate H.
  cbn [combine forallb fst snd] in H.
  apply andb_prop in H as [Hl H]. apply andb_prop in H as [Hx H]. apply Z.eqb_eq in Hx.
  f_equal; [apply bv_eq; exact Hx | apply IH; unfold bytes_eqb; rewrite Hl; exact H].
Qed.

Definition cell_ok (c : ccell) : bool :=
  match rdn rl_segs (fun _ => None) (rl (rl_delta (ce_blk c)) (ce_addr c)) (ce_n c) with
  | Some bs => bytes_eqb bs (cell_bytes (ce_n c) (ce_val c))
  | None => false
  end.

Definition cells_check (tbl : list ccell) : bool := forallb cell_ok tbl.

Theorem cell_fact : forall tbl, cells_check tbl = true -> forall i c, nth_error tbl i = Some c ->
  rdn rl_segs (fun _ => None) (rl (rl_delta (ce_blk c)) (ce_addr c)) (ce_n c) = Some (cell_bytes (ce_n c) (ce_val c)).
Proof.
  intros tbl Hok i c Hi. unfold cells_check in Hok. rewrite forallb_forall in Hok.
  pose proof (Hok c (nth_error_In _ _ Hi)) as H. unfold cell_ok in H.
  destruct (rdn rl_segs (fun _ => None) (rl (rl_delta (ce_blk c)) (ce_addr c)) (ce_n c)) as [bs|]; [|discriminate H].
  f_equal. exact (bytes_eqb_true _ _ H).
Qed.
End Cells.

(* [comment removed for export] *)
Class RelocData (RL : Reloc) := {
  rl_data_lo : Z;                      (* [comment removed for export] *)
  rl_data_ok : (0 <=? rl_data_lo) && (rl_data_lo <=? rl_img_hi) && (rl_img_hi <=? 2^32) = true;
  rl_data_wseg : wseg_ok rl_segs (Z_to_bv 64 rl_data_lo) (Z.to_nat (rl_img_hi - rl_data_lo)) = true
}.

Lemma rl_store_ok_data : forall {RL : Reloc} {RD : RelocData RL} m (a : word) n,
  rl_data_lo <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= rl_img_hi ->
  store_ok rl_segs m a n = true.
Proof.
  intros RL RD m a n Hlo Hhi.
  pose proof rl_data_ok as H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  eapply (store_ok_window rl_segs m (Z_to_bv 64 rl_data_lo) a (Z.to_nat (rl_img_hi - rl_data_lo)) n rl_data_lo rl_img_hi);
    [ apply Z_to_bv_small; change (bv_modulus 64) with (2^64); lia | lia | lia | exact rl_data_wseg | exact Hlo | exact Hhi ].
Qed.
