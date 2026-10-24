(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem Cells Step.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Fixpoint ro_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom segs (wa A) with
      | Some b' => bv_eqb b b' && ro_addr segs (wa A) && ro_bytes_b (A + 1) bs'
      | None => false
      end
  end.

Lemma ro_bytes_b_sound : forall bs A, ro_bytes_b A bs = true -> ro_bytes segs A bs.
Proof.
  induction bs as [|b bs IH]; intros A H; cbn in *; [exact I|].
  destruct (seg_rom segs (wa A)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H3]. apply andb_prop in H1. destruct H1 as [H1 H2].
  unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
  split; [split; [exact E| exact H2]|]. apply IH. exact H3.
Qed.

Lemma ro_cells_image : forall m A bs,
  mem_inv segs m -> ro_bytes_b A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  ro_cells segs m A [CB (length bs) bs].
Proof.
  intros m A bs Hinv Hb HA Hl. split.
  - cbn. split; [reflexivity|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply ro_bytes_at; try assumption.
    apply ro_bytes_b_sound. exact Hb.
Qed.

(* [comment removed for export] *)
Fixpoint image_bytes (A : Z) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' => match seg_rom segs (wa A), image_bytes (A + 1) n' with
            | Some b, Some bs => Some (b :: bs)
            | _, _ => None
            end
  end.

Lemma image_bytes_length : forall n A bs, image_bytes A n = Some bs -> length bs = n.
Proof.
  induction n as [|n IH]; intros A bs H; cbn in H.
  - inversion H. reflexivity.
  - destruct (seg_rom segs (wa A)); [|discriminate]. destruct (image_bytes (A + 1) n) eqn:E; [|discriminate].
    inversion H. cbn. f_equal. eapply IH. exact E.
Qed.

End WithSegs.

(* [comment removed for export] *)
