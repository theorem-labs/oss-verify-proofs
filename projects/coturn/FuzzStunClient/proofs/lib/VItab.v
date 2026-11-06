(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition itab := pmap instr.

Definition dec_at (SEGS : list Segment) (pc : Z) : option instr :=
  match fetch_word SEGS (Z_to_bv 64 pc) with
  | Some w => if is_ecall w then None
              else match decode_any w with
                   | Some (i, sz) => if Z.eqb sz 4 then Some i else None
                   | None => None
                   end
  | None => None
  end.

Fixpoint build_itab (SEGS : list Segment) (pc : Z) (n : nat) (acc : itab) : itab :=
  match n with
  | O => acc
  | S n' => build_itab SEGS (pc + 4) n'
            (match dec_at SEGS pc with Some i => pm_set (Z.to_pos pc) i acc | None => acc end)
  end.

Definition itab_get (T : itab) (pc : Z) : option instr :=
  if Z.ltb 0 pc then pm_get (Z.to_pos pc) T else None.

Definition itab_ok (SEGS : list Segment) (T : itab) : Prop :=
  forall pc i, itab_get T pc = Some i ->
    exists w, fetch_word SEGS (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4).

Lemma dec_at_ok SEGS pc i :
  dec_at SEGS pc = Some i ->
  exists w, fetch_word SEGS (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4).
Proof.
  unfold dec_at. destruct (fetch_word SEGS (Z_to_bv 64 pc)) as [w|]; [|discriminate].
  destruct (is_ecall w) eqn:E; [discriminate|].
  destruct (decode_any w) as [[i' sz]|] eqn:Dw; [|discriminate].
  destruct (Z.eqb_spec sz 4); [|discriminate]. intros H; inversion H; subst. exists w; auto.
Qed.

Lemma build_itab_ok SEGS pc n acc :
  itab_ok SEGS acc -> 0 < pc -> itab_ok SEGS (build_itab SEGS pc n acc).
Proof.
  revert pc acc. induction n as [|n IH]; simpl; intros pc acc Hacc Hpc; auto.
  apply IH; [|lia].
  destruct (dec_at SEGS pc) as [i|] eqn:D; auto.
  intros pc' i'. unfold itab_get.
  destruct (Z.ltb_spec 0 pc'); [|discriminate].
  rewrite pm_get_set. destruct (Pos.eqb_spec (Z.to_pos pc') (Z.to_pos pc)).
  - intros X; inversion X; subst. assert (pc' = pc) by lia. subst. apply dec_at_ok; auto.
  - intros X. apply (Hacc pc' i'). unfold itab_get. destruct (Z.ltb_spec 0 pc'); [auto|lia].
Qed.

Lemma itab_ok_empty SEGS : itab_ok SEGS pm_empty.
Proof. intros pc i. unfold itab_get. destruct (Z.ltb 0 pc); [rewrite pm_get_empty|]; discriminate. Qed.

Theorem build_itab_sound SEGS lo n : 0 < lo -> itab_ok SEGS (build_itab SEGS lo n pm_empty).
Proof. intros; apply build_itab_ok; auto using itab_ok_empty. Qed.
