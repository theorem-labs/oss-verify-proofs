(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxMem.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition anon_kind (R : region) : bool := match rg_kind R with KZero | KUnk => true | _ => false end.

Lemma anon_not_entry (R : region) : anon_kind R = true -> is_entry R = false.
Proof. unfold anon_kind, is_entry. destruct (rg_kind R); first [reflexivity | discriminate]. Qed.

(* [comment removed for export] *)
Definition starts_at (ts : terms) (cur : Z) (R : region) : bool :=
  teqb (rg_ts R) ts &&& (wZ (rg_bo R) =? cur) &&& (0 <? to_Z (rg_n R)) &&& anon_kind R.

Fixpoint find_start (ts : terms) (cur : Z) (A : list region) : option region :=
  match A with
  | [] => None
  | R :: A' => if starts_at ts cur R then Some R else find_start ts cur A'
  end.

Lemma find_start_spec (ts : terms) (cur : Z) (A : list region) (R : region) :
  find_start ts cur A = Some R -> In R A /\ rg_ts R = ts /\ wZ (rg_bo R) = cur /\ 0 < to_Z (rg_n R) /\ anon_kind R = true.
Proof.
  induction A as [|X A IH]; cbn [find_start]; [discriminate|]. destruct (starts_at ts cur X) eqn:E.
  - intros H. injection H as <-. unfold starts_at in E.
    apply land_true in E as [E S4]. apply land_true in E as [E S3]. apply land_true in E as [S1 S2].
    apply teqb_eq in S1. apply Z.eqb_eq in S2. apply Z.ltb_lt in S3. split; [left; reflexivity|]. repeat split; assumption.
  - intros H. destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* [comment removed for export] *)
Fixpoint chain (fuel : nat) (ts : terms) (A : list region) (cur stop : Z) : bool :=
  if cur =? stop then true else
  match fuel with
  | O => false
  | S k => match find_start ts cur A with
           | Some R => (cur + to_Z (rg_n R) <=? stop) &&& chain k ts A (cur + to_Z (rg_n R)) stop
           | None => false
           end
  end.

Lemma chain_cover (fuel : nat) (ts : terms) (A : list region) (cur stop : Z) :
  chain fuel ts A cur stop = true -> forall w, cur <= w < stop ->
  exists R, In R A /\ rg_ts R = ts /\ cur <= wZ (rg_bo R) /\ wZ (rg_bo R) <= w < wZ (rg_bo R) + to_Z (rg_n R)
            /\ wZ (rg_bo R) + to_Z (rg_n R) <= stop /\ anon_kind R = true.
Proof.
  revert cur. induction fuel as [|k IH]; intros cur H w Hw; cbn [chain] in H.
  - destruct (cur =? stop) eqn:E; [apply Z.eqb_eq in E; lia | discriminate H].
  - destruct (cur =? stop) eqn:E; [apply Z.eqb_eq in E; lia|].
    destruct (find_start ts cur A) as [R|] eqn:Ef; [|discriminate H]. apply land_true in H as [H1 H2]. apply Z.leb_le in H1.
    destruct (find_start_spec ts cur A R Ef) as (HR & S1 & S2 & S3 & S4).
    destruct (Z_lt_le_dec w (cur + to_Z (rg_n R))) as [L|L].
    + exists R. repeat split; try assumption; lia.
    + destruct (IH _ H2 w ltac:(lia)) as [R1 (G1 & G2 & G3 & G4 & G5 & G6)]. exists R1. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Fixpoint chain_ge (fuel : nat) (ts : terms) (A : list region) (cur stop : Z) : bool :=
  if stop <=? cur then true else
  match fuel with
  | O => false
  | S k => match find_start ts cur A with
           | Some R => chain_ge k ts A (cur + to_Z (rg_n R)) stop
           | None => false
           end
  end.

Lemma chain_ge_cover (fuel : nat) (ts : terms) (A : list region) (cur stop : Z) :
  chain_ge fuel ts A cur stop = true -> forall w, cur <= w < stop ->
  exists R, In R A /\ rg_ts R = ts /\ wZ (rg_bo R) <= w < wZ (rg_bo R) + to_Z (rg_n R) /\ anon_kind R = true.
Proof.
  revert cur. induction fuel as [|k IH]; intros cur H w Hw; cbn [chain_ge] in H.
  - destruct (stop <=? cur) eqn:E; [apply Z.leb_le in E; lia | discriminate H].
  - destruct (stop <=? cur) eqn:E; [apply Z.leb_le in E; lia|].
    destruct (find_start ts cur A) as [R|] eqn:Ef; [|discriminate H].
    destruct (find_start_spec ts cur A R Ef) as (HR & S1 & S2 & S3 & S4).
    destruct (Z_lt_le_dec w (cur + to_Z (rg_n R))) as [L|L].
    + exists R. repeat split; try assumption; lia.
    + exact (IH _ H w ltac:(lia)).
Qed.
