(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import MState Mem Cells Step Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint strcmp_walk (l r : list byte) {struct l} : option Z :=
  match l, r with
  | a :: l', b :: r' =>
      if ((bv_unsigned a =? 0) || negb (bv_unsigned a =? bv_unsigned b))%bool
      then Some (bv_unsigned a - bv_unsigned b)
      else strcmp_walk l' r'
  | _, _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section CStr.
  Variables (s1 s2 j1 j2 : list byte).
  Hypothesis NZ1 : ~ In (Z_to_bv 8 0) s1.
  Hypothesis NZ2 : ~ In (Z_to_bv 8 0) s2.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End CStr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition strchrnul_idx (c : Z) (str : list byte) : nat :=
  match find_byte c str with Some i => i | None => length str end.

Lemma strchrnul_idx_le : forall c str, (strchrnul_idx c str <= length str)%nat.
Proof.
  intros c str. unfold strchrnul_idx. destruct (find_byte c str) as [i|] eqn:E; [|lia].
  destruct (find_byte_Some _ _ _ E) as (Hi & _ & _). lia.
Qed.

Lemma strchrnul_idx_before : forall c str j b, (j < strchrnul_idx c str)%nat ->
  nth_error str j = Some b -> bv_unsigned b <> c.
Proof.
  intros c str j b Hj Hb. unfold strchrnul_idx in Hj. destruct (find_byte c str) as [i|] eqn:E.
  - destruct (find_byte_Some _ _ _ E) as (_ & _ & Hbefore). exact (Hbefore j b Hj Hb).
  - exact (find_byte_None _ _ E j b Hb).
Qed.

Lemma strchrnul_idx_at : forall c str, (strchrnul_idx c str < length str)%nat ->
  exists b, nth_error str (strchrnul_idx c str) = Some b /\ bv_unsigned b = c.
Proof.
  intros c str H. unfold strchrnul_idx in *. destruct (find_byte c str) as [i|] eqn:E.
  - destruct (find_byte_Some _ _ _ E) as (_ & Hb & _). exact Hb.
  - exfalso. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition strchr_res (A c : Z) (str : list byte) : Z :=
  match find_byte c str with Some i => A + Z.of_nat i | None => 0 end.
