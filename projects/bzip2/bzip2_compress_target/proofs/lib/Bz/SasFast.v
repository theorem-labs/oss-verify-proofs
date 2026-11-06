(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Arr.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac sas_u32s :=
  repeat match goal with
  | |- context [length (u32s _)] => rewrite !u32s_length
  | H : context [length (u32s _)] |- _ => rewrite !u32s_length in H
  end.
Ltac sas_u64s :=
  repeat match goal with
  | |- context [length (u64s _)] => rewrite !u64s_length
  | H : context [length (u64s _)] |- _ => rewrite !u64s_length in H
  end.
Ltac sas_upd :=
  repeat match goal with
  | |- context [length (upd _ _ _)] => rewrite !upd_length
  | H : context [length (upd _ _ _)] |- _ => rewrite !upd_length in H
  end.

(* [comment removed for export] *)
Ltac sas3_all := sas_u32s; sas_u64s; sas_upd.

(* [comment removed for export] *)
Local Ltac sas_selftest hook :=
  intros ws bs i x b v H K; hook;
  lazymatch goal with |- (8 * length ws = 8 * length ws)%nat => idtac end;
  lazymatch type of H with (4 * length ws + length (u32s ws) = v + length bs)%nat => idtac end;
  lazymatch goal with v0 := length (u32s ws) |- _ => idtac end;
  lazymatch type of K with (forall ws' : list word, length (u32s ws') = (4 * length ws')%nat) => idtac end;
  reflexivity.
Goal forall (ws : list word) (bs : list byte) (i : nat) (x : word) (b : byte),
  let v := length (u32s ws) in
  (length (u32s (upd ws i x)) + length (upd (u32s ws) i b) = v + length bs)%nat ->
  (forall ws' : list word, length (u32s ws') = (4 * length ws')%nat) ->
  (length (u64s (upd (upd ws i x) i x)) = 8 * length ws)%nat.
Proof. sas_selftest ltac:(rewrite ?u32s_length, ?u64s_length, ?upd_length in *). Qed.
Goal forall (ws : list word) (bs : list byte) (i : nat) (x : word) (b : byte),
  let v := length (u32s ws) in
  (length (u32s (upd ws i x)) + length (upd (u32s ws) i b) = v + length bs)%nat ->
  (forall ws' : list word, length (u32s ws') = (4 * length ws')%nat) ->
  (length (u64s (upd (upd ws i x) i x)) = 8 * length ws)%nat.
Proof. sas_selftest sas3_all. Qed.
