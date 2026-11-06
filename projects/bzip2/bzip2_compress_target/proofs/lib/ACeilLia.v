(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Export ACeil ACeilTac RunW.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac aceil_evars :=
  repeat match goal with
         | |- context [@alloc_ceiling ?i] => is_evar i; let inst := constr:(_ : ACeil) in unify i inst
         | |- context [@run_guard ?i] => is_evar i; let inst := constr:(_ : RunW) in unify i inst
         | |- context [@run_secret ?i] => is_evar i; let inst := constr:(_ : RunW) in unify i inst
         end.
Ltac bz_ceil ::=
  try aceil_evars;
  try (lazymatch goal with
       | _ : (0x7fff7f800000 <= alloc_ceiling)%Z |- _ => fail
       | _ : context [alloc_ceiling] |- _ => pose proof alloc_ceiling_ge as ACRlo__; pose proof alloc_ceiling_le as ACRhi__
       | |- context [alloc_ceiling] => pose proof alloc_ceiling_ge as ACRlo__; pose proof alloc_ceiling_le as ACRhi__
       end);
  try (lazymatch goal with
       | _ : (0 <= run_secret < _)%Z |- _ => fail
       | _ : context [run_secret] |- _ => pose proof run_secret_range as RSR__
       | |- context [run_secret] => pose proof run_secret_range as RSR__
       end);
  try (lazymatch goal with
       | _ : (0 <= run_guard < _)%Z |- _ => fail
       | _ : context [run_guard] |- _ => pose proof run_guard_range as RGR__
       | |- context [run_guard] => pose proof run_guard_range as RGR__
       end).

(* [comment removed for export] *)
Ltac lia ::= first [ Zify.zify; xlia zchecker | aceil_evars; Zify.zify; xlia zchecker | bz_ceil; Zify.zify; xlia zchecker ].
Ltac nia ::= first [ Zify.zify; xnia zchecker | bz_ceil; Zify.zify; xnia zchecker ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SelfTest3. Context {AC : ACeil}. Variable y : Z.
(* [comment removed for export] *)
End SelfTest3.
Section SelfTest4. Context {AC : ACeil} {RW : RunW}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End SelfTest4.
