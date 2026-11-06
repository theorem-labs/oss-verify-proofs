(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export B0Traps.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

(* [comment removed for export] *)
Ltac b_trapb p := let b := eval vm_compute in (b0_trapb p) in b.

(* [comment removed for export] *)
Ltac b_guard :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
      let ta := b_trapb a in
      lazymatch ta with
      | true => if_false_z
      | false =>
          let tb := b_trapb b in
          lazymatch tb with
          | true => if_true_z
          | false => fail "b_guard: neither arm is a trap pc"
          end
      end
  end.
(* [comment removed for export] *)
Ltac b_is_guard :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
      let ta := b_trapb a in
      lazymatch ta with
      | true => idtac
      | false => let tb := b_trapb b in lazymatch tb with true => idtac end
      end
  end.
Ltac b_try_guard := tryif b_is_guard then first [ b_guard | idtac "brun: UNPROVED UBSan trap guard (missing bound?)" ] else idtac.

(* [comment removed for export] *)
Ltac b_new_flag R :=
  lazymatch goal with
  | |- evt _ _ (MS ?R' _ _ _ _ _ _) =>
      match R' with
      | context [Z.b2z ?t] => lazymatch R with context [Z.b2z t] => fail | _ => idtac end
      end
  end.
Ltac b_has_flag :=
  lazymatch goal with |- evt _ _ (MS ?R' _ _ _ _ _ _) => lazymatch R' with context [Z.b2z (_ _ _)] => idtac end end.
Ltac b_flags R := tryif b_new_flag R then (flags; tryif b_has_flag then try flagsb else idtac) else idtac.

Ltac b_regs := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => R end.
Ltac bstep := let R := b_regs in wstep; a_norm; b_flags R; a_try_lit_branch; b_try_guard.
Ltac bstep_nf := let R := b_regs in a_zstep_nofb; bz32; a_norm; b_flags R; a_try_lit_branch; b_try_guard.
Ltac brun_to p :=
  first [ a_at_pc p
        | a_pc_is_lit; bstep; brun_to p
        | fail 1 "brun_to: stopped at an open branch / unproved guard / non-literal pc before reaching" p ].
Ltac brun :=
  first [ a_pc_is_lit; bstep_nf; brun
        | lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "brun: stopped at" pc end ].
