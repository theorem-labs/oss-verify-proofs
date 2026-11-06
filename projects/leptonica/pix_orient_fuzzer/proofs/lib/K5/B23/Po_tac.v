(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import LeptTac RT_fk Bi_fpkit Bi_fpkit2.
Import ListNotations.
Open Scope Z_scope.

Ltac norm_regset ::=
  repeat match goal with
  | |- context [@bvmap_set 5 word ?r ?v ?R] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (@bvmap_set 5 word r v R) with (tset p v R);
      cbv beta iota delta [tset mkR]
  end.

Ltac fa_known :=
  repeat match goal with
  | FA : reg_get ?F _ = ?b |- context [reg_get ?F ?r] =>
      let E := fresh "E" in assert (E : reg_get F r = b) by exact FA; rewrite E; clear E
  end.
Ltac fa_known_in H :=
  repeat match goal with
  | FA : reg_get ?F _ = ?b |- _ =>
      lazymatch type of H with context [reg_get F ?r] =>
        let E := fresh "E" in assert (E : reg_get F r = b) by exact FA; rewrite E in H; clear E end
  end.
Ltac fp_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end;
  fa_known;
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    lazymatch c with context [bword ?t] => fp_lit (bword t) end; br end.
(* [comment removed for export] *)
Ltac po_fpwalk_to stops := repeat (tryif at_stop stops then fail else first [fp_branch | awalk1]).
Ltac po_fpwalk := po_fpwalk_to (@nil Z).
Ltac word_lit_in w H :=
  let z := eval vm_compute in (bv_unsigned w) in
  let E := fresh "WL" in
  assert (E : w = Z_to_bv 64 z) by (vm_compute; reflexivity);
  rewrite E in H; clear E.
