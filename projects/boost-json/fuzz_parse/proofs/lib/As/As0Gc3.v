(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2.   (* [comment removed for export] *)
From Stdlib Require Import PArray Uint63.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init5Logic02eq57Corelib7Numbers6Cyclic5Int639PrimInt63h83int79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6As0Gc3~~~~~~k6aflush_loop" s.
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PArray.length (PArray.make 4194303 acc))
  end.
Lemma gc_flush : ltac2:(zQ "30!h4!k0!o2@3$0$1@2$2No0I0Ijvvvvf").
Proof. vm_cast_no_check (@eq_refl int 4194303%uint63). Qed.
