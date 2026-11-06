(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import EquivZA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition moZ0 (inp : ProcInput) : Model :=
  init_model [] (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 sp_window_lo) 0 inp.

Lemma moZ0_ok : forall inp,
  minv (moZ0 inp) /\ m_halted (moZ0 inp) = None /\ m_fds (moZ0 inp) = init_fds /\ m_fs (moZ0 inp) = in_fs inp.
Proof.
  intros inp. split; [| split; [reflexivity| split; reflexivity]].
  apply minv_init. rewrite Z_to_bv_unsigned. unfold sp_window_lo, sp_window_hi, bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by lia. lia.
Qed.
