(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VItab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition TEXT_LO_ub : Z := 0x13974.
Definition TEXT_N_ub : nat := Z.to_nat ((0x24724 - 0x13974) / 4).

Definition itab_ub : itab := build_itab Ubsan.M.loaded_segments TEXT_LO_ub TEXT_N_ub pm_empty.

Theorem itab_ub_ok : itab_ok Ubsan.M.loaded_segments itab_ub.
Proof. apply build_itab_sound. reflexivity. Qed.
