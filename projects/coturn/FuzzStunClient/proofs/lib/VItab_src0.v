(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VItab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition TEXT_LO_src0 : Z := 0x13894.
Definition TEXT_N_src0 : nat := Z.to_nat ((0x2427c - 0x13894) / 4).

Definition itab_src0 : itab := build_itab Plain.M.loaded_segments TEXT_LO_src0 TEXT_N_src0 pm_empty.

Theorem itab_src0_ok : itab_ok Plain.M.loaded_segments itab_src0.
Proof. apply build_itab_sound. reflexivity. Qed.
