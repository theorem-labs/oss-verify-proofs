(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VItab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition SEGS_asan := Asan.M.loaded_segments.

Definition nins (lo hi : Z) : nat := Z.to_nat ((hi - lo) / 4).

Definition itab_asan : itab :=
  build_itab SEGS_asan 0x9f448 (nins 0x9f448 0x9f4d8)
  (build_itab SEGS_asan 0x82ce4 (nins 0x82ce4 0x93eb8) pm_empty).

Theorem itab_asan_ok : itab_ok SEGS_asan itab_asan.
Proof. unfold itab_asan. repeat (apply build_itab_ok; [|reflexivity]). apply itab_ok_empty. Qed.
