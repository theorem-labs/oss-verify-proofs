(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VItab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition SEGS_both := AsanUbsan.M.loaded_segments.

Definition nins (lo hi : Z) : nat := Z.to_nat ((hi - lo) / 4).

Definition itab_both : itab :=
  build_itab SEGS_both 0x9da84 (nins 0x9da84 0x9db14)
  (build_itab SEGS_both 0x82cd4 (nins 0x82cd4 0x924f4) pm_empty).

Theorem itab_both_ok : itab_ok SEGS_both itab_both.
Proof. unfold itab_both. repeat (apply build_itab_ok; [|reflexivity]). apply itab_ok_empty. Qed.
