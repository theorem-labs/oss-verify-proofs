(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VItab VItab_ub VContract VDriver VGenv_src0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SEGS_ub := Ubsan.M.loaded_segments.

Definition rom_ub : pmap Z :=
  build_rom SEGS_ub 0x36b88 8 (build_rom SEGS_ub 0x257a0 8 (build_rom SEGS_ub 0x10000 (Z.to_nat 0x3000) pm_empty)).

Definition P0_ub : vparams :=
  mkVP 132624 [] [] [(0x26808, 8); (0x36bbc, 4)]
       [(0x10000, 0x58000)]
       [(0x10000, 0x24724); (0x257a0, 0x257a8); (0x36b88, 0x36b90)]
       rom_ub (2 ^ 26) (0x7fff80000000 - 4096) (2 ^ 47).

Definition ctab_ub : pmap contract :=
  pm_of_list [(Z.to_pos 0x23ae8, C_memcpy); (Z.to_pos 0x23eec, C_memset); (Z.to_pos 0x2401c, C_strlen);
              (Z.to_pos 0x23fe4, C_strcmp); (Z.to_pos 0x240ac, C_strncpy); (Z.to_pos 0x239e8, C_bcmp);
              (Z.to_pos 0x23ab8, C_memcmp); (Z.to_pos 0x23938, C_strtoul); (Z.to_pos 0x1b708, C_tolower)].

Definition CI_ub : cimg := mkCI 0x36bbc 0x36c60 (-8).

Definition genv_ub (ranks : bool) : genv :=
  mkGE P0_ub itab_ub ctab_ub CI_ub 0x36c60 0x26808 ranks.
