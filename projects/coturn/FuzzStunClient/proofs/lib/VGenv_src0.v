(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VItab VItab_src0 VContract VDriver.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint build_rom (SEGS : list Segment) (a : Z) (n : nat) (acc : pmap Z) : pmap Z :=
  match n with
  | O => acc
  | S n' => build_rom SEGS (a + 1) n'
            (match seg_rom SEGS (Z_to_bv 64 a) with
             | Some b => pm_set (Z.to_pos a) (bv_unsigned b) acc
             | None => acc
             end)
  end.

Definition SEGS_src0 := Plain.M.loaded_segments.

Definition rom_src0 : pmap Z :=
  build_rom SEGS_src0 0x366d8 8 (build_rom SEGS_src0 0x252f8 8 (build_rom SEGS_src0 0x10000 (Z.to_nat 0x3000) pm_empty)).

Definition P0_src0 : vparams :=
  mkVP 132544 [] [] [(0x26360, 8); (0x3670c, 4)]
       [(0x10000, 0x58000)]
       [(0x10000, 0x2427c); (0x252f8, 0x25300); (0x366d8, 0x366e0)]
       rom_src0 (2 ^ 26) (0x7fff80000000 - 4096) (2 ^ 47).

Definition ctab_src0 : pmap contract :=
  pm_of_list [(Z.to_pos 0x23640, C_memcpy); (Z.to_pos 0x23a44, C_memset); (Z.to_pos 0x23b74, C_strlen);
              (Z.to_pos 0x23b3c, C_strcmp); (Z.to_pos 0x23c04, C_strncpy); (Z.to_pos 0x23540, C_bcmp);
              (Z.to_pos 0x23610, C_memcmp); (Z.to_pos 0x23490, C_strtoul); (Z.to_pos 0x1b260, C_tolower)].

Definition CI_src0 : cimg := mkCI 0x3670c 0x367b0 (-8).

Definition genv_src0 (ranks : bool) : genv :=
  mkGE P0_src0 itab_src0 ctab_src0 CI_src0 0x367b0 0x26360 ranks.
