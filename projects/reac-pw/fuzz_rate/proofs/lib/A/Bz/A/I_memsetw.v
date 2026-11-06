(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/I_memsetw.v, with its module paths, module names and addresses changed; 1 of its 15 lines of code is new or changed and 561 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Bz/A/I_memsetw.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.A Require Import R_small.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition icells_ms (m : mem) : Prop :=
  ro_cells asegs m 0x9be70 [C8 (Z_to_bv 64 0xa4c38)]            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x9c9d8 [C8 (Z_to_bv 64 0xa5919)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0x9dcd8 [C8 (Z_to_bv 64 0x95358)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa4c38 [C8 (Z_to_bv 64 0x7fff8000)]      (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa5919 [C1 (Z_to_bv 8 1)].              (* [comment removed for export] *)
