(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition plan_src13_pfx7 : plan :=
  PX XLayout [ELit 1]
  (PRun []
  (PExt2 0 []
  (PHandoff 31)
  (PExt 19 []
  (PRun []
  (PX XMemcpy []
  (PRun []
  (PSys YBrk
  (PRun []
  (PBrk2
  (PRun []
  (PMmapIn
  (PRun []
  (PMmap
  (PRun [0xb6c40]
  (PRun []
  (PHandoffS 35%nat 706%nat [(706%nat, EVar 5); (707%nat, EVar 701); (708%nat, EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 8192)); (709%nat, EMd Instr.M_MUL (ELit 4096) (EVar 5)); (710%nat, ELit 8192); (711%nat, EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 8192))])))))))
  (PRun []
  (PMmap
  (PRun []
  (PMprotect
  (PRun []
  (PMmap
  (PRun [0xb6c40]
  (PRun []
  (PHandoffS 35%nat 706%nat [(706%nat, EVar 701); (707%nat, EVar 702); (708%nat, EMd Instr.M_MUL (ELit 4096) (EVar 5)); (709%nat, EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 701)) (ELit 4096)); (710%nat, ELit 4096); (711%nat, ELit 18446744073709551615)])))))))))))))))))).
