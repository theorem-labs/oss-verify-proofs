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
Definition plan_src13_pfx1 : plan :=
  PX XLayout [ELit 1]
  (PRun []
  (PExt2 0 []
  (PHandoff 31)
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
  (PExt 11 [ELit 0]
  (PRun []
  (PX XMemcpy []
  (PRun []
  (PExt 13 [] (PHandoffS 35%nat 720%nat [(720%nat, EVar 5); (721%nat, EVar 699); (722%nat, EVar 700); (723%nat, EVar 701); (724%nat, EVar 702); (725%nat, EVar 703); (726%nat, EVar 704); (727%nat, EVar 705); (728%nat, EVar 706); (729%nat, EVar 707); (730%nat, EVar 708); (731%nat, EVar 709); (732%nat, EVar 710); (733%nat, EVar 711); (734%nat, EVar 712); (735%nat, EVar 713); (736%nat, EVar 714); (737%nat, EVar 715); (738%nat, EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 8192)); (739%nat, EMd Instr.M_MUL (ELit 4096) (EVar 5)); (740%nat, ELit 8192); (741%nat, EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 8192))]))))))))))))
  (PRun []
  (PMmap
  (PRun []
  (PMprotect
  (PRun []
  (PMmap
  (PRun [0xb6c40]
  (PRun []
  (PExt 11 [ELit 0]
  (PRun []
  (PX XMemcpy []
  (PRun []
  (PExt 13 [] (PHandoffS 35%nat 720%nat [(720%nat, EVar 699); (721%nat, EVar 700); (722%nat, EVar 701); (723%nat, EVar 702); (724%nat, EVar 703); (725%nat, EVar 704); (726%nat, EVar 705); (727%nat, EVar 706); (728%nat, EVar 707); (729%nat, EVar 708); (730%nat, EVar 709); (731%nat, EVar 710); (732%nat, EVar 711); (733%nat, EVar 712); (734%nat, EVar 713); (735%nat, EVar 714); (736%nat, EVar 715); (737%nat, EVar 716); (738%nat, EMd Instr.M_MUL (ELit 4096) (EVar 5)); (739%nat, EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 699)) (ELit 4096)); (740%nat, ELit 4096); (741%nat, ELit 18446744073709551615)])))))))))))))))))))))).
