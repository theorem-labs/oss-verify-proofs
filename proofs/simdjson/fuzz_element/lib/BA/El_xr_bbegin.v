(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_core.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_xs_coreA El_xs_adaptA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Open Scope Z_scope.

Definition el_ranges_bbegin : list (Z * nat) := [(0x6c4e4, 1%nat); (0xb1ee8, 7%nat); (0xe9c04, 5%nat); (0xe9c78, 5%nat); (0xe9df4, 6%nat); (0x104dd0, 1%nat); (0x1051c8, 53%nat); (0x1052d8, 52%nat); (0x105500, 15%nat); (0x105540, 2%nat); (0x105578, 7%nat); (0x1055a8, 8%nat); (0x1061a0, 10%nat); (0x106218, 7%nat); (0x106248, 22%nat); (0x1062c8, 11%nat); (0x106528, 2%nat); (0x1065a4, 32%nat); (0x106670, 31%nat); (0x106750, 21%nat); (0x1067cc, 18%nat); (0x106870, 5%nat); (0x106894, 12%nat); (0x106ecc, 38%nat); (0x106f90, 2%nat); (0x106fa0, 2%nat); (0x106fcc, 10%nat); (0x106ffc, 22%nat); (0x1070b4, 26%nat); (0x107138, 21%nat); (0x1071b8, 18%nat); (0x107204, 124%nat); (0x1073f8, 11%nat); (0x1074f4, 15%nat); (0x107580, 9%nat); (0x107888, 15%nat); (0x107940, 5%nat); (0x10795c, 15%nat); (0x1079f4, 7%nat); (0x107a1c, 14%nat); (0x1433c4, 47%nat); (0x1434cc, 11%nat); (0x143598, 14%nat); (0x1436c4, 31%nat); (0x14374c, 15%nat); (0x1437c4, 5%nat); (0x1437f8, 7%nat); (0x1438a0, 7%nat); (0x1438e4, 2%nat); (0x143df4, 25%nat); (0x143eb8, 21%nat); (0x143fc0, 21%nat); (0x144048, 16%nat); (0x1440cc, 18%nat); (0x144144, 42%nat); (0x14423c, 56%nat); (0x14438c, 49%nat); (0x144480, 2%nat); (0x1444f8, 26%nat); (0x1445c4, 19%nat); (0x144674, 29%nat); (0x144750, 14%nat); (0x14491c, 43%nat); (0x144a54, 50%nat); (0x144b28, 21%nat); (0x144d24, 47%nat); (0x144e58, 49%nat); (0x144f34, 14%nat); (0x144f74, 58%nat); (0x1450b4, 25%nat); (0x145120, 12%nat); (0x145158, 11%nat); (0x1451f4, 8%nat); (0x14521c, 6%nat); (0x145318, 8%nat); (0x145354, 2%nat); (0x145380, 36%nat); (0x14541c, 5%nat); (0x1454d4, 34%nat); (0x1455fc, 5%nat); (0x1461ec, 54%nat); (0x1462ec, 27%nat); (0x14636c, 19%nat); (0x1463d0, 9%nat); (0x1463fc, 10%nat); (0x1464b4, 70%nat); (0x1465d0, 20%nat); (0x146824, 29%nat); (0x146994, 17%nat); (0x146aec, 13%nat); (0x146b24, 16%nat); (0x146cec, 10%nat); (0x147048, 22%nat); (0x147550, 11%nat); (0x147580, 26%nat); (0x147690, 15%nat); (0x1476ec, 2%nat); (0x147858, 16%nat); (0x1479b8, 20%nat); (0x147c34, 21%nat); (0x147c94, 26%nat); (0x147e0c, 16%nat); (0x147eb0, 5%nat); (0x147ecc, 12%nat); (0x147f98, 53%nat); (0x1481f4, 22%nat); (0x148d90, 13%nat); (0x148df0, 9%nat); (0x148e7c, 37%nat); (0x148f1c, 9%nat); (0x149060, 16%nat); (0x1490a4, 76%nat); (0x1491e0, 24%nat); (0x149244, 12%nat); (0x14954c, 86%nat); (0x1496d0, 35%nat); (0x149e5c, 64%nat); (0x149fdc, 4%nat); (0x14b82c, 55%nat); (0x14b910, 22%nat); (0x14b994, 15%nat)].
Definition el_IT_bbegin : itab := itab_of_ranges asegs el_ranges_bbegin PTLeaf.
Definition el_hcs_bbegin : list hcellA := [(8, 8%nat, HVopq); (16, 8%nat, HVopq); (24, 8%nat, HVlit 0xb1c18)].
Definition el_xr_bbegin : xregs_exit := [(18%nat, EVar 18); (19%nat, EVar 19); (20%nat, EVar 20); (21%nat, EVar 21); (23%nat, EVar 23); (24%nat, EVar 24); (25%nat, EVar 25); (26%nat, EVar 26); (27%nat, EVar 27)].
Definition el_xk_bbegin : xstack_exit := [(24, ELit 0xb1f04); (16, EVar 50); (8, EVar 49)].

Lemma xr_bbegin_ok : forall uw : bool,
  exit_okA 32 el_xr_bbegin el_xk_bbegin (xautoXA 32 el_IT_bbegin XS_END_A XSA_FUEL XSA_K (xs_ss0A 32 el_hcs_bbegin 0xb3014 uw)) = true.
Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
