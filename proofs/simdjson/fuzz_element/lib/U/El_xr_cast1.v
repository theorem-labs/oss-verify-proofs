(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_xs_core El_xs_kitP El_xs_adapt El_xs_frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Open Scope Z_scope.

Definition el_ranges_cast1 : list (Z * nat) := [(0x3c4f8, 10%nat); (0x3d848, 12%nat); (0x5efbc, 5%nat); (0x5f030, 5%nat); (0x5f1ac, 6%nat); (0x7a188, 1%nat); (0x7a580, 120%nat); (0x7a8b8, 50%nat); (0x7b558, 10%nat); (0x7b5d0, 55%nat); (0x7b8e0, 2%nat); (0x7b95c, 32%nat); (0x7ba28, 31%nat); (0x7bb08, 54%nat); (0x7bc28, 22%nat); (0x7c1b8, 6%nat); (0x7c240, 115%nat); (0x7c46c, 220%nat); (0x7c8ac, 15%nat); (0x7c938, 9%nat); (0x7cc40, 15%nat); (0x7ccf8, 22%nat); (0x7cdac, 24%nat); (0xb877c, 47%nat); (0xb8884, 11%nat); (0xb8950, 14%nat); (0xb8a7c, 84%nat); (0xb8c58, 19%nat); (0xb91ac, 25%nat); (0xb9270, 21%nat); (0xb9378, 50%nat); (0xb9484, 72%nat); (0xb95f4, 56%nat); (0xb9744, 63%nat); (0xb98b0, 26%nat); (0xb997c, 19%nat); (0xb9a2c, 29%nat); (0xb9b08, 14%nat); (0xb9cd4, 43%nat); (0xb9e0c, 74%nat); (0xba0dc, 47%nat); (0xba210, 129%nat); (0xba46c, 52%nat); (0xba5ac, 16%nat); (0xba6d0, 70%nat); (0xba88c, 34%nat); (0xba9b4, 5%nat); (0xbb5a4, 142%nat); (0xbb86c, 91%nat); (0xbbbdc, 16%nat); (0xbbc1c, 120%nat); (0xbbd4c, 17%nat); (0xbbea4, 30%nat); (0xbc0a4, 10%nat); (0xbc400, 22%nat); (0xbc908, 38%nat); (0xbca48, 25%nat); (0xbcc10, 16%nat); (0xbcd70, 20%nat); (0xbcfec, 50%nat); (0xbd1c4, 16%nat); (0xbd268, 19%nat); (0xbd350, 53%nat); (0xbd5ac, 22%nat); (0xbe148, 33%nat); (0xbe234, 49%nat); (0xbe418, 133%nat); (0xbe904, 132%nat); (0xbf030, 132%nat); (0xc0250, 105%nat)].
Definition el_IT_cast1 : itab := itab_of_ranges usegs el_ranges_cast1 PTLeaf.
Lemma xr_cast1_ok : forall uw : bool, exit_ok (xautoP el_IT_cast1 xs_W xs_RW 0x7c1b8 XS_FUEL XS_KD (xs_ssD 32 [] 0x3d848 0x3c378 uw)) = true.
Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
