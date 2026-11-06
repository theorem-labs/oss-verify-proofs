(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Image.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_core El_xs_kitP El_xs_adapt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Open Scope Z_scope.

Definition el_ranges_begin : list (Z * nat) := [(0x3bf98, 7%nat); (0x3c460, 10%nat); (0x533bc, 5%nat); (0x53430, 5%nat); (0x535ac, 6%nat); (0x6e588, 1%nat); (0x6e980, 120%nat); (0x6ecb8, 50%nat); (0x6f958, 10%nat); (0x6f9d0, 55%nat); (0x6fce0, 2%nat); (0x6fd5c, 32%nat); (0x6fe28, 31%nat); (0x6ff08, 54%nat); (0x70028, 22%nat); (0x705b8, 6%nat); (0x70640, 115%nat); (0x7086c, 220%nat); (0x70cac, 15%nat); (0x70d38, 9%nat); (0x71040, 15%nat); (0x710f8, 22%nat); (0x711ac, 24%nat); (0xacb7c, 47%nat); (0xacc84, 11%nat); (0xacd50, 14%nat); (0xace7c, 84%nat); (0xad058, 19%nat); (0xad5ac, 25%nat); (0xad670, 21%nat); (0xad778, 50%nat); (0xad884, 72%nat); (0xad9f4, 56%nat); (0xadb44, 63%nat); (0xadcb0, 26%nat); (0xadd7c, 19%nat); (0xade2c, 29%nat); (0xadf08, 14%nat); (0xae0d4, 43%nat); (0xae20c, 74%nat); (0xae4dc, 47%nat); (0xae610, 129%nat); (0xae86c, 52%nat); (0xae9ac, 16%nat); (0xaead0, 70%nat); (0xaec8c, 34%nat); (0xaedb4, 5%nat); (0xaf9a4, 142%nat); (0xafc6c, 91%nat); (0xaffdc, 16%nat); (0xb014c, 17%nat); (0xb02a4, 30%nat); (0xb04a4, 10%nat); (0xb0800, 22%nat); (0xb0d08, 38%nat); (0xb0e48, 25%nat); (0xb1010, 16%nat); (0xb1170, 20%nat); (0xb13ec, 50%nat); (0xb15c4, 16%nat); (0xb1668, 19%nat); (0xb1750, 53%nat); (0xb19ac, 22%nat); (0xb2548, 33%nat); (0xb2634, 49%nat); (0xb2818, 133%nat); (0xb2d04, 132%nat); (0xb3430, 132%nat); (0xb4650, 105%nat)].
Definition el_IT_begin : itab := itab_of_ranges psegs el_ranges_begin PTLeaf.
Lemma xr_begin_ok : forall uw : bool, exit_ok (xautoP el_IT_begin xs_W xs_RW 0x705b8 XS_FUEL XS_K (xs_ss0 0x3c460 0x3bed8 uw)) = true.
Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
