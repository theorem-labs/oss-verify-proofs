(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import ImageA.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_core.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import El_xs_coreA El_xs_adaptA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Open Scope Z_scope.

Definition el_ranges_bcstr : list (Z * nat) := [(0x6cb94, 1%nat); (0xb27a4, 8%nat); (0xb8354, 27%nat); (0xf8790, 5%nat); (0xf8804, 5%nat); (0xf8980, 6%nat); (0x11395c, 1%nat); (0x113d54, 120%nat); (0x11408c, 50%nat); (0x114d2c, 10%nat); (0x114da4, 55%nat); (0x1150b4, 2%nat); (0x115130, 32%nat); (0x1151fc, 31%nat); (0x1152dc, 54%nat); (0x1153fc, 22%nat); (0x11598c, 6%nat); (0x115a14, 115%nat); (0x115c40, 220%nat); (0x116080, 15%nat); (0x11610c, 9%nat); (0x116414, 15%nat); (0x1164cc, 22%nat); (0x116580, 24%nat); (0x151f50, 47%nat); (0x152058, 11%nat); (0x152124, 14%nat); (0x152250, 84%nat); (0x15242c, 19%nat); (0x152980, 25%nat); (0x152a44, 21%nat); (0x152b4c, 50%nat); (0x152c58, 72%nat); (0x152dc8, 56%nat); (0x152f18, 63%nat); (0x153084, 26%nat); (0x153150, 19%nat); (0x153200, 29%nat); (0x1532dc, 14%nat); (0x1534a8, 43%nat); (0x1535e0, 74%nat); (0x1538b0, 47%nat); (0x1539e4, 129%nat); (0x153c40, 52%nat); (0x153d80, 16%nat); (0x153ea4, 70%nat); (0x154060, 34%nat); (0x154188, 5%nat); (0x154d78, 142%nat); (0x155040, 91%nat); (0x1553b0, 16%nat); (0x155520, 17%nat); (0x155678, 30%nat); (0x155878, 10%nat); (0x155bd4, 22%nat); (0x1560dc, 38%nat); (0x15621c, 25%nat); (0x1563e4, 16%nat); (0x156544, 20%nat); (0x1567c0, 50%nat); (0x156998, 16%nat); (0x156a3c, 19%nat); (0x156b24, 53%nat); (0x156d80, 22%nat); (0x15791c, 33%nat); (0x157a08, 49%nat); (0x157bec, 133%nat); (0x1580d8, 132%nat); (0x158968, 132%nat); (0x15a3b8, 105%nat)].
Definition el_IT_bcstr : itab := itab_of_ranges bsegs el_ranges_bcstr PTLeaf.
Definition el_hcs_bcstr : list hcellA := [(0, 8%nat, HVopq); (8, 8%nat, HVopq); (16, 8%nat, HVopq); (24, 8%nat, HVopq); (32, 8%nat, HVopq); (40, 8%nat, HVlit 0xb2400)].
Definition el_xr_bcstr : xregs_exit := [(18%nat, EVar 51); (19%nat, EVar 50); (20%nat, EVar 49); (21%nat, EVar 21); (24%nat, EVar 24); (25%nat, EVar 25); (26%nat, EVar 26); (27%nat, EVar 27)].
Definition el_xk_bcstr : xstack_exit := [(40, ELit 0xb27c4); (32, EVar 53); (24, EVar 52)].

Lemma xr_bcstr_ok : forall uw : bool,
  exit_okA 48 el_xr_bcstr el_xk_bcstr (xautoXA 48 el_IT_bcstr XS_END_A XSA_FUEL XSA_K (xs_ss0A 48 el_hcs_bcstr 0xb83c0 uw)) = true.
Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
