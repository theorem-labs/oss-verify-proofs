(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanItabFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition HO_NXT : nat := 136.
Definition T_VAR : nat := 10.
Definition V_TF : nat := 11.    (* [comment removed for export] *)
Definition V_ST : nat := 12.    (* [comment removed for export] *)

Definition KCm : nat := 0.
Definition BFUELm : nat := 400000.
Definition FUELm : nat := 6000.

Definition main_ranges : list (Z * nat) := [(0x4e000, 9216%nat); (0x59000, 19456%nat); (0x73000, 7168%nat); (0x7b000, 31744%nat); (0x9e000, 3072%nat); (0xa3000, 10240%nat); (0xc8000, 2048%nat); (0xe3000, 6144%nat); (0xed000, 4096%nat); (0xfb000, 5120%nat); (0x103000, 3072%nat); (0x10a000, 26624%nat)]%Z.

Definition ITm : itab := mk_itab_ranges_fast ASEGS main_ranges.
Lemma ITm_ok : itab_sound ASEGS ITm.
Proof. apply mk_itab_ranges_fast_sound. Qed.

Definition e_r : expr := eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar T_VAR))) 36703.
