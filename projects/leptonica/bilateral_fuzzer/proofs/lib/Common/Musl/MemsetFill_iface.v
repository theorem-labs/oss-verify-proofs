(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatSim Hoare StoreOk.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition memset_fill_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

Definition memset_fill_stmt {fx : FPState} (segs : list MemImageType.Segment) (entry : word) : Prop :=
  forall regs (M rom : word -> option byte) (d n c : Z) (ret : word),
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z -> (0 <= c < 256)%Z ->
    store_ok segs M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 c ->
    getr regs 12 = Z_to_bv 64 n ->
    exists regs' M',
      msteps segs (mkst regs entry M rom) (mkst regs' ret M' rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r memset_fill_clob) regs regs'
      /\ (forall x : word, (bv_unsigned x < d \/ d + n <= bv_unsigned x)%Z -> M' x = M x)
      /\ mem_grows M M'
      /\ (forall i, (0 <= i < n)%Z -> M' (Z_to_bv 64 (d + i)) <> None).
