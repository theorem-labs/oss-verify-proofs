(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition st3b_plan_ (_ : unit) : plan :=
  PRun [] (* [comment removed for export] *)
  (PBump 514 (* [comment removed for export] *)
  (PMmap (PContra) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMprotect (PContra) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PBump 515 (* [comment removed for export] *)
  (PMmap (PContra) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [0x1aab18] (* [comment removed for export] *)
  (PBump 548 (* [comment removed for export] *)
  (PHandoff 10)))))))))))))).
Abbreviation st3b_plan := (st3b_plan_ tt).
Definition st3b_ranges : list (Z * nat) := [(0x1c2060, 1024%nat); (0x1ca060, 3072%nat); (0x1d2060, 1024%nat); (0x1d5060, 1024%nat); (0x1da060, 1024%nat); (0x1f2060, 2048%nat); (0x51d054, 3072%nat); (0x521054, 1024%nat); (0x528054, 2048%nat)].
Definition st3b_est : nat := 548.
