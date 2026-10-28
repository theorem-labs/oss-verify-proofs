(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition st3a_plan_ (_ : unit) : plan :=
  PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PBump 515 (* [comment removed for export] *)
  (PMmap (PContra) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [0x1a5a88] (* [comment removed for export] *)
  (PBump 548 (* [comment removed for export] *)
  (PHandoff 10)))))))))) (PContra)).
Abbreviation st3a_plan := (st3a_plan_ tt).
Definition st3a_ranges : list (Z * nat) := [(0x1bcfd0, 1024%nat); (0x1c4fd0, 3072%nat); (0x1ccfd0, 1024%nat); (0x1cffd0, 1024%nat); (0x1d4fd0, 1024%nat); (0x1ecfd0, 2278%nat); (0x555b78, 3072%nat); (0x559b78, 1024%nat); (0x560b78, 2048%nat); (0x564b78, 1024%nat)].
Definition st3a_est : nat := 548.
