(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition c7m_plan_ (_ : unit) : plan :=
  PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x1ca974] (* [comment removed for export] *)
  (PBump 1092 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 27))))))))))).
Abbreviation c7m_plan := (c7m_plan_ tt).

Definition c7m_ranges : list (Z * nat) := [(0x1c9fd0, 1024%nat); (0x1cffd0, 1024%nat)].
