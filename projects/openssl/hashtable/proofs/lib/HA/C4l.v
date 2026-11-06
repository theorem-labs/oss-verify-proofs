(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition c4l_plan_ (_ : unit) : plan :=
  PRun [] (* [comment removed for export] *)
  (PExt 10 []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x1d5654] (* [comment removed for export] *)
  (PExt 0 [ELit 1]
  (PRun [] (* [comment removed for export] *)
  (PX XMemIsZero []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x5281e8] (* [comment removed for export] *)
  (PExt 1 [ELit 1]
  (PRun [] (* [comment removed for export] *)
  (PX XMemIsZero []
  (PRun [] (* [comment removed for export] *)
  (PX XMemIsZero []
  (PRun [0x5247fc] (* [comment removed for export] *)
  (PExt 2 [ELit 1]
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1aab84] (* [comment removed for export] *)
  (PBump 774 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 21))))))))))))))))))))))))))))))))).
Abbreviation c4l_plan := (c4l_plan_ tt).
Definition c4l_top_ (_ : unit) : plan := PSplit (EVar 7) 4095 (PHandoff 96) (PX XLayout [ELit 1] (c4l_plan)).
Abbreviation c4l_top := (c4l_top_ tt).
Definition c4l_ranges : list (Z * nat) := [(0x19a060, 1024%nat); (0x1ab060, 3072%nat); (0x1af060, 3072%nat); (0x1c1060, 2048%nat); (0x1c5060, 1024%nat); (0x1c9060, 2048%nat); (0x1d5060, 1024%nat); (0x1df060, 1024%nat); (0x1e2060, 1024%nat); (0x1f3060, 2048%nat); (0x51c060, 2045%nat); (0x522054, 4096%nat); (0x528054, 2048%nat)].
