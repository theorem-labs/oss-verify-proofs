(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition ke1b_post (N0 VP VB VL : nat) : plan :=
  PCase2 (EVar VL) 65536 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1ee25c]
  (PRespell 19 (EVar VL)
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1ee620] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 80) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 201)))))))))))
  (PCase2 (EVar VL) 65600 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 17 []
  (PRun [0x1aab04] (* [comment removed for export] *)
  (PExt 101 []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1ee25c]
  (PRespell 19 (EVar VL)
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1ee620] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 80) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 201)))))))))))))))))))
  (PRun [] (* [comment removed for export] *)
  (PExt 17 []
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PBand VB (* [comment removed for export] *)
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1ee25c]
  (PRespell 19 (EVar VL)
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1ee620] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 80) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 201)))))))))))))))
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1ee25c]
  (PRespell 19 (EVar VL)
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1ee620] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 80) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 201))))))))))))))))))))))))).
Definition ke1b_pre (k : plan) : plan :=
  PCompact (* [comment removed for export] *)
  (PExt 18 [] (* [comment removed for export] *)
  (k)).
Definition ke1b_plan (N0 VP VB VL : nat) (inv : acs) (nextp : plan) : plan :=
  ke1b_pre (ke1b_post N0 VP VB VL).
Definition ke1b_ranges : list (Z * nat) := [(0x198fd0, 3072%nat); (0x1a6fd0, 1024%nat); (0x1a9fd0, 1024%nat); (0x1bbfd0, 3072%nat); (0x1bffd0, 1024%nat); (0x1c4fd0, 1024%nat); (0x1c6fd0, 2048%nat); (0x1cffd0, 1024%nat); (0x1edfd0, 1254%nat); (0x554b84, 2045%nat); (0x55ab78, 1024%nat); (0x560b78, 2048%nat); (0x563b78, 1024%nat); (0x567b78, 1023%nat)].
