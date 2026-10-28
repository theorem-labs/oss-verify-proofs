(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition kra_body (N0 VP VB VL : nat) (nextp : plan) : plan :=
  PRun [] (* [comment removed for export] *)
  (PExt 12 []
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
  (PRun [0x1ee240] (* [comment removed for export] *)
  nextp)))))
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1ee240] (* [comment removed for export] *)
  nextp))))))))))))).
Definition kra_post (N0 VP VB VL : nat) : plan :=
  PRun [] (* [comment removed for export] *)
  (PExt 12 []
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
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1a5af4] (PBump (N0 + 281) (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 230))))))))))))))))))))))))))))))))))
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1a5af4] (PBump (N0 + 281) (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 230)))))))))))))))))))))))))))))))))))))))))).
Definition kra_pre (k : plan) : plan :=
  PCompact (* [comment removed for export] *)
  (PExt 18 [] (* [comment removed for export] *)
  (k)).
Definition kra_plan (N0 VP VB VL : nat) (inv : acs) (nextp : plan) : plan :=
  kra_pre (PLoop (N0 + 0) (ELit 511) inv (* [comment removed for export] *)
  (kra_body N0 VP VB VL nextp)
  (kra_post N0 VP VB VL)).
Definition kra_ranges : list (Z * nat) := [(0x194fd0, 1024%nat); (0x197fd0, 1024%nat); (0x199fd0, 1024%nat); (0x1a6fd0, 1024%nat); (0x1a9fd0, 3072%nat); (0x1b1fd0, 1024%nat); (0x1bbfd0, 3072%nat); (0x1bffd0, 1024%nat); (0x1c4fd0, 1024%nat); (0x1cffd0, 1024%nat); (0x1dcfd0, 1024%nat); (0x1edfd0, 2131%nat); (0x554b84, 2045%nat); (0x55ab78, 4096%nat); (0x560b78, 2048%nat); (0x567b78, 1023%nat)].
