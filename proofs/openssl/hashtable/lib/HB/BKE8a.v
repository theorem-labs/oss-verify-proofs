(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition ke8a_body (N0 VP VB VL : nat) (nextp : plan) : plan :=
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
Definition ke8a_post (N0 VP VB VL : nat) : plan :=
  PCase2 (EVar (N0 + 1)) 0 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1ee25c]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1ee620] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208)))))))))))
  (PCase2 (EVar (N0 + 1)) 64 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 17 []
  (PRun [0x1aab04] (* [comment removed for export] *)
  (PExt 101 []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PCase2 (EVar (N0 + 0)) 254 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1ee25c]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1ee620] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208)))))))))))
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1ee25c]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1ee620] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208))))))))))))))))))))
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
  (PCase2 (EVar (N0 + 0)) 254 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1ee25c]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1ee620] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208)))))))))))
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1ee25c]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1ee620] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208))))))))))))))))
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PCase2 (EVar (N0 + 0)) 254 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1ee25c]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1ee620] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208)))))))))))
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1ee25c]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1ee620] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208)))))))))))))))))))))))))).
Definition ke8a_pre (k : plan) : plan :=
  PCompact (* [comment removed for export] *)
  (PExt 18 [] (* [comment removed for export] *)
  (PExt 19 [] (* [comment removed for export] *)
  (PExt 18 [] (* [comment removed for export] *)
  (k)))).
Definition ke8a_plan (N0 VP VB VL : nat) (inv : acs) (nextp : plan) : plan :=
  ke8a_pre (PLoop (N0 + 2) (eaddz (EVar (N0 + 0)) (-128)) inv (* [comment removed for export] *)
  (ke8a_body N0 VP VB VL nextp)
  (ke8a_post N0 VP VB VL)).
Definition ke8a_ranges : list (Z * nat) := [(0x197fd0, 1024%nat); (0x199fd0, 1024%nat); (0x1a6fd0, 1024%nat); (0x1a9fd0, 1024%nat); (0x1bbfd0, 3072%nat); (0x1bffd0, 1024%nat); (0x1c4fd0, 1024%nat); (0x1cffd0, 1024%nat); (0x1edfd0, 1254%nat); (0x554b84, 2045%nat); (0x55ab78, 1024%nat); (0x560b78, 2048%nat); (0x567b78, 1023%nat)].
