(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition ke8b_body (N0 VP VB VL : nat) (nextp : plan) : plan :=
  PRun [] (* [comment removed for export] *)
  (PExt 12 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PBand VB (* [comment removed for export] *)
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1f32d0] (* [comment removed for export] *)
  nextp)))))
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1f32d0] (* [comment removed for export] *)
  nextp))))))))))))).
Definition ke8b_post (N0 VP VB VL : nat) : plan :=
  PCase2 (EVar (N0 + 1)) 0 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1f32ec]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1f36b0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208)))))))))))
  (PCase2 (EVar (N0 + 1)) 64 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 17 []
  (PRun [0x1afb94] (* [comment removed for export] *)
  (PExt 101 []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PCase2 (EVar (N0 + 0)) 254 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1f32ec]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1f36b0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208)))))))))))
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1f32ec]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1f36b0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208))))))))))))))))))))
  (PRun [] (* [comment removed for export] *)
  (PExt 17 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PBand VB (* [comment removed for export] *)
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PCase2 (EVar (N0 + 0)) 254 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1f32ec]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1f36b0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208)))))))))))
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1f32ec]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1f36b0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208))))))))))))))))
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PCase2 (EVar (N0 + 0)) 254 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1f32ec]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1f36b0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208)))))))))))
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [0x1f32ec]
  (PRespell 19 (ION.lensplit_len (N0 + 0) (N0 + 1))
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [0x1f36b0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 115) (PHavoc [5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PHandoff 208)))))))))))))))))))))))))).
Definition ke8b_pre (k : plan) : plan :=
  PCompact (* [comment removed for export] *)
  (PExt 18 [] (* [comment removed for export] *)
  (PExt 19 [] (* [comment removed for export] *)
  (PExt 18 [] (* [comment removed for export] *)
  (k)))).
Definition ke8b_plan (N0 VP VB VL : nat) (inv : acs) (nextp : plan) : plan :=
  ke8b_pre (PLoop (N0 + 2) (eaddz (EVar (N0 + 0)) (-128)) inv (* [comment removed for export] *)
  (ke8b_body N0 VP VB VL nextp)
  (ke8b_post N0 VP VB VL)).
Definition ke8b_ranges : list (Z * nat) := [(0x19d060, 1024%nat); (0x19f060, 1024%nat); (0x1ac060, 1024%nat); (0x1af060, 1024%nat); (0x1c1060, 3072%nat); (0x1c5060, 1024%nat); (0x1ca060, 1024%nat); (0x1d5060, 1024%nat); (0x1f3060, 1024%nat); (0x51c060, 2045%nat); (0x522054, 1024%nat); (0x528054, 2048%nat); (0x52f054, 1023%nat)].
