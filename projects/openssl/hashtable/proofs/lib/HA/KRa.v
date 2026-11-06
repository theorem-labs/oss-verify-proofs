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
Definition kra_body (N0 VP VB VL : nat) (nextp : plan) : plan :=
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
Definition kra_post (N0 VP VB VL : nat) : plan :=
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
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1aab84] (PBump (N0 + 281) (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 230))))))))))))))))))))))))))))))))))
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1aab84] (PBump (N0 + 281) (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 230)))))))))))))))))))))))))))))))))))))))))).
Definition kra_pre (k : plan) : plan :=
  PCompact (* [comment removed for export] *)
  (PExt 18 [] (* [comment removed for export] *)
  (k)).
Definition kra_plan (N0 VP VB VL : nat) (inv : acs) (nextp : plan) : plan :=
  kra_pre (PLoop (N0 + 0) (ELit 511) inv (* [comment removed for export] *)
  (kra_body N0 VP VB VL nextp)
  (kra_post N0 VP VB VL)).
Definition kra_ranges : list (Z * nat) := [(0x19a060, 1024%nat); (0x19d060, 1024%nat); (0x19f060, 1024%nat); (0x1ac060, 1024%nat); (0x1af060, 3072%nat); (0x1b7060, 1024%nat); (0x1c1060, 3072%nat); (0x1c5060, 1024%nat); (0x1ca060, 1024%nat); (0x1d5060, 1024%nat); (0x1e2060, 1024%nat); (0x1f3060, 2048%nat); (0x51c060, 2045%nat); (0x522054, 4096%nat); (0x528054, 2048%nat); (0x52f054, 1023%nat)].
