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
Definition kw2b_post (N0 VP VB VL : nat) : plan :=
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
  (PExt 12 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PBump (N0 + 144)
  (PMmap (PContra)
  (PBand 0 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (escale 4096 (EVar VB)) (ELit 270336)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x19b684] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x19b6bc] (* [comment removed for export] *)
  (PBump (N0 + 243)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar (N0 + 144))) (escale 4096 (EVar VB)) 0x1c2d30 []%nat
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x19f678] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 511) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 103)))))))))))))))))))))))))))))))))))))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (escale 4096 (EVar VB)) (ELit 270336)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x19b684] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x19b6bc] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar (N0 + 144))) (escale 4096 (EVar VP)) 0x19b6f8 []%nat
  (PBump (N0 + 243)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x19f678] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 511) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 103)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PExt 12 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PBump (N0 + 144)
  (PMmap (PContra)
  (PBand 0 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (escale 4096 (EVar VB)) (ELit 270336)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x19b684] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x19b6bc] (* [comment removed for export] *)
  (PBump (N0 + 243)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x19f678] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 511) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 103))))))))))))))))))))))))))))))))))))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (escale 4096 (EVar VB)) (ELit 270336)
  (PShDisj (escale 4096 (EVar (N0 + 144))) (ELit 532480) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x19b684] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x19b6bc] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar (N0 + 144))) (escale 4096 (EVar VP)) 0x19b6f8 []%nat
  (PBump (N0 + 243)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar (N0 + 144))) (escale 4096 (EVar VB)) 0x1c2d30 []%nat
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x19f678] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 511) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 103)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition kw2b_pre (k : plan) : plan :=
  PCompact (* [comment removed for export] *)
  (PExt 18 [] (* [comment removed for export] *)
  (k)).
Definition kw2b_plan (N0 VP VB VL : nat) (inv : acs) (nextp : plan) : plan :=
  kw2b_pre (kw2b_post N0 VP VB VL).
Definition kw2b_ranges : list (Z * nat) := [(0x19a060, 2048%nat); (0x19f060, 2048%nat); (0x1ac060, 1024%nat); (0x1af060, 1024%nat); (0x1c1060, 5120%nat); (0x1c9060, 5120%nat); (0x1cf060, 1024%nat); (0x1d1060, 2048%nat); (0x1d5060, 1024%nat); (0x1d7060, 2048%nat); (0x1e5060, 2048%nat); (0x1f2060, 2048%nat); (0x51d054, 1024%nat); (0x528054, 2048%nat); (0x52b054, 1024%nat); (0x52f054, 1023%nat)].
