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
Definition kw8b_body (N0 VP VB VL : nat) (nextp : plan) : plan :=
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
Definition kw8b_post (N0 VP VB VL : nat) : plan :=
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
  (PBump (N0 + 105)
  (PMmap (PContra)
  (PBand 0 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (escale 4096 (EVar VB)) (ELit 16785408)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PBump (N0 + 204)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 105))) (escale 4096 (EVar VB)) 0x1c2d30 []%nat
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
  (PRun [0x19d0dc] (* [comment removed for export] *)
  (PJoin (ELit 0) (6732616) 4
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 472) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 109)))))))))))))))))))))))))))))))))))))))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (escale 4096 (EVar VB)) (ELit 16785408)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 105))) (escale 4096 (EVar VP)) 0x19b6f8 []%nat
  (PBump (N0 + 204)
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
  (PRun [0x19d0dc] (* [comment removed for export] *)
  (PJoin (ELit 0) (6732616) 4
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 472) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 109)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PBump (N0 + 105)
  (PMmap (PContra)
  (PBand 0 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (escale 4096 (EVar VB)) (ELit 16785408)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PBump (N0 + 204)
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
  (PRun [0x19d0dc] (* [comment removed for export] *)
  (PJoin (ELit 0) (6732616) 4
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 472) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 109))))))))))))))))))))))))))))))))))))))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (escale 4096 (EVar VB)) (ELit 16785408)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 33562624) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 105))) (escale 4096 (EVar VP)) 0x19b6f8 []%nat
  (PBump (N0 + 204)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 105))) (escale 4096 (EVar VB)) 0x1c2d30 []%nat
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
  (PRun [0x19d0dc] (* [comment removed for export] *)
  (PJoin (ELit 0) (6732616) 4
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 472) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 109)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition kw8b_pre (k : plan) : plan :=
  PCompact (* [comment removed for export] *)
  (PExt 18 [] (* [comment removed for export] *)
  (k)).
Definition kw8b_plan (N0 VP VB VL : nat) (inv : acs) (nextp : plan) : plan :=
  kw8b_pre (PLoop (N0 + 0) (ELit 127) inv (* [comment removed for export] *)
  (kw8b_body N0 VP VB VL nextp)
  (kw8b_post N0 VP VB VL)).
Definition kw8b_ranges : list (Z * nat) := [(0x19a060, 2048%nat); (0x19d060, 1024%nat); (0x19f060, 2048%nat); (0x1ac060, 1024%nat); (0x1af060, 1024%nat); (0x1c1060, 5120%nat); (0x1c9060, 5120%nat); (0x1cf060, 1024%nat); (0x1d1060, 2048%nat); (0x1d5060, 1024%nat); (0x1d7060, 2048%nat); (0x1e5060, 2048%nat); (0x1f2060, 2048%nat); (0x51d054, 1024%nat); (0x528054, 2048%nat); (0x52b054, 1024%nat); (0x52f054, 1023%nat)].
