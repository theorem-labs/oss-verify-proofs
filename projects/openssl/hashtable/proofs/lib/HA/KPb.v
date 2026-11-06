(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO C4e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition kpb_plan (N0 VP VB VL : nat) : plan :=
  PRun [] (* [comment removed for export] *)
  (PBump (N0 + 0)
  (PExt2 0 [] (c4e_plan)
  (PExt 18 []
  (PRun [] (* [comment removed for export] *)
  (PBump (N0 + 1)
  (PMmap (PContra)
  (PBand 0 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x19b684] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x19b6bc] (* [comment removed for export] *)
  (PBump (N0 + 116)
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
  (PRun [] (* [comment removed for export] *)
  (PExt 11 [ELit 0]
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
  (PBump (N0 + 345)
  (PMmap (PContra)
  (PBand 0 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar (N0 + 1))) (ELit 73728)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PBump (N0 + 444)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 345))) (escale 4096 (EVar (N0 + 1))) 0x1c2d30 []%nat
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x19f678] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 886) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 101))))))))) (PContra))))))) (PContra)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar (N0 + 1))) (ELit 73728)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 345))) (escale 4096 (EVar VP)) 0x19b6f8 []%nat
  (PBump (N0 + 444)
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
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x19f678] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 886) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 101))))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (PContra))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x19b684] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x19b6bc] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar (N0 + 1))) (escale 4096 (EVar VP)) 0x19b6f8 []%nat
  (PBump (N0 + 116)
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
  (PRun [] (* [comment removed for export] *)
  (PExt 11 [ELit 0]
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
  (PBump (N0 + 345)
  (PMmap (PContra)
  (PBand 0 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar (N0 + 1))) (ELit 73728)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PBump (N0 + 444)
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
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x19f678] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 886) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 101))))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar (N0 + 1))) (ELit 73728)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 345))) (escale 4096 (EVar VP)) 0x19b6f8 []%nat
  (PBump (N0 + 444)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 345))) (escale 4096 (EVar (N0 + 1))) 0x1c2d30 []%nat
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c554c] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x19f678] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1c4bc4] (* [comment removed for export] *)
  (PDiamondT 0x1c4e48 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1f32d0] (PDropRange (ELit 12129424) (ELit 65536) (PBump (N0 + 886) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 101))))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (PContra))))))))))))))))))))).
Definition kpb_ranges : list (Z * nat) := [(0x19a060, 2048%nat); (0x19e060, 3072%nat); (0x1ab060, 2048%nat); (0x1af060, 1024%nat); (0x1c1060, 5120%nat); (0x1c9060, 5120%nat); (0x1cf060, 1024%nat); (0x1d1060, 2048%nat); (0x1d5060, 1024%nat); (0x1d7060, 2048%nat); (0x1df060, 1024%nat); (0x1e1060, 1024%nat); (0x1e3060, 1024%nat); (0x1e5060, 2048%nat); (0x1f2060, 2048%nat); (0x51c060, 2045%nat); (0x528054, 2048%nat); (0x52b054, 1024%nat); (0x52f054, 1023%nat)].
