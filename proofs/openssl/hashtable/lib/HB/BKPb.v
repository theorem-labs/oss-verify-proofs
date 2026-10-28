(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BC4e.
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
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1965f4] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x19662c] (* [comment removed for export] *)
  (PBump (N0 + 116)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PExt 11 [ELit 0]
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PBump (N0 + 345)
  (PMmap (PContra)
  (PBand 0 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar (N0 + 1))) (ELit 73728)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1965f4] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x19662c] (* [comment removed for export] *)
  (PBump (N0 + 444)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar (N0 + 345))) (escale 4096 (EVar (N0 + 1))) 0x1bdca0 []%nat
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c04bc] (* [comment removed for export] *)
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
  (PRun [0x19a5e8] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1ee240] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 886) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 101))))))))) (PContra))))))) (PContra)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar (N0 + 1))) (ELit 73728)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1965f4] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x19662c] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar (N0 + 345))) (escale 4096 (EVar VP)) 0x196668 []%nat
  (PBump (N0 + 444)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c04bc] (* [comment removed for export] *)
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
  (PRun [0x19a5e8] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1ee240] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 886) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 101))))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (PContra))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 1))) (ELit 73728) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1965f4] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x19662c] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar (N0 + 1))) (escale 4096 (EVar VP)) 0x196668 []%nat
  (PBump (N0 + 116)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PExt 11 [ELit 0]
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PBump (N0 + 345)
  (PMmap (PContra)
  (PBand 0 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar (N0 + 1))) (ELit 73728)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1965f4] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x19662c] (* [comment removed for export] *)
  (PBump (N0 + 444)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c04bc] (* [comment removed for export] *)
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
  (PRun [0x19a5e8] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1ee240] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 886) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 101))))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar (N0 + 1))) (ELit 73728)
  (PShDisj (escale 4096 (EVar (N0 + 345))) (ELit 139264) (escale 4096 (EVar VP)) (ELit 137439023104)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1965f4] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x19662c] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar (N0 + 345))) (escale 4096 (EVar VP)) 0x196668 []%nat
  (PBump (N0 + 444)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar (N0 + 345))) (escale 4096 (EVar (N0 + 1))) 0x1bdca0 []%nat
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c04bc] (* [comment removed for export] *)
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
  (PRun [0x19a5e8] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (PContra)
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x1ee240] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 886) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 101))))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (PContra))))))))))))))))))))).
Definition kpb_ranges : list (Z * nat) := [(0x194fd0, 2048%nat); (0x198fd0, 3072%nat); (0x1a5fd0, 2048%nat); (0x1a9fd0, 1024%nat); (0x1bbfd0, 5120%nat); (0x1c3fd0, 5120%nat); (0x1c9fd0, 1024%nat); (0x1cbfd0, 2048%nat); (0x1cffd0, 1024%nat); (0x1d1fd0, 2048%nat); (0x1d9fd0, 1024%nat); (0x1dbfd0, 1024%nat); (0x1ddfd0, 1095%nat); (0x1dffd0, 2048%nat); (0x1ecfd0, 2278%nat); (0x554b84, 2045%nat); (0x560b78, 2048%nat); (0x563b78, 1024%nat); (0x567b78, 1023%nat)].
