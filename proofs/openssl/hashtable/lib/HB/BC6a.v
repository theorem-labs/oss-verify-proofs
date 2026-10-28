(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan BC4e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition c6a_band1l_ (_ : unit) : plan :=
  PShDisj (escale 4096 (EVar 575)) (ELit 73728) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar 575)) (ELit 73728) (eaddz e_pgsp (-8388608)) (ELit 12582912)
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
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x19662c] (* [comment removed for export] *)
  (PBump 690
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
  (PCase2 (EVar 574) 0 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
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
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra)))))))))))))))))))))))))
  (PCase2 (EVar 574) 64 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 11 [ELit 0]
  (PRun [0x1aab04] (* [comment removed for export] *)
  (PExt 101 []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PCase2 (EVar 574) 5 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
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
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra)))))))))))))))))))))))))
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
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
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))
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
  (PExt 13 []
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
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
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (PContra)))))))))))).
Abbreviation c6a_band1l := (c6a_band1l_ tt).
Definition c6a_band2h_ (_ : unit) : plan :=
  PShDisj (escale 4096 (EVar 575)) (ELit 73728) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar 575)) (ELit 73728) (eaddz e_pgsp (-8388608)) (ELit 12582912)
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
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x19662c] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar 575)) (escale 4096 (EVar 235)) 0x196668 []%nat
  (PBump 690
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
  (PCase2 (EVar 574) 0 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
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
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra)))))))))))))))))))))))))
  (PCase2 (EVar 574) 64 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 11 [ELit 0]
  (PRun [0x1aab04] (* [comment removed for export] *)
  (PExt 101 []
  (PRun [0x1bdc98] (* [comment removed for export] *)
  (PDiamond 0x1bdca0 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PCase2 (EVar 574) 5 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
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
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra)))))))))))))))))))))))))
  (PRun [] (* [comment removed for export] *)
  (PExt 13 []
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
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
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))
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
  (PExt 13 []
  (PRun [] (* [comment removed for export] *)
  (PExt 15 []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
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
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (PContra)))))))))))).
Abbreviation c6a_band2h := (c6a_band2h_ tt).
Definition c6a_plan_ (_ : unit) : plan :=
  PRun [] (* [comment removed for export] *)
  (PBump 574
  (PExt2 0 [] (c4e_plan)
  (PExt 18 []
  (PRun [] (* [comment removed for export] *)
  (PBump 575
  (PMmap (PContra)
  (PBand 0 (c6a_band1l) (c6a_band2h)))))))).
Abbreviation c6a_plan := (c6a_plan_ tt).

Definition c6a_ranges : list (Z * nat) := [(0x194fd0, 2048%nat); (0x198fd0, 3072%nat); (0x1a5fd0, 2048%nat); (0x1a9fd0, 2048%nat); (0x1bbfd0, 5120%nat); (0x1c3fd0, 5120%nat); (0x1c9fd0, 1024%nat); (0x1cbfd0, 2048%nat); (0x1cffd0, 1024%nat); (0x1d1fd0, 2048%nat); (0x1d9fd0, 1024%nat); (0x1dbfd0, 3143%nat); (0x1dffd0, 2048%nat); (0x1ecfd0, 3155%nat); (0x554b84, 2045%nat); (0x55ab78, 2048%nat); (0x560b78, 2048%nat); (0x563b78, 1024%nat); (0x567b78, 1023%nat)].
