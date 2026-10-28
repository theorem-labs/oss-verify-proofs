(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan BC4e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition c4d1_band1l_ (_ : unit) : plan :=
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
  (PRun [] (* [comment removed for export] *)
  (PExt 14 []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x1d05c4] (* [comment removed for export] *)
  (PExt 0 [ELit 1]
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x560d0c] (* [comment removed for export] *)
  (PExt 1 [ELit 1]
  (PRun [0x55d320] (* [comment removed for export] *)
  (PExt 2 [ELit 1]
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PExt 3 [ELit 1]
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 991 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 23)))))))))))))))))))))))))))))))))))))))))))))) (PContra)))))))))))).
Abbreviation c4d1_band1l := (c4d1_band1l_ tt).
Definition c4d1_band2h_ (_ : unit) : plan :=
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
  (PRun [] (* [comment removed for export] *)
  (PExt 14 []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x1d05c4] (* [comment removed for export] *)
  (PExt 0 [ELit 1]
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x560d0c] (* [comment removed for export] *)
  (PExt 1 [ELit 1]
  (PRun [0x55d320] (* [comment removed for export] *)
  (PExt 2 [ELit 1]
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PExt 3 [ELit 1]
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 991 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 23))))))))))))))))))))))))))))))))))))))))))))))) (PContra)))))))))))).
Abbreviation c4d1_band2h := (c4d1_band2h_ tt).
Definition c4d1_plan_ (_ : unit) : plan :=
  PRun [] (* [comment removed for export] *)
  (PExt2 0 [] (c4e_plan)
  (PRun [] (* [comment removed for export] *)
  (PBump 575
  (PMmap (PContra)
  (PBand 0 (c4d1_band1l) (c4d1_band2h)))))).
Abbreviation c4d1_plan := (c4d1_plan_ tt).
Definition c4d1_top_ (_ : unit) : plan := PSplit (EVar 7) 0 (PHandoff 95) (PSplit (EVar 7) 2 (PX XLayout [ELit 1] (c4d1_plan)) (PHandoff 94)).
Abbreviation c4d1_top := (c4d1_top_ tt).
Definition c4d1_ranges : list (Z * nat) := [(0x194fd0, 2048%nat); (0x199fd0, 2048%nat); (0x1a5fd0, 2048%nat); (0x1a9fd0, 3072%nat); (0x1bbfd0, 5120%nat); (0x1c3fd0, 5120%nat); (0x1c9fd0, 1024%nat); (0x1cbfd0, 2048%nat); (0x1cffd0, 1024%nat); (0x1d1fd0, 2048%nat); (0x1d9fd0, 1024%nat); (0x1dbfd0, 3143%nat); (0x1dffd0, 2048%nat); (0x1ecfd0, 3155%nat); (0x554b84, 2045%nat); (0x55ab78, 4096%nat); (0x560b78, 2048%nat); (0x563b78, 1024%nat); (0x567b78, 1023%nat)].
