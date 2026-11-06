(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan C4e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition c6c_band1l_ (_ : unit) : plan :=
  PShDisj (escale 4096 (EVar 575)) (ELit 73728) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar 575)) (ELit 73728) (eaddz e_pgsp (-8388608)) (ELit 12582912)
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
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x19b6bc] (* [comment removed for export] *)
  (PBump 690
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
  (PRun [0x1aab84] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra)))))))))))))))))))))))))
  (PCase2 (EVar 574) 64 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 11 [ELit 0]
  (PRun [0x1afb94] (* [comment removed for export] *)
  (PExt 101 []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
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
  (PRun [0x1aab84] (* [comment removed for export] *)
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
  (PRun [0x1aab84] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))
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
  (PRun [0x1aab84] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (PContra)))))))))))).
Abbreviation c6c_band1l := (c6c_band1l_ tt).
Definition c6c_band2h_ (_ : unit) : plan :=
  PShDisj (escale 4096 (EVar 575)) (ELit 73728) (ELit 65536) (ELit 12288000)
  (PShDisj (escale 4096 (EVar 575)) (ELit 73728) (eaddz e_pgsp (-8388608)) (ELit 12582912)
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
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy []
  (PRun [0x19b6bc] (* [comment removed for export] *)
  (PDiamondDisj (escale 4096 (EVar 575)) (escale 4096 (EVar 235)) 0x19b6f8 []%nat
  (PBump 690
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
  (PRun [0x1aab84] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra)))))))))))))))))))))))))
  (PCase2 (EVar 574) 64 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 11 [ELit 0]
  (PRun [0x1afb94] (* [comment removed for export] *)
  (PExt 101 []
  (PRun [0x1c2d28] (* [comment removed for export] *)
  (PDiamond 0x1c2d30 []%nat
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
  (PRun [0x1aab84] (* [comment removed for export] *)
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
  (PRun [0x1aab84] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra))))))))))))))))))))))))))))))))))
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
  (PRun [0x1aab84] (* [comment removed for export] *)
  (PBump 1200 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 24)))))))) (PContra))))))) (PContra)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (PContra)))))))))))).
Abbreviation c6c_band2h := (c6c_band2h_ tt).
Definition c6c_plan_ (_ : unit) : plan :=
  PRun [] (* [comment removed for export] *)
  (PBump 574
  (PExt2 0 [] (c4e_plan)
  (PExt 18 []
  (PRun [] (* [comment removed for export] *)
  (PBump 575
  (PMmap (PContra)
  (PBand 0 (c6c_band1l) (c6c_band2h)))))))).
Abbreviation c6c_plan := (c6c_plan_ tt).

Definition c6c_ranges : list (Z * nat) := [(0x19a060, 2048%nat); (0x19e060, 3072%nat); (0x1ab060, 2048%nat); (0x1af060, 2048%nat); (0x1c1060, 5120%nat); (0x1c9060, 5120%nat); (0x1cf060, 1024%nat); (0x1d1060, 2048%nat); (0x1d5060, 1024%nat); (0x1d7060, 2048%nat); (0x1df060, 1024%nat); (0x1e1060, 3072%nat); (0x1e5060, 2048%nat); (0x1f2060, 3072%nat); (0x51c060, 2045%nat); (0x522054, 2048%nat); (0x528054, 2048%nat); (0x52b054, 1024%nat); (0x52f054, 1023%nat)].
