(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition kw9b_body (N0 VP VB VL : nat) (nextp : plan) : plan :=
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
Definition kw9b_post (N0 VP VB VL : nat) : plan :=
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
  (PRun [] (* [comment removed for export] *)
  (PBump (N0 + 105)
  (PMmap (PContra)
  (PBand 0 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (escale 4096 (EVar VB)) (ELit 33562624)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PBump (N0 + 204)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 105))) (escale 4096 (EVar VB)) 0x1bdca0 []%nat
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x19a5e8] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x19804c] (* [comment removed for export] *)
  (PJoin (ELit 0) (6940552) 4
  (PRun [0x1ee240] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 472) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 110)))))))))))))))))))))))))))))))))))))))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (escale 4096 (EVar VB)) (ELit 33562624)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 105))) (escale 4096 (EVar VP)) 0x196668 []%nat
  (PBump (N0 + 204)
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
  (PRun [0x19a5e8] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x19804c] (* [comment removed for export] *)
  (PJoin (ELit 0) (6940552) 4
  (PRun [0x1ee240] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 472) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 110)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PBump (N0 + 105)
  (PMmap (PContra)
  (PBand 0 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (escale 4096 (EVar VB)) (ELit 33562624)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PBump (N0 + 204)
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
  (PRun [0x19a5e8] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x19804c] (* [comment removed for export] *)
  (PJoin (ELit 0) (6940552) 4
  (PRun [0x1ee240] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 472) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 110))))))))))))))))))))))))))))))))))))))))))))))))))
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (ELit 65536) (ELit 12496896)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (eaddz e_pgsp (-8388608)) (ELit 12582912)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (escale 4096 (EVar VB)) (ELit 33562624)
  (PShDisj (escale 4096 (EVar (N0 + 105))) (ELit 67117056) (escale 4096 (EVar VP)) (ELit 137439023104)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 105))) (escale 4096 (EVar VP)) 0x196668 []%nat
  (PBump (N0 + 204)
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
  (PDiamondDisj (escale 4096 (EVar (N0 + 105))) (escale 4096 (EVar VB)) 0x1bdca0 []%nat
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [0x1c04bc] (* [comment removed for export] *)
  (PExt 100 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x19a5e8] (* [comment removed for export] *)
  (PJoin e_spw (-2248) 8
  (PRun [0x1bfb34] (* [comment removed for export] *)
  (PDiamondT 0x1bfdb8 6 []%nat
  (PRun [] (* [comment removed for export] *)
  (PX XMemset []
  (PRun [0x19804c] (* [comment removed for export] *)
  (PJoin (ELit 0) (6940552) 4
  (PRun [0x1ee240] (PDropRange (ELit 12337360) (ELit 65536) (PBump (N0 + 472) (PHavoc [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat (PHandoff 110)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition kw9b_pre (k : plan) : plan :=
  PCompact (* [comment removed for export] *)
  (PExt 18 [] (* [comment removed for export] *)
  (k)).
Definition kw9b_plan (N0 VP VB VL : nat) (inv : acs) (nextp : plan) : plan :=
  kw9b_pre (PLoop (N0 + 0) (ELit 255) inv (* [comment removed for export] *)
  (kw9b_body N0 VP VB VL nextp)
  (kw9b_post N0 VP VB VL)).
Definition kw9b_ranges : list (Z * nat) := [(0x194fd0, 2048%nat); (0x197fd0, 1024%nat); (0x199fd0, 2048%nat); (0x1a6fd0, 1024%nat); (0x1a9fd0, 1024%nat); (0x1bbfd0, 5120%nat); (0x1c3fd0, 5120%nat); (0x1c9fd0, 1024%nat); (0x1cbfd0, 2048%nat); (0x1cffd0, 1024%nat); (0x1d1fd0, 2048%nat); (0x1dffd0, 2048%nat); (0x1ecfd0, 2278%nat); (0x555b78, 1024%nat); (0x560b78, 2048%nat); (0x563b78, 1024%nat); (0x567b78, 1023%nat)].
