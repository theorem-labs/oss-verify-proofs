(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition c3m3_plan_ (_ : unit) : plan :=
  PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [0x1d05c4] (* [comment removed for export] *)
  (PExt 0 [ELit 0]
  (PSplit (EVar 3) 63 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x560d0c] (* [comment removed for export] *)
  (PExt 1 [ELit 0]
  (PRun [0x55d320] (* [comment removed for export] *)
  (PExt 2 [ELit 0]
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PSplit (EVar 3) 0 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 3 [ELit 0]
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 798 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 20))))))))))
  (PRun [] (* [comment removed for export] *)
  (PExt 3 [ELit 0]
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 798 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 20)))))))))))))))))))))))
  (PRun [] (* [comment removed for export] *)
  (PX XMemIsZero []
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [0x560d0c] (* [comment removed for export] *)
  (PExt 1 [ELit 0]
  (PRun [] (* [comment removed for export] *)
  (PX XMemIsZero []
  (PRun [] (* [comment removed for export] *)
  (PX XMemIsZero []
  (PRun [0x55d320] (* [comment removed for export] *)
  (PExt 2 [ELit 0]
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PSplit (EVar 3) 64 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 3 [ELit 0]
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 798 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 20))))))))))
  (PSplit (EVar 3) 73 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemIsZero []
  (PRun [] (* [comment removed for export] *)
  (PX XMemIsZero []
  (PRun [] (* [comment removed for export] *)
  (PExt 3 [ELit 0]
  (PSplit (EVar 3) 66 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 798 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 20))))))))
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 798 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 20)))))))))))))))
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy []
  (PRun [] (* [comment removed for export] *)
  (PEmit 0 []
  (PRun [0x1a5af4] (* [comment removed for export] *)
  (PBump 798 (PHavoc [5; 6; 7; 16; 17; 28; 29; 30; 31]%nat (PHandoff 20)))))))))))))))))))))))))))))))))).
Abbreviation c3m3_plan := (c3m3_plan_ tt).
Definition c3m3_top_ (_ : unit) : plan := PSplit (EVar 1) 2 (PHandoff 98) (PX XLayout [ELit 1] (c3m3_plan)).
Abbreviation c3m3_top := (c3m3_top_ tt).
Definition c3m3_ranges : list (Z * nat) := [(0x194fd0, 1024%nat); (0x1a5fd0, 3072%nat); (0x1a9fd0, 3072%nat); (0x1bbfd0, 3072%nat); (0x1bffd0, 1024%nat); (0x1c3fd0, 2048%nat); (0x1cffd0, 1024%nat); (0x1d9fd0, 1024%nat); (0x1dcfd0, 1024%nat); (0x1edfd0, 2131%nat); (0x554b84, 2045%nat); (0x55ab78, 4096%nat); (0x560b78, 2048%nat)].
