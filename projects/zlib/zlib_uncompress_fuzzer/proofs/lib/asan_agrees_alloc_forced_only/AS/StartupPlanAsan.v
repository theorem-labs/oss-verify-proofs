(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup_plan_brkfail1 : plan :=
  PRun []
  (PMmap
  (PSpin )
  (PGhost (eaddz (escale 4096 (EVar 395)) 4096) (ELit 4096)
  (PRun []
  (PMprotect
  (PSpin )
  (PRun []
  (PMmap
  (PSpin )
  (PGhost (escale 4096 (EVar 396)) (ELit 4096)
  (PIntro 1 1
  (PGhost (escale 4096 (EVar 397)) (ELit 4096)
  (PRun []
  (PX XIMemset []
  (PRun []
  (PX XIMemset []
  (PRun [0x8cacc]
  (PBump 437
  (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PFog 0 8192
  (PFog 1 8192
  (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (escale 4096 (EVar 396)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (escale 4096 (EVar 395)) (ELit 8192)
  (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (escale 4096 (EVar 396)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (escale 4096 (EVar 395)) (ELit 8192)
  (PShDisj (escale 4096 (EVar 245)) (ELit 4096) (escale 4096 (EVar 396)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 245)) (ELit 4096) (escale 4096 (EVar 395)) (ELit 8192)
  (PShDisj (escale 4096 (EVar 228)) (ELit 65536) (escale 4096 (EVar 396)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 228)) (ELit 65536) (escale 4096 (EVar 395)) (ELit 8192)
  (PShDisj (escale 4096 (EVar 227)) (ELit 4096) (escale 4096 (EVar 396)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 227)) (ELit 4096) (escale 4096 (EVar 395)) (ELit 8192)
  (PShDisj (eaddz (eadd (escale 4096 (EVar 208)) (escale (-4096) (EVar 209))) 137439019008) (ELit 4096) (escale 4096 (EVar 396)) (ELit 4096)
  (PShDisj (eaddz (eadd (escale 4096 (EVar 208)) (escale (-4096) (EVar 209))) 137439019008) (ELit 4096) (escale 4096 (EVar 395)) (ELit 8192)
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (escale 4096 (EVar 396)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (escale 4096 (EVar 395)) (ELit 8192)
  (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (escale 4096 (EVar 396)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (escale 4096 (EVar 395)) (ELit 8192)
  (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (escale 4096 (EVar 396)) (ELit 4096)
  (PGhost (escale 4096 (EVar 394)) (ELit 8192)
  (PGhost (escale 4096 (EVar 397)) (ELit 4096)
  (PUnvis (eaddz (escale 4096 (EVar 395)) 4096) (ELit 4096)
  (PUnvis (escale 4096 (EVar 396)) (ELit 4096)
  (PFact (KDisj (SA (escale 4096 (EVar 394)) 0) (ELit 8192) (SA (ELit 2147446784) 0) (ELit 17592186048512))
  (PFact (KDisj (SA (escale 4096 (EVar 395)) 0) (ELit 8192) (SA (ELit 2147446784) 0) (ELit 17592186048512))
  (PFact (KDisj (SA (escale 4096 (EVar 396)) 0) (ELit 4096) (SA (ELit 2147446784) 0) (ELit 17592186048512))
  (PFact (KDisj (SA (escale 4096 (EVar 397)) 0) (ELit 4096) (SA (ELit 2147446784) 0) (ELit 17592186048512))
  (PFact (KRange (EVar 394) 1662 524277)
  (PFact (KRange (EVar 395) 1 34359736319)
  (PFact (KRange (EVar 396) 1 34359736319)
  (PFact (KRange (EVar 397) 1 34359736319)
  (PHavocBrk 0x67e000 0x8067f000
  (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 0 4095)
  (PFact (KRange (EVar 344) 0 1)
  (PHandoff 0 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_qc2 : plan :=
  PRun []
  (PX XMemcpy []
  (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 0 4095)
  (PFact (KRange (EVar 344) 0 1)
  (PHandoff 12 )))).

Definition startup_plan_tail3 : plan :=
  PRun [0x7879c]
  (PFresh 10 12 (Some (e_pd))
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x5ddfc]
  (PSplit e_atr8 17592186044384
  (startup_plan_qc2)
  (PSplit e_atr8 17592186044385
   (PRespell 13 (ELit 17594333495289)
    (PRespell 14 (ELit 17594333495289)
    (startup_plan_qc2)))
   (PSplit e_atr8 17592186044386
    (PRespell 13 (ELit 17594333495290)
     (PRespell 14 (ELit 17594333495290)
     (startup_plan_qc2)))
    (PSplit e_atr8 17592186044387
     (PRespell 13 (ELit 17594333495291)
      (PRespell 14 (ELit 17594333495291)
      (startup_plan_qc2)))
     (PSplit e_atr8 17592186044388
      (PRespell 13 (ELit 17594333495292)
       (PRespell 14 (ELit 17594333495292)
       (startup_plan_qc2)))
      (PSplit e_atr8 17592186044389
       (PRespell 13 (ELit 17594333495293)
        (PRespell 14 (ELit 17594333495293)
        (startup_plan_qc2)))
       (PSplit e_atr8 17592186044390
        (PRespell 13 (ELit 17594333495294)
         (PRespell 14 (ELit 17594333495294)
         (startup_plan_qc2)))
        (PRespell 13 (ELit 17594333495295)
         (PRespell 14 (ELit 17594333495295)
         (startup_plan_qc2)))))))))))))))))))).

Definition startup_plan_s2A4 : plan :=
  PBump 344
  (startup_plan_tail3).

Definition startup_plan_place5 : plan :=
  PShDisj (escale 4096 (EVar 228)) (ELit 65536) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 228)) (ELit 65536) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 245)) (ELit 4096) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 245)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 311)) (ELit 4096) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 311)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (escale 4096 (EVar 311)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 245)) (ELit 4096) (escale 4096 (EVar 311)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 228)) (ELit 65536) (escale 4096 (EVar 311)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 227)) (ELit 4096) (escale 4096 (EVar 311)) (ELit 4096)
  (PShDisj (eaddz (eadd (escale 4096 (EVar 208)) (escale (-4096) (EVar 209))) 137439019008) (ELit 4096) (escale 4096 (EVar 311)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (escale 4096 (EVar 311)) (ELit 4096)
  (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (escale 4096 (EVar 311)) (ELit 4096)
  (PSys YMunmap
  (PHandoff 11 ))))))))))))))))))))))))))))))))))))).

Definition startup_plan_segA : plan :=
  PRun [0x71440]
  (PX XMaxVA []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x65924]
  (PDropRange (ELit 0xd5f38) (ELit 0x12b0)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x78268]
  (PFresh 9 12 None
  (PRun []
  (PMmapIn
  (PSpin )
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 226)) (ELit 8388608) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 226)) (ELit 8388608) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 227)) (ELit 4096) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 227)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PMmap
  (PSpin )
  (PCase2 (EVar 228) 524263
  (startup_plan_place5)
  (PExt 2 [EVar 228]
   (startup_plan_place5)))))))))))))))
  (PSpin )))))))))))))))).

Definition startup_plan_segB : plan :=
  PSplit (EVar 6) 10
  (startup_plan_s2A4)
  (startup_plan_s2A4).

Definition startup_plan_segC : plan :=
  PSplit (EVar 5) 524277
  (PExt 4 []
   (PGhost (escale 4096 (EVar 394)) (ELit 8192)
   (PRun []
   (PSys YBrk
   (PRun []
   (PBrk2
   (startup_plan_brkfail1)
   (PRun []
    (PMmapIn
    (PSpin )
    (PIntro 1 1
    (PGhost (eaddz (escale 4096 (EVar 395)) 4096) (ELit 4096)
    (PIntro 1 1
    (PGhost (escale 4096 (EVar 396)) (ELit 4096)
    (PRun []
    (PMmap
    (PSpin )
    (PGhost (escale 4096 (EVar 397)) (ELit 4096)
    (PRun []
    (PX XIMemset []
    (PRun []
    (PX XIMemset []
    (PRun [0x8cacc]
    (PBump 437
    (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
    (PFog 0 8192
    (PFog 1 8192
    (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (ELit 65536) (ELit 6742016)
    (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (ELit 65536) (ELit 6742016)
    (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (ELit 65536) (ELit 6742016)
    (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (ELit 65536) (ELit 6742016)
    (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (escale 4096 (EVar 397)) (ELit 4096)
    (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (escale 4096 (EVar 394)) (ELit 8192)
    (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (escale 4096 (EVar 397)) (ELit 4096)
    (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (escale 4096 (EVar 394)) (ELit 8192)
    (PShDisj (escale 4096 (EVar 245)) (ELit 4096) (escale 4096 (EVar 397)) (ELit 4096)
    (PShDisj (escale 4096 (EVar 245)) (ELit 4096) (escale 4096 (EVar 394)) (ELit 8192)
    (PShDisj (escale 4096 (EVar 228)) (ELit 65536) (escale 4096 (EVar 397)) (ELit 4096)
    (PShDisj (escale 4096 (EVar 228)) (ELit 65536) (escale 4096 (EVar 394)) (ELit 8192)
    (PShDisj (escale 4096 (EVar 227)) (ELit 4096) (escale 4096 (EVar 397)) (ELit 4096)
    (PShDisj (escale 4096 (EVar 227)) (ELit 4096) (escale 4096 (EVar 394)) (ELit 8192)
    (PShDisj (eaddz (eadd (escale 4096 (EVar 208)) (escale (-4096) (EVar 209))) 137439019008) (ELit 4096) (escale 4096 (EVar 397)) (ELit 4096)
    (PShDisj (eaddz (eadd (escale 4096 (EVar 208)) (escale (-4096) (EVar 209))) 137439019008) (ELit 4096) (escale 4096 (EVar 394)) (ELit 8192)
    (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (escale 4096 (EVar 397)) (ELit 4096)
    (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (escale 4096 (EVar 394)) (ELit 8192)
    (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (escale 4096 (EVar 397)) (ELit 4096)
    (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (escale 4096 (EVar 394)) (ELit 8192)
    (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (escale 4096 (EVar 397)) (ELit 4096)
    (PUnvis (escale 4096 (EVar 394)) (ELit 8192)
    (PUnvis (escale 4096 (EVar 397)) (ELit 4096)
    (PGhost (eaddz (escale 4096 (EVar 395)) 4096) (ELit 4096)
    (PGhost (escale 4096 (EVar 396)) (ELit 4096)
    (PFact (KDisj (SA (escale 4096 (EVar 394)) 0) (ELit 8192) (SA (ELit 2147446784) 0) (ELit 17592186048512))
    (PFact (KDisj (SA (escale 4096 (EVar 395)) 0) (ELit 8192) (SA (ELit 2147446784) 0) (ELit 17592186048512))
    (PFact (KDisj (SA (escale 4096 (EVar 396)) 0) (ELit 4096) (SA (ELit 2147446784) 0) (ELit 17592186048512))
    (PFact (KDisj (SA (escale 4096 (EVar 397)) 0) (ELit 4096) (SA (ELit 2147446784) 0) (ELit 17592186048512))
    (PFact (KRange (EVar 394) 1662 524277)
    (PFact (KRange (EVar 395) 1 34359736319)
    (PFact (KRange (EVar 396) 1 34359736319)
    (PFact (KRange (EVar 397) 1 34359736319)
    (PHavocBrk 0x67e000 0x8067f000
    (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 0 4095)
    (PFact (KRange (EVar 344) 0 1)
    (PHandoff 0 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (PSpin )))))))))
  (PIntro 1662 524277
   (PGhost (escale 4096 (EVar 394)) (ELit 8192)
   (PRun []
   (PSys YBrk
   (PRun []
   (PSys YBrk
   (startup_plan_brkfail1))))))).

Definition startup_plan : plan :=
  PRun []
  (PX XIMemset []
  (PRun []
  (PX XEnvScan []
  (PRun []
  (PX XPnScan []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PSys YSetTid
  (PRun []
  (PRun [0xbc404]
  (PExt 1 [ELit 0x67b838; ELit 8]
  (PRun [0x71440]
  (PX XMaxVA []
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PMmap
  (PSpin )
  (PRun []
  (PMmap
  (PSpin )
  (PRun [0x70224]
  (PX XIStrncpy []
  (PRun [0x70224]
  (PX XIStrncpy []
  (PRun [0x6585c]
  (PDropRange (ELit 0x168100) (ELit 0xfff) (PDropRange (ELit 0x169100) (ELit 0xfff)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PX XIMemset []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun [0x49314]
  (PRun [0x497a0]
  (PRun [0x6e0d4]
  (PRun [0x6e554]
  (PRun [0x6e9cc]
  (PRun [0x49800]
  (PRun [0x6e0d4]
  (PRun [0x6e554]
  (PRun [0x6e9cc]
  (PRun [0x49850]
  (PRun [0x6e0d4]
  (PRun [0x6e554]
  (PRun [0x6e9cc]
  (PRun [0x49860]
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemset []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun [0x65860]
  (PDropRange (escale 4096 (EVar 78)) (ELit 0x10000)
  (PHandoff 10 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_ranges : list (Z * nat) := [(0x3bee0, 24%nat); (0x3c030, 20%nat); (0x3c1e0, 84%nat); (0x3e4b0, 12%nat); (0x3e500, 8%nat); (0x3e5d0, 8%nat); (0x3e6e0, 8%nat); (0x3e720, 4%nat); (0x3e740, 24%nat); (0x3e840, 48%nat); (0x3e990, 8%nat); (0x3e9e0, 20%nat); (0x3ea80, 20%nat); (0x3f6c0, 24%nat); (0x3f7b0, 12%nat); (0x42d50, 12%nat); (0x42e00, 8%nat); (0x43300, 32%nat); (0x433d0, 12%nat); (0x47f80, 48%nat); (0x48740, 16%nat); (0x48bc0, 876%nat); (0x499c0, 4%nat); (0x499e0, 8%nat); (0x49a40, 52%nat); (0x4cb20, 12%nat); (0x4d800, 4%nat); (0x52120, 36%nat); (0x531a0, 40%nat); (0x53260, 36%nat); (0x54090, 6628%nat); (0x5cd70, 92%nat); (0x5d5b0, 24%nat); (0x5d640, 40%nat); (0x5d750, 4%nat); (0x5d790, 12%nat); (0x5dd60, 104%nat); (0x5e350, 8%nat); (0x5e390, 8%nat); (0x5e580, 24%nat); (0x5e6b0, 12%nat); (0x5ef60, 4%nat); (0x5f9e0, 8%nat); (0x5fa10, 40%nat); (0x5fb70, 8%nat); (0x5fc40, 36%nat); (0x5fd70, 16%nat); (0x5ff00, 32%nat); (0x60390, 76%nat); (0x604f0, 20%nat); (0x60af0, 20%nat); (0x60b70, 8%nat); (0x60bb0, 12%nat); (0x60c70, 12%nat); (0x60cf0, 8%nat); (0x60d20, 4%nat); (0x64b60, 12%nat); (0x65300, 28%nat); (0x657c0, 44%nat); (0x65880, 104%nat); (0x65a70, 16%nat); (0x65ce0, 12%nat); (0x65d20, 40%nat); (0x65f50, 4%nat); (0x65fe0, 8%nat); (0x662c0, 4%nat); (0x66300, 108%nat); (0x664e0, 40%nat); (0x66770, 16%nat); (0x667f0, 8%nat); (0x67440, 16%nat); (0x67720, 36%nat); (0x67ce0, 4%nat); (0x67e60, 40%nat); (0x67f10, 8%nat); (0x67f50, 40%nat); (0x68270, 28%nat); (0x68300, 16%nat); (0x68400, 12%nat); (0x684f0, 8%nat); (0x68530, 24%nat); (0x68650, 32%nat); (0x68720, 12%nat); (0x68770, 20%nat); (0x687e0, 36%nat); (0x68920, 20%nat); (0x68a20, 32%nat); (0x68b10, 36%nat); (0x68bc0, 16%nat); (0x68c50, 48%nat); (0x68d60, 28%nat); (0x69e50, 44%nat); (0x69f70, 40%nat); (0x6a020, 36%nat); (0x6a630, 76%nat); (0x6a790, 12%nat); (0x6a7e0, 4%nat); (0x6a810, 8%nat); (0x6be30, 8%nat); (0x6c4d0, 8%nat); (0x6c500, 4%nat); (0x6c520, 4%nat); (0x6c540, 4%nat); (0x6c790, 12%nat); (0x6c7d0, 24%nat); (0x6cbe0, 4%nat); (0x6cc30, 4%nat); (0x6cef0, 12%nat); (0x6cf30, 32%nat); (0x6d0e0, 12%nat); (0x6d730, 92%nat); (0x6dbe0, 1204%nat); (0x6f360, 28%nat); (0x6f3f0, 24%nat); (0x6f4e0, 44%nat); (0x6f5b0, 20%nat); (0x6f670, 20%nat); (0x6f750, 12%nat); (0x6f7b0, 28%nat); (0x6f830, 32%nat); (0x6fa30, 20%nat); (0x6fa90, 20%nat); (0x6fd70, 12%nat); (0x6fdf0, 28%nat); (0x6fea0, 8%nat); (0x6fed0, 4%nat); (0x6ff40, 28%nat); (0x701b0, 12%nat); (0x70220, 24%nat); (0x70290, 4%nat); (0x70320, 44%nat); (0x705d0, 16%nat); (0x708c0, 24%nat); (0x71400, 68%nat); (0x71520, 4%nat); (0x71840, 16%nat); (0x71890, 4%nat); (0x71a60, 4%nat); (0x71cb0, 64%nat); (0x71e40, 28%nat); (0x72300, 68%nat); (0x729a0, 20%nat); (0x72af0, 12%nat); (0x73160, 8%nat); (0x74d60, 16%nat); (0x74dc0, 12%nat); (0x74fa0, 8%nat); (0x74ff0, 36%nat); (0x750a0, 24%nat); (0x75240, 20%nat); (0x758c0, 8%nat); (0x75910, 8%nat); (0x75990, 56%nat); (0x75a90, 8%nat); (0x75b50, 36%nat); (0x75c70, 20%nat); (0x75ce0, 4%nat); (0x75f20, 92%nat); (0x760f0, 4%nat); (0x76130, 16%nat); (0x76180, 48%nat); (0x76250, 64%nat); (0x763e0, 12%nat); (0x76d00, 44%nat); (0x76e30, 52%nat); (0x76f10, 28%nat); (0x77030, 48%nat); (0x778e0, 8%nat); (0x77920, 8%nat); (0x77af0, 4%nat); (0x78210, 36%nat); (0x78700, 44%nat); (0x78810, 12%nat); (0x789f0, 36%nat); (0x78c60, 4%nat); (0x78ca0, 4%nat); (0x78ce0, 32%nat); (0x78de0, 40%nat); (0x78e90, 12%nat); (0x79290, 4%nat); (0x79560, 64%nat); (0x79670, 48%nat); (0x79ab0, 12%nat); (0x79b10, 4%nat); (0x79ba0, 4%nat); (0x79d30, 40%nat); (0x79e30, 8%nat); (0x7a440, 12%nat); (0x7a4a0, 20%nat); (0x7a690, 8%nat); (0x7be90, 20%nat); (0x863c0, 264%nat); (0x86aa0, 12%nat); (0x86b20, 12%nat); (0x89270, 8%nat); (0x8c1d0, 28%nat); (0x8c250, 28%nat); (0x8c2e0, 104%nat); (0x8cac0, 4%nat); (0xbbad0, 32%nat); (0xbbb80, 28%nat); (0xbbce0, 92%nat); (0xbbf10, 72%nat); (0xbc100, 96%nat); (0xbc2ac, 94%nat); (0xbc604, 28%nat); (0xbc684, 24%nat); (0xbca74, 100%nat); (0xbcc14, 24%nat); (0xbd354, 8%nat); (0xbda04, 56%nat); (0xbdaf4, 140%nat); (0xbdd44, 12%nat); (0xbddc4, 12%nat); (0xbded4, 24%nat); (0xbdf94, 16%nat); (0xbdfe4, 60%nat); (0xbe234, 164%nat); (0xbe5d4, 156%nat); (0xbe8b4, 108%nat); (0xc0e84, 84%nat); (0xc6154, 8%nat); (0xc6264, 12%nat); (0xc62b4, 16%nat); (0xc6514, 12%nat); (0xc6554, 72%nat); (0xc6a24, 12%nat); (0xc6c24, 8%nat); (0xc6cb4, 8%nat); (0xc6d44, 64%nat); (0xc7e04, 12%nat); (0xc81a4, 60%nat); (0xc8524, 32%nat); (0xc85c4, 20%nat); (0xc86c4, 24%nat); (0xc8744, 24%nat); (0xc8db4, 28%nat)]%Z.
Definition startup_plan_ranges_0 : list (Z * nat) := [(0x3bee0, 24%nat); (0x42d50, 12%nat); (0x42e00, 8%nat); (0x43300, 32%nat); (0x433d0, 12%nat); (0x48bc0, 876%nat); (0x499c0, 4%nat); (0x499e0, 8%nat); (0x49a40, 52%nat); (0x5ced0, 4%nat); (0x5d5b0, 20%nat); (0x5d680, 24%nat); (0x5dd60, 20%nat); (0x5de90, 28%nat); (0x5e390, 4%nat); (0x5e580, 24%nat); (0x5e6b0, 12%nat); (0x5f9e0, 8%nat); (0x64b60, 12%nat); (0x65300, 28%nat); (0x657c0, 16%nat); (0x65810, 24%nat); (0x65880, 20%nat); (0x65ce0, 12%nat); (0x65d20, 16%nat); (0x66300, 108%nat); (0x667f0, 8%nat); (0x6a630, 76%nat); (0x6be30, 8%nat); (0x6c4d0, 8%nat); (0x6c500, 4%nat); (0x6c520, 4%nat); (0x6c540, 4%nat); (0x6c790, 12%nat); (0x6c7d0, 24%nat); (0x6cbe0, 4%nat); (0x6cc30, 4%nat); (0x6d750, 84%nat); (0x6dbe0, 1204%nat); (0x6f360, 28%nat); (0x6f3f0, 24%nat); (0x6f4e0, 44%nat); (0x6f5b0, 20%nat); (0x6f670, 20%nat); (0x6f750, 12%nat); (0x6f7b0, 28%nat); (0x6f830, 32%nat); (0x6fa30, 20%nat); (0x6fa90, 20%nat); (0x6fd70, 12%nat); (0x6fdf0, 28%nat); (0x6ff60, 20%nat); (0x701b0, 12%nat); (0x70220, 24%nat); (0x70290, 4%nat); (0x705d0, 16%nat); (0x708c0, 24%nat); (0x71400, 68%nat); (0x71520, 4%nat); (0x71cb0, 64%nat); (0x729a0, 20%nat); (0x72af0, 12%nat); (0x79560, 4%nat); (0x863c0, 264%nat); (0x89270, 8%nat); (0x8c300, 96%nat); (0x8cac0, 4%nat); (0xbbad0, 32%nat); (0xbbb80, 28%nat); (0xbbce0, 92%nat); (0xbbf10, 72%nat); (0xbc100, 96%nat); (0xbc2ac, 94%nat); (0xc8784, 8%nat)]%Z.
Definition startup_plan_ranges_A : list (Z * nat) := [(0x3c030, 20%nat); (0x3c1e0, 84%nat); (0x3e4b0, 12%nat); (0x3e500, 8%nat); (0x3e5d0, 8%nat); (0x3e6e0, 8%nat); (0x3e720, 4%nat); (0x3e740, 24%nat); (0x3e840, 48%nat); (0x3e990, 8%nat); (0x3e9e0, 20%nat); (0x3ea80, 20%nat); (0x3f6c0, 24%nat); (0x3f7b0, 12%nat); (0x4cb20, 12%nat); (0x4d800, 4%nat); (0x52120, 36%nat); (0x531a0, 40%nat); (0x53260, 36%nat); (0x54090, 6628%nat); (0x5cd70, 92%nat); (0x5d5b0, 24%nat); (0x5d640, 20%nat); (0x5d750, 4%nat); (0x5d790, 12%nat); (0x5e350, 8%nat); (0x5e390, 8%nat); (0x5e580, 24%nat); (0x5e6b0, 12%nat); (0x5ef60, 4%nat); (0x5f9e0, 8%nat); (0x5fa10, 40%nat); (0x5fb70, 8%nat); (0x5fc40, 32%nat); (0x5fd70, 16%nat); (0x5ff00, 32%nat); (0x60390, 76%nat); (0x604f0, 20%nat); (0x60af0, 20%nat); (0x60b70, 8%nat); (0x60bb0, 12%nat); (0x65300, 28%nat); (0x65860, 4%nat); (0x65880, 84%nat); (0x65a70, 16%nat); (0x65d80, 16%nat); (0x65f50, 4%nat); (0x664e0, 40%nat); (0x66770, 16%nat); (0x667f0, 8%nat); (0x67440, 16%nat); (0x67ce0, 4%nat); (0x67e60, 40%nat); (0x67f10, 8%nat); (0x67f50, 40%nat); (0x68270, 12%nat); (0x68720, 12%nat); (0x68770, 12%nat); (0x68b10, 20%nat); (0x68c50, 24%nat); (0x68d60, 28%nat); (0x69e60, 40%nat); (0x69f70, 40%nat); (0x6a020, 36%nat); (0x6a640, 60%nat); (0x6a740, 8%nat); (0x6a790, 12%nat); (0x6a7e0, 4%nat); (0x6a810, 8%nat); (0x6c4d0, 8%nat); (0x6c500, 4%nat); (0x6c520, 4%nat); (0x6c540, 4%nat); (0x6cbe0, 4%nat); (0x6cc30, 4%nat); (0x6cef0, 12%nat); (0x6cf30, 32%nat); (0x6d0e0, 12%nat); (0x6d730, 8%nat); (0x6fd70, 12%nat); (0x70320, 44%nat); (0x705d0, 16%nat); (0x71400, 68%nat); (0x71520, 4%nat); (0x71840, 16%nat); (0x71890, 4%nat); (0x71a60, 4%nat); (0x71cb0, 64%nat); (0x71e40, 28%nat); (0x72300, 68%nat); (0x729a0, 20%nat); (0x72af0, 12%nat); (0x73160, 8%nat); (0x758c0, 8%nat); (0x75910, 8%nat); (0x75990, 56%nat); (0x75a90, 8%nat); (0x75b50, 36%nat); (0x75c70, 20%nat); (0x75f20, 92%nat); (0x760f0, 4%nat); (0x76130, 16%nat); (0x76180, 48%nat); (0x76250, 64%nat); (0x763e0, 12%nat); (0x77030, 48%nat); (0x778e0, 8%nat); (0x77920, 8%nat); (0x77af0, 4%nat); (0x78210, 36%nat); (0x78700, 40%nat); (0x789f0, 36%nat); (0x78c60, 4%nat); (0x78ca0, 4%nat); (0x78ce0, 32%nat); (0x78de0, 32%nat); (0x79290, 4%nat); (0x79560, 64%nat); (0x79670, 48%nat); (0x79ab0, 12%nat); (0x79b10, 4%nat); (0x79ba0, 4%nat); (0x79d30, 40%nat); (0x79e30, 8%nat); (0x7a440, 12%nat); (0x7a4a0, 20%nat); (0x7a690, 8%nat); (0x7be90, 20%nat); (0xbbad0, 32%nat); (0xbbb80, 28%nat); (0xbbce0, 8%nat); (0xbc604, 28%nat); (0xbc684, 24%nat); (0xbcab4, 84%nat); (0xbcc14, 24%nat); (0xc6554, 72%nat); (0xc6a24, 12%nat); (0xc6c24, 8%nat); (0xc6cb4, 8%nat); (0xc6d44, 16%nat); (0xc7e04, 12%nat); (0xc81a4, 60%nat); (0xc8524, 32%nat); (0xc85c4, 20%nat); (0xc86c4, 24%nat); (0xc8744, 20%nat)]%Z.
Definition startup_plan_ranges_B : list (Z * nat) := [(0x47f80, 48%nat); (0x48740, 16%nat); (0x4d800, 4%nat); (0x52120, 36%nat); (0x5ced0, 4%nat); (0x5dd60, 80%nat); (0x5fa10, 40%nat); (0x5fb70, 8%nat); (0x5fc40, 36%nat); (0x5fd70, 16%nat); (0x60b70, 8%nat); (0x60c70, 12%nat); (0x60cf0, 8%nat); (0x60d20, 4%nat); (0x659c0, 8%nat); (0x65a70, 16%nat); (0x65fe0, 8%nat); (0x662c0, 4%nat); (0x68270, 28%nat); (0x68300, 16%nat); (0x68400, 12%nat); (0x684f0, 8%nat); (0x68530, 24%nat); (0x68650, 32%nat); (0x687a0, 8%nat); (0x687e0, 36%nat); (0x68920, 20%nat); (0x68a20, 32%nat); (0x68b50, 20%nat); (0x68bc0, 16%nat); (0x68cb0, 24%nat); (0x69e50, 4%nat); (0x6c4d0, 8%nat); (0x6c500, 4%nat); (0x6c520, 4%nat); (0x6c540, 4%nat); (0x705d0, 16%nat); (0x71cc0, 60%nat); (0x71e70, 16%nat); (0x729a0, 20%nat); (0x72af0, 12%nat); (0x75990, 36%nat); (0x75a90, 8%nat); (0x75b50, 24%nat); (0x75ce0, 4%nat); (0x76d00, 44%nat); (0x76e30, 52%nat); (0x76f10, 28%nat); (0x78700, 44%nat); (0x78810, 12%nat); (0x78d10, 20%nat); (0x78e20, 24%nat); (0x78e90, 12%nat); (0x86aa0, 12%nat); (0x86b20, 12%nat); (0xbd354, 8%nat); (0xbda04, 56%nat); (0xbdaf4, 32%nat); (0xbdce4, 16%nat); (0xbdd44, 12%nat); (0xbddc4, 12%nat); (0xbded4, 24%nat); (0xbdf94, 16%nat); (0xbdfe4, 12%nat); (0xbe054, 32%nat); (0xbe234, 12%nat); (0xc6154, 8%nat); (0xc6264, 12%nat); (0xc62b4, 16%nat); (0xc6514, 12%nat); (0xc6554, 72%nat); (0xc6d44, 36%nat); (0xc7e04, 12%nat)]%Z.
Definition startup_plan_ranges_C : list (Z * nat) := [(0x5de60, 16%nat); (0x657f0, 12%nat); (0x659e0, 16%nat); (0x65d50, 12%nat); (0x67720, 36%nat); (0x6cbe0, 4%nat); (0x6cc30, 4%nat); (0x6fdf0, 12%nat); (0x6fe50, 4%nat); (0x6fea0, 8%nat); (0x6fed0, 4%nat); (0x6ff40, 12%nat); (0x74d60, 16%nat); (0x74dc0, 12%nat); (0x74fa0, 8%nat); (0x74ff0, 36%nat); (0x750a0, 24%nat); (0x75240, 20%nat); (0x8c1d0, 28%nat); (0x8c250, 28%nat); (0x8c2e0, 12%nat); (0x8cac0, 4%nat); (0xbca74, 20%nat); (0xbda04, 24%nat); (0xbda84, 24%nat); (0xbdaf4, 124%nat); (0xbdff4, 56%nat); (0xbe234, 164%nat); (0xbe5d4, 156%nat); (0xbe8b4, 108%nat); (0xc0e84, 84%nat); (0xc6154, 8%nat); (0xc6264, 12%nat); (0xc62b4, 16%nat); (0xc6514, 12%nat); (0xc6a24, 12%nat); (0xc6c24, 8%nat); (0xc6cb4, 8%nat); (0xc6db4, 36%nat); (0xc8db4, 28%nat)]%Z.
