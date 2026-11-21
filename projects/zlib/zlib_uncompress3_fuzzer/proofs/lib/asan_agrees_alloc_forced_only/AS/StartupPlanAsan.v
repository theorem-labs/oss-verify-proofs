(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AsanPlan.
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
  (PRun [0x8cde4]
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
  PRun [0x78990]
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
  (PRun [0x5dff0]
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
  PRun [0x71634]
  (PX XMaxVA []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x65b18]
  (PDropRange (ELit 0xd6278) (ELit 0x12b0)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (ELit 65536) (ELit 6742016)
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x7845c]
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
    (PRun [0x8cde4]
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
  (PRun [0xbc764]
  (PExt 1 [ELit 0x67bb78; ELit 8]
  (PRun [0x71634]
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
  (PRun [0x70418]
  (PX XIStrncpy []
  (PRun [0x70418]
  (PX XIStrncpy []
  (PRun [0x65a50]
  (PDropRange (ELit 0x168440) (ELit 0xfff) (PDropRange (ELit 0x169440) (ELit 0xfff)
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
  (PRun [0x49508]
  (PRun [0x49994]
  (PRun [0x6e2c8]
  (PRun [0x6e748]
  (PRun [0x6ebc0]
  (PRun [0x499f4]
  (PRun [0x6e2c8]
  (PRun [0x6e748]
  (PRun [0x6ebc0]
  (PRun [0x49a44]
  (PRun [0x6e2c8]
  (PRun [0x6e748]
  (PRun [0x6ebc0]
  (PRun [0x49a54]
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
  (PRun [0x65a54]
  (PDropRange (escale 4096 (EVar 78)) (ELit 0x10000)
  (PHandoff 10 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_ranges : list (Z * nat) := [(0x3bf40, 24%nat); (0x3c090, 20%nat); (0x3c240, 88%nat); (0x3e510, 16%nat); (0x3e560, 12%nat); (0x3e630, 12%nat); (0x3e740, 12%nat); (0x3e780, 36%nat); (0x3e8a0, 52%nat); (0x3e9e0, 16%nat); (0x3ea30, 28%nat); (0x3eae0, 24%nat); (0x3f720, 24%nat); (0x3f810, 16%nat); (0x42db0, 16%nat); (0x42e60, 12%nat); (0x43360, 36%nat); (0x43430, 12%nat); (0x47fe0, 52%nat); (0x487a0, 20%nat); (0x48db0, 880%nat); (0x49bb0, 16%nat); (0x49c30, 52%nat); (0x4cd10, 16%nat); (0x4d9f0, 8%nat); (0x52310, 36%nat); (0x53390, 44%nat); (0x53450, 40%nat); (0x54280, 6628%nat); (0x5cf60, 96%nat); (0x5d7a0, 28%nat); (0x5d830, 40%nat); (0x5d940, 8%nat); (0x5d980, 16%nat); (0x5df50, 104%nat); (0x5e540, 28%nat); (0x5e760, 28%nat); (0x5e8a0, 16%nat); (0x5f150, 8%nat); (0x5fbd0, 56%nat); (0x5fd50, 12%nat); (0x5fe20, 44%nat); (0x5ff60, 20%nat); (0x600f0, 36%nat); (0x60580, 80%nat); (0x606e0, 24%nat); (0x60ce0, 24%nat); (0x60d60, 12%nat); (0x60da0, 12%nat); (0x60e60, 16%nat); (0x60ee0, 20%nat); (0x64d50, 12%nat); (0x654f0, 32%nat); (0x659b0, 156%nat); (0x65c60, 20%nat); (0x65ed0, 60%nat); (0x66140, 8%nat); (0x661d0, 12%nat); (0x664a0, 12%nat); (0x664f0, 112%nat); (0x666d0, 44%nat); (0x66960, 16%nat); (0x669e0, 8%nat); (0x67630, 20%nat); (0x67910, 36%nat); (0x67ec0, 12%nat); (0x68050, 56%nat); (0x68140, 44%nat); (0x68460, 56%nat); (0x685f0, 16%nat); (0x686d0, 16%nat); (0x68720, 28%nat); (0x68840, 36%nat); (0x68900, 20%nat); (0x68960, 24%nat); (0x689d0, 40%nat); (0x68b10, 24%nat); (0x68c10, 36%nat); (0x68d00, 40%nat); (0x68db0, 20%nat); (0x68e40, 52%nat); (0x68f50, 28%nat); (0x6a040, 48%nat); (0x6a150, 84%nat); (0x6a820, 76%nat); (0x6a980, 28%nat); (0x6aa00, 12%nat); (0x6c020, 8%nat); (0x6c6c0, 32%nat); (0x6c980, 44%nat); (0x6cdd0, 8%nat); (0x6ce20, 8%nat); (0x6d0e0, 48%nat); (0x6d2c0, 20%nat); (0x6d920, 96%nat); (0x6ddd0, 1208%nat); (0x6f540, 32%nat); (0x6f5e0, 28%nat); (0x6f6d0, 48%nat); (0x6f7a0, 24%nat); (0x6f850, 24%nat); (0x6f940, 16%nat); (0x6f9a0, 68%nat); (0x6fc20, 48%nat); (0x6ff60, 16%nat); (0x6ffe0, 32%nat); (0x70090, 20%nat); (0x70130, 32%nat); (0x70390, 20%nat); (0x70410, 32%nat); (0x70510, 44%nat); (0x707c0, 20%nat); (0x70aa0, 28%nat); (0x715f0, 68%nat); (0x71710, 8%nat); (0x71a20, 32%nat); (0x71c50, 8%nat); (0x71ea0, 68%nat); (0x72030, 32%nat); (0x724f0, 72%nat); (0x72b90, 24%nat); (0x72ce0, 16%nat); (0x73350, 8%nat); (0x74f50, 36%nat); (0x75180, 16%nat); (0x751e0, 40%nat); (0x75290, 28%nat); (0x75430, 24%nat); (0x75aa0, 16%nat); (0x75af0, 16%nat); (0x75b70, 80%nat); (0x75d40, 40%nat); (0x75e60, 36%nat); (0x76110, 92%nat); (0x762e0, 8%nat); (0x76320, 68%nat); (0x76440, 64%nat); (0x765d0, 16%nat); (0x76ef0, 44%nat); (0x77020, 52%nat); (0x77100, 32%nat); (0x77220, 52%nat); (0x77ad0, 28%nat); (0x77ce0, 8%nat); (0x783f0, 40%nat); (0x788f0, 48%nat); (0x78a00, 16%nat); (0x78be0, 36%nat); (0x78e50, 8%nat); (0x78e80, 12%nat); (0x78ec0, 40%nat); (0x78fd0, 40%nat); (0x79080, 16%nat); (0x79480, 8%nat); (0x79750, 120%nat); (0x79ca0, 12%nat); (0x79cf0, 12%nat); (0x79d90, 8%nat); (0x79f20, 44%nat); (0x7a020, 12%nat); (0x7a630, 16%nat); (0x7a680, 28%nat); (0x7a880, 8%nat); (0x7c080, 24%nat); (0x865b0, 268%nat); (0x86c90, 16%nat); (0x86d10, 12%nat); (0x89460, 12%nat); (0x8c3c0, 64%nat); (0x8c4d0, 108%nat); (0x8cdd0, 8%nat); (0xbbe30, 32%nat); (0xbbee0, 28%nat); (0xbc040, 92%nat); (0xbc270, 72%nat); (0xbc460, 96%nat); (0xbc60c, 94%nat); (0xbc964, 28%nat); (0xbc9e4, 24%nat); (0xbcdd4, 100%nat); (0xbcf74, 24%nat); (0xbd6b4, 8%nat); (0xbdd64, 56%nat); (0xbde54, 140%nat); (0xbe0a4, 12%nat); (0xbe124, 12%nat); (0xbe234, 24%nat); (0xbe2f4, 16%nat); (0xbe344, 60%nat); (0xbe594, 164%nat); (0xbe934, 156%nat); (0xbec14, 108%nat); (0xc11e4, 84%nat); (0xc64b4, 8%nat); (0xc65c4, 12%nat); (0xc6614, 16%nat); (0xc6874, 12%nat); (0xc68b4, 72%nat); (0xc6d84, 12%nat); (0xc6f84, 8%nat); (0xc7014, 8%nat); (0xc70a4, 64%nat); (0xc8164, 12%nat); (0xc8504, 60%nat); (0xc8884, 32%nat); (0xc8924, 20%nat); (0xc8a24, 24%nat); (0xc8aa4, 24%nat); (0xc9114, 28%nat)]%Z.
Definition startup_plan_ranges_0 : list (Z * nat) := [(0x3bf40, 24%nat); (0x42db0, 16%nat); (0x42e60, 12%nat); (0x43360, 36%nat); (0x43430, 12%nat); (0x48db0, 880%nat); (0x49bb0, 16%nat); (0x49c30, 52%nat); (0x5d0b0, 12%nat); (0x5d7a0, 20%nat); (0x5d870, 24%nat); (0x5df50, 24%nat); (0x5e080, 28%nat); (0x5e580, 8%nat); (0x5e760, 28%nat); (0x5e8a0, 16%nat); (0x5fbd0, 12%nat); (0x64d50, 12%nat); (0x654f0, 32%nat); (0x659b0, 72%nat); (0x65ed0, 36%nat); (0x664f0, 112%nat); (0x669e0, 8%nat); (0x6a820, 76%nat); (0x6c020, 8%nat); (0x6c6c0, 32%nat); (0x6c980, 44%nat); (0x6cdd0, 8%nat); (0x6ce20, 8%nat); (0x6d930, 92%nat); (0x6ddd0, 1208%nat); (0x6f540, 32%nat); (0x6f5e0, 28%nat); (0x6f6d0, 48%nat); (0x6f7a0, 24%nat); (0x6f850, 24%nat); (0x6f940, 16%nat); (0x6f9a0, 68%nat); (0x6fc20, 48%nat); (0x6ff60, 16%nat); (0x6ffe0, 32%nat); (0x70150, 24%nat); (0x70390, 20%nat); (0x70410, 32%nat); (0x707c0, 16%nat); (0x70aa0, 28%nat); (0x715f0, 68%nat); (0x71710, 8%nat); (0x71ea0, 68%nat); (0x72b90, 24%nat); (0x72ce0, 16%nat); (0x79750, 8%nat); (0x865b0, 268%nat); (0x89460, 12%nat); (0x8c4f0, 100%nat); (0x8cdd0, 8%nat); (0xbbe30, 32%nat); (0xbbee0, 28%nat); (0xbc040, 92%nat); (0xbc270, 72%nat); (0xbc460, 96%nat); (0xbc60c, 94%nat); (0xc8ae4, 8%nat)]%Z.
Definition startup_plan_ranges_A : list (Z * nat) := [(0x3c090, 20%nat); (0x3c240, 88%nat); (0x3e510, 16%nat); (0x3e560, 12%nat); (0x3e630, 12%nat); (0x3e740, 12%nat); (0x3e780, 36%nat); (0x3e8a0, 52%nat); (0x3e9e0, 16%nat); (0x3ea30, 28%nat); (0x3eae0, 24%nat); (0x3f720, 24%nat); (0x3f810, 16%nat); (0x4cd10, 16%nat); (0x4d9f0, 8%nat); (0x52310, 36%nat); (0x53390, 44%nat); (0x53450, 40%nat); (0x54280, 6628%nat); (0x5cf60, 92%nat); (0x5d7a0, 28%nat); (0x5d830, 20%nat); (0x5d940, 8%nat); (0x5d980, 16%nat); (0x5e540, 28%nat); (0x5e760, 28%nat); (0x5e8a0, 16%nat); (0x5f150, 8%nat); (0x5fbd0, 56%nat); (0x5fd50, 12%nat); (0x5fe20, 40%nat); (0x5ff60, 20%nat); (0x600f0, 36%nat); (0x60580, 80%nat); (0x606e0, 24%nat); (0x60ce0, 24%nat); (0x60d60, 12%nat); (0x60da0, 12%nat); (0x654f0, 32%nat); (0x65a40, 96%nat); (0x65c60, 20%nat); (0x65f60, 24%nat); (0x66140, 8%nat); (0x666d0, 44%nat); (0x66960, 16%nat); (0x669e0, 8%nat); (0x67630, 20%nat); (0x67ec0, 12%nat); (0x68050, 56%nat); (0x68140, 44%nat); (0x68460, 16%nat); (0x68900, 20%nat); (0x68960, 16%nat); (0x68d00, 20%nat); (0x68e40, 28%nat); (0x68f50, 28%nat); (0x6a050, 44%nat); (0x6a150, 84%nat); (0x6a830, 72%nat); (0x6a980, 28%nat); (0x6aa00, 12%nat); (0x6c6c0, 32%nat); (0x6cdd0, 8%nat); (0x6ce20, 8%nat); (0x6d0e0, 48%nat); (0x6d2c0, 20%nat); (0x6d920, 12%nat); (0x6ff60, 16%nat); (0x70510, 44%nat); (0x707c0, 20%nat); (0x715f0, 68%nat); (0x71710, 8%nat); (0x71a20, 32%nat); (0x71c50, 8%nat); (0x71ea0, 68%nat); (0x72030, 32%nat); (0x724f0, 72%nat); (0x72b90, 24%nat); (0x72ce0, 16%nat); (0x73350, 8%nat); (0x75aa0, 16%nat); (0x75af0, 16%nat); (0x75b70, 80%nat); (0x75d40, 40%nat); (0x75e60, 24%nat); (0x76110, 92%nat); (0x762e0, 8%nat); (0x76320, 68%nat); (0x76440, 64%nat); (0x765d0, 16%nat); (0x77220, 52%nat); (0x77ad0, 28%nat); (0x77ce0, 8%nat); (0x783f0, 40%nat); (0x788f0, 44%nat); (0x78be0, 36%nat); (0x78e50, 8%nat); (0x78e80, 12%nat); (0x78ec0, 40%nat); (0x78fd0, 36%nat); (0x79480, 8%nat); (0x79750, 120%nat); (0x79ca0, 12%nat); (0x79cf0, 12%nat); (0x79d90, 8%nat); (0x79f20, 44%nat); (0x7a020, 12%nat); (0x7a630, 16%nat); (0x7a680, 28%nat); (0x7a880, 8%nat); (0x7c080, 24%nat); (0xbbe30, 32%nat); (0xbbee0, 28%nat); (0xbc040, 8%nat); (0xbc964, 28%nat); (0xbc9e4, 24%nat); (0xbce14, 84%nat); (0xbcf74, 24%nat); (0xc68b4, 72%nat); (0xc6d84, 12%nat); (0xc6f84, 8%nat); (0xc7014, 8%nat); (0xc70a4, 16%nat); (0xc8164, 12%nat); (0xc8504, 60%nat); (0xc8884, 32%nat); (0xc8924, 20%nat); (0xc8a24, 24%nat); (0xc8aa4, 20%nat)]%Z.
Definition startup_plan_ranges_B : list (Z * nat) := [(0x47fe0, 52%nat); (0x487a0, 20%nat); (0x4d9f0, 8%nat); (0x52310, 36%nat); (0x5d0c0, 8%nat); (0x5df50, 84%nat); (0x5fbf0, 48%nat); (0x5fd50, 12%nat); (0x5fe20, 44%nat); (0x5ff60, 20%nat); (0x60d60, 12%nat); (0x60e60, 16%nat); (0x60ee0, 20%nat); (0x65bb0, 12%nat); (0x65c60, 20%nat); (0x661d0, 12%nat); (0x664a0, 12%nat); (0x68460, 56%nat); (0x685f0, 16%nat); (0x686d0, 16%nat); (0x68720, 28%nat); (0x68840, 36%nat); (0x68980, 16%nat); (0x689d0, 40%nat); (0x68b10, 24%nat); (0x68c10, 36%nat); (0x68d40, 24%nat); (0x68db0, 20%nat); (0x68e90, 32%nat); (0x6a040, 8%nat); (0x6c6c0, 32%nat); (0x707c0, 20%nat); (0x71eb0, 64%nat); (0x72060, 20%nat); (0x72b90, 24%nat); (0x72ce0, 16%nat); (0x75b70, 44%nat); (0x75c80, 12%nat); (0x75d40, 28%nat); (0x75ec0, 12%nat); (0x76ef0, 44%nat); (0x77020, 52%nat); (0x77100, 32%nat); (0x788f0, 48%nat); (0x78a00, 16%nat); (0x78f00, 24%nat); (0x79010, 24%nat); (0x79080, 16%nat); (0x86c90, 16%nat); (0x86d10, 12%nat); (0xbd6b4, 8%nat); (0xbdd64, 56%nat); (0xbde54, 32%nat); (0xbe044, 16%nat); (0xbe0a4, 12%nat); (0xbe124, 12%nat); (0xbe234, 24%nat); (0xbe2f4, 16%nat); (0xbe344, 12%nat); (0xbe3b4, 32%nat); (0xbe594, 12%nat); (0xc64b4, 8%nat); (0xc65c4, 12%nat); (0xc6614, 16%nat); (0xc6874, 12%nat); (0xc68b4, 72%nat); (0xc70a4, 36%nat); (0xc8164, 12%nat)]%Z.
Definition startup_plan_ranges_C : list (Z * nat) := [(0x5e050, 20%nat); (0x659e0, 12%nat); (0x65bc0, 24%nat); (0x65f40, 12%nat); (0x67910, 36%nat); (0x6cdd0, 8%nat); (0x6ce20, 8%nat); (0x6ffe0, 16%nat); (0x70040, 8%nat); (0x70090, 20%nat); (0x70130, 16%nat); (0x74f50, 36%nat); (0x75180, 16%nat); (0x751e0, 40%nat); (0x75290, 28%nat); (0x75430, 24%nat); (0x8c3c0, 64%nat); (0x8c4d0, 16%nat); (0x8cdd0, 8%nat); (0xbcdd4, 20%nat); (0xbdd64, 24%nat); (0xbdde4, 24%nat); (0xbde54, 124%nat); (0xbe354, 56%nat); (0xbe594, 164%nat); (0xbe934, 156%nat); (0xbec14, 108%nat); (0xc11e4, 84%nat); (0xc64b4, 8%nat); (0xc65c4, 12%nat); (0xc6614, 16%nat); (0xc6874, 12%nat); (0xc6d84, 12%nat); (0xc6f84, 8%nat); (0xc7014, 8%nat); (0xc7114, 36%nat); (0xc9114, 28%nat)]%Z.
