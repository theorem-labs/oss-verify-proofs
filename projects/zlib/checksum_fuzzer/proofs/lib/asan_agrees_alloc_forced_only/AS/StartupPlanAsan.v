(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AsanPlan.
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
  (PRun [0x808f8]
  (PBump 437
  (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PFog 0 8192
  (PFog 1 8192
  (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (ELit 65536) (ELit 6189056)
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
  (PFact (KRange (EVar 394) 1527 524277)
  (PFact (KRange (EVar 395) 1 34359736319)
  (PFact (KRange (EVar 396) 1 34359736319)
  (PFact (KRange (EVar 397) 1 34359736319)
  (PHavocBrk 0x5f7000 0x805f9000
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
  PRun [0x6c390]
  (PFresh 10 12 (Some (e_pd))
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x520c0]
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
  PShDisj (escale 4096 (EVar 228)) (ELit 65536) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 228)) (ELit 65536) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 245)) (ELit 4096) (ELit 65536) (ELit 6189056)
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
  (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 311)) (ELit 4096) (ELit 65536) (ELit 6189056)
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
  PRun [0x65034]
  (PX XMaxVA []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x59518]
  (PDropRange (ELit 0x9f2f8) (ELit 0x12b0)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x6be5c]
  (PFresh 9 12 None
  (PRun []
  (PMmapIn
  (PSpin )
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 226)) (ELit 8388608) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 226)) (ELit 8388608) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 227)) (ELit 4096) (ELit 65536) (ELit 6189056)
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
    (PRun [0x808f8]
    (PBump 437
    (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
    (PFog 0 8192
    (PFog 1 8192
    (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (ELit 65536) (ELit 6189056)
    (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (ELit 65536) (ELit 6189056)
    (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (ELit 65536) (ELit 6189056)
    (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (ELit 65536) (ELit 6189056)
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
    (PFact (KRange (EVar 394) 1527 524277)
    (PFact (KRange (EVar 395) 1 34359736319)
    (PFact (KRange (EVar 396) 1 34359736319)
    (PFact (KRange (EVar 397) 1 34359736319)
    (PHavocBrk 0x5f7000 0x805f9000
    (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 0 4095)
    (PFact (KRange (EVar 344) 0 1)
    (PHandoff 0 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (PSpin )))))))))
  (PIntro 1527 524277
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
  (PRun [0x88f78]
  (PExt 1 [ELit 0x5f49d0; ELit 8]
  (PRun [0x65034]
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
  (PRun [0x63e18]
  (PX XIStrncpy []
  (PRun [0x63e18]
  (PX XIStrncpy []
  (PRun [0x59450]
  (PDropRange (ELit 0x1314c0) (ELit 0xfff) (PDropRange (ELit 0x1324c0) (ELit 0xfff)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PX XIMemset []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun [0x3e29c]
  (PRun [0x3e728]
  (PRun [0x61cc8]
  (PRun [0x62148]
  (PRun [0x625c0]
  (PRun [0x3e788]
  (PRun [0x61cc8]
  (PRun [0x62148]
  (PRun [0x625c0]
  (PRun [0x3e7d8]
  (PRun [0x61cc8]
  (PRun [0x62148]
  (PRun [0x625c0]
  (PRun [0x3e7e8]
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
  (PRun [0x59454]
  (PDropRange (escale 4096 (EVar 78)) (ELit 0x10000)
  (PHandoff 10 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_ranges : list (Z * nat) := [(0x31868, 20%nat); (0x319b8, 16%nat); (0x31b58, 84%nat); (0x33b68, 12%nat); (0x33bb8, 8%nat); (0x33c88, 12%nat); (0x33d98, 12%nat); (0x33dd8, 36%nat); (0x33f08, 48%nat); (0x34048, 12%nat); (0x34098, 24%nat); (0x34138, 24%nat); (0x34d78, 24%nat); (0x34e68, 12%nat); (0x38408, 12%nat); (0x384b8, 12%nat); (0x389c8, 28%nat); (0x38a88, 12%nat); (0x3d638, 28%nat); (0x3d6b8, 16%nat); (0x3db18, 888%nat); (0x3e948, 4%nat); (0x3e968, 8%nat); (0x3e9c8, 52%nat); (0x41aa8, 12%nat); (0x42788, 4%nat); (0x46fe8, 32%nat); (0x48008, 40%nat); (0x480c8, 36%nat); (0x48ef8, 6624%nat); (0x51bd8, 112%nat); (0x51dc8, 36%nat); (0x51ed8, 4%nat); (0x51f18, 12%nat); (0x52028, 100%nat); (0x52618, 8%nat); (0x52648, 12%nat); (0x52838, 24%nat); (0x52978, 12%nat); (0x52da8, 4%nat); (0x53828, 52%nat); (0x539a8, 8%nat); (0x53a78, 40%nat); (0x53bb8, 16%nat); (0x53d48, 32%nat); (0x541d8, 76%nat); (0x54338, 20%nat); (0x54938, 20%nat); (0x549b8, 8%nat); (0x549f8, 8%nat); (0x54ab8, 12%nat); (0x54b38, 8%nat); (0x54b68, 4%nat); (0x58758, 8%nat); (0x58ef8, 28%nat); (0x593b8, 44%nat); (0x59478, 104%nat); (0x59668, 16%nat); (0x598d8, 56%nat); (0x59b48, 4%nat); (0x59bd8, 8%nat); (0x59ea8, 8%nat); (0x59ef8, 108%nat); (0x5a0d8, 40%nat); (0x5a368, 12%nat); (0x5a3e8, 4%nat); (0x5b038, 16%nat); (0x5b318, 32%nat); (0x5b8c8, 8%nat); (0x5ba58, 40%nat); (0x5bb08, 8%nat); (0x5bb48, 40%nat); (0x5be68, 28%nat); (0x5bee8, 20%nat); (0x5bff8, 12%nat); (0x5c0d8, 12%nat); (0x5c128, 24%nat); (0x5c248, 32%nat); (0x5c308, 16%nat); (0x5c368, 20%nat); (0x5c3d8, 36%nat); (0x5c518, 20%nat); (0x5c618, 32%nat); (0x5c708, 36%nat); (0x5c7b8, 16%nat); (0x5c848, 48%nat); (0x5c958, 24%nat); (0x5da48, 44%nat); (0x5db58, 44%nat); (0x5dc18, 32%nat); (0x5e228, 72%nat); (0x5e388, 12%nat); (0x5e3c8, 8%nat); (0x5e408, 8%nat); (0x5fa28, 4%nat); (0x600c8, 8%nat); (0x600f8, 16%nat); (0x60388, 40%nat); (0x607d8, 4%nat); (0x60828, 4%nat); (0x60ae8, 12%nat); (0x60b28, 28%nat); (0x60cc8, 16%nat); (0x61328, 92%nat); (0x617d8, 1204%nat); (0x62f48, 28%nat); (0x62fe8, 24%nat); (0x630d8, 44%nat); (0x631a8, 20%nat); (0x63258, 20%nat); (0x63348, 12%nat); (0x633a8, 64%nat); (0x63628, 20%nat); (0x63688, 20%nat); (0x63968, 12%nat); (0x639e8, 28%nat); (0x63a98, 8%nat); (0x63ac8, 4%nat); (0x63b38, 28%nat); (0x63d98, 16%nat); (0x63e18, 28%nat); (0x63f18, 40%nat); (0x641c8, 16%nat); (0x644a8, 24%nat); (0x64ff8, 64%nat); (0x65118, 4%nat); (0x65428, 20%nat); (0x65488, 4%nat); (0x65658, 4%nat); (0x658a8, 64%nat); (0x65a38, 28%nat); (0x65ef8, 68%nat); (0x66598, 20%nat); (0x666e8, 12%nat); (0x66d58, 4%nat); (0x68958, 16%nat); (0x689a8, 12%nat); (0x68b88, 12%nat); (0x68be8, 36%nat); (0x68c98, 24%nat); (0x68e38, 20%nat); (0x694a8, 12%nat); (0x694f8, 12%nat); (0x69578, 60%nat); (0x69678, 12%nat); (0x69748, 36%nat); (0x69868, 20%nat); (0x698c8, 8%nat); (0x69b18, 88%nat); (0x69ce8, 4%nat); (0x69d28, 16%nat); (0x69d78, 44%nat); (0x69e48, 12%nat); (0x69e88, 44%nat); (0x69fd8, 12%nat); (0x6a8f8, 40%nat); (0x6aa28, 48%nat); (0x6ab08, 28%nat); (0x6ac28, 48%nat); (0x6b4d8, 8%nat); (0x6b508, 12%nat); (0x6b6e8, 4%nat); (0x6bdf8, 36%nat); (0x6c2f8, 44%nat); (0x6c408, 12%nat); (0x6c5e8, 32%nat); (0x6c858, 4%nat); (0x6c888, 8%nat); (0x6c8c8, 36%nat); (0x6c9d8, 36%nat); (0x6ca88, 12%nat); (0x6ce88, 4%nat); (0x6d158, 64%nat); (0x6d268, 48%nat); (0x6d6a8, 8%nat); (0x6d6f8, 8%nat); (0x6d798, 4%nat); (0x6d928, 40%nat); (0x6da28, 8%nat); (0x6e038, 12%nat); (0x6e088, 24%nat); (0x6e288, 4%nat); (0x6fa88, 20%nat); (0x79fb8, 264%nat); (0x7a698, 12%nat); (0x7a718, 8%nat); (0x7ce68, 8%nat); (0x7fdc8, 28%nat); (0x7fe48, 28%nat); (0x7fed8, 104%nat); (0x808e8, 8%nat); (0x88658, 28%nat); (0x886f8, 24%nat); (0x88858, 52%nat); (0x88938, 36%nat); (0x88a98, 20%nat); (0x88af8, 40%nat); (0x88c78, 96%nat); (0x88e20, 79%nat); (0x88f6c, 12%nat); (0x8918c, 24%nat); (0x891fc, 24%nat); (0x895fc, 4%nat); (0x8962c, 84%nat); (0x8979c, 16%nat); (0x89ecc, 4%nat); (0x8a58c, 48%nat); (0x8a67c, 116%nat); (0x8a85c, 16%nat); (0x8a8bc, 8%nat); (0x8a93c, 8%nat); (0x8aa5c, 16%nat); (0x8ab1c, 8%nat); (0x8ab5c, 56%nat); (0x8adac, 72%nat); (0x8aedc, 88%nat); (0x8b14c, 44%nat); (0x8b20c, 96%nat); (0x8b39c, 8%nat); (0x8b42c, 68%nat); (0x8b54c, 32%nat); (0x8d9fc, 80%nat); (0x92aac, 8%nat); (0x92bcc, 8%nat); (0x92c0c, 12%nat); (0x92e6c, 8%nat); (0x92ebc, 64%nat); (0x9337c, 8%nat); (0x9357c, 4%nat); (0x9360c, 4%nat); (0x936ac, 56%nat); (0x9475c, 8%nat); (0x94afc, 32%nat); (0x94b8c, 20%nat); (0x94e7c, 28%nat); (0x94f1c, 16%nat); (0x9501c, 20%nat); (0x9509c, 20%nat); (0x9571c, 8%nat); (0x9574c, 8%nat)]%Z.
Definition startup_plan_ranges_0 : list (Z * nat) := [(0x31868, 20%nat); (0x38408, 12%nat); (0x384b8, 12%nat); (0x389c8, 28%nat); (0x38a88, 12%nat); (0x3db48, 876%nat); (0x3e948, 4%nat); (0x3e968, 8%nat); (0x3e9c8, 52%nat); (0x51d28, 20%nat); (0x51e08, 20%nat); (0x52028, 20%nat); (0x52158, 24%nat); (0x52658, 4%nat); (0x52838, 24%nat); (0x52978, 12%nat); (0x53828, 8%nat); (0x58758, 8%nat); (0x58ef8, 28%nat); (0x593b8, 16%nat); (0x59408, 24%nat); (0x59478, 20%nat); (0x598d8, 32%nat); (0x59ef8, 108%nat); (0x5a3e8, 4%nat); (0x5e228, 28%nat); (0x5e2a8, 40%nat); (0x5fa28, 4%nat); (0x600c8, 8%nat); (0x600f8, 16%nat); (0x60388, 40%nat); (0x607d8, 4%nat); (0x60828, 4%nat); (0x61338, 88%nat); (0x617d8, 1204%nat); (0x62f48, 28%nat); (0x62fe8, 24%nat); (0x630d8, 44%nat); (0x631a8, 20%nat); (0x63258, 20%nat); (0x63348, 12%nat); (0x633a8, 64%nat); (0x63628, 20%nat); (0x63688, 20%nat); (0x63968, 12%nat); (0x639e8, 28%nat); (0x63b58, 20%nat); (0x63d98, 16%nat); (0x63e18, 28%nat); (0x641c8, 12%nat); (0x644a8, 24%nat); (0x64ff8, 64%nat); (0x65118, 4%nat); (0x658a8, 64%nat); (0x66598, 20%nat); (0x666e8, 12%nat); (0x6d158, 4%nat); (0x79fb8, 264%nat); (0x7ce68, 8%nat); (0x7fef8, 96%nat); (0x808e8, 4%nat); (0x88658, 28%nat); (0x886f8, 24%nat); (0x88858, 52%nat); (0x88938, 36%nat); (0x88a98, 20%nat); (0x88af8, 40%nat); (0x88c78, 96%nat); (0x88e20, 79%nat); (0x88f6c, 12%nat); (0x950dc, 4%nat)]%Z.
Definition startup_plan_ranges_A : list (Z * nat) := [(0x319b8, 16%nat); (0x31b58, 84%nat); (0x33b68, 12%nat); (0x33bb8, 8%nat); (0x33c88, 12%nat); (0x33d98, 12%nat); (0x33dd8, 36%nat); (0x33f08, 48%nat); (0x34048, 12%nat); (0x34098, 24%nat); (0x34138, 24%nat); (0x34d78, 24%nat); (0x34e68, 12%nat); (0x41aa8, 12%nat); (0x42788, 4%nat); (0x46fe8, 32%nat); (0x48008, 40%nat); (0x480c8, 36%nat); (0x48ef8, 6624%nat); (0x51bd8, 112%nat); (0x51dc8, 16%nat); (0x51ed8, 4%nat); (0x51f18, 12%nat); (0x52618, 8%nat); (0x52648, 12%nat); (0x52838, 24%nat); (0x52978, 12%nat); (0x52da8, 4%nat); (0x53828, 52%nat); (0x539a8, 8%nat); (0x53a78, 36%nat); (0x53bb8, 16%nat); (0x53d48, 32%nat); (0x541d8, 76%nat); (0x54338, 20%nat); (0x54938, 20%nat); (0x549b8, 8%nat); (0x549f8, 8%nat); (0x58ef8, 28%nat); (0x59448, 8%nat); (0x59478, 80%nat); (0x59668, 16%nat); (0x59968, 20%nat); (0x59b48, 4%nat); (0x5a0d8, 40%nat); (0x5a368, 12%nat); (0x5a3e8, 4%nat); (0x5b038, 16%nat); (0x5b8c8, 8%nat); (0x5ba58, 40%nat); (0x5bb08, 8%nat); (0x5bb48, 40%nat); (0x5be68, 12%nat); (0x5c308, 16%nat); (0x5c368, 12%nat); (0x5c708, 16%nat); (0x5c848, 24%nat); (0x5c958, 24%nat); (0x5da58, 40%nat); (0x5db58, 44%nat); (0x5dc18, 32%nat); (0x5e238, 60%nat); (0x5e338, 4%nat); (0x5e388, 12%nat); (0x5e3c8, 8%nat); (0x5e408, 8%nat); (0x600c8, 8%nat); (0x600f8, 16%nat); (0x607d8, 4%nat); (0x60828, 4%nat); (0x60ae8, 12%nat); (0x60b28, 28%nat); (0x60cc8, 16%nat); (0x61328, 8%nat); (0x63968, 12%nat); (0x63f18, 40%nat); (0x641c8, 16%nat); (0x64ff8, 64%nat); (0x65118, 4%nat); (0x65428, 20%nat); (0x65488, 4%nat); (0x65658, 4%nat); (0x658a8, 64%nat); (0x65a38, 28%nat); (0x65ef8, 68%nat); (0x66598, 20%nat); (0x666e8, 12%nat); (0x66d58, 4%nat); (0x694a8, 12%nat); (0x694f8, 12%nat); (0x69578, 60%nat); (0x69678, 12%nat); (0x69748, 36%nat); (0x69868, 20%nat); (0x69b18, 88%nat); (0x69ce8, 4%nat); (0x69d28, 16%nat); (0x69d78, 44%nat); (0x69e48, 12%nat); (0x69e88, 44%nat); (0x69fd8, 12%nat); (0x6ac28, 48%nat); (0x6b4d8, 8%nat); (0x6b508, 12%nat); (0x6b6e8, 4%nat); (0x6bdf8, 36%nat); (0x6c2f8, 40%nat); (0x6c5e8, 32%nat); (0x6c858, 4%nat); (0x6c888, 8%nat); (0x6c8c8, 36%nat); (0x6c9d8, 32%nat); (0x6ce88, 4%nat); (0x6d158, 64%nat); (0x6d268, 48%nat); (0x6d6a8, 8%nat); (0x6d6f8, 8%nat); (0x6d798, 4%nat); (0x6d928, 40%nat); (0x6da28, 8%nat); (0x6e038, 12%nat); (0x6e088, 24%nat); (0x6e288, 4%nat); (0x6fa88, 20%nat); (0x88658, 28%nat); (0x886f8, 24%nat); (0x88858, 8%nat); (0x8918c, 24%nat); (0x891fc, 24%nat); (0x8962c, 84%nat); (0x8979c, 16%nat); (0x92ebc, 64%nat); (0x9337c, 8%nat); (0x9357c, 4%nat); (0x9360c, 4%nat); (0x936ac, 12%nat); (0x9475c, 8%nat); (0x94afc, 32%nat); (0x94b8c, 20%nat); (0x94e7c, 28%nat); (0x94f1c, 16%nat); (0x9501c, 20%nat); (0x9509c, 16%nat)]%Z.
Definition startup_plan_ranges_B : list (Z * nat) := [(0x3d638, 28%nat); (0x3d6b8, 16%nat); (0x3db18, 16%nat); (0x42788, 4%nat); (0x46fe8, 32%nat); (0x51d38, 4%nat); (0x52028, 80%nat); (0x53848, 12%nat); (0x53888, 28%nat); (0x539a8, 8%nat); (0x53a78, 40%nat); (0x53bb8, 16%nat); (0x549b8, 8%nat); (0x54ab8, 12%nat); (0x54b38, 8%nat); (0x54b68, 4%nat); (0x595b8, 8%nat); (0x59668, 16%nat); (0x59bd8, 8%nat); (0x59ea8, 8%nat); (0x5be68, 28%nat); (0x5bee8, 20%nat); (0x5bff8, 12%nat); (0x5c0d8, 12%nat); (0x5c128, 24%nat); (0x5c248, 32%nat); (0x5c388, 12%nat); (0x5c3d8, 36%nat); (0x5c518, 20%nat); (0x5c618, 32%nat); (0x5c748, 20%nat); (0x5c7b8, 16%nat); (0x5c898, 28%nat); (0x5da48, 4%nat); (0x600c8, 8%nat); (0x600f8, 16%nat); (0x641c8, 16%nat); (0x658b8, 60%nat); (0x65a68, 16%nat); (0x66598, 20%nat); (0x666e8, 12%nat); (0x69578, 40%nat); (0x69688, 8%nat); (0x69748, 24%nat); (0x698c8, 8%nat); (0x6a8f8, 40%nat); (0x6aa28, 48%nat); (0x6ab08, 28%nat); (0x6c2f8, 44%nat); (0x6c408, 12%nat); (0x6c908, 20%nat); (0x6ca18, 20%nat); (0x6ca88, 12%nat); (0x7a698, 12%nat); (0x7a718, 8%nat); (0x89ecc, 4%nat); (0x8a58c, 48%nat); (0x8a67c, 24%nat); (0x8a85c, 16%nat); (0x8a8bc, 8%nat); (0x8a93c, 8%nat); (0x8aa5c, 16%nat); (0x8ab1c, 8%nat); (0x8ab5c, 8%nat); (0x8abcc, 28%nat); (0x8adac, 12%nat); (0x92aac, 8%nat); (0x92bcc, 8%nat); (0x92c0c, 12%nat); (0x92e6c, 8%nat); (0x92ebc, 64%nat); (0x936ac, 28%nat); (0x9475c, 8%nat)]%Z.
Definition startup_plan_ranges_C : list (Z * nat) := [(0x52128, 16%nat); (0x593e8, 8%nat); (0x595c8, 20%nat); (0x59948, 8%nat); (0x5b318, 32%nat); (0x607d8, 4%nat); (0x60828, 4%nat); (0x639e8, 12%nat); (0x63a48, 4%nat); (0x63a98, 8%nat); (0x63ac8, 4%nat); (0x63b38, 12%nat); (0x68958, 16%nat); (0x689a8, 12%nat); (0x68b88, 12%nat); (0x68be8, 36%nat); (0x68c98, 24%nat); (0x68e38, 20%nat); (0x7fdc8, 28%nat); (0x7fe48, 28%nat); (0x7fed8, 12%nat); (0x808f8, 4%nat); (0x895fc, 4%nat); (0x8962c, 4%nat); (0x8a58c, 20%nat); (0x8a60c, 16%nat); (0x8a67c, 116%nat); (0x8ab6c, 52%nat); (0x8adac, 72%nat); (0x8aedc, 88%nat); (0x8b14c, 44%nat); (0x8b20c, 96%nat); (0x8b39c, 8%nat); (0x8b42c, 68%nat); (0x8b54c, 32%nat); (0x8d9fc, 80%nat); (0x92aac, 8%nat); (0x92bcc, 8%nat); (0x92c0c, 12%nat); (0x92e6c, 8%nat); (0x9337c, 8%nat); (0x9357c, 4%nat); (0x9360c, 4%nat); (0x9370c, 32%nat); (0x9571c, 8%nat); (0x9574c, 8%nat)]%Z.
