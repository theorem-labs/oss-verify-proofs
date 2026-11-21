(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup_plan_both_brkfail1 : plan :=
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
  (PRun [0x80834]
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

Definition startup_plan_both_qc2 : plan :=
  PRun []
  (PX XMemcpy []
  (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 0 4095)
  (PFact (KRange (EVar 344) 0 1)
  (PHandoff 12 )))).

Definition startup_plan_both_tail3 : plan :=
  PRun [0x6c318]
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
  (PRun [0x52048]
  (PSplit e_atr8 17592186044384
  (startup_plan_both_qc2)
  (PSplit e_atr8 17592186044385
   (PRespell 13 (ELit 17594333495289)
    (PRespell 14 (ELit 17594333495289)
    (startup_plan_both_qc2)))
   (PSplit e_atr8 17592186044386
    (PRespell 13 (ELit 17594333495290)
     (PRespell 14 (ELit 17594333495290)
     (startup_plan_both_qc2)))
    (PSplit e_atr8 17592186044387
     (PRespell 13 (ELit 17594333495291)
      (PRespell 14 (ELit 17594333495291)
      (startup_plan_both_qc2)))
     (PSplit e_atr8 17592186044388
      (PRespell 13 (ELit 17594333495292)
       (PRespell 14 (ELit 17594333495292)
       (startup_plan_both_qc2)))
      (PSplit e_atr8 17592186044389
       (PRespell 13 (ELit 17594333495293)
        (PRespell 14 (ELit 17594333495293)
        (startup_plan_both_qc2)))
       (PSplit e_atr8 17592186044390
        (PRespell 13 (ELit 17594333495294)
         (PRespell 14 (ELit 17594333495294)
         (startup_plan_both_qc2)))
        (PRespell 13 (ELit 17594333495295)
         (PRespell 14 (ELit 17594333495295)
         (startup_plan_both_qc2)))))))))))))))))))).

Definition startup_plan_both_s2A4 : plan :=
  PBump 344
  (startup_plan_both_tail3).

Definition startup_plan_both_place5 : plan :=
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

Definition startup_plan_both_segA : plan :=
  PRun [0x64fbc]
  (PX XMaxVA []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x594a0]
  (PDropRange (ELit 0x9f3f8) (ELit 0x12b0)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (ELit 65536) (ELit 6189056)
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x6bde4]
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
  (startup_plan_both_place5)
  (PExt 2 [EVar 228]
   (startup_plan_both_place5)))))))))))))))
  (PSpin )))))))))))))))).

Definition startup_plan_both_segB : plan :=
  PSplit (EVar 6) 10
  (startup_plan_both_s2A4)
  (startup_plan_both_s2A4).

Definition startup_plan_both_segC : plan :=
  PSplit (EVar 5) 524277
  (PExt 4 []
   (PGhost (escale 4096 (EVar 394)) (ELit 8192)
   (PRun []
   (PSys YBrk
   (PRun []
   (PBrk2
   (startup_plan_both_brkfail1)
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
    (PRun [0x80834]
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
   (startup_plan_both_brkfail1))))))).

Definition startup_plan_both : plan :=
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
  (PRun [0x890c8]
  (PExt 1 [ELit 0x5f4ad0; ELit 8]
  (PRun [0x64fbc]
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
  (PRun [0x63da0]
  (PX XIStrncpy []
  (PRun [0x63da0]
  (PX XIStrncpy []
  (PRun [0x593d8]
  (PDropRange (ELit 0x1315c0) (ELit 0xfff) (PDropRange (ELit 0x1325c0) (ELit 0xfff)
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
  (PRun [0x3e224]
  (PRun [0x3e6b0]
  (PRun [0x61c50]
  (PRun [0x620d0]
  (PRun [0x62548]
  (PRun [0x3e710]
  (PRun [0x61c50]
  (PRun [0x620d0]
  (PRun [0x62548]
  (PRun [0x3e760]
  (PRun [0x61c50]
  (PRun [0x620d0]
  (PRun [0x62548]
  (PRun [0x3e770]
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
  (PRun [0x593dc]
  (PDropRange (escale 4096 (EVar 78)) (ELit 0x10000)
  (PHandoff 10 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_both_ranges : list (Z * nat) := [(0x317f4, 20%nat); (0x31934, 20%nat); (0x31ae4, 84%nat); (0x33af4, 12%nat); (0x33b44, 8%nat); (0x33c14, 8%nat); (0x33d24, 8%nat); (0x33d64, 4%nat); (0x33d84, 24%nat); (0x33e84, 48%nat); (0x33fd4, 8%nat); (0x34024, 20%nat); (0x340c4, 20%nat); (0x34d04, 24%nat); (0x34df4, 12%nat); (0x38394, 12%nat); (0x38444, 8%nat); (0x38944, 32%nat); (0x38a14, 12%nat); (0x3d5c4, 48%nat); (0x3daa4, 888%nat); (0x3e8d4, 4%nat); (0x3e8f4, 4%nat); (0x3e954, 48%nat); (0x41a34, 12%nat); (0x42704, 4%nat); (0x46f74, 32%nat); (0x47f94, 40%nat); (0x48054, 36%nat); (0x48e84, 6624%nat); (0x51b54, 116%nat); (0x51d54, 36%nat); (0x51e64, 4%nat); (0x51ea4, 12%nat); (0x51fb4, 100%nat); (0x525a4, 4%nat); (0x525d4, 12%nat); (0x527c4, 24%nat); (0x52904, 12%nat); (0x52d34, 4%nat); (0x537b4, 52%nat); (0x53934, 8%nat); (0x53a04, 40%nat); (0x53b44, 16%nat); (0x53cd4, 28%nat); (0x54164, 76%nat); (0x542c4, 20%nat); (0x548c4, 16%nat); (0x54944, 8%nat); (0x54984, 8%nat); (0x54a44, 8%nat); (0x54ac4, 4%nat); (0x54af4, 4%nat); (0x586e4, 8%nat); (0x58e74, 28%nat); (0x59344, 44%nat); (0x59404, 104%nat); (0x595f4, 16%nat); (0x59864, 56%nat); (0x59ad4, 4%nat); (0x59b54, 12%nat); (0x59e34, 4%nat); (0x59e84, 108%nat); (0x5a064, 36%nat); (0x5a2e4, 16%nat); (0x5a364, 8%nat); (0x5afc4, 4%nat); (0x5afe4, 8%nat); (0x5b2a4, 32%nat); (0x5b854, 8%nat); (0x5b9e4, 36%nat); (0x5ba94, 4%nat); (0x5bac4, 44%nat); (0x5bdf4, 28%nat); (0x5be74, 20%nat); (0x5bf84, 12%nat); (0x5c064, 8%nat); (0x5c0b4, 20%nat); (0x5c1d4, 32%nat); (0x5c294, 16%nat); (0x5c2f4, 16%nat); (0x5c364, 32%nat); (0x5c494, 24%nat); (0x5c5a4, 32%nat); (0x5c684, 36%nat); (0x5c734, 20%nat); (0x5c7c4, 52%nat); (0x5c8d4, 28%nat); (0x5d9d4, 44%nat); (0x5dae4, 40%nat); (0x5dba4, 12%nat); (0x5dbe4, 16%nat); (0x5e1b4, 72%nat); (0x5e304, 12%nat); (0x5e354, 8%nat); (0x5e394, 4%nat); (0x5f9b4, 4%nat); (0x60054, 12%nat); (0x60094, 12%nat); (0x60314, 8%nat); (0x60344, 24%nat); (0x60764, 4%nat); (0x607a4, 4%nat); (0x60a74, 44%nat); (0x60c54, 12%nat); (0x612b4, 92%nat); (0x61754, 1208%nat); (0x62ed4, 28%nat); (0x62f74, 24%nat); (0x63064, 44%nat); (0x63134, 20%nat); (0x631e4, 20%nat); (0x632d4, 12%nat); (0x63324, 64%nat); (0x635b4, 16%nat); (0x63614, 20%nat); (0x638f4, 12%nat); (0x63974, 24%nat); (0x63a24, 8%nat); (0x63a54, 4%nat); (0x63ac4, 28%nat); (0x63d24, 12%nat); (0x63d94, 24%nat); (0x63e04, 4%nat); (0x63ea4, 40%nat); (0x64154, 16%nat); (0x64434, 24%nat); (0x64f84, 64%nat); (0x65094, 8%nat); (0x653b4, 20%nat); (0x65414, 4%nat); (0x655d4, 8%nat); (0x65834, 60%nat); (0x659c4, 28%nat); (0x65e74, 72%nat); (0x66514, 20%nat); (0x66664, 16%nat); (0x66ce4, 4%nat); (0x688d4, 20%nat); (0x68934, 12%nat); (0x68b14, 12%nat); (0x68b74, 32%nat); (0x68c24, 24%nat); (0x68dc4, 16%nat); (0x69434, 12%nat); (0x69484, 8%nat); (0x69504, 56%nat); (0x69604, 12%nat); (0x696d4, 36%nat); (0x697f4, 20%nat); (0x69854, 8%nat); (0x69aa4, 88%nat); (0x69c64, 8%nat); (0x69cb4, 16%nat); (0x69d04, 44%nat); (0x69dc4, 16%nat); (0x69e14, 44%nat); (0x69f64, 12%nat); (0x6a884, 40%nat); (0x6a9a4, 52%nat); (0x6aa84, 32%nat); (0x6aba4, 52%nat); (0x6b464, 8%nat); (0x6b494, 12%nat); (0x6b664, 8%nat); (0x6bd84, 36%nat); (0x6c284, 44%nat); (0x6c394, 8%nat); (0x6c564, 36%nat); (0x6c7e4, 4%nat); (0x6c814, 4%nat); (0x6c854, 36%nat); (0x6c964, 36%nat); (0x6ca14, 8%nat); (0x6ce14, 4%nat); (0x6d0d4, 120%nat); (0x6d634, 8%nat); (0x6d684, 8%nat); (0x6d724, 4%nat); (0x6d8a4, 44%nat); (0x6d9b4, 8%nat); (0x6dfc4, 12%nat); (0x6e014, 24%nat); (0x6e204, 8%nat); (0x6fa14, 20%nat); (0x79f34, 264%nat); (0x7a624, 12%nat); (0x7a6a4, 8%nat); (0x7cdf4, 4%nat); (0x7fd54, 28%nat); (0x7fdd4, 24%nat); (0x7fe54, 108%nat); (0x80824, 8%nat); (0x887a0, 28%nat); (0x88850, 24%nat); (0x889b0, 4%nat); (0x889d0, 80%nat); (0x88be0, 24%nat); (0x88c50, 40%nat); (0x88dd0, 48%nat); (0x88ea0, 40%nat); (0x88f70, 77%nat); (0x890b4, 12%nat); (0x892d4, 24%nat); (0x89354, 20%nat); (0x89744, 8%nat); (0x89774, 84%nat); (0x898e4, 20%nat); (0x8a024, 4%nat); (0x8a6d4, 52%nat); (0x8a7c4, 16%nat); (0x8a814, 100%nat); (0x8a9b4, 12%nat); (0x8aa14, 8%nat); (0x8aa94, 8%nat); (0x8aba4, 20%nat); (0x8ac64, 12%nat); (0x8acb4, 56%nat); (0x8af04, 72%nat); (0x8b034, 84%nat); (0x8b2a4, 4%nat); (0x8b2c4, 132%nat); (0x8b4e4, 8%nat); (0x8b584, 68%nat); (0x8b6a4, 32%nat); (0x8db54, 16%nat); (0x8dba4, 60%nat); (0x92c04, 4%nat); (0x92d14, 8%nat); (0x92d64, 12%nat); (0x92fc4, 8%nat); (0x93004, 64%nat); (0x934d4, 4%nat); (0x936c4, 4%nat); (0x93754, 8%nat); (0x937f4, 12%nat); (0x93834, 44%nat); (0x948a4, 12%nat); (0x94c54, 56%nat); (0x94fc4, 28%nat); (0x95074, 16%nat); (0x95164, 24%nat); (0x951f4, 20%nat); (0x95864, 12%nat); (0x958a4, 8%nat)]%Z.
Definition startup_plan_both_ranges_0 : list (Z * nat) := [(0x317f4, 20%nat); (0x38394, 12%nat); (0x38444, 8%nat); (0x38944, 32%nat); (0x38a14, 12%nat); (0x3dad4, 876%nat); (0x3e8d4, 4%nat); (0x3e8f4, 4%nat); (0x3e954, 48%nat); (0x51cb4, 20%nat); (0x51d84, 24%nat); (0x51fb4, 20%nat); (0x520e4, 24%nat); (0x525d4, 4%nat); (0x527c4, 24%nat); (0x52904, 12%nat); (0x537b4, 8%nat); (0x586e4, 8%nat); (0x58e74, 28%nat); (0x59344, 12%nat); (0x59384, 28%nat); (0x59404, 16%nat); (0x59864, 32%nat); (0x59e84, 108%nat); (0x5a364, 8%nat); (0x5e1b4, 28%nat); (0x5e234, 16%nat); (0x5e284, 20%nat); (0x5f9b4, 4%nat); (0x60054, 12%nat); (0x60094, 12%nat); (0x60314, 8%nat); (0x60344, 24%nat); (0x60764, 4%nat); (0x607a4, 4%nat); (0x612c4, 88%nat); (0x61754, 1208%nat); (0x62ed4, 28%nat); (0x62f74, 24%nat); (0x63064, 44%nat); (0x63134, 20%nat); (0x631e4, 20%nat); (0x632d4, 12%nat); (0x63324, 64%nat); (0x635b4, 16%nat); (0x63614, 20%nat); (0x638f4, 12%nat); (0x63974, 24%nat); (0x63ae4, 20%nat); (0x63d24, 12%nat); (0x63d94, 24%nat); (0x63e04, 4%nat); (0x64154, 12%nat); (0x64434, 24%nat); (0x64f84, 64%nat); (0x65094, 8%nat); (0x65834, 60%nat); (0x66514, 20%nat); (0x66664, 16%nat); (0x6d0d4, 4%nat); (0x79f34, 264%nat); (0x7cdf4, 4%nat); (0x7fe84, 96%nat); (0x80824, 4%nat); (0x887a0, 28%nat); (0x88850, 24%nat); (0x889b0, 4%nat); (0x889d0, 80%nat); (0x88be0, 24%nat); (0x88c50, 40%nat); (0x88dd0, 48%nat); (0x88ea0, 40%nat); (0x88f70, 77%nat); (0x890b4, 12%nat); (0x95224, 8%nat)]%Z.
Definition startup_plan_both_ranges_A : list (Z * nat) := [(0x31934, 20%nat); (0x31ae4, 84%nat); (0x33af4, 12%nat); (0x33b44, 8%nat); (0x33c14, 8%nat); (0x33d24, 8%nat); (0x33d64, 4%nat); (0x33d84, 24%nat); (0x33e84, 48%nat); (0x33fd4, 8%nat); (0x34024, 20%nat); (0x340c4, 20%nat); (0x34d04, 24%nat); (0x34df4, 12%nat); (0x41a34, 12%nat); (0x42704, 4%nat); (0x46f74, 32%nat); (0x47f94, 40%nat); (0x48054, 36%nat); (0x48e84, 6624%nat); (0x51b54, 116%nat); (0x51d54, 16%nat); (0x51e64, 4%nat); (0x51ea4, 12%nat); (0x525a4, 4%nat); (0x525d4, 12%nat); (0x527c4, 24%nat); (0x52904, 12%nat); (0x52d34, 4%nat); (0x537b4, 52%nat); (0x53934, 8%nat); (0x53a04, 36%nat); (0x53b44, 16%nat); (0x53cd4, 28%nat); (0x54164, 76%nat); (0x542c4, 20%nat); (0x548c4, 16%nat); (0x54944, 8%nat); (0x54984, 8%nat); (0x58e74, 28%nat); (0x593d4, 8%nat); (0x59404, 80%nat); (0x595f4, 16%nat); (0x598f4, 20%nat); (0x59ad4, 4%nat); (0x5a064, 36%nat); (0x5a2e4, 16%nat); (0x5a364, 8%nat); (0x5afc4, 4%nat); (0x5afe4, 8%nat); (0x5b854, 8%nat); (0x5b9e4, 36%nat); (0x5ba94, 4%nat); (0x5bac4, 44%nat); (0x5bdf4, 12%nat); (0x5c294, 16%nat); (0x5c2f4, 12%nat); (0x5c684, 20%nat); (0x5c7c4, 28%nat); (0x5c8d4, 28%nat); (0x5d9d4, 44%nat); (0x5dae4, 40%nat); (0x5dba4, 12%nat); (0x5dbe4, 16%nat); (0x5e1c4, 68%nat); (0x5e304, 12%nat); (0x5e354, 8%nat); (0x5e394, 4%nat); (0x60054, 12%nat); (0x60094, 12%nat); (0x60764, 4%nat); (0x607a4, 4%nat); (0x60a74, 44%nat); (0x60c54, 12%nat); (0x612b4, 8%nat); (0x638f4, 12%nat); (0x63ea4, 40%nat); (0x64154, 16%nat); (0x64f84, 64%nat); (0x65094, 8%nat); (0x653b4, 20%nat); (0x65414, 4%nat); (0x655d4, 8%nat); (0x65834, 60%nat); (0x659c4, 28%nat); (0x65e74, 72%nat); (0x66514, 20%nat); (0x66664, 16%nat); (0x66ce4, 4%nat); (0x69434, 12%nat); (0x69484, 8%nat); (0x69504, 56%nat); (0x69604, 12%nat); (0x696d4, 36%nat); (0x697f4, 20%nat); (0x69aa4, 88%nat); (0x69c64, 8%nat); (0x69cb4, 16%nat); (0x69d04, 44%nat); (0x69dc4, 16%nat); (0x69e14, 44%nat); (0x69f64, 12%nat); (0x6aba4, 52%nat); (0x6b464, 8%nat); (0x6b494, 12%nat); (0x6b664, 8%nat); (0x6bd84, 36%nat); (0x6c284, 40%nat); (0x6c564, 36%nat); (0x6c7e4, 4%nat); (0x6c814, 4%nat); (0x6c854, 36%nat); (0x6c964, 32%nat); (0x6ce14, 4%nat); (0x6d0e4, 116%nat); (0x6d634, 8%nat); (0x6d684, 8%nat); (0x6d724, 4%nat); (0x6d8a4, 44%nat); (0x6d9b4, 8%nat); (0x6dfc4, 12%nat); (0x6e014, 24%nat); (0x6e204, 8%nat); (0x6fa14, 20%nat); (0x887a0, 28%nat); (0x88850, 24%nat); (0x889b0, 4%nat); (0x892d4, 24%nat); (0x89354, 20%nat); (0x89784, 80%nat); (0x898e4, 20%nat); (0x93004, 64%nat); (0x934d4, 4%nat); (0x936c4, 4%nat); (0x93754, 8%nat); (0x937f4, 12%nat); (0x948a4, 12%nat); (0x94c54, 56%nat); (0x94fc4, 28%nat); (0x95074, 16%nat); (0x95164, 24%nat); (0x951f4, 16%nat)]%Z.
Definition startup_plan_both_ranges_B : list (Z * nat) := [(0x3d5c4, 48%nat); (0x3daa4, 12%nat); (0x42704, 4%nat); (0x46f74, 32%nat); (0x51cb4, 4%nat); (0x51fb4, 80%nat); (0x537d4, 44%nat); (0x53934, 8%nat); (0x53a04, 40%nat); (0x53b44, 16%nat); (0x54944, 8%nat); (0x54a44, 8%nat); (0x54ac4, 4%nat); (0x54af4, 4%nat); (0x59534, 12%nat); (0x595f4, 16%nat); (0x59b54, 12%nat); (0x59e34, 4%nat); (0x5bdf4, 28%nat); (0x5be74, 20%nat); (0x5bf84, 12%nat); (0x5c064, 8%nat); (0x5c0b4, 20%nat); (0x5c1d4, 32%nat); (0x5c314, 8%nat); (0x5c364, 32%nat); (0x5c494, 24%nat); (0x5c5a4, 32%nat); (0x5c6c4, 20%nat); (0x5c734, 20%nat); (0x5c824, 28%nat); (0x5d9d4, 4%nat); (0x60054, 12%nat); (0x60094, 12%nat); (0x64154, 16%nat); (0x65844, 56%nat); (0x659f4, 16%nat); (0x66514, 20%nat); (0x66664, 16%nat); (0x69504, 36%nat); (0x69614, 8%nat); (0x696d4, 24%nat); (0x69854, 8%nat); (0x6a884, 40%nat); (0x6a9a4, 52%nat); (0x6aa84, 32%nat); (0x6c284, 44%nat); (0x6c394, 8%nat); (0x6c894, 20%nat); (0x6c9a4, 20%nat); (0x6ca14, 8%nat); (0x7a624, 12%nat); (0x7a6a4, 8%nat); (0x8a024, 4%nat); (0x8a6d4, 52%nat); (0x8a7c4, 4%nat); (0x8a7e4, 8%nat); (0x8a814, 8%nat); (0x8a9b4, 12%nat); (0x8aa14, 8%nat); (0x8aa94, 8%nat); (0x8aba4, 20%nat); (0x8ac64, 12%nat); (0x8acb4, 8%nat); (0x8ad24, 28%nat); (0x8af04, 8%nat); (0x92c04, 4%nat); (0x92d14, 8%nat); (0x92d64, 12%nat); (0x92fc4, 8%nat); (0x93004, 64%nat); (0x937f4, 12%nat); (0x93834, 16%nat); (0x948a4, 12%nat)]%Z.
Definition startup_plan_both_ranges_C : list (Z * nat) := [(0x520b4, 16%nat); (0x59374, 8%nat); (0x59554, 20%nat); (0x598d4, 8%nat); (0x5b2a4, 32%nat); (0x60764, 4%nat); (0x607a4, 4%nat); (0x63974, 12%nat); (0x639c4, 4%nat); (0x63a24, 8%nat); (0x63a54, 4%nat); (0x63ac4, 8%nat); (0x688d4, 20%nat); (0x68934, 12%nat); (0x68b14, 12%nat); (0x68b74, 32%nat); (0x68c24, 24%nat); (0x68dc4, 16%nat); (0x7fd54, 28%nat); (0x7fdd4, 24%nat); (0x7fe54, 12%nat); (0x80834, 4%nat); (0x89744, 8%nat); (0x89774, 4%nat); (0x8a6d4, 20%nat); (0x8a754, 20%nat); (0x8a7c4, 16%nat); (0x8a814, 100%nat); (0x8acc4, 52%nat); (0x8af04, 72%nat); (0x8b034, 84%nat); (0x8b2a4, 4%nat); (0x8b2c4, 132%nat); (0x8b4e4, 8%nat); (0x8b584, 68%nat); (0x8b6a4, 32%nat); (0x8db54, 16%nat); (0x8dba4, 60%nat); (0x92c04, 4%nat); (0x92d14, 8%nat); (0x92d64, 12%nat); (0x92fc4, 8%nat); (0x934d4, 4%nat); (0x936c4, 4%nat); (0x93754, 8%nat); (0x93864, 32%nat); (0x95864, 12%nat); (0x958a4, 8%nat)]%Z.
