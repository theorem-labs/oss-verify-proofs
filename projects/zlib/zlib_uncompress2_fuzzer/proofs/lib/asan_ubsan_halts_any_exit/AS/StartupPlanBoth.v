(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import AsanPlan.
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
  (PRun [0x8cd40]
  (PBump 437
  (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PFog 0 8192
  (PFog 1 8192
  (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (ELit 65536) (ELit 6746112)
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
  (PFact (KRange (EVar 394) 1663 524277)
  (PFact (KRange (EVar 395) 1 34359736319)
  (PFact (KRange (EVar 396) 1 34359736319)
  (PFact (KRange (EVar 397) 1 34359736319)
  (PHavocBrk 0x67f000 0x80681000
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
  PRun [0x789b8]
  (PFresh 10 12 (Some (e_pd))
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x5e018]
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
  PShDisj (escale 4096 (EVar 228)) (ELit 65536) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 228)) (ELit 65536) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 245)) (ELit 4096) (ELit 65536) (ELit 6746112)
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
  (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 311)) (ELit 4096) (ELit 65536) (ELit 6746112)
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
  PRun [0x7165c]
  (PX XMaxVA []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x65b40]
  (PDropRange (ELit 0xd76b8) (ELit 0x12b0)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x78484]
  (PFresh 9 12 None
  (PRun []
  (PMmapIn
  (PSpin )
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 226)) (ELit 8388608) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 226)) (ELit 8388608) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 227)) (ELit 4096) (ELit 65536) (ELit 6746112)
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
    (PRun [0x8cd40]
    (PBump 437
    (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
    (PFog 0 8192
    (PFog 1 8192
    (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (ELit 65536) (ELit 6746112)
    (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (ELit 65536) (ELit 6746112)
    (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (ELit 65536) (ELit 6746112)
    (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen)
    (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (ELit 65536) (ELit 6746112)
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
    (PFact (KRange (EVar 394) 1663 524277)
    (PFact (KRange (EVar 395) 1 34359736319)
    (PFact (KRange (EVar 396) 1 34359736319)
    (PFact (KRange (EVar 397) 1 34359736319)
    (PHavocBrk 0x67f000 0x80681000
    (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 0 4095)
    (PFact (KRange (EVar 344) 0 1)
    (PHandoff 0 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (PSpin )))))))))
  (PIntro 1663 524277
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
  (PRun [0xbdba4]
  (PExt 1 [ELit 0x67cfb8; ELit 8]
  (PRun [0x7165c]
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
  (PRun [0x70440]
  (PX XIStrncpy []
  (PRun [0x70440]
  (PX XIStrncpy []
  (PRun [0x65a78]
  (PDropRange (ELit 0x169880) (ELit 0xfff) (PDropRange (ELit 0x16a880) (ELit 0xfff)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun []
  (PX XIMemset []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun [0x49530]
  (PRun [0x499bc]
  (PRun [0x6e2f0]
  (PRun [0x6e770]
  (PRun [0x6ebe8]
  (PRun [0x49a1c]
  (PRun [0x6e2f0]
  (PRun [0x6e770]
  (PRun [0x6ebe8]
  (PRun [0x49a6c]
  (PRun [0x6e2f0]
  (PRun [0x6e770]
  (PRun [0x6ebe8]
  (PRun [0x49a7c]
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
  (PRun [0x65a7c]
  (PDropRange (escale 4096 (EVar 78)) (ELit 0x10000)
  (PHandoff 10 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_both_ranges : list (Z * nat) := [(0x3bf68, 24%nat); (0x3c0b8, 20%nat); (0x3c268, 88%nat); (0x3e538, 16%nat); (0x3e588, 12%nat); (0x3e658, 12%nat); (0x3e768, 12%nat); (0x3e7a8, 36%nat); (0x3e8c8, 52%nat); (0x3ea08, 16%nat); (0x3ea58, 28%nat); (0x3eb08, 24%nat); (0x3f748, 24%nat); (0x3f838, 16%nat); (0x42dd8, 16%nat); (0x42e88, 12%nat); (0x43388, 36%nat); (0x43458, 12%nat); (0x48008, 52%nat); (0x487c8, 20%nat); (0x48dd8, 880%nat); (0x49bd8, 16%nat); (0x49c58, 52%nat); (0x4cd38, 16%nat); (0x4da18, 8%nat); (0x52338, 36%nat); (0x533b8, 44%nat); (0x53478, 40%nat); (0x542a8, 6628%nat); (0x5cf88, 96%nat); (0x5d7c8, 28%nat); (0x5d858, 40%nat); (0x5d968, 8%nat); (0x5d9a8, 16%nat); (0x5df78, 104%nat); (0x5e568, 28%nat); (0x5e788, 28%nat); (0x5e8c8, 16%nat); (0x5f178, 8%nat); (0x5fbf8, 56%nat); (0x5fd78, 12%nat); (0x5fe48, 44%nat); (0x5ff88, 20%nat); (0x60118, 36%nat); (0x605a8, 80%nat); (0x60708, 24%nat); (0x60d08, 24%nat); (0x60d88, 12%nat); (0x60dc8, 12%nat); (0x60e88, 16%nat); (0x60f08, 20%nat); (0x64d78, 12%nat); (0x65518, 32%nat); (0x659d8, 156%nat); (0x65c88, 20%nat); (0x65ef8, 60%nat); (0x66168, 8%nat); (0x661f8, 12%nat); (0x664c8, 12%nat); (0x66518, 112%nat); (0x666f8, 44%nat); (0x66988, 16%nat); (0x66a08, 8%nat); (0x67658, 20%nat); (0x67938, 36%nat); (0x67ee8, 12%nat); (0x68078, 56%nat); (0x68168, 44%nat); (0x68488, 56%nat); (0x68618, 16%nat); (0x686f8, 16%nat); (0x68748, 28%nat); (0x68868, 36%nat); (0x68928, 20%nat); (0x68988, 24%nat); (0x689f8, 40%nat); (0x68b38, 24%nat); (0x68c38, 36%nat); (0x68d28, 40%nat); (0x68dd8, 20%nat); (0x68e68, 52%nat); (0x68f78, 28%nat); (0x6a068, 48%nat); (0x6a178, 84%nat); (0x6a848, 76%nat); (0x6a9a8, 28%nat); (0x6aa28, 12%nat); (0x6c048, 8%nat); (0x6c6e8, 32%nat); (0x6c9a8, 44%nat); (0x6cdf8, 8%nat); (0x6ce48, 8%nat); (0x6d108, 48%nat); (0x6d2e8, 20%nat); (0x6d948, 96%nat); (0x6ddf8, 1208%nat); (0x6f568, 32%nat); (0x6f608, 28%nat); (0x6f6f8, 48%nat); (0x6f7c8, 24%nat); (0x6f878, 24%nat); (0x6f968, 16%nat); (0x6f9c8, 68%nat); (0x6fc48, 48%nat); (0x6ff88, 16%nat); (0x70008, 32%nat); (0x700b8, 20%nat); (0x70158, 32%nat); (0x703b8, 20%nat); (0x70438, 32%nat); (0x70538, 44%nat); (0x707e8, 20%nat); (0x70ac8, 28%nat); (0x71618, 68%nat); (0x71738, 8%nat); (0x71a48, 32%nat); (0x71c78, 8%nat); (0x71ec8, 68%nat); (0x72058, 32%nat); (0x72518, 72%nat); (0x72bb8, 24%nat); (0x72d08, 16%nat); (0x73378, 8%nat); (0x74f78, 36%nat); (0x751a8, 16%nat); (0x75208, 40%nat); (0x752b8, 28%nat); (0x75458, 24%nat); (0x75ac8, 16%nat); (0x75b18, 16%nat); (0x75b98, 80%nat); (0x75d68, 40%nat); (0x75e88, 36%nat); (0x76138, 92%nat); (0x76308, 8%nat); (0x76348, 68%nat); (0x76468, 64%nat); (0x765f8, 16%nat); (0x76f18, 44%nat); (0x77048, 52%nat); (0x77128, 32%nat); (0x77248, 52%nat); (0x77af8, 28%nat); (0x77d08, 8%nat); (0x78418, 40%nat); (0x78918, 48%nat); (0x78a28, 16%nat); (0x78c08, 36%nat); (0x78e78, 8%nat); (0x78ea8, 12%nat); (0x78ee8, 40%nat); (0x78ff8, 40%nat); (0x790a8, 16%nat); (0x794a8, 8%nat); (0x79778, 120%nat); (0x79cc8, 12%nat); (0x79d18, 12%nat); (0x79db8, 8%nat); (0x79f48, 44%nat); (0x7a048, 12%nat); (0x7a658, 16%nat); (0x7a6a8, 28%nat); (0x7a8a8, 8%nat); (0x7c0a8, 24%nat); (0x865d8, 268%nat); (0x86cb8, 16%nat); (0x86d38, 12%nat); (0x89488, 12%nat); (0x8c3e8, 64%nat); (0x8c4f8, 108%nat); (0x8cd28, 12%nat); (0xbd278, 32%nat); (0xbd328, 28%nat); (0xbd488, 92%nat); (0xbd6b8, 72%nat); (0xbd8a8, 96%nat); (0xbda4c, 96%nat); (0xbddac, 28%nat); (0xbde2c, 24%nat); (0xbe21c, 100%nat); (0xbe3bc, 24%nat); (0xbeafc, 8%nat); (0xbf1ac, 56%nat); (0xbf29c, 140%nat); (0xbf4ec, 12%nat); (0xbf56c, 12%nat); (0xbf67c, 24%nat); (0xbf73c, 16%nat); (0xbf78c, 60%nat); (0xbf9dc, 164%nat); (0xbfd7c, 156%nat); (0xc005c, 108%nat); (0xc262c, 84%nat); (0xc78fc, 8%nat); (0xc7a0c, 12%nat); (0xc7a5c, 16%nat); (0xc7cbc, 12%nat); (0xc7cfc, 72%nat); (0xc81cc, 12%nat); (0xc83cc, 8%nat); (0xc845c, 8%nat); (0xc84ec, 64%nat); (0xc95ac, 12%nat); (0xc994c, 60%nat); (0xc9ccc, 32%nat); (0xc9d6c, 20%nat); (0xc9e6c, 24%nat); (0xc9eec, 24%nat); (0xca55c, 28%nat)]%Z.
Definition startup_plan_both_ranges_0 : list (Z * nat) := [(0x3bf68, 24%nat); (0x42dd8, 16%nat); (0x42e88, 12%nat); (0x43388, 36%nat); (0x43458, 12%nat); (0x48dd8, 880%nat); (0x49bd8, 16%nat); (0x49c58, 52%nat); (0x5d0d8, 12%nat); (0x5d7c8, 20%nat); (0x5d898, 24%nat); (0x5df78, 24%nat); (0x5e0a8, 28%nat); (0x5e5a8, 8%nat); (0x5e788, 28%nat); (0x5e8c8, 16%nat); (0x5fbf8, 12%nat); (0x64d78, 12%nat); (0x65518, 32%nat); (0x659d8, 72%nat); (0x65ef8, 36%nat); (0x66518, 112%nat); (0x66a08, 8%nat); (0x6a848, 76%nat); (0x6c048, 8%nat); (0x6c6e8, 32%nat); (0x6c9a8, 44%nat); (0x6cdf8, 8%nat); (0x6ce48, 8%nat); (0x6d958, 92%nat); (0x6ddf8, 1208%nat); (0x6f568, 32%nat); (0x6f608, 28%nat); (0x6f6f8, 48%nat); (0x6f7c8, 24%nat); (0x6f878, 24%nat); (0x6f968, 16%nat); (0x6f9c8, 68%nat); (0x6fc48, 48%nat); (0x6ff88, 16%nat); (0x70008, 32%nat); (0x70178, 24%nat); (0x703b8, 20%nat); (0x70438, 32%nat); (0x707e8, 16%nat); (0x70ac8, 28%nat); (0x71618, 68%nat); (0x71738, 8%nat); (0x71ec8, 68%nat); (0x72bb8, 24%nat); (0x72d08, 16%nat); (0x79778, 8%nat); (0x865d8, 268%nat); (0x89488, 12%nat); (0x8c518, 100%nat); (0x8cd28, 8%nat); (0xbd278, 32%nat); (0xbd328, 28%nat); (0xbd488, 92%nat); (0xbd6b8, 72%nat); (0xbd8a8, 96%nat); (0xbda4c, 96%nat); (0xc9f2c, 8%nat)]%Z.
Definition startup_plan_both_ranges_A : list (Z * nat) := [(0x3c0b8, 20%nat); (0x3c268, 88%nat); (0x3e538, 16%nat); (0x3e588, 12%nat); (0x3e658, 12%nat); (0x3e768, 12%nat); (0x3e7a8, 36%nat); (0x3e8c8, 52%nat); (0x3ea08, 16%nat); (0x3ea58, 28%nat); (0x3eb08, 24%nat); (0x3f748, 24%nat); (0x3f838, 16%nat); (0x4cd38, 16%nat); (0x4da18, 8%nat); (0x52338, 36%nat); (0x533b8, 44%nat); (0x53478, 40%nat); (0x542a8, 6628%nat); (0x5cf88, 92%nat); (0x5d7c8, 28%nat); (0x5d858, 20%nat); (0x5d968, 8%nat); (0x5d9a8, 16%nat); (0x5e568, 28%nat); (0x5e788, 28%nat); (0x5e8c8, 16%nat); (0x5f178, 8%nat); (0x5fbf8, 56%nat); (0x5fd78, 12%nat); (0x5fe48, 40%nat); (0x5ff88, 20%nat); (0x60118, 36%nat); (0x605a8, 80%nat); (0x60708, 24%nat); (0x60d08, 24%nat); (0x60d88, 12%nat); (0x60dc8, 12%nat); (0x65518, 32%nat); (0x65a68, 96%nat); (0x65c88, 20%nat); (0x65f88, 24%nat); (0x66168, 8%nat); (0x666f8, 44%nat); (0x66988, 16%nat); (0x66a08, 8%nat); (0x67658, 20%nat); (0x67ee8, 12%nat); (0x68078, 56%nat); (0x68168, 44%nat); (0x68488, 16%nat); (0x68928, 20%nat); (0x68988, 16%nat); (0x68d28, 20%nat); (0x68e68, 28%nat); (0x68f78, 28%nat); (0x6a078, 44%nat); (0x6a178, 84%nat); (0x6a858, 72%nat); (0x6a9a8, 28%nat); (0x6aa28, 12%nat); (0x6c6e8, 32%nat); (0x6cdf8, 8%nat); (0x6ce48, 8%nat); (0x6d108, 48%nat); (0x6d2e8, 20%nat); (0x6d948, 12%nat); (0x6ff88, 16%nat); (0x70538, 44%nat); (0x707e8, 20%nat); (0x71618, 68%nat); (0x71738, 8%nat); (0x71a48, 32%nat); (0x71c78, 8%nat); (0x71ec8, 68%nat); (0x72058, 32%nat); (0x72518, 72%nat); (0x72bb8, 24%nat); (0x72d08, 16%nat); (0x73378, 8%nat); (0x75ac8, 16%nat); (0x75b18, 16%nat); (0x75b98, 80%nat); (0x75d68, 40%nat); (0x75e88, 24%nat); (0x76138, 92%nat); (0x76308, 8%nat); (0x76348, 68%nat); (0x76468, 64%nat); (0x765f8, 16%nat); (0x77248, 52%nat); (0x77af8, 28%nat); (0x77d08, 8%nat); (0x78418, 40%nat); (0x78918, 44%nat); (0x78c08, 36%nat); (0x78e78, 8%nat); (0x78ea8, 12%nat); (0x78ee8, 40%nat); (0x78ff8, 36%nat); (0x794a8, 8%nat); (0x79778, 120%nat); (0x79cc8, 12%nat); (0x79d18, 12%nat); (0x79db8, 8%nat); (0x79f48, 44%nat); (0x7a048, 12%nat); (0x7a658, 16%nat); (0x7a6a8, 28%nat); (0x7a8a8, 8%nat); (0x7c0a8, 24%nat); (0xbd278, 32%nat); (0xbd328, 28%nat); (0xbd488, 8%nat); (0xbddac, 28%nat); (0xbde2c, 24%nat); (0xbe25c, 84%nat); (0xbe3bc, 24%nat); (0xc7cfc, 72%nat); (0xc81cc, 12%nat); (0xc83cc, 8%nat); (0xc845c, 8%nat); (0xc84ec, 16%nat); (0xc95ac, 12%nat); (0xc994c, 60%nat); (0xc9ccc, 32%nat); (0xc9d6c, 20%nat); (0xc9e6c, 24%nat); (0xc9eec, 20%nat)]%Z.
Definition startup_plan_both_ranges_B : list (Z * nat) := [(0x48008, 52%nat); (0x487c8, 20%nat); (0x4da18, 8%nat); (0x52338, 36%nat); (0x5d0e8, 8%nat); (0x5df78, 84%nat); (0x5fc18, 48%nat); (0x5fd78, 12%nat); (0x5fe48, 44%nat); (0x5ff88, 20%nat); (0x60d88, 12%nat); (0x60e88, 16%nat); (0x60f08, 20%nat); (0x65bd8, 12%nat); (0x65c88, 20%nat); (0x661f8, 12%nat); (0x664c8, 12%nat); (0x68488, 56%nat); (0x68618, 16%nat); (0x686f8, 16%nat); (0x68748, 28%nat); (0x68868, 36%nat); (0x689a8, 16%nat); (0x689f8, 40%nat); (0x68b38, 24%nat); (0x68c38, 36%nat); (0x68d68, 24%nat); (0x68dd8, 20%nat); (0x68eb8, 32%nat); (0x6a068, 8%nat); (0x6c6e8, 32%nat); (0x707e8, 20%nat); (0x71ed8, 64%nat); (0x72088, 20%nat); (0x72bb8, 24%nat); (0x72d08, 16%nat); (0x75b98, 44%nat); (0x75ca8, 12%nat); (0x75d68, 28%nat); (0x75ee8, 12%nat); (0x76f18, 44%nat); (0x77048, 52%nat); (0x77128, 32%nat); (0x78918, 48%nat); (0x78a28, 16%nat); (0x78f28, 24%nat); (0x79038, 24%nat); (0x790a8, 16%nat); (0x86cb8, 16%nat); (0x86d38, 12%nat); (0xbeafc, 8%nat); (0xbf1ac, 56%nat); (0xbf29c, 32%nat); (0xbf48c, 16%nat); (0xbf4ec, 12%nat); (0xbf56c, 12%nat); (0xbf67c, 24%nat); (0xbf73c, 16%nat); (0xbf78c, 12%nat); (0xbf7fc, 32%nat); (0xbf9dc, 12%nat); (0xc78fc, 8%nat); (0xc7a0c, 12%nat); (0xc7a5c, 16%nat); (0xc7cbc, 12%nat); (0xc7cfc, 72%nat); (0xc84ec, 36%nat); (0xc95ac, 12%nat)]%Z.
Definition startup_plan_both_ranges_C : list (Z * nat) := [(0x5e078, 20%nat); (0x65a08, 12%nat); (0x65be8, 24%nat); (0x65f68, 12%nat); (0x67938, 36%nat); (0x6cdf8, 8%nat); (0x6ce48, 8%nat); (0x70008, 16%nat); (0x70068, 8%nat); (0x700b8, 20%nat); (0x70158, 16%nat); (0x74f78, 36%nat); (0x751a8, 16%nat); (0x75208, 40%nat); (0x752b8, 28%nat); (0x75458, 24%nat); (0x8c3e8, 64%nat); (0x8c4f8, 16%nat); (0x8cd38, 8%nat); (0xbe21c, 20%nat); (0xbf1ac, 24%nat); (0xbf22c, 24%nat); (0xbf29c, 124%nat); (0xbf79c, 56%nat); (0xbf9dc, 164%nat); (0xbfd7c, 156%nat); (0xc005c, 108%nat); (0xc262c, 84%nat); (0xc78fc, 8%nat); (0xc7a0c, 12%nat); (0xc7a5c, 16%nat); (0xc7cbc, 12%nat); (0xc81cc, 12%nat); (0xc83cc, 8%nat); (0xc845c, 8%nat); (0xc855c, 36%nat); (0xca55c, 28%nat)]%Z.
