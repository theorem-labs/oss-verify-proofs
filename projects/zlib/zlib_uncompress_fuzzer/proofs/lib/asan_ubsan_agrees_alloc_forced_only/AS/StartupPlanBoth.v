(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AsanPlan.
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
  (PRun [0x8caf4]
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
  PRun [0x787c4]
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
  (PRun [0x5de24]
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
  PRun [0x71468]
  (PX XMaxVA []
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x6594c]
  (PDropRange (ELit 0xd7438) (ELit 0x12b0)
  (PRun []
  (PMmap
  (PSpin )
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (ELit 65536) (ELit 6746112)
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (eaddz e_pd (-8388608)) (e_stkwlen)
  (PRun [0x78290]
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
    (PRun [0x8caf4]
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
  (PRun [0xbd904]
  (PExt 1 [ELit 0x67cd38; ELit 8]
  (PRun [0x71468]
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
  (PRun [0x7024c]
  (PX XIStrncpy []
  (PRun [0x7024c]
  (PX XIStrncpy []
  (PRun [0x65884]
  (PDropRange (ELit 0x169600) (ELit 0xfff) (PDropRange (ELit 0x16a600) (ELit 0xfff)
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
  (PRun [0x4933c]
  (PRun [0x497c8]
  (PRun [0x6e0fc]
  (PRun [0x6e57c]
  (PRun [0x6e9f4]
  (PRun [0x49828]
  (PRun [0x6e0fc]
  (PRun [0x6e57c]
  (PRun [0x6e9f4]
  (PRun [0x49878]
  (PRun [0x6e0fc]
  (PRun [0x6e57c]
  (PRun [0x6e9f4]
  (PRun [0x49888]
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
  (PRun [0x65888]
  (PDropRange (escale 4096 (EVar 78)) (ELit 0x10000)
  (PHandoff 10 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_both_ranges : list (Z * nat) := [(0x3bf10, 20%nat); (0x3c060, 16%nat); (0x3c200, 84%nat); (0x3e4d0, 12%nat); (0x3e530, 4%nat); (0x3e600, 8%nat); (0x3e700, 12%nat); (0x3e740, 36%nat); (0x3e870, 48%nat); (0x3e9b0, 12%nat); (0x3ea00, 24%nat); (0x3eaa0, 24%nat); (0x3f6e0, 24%nat); (0x3f7d0, 12%nat); (0x42d70, 12%nat); (0x42e30, 8%nat); (0x43330, 32%nat); (0x433f0, 12%nat); (0x47fa0, 28%nat); (0x48020, 20%nat); (0x48770, 12%nat); (0x48be0, 880%nat); (0x499e0, 16%nat); (0x49a70, 48%nat); (0x4cb40, 16%nat); (0x4d820, 4%nat); (0x52150, 32%nat); (0x531d0, 40%nat); (0x53290, 36%nat); (0x540c0, 6624%nat); (0x5cd90, 96%nat); (0x5d5e0, 24%nat); (0x5d670, 36%nat); (0x5d780, 4%nat); (0x5d7c0, 12%nat); (0x5dd90, 100%nat); (0x5e380, 4%nat); (0x5e3b0, 12%nat); (0x5e5a0, 24%nat); (0x5e6e0, 12%nat); (0x5ef90, 4%nat); (0x5fa10, 52%nat); (0x5fb90, 8%nat); (0x5fc60, 40%nat); (0x5fda0, 16%nat); (0x5ff30, 28%nat); (0x603c0, 76%nat); (0x60520, 20%nat); (0x60b20, 16%nat); (0x60ba0, 8%nat); (0x60be0, 8%nat); (0x60ca0, 8%nat); (0x60d20, 4%nat); (0x60d50, 4%nat); (0x64b90, 8%nat); (0x65320, 28%nat); (0x657f0, 44%nat); (0x658b0, 104%nat); (0x65aa0, 16%nat); (0x65d10, 56%nat); (0x65f80, 4%nat); (0x66000, 12%nat); (0x662e0, 4%nat); (0x66330, 108%nat); (0x66510, 36%nat); (0x66790, 16%nat); (0x66810, 8%nat); (0x67470, 4%nat); (0x67490, 8%nat); (0x67750, 32%nat); (0x67d00, 8%nat); (0x67e90, 36%nat); (0x67f40, 4%nat); (0x67f70, 44%nat); (0x682a0, 28%nat); (0x68320, 20%nat); (0x68430, 12%nat); (0x68510, 8%nat); (0x68560, 20%nat); (0x68680, 32%nat); (0x68740, 16%nat); (0x687a0, 16%nat); (0x68810, 32%nat); (0x68940, 24%nat); (0x68a50, 32%nat); (0x68b30, 36%nat); (0x68be0, 20%nat); (0x68c70, 52%nat); (0x68d80, 28%nat); (0x69e80, 44%nat); (0x69f90, 40%nat); (0x6a050, 12%nat); (0x6a090, 16%nat); (0x6a660, 72%nat); (0x6a7b0, 12%nat); (0x6a800, 8%nat); (0x6a840, 4%nat); (0x6be60, 4%nat); (0x6c500, 12%nat); (0x6c540, 12%nat); (0x6c7c0, 8%nat); (0x6c7f0, 24%nat); (0x6cc10, 4%nat); (0x6cc50, 4%nat); (0x6cf20, 44%nat); (0x6d100, 12%nat); (0x6d760, 92%nat); (0x6dc00, 1208%nat); (0x6f380, 28%nat); (0x6f420, 24%nat); (0x6f510, 44%nat); (0x6f5e0, 20%nat); (0x6f690, 20%nat); (0x6f780, 12%nat); (0x6f7d0, 64%nat); (0x6fa60, 16%nat); (0x6fac0, 20%nat); (0x6fda0, 12%nat); (0x6fe20, 24%nat); (0x6fed0, 8%nat); (0x6ff00, 4%nat); (0x6ff70, 28%nat); (0x701d0, 12%nat); (0x70240, 24%nat); (0x702b0, 4%nat); (0x70350, 40%nat); (0x70600, 16%nat); (0x708e0, 24%nat); (0x71430, 64%nat); (0x71540, 8%nat); (0x71860, 20%nat); (0x718c0, 4%nat); (0x71a80, 8%nat); (0x71ce0, 60%nat); (0x71e70, 28%nat); (0x72320, 72%nat); (0x729c0, 20%nat); (0x72b10, 16%nat); (0x73190, 4%nat); (0x74d80, 20%nat); (0x74de0, 12%nat); (0x74fc0, 12%nat); (0x75020, 32%nat); (0x750d0, 24%nat); (0x75270, 16%nat); (0x758e0, 12%nat); (0x75930, 8%nat); (0x759b0, 56%nat); (0x75ab0, 12%nat); (0x75b80, 36%nat); (0x75ca0, 20%nat); (0x75d00, 8%nat); (0x75f50, 88%nat); (0x76110, 8%nat); (0x76160, 16%nat); (0x761b0, 44%nat); (0x76270, 16%nat); (0x762c0, 44%nat); (0x76410, 12%nat); (0x76d30, 40%nat); (0x76e50, 52%nat); (0x76f30, 32%nat); (0x77050, 52%nat); (0x77910, 8%nat); (0x77940, 12%nat); (0x77b10, 8%nat); (0x78230, 36%nat); (0x78730, 44%nat); (0x78840, 8%nat); (0x78a10, 36%nat); (0x78c90, 4%nat); (0x78cc0, 4%nat); (0x78d00, 36%nat); (0x78e10, 36%nat); (0x78ec0, 8%nat); (0x792c0, 4%nat); (0x79580, 120%nat); (0x79ae0, 8%nat); (0x79b30, 8%nat); (0x79bd0, 4%nat); (0x79d50, 44%nat); (0x79e60, 8%nat); (0x7a470, 12%nat); (0x7a4c0, 24%nat); (0x7a6b0, 8%nat); (0x7bec0, 20%nat); (0x863e0, 264%nat); (0x86ad0, 12%nat); (0x86b50, 8%nat); (0x892a0, 4%nat); (0x8c200, 28%nat); (0x8c280, 24%nat); (0x8c300, 108%nat); (0x8cae0, 8%nat); (0xbcfe0, 28%nat); (0xbd080, 28%nat); (0xbd1e0, 96%nat); (0xbd420, 68%nat); (0xbd600, 96%nat); (0xbd7ac, 94%nat); (0xbdb04, 56%nat); (0xbdf74, 12%nat); (0xbdfb4, 84%nat); (0xbe114, 24%nat); (0xbe854, 8%nat); (0xbef14, 52%nat); (0xbeff4, 144%nat); (0xbf244, 12%nat); (0xbf2c4, 12%nat); (0xbf3d4, 24%nat); (0xbf4a4, 12%nat); (0xbf4e4, 60%nat); (0xbf734, 164%nat); (0xbfad4, 156%nat); (0xbfdb4, 108%nat); (0xc2384, 84%nat); (0xc7654, 12%nat); (0xc7774, 12%nat); (0xc77b4, 16%nat); (0xc7a14, 12%nat); (0xc7a64, 68%nat); (0xc7f24, 12%nat); (0xc8124, 8%nat); (0xc81b4, 8%nat); (0xc8254, 60%nat); (0xc9304, 12%nat); (0xc96a4, 60%nat); (0xc9a24, 32%nat); (0xc9ac4, 20%nat); (0xc9bc4, 24%nat); (0xc9c44, 24%nat); (0xca2c4, 24%nat)]%Z.
Definition startup_plan_both_ranges_0 : list (Z * nat) := [(0x3bf10, 20%nat); (0x42d70, 12%nat); (0x42e30, 8%nat); (0x43330, 32%nat); (0x433f0, 12%nat); (0x48be0, 880%nat); (0x499e0, 16%nat); (0x49a70, 48%nat); (0x5cef0, 8%nat); (0x5d5e0, 16%nat); (0x5d6a0, 24%nat); (0x5dd90, 20%nat); (0x5dec0, 24%nat); (0x5e3b0, 4%nat); (0x5e5a0, 24%nat); (0x5e6e0, 12%nat); (0x5fa10, 8%nat); (0x64b90, 8%nat); (0x65320, 28%nat); (0x657f0, 12%nat); (0x65830, 28%nat); (0x658b0, 16%nat); (0x65d10, 32%nat); (0x66330, 108%nat); (0x66810, 8%nat); (0x6a660, 28%nat); (0x6a6e0, 16%nat); (0x6a730, 20%nat); (0x6be60, 4%nat); (0x6c500, 12%nat); (0x6c540, 12%nat); (0x6c7c0, 8%nat); (0x6c7f0, 24%nat); (0x6cc10, 4%nat); (0x6cc50, 4%nat); (0x6d770, 88%nat); (0x6dc00, 1208%nat); (0x6f380, 28%nat); (0x6f420, 24%nat); (0x6f510, 44%nat); (0x6f5e0, 20%nat); (0x6f690, 20%nat); (0x6f780, 12%nat); (0x6f7d0, 64%nat); (0x6fa60, 16%nat); (0x6fac0, 20%nat); (0x6fda0, 12%nat); (0x6fe20, 24%nat); (0x6ff90, 20%nat); (0x701d0, 12%nat); (0x70240, 24%nat); (0x702b0, 4%nat); (0x70600, 12%nat); (0x708e0, 24%nat); (0x71430, 64%nat); (0x71540, 8%nat); (0x71ce0, 60%nat); (0x729c0, 20%nat); (0x72b10, 16%nat); (0x79580, 4%nat); (0x863e0, 264%nat); (0x892a0, 4%nat); (0x8c330, 96%nat); (0x8cae0, 8%nat); (0xbcfe0, 28%nat); (0xbd080, 28%nat); (0xbd1e0, 96%nat); (0xbd420, 68%nat); (0xbd600, 96%nat); (0xbd7ac, 94%nat); (0xc9c84, 8%nat)]%Z.
Definition startup_plan_both_ranges_A : list (Z * nat) := [(0x3c060, 16%nat); (0x3c200, 84%nat); (0x3e4d0, 12%nat); (0x3e530, 4%nat); (0x3e600, 8%nat); (0x3e700, 12%nat); (0x3e740, 36%nat); (0x3e870, 48%nat); (0x3e9b0, 12%nat); (0x3ea00, 24%nat); (0x3eaa0, 24%nat); (0x3f6e0, 24%nat); (0x3f7d0, 12%nat); (0x4cb40, 16%nat); (0x4d820, 4%nat); (0x52150, 32%nat); (0x531d0, 40%nat); (0x53290, 36%nat); (0x540c0, 6624%nat); (0x5cd90, 92%nat); (0x5d5e0, 24%nat); (0x5d670, 16%nat); (0x5d780, 4%nat); (0x5d7c0, 12%nat); (0x5e380, 4%nat); (0x5e3b0, 12%nat); (0x5e5a0, 24%nat); (0x5e6e0, 12%nat); (0x5ef90, 4%nat); (0x5fa10, 52%nat); (0x5fb90, 8%nat); (0x5fc60, 36%nat); (0x5fda0, 16%nat); (0x5ff30, 28%nat); (0x603c0, 76%nat); (0x60520, 20%nat); (0x60b20, 16%nat); (0x60ba0, 8%nat); (0x60be0, 8%nat); (0x65320, 28%nat); (0x65880, 8%nat); (0x658b0, 80%nat); (0x65aa0, 16%nat); (0x65da0, 20%nat); (0x65f80, 4%nat); (0x66510, 36%nat); (0x66790, 16%nat); (0x66810, 8%nat); (0x67470, 4%nat); (0x67490, 8%nat); (0x67d00, 8%nat); (0x67e90, 36%nat); (0x67f40, 4%nat); (0x67f70, 44%nat); (0x682a0, 12%nat); (0x68740, 16%nat); (0x687a0, 12%nat); (0x68b30, 20%nat); (0x68c70, 28%nat); (0x68d80, 28%nat); (0x69e80, 44%nat); (0x69f90, 40%nat); (0x6a050, 12%nat); (0x6a090, 16%nat); (0x6a670, 68%nat); (0x6a7b0, 12%nat); (0x6a800, 8%nat); (0x6a840, 4%nat); (0x6c500, 12%nat); (0x6c540, 12%nat); (0x6cc10, 4%nat); (0x6cc50, 4%nat); (0x6cf20, 44%nat); (0x6d100, 12%nat); (0x6d760, 8%nat); (0x6fda0, 12%nat); (0x70350, 40%nat); (0x70600, 16%nat); (0x71430, 64%nat); (0x71540, 8%nat); (0x71860, 20%nat); (0x718c0, 4%nat); (0x71a80, 8%nat); (0x71ce0, 60%nat); (0x71e70, 28%nat); (0x72320, 72%nat); (0x729c0, 20%nat); (0x72b10, 16%nat); (0x73190, 4%nat); (0x758e0, 12%nat); (0x75930, 8%nat); (0x759b0, 56%nat); (0x75ab0, 12%nat); (0x75b80, 36%nat); (0x75ca0, 20%nat); (0x75f50, 88%nat); (0x76110, 8%nat); (0x76160, 16%nat); (0x761b0, 44%nat); (0x76270, 16%nat); (0x762c0, 44%nat); (0x76410, 12%nat); (0x77050, 52%nat); (0x77910, 8%nat); (0x77940, 12%nat); (0x77b10, 8%nat); (0x78230, 36%nat); (0x78730, 40%nat); (0x78a10, 36%nat); (0x78c90, 4%nat); (0x78cc0, 4%nat); (0x78d00, 36%nat); (0x78e10, 32%nat); (0x792c0, 4%nat); (0x79590, 116%nat); (0x79ae0, 8%nat); (0x79b30, 8%nat); (0x79bd0, 4%nat); (0x79d50, 44%nat); (0x79e60, 8%nat); (0x7a470, 12%nat); (0x7a4c0, 24%nat); (0x7a6b0, 8%nat); (0x7bec0, 20%nat); (0xbcfe0, 28%nat); (0xbd080, 28%nat); (0xbd1e0, 12%nat); (0xbdb04, 56%nat); (0xbdfb4, 84%nat); (0xbe114, 24%nat); (0xc7a64, 68%nat); (0xc7f24, 12%nat); (0xc8124, 8%nat); (0xc81b4, 8%nat); (0xc8254, 16%nat); (0xc9304, 12%nat); (0xc96a4, 60%nat); (0xc9a24, 32%nat); (0xc9ac4, 20%nat); (0xc9bc4, 24%nat); (0xc9c44, 20%nat)]%Z.
Definition startup_plan_both_ranges_B : list (Z * nat) := [(0x47fa0, 28%nat); (0x48020, 20%nat); (0x48770, 12%nat); (0x4d820, 4%nat); (0x52150, 32%nat); (0x5cf00, 4%nat); (0x5dd90, 80%nat); (0x5fa30, 44%nat); (0x5fb90, 8%nat); (0x5fc60, 40%nat); (0x5fda0, 16%nat); (0x60ba0, 8%nat); (0x60ca0, 8%nat); (0x60d20, 4%nat); (0x60d50, 4%nat); (0x659e0, 12%nat); (0x65aa0, 16%nat); (0x66000, 12%nat); (0x662e0, 4%nat); (0x682a0, 28%nat); (0x68320, 20%nat); (0x68430, 12%nat); (0x68510, 8%nat); (0x68560, 20%nat); (0x68680, 32%nat); (0x687c0, 8%nat); (0x68810, 32%nat); (0x68940, 24%nat); (0x68a50, 32%nat); (0x68b70, 20%nat); (0x68be0, 20%nat); (0x68cd0, 28%nat); (0x69e80, 4%nat); (0x6c500, 12%nat); (0x6c540, 12%nat); (0x70600, 16%nat); (0x71cf0, 56%nat); (0x71ea0, 16%nat); (0x729c0, 20%nat); (0x72b10, 16%nat); (0x759b0, 36%nat); (0x75ac0, 8%nat); (0x75b80, 24%nat); (0x75d00, 8%nat); (0x76d30, 40%nat); (0x76e50, 52%nat); (0x76f30, 32%nat); (0x78730, 44%nat); (0x78840, 8%nat); (0x78d40, 20%nat); (0x78e50, 20%nat); (0x78ec0, 8%nat); (0x86ad0, 12%nat); (0x86b50, 8%nat); (0xbe854, 8%nat); (0xbef14, 52%nat); (0xbeff4, 32%nat); (0xbf1e4, 20%nat); (0xbf244, 12%nat); (0xbf2c4, 12%nat); (0xbf3d4, 24%nat); (0xbf4a4, 12%nat); (0xbf4e4, 12%nat); (0xbf554, 32%nat); (0xbf734, 12%nat); (0xc7654, 12%nat); (0xc7774, 12%nat); (0xc77b4, 16%nat); (0xc7a14, 12%nat); (0xc7a64, 68%nat); (0xc8254, 32%nat); (0xc9304, 12%nat)]%Z.
Definition startup_plan_both_ranges_C : list (Z * nat) := [(0x5de90, 16%nat); (0x65820, 8%nat); (0x65a00, 20%nat); (0x65d80, 8%nat); (0x67750, 32%nat); (0x6cc10, 4%nat); (0x6cc50, 4%nat); (0x6fe20, 12%nat); (0x6fe70, 4%nat); (0x6fed0, 8%nat); (0x6ff00, 4%nat); (0x6ff70, 8%nat); (0x74d80, 20%nat); (0x74de0, 12%nat); (0x74fc0, 12%nat); (0x75020, 32%nat); (0x750d0, 24%nat); (0x75270, 16%nat); (0x8c200, 28%nat); (0x8c280, 24%nat); (0x8c300, 12%nat); (0x8caf0, 4%nat); (0xbdf74, 12%nat); (0xbdfb4, 8%nat); (0xbef14, 24%nat); (0xbef84, 24%nat); (0xbeff4, 124%nat); (0xbf4f4, 56%nat); (0xbf734, 164%nat); (0xbfad4, 156%nat); (0xbfdb4, 108%nat); (0xc2384, 84%nat); (0xc7654, 12%nat); (0xc7774, 12%nat); (0xc77b4, 16%nat); (0xc7a14, 12%nat); (0xc7f24, 12%nat); (0xc8124, 8%nat); (0xc81b4, 8%nat); (0xc82b4, 36%nat); (0xca2c4, 24%nat)]%Z.
