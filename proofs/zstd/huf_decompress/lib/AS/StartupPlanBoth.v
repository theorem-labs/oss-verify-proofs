(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import AsanPlan.
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
  (PRun [0x8026c] 
  (PBump 437 
  (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat 
  (PFog 0 8192 
  (PFog 1 8192 
  (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen) 
  (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (ELit 65536) (ELit 6287360) 
  (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen) 
  (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (ELit 65536) (ELit 6287360) 
  (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen) 
  (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (ELit 65536) (ELit 6287360) 
  (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen) 
  (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (ELit 65536) (ELit 6287360) 
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
  (PFact (KRange (EVar 394) 1551 524277) 
  (PFact (KRange (EVar 395) 1 34359736319) 
  (PFact (KRange (EVar 396) 1 34359736319) 
  (PFact (KRange (EVar 397) 1 34359736319) 
  (PHavocBrk 0x60f000 0x80611000 
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
  PRun [0x6be08] 
  (PFresh 10 12 (Some (e_pd)) 
  (PRun [] 
  (PX XMemset [] 
  (PRun [] 
  (PX XMemset [] 
  (PRun [] 
  (PMmap 
  (PSpin )
  (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (ELit 65536) (ELit 6287360) 
  (PShDisj (escale 4096 (EVar 377)) (ELit 11571200) (eaddz e_pd (-8388608)) (e_stkwlen) 
  (PRun [0x51b38] 
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
  PShDisj (escale 4096 (EVar 228)) (ELit 65536) (ELit 65536) (ELit 6287360) 
  (PShDisj (escale 4096 (EVar 228)) (ELit 65536) (eaddz e_pd (-8388608)) (e_stkwlen) 
  (PRun [] 
  (PX XMemset [] 
  (PRun [] 
  (PMmap 
  (PSpin )
  (PShDisj (escale 4096 (EVar 245)) (ELit 4096) (ELit 65536) (ELit 6287360) 
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
  (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (ELit 65536) (ELit 6287360) 
  (PShDisj (escale 4096 (EVar 310)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen) 
  (PRun [] 
  (PMmap 
  (PSpin )
  (PShDisj (escale 4096 (EVar 311)) (ELit 4096) (ELit 65536) (ELit 6287360) 
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
  PRun [0x64aac] 
  (PX XMaxVA [] 
  (PRun [] 
  (PMmap 
  (PSpin )
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (ELit 65536) (ELit 6287360) 
  (PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (eaddz e_pd (-8388608)) (e_stkwlen) 
  (PRun [0x58f90] 
  (PDropRange (ELit 0xb7bf8) (ELit 0x12b0) 
  (PRun [] 
  (PMmap 
  (PSpin )
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (ELit 65536) (ELit 6287360) 
  (PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (eaddz e_pd (-8388608)) (e_stkwlen) 
  (PRun [0x6b8d4] 
  (PFresh 9 12 None 
  (PRun [] 
  (PMmapIn 
  (PSpin )
  (PRun [] 
  (PX XMemset [] 
  (PRun [] 
  (PMmap 
  (PSpin )
  (PShDisj (escale 4096 (EVar 226)) (ELit 8388608) (ELit 65536) (ELit 6287360) 
  (PShDisj (escale 4096 (EVar 226)) (ELit 8388608) (eaddz e_pd (-8388608)) (e_stkwlen) 
  (PRun [] 
  (PMmap 
  (PSpin )
  (PShDisj (escale 4096 (EVar 227)) (ELit 4096) (ELit 65536) (ELit 6287360) 
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
    (PRun [0x8026c] 
    (PBump 437 
    (PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat 
    (PFog 0 8192 
    (PFog 1 8192 
    (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen) 
    (PShDisj (escale 4096 (EVar 396)) (ELit 4096) (ELit 65536) (ELit 6287360) 
    (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen) 
    (PShDisj (escale 4096 (EVar 395)) (ELit 8192) (ELit 65536) (ELit 6287360) 
    (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (eaddz e_pd (-8388608)) (e_stkwlen) 
    (PShDisj (escale 4096 (EVar 397)) (ELit 4096) (ELit 65536) (ELit 6287360) 
    (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (eaddz e_pd (-8388608)) (e_stkwlen) 
    (PShDisj (escale 4096 (EVar 394)) (ELit 8192) (ELit 65536) (ELit 6287360) 
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
    (PFact (KRange (EVar 394) 1551 524277) 
    (PFact (KRange (EVar 395) 1 34359736319) 
    (PFact (KRange (EVar 396) 1 34359736319) 
    (PFact (KRange (EVar 397) 1 34359736319) 
    (PHavocBrk 0x60f000 0x80611000 
    (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 0 4095) 
    (PFact (KRange (EVar 344) 0 1) 
    (PHandoff 0 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (PSpin )))))))))
  (PIntro 1551 524277 
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
  (PRun [0xa1918] 
  (PExt 1 [ELit 0x60d2d0; ELit 8] 
  (PRun [0x64aac] 
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
  (PRun [0x63890] 
  (PX XIStrncpy [] 
  (PRun [0x63890] 
  (PX XIStrncpy [] 
  (PRun [0x58ec8] 
  (PDropRange (ELit 0x149dc0) (ELit 0xfff) (PDropRange (ELit 0x14adc0) (ELit 0xfff) 
  (PRun [] 
  (PMmap 
  (PSpin )
  (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (ELit 65536) (ELit 6287360) 
  (PShDisj (escale 4096 (EVar 78)) (ELit 65536) (eaddz e_pd (-8388608)) (e_stkwlen) 
  (PRun [] 
  (PX XIMemset [] 
  (PRun [] 
  (PX XIMemcpy [] 
  (PRun [] 
  (PX XIMemcpy [] 
  (PRun [0x3d638] 
  (PRun [0x3dac4] 
  (PRun [0x61740] 
  (PRun [0x61bc0] 
  (PRun [0x62038] 
  (PRun [0x3db24] 
  (PRun [0x61740] 
  (PRun [0x61bc0] 
  (PRun [0x62038] 
  (PRun [0x3db74] 
  (PRun [0x61740] 
  (PRun [0x61bc0] 
  (PRun [0x62038] 
  (PRun [0x3db84] 
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
  (PRun [0x58ecc] 
  (PDropRange (escale 4096 (EVar 78)) (ELit 0x10000) 
  (PHandoff 10 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).


Definition startup_plan_ranges : list (Z * nat) := [(0x30664, 27%nat); (0x307b4, 20%nat); (0x30964, 84%nat); (0x32974, 12%nat); (0x329c4, 8%nat); (0x32a94, 8%nat); (0x32ba4, 8%nat); (0x32be4, 32%nat); (0x32d04, 48%nat); (0x32e44, 12%nat); (0x32e94, 24%nat); (0x32f44, 20%nat); (0x33b84, 20%nat); (0x33c74, 12%nat); (0x37214, 12%nat); (0x372c4, 8%nat); (0x377c4, 32%nat); (0x37894, 8%nat); (0x3c444, 48%nat); (0x3cc04, 16%nat); (0x3cee4, 876%nat); (0x3dce4, 4%nat); (0x3dd04, 8%nat); (0x3dd64, 52%nat); (0x40e44, 12%nat); (0x41b24, 4%nat); (0x46384, 32%nat); (0x473a4, 40%nat); (0x47464, 36%nat); (0x48294, 6624%nat); (0x50f74, 92%nat); (0x517b4, 24%nat); (0x51844, 36%nat); (0x51954, 4%nat); (0x51994, 12%nat); (0x51aa4, 100%nat); (0x52094, 4%nat); (0x520c4, 12%nat); (0x522b4, 24%nat); (0x523f4, 12%nat); (0x52824, 4%nat); (0x532a4, 52%nat); (0x53424, 8%nat); (0x534f4, 40%nat); (0x53634, 16%nat); (0x537c4, 28%nat); (0x53c54, 76%nat); (0x53db4, 20%nat); (0x543b4, 16%nat); (0x54434, 8%nat); (0x54474, 8%nat); (0x54534, 8%nat); (0x545b4, 4%nat); (0x545e4, 4%nat); (0x581d4, 8%nat); (0x58964, 28%nat); (0x58e34, 44%nat); (0x58ef4, 104%nat); (0x590e4, 16%nat); (0x59354, 56%nat); (0x595c4, 4%nat); (0x59644, 12%nat); (0x59924, 4%nat); (0x59974, 156%nat); (0x59dd4, 16%nat); (0x59e54, 8%nat); (0x5aab4, 4%nat); (0x5aad4, 8%nat); (0x5ad94, 32%nat); (0x5b344, 8%nat); (0x5b4d4, 36%nat); (0x5b584, 4%nat); (0x5b5b4, 44%nat); (0x5b8e4, 28%nat); (0x5b964, 20%nat); (0x5ba74, 12%nat); (0x5bb54, 8%nat); (0x5bba4, 20%nat); (0x5bcc4, 32%nat); (0x5bd84, 16%nat); (0x5bde4, 16%nat); (0x5be54, 32%nat); (0x5bf84, 24%nat); (0x5c094, 32%nat); (0x5c174, 36%nat); (0x5c224, 20%nat); (0x5c2b4, 52%nat); (0x5c3c4, 28%nat); (0x5d4c4, 44%nat); (0x5d5d4, 40%nat); (0x5d694, 12%nat); (0x5d6d4, 16%nat); (0x5dca4, 72%nat); (0x5ddf4, 12%nat); (0x5de44, 8%nat); (0x5de84, 4%nat); (0x5f4a4, 16%nat); (0x5fb44, 12%nat); (0x5fb84, 12%nat); (0x5fe04, 8%nat); (0x5fe34, 24%nat); (0x60254, 4%nat); (0x60294, 4%nat); (0x60564, 44%nat); (0x60744, 12%nat); (0x60da4, 92%nat); (0x61244, 1208%nat); (0x629c4, 28%nat); (0x62a64, 24%nat); (0x62b54, 44%nat); (0x62c24, 20%nat); (0x62cd4, 20%nat); (0x62dc4, 12%nat); (0x62e14, 64%nat); (0x630a4, 16%nat); (0x63104, 20%nat); (0x633e4, 12%nat); (0x63464, 24%nat); (0x63514, 8%nat); (0x63544, 4%nat); (0x635b4, 28%nat); (0x63814, 12%nat); (0x63884, 24%nat); (0x638f4, 4%nat); (0x63994, 40%nat); (0x63c44, 16%nat); (0x63f24, 24%nat); (0x64a74, 64%nat); (0x64b84, 8%nat); (0x64ea4, 20%nat); (0x64f04, 4%nat); (0x650c4, 8%nat); (0x65324, 60%nat); (0x65424, 8%nat); (0x654b4, 28%nat); (0x65964, 76%nat); (0x65aa4, 20%nat); (0x66004, 20%nat); (0x66154, 16%nat); (0x66214, 60%nat); (0x66324, 4%nat); (0x66344, 8%nat); (0x663a4, 20%nat); (0x66564, 28%nat); (0x66654, 24%nat); (0x667d4, 4%nat); (0x668d4, 16%nat); (0x66b24, 36%nat); (0x66bc4, 40%nat); (0x66c74, 8%nat); (0x66ca4, 8%nat); (0x66ce4, 48%nat); (0x683c4, 20%nat); (0x68424, 12%nat); (0x68604, 12%nat); (0x68664, 32%nat); (0x68714, 24%nat); (0x688b4, 16%nat); (0x68f24, 12%nat); (0x68f74, 8%nat); (0x68ff4, 56%nat); (0x690f4, 12%nat); (0x691c4, 36%nat); (0x692e4, 20%nat); (0x69344, 8%nat); (0x69594, 88%nat); (0x69754, 8%nat); (0x697a4, 16%nat); (0x697f4, 44%nat); (0x698b4, 16%nat); (0x69904, 44%nat); (0x69a54, 12%nat); (0x6a374, 40%nat); (0x6a494, 52%nat); (0x6a574, 32%nat); (0x6a694, 52%nat); (0x6af54, 8%nat); (0x6af84, 12%nat); (0x6b154, 8%nat); (0x6b874, 36%nat); (0x6bd74, 44%nat); (0x6be84, 8%nat); (0x6c054, 36%nat); (0x6c2d4, 4%nat); (0x6c304, 4%nat); (0x6c344, 36%nat); (0x6c454, 36%nat); (0x6c504, 8%nat); (0x6c904, 4%nat); (0x6cbc4, 120%nat); (0x6d124, 8%nat); (0x6d174, 8%nat); (0x6d214, 4%nat); (0x6d394, 44%nat); (0x6d4a4, 8%nat); (0x6dab4, 12%nat); (0x6db04, 32%nat); (0x6dcf4, 8%nat); (0x6f504, 20%nat); (0x79a24, 264%nat); (0x7a114, 12%nat); (0x7a194, 8%nat); (0x7c8e4, 4%nat); (0x7f844, 28%nat); (0x7f8c4, 24%nat); (0x7f944, 108%nat); (0x80258, 8%nat); (0xa0ff0, 28%nat); (0xa10a0, 24%nat); (0xa1200, 4%nat); (0xa1220, 80%nat); (0xa1430, 24%nat); (0xa14a0, 40%nat); (0xa1620, 48%nat); (0xa16f0, 40%nat); (0xa17c0, 100%nat); (0xa1b20, 28%nat); (0xa1ba0, 21%nat); (0xa1f90, 97%nat); (0xa2130, 21%nat); (0xa2870, 5%nat); (0xa2f24, 52%nat); (0xa3010, 17%nat); (0xa3060, 137%nat); (0xa32e0, 9%nat); (0xa33f0, 21%nat); (0xa34b4, 12%nat); (0xa3500, 57%nat); (0xa3750, 73%nat); (0xa3880, 116%nat); (0xa3af0, 5%nat); (0xa3b10, 168%nat); (0xa3dc0, 73%nat); (0xa3ef0, 33%nat); (0xa63a0, 81%nat); (0xab450, 5%nat); (0xab560, 9%nat); (0xab5b0, 13%nat); (0xab810, 9%nat); (0xab850, 68%nat); (0xabd20, 8%nat); (0xabf14, 7%nat); (0xabfa4, 8%nat); (0xac040, 13%nat); (0xac080, 45%nat); (0xad0f4, 12%nat); (0xad4a0, 57%nat); (0xad814, 31%nat); (0xad8c0, 17%nat); (0xad9b4, 24%nat); (0xada40, 21%nat); (0xae0b0, 13%nat); (0xae0f0, 9%nat)]%Z.

Definition startup_plan_ranges_0 : list (Z * nat) := [(0x30664, 27%nat); (0x37214, 12%nat); (0x372c4, 8%nat); (0x377c4, 32%nat); (0x37894, 8%nat); (0x3cee4, 876%nat); (0x3dce4, 4%nat); (0x3dd04, 8%nat); (0x3dd64, 52%nat); (0x510c4, 8%nat); (0x517b4, 16%nat); (0x51874, 24%nat); (0x51aa4, 20%nat); (0x51bd4, 24%nat); (0x520c4, 4%nat); (0x522b4, 24%nat); (0x523f4, 12%nat); (0x532a4, 8%nat); (0x581d4, 8%nat); (0x58964, 28%nat); (0x58e34, 12%nat); (0x58e74, 28%nat); (0x58ef4, 16%nat); (0x59354, 32%nat); (0x59974, 120%nat); (0x59e54, 8%nat); (0x5dca4, 28%nat); (0x5dd24, 16%nat); (0x5dd74, 20%nat); (0x5f4a4, 16%nat); (0x5fb44, 12%nat); (0x5fb84, 12%nat); (0x5fe04, 8%nat); (0x5fe34, 24%nat); (0x60254, 4%nat); (0x60294, 4%nat); (0x60db4, 88%nat); (0x61244, 1208%nat); (0x629c4, 28%nat); (0x62a64, 24%nat); (0x62b54, 44%nat); (0x62c24, 20%nat); (0x62cd4, 20%nat); (0x62dc4, 12%nat); (0x62e14, 64%nat); (0x630a4, 16%nat); (0x63104, 20%nat); (0x633e4, 12%nat); (0x63464, 24%nat); (0x635d4, 20%nat); (0x63814, 12%nat); (0x63884, 24%nat); (0x638f4, 4%nat); (0x63c44, 12%nat); (0x63f24, 24%nat); (0x64a74, 64%nat); (0x64b84, 8%nat); (0x65324, 60%nat); (0x65424, 8%nat); (0x66004, 20%nat); (0x66154, 16%nat); (0x6cbc4, 4%nat); (0x79a24, 264%nat); (0x7c8e4, 4%nat); (0x7f974, 96%nat); (0x80258, 8%nat); (0xa0ff0, 28%nat); (0xa10a0, 24%nat); (0xa1200, 4%nat); (0xa1220, 80%nat); (0xa1430, 24%nat); (0xa14a0, 40%nat); (0xa1620, 48%nat); (0xa16f0, 40%nat); (0xa17c0, 93%nat); (0xada74, 8%nat)]%Z.

Definition startup_plan_ranges_A : list (Z * nat) := [(0x307b4, 20%nat); (0x30964, 84%nat); (0x32974, 12%nat); (0x329c4, 8%nat); (0x32a94, 8%nat); (0x32ba4, 8%nat); (0x32be4, 32%nat); (0x32d04, 48%nat); (0x32e44, 12%nat); (0x32e94, 24%nat); (0x32f44, 20%nat); (0x33b84, 20%nat); (0x33c74, 12%nat); (0x40e44, 12%nat); (0x41b24, 4%nat); (0x46384, 32%nat); (0x473a4, 40%nat); (0x47464, 36%nat); (0x48294, 6624%nat); (0x50f74, 88%nat); (0x517b4, 24%nat); (0x51844, 16%nat); (0x51954, 4%nat); (0x51994, 12%nat); (0x52094, 4%nat); (0x520c4, 12%nat); (0x522b4, 24%nat); (0x523f4, 12%nat); (0x52824, 4%nat); (0x532a4, 52%nat); (0x53424, 8%nat); (0x534f4, 36%nat); (0x53634, 16%nat); (0x537c4, 28%nat); (0x53c54, 76%nat); (0x53db4, 20%nat); (0x543b4, 16%nat); (0x54434, 8%nat); (0x54474, 8%nat); (0x58964, 28%nat); (0x58ec4, 8%nat); (0x58ef4, 80%nat); (0x590e4, 16%nat); (0x593e4, 20%nat); (0x595c4, 4%nat); (0x59b54, 36%nat); (0x59dd4, 16%nat); (0x59e54, 8%nat); (0x5aab4, 4%nat); (0x5aad4, 8%nat); (0x5b344, 8%nat); (0x5b4d4, 36%nat); (0x5b584, 4%nat); (0x5b5b4, 44%nat); (0x5b8e4, 12%nat); (0x5bd84, 16%nat); (0x5bde4, 12%nat); (0x5c174, 20%nat); (0x5c2b4, 28%nat); (0x5c3c4, 28%nat); (0x5d4c4, 44%nat); (0x5d5d4, 40%nat); (0x5d694, 12%nat); (0x5d6d4, 16%nat); (0x5dcb4, 68%nat); (0x5ddf4, 12%nat); (0x5de44, 8%nat); (0x5de84, 4%nat); (0x5f4a4, 16%nat); (0x5fb44, 12%nat); (0x5fb84, 12%nat); (0x60254, 4%nat); (0x60294, 4%nat); (0x60564, 44%nat); (0x60744, 12%nat); (0x60da4, 8%nat); (0x633e4, 12%nat); (0x63464, 12%nat); (0x634b4, 4%nat); (0x63994, 40%nat); (0x63c44, 16%nat); (0x64a74, 64%nat); (0x64b84, 8%nat); (0x64ea4, 20%nat); (0x64f04, 4%nat); (0x650c4, 8%nat); (0x65324, 60%nat); (0x65424, 8%nat); (0x654b4, 28%nat); (0x65964, 76%nat); (0x65aa4, 20%nat); (0x66004, 20%nat); (0x66154, 16%nat); (0x66214, 60%nat); (0x66324, 4%nat); (0x66344, 8%nat); (0x663a4, 20%nat); (0x66564, 28%nat); (0x66654, 24%nat); (0x667d4, 4%nat); (0x668d4, 16%nat); (0x66b24, 36%nat); (0x66bc4, 40%nat); (0x66c74, 8%nat); (0x66ca4, 8%nat); (0x66ce4, 48%nat); (0x68f24, 12%nat); (0x68f74, 8%nat); (0x68ff4, 56%nat); (0x690f4, 12%nat); (0x691c4, 36%nat); (0x692e4, 20%nat); (0x69594, 88%nat); (0x69754, 8%nat); (0x697a4, 16%nat); (0x697f4, 44%nat); (0x698b4, 16%nat); (0x69904, 44%nat); (0x69a54, 12%nat); (0x6a694, 52%nat); (0x6af54, 8%nat); (0x6af84, 12%nat); (0x6b154, 8%nat); (0x6b874, 36%nat); (0x6bd74, 40%nat); (0x6c054, 36%nat); (0x6c2d4, 4%nat); (0x6c304, 4%nat); (0x6c344, 36%nat); (0x6c454, 32%nat); (0x6c904, 4%nat); (0x6cbd4, 116%nat); (0x6d124, 8%nat); (0x6d174, 8%nat); (0x6d214, 4%nat); (0x6d394, 44%nat); (0x6d4a4, 8%nat); (0x6dab4, 12%nat); (0x6db04, 32%nat); (0x6dcf4, 8%nat); (0x6f504, 20%nat); (0xa0ff0, 28%nat); (0xa10a0, 24%nat); (0xa1200, 4%nat); (0xa1b20, 28%nat); (0xa1ba0, 21%nat); (0xa1fd0, 81%nat); (0xa2130, 21%nat); (0xab850, 68%nat); (0xabd20, 8%nat); (0xabf14, 7%nat); (0xabfa4, 8%nat); (0xac040, 13%nat); (0xad0f4, 12%nat); (0xad4a0, 57%nat); (0xad814, 31%nat); (0xad8c0, 17%nat); (0xad9b4, 24%nat); (0xada40, 17%nat)]%Z.

Definition startup_plan_ranges_B : list (Z * nat) := [(0x3c444, 48%nat); (0x3cc04, 16%nat); (0x41b24, 4%nat); (0x46384, 32%nat); (0x510d4, 4%nat); (0x51aa4, 80%nat); (0x532c4, 44%nat); (0x53424, 8%nat); (0x534f4, 40%nat); (0x53634, 16%nat); (0x54434, 8%nat); (0x54534, 8%nat); (0x545b4, 4%nat); (0x545e4, 4%nat); (0x59024, 12%nat); (0x590e4, 16%nat); (0x59644, 12%nat); (0x59924, 4%nat); (0x5b8e4, 28%nat); (0x5b964, 20%nat); (0x5ba74, 12%nat); (0x5bb54, 8%nat); (0x5bba4, 20%nat); (0x5bcc4, 32%nat); (0x5be04, 8%nat); (0x5be54, 32%nat); (0x5bf84, 24%nat); (0x5c094, 32%nat); (0x5c1b4, 20%nat); (0x5c224, 20%nat); (0x5c314, 28%nat); (0x5d4c4, 4%nat); (0x5f4a4, 16%nat); (0x5fb44, 12%nat); (0x5fb84, 12%nat); (0x63c44, 16%nat); (0x65334, 56%nat); (0x65424, 8%nat); (0x654e4, 16%nat); (0x66004, 20%nat); (0x66154, 16%nat); (0x68ff4, 36%nat); (0x69104, 8%nat); (0x691c4, 24%nat); (0x69344, 8%nat); (0x6a374, 40%nat); (0x6a494, 52%nat); (0x6a574, 32%nat); (0x6bd74, 44%nat); (0x6be84, 8%nat); (0x6c384, 20%nat); (0x6c494, 20%nat); (0x6c504, 8%nat); (0x7a114, 12%nat); (0x7a194, 8%nat); (0xa2870, 5%nat); (0xa2f24, 52%nat); (0xa3014, 4%nat); (0xa3034, 8%nat); (0xa3064, 8%nat); (0xa3200, 16%nat); (0xa3260, 9%nat); (0xa32e0, 9%nat); (0xa33f0, 21%nat); (0xa34b4, 12%nat); (0xa3500, 9%nat); (0xa3570, 29%nat); (0xa3750, 9%nat); (0xab450, 5%nat); (0xab560, 9%nat); (0xab5b0, 13%nat); (0xab810, 9%nat); (0xab850, 68%nat); (0xac040, 13%nat); (0xac080, 17%nat); (0xad0f4, 12%nat)]%Z.

Definition startup_plan_ranges_C : list (Z * nat) := [(0x51ba4, 16%nat); (0x58e64, 8%nat); (0x59044, 20%nat); (0x593c4, 8%nat); (0x5ad94, 32%nat); (0x60254, 4%nat); (0x60294, 4%nat); (0x63464, 12%nat); (0x634b4, 4%nat); (0x63514, 8%nat); (0x63544, 4%nat); (0x635b4, 8%nat); (0x683c4, 20%nat); (0x68424, 12%nat); (0x68604, 12%nat); (0x68664, 32%nat); (0x68714, 24%nat); (0x688b4, 16%nat); (0x7f844, 28%nat); (0x7f8c4, 24%nat); (0x7f944, 12%nat); (0x80268, 4%nat); (0xa1930, 8%nat); (0xa1f90, 20%nat); (0xa2f24, 23%nat); (0xa2fa0, 21%nat); (0xa3010, 17%nat); (0xa3060, 108%nat); (0xa3240, 12%nat); (0xa3510, 53%nat); (0xa3750, 73%nat); (0xa3880, 116%nat); (0xa3af0, 5%nat); (0xa3b10, 168%nat); (0xa3dc0, 73%nat); (0xa3ef0, 33%nat); (0xa63a0, 81%nat); (0xab454, 4%nat); (0xab564, 8%nat); (0xab5b4, 12%nat); (0xab814, 8%nat); (0xabd20, 8%nat); (0xabf14, 7%nat); (0xabfa4, 8%nat); (0xac0b0, 33%nat); (0xae0b0, 13%nat); (0xae0f0, 9%nat)]%Z.
