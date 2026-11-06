(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AsanPlan.
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
(PRun [0x81600]
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
PRun [0x6ccb0]
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
(PRun [0x529e0]
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
PRun [0x65954]
(PX XMaxVA []
(PRun []
(PMmap
(PSpin )
(PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (ELit 65536) (ELit 6189056)
(PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (eaddz e_pd (-8388608)) (e_stkwlen)
(PRun [0x59e38]
(PDropRange (ELit 0x9fd78) (ELit 0x12b0)
(PRun []
(PMmap
(PSpin )
(PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (ELit 65536) (ELit 6189056)
(PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (eaddz e_pd (-8388608)) (e_stkwlen)
(PRun [0x6c77c]
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
(PRun [0x81600]
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
(PRun [0x88f70]
(PExt 1 [ELit 0x5f5450; ELit 8]
(PRun [0x65954]
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
(PRun [0x64738]
(PX XIStrncpy []
(PRun [0x64738]
(PX XIStrncpy []
(PRun [0x59d70]
(PDropRange (ELit 0x131f40) (ELit 0xfff) (PDropRange (ELit 0x132f40) (ELit 0xfff)
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
(PRun [0x3e4e0]
(PRun [0x3e96c]
(PRun [0x625e8]
(PRun [0x62a68]
(PRun [0x62ee0]
(PRun [0x3e9cc]
(PRun [0x625e8]
(PRun [0x62a68]
(PRun [0x62ee0]
(PRun [0x3ea1c]
(PRun [0x625e8]
(PRun [0x62a68]
(PRun [0x62ee0]
(PRun [0x3ea2c]
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
(PRun [0x59d74]
(PDropRange (escale 4096 (EVar 78)) (ELit 0x10000)
(PHandoff 10 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_ranges_0 : list (Z * nat) := [(0x31250, 20%nat); (0x37df0, 12%nat); (0x37eb0, 8%nat); (0x383b0, 32%nat); (0x38470, 12%nat); (0x3dd90, 876%nat); (0x3eb90, 4%nat); (0x3ebb0, 4%nat); (0x3ec10, 48%nat); (0x51f70, 4%nat); (0x52650, 20%nat); (0x52720, 24%nat); (0x52940, 20%nat); (0x52a80, 24%nat); (0x52f70, 4%nat); (0x53160, 24%nat); (0x53290, 12%nat); (0x54150, 4%nat); (0x59080, 8%nat); (0x59810, 28%nat); (0x59cd0, 16%nat); (0x59d20, 48%nat); (0x5a1f0, 32%nat); (0x5a820, 104%nat); (0x5ad00, 8%nat); (0x5eb50, 28%nat); (0x5ebd0, 40%nat); (0x60340, 8%nat); (0x609f0, 4%nat); (0x60a10, 4%nat); (0x60a30, 12%nat); (0x60ca0, 12%nat); (0x60ce0, 24%nat); (0x61100, 4%nat); (0x61140, 4%nat); (0x61c60, 84%nat); (0x620f0, 1204%nat); (0x63870, 28%nat); (0x63900, 28%nat); (0x63a00, 44%nat); (0x63ad0, 16%nat); (0x63b80, 20%nat); (0x63c60, 12%nat); (0x63cc0, 28%nat); (0x63d40, 32%nat); (0x63f50, 16%nat); (0x63fb0, 16%nat); (0x64290, 12%nat); (0x64300, 28%nat); (0x64470, 20%nat); (0x646c0, 12%nat); (0x64730, 24%nat); (0x647a0, 4%nat); (0x64ae0, 16%nat); (0x64dd0, 24%nat); (0x65920, 64%nat); (0x65a30, 4%nat); (0x661c0, 64%nat); (0x66eb0, 20%nat); (0x67000, 12%nat); (0x6da70, 4%nat); (0x7a8d0, 264%nat); (0x7d790, 4%nat); (0x80810, 100%nat); (0x815f0, 4%nat); (0x88650, 28%nat); (0x886f0, 24%nat); (0x88850, 52%nat); (0x88930, 36%nat); (0x88a90, 20%nat); (0x88af0, 40%nat); (0x88c70, 94%nat); (0x88e18, 79%nat); (0x88f64, 12%nat); (0x950d4, 4%nat)]%Z.
Definition startup_plan_ranges_A : list (Z * nat) := [(0x313a0, 16%nat); (0x31550, 84%nat); (0x33550, 12%nat); (0x335b0, 4%nat); (0x33680, 8%nat); (0x33780, 12%nat); (0x337c0, 36%nat); (0x338f0, 48%nat); (0x33a30, 12%nat); (0x33a80, 24%nat); (0x33b20, 24%nat); (0x34760, 24%nat); (0x34850, 12%nat); (0x41cf0, 12%nat); (0x429c0, 4%nat); (0x47230, 32%nat); (0x48250, 40%nat); (0x48310, 36%nat); (0x49140, 6624%nat); (0x51e10, 92%nat); (0x52650, 28%nat); (0x526f0, 16%nat); (0x52800, 4%nat); (0x52830, 16%nat); (0x52f30, 8%nat); (0x52f70, 8%nat); (0x53160, 24%nat); (0x53290, 12%nat); (0x536d0, 4%nat); (0x54150, 4%nat); (0x54170, 40%nat); (0x542d0, 8%nat); (0x543a0, 32%nat); (0x544d0, 20%nat); (0x54670, 28%nat); (0x54af0, 76%nat); (0x54c60, 16%nat); (0x55260, 16%nat); (0x552d0, 12%nat); (0x55310, 12%nat); (0x59810, 28%nat); (0x59d70, 92%nat); (0x59f90, 16%nat); (0x5a290, 16%nat); (0x5a460, 8%nat); (0x5aa00, 36%nat); (0x5ac80, 16%nat); (0x5ad00, 8%nat); (0x5b950, 8%nat); (0x5b980, 8%nat); (0x5c1f0, 4%nat); (0x5c380, 36%nat); (0x5c420, 8%nat); (0x5c460, 40%nat); (0x5c790, 8%nat); (0x5cc30, 16%nat); (0x5cc90, 12%nat); (0x5d020, 20%nat); (0x5d160, 28%nat); (0x5d270, 28%nat); (0x5e370, 44%nat); (0x5e480, 40%nat); (0x5e530, 16%nat); (0x5e580, 16%nat); (0x5eb50, 72%nat); (0x5eca0, 12%nat); (0x5ecf0, 4%nat); (0x5ed30, 4%nat); (0x609f0, 4%nat); (0x60a10, 4%nat); (0x60a30, 12%nat); (0x61100, 4%nat); (0x61140, 4%nat); (0x61410, 44%nat); (0x615f0, 12%nat); (0x61c40, 12%nat); (0x64290, 12%nat); (0x64830, 44%nat); (0x64ae0, 20%nat); (0x65920, 64%nat); (0x65a30, 4%nat); (0x65d50, 16%nat); (0x65da0, 4%nat); (0x65f70, 4%nat); (0x661c0, 64%nat); (0x66350, 32%nat); (0x66810, 72%nat); (0x66eb0, 20%nat); (0x67000, 12%nat); (0x67670, 8%nat); (0x69dd0, 12%nat); (0x69e20, 8%nat); (0x69ea0, 56%nat); (0x69fa0, 8%nat); (0x6a060, 40%nat); (0x6a190, 16%nat); (0x6a440, 88%nat); (0x6a600, 4%nat); (0x6a650, 12%nat); (0x6a6a0, 44%nat); (0x6a760, 64%nat); (0x6a900, 12%nat); (0x6b540, 48%nat); (0x6bdf0, 12%nat); (0x6be30, 12%nat); (0x6c000, 8%nat); (0x6c720, 36%nat); (0x6cc20, 36%nat); (0x6cf00, 36%nat); (0x6d170, 8%nat); (0x6d1b0, 4%nat); (0x6d1f0, 32%nat); (0x6d2f0, 36%nat); (0x6d7b0, 4%nat); (0x6da70, 64%nat); (0x6db80, 48%nat); (0x6dfd0, 8%nat); (0x6e020, 4%nat); (0x6e0b0, 4%nat); (0x6e240, 40%nat); (0x6e340, 8%nat); (0x6e950, 16%nat); (0x6e9b0, 24%nat); (0x6eba0, 8%nat); (0x703b0, 20%nat); (0x88650, 28%nat); (0x886f0, 24%nat); (0x88850, 8%nat); (0x89184, 24%nat); (0x891f4, 24%nat); (0x89624, 84%nat); (0x89794, 16%nat); (0x92eb4, 64%nat); (0x93374, 8%nat); (0x93574, 4%nat); (0x93604, 4%nat); (0x936a4, 12%nat); (0x94754, 8%nat); (0x94af4, 32%nat); (0x94b84, 20%nat); (0x94e74, 28%nat); (0x94f14, 16%nat); (0x95014, 20%nat); (0x95094, 16%nat)]%Z.
Definition startup_plan_ranges_B : list (Z * nat) := [(0x3d020, 28%nat); (0x3d0a0, 20%nat); (0x3d7f0, 12%nat); (0x429c0, 4%nat); (0x47230, 32%nat); (0x51f70, 4%nat); (0x52940, 80%nat); (0x54170, 40%nat); (0x542d0, 8%nat); (0x543a0, 36%nat); (0x544d0, 20%nat); (0x552d0, 12%nat); (0x553e0, 8%nat); (0x55450, 8%nat); (0x55490, 4%nat); (0x59ed0, 12%nat); (0x59f90, 16%nat); (0x5a4f0, 8%nat); (0x5a7d0, 4%nat); (0x5c790, 28%nat); (0x5c810, 20%nat); (0x5c910, 16%nat); (0x5ca00, 8%nat); (0x5ca50, 20%nat); (0x5cb70, 32%nat); (0x5ccb0, 8%nat); (0x5cd00, 32%nat); (0x5ce30, 20%nat); (0x5cf30, 32%nat); (0x5d060, 20%nat); (0x5d0d0, 20%nat); (0x5d1c0, 28%nat); (0x5e360, 4%nat); (0x609f0, 4%nat); (0x60a10, 4%nat); (0x60a30, 12%nat); (0x64ae0, 20%nat); (0x661d0, 60%nat); (0x66380, 20%nat); (0x66eb0, 20%nat); (0x67000, 12%nat); (0x69ea0, 36%nat); (0x69fa0, 8%nat); (0x6a060, 24%nat); (0x6a1f0, 8%nat); (0x6b210, 44%nat); (0x6b340, 52%nat); (0x6b420, 32%nat); (0x6cc20, 40%nat); (0x6cd20, 12%nat); (0x6d220, 20%nat); (0x6d340, 20%nat); (0x6d3a0, 12%nat); (0x7afb0, 12%nat); (0x7b040, 8%nat); (0x89ec4, 4%nat); (0x8a584, 48%nat); (0x8a674, 24%nat); (0x8a854, 16%nat); (0x8a8b4, 8%nat); (0x8a934, 8%nat); (0x8aa54, 16%nat); (0x8ab14, 8%nat); (0x8ab54, 8%nat); (0x8abc4, 28%nat); (0x8ada4, 12%nat); (0x92aa4, 8%nat); (0x92bc4, 8%nat); (0x92c04, 12%nat); (0x92e64, 8%nat); (0x92eb4, 64%nat); (0x936a4, 28%nat); (0x94754, 8%nat)]%Z.
Definition startup_plan_ranges_C : list (Z * nat) := [(0x52a40, 16%nat); (0x59d00, 12%nat); (0x59ef0, 16%nat); (0x5a270, 8%nat); (0x5bc30, 36%nat); (0x61100, 4%nat); (0x61140, 4%nat); (0x64300, 16%nat); (0x64360, 4%nat); (0x643c0, 16%nat); (0x64460, 8%nat); (0x69270, 16%nat); (0x692d0, 12%nat); (0x694b0, 8%nat); (0x69510, 32%nat); (0x695b0, 24%nat); (0x69760, 16%nat); (0x806f0, 24%nat); (0x80760, 28%nat); (0x807f0, 12%nat); (0x81600, 4%nat); (0x895f4, 4%nat); (0x89624, 4%nat); (0x8a584, 20%nat); (0x8a604, 16%nat); (0x8a674, 116%nat); (0x8ab64, 52%nat); (0x8ada4, 72%nat); (0x8aed4, 88%nat); (0x8b144, 44%nat); (0x8b204, 96%nat); (0x8b394, 8%nat); (0x8b424, 68%nat); (0x8b544, 32%nat); (0x8d9f4, 80%nat); (0x92aa4, 8%nat); (0x92bc4, 8%nat); (0x92c04, 12%nat); (0x92e64, 8%nat); (0x93374, 8%nat); (0x93574, 4%nat); (0x93604, 4%nat); (0x93704, 32%nat); (0x95714, 8%nat); (0x95744, 8%nat)]%Z.
