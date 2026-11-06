(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AsanPlan.
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
(PRun [0x81518]
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
PRun [0x6cb9c]
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
(PRun [0x528cc]
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
PRun [0x65840]
(PX XMaxVA []
(PRun []
(PMmap
(PSpin )
(PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (ELit 65536) (ELit 6189056)
(PShDisj (escale 4096 (EVar 207)) (ELit 3727360) (eaddz e_pd (-8388608)) (e_stkwlen)
(PRun [0x59d24]
(PDropRange (ELit 0x9fe38) (ELit 0x12b0)
(PRun []
(PMmap
(PSpin )
(PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (ELit 65536) (ELit 6189056)
(PShDisj (escale 4096 (EVar 208)) (ELit 137439023104) (eaddz e_pd (-8388608)) (e_stkwlen)
(PRun [0x6c668]
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
(PRun [0x81518]
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
(PRun [0x89100]
(PExt 1 [ELit 0x5f5510; ELit 8]
(PRun [0x65840]
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
(PRun [0x64624]
(PX XIStrncpy []
(PRun [0x64624]
(PX XIStrncpy []
(PRun [0x59c5c]
(PDropRange (ELit 0x132000) (ELit 0xfff) (PDropRange (ELit 0x133000) (ELit 0xfff)
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
(PRun [0x3e3cc]
(PRun [0x3e858]
(PRun [0x624d4]
(PRun [0x62954]
(PRun [0x62dcc]
(PRun [0x3e8b8]
(PRun [0x624d4]
(PRun [0x62954]
(PRun [0x62dcc]
(PRun [0x3e908]
(PRun [0x624d4]
(PRun [0x62954]
(PRun [0x62dcc]
(PRun [0x3e918]
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
(PRun [0x59c60]
(PDropRange (escale 4096 (EVar 78)) (ELit 0x10000)
(PHandoff 10 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_both_ranges_0 : list (Z * nat) := [(0x31140, 20%nat); (0x37ce0, 12%nat); (0x37d90, 12%nat); (0x382a0, 28%nat); (0x38360, 12%nat); (0x3dc70, 880%nat); (0x3ea70, 16%nat); (0x3eb00, 48%nat); (0x51e60, 4%nat); (0x52540, 20%nat); (0x52610, 24%nat); (0x52830, 20%nat); (0x52960, 28%nat); (0x52e60, 4%nat); (0x53050, 24%nat); (0x53180, 12%nat); (0x54030, 8%nat); (0x58f60, 12%nat); (0x59700, 28%nat); (0x59bc0, 16%nat); (0x59c10, 24%nat); (0x59c80, 20%nat); (0x5a0e0, 12%nat); (0x5a120, 16%nat); (0x5a700, 108%nat); (0x5abf0, 8%nat); (0x5ea30, 76%nat); (0x60230, 8%nat); (0x608d0, 8%nat); (0x60900, 4%nat); (0x60920, 4%nat); (0x60940, 4%nat); (0x60b90, 12%nat); (0x60bd0, 24%nat); (0x60fe0, 4%nat); (0x61030, 4%nat); (0x61b50, 84%nat); (0x61fe0, 1204%nat); (0x63760, 28%nat); (0x637f0, 24%nat); (0x638e0, 44%nat); (0x639b0, 20%nat); (0x63a70, 20%nat); (0x63b50, 12%nat); (0x63bb0, 28%nat); (0x63c30, 32%nat); (0x63e30, 20%nat); (0x63e90, 20%nat); (0x64170, 12%nat); (0x641f0, 28%nat); (0x64360, 20%nat); (0x645b0, 12%nat); (0x64620, 24%nat); (0x64690, 4%nat); (0x649d0, 16%nat); (0x64cc0, 24%nat); (0x65800, 68%nat); (0x65920, 4%nat); (0x660b0, 64%nat); (0x66da0, 20%nat); (0x66ef0, 12%nat); (0x6d960, 4%nat); (0x7a7c0, 264%nat); (0x7d670, 8%nat); (0x80700, 96%nat); (0x81500, 8%nat); (0x887e0, 28%nat); (0x88880, 24%nat); (0x889e0, 52%nat); (0x88ac0, 36%nat); (0x88c20, 20%nat); (0x88c80, 40%nat); (0x88e00, 94%nat); (0x88fa8, 79%nat); (0x890f4, 12%nat); (0x95264, 4%nat)]%Z.
Definition startup_plan_both_ranges_A : list (Z * nat) := [(0x31290, 16%nat); (0x31430, 84%nat); (0x33440, 12%nat); (0x33490, 8%nat); (0x33560, 12%nat); (0x33670, 12%nat); (0x336b0, 36%nat); (0x337e0, 48%nat); (0x33920, 12%nat); (0x33970, 24%nat); (0x33a10, 24%nat); (0x34650, 24%nat); (0x34740, 12%nat); (0x41bd0, 16%nat); (0x428b0, 4%nat); (0x47110, 36%nat); (0x48130, 44%nat); (0x48200, 32%nat); (0x49030, 6624%nat); (0x51d00, 92%nat); (0x52540, 24%nat); (0x525d0, 20%nat); (0x526e0, 4%nat); (0x52720, 12%nat); (0x52e20, 8%nat); (0x52e60, 8%nat); (0x53050, 24%nat); (0x53180, 12%nat); (0x535b0, 4%nat); (0x54030, 8%nat); (0x54060, 40%nat); (0x541c0, 8%nat); (0x54290, 32%nat); (0x543c0, 16%nat); (0x54550, 32%nat); (0x549e0, 76%nat); (0x54b40, 20%nat); (0x55140, 20%nat); (0x551c0, 8%nat); (0x55200, 12%nat); (0x59700, 28%nat); (0x59c60, 4%nat); (0x59c80, 84%nat); (0x59e70, 16%nat); (0x5a180, 16%nat); (0x5a350, 4%nat); (0x5a8e0, 40%nat); (0x5ab70, 16%nat); (0x5abf0, 8%nat); (0x5b840, 16%nat); (0x5c0e0, 4%nat); (0x5c260, 40%nat); (0x5c310, 8%nat); (0x5c350, 40%nat); (0x5c670, 12%nat); (0x5cb20, 12%nat); (0x5cb70, 12%nat); (0x5cf10, 20%nat); (0x5d050, 24%nat); (0x5d160, 28%nat); (0x5e260, 40%nat); (0x5e370, 40%nat); (0x5e420, 36%nat); (0x5ea40, 60%nat); (0x5eb40, 8%nat); (0x5eb90, 12%nat); (0x5ebe0, 4%nat); (0x5ec10, 8%nat); (0x608d0, 8%nat); (0x60900, 4%nat); (0x60920, 4%nat); (0x60940, 4%nat); (0x60fe0, 4%nat); (0x61030, 4%nat); (0x612f0, 12%nat); (0x61330, 32%nat); (0x614e0, 12%nat); (0x61b30, 8%nat); (0x64170, 12%nat); (0x64720, 44%nat); (0x649d0, 16%nat); (0x65800, 68%nat); (0x65920, 4%nat); (0x65c40, 16%nat); (0x65c90, 4%nat); (0x65e60, 4%nat); (0x660b0, 64%nat); (0x66240, 28%nat); (0x66700, 68%nat); (0x66da0, 20%nat); (0x66ef0, 12%nat); (0x67560, 8%nat); (0x69cc0, 8%nat); (0x69d10, 8%nat); (0x69d90, 56%nat); (0x69e90, 8%nat); (0x69f50, 36%nat); (0x6a070, 20%nat); (0x6a320, 92%nat); (0x6a4f0, 4%nat); (0x6a530, 16%nat); (0x6a580, 48%nat); (0x6a650, 64%nat); (0x6a7e0, 12%nat); (0x6b430, 48%nat); (0x6bce0, 8%nat); (0x6bd20, 8%nat); (0x6bef0, 4%nat); (0x6c610, 36%nat); (0x6cb00, 40%nat); (0x6cdf0, 36%nat); (0x6d060, 4%nat); (0x6d0a0, 4%nat); (0x6d0e0, 32%nat); (0x6d1e0, 32%nat); (0x6d690, 4%nat); (0x6d960, 64%nat); (0x6da70, 48%nat); (0x6deb0, 12%nat); (0x6df10, 4%nat); (0x6dfa0, 4%nat); (0x6e130, 40%nat); (0x6e230, 8%nat); (0x6e840, 12%nat); (0x6e8a0, 20%nat); (0x6ea90, 8%nat); (0x70290, 20%nat); (0x887e0, 28%nat); (0x88880, 24%nat); (0x889e0, 8%nat); (0x89314, 24%nat); (0x89384, 24%nat); (0x897b4, 84%nat); (0x89924, 16%nat); (0x93044, 64%nat); (0x93504, 8%nat); (0x93704, 4%nat); (0x93794, 4%nat); (0x93834, 12%nat); (0x948e4, 8%nat); (0x94c84, 32%nat); (0x94d14, 20%nat); (0x95004, 28%nat); (0x950a4, 16%nat); (0x951a4, 20%nat); (0x95224, 16%nat)]%Z.
Definition startup_plan_both_ranges_B : list (Z * nat) := [(0x3cf10, 28%nat); (0x3cf90, 16%nat); (0x3d6d0, 16%nat); (0x428b0, 4%nat); (0x47110, 36%nat); (0x51e60, 4%nat); (0x52830, 80%nat); (0x54060, 40%nat); (0x541c0, 8%nat); (0x54290, 36%nat); (0x543c0, 16%nat); (0x551c0, 8%nat); (0x552c0, 12%nat); (0x55340, 8%nat); (0x55370, 4%nat); (0x59dc0, 8%nat); (0x59e70, 16%nat); (0x5a3e0, 8%nat); (0x5a6c0, 4%nat); (0x5c670, 28%nat); (0x5c700, 16%nat); (0x5c800, 12%nat); (0x5c8f0, 8%nat); (0x5c930, 24%nat); (0x5ca50, 32%nat); (0x5cba0, 8%nat); (0x5cbe0, 36%nat); (0x5cd20, 20%nat); (0x5ce20, 32%nat); (0x5cf50, 20%nat); (0x5cfc0, 16%nat); (0x5d0b0, 24%nat); (0x5e250, 4%nat); (0x608d0, 8%nat); (0x60900, 4%nat); (0x60920, 4%nat); (0x60940, 4%nat); (0x649d0, 16%nat); (0x660c0, 60%nat); (0x66270, 16%nat); (0x66da0, 20%nat); (0x66ef0, 12%nat); (0x69d90, 36%nat); (0x69e90, 8%nat); (0x69f50, 24%nat); (0x6a0e0, 4%nat); (0x6b100, 44%nat); (0x6b230, 52%nat); (0x6b310, 28%nat); (0x6cb00, 44%nat); (0x6cc10, 12%nat); (0x6d110, 20%nat); (0x6d220, 24%nat); (0x6d290, 12%nat); (0x7aea0, 12%nat); (0x7af20, 12%nat); (0x8a054, 4%nat); (0x8a714, 48%nat); (0x8a804, 24%nat); (0x8a9e4, 16%nat); (0x8aa44, 8%nat); (0x8aac4, 8%nat); (0x8abe4, 16%nat); (0x8aca4, 8%nat); (0x8ace4, 8%nat); (0x8ad54, 28%nat); (0x8af34, 12%nat); (0x92c34, 8%nat); (0x92d54, 8%nat); (0x92d94, 12%nat); (0x92ff4, 8%nat); (0x93044, 64%nat); (0x93834, 28%nat); (0x948e4, 8%nat)]%Z.
Definition startup_plan_both_ranges_C : list (Z * nat) := [(0x52930, 16%nat); (0x59bf0, 12%nat); (0x59de0, 16%nat); (0x5a150, 12%nat); (0x5bb20, 36%nat); (0x60fe0, 4%nat); (0x61030, 4%nat); (0x641f0, 12%nat); (0x64250, 4%nat); (0x642a0, 8%nat); (0x642d0, 4%nat); (0x64340, 12%nat); (0x69160, 16%nat); (0x691c0, 12%nat); (0x693a0, 8%nat); (0x693f0, 36%nat); (0x694a0, 24%nat); (0x69640, 20%nat); (0x805d0, 28%nat); (0x80650, 28%nat); (0x806e0, 12%nat); (0x81510, 4%nat); (0x89784, 4%nat); (0x897b4, 4%nat); (0x8a714, 20%nat); (0x8a794, 16%nat); (0x8a804, 116%nat); (0x8acf4, 52%nat); (0x8af34, 72%nat); (0x8b064, 88%nat); (0x8b2d4, 44%nat); (0x8b394, 96%nat); (0x8b524, 8%nat); (0x8b5b4, 68%nat); (0x8b6d4, 32%nat); (0x8db84, 80%nat); (0x92c34, 8%nat); (0x92d54, 8%nat); (0x92d94, 12%nat); (0x92ff4, 8%nat); (0x93504, 8%nat); (0x93704, 4%nat); (0x93794, 4%nat); (0x93894, 32%nat); (0x958a4, 8%nat); (0x958d4, 8%nat)]%Z.
