(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition startup_plan_rcase1 : plan :=
  PRun [0x3e6ac] (* [comment removed for export] *)
  (PJoin e_sp0 (-2280) 8 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 452)) (ELit 1048576) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 452)) (ELit 1048576) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 453)) (ELit 8388608) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 453)) (ELit 8388608) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [0x3e6bc] (* [comment removed for export] *)
  (PExt 113 [ELit 100] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 470)) (ELit 4096) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 470)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [0x7fa48] (* [comment removed for export] *)
  (PBump 607 (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PFog 3 8192 (* [comment removed for export] *)
  (PFog 4 8192 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 5)) (ELit 8192) (escale 4096 (EVar 401)) (ELit 11571200) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 418)) (ELit 4096) (escale 4096 (EVar 401)) (ELit 11571200) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 5)) (ELit 8192) (escale 4096 (EVar 452)) (ELit 1048576) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 418)) (ELit 4096) (escale 4096 (EVar 452)) (ELit 1048576) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 5)) (ELit 8192) (escale 4096 (EVar 453)) (ELit 8388608) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 418)) (ELit 4096) (escale 4096 (EVar 453)) (ELit 8388608) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 5)) (ELit 8192) (escale 4096 (EVar 470)) (ELit 4096) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 418)) (ELit 4096) (escale 4096 (EVar 470)) (ELit 4096) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 5)) (ELit 8192) (escale 4096 (EVar 418)) (ELit 4096) (* [comment removed for export] *)
  (PUnvis (escale 4096 (EVar 5)) (ELit 8192) (* [comment removed for export] *)
  (PExt 114 [escale 4096 (EVar 5); ELit 8192; escale 4096 (EVar 5); ELit 8192; ELit 1; ELit 34359736319] (* [comment removed for export] *)
  (PUnvis (escale 4096 (EVar 418)) (ELit 4096) (* [comment removed for export] *)
  (PExt 114 [escale 4096 (EVar 418); ELit 4096; escale 4096 (EVar 418); ELit 4096; ELit 1; ELit 34359736319] (* [comment removed for export] *)
  (PHavocBrk 0x5fc000 0x805fe000 (* [comment removed for export] *)
  (PGcKeep [(ELit 2147459072, ELit 841728); (ELit 17594064011264, ELit 269484032); (ELit 648560, ELit 32); (ELit 649696, ELit 32); (ELit 649912, ELit 160); (ELit 652880, ELit 24); (ELit 653120, ELit 176); (ELit 657376, ELit 184); (ELit 657648, ELit 24); (ELit 657728, ELit 88); (ELit 667800, ELit 168); (ELit 668032, ELit 176); (ELit 668272, ELit 88); (ELit 668416, ELit 24); (ELit 668512, ELit 432); (ELit 669000, ELit 192); (ELit 669304, ELit 72); (ELit 669688, ELit 56); (ELit 669800, ELit 40); (ELit 669888, ELit 56); (ELit 672624, ELit 32); (ELit 672712, ELit 80); (ELit 672872, ELit 24); (ELit 680976, ELit 32); (ELit 682928, ELit 32); (ELit 686224, ELit 56); (ELit 1216024, ELit 24); (ELit 1271360, ELit 48); (ELit 1279608, ELit 32); (ELit 1279744, ELit 136); (ELit 1279960, ELit 32); (ELit 1280600, ELit 24); (ELit 1542784, ELit 48); (ELit 2503888, ELit 24); (ELit 2567064, ELit 24); (ELit 3675456, ELit 24); (ELit 5132656, ELit 24); (ELit 5472720, ELit 24); (ELit 5777448, ELit 24); (ELit 5802640, ELit 40); (ELit 6132232, ELit 24); (ELit 6134464, ELit 24); (ELit 6134544, ELit 24); (ELit 6134624, ELit 72); (ELit 6134768, ELit 8); (ELit 6265776, ELit 64); (ELit 6266072, ELit 24); (ELit 6266328, ELit 56); (ELit 6267488, ELit 24); (ELit 6270736, ELit 24); (eaddz e_sp0 (0), ELit 32); (eaddz e_sp0 (184), ELit 4128); (escale 4096 (EVar 93), ELit 0); (escale 4096 (EVar 222), ELit 0); (eaddz (escale 4096 (EVar 223)) (4295008248), ELit 24); (eaddz (escale 4096 (EVar 223)) (8589975544), ELit 24); (eaddz (escale 4096 (EVar 223)) (25769844776), ELit 24); (eaddz (escale 4096 (EVar 223)) (73014485096), ELit 24); (eaddz (escale 4096 (EVar 223)) (98784289000), ELit 24); (eaddz (escale 4096 (EVar 223)) (128849060840), ELit 24); (eaddz (escale 4096 (EVar 223)) (137438994552), ELit 224); (eaddz (escale 4096 (EVar 223)) (137438995192), ELit 96); (eaddz (escale 4096 (EVar 223)) (137438996600), ELit 96); (eaddz (escale 4096 (EVar 223)) (137438997368), ELit 224); (eaddz (escale 4096 (EVar 223)) (137438998264), ELit 96); (escale 4096 (EVar 241), ELit 0); (eaddz (escale 4096 (EVar 242)) (-8), ELit 128); (eaddz (escale 4096 (EVar 242)) (280), ELit 24); (eaddz (escale 4096 (EVar 242)) (360), ELit 24); (eaddz (escale 4096 (EVar 242)) (680), ELit 24); (eaddz (escale 4096 (EVar 242)) (1560), ELit 24); (eaddz (escale 4096 (EVar 242)) (2040), ELit 24); (eaddz (escale 4096 (EVar 242)) (2120), ELit 24); (eaddz (escale 4096 (EVar 242)) (2600), ELit 24); (eaddz (escale 4096 (EVar 242)) (2776), ELit 200); (eaddz (escale 4096 (EVar 242)) (3040), ELit 144); (eaddz (escale 4096 (EVar 243)) (0), ELit 24); (eaddz (escale 4096 (EVar 243)) (144), ELit 24); (escale 4096 (EVar 269), ELit 0); (eaddz (escale 4096 (EVar 334)) (16), ELit 24); (escale 4096 (EVar 335), ELit 0); (eaddz (escale 4096 (EVar 401)) (32), ELit 80); (eaddz (escale 4096 (EVar 401)) (35832), ELit 24); (escale 4096 (EVar 418), ELit 0); (escale 4096 (EVar 418), ELit 0); (escale 4096 (EVar 451), ELit 0); (escale 4096 (EVar 452), ELit 0); (escale 4096 (EVar 469), ELit 0); (escale 4096 (EVar 470), ELit 0)] (* [comment removed for export] *)
  (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 368))) 3935) 0 4095) (* [comment removed for export] *)
  (PFact (KRange (EVar 368) 0 8) (* [comment removed for export] *)
  (PHandoff 0 (* [comment removed for export] *))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_rcase2 : plan :=
  PRun [0x3e6ac] (* [comment removed for export] *)
  (PJoin e_sp0 (-2280) 8 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 452)) (ELit 1048576) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 452)) (ELit 1048576) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 453)) (ELit 8388608) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 453)) (ELit 8388608) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [0x3e6bc] (* [comment removed for export] *)
  (PExt 113 [ELit 100] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 470)) (ELit 4096) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 470)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [0x7fa48] (* [comment removed for export] *)
  (PBump 607 (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (* [comment removed for export] *)
  (PFog 3 8192 (* [comment removed for export] *)
  (PFog 4 8192 (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 418)) (ELit 8192) (escale 4096 (EVar 401)) (ELit 11571200) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 419)) (ELit 4096) (escale 4096 (EVar 401)) (ELit 11571200) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 418)) (ELit 8192) (escale 4096 (EVar 452)) (ELit 1048576) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 419)) (ELit 4096) (escale 4096 (EVar 452)) (ELit 1048576) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 418)) (ELit 8192) (escale 4096 (EVar 453)) (ELit 8388608) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 419)) (ELit 4096) (escale 4096 (EVar 453)) (ELit 8388608) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 418)) (ELit 8192) (escale 4096 (EVar 470)) (ELit 4096) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 419)) (ELit 4096) (escale 4096 (EVar 470)) (ELit 4096) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 418)) (ELit 8192) (escale 4096 (EVar 419)) (ELit 4096) (* [comment removed for export] *)
  (PUnvis (eaddz (escale 4096 (EVar 418)) 4096) (ELit 4096) (* [comment removed for export] *)
  (PExt 114 [eaddz (escale 4096 (EVar 418)) 4096; ELit 4096; escale 4096 (EVar 418); ELit 8192; ELit 1; ELit 34359736319] (* [comment removed for export] *)
  (PUnvis (escale 4096 (EVar 419)) (ELit 4096) (* [comment removed for export] *)
  (PExt 114 [escale 4096 (EVar 419); ELit 4096; escale 4096 (EVar 419); ELit 4096; ELit 1; ELit 34359736319] (* [comment removed for export] *)
  (PHavocBrk 0x5fc000 0x805fe000 (* [comment removed for export] *)
  (PGcKeep [(ELit 2147459072, ELit 841728); (ELit 17594064011264, ELit 269484032); (ELit 648560, ELit 32); (ELit 649696, ELit 32); (ELit 649912, ELit 160); (ELit 652880, ELit 24); (ELit 653120, ELit 176); (ELit 657376, ELit 184); (ELit 657648, ELit 24); (ELit 657728, ELit 88); (ELit 667800, ELit 168); (ELit 668032, ELit 176); (ELit 668272, ELit 88); (ELit 668416, ELit 24); (ELit 668512, ELit 432); (ELit 669000, ELit 192); (ELit 669304, ELit 72); (ELit 669688, ELit 56); (ELit 669800, ELit 40); (ELit 669888, ELit 56); (ELit 672624, ELit 32); (ELit 672712, ELit 80); (ELit 672872, ELit 24); (ELit 680976, ELit 32); (ELit 682928, ELit 32); (ELit 686224, ELit 56); (ELit 1216024, ELit 24); (ELit 1271360, ELit 48); (ELit 1279608, ELit 32); (ELit 1279744, ELit 136); (ELit 1279960, ELit 32); (ELit 1280600, ELit 24); (ELit 1542784, ELit 48); (ELit 2503888, ELit 24); (ELit 2567064, ELit 24); (ELit 3675456, ELit 24); (ELit 5132656, ELit 24); (ELit 5472720, ELit 24); (ELit 5777448, ELit 24); (ELit 5802640, ELit 40); (ELit 6132232, ELit 24); (ELit 6134464, ELit 24); (ELit 6134544, ELit 24); (ELit 6134624, ELit 72); (ELit 6134768, ELit 8); (ELit 6265776, ELit 64); (ELit 6266072, ELit 24); (ELit 6266328, ELit 56); (ELit 6267488, ELit 24); (ELit 6270736, ELit 24); (eaddz e_sp0 (0), ELit 32); (eaddz e_sp0 (184), ELit 4128); (escale 4096 (EVar 93), ELit 0); (escale 4096 (EVar 222), ELit 0); (eaddz (escale 4096 (EVar 223)) (4295008248), ELit 24); (eaddz (escale 4096 (EVar 223)) (8589975544), ELit 24); (eaddz (escale 4096 (EVar 223)) (25769844776), ELit 24); (eaddz (escale 4096 (EVar 223)) (73014485096), ELit 24); (eaddz (escale 4096 (EVar 223)) (98784289000), ELit 24); (eaddz (escale 4096 (EVar 223)) (128849060840), ELit 24); (eaddz (escale 4096 (EVar 223)) (137438994552), ELit 224); (eaddz (escale 4096 (EVar 223)) (137438995192), ELit 96); (eaddz (escale 4096 (EVar 223)) (137438996600), ELit 96); (eaddz (escale 4096 (EVar 223)) (137438997368), ELit 224); (eaddz (escale 4096 (EVar 223)) (137438998264), ELit 96); (escale 4096 (EVar 241), ELit 0); (eaddz (escale 4096 (EVar 242)) (-8), ELit 128); (eaddz (escale 4096 (EVar 242)) (280), ELit 24); (eaddz (escale 4096 (EVar 242)) (360), ELit 24); (eaddz (escale 4096 (EVar 242)) (680), ELit 24); (eaddz (escale 4096 (EVar 242)) (1560), ELit 24); (eaddz (escale 4096 (EVar 242)) (2040), ELit 24); (eaddz (escale 4096 (EVar 242)) (2120), ELit 24); (eaddz (escale 4096 (EVar 242)) (2600), ELit 24); (eaddz (escale 4096 (EVar 242)) (2776), ELit 200); (eaddz (escale 4096 (EVar 242)) (3040), ELit 144); (eaddz (escale 4096 (EVar 243)) (0), ELit 24); (eaddz (escale 4096 (EVar 243)) (144), ELit 24); (escale 4096 (EVar 269), ELit 0); (eaddz (escale 4096 (EVar 334)) (16), ELit 24); (escale 4096 (EVar 335), ELit 0); (eaddz (escale 4096 (EVar 401)) (32), ELit 80); (eaddz (escale 4096 (EVar 401)) (35832), ELit 24); (escale 4096 (EVar 418), ELit 0); (escale 4096 (EVar 418), ELit 0); (escale 4096 (EVar 451), ELit 0); (escale 4096 (EVar 452), ELit 0); (escale 4096 (EVar 469), ELit 0); (escale 4096 (EVar 470), ELit 0)] (* [comment removed for export] *)
  (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 368))) 3935) 0 4095) (* [comment removed for export] *)
  (PFact (KRange (EVar 368) 0 8) (* [comment removed for export] *)
  (PHandoff 0 (* [comment removed for export] *))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_brkfail3 : plan :=
  PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 418)) (ELit 8192) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 418)) (ELit 8192) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMprotect (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 419)) (ELit 4096) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 419)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [0x7288c] (* [comment removed for export] *)
  (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 368))) 3935) 4030 (* [comment removed for export] *)
  (startup_plan_rcase2)
  (startup_plan_rcase2)))))))))))))))).

Definition startup_plan_arm6 : plan :=
  PBump 368 (* [comment removed for export] *)
  (  PRun [0x6bd64] (* [comment removed for export] *)
  (PFresh 10 12 (Some (escale 32768 (EVar 0))) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PFact (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 368))) (ELit 3935)) 0 4095) (* [comment removed for export] *)
  (PFact (KRange (EVar 368) 0 8) (* [comment removed for export] *)
  (PMerge 1 (* [comment removed for export] *)))))))).

Definition startup_plan_rest : plan :=
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 401)) (ELit 11571200) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 401)) (ELit 11571200) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PSys YBrk (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PBrkU (* [comment removed for export] *)
  (startup_plan_brkfail3)
  (PRun [] (* [comment removed for export] *)
   (PMmapIn (* [comment removed for export] *)
   (PContra (* [comment removed for export] *))
   (PRun [] (* [comment removed for export] *)
   (PMmap (* [comment removed for export] *)
   (PContra (* [comment removed for export] *))
   (PShDisj (escale 4096 (EVar 418)) (ELit 4096) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
   (PShDisj (escale 4096 (EVar 418)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
   (PIntro 1 34359736319 (* [comment removed for export] *)
   (PRun [] (* [comment removed for export] *)
   (PX XIMemset [] (* [comment removed for export] *)
   (PRun [] (* [comment removed for export] *)
   (PX XIMemset [] (* [comment removed for export] *)
   (PRun [0x7288c] (* [comment removed for export] *)
   (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 368))) 3935) 4030 (* [comment removed for export] *)
   (startup_plan_rcase1)
   (startup_plan_rcase1))))))))))))
   (PContra (* [comment removed for export] *)))))))))))))))).

(* [comment removed for export] *)
Definition startup_js1 : acs :=
{|
  a_ss :=
    SS 374940
      [ELit 0; EVar 369; EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6))) (ELit (-320)); ELit 67584; ELit 6134640; EVar 370; EVar 371; 
       EVar 372; EMd M_MUL (ELit 4096) (EVar 242); ELit 0; EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EVar 368))) (ELit 2146402304); 
       EVar 374; EVar 375; EVar 376; EVar 377; EVar 378; EVar 379; EVar 380; ELit 1; ELit 686232; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; EVar 381; 
       EVar 382; EVar 383; EVar 384]
      []
      [KRange (EVar 368) 0 8; KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 368))) (ELit 3935)) 0 4095;
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -320 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -312 |} 8 (ELit 686232);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -304 |} 8 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -296 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -288 |} 8 (EMd M_MUL (ELit 4096) (EVar 242));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -280 |} 8 (ELit 376824);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 64 |} 8 (ELit 6134648);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 16 |} 8 (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EVar 368))) (ELit (-8388608)));
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 8 |} 8 (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EVar 368)));
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 56 |} 8 (ELit 6136708); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 48 |} 8 (ELit 6136488);
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 335); a_off := 2147450880 |} (ELit 512)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 335); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192); KRange (EVar 335) 1 34359736319;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 1280328 |} 1 (ELit 1); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 32 |} 8 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 24 |} 8 (ELit 6134640); KWord {| a_base := ELit 0; a_off := 669696 |} 1 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 669697 |} 3 (ELit 0); KWord {| a_base := ELit 0; a_off := 1280248 |} 8 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6134648 |} 8 (EMd M_MUL (ELit 4096) (EVar 334));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 334); a_off := 2147450880 |} (ELit 512)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 334); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192);
       KWr {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 24);
       KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 40 |} (ELit 4056); KRange (EVar 334) 1 34359736319;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 40 |} 1 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 32 |} 8 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 24 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -264 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -256 |} 8 (EMd M_MUL (ELit 4096) (EVar 242));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -248 |} 8 (ELit 377464); KWord {| a_base := ELit 0; a_off := 6134490 |} 1 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6270744 |} 8 (EMd M_MUL (ELit 4096) (EVar 243)); KWord {| a_base := ELit 0; a_off := 687408 |} 8 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} 8 (EMd M_MUL (ELit 4096) (EVar 243));
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 152 |} 8 (EMd M_MUL (ELit 4096) (EVar 242)); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 116 |} 1 (ELit 1);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 112 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 687424 |} 8 (ELit 1);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 40 |} 8 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 16 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 687440 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 687432 |} 8 (ELit 1);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} 8 (EMd M_MUL (ELit 4096) (EVar 243)); KWord {| a_base := ELit 0; a_off := 687472 |} 8 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 687464 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 687456 |} 8 (EMd M_MUL (ELit 4096) (EVar 269));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 269); a_off := 2147450880 |} (ELit 512)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 269); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192);
       KWr {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 8 |} (ELit 4088); KRange (EVar 269) 1 34359736319;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 687304 |} 8 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} 8 (ELit 648728);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 148 |} 2 (ELit 1024); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 144 |} 4 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 24 |} 4 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 8 |} 4 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 48 |} 1 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 32 |} 8 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 136 |} 8 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 128 |} 4 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 120 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 687328 |} 8 (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 243)) (ELit 160));
       KWord {| a_base := ELit 0; a_off := 687320 |} 8 (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 243)) (ELit 65536));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 243); a_off := 2147450880 |} (ELit 8192)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 243); a_off := 2147450880 |} (ELit 8192) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192);
       KWr {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 12 |} (ELit 4);
       KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 28 |} (ELit 4); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 49 |} (ELit 63);
       KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 117 |} (ELit 3); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 132 |} (ELit 4);
       KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 150 |} (ELit 2); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 160 |} (ELit 65376);
       KRange (EVar 243) 1532 34359736304; KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 687376 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 687368 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 687360 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 687352 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 687296 |} 8 (ELit 687336); KWord {| a_base := ELit 0; a_off := 687280 |} 1 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 687348 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 687344 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 687336 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 687380 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 687372 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 687288 |} 8 (ELit 687384);
       KWord {| a_base := ELit 0; a_off := 687512 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 687504 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 687496 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 687488 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 687480 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 687544 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 687536 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 687528 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 687520 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 687448 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 687420 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 687416 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 687400 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 687392 |} 8 (ELit 18446744073709551615);
       KWord {| a_base := ELit 0; a_off := 687384 |} 8 (ELit 381996);
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 242); a_off := 2147450880 |} (ELit 512)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 242); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192);
       KWr {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 41 |} (ELit 7);
       KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 72 |} (ELit 4024); KRange (EVar 242) 1 34359736319;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -272 |} 8 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -232 |} 8 (ELit 686232);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -224 |} 8 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -216 |} 8 (ELit 1279720);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -208 |} 8 (ELit 672696);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -200 |} 8 (ELit 364428);
       KWord {| a_base := ELit 0; a_off := 1280288 |} 8 (ELit 455848); KWord {| a_base := ELit 0; a_off := 6265800 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 6266080 |} 8 (ELit 455848);
       KWord {| a_base := ELit 0; a_off := 6265824 |} 8 (ELit 583092); KWord {| a_base := ELit 0; a_off := 6265808 |} 8 (ELit 6265816);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -240 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 1280600 |} 1 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 686232 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 686233 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 672632 |} 8 (ELit 1099511627776);
       KWord {| a_base := ELit 0; a_off := 672642 |} 2 (ELit 2048); KWord {| a_base := ELit 0; a_off := 672640 |} 2 (ELit 16); KWord {| a_base := ELit 0; a_off := 672644 |} 1 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 669897 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 669896 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 669824 |} 8 (ELit 1048576);
       KWord {| a_base := ELit 0; a_off := 669816 |} 8 (ELit 241591905); KWord {| a_base := ELit 0; a_off := 669808 |} 8 (ELit 268435456);
       KWord {| a_base := ELit 0; a_off := 669088 |} 8 (EMd M_MUL (ELit 4096) (EVar 241)); KWord {| a_base := ELit 0; a_off := 669112 |} 8 (ELit 102840);
       KWord {| a_base := ELit 0; a_off := 669104 |} 8 (ELit 8388608); KWord {| a_base := ELit 0; a_off := 669096 |} 8 (EMd M_MUL (ELit 4096) (EVar 241));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 241); a_off := 2147450880 |} (ELit 1048576)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 241); a_off := 2147450880 |} (ELit 1048576) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192); KRange (EVar 241) 1532 34359734272;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 669080 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 669056 |} 4 (ELit 18446744073709551615);
       KWord {| a_base := ELit 0; a_off := 686392 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 686384 |} 8 (ELit 1);
       KWr {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 223)) (EMd M_MUL (ELit (-4096)) (EVar 224)); a_off := 137439019008 |} (ELit 4096);
       KZero {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 223)) (EMd M_MUL (ELit (-4096)) (EVar 224)); a_off := 137439019008 |} (ELit 4096);
       KWord {| a_base := ELit 0; a_off := 669064 |} 8 (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 223)) (EMd M_MUL (ELit (-4096)) (EVar 224))) (ELit 137439019008));
       KWord {| a_base := ELit 0; a_off := 669048 |} 8 (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 223)) (EMd M_MUL (ELit (-4096)) (EVar 224))) (ELit 65536)); 
       KRange (EVar 224) 0 15; KRange (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 224)) (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 223)) (ELit 65535))) 0 0;
       KWord {| a_base := ELit 0; a_off := 669032 |} 8 (ELit 92859); KWord {| a_base := ELit 0; a_off := 669024 |} 8 (ELit 137439023104);
       KWord {| a_base := ELit 0; a_off := 669016 |} 8 (EMd M_MUL (ELit 4096) (EVar 223));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 223); a_off := 2147450880 |} (ELit 17179877888)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 223); a_off := 2147450880 |} (ELit 17179877888) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192);
       KRange (EVar 223) 4295491576 34326181871;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 669072 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 1216033 |} 1 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -164 |} 4 (ELit 18446744073709551615);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -167 |} 1 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -168 |} 1 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -170 |} 2 (ELit 2048);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -172 |} 2 (ELit 16);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -176 |} 4 (ELit 1024);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -180 |} 4 (ELit 256);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -166 |} 2 (ELit 43690); KWord {| a_base := ELit 0; a_off := 6270688 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6269656 |} 8 (ELit 345104); KWord {| a_base := ELit 0; a_off := 6270680 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 680996 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6134552 |} 8 (ELit 6270744); KWord {| a_base := ELit 0; a_off := 680992 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 682936 |} 8 (ELit 2147450880);
       KWord {| a_base := ELit 0; a_off := 680954 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 680952 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 680956 |} 4 (ELit 299);
       KWord {| a_base := ELit 0; a_off := 680968 |} 8 (EMd M_MUL (ELit 4096) (EVar 222)); KWord {| a_base := ELit 0; a_off := 680960 |} 8 (ELit 680968);
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 222); a_off := 2147450880 |} (ELit 465920)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 222); a_off := 2147450880 |} (ELit 465920) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192);
       KWr {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360);
       KRange (EVar 222) 1532 34359735410; KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 680953 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1216024 |} 8 (ELit 365856); KWord {| a_base := ELit 0; a_off := 657808 |} 8 (ELit 8);
       KWord {| a_base := ELit 0; a_off := 682944 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 1279712 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 657832 |} 4 (ELit 2);
       KWord {| a_base := ELit 0; a_off := 1279713 |} 3 (ELit 0); KWord {| a_base := ELit 0; a_off := 1280208 |} 8 (ELit 345620); KWord {| a_base := ELit 0; a_off := 1280272 |} 8 (ELit 365716);
       KWord {| a_base := ELit 0; a_off := 1280280 |} 8 (ELit 365484); KWord {| a_base := ELit 0; a_off := 686240 |} 8 (ELit 140737488355327);
       KWord {| a_base := ELit 0; a_off := 686268 |} 4 (ELit 30); KWord {| a_base := ELit 0; a_off := 680988 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 680984 |} 4 (ELit 2);
       KWord {| a_base := ELit 0; a_off := 672774 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1279720 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 1279728 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1279736 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279744 |} 8 (ELit 81553); KWord {| a_base := ELit 0; a_off := 1279752 |} 8 (ELit 128849084416);
       KWord {| a_base := ELit 0; a_off := 1279760 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279768 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279776 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1279784 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279792 |} 8 (ELit 1103823372545);
       KWord {| a_base := ELit 0; a_off := 1279800 |} 8 (ELit 4294967296); KWord {| a_base := ELit 0; a_off := 1279808 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279816 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1279824 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279832 |} 8 (ELit 65537);
       KWord {| a_base := ELit 0; a_off := 1279840 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1279848 |} 8 (ELit 71687);
       KWord {| a_base := ELit 0; a_off := 1279856 |} 8 (ELit 256); KWord {| a_base := ELit 0; a_off := 1279864 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279872 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1279880 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1279888 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1279896 |} 8 (ELit 18446744069414584320); KWord {| a_base := ELit 0; a_off := 1279904 |} 8 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 1279912 |} 8 (ELit 82413); KWord {| a_base := ELit 0; a_off := 1279920 |} 8 (ELit 81553); KWord {| a_base := ELit 0; a_off := 1279928 |} 8 (ELit 81553);
       KWord {| a_base := ELit 0; a_off := 1279936 |} 8 (ELit 1103823372544); KWord {| a_base := ELit 0; a_off := 1279944 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1279952 |} 8 (ELit 121305); KWord {| a_base := ELit 0; a_off := 1279960 |} 8 (ELit 72339073309605888);
       KWord {| a_base := ELit 0; a_off := 1279968 |} 8 (ELit 72340172838076673); KWord {| a_base := ELit 0; a_off := 1279976 |} 8 (ELit 16843009);
       KWord {| a_base := ELit 0; a_off := 1279984 |} 8 (ELit 1103806595073); KWord {| a_base := ELit 0; a_off := 1279992 |} 8 (ELit 101169);
       KWord {| a_base := ELit 0; a_off := 1280000 |} 8 (ELit 281474976710912); KWord {| a_base := ELit 0; a_off := 672704 |} 4 (ELit 1024);
       KWord {| a_base := ELit 0; a_off := 672700 |} 4 (ELit 256); KWord {| a_base := ELit 0; a_off := 1271384 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1216016 |} 8 (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 93)) (ELit 19880)); KWord {| a_base := ELit 0; a_off := 6066696 |} 2 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6066688 |} 8 (ELit 81553); KWord {| a_base := ELit 0; a_off := 6066680 |} 2 (ELit 0); KWord {| a_base := ELit 0; a_off := 6066088 |} 4 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6066064 |} 4 (ELit 257); KWord {| a_base := ELit 0; a_off := 6066056 |} 8 (ELit 72340172821233664);
       KWord {| a_base := ELit 0; a_off := 6066052 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6066048 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6066080 |} 8 (ELit 81553);
       KWord {| a_base := ELit 0; a_off := 6066072 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 6066070 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6066068 |} 2 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 672786 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 672716 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 672800 |} 8 (ELit 81553);
       KWord {| a_base := ELit 0; a_off := 672796 |} 4 (ELit 2); KWord {| a_base := ELit 0; a_off := 672792 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 672788 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 672784 |} 2 (ELit 1); KWord {| a_base := ELit 0; a_off := 672776 |} 8 (ELit 72340172838010881);
       KWord {| a_base := ELit 0; a_off := 672768 |} 6 (ELit 4294967296); KWord {| a_base := ELit 0; a_off := 672775 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 672740 |} 4 (ELit 4096);
       KWord {| a_base := ELit 0; a_off := 672736 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 672728 |} 8 (ELit 85899345936);
       KWord {| a_base := ELit 0; a_off := 672720 |} 8 (ELit 72340168526266369); KWord {| a_base := ELit 0; a_off := 672712 |} 4 (ELit 2048); KWord {| a_base := ELit 0; a_off := 672760 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 672756 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 672752 |} 4 (ELit 85); KWord {| a_base := ELit 0; a_off := 672744 |} 8 (ELit 816043786240);
       KWord {| a_base := ELit 0; a_off := 672708 |} 4 (ELit 16); KWord {| a_base := ELit 0; a_off := 672696 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 672808 |} 4 (ELit 65793);
       KWord {| a_base := ELit 0; a_off := 1216008 |} 8 (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 93)) (ELit 65536));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 93); a_off := 2147450880 |} (ELit 8192)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 93); a_off := 2147450880 |} (ELit 8192) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192);
       KWr {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 65536 |} (ELit 0); KRange (EVar 93) 1532 34359736304;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := ELit 65536; a_off := 0 |} (ELit 6209536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 1271392 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 686264 |} 1 (ELit 1);
       KWr {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KZero {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KWr {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 2) (EVar 6)); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-2)) (EVar 6))) (ELit 17592187092992));
       KZero {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 2) (EVar 6)); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-2)) (EVar 6))) (ELit 17592187092992));
       KWr {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192); KZero {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776192);
       KWord {| a_base := ELit 0; a_off := 1271376 |} 8 (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6))) (ELit (-160)));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -160 |} 8 (ELit 12297829382473034410);
       KWord {| a_base := ELit 0; a_off := 657816 |} 8 (ELit 131731);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -152 |} 8
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EMd M_MUL (ELit 16) (EVar 6)))) (ELit 16));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -144 |} 8 (ELit 522824);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -136 |} 8 (ELit 648536);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -128 |} 8 (ELit 686232);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -120 |} 8 (ELit 365348); KWord {| a_base := ELit 0; a_off := 686234 |} 2 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -112 |} 8 (ELit 648568);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -104 |} 8 (ELit 525448);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -88 |} 8 (ELit 581192);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -72 |} 8 (EVar 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -64 |} 8
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6))) (ELit 8));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -56 |} 8 (ELit 581368);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -40 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -32 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -24 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -16 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -8 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6134624 |} 8 (EVar 60);
       KWord {| a_base := ELit 0; a_off := 6265776 |} 8 (EVar 60); KWord {| a_base := ELit 0; a_off := 6265777 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6265776 |} 1 (EBlob false 25 0 1);
       KWord {| a_base := ELit 0; a_off := 6265778 |} 6 (EBlob false 25 2 6); KWord {| a_base := ELit 0; a_off := 6134464 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6134456 |} 8 (ELit 6134440); KWord {| a_base := ELit 0; a_off := 6134448 |} 8 (ELit 6134440);
       KWord {| a_base := ELit 0; a_off := 6134560 |} 8 (ELit 6134560); KWord {| a_base := ELit 0; a_off := 6134592 |} 8 (ELit 6266424); KWord {| a_base := ELit 0; a_off := 6134472 |} 4 (EVar 43);
       KRange (EVar 43) 1 4194303; KWord {| a_base := ELit 0; a_off := 6134480 |} 4 (ELit 2); KWord {| a_base := ELit 0; a_off := 6266368 |} 1 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6134440 |} 8 (ELit 6134440); KWord {| a_base := ELit 0; a_off := 6134632 |} 8 (ELit 6134672); KWord {| a_base := ELit 0; a_off := 6134672 |} 8 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6134680 |} 8 (ELit 6136688); KWord {| a_base := ELit 0; a_off := 6266400 |} 8 (ELit 8); KWord {| a_base := ELit 0; a_off := 6266392 |} 8 (ELit 248);
       KWord {| a_base := ELit 0; a_off := 6265768 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6265752 |} 8 (ELit 24); KWord {| a_base := ELit 0; a_off := 6266408 |} 8 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6266384 |} 8 (ELit 6265728); KWord {| a_base := ELit 0; a_off := 6265760 |} 8 (ELit 8); KWord {| a_base := ELit 0; a_off := 6265744 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6265736 |} 8 (ELit 644440);
       KWord {| a_base := ELit 0; a_off := 6266360 |} 8
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6)))))
            (ELit 184));
       KWord {| a_base := ELit 0; a_off := 6266416 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 6266472 |} 8 (EVar 9);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -184 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6266376 |} 8
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6)))))
            (ELit 24));
       KWord {| a_base := ELit 0; a_off := 6134432 |} 8
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EMd M_MUL (ELit 16) (EVar 6)))) (ELit 16));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -48 |} 8
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6))) (ELit 8));
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 72
         |} 8 (ELit 16);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 80
         |} 8 (EVar 9);
       KRange (EVar 0) 4294901760 4294967295; KRange (EVar 6) 0 2047;
       KRange
         (EAlu ALU_ADD
            (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0))
               (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 4)) (EMd M_MUL (ELit 16) (EVar 6))))))
            (ELit 200))
         140735340871872 140737488355328;
       KRange (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EAlu ALU_ADD (EVar 1) (EAlu ALU_ADD (EVar 2) (EAlu ALU_ADD (EVar 4) (EMd M_MUL (ELit 2) (EVar 6)))))) 17591917608961 17592186044393;
       KRange (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6))) 140735340871680 140737488355136;
       KRange (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 2) (EVar 6))) 17591917608960 17592186044392; KRange (EVar 1) 1 1024; KRange (EVar 2) 0 256; KRange (EVar 3) 0 131071;
       KRange (EVar 7) 0 131071; KRange (EVar 8) 0 4294967294; KRange (EVar 4) 0 280000; KRange (EVar 5) 1532 525820;
       KRange (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 3)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 4)) (EMd M_MUL (ELit (-1)) (EVar 7)))) 1 2240000;
       KRange
         (EAlu ALU_ADD
            (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0))
               (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EVar 3) (EMd M_MUL (ELit 16) (EVar 6))))))
            (ELit 185))
         140735340871865 140737488355312;
       KRange
         (EAlu ALU_ADD
            (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0))
               (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EVar 3) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EVar 7))))))
            (ELit 185))
         140735340871865 140737488355312;
       KWr {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -8388608 |} (ELit 8388608);
       KZero {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -192 |} (ELit 8);
       KZero {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -96 |} (ELit 8);
       KZero {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -80 |} (ELit 8);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := 0 |} 8 (EVar 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := 8 |} 8
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6)))))
            (ELit 184));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := 16 |} 8
         (EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar 1))
            (EAlu ALU_ADD
               (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0))
                  (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EVar 3) (EMd M_MUL (ELit 16) (EVar 6))))))
               (ELit 185)));
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 24
         |} 8 (ELit 3);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 32
         |} 8 (ELit 65600);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 40
         |} 8 (ELit 4);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 48
         |} 8 (ELit 56);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 56
         |} 8 (ELit 5);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 64
         |} 8 (ELit 11);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 88
         |} 8 (ELit 6);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 96
         |} 8 (ELit 4096);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 104
         |} 8 (ELit 11);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 112
         |} 8 (EVar 8);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 120
         |} 8 (ELit 12);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 128
         |} 8 (EVar 8);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 136
         |} 8 (ELit 23);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 144
         |} 8 (ELit 0);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 152
         |} 8 (ELit 25);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 160
         |} 8
         (EAlu ALU_ADD
            (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0))
               (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 4)) (EMd M_MUL (ELit 16) (EVar 6))))))
            (ELit 184));
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 168
         |} 8 (ELit 0);
       KWord
         {|
           a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))));
           a_off := 176
         |} 8 (ELit 0);
       KBlob
         {|
           a_base :=
             EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0))
               (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 4)) (EMd M_MUL (ELit 16) (EVar 6)))));
           a_off := 184
         |} (ELit 16) 25;
       KImg 65536 657808; KImg 657824 657832; KImg 657836 669016; KImg 669040 669048; KImg 669060 669064; KImg 669073 669080; KImg 669120 669696; KImg 669700 669808; KImg 669832 669896;
       KImg 669898 672632; KImg 672645 672696; KImg 672717 672720; KImg 672737 672740; KImg 672757 672760; KImg 672787 672788; KImg 672793 672796; KImg 672812 672952; KImg 677736 680952;
       KImg 680955 680956; KImg 680976 680984; KImg 680989 680992; KImg 680993 680996; KImg 681000 682936; KImg 682948 686232; KImg 686236 686240; KImg 686248 686264; KImg 686265 686268;
       KImg 686272 686384; KImg 686400 687280; KImg 687281 687288; KImg 687312 687320; KImg 687404 687408; KImg 687548 1216008; KImg 1216032 1216033; KImg 1216034 1271376; 
       KImg 1271388 1271392; KImg 1271400 1271424; KImg 1275519 1275520; KImg 1279615 1279712; KImg 1279716 1279720; KImg 1280008 1280208; KImg 1280216 1280248; KImg 1280256 1280272;
       KImg 1280296 1280328; KImg 1280329 1280600; KImg 1280601 6066048; KImg 6066049 6066052; KImg 6066071 6066072; KImg 6066076 6066080; KImg 6066092 6066680; KImg 6066682 6066688;
       KImg 6066698 6134432; KImg 6134476 6134480; KImg 6134484 6134490; KImg 6134491 6134552; KImg 6134568 6134592; KImg 6134600 6134624; KImg 6134640 6134648; KImg 6134656 6134672;
       KImg 6134688 6265736; KImg 6265784 6265800; KImg 6265804 6265808; KImg 6265816 6265824; KImg 6265832 6266080; KImg 6266088 6266352; KImg 6266369 6266376; KImg 6266424 6266472;
       KImg 6266480 6269656; KImg 6269664 6270680; KImg 6270684 6270688; KImg 6270692 6270744; KImg 6270752 6275072; KWr {| a_base := ELit 0; a_off := 647168 |} (ELit 5627904)]
      385;
  a_maps :=
    [{| am_base := EMd M_MUL (ELit 4096) (EVar 334); am_len := ELit 4096; am_kind := KRW |}; {| am_base := EMd M_MUL (ELit 4096) (EVar 269); am_len := ELit 4096; am_kind := KRW |};
     {| am_base := EMd M_MUL (ELit 4096) (EVar 243); am_len := ELit 65536; am_kind := KRW |}; {| am_base := EMd M_MUL (ELit 4096) (EVar 242); am_len := ELit 4096; am_kind := KRW |};
     {| am_base := EMd M_MUL (ELit 4096) (EVar 241); am_len := ELit 8388608; am_kind := KNONELAZY |}; {| am_base := EMd M_MUL (ELit 4096) (EVar 223); am_len := ELit 137439023104; am_kind := KRW |};
     {| am_base := EMd M_MUL (ELit 4096) (EVar 222); am_len := ELit 3727360; am_kind := KRW |}; {| am_base := EMd M_MUL (ELit 4096) (EVar 93); am_len := ELit 65536; am_kind := KRW |};
     {| am_base := ELit 2201439137792; am_len := ELit 15392894357504; am_kind := KRWLAZY |}; {| am_base := ELit 2415882240; am_len := ELit 2199023255552; am_kind := KNONELAZY |};
     {| am_base := ELit 2147446784; am_len := ELit 268435456; am_kind := KRWLAZY |}];
  a_totsz := 17729643544576;
  a_ylo := 23387528589312;
  a_eager := 3878912;
  a_vis :=
    [(EMd M_MUL (ELit 4096) (EVar 334), ELit 4096); (EMd M_MUL (ELit 4096) (EVar 269), ELit 4096); (EMd M_MUL (ELit 4096) (EVar 243), ELit 65536); (EMd M_MUL (ELit 4096) (EVar 242), ELit 4096);
     (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 223)) (EMd M_MUL (ELit (-4096)) (EVar 224))) (ELit 137439019008), ELit 4096); (EMd M_MUL (ELit 4096) (EVar 222), ELit 3727360);
     (EMd M_MUL (ELit 4096) (EVar 93), ELit 65536); (ELit 65536, ELit 6209536);
     (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit (-8388608)),
      EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-32768)) (EVar 0)) (EMd M_MUL (ELit (-4096)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 140737496743936));
     (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6))) (ELit (-8388608)),
      EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-32768)) (EVar 0)) (EMd M_MUL (ELit (-16)) (EVar 6))) (ELit 140737496743936))];
  a_ghost := [(EMd M_MUL (ELit 4096) (EVar 335), ELit 4096)];
  a_abytes := 4862246912;
  a_brk := EMd M_MUL (ELit 4096) (EVar 5);
  a_fd := FdStd;
  a_tidset := true
|}.

Definition startup_plan : plan :=
  PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XEnvScan [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XPnScan [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PSys YSetTid (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [0x8e2dc] (* [comment removed for export] *)
  (PWordFresh (ELit 0x5f9bb0) 8 (* [comment removed for export] *)
  (PRun [0x64a78] (* [comment removed for export] *)
  (PRespell 10 (ELit 0x7fffffffffff) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 40 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 40 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 40 [] (* [comment removed for export] *)
  (PRun [0x637ec] (* [comment removed for export] *)
  (PX XIStrncpy [] (* [comment removed for export] *)
  (PRun [0x637ec] (* [comment removed for export] *)
  (PX XIStrncpy [] (* [comment removed for export] *)
  (PRun [0x58e24] (* [comment removed for export] *)
  (PDropRange (ELit 0x136680) (ELit 0xfff) (PDropRange (ELit 0x137680) (ELit 0xfff) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 93)) (ELit 65536) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 93)) (ELit 65536) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [0x3d400] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 4800) (ELit 240) (* [comment removed for export] *)
  (PRun [0x3d818] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 5040) (ELit 320) (* [comment removed for export] *)
  (PRun [0x61400] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 5360) (ELit 320) (* [comment removed for export] *)
  (PRun [0x61820] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 1536) (ELit 264) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 5680) (ELit 128) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 5824) (ELit 176) (* [comment removed for export] *)
  (PRun [0x61c54] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 1800) (ELit 480) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 6000) (ELit 336) (* [comment removed for export] *)
  (PRun [0x62074] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 2280) (ELit 504) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 6336) (ELit 320) (* [comment removed for export] *)
  (PRun [0x6308c] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 2784) (ELit 432) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 6656) (ELit 320) (* [comment removed for export] *)
  (PRun [0x61230] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 6976) (ELit 432) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 11776) (ELit 296) (* [comment removed for export] *)
  (PRun [0x61670] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 7408) (ELit 504) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 12072) (ELit 328) (* [comment removed for export] *)
  (PRun [0x61a98] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 7912) (ELit 480) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 12400) (ELit 320) (* [comment removed for export] *)
  (PRun [0x61ec4] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 8392) (ELit 480) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 12720) (ELit 336) (* [comment removed for export] *)
  (PRun [0x622e4] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 8872) (ELit 504) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 13056) (ELit 320) (* [comment removed for export] *)
  (PRun [0x61318] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 9376) (ELit 144) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 13376) (ELit 368) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 18304) (ELit 176) (* [comment removed for export] *)
  (PRun [0x61748] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 13744) (ELit 504) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 18480) (ELit 320) (* [comment removed for export] *)
  (PRun [0x61b68] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 14248) (ELit 480) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 18800) (ELit 320) (* [comment removed for export] *)
  (PRun [0x61f94] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 14728) (ELit 480) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 19120) (ELit 336) (* [comment removed for export] *)
  (PRun [0x623b0] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 15208) (ELit 504) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 19456) (ELit 320) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 19776) (ELit 64) (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [0x58e28] (* [comment removed for export] *)
  (PDropRange (escale 4096 (EVar 93)) (ELit 0x10000) (* [comment removed for export] *)
  (PRun [0x64a78] (* [comment removed for export] *)
  (PRespell 10 (ELit 0x7fffffffffff) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 222)) (ELit 3727360) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 222)) (ELit 3727360) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [0x58eec] (* [comment removed for export] *)
  (PDropRange (ELit 0xa44b8) (ELit 0x12b0) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 223)) (ELit 137439023104) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 223)) (ELit 137439023104) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [0x6b830] (* [comment removed for export] *)
  (PFresh 9 12 None (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 241)) (ELit 8388608) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 241)) (ELit 8388608) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 242)) (ELit 4096) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 242)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 243)) (ELit 65536) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 243)) (ELit 65536) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [0x53228] (* [comment removed for export] *)
  (PDisjDia (escale 4096 (EVar 243)) (ELit 2147446784) 0 0x534ac [13; 14; 15; 16; 17; 5; 6; 7; 28]%nat (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 269)) (ELit 4096) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 269)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemIsZero [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 334)) (ELit 4096) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 334)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 335)) (ELit 4096) (ELit 65536) (ELit 6209536) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 335)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PSys YMunmap (* [comment removed for export] *)
  (PVia 1 startup_js1 385 (* [comment removed for export] *)
  (PSplit (EVar 6) 10 (* [comment removed for export] *)
  (startup_plan_arm6)
  (PSplit (EVar 6) 1802 (* [comment removed for export] *)
   (startup_plan_arm6)
   (startup_plan_arm6)))
  (startup_plan_rest))))))))))))))))))))))))))))))))))))))))))))))
  (PContra (* [comment removed for export] *))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition startup_plan_ranges : list (Z * nat) := [(0x30000, 1024%nat); (0x32000, 2048%nat); (0x36000, 2048%nat); (0x3c000, 6144%nat); (0x46000, 9216%nat); (0x50000, 5120%nat); (0x58000, 6144%nat); (0x5f000, 8192%nat); (0x68000, 6144%nat); (0x6f000, 5120%nat); (0x79000, 2048%nat); (0x7c000, 1024%nat); (0x7f000, 2048%nat); (0x8d000, 4096%nat); (0x92000, 1024%nat); (0x97000, 4096%nat)]%Z.
