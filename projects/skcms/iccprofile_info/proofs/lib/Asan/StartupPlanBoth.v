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
  PRun [0x3e6d8] (* [comment removed for export] *)
  (PJoin e_sp0 (-2280) 8 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 452)) (ELit 1048576) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 452)) (ELit 1048576) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 453)) (ELit 8388608) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 453)) (ELit 8388608) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [0x3e6e8] (* [comment removed for export] *)
  (PExt 113 [ELit 100] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 470)) (ELit 4096) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 470)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
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
  (PRun [0x7fa74] (* [comment removed for export] *)
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
  (PHavocBrk 0x5fd000 0x805ff000 (* [comment removed for export] *)
  (PGcKeep [(ELit 2147459072, ELit 841728); (ELit 17594064011264, ELit 269484032); (ELit 652192, ELit 32); (ELit 653328, ELit 32); (ELit 653544, ELit 160); (ELit 656512, ELit 24); (ELit 656752, ELit 176); (ELit 661008, ELit 184); (ELit 661280, ELit 24); (ELit 661360, ELit 88); (ELit 671432, ELit 168); (ELit 671664, ELit 176); (ELit 671904, ELit 88); (ELit 672048, ELit 24); (ELit 672144, ELit 384); (ELit 672584, ELit 192); (ELit 672888, ELit 72); (ELit 673272, ELit 56); (ELit 673384, ELit 40); (ELit 673472, ELit 56); (ELit 676208, ELit 32); (ELit 676296, ELit 80); (ELit 676456, ELit 24); (ELit 684560, ELit 32); (ELit 686512, ELit 32); (ELit 689808, ELit 56); (ELit 1219608, ELit 24); (ELit 1274944, ELit 48); (ELit 1283192, ELit 32); (ELit 1283328, ELit 136); (ELit 1283544, ELit 32); (ELit 1284184, ELit 24); (ELit 1546368, ELit 48); (ELit 2507472, ELit 24); (ELit 2570648, ELit 24); (ELit 3679040, ELit 24); (ELit 5136240, ELit 24); (ELit 5476304, ELit 24); (ELit 5781032, ELit 24); (ELit 5806224, ELit 40); (ELit 6135816, ELit 24); (ELit 6138048, ELit 24); (ELit 6138128, ELit 24); (ELit 6138208, ELit 72); (ELit 6138352, ELit 8); (ELit 6269360, ELit 64); (ELit 6269656, ELit 24); (ELit 6269912, ELit 56); (ELit 6271072, ELit 24); (ELit 6274320, ELit 24); (eaddz e_sp0 (0), ELit 32); (eaddz e_sp0 (184), ELit 4128); (escale 4096 (EVar 93), ELit 0); (escale 4096 (EVar 222), ELit 0); (eaddz (escale 4096 (EVar 223)) (4295008248), ELit 24); (eaddz (escale 4096 (EVar 223)) (8589975544), ELit 24); (eaddz (escale 4096 (EVar 223)) (25769844776), ELit 24); (eaddz (escale 4096 (EVar 223)) (73014485096), ELit 24); (eaddz (escale 4096 (EVar 223)) (98784289000), ELit 24); (eaddz (escale 4096 (EVar 223)) (128849060840), ELit 24); (eaddz (escale 4096 (EVar 223)) (137438994552), ELit 224); (eaddz (escale 4096 (EVar 223)) (137438995192), ELit 96); (eaddz (escale 4096 (EVar 223)) (137438996600), ELit 96); (eaddz (escale 4096 (EVar 223)) (137438997368), ELit 224); (eaddz (escale 4096 (EVar 223)) (137438998264), ELit 96); (escale 4096 (EVar 241), ELit 0); (eaddz (escale 4096 (EVar 242)) (-8), ELit 128); (eaddz (escale 4096 (EVar 242)) (280), ELit 24); (eaddz (escale 4096 (EVar 242)) (360), ELit 24); (eaddz (escale 4096 (EVar 242)) (680), ELit 24); (eaddz (escale 4096 (EVar 242)) (1560), ELit 24); (eaddz (escale 4096 (EVar 242)) (2040), ELit 24); (eaddz (escale 4096 (EVar 242)) (2120), ELit 24); (eaddz (escale 4096 (EVar 242)) (2600), ELit 24); (eaddz (escale 4096 (EVar 242)) (2776), ELit 200); (eaddz (escale 4096 (EVar 242)) (3040), ELit 144); (eaddz (escale 4096 (EVar 243)) (0), ELit 24); (eaddz (escale 4096 (EVar 243)) (144), ELit 24); (escale 4096 (EVar 269), ELit 0); (eaddz (escale 4096 (EVar 334)) (16), ELit 24); (escale 4096 (EVar 335), ELit 0); (eaddz (escale 4096 (EVar 401)) (32), ELit 80); (eaddz (escale 4096 (EVar 401)) (35832), ELit 24); (escale 4096 (EVar 418), ELit 0); (escale 4096 (EVar 418), ELit 0); (escale 4096 (EVar 451), ELit 0); (escale 4096 (EVar 452), ELit 0); (escale 4096 (EVar 469), ELit 0); (escale 4096 (EVar 470), ELit 0)] (* [comment removed for export] *)
  (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 368))) 3935) 0 4095) (* [comment removed for export] *)
  (PFact (KRange (EVar 368) 0 8) (* [comment removed for export] *)
  (PHandoff 0 (* [comment removed for export] *))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_rcase2 : plan :=
  PRun [0x3e6d8] (* [comment removed for export] *)
  (PJoin e_sp0 (-2280) 8 (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 452)) (ELit 1048576) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 452)) (ELit 1048576) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 453)) (ELit 8388608) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 453)) (ELit 8388608) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [0x3e6e8] (* [comment removed for export] *)
  (PExt 113 [ELit 100] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 470)) (ELit 4096) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 470)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)
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
  (PRun [0x7fa74] (* [comment removed for export] *)
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
  (PHavocBrk 0x5fd000 0x805ff000 (* [comment removed for export] *)
  (PGcKeep [(ELit 2147459072, ELit 841728); (ELit 17594064011264, ELit 269484032); (ELit 652192, ELit 32); (ELit 653328, ELit 32); (ELit 653544, ELit 160); (ELit 656512, ELit 24); (ELit 656752, ELit 176); (ELit 661008, ELit 184); (ELit 661280, ELit 24); (ELit 661360, ELit 88); (ELit 671432, ELit 168); (ELit 671664, ELit 176); (ELit 671904, ELit 88); (ELit 672048, ELit 24); (ELit 672144, ELit 384); (ELit 672584, ELit 192); (ELit 672888, ELit 72); (ELit 673272, ELit 56); (ELit 673384, ELit 40); (ELit 673472, ELit 56); (ELit 676208, ELit 32); (ELit 676296, ELit 80); (ELit 676456, ELit 24); (ELit 684560, ELit 32); (ELit 686512, ELit 32); (ELit 689808, ELit 56); (ELit 1219608, ELit 24); (ELit 1274944, ELit 48); (ELit 1283192, ELit 32); (ELit 1283328, ELit 136); (ELit 1283544, ELit 32); (ELit 1284184, ELit 24); (ELit 1546368, ELit 48); (ELit 2507472, ELit 24); (ELit 2570648, ELit 24); (ELit 3679040, ELit 24); (ELit 5136240, ELit 24); (ELit 5476304, ELit 24); (ELit 5781032, ELit 24); (ELit 5806224, ELit 40); (ELit 6135816, ELit 24); (ELit 6138048, ELit 24); (ELit 6138128, ELit 24); (ELit 6138208, ELit 72); (ELit 6138352, ELit 8); (ELit 6269360, ELit 64); (ELit 6269656, ELit 24); (ELit 6269912, ELit 56); (ELit 6271072, ELit 24); (ELit 6274320, ELit 24); (eaddz e_sp0 (0), ELit 32); (eaddz e_sp0 (184), ELit 4128); (escale 4096 (EVar 93), ELit 0); (escale 4096 (EVar 222), ELit 0); (eaddz (escale 4096 (EVar 223)) (4295008248), ELit 24); (eaddz (escale 4096 (EVar 223)) (8589975544), ELit 24); (eaddz (escale 4096 (EVar 223)) (25769844776), ELit 24); (eaddz (escale 4096 (EVar 223)) (73014485096), ELit 24); (eaddz (escale 4096 (EVar 223)) (98784289000), ELit 24); (eaddz (escale 4096 (EVar 223)) (128849060840), ELit 24); (eaddz (escale 4096 (EVar 223)) (137438994552), ELit 224); (eaddz (escale 4096 (EVar 223)) (137438995192), ELit 96); (eaddz (escale 4096 (EVar 223)) (137438996600), ELit 96); (eaddz (escale 4096 (EVar 223)) (137438997368), ELit 224); (eaddz (escale 4096 (EVar 223)) (137438998264), ELit 96); (escale 4096 (EVar 241), ELit 0); (eaddz (escale 4096 (EVar 242)) (-8), ELit 128); (eaddz (escale 4096 (EVar 242)) (280), ELit 24); (eaddz (escale 4096 (EVar 242)) (360), ELit 24); (eaddz (escale 4096 (EVar 242)) (680), ELit 24); (eaddz (escale 4096 (EVar 242)) (1560), ELit 24); (eaddz (escale 4096 (EVar 242)) (2040), ELit 24); (eaddz (escale 4096 (EVar 242)) (2120), ELit 24); (eaddz (escale 4096 (EVar 242)) (2600), ELit 24); (eaddz (escale 4096 (EVar 242)) (2776), ELit 200); (eaddz (escale 4096 (EVar 242)) (3040), ELit 144); (eaddz (escale 4096 (EVar 243)) (0), ELit 24); (eaddz (escale 4096 (EVar 243)) (144), ELit 24); (escale 4096 (EVar 269), ELit 0); (eaddz (escale 4096 (EVar 334)) (16), ELit 24); (escale 4096 (EVar 335), ELit 0); (eaddz (escale 4096 (EVar 401)) (32), ELit 80); (eaddz (escale 4096 (EVar 401)) (35832), ELit 24); (escale 4096 (EVar 418), ELit 0); (escale 4096 (EVar 418), ELit 0); (escale 4096 (EVar 451), ELit 0); (escale 4096 (EVar 452), ELit 0); (escale 4096 (EVar 469), ELit 0); (escale 4096 (EVar 470), ELit 0)] (* [comment removed for export] *)
  (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 368))) 3935) 0 4095) (* [comment removed for export] *)
  (PFact (KRange (EVar 368) 0 8) (* [comment removed for export] *)
  (PHandoff 0 (* [comment removed for export] *))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_brkfail3 : plan :=
  PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 418)) (ELit 8192) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 418)) (ELit 8192) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMprotect (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 419)) (ELit 4096) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 419)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [0x728b8] (* [comment removed for export] *)
  (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 368))) 3935) 4030 (* [comment removed for export] *)
  (startup_plan_rcase2)
  (startup_plan_rcase2)))))))))))))))).

Definition startup_plan_arm6 : plan :=
  PBump 368 (* [comment removed for export] *)
  (  PRun [0x6bd90] (* [comment removed for export] *)
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
  (PShDisj (escale 4096 (EVar 401)) (ELit 11571200) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
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
   (PShDisj (escale 4096 (EVar 418)) (ELit 4096) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
   (PShDisj (escale 4096 (EVar 418)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
   (PIntro 1 34359736319 (* [comment removed for export] *)
   (PRun [] (* [comment removed for export] *)
   (PX XIMemset [] (* [comment removed for export] *)
   (PRun [] (* [comment removed for export] *)
   (PX XIMemset [] (* [comment removed for export] *)
   (PRun [0x728b8] (* [comment removed for export] *)
   (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 368))) 3935) 4030 (* [comment removed for export] *)
   (startup_plan_rcase1)
   (startup_plan_rcase1))))))))))))
   (PContra (* [comment removed for export] *)))))))))))))))).

(* [comment removed for export] *)
Definition startup_js1 : acs :=
{|
  a_ss :=
    SS 374984
      [ELit 0; EVar 369; EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6))) (ELit (-320)); ELit 67584; ELit 6138224; EVar 370; EVar 371; 
       EVar 372; EMd M_MUL (ELit 4096) (EVar 242); ELit 0; EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EVar 368))) (ELit 2146402304); 
       EVar 374; EVar 375; EVar 376; EVar 377; EVar 378; EVar 379; EVar 380; ELit 1; ELit 689816; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; EVar 381; 
       EVar 382; EVar 383; EVar 384]
      []
      [KRange (EVar 368) 0 8; KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit (-4096)) (EVar 368))) (ELit 3935)) 0 4095;
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -320 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -312 |} 8 (ELit 689816);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -304 |} 8 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -296 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -288 |} 8 (EMd M_MUL (ELit 4096) (EVar 242));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -280 |} 8 (ELit 376868);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 64 |} 8 (ELit 6138232);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 16 |} 8 (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EVar 368))) (ELit (-8388608)));
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 8 |} 8 (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EVar 368)));
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 56 |} 8 (ELit 6140292); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 48 |} 8 (ELit 6140072);
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 335); a_off := 2147450880 |} (ELit 512)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 335); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704); KRange (EVar 335) 1 34359736319;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 335); a_off := 0 |} (ELit 4096)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 1283912 |} 1 (ELit 1); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 32 |} 8 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 24 |} 8 (ELit 6138224); KWord {| a_base := ELit 0; a_off := 673280 |} 1 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 673281 |} 3 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283832 |} 8 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6138232 |} 8 (EMd M_MUL (ELit 4096) (EVar 334));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 334); a_off := 2147450880 |} (ELit 512)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 334); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704);
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
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 334); a_off := 0 |} (ELit 4096)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 40 |} 1 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 32 |} 8 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 24 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -264 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -256 |} 8 (EMd M_MUL (ELit 4096) (EVar 242));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -248 |} 8 (ELit 377508); KWord {| a_base := ELit 0; a_off := 6138074 |} 1 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6274328 |} 8 (EMd M_MUL (ELit 4096) (EVar 243)); KWord {| a_base := ELit 0; a_off := 690992 |} 8 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} 8 (EMd M_MUL (ELit 4096) (EVar 243));
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 152 |} 8 (EMd M_MUL (ELit 4096) (EVar 242)); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 116 |} 1 (ELit 1);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 112 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 691008 |} 8 (ELit 1);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 40 |} 8 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 16 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 691024 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 691016 |} 8 (ELit 1);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} 8 (EMd M_MUL (ELit 4096) (EVar 243)); KWord {| a_base := ELit 0; a_off := 691056 |} 8 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 691048 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 691040 |} 8 (EMd M_MUL (ELit 4096) (EVar 269));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 269); a_off := 2147450880 |} (ELit 512)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 269); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704);
       KWr {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 8 |} (ELit 4088); KRange (EVar 269) 1 34359736319;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 269); a_off := 0 |} (ELit 4096)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 690888 |} 8 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} 8 (ELit 652360);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 148 |} 2 (ELit 1024); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 144 |} 4 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 24 |} 4 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 8 |} 4 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 48 |} 1 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 32 |} 8 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 136 |} 8 (ELit 0); KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 128 |} 4 (ELit 0);
       KWord {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 120 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 690912 |} 8 (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 243)) (ELit 160));
       KWord {| a_base := ELit 0; a_off := 690904 |} 8 (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 243)) (ELit 65536));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 243); a_off := 2147450880 |} (ELit 8192)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 243); a_off := 2147450880 |} (ELit 8192) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704);
       KWr {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 12 |} (ELit 4);
       KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 28 |} (ELit 4); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 49 |} (ELit 63);
       KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 117 |} (ELit 3); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 132 |} (ELit 4);
       KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 150 |} (ELit 2); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 160 |} (ELit 65376);
       KRange (EVar 243) 1533 34359736304; KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 243); a_off := 0 |} (ELit 65536)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 690960 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 690952 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 690944 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 690936 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 690880 |} 8 (ELit 690920); KWord {| a_base := ELit 0; a_off := 690864 |} 1 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 690932 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 690928 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 690920 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 690964 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 690956 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 690872 |} 8 (ELit 690968);
       KWord {| a_base := ELit 0; a_off := 691096 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 691088 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 691080 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 691072 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 691064 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 691128 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 691120 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 691112 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 691104 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 691032 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 691004 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 691000 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 690984 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 690976 |} 8 (ELit 18446744073709551615);
       KWord {| a_base := ELit 0; a_off := 690968 |} 8 (ELit 382040);
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 242); a_off := 2147450880 |} (ELit 512)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 242); a_off := 2147450880 |} (ELit 512) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704);
       KWr {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 41 |} (ELit 7);
       KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 72 |} (ELit 4024); KRange (EVar 242) 1 34359736319;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 242); a_off := 0 |} (ELit 4096)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -272 |} 8 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -232 |} 8 (ELit 689816);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -224 |} 8 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -216 |} 8 (ELit 1283304);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -208 |} 8 (ELit 676280);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -200 |} 8 (ELit 364472);
       KWord {| a_base := ELit 0; a_off := 1283872 |} 8 (ELit 455892); KWord {| a_base := ELit 0; a_off := 6269384 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 6269664 |} 8 (ELit 455892);
       KWord {| a_base := ELit 0; a_off := 6269408 |} 8 (ELit 586724); KWord {| a_base := ELit 0; a_off := 6269392 |} 8 (ELit 6269400);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -240 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 1284184 |} 1 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 689816 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 689817 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 676216 |} 8 (ELit 1099511627776);
       KWord {| a_base := ELit 0; a_off := 676226 |} 2 (ELit 2048); KWord {| a_base := ELit 0; a_off := 676224 |} 2 (ELit 16); KWord {| a_base := ELit 0; a_off := 676228 |} 1 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 673481 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 673480 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 673408 |} 8 (ELit 1048576);
       KWord {| a_base := ELit 0; a_off := 673400 |} 8 (ELit 241591905); KWord {| a_base := ELit 0; a_off := 673392 |} 8 (ELit 268435456);
       KWord {| a_base := ELit 0; a_off := 672672 |} 8 (EMd M_MUL (ELit 4096) (EVar 241)); KWord {| a_base := ELit 0; a_off := 672696 |} 8 (ELit 102840);
       KWord {| a_base := ELit 0; a_off := 672688 |} 8 (ELit 8388608); KWord {| a_base := ELit 0; a_off := 672680 |} 8 (EMd M_MUL (ELit 4096) (EVar 241));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 241); a_off := 2147450880 |} (ELit 1048576)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 241); a_off := 2147450880 |} (ELit 1048576) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704); KRange (EVar 241) 1533 34359734272;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 241); a_off := 0 |} (ELit 8388608)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 672664 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 672640 |} 4 (ELit 18446744073709551615);
       KWord {| a_base := ELit 0; a_off := 689976 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 689968 |} 8 (ELit 1);
       KWr {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 223)) (EMd M_MUL (ELit (-4096)) (EVar 224)); a_off := 137439019008 |} (ELit 4096);
       KZero {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 223)) (EMd M_MUL (ELit (-4096)) (EVar 224)); a_off := 137439019008 |} (ELit 4096);
       KWord {| a_base := ELit 0; a_off := 672648 |} 8 (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 223)) (EMd M_MUL (ELit (-4096)) (EVar 224))) (ELit 137439019008));
       KWord {| a_base := ELit 0; a_off := 672632 |} 8 (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 223)) (EMd M_MUL (ELit (-4096)) (EVar 224))) (ELit 65536)); 
       KRange (EVar 224) 0 15; KRange (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 224)) (EAlu ALU_AND (EMd M_MUL (ELit 4096) (EVar 223)) (ELit 65535))) 0 0;
       KWord {| a_base := ELit 0; a_off := 672616 |} 8 (ELit 92859); KWord {| a_base := ELit 0; a_off := 672608 |} 8 (ELit 137439023104);
       KWord {| a_base := ELit 0; a_off := 672600 |} 8 (EMd M_MUL (ELit 4096) (EVar 223));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 223); a_off := 2147450880 |} (ELit 17179877888)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 223); a_off := 2147450880 |} (ELit 17179877888) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704);
       KRange (EVar 223) 4295491576 34326181871;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 223); a_off := 0 |} (ELit 137439023104)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 672656 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 1219617 |} 1 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -164 |} 4 (ELit 18446744073709551615);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -167 |} 1 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -168 |} 1 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -170 |} 2 (ELit 2048);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -172 |} 2 (ELit 16);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -176 |} 4 (ELit 1024);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -180 |} 4 (ELit 256);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -166 |} 2 (ELit 43690); KWord {| a_base := ELit 0; a_off := 6274272 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6273240 |} 8 (ELit 345148); KWord {| a_base := ELit 0; a_off := 6274264 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 684580 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6138136 |} 8 (ELit 6274328); KWord {| a_base := ELit 0; a_off := 684576 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 686520 |} 8 (ELit 2147450880);
       KWord {| a_base := ELit 0; a_off := 684538 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 684536 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 684540 |} 4 (ELit 299);
       KWord {| a_base := ELit 0; a_off := 684552 |} 8 (EMd M_MUL (ELit 4096) (EVar 222)); KWord {| a_base := ELit 0; a_off := 684544 |} 8 (ELit 684552);
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 222); a_off := 2147450880 |} (ELit 465920)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 222); a_off := 2147450880 |} (ELit 465920) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704);
       KWr {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360);
       KRange (EVar 222) 1533 34359735410; KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 222); a_off := 0 |} (ELit 3727360)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 684537 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1219608 |} 8 (ELit 365900); KWord {| a_base := ELit 0; a_off := 661440 |} 8 (ELit 8);
       KWord {| a_base := ELit 0; a_off := 686528 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 1283296 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 661464 |} 4 (ELit 2);
       KWord {| a_base := ELit 0; a_off := 1283297 |} 3 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283792 |} 8 (ELit 345664); KWord {| a_base := ELit 0; a_off := 1283856 |} 8 (ELit 365760);
       KWord {| a_base := ELit 0; a_off := 1283864 |} 8 (ELit 365528); KWord {| a_base := ELit 0; a_off := 689824 |} 8 (ELit 140737488355327);
       KWord {| a_base := ELit 0; a_off := 689852 |} 4 (ELit 30); KWord {| a_base := ELit 0; a_off := 684572 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 684568 |} 4 (ELit 2);
       KWord {| a_base := ELit 0; a_off := 676358 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1283304 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 1283312 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1283320 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283328 |} 8 (ELit 81553); KWord {| a_base := ELit 0; a_off := 1283336 |} 8 (ELit 128849084416);
       KWord {| a_base := ELit 0; a_off := 1283344 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283352 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283360 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1283368 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283376 |} 8 (ELit 1103823372545);
       KWord {| a_base := ELit 0; a_off := 1283384 |} 8 (ELit 4294967296); KWord {| a_base := ELit 0; a_off := 1283392 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283400 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1283408 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283416 |} 8 (ELit 65537);
       KWord {| a_base := ELit 0; a_off := 1283424 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1283432 |} 8 (ELit 71687);
       KWord {| a_base := ELit 0; a_off := 1283440 |} 8 (ELit 256); KWord {| a_base := ELit 0; a_off := 1283448 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283456 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1283464 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283472 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1283480 |} 8 (ELit 18446744069414584320); KWord {| a_base := ELit 0; a_off := 1283488 |} 8 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 1283496 |} 8 (ELit 82413); KWord {| a_base := ELit 0; a_off := 1283504 |} 8 (ELit 81553); KWord {| a_base := ELit 0; a_off := 1283512 |} 8 (ELit 81553);
       KWord {| a_base := ELit 0; a_off := 1283520 |} 8 (ELit 1103823372544); KWord {| a_base := ELit 0; a_off := 1283528 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1283536 |} 8 (ELit 121305); KWord {| a_base := ELit 0; a_off := 1283544 |} 8 (ELit 72339073309605888);
       KWord {| a_base := ELit 0; a_off := 1283552 |} 8 (ELit 72340172838076673); KWord {| a_base := ELit 0; a_off := 1283560 |} 8 (ELit 16843009);
       KWord {| a_base := ELit 0; a_off := 1283568 |} 8 (ELit 1103806595073); KWord {| a_base := ELit 0; a_off := 1283576 |} 8 (ELit 101169);
       KWord {| a_base := ELit 0; a_off := 1283584 |} 8 (ELit 281474976710912); KWord {| a_base := ELit 0; a_off := 676288 |} 4 (ELit 1024);
       KWord {| a_base := ELit 0; a_off := 676284 |} 4 (ELit 256); KWord {| a_base := ELit 0; a_off := 1274968 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 1219600 |} 8 (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 93)) (ELit 19880)); KWord {| a_base := ELit 0; a_off := 6070280 |} 2 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6070272 |} 8 (ELit 81553); KWord {| a_base := ELit 0; a_off := 6070264 |} 2 (ELit 0); KWord {| a_base := ELit 0; a_off := 6069672 |} 4 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6069648 |} 4 (ELit 257); KWord {| a_base := ELit 0; a_off := 6069640 |} 8 (ELit 72340172821233664);
       KWord {| a_base := ELit 0; a_off := 6069636 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6069632 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6069664 |} 8 (ELit 81553);
       KWord {| a_base := ELit 0; a_off := 6069656 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 6069654 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6069652 |} 2 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 676370 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 676300 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 676384 |} 8 (ELit 81553);
       KWord {| a_base := ELit 0; a_off := 676380 |} 4 (ELit 2); KWord {| a_base := ELit 0; a_off := 676376 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 676372 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 676368 |} 2 (ELit 1); KWord {| a_base := ELit 0; a_off := 676360 |} 8 (ELit 72340172838010881);
       KWord {| a_base := ELit 0; a_off := 676352 |} 6 (ELit 4294967296); KWord {| a_base := ELit 0; a_off := 676359 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 676324 |} 4 (ELit 4096);
       KWord {| a_base := ELit 0; a_off := 676320 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 676312 |} 8 (ELit 85899345936);
       KWord {| a_base := ELit 0; a_off := 676304 |} 8 (ELit 72340168526266369); KWord {| a_base := ELit 0; a_off := 676296 |} 4 (ELit 2048); KWord {| a_base := ELit 0; a_off := 676344 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 676340 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 676336 |} 4 (ELit 85); KWord {| a_base := ELit 0; a_off := 676328 |} 8 (ELit 816043786240);
       KWord {| a_base := ELit 0; a_off := 676292 |} 4 (ELit 16); KWord {| a_base := ELit 0; a_off := 676280 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 676392 |} 4 (ELit 65793);
       KWord {| a_base := ELit 0; a_off := 1219592 |} 8 (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 93)) (ELit 65536));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 93); a_off := 2147450880 |} (ELit 8192)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KDisj {| a_base := EMd M_MUL (ELit 512) (EVar 93); a_off := 2147450880 |} (ELit 8192) {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704);
       KWr {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536); KZero {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 65536 |} (ELit 0); KRange (EVar 93) 1533 34359736304;
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := ELit 2147446784; a_off := 0 |} (ELit 17592186048512);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536) {| a_base := ELit 65536; a_off := 0 |} (ELit 6213632);
       KDisj {| a_base := EMd M_MUL (ELit 4096) (EVar 93); a_off := 0 |} (ELit 65536)
         {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := -8388608 |} (ELit 2155876352);
       KWord {| a_base := ELit 0; a_off := 1274976 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 689848 |} 1 (ELit 1);
       KWr {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KZero {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EAlu ALU_SRL (EVar 6) (ELit 8))); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 17592187092992));
       KWr {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 2) (EVar 6)); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-2)) (EVar 6))) (ELit 17592187092992));
       KZero {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 2) (EVar 6)); a_off := 2146402304 |}
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-2)) (EVar 6))) (ELit 17592187092992));
       KWr {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704); KZero {| a_base := ELit 0; a_off := 2147459072 |} (ELit 776704);
       KWord {| a_base := ELit 0; a_off := 1274960 |} 8 (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6))) (ELit (-160)));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -160 |} 8 (ELit 12297829382473034410);
       KWord {| a_base := ELit 0; a_off := 661448 |} 8 (ELit 131724);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -152 |} 8
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EMd M_MUL (ELit 16) (EVar 6)))) (ELit 16));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -144 |} 8 (ELit 522868);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -136 |} 8 (ELit 652168);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -128 |} 8 (ELit 689816);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -120 |} 8 (ELit 365392); KWord {| a_base := ELit 0; a_off := 689818 |} 2 (ELit 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -112 |} 8 (ELit 652200);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -104 |} 8 (ELit 525628);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -88 |} 8 (ELit 584824);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -72 |} 8 (EVar 1);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -64 |} 8
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6))) (ELit 8));
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -56 |} 8 (ELit 585000);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -40 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -32 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -24 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -16 |} 8 (ELit 0);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -8 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6138208 |} 8 (EVar 60);
       KWord {| a_base := ELit 0; a_off := 6269360 |} 8 (EVar 60); KWord {| a_base := ELit 0; a_off := 6269361 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6269360 |} 1 (EBlob false 25 0 1);
       KWord {| a_base := ELit 0; a_off := 6269362 |} 6 (EBlob false 25 2 6); KWord {| a_base := ELit 0; a_off := 6138048 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6138040 |} 8 (ELit 6138024); KWord {| a_base := ELit 0; a_off := 6138032 |} 8 (ELit 6138024);
       KWord {| a_base := ELit 0; a_off := 6138144 |} 8 (ELit 6138144); KWord {| a_base := ELit 0; a_off := 6138176 |} 8 (ELit 6270008); KWord {| a_base := ELit 0; a_off := 6138056 |} 4 (EVar 43);
       KRange (EVar 43) 1 4194303; KWord {| a_base := ELit 0; a_off := 6138064 |} 4 (ELit 2); KWord {| a_base := ELit 0; a_off := 6269952 |} 1 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6138024 |} 8 (ELit 6138024); KWord {| a_base := ELit 0; a_off := 6138216 |} 8 (ELit 6138256); KWord {| a_base := ELit 0; a_off := 6138256 |} 8 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6138264 |} 8 (ELit 6140272); KWord {| a_base := ELit 0; a_off := 6269984 |} 8 (ELit 8); KWord {| a_base := ELit 0; a_off := 6269976 |} 8 (ELit 248);
       KWord {| a_base := ELit 0; a_off := 6269352 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6269336 |} 8 (ELit 24); KWord {| a_base := ELit 0; a_off := 6269992 |} 8 (ELit 1);
       KWord {| a_base := ELit 0; a_off := 6269968 |} 8 (ELit 6269312); KWord {| a_base := ELit 0; a_off := 6269344 |} 8 (ELit 8); KWord {| a_base := ELit 0; a_off := 6269328 |} 8 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6269320 |} 8 (ELit 648072);
       KWord {| a_base := ELit 0; a_off := 6269944 |} 8
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6)))))
            (ELit 184));
       KWord {| a_base := ELit 0; a_off := 6270000 |} 8 (ELit 4096); KWord {| a_base := ELit 0; a_off := 6270056 |} 8 (EVar 9);
       KWord {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)); a_off := -184 |} 4 (ELit 0);
       KWord {| a_base := ELit 0; a_off := 6269960 |} 8
         (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6)))))
            (ELit 24));
       KWord {| a_base := ELit 0; a_off := 6138016 |} 8
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
       KRange (EVar 7) 0 131071; KRange (EVar 8) 0 4294967294; KRange (EVar 4) 0 280000; KRange (EVar 5) 1533 525821;
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
       KImg 65536 661440; KImg 661456 661464; KImg 661468 672600; KImg 672624 672632; KImg 672644 672648; KImg 672657 672664; KImg 672704 673280; KImg 673284 673392; KImg 673416 673480;
       KImg 673482 676216; KImg 676229 676280; KImg 676301 676304; KImg 676321 676324; KImg 676341 676344; KImg 676371 676372; KImg 676377 676380; KImg 676396 676536; KImg 681320 684536;
       KImg 684539 684540; KImg 684560 684568; KImg 684573 684576; KImg 684577 684580; KImg 684584 686520; KImg 686532 689816; KImg 689820 689824; KImg 689832 689848; KImg 689849 689852;
       KImg 689856 689968; KImg 689984 690864; KImg 690865 690872; KImg 690896 690904; KImg 690988 690992; KImg 691132 1219592; KImg 1219616 1219617; KImg 1219618 1274960; 
       KImg 1274972 1274976; KImg 1274984 1275008; KImg 1279103 1279104; KImg 1283199 1283296; KImg 1283300 1283304; KImg 1283592 1283792; KImg 1283800 1283832; KImg 1283840 1283856;
       KImg 1283880 1283912; KImg 1283913 1284184; KImg 1284185 6069632; KImg 6069633 6069636; KImg 6069655 6069656; KImg 6069660 6069664; KImg 6069676 6070264; KImg 6070266 6070272;
       KImg 6070282 6138016; KImg 6138060 6138064; KImg 6138068 6138074; KImg 6138075 6138136; KImg 6138152 6138176; KImg 6138184 6138208; KImg 6138224 6138232; KImg 6138240 6138256;
       KImg 6138272 6269320; KImg 6269368 6269384; KImg 6269388 6269392; KImg 6269400 6269408; KImg 6269416 6269664; KImg 6269672 6269936; KImg 6269953 6269960; KImg 6270008 6270056;
       KImg 6270064 6273240; KImg 6273248 6274264; KImg 6274268 6274272; KImg 6274276 6274328; KImg 6274336 6279168; KWr {| a_base := ELit 0; a_off := 651264 |} (ELit 5627904)]
      385;
  a_maps :=
    [{| am_base := EMd M_MUL (ELit 4096) (EVar 334); am_len := ELit 4096; am_kind := KRW |}; {| am_base := EMd M_MUL (ELit 4096) (EVar 269); am_len := ELit 4096; am_kind := KRW |};
     {| am_base := EMd M_MUL (ELit 4096) (EVar 243); am_len := ELit 65536; am_kind := KRW |}; {| am_base := EMd M_MUL (ELit 4096) (EVar 242); am_len := ELit 4096; am_kind := KRW |};
     {| am_base := EMd M_MUL (ELit 4096) (EVar 241); am_len := ELit 8388608; am_kind := KNONELAZY |}; {| am_base := EMd M_MUL (ELit 4096) (EVar 223); am_len := ELit 137439023104; am_kind := KRW |};
     {| am_base := EMd M_MUL (ELit 4096) (EVar 222); am_len := ELit 3727360; am_kind := KRW |}; {| am_base := EMd M_MUL (ELit 4096) (EVar 93); am_len := ELit 65536; am_kind := KRW |};
     {| am_base := ELit 2201439137792; am_len := ELit 15392894357504; am_kind := KRWLAZY |}; {| am_base := ELit 2415882240; am_len := ELit 2199023255552; am_kind := KNONELAZY |};
     {| am_base := ELit 2147446784; am_len := ELit 268435456; am_kind := KRWLAZY |}];
  a_totsz := 17729643548672;
  a_ylo := 23387528589312;
  a_eager := 3878912;
  a_vis :=
    [(EMd M_MUL (ELit 4096) (EVar 334), ELit 4096); (EMd M_MUL (ELit 4096) (EVar 269), ELit 4096); (EMd M_MUL (ELit 4096) (EVar 243), ELit 65536); (EMd M_MUL (ELit 4096) (EVar 242), ELit 4096);
     (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 223)) (EMd M_MUL (ELit (-4096)) (EVar 224))) (ELit 137439019008), ELit 4096); (EMd M_MUL (ELit 4096) (EVar 222), ELit 3727360);
     (EMd M_MUL (ELit 4096) (EVar 93), ELit 65536); (ELit 65536, ELit 6213632);
     (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit (-8388608)),
      EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-32768)) (EVar 0)) (EMd M_MUL (ELit (-4096)) (EAlu ALU_SRL (EVar 6) (ELit 8)))) (ELit 140737496743936));
     (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6))) (ELit (-8388608)),
      EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-32768)) (EVar 0)) (EMd M_MUL (ELit (-16)) (EVar 6))) (ELit 140737496743936))];
  a_ghost := [(EMd M_MUL (ELit 4096) (EVar 335), ELit 4096)];
  a_abytes := 4862251520;
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
  (PRun [0x8f10c] (* [comment removed for export] *)
  (PWordFresh (ELit 0x5fa9b0) 8 (* [comment removed for export] *)
  (PRun [0x64aa4] (* [comment removed for export] *)
  (PRespell 10 (ELit 0x7fffffffffff) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 40 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 40 [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PExt 40 [] (* [comment removed for export] *)
  (PRun [0x63818] (* [comment removed for export] *)
  (PX XIStrncpy [] (* [comment removed for export] *)
  (PRun [0x63818] (* [comment removed for export] *)
  (PX XIStrncpy [] (* [comment removed for export] *)
  (PRun [0x58e50] (* [comment removed for export] *)
  (PDropRange (ELit 0x137480) (ELit 0xfff) (PDropRange (ELit 0x138480) (ELit 0xfff) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 93)) (ELit 65536) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 93)) (ELit 65536) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XIMemcpy [] (* [comment removed for export] *)
  (PRun [0x3d42c] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 4800) (ELit 240) (* [comment removed for export] *)
  (PRun [0x3d844] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 5040) (ELit 320) (* [comment removed for export] *)
  (PRun [0x6142c] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 5360) (ELit 320) (* [comment removed for export] *)
  (PRun [0x6184c] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 1536) (ELit 264) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 5680) (ELit 128) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 5824) (ELit 176) (* [comment removed for export] *)
  (PRun [0x61c80] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 1800) (ELit 480) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 6000) (ELit 336) (* [comment removed for export] *)
  (PRun [0x620a0] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 2280) (ELit 504) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 6336) (ELit 320) (* [comment removed for export] *)
  (PRun [0x630b8] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 2784) (ELit 432) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 6656) (ELit 320) (* [comment removed for export] *)
  (PRun [0x6125c] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 6976) (ELit 432) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 11776) (ELit 296) (* [comment removed for export] *)
  (PRun [0x6169c] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 7408) (ELit 504) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 12072) (ELit 328) (* [comment removed for export] *)
  (PRun [0x61ac4] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 7912) (ELit 480) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 12400) (ELit 320) (* [comment removed for export] *)
  (PRun [0x61ef0] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 8392) (ELit 480) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 12720) (ELit 336) (* [comment removed for export] *)
  (PRun [0x62310] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 8872) (ELit 504) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 13056) (ELit 320) (* [comment removed for export] *)
  (PRun [0x61344] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 9376) (ELit 144) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 13376) (ELit 368) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 18304) (ELit 176) (* [comment removed for export] *)
  (PRun [0x61774] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 13744) (ELit 504) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 18480) (ELit 320) (* [comment removed for export] *)
  (PRun [0x61b94] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 14248) (ELit 480) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 18800) (ELit 320) (* [comment removed for export] *)
  (PRun [0x61fc0] (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 14728) (ELit 480) (* [comment removed for export] *)
  (PDropRange (eaddz (escale 4096 (EVar 93)) 19120) (ELit 336) (* [comment removed for export] *)
  (PRun [0x623dc] (* [comment removed for export] *)
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
  (PRun [0x58e54] (* [comment removed for export] *)
  (PDropRange (escale 4096 (EVar 93)) (ELit 0x10000) (* [comment removed for export] *)
  (PRun [0x64aa4] (* [comment removed for export] *)
  (PRespell 10 (ELit 0x7fffffffffff) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 222)) (ELit 3727360) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 222)) (ELit 3727360) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [0x58f18] (* [comment removed for export] *)
  (PDropRange (ELit 0xa52b8) (ELit 0x12b0) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 223)) (ELit 137439023104) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 223)) (ELit 137439023104) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [0x6b85c] (* [comment removed for export] *)
  (PFresh 9 12 None (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmapIn (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 241)) (ELit 8388608) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 241)) (ELit 8388608) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 242)) (ELit 4096) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 242)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 243)) (ELit 65536) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 243)) (ELit 65536) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [0x53254] (* [comment removed for export] *)
  (PDisjDia (escale 4096 (EVar 243)) (ELit 2147446784) 0 0x534d8 [13; 14; 15; 16; 17; 5; 6; 7; 28]%nat (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 269)) (ELit 4096) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
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
  (PShDisj (escale 4096 (EVar 334)) (ELit 4096) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
  (PShDisj (escale 4096 (EVar 334)) (ELit 4096) (eaddz e_pd (-8388608)) (esub (ELit 140737496743936) e_pd) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PMmap (* [comment removed for export] *)
  (PContra (* [comment removed for export] *))
  (PShDisj (escale 4096 (EVar 335)) (ELit 4096) (ELit 65536) (ELit 6213632) (* [comment removed for export] *)
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
Definition startup_plan_ranges : list (Z * nat) := [(0x30000, 1024%nat); (0x32000, 2048%nat); (0x36000, 2048%nat); (0x3c000, 6144%nat); (0x46000, 9216%nat); (0x50000, 5120%nat); (0x58000, 6144%nat); (0x5f000, 8192%nat); (0x68000, 6144%nat); (0x6f000, 5120%nat); (0x79000, 2048%nat); (0x7c000, 1024%nat); (0x7f000, 2048%nat); (0x8e000, 4096%nat); (0x93000, 1024%nat); (0x98000, 4096%nat)]%Z.
