(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the plan is fuzz_qdisc.asan's own: cgif_file_fuzzer's start-up plan (A/AB05.v at c8557374ad2e) relocated to this image by remap.py (asan-kit) with port_core 0e4e065eab9f's elfmap map, its itab ranges from itabranges.py --rule text (the .text whole: (0x2f9e4, 102995)), and each registration arm's tail measured by plantail.py probef on this image (all 50 arms [XMemset; XMemset; main], no PMmap: one asan global, no ODR indicator) and written by plantail.py insert --replace-tail --from-probe; the donor checker accepts the start-up with it (Cert: cgif's startup_shape) (h-small-a3). *)
(* Read from: fuzz_qdisc.asan (reac-pw/fuzz_qdisc asan) sha256 980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e; unstripped twin sha256 d77ead7cec5c42ebc28aff0443565f333cbb4dd08f5f1101d3deb805d5e34aac *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK0c.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK09 YA01 YA0c.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AB03.
Import ListNotations. Import AX2. Import APC. Import APG.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition startup_plan_tfib_brkfail1 : plan :=
PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 14  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 15  ))))))))))))))))))))))))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 12  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 13  ))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 10  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 11  ))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 8  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 9  ))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_tail2 : plan :=
PRun [0x6a508]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x50240]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x50288]
(PExt 2 [ELit 15; ELit 16]
(PRun []
(PX XMemcpy []
(PRun []
(PSys YBrk
(PRun []
(PBrk2
(startup_plan_tfib_brkfail1)
(PRun []
(PMmapIn
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 6  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 7  ))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 4  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 5  ))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 2  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 3  ))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 0  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 1  ))))))))))))))))))))))))))))))
(PExt 64 [eadd (escale 4096 (EVar 5)) (ELit 4096)]
(PUnvis (escale 4096 (EVar 5)) (ELit 4096)
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 42  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 43  ))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 40  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 41  ))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_s2A3 : plan :=
PBump 391
(startup_plan_tfib_tail2).
Definition startup_plan_tfib_brkfail4 : plan :=
PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 30  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 31  ))))))))))))))))))))))))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 28  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 29  ))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 26  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 27  ))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 24  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 25  ))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_tail5 : plan :=
PRun [0x6a508]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x50240]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x50288]
(PExt 2 [ELit 15; ELit 16]
(PRun []
(PX XMemcpy []
(PRun []
(PSys YBrk
(PRun []
(PBrk2
(startup_plan_tfib_brkfail4)
(PRun []
(PMmapIn
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 22  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 23  ))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 20  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 21  ))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 18  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 19  ))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 16  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 17  ))))))))))))))))))))))))))))))
(PExt 64 [eadd (escale 4096 (EVar 5)) (ELit 4096)]
(PUnvis (escale 4096 (EVar 5)) (ELit 4096)
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 46  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 47  ))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 44  )))))))))))))))))))))
(PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 45  ))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_s2B6 : plan :=
PBump 391
(startup_plan_tfib_tail5).
Definition startup_plan_tfib_rcase7 : plan :=
PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 32  )))))))))))))))))))).
Definition startup_plan_tfib_rcase8 : plan :=
PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 33  )))))))))))))))))))).
Definition startup_plan_tfib_rcase9 : plan :=
PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 34  )))))))))))))))))))).
Definition startup_plan_tfib_rcase10 : plan :=
PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 35  )))))))))))))))))))).
Definition startup_plan_tfib_rcase11 : plan :=
PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 48  )))))))))))))))))))).
Definition startup_plan_tfib_rcase12 : plan :=
PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 49  )))))))))))))))))))).
Definition startup_plan_tfib_rcase13 : plan :=
PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 36  )))))))))))))))))))).
Definition startup_plan_tfib_rcase14 : plan :=
PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 37  )))))))))))))))))))).
Definition startup_plan_tfib_rcase15 : plan :=
PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 38  )))))))))))))))))))).
Definition startup_plan_tfib_rcase16 : plan :=
PRun [0x3d52c]
(PForget []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7e1ec]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 39  )))))))))))))))))))).
Definition startup_plan_tfib_brkfail17 : plan :=
PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase16)
(startup_plan_tfib_rcase16))))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase15)
(startup_plan_tfib_rcase15))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase14)
(startup_plan_tfib_rcase14))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase13)
(startup_plan_tfib_rcase13))))))))))))).
Definition startup_plan_tfib_tail18 : plan :=
PRun [0x6a508]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x50240]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x50288]
(PExt 2 [ELit 15; ELit 16]
(PRun []
(PX XMemcpy []
(PRun []
(PSys YBrk
(PRun []
(PBrk2
(startup_plan_tfib_brkfail17)
(PRun []
(PMmapIn
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase10)
(startup_plan_tfib_rcase10))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase9)
(startup_plan_tfib_rcase9))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase8)
(startup_plan_tfib_rcase8))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase7)
(startup_plan_tfib_rcase7))))))))))
(PExt 64 [eadd (escale 4096 (EVar 5)) (ELit 4096)]
(PUnvis (escale 4096 (EVar 5)) (ELit 4096)
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase12)
(startup_plan_tfib_rcase12))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x710e4]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase11)
(startup_plan_tfib_rcase11))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_s2C19 : plan :=
PBump 391
(startup_plan_tfib_tail18).
Definition startup_plan_tfib_band20_arm : plan :=
PRun []
(PX XMemset []
(PMerge 1%nat  )).
Definition startup_plan_tfib_band20 : plan :=
(PRun []
(PMmap
(PRun []
(PSpin  ))
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
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun []
(PSys YMunmap
(PSplit (EVar 6) 10
(startup_plan_tfib_s2A3)
(PSplit (EVar 6) 1802
(startup_plan_tfib_s2B6)
(startup_plan_tfib_s2C19))))))))))))))))))))))).
Definition startup_plan_tfib_tospin21 : plan :=
PRun []
(PX XIMemset []
(PRun [0x65300]
(PFresh 21 0 None
(PRun [0x65300]
(PFresh 21 0 None
(PRun [0x65300]
(PFresh 21 0 None
(PRun [0x65300]
(PFresh 21 0 None
(PRun [0x65300]
(PFresh 21 0 None
(PRun [0x65300]
(PFresh 21 0 None
(PRun [0x65300]
(PFresh 21 0 None
(PRun [0x65300]
(PFresh 21 0 None
(PRun [0x65300]
(PFresh 21 0 None
(PRun [0x65300]
(PFresh 21 0 None
(PCase2 (EVar 281) 15
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun []
(PSpin  ))))))))))))))))))))))
(PRun [0x65300]
(PFresh 21 0 None
(PCase2 (EVar 282) 15
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun []
(PSpin  ))))))))))))))))))))))))
(PRun [0x65300]
(PFresh 21 0 None
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun [0x65490]
(PDiamond 0x65468 [16]%nat
(PRun []
(PSpin  ))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib : plan :=
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
(PX XIMemcpy []
(PRun [0x850b8]
(PExt 0 [ELit 0x5f0850; ELit 8]
(PRun [0x631ac]
(PExt 1 []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x61f90]
(PX XIStrncpy []
(PRun [0x61f90]
(PX XIStrncpy []
(PRun [0x575c8]
(PDropRange (ELit 0x12d340) (ELit 0xfff) (PDropRange (ELit 0x12e340) (ELit 0xfff)
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemcpy []
(PRun []
(PX XIMemcpy []
(PRun [0x3c0bc]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3c278]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3c424]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3c5ec]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3c798]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5fa34]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5fc00]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5fdb0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5ff7c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60134]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x602f8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x604a8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6066c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6081c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x609e0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60ba0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x782e8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x78490]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5fa34]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5fc00]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5fdb0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5ff7c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60134]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x602f8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x604a8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6066c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6081c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x609e0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60ba0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3c93c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5fa34]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5fc00]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5fdb0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x5ff7c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60134]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x602f8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x604a8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6066c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6081c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x609e0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60ba0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
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
(PRun [0x575cc]
(PGcKeep [(escale 4096 (EVar 109), ELit 0)]
(PRun [0x631ac]
(PExt 1 []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x57690]
(PDropRange (ELit 0x9b178) (ELit 0x12b0)
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x69fd4]
(PFresh 9 12 None
(PRun []
(PMmapIn
(startup_plan_tfib_tospin21)
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x519cc]
(PVia 1%nat JS_tfib_band 292%nat
(PCaseDisj (ELit 2147446784) (escale 4096 (EVar 275))
(startup_plan_tfib_band20_arm)
(startup_plan_tfib_band20_arm))
(startup_plan_tfib_band20)))))))))))
(startup_plan_tfib_tospin21))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_ranges : list (Z * nat) := [(0x2f9e4, 102995%nat)]%Z.
