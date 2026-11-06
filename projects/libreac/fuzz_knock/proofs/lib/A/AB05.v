(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the plan is fuzz_knock.asan's own: cgif's start-up plan relocated to this image, its itab ranges from itabranges.py --rule text (the .text whole), the registration arm and its loop dropped by plantail.py drop-registration / drop-nodes (0 ASan globals), and ten start-up cells pinned as literals by plantail.py pin-cells. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK0c.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK09 YA01 YA0c.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AB03.
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
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 14))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 15))))))))))  ))))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 12))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 13))))))))))  ))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 10))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 11))))))))))  ))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 8))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 9))))))))))  ))))))))))))).
Definition startup_plan_tfib_tail2 : plan :=
PRun [0x6ad4c]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x50a84]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x50acc]
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
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 6))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 7))))))))))  ))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 4))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 5))))))))))  ))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 2))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 3))))))))))  ))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 0))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 1))))))))))  ))))))))))
(PExt 64 [eadd (escale 4096 (EVar 5)) (ELit 4096)]
(PUnvis (escale 4096 (EVar 5)) (ELit 4096)
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 42))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 43))))))))))  ))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 40))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 41))))))))))  ))))))))))))))))))))))))))))))).
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
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 30))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 31))))))))))  ))))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 28))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 29))))))))))  ))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 26))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 27))))))))))  ))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 24))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 25))))))))))  ))))))))))))).
Definition startup_plan_tfib_tail5 : plan :=
PRun [0x6ad4c]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x50a84]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x50acc]
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
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 22))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 23))))))))))  ))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 20))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 21))))))))))  ))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 18))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 19))))))))))  ))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 16))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 17))))))))))  ))))))))))
(PExt 64 [eadd (escale 4096 (EVar 5)) (ELit 4096)]
(PUnvis (escale 4096 (EVar 5)) (ELit 4096)
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 46))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 47))))))))))  ))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 44))))))))))  )))
(PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 45))))))))))  ))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_s2B6 : plan :=
PBump 391
(startup_plan_tfib_tail5).
Definition startup_plan_tfib_rcase7 : plan :=
PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 32))))))))))  )).
Definition startup_plan_tfib_rcase8 : plan :=
PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 33))))))))))  )).
Definition startup_plan_tfib_rcase9 : plan :=
PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 34))))))))))  )).
Definition startup_plan_tfib_rcase10 : plan :=
PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 35))))))))))  )).
Definition startup_plan_tfib_rcase11 : plan :=
PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 48))))))))))  )).
Definition startup_plan_tfib_rcase12 : plan :=
PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 49))))))))))  )).
Definition startup_plan_tfib_rcase13 : plan :=
PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 36))))))))))  )).
Definition startup_plan_tfib_rcase14 : plan :=
PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 37))))))))))  )).
Definition startup_plan_tfib_rcase15 : plan :=
PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 38))))))))))  )).
Definition startup_plan_tfib_rcase16 : plan :=
PRun [0x7ea30]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PJoin (ELit 0) 0x9ae80 8 (PJoin (ELit 0) 0x9bd48 8 (PJoin (ELit 0) 0x9bd60 8 (PJoin (ELit 0) 0x9bd70 8 (PJoin (ELit 0) 0x9bd90 8 (PJoin (ELit 0) 0x9bd98 8 (PJoin (ELit 0) 0x9bda8 8 (PJoin (ELit 0) 0x9af00 8 (PJoin (ELit 0) 0x9af10 8 (PJoin (ELit 0) 0x9bd00 8 (PHandoff 39))))))))))  )).
Definition startup_plan_tfib_brkfail17 : plan :=
PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase16)
(startup_plan_tfib_rcase16))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase15)
(startup_plan_tfib_rcase15))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase14)
(startup_plan_tfib_rcase14))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase13)
(startup_plan_tfib_rcase13))))))))))).
Definition startup_plan_tfib_tail18 : plan :=
PRun [0x6ad4c]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x50a84]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x50acc]
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
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase10)
(startup_plan_tfib_rcase10))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase9)
(startup_plan_tfib_rcase9))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase8)
(startup_plan_tfib_rcase8))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase7)
(startup_plan_tfib_rcase7))))))))
(PExt 64 [eadd (escale 4096 (EVar 5)) (ELit 4096)]
(PUnvis (escale 4096 (EVar 5)) (ELit 4096)
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase12)
(startup_plan_tfib_rcase12))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase11)
(startup_plan_tfib_rcase11))))))))))))))))))))))))))))).
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
(PRun [0x65b44]
(PFresh 21 0 None
(PRun [0x65b44]
(PFresh 21 0 None
(PRun [0x65b44]
(PFresh 21 0 None
(PRun [0x65b44]
(PFresh 21 0 None
(PRun [0x65b44]
(PFresh 21 0 None
(PRun [0x65b44]
(PFresh 21 0 None
(PRun [0x65b44]
(PFresh 21 0 None
(PRun [0x65b44]
(PFresh 21 0 None
(PRun [0x65b44]
(PFresh 21 0 None
(PRun [0x65b44]
(PFresh 21 0 None
(PCase2 (EVar 281) 15
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun []
(PSpin  ))))))))))))))))))))))
(PRun [0x65b44]
(PFresh 21 0 None
(PCase2 (EVar 282) 15
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun []
(PSpin  ))))))))))))))))))))))))
(PRun [0x65b44]
(PFresh 21 0 None
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
(PRun [0x65cd4]
(PDiamond 0x65cac [16]%nat
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
(PRun [0x85dc8]
(PExt 0 [ELit 0x5f1510; ELit 8]
(PRun [0x639f0]
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
(PRun [0x627d4]
(PX XIStrncpy []
(PRun [0x627d4]
(PX XIStrncpy []
(PRun [0x57e0c]
(PDropRange (ELit 0x12e000) (ELit 0xfff) (PDropRange (ELit 0x12f000) (ELit 0xfff)
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
(PRun [0x3c728]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3c8e4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3ca90]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3cc58]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3ce04]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60278]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60444]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x605f4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x607c0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60978]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60b3c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60cec]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60eb0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61060]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61224]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x613e4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x78b2c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x78cd4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60278]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60444]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x605f4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x607c0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60978]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60b3c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60cec]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60eb0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61060]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61224]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x613e4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3cfa8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60278]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60444]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x605f4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x607c0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60978]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60b3c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60cec]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x60eb0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61060]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61224]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x613e4]
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
(PRun [0x57e10]
(PGcKeep [(escale 4096 (EVar 109), ELit 0)]
(PRun [0x639f0]
(PExt 1 []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x57ed4]
(PDropRange (ELit 0x9be38) (ELit 0x12b0)
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x6a818]
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
(PRun [0x52210]
(PVia 1%nat JS_tfib_band 292%nat
(PCaseDisj (ELit 2147446784) (escale 4096 (EVar 275))
(startup_plan_tfib_band20_arm)
(startup_plan_tfib_band20_arm))
(startup_plan_tfib_band20)))))))))))
(startup_plan_tfib_tospin21))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_ranges : list (Z * nat) := [(0x2fa9c, 103785%nat)]%Z.
