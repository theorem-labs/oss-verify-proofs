(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB05.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; startup_plan_tfib_ranges recomputed for fuzz_grant.asan's code, and each hand-off tail has ten more (PRun [] / PX XMemset) pairs, one per call into memset (0x95e30) that the poisoning of fuzz_grant's 13 registered globals makes before main (measured by a Theorem Labs lane's tools/startup/plantail.py probe). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK0c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK09 YA01 YA0c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AB03.
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
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 14  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 15  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 12  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 13  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 10  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 11  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 8  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 9  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_tail2 : plan :=
PRun [0x6c52c]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x52264]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x522ac]
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
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 6  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 7  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 4  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 5  ))))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 2  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 3  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 0  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 1  ))))))))))))))))))))))))))))))))))))))))))))))))))))))
(PExt 64 [eadd (escale 4096 (EVar 5)) (ELit 4096)]
(PUnvis (escale 4096 (EVar 5)) (ELit 4096)
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 42  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 43  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 40  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 41  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
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
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 30  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 31  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 28  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 29  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 26  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 27  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 24  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 25  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_tail5 : plan :=
PRun [0x6c52c]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x52264]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x522ac]
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
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 22  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 23  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 20  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 21  ))))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 18  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 19  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 16  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 17  ))))))))))))))))))))))))))))))))))))))))))))))))))))))
(PExt 64 [eadd (escale 4096 (EVar 5)) (ELit 4096)]
(PUnvis (escale 4096 (EVar 5)) (ELit 4096)
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 46  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 47  ))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 44  )))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 45  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_s2B6 : plan :=
PBump 391
(startup_plan_tfib_tail5).
Definition startup_plan_tfib_rcase7 : plan :=
PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 32  )))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase8 : plan :=
PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 33  )))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase9 : plan :=
PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 34  )))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase10 : plan :=
PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 35  )))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase11 : plan :=
PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 48  )))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase12 : plan :=
PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 49  )))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase13 : plan :=
PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 36  )))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase14 : plan :=
PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 37  )))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase15 : plan :=
PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 38  )))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase16 : plan :=
PRun [0x3edb4]
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
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x80210]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 39  )))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_brkfail17 : plan :=
PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
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
(PRun [0x73108]
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
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase14)
(startup_plan_tfib_rcase14))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase13)
(startup_plan_tfib_rcase13))))))))))))).
Definition startup_plan_tfib_tail18 : plan :=
PRun [0x6c52c]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x52264]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x522ac]
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
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase10)
(startup_plan_tfib_rcase10))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
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
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase8)
(startup_plan_tfib_rcase8))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
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
(PRun [0x73108]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase12)
(startup_plan_tfib_rcase12))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x73108]
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
(PRun [0x67324]
(PFresh 21 0 None
(PRun [0x67324]
(PFresh 21 0 None
(PRun [0x67324]
(PFresh 21 0 None
(PRun [0x67324]
(PFresh 21 0 None
(PRun [0x67324]
(PFresh 21 0 None
(PRun [0x67324]
(PFresh 21 0 None
(PRun [0x67324]
(PFresh 21 0 None
(PRun [0x67324]
(PFresh 21 0 None
(PRun [0x67324]
(PFresh 21 0 None
(PRun [0x67324]
(PFresh 21 0 None
(PCase2 (EVar 281) 15
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun []
(PSpin  ))))))))))))))))))))))
(PRun [0x67324]
(PFresh 21 0 None
(PCase2 (EVar 282) 15
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun []
(PSpin  ))))))))))))))))))))))))
(PRun [0x67324]
(PFresh 21 0 None
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
(PRun [0x674b4]
(PDiamond 0x6748c [16]%nat
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
(PRun [0x8bee8]
(PExt 0 [ELit 0x5f7b10; ELit 8]
(PRun [0x651d0]
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
(PRun [0x63fb4]
(PX XIStrncpy []
(PRun [0x63fb4]
(PX XIStrncpy []
(PRun [0x595ec]
(PDropRange (ELit 0x134600) (ELit 0xfff) (PDropRange (ELit 0x135600) (ELit 0xfff)
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
(PRun [0x3d944]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3db00]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3dcac]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3de74]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3e020]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61a58]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61c24]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61dd4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61fa0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62158]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6231c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x624cc]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62690]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62840]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62a04]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62bc4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x7a30c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x7a4b4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61a58]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61c24]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61dd4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61fa0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62158]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6231c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x624cc]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62690]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62840]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62a04]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62bc4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3e1c4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61a58]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61c24]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61dd4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61fa0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62158]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6231c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x624cc]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62690]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62840]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62a04]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62bc4]
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
(PRun [0x595f0]
(PGcKeep [(escale 4096 (EVar 109), ELit 0)]
(PRun [0x651d0]
(PExt 1 []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x596b4]
(PDropRange (ELit 0xa2438) (ELit 0x12b0)
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x6bff8]
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
(PRun [0x539f0]
(PVia 1%nat JS_tfib_band 292%nat
(PCaseDisj (ELit 2147446784) (escale 4096 (EVar 275))
(startup_plan_tfib_band20_arm)
(startup_plan_tfib_band20_arm))
(startup_plan_tfib_band20)))))))))))
(startup_plan_tfib_tospin21))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_ranges : list (Z * nat) := [(0x307dc, 857%nat); (0x324d0, 2076%nat); (0x364d0, 2076%nat); (0x3c4d0, 6378%nat); (0x46808, 8854%nat); (0x511f0, 4124%nat); (0x581f0, 25628%nat); (0x721f0, 2076%nat); (0x791f0, 2076%nat); (0x7c1f0, 1052%nat); (0x7f1f0, 4124%nat); (0x8a99c, 4269%nat); (0x8f99c, 2051%nat); (0x95524, 4269%nat)]%Z.
