(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the start-up plan of libreac/fuzz_decode: the donor A/AB05.v at origin/ossv/recipes c8557374ad2e relocated onto fuzz_decode.asan (every PRun/PDiamond pc and PExt/PDropRange address by the binmatch identical-function and data-object map), startup_plan_tfib_ranges recomputed by tools/startup/itabranges.py (14 ranges, 68190 words), and the tail measured by tools/startup/plantail.py probef on this image *)
(* Read from: fuzz_decode.asan (libreac/fuzz_decode asan) sha256 5973b76807d8d2e14b82dc6afde70a2c882923658406aeca43681719cb4e8036; unstripped twin sha256 4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2 *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK0c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK09 YA01 YA0c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB03.
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
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 14  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 15  ))))))))))))))))))))))))))))))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 12  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 13  ))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 10  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 11  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 8  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 9  ))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_tail2 : plan :=
PRun [0x6bee0]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x51678]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x516c0]
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
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 6  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 7  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 4  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 5  ))))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 2  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 3  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 0  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 1  ))))))))))))))))))))))))))))))))))))
(PExt 64 [eadd (escale 4096 (EVar 5)) (ELit 4096)]
(PUnvis (escale 4096 (EVar 5)) (ELit 4096)
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 42  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 43  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 40  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 41  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
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
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 30  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 31  ))))))))))))))))))))))))))))))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 28  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 29  ))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 26  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 27  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 24  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 25  ))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_tail5 : plan :=
PRun [0x6bee0]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x51678]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x516c0]
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
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 22  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 23  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 20  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 21  ))))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 18  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 19  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 16  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 17  ))))))))))))))))))))))))))))))))))))
(PExt 64 [eadd (escale 4096 (EVar 5)) (ELit 4096)]
(PUnvis (escale 4096 (EVar 5)) (ELit 4096)
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 46  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 47  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 44  )))))))))))))))))))))))))))
(PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 45  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_s2B6 : plan :=
PBump 391
(startup_plan_tfib_tail5).
Definition startup_plan_tfib_rcase7 : plan :=
PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 32  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase8 : plan :=
PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 33  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase9 : plan :=
PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 34  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase10 : plan :=
PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 35  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase11 : plan :=
PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 48  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase12 : plan :=
PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 49  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase13 : plan :=
PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 36  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase14 : plan :=
PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 37  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase15 : plan :=
PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 38  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase16 : plan :=
PRun [0x3e1c8]
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
(PMmap
(PRun []
(PSpin  ))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun [0x7fbc4]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 39  )))))))))))))))))))))))))).
Definition startup_plan_tfib_brkfail17 : plan :=
PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
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
(PRun [0x72abc]
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
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase14)
(startup_plan_tfib_rcase14))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase13)
(startup_plan_tfib_rcase13))))))))))))).
Definition startup_plan_tfib_tail18 : plan :=
PRun [0x6bee0]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x51678]
(PExt 2 [ELit 15; ELit 16]
(PRun [0x516c0]
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
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase10)
(startup_plan_tfib_rcase10))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
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
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase8)
(startup_plan_tfib_rcase8))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
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
(PRun [0x72abc]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase12)
(startup_plan_tfib_rcase12))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [0x72abc]
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
(PRun [0x66cd8]
(PFresh 21 0 None
(PRun [0x66cd8]
(PFresh 21 0 None
(PRun [0x66cd8]
(PFresh 21 0 None
(PRun [0x66cd8]
(PFresh 21 0 None
(PRun [0x66cd8]
(PFresh 21 0 None
(PRun [0x66cd8]
(PFresh 21 0 None
(PRun [0x66cd8]
(PFresh 21 0 None
(PRun [0x66cd8]
(PFresh 21 0 None
(PRun [0x66cd8]
(PFresh 21 0 None
(PRun [0x66cd8]
(PFresh 21 0 None
(PCase2 (EVar 281) 15
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun []
(PSpin  ))))))))))))))))))))))
(PRun [0x66cd8]
(PFresh 21 0 None
(PCase2 (EVar 282) 15
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun []
(PSpin  ))))))))))))))))))))))))
(PRun [0x66cd8]
(PFresh 21 0 None
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
(PRun [0x66e68]
(PDiamond 0x66e40 [16]%nat
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
(PRun [0x8852c]
(PExt 0 [ELit 0x5f3d98; ELit 8]
(PRun [0x64b84]
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
(PRun [0x63968]
(PX XIStrncpy []
(PRun [0x63968]
(PX XIStrncpy []
(PRun [0x58e8c]
(PDropRange (ELit 0x130880) (ELit 0xfff) (PDropRange (ELit 0x131880) (ELit 0xfff)
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
(PRun [0x3cd58]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3cf14]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3d0c0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3d288]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3d434]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6140c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x615d8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61788]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61954]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61b0c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61cd0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61e80]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62044]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x621f4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x623b8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62578]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x79cc0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x79e68]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6140c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x615d8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61788]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61954]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61b0c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61cd0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61e80]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62044]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x621f4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x623b8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62578]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x3d5d8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x6140c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x615d8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61788]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61954]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61b0c]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61cd0]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x61e80]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62044]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x621f4]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x623b8]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [0x62578]
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
(PRun [0x58e90]
(PGcKeep [(escale 4096 (EVar 109), ELit 0)]
(PRun [0x64b84]
(PExt 1 []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x58f54]
(PDropRange (ELit 0x9e6b8) (ELit 0x12b0)
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [0x6b9ac]
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
(PRun [0x53040]
(PVia 1%nat JS_tfib_band 292%nat
(PCaseDisj (ELit 2147446784) (escale 4096 (EVar 275))
(startup_plan_tfib_band20_arm)
(startup_plan_tfib_band20_arm))
(startup_plan_tfib_band20)))))))))))
(startup_plan_tfib_tospin21))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_ranges : list (Z * nat) := [(0x30008, 857%nat); (0x31ddc, 2076%nat); (0x35ddc, 2076%nat); (0x3bddc, 6060%nat); (0x45c1c, 8854%nat); (0x50604, 4267%nat); (0x57a90, 25697%nat); (0x71ba4, 2076%nat); (0x78ba4, 2076%nat); (0x7bba4, 1052%nat); (0x7eba4, 2510%nat); (0x86fe0, 4269%nat); (0x8bfe0, 2051%nat); (0x91b68, 4269%nat)]%Z.
