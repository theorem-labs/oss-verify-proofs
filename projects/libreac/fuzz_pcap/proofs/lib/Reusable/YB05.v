(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Provenance, MEASURED: the relocated start-up plan with the MEASURED tail -- the donor's four PX XMemset pairs plus the one more that plantail f8aa639d5cc7 (a Theorem Labs tool at 3b0bd0f3826) measured, present in all 50 tails (pass2-ubsan-p.md (sha256 cee11748cd73; internal record), delivered as YB05.v (sha256 55322bdda02d; internal record)); the 2026-10-29 re-run of regen.sh (sha256 a5e9208eec8d; internal record) with that version reproduces this file BYTE-EQUAL (probe: 1 missing pair before main; `insert --nodes XMemset --count 1`: 50 tails got 1 node each).  Nothing is filled; codeptr c0ce606ed1fa (startup-set 2026-10-29): 0 findings / 0 stale on every file, with 20 declarations carrying their measured reasons in declarations-20.sh (sha256 880286aef98b; internal record); AB1m / YB1m UNMEASURED (no address literal; BFUEL is %nat); logs final20.txt (sha256 b2b70d12a063; internal record) / final20.no-b1m.txt (sha256 be056cbfc3b7; internal record) (a Theorem Labs lane); an independent run by a second lane agrees *)
(* gated: a Theorem Labs lane PASS A+B at c061542723f / 731386609e0 *)
(* Before commit 5098883da0b3 (2026-10-29) brought YF0l and YB13 into this tree, the asan-ubsan files built ONLY in a union that also included a working branch 27d40cfe97f76cd158308a2aef684e7e509db360: lib/Reusable/YF0m.v Requires YF0l and lib/Reusable/YD2i.v Requires YB13, both of them core files of that branch. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK0c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK09 YA01 YA0c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB03.
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 14  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 15  ))))))))))))))))))))))))))))))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 12  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 13  ))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 10  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 11  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 8  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 9  ))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_tail2 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer26GetThreadStackTopAndBottomEbPmS0_ + 0x90)%Z)]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [(symaddr (Symbols.AsanUbsan.s___interceptor_memcpy + 0x9c)%Z)]
(PExt 2 [ELit 15; ELit 16]
(PRun [(symaddr (Symbols.AsanUbsan.s___interceptor_memcpy + 0xe4)%Z)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 6  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 7  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 4  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 5  ))))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 2  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 3  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 0  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 42  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 43  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 40  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 30  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 31  ))))))))))))))))))))))))))))))))))
(PRun []
(PMprotect
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 28  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 29  ))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 26  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 27  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 24  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 25  ))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_tail5 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer26GetThreadStackTopAndBottomEbPmS0_ + 0x90)%Z)]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [(symaddr (Symbols.AsanUbsan.s___interceptor_memcpy + 0x9c)%Z)]
(PExt 2 [ELit 15; ELit 16]
(PRun [(symaddr (Symbols.AsanUbsan.s___interceptor_memcpy + 0xe4)%Z)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 22  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 23  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 20  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 21  ))))))))))))))))))))))))))))))))))))
(PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 18  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 19  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 16  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 46  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 47  ))))))))))))))))))))))))))))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 44  )))))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 45  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_s2B6 : plan :=
PBump 391
(startup_plan_tfib_tail5).
Definition startup_plan_tfib_rcase7 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 32  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase8 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 33  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase9 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 34  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase10 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 35  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase11 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 48  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase12 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 49  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase13 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 36  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase14 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 37  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase15 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 38  )))))))))))))))))))))))))).
Definition startup_plan_tfib_rcase16 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s___asan_register_globals + 0x130)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s_main)]
(PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
(PHandoff 39  )))))))))))))))))))))))))).
Definition startup_plan_tfib_brkfail17 : plan :=
PRun []
(PMmap
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase14)
(startup_plan_tfib_rcase14))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase13)
(startup_plan_tfib_rcase13))))))))))))).
Definition startup_plan_tfib_tail18 : plan :=
PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer26GetThreadStackTopAndBottomEbPmS0_ + 0x90)%Z)]
(PFresh 10 12 (Some (escale 32768 (EVar 0)))
(PRun []
(PX XMemset []
(PRun []
(PX XMemset []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [(symaddr (Symbols.AsanUbsan.s___interceptor_memcpy + 0x9c)%Z)]
(PExt 2 [ELit 15; ELit 16]
(PRun [(symaddr (Symbols.AsanUbsan.s___interceptor_memcpy + 0xe4)%Z)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase10)
(startup_plan_tfib_rcase10))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase8)
(startup_plan_tfib_rcase8))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
(PBump 500
(PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 391))) 3935) 4030
(startup_plan_tfib_rcase12)
(startup_plan_tfib_rcase12))))))))
(PRun []
(PX XIMemset []
(PRun []
(PX XIMemset []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj + 0xac)%Z)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PCase2 (EVar 281) 15
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun []
(PSpin  ))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PCase2 (EVar 282) 15
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun []
(PSpin  ))))))))))))))))))))))))
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0xdc)%Z)]
(PFresh 21 0 None
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x26c)%Z)]
(PDiamond (symaddr (Symbols.AsanUbsan.s__ZN11__sanitizerL12AppendNumberEPPcPKcyhhbbb + 0x244)%Z) [16]%nat
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
(PRun [(symaddr (Symbols.AsanUbsan.s___init_ssp + 0x48)%Z)]
(PExt 0 [ELit (symaddr Symbols.AsanUbsan.s___stack_chk_guard); ELit 8]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer24GetMaxUserVirtualAddressEv + 0x34)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s__ZN11__sanitizer16internal_strncpyEPcPKcm)]
(PX XIStrncpy []
(PRun [(symaddr Symbols.AsanUbsan.s__ZN11__sanitizer16internal_strncpyEPcPKcm)]
(PX XIStrncpy []
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN6__asanL16AsanInitInternalEv + 0x94)%Z)]
(PDropRange (ELit (symaddr Symbols.AsanUbsan.s__ZN11__sanitizerL22process_name_cache_strE)) (ELit 0xfff) (PDropRange (ELit (symaddr Symbols.AsanUbsan.s__ZN11__sanitizerL21binary_name_cache_strE)) (ELit 0xfff)
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN6__asan15InitializeFlagsEv + 0x3f8)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN6__asan15InitializeFlagsEv + 0x5b4)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN6__asan15InitializeFlagsEv + 0x760)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN6__asan15InitializeFlagsEv + 0x928)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN6__asan15InitializeFlagsEv + 0xad4)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xe4)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x2b0)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x460)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x62c)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x7e4)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x9a8)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xb58)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xd1c)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xecc)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x1090)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x1250)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN6__lsan17RegisterLsanFlagsEPN11__sanitizer10FlagParserEPNS_5FlagsE + 0x174)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN6__lsan17RegisterLsanFlagsEPN11__sanitizer10FlagParserEPNS_5FlagsE + 0x31c)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xe4)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x2b0)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x460)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x62c)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x7e4)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x9a8)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xb58)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xd1c)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xecc)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x1090)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x1250)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN6__asan15InitializeFlagsEv + 0xc78)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xe4)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x2b0)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x460)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x62c)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x7e4)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x9a8)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xb58)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xd1c)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0xecc)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x1090)%Z)]
(PGcKeep [((escale 4096 (EVar 109)), ELit 1536); (EAlu Instr.ALU_ADD (escale 4096 (EVar 109)) (ELit 5808), ELit 16)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE + 0x1250)%Z)]
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
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN6__asanL16AsanInitInternalEv + 0x98)%Z)]
(PGcKeep [(escale 4096 (EVar 109), ELit 0)]
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer24GetMaxUserVirtualAddressEv + 0x34)%Z)]
(PExt 1 []
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN6__asanL16AsanInitInternalEv + 0x15c)%Z)]
(PDropRange (ELit (symaddr Symbols.AsanUbsan.s__ZL11ioctl_table)) (ELit 0x12b0)
(PRun []
(PMmap
(PRun []
(PSpin  ))
(PRun [(symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer20ReservedAddressRange11InitAlignedEmmPKc + 0x58)%Z)]
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
(PRun [(symaddr Symbols.AsanUbsan.s__ZN6__asan12PoisonShadowEmmh)]
(PVia 1%nat JS_tfib_band 292%nat
(PCaseDisj (ELit 2147446784) (escale 4096 (EVar 275))
(startup_plan_tfib_band20_arm)
(startup_plan_tfib_band20_arm))
(startup_plan_tfib_band20)))))))))))
(startup_plan_tfib_tospin21))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition startup_plan_tfib_ranges : list (Z * nat) := [((symaddr Symbols.AsanUbsan.s__start), (symwords Symbols.AsanUbsan.s__start (Symbols.AsanUbsan.s__ZN6__asan28AsanThreadLocalMallocStorage10CommitBackEv + 0x194)%Z)); ((symaddr (Symbols.AsanUbsan.s__ZN6__lsan13LockAllocatorEv + 0x128)%Z), (symwords (Symbols.AsanUbsan.s__ZN6__lsan13LockAllocatorEv + 0x128)%Z (Symbols.AsanUbsan.s__ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17ReturnToAllocatorEPNS_12MemoryMapperIS5_EEPNS_14AllocatorStatsEmPKjm + 0x168)%Z)); ((symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x344)%Z), (symwords (Symbols.AsanUbsan.s__ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm + 0x344)%Z (Symbols.AsanUbsan.s__ZNK6__asan22HeapAddressDescription5PrintEv + 0xfc)%Z)); ((symaddr (Symbols.AsanUbsan.s__ZN6__asan12ErrorGeneric5PrintEv + 0xcac)%Z), (symwords (Symbols.AsanUbsan.s__ZN6__asan12ErrorGeneric5PrintEv + 0xcac)%Z (Symbols.AsanUbsan.s____interceptor_strcmp + 0x15c)%Z)); ((symaddr (Symbols.AsanUbsan.s___interceptor_pthread_attr_getstack + 0x150)%Z), (symwords (Symbols.AsanUbsan.s___interceptor_pthread_attr_getstack + 0x150)%Z (Symbols.AsanUbsan.s__ZL16ioctl_table_fillv + 0x6870)%Z)); ((symaddr (Symbols.AsanUbsan.s__ZL16ioctl_table_fillv + 0x8830)%Z), (symwords (Symbols.AsanUbsan.s__ZL16ioctl_table_fillv + 0x8830)%Z (Symbols.AsanUbsan.s__ZN6__asan9Decorator10ShadowByteEh + 0xa0)%Z)); ((symaddr (Symbols.AsanUbsan.s___asan_set_error_report_callback + 0x80)%Z), (symwords (Symbols.AsanUbsan.s___asan_set_error_report_callback + 0x80)%Z (Symbols.AsanUbsan.s__ZN11__sanitizer24InternalMmapVectorNoCtorINS_6detail12DenseMapPairIPmS3_EELb0EE7ReallocEm + 0x44)%Z)); ((symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer8DenseMapINS_6detail12DenseMapPairIjmEEjNS_12DenseMapInfoIS3_EENS2_IS3_jEEE15allocateBucketsEj + 0x180)%Z), (symwords (Symbols.AsanUbsan.s__ZN11__sanitizer8DenseMapINS_6detail12DenseMapPairIjmEEjNS_12DenseMapInfoIS3_EENS2_IS3_jEEE15allocateBucketsEj + 0x180)%Z (Symbols.AsanUbsan.s__ZN11__sanitizer26FormattedStackTracePrinter10RenderDataEPNS_20InternalScopedStringEPKcPKNS_8DataInfoES4_ + 0x6c)%Z)); ((symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer21ScopedErrorReportLock4LockEv + 0xf8)%Z), (symwords (Symbols.AsanUbsan.s__ZN11__sanitizer21ScopedErrorReportLock4LockEv + 0xf8)%Z (Symbols.AsanUbsan.s__ZN6__lsanL13CheckForLeaksEv + 0x4)%Z)); ((symaddr (Symbols.AsanUbsan.s__ZN6__lsan10LeakReport14ReportTopLeaksEm + 0x5c)%Z), (symwords (Symbols.AsanUbsan.s__ZN6__lsan10LeakReport14ReportTopLeaksEm + 0x5c)%Z (Symbols.AsanUbsan.s__ZN6__lsanL21CheckForLeaksCallbackERKN11__sanitizer20SuspendedThreadsListEPv + 0x114)%Z)); ((symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer12SortAndDedupINS_18InternalMmapVectorIjEENS_11CompareLessIjEEEEvRT_T0_ + 0x104)%Z), (symwords (Symbols.AsanUbsan.s__ZN11__sanitizer12SortAndDedupINS_18InternalMmapVectorIjEENS_11CompareLessIjEEEEvRT_T0_ + 0x104)%Z (Symbols.AsanUbsan.s_pcap_source_open + 0x8)%Z)); ((symaddr (Symbols.AsanUbsan.s__ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE7findFDEERS1_mmmmPNS2_8FDE_InfoEPNS2_8CIE_InfoE + 0xec)%Z), (symwords (Symbols.AsanUbsan.s__ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE7findFDEERS1_mmmmPNS2_8FDE_InfoEPNS2_8CIE_InfoE + 0xec)%Z (Symbols.AsanUbsan.s___multf3 + 0x188)%Z)); ((symaddr (Symbols.AsanUbsan.s___divtf3 + 0xe4)%Z), (symwords (Symbols.AsanUbsan.s___divtf3 + 0xe4)%Z (Symbols.AsanUbsan.s___stdio_write + 0xe0)%Z)); ((symaddr (Symbols.AsanUbsan.s_sn_write + 0xc4)%Z), (symwords (Symbols.AsanUbsan.s_sn_write + 0xc4)%Z (Symbols.AsanUbsan.s_do_tzset + 0x350)%Z))]%Z.
