(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Section s1_plan_sec.
(* [comment removed for export] *)
Variable js_2 : acs.
Variable js_11 : acs.

Definition s1_plan_brkfail1 : plan :=
  (* Low brk base, brk growth refused: mmap fallback for the meta area, then hole 0. *)
  PRun [] (
  PExt 5 [ELit 1; ELit 34359736319; ELit 4096] (
  PGhost (escale 4096 (EVar 455)) (ELit 4096) (
  PMmap (
  PRun [] (
  PMprotect (
  PRun [] (
  PMmap (
  PRun [] (
  PX XIMemset [] (
  PRun [] (
  PX XIMemset [] (
  PRun [0x822d0] (
  PBump 498 (
  PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (
  PHavocBrk 6303744 2153795584 (
  PFog 0 8192 (
  PFog 1 8192 (
  PUnvis (eaddz (escale 4096 (EVar 456)) 4096) (ELit 4096) (
  PUnvis (escale 4096 (EVar 457)) (ELit 4096) (
  PGhost (escale 4096 (EVar 5)) (ELit 8192) (
  PGhost (escale 4096 (EVar 455)) (ELit 4096) (
  PGhost (eaddz (escale 4096 (EVar 456)) 4096) (ELit 4096) (
  PGhost (escale 4096 (EVar 457)) (ELit 4096) (
  PFact (KRange (EVar 456) 1 34359736319) (
  PHandoff 0))))))))))))))))))))))))).

Definition s1_plan_brkblocked2 : plan :=
  (* High brk base, growth blocked by the shadow: mmap fallback, then hole 1. *)
  PRun [] (
  PExt 5 [ELit 1; ELit 34359736319; ELit 4096] (
  PGhost (escale 4096 (EVar 455)) (ELit 4096) (
  PMmap (
  PRun [] (
  PMprotect (
  PRun [] (
  PMmap (
  PRun [] (
  PX XIMemset [] (
  PRun [] (
  PX XIMemset [] (
  PRun [0x822d0] (
  PBump 498 (
  PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (
  PHavocBrk 6303744 2153795584 (
  PFog 0 8192 (
  PFog 1 8192 (
  PUnvis (eaddz (escale 4096 (EVar 456)) 4096) (ELit 4096) (
  PUnvis (escale 4096 (EVar 457)) (ELit 4096) (
  PGhost (escale 4096 (EVar 455)) (ELit 4096) (
  PGhost (eaddz (escale 4096 (EVar 456)) 4096) (ELit 4096) (
  PGhost (escale 4096 (EVar 457)) (ELit 4096) (
  PFact (KRange (EVar 456) 1 34359736319) (
  PHandoff 1)))))))))))))))))))))))).

Definition s1_plan_tail3 : plan :=
  (* From the brk growth request to the two handoff states. *)
  PSplit (EVar 5) 524277
    (PBrk2 s1_plan_brkfail1
       (PRun [] (
        PMmapIn (
        PRun [] (
        PMmap (
        PExt 5 [ELit 1; ELit 34359736319; ELit 8192] (
        PExt 5 [ELit 1; ELit 34359736319; ELit 4096] (
        PGhost (escale 4096 (EVar 455)) (ELit 4096) (
        PGhost (eaddz (escale 4096 (EVar 456)) 4096) (ELit 4096) (
        PGhost (escale 4096 (EVar 457)) (ELit 4096) (
        PRun [] (
        PX XIMemset [] (
        PRun [] (
        PX XIMemset [] (
        PRun [0x822d0] (
        PBump 498 (
        PHavoc [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (
        PHavocBrk 6303744 2153795584 (
        PFog 0 8192 (
        PFog 1 8192 (
        PUnvis (escale 4096 (EVar 5)) (ELit 8192) (
        PUnvis (escale 4096 (EVar 455)) (ELit 4096) (
        PGhost (eaddz (escale 4096 (EVar 456)) 4096) (ELit 4096) (
        PGhost (escale 4096 (EVar 457)) (ELit 4096) (
        PHandoff 0)))))))))))))))))))))))))
    (PSys YBrk s1_plan_brkblocked2).

Definition s1_plan_s2A4 : plan :=
  PRun [0x6dbcc] (* [comment removed for export] *)
  (PFresh 10 12 (Some (e_psp0)) (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PBump 423 (* [comment removed for export] *)
  (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 374))) 3935) 0 4095) (* [comment removed for export] *)
  (PFact (KRange (EVar 374) 0 1) (* [comment removed for export] *)
  (PHavoc [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PMerge 2) (* [comment removed for export] *)))))))))).

Definition s1_plan_arm11_5 : plan :=
  PExt 3 [escale 4096 (EVar 246); ELit 65536; ELit 4295491576] (* [comment removed for export] *)
  (PRun [] (* [comment removed for export] *)
  (PX XMemset [] (* [comment removed for export] *)
  (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PMerge 11) (* [comment removed for export] *)))).

Definition s1_plan : plan :=
  (* The whole S1 plan, joining at js_11 and js_2. *)
  PRun [] (
  PX XIMemset [] (
  PRun [] (
  PX XEnvScan [] (
  PRun [] (
  PX XPnScan [] (
  PRun [] (
  PX XIMemcpy [] (
  PRun [] (
  PSys YSetTid (
  PRun [] (
  PX XIMemcpy [] (
  PRun [] (
  PExt 1 [ELit 6296976; ELit 8] (
  PRun [] (
  PX XMaxVA [] (
  PRun [] (
  PMmap (
  PRun [] (
  PMmap (
  PRun [] (
  PMmap (
  PRun [] (
  PBump 95 (
  PMmap (
  PRun [] (
  PX XIMemset [] (
  PRun [] (
  PX XIMemcpy [] (
  PRun [] (
  PX XIMemcpy [] (
  PRun [] (
  PX XIMemcpy [] (
  PRun [] (
  PX XIMemcpy [] (
  PRun [] (
  PX XIMemset [] (
  PRun [] (
  PX XIMemcpy [] (
  PRun [] (
  PX XIMemcpy [] (
  PRun [] (
  PX XMaxVA [] (
  PRun [] (
  PMmap (
  PRun [] (
  PMmap (
  PRun [0x6d698] (
  PFresh 9 12 None (
  PRun [] (
  PMmapIn (
  PRun [] (
  PExt 3 [escale 4096 (EVar 226); ELit 137439023104; ELit 4295491576] (
  PRun [] (
  PX XMemset [] (
  PRun [] (
  PMmap (
  PRun [] (
  PMmap (
  PRun [] (
  PMmap (
  PRun [] (
  PDropRange (escale 4096 (EVar 95)) (ELit 65536) (
  PVia 11 js_11 247
    (PCase2 (EVar 246) 524263
       (PRun [] (PX XMemset [] (PMerge 11)))
       s1_plan_arm11_5)
    (PRun [] (
     PMmap (
     PRun [] (
     PX XIMemcpy [] (
     PRun [] (
     PX XIMemcpy [] (
     PRun [] (
     PX XMemIsZero [] (
     PRun [] (
     PX XMemset [] (
     PRun [] (
     PMmap (
     PRun [] (
     PMmap (
     PRun [] (
     PX XIMemcpy [] (
     PRun [] (
     PX XIMemcpy [] (
     PRun [] (
     PSys YMunmap (
     PVia 2 js_2 375
       (PSplit (EVar 6) 10 s1_plan_s2A4 s1_plan_s2A4)
       (PRun [] (
        PMmap (
        PRun [] (
        PExt 4 [ELit 15] (
        PRun [] (
        PX XMemcpy [] (
        PRun [] (
        PSys YBrk (
        PRun [] (
        PSplit (EVar 10) 0 s1_plan_tail3
          (PSplit (EVar 10) 6 s1_plan_tail3 s1_plan_tail3))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

End s1_plan_sec.
(* [comment removed for export] *)
Definition s1_plan_ranges : list (Z * nat) := [(0x31788, 303%nat); (0x33c98, 423%nat); (0x34ea8, 101%nat); (0x38538, 83%nat); (0x38af0, 90%nat); (0x3d768, 78%nat); (0x3df2c, 44%nat); (0x3e39c, 1008%nat); (0x422fc, 43%nat); (0x42fd8, 33%nat); (0x47840, 63%nat); (0x48924, 113%nat); (0x49818, 6654%nat); (0x524f0, 119%nat); (0x52b0c, 34%nat); (0x531f0, 319%nat); (0x53ad0, 53%nat); (0x53cf8, 119%nat); (0x545ac, 33%nat); (0x5502c, 387%nat); (0x559d8, 137%nat); (0x5613c, 173%nat); (0x59f5c, 38%nat); (0x5a6f4, 57%nat); (0x5abb8, 218%nat); (0x5b0d8, 85%nat); (0x5b348, 73%nat); (0x5b6b0, 206%nat); (0x5bb64, 68%nat); (0x5c838, 46%nat); (0x5cb18, 63%nat); (0x5d0d0, 227%nat); (0x5d66c, 754%nat); (0x5f248, 179%nat); (0x5fa2c, 155%nat); (0x61228, 35%nat); (0x618cc, 58%nat); (0x61b88, 68%nat); (0x61fdc, 51%nat); (0x622ec, 163%nat); (0x62b28, 121%nat); (0x62fd4, 1234%nat); (0x64750, 370%nat); (0x64e2c, 72%nat); (0x6516c, 172%nat); (0x655a0, 165%nat); (0x659c8, 46%nat); (0x65cb0, 53%nat); (0x667fc, 104%nat); (0x66c30, 55%nat); (0x66e54, 34%nat); (0x670a8, 158%nat); (0x676f4, 99%nat); (0x67d94, 126%nat); (0x68558, 35%nat); (0x6a154, 64%nat); (0x6a390, 218%nat); (0x6acb0, 300%nat); (0x6b31c, 345%nat); (0x6c0f8, 281%nat); (0x6ccd8, 54%nat); (0x6cee4, 35%nat); (0x6d600, 65%nat); (0x6dafc, 107%nat); (0x6dde4, 64%nat); (0x6e058, 180%nat); (0x6e68c, 33%nat); (0x6e954, 146%nat); (0x6eeac, 92%nat); (0x6f124, 102%nat); (0x6f838, 74%nat); (0x6fa84, 36%nat); (0x7128c, 49%nat); (0x7b7b4, 293%nat); (0x7be98, 71%nat); (0x7e66c, 35%nat); (0x815cc, 201%nat); (0x82284, 36%nat); (0x91c78, 621%nat); (0x927a8, 81%nat); (0x92c18, 151%nat); (0x934f4, 33%nat); (0x93bac, 1071%nat); (0x972c4, 109%nat); (0x9e88c, 129%nat); (0x9ec4c, 111%nat); (0x9f15c, 35%nat); (0x9f354, 163%nat); (0xa0534, 39%nat); (0xa08dc, 85%nat); (0xa0c54, 187%nat); (0xa14f0, 52%nat)]%Z.
