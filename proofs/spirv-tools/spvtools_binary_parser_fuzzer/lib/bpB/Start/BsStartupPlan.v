(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BothPlan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsStartupFz.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup_plan_brkfail1 : plan :=
  PRun []
  (PMmap1
  (PRangeGaps 409 4096
  (PRun []
  (PMprotect1
  (PRun []
  (PMmap1
  (PRangeGaps 410 4096
  (PBump 411
  (PRun []
  (PX XIMemset []
  (PRun []
  (PX XIMemset []
  (PRun [0xdb2ec]
  (PCase2 (EVar 10) 5
  (PHandoff 102  )
  (PHandoff 103  ))))))))))))))).

Definition startup_plan_tail2 : plan :=
  PRun [0xd470c]
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap1
  (PRangeGaps 392 4096
  (PRun [0xb9818]
  (PRun [0xb9860]
  (PRun []
  (PX XMemcpy []
  (PRun []
  (PSys YBrk
  (PRun []
  (PBrk2
  (startup_plan_brkfail1)
  (PRangeGaps 5 4096
   (PRun []
   (PMmapIn1
   (PRun []
   (PMmap1
   (PRangeGaps 409 4096
   (PBump 411
   (PRun []
   (PX XIMemset []
   (PRun []
   (PX XIMemset []
   (PRun [0xdb2ec]
   (PCase2 (EVar 10) 5
   (PHandoff 100  )
   (PHandoff 101  ))))))))))))))))))))))))))))).

Definition startup_plan_s2A3 : plan :=
  PBump 360
  (startup_plan_tail2).

Definition startup_plan_brkfail4 : plan :=
  PRun []
  (PMmap1
  (PRangeGaps 409 4096
  (PRun []
  (PMprotect1
  (PRun []
  (PMmap1
  (PRangeGaps 410 4096
  (PBump 411
  (PRun []
  (PX XIMemset []
  (PRun []
  (PX XIMemset []
  (PRun [0xdb2ec]
  (PHandoff 105  )))))))))))))).

Definition startup_plan_tail5 : plan :=
  PRun [0xd470c]
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap1
  (PRangeGaps 392 4096
  (PRun [0xb9818]
  (PRun [0xb9860]
  (PRun []
  (PX XMemcpy []
  (PRun []
  (PSys YBrk
  (PRun []
  (PBrk2
  (startup_plan_brkfail4)
  (PRangeGaps 5 4096
   (PRun []
   (PMmapIn1
   (PRun []
   (PMmap1
   (PRangeGaps 409 4096
   (PBump 411
   (PRun []
   (PX XIMemset []
   (PRun []
   (PX XIMemset []
   (PRun [0xdb2ec]
   (PHandoff 104  )))))))))))))))))))))))))))).

Definition startup_plan_s2D6 : plan :=
  PBump 360
  (startup_plan_tail5).

Definition startup_plan_side7 : plan :=
  PRun []
  (PX XMemset []
  (PRun []
  (PHandoff 90  ))).

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
  (PX XIMemcpy []
  (PRun [0x165084]
  (PNameCell (ELit 0x6e5898) 8
  (PRun []
  (PX XSmear []
  (PRun []
  (PMmap1
  (PRun []
  (PMmap1
  (PRun []
  (PMmap1
  (PRun [0xcc17c]
  (PX XIStrncpy []
  (PRun [0xcc17c]
  (PX XIStrncpy []
  (PRun [0xc17b4]
  (PDropRange (ELit 0x220b00) (ELit 0xfff) (PDropRange (ELit 0x221b00) (ELit 0xfff)
  (PRun []
  (PMmap1
  (PRangeGaps 94 4096
  (PRun []
  (PX XIMemset []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PFrozen 79 fz_hulls_79 fz_wins_79 fz_cold_79
    [FRun false [0x9eb38]; FRun false [0x9ee68]; FRun false [0x9f1a8]; FRun false [0xc9c74]; FRun false [0xc9fbc]; FRun false [0xca30c]; FRun false [0xca64c]; FRun true [0xca98c]]
  (PFrozen 80 fz_hulls_80 fz_wins_80 fz_cold_80
    [FRun false [0xcaccc]; FRun false [0xe2654]; FRun false [0xc9c74]; FRun false [0xc9fbc]; FRun false [0xca30c]; FRun false [0xca64c]; FRun false [0xca98c]; FRun true [0xcaccc]]
  (PFrozen 81 fz_hulls_81 fz_wins_81 fz_cold_81
    [FRun false [0xc9c74]; FRun false [0xc9fbc]; FRun false [0xca30c]; FRun false [0xca64c]; FRun false [0xca98c]; FRun false [0xcaccc]; FRun true []]
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemset []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun [0xc17b8]
  (PDropRange (escale 4096 (EVar 94)) (ELit 0x10000)
  (PRun []
  (PX XSmear []
  (PRun []
  (PMmap1
  (PRangeGaps 223 4096
  (PFrozen 1 fz_hulls_1 fz_wins_1 fz_cold_1
    [FRun false [0xafa98]; FRun false [0xafe98]; FRun false [0xb0298]; FRun false [0xb0698]; FRun false [0xb0a98]; FRun false [0xb0e98]; FRun false [0xb1298]; FRun true [0xb1698]]
  (PFrozen 2 fz_hulls_2 fz_wins_2 fz_cold_2
    [FRun false [0xb1a98]; FRun false [0xb1e98]; FRun false [0xb2298]; FRun false [0xb2698]; FRun false [0xb2a98]; FRun false [0xb2e98]; FRun false [0xb3298]; FRun true [0xb3698]]
  (PFrozen 3 fz_hulls_3 fz_wins_3 fz_cold_3
    [FRun false [0xb3a98]; FRun false [0xb3e98]; FRun false [0xb4298]; FRun false [0xb4698]; FRun false [0xb4a98]; FRun false [0xb4e98]; FRun false [0xb5298]; FRun true [0xb5698]]
  (PFrozen 4 fz_hulls_4 fz_wins_4 fz_cold_4
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 5 fz_hulls_5 fz_wins_5 fz_cold_5
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 6 fz_hulls_6 fz_wins_6 fz_cold_6
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 7 fz_hulls_7 fz_wins_7 fz_cold_7
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 8 fz_hulls_8 fz_wins_8 fz_cold_8
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 9 fz_hulls_9 fz_wins_9 fz_cold_9
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 10 fz_hulls_10 fz_wins_10 fz_cold_10
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 11 fz_hulls_11 fz_wins_11 fz_cold_11
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 12 fz_hulls_12 fz_wins_12 fz_cold_12
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 13 fz_hulls_13 fz_wins_13 fz_cold_13
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 14 fz_hulls_14 fz_wins_14 fz_cold_14
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 15 fz_hulls_15 fz_wins_15 fz_cold_15
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 16 fz_hulls_16 fz_wins_16 fz_cold_16
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 17 fz_hulls_17 fz_wins_17 fz_cold_17
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 18 fz_hulls_18 fz_wins_18 fz_cold_18
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 19 fz_hulls_19 fz_wins_19 fz_cold_19
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 20 fz_hulls_20 fz_wins_20 fz_cold_20
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 21 fz_hulls_21 fz_wins_21 fz_cold_21
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 22 fz_hulls_22 fz_wins_22 fz_cold_22
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 23 fz_hulls_23 fz_wins_23 fz_cold_23
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 24 fz_hulls_24 fz_wins_24 fz_cold_24
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 25 fz_hulls_25 fz_wins_25 fz_cold_25
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 26 fz_hulls_26 fz_wins_26 fz_cold_26
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 27 fz_hulls_27 fz_wins_27 fz_cold_27
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 28 fz_hulls_28 fz_wins_28 fz_cold_28
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 29 fz_hulls_29 fz_wins_29 fz_cold_29
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 30 fz_hulls_30 fz_wins_30 fz_cold_30
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 31 fz_hulls_31 fz_wins_31 fz_cold_31
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 32 fz_hulls_32 fz_wins_32 fz_cold_32
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 33 fz_hulls_33 fz_wins_33 fz_cold_33
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 34 fz_hulls_34 fz_wins_34 fz_cold_34
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 35 fz_hulls_35 fz_wins_35 fz_cold_35
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 36 fz_hulls_36 fz_wins_36 fz_cold_36
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 37 fz_hulls_37 fz_wins_37 fz_cold_37
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 38 fz_hulls_38 fz_wins_38 fz_cold_38
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 39 fz_hulls_39 fz_wins_39 fz_cold_39
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 40 fz_hulls_40 fz_wins_40 fz_cold_40
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7f78]; FRun true [0xb7f78]]
  (PFrozen 41 fz_hulls_41 fz_wins_41 fz_cold_41
    [FRun false [0xb7f78]; FRun false [0xb7f78]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 42 fz_hulls_42 fz_wins_42 fz_cold_42
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 43 fz_hulls_43 fz_wins_43 fz_cold_43
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 44 fz_hulls_44 fz_wins_44 fz_cold_44
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 45 fz_hulls_45 fz_wins_45 fz_cold_45
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 46 fz_hulls_46 fz_wins_46 fz_cold_46
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 47 fz_hulls_47 fz_wins_47 fz_cold_47
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 48 fz_hulls_48 fz_wins_48 fz_cold_48
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 49 fz_hulls_49 fz_wins_49 fz_cold_49
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 50 fz_hulls_50 fz_wins_50 fz_cold_50
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 51 fz_hulls_51 fz_wins_51 fz_cold_51
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 52 fz_hulls_52 fz_wins_52 fz_cold_52
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 53 fz_hulls_53 fz_wins_53 fz_cold_53
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 54 fz_hulls_54 fz_wins_54 fz_cold_54
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 55 fz_hulls_55 fz_wins_55 fz_cold_55
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 56 fz_hulls_56 fz_wins_56 fz_cold_56
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 57 fz_hulls_57 fz_wins_57 fz_cold_57
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 58 fz_hulls_58 fz_wins_58 fz_cold_58
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 59 fz_hulls_59 fz_wins_59 fz_cold_59
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 60 fz_hulls_60 fz_wins_60 fz_cold_60
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 61 fz_hulls_61 fz_wins_61 fz_cold_61
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 62 fz_hulls_62 fz_wins_62 fz_cold_62
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 63 fz_hulls_63 fz_wins_63 fz_cold_63
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 64 fz_hulls_64 fz_wins_64 fz_cold_64
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 65 fz_hulls_65 fz_wins_65 fz_cold_65
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 66 fz_hulls_66 fz_wins_66 fz_cold_66
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 67 fz_hulls_67 fz_wins_67 fz_cold_67
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 68 fz_hulls_68 fz_wins_68 fz_cold_68
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 69 fz_hulls_69 fz_wins_69 fz_cold_69
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 70 fz_hulls_70 fz_wins_70 fz_cold_70
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 71 fz_hulls_71 fz_wins_71 fz_cold_71
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 72 fz_hulls_72 fz_wins_72 fz_cold_72
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 73 fz_hulls_73 fz_wins_73 fz_cold_73
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 74 fz_hulls_74 fz_wins_74 fz_cold_74
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 75 fz_hulls_75 fz_wins_75 fz_cold_75
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 76 fz_hulls_76 fz_wins_76 fz_cold_76
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 77 fz_hulls_77 fz_wins_77 fz_cold_77
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xb7fd8]]
  (PFrozen 78 fz_hulls_78 fz_wins_78 fz_cold_78
    [FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun false [0xb7fd8]; FRun true [0xc187c]]
  (PDropRange (ELit 0x18e938) (ELit 0x12b0)
  (PRun []
  (PMmap1
  (PRangeGaps 224 4096
  (PRun [0xd41dc]
  (PFresh 9 12 None
  (PRun []
  (PMmapIn1
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap1
  (PRangeGaps 242 4096
  (PRun []
  (PMmap1
  (PRangeGaps 243 4096
  (PRun []
  (PMmapGaps
  [  (startup_plan_side7);
  (startup_plan_side7)])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_seg90 : plan :=
  PRun []
  (PMmap1
  (PRangeGaps 261 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PMmap1
  (PRangeGaps 326 4096
  (PRun []
  (PMmap1
  (PRangeGaps 327 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PSys YMunmap
  (PSplit (EVar 10) 10
  (PHandoff 91  )
  (PHandoff 94  )))))))))))))))))))))))).

Definition startup_plan_seg91 : plan :=
  startup_plan_s2A3.

Definition startup_plan_seg94 : plan :=
  startup_plan_s2D6.

Definition startup_plan_seg100 : plan :=
  PRun [0xa0300]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap1
  (PRangeGaps 443 4096
  (PRun []
  (PMmap1
  (PRangeGaps 444 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap1
  (PRangeGaps 461 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PFrozen 90 fz_hulls_90 fz_wins_90 fz_cold_90
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 91 fz_hulls_91 fz_wins_91 fz_cold_91
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 92 fz_hulls_92 fz_wins_92 fz_cold_92
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 93 fz_hulls_93 fz_wins_93 fz_cold_93
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 94 fz_hulls_94 fz_wins_94 fz_cold_94
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 95 fz_hulls_95 fz_wins_95 fz_cold_95
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 96 fz_hulls_96 fz_wins_96 fz_cold_96
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 97 fz_hulls_97 fz_wins_97 fz_cold_97
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 98 fz_hulls_98 fz_wins_98 fz_cold_98
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 99 fz_hulls_99 fz_wins_99 fz_cold_99
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 100 fz_hulls_100 fz_wins_100 fz_cold_100
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 101 fz_hulls_101 fz_wins_101 fz_cold_101
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 102 fz_hulls_102 fz_wins_102 fz_cold_102
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 103 fz_hulls_103 fz_wins_103 fz_cold_103
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 104 fz_hulls_104 fz_wins_104 fz_cold_104
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 105 fz_hulls_105 fz_wins_105 fz_cold_105
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 106 fz_hulls_106 fz_wins_106 fz_cold_106
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 107 fz_hulls_107 fz_wins_107 fz_cold_107
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 108 fz_hulls_108 fz_wins_108 fz_cold_108
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 109 fz_hulls_109 fz_wins_109 fz_cold_109
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 110 fz_hulls_110 fz_wins_110 fz_cold_110
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 111 fz_hulls_111 fz_wins_111 fz_cold_111
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 112 fz_hulls_112 fz_wins_112 fz_cold_112
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 113 fz_hulls_113 fz_wins_113 fz_cold_113
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 114 fz_hulls_114 fz_wins_114 fz_cold_114
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 115 fz_hulls_115 fz_wins_115 fz_cold_115
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 116 fz_hulls_116 fz_wins_116 fz_cold_116
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 117 fz_hulls_117 fz_wins_117 fz_cold_117
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 118 fz_hulls_118 fz_wins_118 fz_cold_118
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 119 fz_hulls_119 fz_wins_119 fz_cold_119
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 120 fz_hulls_120 fz_wins_120 fz_cold_120
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 121 fz_hulls_121 fz_wins_121 fz_cold_121
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 122 fz_hulls_122 fz_wins_122 fz_cold_122
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 123 fz_hulls_123 fz_wins_123 fz_cold_123
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 124 fz_hulls_124 fz_wins_124 fz_cold_124
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 125 fz_hulls_125 fz_wins_125 fz_cold_125
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 126 fz_hulls_126 fz_wins_126 fz_cold_126
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 127 fz_hulls_127 fz_wins_127 fz_cold_127
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 128 fz_hulls_128 fz_wins_128 fz_cold_128
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 129 fz_hulls_129 fz_wins_129 fz_cold_129
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 130 fz_hulls_130 fz_wins_130 fz_cold_130
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 131 fz_hulls_131 fz_wins_131 fz_cold_131
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 132 fz_hulls_132 fz_wins_132 fz_cold_132
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 133 fz_hulls_133 fz_wins_133 fz_cold_133
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 134 fz_hulls_134 fz_wins_134 fz_cold_134
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 135 fz_hulls_135 fz_wins_135 fz_cold_135
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 136 fz_hulls_136 fz_wins_136 fz_cold_136
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 137 fz_hulls_137 fz_wins_137 fz_cold_137
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 138 fz_hulls_138 fz_wins_138 fz_cold_138
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 139 fz_hulls_139 fz_wins_139 fz_cold_139
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 140 fz_hulls_140 fz_wins_140 fz_cold_140
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 141 fz_hulls_141 fz_wins_141 fz_cold_141
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 142 fz_hulls_142 fz_wins_142 fz_cold_142
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 143 fz_hulls_143 fz_wins_143 fz_cold_143
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 144 fz_hulls_144 fz_wins_144 fz_cold_144
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 145 fz_hulls_145 fz_wins_145 fz_cold_145
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 146 fz_hulls_146 fz_wins_146 fz_cold_146
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 147 fz_hulls_147 fz_wins_147 fz_cold_147
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 148 fz_hulls_148 fz_wins_148 fz_cold_148
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 149 fz_hulls_149 fz_wins_149 fz_cold_149
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 150 fz_hulls_150 fz_wins_150 fz_cold_150
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 151 fz_hulls_151 fz_wins_151 fz_cold_151
    [FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 152 fz_hulls_152 fz_wins_152 fz_cold_152
    [FRun true []]
  (PX XMemIsZero []
  (PFrozen 82 fz_hulls_82 fz_wins_82 fz_cold_82
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 83 fz_hulls_83 fz_wins_83 fz_cold_83
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 84 fz_hulls_84 fz_wins_84 fz_cold_84
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 85 fz_hulls_85 fz_wins_85 fz_cold_85
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 86 fz_hulls_86 fz_wins_86 fz_cold_86
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 87 fz_hulls_87 fz_wins_87 fz_cold_87
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 88 fz_hulls_88 fz_wins_88 fz_cold_88
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 89 fz_hulls_89 fz_wins_89 fz_cold_89
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []]
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun [0xe83f4]
  (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 0  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_seg101 : plan :=
  PRun [0xa0300]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap1
  (PRangeGaps 443 4096
  (PRun []
  (PMmap1
  (PRangeGaps 444 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap1
  (PRangeGaps 461 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PFrozen 161 fz_hulls_161 fz_wins_161 fz_cold_161
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 162 fz_hulls_162 fz_wins_162 fz_cold_162
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 163 fz_hulls_163 fz_wins_163 fz_cold_163
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 164 fz_hulls_164 fz_wins_164 fz_cold_164
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 165 fz_hulls_165 fz_wins_165 fz_cold_165
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 166 fz_hulls_166 fz_wins_166 fz_cold_166
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 167 fz_hulls_167 fz_wins_167 fz_cold_167
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 168 fz_hulls_168 fz_wins_168 fz_cold_168
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 169 fz_hulls_169 fz_wins_169 fz_cold_169
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 170 fz_hulls_170 fz_wins_170 fz_cold_170
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 171 fz_hulls_171 fz_wins_171 fz_cold_171
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 172 fz_hulls_172 fz_wins_172 fz_cold_172
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 173 fz_hulls_173 fz_wins_173 fz_cold_173
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 174 fz_hulls_174 fz_wins_174 fz_cold_174
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 175 fz_hulls_175 fz_wins_175 fz_cold_175
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 176 fz_hulls_176 fz_wins_176 fz_cold_176
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 177 fz_hulls_177 fz_wins_177 fz_cold_177
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 178 fz_hulls_178 fz_wins_178 fz_cold_178
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 179 fz_hulls_179 fz_wins_179 fz_cold_179
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 180 fz_hulls_180 fz_wins_180 fz_cold_180
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 181 fz_hulls_181 fz_wins_181 fz_cold_181
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 182 fz_hulls_182 fz_wins_182 fz_cold_182
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 183 fz_hulls_183 fz_wins_183 fz_cold_183
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 184 fz_hulls_184 fz_wins_184 fz_cold_184
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 185 fz_hulls_185 fz_wins_185 fz_cold_185
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 186 fz_hulls_186 fz_wins_186 fz_cold_186
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 187 fz_hulls_187 fz_wins_187 fz_cold_187
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 188 fz_hulls_188 fz_wins_188 fz_cold_188
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 189 fz_hulls_189 fz_wins_189 fz_cold_189
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 190 fz_hulls_190 fz_wins_190 fz_cold_190
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 191 fz_hulls_191 fz_wins_191 fz_cold_191
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 192 fz_hulls_192 fz_wins_192 fz_cold_192
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 193 fz_hulls_193 fz_wins_193 fz_cold_193
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 194 fz_hulls_194 fz_wins_194 fz_cold_194
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 195 fz_hulls_195 fz_wins_195 fz_cold_195
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 196 fz_hulls_196 fz_wins_196 fz_cold_196
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 197 fz_hulls_197 fz_wins_197 fz_cold_197
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 198 fz_hulls_198 fz_wins_198 fz_cold_198
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 199 fz_hulls_199 fz_wins_199 fz_cold_199
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 200 fz_hulls_200 fz_wins_200 fz_cold_200
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 201 fz_hulls_201 fz_wins_201 fz_cold_201
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 202 fz_hulls_202 fz_wins_202 fz_cold_202
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 203 fz_hulls_203 fz_wins_203 fz_cold_203
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 204 fz_hulls_204 fz_wins_204 fz_cold_204
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 205 fz_hulls_205 fz_wins_205 fz_cold_205
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 206 fz_hulls_206 fz_wins_206 fz_cold_206
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 207 fz_hulls_207 fz_wins_207 fz_cold_207
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 208 fz_hulls_208 fz_wins_208 fz_cold_208
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 209 fz_hulls_209 fz_wins_209 fz_cold_209
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 210 fz_hulls_210 fz_wins_210 fz_cold_210
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 211 fz_hulls_211 fz_wins_211 fz_cold_211
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 212 fz_hulls_212 fz_wins_212 fz_cold_212
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 213 fz_hulls_213 fz_wins_213 fz_cold_213
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 214 fz_hulls_214 fz_wins_214 fz_cold_214
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 215 fz_hulls_215 fz_wins_215 fz_cold_215
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 216 fz_hulls_216 fz_wins_216 fz_cold_216
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 217 fz_hulls_217 fz_wins_217 fz_cold_217
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 218 fz_hulls_218 fz_wins_218 fz_cold_218
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 219 fz_hulls_219 fz_wins_219 fz_cold_219
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 220 fz_hulls_220 fz_wins_220 fz_cold_220
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 221 fz_hulls_221 fz_wins_221 fz_cold_221
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 222 fz_hulls_222 fz_wins_222 fz_cold_222
    [FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 223 fz_hulls_223 fz_wins_223 fz_cold_223
    [FRun true []]
  (PX XMemIsZero []
  (PFrozen 153 fz_hulls_153 fz_wins_153 fz_cold_153
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 154 fz_hulls_154 fz_wins_154 fz_cold_154
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 155 fz_hulls_155 fz_wins_155 fz_cold_155
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 156 fz_hulls_156 fz_wins_156 fz_cold_156
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 157 fz_hulls_157 fz_wins_157 fz_cold_157
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 158 fz_hulls_158 fz_wins_158 fz_cold_158
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 159 fz_hulls_159 fz_wins_159 fz_cold_159
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 160 fz_hulls_160 fz_wins_160 fz_cold_160
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []]
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun [0xe83f4]
  (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 1  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_seg102 : plan :=
  PRun [0xa0300]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap1
  (PRangeGaps 443 4096
  (PRun []
  (PMmap1
  (PRangeGaps 444 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap1
  (PRangeGaps 461 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PFrozen 232 fz_hulls_232 fz_wins_232 fz_cold_232
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 233 fz_hulls_233 fz_wins_233 fz_cold_233
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 234 fz_hulls_234 fz_wins_234 fz_cold_234
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 235 fz_hulls_235 fz_wins_235 fz_cold_235
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 236 fz_hulls_236 fz_wins_236 fz_cold_236
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 237 fz_hulls_237 fz_wins_237 fz_cold_237
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 238 fz_hulls_238 fz_wins_238 fz_cold_238
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 239 fz_hulls_239 fz_wins_239 fz_cold_239
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 240 fz_hulls_240 fz_wins_240 fz_cold_240
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 241 fz_hulls_241 fz_wins_241 fz_cold_241
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 242 fz_hulls_242 fz_wins_242 fz_cold_242
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 243 fz_hulls_243 fz_wins_243 fz_cold_243
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 244 fz_hulls_244 fz_wins_244 fz_cold_244
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 245 fz_hulls_245 fz_wins_245 fz_cold_245
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 246 fz_hulls_246 fz_wins_246 fz_cold_246
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 247 fz_hulls_247 fz_wins_247 fz_cold_247
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 248 fz_hulls_248 fz_wins_248 fz_cold_248
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 249 fz_hulls_249 fz_wins_249 fz_cold_249
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 250 fz_hulls_250 fz_wins_250 fz_cold_250
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 251 fz_hulls_251 fz_wins_251 fz_cold_251
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 252 fz_hulls_252 fz_wins_252 fz_cold_252
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 253 fz_hulls_253 fz_wins_253 fz_cold_253
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 254 fz_hulls_254 fz_wins_254 fz_cold_254
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 255 fz_hulls_255 fz_wins_255 fz_cold_255
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 256 fz_hulls_256 fz_wins_256 fz_cold_256
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 257 fz_hulls_257 fz_wins_257 fz_cold_257
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 258 fz_hulls_258 fz_wins_258 fz_cold_258
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 259 fz_hulls_259 fz_wins_259 fz_cold_259
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 260 fz_hulls_260 fz_wins_260 fz_cold_260
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 261 fz_hulls_261 fz_wins_261 fz_cold_261
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 262 fz_hulls_262 fz_wins_262 fz_cold_262
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 263 fz_hulls_263 fz_wins_263 fz_cold_263
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 264 fz_hulls_264 fz_wins_264 fz_cold_264
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 265 fz_hulls_265 fz_wins_265 fz_cold_265
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 266 fz_hulls_266 fz_wins_266 fz_cold_266
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 267 fz_hulls_267 fz_wins_267 fz_cold_267
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 268 fz_hulls_268 fz_wins_268 fz_cold_268
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 269 fz_hulls_269 fz_wins_269 fz_cold_269
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 270 fz_hulls_270 fz_wins_270 fz_cold_270
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 271 fz_hulls_271 fz_wins_271 fz_cold_271
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 272 fz_hulls_272 fz_wins_272 fz_cold_272
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 273 fz_hulls_273 fz_wins_273 fz_cold_273
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 274 fz_hulls_274 fz_wins_274 fz_cold_274
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 275 fz_hulls_275 fz_wins_275 fz_cold_275
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 276 fz_hulls_276 fz_wins_276 fz_cold_276
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 277 fz_hulls_277 fz_wins_277 fz_cold_277
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 278 fz_hulls_278 fz_wins_278 fz_cold_278
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 279 fz_hulls_279 fz_wins_279 fz_cold_279
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 280 fz_hulls_280 fz_wins_280 fz_cold_280
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 281 fz_hulls_281 fz_wins_281 fz_cold_281
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 282 fz_hulls_282 fz_wins_282 fz_cold_282
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 283 fz_hulls_283 fz_wins_283 fz_cold_283
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 284 fz_hulls_284 fz_wins_284 fz_cold_284
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 285 fz_hulls_285 fz_wins_285 fz_cold_285
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 286 fz_hulls_286 fz_wins_286 fz_cold_286
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 287 fz_hulls_287 fz_wins_287 fz_cold_287
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 288 fz_hulls_288 fz_wins_288 fz_cold_288
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 289 fz_hulls_289 fz_wins_289 fz_cold_289
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 290 fz_hulls_290 fz_wins_290 fz_cold_290
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 291 fz_hulls_291 fz_wins_291 fz_cold_291
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 292 fz_hulls_292 fz_wins_292 fz_cold_292
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 293 fz_hulls_293 fz_wins_293 fz_cold_293
    [FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 294 fz_hulls_294 fz_wins_294 fz_cold_294
    [FRun true []]
  (PX XMemIsZero []
  (PFrozen 224 fz_hulls_224 fz_wins_224 fz_cold_224
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 225 fz_hulls_225 fz_wins_225 fz_cold_225
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 226 fz_hulls_226 fz_wins_226 fz_cold_226
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 227 fz_hulls_227 fz_wins_227 fz_cold_227
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 228 fz_hulls_228 fz_wins_228 fz_cold_228
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 229 fz_hulls_229 fz_wins_229 fz_cold_229
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 230 fz_hulls_230 fz_wins_230 fz_cold_230
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 231 fz_hulls_231 fz_wins_231 fz_cold_231
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []]
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun [0xe83f4]
  (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 2  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_seg103 : plan :=
  PRun [0xa0300]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap1
  (PRangeGaps 443 4096
  (PRun []
  (PMmap1
  (PRangeGaps 444 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap1
  (PRangeGaps 461 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PFrozen 303 fz_hulls_303 fz_wins_303 fz_cold_303
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 304 fz_hulls_304 fz_wins_304 fz_cold_304
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 305 fz_hulls_305 fz_wins_305 fz_cold_305
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 306 fz_hulls_306 fz_wins_306 fz_cold_306
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 307 fz_hulls_307 fz_wins_307 fz_cold_307
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 308 fz_hulls_308 fz_wins_308 fz_cold_308
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 309 fz_hulls_309 fz_wins_309 fz_cold_309
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 310 fz_hulls_310 fz_wins_310 fz_cold_310
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 311 fz_hulls_311 fz_wins_311 fz_cold_311
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 312 fz_hulls_312 fz_wins_312 fz_cold_312
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 313 fz_hulls_313 fz_wins_313 fz_cold_313
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 314 fz_hulls_314 fz_wins_314 fz_cold_314
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 315 fz_hulls_315 fz_wins_315 fz_cold_315
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 316 fz_hulls_316 fz_wins_316 fz_cold_316
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 317 fz_hulls_317 fz_wins_317 fz_cold_317
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 318 fz_hulls_318 fz_wins_318 fz_cold_318
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 319 fz_hulls_319 fz_wins_319 fz_cold_319
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 320 fz_hulls_320 fz_wins_320 fz_cold_320
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 321 fz_hulls_321 fz_wins_321 fz_cold_321
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 322 fz_hulls_322 fz_wins_322 fz_cold_322
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 323 fz_hulls_323 fz_wins_323 fz_cold_323
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 324 fz_hulls_324 fz_wins_324 fz_cold_324
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 325 fz_hulls_325 fz_wins_325 fz_cold_325
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 326 fz_hulls_326 fz_wins_326 fz_cold_326
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 327 fz_hulls_327 fz_wins_327 fz_cold_327
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 328 fz_hulls_328 fz_wins_328 fz_cold_328
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 329 fz_hulls_329 fz_wins_329 fz_cold_329
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 330 fz_hulls_330 fz_wins_330 fz_cold_330
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 331 fz_hulls_331 fz_wins_331 fz_cold_331
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 332 fz_hulls_332 fz_wins_332 fz_cold_332
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 333 fz_hulls_333 fz_wins_333 fz_cold_333
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 334 fz_hulls_334 fz_wins_334 fz_cold_334
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 335 fz_hulls_335 fz_wins_335 fz_cold_335
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 336 fz_hulls_336 fz_wins_336 fz_cold_336
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 337 fz_hulls_337 fz_wins_337 fz_cold_337
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 338 fz_hulls_338 fz_wins_338 fz_cold_338
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 339 fz_hulls_339 fz_wins_339 fz_cold_339
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 340 fz_hulls_340 fz_wins_340 fz_cold_340
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 341 fz_hulls_341 fz_wins_341 fz_cold_341
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 342 fz_hulls_342 fz_wins_342 fz_cold_342
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 343 fz_hulls_343 fz_wins_343 fz_cold_343
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 344 fz_hulls_344 fz_wins_344 fz_cold_344
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 345 fz_hulls_345 fz_wins_345 fz_cold_345
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 346 fz_hulls_346 fz_wins_346 fz_cold_346
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 347 fz_hulls_347 fz_wins_347 fz_cold_347
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 348 fz_hulls_348 fz_wins_348 fz_cold_348
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 349 fz_hulls_349 fz_wins_349 fz_cold_349
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 350 fz_hulls_350 fz_wins_350 fz_cold_350
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 351 fz_hulls_351 fz_wins_351 fz_cold_351
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 352 fz_hulls_352 fz_wins_352 fz_cold_352
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 353 fz_hulls_353 fz_wins_353 fz_cold_353
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 354 fz_hulls_354 fz_wins_354 fz_cold_354
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 355 fz_hulls_355 fz_wins_355 fz_cold_355
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 356 fz_hulls_356 fz_wins_356 fz_cold_356
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 357 fz_hulls_357 fz_wins_357 fz_cold_357
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 358 fz_hulls_358 fz_wins_358 fz_cold_358
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 359 fz_hulls_359 fz_wins_359 fz_cold_359
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 360 fz_hulls_360 fz_wins_360 fz_cold_360
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 361 fz_hulls_361 fz_wins_361 fz_cold_361
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 362 fz_hulls_362 fz_wins_362 fz_cold_362
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 363 fz_hulls_363 fz_wins_363 fz_cold_363
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 364 fz_hulls_364 fz_wins_364 fz_cold_364
    [FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 365 fz_hulls_365 fz_wins_365 fz_cold_365
    [FRun true []]
  (PX XMemIsZero []
  (PFrozen 295 fz_hulls_295 fz_wins_295 fz_cold_295
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 296 fz_hulls_296 fz_wins_296 fz_cold_296
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 297 fz_hulls_297 fz_wins_297 fz_cold_297
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 298 fz_hulls_298 fz_wins_298 fz_cold_298
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 299 fz_hulls_299 fz_wins_299 fz_cold_299
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 300 fz_hulls_300 fz_wins_300 fz_cold_300
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 301 fz_hulls_301 fz_wins_301 fz_cold_301
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 302 fz_hulls_302 fz_wins_302 fz_cold_302
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []]
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun [0xe83f4]
  (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 3  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_seg104 : plan :=
  PRun [0xa0300]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap1
  (PRangeGaps 443 4096
  (PRun []
  (PMmap1
  (PRangeGaps 444 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap1
  (PRangeGaps 461 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PFrozen 374 fz_hulls_374 fz_wins_374 fz_cold_374
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 375 fz_hulls_375 fz_wins_375 fz_cold_375
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 376 fz_hulls_376 fz_wins_376 fz_cold_376
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 377 fz_hulls_377 fz_wins_377 fz_cold_377
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 378 fz_hulls_378 fz_wins_378 fz_cold_378
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 379 fz_hulls_379 fz_wins_379 fz_cold_379
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 380 fz_hulls_380 fz_wins_380 fz_cold_380
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 381 fz_hulls_381 fz_wins_381 fz_cold_381
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 382 fz_hulls_382 fz_wins_382 fz_cold_382
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 383 fz_hulls_383 fz_wins_383 fz_cold_383
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 384 fz_hulls_384 fz_wins_384 fz_cold_384
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 385 fz_hulls_385 fz_wins_385 fz_cold_385
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 386 fz_hulls_386 fz_wins_386 fz_cold_386
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 387 fz_hulls_387 fz_wins_387 fz_cold_387
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 388 fz_hulls_388 fz_wins_388 fz_cold_388
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 389 fz_hulls_389 fz_wins_389 fz_cold_389
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 390 fz_hulls_390 fz_wins_390 fz_cold_390
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 391 fz_hulls_391 fz_wins_391 fz_cold_391
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 392 fz_hulls_392 fz_wins_392 fz_cold_392
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 393 fz_hulls_393 fz_wins_393 fz_cold_393
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 394 fz_hulls_394 fz_wins_394 fz_cold_394
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 395 fz_hulls_395 fz_wins_395 fz_cold_395
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 396 fz_hulls_396 fz_wins_396 fz_cold_396
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 397 fz_hulls_397 fz_wins_397 fz_cold_397
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 398 fz_hulls_398 fz_wins_398 fz_cold_398
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 399 fz_hulls_399 fz_wins_399 fz_cold_399
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 400 fz_hulls_400 fz_wins_400 fz_cold_400
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 401 fz_hulls_401 fz_wins_401 fz_cold_401
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 402 fz_hulls_402 fz_wins_402 fz_cold_402
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 403 fz_hulls_403 fz_wins_403 fz_cold_403
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 404 fz_hulls_404 fz_wins_404 fz_cold_404
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 405 fz_hulls_405 fz_wins_405 fz_cold_405
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 406 fz_hulls_406 fz_wins_406 fz_cold_406
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 407 fz_hulls_407 fz_wins_407 fz_cold_407
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 408 fz_hulls_408 fz_wins_408 fz_cold_408
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 409 fz_hulls_409 fz_wins_409 fz_cold_409
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 410 fz_hulls_410 fz_wins_410 fz_cold_410
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 411 fz_hulls_411 fz_wins_411 fz_cold_411
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 412 fz_hulls_412 fz_wins_412 fz_cold_412
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 413 fz_hulls_413 fz_wins_413 fz_cold_413
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 414 fz_hulls_414 fz_wins_414 fz_cold_414
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 415 fz_hulls_415 fz_wins_415 fz_cold_415
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 416 fz_hulls_416 fz_wins_416 fz_cold_416
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 417 fz_hulls_417 fz_wins_417 fz_cold_417
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 418 fz_hulls_418 fz_wins_418 fz_cold_418
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 419 fz_hulls_419 fz_wins_419 fz_cold_419
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 420 fz_hulls_420 fz_wins_420 fz_cold_420
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 421 fz_hulls_421 fz_wins_421 fz_cold_421
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 422 fz_hulls_422 fz_wins_422 fz_cold_422
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 423 fz_hulls_423 fz_wins_423 fz_cold_423
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 424 fz_hulls_424 fz_wins_424 fz_cold_424
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 425 fz_hulls_425 fz_wins_425 fz_cold_425
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 426 fz_hulls_426 fz_wins_426 fz_cold_426
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 427 fz_hulls_427 fz_wins_427 fz_cold_427
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 428 fz_hulls_428 fz_wins_428 fz_cold_428
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 429 fz_hulls_429 fz_wins_429 fz_cold_429
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 430 fz_hulls_430 fz_wins_430 fz_cold_430
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 431 fz_hulls_431 fz_wins_431 fz_cold_431
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 432 fz_hulls_432 fz_wins_432 fz_cold_432
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 433 fz_hulls_433 fz_wins_433 fz_cold_433
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 434 fz_hulls_434 fz_wins_434 fz_cold_434
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 435 fz_hulls_435 fz_wins_435 fz_cold_435
    [FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 436 fz_hulls_436 fz_wins_436 fz_cold_436
    [FRun true []]
  (PX XMemIsZero []
  (PFrozen 366 fz_hulls_366 fz_wins_366 fz_cold_366
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 367 fz_hulls_367 fz_wins_367 fz_cold_367
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 368 fz_hulls_368 fz_wins_368 fz_cold_368
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 369 fz_hulls_369 fz_wins_369 fz_cold_369
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 370 fz_hulls_370 fz_wins_370 fz_cold_370
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 371 fz_hulls_371 fz_wins_371 fz_cold_371
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 372 fz_hulls_372 fz_wins_372 fz_cold_372
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 373 fz_hulls_373 fz_wins_373 fz_cold_373
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []]
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun [0xe83f4]
  (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 4  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan_seg105 : plan :=
  PRun [0xa0300]
  (PJoin e_sp0 (-2280) 8
  (PRun []
  (PMmap1
  (PRangeGaps 443 4096
  (PRun []
  (PMmap1
  (PRangeGaps 444 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PMmap1
  (PRangeGaps 461 4096
  (PRun []
  (PX XIMemcpy []
  (PRun []
  (PX XIMemcpy []
  (PFrozen 445 fz_hulls_445 fz_wins_445 fz_cold_445
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 446 fz_hulls_446 fz_wins_446 fz_cold_446
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 447 fz_hulls_447 fz_wins_447 fz_cold_447
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 448 fz_hulls_448 fz_wins_448 fz_cold_448
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 449 fz_hulls_449 fz_wins_449 fz_cold_449
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 450 fz_hulls_450 fz_wins_450 fz_cold_450
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 451 fz_hulls_451 fz_wins_451 fz_cold_451
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 452 fz_hulls_452 fz_wins_452 fz_cold_452
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 453 fz_hulls_453 fz_wins_453 fz_cold_453
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 454 fz_hulls_454 fz_wins_454 fz_cold_454
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 455 fz_hulls_455 fz_wins_455 fz_cold_455
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 456 fz_hulls_456 fz_wins_456 fz_cold_456
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 457 fz_hulls_457 fz_wins_457 fz_cold_457
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 458 fz_hulls_458 fz_wins_458 fz_cold_458
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 459 fz_hulls_459 fz_wins_459 fz_cold_459
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 460 fz_hulls_460 fz_wins_460 fz_cold_460
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 461 fz_hulls_461 fz_wins_461 fz_cold_461
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 462 fz_hulls_462 fz_wins_462 fz_cold_462
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 463 fz_hulls_463 fz_wins_463 fz_cold_463
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 464 fz_hulls_464 fz_wins_464 fz_cold_464
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 465 fz_hulls_465 fz_wins_465 fz_cold_465
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 466 fz_hulls_466 fz_wins_466 fz_cold_466
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 467 fz_hulls_467 fz_wins_467 fz_cold_467
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 468 fz_hulls_468 fz_wins_468 fz_cold_468
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 469 fz_hulls_469 fz_wins_469 fz_cold_469
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 470 fz_hulls_470 fz_wins_470 fz_cold_470
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 471 fz_hulls_471 fz_wins_471 fz_cold_471
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 472 fz_hulls_472 fz_wins_472 fz_cold_472
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 473 fz_hulls_473 fz_wins_473 fz_cold_473
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 474 fz_hulls_474 fz_wins_474 fz_cold_474
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 475 fz_hulls_475 fz_wins_475 fz_cold_475
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 476 fz_hulls_476 fz_wins_476 fz_cold_476
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 477 fz_hulls_477 fz_wins_477 fz_cold_477
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 478 fz_hulls_478 fz_wins_478 fz_cold_478
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 479 fz_hulls_479 fz_wins_479 fz_cold_479
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 480 fz_hulls_480 fz_wins_480 fz_cold_480
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 481 fz_hulls_481 fz_wins_481 fz_cold_481
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 482 fz_hulls_482 fz_wins_482 fz_cold_482
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 483 fz_hulls_483 fz_wins_483 fz_cold_483
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 484 fz_hulls_484 fz_wins_484 fz_cold_484
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 485 fz_hulls_485 fz_wins_485 fz_cold_485
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 486 fz_hulls_486 fz_wins_486 fz_cold_486
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 487 fz_hulls_487 fz_wins_487 fz_cold_487
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 488 fz_hulls_488 fz_wins_488 fz_cold_488
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 489 fz_hulls_489 fz_wins_489 fz_cold_489
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 490 fz_hulls_490 fz_wins_490 fz_cold_490
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 491 fz_hulls_491 fz_wins_491 fz_cold_491
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 492 fz_hulls_492 fz_wins_492 fz_cold_492
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 493 fz_hulls_493 fz_wins_493 fz_cold_493
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 494 fz_hulls_494 fz_wins_494 fz_cold_494
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 495 fz_hulls_495 fz_wins_495 fz_cold_495
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 496 fz_hulls_496 fz_wins_496 fz_cold_496
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 497 fz_hulls_497 fz_wins_497 fz_cold_497
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 498 fz_hulls_498 fz_wins_498 fz_cold_498
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 499 fz_hulls_499 fz_wins_499 fz_cold_499
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 500 fz_hulls_500 fz_wins_500 fz_cold_500
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 501 fz_hulls_501 fz_wins_501 fz_cold_501
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 502 fz_hulls_502 fz_wins_502 fz_cold_502
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 503 fz_hulls_503 fz_wins_503 fz_cold_503
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 504 fz_hulls_504 fz_wins_504 fz_cold_504
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 505 fz_hulls_505 fz_wins_505 fz_cold_505
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 506 fz_hulls_506 fz_wins_506 fz_cold_506
    [FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 507 fz_hulls_507 fz_wins_507 fz_cold_507
    [FRun true []]
  (PX XMemIsZero []
  (PFrozen 437 fz_hulls_437 fz_wins_437 fz_cold_437
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 438 fz_hulls_438 fz_wins_438 fz_cold_438
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 439 fz_hulls_439 fz_wins_439 fz_cold_439
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 440 fz_hulls_440 fz_wins_440 fz_cold_440
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 441 fz_hulls_441 fz_wins_441 fz_cold_441
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 442 fz_hulls_442 fz_wins_442 fz_cold_442
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 443 fz_hulls_443 fz_wins_443 fz_cold_443
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []; FFill false]
  (PFrozen 444 fz_hulls_444 fz_wins_444 fz_cold_444
    [FRun false []; FFill false; FRun false []; FFill false; FRun false []; FFill false; FRun true []]
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun []
  (PX XMemIsZero []
  (PRun []
  (PX XMemset []
  (PRun [0xe83f4]
  (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat
  (PHandoff 5  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition startup_plan2 : plan := startup_plan_seg90.

Definition startup_plan_ranges : list (Z * nat) := [(0x91000, 23552%nat); (0xa9000, 54272%nat); (0xe0000, 16384%nat); (0x121000, 10240%nat); (0x140000, 9216%nat); (0x14a000, 8192%nat); (0x158000, 8192%nat); (0x162000, 13312%nat); (0x175000, 9216%nat)]%Z.

Definition CERT_KC0 : nat := 0.
Definition CERT_BFUEL : nat := 400000.
Definition CERT_FUEL : nat := 3000.
