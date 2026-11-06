(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan MainItab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition AL_STOPS_A : list Z := [555932; 1165988; 1127536; 491496; 481836; 481908].

(* [comment removed for export] *)
Definition KEEP_usage_bs_asan : list expr := [(ELit 0); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 2) (EVar 6)))].
Definition KEEP_usage_rs_asan : list (Z * Z) := [(66432, 66752); (67648, 67776); (81728, 81856); (83776, 83840); (89024, 89152); (90496, 90624); (109952, 110080); (116736, 116800); (177808, 178064); (1196864, 1197792); (1219936, 1220008); (1220016, 1220072); (1220200, 1220328); (1223144, 1223208); (1223400, 1223456); (1223464, 1223536); (1223664, 1223792); (1227072, 1228080); (1228280, 1228472); (1238584, 1240128); (1243776, 1243840); (1243904, 1244032); (1252032, 1252096); (1253952, 1254080); (1257280, 1257408); (1850816, 1850944); (1851008, 1851072); (1851648, 1851712); (6709568, 6709856); (6841136, 6841192); (6709856, 6710192); (6841192, 6842048); (6841168, 6841192); (6709856, 6709960); (6710152, 6710192); (6841192, 6841280); (6841472, 6841536); (6841728, 6841856); (6843136, 6843264); (2147459072, 2148290560); (2147462144, 2147462272); (2147468672, 2147469120); (2147605735, 2147605928); (2148288744, 2148288872); (17594199277440, 17594199278144)].

(* [comment removed for export] *)
Definition KEEP_operr_bs_asan : list expr := [(ELit 0); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 2) (EVar 6)))].
Definition KEEP_operr_rs_asan : list (Z * Z) := [(66432, 66752); (67648, 67776); (81728, 81856); (83776, 83840); (89024, 89152); (109952, 110080); (116736, 116800); (126976, 127104); (177808, 178064); (1196864, 1197792); (1219936, 1220008); (1220016, 1220072); (1220200, 1220328); (1223144, 1223208); (1223400, 1223456); (1223464, 1223536); (1223664, 1223792); (1227072, 1228080); (1228280, 1228472); (1238584, 1240128); (1243776, 1243840); (1243904, 1244032); (1252032, 1252096); (1253952, 1254080); (1257280, 1257408); (1850816, 1850944); (1851008, 1851072); (1851648, 1851712); (6709568, 6709856); (6841136, 6841192); (6709856, 6710192); (6841192, 6842048); (6841168, 6841192); (6709856, 6709960); (6710152, 6710192); (6841192, 6841280); (6841472, 6841536); (6841728, 6841856); (6843136, 6843264); (2147459072, 2148290560); (2147466688, 2147466816); (2147468672, 2147469120); (2147605735, 2147605928); (2148288744, 2148288872); (17594199277440, 17594199278272)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition usage_0_0_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 0] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 0] 
  (PRun AL_STOPS_A (PExt 2 [ELit 0] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 3 [ELit 0] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition usage_1_63_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 0] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 0] 
  (PRun AL_STOPS_A (PExt 2 [ELit 0] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PExt 3 [ELit 0] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition usage_64_64_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 0] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 0] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 2 [ELit 0] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PExt 3 [ELit 0] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition usage_65_66_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 0] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 0] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 2 [ELit 0] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 3 [ELit 0] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition usage_67_73_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 0] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 0] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 2 [ELit 0] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 3 [ELit 0] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition usage_74_inf_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 0] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 0] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 2 [ELit 0] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition plan_usage_body_asan : plan := PSplit (EVar 3) 0 usage_0_0_asan (PSplit (EVar 3) 63 usage_1_63_asan (PSplit (EVar 3) 64 usage_64_64_asan (PSplit (EVar 3) 66 usage_65_66_asan (PSplit (EVar 3) 73 usage_67_73_asan (usage_74_inf_asan))))).
Definition plan_usage_r0_asan : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (plan_usage_body_asan))).
Definition plan_usage_r1_asan : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (plan_usage_body_asan))).
(* [comment removed for export] *)
Definition plan_u0_0_0_asan : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_0_0_asan))).
Definition plan_u1_0_0_asan : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_0_0_asan))).
Definition plan_u0_1_63_asan : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_1_63_asan))).
Definition plan_u1_1_63_asan : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_1_63_asan))).
Definition plan_u0_64_64_asan : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_64_64_asan))).
Definition plan_u1_64_64_asan : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_64_64_asan))).
Definition plan_u0_65_66_asan : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_65_66_asan))).
Definition plan_u1_65_66_asan : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_65_66_asan))).
Definition plan_u0_67_73_asan : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_67_73_asan))).
Definition plan_u1_67_73_asan : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_67_73_asan))).
Definition plan_u0_74_inf_asan : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_74_inf_asan))).
Definition plan_u1_74_inf_asan : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_asan KEEP_usage_rs_asan (usage_74_inf_asan))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition frag_operr0_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 1] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 1] 
  (PRun AL_STOPS_A (PExt 2 [ELit 1] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 3 [ELit 1] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition frag_operr_1_62_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 1] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 1] 
  (PRun AL_STOPS_A (PExt 2 [ELit 1] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PExt 3 [ELit 1] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition frag_operr_63_63_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 1] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 1] 
  (PRun AL_STOPS_A (PExt 2 [ELit 1] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PExt 3 [ELit 1] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition frag_operr_64_64_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 1] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 1] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 2 [ELit 1] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition frag_operr_65_4095_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 1] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 1] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 2 [ELit 1] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition frag_operr_asan : plan := PKeepOnly KEEP_operr_bs_asan KEEP_operr_rs_asan (PSplit (EVar 7) 62 frag_operr_1_62_asan (PSplit (EVar 7) 63 frag_operr_63_63_asan (PSplit (EVar 7) 64 frag_operr_64_64_asan (frag_operr_65_4095_asan)))).
(* [comment removed for export] *)
Definition frag_operr_long_asan : plan :=
  PRun AL_STOPS_A 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 0 [ELit 1] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PX XIMemset [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PExt 1 [ELit 1] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 100 [] 
  (PRun AL_STOPS_A (PExt 2 [ELit 1] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PExt 102 [] 
  (PRun AL_STOPS_A (PExt 103 [] 
  (PRun AL_STOPS_A (PX XMemcpy [] 
  (PRun AL_STOPS_A (PEmit 0 [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PX XMemset [] 
  (PRun AL_STOPS_A (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

