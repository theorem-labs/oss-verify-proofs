(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan MainItab ArgFragsAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition KEEP_dir_bs_asan : list expr := [(ELit 0); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 2) (EVar 6)))].
Definition KEEP_dir_rs_asan : list (Z * Z) := [(66560, 66752); (67648, 67776); (81728, 81856); (83776, 83840); (89024, 89152); (109952, 110080); (116736, 116800); (126976, 127104); (177808, 178064); (1196864, 1197792); (1219936, 1220008); (1220016, 1220072); (1220200, 1220328); (1223144, 1223208); (1223400, 1223456); (1223464, 1223536); (1223664, 1223792); (1227072, 1228080); (1228280, 1228472); (1238584, 1240128); (1243776, 1243840); (1243904, 1244032); (1252032, 1252096); (1253952, 1254080); (1257280, 1257344); (1850816, 1850944); (1851008, 1851072); (1851648, 1851712); (6709568, 6709856); (6841136, 6841192); (6709856, 6710192); (6841192, 6842048); (6841168, 6841192); (6709856, 6709960); (6710152, 6710192); (6841192, 6841280); (6841472, 6841536); (6841728, 6841856); (6843136, 6843264); (2147459072, 2148290560); (2147466688, 2147466816); (2147468672, 2147469120); (2147605735, 2147605928); (2148288744, 2148288872); (17594199277440, 17594199277696)].

Definition frag_rderr_asan : plan :=
  PKeepOnly KEEP_dir_bs_asan KEEP_dir_rs_asan (PRun AL_STOPS_A 
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
  (PRun AL_STOPS_A (PExit))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
