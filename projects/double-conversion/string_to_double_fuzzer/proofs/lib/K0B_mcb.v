(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanPlan ArgFragsAsan.
From Corelib Require Import PrimString.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanStateCodec AsanPlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition seg_mcbbf_r0_1 : plan := dec_plan (PE [] [] [] [] [] []) "#0,1#75:10&6'#1000$?'#1000$10#75:18,,3<#0,1#77?>8$6,64,2('#1000$?#1800#10000#0,1#77?>8$6,64,#0,%;,<++$24@-1&8&6@#200000000000000},8#1,1#31{,8#,1-6$43,#0,1#:4434#<,;,5,6,7,>,?,10,11,1<,1=,1>,1?%5,15,6<,;,6=,<,6>,=,61,13,62,14,63,15,6?,16,70,17,71,18,72,19,73,1:,74,1;,75,1<,76,1=,24,1>,23,1?,1>,20,1?,21,20,22,21,23,22,24$;,385"%pstring.
Definition seg_mcbbf : plan :=
  PBump 60
  (PZoneHull (escale 4096 (EVar 35))
  (PShDisj (escale 4096 (EVar 35)) (ELit 11571200) (escale 4096 (EVar 16)) (ELit 137439023104)
  (seg_mcbbf_r0_1))).

Definition seg_mcbb_ranges : list (Z * nat) := [(0x74000, 6144%nat); (0x87000, 2048%nat); (0xa4000, 2048%nat); (0x11c000, 2048%nat)]%Z.
