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

Definition seg_mcbf_r0_1 : plan := dec_plan (PE [] [] [] [] [] []) "#0,1#75:10&6'#1000$?'#1000$10#75:18,,3=#0,1#77?>8$6,64,2('#1000$?#1800#10000#0,1#77?>8$6,64,#0,$43,#0,1#:4434#<,;,5,6,7,>,?,10,11,1<,1=,1>,1?#6'$>#1#?<00#8,2,9,106%5,15,6=,;,6>,<,6?,=,62,13,63,14,64,15,70,16,71,17,72,18,73,19,74,1:,75,1;,76,1<,77,1=,24,1>,1>,1?,1?,20,20,21,21,22,22,23,23,24$;,48"%pstring.

Definition seg_mcbf : plan :=
  PBump 61
  (PZoneHull (escale 4096 (EVar 36))
  (PShDisj (escale 4096 (EVar 36)) (ELit 11571200) (escale 4096 (EVar 16)) (ELit 137439023104)
  (seg_mcbf_r0_1))).

Definition seg_mcb_ranges : list (Z * nat) := [(0x74000, 6144%nat); (0x87000, 2048%nat); (0xa4000, 2048%nat); (0x11c000, 2048%nat)]%Z.
