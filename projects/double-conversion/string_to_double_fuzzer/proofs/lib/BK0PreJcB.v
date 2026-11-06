(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanPlan ArgFragsBoth.
From Corelib Require Import PrimString.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanStateCodec AsanPlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Section pre_jcb_al_sec.

Variable js_2 : acs.

Definition pre_jcbf_cfgarm1 : plan :=
  PRun [0xa455c]
  (PRespell 21 (EAlu Instr.ALU_ADD (ELit 1) (EMd Instr.M_MUL (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) (ELit 32767)) (ELit 15)))) (PHavoc [10]%nat (PMerge 2))  ).

Definition pre_jcbf_r0_2 : plan := dec_plan (PE [pre_jcbf_cfgarm1] [js_2] [] [] [] []) "$6,12,#0,$6,;,1##0,1#7812<$6,64,#0,1#75;50&0'#1000$>#0,1#7812<$6,64,#0,1#7812<$6,64,2('#1000$>#1800#10000#0,$43,#0,$6,=,#0,$6,?,#0,1#:4548%7,2!,7;#1&8&6@#200000000000000},8#1,1#31{,8#,1#!#1&9{,8#2,1#3#!#1&9{,8#2,1#3#1!#1&9{,8#2,1#3#2!!&0'#1000$>#>,8#!$6,1<,2+$7;&8&6@#200000000000000},8#1,1#31{,8#,1+$22-6#0,1#:4560#<,;,5,6,7,>,?,10,11,1<,1=,1>,1?#6'+$7;&8&6@#200000000000000},8#1,1#31{,8#,1##???9#6'$7;#1#?<00#6'$22#6#????#6'++$22@-1&8&6@#200000000000000},8#1,1#31{,8#,1-6#1#?<00#8,9,4,=,1<,2?,127,128,19>,19?,1:;%5,2<,7<,;,7=,<,7>,=,7;,>,>,?,22,10,7?,11,80,12,81,13,82,14,83,15,84,16,85,17,86,18,1?,19,1>,1:,17,1;,18,1<,19,1=,1;,1>,1<,1?,1=,20,1:,21,20,22,21,23,23,24,24,25,25,26,26,27,27,28,28,29,29,2:,2:,2;,2;,2<,2<,2=,2=,2>,2>,2?,2?,30,30,31,31,32,32,33,33,34,34,35,35,36$;,34"%pstring.

Definition pre_jcbf : plan :=
  PBump 54
  (PZoneHull (escale 4096 (EVar 31))
  (PShDisj (escale 4096 (EVar 31)) (ELit 11571200) (escale 4096 (EVar 30)) (ELit 137439023104)
  (pre_jcbf_r0_2))).

End pre_jcb_al_sec.

Definition pre_jcb_al_ranges : list (Z * nat) := [(0x60000, 4096%nat); (0x74000, 6144%nat); (0x7d000, 2048%nat); (0x87000, 3072%nat); (0xa4000, 2048%nat); (0x10c000, 2048%nat); (0x113000, 2048%nat); (0x11c000, 3072%nat); (0x123000, 1024%nat)]%Z.
