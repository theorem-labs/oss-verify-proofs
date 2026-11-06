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
Section zf_b_al_sec.
Variable js_2 : acs.
Definition zf_bf_cfgarm1 : plan :=
  PRun [0xa447c]
  (PRespell 21 (EAlu Instr.ALU_ADD (ELit 1) (EMd Instr.M_MUL (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) (ELit 32767)) (ELit 15)))) (PHavoc [10]%nat (PMerge 2))  ).
Definition zf_bf_r0_2 : plan := dec_plan (PE [zf_bf_cfgarm1] [js_2] [] [] [] []) "$6,12,#0,$6,;,1##0,1#77?>8$6,64,#0,1#75:0<&0'#1000$>#0,1#77?>8$6,64,#0,1#77?>8$6,64,2('#1000$>#1800#10000#0,$43,#0,$6,=,#0,$6,?,#0,1#:4404%7,2!,7;#1&8&6@#200000000000000},8#1,1#31{,8#,1#!#1&9{,8#2,1#3#!#1&9{,8#2,1#3#1!#1&9{,8#2,1#3#2!!&0'#1000$>#0,1#:4480#<,;,5,6,7,>,?,10,11,1<,1=,1>,1?#6'$22#6#????#8,2<,8,17,26,27,28,29,2:,31,32,33,34,35,36,37,38,39,3:,3;,3<,3=,52,90,:1,<1,?1,10:,114,118,124,125,126,127,128,12;,134,135,14=,165,166,19?,1:0,1:3,1:<,1:?%5,1>,7;,;,7<,<,7=,=,7>,?,7?,10,80,11,81,12,82,13,83,14,84,15,85,16,22,17,1?,18,1>,19,17,1:,18,1;,1;,1<,1<,1=,19,1>,1:,1?,23,22,24,23,25,24,26,25,27,26,28,27,29,28,2:,29,2;,2:,1=,2;$;,398"%pstring.
Definition zf_bf : plan :=
  PBump 54
  (PZoneHull (escale 4096 (EVar 31))
  (PShDisj (escale 4096 (EVar 31)) (ELit 11571200) (escale 4096 (EVar 30)) (ELit 137439023104)
  (zf_bf_r0_2))).
End zf_b_al_sec.
Definition zf_b_al_ranges : list (Z * nat) := [(0x60000, 4096%nat); (0x74000, 6144%nat); (0x7d000, 2048%nat); (0x87000, 2048%nat); (0xa3000, 3072%nat); (0x10b000, 2048%nat); (0x113000, 2048%nat); (0x11c000, 3072%nat); (0x123000, 1024%nat)]%Z.
