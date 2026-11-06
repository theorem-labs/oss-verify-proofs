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
Definition err_ovra_r0_1 : plan := dec_plan (PE [] [] [e_sp0] [] [] []) "$6,12,#0,$6,;,1##0,1#62<<8$6,65,#0,1#75;50&0'#1000$>#0,1#75;70$6,66,#0,1#75;;8$6,67,#0,$43,#0,$6,=,#0,$6,?,#0,1#11394<$7,,#2(`'#10$6'#1000$:#8?5?#?<>#0,#<,2,13,15%:,4(~-8?8(~-;8(~-:8(~-:0#8,:,15,16,1:,1;,1=,2:,4>,60,1;2,1;3%5,2=,>,;,17,<,18,=,19,>,1:,?,1;,10,1<,11,1=,12,1>,13,1?,14,20,15,21,16,23,17,24,18,25,19,26,1:,27,1;,28,1<,29,1=,2:,1>,2;,1?,2<,20,2=,21,2>,22,2?,23,30,24,31,25,32,26,33,27,34,28,35,29,51,2:,52,2;,53,2<,5;,2=,5<,2>,5=,2?,5>,30,5?,31,60,32,61,33,62,34,63,35,64,36,65,37&=,32#0,#<,2,13,15%:,4(~-8?8(~-;8(~-:8(~-:0#8,:,15,16,1:,1;,1=,2:,4>,60,1;2,1;3%5,2=,>,;,17,<,18,=,19,>,1:,?,1;,10,1<,11,1=,12,1>,13,1?,14,20,15,21,16,23,17,24,18,25,19,26,1:,27,1;,28,1<,29,1=,2:,1>,2;,1?,2<,20,2=,21,2>,22,2?,23,30,24,31,25,32,26,33,27,34,28,35,29,51,2:,52,2;,53,2<,5;,2=,5<,2>,5=,2?,5>,30,5?,31,60,32,61,33,62,34,63,35,64,36,65,37&=,33"%pstring.

Definition err_ovra : plan := PBump 54 (PZoneHull (escale 4096 (EVar 31)) (PShDisj (escale 4096 (EVar 31)) (ELit 11571200) (escale 4096 (EVar 30)) (ELit 137439023104) err_ovra_r0_1)).

 
Definition errd_ovra_ranges : list (Z * nat) := [(0x4e000, 3072%nat); (0x52000, 5120%nat); (0x5e000, 6144%nat); (0x74000, 6144%nat); (0x7c000, 10240%nat); (0x87000, 5120%nat); (0x92000, 7168%nat); (0xa4000, 2048%nat); (0x10b000, 3072%nat); (0x113000, 3072%nat); (0x11c000, 5120%nat); (0x123000, 1024%nat)]%Z.
