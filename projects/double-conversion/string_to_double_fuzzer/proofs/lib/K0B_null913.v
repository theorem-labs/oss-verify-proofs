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
Section nulltail913_sec.
Variable js_10 : acs.
Definition nulltail913_cntx1 : plan := PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] PExit)))))))))))))))))))).
Definition nulltail913_cntarm2 : plan := PRun [672480] (PRespell 8 (EMd Instr.M_MUL (ELit 2) (EAlu Instr.ALU_SLTU (EBlob true 8 1 1) (ELit 9223372036854775808))) (PHavoc [1; 10; 11; 5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PMerge 10))).
Definition nulltail913_r0_3_fb1 : plan := dec_plan (PE [nulltail913_cntx1] [] [e_sp0] [] [] []) "&0'#1000$?#0,$40,#0,$40,#0,$40,#0,$40,#0,1#53?8<#7~-8<8,8#0,$41,#0,1#776;8&3'#1000$?#778>4,9,=,>,?,10,11,5,6,7,1<,9;#0,$42,#0,%<#0,$0#0,$=#0,$=#0,$42,#0,%<#0,$0#0,$=#0,$=#0,$42,#0,1#55168$49,1#8#0,1#:42>8#1},8#1,1^#7#???????????????!!#0,$0#0,$=#0,$=#0,$0#0,$=#0,$="%pstring.
Definition nulltail913_r0_3 : plan := PRun [672352] (PVia 10 js_10 75 (PSplit (EBlob true 8 1 1) 9223372036854775807 nulltail913_cntarm2 nulltail913_cntarm2) (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 36703) 4046 nulltail913_r0_3_fb1 nulltail913_r0_3_fb1)).
Definition nulltail913 : plan := PBump 59 (PZoneHull (escale 4096 (EVar 31)) (PShDisj (escale 4096 (EVar 31)) (ELit 11571200) (escale 4096 (EVar 27)) (ELit 137439023104) nulltail913_r0_3)).
End nulltail913_sec.
Definition nulltail913_ranges : list (Z * nat) := [(0x4e000, 3072%nat); (0x52000, 5120%nat); (0x5e000, 2048%nat); (0x76000, 4096%nat); (0x7c000, 10240%nat); (0x87000, 5120%nat); (0x92000, 3072%nat); (0x96000, 3072%nat); (0xa3000, 3072%nat); (0x10b000, 2048%nat); (0x113000, 2048%nat); (0x11c000, 5120%nat)]%Z.
