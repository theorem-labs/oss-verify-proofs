(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
Section nulltail911_sec.
Variable js_10 : acs.
Definition nulltail911_cntx1 : plan := PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] (PX XMemset [] (PRun [] PExit)))))))))))))))))))).
Definition nulltail911_cntarm2 : plan := PRun [672804] (PRespell 8 (EMd Instr.M_MUL (ELit 2) (EAlu Instr.ALU_SLTU (EBlob true 8 1 1) (ELit 9223372036854775808))) (PHavoc [1; 10; 11; 5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PMerge 10))).
Definition nulltail911_r0_3_fb1 : plan := dec_plan (PE [nulltail911_cntx1] [] [e_sp0] [] [] []) "&0'#1000$?#0,$40,#0,$40,#0,$40,#0,$40,#0,1#540=0#7~-8<8,8#0,$41,#0,1#777?<&3'#1000$?#77:28,9,=,>,?,10,11,5,6,7,1<,9;#0,$42,#0,%<#0,$0#0,$=#0,$=#0,$42,#0,1#552:<$49,1#8#0,1#:442<#1},8#1,1^#7#???????????????!!#0,$0#0,$=#0,$="%pstring.
Definition nulltail911_r0_3 : plan := PRun [672676] (PVia 10 js_10 75 (PSplit (EBlob true 8 1 1) 9223372036854775807 nulltail911_cntarm2 nulltail911_cntarm2) (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 10))) 36703) 4046 nulltail911_r0_3_fb1 nulltail911_r0_3_fb1)).
Definition nulltail911 : plan := PBump 59 (PZoneHull (escale 4096 (EVar 31)) (PShDisj (escale 4096 (EVar 31)) (ELit 11571200) (escale 4096 (EVar 27)) (ELit 137439023104) nulltail911_r0_3)).
End nulltail911_sec.
Definition nulltail911_ranges : list (Z * nat) := [(0x4e000, 3072%nat); (0x52000, 5120%nat); (0x5e000, 2048%nat); (0x76000, 4096%nat); (0x7c000, 10240%nat); (0x87000, 5120%nat); (0x92000, 7168%nat); (0xa4000, 2048%nat); (0x10b000, 2048%nat); (0x113000, 3072%nat); (0x11d000, 4096%nat)]%Z.
