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

Definition spintail44_tospin1 : plan := dec_plan (PE [] [] [] [] [] []) "#0,$40,#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,$40,#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,$="%pstring.

Definition spintail44_tospin2 : plan := dec_plan (PE [] [] [] [] [] []) "#0,$40,#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,$40,#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,$="%pstring.

Definition spintail44_tospin3 : plan := dec_plan (PE [] [] [] [] [] []) "#0,$40,#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,$40,#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,$="%pstring.

Definition spintail44_tospin4 : plan := dec_plan (PE [] [] [] [] [] []) "#0,$40,#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,$="%pstring.

Definition spintail44 : plan := PBump 38 (PZones (escale 4096 (EVar 14)) (PCase2 (EVar 14) 4095 spintail44_tospin1 (PCase2 (EVar 14) 65535 spintail44_tospin2 (PCase2 (EVar 14) 522231 spintail44_tospin3 spintail44_tospin4)))).
