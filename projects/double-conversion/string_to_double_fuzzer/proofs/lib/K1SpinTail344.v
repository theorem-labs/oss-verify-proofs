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

Definition k1spintail344_tospin1 : plan := dec_plan (PE [] [] [] [] [] []) "#0,$40,#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,$40,#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,$="%pstring.

Definition k1spintail344_tospin2 : plan := dec_plan (PE [] [] [] [] [] []) "#0,$40,#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,$40,#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,$="%pstring.

Definition k1spintail344_tospin3 : plan := dec_plan (PE [] [] [] [] [] []) "#0,$40,#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,$40,#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,$="%pstring.

Definition k1spintail344_tospin4 : plan := dec_plan (PE [] [] [] [] [] []) "#0,$40,#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;200#>,15#!#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,1#8;390%4#8;368,1,10#0,$="%pstring.

Definition k1spintail344 : plan := PBump 39 (PZones (escale 4096 (EVar 15)) (PCase2 (EVar 15) 4095 k1spintail344_tospin1 (PCase2 (EVar 15) 65535 k1spintail344_tospin2 (PCase2 (EVar 15) 522231 k1spintail344_tospin3 k1spintail344_tospin4)))).
