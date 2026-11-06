(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require CTabKB.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_5db48 : bv 32 := 0xfe010113.
Lemma F_5db48 : CTabKB.F 0x5db48 W_5db48.
Proof. vm_refl. Qed.
Lemma D_5db48 : CTabKB.D W_5db48 (OpImm ALU_ADD 2 2 4064).
Proof. vm_refl. Qed.
Definition W_5db4c : bv 32 := 0x00113c23.
Lemma F_5db4c : CTabKB.F 0x5db4c W_5db4c.
Proof. vm_refl. Qed.
Lemma D_5db4c : CTabKB.D W_5db4c (Store SZ8 2 1 24).
Proof. vm_refl. Qed.
Definition W_5db50 : bv 32 := 0x00813823.
Lemma F_5db50 : CTabKB.F 0x5db50 W_5db50.
Proof. vm_refl. Qed.
Lemma D_5db50 : CTabKB.D W_5db50 (Store SZ8 2 8 16).
Proof. vm_refl. Qed.
Definition W_5db54 : bv 32 := 0x00913423.
Lemma F_5db54 : CTabKB.F 0x5db54 W_5db54.
Proof. vm_refl. Qed.
Lemma D_5db54 : CTabKB.D W_5db54 (Store SZ8 2 9 8).
Proof. vm_refl. Qed.
Definition W_5db58 : bv 32 := 0x01213023.
Lemma F_5db58 : CTabKB.F 0x5db58 W_5db58.
Proof. vm_refl. Qed.
Lemma D_5db58 : CTabKB.D W_5db58 (Store SZ8 2 18 0).
Proof. vm_refl. Qed.
Definition W_5db5c : bv 32 := 0x02010413.
Lemma F_5db5c : CTabKB.F 0x5db5c W_5db5c.
Proof. vm_refl. Qed.
Lemma D_5db5c : CTabKB.D W_5db5c (OpImm ALU_ADD 8 2 32).
Proof. vm_refl. Qed.
Definition W_5db60 : bv 32 := 0x000d7517.
Lemma F_5db60 : CTabKB.F 0x5db60 W_5db60.
Proof. vm_refl. Qed.
Lemma D_5db60 : CTabKB.D W_5db60 (Auipc 10 215).
Proof. vm_refl. Qed.
Definition W_5db64 : bv 32 := 0x63850513.
Lemma F_5db64 : CTabKB.F 0x5db64 W_5db64.
Proof. vm_refl. Qed.
Lemma D_5db64 : CTabKB.D W_5db64 (OpImm ALU_ADD 10 10 1592).
Proof. vm_refl. Qed.
Definition W_5db68 : bv 32 := 0x200050ef.
Lemma F_5db68 : CTabKB.F 0x5db68 W_5db68.
Proof. vm_refl. Qed.
Lemma D_5db68 : CTabKB.D W_5db68 (Jal 1 20992).
Proof. vm_refl. Qed.
Definition W_5db6c : bv 32 := 0x00053483.
Lemma F_5db6c : CTabKB.F 0x5db6c W_5db6c.
Proof. vm_refl. Qed.
Lemma D_5db6c : CTabKB.D W_5db6c (Load SZ8 true 9 10 0).
Proof. vm_refl. Qed.
Definition W_5db70 : bv 32 := 0x08048863.
Lemma F_5db70 : CTabKB.F 0x5db70 W_5db70.
Proof. vm_refl. Qed.
Lemma D_5db70 : CTabKB.D W_5db70 (Branch BC_EQ 9 0 144).
Proof. vm_refl. Qed.
Definition W_5db74 : bv 32 := 0x0604c503.
Lemma F_5db74 : CTabKB.F 0x5db74 W_5db74.
Proof. vm_refl. Qed.
Lemma D_5db74 : CTabKB.D W_5db74 (Load SZ1 false 10 9 96).
Proof. vm_refl. Qed.
Definition W_5db78 : bv 32 := 0x0584b903.
Lemma F_5db78 : CTabKB.F 0x5db78 W_5db78.
Proof. vm_refl. Qed.
Lemma D_5db78 : CTabKB.D W_5db78 (Load SZ8 true 18 9 88).
Proof. vm_refl. Qed.
Definition W_5db7c : bv 32 := 0x00050863.
Lemma F_5db7c : CTabKB.F 0x5db7c W_5db7c.
Proof. vm_refl. Qed.
Lemma D_5db7c : CTabKB.D W_5db7c (Branch BC_EQ 10 0 16).
Proof. vm_refl. Qed.
Definition W_5db80 : bv 32 := 0x00048513.
Lemma F_5db80 : CTabKB.F 0x5db80 W_5db80.
Proof. vm_refl. Qed.
Lemma D_5db80 : CTabKB.D W_5db80 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5db84 : bv 32 := 0x00040593.
Lemma F_5db84 : CTabKB.F 0x5db84 W_5db84.
Proof. vm_refl. Qed.
Lemma D_5db84 : CTabKB.D W_5db84 (OpImm ALU_ADD 11 8 0).
Proof. vm_refl. Qed.
Definition W_5db88 : bv 32 := 0xd28ff0ef.
Lemma F_5db88 : CTabKB.F 0x5db88 W_5db88.
Proof. vm_refl. Qed.
Lemma D_5db88 : CTabKB.D W_5db88 (Jal 1 2094376).
Proof. vm_refl. Qed.
Definition W_5db8c : bv 32 := 0xff690593.
Lemma F_5db8c : CTabKB.F 0x5db8c W_5db8c.
Proof. vm_refl. Qed.
Lemma D_5db8c : CTabKB.D W_5db8c (OpImm ALU_ADD 11 18 4086).
Proof. vm_refl. Qed.
Definition W_5db90 : bv 32 := 0x00100513.
Lemma F_5db90 : CTabKB.F 0x5db90 W_5db90.
Proof. vm_refl. Qed.
Lemma D_5db90 : CTabKB.D W_5db90 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5db94 : bv 32 := 0x00b51533.
Lemma F_5db94 : CTabKB.F 0x5db94 W_5db94.
Proof. vm_refl. Qed.
Lemma D_5db94 : CTabKB.D W_5db94 (Op ALU_SLL 10 10 11).
Proof. vm_refl. Qed.
Definition W_5db98 : bv 32 := 0x0005061b.
Lemma F_5db98 : CTabKB.F 0x5db98 W_5db98.
Proof. vm_refl. Qed.
Lemma D_5db98 : CTabKB.D W_5db98 (OpImm32 12 10 0).
Proof. vm_refl. Qed.
Definition W_5db9c : bv 32 := 0x08c05263.
Lemma F_5db9c : CTabKB.F 0x5db9c W_5db9c.
Proof. vm_refl. Qed.
Lemma D_5db9c : CTabKB.D W_5db9c (Branch BC_GE 0 12 132).
Proof. vm_refl. Qed.
Definition W_5dba0 : bv 32 := 0x000016b7.
Lemma F_5dba0 : CTabKB.F 0x5dba0 W_5dba0.
Proof. vm_refl. Qed.
Lemma D_5dba0 : CTabKB.D W_5dba0 (Lui 13 1).
Proof. vm_refl. Qed.
Definition W_5dba4 : bv 32 := 0xff190613.
Lemma F_5dba4 : CTabKB.F 0x5dba4 W_5dba4.
Proof. vm_refl. Qed.
Lemma D_5dba4 : CTabKB.D W_5dba4 (OpImm ALU_ADD 12 18 4081).
Proof. vm_refl. Qed.
Definition W_5dba8 : bv 32 := 0x3c000713.
Lemma F_5dba8 : CTabKB.F 0x5dba8 W_5dba8.
Proof. vm_refl. Qed.
Lemma D_5dba8 : CTabKB.D W_5dba8 (OpImm ALU_ADD 14 0 960).
Proof. vm_refl. Qed.
Definition W_5dbac : bv 32 := 0xfff00793.
Lemma F_5dbac : CTabKB.F 0x5dbac W_5dbac.
Proof. vm_refl. Qed.
Lemma D_5dbac : CTabKB.D W_5dbac (OpImm ALU_ADD 15 0 4095).
Proof. vm_refl. Qed.
Definition W_5dbb0 : bv 32 := 0x00c71733.
Lemma F_5dbb0 : CTabKB.F 0x5dbb0 W_5dbb0.
Proof. vm_refl. Qed.
Lemma D_5dbb0 : CTabKB.D W_5dbb0 (Op ALU_SLL 14 14 12).
Proof. vm_refl. Qed.
Definition W_5dbb4 : bv 32 := 0x0204b603.
Lemma F_5dbb4 : CTabKB.F 0x5dbb4 W_5dbb4.
Proof. vm_refl. Qed.
Lemma D_5dbb4 : CTabKB.D W_5dbb4 (Load SZ8 true 12 9 32).
Proof. vm_refl. Qed.
Definition W_5dbb8 : bv 32 := 0x00b797b3.
Lemma F_5dbb8 : CTabKB.F 0x5dbb8 W_5dbb8.
Proof. vm_refl. Qed.
Lemma D_5dbb8 : CTabKB.D W_5dbb8 (Op ALU_SLL 15 15 11).
Proof. vm_refl. Qed.
Definition W_5dbbc : bv 32 := 0xfff50813.
Lemma F_5dbbc : CTabKB.F 0x5dbbc W_5dbbc.
Proof. vm_refl. Qed.
Lemma D_5dbbc : CTabKB.D W_5dbbc (OpImm ALU_ADD 16 10 4095).
Proof. vm_refl. Qed.
Definition W_5dbc0 : bv 32 := 0x00d485b3.
Lemma F_5dbc0 : CTabKB.F 0x5dbc0 W_5dbc0.
Proof. vm_refl. Qed.
Lemma D_5dbc0 : CTabKB.D W_5dbc0 (Op ALU_ADD 11 9 13).
Proof. vm_refl. Qed.
Definition W_5dbc4 : bv 32 := 0x00e586b3.
Lemma F_5dbc4 : CTabKB.F 0x5dbc4 W_5dbc4.
Proof. vm_refl. Qed.
Lemma D_5dbc4 : CTabKB.D W_5dbc4 (Op ALU_ADD 13 11 14).
Proof. vm_refl. Qed.
Definition W_5dbc8 : bv 32 := 0xfff7c713.
Lemma F_5dbc8 : CTabKB.F 0x5dbc8 W_5dbc8.
Proof. vm_refl. Qed.
Lemma D_5dbc8 : CTabKB.D W_5dbc8 (OpImm ALU_XOR 14 15 4095).
Proof. vm_refl. Qed.
Definition W_5dbcc : bv 32 := 0x02081813.
Lemma F_5dbcc : CTabKB.F 0x5dbcc W_5dbcc.
Proof. vm_refl. Qed.
Lemma D_5dbcc : CTabKB.D W_5dbcc (ShiftImm ALU_SLL 16 16 32).
Proof. vm_refl. Qed.
Definition W_5dbd0 : bv 32 := 0x02085793.
Lemma F_5dbd0 : CTabKB.F 0x5dbd0 W_5dbd0.
Proof. vm_refl. Qed.
Lemma D_5dbd0 : CTabKB.D W_5dbd0 (ShiftImm ALU_SRL 15 16 32).
Proof. vm_refl. Qed.
Definition W_5dbd4 : bv 32 := 0x00f607b3.
Lemma F_5dbd4 : CTabKB.F 0x5dbd4 W_5dbd4.
Proof. vm_refl. Qed.
Lemma D_5dbd4 : CTabKB.D W_5dbd4 (Op ALU_ADD 15 12 15).
Proof. vm_refl. Qed.
Definition W_5dbd8 : bv 32 := 0x00178813.
Lemma F_5dbd8 : CTabKB.F 0x5dbd8 W_5dbd8.
Proof. vm_refl. Qed.
Lemma D_5dbd8 : CTabKB.D W_5dbd8 (OpImm ALU_ADD 16 15 1).
Proof. vm_refl. Qed.
Definition W_5dbdc : bv 32 := 0x00e678b3.
Lemma F_5dbdc : CTabKB.F 0x5dbdc W_5dbdc.
Proof. vm_refl. Qed.
Lemma D_5dbdc : CTabKB.D W_5dbdc (Op ALU_AND 17 12 14).
Proof. vm_refl. Qed.
Definition W_5dbe0 : bv 32 := 0x011687b3.
Lemma F_5dbe0 : CTabKB.F 0x5dbe0 W_5dbe0.
Proof. vm_refl. Qed.
Lemma D_5dbe0 : CTabKB.D W_5dbe0 (Op ALU_ADD 15 13 17).
Proof. vm_refl. Qed.
Definition W_5dbe4 : bv 32 := 0x0007c283.
Lemma F_5dbe4 : CTabKB.F 0x5dbe4 W_5dbe4.
Proof. vm_refl. Qed.
Lemma D_5dbe4 : CTabKB.D W_5dbe4 (Load SZ1 false 5 15 0).
Proof. vm_refl. Qed.
Definition W_5dbe8 : bv 32 := 0x06028663.
Lemma F_5dbe8 : CTabKB.F 0x5dbe8 W_5dbe8.
Proof. vm_refl. Qed.
Lemma D_5dbe8 : CTabKB.D W_5dbe8 (Branch BC_EQ 5 0 108).
Proof. vm_refl. Qed.
Definition W_5dbec : bv 32 := 0xfff5051b.
Lemma F_5dbec : CTabKB.F 0x5dbec W_5dbec.
Proof. vm_refl. Qed.
Lemma D_5dbec : CTabKB.D W_5dbec (OpImm32 10 10 4095).
Proof. vm_refl. Qed.
Definition W_5dbf0 : bv 32 := 0x00160613.
Lemma F_5dbf0 : CTabKB.F 0x5dbf0 W_5dbf0.
Proof. vm_refl. Qed.
Lemma D_5dbf0 : CTabKB.D W_5dbf0 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5dbf4 : bv 32 := 0xfe0514e3.
Lemma F_5dbf4 : CTabKB.F 0x5dbf4 W_5dbf4.
Proof. vm_refl. Qed.
Lemma D_5dbf4 : CTabKB.D W_5dbf4 (Branch BC_NE 10 0 8168).
Proof. vm_refl. Qed.
Definition W_5dbf8 : bv 32 := 0x0304b023.
Lemma F_5dbf8 : CTabKB.F 0x5dbf8 W_5dbf8.
Proof. vm_refl. Qed.
Lemma D_5dbf8 : CTabKB.D W_5dbf8 (Store SZ8 9 16 32).
Proof. vm_refl. Qed.
Definition W_5dbfc : bv 32 := 0x0400006f.
Lemma F_5dbfc : CTabKB.F 0x5dbfc W_5dbfc.
Proof. vm_refl. Qed.
Lemma D_5dbfc : CTabKB.D W_5dbfc (Jal 0 64).
Proof. vm_refl. Qed.
Definition W_5dc00 : bv 32 := 0x000d6517.
Lemma F_5dc00 : CTabKB.F 0x5dc00 W_5dc00.
Proof. vm_refl. Qed.
Lemma D_5dc00 : CTabKB.D W_5dc00 (Auipc 10 214).
Proof. vm_refl. Qed.
Definition W_5dc04 : bv 32 := 0x7f853503.
Lemma F_5dc04 : CTabKB.F 0x5dc04 W_5dc04.
Proof. vm_refl. Qed.
Lemma D_5dc04 : CTabKB.D W_5dc04 (Load SZ8 true 10 10 2040).
Proof. vm_refl. Qed.
Definition W_5dc08 : bv 32 := 0x00052503.
Lemma F_5dc08 : CTabKB.F 0x5dc08 W_5dc08.
Proof. vm_refl. Qed.
Lemma D_5dc08 : CTabKB.D W_5dc08 (Load SZ4 true 10 10 0).
Proof. vm_refl. Qed.
Definition W_5dc0c : bv 32 := 0x02050863.
Lemma F_5dc0c : CTabKB.F 0x5dc0c W_5dc0c.
Proof. vm_refl. Qed.
Lemma D_5dc0c : CTabKB.D W_5dc0c (Branch BC_EQ 10 0 48).
Proof. vm_refl. Qed.
Definition W_5dc10 : bv 32 := 0x64c250ef.
Lemma F_5dc10 : CTabKB.F 0x5dc10 W_5dc10.
Proof. vm_refl. Qed.
Lemma D_5dc10 : CTabKB.D W_5dc10 (Jal 1 153164).
Proof. vm_refl. Qed.
Definition W_5dc14 : bv 32 := 0x02050463.
Lemma F_5dc14 : CTabKB.F 0x5dc14 W_5dc14.
Proof. vm_refl. Qed.
Lemma D_5dc14 : CTabKB.D W_5dc14 (Branch BC_EQ 10 0 40).
Proof. vm_refl. Qed.
Definition W_5dc18 : bv 32 := 0x02850583.
Lemma F_5dc18 : CTabKB.F 0x5dc18 W_5dc18.
Proof. vm_refl. Qed.
Lemma D_5dc18 : CTabKB.D W_5dc18 (Load SZ1 true 11 10 40).
Proof. vm_refl. Qed.
Definition W_5dc1c : bv 32 := 0x0c058e63.
Lemma F_5dc1c : CTabKB.F 0x5dc1c W_5dc1c.
Proof. vm_refl. Qed.
Lemma D_5dc1c : CTabKB.D W_5dc1c (Branch BC_EQ 11 0 220).
Proof. vm_refl. Qed.
Definition W_5dc20 : bv 32 := 0x00000513.
Lemma F_5dc20 : CTabKB.F 0x5dc20 W_5dc20.
Proof. vm_refl. Qed.
Lemma D_5dc20 : CTabKB.D W_5dc20 (OpImm ALU_ADD 10 0 0).
Proof. vm_refl. Qed.
Definition W_5dc24 : bv 32 := 0x01813083.
Lemma F_5dc24 : CTabKB.F 0x5dc24 W_5dc24.
Proof. vm_refl. Qed.
Lemma D_5dc24 : CTabKB.D W_5dc24 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5dc28 : bv 32 := 0x01013403.
Lemma F_5dc28 : CTabKB.F 0x5dc28 W_5dc28.
Proof. vm_refl. Qed.
Lemma D_5dc28 : CTabKB.D W_5dc28 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5dc2c : bv 32 := 0x00813483.
Lemma F_5dc2c : CTabKB.F 0x5dc2c W_5dc2c.
Proof. vm_refl. Qed.
Lemma D_5dc2c : CTabKB.D W_5dc2c (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5dc30 : bv 32 := 0x00013903.
Lemma F_5dc30 : CTabKB.F 0x5dc30 W_5dc30.
Proof. vm_refl. Qed.
Lemma D_5dc30 : CTabKB.D W_5dc30 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5dc34 : bv 32 := 0x02010113.
Lemma F_5dc34 : CTabKB.F 0x5dc34 W_5dc34.
Proof. vm_refl. Qed.
Lemma D_5dc34 : CTabKB.D W_5dc34 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5dc38 : bv 32 := 0x00008067.
Lemma F_5dc38 : CTabKB.F 0x5dc38 W_5dc38.
Proof. vm_refl. Qed.
Lemma D_5dc38 : CTabKB.D W_5dc38 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5dc3c : bv 32 := 0x01813083.
Lemma F_5dc3c : CTabKB.F 0x5dc3c W_5dc3c.
Proof. vm_refl. Qed.
Lemma D_5dc3c : CTabKB.D W_5dc3c (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5dc40 : bv 32 := 0x01013403.
Lemma F_5dc40 : CTabKB.F 0x5dc40 W_5dc40.
Proof. vm_refl. Qed.
Lemma D_5dc40 : CTabKB.D W_5dc40 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5dc44 : bv 32 := 0x00813483.
Lemma F_5dc44 : CTabKB.F 0x5dc44 W_5dc44.
Proof. vm_refl. Qed.
Lemma D_5dc44 : CTabKB.D W_5dc44 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5dc48 : bv 32 := 0x00013903.
Lemma F_5dc48 : CTabKB.F 0x5dc48 W_5dc48.
Proof. vm_refl. Qed.
Lemma D_5dc48 : CTabKB.D W_5dc48 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5dc4c : bv 32 := 0x02010113.
Lemma F_5dc4c : CTabKB.F 0x5dc4c W_5dc4c.
Proof. vm_refl. Qed.
Lemma D_5dc4c : CTabKB.D W_5dc4c (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5dc50 : bv 32 := 0x00008067.
Lemma F_5dc50 : CTabKB.F 0x5dc50 W_5dc50.
Proof. vm_refl. Qed.
Lemma D_5dc50 : CTabKB.D W_5dc50 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5dc54 : bv 32 := 0x00160613.
Lemma F_5dc54 : CTabKB.F 0x5dc54 W_5dc54.
Proof. vm_refl. Qed.
Lemma D_5dc54 : CTabKB.D W_5dc54 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5dc58 : bv 32 := 0x00100513.
Lemma F_5dc58 : CTabKB.F 0x5dc58 W_5dc58.
Proof. vm_refl. Qed.
Lemma D_5dc58 : CTabKB.D W_5dc58 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5dc5c : bv 32 := 0xffb90693.
Lemma F_5dc5c : CTabKB.F 0x5dc5c W_5dc5c.
Proof. vm_refl. Qed.
Lemma D_5dc5c : CTabKB.D W_5dc5c (OpImm ALU_ADD 13 18 4091).
Proof. vm_refl. Qed.
Definition W_5dc60 : bv 32 := 0x02c4b023.
Lemma F_5dc60 : CTabKB.F 0x5dc60 W_5dc60.
Proof. vm_refl. Qed.
Lemma D_5dc60 : CTabKB.D W_5dc60 (Store SZ8 9 12 32).
Proof. vm_refl. Qed.
Definition W_5dc64 : bv 32 := 0x00a78023.
Lemma F_5dc64 : CTabKB.F 0x5dc64 W_5dc64.
Proof. vm_refl. Qed.
Lemma D_5dc64 : CTabKB.D W_5dc64 (Store SZ1 15 10 0).
Proof. vm_refl. Qed.
Definition W_5dc68 : bv 32 := 0x00d51533.
Lemma F_5dc68 : CTabKB.F 0x5dc68 W_5dc68.
Proof. vm_refl. Qed.
Lemma D_5dc68 : CTabKB.D W_5dc68 (Op ALU_SLL 10 10 13).
Proof. vm_refl. Qed.
Definition W_5dc6c : bv 32 := 0x00400613.
Lemma F_5dc6c : CTabKB.F 0x5dc6c W_5dc6c.
Proof. vm_refl. Qed.
Lemma D_5dc6c : CTabKB.D W_5dc6c (OpImm ALU_ADD 12 0 4).
Proof. vm_refl. Qed.
Definition W_5dc70 : bv 32 := 0x00a89893.
Lemma F_5dc70 : CTabKB.F 0x5dc70 W_5dc70.
Proof. vm_refl. Qed.
Lemma D_5dc70 : CTabKB.D W_5dc70 (ShiftImm ALU_SLL 17 17 10).
Proof. vm_refl. Qed.
Definition W_5dc74 : bv 32 := 0x01261633.
Lemma F_5dc74 : CTabKB.F 0x5dc74 W_5dc74.
Proof. vm_refl. Qed.
Lemma D_5dc74 : CTabKB.D W_5dc74 (Op ALU_SLL 12 12 18).
Proof. vm_refl. Qed.
Definition W_5dc78 : bv 32 := 0x00a58533.
Lemma F_5dc78 : CTabKB.F 0x5dc78 W_5dc78.
Proof. vm_refl. Qed.
Lemma D_5dc78 : CTabKB.D W_5dc78 (Op ALU_ADD 10 11 10).
Proof. vm_refl. Qed.
Definition W_5dc7c : bv 32 := 0x01160633.
Lemma F_5dc7c : CTabKB.F 0x5dc7c W_5dc7c.
Proof. vm_refl. Qed.
Lemma D_5dc7c : CTabKB.D W_5dc7c (Op ALU_ADD 12 12 17).
Proof. vm_refl. Qed.
Definition W_5dc80 : bv 32 := 0x00c504b3.
Lemma F_5dc80 : CTabKB.F 0x5dc80 W_5dc80.
Proof. vm_refl. Qed.
Lemma D_5dc80 : CTabKB.D W_5dc80 (Op ALU_ADD 9 10 12).
Proof. vm_refl. Qed.
Definition W_5dc84 : bv 32 := 0x0084bc23.
Lemma F_5dc84 : CTabKB.F 0x5dc84 W_5dc84.
Proof. vm_refl. Qed.
Lemma D_5dc84 : CTabKB.D W_5dc84 (Store SZ8 9 8 24).
Proof. vm_refl. Qed.
Definition W_5dc88 : bv 32 := 0x3ef4bc23.
Lemma F_5dc88 : CTabKB.F 0x5dc88 W_5dc88.
Proof. vm_refl. Qed.
Lemma D_5dc88 : CTabKB.D W_5dc88 (Store SZ8 9 15 1016).
Proof. vm_refl. Qed.
Definition W_5dc8c : bv 32 := 0x00048513.
Lemma F_5dc8c : CTabKB.F 0x5dc8c W_5dc8c.
Proof. vm_refl. Qed.
Lemma D_5dc8c : CTabKB.D W_5dc8c (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5dc90 : bv 32 := 0x084000ef.
Lemma F_5dc90 : CTabKB.F 0x5dc90 W_5dc90.
Proof. vm_refl. Qed.
Lemma D_5dc90 : CTabKB.D W_5dc90 (Jal 1 132).
Proof. vm_refl. Qed.
Definition W_5dc94 : bv 32 := 0x00050593.
Lemma F_5dc94 : CTabKB.F 0x5dc94 W_5dc94.
Proof. vm_refl. Qed.
Lemma D_5dc94 : CTabKB.D W_5dc94 (OpImm ALU_ADD 11 10 0).
Proof. vm_refl. Qed.
Definition W_5dc98 : bv 32 := 0x00048513.
Lemma F_5dc98 : CTabKB.F 0x5dc98 W_5dc98.
Proof. vm_refl. Qed.
Lemma D_5dc98 : CTabKB.D W_5dc98 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5dc9c : bv 32 := 0x00000613.
Lemma F_5dc9c : CTabKB.F 0x5dc9c W_5dc9c.
Proof. vm_refl. Qed.
Lemma D_5dc9c : CTabKB.D W_5dc9c (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_5dca0 : bv 32 := 0x0005b023.
Lemma F_5dca0 : CTabKB.F 0x5dca0 W_5dca0.
Proof. vm_refl. Qed.
Lemma D_5dca0 : CTabKB.D W_5dca0 (Store SZ8 11 0 0).
Proof. vm_refl. Qed.
Definition W_5dca4 : bv 32 := 0x0005b423.
Lemma F_5dca4 : CTabKB.F 0x5dca4 W_5dca4.
Proof. vm_refl. Qed.
Lemma D_5dca4 : CTabKB.D W_5dca4 (Store SZ8 11 0 8).
Proof. vm_refl. Qed.
Definition W_5dca8 : bv 32 := 0x0005b823.
Lemma F_5dca8 : CTabKB.F 0x5dca8 W_5dca8.
Proof. vm_refl. Qed.
Lemma D_5dca8 : CTabKB.D W_5dca8 (Store SZ8 11 0 16).
Proof. vm_refl. Qed.
Definition W_5dcac : bv 32 := 0x0005bc23.
Lemma F_5dcac : CTabKB.F 0x5dcac W_5dcac.
Proof. vm_refl. Qed.
Lemma D_5dcac : CTabKB.D W_5dcac (Store SZ8 11 0 24).
Proof. vm_refl. Qed.
Definition W_5dcb0 : bv 32 := 0x0205b023.
Lemma F_5dcb0 : CTabKB.F 0x5dcb0 W_5dcb0.
Proof. vm_refl. Qed.
Lemma D_5dcb0 : CTabKB.D W_5dcb0 (Store SZ8 11 0 32).
Proof. vm_refl. Qed.
Definition W_5dcb4 : bv 32 := 0x0205b423.
Lemma F_5dcb4 : CTabKB.F 0x5dcb4 W_5dcb4.
Proof. vm_refl. Qed.
Lemma D_5dcb4 : CTabKB.D W_5dcb4 (Store SZ8 11 0 40).
Proof. vm_refl. Qed.
Definition W_5dcb8 : bv 32 := 0x0205b823.
Lemma F_5dcb8 : CTabKB.F 0x5dcb8 W_5dcb8.
Proof. vm_refl. Qed.
Lemma D_5dcb8 : CTabKB.D W_5dcb8 (Store SZ8 11 0 48).
Proof. vm_refl. Qed.
Definition W_5dcbc : bv 32 := 0x0205bc23.
Lemma F_5dcbc : CTabKB.F 0x5dcbc W_5dcbc.
Proof. vm_refl. Qed.
Lemma D_5dcbc : CTabKB.D W_5dcbc (Store SZ8 11 0 56).
Proof. vm_refl. Qed.
Definition W_5dcc0 : bv 32 := 0x0405b023.
Lemma F_5dcc0 : CTabKB.F 0x5dcc0 W_5dcc0.
Proof. vm_refl. Qed.
Lemma D_5dcc0 : CTabKB.D W_5dcc0 (Store SZ8 11 0 64).
Proof. vm_refl. Qed.
Definition W_5dcc4 : bv 32 := 0x0405b423.
Lemma F_5dcc4 : CTabKB.F 0x5dcc4 W_5dcc4.
Proof. vm_refl. Qed.
Lemma D_5dcc4 : CTabKB.D W_5dcc4 (Store SZ8 11 0 72).
Proof. vm_refl. Qed.
Definition W_5dcc8 : bv 32 := 0x0405b823.
Lemma F_5dcc8 : CTabKB.F 0x5dcc8 W_5dcc8.
Proof. vm_refl. Qed.
Lemma D_5dcc8 : CTabKB.D W_5dcc8 (Store SZ8 11 0 80).
Proof. vm_refl. Qed.
Definition W_5dccc : bv 32 := 0x0405bc23.
Lemma F_5dccc : CTabKB.F 0x5dccc W_5dccc.
Proof. vm_refl. Qed.
Lemma D_5dccc : CTabKB.D W_5dccc (Store SZ8 11 0 88).
Proof. vm_refl. Qed.
Definition W_5dcd0 : bv 32 := 0x0605b023.
Lemma F_5dcd0 : CTabKB.F 0x5dcd0 W_5dcd0.
Proof. vm_refl. Qed.
Lemma D_5dcd0 : CTabKB.D W_5dcd0 (Store SZ8 11 0 96).
Proof. vm_refl. Qed.
Definition W_5dcd4 : bv 32 := 0x0605b423.
Lemma F_5dcd4 : CTabKB.F 0x5dcd4 W_5dcd4.
Proof. vm_refl. Qed.
Lemma D_5dcd4 : CTabKB.D W_5dcd4 (Store SZ8 11 0 104).
Proof. vm_refl. Qed.
Definition W_5dcd8 : bv 32 := 0x0605b823.
Lemma F_5dcd8 : CTabKB.F 0x5dcd8 W_5dcd8.
Proof. vm_refl. Qed.
Lemma D_5dcd8 : CTabKB.D W_5dcd8 (Store SZ8 11 0 112).
Proof. vm_refl. Qed.
Definition W_5dcdc : bv 32 := 0x0605bc23.
Lemma F_5dcdc : CTabKB.F 0x5dcdc W_5dcdc.
Proof. vm_refl. Qed.
Lemma D_5dcdc : CTabKB.D W_5dcdc (Store SZ8 11 0 120).
Proof. vm_refl. Qed.
Definition W_5dce0 : bv 32 := 0x01813083.
Lemma F_5dce0 : CTabKB.F 0x5dce0 W_5dce0.
Proof. vm_refl. Qed.
Lemma D_5dce0 : CTabKB.D W_5dce0 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5dce4 : bv 32 := 0x01013403.
Lemma F_5dce4 : CTabKB.F 0x5dce4 W_5dce4.
Proof. vm_refl. Qed.
Lemma D_5dce4 : CTabKB.D W_5dce4 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5dce8 : bv 32 := 0x00813483.
Lemma F_5dce8 : CTabKB.F 0x5dce8 W_5dce8.
Proof. vm_refl. Qed.
Lemma D_5dce8 : CTabKB.D W_5dce8 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5dcec : bv 32 := 0x00013903.
Lemma F_5dcec : CTabKB.F 0x5dcec W_5dcec.
Proof. vm_refl. Qed.
Lemma D_5dcec : CTabKB.D W_5dcec (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5dcf0 : bv 32 := 0x02010113.
Lemma F_5dcf0 : CTabKB.F 0x5dcf0 W_5dcf0.
Proof. vm_refl. Qed.
Lemma D_5dcf0 : CTabKB.D W_5dcf0 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5dcf4 : bv 32 := 0x00008067.
Lemma F_5dcf4 : CTabKB.F 0x5dcf4 W_5dcf4.
Proof. vm_refl. Qed.
Lemma D_5dcf4 : CTabKB.D W_5dcf4 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5dcf8 : bv 32 := 0x04853483.
Lemma F_5dcf8 : CTabKB.F 0x5dcf8 W_5dcf8.
Proof. vm_refl. Qed.
Lemma D_5dcf8 : CTabKB.D W_5dcf8 (Load SZ8 true 9 10 72).
Proof. vm_refl. Qed.
