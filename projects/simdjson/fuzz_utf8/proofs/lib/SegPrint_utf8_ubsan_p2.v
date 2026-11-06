(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition PSEG_IN : acs := {| a_ss := SS 242512 [(ELit 0);
   (ELit 242340);
   (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (ELit (-208)));
   (ELit 67584);
   (ELit 973432);
   (EVar 64);
   (EVar 65);
   (EVar 66);
   (EVar 67);
   (EVar 68);
   (EVar 69);
   (ELit 0);
   (EVar 70);
   (EVar 71);
   (EVar 72);
   (EVar 73);
   (EVar 74);
   (EVar 75);
   (EVar 76);
   (EVar 77);
   (EVar 78);
   (EVar 79);
   (EVar 80);
   (EVar 81);
   (EVar 82);
   (EVar 83);
   (EVar 84);
   (EVar 85);
   (EVar 86);
   (EVar 87);
   (EVar 88);
   (EVar 89)] [] [KRange (EVar 1) 2 2;
   KRange (EVar 3) 0 131071;
   KRange (EVar 7) 1 4095;
   KRange (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 3;
   KWord {| a_base := ELit 0; a_off := 898632 |} 4 (ELit 5);
   KWord {| a_base := ELit 0; a_off := 898672 |} 8 (ELit 1107560);
   KWord {| a_base := ELit 0; a_off := 898664 |} 8 (ELit 1108584);
   KWord {| a_base := ELit 0; a_off := 898776 |} 4 (ELit 18446744073709551615);
   KRange (EVar 1) 2 2;
   KRange (EVar 3) 0 131071;
   KRange (EVar 7) 1 4095;
   KRange (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 1 32767;
   KRange (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 3;
   KRange (EVar 1) 2 2;
   KRange (EVar 3) 0 131071;
   KRange (EVar 7) 1 4095;
   KWord {| a_base := ELit 0; a_off := 1105128 |} 8 (EVar 90);
   KWord {| a_base := ELit 0; a_off := 1105129 |} 1 (ELit 0);
   KRange (EVar 0) 4294901760 4294967295;
   KRange (EVar 6) 0 2047;
   KRange (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 4)) (EMd Instr.M_MUL (ELit 16) (EVar 6)))))) (ELit 200)) 140735340871872 140737488355328;
   KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EVar 4) (EMd Instr.M_MUL (ELit 2) (EVar 6)))))) 17591917608961 17592186044393;
   KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) 140735340871680 140737488355136;
   KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 2) (EVar 6))) 17591917608960 17592186044392;
   KRange (EVar 1) 1 1024;
   KRange (EVar 2) 0 256;
   KRange (EVar 3) 0 131071;
   KRange (EVar 7) 0 131071;
   KRange (EVar 8) 0 4294967294;
   KRange (EVar 9) 4397 2101549;
   KRange (EVar 4) 0 280000;
   KRange (EVar 5) 271 524559;
   KWr {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6)); a_off := -8388608 |} (ELit 8388608);
   KWr {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 4)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))); a_off := 184 |} (ELit 16);
   KImg 68784 68792;
   KImg 137016 137024;
   KImg 137136 137144;
   KImg 137240 137248;
   KImg 893032 893040;
   KImg 898728 898736;
   KImg 898772 898776;
   KImg 1107561 1110016;
   KWr {| a_base := ELit 0; a_off := 868352 |} (ELit 241664)] 156%nat;
   a_maps := [{| am_base := EVar 92; am_len := EVar 93; am_kind := KRW |}; {| am_base := EVar 94; am_len := EVar 95; am_kind := KRW |}; {| am_base := EVar 96; am_len := EVar 97; am_kind := KRW |}; {| am_base := EVar 98; am_len := EVar 99; am_kind := KRW |}; {| am_base := EVar 100; am_len := EVar 101; am_kind := KRW |}; {| am_base := EVar 102; am_len := EVar 103; am_kind := KRW |}; {| am_base := EVar 104; am_len := EVar 105; am_kind := KRW |}; {| am_base := EVar 106; am_len := EVar 107; am_kind := KRW |}; {| am_base := EVar 108; am_len := EVar 109; am_kind := KRW |}; {| am_base := EVar 110; am_len := EVar 111; am_kind := KRW |}; {| am_base := EVar 112; am_len := EVar 113; am_kind := KRW |}; {| am_base := EVar 114; am_len := EVar 115; am_kind := KRW |}]; a_totsz := 1099511627776; a_ylo := 0; a_eager := 1099511627776; a_vis := [(EVar 116, EVar 117); (EVar 118, EVar 119); (EVar 120, EVar 121); (EVar 122, EVar 123); (EVar 124, EVar 125); (EVar 126, EVar 127); (EVar 128, EVar 129); (EVar 130, EVar 131); (EVar 132, EVar 133); (EVar 134, EVar 135); (EVar 136, EVar 137); (EVar 138, EVar 139); (EVar 140, EVar 141); (EVar 142, EVar 143); (EVar 144, EVar 145); (EVar 146, EVar 147)]; a_ghost := [(EVar 148, EVar 149); (EVar 150, EVar 151); (EVar 152, EVar 153); (EVar 154, EVar 155)]; a_abytes := 4398046511104;
   a_brk := EVar 91; a_fd := FdStd; a_tidset := true; a_props := [] |}.
Definition PSEG_W : list (saddr * expr) := [(SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (-1256), ELit 1048);
   (SA (ELit 0) 898632, ELit 4);
   (SA (ELit 0) 898672, ELit 8);
   (SA (ELit 0) 1107560, ELit 2456)].
Definition PSEG_OUT0 : acs := {| a_ss := SS 242340 [(ELit 0);
   (ELit 242340);
   (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))) (ELit (-208)));
   (ELit 67584);
   (ELit 973432);
   (EVar 237);
   (EVar 238);
   (EVar 239);
   (EVar 67);
   (EVar 68);
   (ELit 2);
   (EVar 90);
   (EVar 90);
   (EVar 243);
   (EVar 244);
   (EVar 245);
   (EVar 246);
   (EVar 247);
   (EVar 76);
   (EVar 77);
   (EVar 78);
   (EVar 79);
   (EVar 80);
   (EVar 81);
   (EVar 82);
   (EVar 83);
   (EVar 84);
   (EVar 85);
   (EVar 248);
   (EVar 249);
   (EVar 250);
   (EVar 251)] [] [KWord {| a_base := ELit 0; a_off := 898632 |} 4 (ELit 5);
   KWord {| a_base := ELit 0; a_off := 898672 |} 8 (ELit 1107562);
   KWord {| a_base := ELit 0; a_off := 1107561 |} 1 (ELit 10);
   KWord {| a_base := ELit 0; a_off := 1107560 |} 1 (ELit 48);
   KWr {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6)); a_off := -8388608 |} (ELit 8388608);
   KWr {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 4)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))); a_off := 184 |} (ELit 16);
   KImg 1107562 1110016;
   KWr {| a_base := ELit 0; a_off := 868352 |} (ELit 241664)] 252%nat;
   a_maps := [{| am_base := EVar 92; am_len := EVar 93; am_kind := KRW |}; {| am_base := EVar 94; am_len := EVar 95; am_kind := KRW |}; {| am_base := EVar 96; am_len := EVar 97; am_kind := KRW |}; {| am_base := EVar 98; am_len := EVar 99; am_kind := KRW |}; {| am_base := EVar 100; am_len := EVar 101; am_kind := KRW |}; {| am_base := EVar 102; am_len := EVar 103; am_kind := KRW |}; {| am_base := EVar 104; am_len := EVar 105; am_kind := KRW |}; {| am_base := EVar 106; am_len := EVar 107; am_kind := KRW |}; {| am_base := EVar 108; am_len := EVar 109; am_kind := KRW |}; {| am_base := EVar 110; am_len := EVar 111; am_kind := KRW |}; {| am_base := EVar 112; am_len := EVar 113; am_kind := KRW |}; {| am_base := EVar 114; am_len := EVar 115; am_kind := KRW |}]; a_totsz := 1099511627776; a_ylo := 0; a_eager := 1099511627776; a_vis := [(EVar 116, EVar 117); (EVar 118, EVar 119); (EVar 120, EVar 121); (EVar 122, EVar 123); (EVar 124, EVar 125); (EVar 126, EVar 127); (EVar 128, EVar 129); (EVar 130, EVar 131); (EVar 132, EVar 133); (EVar 134, EVar 135); (EVar 136, EVar 137); (EVar 138, EVar 139); (EVar 140, EVar 141); (EVar 142, EVar 143); (EVar 144, EVar 145); (EVar 146, EVar 147)]; a_ghost := [(EVar 148, EVar 149); (EVar 150, EVar 151); (EVar 152, EVar 153); (EVar 154, EVar 155)]; a_abytes := 4398046511104;
   a_brk := EVar 91; a_fd := FdStd; a_tidset := true; a_props := [] |}.
Definition pseg_body : plan := (PRun [] (PX XMemcpy [] (PRun [] (PX XMemcpy [] (PRun [] (PX XMemset [] (PRun [] (PX XMemcpy [] (PRun [] (PX XMemcpy [] (PRun [] (PX XMemcpy [] (PRun [242340] (PBreak 0%nat [(237%nat, EVar 237); (238%nat, EVar 238); (239%nat, EVar 239); (243%nat, EVar 243); (244%nat, EVar 244); (245%nat, EVar 245); (246%nat, EVar 246); (247%nat, EVar 247); (248%nat, EVar 248); (249%nat, EVar 249); (250%nat, EVar 250); (251%nat, EVar 251)])))))))))))))).
Definition SD_print : segdef := SEG 64%nat 156%nat PSEG_IN PSEG_W [PSEG_OUT0] (SHole 0) pseg_body 3000%nat 400000%nat.
