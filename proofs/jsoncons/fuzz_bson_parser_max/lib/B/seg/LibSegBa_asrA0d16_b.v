(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_ecee19_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_ecee19_b.ITR.
Definition IT : itab := SegItab_Ba_ecee19_b.IT.
Definition ENDS : list Z := [894976].
Definition STOPS1 : list Z := [894976] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 61; EAlu Instr.ALU_ADD (EVar 2) (ELit (-160)); EVar 3; EVar 4; EVar 62; EVar 63; EVar 64; EAlu Instr.ALU_ADD (EVar 2) (ELit 16); EAlu Instr.ALU_ADD (EVar 2) (ELit (-160)); (EMd Instr.M_MUL (ELit 32) (EVar 50)); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; EVar 18; EVar 36; EVar 20; EVar 21; EVar 38; EVar 23; EVar 24; EVar 25; EVar 26; ELit 2147450880; EVar 72; EVar 73; EVar 74; EVar 75].
Definition kn0 : list kentry := [KImg 65536 1282048;
   KWord (SA (ELit 0) 1309752) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1309760) 4 (ELit 1);
   KRange (EVar 2) 140735332487232 140737488355312;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-160)) (ELit 176);
   KRange (EVar 36) 6905856 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KWr (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 2) (-160)) (ELit 176) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KWord (SA (EVar 36) (280)) 8 (EVar 35);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KRange (EVar 2) 140735332487248 140737488355328;
   KWr (SA (EVar 2) (-160)) (ELit 160);
   KDisj (SA (EVar 2) (-160)) (ELit 160) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (288)) 8 (ELit 0);
   KRange (EVar 45) 6905856 140737488355056;
   KAlign (EVar 45) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 45) 0) (ELit 272);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 45) (ELit 3)) 2147450880) (ELit 34);
   KWr (SA (EVar 45) 0) (ELit 272);
   KDisj (SA (EVar 2) (-160)) (ELit 160) (SA (EVar 45) 0) (ELit 272);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 45) 0) (ELit 272);
   KWord (SA (EVar 36) (240)) 8 (EVar 45);
   KWord (SA (EVar 36) (248)) 8 ((EAlu Instr.ALU_ADD (EVar 45) (ELit 16)));
   KWord (SA (EVar 45) (0)) 8 (ELit 1265968);
   KWord (SA (EVar 45) (16)) 8 (ELit 1265728);
   KWord (SA (EVar 45) (152)) 4 (ELit 0);
   KWord (SA (EVar 45) (156)) 4 (ELit 0);
   KWord (SA (EVar 45) (160)) 8 ((EAlu Instr.ALU_ADD (EVar 45) (ELit 16)));
   KZero (SA (ELit 0) 2147609123) (ELit 1);
   KZero (SA (ELit 0) 2147609104) (ELit 1);
   KRange (EVar 38) 16384 16384;
   KWord (SA (EVar 2) (-136)) 8 (EVar 37);
   KWord (SA (EVar 2) (-88)) 8 (EVar 27);
   KWord (SA (EVar 2) (-80)) 8 (EVar 26);
   KWord (SA (EVar 2) (-72)) 8 (EVar 25);
   KWord (SA (EVar 2) (-64)) 8 (EVar 24);
   KWord (SA (EVar 2) (-56)) 8 (EVar 23);
   KWord (SA (EVar 2) (-48)) 8 (EVar 22);
   KWord (SA (EVar 2) (-40)) 8 (EVar 21);
   KWord (SA (EVar 2) (-32)) 8 (EVar 20);
   KWord (SA (EVar 2) (-24)) 8 (EVar 19);
   KWord (SA (EVar 2) (-16)) 8 (EVar 18);
   KWord (SA (EVar 2) (-8)) 8 (EVar 9);
   KWord (SA (EVar 2) 0) 8 (EVar 8);
   KWord (SA (EVar 2) 8) 8 (EVar 1);
   KWord (SA (EVar 2) (-144)) 8 (ELit 0);
   KRange (EVar 50) 215808 4398046511102;
   KAlign (EVar 50) 4;
   KUnk (SA (EMd Instr.M_MUL (ELit 32) (EVar 50)) 0) (ELit 128);
   KWr (SA (EMd Instr.M_MUL (ELit 32) (EVar 50)) 0) (ELit 128);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EMd Instr.M_MUL (ELit 32) (EVar 50)) 0) (ELit 128);
   KWr (SA (EMd Instr.M_MUL (ELit 4) (EVar 50)) 2147450880) (ELit 16);
   KWord (SA (EMd Instr.M_MUL (ELit 32) (EVar 50)) 120) 8 (EVar 51);
   KRange (EVar 51) 4096 140737488355327;
   KWr (SA (EVar 51) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 51) 0) (ELit 1);
   KDisj (SA (EMd Instr.M_MUL (ELit 32) (EVar 50)) 0) (ELit 128) (SA (EVar 51) 0) (ELit 1);
   KDisj (SA (EVar 2) (-160)) (ELit 176) (SA (EMd Instr.M_MUL (ELit 32) (EVar 50)) 0) (ELit 128);
   KDisj (SA (EVar 2) (-160)) (ELit 176) (SA (EVar 51) 0) (ELit 1);
   KDisj (SA (EMd Instr.M_MUL (ELit 32) (EVar 50)) 0) (ELit 128) (SA (EMd Instr.M_MUL (ELit 4) (EVar 50)) 2147450880) (ELit 16);
   KDisj (SA (EVar 51) 0) (ELit 1) (SA (EMd Instr.M_MUL (ELit 4) (EVar 50)) 2147450880) (ELit 16);
   KDisj (SA (EVar 2) (-160)) (ELit 176) (SA (EMd Instr.M_MUL (ELit 4) (EVar 50)) 2147450880) (ELit 16);
   KDisj (SA (EMd Instr.M_MUL (ELit 32) (EVar 50)) 0) (ELit 128) (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 51) 0) (ELit 1) (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EMd Instr.M_MUL (ELit 4) (EVar 50)) 2147450880) (ELit 16) (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EMd Instr.M_MUL (ELit 4) (EVar 50)) 2147450880) (ELit 16) (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KDisj (SA (EMd Instr.M_MUL (ELit 32) (EVar 50)) 0) (ELit 128) (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KDisj (SA (EVar 51) 0) (ELit 1) (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KDisj (SA (EMd Instr.M_MUL (ELit 32) (EVar 50)) 0) (ELit 128) (SA (EVar 45) 0) (ELit 272);
   KDisj (SA (EVar 51) 0) (ELit 1) (SA (EVar 45) 0) (ELit 272);
   KDisj (SA (EMd Instr.M_MUL (ELit 4) (EVar 50)) 2147450880) (ELit 16) (SA (EVar 45) 0) (ELit 272);
   KDisj (SA (EMd Instr.M_MUL (ELit 4) (EVar 50)) 2147450880) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 45) (ELit 3)) 2147450880) (ELit 34);
   KDisj (SA (EMd Instr.M_MUL (ELit 32) (EVar 50)) 0) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar 45) (ELit 3)) 2147450880) (ELit 34);
   KDisj (SA (EVar 51) 0) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 45) (ELit 3)) 2147450880) (ELit 34);
   KRange (EVar 37) 4096 140737488338944].
Definition ss0 : sym_state := SS 716228 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-152), ELit 16); ((EVar 2), (-112), ELit 8); ((EMd Instr.M_MUL (ELit 32) (EVar 50)), (0), ELit 24); ((EMd Instr.M_MUL (ELit 32) (EVar 50)), (32), ELit 8); ((EMd Instr.M_MUL (ELit 4) (EVar 50)), (2147450880), ELit 12)].
Definition F0L : list SR.region := [((EVar 2), (-152), 16); ((EVar 2), (-112), 8); ((EMd Instr.M_MUL (ELit 32) (EVar 50)), (0), 24); ((EMd Instr.M_MUL (ELit 32) (EVar 50)), (32), 8); ((EMd Instr.M_MUL (ELit 4) (EVar 50)), (2147450880), 12)].
Definition BF : nat := 1000.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [894976; 894976])], (93, SS 894976 [ELit 0; ELit 717164; EAlu Instr.ALU_ADD (EVar 2) (ELit (-160)); EVar 3; EVar 4; EVar 62; EVar 63; EVar 64; EAlu Instr.ALU_ADD (EVar 2) (ELit 16); EAlu Instr.ALU_ADD (EVar 2) (ELit (-160)); EAlu Instr.ALU_ADD (EVar 45) (ELit 16); EVar 37; ELit 16384; ELit 894976; ELit 0; ELit 18446744073709551603; EMd Instr.M_MUL (ELit 32) (EVar 50); EVar 71; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit 288)) (ELit 3)) (ELit 2147450880); EVar 36; ELit 0; EVar 21; EAlu Instr.ALU_ADD (EVar 36) (ELit 240); EAlu Instr.ALU_ADD (EVar 36) (ELit 288); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit 240)) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4) (EVar 50)) (ELit 2147450880); EMd Instr.M_MUL (ELit 32) (EVar 50); ELit 2147450880; EVar 72; EVar 73; EVar 74; EVar 75] [] [KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32) (EVar 50)) (ELit 32)); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EMd Instr.M_MUL (ELit 32) (EVar 50)); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EMd Instr.M_MUL (ELit 32) (EVar 50)); KWord {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 32 |} 8 (EVar 38); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450891 |} 1 (ELit 18446744073709551603); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450890 |} 1 (ELit 18446744073709551603); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450889 |} 1 (ELit 18446744073709551603); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450888 |} 1 (ELit 18446744073709551608); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450883 |} 1 (ELit 18446744073709551601); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450882 |} 1 (ELit 18446744073709551601); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450881 |} 1 (ELit 18446744073709551601); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450880 |} 1 (ELit 18446744073709551601); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450887 |} 1 (ELit 18446744073709551602); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450886 |} 1 (ELit 18446744073709551602); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450885 |} 1 (ELit 18446744073709551602); KWord {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450884 |} 1 (ELit 0); KWord {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 16 |} 8 (ELit 716108); KWord {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 8 |} 8 (ELit 127274); KWord {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 0 |} 8 (ELit 1102416563); KImg 65536 1282048; KWord {| a_base := ELit 0; a_off := 1309752 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1309760 |} 4 (ELit 1); KRange (EVar 2) 140735332487232 140737488355312; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -160 |} (ELit 176); KRange (EVar 36) 6905856 140737488355032; KAlign (EVar 36) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 36; a_off := 0 |} (ELit 296); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit 8)) (ELit 3); a_off := 2147450880 |} (ELit 36); KWr {| a_base := EVar 36; a_off := 0 |} (ELit 296); KDisj {| a_base := EVar 2; a_off := -160 |} (ELit 176) {| a_base := EVar 36; a_off := 0 |} (ELit 296); KWord {| a_base := EVar 36; a_off := 264 |} 8 (EVar 34); KWord {| a_base := EVar 36; a_off := 272 |} 8 (ELit 16384); KWord {| a_base := EVar 36; a_off := 280 |} 8 (EVar 35); KUnk {| a_base := EVar 36; a_off := 256 |} (ELit 8); KRange (EVar 2) 140735332487248 140737488355328; KWr {| a_base := EVar 2; a_off := -160 |} (ELit 160); KDisj {| a_base := EVar 2; a_off := -160 |} (ELit 160) {| a_base := EVar 36; a_off := 0 |} (ELit 296); KWord {| a_base := EVar 36; a_off := 288 |} 8 (ELit 0); KRange (EVar 45) 6905856 140737488355056; KAlign (EVar 45) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 45; a_off := 0 |} (ELit 272); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 45) (ELit 3); a_off := 2147450880 |} (ELit 34); KWr {| a_base := EVar 45; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -160 |} (ELit 160) {| a_base := EVar 45; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 36; a_off := 0 |} (ELit 296) {| a_base := EVar 45; a_off := 0 |} (ELit 272); KWord {| a_base := EVar 36; a_off := 240 |} 8 (EVar 45); KWord {| a_base := EVar 36; a_off := 248 |} 8 (EAlu Instr.ALU_ADD (EVar 45) (ELit 16)); KWord {| a_base := EVar 45; a_off := 0 |} 8 (ELit 1265968); KWord {| a_base := EVar 45; a_off := 16 |} 8 (ELit 1265728); KWord {| a_base := EVar 45; a_off := 152 |} 4 (ELit 0); KWord {| a_base := EVar 45; a_off := 156 |} 4 (ELit 0); KWord {| a_base := EVar 45; a_off := 160 |} 8 (EAlu Instr.ALU_ADD (EVar 45) (ELit 16)); KZero {| a_base := ELit 0; a_off := 2147609123 |} (ELit 1); KZero {| a_base := ELit 0; a_off := 2147609104 |} (ELit 1); KRange (EVar 38) 16384 16384; KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 37); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := 0 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := 8 |} 8 (EVar 1); KRange (EVar 50) 215808 4398046511102; KAlign (EVar 50) 4; KUnk {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 24 |} (ELit 8); KUnk {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 40 |} (ELit 88); KWr {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 0 |} (ELit 128); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 0 |} (ELit 128); KWr {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450880 |} (ELit 16); KWord {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 120 |} 8 (EVar 51); KRange (EVar 51) 4096 140737488355327; KWr {| a_base := EVar 51; a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 51; a_off := 0 |} (ELit 1); KDisj {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 0 |} (ELit 128) {| a_base := EVar 51; a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 2; a_off := -160 |} (ELit 176) {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 0 |} (ELit 128); KDisj {| a_base := EVar 2; a_off := -160 |} (ELit 176) {| a_base := EVar 51; a_off := 0 |} (ELit 1); KDisj {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 0 |} (ELit 128) {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450880 |} (ELit 16); KDisj {| a_base := EVar 51; a_off := 0 |} (ELit 1) {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450880 |} (ELit 16); KDisj {| a_base := EVar 2; a_off := -160 |} (ELit 176) {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450880 |} (ELit 16); KDisj {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 0 |} (ELit 128) {| a_base := EVar 36; a_off := 0 |} (ELit 296); KDisj {| a_base := EVar 51; a_off := 0 |} (ELit 1) {| a_base := EVar 36; a_off := 0 |} (ELit 296); KDisj {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450880 |} (ELit 16) {| a_base := EVar 36; a_off := 0 |} (ELit 296); KDisj {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450880 |} (ELit 16) {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit 8)) (ELit 3); a_off := 2147450880 |} (ELit 36); KDisj {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 0 |} (ELit 128) {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit 8)) (ELit 3); a_off := 2147450880 |} (ELit 36); KDisj {| a_base := EVar 51; a_off := 0 |} (ELit 1) {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit 8)) (ELit 3); a_off := 2147450880 |} (ELit 36); KDisj {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 0 |} (ELit 128) {| a_base := EVar 45; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 51; a_off := 0 |} (ELit 1) {| a_base := EVar 45; a_off := 0 |} (ELit 272); KDisj {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450880 |} (ELit 16) {| a_base := EVar 45; a_off := 0 |} (ELit 272); KDisj {| a_base := EMd Instr.M_MUL (ELit 4) (EVar 50); a_off := 2147450880 |} (ELit 16) {| a_base := EAlu Instr.ALU_SRL (EVar 45) (ELit 3); a_off := 2147450880 |} (ELit 34); KDisj {| a_base := EMd Instr.M_MUL (ELit 32) (EVar 50); a_off := 0 |} (ELit 128) {| a_base := EAlu Instr.ALU_SRL (EVar 45) (ELit 3); a_off := 2147450880 |} (ELit 34); KDisj {| a_base := EVar 51; a_off := 0 |} (ELit 1) {| a_base := EAlu Instr.ALU_SRL (EVar 45) (ELit 3); a_off := 2147450880 |} (ELit 34); KRange (EVar 37) 4096 140737488338944] 80))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 894976 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_ecee19_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 716228 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_ecee19_b.IT SegItab_Ba_ecee19_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 716228 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
