(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ba0PlanKit Ba0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.seg Require SegItab_Ba_d01ee6.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_d01ee6.ITR.
Definition IT : itab := SegItab_Ba_d01ee6.IT.
Definition ENDS : list Z := [720356].
Definition STOPS1 : list Z := [720356] ++ ENDS.
Definition NX0 : nat := 130.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-224))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (EVar 2); (EAlu Instr.ALU_ADD (EVar 2) (ELit (-224))); (EVar 57); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; ELit 145760; (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))); (EVar 50); (EVar 33); ELit 2147450880; (EVar 34); (EAlu Instr.ALU_ADD (EVar 33) (ELit (368))); (EVar 36); (EVar 81); (EVar 80); (EVar 50); EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1269760;
   KWord (SA (ELit 0) 1300408) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1300416) 4 (ELit 1);
   KRange (EVar 2) 140735332487392 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-224)) (ELit 224);
   KRange (EVar 33) 6897664 140737488354912;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 416);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (8))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (10))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (400))) (ELit 3)) 2147450880) (ELit 1);
   KDisj (SA (EVar 2) (-224)) (ELit 224) (SA (EVar 33) 0) (ELit 416);
   KRange (EVar 50) 6897664 140737488354816;
   KAlign (EVar 50) 32;
   KUnk (SA (EVar 50) 0) (ELit 512);
   KWr (SA (EVar 50) 0) (ELit 512);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 512);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) 2147450880) (ELit 64);
   KWord (SA (EVar 50) 504) 8 (EVar 51);
   KRange (EVar 51) 4096 140737488355327;
   KWr (SA (EVar 51) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 51) 0) (ELit 1);
   KDisj (SA (EVar 50) 0) (ELit 512) (SA (EVar 51) 0) (ELit 1);
   KDisj (SA (EVar 2) (-224)) (ELit 224) (SA (EVar 50) 0) (ELit 512);
   KDisj (SA (EVar 2) (-224)) (ELit 224) (SA (EVar 51) 0) (ELit 1);
   KDisj (SA (EVar 33) 0) (ELit 416) (SA (EVar 50) 0) (ELit 512);
   KDisj (SA (EVar 33) 0) (ELit 416) (SA (EVar 51) 0) (ELit 1);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 52) (SA (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) 2147450880) (ELit 64);
   KDisj (SA (ELit 0) 65536) (ELit 6832128) (SA (EVar 50) 0) (ELit 512);
   KDisj (SA (ELit 0) 65536) (ELit 6832128) (SA (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) 2147450880) (ELit 64);
   KDisj (SA (ELit 0) 65536) (ELit 6832128) (SA (EVar 51) 0) (ELit 1);
   KRange (EVar 57) 4096 140737488355296;
   KAlign (EVar 57) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 57) 0) (ELit 24);
   KWr (SA (EVar 57) 0) (ELit 24);
   KDisj (SA (EVar 2) (-224)) (ELit 224) (SA (EVar 57) 0) (ELit 24);
   KDisj (SA (EVar 57) 0) (ELit 24) (SA (EVar 33) 0) (ELit 416);
   KDisj (SA (ELit 0) 65536) (ELit 6832128) (SA (EVar 57) 0) (ELit 24);
   KDisj (SA (EVar 57) 0) (ELit 24) (SA (EVar 50) 0) (ELit 512);
   KDisj (SA (EVar 57) 0) (ELit 24) (SA (EVar 51) 0) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 57) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit (2))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit (4))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit (6))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit (8))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit (10))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit (12))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit (14))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit (16))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit (18))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit (20))) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit (22))) (ELit 3)) 2147450880) (ELit 1);
   KRange (EVar 88) 0 255;
   KWord (SA (EMd Instr.M_MUL (ELit 2) (EVar 88)) 145760) 1 (EVar 108);
   KRange (EVar 108) 0 255;
   KWord (SA (EMd Instr.M_MUL (ELit 2) (EVar 88)) 145761) 1 (EVar 120);
   KRange (EVar 120) 0 255;
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 88)) (ELit (145760))) (ELit 3)) 2147450880) (ELit 1);
   KRange (EVar 89) 0 255;
   KWord (SA (EMd Instr.M_MUL (ELit 2) (EVar 89)) 145760) 1 (EVar 109);
   KRange (EVar 109) 0 255;
   KWord (SA (EMd Instr.M_MUL (ELit 2) (EVar 89)) 145761) 1 (EVar 121);
   KRange (EVar 121) 0 255;
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 89)) (ELit (145760))) (ELit 3)) 2147450880) (ELit 1);
   KRange (EVar 90) 0 255;
   KWord (SA (EMd Instr.M_MUL (ELit 2) (EVar 90)) 145760) 1 (EVar 110);
   KRange (EVar 110) 0 255;
   KWord (SA (EMd Instr.M_MUL (ELit 2) (EVar 90)) 145761) 1 (EVar 122);
   KRange (EVar 122) 0 255;
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 90)) (ELit (145760))) (ELit 3)) 2147450880) (ELit 1);
   KRange (EVar 91) 0 255;
   KWord (SA (EMd Instr.M_MUL (ELit 2) (EVar 91)) 145760) 1 (EVar 111);
   KRange (EVar 111) 0 255;
   KWord (SA (EMd Instr.M_MUL (ELit 2) (EVar 91)) 145761) 1 (EVar 123);
   KRange (EVar 123) 0 255;
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 91)) (ELit (145760))) (ELit 3)) 2147450880) (ELit 1);
   KWord (SA (EVar 2) (-160)) 8 (EVar 88);
   KWord (SA (EVar 2) (-152)) 8 (EVar 89);
   KWord (SA (EVar 2) (-144)) 8 (EVar 90);
   KWord (SA (EVar 2) (-136)) 8 (EVar 91)].
Definition ss0 : sym_state := SS 720132 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 57), (16), ELit 8)].
Definition F0L : list SR.region := [((EVar 57), (16), 8)].
Definition BF : nat := 1000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

(* [comment removed for export] *)
Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [720356; 720356])], (93, SS 720356 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-224)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-224)); EAlu Instr.ALU_ADD (EVar 57) (ELit 22); EVar 133; ELit 0; EVar 13; EVar 14; ELit 0; EVar 16; ELit 145760; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit 2147450880); EVar 50; EVar 33; ELit 2147450880; EVar 34; EAlu Instr.ALU_ADD (EVar 33) (ELit 368); EVar 36; EVar 81; EVar 80; EVar 50; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 57; a_off := 22 |} 2 (EVar 133); KWord {| a_base := EVar 57; a_off := 20 |} 2 (EVar 132); KWord {| a_base := EVar 57; a_off := 18 |} 2 (EVar 131); KWord {| a_base := EVar 57; a_off := 16 |} 2 (EVar 130); KImg 65536 1269760; KWord {| a_base := ELit 0; a_off := 1300408 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1300416 |} 4 (ELit 1); KRange (EVar 2) 140735332487392 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -224 |} (ELit 224); KRange (EVar 33) 6897664 140737488354912; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 416); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 8)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 10)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 400)) (ELit 3); a_off := 2147450880 |} (ELit 1); KDisj {| a_base := EVar 2; a_off := -224 |} (ELit 224) {| a_base := EVar 33; a_off := 0 |} (ELit 416); KRange (EVar 50) 6897664 140737488354816; KAlign (EVar 50) 32; KUnk {| a_base := EVar 50; a_off := 0 |} (ELit 512); KWr {| a_base := EVar 50; a_off := 0 |} (ELit 512); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 50; a_off := 0 |} (ELit 512); KWr {| a_base := EAlu Instr.ALU_SRL (EVar 50) (ELit 3); a_off := 2147450880 |} (ELit 64); KWord {| a_base := EVar 50; a_off := 504 |} 8 (EVar 51); KRange (EVar 51) 4096 140737488355327; KWr {| a_base := EVar 51; a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 51; a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 50; a_off := 0 |} (ELit 512) {| a_base := EVar 51; a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 2; a_off := -224 |} (ELit 224) {| a_base := EVar 50; a_off := 0 |} (ELit 512); KDisj {| a_base := EVar 2; a_off := -224 |} (ELit 224) {| a_base := EVar 51; a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 33; a_off := 0 |} (ELit 416) {| a_base := EVar 50; a_off := 0 |} (ELit 512); KDisj {| a_base := EVar 33; a_off := 0 |} (ELit 416) {| a_base := EVar 51; a_off := 0 |} (ELit 1); KDisj {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 52) {| a_base := EAlu Instr.ALU_SRL (EVar 50) (ELit 3); a_off := 2147450880 |} (ELit 64); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6832128) {| a_base := EVar 50; a_off := 0 |} (ELit 512); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6832128) {| a_base := EAlu Instr.ALU_SRL (EVar 50) (ELit 3); a_off := 2147450880 |} (ELit 64); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6832128) {| a_base := EVar 51; a_off := 0 |} (ELit 1); KRange (EVar 57) 4096 140737488355296; KAlign (EVar 57) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 57; a_off := 0 |} (ELit 24); KWr {| a_base := EVar 57; a_off := 0 |} (ELit 24); KDisj {| a_base := EVar 2; a_off := -224 |} (ELit 224) {| a_base := EVar 57; a_off := 0 |} (ELit 24); KDisj {| a_base := EVar 57; a_off := 0 |} (ELit 24) {| a_base := EVar 33; a_off := 0 |} (ELit 416); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6832128) {| a_base := EVar 57; a_off := 0 |} (ELit 24); KDisj {| a_base := EVar 57; a_off := 0 |} (ELit 24) {| a_base := EVar 50; a_off := 0 |} (ELit 512); KDisj {| a_base := EVar 57; a_off := 0 |} (ELit 24) {| a_base := EVar 51; a_off := 0 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 57) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit 2)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit 4)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit 6)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit 8)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit 10)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit 12)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit 14)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit 16)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit 18)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit 20)) (ELit 3); a_off := 2147450880 |} (ELit 1); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 57) (ELit 22)) (ELit 3); a_off := 2147450880 |} (ELit 1); KRange (EVar 88) 0 255; KWord {| a_base := EMd Instr.M_MUL (ELit 2) (EVar 88); a_off := 145760 |} 1 (EVar 108); KRange (EVar 108) 0 255; KWord {| a_base := EMd Instr.M_MUL (ELit 2) (EVar 88); a_off := 145761 |} 1 (EVar 120); KRange (EVar 120) 0 255; KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 88)) (ELit 145760)) (ELit 3); a_off := 2147450880 |} (ELit 1); KRange (EVar 89) 0 255; KWord {| a_base := EMd Instr.M_MUL (ELit 2) (EVar 89); a_off := 145760 |} 1 (EVar 109); KRange (EVar 109) 0 255; KWord {| a_base := EMd Instr.M_MUL (ELit 2) (EVar 89); a_off := 145761 |} 1 (EVar 121); KRange (EVar 121) 0 255; KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 89)) (ELit 145760)) (ELit 3); a_off := 2147450880 |} (ELit 1); KRange (EVar 90) 0 255; KWord {| a_base := EMd Instr.M_MUL (ELit 2) (EVar 90); a_off := 145760 |} 1 (EVar 110); KRange (EVar 110) 0 255; KWord {| a_base := EMd Instr.M_MUL (ELit 2) (EVar 90); a_off := 145761 |} 1 (EVar 122); KRange (EVar 122) 0 255; KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 90)) (ELit 145760)) (ELit 3); a_off := 2147450880 |} (ELit 1); KRange (EVar 91) 0 255; KWord {| a_base := EMd Instr.M_MUL (ELit 2) (EVar 91); a_off := 145760 |} 1 (EVar 111); KRange (EVar 111) 0 255; KWord {| a_base := EMd Instr.M_MUL (ELit 2) (EVar 91); a_off := 145761 |} 1 (EVar 123); KRange (EVar 123) 0 255; KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 91)) (ELit 145760)) (ELit 3); a_off := 2147450880 |} (ELit 1); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 88); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EVar 89); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 90); KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 91)] 134))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.   (* [comment removed for export] *)
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.
(* [comment removed for export] *)
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)      (* [comment removed for export] *)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

(* [comment removed for export] *)
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 720356 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_d01ee6.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720132 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_d01ee6.IT SegItab_Ba_d01ee6.IT_sound BF NX0 BR XSTEP F0 PSS plan 720132 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
