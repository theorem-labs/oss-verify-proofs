(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_eaebd5_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_eaebd5_b.ITR.
Definition IT : itab := SegItab_Ba_eaebd5_b.IT.
Definition ENDS : list Z := [1180172].
Definition STOPS1 : list Z := [1180172] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 687464; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 1293512; ELit 108788; ELit 67108864; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-3248)) (ELit 3248);
   KUnk (SA (EVar 2) (-3248)) (ELit 3248);
   KImg 65536 1282048;
   KZero (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) (2147450760)) (ELit 80);
   KWord (SA (ELit 0) (2147464472)) 8 (ELit 0); KWord (SA (ELit 0) (2147464480)) 8 (ELit 0);
   KWr (SA (ELit 0) (1293512)) (ELit 4);
   KWr (SA (ELit 0) (1293520)) (ELit 8);
   KWr (SA (ELit 0) (1293528)) (ELit 8);
   KWr (SA (ELit 0) (1293544)) (ELit 8);
   KWr (SA (ELit 0) (1293552)) (ELit 8);
   KWr (SA (ELit 0) (1293568)) (ELit 8);
   KWr (SA (ELit 0) (1293600)) (ELit 8);
   KWr (SA (ELit 0) (1293608)) (ELit 8);
   KWr (SA (ELit 0) (1293648)) (ELit 4);
   KWord (SA (ELit 0) (1313048)) 1 (ELit 1);
   KWord (SA (ELit 0) (1906620)) 1 (ELit 1);
   KWord (SA (ELit 0) (1309752)) 8 (ELit 2147450880);
   KWord (SA (ELit 0) (1282896)) 8 (ELit 1184024);
   KWord (SA (ELit 0) (6896960)) 8 (EVar 40);
   KWord (SA (ELit 0) (1293652)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1293512)) 4 (ELit 5);
   KWord (SA (ELit 0) (1293608)) 8 (ELit 0);
   KWord (SA (ELit 0) (1293600)) 8 (ELit 6898968);
   KWord (SA (ELit 0) (1293648)) 4 (ELit 0);
   KWord (SA (ELit 0) (1293656)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1313049)) 1 (ELit 1);
   KWord (SA (ELit 0) (1283272)) 8 (ELit 1218816);
   KWord (SA (ELit 0) (1293584)) 8 (ELit 1180112)].
Definition ss0 : sym_state := SS 406460 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3248), ELit 3248); (ELit 0, (1293512), ELit 4); (ELit 0, (1293520), ELit 8); (ELit 0, (1293528), ELit 8); (ELit 0, (1293544), ELit 8); (ELit 0, (1293552), ELit 8); (ELit 0, (1293568), ELit 8); (ELit 0, (1293600), ELit 8); (ELit 0, (1293608), ELit 8); (ELit 0, (1293648), ELit 4)].
Definition F0L : list SR.region := [(EVar 2, (-3248), 3248); (ELit 0, (1293512), 4); (ELit 0, (1293520), 8); (ELit 0, (1293528), 8); (ELit 0, (1293544), 8); (ELit 0, (1293552), 8); (ELit 0, (1293568), 8); (ELit 0, (1293600), 8); (ELit 0, (1293608), 8); (ELit 0, (1293648), 4)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [1180172; 1180172])], (93, SS 1180172 [ELit 0; ELit 1184320; EAlu Instr.ALU_ADD (EVar 2) (ELit (-592)); EVar 3; EVar 4; ELit 115; ELit 101; ELit 100; ELit 0; ELit 1293512; EVar 40; ELit 0; ELit 0; ELit 1180112; ELit 0; ELit 101; ELit 102; ELit 117; ELit 6896960; ELit 1; ELit 6898968; ELit 6896960; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; ELit 10; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -552 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -544 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -536 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -528 |} 8 (ELit 6898968); KWord {| a_base := EVar 2; a_off := -520 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -512 |} 8 (ELit 6896960); KWord {| a_base := EVar 2; a_off := -504 |} 8 (ELit 38); KWord {| a_base := EVar 2; a_off := -496 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := -488 |} 8 (ELit 1184320); KWord {| a_base := ELit 0; a_off := 1293552 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-426))); KWord {| a_base := EVar 2; a_off := -427 |} 1 (ELit 10); KWord {| a_base := EVar 2; a_off := -428 |} 1 (ELit 100); KWord {| a_base := EVar 2; a_off := -429 |} 1 (ELit 101); KWord {| a_base := EVar 2; a_off := -430 |} 1 (ELit 115); KWord {| a_base := EVar 2; a_off := -431 |} 1 (ELit 117); KWord {| a_base := EVar 2; a_off := -432 |} 1 (ELit 102); KWord {| a_base := EVar 2; a_off := -433 |} 1 (ELit 101); KWord {| a_base := EVar 2; a_off := -434 |} 1 (ELit 114); KWord {| a_base := EVar 2; a_off := -435 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := -436 |} 1 (ELit 44); KWord {| a_base := EVar 2; a_off := -437 |} 1 (ELit 115); KWord {| a_base := EVar 2; a_off := -438 |} 1 (ELit 101); KWord {| a_base := EVar 2; a_off := -439 |} 1 (ELit 116); KWord {| a_base := EVar 2; a_off := -440 |} 1 (ELit 121); KWord {| a_base := EVar 2; a_off := -441 |} 1 (ELit 98); KWord {| a_base := EVar 2; a_off := -442 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := -1168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -1160 |} 8 (ELit 108804); KWord {| a_base := EVar 2; a_off := -1152 |} 8 (ELit 16); KWord {| a_base := EVar 2; a_off := -1144 |} 8 (ELit 108820); KWord {| a_base := EVar 2; a_off := -1136 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := -1128 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -1120 |} 8 (ELit 108804); KWord {| a_base := EVar 2; a_off := -1112 |} 8 (ELit 16); KWord {| a_base := EVar 2; a_off := -1104 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := -1096 |} 8 (ELit 1182924); KWord {| a_base := EVar 2; a_off := -1080 |} 8 (ELit 108820); KWord {| a_base := EVar 2; a_off := -1072 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := -1064 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -1056 |} 8 (ELit 2147483625); KWord {| a_base := EVar 2; a_off := -1048 |} 8 (ELit 2147483647); KWord {| a_base := EVar 2; a_off := -1040 |} 8 (ELit 37); KWord {| a_base := EVar 2; a_off := -1032 |} 8 (ELit 1184784); KWord {| a_base := EVar 2; a_off := -443 |} 1 (ELit 52); KWord {| a_base := EVar 2; a_off := -444 |} 1 (ELit 54); KWord {| a_base := EVar 2; a_off := -445 |} 1 (ELit 56); KWord {| a_base := EVar 2; a_off := -446 |} 1 (ELit 56); KWord {| a_base := EVar 2; a_off := -447 |} 1 (ELit 48); KWord {| a_base := EVar 2; a_off := -448 |} 1 (ELit 49); KWord {| a_base := EVar 2; a_off := -449 |} 1 (ELit 55); KWord {| a_base := EVar 2; a_off := -450 |} 1 (ELit 54); KWord {| a_base := EVar 2; a_off := -1016 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -992 |} 8 (ELit 8); KWord {| a_base := EVar 2; a_off := -1008 |} 8 (ELit 8); KWord {| a_base := EVar 2; a_off := -856 |} 1 (ELit 54); KWord {| a_base := EVar 2; a_off := -1024 |} 8 (ELit 69053); KWord {| a_base := EVar 2; a_off := -855 |} 1 (ELit 55); KWord {| a_base := EVar 2; a_off := -854 |} 1 (ELit 49); KWord {| a_base := EVar 2; a_off := -853 |} 1 (ELit 48); KWord {| a_base := EVar 2; a_off := -852 |} 1 (ELit 56); KWord {| a_base := EVar 2; a_off := -851 |} 1 (ELit 56); KWord {| a_base := EVar 2; a_off := -850 |} 1 (ELit 54); KWord {| a_base := EVar 2; a_off := -849 |} 1 (ELit 52); KWord {| a_base := EVar 2; a_off := -1000 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -912 |} 8 (ELit 67108864); KWord {| a_base := EVar 2; a_off := -480 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-40))); KWord {| a_base := EVar 2; a_off := -451 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := -452 |} 1 (ELit 61); KWord {| a_base := EVar 2; a_off := -456 |} 4 (ELit 1042314357); KWord {| a_base := EVar 2; a_off := -460 |} 4 (ELit 1886284064); KWord {| a_base := EVar 2; a_off := -464 |} 4 (ELit 979987555); KWord {| a_base := EVar 2; a_off := -984 |} 8 (ELit 18446744072850558157); KWord {| a_base := EVar 2; a_off := -976 |} 8 (ELit 18446744073709486079); KWord {| a_base := EVar 2; a_off := -920 |} 8 (ELit 214748364); KWord {| a_base := EVar 2; a_off := -944 |} 8 (ELit 75913); KWord {| a_base := EVar 2; a_off := -592 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -928 |} 8 (ELit 6896960); KWord {| a_base := EVar 2; a_off := -936 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -952 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-480))); KWord {| a_base := EVar 2; a_off := -968 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-384))); KWord {| a_base := EVar 2; a_off := -960 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-216))); KWord {| a_base := EVar 2; a_off := -584 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -576 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -568 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -560 |} 8 (EVar 24); KWord {| a_base := ELit 0; a_off := 1293544 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-384))); KWord {| a_base := ELit 0; a_off := 1293528 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1293520 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1293568 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-464))); KWord {| a_base := ELit 0; a_off := 1293648 |} 4 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1293608 |} 8 (ELit 80); KWord {| a_base := ELit 0; a_off := 1293600 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-464))); KWord {| a_base := ELit 0; a_off := 1293512 |} 4 (ELit 5); KWord {| a_base := EVar 2; a_off := -192 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -208 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -216 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -472 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -168 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 108788); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 426864); KWord {| a_base := EVar 2; a_off := -2320 |} 8 (ELit 18446744073709551615); KWord {| a_base := EVar 2; a_off := -2289 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2290 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2291 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2292 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2293 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2294 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2295 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2296 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2297 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2298 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2299 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2300 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2301 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2302 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2303 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2304 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2305 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2306 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2307 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2308 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2309 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2310 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2311 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2312 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2321 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2322 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2323 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2324 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2325 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2326 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2327 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2328 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2384 |} 8 (ELit 10); KWord {| a_base := EVar 2; a_off := -2376 |} 8 (ELit 108802); KWord {| a_base := EVar 2; a_off := -2368 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-112))); KWord {| a_base := EVar 2; a_off := -2360 |} 8 (ELit 422676); KWord {| a_base := EVar 2; a_off := -2344 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-232))); KWord {| a_base := EVar 2; a_off := -2336 |} 8 (ELit 133306); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 15); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 14); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 13); KWord {| a_base := EVar 2; a_off := -48 |} 8 (ELit 67108864); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 17); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 16); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -56 |} 8 (ELit 687464); KRange (EVar 2) 140735332552704 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -3248 |} (ELit 3248); KUnk {| a_base := EVar 2; a_off := -3248 |} (ELit 864); KUnk {| a_base := EVar 2; a_off := -2352 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -2288 |} (ELit 1120); KUnk {| a_base := EVar 2; a_off := -1088 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -904 |} (ELit 48); KUnk {| a_base := EVar 2; a_off := -848 |} (ELit 256); KUnk {| a_base := EVar 2; a_off := -426 |} (ELit 210); KUnk {| a_base := EVar 2; a_off := -112 |} (ELit 8); KImg 65536 1282048; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450760 |} (ELit 80); KWord {| a_base := ELit 0; a_off := 2147464472 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147464480 |} 8 (ELit 0); KWr {| a_base := ELit 0; a_off := 1293512 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 1293520 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293528 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293544 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293552 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293568 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293600 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293608 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293648 |} (ELit 4); KWord {| a_base := ELit 0; a_off := 1313048 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1906620 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1309752 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1282896 |} 8 (ELit 1184024); KWord {| a_base := ELit 0; a_off := 6896960 |} 8 (EVar 40); KWord {| a_base := ELit 0; a_off := 1293652 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1293656 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1313049 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1283272 |} 8 (ELit 1218816); KWord {| a_base := ELit 0; a_off := 1293584 |} 8 (ELit 1180112)] 140))).
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
Definition ps0 : SR.post_spec := SR.PS 1180172 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_eaebd5_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 406460 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_eaebd5_b.IT SegItab_Ba_eaebd5_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 406460 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
