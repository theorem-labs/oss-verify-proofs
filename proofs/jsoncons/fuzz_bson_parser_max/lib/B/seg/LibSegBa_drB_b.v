(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_8b19f9_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_8b19f9_b.ITR.
Definition IT : itab := SegItab_Ba_8b19f9_b.IT.
Definition ENDS : list Z := [406384].
Definition STOPS1 : list Z := [406384] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (EAlu Instr.ALU_ADD (EVar 2) (ELit (2240))); EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 127272; EVar 120; EVar 121; EVar 122; EVar 123; (EAlu Instr.ALU_ADD (EVar 2) (ELit (56))); ELit 12297829382473034410; ELit 18446744073709551615; ELit 37; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-896)) (ELit 3136);
   KUnk (SA (EVar 2) (-896)) (ELit 3136);
   KImg 65536 1282048;
   KRange (EVar 33) 140735332552704 140737488355311;
   KRange (EVar 34) 1 1;
   KDisj (SA (EVar 2) (-896)) (ELit 3136) (SA (EVar 33) 0) (EAlu Instr.ALU_ADD (EVar 34) (ELit 1));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) (2147451102)) (ELit 32);
   KWord (SA (ELit 0) (2147466776)) 8 (ELit 0);
   KWord (SA (ELit 0) (2147466784)) 8 (ELit 0);
   KWr (SA (ELit 0) (1293512)) (ELit 4);
   KWr (SA (ELit 0) (1293520)) (ELit 8);
   KWr (SA (ELit 0) (1293528)) (ELit 8);
   KWr (SA (ELit 0) (1293544)) (ELit 8);
   KWr (SA (ELit 0) (1293552)) (ELit 8);
   KWr (SA (ELit 0) (1293568)) (ELit 8);
   KWr (SA (ELit 0) (1293600)) (ELit 8);
   KWr (SA (ELit 0) (1293608)) (ELit 8);
   KWr (SA (ELit 0) (1293648)) (ELit 4);
   KWord (SA (EVar 2) (2232)) 8 (ELit 426800);
   KWord (SA (EVar 2) (2224)) 8 (ELit 127251);
   KWord (SA (EVar 2) (2216)) 8 (ELit 1293512);
   KWord (SA (EVar 2) (2208)) 8 ((EAlu Instr.ALU_ADD (EVar 2) (ELit (2304))));
   KWord (SA (EVar 2) (2200)) 8 (EVar 19);
   KWord (SA (EVar 2) (2192)) 8 (EVar 20);
   KWord (SA (EVar 2) (2184)) 8 (EVar 21);
   KWord (SA (EVar 2) (2176)) 8 (EVar 22);
   KWord (SA (EVar 2) (2168)) 8 (EVar 23);
   KWord (SA (EVar 2) (2160)) 8 (EVar 24);
   KWord (SA (EVar 2) (2152)) 8 (EVar 25);
   KWord (SA (EVar 2) (2144)) 8 (EVar 26);
   KWord (SA (EVar 2) (2136)) 8 (EVar 27);
   KWord (SA (ELit 0) (1282896)) 8 (ELit 1184024);
   KWord (SA (EVar 2) (2264)) 8 ((EAlu Instr.ALU_ADD (EVar 2) (ELit (2304))));
   KWord (SA (ELit 0) (6896960)) 8 (EVar 40);
   KWord (SA (ELit 0) (1293652)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1293512)) 4 (ELit 5);
   KWord (SA (ELit 0) (1293608)) 8 (ELit 0);
   KWord (SA (ELit 0) (1293600)) 8 (ELit 6898968);
   KWord (SA (ELit 0) (1293648)) 4 (ELit 0);
   KWord (SA (ELit 0) (1293656)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1313049)) 1 (ELit 1);
   KWord (SA (ELit 0) (1309752)) 8 (ELit 2147450880);
   KWord (SA (ELit 0) (1283272)) 8 (ELit 1218816);
   KWord (SA (EVar 2) (2304)) 8 ((EVar 33))].
Definition ss0 : sym_state := SS 422932 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-896), ELit 3136); (ELit 0, (1293512), ELit 4); (ELit 0, (1293520), ELit 8); (ELit 0, (1293528), ELit 8); (ELit 0, (1293544), ELit 8); (ELit 0, (1293552), ELit 8); (ELit 0, (1293568), ELit 8); (ELit 0, (1293600), ELit 8); (ELit 0, (1293608), ELit 8); (ELit 0, (1293648), ELit 4)].
Definition F0L : list SR.region := [(EVar 2, (-896), 3136); (ELit 0, (1293512), 4); (ELit 0, (1293520), 8); (ELit 0, (1293528), 8); (ELit 0, (1293544), 8); (ELit 0, (1293552), 8); (ELit 0, (1293568), 8); (ELit 0, (1293600), 8); (ELit 0, (1293608), 8); (ELit 0, (1293648), 4)].
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
  (([SGA.AStep (SR.SBlock [406384; 406384])], (93, SS 406384 [ELit 0; ELit 1186016; EAlu Instr.ALU_ADD (EVar 2) (ELit 1328); EVar 3; EVar 4; ELit 0; ELit 114; ELit 32; ELit 37; ELit 2147483647; EVar 33; ELit 2147483647; EAlu Instr.ALU_ADD (EVar 2) (ELit 1872); EAlu Instr.ALU_ADD (EVar 2) (ELit 2312); ELit 31; ELit 18446744073709551558; ELit 115; ELit 8; ELit 2147483628; ELit 19; ELit 1293512; ELit 127272; ELit 0; EVar 33; ELit 0; ELit 18446744073709551615; ELit 0; ELit 0; ELit 111; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := 1440 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := 1872 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 2312)); KWord {| a_base := ELit 0; a_off := 1293552 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 1907)); KWord {| a_base := EVar 2; a_off := 1184 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := 1192 |} 8 (ELit 127270); KWord {| a_base := EVar 2; a_off := 1200 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 1208 |} 8 (ELit 127270); KWord {| a_base := EVar 2; a_off := 1216 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := 1224 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 1232 |} 8 (ELit 127270); KWord {| a_base := EVar 2; a_off := 1240 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 1248 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := 1256 |} 8 (ELit 1182924); KWord {| a_base := EVar 2; a_off := 1272 |} 8 (ELit 127270); KWord {| a_base := EVar 2; a_off := 1280 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := 1288 |} 8 (ELit 19); KWord {| a_base := EVar 2; a_off := 1296 |} 8 (ELit 2147483628); KWord {| a_base := EVar 2; a_off := 1304 |} 8 (ELit 2147483647); KWord {| a_base := EVar 2; a_off := 1312 |} 8 (ELit 37); KWord {| a_base := EVar 2; a_off := 1320 |} 8 (ELit 1184784); KWord {| a_base := EVar 2; a_off := 1906 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := 1905 |} 1 (ELit 110); KWord {| a_base := EVar 2; a_off := 1904 |} 1 (ELit 111); KWord {| a_base := EVar 2; a_off := 1903 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := 1902 |} 1 (ELit 114); KWord {| a_base := EVar 2; a_off := 1901 |} 1 (ELit 111); KWord {| a_base := EVar 2; a_off := 1900 |} 1 (ELit 114); KWord {| a_base := EVar 2; a_off := 1899 |} 1 (ELit 114); KWord {| a_base := EVar 2; a_off := 1898 |} 1 (ELit 101); KWord {| a_base := EVar 2; a_off := 1897 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := 1896 |} 1 (ELit 100); KWord {| a_base := EVar 2; a_off := 1895 |} 1 (ELit 97); KWord {| a_base := EVar 2; a_off := 1894 |} 1 (ELit 101); KWord {| a_base := EVar 2; a_off := 1893 |} 1 (ELit 114); KWord {| a_base := EVar 2; a_off := 1892 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := 1891 |} 1 (ELit 58); KWord {| a_base := EVar 2; a_off := 1890 |} 1 (ELit 105); KWord {| a_base := EVar 2; a_off := 1889 |} 1 (ELit 108); KWord {| a_base := EVar 2; a_off := 1888 |} 1 (ELit 99); KWord {| a_base := EVar 2; a_off := 1368 |} 8 (ELit 18446744072850558157); KWord {| a_base := EVar 2; a_off := 1376 |} 8 (ELit 18446744073709486079); KWord {| a_base := EVar 2; a_off := 1432 |} 8 (ELit 214748364); KWord {| a_base := EVar 2; a_off := 1408 |} 8 (ELit 75913); KWord {| a_base := EVar 2; a_off := 1760 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := 1424 |} 8 (ELit 6896960); KWord {| a_base := EVar 2; a_off := 1416 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 1400 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 1872)); KWord {| a_base := EVar 2; a_off := 1384 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 1968)); KWord {| a_base := EVar 2; a_off := 1392 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 2136)); KWord {| a_base := EVar 2; a_off := 1768 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := 1776 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := 1784 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := 1792 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := 1800 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := 1808 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := 1816 |} 8 (ELit 5); KWord {| a_base := EVar 2; a_off := 1824 |} 8 (ELit 6898968); KWord {| a_base := EVar 2; a_off := 1832 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := 1840 |} 8 (ELit 6896960); KWord {| a_base := EVar 2; a_off := 1848 |} 8 (ELit 127251); KWord {| a_base := EVar 2; a_off := 1856 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := 1864 |} 8 (ELit 1184288); KWord {| a_base := ELit 0; a_off := 1293544 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 1968)); KWord {| a_base := ELit 0; a_off := 1293528 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1293520 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1293568 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 1888)); KWord {| a_base := ELit 0; a_off := 1293648 |} 4 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1293608 |} 8 (ELit 80); KWord {| a_base := ELit 0; a_off := 1293600 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 1888)); KWord {| a_base := ELit 0; a_off := 1293512 |} 4 (ELit 5); KWord {| a_base := EVar 2; a_off := 2160 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 2152 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 2144 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 2136 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 2168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 1880 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 2304)); KWord {| a_base := EVar 2; a_off := 2176 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := 2184 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := 2192 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := 2200 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := 2208 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 2304)); KWord {| a_base := EVar 2; a_off := 2216 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := 2224 |} 8 (ELit 127251); KWord {| a_base := EVar 2; a_off := 2232 |} 8 (ELit 426864); KWord {| a_base := EVar 2; a_off := 32 |} 8 (ELit 18446744073709551615); KWord {| a_base := EVar 2; a_off := 63 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 62 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 61 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 60 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 59 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 58 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 57 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 56 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 55 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 54 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 53 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 52 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 51 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 50 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 49 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 48 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 47 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 46 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 45 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 44 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 43 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 42 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 41 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 40 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 31 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 30 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 29 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 28 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 27 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 26 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 25 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := 24 |} 1 (ELit 0); KRange (EVar 2) 140735332552704 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -896 |} (ELit 3136); KUnk {| a_base := EVar 2; a_off := -896 |} (ELit 920); KUnk {| a_base := EVar 2; a_off := 64 |} (ELit 1120); KUnk {| a_base := EVar 2; a_off := 1264 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := 1328 |} (ELit 40); KUnk {| a_base := EVar 2; a_off := 1448 |} (ELit 312); KUnk {| a_base := EVar 2; a_off := 1907 |} (ELit 229); KImg 65536 1282048; KRange (EVar 33) 140735332552704 140737488355311; KRange (EVar 34) 1 1; KDisj {| a_base := EVar 2; a_off := -896 |} (ELit 3136) {| a_base := EVar 33; a_off := 0 |} (EAlu Instr.ALU_ADD (EVar 34) (ELit 1)); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147451102 |} (ELit 32); KWord {| a_base := ELit 0; a_off := 2147466776 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147466784 |} 8 (ELit 0); KWr {| a_base := ELit 0; a_off := 1293512 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 1293520 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293528 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293544 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293552 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293568 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293600 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293608 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293648 |} (ELit 4); KWord {| a_base := ELit 0; a_off := 1282896 |} 8 (ELit 1184024); KWord {| a_base := EVar 2; a_off := 2264 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 2304)); KWord {| a_base := ELit 0; a_off := 6896960 |} 8 (EVar 40); KWord {| a_base := ELit 0; a_off := 1293652 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1293656 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1313049 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1309752 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1283272 |} 8 (ELit 1218816); KWord {| a_base := EVar 2; a_off := 2304 |} 8 (EVar 33)] 140))).
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
Definition ps0 : SR.post_spec := SR.PS 406384 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_8b19f9_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 422932 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_8b19f9_b.IT SegItab_Ba_8b19f9_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 422932 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
