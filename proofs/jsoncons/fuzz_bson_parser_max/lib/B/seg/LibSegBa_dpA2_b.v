(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_10a531_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_10a531_b.ITR.
Definition IT : itab := SegItab_Ba_10a531_b.IT.
Definition ENDS : list Z := [688024].
Definition STOPS1 : list Z := [688024] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 688024; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 85514; EAlu Instr.ALU_ADD (EVar 2) (ELit (24)); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-3232)) (ELit 3232);
   KUnk (SA (EVar 2) (-3232)) (ELit 3232);
   KImg 65536 1282048;
   KZero (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) (2147450764)) (ELit 24);
   KWord (SA (ELit 0) (2147461560)) 8 (ELit 0); KWord (SA (ELit 0) (2147461568)) 8 (ELit 0);
   KWord (SA (ELit 0) (2148313248)) 8 (ELit 0);
   KWr (SA (ELit 0) (1293752)) (ELit 4);
   KWr (SA (ELit 0) (1293792)) (ELit 8);
   KWr (SA (ELit 0) (6898976)) (ELit 1);
   KWr (SA (ELit 0) (6898977)) (ELit 1);
   KWord (SA (ELit 0) (1313048)) 1 (ELit 1);
   KWord (SA (ELit 0) (1906620)) 1 (ELit 1);
   KWord (SA (ELit 0) (1309752)) 8 (ELit 2147450880);
   KWord (SA (ELit 0) (1282888)) 8 (ELit 1209340);
   KWord (SA (ELit 0) (1282896)) 8 (ELit 1184024);
   KWord (SA (ELit 0) (6896960)) 8 (EVar 40);
   KWord (SA (ELit 0) (1293892)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1293752)) 4 (ELit 5);
   KWord (SA (ELit 0) (1293848)) 8 (ELit 1024);
   KWord (SA (ELit 0) (1293784)) 8 (ELit 6900000);
   KWord (SA (ELit 0) (1293792)) 8 (ELit 6898976);
   KWord (SA (ELit 0) (1293896)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1313049)) 1 (ELit 1);
   KWord (SA (ELit 0) (1283272)) 8 (ELit 1218816);
   KWord (SA (EVar 2) (24)) 4 (ELit 0);
   KWord (SA (ELit 0) (1283280)) 8 (ELit 1219844)].
Definition ss0 : sym_state := SS 406444 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1293752), ELit 4); (ELit 0, (1293792), ELit 8); (ELit 0, (6898976), ELit 1); (ELit 0, (6898977), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1293752), 4); (ELit 0, (1293792), 8); (ELit 0, (6898976), 1); (ELit 0, (6898977), 1)].
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
  (([SGA.AStep (SR.SBlock [688024; 688024])], (93, SS 688024 [ELit 0; ELit 688024; EVar 2; EVar 3; EVar 4; ELit 0; EVar 6; EVar 7; EVar 8; EVar 9; ELit 2; EVar 40; EVar 40; ELit 6898977; ELit 0; ELit 1; ELit 0; ELit 0; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := ELit 0; a_off := 1293752 |} 4 (ELit 5); KWord {| a_base := ELit 0; a_off := 1293792 |} 8 (ELit 6898978); KWord {| a_base := ELit 0; a_off := 6898977 |} 1 (ELit 10); KWord {| a_base := EVar 2; a_off := -1152 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -1144 |} 8 (ELit 85516); KWord {| a_base := EVar 2; a_off := -1136 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -1128 |} 8 (ELit 85517); KWord {| a_base := EVar 2; a_off := -1120 |} 8 (ELit 1293752); KWord {| a_base := EVar 2; a_off := -1112 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -1104 |} 8 (ELit 85516); KWord {| a_base := EVar 2; a_off := -1096 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -1088 |} 8 (ELit 1293752); KWord {| a_base := EVar 2; a_off := -1080 |} 8 (ELit 1182924); KWord {| a_base := EVar 2; a_off := -1064 |} 8 (ELit 85517); KWord {| a_base := EVar 2; a_off := -1056 |} 8 (ELit 1293752); KWord {| a_base := EVar 2; a_off := -1048 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -1040 |} 8 (ELit 2147483646); KWord {| a_base := EVar 2; a_off := -1032 |} 8 (ELit 2147483647); KWord {| a_base := EVar 2; a_off := -1024 |} 8 (ELit 37); KWord {| a_base := EVar 2; a_off := -1016 |} 8 (ELit 1184784); KWord {| a_base := ELit 0; a_off := 6898976 |} 1 (ELit 48); KWord {| a_base := EVar 2; a_off := -832 |} 1 (ELit 48); KWord {| a_base := EVar 2; a_off := -1072 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -1000 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -976 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -992 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -1008 |} 8 (ELit 69053); KWord {| a_base := EVar 2; a_off := -984 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -896 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -464 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 32)); KWord {| a_base := EVar 2; a_off := -968 |} 8 (ELit 18446744072850558157); KWord {| a_base := EVar 2; a_off := -960 |} 8 (ELit 18446744073709486079); KWord {| a_base := EVar 2; a_off := -904 |} 8 (ELit 214748364); KWord {| a_base := EVar 2; a_off := -928 |} 8 (ELit 75913); KWord {| a_base := EVar 2; a_off := -576 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -912 |} 8 (ELit 6896960); KWord {| a_base := EVar 2; a_off := -920 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -936 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-464))); KWord {| a_base := EVar 2; a_off := -952 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-368))); KWord {| a_base := EVar 2; a_off := -944 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-200))); KWord {| a_base := EVar 2; a_off := -568 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -560 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -552 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -544 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -536 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -528 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -520 |} 8 (ELit 5); KWord {| a_base := EVar 2; a_off := -512 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -504 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -496 |} 8 (ELit 6896960); KWord {| a_base := EVar 2; a_off := -488 |} 8 (ELit 85514); KWord {| a_base := EVar 2; a_off := -480 |} 8 (ELit 1293752); KWord {| a_base := EVar 2; a_off := -472 |} 8 (ELit 1184288); KWord {| a_base := EVar 2; a_off := -176 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -192 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -456 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 24)); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 24)); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 1293752); KWord {| a_base := EVar 2; a_off := -112 |} 8 (ELit 85514); KWord {| a_base := EVar 2; a_off := -104 |} 8 (ELit 424640); KWord {| a_base := EVar 2; a_off := -2304 |} 8 (ELit 18446744073709551615); KWord {| a_base := EVar 2; a_off := -2273 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2274 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2275 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2276 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2277 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2278 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2279 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2280 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2281 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2282 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2283 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2284 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2285 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2286 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2287 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2288 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2289 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2290 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2291 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2292 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2293 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2294 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2295 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2296 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2305 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2306 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2307 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2308 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2309 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2310 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2311 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2312 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2368 |} 8 (ELit 10); KWord {| a_base := EVar 2; a_off := -2360 |} 8 (ELit 85514); KWord {| a_base := EVar 2; a_off := -2352 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-96))); KWord {| a_base := EVar 2; a_off := -2344 |} 8 (ELit 422676); KWord {| a_base := EVar 2; a_off := -2328 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-216))); KWord {| a_base := EVar 2; a_off := -2320 |} 8 (ELit 133306); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 24)); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 24)); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 24)); KWord {| a_base := EVar 2; a_off := -64 |} 8 (ELit 85514); KWord {| a_base := EVar 2; a_off := -56 |} 8 (ELit 421712); KWord {| a_base := EVar 2; a_off := -2256 |} 8 (ELit 18446744073709551615); KWord {| a_base := EVar 2; a_off := -2225 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2226 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2227 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2228 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2229 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2230 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2231 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2232 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2233 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2234 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2235 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2236 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2237 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2238 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2239 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2240 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2241 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2242 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2243 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2244 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2245 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2246 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2247 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2248 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2257 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2258 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2259 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2260 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2261 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2262 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2263 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2264 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2272 |} 8 (ELit 83588); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 24)); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 24)); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 688024); KRange (EVar 2) 140735332552704 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -3232 |} (ELit 3232); KUnk {| a_base := EVar 2; a_off := -3232 |} (ELit 864); KUnk {| a_base := EVar 2; a_off := -2336 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -2224 |} (ELit 1072); KUnk {| a_base := EVar 2; a_off := -888 |} (ELit 56); KUnk {| a_base := EVar 2; a_off := -831 |} (ELit 255); KUnk {| a_base := EVar 2; a_off := -448 |} (ELit 248); KUnk {| a_base := EVar 2; a_off := -48 |} (ELit 8); KImg 65536 1282048; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450764 |} (ELit 24); KWord {| a_base := ELit 0; a_off := 2147461560 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147461568 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2148313248 |} 8 (ELit 0); KWr {| a_base := ELit 0; a_off := 1293752 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 1293792 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 6898976 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 6898977 |} (ELit 1); KWord {| a_base := ELit 0; a_off := 1313048 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1906620 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1309752 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1282888 |} 8 (ELit 1209340); KWord {| a_base := ELit 0; a_off := 1282896 |} 8 (ELit 1184024); KWord {| a_base := ELit 0; a_off := 6896960 |} 8 (EVar 40); KWord {| a_base := ELit 0; a_off := 1293892 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1293848 |} 8 (ELit 1024); KWord {| a_base := ELit 0; a_off := 1293784 |} 8 (ELit 6900000); KWord {| a_base := ELit 0; a_off := 1293896 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1313049 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1283272 |} 8 (ELit 1218816); KWord {| a_base := EVar 2; a_off := 24 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 1283280 |} 8 (ELit 1219844)] 56))).
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
Definition ps0 : SR.post_spec := SR.PS 688024 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_10a531_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 406444 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_10a531_b.IT SegItab_Ba_10a531_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 406444 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
