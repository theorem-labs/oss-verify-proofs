(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin As0PlanKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(318444, 1%nat) ; (329040, 690%nat) ; (332772, 54%nat) ; (344208, 102%nat) ; (385232, 1%nat) ; (389840, 380%nat) ; (421860, 40%nat) ; (463712, 24%nat) ; (463892, 13%nat) ; (464052, 7%nat) ; (798124, 100%nat) ; (800592, 21%nat) ; (800676, 78%nat) ; (801848, 108%nat) ; (802280, 908%nat) ; (805912, 16%nat) ; (805976, 61%nat) ; (833320, 257%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [798184].
Definition STOPS1 : list Z := [798184] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 580684; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 892832; ELit 107977; ELit 67108864; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-3248)) (ELit 3248);
   KUnk (SA (EVar 2) (-3248)) (ELit 3248);
   KImg 65536 880640;
   KZero (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) (2147450760)) (ELit 80);
   KWord (SA (ELit 0) (2147464376)) 8 (ELit 0);
   KWr (SA (ELit 0) (892832)) (ELit 4);
   KWr (SA (ELit 0) (892840)) (ELit 8);
   KWr (SA (ELit 0) (892848)) (ELit 8);
   KWr (SA (ELit 0) (892864)) (ELit 8);
   KWr (SA (ELit 0) (892872)) (ELit 8);
   KWr (SA (ELit 0) (892888)) (ELit 8);
   KWr (SA (ELit 0) (892920)) (ELit 8);
   KWr (SA (ELit 0) (892928)) (ELit 8);
   KWr (SA (ELit 0) (892968)) (ELit 4);
   KWord (SA (ELit 0) (911384)) 1 (ELit 1);
   KWord (SA (ELit 0) (1504956)) 1 (ELit 1);
   KWord (SA (ELit 0) (908088)) 8 (ELit 2147450880);
   KWord (SA (ELit 0) (882416)) 8 (ELit 801848);
   KWord (SA (ELit 0) (6491464)) 8 (EVar 40);
   KWord (SA (ELit 0) (892972)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (892832)) 4 (ELit 5);
   KWord (SA (ELit 0) (892928)) 8 (ELit 0);
   KWord (SA (ELit 0) (892920)) 8 (ELit 6493200);
   KWord (SA (ELit 0) (892968)) 4 (ELit 0);
   KWord (SA (ELit 0) (892976)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (911385)) 1 (ELit 1);
   KWord (SA (ELit 0) (882704)) 8 (ELit 833320);
   KWord (SA (ELit 0) (892904)) 8 (ELit 798124)].
Definition ss0 : sym_state := SS 318444 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3248), ELit 3248); (ELit 0, (892832), ELit 4); (ELit 0, (892840), ELit 8); (ELit 0, (892848), ELit 8); (ELit 0, (892864), ELit 8); (ELit 0, (892872), ELit 8); (ELit 0, (892888), ELit 8); (ELit 0, (892920), ELit 8); (ELit 0, (892928), ELit 8); (ELit 0, (892968), ELit 4)].
Definition F0L : list SR.region := [(EVar 2, (-3248), 3248); (ELit 0, (892832), 4); (ELit 0, (892840), 8); (ELit 0, (892848), 8); (ELit 0, (892864), 8); (ELit 0, (892872), 8); (ELit 0, (892888), 8); (ELit 0, (892920), 8); (ELit 0, (892928), 8); (ELit 0, (892968), 4)].
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
  (([SGA.AStep (SR.SBlock [798184; 798184])], (93, SS 798184 [ELit 0; ELit 802144; EAlu Instr.ALU_ADD (EVar 2) (ELit (-592)); EVar 3; EVar 4; EAlu Instr.ALU_ADD (EVar 2) (ELit (-427)); ELit 114; ELit 101; ELit 0; ELit 892832; EVar 40; ELit 0; ELit 0; ELit 798124; ELit 0; ELit 115; ELit 101; ELit 100; ELit 6491464; ELit 1; ELit 6493200; ELit 6491464; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; ELit 102; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -552 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -544 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -536 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -528 |} 8 (ELit 6493200); KWord {| a_base := EVar 2; a_off := -520 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -512 |} 8 (ELit 6491464); KWord {| a_base := EVar 2; a_off := -504 |} 8 (ELit 38); KWord {| a_base := EVar 2; a_off := -496 |} 8 (ELit 892832); KWord {| a_base := EVar 2; a_off := -488 |} 8 (ELit 802144); KWord {| a_base := ELit 0; a_off := 892872 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-426))); KWord {| a_base := EVar 2; a_off := -427 |} 1 (ELit 10); KWord {| a_base := EVar 2; a_off := -428 |} 1 (ELit 100); KWord {| a_base := EVar 2; a_off := -429 |} 1 (ELit 101); KWord {| a_base := EVar 2; a_off := -430 |} 1 (ELit 115); KWord {| a_base := EVar 2; a_off := -431 |} 1 (ELit 117); KWord {| a_base := EVar 2; a_off := -432 |} 1 (ELit 102); KWord {| a_base := EVar 2; a_off := -433 |} 1 (ELit 101); KWord {| a_base := EVar 2; a_off := -434 |} 1 (ELit 114); KWord {| a_base := EVar 2; a_off := -435 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := -436 |} 1 (ELit 44); KWord {| a_base := EVar 2; a_off := -437 |} 1 (ELit 115); KWord {| a_base := EVar 2; a_off := -438 |} 1 (ELit 101); KWord {| a_base := EVar 2; a_off := -439 |} 1 (ELit 116); KWord {| a_base := EVar 2; a_off := -440 |} 1 (ELit 121); KWord {| a_base := EVar 2; a_off := -441 |} 1 (ELit 98); KWord {| a_base := EVar 2; a_off := -442 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := -1168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -1160 |} 8 (ELit 107993); KWord {| a_base := EVar 2; a_off := -1152 |} 8 (ELit 16); KWord {| a_base := EVar 2; a_off := -1144 |} 8 (ELit 108009); KWord {| a_base := EVar 2; a_off := -1136 |} 8 (ELit 892832); KWord {| a_base := EVar 2; a_off := -1128 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -1120 |} 8 (ELit 107993); KWord {| a_base := EVar 2; a_off := -1112 |} 8 (ELit 16); KWord {| a_base := EVar 2; a_off := -1104 |} 8 (ELit 892832); KWord {| a_base := EVar 2; a_off := -1096 |} 8 (ELit 800936); KWord {| a_base := EVar 2; a_off := -1080 |} 8 (ELit 108009); KWord {| a_base := EVar 2; a_off := -1072 |} 8 (ELit 892832); KWord {| a_base := EVar 2; a_off := -1064 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -1056 |} 8 (ELit 2147483625); KWord {| a_base := EVar 2; a_off := -1048 |} 8 (ELit 2147483647); KWord {| a_base := EVar 2; a_off := -1040 |} 8 (ELit 37); KWord {| a_base := EVar 2; a_off := -1032 |} 8 (ELit 802608); KWord {| a_base := EVar 2; a_off := -443 |} 1 (ELit 52); KWord {| a_base := EVar 2; a_off := -444 |} 1 (ELit 54); KWord {| a_base := EVar 2; a_off := -445 |} 1 (ELit 56); KWord {| a_base := EVar 2; a_off := -446 |} 1 (ELit 56); KWord {| a_base := EVar 2; a_off := -447 |} 1 (ELit 48); KWord {| a_base := EVar 2; a_off := -448 |} 1 (ELit 49); KWord {| a_base := EVar 2; a_off := -449 |} 1 (ELit 55); KWord {| a_base := EVar 2; a_off := -450 |} 1 (ELit 54); KWord {| a_base := EVar 2; a_off := -1016 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -992 |} 8 (ELit 8); KWord {| a_base := EVar 2; a_off := -1008 |} 8 (ELit 8); KWord {| a_base := EVar 2; a_off := -856 |} 1 (ELit 54); KWord {| a_base := EVar 2; a_off := -1024 |} 8 (ELit 68858); KWord {| a_base := EVar 2; a_off := -855 |} 1 (ELit 55); KWord {| a_base := EVar 2; a_off := -854 |} 1 (ELit 49); KWord {| a_base := EVar 2; a_off := -853 |} 1 (ELit 48); KWord {| a_base := EVar 2; a_off := -852 |} 1 (ELit 56); KWord {| a_base := EVar 2; a_off := -851 |} 1 (ELit 56); KWord {| a_base := EVar 2; a_off := -850 |} 1 (ELit 54); KWord {| a_base := EVar 2; a_off := -849 |} 1 (ELit 52); KWord {| a_base := EVar 2; a_off := -1000 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -912 |} 8 (ELit 67108864); KWord {| a_base := EVar 2; a_off := -480 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-40))); KWord {| a_base := EVar 2; a_off := -451 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := -452 |} 1 (ELit 61); KWord {| a_base := EVar 2; a_off := -453 |} 1 (ELit 62); KWord {| a_base := EVar 2; a_off := -454 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := -455 |} 1 (ELit 116); KWord {| a_base := EVar 2; a_off := -456 |} 1 (ELit 117); KWord {| a_base := EVar 2; a_off := -457 |} 1 (ELit 112); KWord {| a_base := EVar 2; a_off := -458 |} 1 (ELit 110); KWord {| a_base := EVar 2; a_off := -459 |} 1 (ELit 105); KWord {| a_base := EVar 2; a_off := -460 |} 1 (ELit 32); KWord {| a_base := EVar 2; a_off := -461 |} 1 (ELit 58); KWord {| a_base := EVar 2; a_off := -462 |} 1 (ELit 105); KWord {| a_base := EVar 2; a_off := -463 |} 1 (ELit 108); KWord {| a_base := EVar 2; a_off := -464 |} 1 (ELit 99); KWord {| a_base := EVar 2; a_off := -984 |} 8 (ELit 18446744072850558157); KWord {| a_base := EVar 2; a_off := -976 |} 8 (ELit 18446744073709486079); KWord {| a_base := EVar 2; a_off := -920 |} 8 (ELit 214748364); KWord {| a_base := EVar 2; a_off := -944 |} 8 (ELit 75913); KWord {| a_base := EVar 2; a_off := -592 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -928 |} 8 (ELit 6491464); KWord {| a_base := EVar 2; a_off := -936 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -952 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-480))); KWord {| a_base := EVar 2; a_off := -968 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-384))); KWord {| a_base := EVar 2; a_off := -960 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-216))); KWord {| a_base := EVar 2; a_off := -584 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -576 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -568 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -560 |} 8 (EVar 24); KWord {| a_base := ELit 0; a_off := 892864 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-384))); KWord {| a_base := ELit 0; a_off := 892848 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 892840 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 892888 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-464))); KWord {| a_base := ELit 0; a_off := 892968 |} 4 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 892928 |} 8 (ELit 80); KWord {| a_base := ELit 0; a_off := 892920 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-464))); KWord {| a_base := ELit 0; a_off := 892832 |} 4 (ELit 5); KWord {| a_base := EVar 2; a_off := -192 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -208 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -216 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -472 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -168 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 892832); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 107977); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 332964); KWord {| a_base := EVar 2; a_off := -2320 |} 8 (ELit 18446744073709551615); KWord {| a_base := EVar 2; a_off := -2289 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2290 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2291 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2292 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2293 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2294 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2295 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2296 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2297 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2298 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2299 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2300 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2301 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2302 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2303 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2304 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2305 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2306 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2307 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2308 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2309 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2310 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2311 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2312 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2321 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2322 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2323 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2324 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2325 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2326 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2327 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2328 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -2384 |} 8 (ELit 10); KWord {| a_base := EVar 2; a_off := -2376 |} 8 (ELit 107991); KWord {| a_base := EVar 2; a_off := -2368 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-112))); KWord {| a_base := EVar 2; a_off := -2360 |} 8 (ELit 329948); KWord {| a_base := EVar 2; a_off := -2344 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-232))); KWord {| a_base := EVar 2; a_off := -2336 |} 8 (ELit 131724); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 15); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 14); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 13); KWord {| a_base := EVar 2; a_off := -48 |} 8 (ELit 67108864); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 17); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 16); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -56 |} 8 (ELit 580684); KRange (EVar 2) 140735332552704 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -3248 |} (ELit 3248); KUnk {| a_base := EVar 2; a_off := -3248 |} (ELit 864); KUnk {| a_base := EVar 2; a_off := -2352 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -2288 |} (ELit 1120); KUnk {| a_base := EVar 2; a_off := -1088 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -904 |} (ELit 48); KUnk {| a_base := EVar 2; a_off := -848 |} (ELit 256); KUnk {| a_base := EVar 2; a_off := -426 |} (ELit 210); KUnk {| a_base := EVar 2; a_off := -112 |} (ELit 8); KImg 65536 880640; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450760 |} (ELit 80); KWord {| a_base := ELit 0; a_off := 2147464376 |} 8 (ELit 0); KWr {| a_base := ELit 0; a_off := 892832 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 892840 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 892848 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 892864 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 892872 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 892888 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 892920 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 892928 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 892968 |} (ELit 4); KWord {| a_base := ELit 0; a_off := 911384 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1504956 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 908088 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 882416 |} 8 (ELit 801848); KWord {| a_base := ELit 0; a_off := 6491464 |} 8 (EVar 40); KWord {| a_base := ELit 0; a_off := 892972 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 892976 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 911385 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 882704 |} 8 (ELit 833320); KWord {| a_base := ELit 0; a_off := 892904 |} 8 (ELit 798124)] 140))).
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
Definition ps0 : SR.post_spec := SR.PS 798184 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 318444 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 318444 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
