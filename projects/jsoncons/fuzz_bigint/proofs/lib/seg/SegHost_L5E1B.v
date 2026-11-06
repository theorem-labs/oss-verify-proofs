(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Src0PlanKit Src0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require SegItab_S_66c025.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LibSegZ_e1c1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_66c025.ITR.
Definition IT : itab := SegItab_S_66c025.IT.
Definition ENDS : list Z := [309572].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; ELit 22; ELit 390752; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-1280)) (ELit 1280);
   KUnk (SA (EVar 2) (-1280)) (ELit 1280);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 160);
   KUnk (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 2) (-1280)) (ELit 1280) (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 10) (-128)) (ELit 160) (SA (ELit 0) 65536) (ELit 528384);
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (ELit 0) (459668)) 4 (EVar 35);
   KWr (SA (ELit 0) (459668)) (ELit 4);
   KWord (SA (ELit 0) (459784)) 8 (ELit 591616);
   KWord (SA (ELit 0) (591656)) 8 (ELit 0);
   KWord (SA (EVar 2) (-1152)) 8 (EVar 40);
   KWord (SA (EVar 2) (-40)) 8 (EVar 41)].
Definition ss0 : sym_state := SS 133708 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-1280), ELit 1280); (EVar 10, (0), ELit 8); (ELit 0, (459668), ELit 4)].
Definition F0L : list SR.region := [(EVar 2, (-1280), 1280); (EVar 10, (0), 8); (ELit 0, (459668), 4)].
Definition BF : nat := 200000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).

(* [comment removed for export] *)
Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309572])], (93, SS 364652 [ELit 0; ELit 364540; EAlu Instr.ALU_ADD (EVar 2) (ELit (-1216)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168)); ELit 88564; ELit 88564; ELit 0; ELit 87904; ELit 264232; EVar 14; EVar 15; EVar 16; EVar 17; ELit 1024; ELit 22; EExt true 0 4 (EVar 35); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -1216 |} 8 (ELit 459668); KWord {| a_base := EVar 2; a_off := -1208 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168))); KWord {| a_base := EVar 2; a_off := -1200 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-56))); KWord {| a_base := EVar 2; a_off := -1192 |} 8 (ELit 263848); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -112 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -104 |} 8 (ELit 264340); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -80 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 266940); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 133712); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -1280 |} (ELit 1280); KUnk {| a_base := EVar 2; a_off := -1280 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -1184 |} (ELit 1040); KUnk {| a_base := EVar 2; a_off := -96 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -64 |} (ELit 32); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 2; a_off := -1280 |} (ELit 1280) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := ELit 0; a_off := 459668 |} 4 (EVar 35); KWr {| a_base := ELit 0; a_off := 459668 |} (ELit 4); KWord {| a_base := ELit 0; a_off := 459784 |} 8 (ELit 591616); KWord {| a_base := ELit 0; a_off := 591656 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -1152 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 41)] 56))).
Definition s1 : sym_state := snd (snd ex1).

(* [comment removed for export] *)
Definition s2 : sym_state :=
  (SS 364540 [ELit 0; ELit 364540; EAlu Instr.ALU_ADD (EVar 2) (ELit (-1216)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168)); ELit 88564; ELit 16; EVar 56; EVar 57; EVar 58; EVar 59; EVar 60; EVar 61; EVar 17; ELit 1024; ELit 22; EExt true 0 4 (EVar 35); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -1216 |} 8 (ELit 459668); KWord {| a_base := EVar 2; a_off := -1208 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168))); KWord {| a_base := EVar 2; a_off := -1200 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-56))); KWord {| a_base := EVar 2; a_off := -1192 |} 8 (ELit 263848); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -112 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -104 |} 8 (ELit 264340); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -80 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 266940); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 133712); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -1280 |} (ELit 1280); KUnk {| a_base := EVar 2; a_off := -1280 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -1184 |} (ELit 1040); KUnk {| a_base := EVar 2; a_off := -96 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -64 |} (ELit 32); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 2; a_off := -1280 |} (ELit 1280) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := ELit 0; a_off := 459668 |} 4 (EVar 35); KWr {| a_base := ELit 0; a_off := 459668 |} (ELit 4); KWord {| a_base := ELit 0; a_off := 459784 |} 8 (ELit 591616); KWord {| a_base := ELit 0; a_off := 591656 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -1152 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 41)] 62).

(* [comment removed for export] *)
Definition ex3 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309572]); SGA.AStep SR.SCopy; SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309572])], (93, SS 364652 [ELit 0; ELit 263928; EAlu Instr.ALU_ADD (EVar 2) (ELit (-1184)); ELit 67584; ELit 459832; EVar 63; EVar 64; EVar 65; EAlu Instr.ALU_ADD (EVar 2) (ELit (-56)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168)); EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; EVar 72; EVar 73; ELit 459668; ELit 22; EExt true 0 4 (EVar 35); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 74; EVar 75; EVar 76; EVar 77] [] [KWord {| a_base := ELit 0; a_off := 459668 |} 4 (EExt true 0 4 (EVar 35)); KWord {| a_base := EVar 2; a_off := -1168 |} 8 (ELit 2334106421097295433); KWord {| a_base := EVar 2; a_off := -1160 |} 8 (ELit 8389754676633367137); KWord {| a_base := EVar 2; a_off := -1152 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -1216 |} 8 (ELit 459668); KWord {| a_base := EVar 2; a_off := -1208 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168))); KWord {| a_base := EVar 2; a_off := -1200 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-56))); KWord {| a_base := EVar 2; a_off := -1192 |} 8 (ELit 263848); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -112 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -104 |} 8 (ELit 264340); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -80 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 266940); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 133712); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -1280 |} (ELit 1280); KUnk {| a_base := EVar 2; a_off := -1280 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -1184 |} (ELit 16); KUnk {| a_base := EVar 2; a_off := -1151 |} (ELit 1007); KUnk {| a_base := EVar 2; a_off := -96 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -64 |} (ELit 32); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 2; a_off := -1280 |} (ELit 1280) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWr {| a_base := ELit 0; a_off := 459668 |} (ELit 4); KWord {| a_base := ELit 0; a_off := 459784 |} 8 (ELit 591616); KWord {| a_base := ELit 0; a_off := 591656 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 41)] 78))).
Definition s3 : sym_state := snd (snd ex3).

(* [comment removed for export] *)
Definition s4 : sym_state :=
  (SS 263928 [ELit 0; ELit 263928; EAlu Instr.ALU_ADD (EVar 2) (ELit (-1184)); ELit 67584; ELit 459832; EVar 63; EVar 64; EVar 65; EAlu Instr.ALU_ADD (EVar 2) (ELit (-56)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168)); ELit 16; EVar 78; EVar 79; EVar 80; EVar 81; EVar 82; EVar 83; EVar 73; ELit 459668; ELit 22; EExt true 0 4 (EVar 35); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 74; EVar 75; EVar 76; EVar 77] [] [KWord {| a_base := ELit 0; a_off := 459668 |} 4 (EExt true 0 4 (EVar 35)); KWord {| a_base := EVar 2; a_off := -1168 |} 8 (ELit 2334106421097295433); KWord {| a_base := EVar 2; a_off := -1160 |} 8 (ELit 8389754676633367137); KWord {| a_base := EVar 2; a_off := -1152 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -1216 |} 8 (ELit 459668); KWord {| a_base := EVar 2; a_off := -1208 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168))); KWord {| a_base := EVar 2; a_off := -1200 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-56))); KWord {| a_base := EVar 2; a_off := -1192 |} 8 (ELit 263848); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -112 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -104 |} 8 (ELit 264340); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -80 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 266940); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 133712); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -1280 |} (ELit 1280); KUnk {| a_base := EVar 2; a_off := -1280 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -1184 |} (ELit 16); KUnk {| a_base := EVar 2; a_off := -1151 |} (ELit 1007); KUnk {| a_base := EVar 2; a_off := -96 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -64 |} (ELit 32); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 2; a_off := -1280 |} (ELit 1280) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWr {| a_base := ELit 0; a_off := 459668 |} (ELit 4); KWord {| a_base := ELit 0; a_off := 459784 |} 8 (ELit 591616); KWord {| a_base := ELit 0; a_off := 591656 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 41)] 84).

(* [comment removed for export] *)
Definition ex5 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309572]); SGA.AStep SR.SCopy; SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309572])], (93, SS 364652 [ELit 0; ELit 263448; EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)); ELit 67584; ELit 459832; EVar 85; EVar 86; EVar 87; EVar 10; EAlu Instr.ALU_ADD (EVar 2) (ELit (-55)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-55)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-56)); EVar 90; EVar 91; EVar 92; EVar 93; EVar 94; EVar 95; ELit 22; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 96; EVar 97; EVar 98; EVar 99] [] [KWord {| a_base := EVar 10; a_off := 0 |} 8 (ELit 385144); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -96 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -80 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 266968); KWord {| a_base := EVar 2; a_off := -39 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -55 |} 8 (ELit 2334106421097295433); KWord {| a_base := EVar 2; a_off := -47 |} 8 (ELit 8389754676633367137); KWord {| a_base := EVar 2; a_off := -56 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 459668 |} 4 (EExt true 0 4 (EVar 35)); KWord {| a_base := EVar 2; a_off := -1168 |} 8 (ELit 2334106421097295433); KWord {| a_base := EVar 2; a_off := -1160 |} 8 (ELit 8389754676633367137); KWord {| a_base := EVar 2; a_off := -1152 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -1216 |} 8 (ELit 459668); KWord {| a_base := EVar 2; a_off := -1208 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168))); KWord {| a_base := EVar 2; a_off := -1200 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-56))); KWord {| a_base := EVar 2; a_off := -1192 |} 8 (ELit 263848); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -112 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 133712); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -1280 |} (ELit 1280); KUnk {| a_base := EVar 2; a_off := -1280 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -1184 |} (ELit 16); KUnk {| a_base := EVar 2; a_off := -1151 |} (ELit 1007); KUnk {| a_base := EVar 2; a_off := -64 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -38 |} (ELit 6); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 128); KUnk {| a_base := EVar 10; a_off := 8 |} (ELit 24); KDisj {| a_base := EVar 2; a_off := -1280 |} (ELit 1280) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWr {| a_base := ELit 0; a_off := 459668 |} (ELit 4); KWord {| a_base := ELit 0; a_off := 459784 |} 8 (ELit 591616); KWord {| a_base := ELit 0; a_off := 591656 |} 8 (ELit 0)] 100))).
Definition s5 : sym_state := snd (snd ex5).

(* [comment removed for export] *)
Definition s6 : sym_state :=
  (SS 263448 [ELit 0; ELit 263448; EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)); ELit 67584; ELit 459832; EVar 85; EVar 86; EVar 87; EVar 10; EAlu Instr.ALU_ADD (EVar 2) (ELit (-55)); ELit 16; EVar 100; EVar 101; EVar 102; EVar 103; EVar 104; EVar 105; EVar 95; ELit 22; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 96; EVar 97; EVar 98; EVar 99] [] [KWord {| a_base := EVar 10; a_off := 0 |} 8 (ELit 385144); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -96 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -80 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 266968); KWord {| a_base := EVar 2; a_off := -39 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -55 |} 8 (ELit 2334106421097295433); KWord {| a_base := EVar 2; a_off := -47 |} 8 (ELit 8389754676633367137); KWord {| a_base := EVar 2; a_off := -56 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 459668 |} 4 (EExt true 0 4 (EVar 35)); KWord {| a_base := EVar 2; a_off := -1168 |} 8 (ELit 2334106421097295433); KWord {| a_base := EVar 2; a_off := -1160 |} 8 (ELit 8389754676633367137); KWord {| a_base := EVar 2; a_off := -1152 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -1216 |} 8 (ELit 459668); KWord {| a_base := EVar 2; a_off := -1208 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168))); KWord {| a_base := EVar 2; a_off := -1200 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-56))); KWord {| a_base := EVar 2; a_off := -1192 |} 8 (ELit 263848); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -112 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 133712); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -1280 |} (ELit 1280); KUnk {| a_base := EVar 2; a_off := -1280 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -1184 |} (ELit 16); KUnk {| a_base := EVar 2; a_off := -1151 |} (ELit 1007); KUnk {| a_base := EVar 2; a_off := -64 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -38 |} (ELit 6); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 128); KUnk {| a_base := EVar 10; a_off := 8 |} (ELit 24); KDisj {| a_base := EVar 2; a_off := -1280 |} (ELit 1280) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWr {| a_base := ELit 0; a_off := 459668 |} (ELit 4); KWord {| a_base := ELit 0; a_off := 459784 |} 8 (ELit 591616); KWord {| a_base := ELit 0; a_off := 591656 |} 8 (ELit 0)] 106).

(* [comment removed for export] *)
Definition ex7 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309572])], (93, SS 309572 [ELit 0; ELit 368844; EAlu Instr.ALU_ADD (EVar 2) (ELit (-128)); ELit 67584; ELit 459832; EVar 85; EVar 86; EVar 87; ELit 41; EAlu Instr.ALU_ADD (EVar 2) (ELit (-55)); ELit 41; EVar 100; EVar 101; EVar 102; EVar 103; EVar 104; EVar 105; EVar 95; ELit 16; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 96; EVar 97; EVar 98; EVar 99] [] [KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 263460); KWord {| a_base := EVar 10; a_off := 0 |} 8 (ELit 385144); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -96 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -80 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 266968); KWord {| a_base := EVar 2; a_off := -39 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -55 |} 8 (ELit 2334106421097295433); KWord {| a_base := EVar 2; a_off := -47 |} 8 (ELit 8389754676633367137); KWord {| a_base := EVar 2; a_off := -56 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 459668 |} 4 (EExt true 0 4 (EVar 35)); KWord {| a_base := EVar 2; a_off := -1168 |} 8 (ELit 2334106421097295433); KWord {| a_base := EVar 2; a_off := -1160 |} 8 (ELit 8389754676633367137); KWord {| a_base := EVar 2; a_off := -1152 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -1216 |} 8 (ELit 459668); KWord {| a_base := EVar 2; a_off := -1208 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-1168))); KWord {| a_base := EVar 2; a_off := -1200 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-56))); KWord {| a_base := EVar 2; a_off := -1192 |} 8 (ELit 263848); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -112 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 133712); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -1280 |} (ELit 1280); KUnk {| a_base := EVar 2; a_off := -1280 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -1184 |} (ELit 16); KUnk {| a_base := EVar 2; a_off := -1151 |} (ELit 1007); KUnk {| a_base := EVar 2; a_off := -64 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -38 |} (ELit 6); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 128); KUnk {| a_base := EVar 10; a_off := 8 |} (ELit 24); KDisj {| a_base := EVar 2; a_off := -1280 |} (ELit 1280) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWr {| a_base := ELit 0; a_off := 459668 |} (ELit 4); KWord {| a_base := ELit 0; a_off := 459784 |} 8 (ELit 591616); KWord {| a_base := ELit 0; a_off := 591656 |} 8 (ELit 0)] 106))).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PStep (SR.SStrlen (16)) (SGA.mkplan (fst ex3) (SGP.PStep (SR.SStrlen (16)) (SGA.mkplan (fst ex5) (SGP.PStep (SR.SStrlen (16)) (SGA.mkplan (fst ex7) (SGP.PEnd 0))))))).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s7).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s7).
Definition ps0 : SR.post_spec := SR.PS 309572 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_66c025.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 133708 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_66c025.IT SegItab_S_66c025.IT_sound BF NX0 BR XSTEP F0 PSS plan 133708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e1c1.

Module LibSegZ_e1c2.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_66c025.ITR.
Definition IT : itab := SegItab_S_66c025.IT.
Definition ENDS : list Z := [133732].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-128)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EAlu Instr.ALU_ADD (EVar 2) (ELit (-55)); EVar 37; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; ELit 16; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-192)) (ELit 64);
   KUnk (SA (EVar 2) (-192)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 160);
   KUnk (SA (EVar 10) (-128)) (ELit 160);
   KRange (EVar 37) 4096 140737488355328;
   KAlign (EVar 37) 16;
   KWr (SA (EVar 37) 0) (ELit 41);
   KUnk (SA (EVar 37) 0) (ELit 41);
   KDisj (SA (EVar 2) (-192)) (ELit 192) (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 10) (-128)) (ELit 160) (SA (EVar 37) 0) (ELit 41);
   KDisj (SA (EVar 2) (-192)) (ELit 192) (SA (EVar 37) 0) (ELit 41);
   KDisj (SA (EVar 10) (-128)) (ELit 160) (SA (ELit 0) 65536) (ELit 528384);
   KDisj (SA (EVar 37) 0) (ELit 41) (SA (ELit 0) 65536) (ELit 528384);
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (-120)) 8 (ELit 263460);
   KWord (SA (EVar 2) (-128)) 8 (EVar 10);
   KWord (SA (EVar 2) (-56)) 8 (ELit 7235433442201979168);
   KWord (SA (EVar 2) (-48)) 8 (ELit 7954884667833999648);
   KWord (SA (EVar 2) (-40)) 2 (ELit 116);
   KWord (SA (EVar 2) (-72)) 8 (ELit 266968);
   KWord (SA (EVar 2) (-80)) 8 (ELit 390752);
   KWord (SA (EVar 2) (-88)) 8 (EVar 10);
   KWord (SA (EVar 2) (-96)) 8 (ELit 22);
   KWord (SA (EVar 2) (-104)) 8 (EVar 19);
   KWord (SA (EVar 2) (-8)) 8 (ELit 133712);
   KWord (SA (EVar 2) (-16)) 8 (EVar 10);
   KWord (SA (EVar 2) (-24)) 8 (ELit 22);
   KWord (SA (EVar 2) (-32)) 8 (EVar 41)].
Definition ss0 : sym_state := SS 368844 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-192), ELit 64); (EVar 10, (0), ELit 32); (EVar 37, (0), ELit 41)].
Definition F0L : list SR.region := [(EVar 2, (-192), 64); (EVar 10, (0), 32); (EVar 37, (0), 41)].
Definition BF : nat := 200000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).

(* [comment removed for export] *)
Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 133732]); SGA.AStep SR.SCopy; SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 133732])], (93, SS 133732 [ELit 0; ELit 133712; EVar 2; ELit 67584; ELit 459832; EVar 57; EVar 58; EVar 59; EVar 10; ELit 22; EVar 10; ELit 385840; ELit 267080; EVar 63; EVar 64; EVar 65; EVar 66; EVar 67; EVar 41; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 68; EVar 69; EVar 70; EVar 71] [] [KWord {| a_base := EVar 10; a_off := 24 |} 8 (ELit 390752); KWord {| a_base := EVar 10; a_off := 16 |} 4 (ELit 22); KWord {| a_base := EVar 10; a_off := 0 |} 8 (ELit 385816); KWord {| a_base := EVar 10; a_off := 8 |} 8 (EAlu Instr.ALU_ADD (EVar 37) (ELit 24)); KWord {| a_base := EVar 37; a_off := 24 |} 8 (ELit 2334106421097295433); KWord {| a_base := EVar 37; a_off := 32 |} 8 (ELit 8389754676633367137); KWord {| a_base := EVar 37; a_off := 40 |} 1 (ELit 0); KWord {| a_base := EVar 37; a_off := 16 |} 4 (ELit 0); KWord {| a_base := EVar 37; a_off := 8 |} 8 (ELit 16); KWord {| a_base := EVar 37; a_off := 0 |} 8 (ELit 16); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -192 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -192 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 128); KUnk {| a_base := EVar 10; a_off := 20 |} (ELit 4); KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 16; KWr {| a_base := EVar 37; a_off := 0 |} (ELit 41); KUnk {| a_base := EVar 37; a_off := 20 |} (ELit 4); KUnk {| a_base := EVar 37; a_off := 41 |} (ELit 0); KDisj {| a_base := EVar 2; a_off := -192 |} (ELit 192) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := EVar 37; a_off := 0 |} (ELit 41); KDisj {| a_base := EVar 2; a_off := -192 |} (ELit 192) {| a_base := EVar 37; a_off := 0 |} (ELit 41); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KDisj {| a_base := EVar 37; a_off := 0 |} (ELit 41) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 263460); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -56 |} 8 (ELit 7235433442201979168); KWord {| a_base := EVar 2; a_off := -48 |} 8 (ELit 7954884667833999648); KWord {| a_base := EVar 2; a_off := -40 |} 2 (ELit 116); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 266968); KWord {| a_base := EVar 2; a_off := -80 |} 8 (ELit 390752); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -96 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 133712); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -24 |} 8 (ELit 22); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 41)] 72))).
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
Definition ps0 : SR.post_spec := SR.PS 133732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_66c025.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 368844 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_66c025.IT SegItab_S_66c025.IT_sound BF NX0 BR XSTEP F0 PSS plan 368844 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e1c2.
