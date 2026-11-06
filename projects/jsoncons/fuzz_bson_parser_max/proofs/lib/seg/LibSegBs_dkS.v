(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Bs0PlanKit Bs0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.seg Require SegItab_Bs_aea5cf.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Bs_aea5cf.ITR.
Definition IT : itab := SegItab_Bs_aea5cf.IT.
Definition ENDS : list Z := [695960; 229136; 229200].
Definition STOPS1 : list Z := [695960; 229136; 229200] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-240))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (EAlu Instr.ALU_ADD (EVar 33) (ELit (42))); EVar 33; EVar 10; EVar 11; EVar 37; EVar 39; EVar 36; EVar 15; EVar 16; EVar 17; (EAlu Instr.ALU_ADD (EVar 33) (EVar 38)); EVar 35; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483312 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-240)) (ELit 240);
   KWord (SA (EVar 2) (-8)) 8 (EVar 60);
   KWord (SA (EVar 2) (-16)) 8 (EVar 61);
   KWord (SA (EVar 2) (-24)) 8 (EVar 62);
   KWord (SA (EVar 2) (-32)) 8 (EVar 63);
   KWord (SA (EVar 2) (-40)) 8 (EVar 64);
   KWord (SA (EVar 2) (-48)) 8 (EVar 65);
   KWord (SA (EVar 2) (-56)) 8 (EVar 66);
   KWord (SA (EVar 2) (-64)) 8 (EVar 67);
   KWord (SA (EVar 2) (-72)) 8 (EVar 68);
   KImg 65536 749064;
   KRange (EVar 38) 0 1;
   KRange (EVar 39) 0 4294967295;
   KWord (SA (ELit 0) 815040) 1 (ELit 1);
   KWord (SA (ELit 0) 815072) 1 (ELit 1);
   KWord (SA (ELit 0) 815016) 1 (ELit 16);
   KUnk (SA (ELit 0) 815017) (ELit 8);
   KWord (SA (ELit 0) 815048) 1 (ELit 6);
   KUnk (SA (ELit 0) 815049) (ELit 3);
   KRange (EVar 33) 4096 140737488355286;
   KWr (SA (EVar 33) 0) (ELit 42);
   KDisj (SA (EVar 2) (-240-96)) (ELit (240+96)) (SA (EVar 33) 0) (ELit 42);
   KDisj (SA (EVar 33) 0) (ELit 42) (SA (ELit 0) 65536) (ELit 892928)].
Definition ss0 : sym_state := SS 229112 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
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
  (([SGA.AStep (SR.SBlock [695960; 229136; 229200; 695960; 229136; 229200])], (91, SS 229124 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-240)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 33) (ELit 42); EVar 33; EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 8589934592) (EVar 39)) (ELit 59); ELit 31; EVar 37; EVar 39; EVar 36; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EVar 33) (EVar 38); EVar 35; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 140735332483312 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -240 |} (ELit 240); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 60); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 63); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 64); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 68); KImg 65536 749064; KRange (EVar 38) 0 1; KRange (EVar 39) 0 4294967295; KWord {| a_base := ELit 0; a_off := 815040 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 815072 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 815016 |} 1 (ELit 16); KUnk {| a_base := ELit 0; a_off := 815017 |} (ELit 8); KWord {| a_base := ELit 0; a_off := 815048 |} 1 (ELit 6); KUnk {| a_base := ELit 0; a_off := 815049 |} (ELit 3); KRange (EVar 33) 4096 140737488355286; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 2; a_off := -336 |} (ELit 336) {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 33; a_off := 0 |} (ELit 42) {| a_base := ELit 0; a_off := 65536 |} (ELit 892928)] 80))).
Definition s1 : sym_state := snd (snd ex1).

(* [comment removed for export] *)
Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

(* [comment removed for export] *)
Definition ex3 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [695960; 229136; 229200; 695960; 229136; 229200])], (93, SS 695960 [ELit 0; ELit 229304; EAlu Instr.ALU_ADD (EVar 2) (ELit (-240)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 42; EVar 33; EVar 33; ELit 815049; ELit 3; EVar 39; EVar 36; EVar 15; EVar 16; EVar 17; ELit 815048; EVar 35; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 8589934592) (EVar 39)) (ELit 59)) (ELit 31)) (ELit 1)) 1 1; KRange (EVar 2) 140735332483312 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -240 |} (ELit 240); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 60); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 63); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 64); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 68); KImg 65536 749064; KRange (EVar 38) 0 1; KRange (EVar 39) 0 4294967295; KWord {| a_base := ELit 0; a_off := 815040 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 815072 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 815016 |} 1 (ELit 16); KUnk {| a_base := ELit 0; a_off := 815017 |} (ELit 8); KWord {| a_base := ELit 0; a_off := 815048 |} 1 (ELit 6); KUnk {| a_base := ELit 0; a_off := 815049 |} (ELit 3); KRange (EVar 33) 4096 140737488355286; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 2; a_off := -336 |} (ELit 336) {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 33; a_off := 0 |} (ELit 42) {| a_base := ELit 0; a_off := 65536 |} (ELit 892928)] 80))).
Definition s3 : sym_state := snd (snd ex3).

(* [comment removed for export] *)
Definition ex4 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [695960; 229136; 229200; 695960; 229136; 229200])], (91, SS 229132 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-240)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 33) (ELit 42); EVar 33; EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 8589934592) (EVar 39)) (ELit 59); ELit 30; EVar 37; EVar 39; EVar 36; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EVar 33) (EVar 38); EVar 35; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 8589934592) (EVar 39)) (ELit 59)) (ELit 31)) (ELit 1)) 0 0; KRange (EVar 2) 140735332483312 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -240 |} (ELit 240); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 60); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 63); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 64); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 68); KImg 65536 749064; KRange (EVar 38) 0 1; KRange (EVar 39) 0 4294967295; KWord {| a_base := ELit 0; a_off := 815040 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 815072 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 815016 |} 1 (ELit 16); KUnk {| a_base := ELit 0; a_off := 815017 |} (ELit 8); KWord {| a_base := ELit 0; a_off := 815048 |} 1 (ELit 6); KUnk {| a_base := ELit 0; a_off := 815049 |} (ELit 3); KRange (EVar 33) 4096 140737488355286; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 2; a_off := -336 |} (ELit 336) {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 33; a_off := 0 |} (ELit 42) {| a_base := ELit 0; a_off := 65536 |} (ELit 892928)] 80))).
Definition s4 : sym_state := snd (snd ex4).

(* [comment removed for export] *)
Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

(* [comment removed for export] *)
Definition ex6 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [695960; 229136; 229200; 695960; 229136; 229200])], (90, SS 229136 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-240)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 33) (ELit 42); EVar 33; EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 8589934592) (EVar 39)) (ELit 59); ELit 30; EVar 37; EVar 39; EVar 36; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EVar 33) (EVar 38); EVar 35; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 8589934592) (EVar 39)) (ELit 59)) (ELit 30)) (ELit 1)) 1 1; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 8589934592) (EVar 39)) (ELit 59)) (ELit 31)) (ELit 1)) 0 0; KRange (EVar 2) 140735332483312 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -240 |} (ELit 240); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 60); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 63); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 64); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 68); KImg 65536 749064; KRange (EVar 38) 0 1; KRange (EVar 39) 0 4294967295; KWord {| a_base := ELit 0; a_off := 815040 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 815072 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 815016 |} 1 (ELit 16); KUnk {| a_base := ELit 0; a_off := 815017 |} (ELit 8); KWord {| a_base := ELit 0; a_off := 815048 |} 1 (ELit 6); KUnk {| a_base := ELit 0; a_off := 815049 |} (ELit 3); KRange (EVar 33) 4096 140737488355286; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 2; a_off := -336 |} (ELit 336) {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 33; a_off := 0 |} (ELit 42) {| a_base := ELit 0; a_off := 65536 |} (ELit 892928)] 80))).
Definition s6 : sym_state := snd (snd ex6).

(* [comment removed for export] *)
Definition ex7 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [695960; 229136; 229200; 695960; 229136; 229200])], (90, SS 229200 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-240)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 33) (ELit 42); EVar 33; EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 8589934592) (EVar 39)) (ELit 59); ELit 30; EVar 37; EVar 39; EVar 36; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EVar 33) (EVar 38); EVar 35; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 8589934592) (EVar 39)) (ELit 59)) (ELit 30)) (ELit 1)) 0 0; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 8589934592) (EVar 39)) (ELit 59)) (ELit 31)) (ELit 1)) 0 0; KRange (EVar 2) 140735332483312 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -240 |} (ELit 240); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 60); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 63); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 64); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 68); KImg 65536 749064; KRange (EVar 38) 0 1; KRange (EVar 39) 0 4294967295; KWord {| a_base := ELit 0; a_off := 815040 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 815072 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 815016 |} 1 (ELit 16); KUnk {| a_base := ELit 0; a_off := 815017 |} (ELit 8); KWord {| a_base := ELit 0; a_off := 815048 |} 1 (ELit 6); KUnk {| a_base := ELit 0; a_off := 815049 |} (ELit 3); KRange (EVar 33) 4096 140737488355286; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 2; a_off := -336 |} (ELit 336) {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 33; a_off := 0 |} (ELit 42) {| a_base := ELit 0; a_off := 65536 |} (ELit 892928)] 80))).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PEnd 2))))).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 695960 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 229136 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

(* [comment removed for export] *)
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 229200 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Bs_aea5cf.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 229112 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_Bs_aea5cf.IT SegItab_Bs_aea5cf.IT_sound BF NX0 BR XSTEP F0 PSS plan 229112 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
