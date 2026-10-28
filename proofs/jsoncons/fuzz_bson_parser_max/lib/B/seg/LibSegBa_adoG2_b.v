(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_ded56e_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_ded56e_b.ITR.
Definition IT : itab := SegItab_Ba_ded56e_b.IT.
Definition ENDS : list Z := [738060; 738992].
Definition STOPS1 : list Z := [738060; 738992] ++ ENDS.
Definition NX0 : nat := 100.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-256))); EVar 3; EVar 4; ELit 36; EVar 6; EVar 7; (EVar 2); (EAlu Instr.ALU_ADD (EVar 2) (ELit (-256))); (EVar 77); EVar 11; (EVar 76); (ELit 0); EVar 14; (ELit 2); (EVar 75); (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 77)) (EMd Instr.M_MUL (ELit 4) (EVar 76))) (ELit (-1))) (ELit 2)); (EVar 77); ELit 2147450880; (EVar 33); EVar 21; EVar 22; (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit 2147450880)); EVar 24; EVar 25; EVar 26; (EVar 50); EVar 28; EVar 29; (EVar 38); EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487296 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-256)) (ELit 256);
   KRange (EVar 77) 4096 140737488355320;
   KAlign (EVar 77) 4;
   KZero (SA (EAlu Instr.ALU_SRL (EVar 77) (ELit 3)) 2147450880) (ELit 1);
   KWord (SA (EVar 77) 0) 1 (EVar 80);
   KRange (EVar 80) 0 9;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 77) 0) (ELit 4);
   KRange (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 4096 140737488355321;
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) (ELit 3)) 2147450880) (ELit 1);
   KWr (SA (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 0) (ELit 1);
   KDisj (SA (EVar 2) (-256)) (ELit 256) (SA (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 0) (ELit 1);
   KDisj (SA (ELit 0) 65536) (ELit 6840320) (SA (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 0) (ELit 1);
   KDisj (SA (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 0) (ELit 1) (SA (EVar 77) 0) (ELit 4);
   KRange (EVar 75) 1 36;
   KRange (EVar 79) 0 1;
   KRange (EVar 76) 0 35;
   KRange (EVar 38) 4096 140737488355280].
Definition ss0 : sym_state := SS 738060 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 38) (EVar 76)), (0), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 38) (EVar 76)), (0), 1)].
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
Definition s1 : sym_state :=
  SS 738124 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; ELit 36; EAlu Instr.ALU_ADD (EVar 80) (ELit 48); ELit 0; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 77; EAlu Instr.ALU_ADD (EVar 38) (EVar 76); EVar 76; ELit 0; EVar 14; ELit 2; EVar 75; EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 77)) (EMd Instr.M_MUL (ELit 4) (EVar 76))) (ELit (-1))) (ELit 2); EVar 77; ELit 2147450880; EVar 33; EVar 21; EVar 22; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EVar 76) (ELit 1); EVar 25; EVar 26; EVar 50; EVar 28; EVar 29; EVar 38; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} 1 (EAlu Instr.ALU_ADD (EVar 80) (ELit 48)); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 77) 4096 140737488355320; KAlign (EVar 77) 4; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 77) (ELit 3); a_off := 2147450880 |} (ELit 1); KWord {| a_base := EVar 77; a_off := 0 |} 1 (EVar 80); KRange (EVar 80) 0 9; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 4096 140737488355321; KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) (ELit 3); a_off := 2147450880 |} (ELit 1); KWr {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 2; a_off := -256 |} (ELit 256) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6840320) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EVar 75) 1 36; KRange (EVar 79) 0 1; KRange (EVar 76) 0 35; KRange (EVar 38) 4096 140737488355280] 100.

(* [comment removed for export] *)
Definition ex2 : list SGA.aitem * (Z * sym_state) :=
  ([], (91, SS 738124 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; ELit 36; EAlu Instr.ALU_ADD (EVar 80) (ELit 48); ELit 0; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 77; EAlu Instr.ALU_ADD (EVar 38) (EVar 76); EVar 76; ELit 0; EVar 14; ELit 2; EVar 75; EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 77)) (EMd Instr.M_MUL (ELit 4) (EVar 76))) (ELit (-1))) (ELit 2); EVar 77; ELit 2147450880; EVar 33; EVar 21; EVar 22; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EVar 76) (ELit 1); EVar 25; EVar 26; EVar 50; EVar 28; EVar 29; EVar 38; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} 1 (EAlu Instr.ALU_ADD (EVar 80) (ELit 48)); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 77) 4096 140737488355320; KAlign (EVar 77) 4; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 77) (ELit 3); a_off := 2147450880 |} (ELit 1); KWord {| a_base := EVar 77; a_off := 0 |} 1 (EVar 80); KRange (EVar 80) 0 9; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 4096 140737488355321; KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) (ELit 3); a_off := 2147450880 |} (ELit 1); KWr {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 2; a_off := -256 |} (ELit 256) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6840320) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EVar 75) 1 36; KRange (EVar 79) 0 1; KRange (EVar 76) 0 35; KRange (EVar 38) 4096 140737488355280] 100)).
Definition s2 : sym_state := snd (snd ex2).

(* [comment removed for export] *)
Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

(* [comment removed for export] *)
Definition ex4 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [738060; 738992; 738060; 738992])], (91, SS 738144 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; ELit 36; EAlu Instr.ALU_ADD (EVar 80) (ELit 48); ELit 0; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EAlu Instr.ALU_ADD (EVar 77) (ELit 4); EAlu Instr.ALU_ADD (EVar 14) (EVar 76); EAlu Instr.ALU_ADD (EVar 76) (ELit 1); ELit 0; EVar 14; ELit 2; EVar 75; EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 77)) (EMd Instr.M_MUL (ELit 4) (EVar 76))) (ELit (-1))) (ELit 2); EAlu Instr.ALU_ADD (EVar 77) (ELit 4); ELit 2147450880; EVar 33; EVar 21; EVar 22; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EVar 76) (ELit 1); EVar 25; EVar 26; EVar 50; EVar 28; EVar 29; EVar 38; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EVar 76) (ELit 1)) (EVar 75)) 1 1; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} 1 (EAlu Instr.ALU_ADD (EVar 80) (ELit 48)); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 77) 4096 140737488355320; KAlign (EVar 77) 4; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 77) (ELit 3); a_off := 2147450880 |} (ELit 1); KWord {| a_base := EVar 77; a_off := 0 |} 1 (EVar 80); KRange (EVar 80) 0 9; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 4096 140737488355321; KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) (ELit 3); a_off := 2147450880 |} (ELit 1); KWr {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 2; a_off := -256 |} (ELit 256) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6840320) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EVar 75) 1 36; KRange (EVar 79) 0 1; KRange (EVar 76) 0 35; KRange (EVar 38) 4096 140737488355280] 100)).
Definition s4 : sym_state := snd (snd ex4).

(* [comment removed for export] *)
Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

(* [comment removed for export] *)
Definition ex6 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [738060; 738992; 738060; 738992])], (93, SS 738060 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; ELit 36; EAlu Instr.ALU_ADD (EVar 80) (ELit 48); ELit 0; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EAlu Instr.ALU_ADD (EVar 77) (ELit 4); EAlu Instr.ALU_ADD (EVar 14) (EVar 76); EAlu Instr.ALU_ADD (EVar 76) (ELit 1); ELit 0; EVar 14; ELit 2; EVar 75; EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 77)) (EMd Instr.M_MUL (ELit 4) (EVar 76))) (ELit (-1))) (ELit 2); EAlu Instr.ALU_ADD (EVar 77) (ELit 4); ELit 2147450880; EVar 33; EVar 21; EVar 22; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EVar 76) (ELit 1); EVar 25; EVar 26; EVar 50; EVar 28; EVar 29; EVar 38; EVar 31] [] [KRange (EAlu Instr.ALU_SLT (EAlu Instr.ALU_ADD (EVar 14) (EVar 76)) (ELit 36)) 1 1; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EVar 76) (ELit 1)) (EVar 75)) 1 1; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} 1 (EAlu Instr.ALU_ADD (EVar 80) (ELit 48)); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 77) 4096 140737488355320; KAlign (EVar 77) 4; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 77) (ELit 3); a_off := 2147450880 |} (ELit 1); KWord {| a_base := EVar 77; a_off := 0 |} 1 (EVar 80); KRange (EVar 80) 0 9; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 4096 140737488355321; KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) (ELit 3); a_off := 2147450880 |} (ELit 1); KWr {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 2; a_off := -256 |} (ELit 256) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6840320) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EVar 75) 1 36; KRange (EVar 79) 0 1; KRange (EVar 76) 0 35; KRange (EVar 38) 4096 140737488355280] 100)).
Definition s6 : sym_state := snd (snd ex6).

(* [comment removed for export] *)
Definition ex7 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [738060; 738992; 738060; 738992])], (93, SS 738992 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; ELit 36; EAlu Instr.ALU_ADD (EVar 80) (ELit 48); ELit 0; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EAlu Instr.ALU_ADD (EVar 77) (ELit 4); EAlu Instr.ALU_ADD (EVar 14) (EVar 76); EAlu Instr.ALU_ADD (EVar 76) (ELit 1); ELit 0; EVar 14; ELit 2; EVar 75; EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 77)) (EMd Instr.M_MUL (ELit 4) (EVar 76))) (ELit (-1))) (ELit 2); EAlu Instr.ALU_ADD (EVar 77) (ELit 4); ELit 2147450880; EVar 33; EVar 21; EVar 22; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) (ELit 1); ELit 0; EVar 26; EVar 50; EVar 28; EVar 29; EVar 38; EVar 31] [] [KRange (EAlu Instr.ALU_SLT (EAlu Instr.ALU_ADD (EVar 14) (EVar 76)) (ELit 36)) 0 0; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EVar 76) (ELit 1)) (EVar 75)) 1 1; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} 1 (EAlu Instr.ALU_ADD (EVar 80) (ELit 48)); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 77) 4096 140737488355320; KAlign (EVar 77) 4; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 77) (ELit 3); a_off := 2147450880 |} (ELit 1); KWord {| a_base := EVar 77; a_off := 0 |} 1 (EVar 80); KRange (EVar 80) 0 9; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 4096 140737488355321; KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) (ELit 3); a_off := 2147450880 |} (ELit 1); KWr {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 2; a_off := -256 |} (ELit 256) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6840320) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EVar 75) 1 36; KRange (EVar 79) 0 1; KRange (EVar 76) 0 35; KRange (EVar 38) 4096 140737488355280] 100)).
Definition s7 : sym_state := snd (snd ex7).

(* [comment removed for export] *)
Definition ex8 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [738060; 738992; 738060; 738992])], (93, SS 738992 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; ELit 36; EAlu Instr.ALU_ADD (EVar 80) (ELit 48); ELit 0; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 77; EAlu Instr.ALU_ADD (EVar 38) (EVar 76); EVar 76; ELit 0; EVar 14; ELit 2; EVar 75; EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 77)) (EMd Instr.M_MUL (ELit 4) (EVar 76))) (ELit (-1))) (ELit 2); EVar 77; ELit 2147450880; EVar 33; EVar 21; EVar 22; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) (ELit 1); ELit 0; EVar 26; EVar 50; EVar 28; EVar 29; EVar 38; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_ADD (EVar 76) (ELit 1)) (EVar 75)) 0 0; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} 1 (EAlu Instr.ALU_ADD (EVar 80) (ELit 48)); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 77) 4096 140737488355320; KAlign (EVar 77) 4; KZero {| a_base := EAlu Instr.ALU_SRL (EVar 77) (ELit 3); a_off := 2147450880 |} (ELit 1); KWord {| a_base := EVar 77; a_off := 0 |} 1 (EVar 80); KRange (EVar 80) 0 9; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) 4096 140737488355321; KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 38) (EVar 76)) (ELit 3); a_off := 2147450880 |} (ELit 1); KWr {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EVar 2; a_off := -256 |} (ELit 256) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6840320) {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1); KDisj {| a_base := EAlu Instr.ALU_ADD (EVar 38) (EVar 76); a_off := 0 |} (ELit 1) {| a_base := EVar 77; a_off := 0 |} (ELit 4); KRange (EVar 75) 1 36; KRange (EVar 79) 0 1; KRange (EVar 76) 0 35; KRange (EVar 38) 4096 140737488355280] 100)).
Definition s8 : sym_state := snd (snd ex8).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 0)) (SGA.mkplan (fst ex7) (SGP.PEnd 2)))) (SGA.mkplan (fst ex8) (SGP.PEnd 1)))).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s6).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s6).
Definition ps0 : SR.post_spec := SR.PS 738060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s8).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s8).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s8 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s8 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s8).
Definition ps1 : SR.post_spec := SR.PS 738992 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

(* [comment removed for export] *)
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 738992 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_ded56e_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 738060 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_ded56e_b.IT SegItab_Ba_ded56e_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 738060 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
