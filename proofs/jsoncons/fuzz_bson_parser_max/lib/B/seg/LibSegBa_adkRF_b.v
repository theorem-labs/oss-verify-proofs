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
Definition ENDS : list Z := [737736; 737864].
Definition STOPS1 : list Z := [737736; 737864] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EAluw Instr.ALU_ADD (EVar 41) (ELit 0); EVar 41; EVar 42; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EVar 50) (ELit 32); EAlu Instr.ALU_SUB (ELit 3) (EVar 40); ELit 1000000000; EVar 21; EAlu Instr.ALU_ADD (EVar 2) (ELit (-104)); ELit 14757395259826634752; EVar 40; ELit 19342813113834067; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 50) (ELit 64)) (EMd Instr.M_MUL (ELit 36) (EVar 40)); ELit 10; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KWord (SA (EVar 2) (-112)) 8 (EVar 42);
   KWord (SA (EVar 2) (-120)) 8 (EVar 41);
   KRange (EVar 2) 140735332487296 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-256)) (ELit 256);
   KRange (EVar 40) 0 3;
   KRange (EVar 50) 4096 140737488354816;
   KWord (SA (EVar 2) (-136)) 8 (EVar 41);
   KWord (SA (EVar 2) (-128)) 8 (EVar 42)].
Definition ss0 : sym_state := SS 737660 regs0 [] kn0 NX0.
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
  ([], (91, SS 737660 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EAluw Instr.ALU_ADD (EVar 41) (ELit 0); EVar 41; EVar 42; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EVar 50) (ELit 32); EAlu Instr.ALU_SUB (ELit 3) (EVar 40); ELit 1000000000; EVar 21; EAlu Instr.ALU_ADD (EVar 2) (ELit (-104)); ELit 14757395259826634752; EVar 40; ELit 19342813113834067; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 50) (ELit 64)) (EMd Instr.M_MUL (ELit 36) (EVar 40)); ELit 10; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 41); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 40) 0 3; KRange (EVar 50) 4096 140737488354816; KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42)] 80)).
Definition s1 : sym_state := snd (snd ex1).
(* [comment removed for export] *)
Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.
(* [comment removed for export] *)
Definition ex3 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [737736; 737864; 737736; 737864])], (91, SS 737668 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EExt true 4 4 (EVar 41); EVar 41; EVar 42; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EVar 50) (ELit 32); EAlu Instr.ALU_SUB (ELit 3) (EVar 40); ELit 1000000000; EVar 21; EAlu Instr.ALU_ADD (EVar 2) (ELit (-104)); ELit 14757395259826634752; EVar 40; ELit 19342813113834067; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 50) (ELit 64)) (EMd Instr.M_MUL (ELit 36) (EVar 40)); ELit 10; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1)) 1 1; KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 41); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 40) 0 3; KRange (EVar 50) 4096 140737488354816; KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42)] 80)).
Definition s3 : sym_state := snd (snd ex3).
(* [comment removed for export] *)
Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.
(* [comment removed for export] *)
Definition ex5 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [737736; 737864; 737736; 737864])], (91, SS 737688 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EExt true 0 4 (EVar 42); ELit 18446744073709551607; EVar 42; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EVar 50) (ELit 32); EAlu Instr.ALU_SUB (ELit 3) (EVar 40); ELit 1000000000; EVar 21; EAlu Instr.ALU_ADD (EVar 2) (ELit (-104)); ELit 14757395259826634752; EVar 40; ELit 19342813113834067; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 50) (ELit 64)) (EMd Instr.M_MUL (ELit 36) (EVar 40)); ELit 10; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1)) 1 1; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1)) 1 1; KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 41); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 40) 0 3; KRange (EVar 50) 4096 140737488354816; KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42)] 80)).
Definition s5 : sym_state := snd (snd ex5).
(* [comment removed for export] *)
Definition arms6 := Eval vm_compute in (match SGP.branch_probe IT s5 with Some e => SGP.case_arms s5 e 0 | None => None end).
Definition f6 : sym_state := match arms6 with Some (Some s, _) => s | _ => s5 end.
Definition t6 : sym_state := match arms6 with Some (_, Some s) => s | _ => s5 end.
(* [comment removed for export] *)
Definition ex7 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [737736; 737864; 737736; 737864])], (91, SS 737708 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EExt true 4 4 (EVar 42); ELit 18446744073709551603; EVar 42; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EVar 50) (ELit 32); EAlu Instr.ALU_SUB (ELit 3) (EVar 40); ELit 1000000000; EVar 21; EAlu Instr.ALU_ADD (EVar 2) (ELit (-104)); ELit 14757395259826634752; EVar 40; ELit 19342813113834067; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 50) (ELit 64)) (EMd Instr.M_MUL (ELit 36) (EVar 40)); ELit 10; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 0 4 (EVar 42)) (ELit 0)) (ELit 1)) 1 1; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1)) 1 1; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1)) 1 1; KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 41); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 40) 0 3; KRange (EVar 50) 4096 140737488354816; KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42)] 80)).
Definition s7 : sym_state := snd (snd ex7).
(* [comment removed for export] *)
Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.
(* [comment removed for export] *)
Definition ex9 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [737736; 737864; 737736; 737864])], (93, SS 737864 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EExt true 4 4 (EVar 42); ELit 18446744073709551603; EVar 42; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EVar 50) (ELit 32); EAlu Instr.ALU_SUB (ELit 3) (EVar 40); ELit 1000000000; EVar 21; EAlu Instr.ALU_ADD (EVar 2) (ELit (-104)); ELit 14757395259826634752; EVar 40; ELit 19342813113834067; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 50) (ELit 64)) (EMd Instr.M_MUL (ELit 36) (EVar 40)); ELit 10; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 42)) (ELit 0)) (ELit 1)) 1 1; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 0 4 (EVar 42)) (ELit 0)) (ELit 1)) 1 1; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1)) 1 1; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1)) 1 1; KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 41); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 40) 0 3; KRange (EVar 50) 4096 140737488354816; KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42)] 80)).
Definition s9 : sym_state := snd (snd ex9).
(* [comment removed for export] *)
Definition ex10 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [737736; 737864; 737736; 737864])], (93, SS 737736 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); ELit 18446744073709551603; EVar 42; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 36) (EVar 40)) (EVar 50)) (ELit 28); EAlu Instr.ALU_SUB (ELit 3) (EVar 40); ELit 1000000000; ELit 0; EAlu Instr.ALU_ADD (EVar 2) (ELit (-104)); ELit 14757395259826634752; EVar 40; ELit 19342813113834067; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 50) (ELit 64)) (EMd Instr.M_MUL (ELit 36) (EVar 40)); ELit 10; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 42)) (ELit 0)) (ELit 1)) 0 0; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 0 4 (EVar 42)) (ELit 0)) (ELit 1)) 1 1; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1)) 1 1; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1)) 1 1; KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 41); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 40) 0 3; KRange (EVar 50) 4096 140737488354816; KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42)] 80)).
Definition s10 : sym_state := snd (snd ex10).
(* [comment removed for export] *)
Definition ex11 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [737736; 737864; 737736; 737864])], (93, SS 737736 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); ELit 18446744073709551607; EVar 42; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 36) (EVar 40)) (EVar 50)) (ELit 28); EAlu Instr.ALU_SUB (ELit 3) (EVar 40); ELit 1000000000; ELit 0; EAlu Instr.ALU_ADD (EVar 2) (ELit (-104)); ELit 14757395259826634752; EVar 40; ELit 19342813113834067; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 50) (ELit 64)) (EMd Instr.M_MUL (ELit 36) (EVar 40)); ELit 10; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 0 4 (EVar 42)) (ELit 0)) (ELit 1)) 0 0; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1)) 1 1; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1)) 1 1; KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 41); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 40) 0 3; KRange (EVar 50) 4096 140737488354816; KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42)] 80)).
Definition s11 : sym_state := snd (snd ex11).
(* [comment removed for export] *)
Definition ex12 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [737736; 737864; 737736; 737864])], (93, SS 737736 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EVar 41; EVar 42; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 36) (EVar 40)) (EVar 50)) (ELit 28); EAlu Instr.ALU_SUB (ELit 3) (EVar 40); ELit 1000000000; ELit 0; EAlu Instr.ALU_ADD (EVar 2) (ELit (-104)); ELit 14757395259826634752; EVar 40; ELit 19342813113834067; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 50) (ELit 64)) (EMd Instr.M_MUL (ELit 36) (EVar 40)); ELit 10; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1)) 0 0; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1)) 1 1; KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 41); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 40) 0 3; KRange (EVar 50) 4096 140737488354816; KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42)] 80)).
Definition s12 : sym_state := snd (snd ex12).
Definition ex13 : list SGA.aitem * (Z * sym_state) :=
  ([SGA.AStep (SR.SBlock [737736; 737864; 737736; 737864])], (93, SS 737736 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EVar 41; EVar 42; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 36) (EVar 40)) (EVar 50)) (ELit 28); EAlu Instr.ALU_SUB (ELit 3) (EVar 40); ELit 1000000000; ELit 0; EAlu Instr.ALU_ADD (EVar 2) (ELit (-104)); ELit 14757395259826634752; EVar 40; ELit 19342813113834067; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 50) (ELit 64)) (EMd Instr.M_MUL (ELit 36) (EVar 40)); ELit 10; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1)) 0 0; KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 41); KRange (EVar 2) 140735332487296 140737488355328; KAlign (EVar 2) 32; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KRange (EVar 40) 0 3; KRange (EVar 50) 4096 140737488354816; KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42)] 80)).
Definition s13 : sym_state := snd (snd ex13).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PBranch (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 0)) (SGA.mkplan (fst ex10) (SGP.PEnd 1)))) (SGA.mkplan (fst ex11) (SGP.PEnd 2)))) (SGA.mkplan (fst ex12) (SGP.PEnd 3)))) (SGA.mkplan (fst ex13) (SGP.PEnd 4))).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s9).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s9).
Definition ps0 : SR.post_spec := SR.PS 737864 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.
(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s10).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s10).
Definition ps1 : SR.post_spec := SR.PS 737736 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.
(* [comment removed for export] *)
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s11).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s11).
Definition ps2 : SR.post_spec := SR.PS 737736 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.
(* [comment removed for export] *)
Definition regs_out3 : list expr := Eval vm_compute in (s_regs s12).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s12).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s12 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s12 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s12).
Definition ps3 : SR.post_spec := SR.PS 737736 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.
(* [comment removed for export] *)
Definition regs_out4 : list expr := Eval vm_compute in (s_regs s13).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s13).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s13 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s13 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s13).
Definition ps4 : SR.post_spec := SR.PS 737736 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_ded56e_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 737660 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_ded56e_b.IT SegItab_Ba_ded56e_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 737660 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
