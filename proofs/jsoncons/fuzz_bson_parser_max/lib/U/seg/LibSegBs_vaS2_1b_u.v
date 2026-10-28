(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u Bs0PlanKitIt_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require SegItab_Bs_7c8953_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Bs_7c8953_u.ITR.
Definition IT : itab := SegItab_Bs_7c8953_u.IT.
Definition ENDS : list Z := [231096; 231136].
Definition STOPS1 : list Z := [231096; 231136] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-96)); EVar 3; EVar 4; ELit 2; ELit (-65); ELit 239; ELit 240; ELit 144; EVar 33; EVar 11; EAlu Instr.ALU_ADD (EVar 33) (EVar 35); ELit 8; ELit (-1); ELit 1; ELit (-62); ELit 245; ELit 244; ELit 143; ELit 80240; ELit (-80241); ELit 3; EVar 23; EVar 37; ELit 1; EVar 26; EVar 27; ELit 224; ELit 160; ELit 237; ELit 159].
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 2 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KWord (SA (EVar 33) 1) 1 (EVar 39);
   KRange (EVar 39) 0 255;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 230916 regs0 [] kn0 NX0.
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
  Eval vm_compute in (AUTO 2000 ss0).
Definition s1 : sym_state := snd (snd ex1).
(* [comment removed for export] *)
Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.
(* [comment removed for export] *)
Definition ex3 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t2).
Definition s3 : sym_state := snd (snd ex3).
(* [comment removed for export] *)
Definition ex4 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f2).
Definition s4 : sym_state := snd (snd ex4).
(* [comment removed for export] *)
Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.
(* [comment removed for export] *)
Definition ex6 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t5).
Definition s6 : sym_state := snd (snd ex6).
(* [comment removed for export] *)
Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.
(* [comment removed for export] *)
Definition ex8 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t7).
Definition s8 : sym_state := snd (snd ex8).
(* [comment removed for export] *)
Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.
(* [comment removed for export] *)
Definition ex10 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t9).
Definition s10 : sym_state := snd (snd ex10).
(* [comment removed for export] *)
Definition ex11 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f9).
Definition s11 : sym_state := snd (snd ex11).
(* [comment removed for export] *)
Definition ex12 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f7).
Definition s12 : sym_state := snd (snd ex12).
(* [comment removed for export] *)
Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.
(* [comment removed for export] *)
Definition ex14 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t13).
Definition s14 : sym_state := snd (snd ex14).
(* [comment removed for export] *)
Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.
(* [comment removed for export] *)
Definition ex16 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t15).
Definition s16 : sym_state := snd (snd ex16).
(* [comment removed for export] *)
Definition ex17 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f15).
Definition s17 : sym_state := snd (snd ex17).
(* [comment removed for export] *)
Definition ex18 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f13).
Definition s18 : sym_state := snd (snd ex18).
(* [comment removed for export] *)
Definition arms19 := Eval vm_compute in (match SGP.branch_probe IT s18 with Some e => SGP.case_arms s18 e 0 | None => None end).
Definition f19 : sym_state := match arms19 with Some (Some s, _) => s | _ => s18 end.
Definition t19 : sym_state := match arms19 with Some (_, Some s) => s | _ => s18 end.
(* [comment removed for export] *)
Definition ex20 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t19).
Definition s20 : sym_state := snd (snd ex20).
(* [comment removed for export] *)
Definition ex21 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f19).
Definition s21 : sym_state := snd (snd ex21).
(* [comment removed for export] *)
Definition arms22 := Eval vm_compute in (match SGP.branch_probe IT s21 with Some e => SGP.case_arms s21 e 0 | None => None end).
Definition f22 : sym_state := match arms22 with Some (Some s, _) => s | _ => s21 end.
Definition t22 : sym_state := match arms22 with Some (_, Some s) => s | _ => s21 end.
(* [comment removed for export] *)
Definition ex23 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t22).
Definition s23 : sym_state := snd (snd ex23).
(* [comment removed for export] *)
Definition ex24 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f22).
Definition s24 : sym_state := snd (snd ex24).
(* [comment removed for export] *)
Definition ex25 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f5).
Definition s25 : sym_state := snd (snd ex25).
(* [comment removed for export] *)
Definition arms26 := Eval vm_compute in (match SGP.branch_probe IT s25 with Some e => SGP.case_arms s25 e 0 | None => None end).
Definition f26 : sym_state := match arms26 with Some (Some s, _) => s | _ => s25 end.
Definition t26 : sym_state := match arms26 with Some (_, Some s) => s | _ => s25 end.
(* [comment removed for export] *)
Definition ex27 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t26).
Definition s27 : sym_state := snd (snd ex27).
(* [comment removed for export] *)
Definition arms28 := Eval vm_compute in (match SGP.branch_probe IT s27 with Some e => SGP.case_arms s27 e 0 | None => None end).
Definition f28 : sym_state := match arms28 with Some (Some s, _) => s | _ => s27 end.
Definition t28 : sym_state := match arms28 with Some (_, Some s) => s | _ => s27 end.
(* [comment removed for export] *)
Definition ex29 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t28).
Definition s29 : sym_state := snd (snd ex29).
(* [comment removed for export] *)
Definition ex30 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f28).
Definition s30 : sym_state := snd (snd ex30).
(* [comment removed for export] *)
Definition ex31 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f26).
Definition s31 : sym_state := snd (snd ex31).
(* [comment removed for export] *)
Definition arms32 := Eval vm_compute in (match SGP.branch_probe IT s31 with Some e => SGP.case_arms s31 e 0 | None => None end).
Definition f32 : sym_state := match arms32 with Some (Some s, _) => s | _ => s31 end.
Definition t32 : sym_state := match arms32 with Some (_, Some s) => s | _ => s31 end.
(* [comment removed for export] *)
Definition ex33 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t32).
Definition s33 : sym_state := snd (snd ex33).
(* [comment removed for export] *)
Definition arms34 := Eval vm_compute in (match SGP.branch_probe IT s33 with Some e => SGP.case_arms s33 e 0 | None => None end).
Definition f34 : sym_state := match arms34 with Some (Some s, _) => s | _ => s33 end.
Definition t34 : sym_state := match arms34 with Some (_, Some s) => s | _ => s33 end.
(* [comment removed for export] *)
Definition ex35 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t34).
Definition s35 : sym_state := snd (snd ex35).
(* [comment removed for export] *)
Definition ex36 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f34).
Definition s36 : sym_state := snd (snd ex36).
(* [comment removed for export] *)
Definition ex37 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f32).
Definition s37 : sym_state := snd (snd ex37).
(* [comment removed for export] *)
Definition arms38 := Eval vm_compute in (match SGP.branch_probe IT s37 with Some e => SGP.case_arms s37 e 0 | None => None end).
Definition f38 : sym_state := match arms38 with Some (Some s, _) => s | _ => s37 end.
Definition t38 : sym_state := match arms38 with Some (_, Some s) => s | _ => s37 end.
(* [comment removed for export] *)
Definition ex39 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t38).
Definition s39 : sym_state := snd (snd ex39).
(* [comment removed for export] *)
Definition ex40 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f38).
Definition s40 : sym_state := snd (snd ex40).
(* [comment removed for export] *)
Definition arms41 := Eval vm_compute in (match SGP.branch_probe IT s40 with Some e => SGP.case_arms s40 e 0 | None => None end).
Definition f41 : sym_state := match arms41 with Some (Some s, _) => s | _ => s40 end.
Definition t41 : sym_state := match arms41 with Some (_, Some s) => s | _ => s40 end.
(* [comment removed for export] *)
Definition ex42 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t41).
Definition s42 : sym_state := snd (snd ex42).
(* [comment removed for export] *)
Definition ex43 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f41).
Definition s43 : sym_state := snd (snd ex43).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 1)) (SGA.mkplan (fst ex11) (SGP.PEnd 2)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PEnd 3)) (SGA.mkplan (fst ex17) (SGP.PEnd 4)))) (SGA.mkplan (fst ex18) (SGP.PBranch (SGA.mkplan (fst ex20) (SGP.PEnd 5)) (SGA.mkplan (fst ex21) (SGP.PBranch (SGA.mkplan (fst ex23) (SGP.PEnd 6)) (SGA.mkplan (fst ex24) (SGP.PEnd 7)))))))))) (SGA.mkplan (fst ex25) (SGP.PBranch (SGA.mkplan (fst ex27) (SGP.PBranch (SGA.mkplan (fst ex29) (SGP.PEnd 8)) (SGA.mkplan (fst ex30) (SGP.PEnd 9)))) (SGA.mkplan (fst ex31) (SGP.PBranch (SGA.mkplan (fst ex33) (SGP.PBranch (SGA.mkplan (fst ex35) (SGP.PEnd 10)) (SGA.mkplan (fst ex36) (SGP.PEnd 11)))) (SGA.mkplan (fst ex37) (SGP.PBranch (SGA.mkplan (fst ex39) (SGP.PEnd 12)) (SGA.mkplan (fst ex40) (SGP.PBranch (SGA.mkplan (fst ex42) (SGP.PEnd 13)) (SGA.mkplan (fst ex43) (SGP.PEnd 14))))))))))))).
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
Definition ps0 : SR.post_spec := SR.PS 231136 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.
(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s10).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s10).
Definition ps1 : SR.post_spec := SR.PS 231136 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.
(* [comment removed for export] *)
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s11).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s11).
Definition ps2 : SR.post_spec := SR.PS 231096 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.
(* [comment removed for export] *)
Definition regs_out3 : list expr := Eval vm_compute in (s_regs s16).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s16).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s16 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s16 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s16).
Definition ps3 : SR.post_spec := SR.PS 231136 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.
(* [comment removed for export] *)
Definition regs_out4 : list expr := Eval vm_compute in (s_regs s17).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s17).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s17 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s17 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s17).
Definition ps4 : SR.post_spec := SR.PS 231096 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.
(* [comment removed for export] *)
Definition regs_out5 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s20).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s20).
Definition ps5 : SR.post_spec := SR.PS 231136 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.
(* [comment removed for export] *)
Definition regs_out6 : list expr := Eval vm_compute in (s_regs s23).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s23).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s23 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s23 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s23).
Definition ps6 : SR.post_spec := SR.PS 231096 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.
(* [comment removed for export] *)
Definition regs_out7 : list expr := Eval vm_compute in (s_regs s24).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s24).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s24 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s24 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s24).
Definition ps7 : SR.post_spec := SR.PS 231136 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.
(* [comment removed for export] *)
Definition regs_out8 : list expr := Eval vm_compute in (s_regs s29).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s29).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s29 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s29 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s29).
Definition ps8 : SR.post_spec := SR.PS 231136 (map (fun i => (i, nth i regs_out8 (ELit 0))) (seq 1 31)) F0L cells8.
(* [comment removed for export] *)
Definition regs_out9 : list expr := Eval vm_compute in (s_regs s30).
Definition exit_sp_off9 : Z := Eval vm_compute in (spoff_of s30).
Definition cells9 : list kentry := Eval vm_compute in (cells_of s30 exit_sp_off9).
Definition nfresh9 : nat := Eval vm_compute in (s_next s30 - NX0)%nat.
Definition exit_pc9 : Z := Eval vm_compute in (s_pc s30).
Definition ps9 : SR.post_spec := SR.PS 231096 (map (fun i => (i, nth i regs_out9 (ELit 0))) (seq 1 31)) F0L cells9.
(* [comment removed for export] *)
Definition regs_out10 : list expr := Eval vm_compute in (s_regs s35).
Definition exit_sp_off10 : Z := Eval vm_compute in (spoff_of s35).
Definition cells10 : list kentry := Eval vm_compute in (cells_of s35 exit_sp_off10).
Definition nfresh10 : nat := Eval vm_compute in (s_next s35 - NX0)%nat.
Definition exit_pc10 : Z := Eval vm_compute in (s_pc s35).
Definition ps10 : SR.post_spec := SR.PS 231136 (map (fun i => (i, nth i regs_out10 (ELit 0))) (seq 1 31)) F0L cells10.
(* [comment removed for export] *)
Definition regs_out11 : list expr := Eval vm_compute in (s_regs s36).
Definition exit_sp_off11 : Z := Eval vm_compute in (spoff_of s36).
Definition cells11 : list kentry := Eval vm_compute in (cells_of s36 exit_sp_off11).
Definition nfresh11 : nat := Eval vm_compute in (s_next s36 - NX0)%nat.
Definition exit_pc11 : Z := Eval vm_compute in (s_pc s36).
Definition ps11 : SR.post_spec := SR.PS 231096 (map (fun i => (i, nth i regs_out11 (ELit 0))) (seq 1 31)) F0L cells11.
(* [comment removed for export] *)
Definition regs_out12 : list expr := Eval vm_compute in (s_regs s39).
Definition exit_sp_off12 : Z := Eval vm_compute in (spoff_of s39).
Definition cells12 : list kentry := Eval vm_compute in (cells_of s39 exit_sp_off12).
Definition nfresh12 : nat := Eval vm_compute in (s_next s39 - NX0)%nat.
Definition exit_pc12 : Z := Eval vm_compute in (s_pc s39).
Definition ps12 : SR.post_spec := SR.PS 231136 (map (fun i => (i, nth i regs_out12 (ELit 0))) (seq 1 31)) F0L cells12.
(* [comment removed for export] *)
Definition regs_out13 : list expr := Eval vm_compute in (s_regs s42).
Definition exit_sp_off13 : Z := Eval vm_compute in (spoff_of s42).
Definition cells13 : list kentry := Eval vm_compute in (cells_of s42 exit_sp_off13).
Definition nfresh13 : nat := Eval vm_compute in (s_next s42 - NX0)%nat.
Definition exit_pc13 : Z := Eval vm_compute in (s_pc s42).
Definition ps13 : SR.post_spec := SR.PS 231096 (map (fun i => (i, nth i regs_out13 (ELit 0))) (seq 1 31)) F0L cells13.
(* [comment removed for export] *)
Definition regs_out14 : list expr := Eval vm_compute in (s_regs s43).
Definition exit_sp_off14 : Z := Eval vm_compute in (spoff_of s43).
Definition cells14 : list kentry := Eval vm_compute in (cells_of s43 exit_sp_off14).
Definition nfresh14 : nat := Eval vm_compute in (s_next s43 - NX0)%nat.
Definition exit_pc14 : Z := Eval vm_compute in (s_pc s43).
Definition ps14 : SR.post_spec := SR.PS 231136 (map (fun i => (i, nth i regs_out14 (ELit 0))) (seq 1 31)) F0L cells14.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8; ps9; ps10; ps11; ps12; ps13; ps14] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Bs_7c8953_u.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 230916 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_Bs_7c8953_u.IT SegItab_Bs_7c8953_u.IT_sound BF NX0 BR XSTEP F0 PSS plan 230916 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
