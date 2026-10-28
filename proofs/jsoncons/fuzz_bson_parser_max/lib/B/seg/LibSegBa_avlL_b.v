(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_0ad7fe_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_0ad7fe_b.ITR.
Definition IT : itab := SegItab_Ba_0ad7fe_b.IT.
Definition ENDS : list Z := [733748; 733952].
Definition STOPS1 : list Z := [733748; 733952] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-112))); EVar 3; EVar 4; ELit 245; ELit 2; ELit (-65); ELit 159; ELit 240; (EVar 33); (EVar 39); EVar 12; (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)); ELit 8; (ELit 18446744073709551615); ELit 1; ELit (-62); (ELit 145280); (ELit 18446744073709406335); ELit 2147450880; ELit 144; ELit 244; ELit 143; EVar 24; (EVar 37); (EVar 34); EVar 27; ELit 239; ELit 224; ELit 160; ELit 237].
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255;
   KRange (EVar 34) 0 140737488355328].
Definition ss0 : sym_state := SS 733672 regs0 [] kn0 NX0.
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
Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.
(* [comment removed for export] *)
Definition ex5 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t4).
Definition s5 : sym_state := snd (snd ex5).
(* [comment removed for export] *)
Definition arms6 := Eval vm_compute in (match SGP.branch_probe IT s5 with Some e => SGP.case_arms s5 e 0 | None => None end).
Definition f6 : sym_state := match arms6 with Some (Some s, _) => s | _ => s5 end.
Definition t6 : sym_state := match arms6 with Some (_, Some s) => s | _ => s5 end.
(* [comment removed for export] *)
Definition ex7 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t6).
Definition s7 : sym_state := snd (snd ex7).
(* [comment removed for export] *)
Definition ex8 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f6).
Definition s8 : sym_state := snd (snd ex8).
(* [comment removed for export] *)
Definition ex9 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f4).
Definition s9 : sym_state := snd (snd ex9).
(* [comment removed for export] *)
Definition arms10 := Eval vm_compute in (match SGP.branch_probe IT s9 with Some e => SGP.case_arms s9 e 0 | None => None end).
Definition f10 : sym_state := match arms10 with Some (Some s, _) => s | _ => s9 end.
Definition t10 : sym_state := match arms10 with Some (_, Some s) => s | _ => s9 end.
(* [comment removed for export] *)
Definition ex11 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t10).
Definition s11 : sym_state := snd (snd ex11).
(* [comment removed for export] *)
Definition arms12 := Eval vm_compute in (match SGP.branch_probe IT s11 with Some e => SGP.case_arms s11 e 0 | None => None end).
Definition f12 : sym_state := match arms12 with Some (Some s, _) => s | _ => s11 end.
Definition t12 : sym_state := match arms12 with Some (_, Some s) => s | _ => s11 end.
(* [comment removed for export] *)
Definition ex13 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t12).
Definition s13 : sym_state := snd (snd ex13).
(* [comment removed for export] *)
Definition ex14 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f12).
Definition s14 : sym_state := snd (snd ex14).
(* [comment removed for export] *)
Definition ex15 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f10).
Definition s15 : sym_state := snd (snd ex15).
(* [comment removed for export] *)
Definition arms16 := Eval vm_compute in (match SGP.branch_probe IT s15 with Some e => SGP.case_arms s15 e 0 | None => None end).
Definition f16 : sym_state := match arms16 with Some (Some s, _) => s | _ => s15 end.
Definition t16 : sym_state := match arms16 with Some (_, Some s) => s | _ => s15 end.
(* [comment removed for export] *)
Definition ex17 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t16).
Definition s17 : sym_state := snd (snd ex17).
(* [comment removed for export] *)
Definition ex18 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f16).
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
Definition ex22 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f2).
Definition s22 : sym_state := snd (snd ex22).
(* [comment removed for export] *)
Definition arms23 := Eval vm_compute in (match SGP.branch_probe IT s22 with Some e => SGP.case_arms s22 e 0 | None => None end).
Definition f23 : sym_state := match arms23 with Some (Some s, _) => s | _ => s22 end.
Definition t23 : sym_state := match arms23 with Some (_, Some s) => s | _ => s22 end.
(* [comment removed for export] *)
Definition ex24 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t23).
Definition s24 : sym_state := snd (snd ex24).
(* [comment removed for export] *)
Definition arms25 := Eval vm_compute in (match SGP.branch_probe IT s24 with Some e => SGP.case_arms s24 e 0 | None => None end).
Definition f25 : sym_state := match arms25 with Some (Some s, _) => s | _ => s24 end.
Definition t25 : sym_state := match arms25 with Some (_, Some s) => s | _ => s24 end.
(* [comment removed for export] *)
Definition ex26 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t25).
Definition s26 : sym_state := snd (snd ex26).
(* [comment removed for export] *)
Definition ex27 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f25).
Definition s27 : sym_state := snd (snd ex27).
(* [comment removed for export] *)
Definition ex28 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f23).
Definition s28 : sym_state := snd (snd ex28).
(* [comment removed for export] *)
Definition arms29 := Eval vm_compute in (match SGP.branch_probe IT s28 with Some e => SGP.case_arms s28 e 0 | None => None end).
Definition f29 : sym_state := match arms29 with Some (Some s, _) => s | _ => s28 end.
Definition t29 : sym_state := match arms29 with Some (_, Some s) => s | _ => s28 end.
(* [comment removed for export] *)
Definition ex30 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t29).
Definition s30 : sym_state := snd (snd ex30).
(* [comment removed for export] *)
Definition arms31 := Eval vm_compute in (match SGP.branch_probe IT s30 with Some e => SGP.case_arms s30 e 0 | None => None end).
Definition f31 : sym_state := match arms31 with Some (Some s, _) => s | _ => s30 end.
Definition t31 : sym_state := match arms31 with Some (_, Some s) => s | _ => s30 end.
(* [comment removed for export] *)
Definition ex32 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t31).
Definition s32 : sym_state := snd (snd ex32).
(* [comment removed for export] *)
Definition ex33 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f31).
Definition s33 : sym_state := snd (snd ex33).
(* [comment removed for export] *)
Definition ex34 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f29).
Definition s34 : sym_state := snd (snd ex34).
(* [comment removed for export] *)
Definition arms35 := Eval vm_compute in (match SGP.branch_probe IT s34 with Some e => SGP.case_arms s34 e 0 | None => None end).
Definition f35 : sym_state := match arms35 with Some (Some s, _) => s | _ => s34 end.
Definition t35 : sym_state := match arms35 with Some (_, Some s) => s | _ => s34 end.
(* [comment removed for export] *)
Definition ex36 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t35).
Definition s36 : sym_state := snd (snd ex36).
(* [comment removed for export] *)
Definition ex37 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f35).
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
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PBranch (SGA.mkplan (fst ex7) (SGP.PEnd 0)) (SGA.mkplan (fst ex8) (SGP.PEnd 1)))) (SGA.mkplan (fst ex9) (SGP.PBranch (SGA.mkplan (fst ex11) (SGP.PBranch (SGA.mkplan (fst ex13) (SGP.PEnd 2)) (SGA.mkplan (fst ex14) (SGP.PEnd 3)))) (SGA.mkplan (fst ex15) (SGP.PBranch (SGA.mkplan (fst ex17) (SGP.PEnd 4)) (SGA.mkplan (fst ex18) (SGP.PBranch (SGA.mkplan (fst ex20) (SGP.PEnd 5)) (SGA.mkplan (fst ex21) (SGP.PEnd 6)))))))))) (SGA.mkplan (fst ex22) (SGP.PBranch (SGA.mkplan (fst ex24) (SGP.PBranch (SGA.mkplan (fst ex26) (SGP.PEnd 7)) (SGA.mkplan (fst ex27) (SGP.PEnd 8)))) (SGA.mkplan (fst ex28) (SGP.PBranch (SGA.mkplan (fst ex30) (SGP.PBranch (SGA.mkplan (fst ex32) (SGP.PEnd 9)) (SGA.mkplan (fst ex33) (SGP.PEnd 10)))) (SGA.mkplan (fst ex34) (SGP.PBranch (SGA.mkplan (fst ex36) (SGP.PEnd 11)) (SGA.mkplan (fst ex37) (SGP.PBranch (SGA.mkplan (fst ex39) (SGP.PEnd 12)) (SGA.mkplan (fst ex40) (SGP.PEnd 13))))))))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.   (* [comment removed for export] *)
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
Definition ps0 : SR.post_spec := SR.PS 733952 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.
(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s8).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s8).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s8 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s8 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s8).
Definition ps1 : SR.post_spec := SR.PS 733748 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.
(* [comment removed for export] *)
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s13).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s13).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s13 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s13 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s13).
Definition ps2 : SR.post_spec := SR.PS 733952 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.
(* [comment removed for export] *)
Definition regs_out3 : list expr := Eval vm_compute in (s_regs s14).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s14).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s14 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s14 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s14).
Definition ps3 : SR.post_spec := SR.PS 733748 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.
(* [comment removed for export] *)
Definition regs_out4 : list expr := Eval vm_compute in (s_regs s17).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s17).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s17 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s17 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s17).
Definition ps4 : SR.post_spec := SR.PS 733952 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.
(* [comment removed for export] *)
Definition regs_out5 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s20).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s20).
Definition ps5 : SR.post_spec := SR.PS 733748 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.
(* [comment removed for export] *)
Definition regs_out6 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s21).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s21).
Definition ps6 : SR.post_spec := SR.PS 733952 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.
(* [comment removed for export] *)
Definition regs_out7 : list expr := Eval vm_compute in (s_regs s26).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s26).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s26 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s26 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s26).
Definition ps7 : SR.post_spec := SR.PS 733952 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.
(* [comment removed for export] *)
Definition regs_out8 : list expr := Eval vm_compute in (s_regs s27).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s27).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s27 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s27 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s27).
Definition ps8 : SR.post_spec := SR.PS 733748 (map (fun i => (i, nth i regs_out8 (ELit 0))) (seq 1 31)) F0L cells8.
(* [comment removed for export] *)
Definition regs_out9 : list expr := Eval vm_compute in (s_regs s32).
Definition exit_sp_off9 : Z := Eval vm_compute in (spoff_of s32).
Definition cells9 : list kentry := Eval vm_compute in (cells_of s32 exit_sp_off9).
Definition nfresh9 : nat := Eval vm_compute in (s_next s32 - NX0)%nat.
Definition exit_pc9 : Z := Eval vm_compute in (s_pc s32).
Definition ps9 : SR.post_spec := SR.PS 733952 (map (fun i => (i, nth i regs_out9 (ELit 0))) (seq 1 31)) F0L cells9.
(* [comment removed for export] *)
Definition regs_out10 : list expr := Eval vm_compute in (s_regs s33).
Definition exit_sp_off10 : Z := Eval vm_compute in (spoff_of s33).
Definition cells10 : list kentry := Eval vm_compute in (cells_of s33 exit_sp_off10).
Definition nfresh10 : nat := Eval vm_compute in (s_next s33 - NX0)%nat.
Definition exit_pc10 : Z := Eval vm_compute in (s_pc s33).
Definition ps10 : SR.post_spec := SR.PS 733748 (map (fun i => (i, nth i regs_out10 (ELit 0))) (seq 1 31)) F0L cells10.
(* [comment removed for export] *)
Definition regs_out11 : list expr := Eval vm_compute in (s_regs s36).
Definition exit_sp_off11 : Z := Eval vm_compute in (spoff_of s36).
Definition cells11 : list kentry := Eval vm_compute in (cells_of s36 exit_sp_off11).
Definition nfresh11 : nat := Eval vm_compute in (s_next s36 - NX0)%nat.
Definition exit_pc11 : Z := Eval vm_compute in (s_pc s36).
Definition ps11 : SR.post_spec := SR.PS 733952 (map (fun i => (i, nth i regs_out11 (ELit 0))) (seq 1 31)) F0L cells11.
(* [comment removed for export] *)
Definition regs_out12 : list expr := Eval vm_compute in (s_regs s39).
Definition exit_sp_off12 : Z := Eval vm_compute in (spoff_of s39).
Definition cells12 : list kentry := Eval vm_compute in (cells_of s39 exit_sp_off12).
Definition nfresh12 : nat := Eval vm_compute in (s_next s39 - NX0)%nat.
Definition exit_pc12 : Z := Eval vm_compute in (s_pc s39).
Definition ps12 : SR.post_spec := SR.PS 733748 (map (fun i => (i, nth i regs_out12 (ELit 0))) (seq 1 31)) F0L cells12.
(* [comment removed for export] *)
Definition regs_out13 : list expr := Eval vm_compute in (s_regs s40).
Definition exit_sp_off13 : Z := Eval vm_compute in (spoff_of s40).
Definition cells13 : list kentry := Eval vm_compute in (cells_of s40 exit_sp_off13).
Definition nfresh13 : nat := Eval vm_compute in (s_next s40 - NX0)%nat.
Definition exit_pc13 : Z := Eval vm_compute in (s_pc s40).
Definition ps13 : SR.post_spec := SR.PS 733952 (map (fun i => (i, nth i regs_out13 (ELit 0))) (seq 1 31)) F0L cells13.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8; ps9; ps10; ps11; ps12; ps13] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_0ad7fe_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 733672 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_0ad7fe_b.IT SegItab_Ba_0ad7fe_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 733672 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
