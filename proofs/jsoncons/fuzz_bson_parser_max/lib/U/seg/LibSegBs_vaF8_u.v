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
Definition ENDS : list Z := [230912; 231096].
Definition STOPS1 : list Z := [230912; 231096] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-96)); EVar 3; EVar 4; ELit 2; ELit (-65); ELit 239; ELit 240; ELit 144; EVar 33; EVar 11; EAlu Instr.ALU_ADD (EVar 33) (EVar 35); ELit 8; ELit (-1); ELit 1; ELit (-62); ELit 245; ELit 244; ELit 143; ELit 80240; ELit (-80241); ELit 3; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; ELit 224; ELit 160; ELit 237; ELit 159].
Definition kn0 : list kentry := [KRange (EVar 33) 1 140737488355328;
   KRange (EVar 35) 8 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KWord (SA (EVar 33) 0) 1 (EVar 36);
   KRange (EVar 36) 0 255;
   KWord (SA (EVar 33) 1) 1 (EVar 37);
   KRange (EVar 37) 0 255;
   KWord (SA (EVar 33) 2) 1 (EVar 38);
   KRange (EVar 38) 0 255;
   KWord (SA (EVar 33) 3) 1 (EVar 39);
   KRange (EVar 39) 0 255;
   KWord (SA (EVar 33) 4) 1 (EVar 40);
   KRange (EVar 40) 0 255;
   KWord (SA (EVar 33) 5) 1 (EVar 41);
   KRange (EVar 41) 0 255;
   KWord (SA (EVar 33) 6) 1 (EVar 42);
   KRange (EVar 42) 0 255;
   KWord (SA (EVar 33) 7) 1 (EVar 43);
   KRange (EVar 43) 0 255].
Definition ss0 : sym_state := SS 230748 regs0 [] kn0 NX0.
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
Definition ex7 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f5).
Definition s7 : sym_state := snd (snd ex7).
(* [comment removed for export] *)
Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.
(* [comment removed for export] *)
Definition ex9 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t8).
Definition s9 : sym_state := snd (snd ex9).
(* [comment removed for export] *)
Definition ex10 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f8).
Definition s10 : sym_state := snd (snd ex10).
(* [comment removed for export] *)
Definition arms11 := Eval vm_compute in (match SGP.branch_probe IT s10 with Some e => SGP.case_arms s10 e 0 | None => None end).
Definition f11 : sym_state := match arms11 with Some (Some s, _) => s | _ => s10 end.
Definition t11 : sym_state := match arms11 with Some (_, Some s) => s | _ => s10 end.
(* [comment removed for export] *)
Definition ex12 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t11).
Definition s12 : sym_state := snd (snd ex12).
(* [comment removed for export] *)
Definition ex13 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f11).
Definition s13 : sym_state := snd (snd ex13).
(* [comment removed for export] *)
Definition arms14 := Eval vm_compute in (match SGP.branch_probe IT s13 with Some e => SGP.case_arms s13 e 0 | None => None end).
Definition f14 : sym_state := match arms14 with Some (Some s, _) => s | _ => s13 end.
Definition t14 : sym_state := match arms14 with Some (_, Some s) => s | _ => s13 end.
(* [comment removed for export] *)
Definition ex15 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t14).
Definition s15 : sym_state := snd (snd ex15).
(* [comment removed for export] *)
Definition ex16 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f14).
Definition s16 : sym_state := snd (snd ex16).
(* [comment removed for export] *)
Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.
(* [comment removed for export] *)
Definition ex18 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t17).
Definition s18 : sym_state := snd (snd ex18).
(* [comment removed for export] *)
Definition ex19 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f17).
Definition s19 : sym_state := snd (snd ex19).
(* [comment removed for export] *)
Definition arms20 := Eval vm_compute in (match SGP.branch_probe IT s19 with Some e => SGP.case_arms s19 e 0 | None => None end).
Definition f20 : sym_state := match arms20 with Some (Some s, _) => s | _ => s19 end.
Definition t20 : sym_state := match arms20 with Some (_, Some s) => s | _ => s19 end.
(* [comment removed for export] *)
Definition ex21 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t20).
Definition s21 : sym_state := snd (snd ex21).
(* [comment removed for export] *)
Definition ex22 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f20).
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
Definition ex25 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f23).
Definition s25 : sym_state := snd (snd ex25).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 2)) (SGA.mkplan (fst ex10) (SGP.PBranch (SGA.mkplan (fst ex12) (SGP.PEnd 3)) (SGA.mkplan (fst ex13) (SGP.PBranch (SGA.mkplan (fst ex15) (SGP.PEnd 4)) (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 5)) (SGA.mkplan (fst ex19) (SGP.PBranch (SGA.mkplan (fst ex21) (SGP.PEnd 6)) (SGA.mkplan (fst ex22) (SGP.PBranch (SGA.mkplan (fst ex24) (SGP.PEnd 7)) (SGA.mkplan (fst ex25) (SGP.PEnd 8))))))))))))))))).
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
Definition ps0 : SR.post_spec := SR.PS 230912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.
(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 230912 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.
(* [comment removed for export] *)
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s9).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s9).
Definition ps2 : SR.post_spec := SR.PS 230912 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.
(* [comment removed for export] *)
Definition regs_out3 : list expr := Eval vm_compute in (s_regs s12).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s12).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s12 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s12 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s12).
Definition ps3 : SR.post_spec := SR.PS 230912 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.
(* [comment removed for export] *)
Definition regs_out4 : list expr := Eval vm_compute in (s_regs s15).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s15).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s15 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s15 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s15).
Definition ps4 : SR.post_spec := SR.PS 230912 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.
(* [comment removed for export] *)
Definition regs_out5 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s18).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s18).
Definition ps5 : SR.post_spec := SR.PS 230912 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.
(* [comment removed for export] *)
Definition regs_out6 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s21).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s21).
Definition ps6 : SR.post_spec := SR.PS 230912 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.
(* [comment removed for export] *)
Definition regs_out7 : list expr := Eval vm_compute in (s_regs s24).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s24).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s24 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s24 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s24).
Definition ps7 : SR.post_spec := SR.PS 230912 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.
(* [comment removed for export] *)
Definition regs_out8 : list expr := Eval vm_compute in (s_regs s25).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s25).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s25 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s25 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s25).
Definition ps8 : SR.post_spec := SR.PS 231096 (map (fun i => (i, nth i regs_out8 (ELit 0))) (seq 1 31)) F0L cells8.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Bs_7c8953_u.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 230748 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_Bs_7c8953_u.IT SegItab_Bs_7c8953_u.IT_sound BF NX0 BR XSTEP F0 PSS plan 230748 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
