(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u Bs0PlanKitIt_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require SegItab_Bs_aea5cf_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Bs_aea5cf_u.ITR.
Definition IT : itab := SegItab_Bs_aea5cf_u.IT.
Definition ENDS : list Z := [232388; 232624].
Definition STOPS1 : list Z := [232388; 232624] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 33) (ELit 42); EAlu Instr.ALU_ADD (EVar 33) (EVar 38); EVar 10; EVar 11; EVar 36; EVar 37; EVar 14; EVar 39; EVar 16; EVar 17; EVar 33; EVar 35; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
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
   KRange (EVar 33) 4096 140737488355286;
   KWr (SA (EVar 33) 0) (ELit 42);
   KDisj (SA (EVar 2) (-240)) (ELit 240) (SA (EVar 33) 0) (ELit 42);
   KImg 65536 754672;
   KRange (EVar 38) 0 1;
   KRange (EVar 39) 0 4294967295].
Definition ss0 : sym_state := SS 233704 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-232), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-232), 16)].
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
Definition ex5 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t4).
Definition s5 : sym_state := snd (snd ex5).
Definition arms6 := Eval vm_compute in (match SGP.branch_probe IT s5 with Some e => SGP.case_arms s5 e 0 | None => None end).
Definition f6 : sym_state := match arms6 with Some (Some s, _) => s | _ => s5 end.
Definition t6 : sym_state := match arms6 with Some (_, Some s) => s | _ => s5 end.
Definition ex7 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t6).
Definition s7 : sym_state := snd (snd ex7).
Definition ex8 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f6).
Definition s8 : sym_state := snd (snd ex8).
Definition ex9 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f4).
Definition s9 : sym_state := snd (snd ex9).
Definition arms10 := Eval vm_compute in (match SGP.branch_probe IT s9 with Some e => SGP.case_arms s9 e 0 | None => None end).
Definition f10 : sym_state := match arms10 with Some (Some s, _) => s | _ => s9 end.
Definition t10 : sym_state := match arms10 with Some (_, Some s) => s | _ => s9 end.
Definition ex11 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t10).
Definition s11 : sym_state := snd (snd ex11).
Definition ex12 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f10).
Definition s12 : sym_state := snd (snd ex12).
Definition ex13 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f2).
Definition s13 : sym_state := snd (snd ex13).
Definition arms14 := Eval vm_compute in (match SGP.branch_probe IT s13 with Some e => SGP.case_arms s13 e 0 | None => None end).
Definition f14 : sym_state := match arms14 with Some (Some s, _) => s | _ => s13 end.
Definition t14 : sym_state := match arms14 with Some (_, Some s) => s | _ => s13 end.
Definition ex15 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t14).
Definition s15 : sym_state := snd (snd ex15).
Definition ex16 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f14).
Definition s16 : sym_state := snd (snd ex16).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PBranch (SGA.mkplan (fst ex7) (SGP.PEnd 0)) (SGA.mkplan (fst ex8) (SGP.PEnd 1)))) (SGA.mkplan (fst ex9) (SGP.PBranch (SGA.mkplan (fst ex11) (SGP.PEnd 2)) (SGA.mkplan (fst ex12) (SGP.PEnd 3)))))) (SGA.mkplan (fst ex13) (SGP.PBranch (SGA.mkplan (fst ex15) (SGP.PEnd 4)) (SGA.mkplan (fst ex16) (SGP.PEnd 5))))).
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
Definition ps0 : SR.post_spec := SR.PS 232624 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.
(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s8).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s8).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s8 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s8 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s8).
Definition ps1 : SR.post_spec := SR.PS 232388 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s11).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s11).
Definition ps2 : SR.post_spec := SR.PS 232624 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.
Definition regs_out3 : list expr := Eval vm_compute in (s_regs s12).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s12).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s12 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s12 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s12).
Definition ps3 : SR.post_spec := SR.PS 232388 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.
Definition regs_out4 : list expr := Eval vm_compute in (s_regs s15).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s15).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s15 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s15 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s15).
Definition ps4 : SR.post_spec := SR.PS 232624 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.
Definition regs_out5 : list expr := Eval vm_compute in (s_regs s16).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s16).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s16 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s16 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s16).
Definition ps5 : SR.post_spec := SR.PS 232388 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Bs_aea5cf_u.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233704 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_Bs_aea5cf_u.IT SegItab_Bs_aea5cf_u.IT_sound BF NX0 BR XSTEP F0 PSS plan 233704 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
