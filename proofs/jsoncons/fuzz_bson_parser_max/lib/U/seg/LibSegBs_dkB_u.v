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
Definition ENDS : list Z := [232388; 232624; 233600].
Definition STOPS1 : list Z := [232388; 232624; 233600] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-256))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (EAlu Instr.ALU_ADD (EVar 33) (ELit (42))); (EAlu Instr.ALU_ADD (EVar 33) (EVar 38)); EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 35; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
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
   KRange (EVar 35) 4096 140737488355312;
   KAlign (EVar 35) 8;
   KWord (SA (EVar 35) 0) 8 (EVar 36);
   KWord (SA (EVar 35) 8) 8 (EVar 37);
   KDisj (SA (EVar 2) (-240)) (ELit 240) (SA (EVar 35) 0) (ELit 16);
   KDisj (SA (EVar 33) 0) (ELit 42) (SA (EVar 35) 0) (ELit 16);
   KRange (EVar 38) 0 1].
Definition ss0 : sym_state := SS 232188 regs0 [] kn0 NX0.
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
Definition ex11 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f9).
Definition s11 : sym_state := snd (snd ex11).
Definition ex12 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f7).
Definition s12 : sym_state := snd (snd ex12).
Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.
Definition ex14 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t13).
Definition s14 : sym_state := snd (snd ex14).
Definition ex15 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f13).
Definition s15 : sym_state := snd (snd ex15).
Definition ex16 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f5).
Definition s16 : sym_state := snd (snd ex16).
Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.
Definition ex18 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 t17).
Definition s18 : sym_state := snd (snd ex18).
Definition ex19 : list SGA.aitem * (Z * sym_state) :=
  Eval vm_compute in (AUTO 2000 f17).
Definition s19 : sym_state := snd (snd ex19).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 1)) (SGA.mkplan (fst ex11) (SGP.PEnd 2)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PEnd 3)) (SGA.mkplan (fst ex15) (SGP.PEnd 4)))))) (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 5)) (SGA.mkplan (fst ex19) (SGP.PEnd 6))))))).
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
Definition ps0 : SR.post_spec := SR.PS 233600 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.
(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s10).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s10).
Definition ps1 : SR.post_spec := SR.PS 232624 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.
(* [comment removed for export] *)
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s11).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s11).
Definition ps2 : SR.post_spec := SR.PS 232388 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.
(* [comment removed for export] *)
Definition regs_out3 : list expr := Eval vm_compute in (s_regs s14).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s14).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s14 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s14 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s14).
Definition ps3 : SR.post_spec := SR.PS 232624 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.
Definition regs_out4 : list expr := Eval vm_compute in (s_regs s15).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s15).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s15 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s15 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s15).
Definition ps4 : SR.post_spec := SR.PS 232388 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.
Definition regs_out5 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s18).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s18).
Definition ps5 : SR.post_spec := SR.PS 232624 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.
Definition regs_out6 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s19).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s19).
Definition ps6 : SR.post_spec := SR.PS 232388 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Bs_aea5cf_u.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 232188 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_Bs_aea5cf_u.IT SegItab_Bs_aea5cf_u.IT_sound BF NX0 BR XSTEP F0 PSS plan 232188 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
