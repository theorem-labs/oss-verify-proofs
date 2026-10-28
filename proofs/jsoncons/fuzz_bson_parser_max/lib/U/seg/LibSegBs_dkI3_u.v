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
Definition ENDS : list Z := [233176; 362808].
Definition STOPS1 : list Z := [233176; 362808] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-256))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (EAlu Instr.ALU_ADD (EVar 33) (ELit (42))); (EAlu Instr.ALU_ADD (EVar 33) (EVar 38)); EVar 70; EVar 71; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 52; (EAlu Instr.ALU_ADD (EVar 33) (EVar 59)); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483312 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-256)) (ELit 256);
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
   KDisj (SA (EVar 2) (-256)) (ELit 256) (SA (EVar 33) 0) (ELit 42);
   KImg 65536 754672;
   KRange (EVar 50) 0 16383;
   KRange (EVar 38) 0 1;
   KRange (EVar 59) 1 37].
Definition ss0 : sym_state := SS 233132 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 33) (EVar 59)), (0), ELit 1); ((EVar 2), (-256), ELit 24)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 33) (EVar 59)), (0), 1); ((EVar 2), (-256), 24)].
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
  (([SGA.AStep (SR.SBlock [233176; 362808; 233176; 362808])], (91, SS 233160 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 33) (ELit 42); EAlu Instr.ALU_ADD (EVar 33) (EVar 38); ELit 69; EVar 71; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 52; EAlu Instr.ALU_ADD (EVar 33) (EVar 59); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -240 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -248 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -256 |} 8 (ELit 0); KWord {| a_base := EAlu Instr.ALU_ADD (EVar 33) (EVar 59); a_off := 0 |} 1 (ELit 69); KRange (EVar 2) 140735332483312 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 60); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 63); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 64); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 68); KRange (EVar 33) 4096 140737488355286; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 2; a_off := -256 |} (ELit 256) {| a_base := EVar 33; a_off := 0 |} (ELit 42); KRange (EVar 50) 0 16383; KRange (EVar 38) 0 1; KRange (EVar 59) 1 37] 80))).
Definition s1 : sym_state := snd (snd ex1).

(* [comment removed for export] *)
Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

(* [comment removed for export] *)
Definition ex3 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [233176; 362808; 233176; 362808])], (93, SS 233176 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 33) (ELit 42); EAlu Instr.ALU_ADD (EVar 33) (EVar 38); ELit 69; EVar 71; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 52; EAlu Instr.ALU_ADD (EVar 33) (EVar 59); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLT (EVar 52) (ELit 0)) 1 1; KWord {| a_base := EVar 2; a_off := -240 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -248 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -256 |} 8 (ELit 0); KWord {| a_base := EAlu Instr.ALU_ADD (EVar 33) (EVar 59); a_off := 0 |} 1 (ELit 69); KRange (EVar 2) 140735332483312 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 60); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 63); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 64); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 68); KRange (EVar 33) 4096 140737488355286; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 2; a_off := -256 |} (ELit 256) {| a_base := EVar 33; a_off := 0 |} (ELit 42); KRange (EVar 50) 0 16383; KRange (EVar 38) 0 1; KRange (EVar 59) 1 37] 80))).
Definition s3 : sym_state := snd (snd ex3).

(* [comment removed for export] *)
Definition ex4 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [233176; 362808; 233176; 362808])], (93, SS 362808 [ELit 0; ELit 233176; EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 33) (ELit 42); EAlu Instr.ALU_ADD (EVar 33) (EVar 38); EAlu Instr.ALU_ADD (EVar 2) (ELit (-256)); ELit 43; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 52; EAlu Instr.ALU_ADD (EVar 33) (EVar 59); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EAlu Instr.ALU_SLT (EVar 52) (ELit 0)) 0 0; KWord {| a_base := EVar 2; a_off := -240 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -248 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -256 |} 8 (ELit 0); KWord {| a_base := EAlu Instr.ALU_ADD (EVar 33) (EVar 59); a_off := 0 |} 1 (ELit 69); KRange (EVar 2) 140735332483312 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -256 |} (ELit 256); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 60); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 63); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 64); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 68); KRange (EVar 33) 4096 140737488355286; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 42); KDisj {| a_base := EVar 2; a_off := -256 |} (ELit 256) {| a_base := EVar 33; a_off := 0 |} (ELit 42); KRange (EVar 50) 0 16383; KRange (EVar 38) 0 1; KRange (EVar 59) 1 37] 80))).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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
Definition ps0 : SR.post_spec := SR.PS 233176 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 362808 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Bs_aea5cf_u.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233132 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_Bs_aea5cf_u.IT SegItab_Bs_aea5cf_u.IT_sound BF NX0 BR XSTEP F0 PSS plan 233132 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
