(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ba0PlanKit Ba0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.seg Require SegItab_Ba_0ad7fe.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_0ad7fe.ITR.
Definition IT : itab := SegItab_Ba_0ad7fe.IT.
Definition ENDS : list Z := [728268; 728456].
Definition STOPS1 : list Z := [728268; 728456] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-96))); EVar 3; EVar 4; ELit 245; ELit (-65); ELit 239; ELit 240; ELit 144; (EVar 33); EVar 11; EVar 12; EVar 13; (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)); ELit 8; ELit 1; ELit (-62); ELit 2147450880; ELit 244; ELit 143; ELit 2; ELit 3; (EVar 36); (EVar 37); ELit 0; EVar 26; EVar 27; ELit 224; ELit 160; ELit 237; ELit 159].
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 728056 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [728268; 728456; 728268; 728456])], (91, SS 728244 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-96)); EVar 3; EVar 4; ELit 245; ELit (-65); ELit 239; ELit 240; ELit 144; EVar 33; ELit 6; EAlu Instr.ALU_ADD (EVar 33) (ELit 1); EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56); EAlu Instr.ALU_ADD (EVar 33) (EVar 35); ELit 8; ELit 1; ELit (-62); ELit 2147450880; ELit 244; ELit 143; ELit 2; ELit 3; EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36); EVar 37; ELit 0; EVar 26; EVar 27; ELit 224; ELit 160; ELit 237; ELit 159] [] [KRange (EVar 33) 0 140737488355328; KRange (EVar 35) 1 67108864; KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328; KRange (EVar 37) 0 255] 60))).
Definition s1 : sym_state := snd (snd ex1).

(* [comment removed for export] *)
Definition ex2 : list SGA.aitem * (Z * sym_state) :=
  (([], (91, SS 728244 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-96)); EVar 3; EVar 4; ELit 245; ELit (-65); ELit 239; ELit 240; ELit 144; EVar 33; ELit 6; EAlu Instr.ALU_ADD (EVar 33) (ELit 1); EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56); EAlu Instr.ALU_ADD (EVar 33) (EVar 35); ELit 8; ELit 1; ELit (-62); ELit 2147450880; ELit 244; ELit 143; ELit 2; ELit 3; EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36); EVar 37; ELit 0; EVar 26; EVar 27; ELit 224; ELit 160; ELit 237; ELit 159] [] [KRange (EVar 33) 0 140737488355328; KRange (EVar 35) 1 67108864; KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328; KRange (EVar 37) 0 255] 60))).
Definition s2 : sym_state := snd (snd ex2).

(* [comment removed for export] *)
Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

(* [comment removed for export] *)
Definition ex4 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [728268; 728456; 728268; 728456])], (93, SS 728456 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-96)); EVar 3; EVar 4; ELit 245; ELit (-65); ELit 239; ELit 240; ELit 144; EVar 33; ELit 6; EAlu Instr.ALU_ADD (EVar 33) (ELit 1); EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56); EAlu Instr.ALU_ADD (EVar 33) (EVar 35); ELit 8; ELit 1; ELit (-62); ELit 2147450880; ELit 244; ELit 143; ELit 2; ELit 3; EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36); EVar 37; ELit 0; EVar 26; EVar 27; ELit 224; ELit 160; ELit 237; ELit 159] [] [KRange (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62))) 1 1; KRange (EVar 33) 0 140737488355328; KRange (EVar 35) 1 67108864; KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328; KRange (EVar 37) 0 255] 60))).
Definition s4 : sym_state := snd (snd ex4).

(* [comment removed for export] *)
Definition ex5 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [728268; 728456; 728268; 728456])], (91, SS 728248 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-96)); EVar 3; EVar 4; ELit 245; ELit (-65); ELit 239; ELit 240; ELit 144; EVar 33; ELit 6; EAlu Instr.ALU_ADD (EVar 33) (ELit 1); EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56); EAlu Instr.ALU_ADD (EVar 33) (EVar 35); ELit 8; ELit 1; ELit (-62); ELit 2147450880; ELit 244; ELit 143; ELit 2; ELit 3; EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36); EVar 37; ELit 0; EVar 26; EVar 27; ELit 224; ELit 160; ELit 237; ELit 159] [] [KRange (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62))) 0 0; KRange (EVar 33) 0 140737488355328; KRange (EVar 35) 1 67108864; KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328; KRange (EVar 37) 0 255] 60))).
Definition s5 : sym_state := snd (snd ex5).

(* [comment removed for export] *)
Definition arms6 := Eval vm_compute in (match SGP.branch_probe IT s5 with Some e => SGP.case_arms s5 e 0 | None => None end).
Definition f6 : sym_state := match arms6 with Some (Some s, _) => s | _ => s5 end.
Definition t6 : sym_state := match arms6 with Some (_, Some s) => s | _ => s5 end.

(* [comment removed for export] *)
Definition ex7 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [728268; 728456; 728268; 728456])], (93, SS 728268 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-96)); EVar 3; EVar 4; ELit 245; ELit (-65); ELit 239; ELit 240; ELit 144; EVar 33; ELit 6; EAlu Instr.ALU_ADD (EVar 33) (ELit 1); EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56); EAlu Instr.ALU_ADD (EVar 33) (EVar 35); ELit 8; ELit 1; ELit (-62); ELit 2147450880; ELit 244; ELit 143; ELit 2; ELit 3; EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36); EVar 37; ELit 0; EVar 26; EVar 27; ELit 224; ELit 160; ELit 237; ELit 159] [] [KRange (EAlu Instr.ALU_SLTU (EVar 37) (ELit 245)) 1 1; KRange (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62))) 0 0; KRange (EVar 33) 0 140737488355328; KRange (EVar 35) 1 67108864; KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328; KRange (EVar 37) 0 255] 60))).
Definition s7 : sym_state := snd (snd ex7).

(* [comment removed for export] *)
Definition ex8 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [728268; 728456; 728268; 728456])], (93, SS 728456 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-96)); EVar 3; EVar 4; ELit 245; ELit (-65); ELit 239; ELit 240; ELit 144; EVar 33; ELit 6; EAlu Instr.ALU_ADD (EVar 33) (ELit 1); EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56); EAlu Instr.ALU_ADD (EVar 33) (EVar 35); ELit 8; ELit 1; ELit (-62); ELit 2147450880; ELit 244; ELit 143; ELit 2; ELit 3; EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36); EVar 37; ELit 0; EVar 26; EVar 27; ELit 224; ELit 160; ELit 237; ELit 159] [] [KRange (EAlu Instr.ALU_SLTU (EVar 37) (ELit 245)) 0 0; KRange (EAlu Instr.ALU_SLT (EAlu Instr.ALU_SRA (EMd Instr.M_MUL (ELit 72057594037927936) (EVar 36)) (ELit 56)) (ELit (-62))) 0 0; KRange (EVar 33) 0 140737488355328; KRange (EVar 35) 1 67108864; KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328; KRange (EVar 37) 0 255] 60))).
Definition s8 : sym_state := snd (snd ex8).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PBranch (SGA.mkplan (fst ex7) (SGP.PEnd 1)) (SGA.mkplan (fst ex8) (SGP.PEnd 2)))))).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 728456 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s7).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s7).
Definition ps1 : SR.post_spec := SR.PS 728268 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

(* [comment removed for export] *)
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s8).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s8).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s8 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s8 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s8).
Definition ps2 : SR.post_spec := SR.PS 728456 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_0ad7fe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 728056 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_0ad7fe.IT SegItab_Ba_0ad7fe.IT_sound BF NX0 BR XSTEP F0 PSS plan 728056 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
