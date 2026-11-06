(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Src0PlanKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LibSegZ_srAd.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(142232, 67%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142400].
Definition STOPS1 : list Z := [136656; 142400; 142496] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 34; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048624 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KRange (EVar 33) 1048576 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (EVar 2) (-48)) (ELit 48) (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 0) 1 (EVar 36);
   KRange (EVar 36) 0 255;
   KWord (SA (EVar 33) 8) 8 (EVar 35);
   KRange (EVar 35) 1 300;
   KRange (EVar 34) 1 63;
   KRange (EAlu Instr.ALU_AND (EVar 36) (ELit 1)) 1 1;
   KWord (SA (EVar 33) 24) 8 (EVar 37);
   KRange (EVar 37) 4096 140737488355328;
   KAlign (EVar 37) 8].
Definition ss0 : sym_state := SS 142232 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-48), ELit 48)].
Definition F0L : list SR.region := [(EVar 2, (-48), 48)].
Definition BF : nat := 1000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).

(* [comment removed for export] *)
Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [136656; 142400; 142496; 142400])], (93, SS 142400 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 33; EVar 34; ELit 0; EVar 35; EAlu Instr.ALU_ADD (EVar 35) (ELit (-1)); EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 34)) (ELit 64); ELit 0; ELit 64; EVar 16; EVar 17; EVar 18; EVar 37; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 1048624 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -48 |} (ELit 48); KRange (EVar 33) 1048576 140737488355296; KAlign (EVar 33) 8; KDisj {| a_base := EVar 2; a_off := -48 |} (ELit 48) {| a_base := EVar 33; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 33; a_off := 0 |} 1 (EVar 36); KRange (EVar 36) 0 255; KWord {| a_base := EVar 33; a_off := 8 |} 8 (EVar 35); KRange (EVar 35) 1 300; KRange (EVar 34) 1 63; KRange (EAlu Instr.ALU_AND (EVar 36) (ELit 1)) 1 1; KWord {| a_base := EVar 33; a_off := 24 |} 8 (EVar 37); KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 8] 48))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 142400 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 142232 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 142232 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_srAd.

Module LibSegZ_srAi.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(142232, 67%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142400].
Definition STOPS1 : list Z := [136656; 142400; 142496] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 34; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048624 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KRange (EVar 33) 1048576 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (EVar 2) (-48)) (ELit 48) (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 0) 1 (EVar 36);
   KRange (EVar 36) 0 255;
   KWord (SA (EVar 33) 8) 8 (EVar 35);
   KRange (EVar 35) 1 300;
   KRange (EVar 34) 1 63;
   KRange (EAlu Instr.ALU_AND (EVar 36) (ELit 1)) 0 0;
   KWord (SA (EVar 33) 24) 8 (EVar 41)].
Definition ss0 : sym_state := SS 142232 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-48), ELit 48)].
Definition F0L : list SR.region := [(EVar 2, (-48), 48)].
Definition BF : nat := 1000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).

(* [comment removed for export] *)
Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [136656; 142400; 142496; 142400])], (93, SS 142400 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 33; EVar 34; ELit 0; EVar 35; EAlu Instr.ALU_ADD (EVar 35) (ELit (-1)); EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 34)) (ELit 64); ELit 0; ELit 64; EVar 16; EVar 17; EVar 18; EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 1048624 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -48 |} (ELit 48); KRange (EVar 33) 1048576 140737488355296; KAlign (EVar 33) 8; KDisj {| a_base := EVar 2; a_off := -48 |} (ELit 48) {| a_base := EVar 33; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 33; a_off := 0 |} 1 (EVar 36); KRange (EVar 36) 0 255; KWord {| a_base := EVar 33; a_off := 8 |} 8 (EVar 35); KRange (EVar 35) 1 300; KRange (EVar 34) 1 63; KRange (EAlu Instr.ALU_AND (EVar 36) (ELit 1)) 0 0; KWord {| a_base := EVar 33; a_off := 24 |} 8 (EVar 41)] 48))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 142400 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 142232 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 142232 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_srAi.

Module LibSegZ_srE.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(142232, 67%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142496].
Definition STOPS1 : list Z := [136656; 142400; 142496] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 42; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 33; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048624 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KWord (SA (EVar 2) (-8)) 8 (EVar 43);
   KWord (SA (EVar 2) (-16)) 8 (EVar 44);
   KWord (SA (EVar 2) (-24)) 8 (EVar 47);
   KWord (SA (EVar 2) (-32)) 8 (EVar 38);
   KWord (SA (EVar 2) (-40)) 8 (EVar 32)].
Definition ss0 : sym_state := SS 142452 regs0 [] kn0 NX0.
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

(* [comment removed for export] *)
Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [136656; 142400; 142496; 142496])], (93, SS 142496 [ELit 0; EVar 43; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 44; EVar 47; EVar 33; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 38; EVar 32; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048624 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -48 |} (ELit 48); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 43); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 44); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 47); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 38); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 32)] 48))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 142496 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 142452 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 142452 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_srE.

Module LibSegZ_srI.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(142232, 67%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142400].
Definition STOPS1 : list Z := [136656; 142400; 142496] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 42; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 33; EVar 34; EVar 39; EVar 35; (EAlu Instr.ALU_ADD (EVar 35) (ELit (-1))); EVar 45; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))); EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 37) 4096 140737488355328;
   KAlign (EVar 37) 8;
   KRange (EVar 35) 1 300;
   KRange (EVar 39) 0 299;
   KRange (EVar 34) 1 63;
   KWr (SA (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))) 0) (ELit 8);
   KWord (SA (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))) 0) 8 (EVar 40);
   KRange (EVar 40) 0 18446744073709551615;
   KRange (APC.esub (EVar 35) (EVar 39)) 2 300;
   KUnk (SA (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))) 8) (ELit 8)].
Definition ss0 : sym_state := SS 142400 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))), (0), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))), (0), 8)].
Definition BF : nat := 1000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).

(* [comment removed for export] *)
Definition s1 : sym_state :=
  (SS 142400 [ELit 0; EVar 42; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 33; EVar 34; EAlu Instr.ALU_ADD (EVar 39) (ELit 1); EVar 35; EAlu Instr.ALU_ADD (EVar 35) (ELit (-1)); EVar 45; EAlu Instr.ALU_OR (EAlu Instr.ALU_SLL (EVar 48) (EVar 45)) (EAlu Instr.ALU_SRL (EVar 40) (EVar 34)); EAlu Instr.ALU_SLL (EVar 48) (EVar 45); EVar 16; EVar 17; EVar 18; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))) (ELit 8); EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39)); a_off := 0 |} 8 (EAlu Instr.ALU_OR (EAlu Instr.ALU_SLL (EVar 48) (EVar 45)) (EAlu Instr.ALU_SRL (EVar 40) (EVar 34))); KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 8; KRange (EVar 35) 1 300; KRange (EVar 39) 0 299; KRange (EVar 34) 1 63; KWr {| a_base := EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39)); a_off := 0 |} (ELit 8); KRange (EVar 40) 0 18446744073709551615; KRange (EAlu Instr.ALU_ADD (EVar 35) (EMd Instr.M_MUL (ELit (-1)) (EVar 39))) 2 300; KUnk {| a_base := EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39)); a_off := 8 |} (ELit 8)] 49).

(* [comment removed for export] *)
Definition ex2 : list SGA.aitem * (Z * sym_state) :=
  (([], (93, SS 142400 [ELit 0; EVar 42; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 33; EVar 34; EAlu Instr.ALU_ADD (EVar 39) (ELit 1); EVar 35; EAlu Instr.ALU_ADD (EVar 35) (ELit (-1)); EVar 45; EAlu Instr.ALU_OR (EAlu Instr.ALU_SLL (EVar 48) (EVar 45)) (EAlu Instr.ALU_SRL (EVar 40) (EVar 34)); EAlu Instr.ALU_SLL (EVar 48) (EVar 45); EVar 16; EVar 17; EVar 18; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))) (ELit 8); EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39)); a_off := 0 |} 8 (EAlu Instr.ALU_OR (EAlu Instr.ALU_SLL (EVar 48) (EVar 45)) (EAlu Instr.ALU_SRL (EVar 40) (EVar 34))); KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 8; KRange (EVar 35) 1 300; KRange (EVar 39) 0 299; KRange (EVar 34) 1 63; KWr {| a_base := EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39)); a_off := 0 |} (ELit 8); KRange (EVar 40) 0 18446744073709551615; KRange (EAlu Instr.ALU_ADD (EVar 35) (EMd Instr.M_MUL (ELit (-1)) (EVar 39))) 2 300; KUnk {| a_base := EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39)); a_off := 8 |} (ELit 8)] 49))).
Definition s2 : sym_state := snd (snd ex2).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGA.mkplan (fst ex2) (SGP.PEnd 0)).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s2).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s2).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s2 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s2 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s2).
Definition ps0 : SR.post_spec := SR.PS 142400 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 142400 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 142400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_srI.

Module LibSegZ_srL.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(142232, 67%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [136656].
Definition STOPS1 : list Z := [136656; 142400; 142496] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 42; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-48))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 33; EVar 34; EVar 39; EVar 35; (EAlu Instr.ALU_ADD (EVar 35) (ELit (-1))); EVar 45; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))); EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 37) 4096 140737488355328;
   KAlign (EVar 37) 8;
   KRange (EVar 35) 1 300;
   KRange (EVar 39) 0 299;
   KRange (EVar 34) 1 63;
   KWr (SA (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))) 0) (ELit 8);
   KWord (SA (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))) 0) 8 (EVar 40);
   KRange (EVar 40) 0 18446744073709551615;
   KRange (APC.esub (EVar 35) (EVar 39)) 1 1].
Definition ss0 : sym_state := SS 142400 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))), (0), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))), (0), 8)].
Definition BF : nat := 1000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).

(* [comment removed for export] *)
Definition s1 : sym_state :=
  (SS 136656 [ELit 0; ELit 142452; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 33; EVar 34; EVar 33; EVar 35; EAlu Instr.ALU_ADD (EVar 35) (ELit (-1)); EVar 45; EAlu Instr.ALU_SRL (EVar 40) (EVar 34); EVar 15; EVar 16; EVar 17; EVar 18; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))) (ELit 8); EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39)); a_off := 0 |} 8 (EAlu Instr.ALU_SRL (EVar 40) (EVar 34)); KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 8; KRange (EVar 35) 1 300; KRange (EVar 39) 0 299; KRange (EVar 34) 1 63; KWr {| a_base := EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39)); a_off := 0 |} (ELit 8); KRange (EVar 40) 0 18446744073709551615; KRange (EAlu Instr.ALU_ADD (EVar 35) (EMd Instr.M_MUL (ELit (-1)) (EVar 39))) 1 1] 48).

(* [comment removed for export] *)
Definition ex2 : list SGA.aitem * (Z * sym_state) :=
  (([], (93, SS 136656 [ELit 0; ELit 142452; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 33; EVar 34; EVar 33; EVar 35; EAlu Instr.ALU_ADD (EVar 35) (ELit (-1)); EVar 45; EAlu Instr.ALU_SRL (EVar 40) (EVar 34); EVar 15; EVar 16; EVar 17; EVar 18; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39))) (ELit 8); EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39)); a_off := 0 |} 8 (EAlu Instr.ALU_SRL (EVar 40) (EVar 34)); KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 8; KRange (EVar 35) 1 300; KRange (EVar 39) 0 299; KRange (EVar 34) 1 63; KWr {| a_base := EAlu Instr.ALU_ADD (EVar 37) (EMd Instr.M_MUL (ELit 8) (EVar 39)); a_off := 0 |} (ELit 8); KRange (EVar 40) 0 18446744073709551615; KRange (EAlu Instr.ALU_ADD (EVar 35) (EMd Instr.M_MUL (ELit (-1)) (EVar 39))) 1 1] 48))).
Definition s2 : sym_state := snd (snd ex2).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGA.mkplan (fst ex2) (SGP.PEnd 0)).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s2).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s2).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s2 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s2 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s2).
Definition ps0 : SR.post_spec := SR.PS 136656 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 142400 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 142400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_srL.
