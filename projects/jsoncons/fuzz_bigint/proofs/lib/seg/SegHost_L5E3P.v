(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Src0PlanKit Src0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require SegItab_S_079d1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LibSegZ_e3p1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [309252].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64);
   KUnk (SA (EVar 2) (-64)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KRange (EVar 38) 4096 140737488355328;
   KAlign (EVar 38) 16;
   KWr (SA (EVar 38) 0) (ELit 48);
   KUnk (SA (EVar 38) 0) (ELit 48);
   KDisj (SA (EVar 2) (-64)) (ELit 96) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 38) 0) (ELit 48);
   KDisj (SA (EVar 2) (-64)) (ELit 96) (SA (EVar 38) 0) (ELit 48);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KDisj (SA (EVar 38) 0) (ELit 48) (SA (ELit 0) 65536) (ELit 528384);
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (0)) 8 (ELit 49);
   KWord (SA (EVar 2) (16)) 8 (EVar 38)].
Definition ss0 : sym_state := SS 136368 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-64), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (-64), 64)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309252])], (93, SS 309252 [ELit 0; ELit 136400; EVar 2; ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 38; ELit 48; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -64 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -64 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 16; KWr {| a_base := EVar 38; a_off := 0 |} (ELit 48); KUnk {| a_base := EVar 38; a_off := 0 |} (ELit 48); KDisj {| a_base := EVar 2; a_off := -64 |} (ELit 96) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := EVar 38; a_off := 0 |} (ELit 48); KDisj {| a_base := EVar 2; a_off := -64 |} (ELit 96) {| a_base := EVar 38; a_off := 0 |} (ELit 48); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KDisj {| a_base := EVar 38; a_off := 0 |} (ELit 48) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := 0 |} 8 (ELit 49); KWord {| a_base := EVar 2; a_off := 16 |} 8 (EVar 38)] 56))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 309252 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 136368 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS plan 136368 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e3p1.

Module LibSegZ_e3p1b.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [136420].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 40; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64);
   KUnk (SA (EVar 2) (-64)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (-64)) (ELit 64) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760].
Definition ss0 : sym_state := SS 136400 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-64), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (-64), 64)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 136420])], (93, SS 136420 [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -64 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -64 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := -64 |} (ELit 64) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760] 56))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 136420 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 136400 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS plan 136400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e3p1b.

Module LibSegZ_e3p2.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [309252].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (128)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (64)) (ELit 64);
   KUnk (SA (EVar 2) (64)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (64)) (ELit 208) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 42) 0) (ELit 64);
   KDisj (SA (EVar 2) (64)) (ELit 208) (SA (EVar 42) 0) (ELit 64);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KDisj (SA (EVar 42) 0) (ELit 64) (SA (ELit 0) 65536) (ELit 528384);
   KRange (EVar 40) 0 255;
   KRange (EVar 41) 0 255;
   KRange (EVar 42) 4096 140737488355328;
   KAlign (EVar 42) 16;
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (200)) 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254));
   KWord (SA (EVar 2) (232)) 1 (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 41) (ELit 254)) (ELit 1));
   KWord (SA (EVar 2) (256)) 8 (EVar 42);
   KWord (SA (EVar 2) (248)) 8 (ELit 8)].
Definition ss0 : sym_state := SS 140248 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (64), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (64), 64)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309252])], (93, SS 309252 [ELit 0; ELit 140316; EAlu Instr.ALU_ADD (EVar 2) (ELit 128); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 9; EVar 42; ELit 64; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := 64 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := 64 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := 64 |} (ELit 208) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := EVar 42; a_off := 0 |} (ELit 64); KDisj {| a_base := EVar 2; a_off := 64 |} (ELit 208) {| a_base := EVar 42; a_off := 0 |} (ELit 64); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KDisj {| a_base := EVar 42; a_off := 0 |} (ELit 64) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KRange (EVar 40) 0 255; KRange (EVar 41) 0 255; KRange (EVar 42) 4096 140737488355328; KAlign (EVar 42) 16; KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := 200 |} 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254)); KWord {| a_base := EVar 2; a_off := 232 |} 1 (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 41) (ELit 254)) (ELit 1)); KWord {| a_base := EVar 2; a_off := 256 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := 248 |} 8 (ELit 8)] 56))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 309252 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140248 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS plan 140248 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e3p2.

Module LibSegZ_e3p2b.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [309252].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (128)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 40; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (64)) (ELit 64);
   KUnk (SA (EVar 2) (64)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (64)) (ELit 240) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 42) 0) (ELit 64);
   KDisj (SA (EVar 2) (64)) (ELit 240) (SA (EVar 42) 0) (ELit 64);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KDisj (SA (EVar 42) 0) (ELit 64) (SA (ELit 0) 65536) (ELit 528384);
   KRange (EVar 41) 0 255;
   KRange (EVar 42) 4096 140737488355328;
   KAlign (EVar 42) 16;
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (264)) 1 (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 41) (ELit 254)) (ELit 1));
   KWord (SA (EVar 2) (288)) 8 (EVar 42);
   KWord (SA (EVar 2) (280)) 8 (ELit 8)].
Definition ss0 : sym_state := SS 140316 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (64), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (64), 64)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309252])], (93, SS 309252 [ELit 0; ELit 140348; EAlu Instr.ALU_ADD (EVar 2) (ELit 128); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 42; ELit 64; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := 64 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := 64 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := 64 |} (ELit 240) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := EVar 42; a_off := 0 |} (ELit 64); KDisj {| a_base := EVar 2; a_off := 64 |} (ELit 240) {| a_base := EVar 42; a_off := 0 |} (ELit 64); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KDisj {| a_base := EVar 42; a_off := 0 |} (ELit 64) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KRange (EVar 41) 0 255; KRange (EVar 42) 4096 140737488355328; KAlign (EVar 42) 16; KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := 264 |} 1 (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 41) (ELit 254)) (ELit 1)); KWord {| a_base := EVar 2; a_off := 288 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := 280 |} 8 (ELit 8)] 56))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 309252 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140316 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS plan 140316 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e3p2b.

Module LibSegZ_e3p2c.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [140392].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (128)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 9; EVar 40; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (64)) (ELit 64);
   KUnk (SA (EVar 2) (64)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (64)) (ELit 240) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KRange (EVar 41) 0 255;
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (296)) 1 (EAlu Instr.ALU_AND (EVar 41) (ELit 254))].
Definition ss0 : sym_state := SS 140348 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (64), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (64), 64)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 140392])], (93, SS 140392 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit 128); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := 64 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := 64 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := 64 |} (ELit 240) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KRange (EVar 41) 0 255; KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := 296 |} 1 (EAlu Instr.ALU_AND (EVar 41) (ELit 254))] 56))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 140392 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140348 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS plan 140348 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e3p2c.

Module LibSegZ_e3p3.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [142228].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (432)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (368)) (ELit 64);
   KUnk (SA (EVar 2) (368)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (368)) (ELit 80) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KRange (EVar 40) 0 255;
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (432)) 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254))].
Definition ss0 : sym_state := SS 142188 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (368), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (368), 64)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 142228])], (93, SS 142228 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit 432); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); ELit 0; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := 368 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := 368 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := 368 |} (ELit 80) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KRange (EVar 40) 0 255; KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := 432 |} 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254))] 56))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 142228 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 142188 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS plan 142188 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e3p3.

Module LibSegZ_e3p4.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [141380].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (480)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (416)) (ELit 64);
   KUnk (SA (EVar 2) (416)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (416)) (ELit 80) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KRange (EVar 40) 0 255;
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (488)) 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254))].
Definition ss0 : sym_state := SS 141340 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (416), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (416), 64)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 141380])], (93, SS 141380 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit 480); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); ELit 0; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := 416 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := 416 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := 416 |} (ELit 80) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KRange (EVar 40) 0 255; KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := 488 |} 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254))] 56))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 141380 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141340 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS plan 141340 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e3p4.

Module LibSegZ_e3p5.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [309252].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (544)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (480)) (ELit 64);
   KUnk (SA (EVar 2) (480)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (480)) (ELit 240) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 43) 0) (ELit 64);
   KDisj (SA (EVar 2) (480)) (ELit 240) (SA (EVar 43) 0) (ELit 64);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KDisj (SA (EVar 43) 0) (ELit 64) (SA (ELit 0) 65536) (ELit 528384);
   KRange (EVar 40) 0 255;
   KRange (EVar 41) 0 255;
   KRange (EVar 42) 0 255;
   KRange (EVar 43) 4096 140737488355328;
   KAlign (EVar 43) 16;
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (616)) 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254));
   KWord (SA (EVar 2) (648)) 1 (EAlu Instr.ALU_AND (EVar 41) (ELit 254));
   KWord (SA (EVar 2) (680)) 1 (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 42) (ELit 254)) (ELit 1));
   KWord (SA (EVar 2) (704)) 8 (EVar 43);
   KWord (SA (EVar 2) (696)) 8 (ELit 8)].
Definition ss0 : sym_state := SS 140244 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (480), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (480), 64)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309252])], (93, SS 309252 [ELit 0; ELit 140348; EAlu Instr.ALU_ADD (EVar 2) (ELit 544); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 9; EVar 43; ELit 64; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := 480 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := 480 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := 480 |} (ELit 240) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := EVar 43; a_off := 0 |} (ELit 64); KDisj {| a_base := EVar 2; a_off := 480 |} (ELit 240) {| a_base := EVar 43; a_off := 0 |} (ELit 64); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KDisj {| a_base := EVar 43; a_off := 0 |} (ELit 64) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KRange (EVar 40) 0 255; KRange (EVar 41) 0 255; KRange (EVar 42) 0 255; KRange (EVar 43) 4096 140737488355328; KAlign (EVar 43) 16; KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := 616 |} 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254)); KWord {| a_base := EVar 2; a_off := 648 |} 1 (EAlu Instr.ALU_AND (EVar 41) (ELit 254)); KWord {| a_base := EVar 2; a_off := 680 |} 1 (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 42) (ELit 254)) (ELit 1)); KWord {| a_base := EVar 2; a_off := 704 |} 8 (EVar 43); KWord {| a_base := EVar 2; a_off := 696 |} 8 (ELit 8)] 56))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 309252 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140244 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS plan 140244 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e3p5.

Module LibSegZ_e3p5b.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [309252].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (544)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 40; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (480)) (ELit 64);
   KUnk (SA (EVar 2) (480)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (480)) (ELit 272) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 42) 0) (ELit 64);
   KDisj (SA (EVar 2) (480)) (ELit 272) (SA (EVar 42) 0) (ELit 64);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KDisj (SA (EVar 42) 0) (ELit 64) (SA (ELit 0) 65536) (ELit 528384);
   KRange (EVar 41) 0 255;
   KRange (EVar 42) 4096 140737488355328;
   KAlign (EVar 42) 16;
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (712)) 1 (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 41) (ELit 254)) (ELit 1));
   KWord (SA (EVar 2) (736)) 8 (EVar 42);
   KWord (SA (EVar 2) (728)) 8 (ELit 8)].
Definition ss0 : sym_state := SS 140348 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (480), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (480), 64)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309252])], (93, SS 309252 [ELit 0; ELit 140388; EAlu Instr.ALU_ADD (EVar 2) (ELit 544); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 42; ELit 64; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := 480 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := 480 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := 480 |} (ELit 272) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := EVar 42; a_off := 0 |} (ELit 64); KDisj {| a_base := EVar 2; a_off := 480 |} (ELit 272) {| a_base := EVar 42; a_off := 0 |} (ELit 64); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KDisj {| a_base := EVar 42; a_off := 0 |} (ELit 64) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KRange (EVar 41) 0 255; KRange (EVar 42) 4096 140737488355328; KAlign (EVar 42) 16; KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := 712 |} 1 (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 41) (ELit 254)) (ELit 1)); KWord {| a_base := EVar 2; a_off := 736 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := 728 |} 8 (ELit 8)] 56))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 309252 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140348 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS plan 140348 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e3p5b.

Module LibSegZ_e3p5c.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [140392].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (544)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 9; EVar 40; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (480)) (ELit 64);
   KUnk (SA (EVar 2) (480)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (480)) (ELit 64) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760].
Definition ss0 : sym_state := SS 140388 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (480), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (480), 64)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 140392])], (93, SS 140392 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit 544); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := 480 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := 480 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := 480 |} (ELit 64) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760] 56))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 140392 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140388 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS plan 140388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e3p5c.

Module LibSegZ_e3p6.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_079d1e.ITR.
Definition IT : itab := SegItab_S_079d1e.IT.
Definition ENDS : list Z := [138620].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (848)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (784)) (ELit 64);
   KUnk (SA (EVar 2) (784)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (784)) (ELit 80) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KRange (EVar 40) 0 255;
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (848)) 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254))].
Definition ss0 : sym_state := SS 138580 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (784), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (784), 64)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 138620])], (93, SS 138620 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit 848); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); ELit 0; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := 784 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := 784 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := 784 |} (ELit 80) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KRange (EVar 40) 0 255; KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := 848 |} 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254))] 56))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 138620 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_079d1e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 138580 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_079d1e.IT SegItab_S_079d1e.IT_sound BF NX0 BR XSTEP F0 PSS plan 138580 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e3p6.
