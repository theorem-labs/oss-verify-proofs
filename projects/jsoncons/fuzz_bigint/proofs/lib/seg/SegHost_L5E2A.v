(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Src0PlanKit Src0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require SegItab_S_101909.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LibSegZ_e2a1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_101909.ITR.
Definition IT : itab := SegItab_S_101909.IT.
Definition ENDS : list Z := [309576].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 16; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-112)) (ELit 112);
   KUnk (SA (EVar 2) (-112)) (ELit 112);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (-112)) (ELit 112) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760].
Definition ss0 : sym_state := SS 140112 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-112), ELit 112)].
Definition F0L : list SR.region := [(EVar 2, (-112), 112)].
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309576])], (93, SS 309576 [ELit 0; ELit 259044; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; ELit 144; EVar 9; ELit 16; ELit 144; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -48 |} 8 (ELit 144); KWord {| a_base := EVar 2; a_off := -40 |} 8 (ELit 257240); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 140116); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -112 |} (ELit 112); KUnk {| a_base := EVar 2; a_off := -112 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -32 |} (ELit 8); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := -112 |} (ELit 112) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760] 56))).
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
Definition ps0 : SR.post_spec := SR.PS 309576 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_101909.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140112 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_101909.IT SegItab_S_101909.IT_sound BF NX0 BR XSTEP F0 PSS plan 140112 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e2a1.

Module LibSegZ_e2a2.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_101909.ITR.
Definition IT : itab := SegItab_S_101909.IT.
Definition ENDS : list Z := [140132].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-128)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-112)) (ELit 64);
   KUnk (SA (EVar 2) (-112)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (-112)) (ELit 112) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (-40)) 8 (ELit 257240);
   KWord (SA (EVar 2) (-48)) 8 (ELit 144);
   KWord (SA (EVar 2) (-8)) 8 (ELit 140116);
   KWord (SA (EVar 2) (-16)) 8 (EVar 40);
   KWord (SA (EVar 2) (-24)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (304)))].
Definition ss0 : sym_state := SS 259044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-112), ELit 64); (EVar 10, (-128), ELit 144)].
Definition F0L : list SR.region := [(EVar 2, (-112), 64); (EVar 10, (-128), 144)].
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 140132]); SGA.AStep SR.SFill; SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 140132])], (93, SS 140132 [ELit 0; ELit 140116; EVar 2; ELit 67584; ELit 459832; EVar 57; EVar 58; EVar 59; EVar 40; EVar 10; EVar 10; ELit 77618; EVar 62; EVar 63; EVar 64; EVar 65; EVar 66; EVar 67; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 68; EVar 69; EVar 70; EVar 71] [] [KZero {| a_base := EVar 10; a_off := -128 |} (ELit 144); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -112 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -112 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := 16 |} (ELit 0); KDisj {| a_base := EVar 2; a_off := -112 |} (ELit 112) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := -40 |} 8 (ELit 257240); KWord {| a_base := EVar 2; a_off := -48 |} 8 (ELit 144); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 140116); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 304))] 72))).
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
Definition ps0 : SR.post_spec := SR.PS 140132 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_101909.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 259044 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_101909.IT SegItab_S_101909.IT_sound BF NX0 BR XSTEP F0 PSS plan 259044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e2a2.

Module LibSegZ_e2c1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_101909.ITR.
Definition IT : itab := SegItab_S_101909.IT.
Definition ENDS : list Z := [309572].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; ELit 77618; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-128)) (ELit 128);
   KUnk (SA (EVar 2) (-128)) (ELit 128);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (-128)) (ELit 128) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760].
Definition ss0 : sym_state := SS 140132 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-128), ELit 128); (EVar 10, (0), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-128), 128); (EVar 10, (0), 8)].
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309572])], (93, SS 364652 [ELit 0; ELit 263600; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 10; ELit 77618; ELit 77618; ELit 77618; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 10; a_off := 0 |} 8 (ELit 385144); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 140136); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -128 |} (ELit 128); KUnk {| a_base := EVar 2; a_off := -128 |} (ELit 88); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 128); KUnk {| a_base := EVar 10; a_off := 8 |} (ELit 8); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760] 56))).
Definition s1 : sym_state := snd (snd ex1).

(* [comment removed for export] *)
Definition s2 : sym_state :=
  (SS 263600 [ELit 0; ELit 263600; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 10; ELit 77618; ELit 12; EVar 56; EVar 57; EVar 58; EVar 59; EVar 60; EVar 61; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 10; a_off := 0 |} 8 (ELit 385144); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 140136); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -128 |} (ELit 128); KUnk {| a_base := EVar 2; a_off := -128 |} (ELit 88); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 128); KUnk {| a_base := EVar 10; a_off := 8 |} (ELit 8); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760] 62).

(* [comment removed for export] *)
Definition ex3 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 309572])], (93, SS 309572 [ELit 0; ELit 368844; EAlu Instr.ALU_ADD (EVar 2) (ELit (-64)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; ELit 37; ELit 77618; ELit 37; EVar 56; EVar 57; EVar 58; EVar 59; EVar 60; EVar 61; EVar 17; ELit 12; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -56 |} 8 (ELit 263612); KWord {| a_base := EVar 10; a_off := 0 |} 8 (ELit 385144); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 140136); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -128 |} (ELit 128); KUnk {| a_base := EVar 2; a_off := -128 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -48 |} (ELit 8); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 128); KUnk {| a_base := EVar 10; a_off := 8 |} (ELit 8); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760] 62))).
Definition s3 : sym_state := snd (snd ex3).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PStep (SR.SStrlen (12)) (SGA.mkplan (fst ex3) (SGP.PEnd 0))).
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
Definition ps0 : SR.post_spec := SR.PS 309572 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_101909.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140132 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_101909.IT SegItab_S_101909.IT_sound BF NX0 BR XSTEP F0 PSS plan 140132 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e2c1.

Module LibSegZ_e2c2.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_101909.ITR.
Definition IT : itab := SegItab_S_101909.IT.
Definition ENDS : list Z := [140156].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-64)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; ELit 77618; EVar 37; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; ELit 12; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-128)) (ELit 64);
   KUnk (SA (EVar 2) (-128)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KRange (EVar 37) 4096 140737488355328;
   KAlign (EVar 37) 16;
   KWr (SA (EVar 37) 0) (ELit 37);
   KUnk (SA (EVar 37) 0) (ELit 37);
   KDisj (SA (EVar 2) (-128)) (ELit 128) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (EVar 37) 0) (ELit 37);
   KDisj (SA (EVar 2) (-128)) (ELit 128) (SA (EVar 37) 0) (ELit 37);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KDisj (SA (EVar 37) 0) (ELit 37) (SA (ELit 0) 65536) (ELit 528384);
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (-56)) 8 (ELit 263612);
   KWord (SA (EVar 2) (-64)) 8 (EVar 10);
   KWord (SA (EVar 2) (-8)) 8 (ELit 140136);
   KWord (SA (EVar 2) (-16)) 8 (EVar 40);
   KWord (SA (EVar 2) (-24)) 8 (EVar 10);
   KWord (SA (EVar 2) (-32)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (416)));
   KWord (SA (EVar 2) (-40)) 8 (ELit 0)].
Definition ss0 : sym_state := SS 368844 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-128), ELit 64); (EVar 10, (8), ELit 8); (EVar 37, (0), ELit 37)].
Definition F0L : list SR.region := [(EVar 2, (-128), 64); (EVar 10, (8), 8); (EVar 37, (0), 37)].
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 140156]); SGA.AStep SR.SCopy; SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 140156])], (93, SS 140156 [ELit 0; ELit 140136; EVar 2; ELit 67584; ELit 459832; EVar 57; EVar 58; EVar 59; EVar 40; EVar 10; EVar 10; ELit 385384; ELit 253816; EVar 63; EVar 64; EVar 65; EVar 66; EVar 67; EAlu Instr.ALU_ADD (EVar 2) (ELit 416); ELit 0; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 68; EVar 69; EVar 70; EVar 71] [] [KWord {| a_base := EVar 10; a_off := 8 |} 8 (EAlu Instr.ALU_ADD (EVar 37) (ELit 24)); KWord {| a_base := EVar 37; a_off := 24 |} 8 (ELit 8532461059501614426); KWord {| a_base := EVar 37; a_off := 32 |} 1 (ELit 105); KWord {| a_base := EVar 37; a_off := 33 |} 1 (ELit 100); KWord {| a_base := EVar 37; a_off := 34 |} 1 (ELit 101); KWord {| a_base := EVar 37; a_off := 35 |} 1 (ELit 46); KWord {| a_base := EVar 37; a_off := 36 |} 1 (ELit 0); KWord {| a_base := EVar 37; a_off := 16 |} 4 (ELit 0); KWord {| a_base := EVar 37; a_off := 8 |} 8 (ELit 12); KWord {| a_base := EVar 37; a_off := 0 |} 8 (ELit 12); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -128 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -128 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 136); KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 16; KWr {| a_base := EVar 37; a_off := 0 |} (ELit 37); KUnk {| a_base := EVar 37; a_off := 20 |} (ELit 4); KUnk {| a_base := EVar 37; a_off := 37 |} (ELit 0); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := EVar 37; a_off := 0 |} (ELit 37); KDisj {| a_base := EVar 2; a_off := -128 |} (ELit 128) {| a_base := EVar 37; a_off := 0 |} (ELit 37); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KDisj {| a_base := EVar 37; a_off := 0 |} (ELit 37) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := -56 |} 8 (ELit 263612); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 140136); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 416)); KWord {| a_base := EVar 2; a_off := -40 |} 8 (ELit 0)] 72))).
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
Definition ps0 : SR.post_spec := SR.PS 140156 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_S_101909.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 368844 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_101909.IT SegItab_S_101909.IT_sound BF NX0 BR XSTEP F0 PSS plan 368844 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e2c2.

Module LibSegZ_e2p1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_101909.ITR.
Definition IT : itab := SegItab_S_101909.IT.
Definition ENDS : list Z := [140392].
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
   KDisj (SA (EVar 2) (-64)) (ELit 240) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KRange (EVar 40) 0 255;
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (168)) 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254))].
Definition ss0 : sym_state := SS 140224 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 140392])], (93, SS 140392 [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -64 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -64 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := -64 |} (ELit 240) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KRange (EVar 40) 0 255; KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := 168 |} 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254))] 56))).
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

Lemma cert : SGP.cert_ok RSEGS SegItab_S_101909.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140224 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_101909.IT SegItab_S_101909.IT_sound BF NX0 BR XSTEP F0 PSS plan 140224 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e2p1.

Module LibSegZ_e2p2.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_S_101909.ITR.
Definition IT : itab := SegItab_S_101909.IT.
Definition ENDS : list Z := [138620].
Definition STOPS1 : list Z := [364196; 362788; 364652; 309572; 309252; 309576] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (304)); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (240)) (ELit 64);
   KUnk (SA (EVar 2) (240)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 144);
   KUnk (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 2) (240)) (ELit 80) (SA (EVar 10) (-128)) (ELit 144);
   KDisj (SA (EVar 10) (-128)) (ELit 144) (SA (ELit 0) 65536) (ELit 528384);
   KRange (EVar 40) 0 255;
   KImg 65536 390664;
   KImg 390704 390736;
   KImg 390752 390760;
   KWord (SA (EVar 2) (304)) 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254))].
Definition ss0 : sym_state := SS 138580 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (240), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (240), 64)].
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
  (([SGA.AStep (SR.SBlock [364196; 362788; 364652; 309572; 309252; 309576; 138620])], (93, SS 138620 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit 304); ELit 67584; ELit 459832; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-32)); ELit 0; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := 240 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := 240 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 144); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 2; a_off := 240 |} (ELit 80) {| a_base := EVar 10; a_off := -128 |} (ELit 144); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 144) {| a_base := ELit 0; a_off := 65536 |} (ELit 528384); KRange (EVar 40) 0 255; KImg 65536 390664; KImg 390704 390736; KImg 390752 390760; KWord {| a_base := EVar 2; a_off := 304 |} 1 (EAlu Instr.ALU_AND (EVar 40) (ELit 254))] 56))).
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

Lemma cert : SGP.cert_ok RSEGS SegItab_S_101909.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 138580 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound_it SegItab_S_101909.IT SegItab_S_101909.IT_sound BF NX0 BR XSTEP F0 PSS plan 138580 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e2p2.
