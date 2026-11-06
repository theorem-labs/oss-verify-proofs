(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Src0PlanKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LibSegZ_d6e2.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141384].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 21; EVar 22; EVar 37; EVar 24; EVar 25; EVar 26; EVar 36; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-136)) 1 (EVar 41);
   KWord (SA (EVar 2) (-128)) 8 (EVar 42);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0;
   KRange (EVar 42) 1 300;
   KRange (EVar 33) 1048576 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 0) 1 (EVar 38);
   KRange (EVar 38) 0 255].
Definition ss0 : sym_state := SS 138708 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 141384])], (93, SS 141384 [ELit 0; ELit 138760; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 41; EVar 35; EAlu Instr.ALU_ADD (EVar 2) (ELit (-168)); EVar 33; EAlu Instr.ALU_ADD (EVar 2) (ELit (-200)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 42; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EVar 38; EVar 37; EVar 24; EVar 25; EVar 26; EVar 36; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -136 |} 1 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0; KRange (EVar 42) 1 300; KRange (EVar 33) 1048576 140737488355296; KAlign (EVar 33) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 33; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 33; a_off := 0 |} 1 (EVar 38); KRange (EVar 38) 0 255] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141384 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 138708 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 138708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6e2.

Module LibSegZ_d6e2d.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141384].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 21; EVar 22; EVar 37; EVar 24; EVar 25; EVar 26; EVar 36; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-136)) 1 (EVar 41);
   KWord (SA (EVar 2) (-128)) 8 (EVar 42);
   KWord (SA (EVar 2) (-112)) 8 (EVar 43);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1;
   KRange (EVar 42) 1 300;
   KRange (EVar 43) 0 18446744073709551615;
   KRange (EVar 33) 1048576 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 0) 1 (EVar 38);
   KRange (EVar 38) 0 255].
Definition ss0 : sym_state := SS 138708 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 141384])], (93, SS 141384 [ELit 0; ELit 138760; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 41; EVar 35; EAlu Instr.ALU_ADD (EVar 2) (ELit (-168)); EVar 33; EAlu Instr.ALU_ADD (EVar 2) (ELit (-200)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 42; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EVar 43; EVar 38; EVar 37; EVar 24; EVar 25; EVar 26; EVar 36; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -136 |} 1 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 43); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1; KRange (EVar 42) 1 300; KRange (EVar 43) 0 18446744073709551615; KRange (EVar 33) 1048576 140737488355296; KAlign (EVar 33) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 33; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 33; a_off := 0 |} 1 (EVar 38); KRange (EVar 38) 0 255] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141384 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 138708 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 138708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6e2d.

Module LibSegZ_d6e2z.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [140112].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 21; EVar 22; EVar 37; EVar 24; EVar 25; EVar 26; EVar 36; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-136)) 1 (EVar 41);
   KWord (SA (EVar 2) (-128)) 8 (ELit 0);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0].
Definition ss0 : sym_state := SS 138708 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 140112])], (93, SS 140112 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 41; EVar 35; ELit 16; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; ELit 0; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EVar 22; EVar 37; EVar 24; EVar 25; EVar 26; EVar 36; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -136 |} 1 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 0); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 140112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 138708 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 138708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6e2z.

Module LibSegZ_d6e4e.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [138836].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 18446744073709551615; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16].
Definition ss0 : sym_state := SS 138812 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 138836])], (93, SS 138836 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 18446744073709551615; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 138836 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 138812 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 138812 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6e4e.

Module LibSegZ_d6e4g1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139420].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 47; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; ELit 1; EVar 20; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); EVar 22; EVar 37; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-168)) 1 (EVar 44);
   KWord (SA (EVar 2) (-160)) 8 (ELit 2);
   KWord (SA (EVar 2) (-120)) 8 (EVar 63);
   KRange (EVar 47) 0 1;
   KRange (EVar 44) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 44) (ELit 1)) 0 0;
   KRange (EVar 63) 4294967296 18446744073709551615;
   KRange (EAlu Instr.ALU_SRL (EVar 63) (ELit 32)) 1 4294967295;
   KRange (EVar 37) 0 1;
   KRange (EVar 33) 1048576 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 0) 1 (EVar 38);
   KRange (EVar 38) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 38) (ELit 1)) 0 0;
   KRange (EVar 35) 1048576 140737488355296].
Definition ss0 : sym_state := SS 138812 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-256), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-256), 8)].
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139420])], (93, SS 139420 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EAlu Instr.ALU_SRL (EVar 63) (ELit 32); ELit 2; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 63; EVar 20; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-152)); EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EAlu Instr.ALU_ADD (EVar 35) (ELit 16); EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -256 |} 8 (EVar 37); KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -168 |} 1 (EVar 44); KWord {| a_base := EVar 2; a_off := -160 |} 8 (ELit 2); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 63); KRange (EVar 47) 0 1; KRange (EVar 44) 0 255; KRange (EAlu Instr.ALU_AND (EVar 44) (ELit 1)) 0 0; KRange (EVar 63) 4294967296 18446744073709551615; KRange (EAlu Instr.ALU_SRL (EVar 63) (ELit 32)) 1 4294967295; KRange (EVar 37) 0 1; KRange (EVar 33) 1048576 140737488355296; KAlign (EVar 33) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 33; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 33; a_off := 0 |} 1 (EVar 38); KRange (EVar 38) 0 255; KRange (EAlu Instr.ALU_AND (EVar 38) (ELit 1)) 0 0; KRange (EVar 35) 1048576 140737488355296] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139420 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 138812 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 138812 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6e4g1.

Module LibSegZ_d6e4g2.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139420].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 47; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; ELit 2; EVar 20; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); EVar 22; EVar 37; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-168)) 1 (EVar 44);
   KRange (EVar 47) 0 1;
   KRange (EVar 44) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 44) (ELit 1)) 0 0;
   KRange (EVar 37) 0 1;
   KRange (EVar 33) 1048576 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 0) 1 (EVar 38);
   KRange (EVar 38) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 38) (ELit 1)) 0 0;
   KRange (EVar 35) 1048576 140737488355296].
Definition ss0 : sym_state := SS 138812 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-256), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-256), 8)].
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139420])], (93, SS 139420 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; ELit 1; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; ELit 2; EVar 20; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-152)); EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EAlu Instr.ALU_ADD (EVar 35) (ELit 16); EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -256 |} 8 (EVar 37); KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -168 |} 1 (EVar 44); KRange (EVar 47) 0 1; KRange (EVar 44) 0 255; KRange (EAlu Instr.ALU_AND (EVar 44) (ELit 1)) 0 0; KRange (EVar 37) 0 1; KRange (EVar 33) 1048576 140737488355296; KAlign (EVar 33) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 33; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 33; a_off := 0 |} 1 (EVar 38); KRange (EVar 38) 0 255; KRange (EAlu Instr.ALU_AND (EVar 38) (ELit 1)) 0 0; KRange (EVar 35) 1048576 140737488355296] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139420 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 138812 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 138812 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6e4g2.

Module LibSegZ_d6e4h.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139164; 139420].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 47; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; ELit 1; EVar 20; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); EVar 22; EVar 37; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-168)) 1 (EVar 44);
   KWord (SA (EVar 2) (-160)) 8 (ELit 2);
   KWord (SA (EVar 2) (-120)) 8 (EVar 63);
   KRange (EVar 47) 0 1;
   KRange (EVar 44) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 44) (ELit 1)) 0 0;
   KRange (EVar 63) 1 4294967295;
   KRange (EAlu Instr.ALU_SRL (EVar 63) (ELit 32)) 0 0;
   KRange (EVar 37) 0 1;
   KRange (EVar 33) 1048576 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 0) 1 (EVar 38);
   KRange (EVar 38) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 38) (ELit 1)) 0 0;
   KRange (EVar 35) 1048576 140737488355296].
Definition ss0 : sym_state := SS 138812 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-256), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-256), 8)].
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139164; 139420])], (93, SS 139164 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; ELit 0; ELit 2; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 63; EVar 20; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-152)); EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EAlu Instr.ALU_ADD (EVar 35) (ELit 16); EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -256 |} 8 (EVar 37); KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -168 |} 1 (EVar 44); KWord {| a_base := EVar 2; a_off := -160 |} 8 (ELit 2); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 63); KRange (EVar 47) 0 1; KRange (EVar 44) 0 255; KRange (EAlu Instr.ALU_AND (EVar 44) (ELit 1)) 0 0; KRange (EVar 63) 1 4294967295; KRange (EAlu Instr.ALU_SRL (EVar 63) (ELit 32)) 0 0; KRange (EVar 37) 0 1; KRange (EVar 33) 1048576 140737488355296; KAlign (EVar 33) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 33; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 33; a_off := 0 |} 1 (EVar 38); KRange (EVar 38) 0 255; KRange (EAlu Instr.ALU_AND (EVar 38) (ELit 1)) 0 0; KRange (EVar 35) 1048576 140737488355296] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139164 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 138812 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 138812 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6e4h.

Module LibSegZ_d6g10dd.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139732].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 20; EVar 21; EVar 22; EVar 72; EVar 71; EVar 25; EVar 26; EVar 79; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-264)) 8 (EVar 68);
   KRange (EVar 68) 0 18446744073709551615;
   KRange (EVar 71) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1;
   KRange (EVar 35) 1048576 140737488355296;
   KAlign (EVar 35) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 35) 0) (ELit 32);
   KWord (SA (EVar 35) 0) 1 (EVar 69);
   KRange (EVar 69) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 1 1;
   KWord (SA (EVar 35) 24) 8 (EVar 78);
   KRange (EVar 78) 0 18446744073709551615;
   KRange (EVar 79) 4096 140737488355328;
   KAlign (EVar 79) 8;
   KWord (SA (EVar 79) 0) 8 (EVar 74);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 72) 0 18446744073709551615].
Definition ss0 : sym_state := SS 139688 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139732])], (93, SS 139732 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 72; EVar 35; EVar 72; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 20; EVar 21; EVar 22; EVar 74; EVar 78; EVar 25; EVar 65; EVar 79; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 68); KRange (EVar 68) 0 18446744073709551615; KRange (EVar 71) 0 255; KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1; KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 35; a_off := 0 |} 1 (EVar 69); KRange (EVar 69) 0 255; KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 1 1; KWord {| a_base := EVar 35; a_off := 24 |} 8 (EVar 78); KRange (EVar 78) 0 18446744073709551615; KRange (EVar 79) 4096 140737488355328; KAlign (EVar 79) 8; KWord {| a_base := EVar 79; a_off := 0 |} 8 (EVar 74); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 72) 0 18446744073709551615] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139688 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139688 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6g10dd.

Module LibSegZ_d6g10di.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139732].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 20; EVar 21; EVar 22; EVar 72; EVar 71; EVar 25; EVar 26; EVar 79; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-264)) 8 (EVar 68);
   KRange (EVar 68) 0 18446744073709551615;
   KRange (EVar 71) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1;
   KRange (EVar 35) 1048576 140737488355296;
   KAlign (EVar 35) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 35) 0) (ELit 32);
   KWord (SA (EVar 35) 0) 1 (EVar 69);
   KRange (EVar 69) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 0 0;
   KRange (EVar 79) 4096 140737488355328;
   KAlign (EVar 79) 8;
   KWord (SA (EVar 79) 0) 8 (EVar 74);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 72) 0 18446744073709551615].
Definition ss0 : sym_state := SS 139688 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139732])], (93, SS 139732 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 72; EVar 35; EVar 72; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 20; EVar 21; EVar 22; EVar 74; EVar 68; EVar 25; EVar 65; EVar 79; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 68); KRange (EVar 68) 0 18446744073709551615; KRange (EVar 71) 0 255; KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1; KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 35; a_off := 0 |} 1 (EVar 69); KRange (EVar 69) 0 255; KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 0 0; KRange (EVar 79) 4096 140737488355328; KAlign (EVar 79) 8; KWord {| a_base := EVar 79; a_off := 0 |} 8 (EVar 74); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 72) 0 18446744073709551615] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139688 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139688 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6g10di.

Module LibSegZ_d6g10id.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139732].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (EAlu Instr.ALU_ADD (EVar 36) (ELit (16))); EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 20; EVar 21; EVar 22; EVar 72; EVar 71; EVar 25; EVar 26; EVar 79; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-264)) 8 (EVar 68);
   KRange (EVar 68) 0 18446744073709551615;
   KRange (EVar 71) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0;
   KRange (EVar 35) 1048576 140737488355296;
   KAlign (EVar 35) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 35) 0) (ELit 32);
   KWord (SA (EVar 35) 0) 1 (EVar 69);
   KRange (EVar 69) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 1 1;
   KWord (SA (EVar 35) 24) 8 (EVar 78);
   KRange (EVar 78) 0 18446744073709551615;
   KRange (EVar 79) 4096 140737488355328;
   KAlign (EVar 79) 8;
   KWord (SA (EVar 79) 0) 8 (EVar 74);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 72) 0 18446744073709551615].
Definition ss0 : sym_state := SS 139688 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139732])], (93, SS 139732 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 36) (ELit 16); EVar 35; EAlu Instr.ALU_ADD (EVar 36) (ELit 16); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 20; EVar 21; EVar 22; EVar 74; EVar 78; EVar 25; EVar 65; EVar 79; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 68); KRange (EVar 68) 0 18446744073709551615; KRange (EVar 71) 0 255; KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0; KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 35; a_off := 0 |} 1 (EVar 69); KRange (EVar 69) 0 255; KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 1 1; KWord {| a_base := EVar 35; a_off := 24 |} 8 (EVar 78); KRange (EVar 78) 0 18446744073709551615; KRange (EVar 79) 4096 140737488355328; KAlign (EVar 79) 8; KWord {| a_base := EVar 79; a_off := 0 |} 8 (EVar 74); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 72) 0 18446744073709551615] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139688 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139688 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6g10id.

Module LibSegZ_d6g10ii.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139732].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (EAlu Instr.ALU_ADD (EVar 36) (ELit (16))); EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 20; EVar 21; EVar 22; EVar 72; EVar 71; EVar 25; EVar 26; EVar 79; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-264)) 8 (EVar 68);
   KRange (EVar 68) 0 18446744073709551615;
   KRange (EVar 71) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0;
   KRange (EVar 35) 1048576 140737488355296;
   KAlign (EVar 35) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 35) 0) (ELit 32);
   KWord (SA (EVar 35) 0) 1 (EVar 69);
   KRange (EVar 69) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 0 0;
   KRange (EVar 79) 4096 140737488355328;
   KAlign (EVar 79) 8;
   KWord (SA (EVar 79) 0) 8 (EVar 74);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 72) 0 18446744073709551615].
Definition ss0 : sym_state := SS 139688 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139732])], (93, SS 139732 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 36) (ELit 16); EVar 35; EAlu Instr.ALU_ADD (EVar 36) (ELit 16); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 20; EVar 21; EVar 22; EVar 74; EVar 68; EVar 25; EVar 65; EVar 79; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 68); KRange (EVar 68) 0 18446744073709551615; KRange (EVar 71) 0 255; KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0; KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 35; a_off := 0 |} 1 (EVar 69); KRange (EVar 69) 0 255; KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 0 0; KRange (EVar 79) 4096 140737488355328; KAlign (EVar 79) 8; KWord {| a_base := EVar 79; a_off := 0 |} 8 (EVar 74); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 72) 0 18446744073709551615] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139688 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139688 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6g10ii.

Module LibSegZ_d6g4d.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [135356].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 64; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 68; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-136)) 1 (EVar 41);
   KWord (SA (EVar 2) (-128)) 8 (EVar 67);
   KWord (SA (EVar 2) (-112)) 8 (EVar 66);
   KWord (SA (EVar 2) (-160)) 8 (EVar 65);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1;
   KRange (EVar 67) 1 3;
   KRange (EVar 65) 1 300;
   KRange (EVar 64) 0 1;
   KRange (EVar 66) 0 18446744073709551615].
Definition ss0 : sym_state := SS 139476 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-296), ELit 8); (EVar 2, (-264), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-296), 8); (EVar 2, (-264), 8)].
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 135356])], (93, SS 135356 [ELit 0; ELit 139520; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 35; EAlu Instr.ALU_ADD (EVar 65) (EMd Instr.M_MUL (ELit (-1)) (EVar 67)); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 66; EVar 67; EVar 22; EVar 23; EVar 68; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 68); KWord {| a_base := EVar 2; a_off := -296 |} 8 (EVar 64); KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -136 |} 1 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 65); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1; KRange (EVar 67) 1 3; KRange (EVar 65) 1 300; KRange (EVar 64) 0 1; KRange (EVar 66) 0 18446744073709551615] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 135356 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139476 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139476 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6g4d.

Module LibSegZ_d6g4i.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [135356].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 64; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 68; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-136)) 1 (EVar 41);
   KWord (SA (EVar 2) (-128)) 8 (EVar 67);
   KWord (SA (EVar 2) (-160)) 8 (EVar 65);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0;
   KRange (EVar 67) 1 3;
   KRange (EVar 65) 1 300;
   KRange (EVar 64) 0 1].
Definition ss0 : sym_state := SS 139476 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-296), ELit 8); (EVar 2, (-264), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-296), 8); (EVar 2, (-264), 8)].
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 135356])], (93, SS 135356 [ELit 0; ELit 139520; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 35; EAlu Instr.ALU_ADD (EVar 65) (EMd Instr.M_MUL (ELit (-1)) (EVar 67)); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 20; EVar 67; EVar 22; EVar 23; EVar 68; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 68); KWord {| a_base := EVar 2; a_off := -296 |} 8 (EVar 64); KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -136 |} 1 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 65); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0; KRange (EVar 67) 1 3; KRange (EVar 65) 1 300; KRange (EVar 64) 0 1] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 135356 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139476 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139476 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6g4i.

Module LibSegZ_d6g5i.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [364196; 139564].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-264)) 8 (EVar 68);
   KRange (EVar 35) 1048576 140737488355296;
   KAlign (EVar 35) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 35) 0) (ELit 32);
   KWord (SA (EVar 35) 0) 1 (EVar 69);
   KRange (EVar 69) 0 255;
   KWord (SA (EVar 35) 8) 8 (EVar 70);
   KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 0 0;
   KRange (EVar 70) 0 300;
   KRange (EVar 68) 0 18446744073709551615].
Definition ss0 : sym_state := SS 139520 regs0 [] kn0 NX0.
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
Definition s1 : sym_state :=
  (SS 139544 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; ELit 0; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 68; EVar 70; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 68); KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 35; a_off := 0 |} 1 (EVar 69); KRange (EVar 69) 0 255; KWord {| a_base := EVar 35; a_off := 8 |} 8 (EVar 70); KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 0 0; KRange (EVar 70) 0 300; KRange (EVar 68) 0 18446744073709551615] 80).

(* [comment removed for export] *)
Definition ce2 : expr := EVar 70.
Definition arms2 := Eval vm_compute in (SGP.case_arms s1 ce2 (0)).
Definition lo2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition hi2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

(* [comment removed for export] *)
Definition ex3 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 364196; 139564])], (93, SS 139564 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; ELit 0; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 68; EVar 70; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 70) 0 0; KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 68); KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 35; a_off := 0 |} 1 (EVar 69); KRange (EVar 69) 0 255; KWord {| a_base := EVar 35; a_off := 8 |} 8 (EVar 70); KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 0 0; KRange (EVar 70) 0 300; KRange (EVar 68) 0 18446744073709551615] 80))).
Definition s3 : sym_state := snd (snd ex3).

(* [comment removed for export] *)
Definition ex4 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 364196; 139564])], (93, SS 364196 [ELit 0; ELit 139564; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 68; ELit 0; EMd Instr.M_MUL (ELit 8) (EVar 70); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 68; EVar 70; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 70) 1 300; KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 68); KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 35; a_off := 0 |} 1 (EVar 69); KRange (EVar 69) 0 255; KWord {| a_base := EVar 35; a_off := 8 |} 8 (EVar 70); KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 0 0; KRange (EVar 70) 0 300; KRange (EVar 68) 0 18446744073709551615] 80))).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PCase ce2 (0) (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PEnd 0))).
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
Definition ps0 : SR.post_spec := SR.PS 364196 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 139564 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139520 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139520 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6g5i.

Module LibSegZ_d6g7d0.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139732; 139648].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 61; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 66; EVar 67; EVar 22; EVar 23; EVar 24; EVar 25; EVar 62; EVar 36; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KRange (EVar 66) 4096 140737488355328;
   KAlign (EVar 66) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 66) 0) (ELit 64);
   KRange (EVar 67) 2 3;
   KWord (SA (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (-8)) 8 (EVar 74);
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (-8)) (ELit 8);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 36) 1048576 140737488355296;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 36) 0) (ELit 32);
   KWord (SA (EVar 36) 0) 1 (EVar 71);
   KRange (EVar 71) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1;
   KWord (SA (EVar 36) 24) 8 (EVar 72);
   KRange (EVar 72) 4096 140737488355328;
   KAlign (EVar 72) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 72) 0) (ELit 64);
   KWord (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72)) (-8)) 8 (EVar 73);
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72)) (-8)) (ELit 8);
   KRange (EVar 73) 0 18446744073709551615;
   KRange (EVar 65) 1 7;
   KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 1 1;
   KRange (EVar 61) 0 1;
   KRange (EVar 62) 0 2].
Definition ss0 : sym_state := SS 139576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-288), ELit 24)].
Definition F0L : list SR.region := [(EVar 2, (-288), 24)].
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139732; 139648])], (93, SS 139732 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 36) (ELit 16); EVar 9; EVar 72; EVar 73; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 66; EVar 67; EAlu Instr.ALU_ADD (EVar 67) (ELit (-1)); EVar 74; EVar 24; EVar 25; EAlu Instr.ALU_ADD (EVar 65) (ELit (-1)); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (ELit (-8)); EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -272 |} 8 (EVar 36); KWord {| a_base := EVar 2; a_off := -280 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -288 |} 8 (EVar 61); KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KRange (EVar 66) 4096 140737488355328; KAlign (EVar 66) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 66; a_off := 0 |} (ELit 64); KRange (EVar 67) 2 3; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67)); a_off := -8 |} 8 (EVar 74); KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67)); a_off := -8 |} (ELit 8); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 36) 1048576 140737488355296; KAlign (EVar 36) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 36; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 36; a_off := 0 |} 1 (EVar 71); KRange (EVar 71) 0 255; KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1; KWord {| a_base := EVar 36; a_off := 24 |} 8 (EVar 72); KRange (EVar 72) 4096 140737488355328; KAlign (EVar 72) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 72; a_off := 0 |} (ELit 64); KWord {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72); a_off := -8 |} 8 (EVar 73); KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72); a_off := -8 |} (ELit 8); KRange (EVar 73) 0 18446744073709551615; KRange (EVar 65) 1 7; KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 1 1; KRange (EVar 61) 0 1; KRange (EVar 62) 0 2] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139576 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6g7d0.

Module LibSegZ_d6g7d1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139732; 139648].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 61; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 66; EVar 67; EVar 22; EVar 23; EVar 24; EVar 25; EVar 62; EVar 36; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KRange (EVar 66) 4096 140737488355328;
   KAlign (EVar 66) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 66) 0) (ELit 64);
   KRange (EVar 67) 2 3;
   KWord (SA (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (-8)) 8 (EVar 74);
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (-8)) (ELit 8);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 36) 1048576 140737488355296;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 36) 0) (ELit 32);
   KWord (SA (EVar 36) 0) 1 (EVar 71);
   KRange (EVar 71) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1;
   KWord (SA (EVar 36) 24) 8 (EVar 72);
   KRange (EVar 72) 4096 140737488355328;
   KAlign (EVar 72) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 72) 0) (ELit 64);
   KWord (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72)) (-8)) 8 (EVar 73);
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72)) (-8)) (ELit 8);
   KRange (EVar 73) 0 18446744073709551615;
   KRange (EVar 65) 1 7;
   KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 0 0;
   KRange (EVar 61) 0 1;
   KRange (EVar 62) 0 2].
Definition ss0 : sym_state := SS 139576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-288), ELit 24)].
Definition F0L : list SR.region := [(EVar 2, (-288), 24)].
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139732; 139648])], (93, SS 139648 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 36) (ELit 16); EVar 9; EVar 72; EVar 73; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 66; EVar 67; EAlu Instr.ALU_ADD (EVar 67) (ELit (-1)); EVar 74; EVar 24; EVar 25; EAlu Instr.ALU_ADD (EVar 65) (ELit (-1)); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (ELit (-8)); EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -272 |} 8 (EVar 36); KWord {| a_base := EVar 2; a_off := -280 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -288 |} 8 (EVar 61); KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KRange (EVar 66) 4096 140737488355328; KAlign (EVar 66) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 66; a_off := 0 |} (ELit 64); KRange (EVar 67) 2 3; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67)); a_off := -8 |} 8 (EVar 74); KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67)); a_off := -8 |} (ELit 8); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 36) 1048576 140737488355296; KAlign (EVar 36) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 36; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 36; a_off := 0 |} 1 (EVar 71); KRange (EVar 71) 0 255; KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1; KWord {| a_base := EVar 36; a_off := 24 |} 8 (EVar 72); KRange (EVar 72) 4096 140737488355328; KAlign (EVar 72) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 72; a_off := 0 |} (ELit 64); KWord {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72); a_off := -8 |} 8 (EVar 73); KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72); a_off := -8 |} (ELit 8); KRange (EVar 73) 0 18446744073709551615; KRange (EVar 65) 1 7; KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 0 0; KRange (EVar 61) 0 1; KRange (EVar 62) 0 2] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139648 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139576 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6g7d1.

Module LibSegZ_d6g7i0.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139732; 139648].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 61; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 66; EVar 67; EVar 22; EVar 23; EVar 24; EVar 25; EVar 62; EVar 36; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KRange (EVar 66) 4096 140737488355328;
   KAlign (EVar 66) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 66) 0) (ELit 64);
   KRange (EVar 67) 2 3;
   KWord (SA (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (-8)) 8 (EVar 74);
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (-8)) (ELit 8);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 36) 1048576 140737488355296;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 36) 0) (ELit 32);
   KWord (SA (EVar 36) 0) 1 (EVar 71);
   KRange (EVar 71) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0;
   KWord (SA (EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65))) 8) 8 (EVar 73);
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65))) 8) (ELit 8);
   KRange (EVar 73) 0 18446744073709551615;
   KRange (EVar 65) 1 2;
   KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 1 1;
   KRange (EVar 61) 0 1;
   KRange (EVar 62) 0 2].
Definition ss0 : sym_state := SS 139576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-288), ELit 24)].
Definition F0L : list SR.region := [(EVar 2, (-288), 24)].
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139732; 139648])], (93, SS 139732 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 36) (ELit 16); EVar 9; EAlu Instr.ALU_ADD (EVar 36) (ELit 16); EVar 73; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 66; EVar 67; EAlu Instr.ALU_ADD (EVar 67) (ELit (-1)); EVar 74; EVar 24; EVar 25; EAlu Instr.ALU_ADD (EVar 65) (ELit (-1)); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (ELit (-8)); EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -272 |} 8 (EVar 36); KWord {| a_base := EVar 2; a_off := -280 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -288 |} 8 (EVar 61); KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KRange (EVar 66) 4096 140737488355328; KAlign (EVar 66) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 66; a_off := 0 |} (ELit 64); KRange (EVar 67) 2 3; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67)); a_off := -8 |} 8 (EVar 74); KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67)); a_off := -8 |} (ELit 8); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 36) 1048576 140737488355296; KAlign (EVar 36) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 36; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 36; a_off := 0 |} 1 (EVar 71); KRange (EVar 71) 0 255; KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65)); a_off := 8 |} 8 (EVar 73); KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65)); a_off := 8 |} (ELit 8); KRange (EVar 73) 0 18446744073709551615; KRange (EVar 65) 1 2; KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 1 1; KRange (EVar 61) 0 1; KRange (EVar 62) 0 2] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139576 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6g7i0.

Module LibSegZ_d6g7i1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139732; 139648].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 61; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 66; EVar 67; EVar 22; EVar 23; EVar 24; EVar 25; EVar 62; EVar 36; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KRange (EVar 66) 4096 140737488355328;
   KAlign (EVar 66) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 66) 0) (ELit 64);
   KRange (EVar 67) 2 3;
   KWord (SA (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (-8)) 8 (EVar 74);
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (-8)) (ELit 8);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 36) 1048576 140737488355296;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 36) 0) (ELit 32);
   KWord (SA (EVar 36) 0) 1 (EVar 71);
   KRange (EVar 71) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0;
   KWord (SA (EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65))) 8) 8 (EVar 73);
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65))) 8) (ELit 8);
   KRange (EVar 73) 0 18446744073709551615;
   KRange (EVar 65) 1 2;
   KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 0 0;
   KRange (EVar 61) 0 1;
   KRange (EVar 62) 0 2].
Definition ss0 : sym_state := SS 139576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-288), ELit 24)].
Definition F0L : list SR.region := [(EVar 2, (-288), 24)].
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139732; 139648])], (93, SS 139648 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EAlu Instr.ALU_ADD (EVar 36) (ELit 16); EVar 9; EAlu Instr.ALU_ADD (EVar 36) (ELit 16); EVar 73; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 65; EVar 66; EVar 67; EAlu Instr.ALU_ADD (EVar 67) (ELit (-1)); EVar 74; EVar 24; EVar 25; EAlu Instr.ALU_ADD (EVar 65) (ELit (-1)); EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67))) (ELit (-8)); EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -272 |} 8 (EVar 36); KWord {| a_base := EVar 2; a_off := -280 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -288 |} 8 (EVar 61); KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KRange (EVar 66) 4096 140737488355328; KAlign (EVar 66) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 66; a_off := 0 |} (ELit 64); KRange (EVar 67) 2 3; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67)); a_off := -8 |} 8 (EVar 74); KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 67)); a_off := -8 |} (ELit 8); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 36) 1048576 140737488355296; KAlign (EVar 36) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 36; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 36; a_off := 0 |} 1 (EVar 71); KRange (EVar 71) 0 255; KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65)); a_off := 8 |} 8 (EVar 73); KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65)); a_off := 8 |} (ELit 8); KRange (EVar 73) 0 18446744073709551615; KRange (EVar 65) 1 2; KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 0 0; KRange (EVar 61) 0 1; KRange (EVar 62) 0 2] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139648 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139576 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6g7i1.

Module LibSegZ_d6x2.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141200; 139920].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-304)) (ELit 304);
   KWord (SA (EVar 2) (-272)) 8 (EVar 36);
   KWord (SA (EVar 2) (-280)) 8 (EVar 62);
   KWord (SA (EVar 2) (-288)) 8 (EVar 61);
   KWord (SA (EVar 2) (-256)) 8 (ELit 1);
   KWord (SA (EVar 2) (-236)) 4 (EVar 77);
   KWord (SA (EVar 2) (-296)) 8 (EVar 64);
   KRange (EVar 35) 1048576 140737488355296;
   KAlign (EVar 35) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 35) 0) (ELit 32);
   KWord (SA (EVar 35) 0) 1 (EVar 69);
   KRange (EVar 69) 0 255;
   KWr (SA (EVar 35) 0) (ELit 32);
   KRange (EVar 61) 0 1;
   KRange (EVar 62) 0 2;
   KRange (EVar 64) 0 1;
   KRange (EVar 77) 0 63;
   KRange (EVar 36) 0 18446744073709551615].
Definition ss0 : sym_state := SS 139844 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 35, (0), ELit 1)].
Definition F0L : list SR.region := [(EVar 35, (0), 1)].
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 141200; 139920])], (93, SS 141200 [ELit 0; ELit 139904; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 35; EVar 33; EVar 36; EVar 77; EVar 64; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 62; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 35; a_off := 0 |} 1 (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 69) (ELit 253)) (EMd Instr.M_MUL (ELit 2) (EVar 61))); KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -304 |} (ELit 304); KWord {| a_base := EVar 2; a_off := -272 |} 8 (EVar 36); KWord {| a_base := EVar 2; a_off := -280 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -288 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -256 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -236 |} 4 (EVar 77); KWord {| a_base := EVar 2; a_off := -296 |} 8 (EVar 64); KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KRange (EVar 69) 0 255; KWr {| a_base := EVar 35; a_off := 0 |} (ELit 32); KRange (EVar 61) 0 1; KRange (EVar 62) 0 2; KRange (EVar 64) 0 1; KRange (EVar 77) 0 63; KRange (EVar 36) 0 18446744073709551615] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141200 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139844 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139844 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6x2.

Module LibSegZ_d6x3.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(138624, 443%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139920].
Definition STOPS1 : list Z := [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-304))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 62; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048880 140737488355328;
   KAlign (EVar 2) 16;
   KRange (EVar 36) 1048576 140737488355296;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-304)) (ELit 304) (SA (EVar 36) 0) (ELit 32);
   KWord (SA (EVar 36) 0) 1 (EVar 71);
   KRange (EVar 71) 0 255;
   KWr (SA (EVar 36) 0) (ELit 32);
   KRange (EVar 62) 0 2].
Definition ss0 : sym_state := SS 139904 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 36, (0), ELit 1)].
Definition F0L : list SR.region := [(EVar 36, (0), 1)].
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
  (([SGA.AStep (SR.SBlock [141384; 137852; 135184; 135356; 257064; 364196; 140396; 140664; 140916; 136656; 141200; 257208; 140104; 139732; 139760; 139920])], (93, SS 139920 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 71) (ELit 253)) (EVar 62); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 62; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 36; a_off := 0 |} 1 (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 71) (ELit 253)) (EVar 62)); KRange (EVar 2) 1048880 140737488355328; KAlign (EVar 2) 16; KRange (EVar 36) 1048576 140737488355296; KAlign (EVar 36) 8; KDisj {| a_base := EVar 2; a_off := -304 |} (ELit 304) {| a_base := EVar 36; a_off := 0 |} (ELit 32); KRange (EVar 71) 0 255; KWr {| a_base := EVar 36; a_off := 0 |} (ELit 32); KRange (EVar 62) 0 2] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 139904 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 139904 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d6x3.
