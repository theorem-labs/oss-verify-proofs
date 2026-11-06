(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ub0PlanKit Ub0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require SegItab_U_6f54b4.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ub0PlanKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LibSegZ_e1a1u.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_U_6f54b4.ITR.
Definition IT : itab := SegItab_U_6f54b4.IT.
Definition ENDS : list Z := [312388].
Definition STOPS1 : list Z := [367008; 365600; 367464; 312384; 312064; 312388] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 462648; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 32; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-112)) (ELit 112);
   KUnk (SA (EVar 2) (-112)) (ELit 112);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 160);
   KUnk (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 2) (-112)) (ELit 112) (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 10) (-128)) (ELit 160) (SA (ELit 0) 65536) (ELit 532480);
   KImg 65536 393472;
   KImg 393512 393544;
   KImg 393560 393568].
Definition ss0 : sym_state := SS 134288 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [367008; 365600; 367464; 312384; 312064; 312388; 312388])], (93, SS 312388 [ELit 0; ELit 261856; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); ELit 67584; ELit 462648; EVar 5; EVar 6; EVar 7; ELit 160; EVar 9; ELit 16; ELit 160; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -48 |} 8 (ELit 160); KWord {| a_base := EVar 2; a_off := -40 |} 8 (ELit 260052); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 134292); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -112 |} (ELit 112); KUnk {| a_base := EVar 2; a_off := -112 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -32 |} (ELit 8); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 2; a_off := -112 |} (ELit 112) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 532480); KImg 65536 393472; KImg 393512 393544; KImg 393560 393568] 56))).
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
Definition ps0 : SR.post_spec := SR.PS 312388 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_U_6f54b4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 134288 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound_it SegItab_U_6f54b4.IT SegItab_U_6f54b4.IT_sound BF NX0 BR XSTEP F0 PSS plan 134288 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e1a1u.

Module LibSegZ_e1a2u.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_U_6f54b4.ITR.
Definition IT : itab := SegItab_U_6f54b4.IT.
Definition ENDS : list Z := [134308].
Definition STOPS1 : list Z := [367008; 365600; 367464; 312384; 312064; 312388] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-48)); ELit 67584; ELit 462648; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 10) (ELit (-128)); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-112)) (ELit 64);
   KUnk (SA (EVar 2) (-112)) (ELit 64);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 160);
   KUnk (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 2) (-112)) (ELit 112) (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 10) (-128)) (ELit 160) (SA (ELit 0) 65536) (ELit 532480);
   KImg 65536 393472;
   KImg 393512 393544;
   KImg 393560 393568;
   KWord (SA (EVar 2) (-40)) 8 (ELit 260052);
   KWord (SA (EVar 2) (-48)) 8 (ELit 160);
   KWord (SA (EVar 2) (-8)) 8 (ELit 134292);
   KWord (SA (EVar 2) (-16)) 8 (EVar 40);
   KWord (SA (EVar 2) (-24)) 8 (ELit 22)].
Definition ss0 : sym_state := SS 261856 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-112), ELit 64); (EVar 10, (-128), ELit 160)].
Definition F0L : list SR.region := [(EVar 2, (-112), 64); (EVar 10, (-128), 160)].
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
  (([SGA.AStep (SR.SBlock [367008; 365600; 367464; 312384; 312064; 312388; 134308]); SGA.AStep SR.SFill; SGA.AStep (SR.SBlock [367008; 365600; 367464; 312384; 312064; 312388; 134308])], (93, SS 134308 [ELit 0; ELit 134292; EVar 2; ELit 67584; ELit 462648; EVar 57; EVar 58; EVar 59; EVar 10; ELit 22; ELit 0; EVar 61; EVar 62; EVar 63; EVar 64; EVar 65; EVar 66; EVar 67; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 68; EVar 69; EVar 70; EVar 71] [] [KZero {| a_base := EVar 10; a_off := -128 |} (ELit 160); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -112 |} (ELit 64); KUnk {| a_base := EVar 2; a_off := -112 |} (ELit 64); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := 32 |} (ELit 0); KDisj {| a_base := EVar 2; a_off := -112 |} (ELit 112) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 532480); KImg 65536 393472; KImg 393512 393544; KImg 393560 393568; KWord {| a_base := EVar 2; a_off := -40 |} 8 (ELit 260052); KWord {| a_base := EVar 2; a_off := -48 |} 8 (ELit 160); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 134292); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -24 |} 8 (ELit 22)] 72))).
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
Definition ps0 : SR.post_spec := SR.PS 134308 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_U_6f54b4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 261856 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound_it SegItab_U_6f54b4.IT SegItab_U_6f54b4.IT_sound BF NX0 BR XSTEP F0 PSS plan 261856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e1a2u.

Module LibSegZ_e1g1u_g0.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_U_6f54b4.ITR.
Definition IT : itab := SegItab_U_6f54b4.IT.
Definition ENDS : list Z := [134324].
Definition STOPS1 : list Z := [367008; 365600; 367464; 312384; 312064; 312388] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 462648; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 40; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-80)) (ELit 80);
   KUnk (SA (EVar 2) (-80)) (ELit 80);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 160);
   KUnk (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 2) (-80)) (ELit 80) (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 10) (-128)) (ELit 160) (SA (ELit 0) 65536) (ELit 532480);
   KImg 65536 393472;
   KImg 393512 393544;
   KImg 393560 393568;
   KWord (SA (ELit 0) (460320)) 1 (ELit 0);
   KWord (SA (ELit 0) (460321)) 1 (ELit 0);
   KWr (SA (ELit 0) (460320)) (ELit 8);
   KWr (SA (ELit 0) (460320)) (ELit 1);
   KWr (SA (ELit 0) (460321)) (ELit 1)].
Definition ss0 : sym_state := SS 134308 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-80), ELit 80); (ELit 0, (460320), ELit 1); (ELit 0, (460321), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-80), 80); (ELit 0, (460320), 1); (ELit 0, (460321), 1)].
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
  (([SGA.AStep (SR.SBlock [367008; 365600; 367464; 312384; 312064; 312388; 134324])], (93, SS 134324 [ELit 0; ELit 134312; EVar 2; ELit 67584; ELit 462648; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 8; EVar 9; ELit 393560; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := ELit 0; a_off := 460321 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 460320 |} 1 (ELit 1); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 134312); KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -80 |} (ELit 80); KUnk {| a_base := EVar 2; a_off := -80 |} (ELit 72); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 2; a_off := -80 |} (ELit 80) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 532480); KImg 65536 393472; KImg 393512 393544; KImg 393560 393568; KWr {| a_base := ELit 0; a_off := 460320 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 460320 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 460321 |} (ELit 1)] 56))).
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
Definition ps0 : SR.post_spec := SR.PS 134324 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_U_6f54b4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 134308 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound_it SegItab_U_6f54b4.IT SegItab_U_6f54b4.IT_sound BF NX0 BR XSTEP F0 PSS plan 134308 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e1g1u_g0.

Module LibSegZ_e1g1u_g1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_U_6f54b4.ITR.
Definition IT : itab := SegItab_U_6f54b4.IT.
Definition ENDS : list Z := [134324].
Definition STOPS1 : list Z := [367008; 365600; 367464; 312384; 312064; 312388] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; ELit 67584; ELit 462648; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 40; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1099511627776 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-80)) (ELit 80);
   KUnk (SA (EVar 2) (-80)) (ELit 80);
   KRange (EVar 10) 4224 140737488355328;
   KAlign (EVar 10) 16;
   KWr (SA (EVar 10) (-128)) (ELit 160);
   KUnk (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 2) (-80)) (ELit 80) (SA (EVar 10) (-128)) (ELit 160);
   KDisj (SA (EVar 10) (-128)) (ELit 160) (SA (ELit 0) 65536) (ELit 532480);
   KImg 65536 393472;
   KImg 393512 393544;
   KImg 393560 393568;
   KWord (SA (ELit 0) (460320)) 1 (ELit 1);
   KWord (SA (ELit 0) (460321)) 1 (ELit 1);
   KWr (SA (ELit 0) (460320)) (ELit 8);
   KWr (SA (ELit 0) (460320)) (ELit 1);
   KWr (SA (ELit 0) (460321)) (ELit 1)].
Definition ss0 : sym_state := SS 134308 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-80), ELit 80); (ELit 0, (460320), ELit 1); (ELit 0, (460321), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-80), 80); (ELit 0, (460320), 1); (ELit 0, (460321), 1)].
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
  (([SGA.AStep (SR.SBlock [367008; 365600; 367464; 312384; 312064; 312388; 134324])], (93, SS 134324 [ELit 0; ELit 134312; EVar 2; ELit 67584; ELit 462648; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 8; EVar 9; ELit 393560; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1099511627776 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -80 |} (ELit 80); KUnk {| a_base := EVar 2; a_off := -80 |} (ELit 80); KRange (EVar 10) 4224 140737488355328; KAlign (EVar 10) 16; KWr {| a_base := EVar 10; a_off := -128 |} (ELit 160); KUnk {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 2; a_off := -80 |} (ELit 80) {| a_base := EVar 10; a_off := -128 |} (ELit 160); KDisj {| a_base := EVar 10; a_off := -128 |} (ELit 160) {| a_base := ELit 0; a_off := 65536 |} (ELit 532480); KImg 65536 393472; KImg 393512 393544; KImg 393560 393568; KWord {| a_base := ELit 0; a_off := 460320 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 460321 |} 1 (ELit 1); KWr {| a_base := ELit 0; a_off := 460320 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 460320 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 460321 |} (ELit 1)] 56))).
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
Definition ps0 : SR.post_spec := SR.PS 134324 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_U_6f54b4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 134308 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound_it SegItab_U_6f54b4.IT SegItab_U_6f54b4.IT_sound BF NX0 BR XSTEP F0 PSS plan 134308 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_e1g1u_g1.

Module LibSegZ_ps1lu.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(134172, 52%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139880].
Definition STOPS1 : list Z := [139880] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483104 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-32)) (ELit 32);
   KWr (SA (EVar 10) 0) (ELit 32);
   KWord (SA (EVar 10) 0) 1 (EVar 40);
   KRange (EVar 40) 0 255;
   KWord (SA (EVar 11) 0) 1 (EVar 41);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1;
   KWord (SA (EVar 11) 8) 8 (EVar 42);
   KWord (SA (EVar 11) 16) 8 (EVar 43);
   KRange (EVar 10) 4096 140737488355327;
   KAlign (EVar 10) 8;
   KRange (EVar 11) 4096 140737488355327;
   KAlign (EVar 11) 8;
   KDisj (SA (EVar 10) 0) (ELit 32) (SA (EVar 11) 0) (ELit 24);
   KDisj (SA (EVar 2) (-32)) (ELit 32) (SA (EVar 10) 0) (ELit 32);
   KDisj (SA (EVar 2) (-32)) (ELit 32) (SA (EVar 11) 0) (ELit 24)].
Definition ss0 : sym_state := SS 134172 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-32), ELit 32); (EVar 10, (0), ELit 32)].
Definition F0L : list SR.region := [(EVar 2, (-32), 32); (EVar 10, (0), 32)].
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
  (([SGA.AStep (SR.SBlock [139880; 139880])], (93, SS 139880 [ELit 0; ELit 134256; EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 43; EVar 42; EVar 10; EVar 42; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 10; a_off := 24 |} 8 (ELit 0); KWord {| a_base := EVar 10; a_off := 16 |} 8 (ELit 0); KWord {| a_base := EVar 10; a_off := 8 |} 8 (ELit 0); KWord {| a_base := EVar 10; a_off := 0 |} 1 (EMd Instr.M_MUL (ELit 4) (EAlu Instr.ALU_SRL (EVar 40) (ELit 2))); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332483104 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -32 |} (ELit 32); KWr {| a_base := EVar 10; a_off := 0 |} (ELit 32); KRange (EVar 40) 0 255; KWord {| a_base := EVar 11; a_off := 0 |} 1 (EVar 41); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1; KWord {| a_base := EVar 11; a_off := 8 |} 8 (EVar 42); KWord {| a_base := EVar 11; a_off := 16 |} 8 (EVar 43); KRange (EVar 10) 4096 140737488355327; KAlign (EVar 10) 8; KRange (EVar 11) 4096 140737488355327; KAlign (EVar 11) 8; KDisj {| a_base := EVar 10; a_off := 0 |} (ELit 32) {| a_base := EVar 11; a_off := 0 |} (ELit 24); KDisj {| a_base := EVar 2; a_off := -32 |} (ELit 32) {| a_base := EVar 10; a_off := 0 |} (ELit 32); KDisj {| a_base := EVar 2; a_off := -32 |} (ELit 32) {| a_base := EVar 11; a_off := 0 |} (ELit 24)] 48))).
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
Definition ps0 : SR.post_spec := SR.PS 139880 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 134172 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 134172 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_ps1lu.

Module LibSegZ_ps1su.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(134172, 52%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139880].
Definition STOPS1 : list Z := [139880] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483104 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-32)) (ELit 32);
   KWr (SA (EVar 10) 0) (ELit 32);
   KWord (SA (EVar 10) 0) 1 (EVar 40);
   KRange (EVar 40) 0 255;
   KWord (SA (EVar 11) 0) 1 (EVar 41);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0;
   KRange (EVar 10) 4096 140737488355327;
   KAlign (EVar 10) 8;
   KRange (EVar 11) 4096 140737488355327;
   KAlign (EVar 11) 8;
   KDisj (SA (EVar 10) 0) (ELit 32) (SA (EVar 11) 0) (ELit 24);
   KDisj (SA (EVar 2) (-32)) (ELit 32) (SA (EVar 10) 0) (ELit 32);
   KDisj (SA (EVar 2) (-32)) (ELit 32) (SA (EVar 11) 0) (ELit 24)].
Definition ss0 : sym_state := SS 134172 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-32), ELit 32); (EVar 10, (0), ELit 32)].
Definition F0L : list SR.region := [(EVar 2, (-32), 32); (EVar 10, (0), 32)].
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
  (([SGA.AStep (SR.SBlock [139880; 139880])], (93, SS 139880 [ELit 0; ELit 134256; EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 11) (ELit 1); EAlu Instr.ALU_SRL (EVar 41) (ELit 1); EVar 10; EAlu Instr.ALU_SRL (EVar 41) (ELit 1); EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 10; a_off := 24 |} 8 (ELit 0); KWord {| a_base := EVar 10; a_off := 16 |} 8 (ELit 0); KWord {| a_base := EVar 10; a_off := 8 |} 8 (ELit 0); KWord {| a_base := EVar 10; a_off := 0 |} 1 (EMd Instr.M_MUL (ELit 4) (EAlu Instr.ALU_SRL (EVar 40) (ELit 2))); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332483104 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -32 |} (ELit 32); KWr {| a_base := EVar 10; a_off := 0 |} (ELit 32); KRange (EVar 40) 0 255; KWord {| a_base := EVar 11; a_off := 0 |} 1 (EVar 41); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0; KRange (EVar 10) 4096 140737488355327; KAlign (EVar 10) 8; KRange (EVar 11) 4096 140737488355327; KAlign (EVar 11) 8; KDisj {| a_base := EVar 10; a_off := 0 |} (ELit 32) {| a_base := EVar 11; a_off := 0 |} (ELit 24); KDisj {| a_base := EVar 2; a_off := -32 |} (ELit 32) {| a_base := EVar 10; a_off := 0 |} (ELit 32); KDisj {| a_base := EVar 2; a_off := -32 |} (ELit 32) {| a_base := EVar 11; a_off := 0 |} (ELit 24)] 48))).
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
Definition ps0 : SR.post_spec := SR.PS 139880 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 134172 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 134172 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_ps1su.

Module LibSegZ_ps2u.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(134172, 52%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [134280].
Definition STOPS1 : list Z := [134280] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; ELit 0; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483104 140737488355328;
   KAlign (EVar 2) 16;
   KWord (SA (EVar 2) (-8)) 8 (EVar 41);
   KWord (SA (EVar 2) (-16)) 8 (EVar 42);
   KWord (SA (EVar 2) (-24)) 8 (EVar 43)].
Definition ss0 : sym_state := SS 134256 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [134280; 134280])], (93, SS 134280 [ELit 0; EVar 41; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 42; EVar 43; EVar 10; ELit 0; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 140735332483104 140737488355328; KAlign (EVar 2) 16; KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 41); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 43)] 48))).
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
Definition ps0 : SR.post_spec := SR.PS 134280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 134256 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 134256 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_ps2u.

Module LibSegZ_ps3u.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(134172, 52%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [134288].
Definition STOPS1 : list Z := [134288] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; ELit 22; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483104 140737488355328;
   KAlign (EVar 2) 16].
Definition ss0 : sym_state := SS 134256 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [134288; 134288])], (93, SS 134288 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; ELit 22; ELit 32; ELit 22; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 140735332483104 140737488355328; KAlign (EVar 2) 16] 48))).
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
Definition ps0 : SR.post_spec := SR.PS 134288 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 134256 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 134256 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_ps3u.
