(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.GcFlush12.  (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ub0PlanKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LibSegZ_d5ue1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [143880].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352)].
Definition ss0 : sym_state := SS 140532 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-352), ELit 352)].
Definition F0L : list SR.region := [(EVar 2, (-352), 352)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 143880])], (93, SS 143880 [ELit 0; ELit 140616; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 35; EAlu Instr.ALU_ADD (EVar 2) (ELit (-136)); EVar 34; EAlu Instr.ALU_ADD (EVar 2) (ELit (-184)); EVar 36; EVar 37; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 21; EVar 22; EVar 37; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352)] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 143880 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140532 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 140532 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ue1.

Module LibSegZ_d5ue2n.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [143880].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 21; EVar 22; EVar 37; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-136)) 1 (EVar 41);
   KWord (SA (EVar 2) (-128)) 8 (EVar 42);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0;
   KRange (EVar 42) 1 1;
   KRange (EVar 33) 1048576 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 0) 1 (EVar 38);
   KRange (EVar 38) 0 255].
Definition ss0 : sym_state := SS 140616 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-152), ELit 16)].
Definition F0L : list SR.region := [(EVar 2, (-152), 16)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 143880])], (93, SS 143880 [ELit 0; ELit 140676; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 35; EAlu Instr.ALU_ADD (EVar 2) (ELit (-184)); EVar 33; EAlu Instr.ALU_ADD (EVar 2) (ELit (-216)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 41; EVar 38; EVar 21; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EVar 37; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -144 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -136 |} 1 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 42); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0; KRange (EVar 42) 1 1; KRange (EVar 33) 1048576 140737488355296; KAlign (EVar 33) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 33; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 33; a_off := 0 |} 1 (EVar 38); KRange (EVar 38) 0 255] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 143880 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140616 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 140616 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ue2n.

Module LibSegZ_d5ue3.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [139548].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 41; EVar 38; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-184)) 1 (EVar 44);
   KWord (SA (EVar 2) (-136)) 1 (EVar 41);
   KRange (EVar 44) 0 255;
   KRange (EVar 41) 0 255;
   KRange (EVar 38) 0 255].
Definition ss0 : sym_state := SS 140676 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-184), ELit 1); (EVar 2, (-136), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-184), 1); (EVar 2, (-136), 1)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 139548])], (93, SS 139548 [ELit 0; ELit 140728; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 2) (ELit (-184)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-136)); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 41; EVar 38; EVar 21; EVar 22; EVar 23; EVar 24; EAlu Instr.ALU_AND (EVar 38) (ELit 2); EAlu Instr.ALU_SRL (EAlu Instr.ALU_XOR (EAlu Instr.ALU_AND (EVar 41) (ELit 2)) (EAlu Instr.ALU_AND (EVar 38) (ELit 2))) (ELit 1); EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -136 |} 1 (EAlu Instr.ALU_AND (EVar 41) (ELit 253)); KWord {| a_base := EVar 2; a_off := -184 |} 1 (EAlu Instr.ALU_AND (EVar 44) (ELit 253)); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KRange (EVar 44) 0 255; KRange (EVar 41) 0 255; KRange (EVar 38) 0 255] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 139548 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140676 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 140676 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ue3.

Module LibSegZ_d5ue4n.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141208].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 33; EVar 47; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-184)) 1 (EVar 44);
   KWord (SA (EVar 2) (-176)) 8 (EVar 45);
   KWord (SA (EVar 2) (-160)) 8 (EVar 46);
   KWord (SA (EVar 2) (-120)) 8 (EVar 63);
   KWord (SA (EVar 2) (-152)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)));
   KWord (SA (EVar 2) (-144)) 8 (ELit 1);
   KRange (EVar 47) 0 1;
   KRange (EVar 44) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 44) (ELit 1)) 1 1;
   KRange (EVar 45) 2 300;
   KRange (EVar 46) 4096 140737488355328;
   KRange (EVar 63) 4294967296 18446744073709551615;
   KRange (EAlu Instr.ALU_SRL (EVar 63) (ELit 32)) 1 4294967295;
   KRange (EVar 33) 1048576 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 0) 1 (EVar 38);
   KRange (EVar 38) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 38) (ELit 1)) 1 1;
   KWord (SA (EVar 33) 8) 8 (EVar 39);
   KRange (EVar 39) 0 300;
   KWord (SA (EVar 33) 24) 8 (EVar 40);
   KRange (EVar 40) 4096 140737488355328].
Definition ss0 : sym_state := SS 140728 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-232), ELit 16); (EVar 2, (-248), ELit 16)].
Definition F0L : list SR.region := [(EVar 2, (-232), 16); (EVar 2, (-248), 16)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141208])], (93, SS 141208 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 33; EAlu Instr.ALU_SRL (EVar 63) (ELit 32); EVar 39; ELit 0; ELit 1; ELit 1; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 63; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -240 |} 8 (EVar 39); KWord {| a_base := EVar 2; a_off := -248 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -224 |} 8 (EVar 39); KWord {| a_base := EVar 2; a_off := -232 |} 8 (EVar 40); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -184 |} 1 (EVar 44); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EVar 45); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 46); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 63); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); KWord {| a_base := EVar 2; a_off := -144 |} 8 (ELit 1); KRange (EVar 47) 0 1; KRange (EVar 44) 0 255; KRange (EAlu Instr.ALU_AND (EVar 44) (ELit 1)) 1 1; KRange (EVar 45) 2 300; KRange (EVar 46) 4096 140737488355328; KRange (EVar 63) 4294967296 18446744073709551615; KRange (EAlu Instr.ALU_SRL (EVar 63) (ELit 32)) 1 4294967295; KRange (EVar 33) 1048576 140737488355296; KAlign (EVar 33) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 33; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 33; a_off := 0 |} 1 (EVar 38); KRange (EVar 38) 0 255; KRange (EAlu Instr.ALU_AND (EVar 38) (ELit 1)) 1 1; KWord {| a_base := EVar 33; a_off := 8 |} 8 (EVar 39); KRange (EVar 39) 0 300; KWord {| a_base := EVar 33; a_off := 24 |} 8 (EVar 40); KRange (EVar 40) 4096 140737488355328] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141208 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 140728 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 140728 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ue4n.

Module LibSegZ_d5uepi.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142328].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-8)) 8 (EVar 48);
   KWord (SA (EVar 2) (-16)) 8 (EVar 49);
   KWord (SA (EVar 2) (-24)) 8 (EVar 50);
   KWord (SA (EVar 2) (-32)) 8 (EVar 51);
   KWord (SA (EVar 2) (-40)) 8 (EVar 52);
   KWord (SA (EVar 2) (-48)) 8 (EVar 53);
   KWord (SA (EVar 2) (-56)) 8 (EVar 54);
   KWord (SA (EVar 2) (-64)) 8 (EVar 55);
   KWord (SA (EVar 2) (-72)) 8 (EVar 56);
   KWord (SA (EVar 2) (-80)) 8 (EVar 57);
   KWord (SA (EVar 2) (-88)) 8 (EVar 58);
   KWord (SA (EVar 2) (-96)) 8 (EVar 59);
   KWord (SA (EVar 2) (-104)) 8 (EVar 60)].
Definition ss0 : sym_state := SS 142272 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 142328])], (93, SS 142328 [ELit 0; EVar 48; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 49; EVar 50; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 51; EVar 52; EVar 53; EVar 54; EVar 55; EVar 56; EVar 57; EVar 58; EVar 59; EVar 60; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 48); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 49); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 50); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 51); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 52); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 53); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 54); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 55); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 56); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 57); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 58); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 59); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 60)] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 142328 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 142272 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 142272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5uepi.

Module LibSegZ_d5ug1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [143880].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16].
Definition ss0 : sym_state := SS 141208 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 143880])], (93, SS 143880 [ELit 0; ELit 141224; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 2) (ELit (-216)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-184)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-280)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 143880 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141208 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug1.

Module LibSegZ_d5ug10.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141596].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 65; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KRange (EVar 35) 1048576 140737488355296;
   KAlign (EVar 35) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 35) 0) (ELit 32);
   KWord (SA (EVar 35) 0) 1 (EVar 69);
   KRange (EVar 69) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 1 1;
   KWord (SA (EVar 35) 24) 8 (EVar 40);
   KWord (SA (EVar 35) 8) 8 (EAlu Instr.ALU_ADD (EVar 70) (ELit (1)));
   KRange (EVar 70) 0 300;
   KRange (EVar 40) 4096 140737488355328].
Definition ss0 : sym_state := SS 141556 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-232), ELit 16)].
Definition F0L : list SR.region := [(EVar 2, (-232), 16)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141596])], (93, SS 141596 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 40; EAlu Instr.ALU_ADD (EVar 70) (ELit 1); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 65; EVar 65; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -224 |} 8 (EAlu Instr.ALU_ADD (EVar 70) (ELit 1)); KWord {| a_base := EVar 2; a_off := -232 |} 8 (EVar 40); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 35; a_off := 0 |} 1 (EVar 69); KRange (EVar 69) 0 255; KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 1 1; KWord {| a_base := EVar 35; a_off := 24 |} 8 (EVar 40); KWord {| a_base := EVar 35; a_off := 8 |} 8 (EAlu Instr.ALU_ADD (EVar 70) (ELit 1)); KRange (EVar 70) 0 300; KRange (EVar 40) 4096 140737488355328] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141556 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141556 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug10.

Module LibSegZ_d5ug2.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [143880].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16].
Definition ss0 : sym_state := SS 141224 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 143880])], (93, SS 143880 [ELit 0; ELit 141240; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 2) (ELit (-280)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-136)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-304)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 143880 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141224 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141224 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug2.

Module LibSegZ_d5ug3.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142636].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352)].
Definition ss0 : sym_state := SS 141240 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-284), ELit 4)].
Definition F0L : list SR.region := [(EVar 2, (-284), 4)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 142636])], (93, SS 142636 [ELit 0; ELit 141264; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EAlu Instr.ALU_ADD (EVar 2) (ELit (-136)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-184)); EAlu Instr.ALU_ADD (EVar 2) (ELit (-284)); EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -284 |} 4 (ELit 0); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352)] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 142636 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141240 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141240 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug3.

Module LibSegZ_d5ug4i.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [136420].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 64; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-136)) 1 (EVar 41);
   KWord (SA (EVar 2) (-128)) 8 (EVar 67);
   KWord (SA (EVar 2) (-176)) 8 (EVar 65);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0;
   KRange (EVar 67) 0 300;
   KRange (EVar 65) 0 300;
   KRange (EVar 64) 0 1].
Definition ss0 : sym_state := SS 141264 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-344), ELit 8); (EVar 2, (-152), ELit 16)].
Definition F0L : list SR.region := [(EVar 2, (-344), 8); (EVar 2, (-152), 16)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 136420])], (93, SS 136420 [ELit 0; ELit 141312; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 35; EAlu Instr.ALU_ADD (EVar 65) (EMd Instr.M_MUL (ELit (-1)) (EVar 67)); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 67; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); EVar 23; EVar 65; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); KWord {| a_base := EVar 2; a_off := -344 |} 8 (EVar 64); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -136 |} 1 (EVar 41); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 67); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EVar 65); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0; KRange (EVar 67) 0 300; KRange (EVar 65) 0 300; KRange (EVar 64) 0 1] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 136420 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141264 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug4i.

Module LibSegZ_d5ug5d.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141360; 141384].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KRange (EVar 35) 1048576 140737488355296;
   KAlign (EVar 35) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 35) 0) (ELit 32);
   KWord (SA (EVar 35) 0) 1 (EVar 69);
   KRange (EVar 69) 0 255;
   KWord (SA (EVar 35) 8) 8 (EVar 70);
   KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 1 1;
   KRange (EVar 70) 0 300;
   KWord (SA (EVar 35) 24) 8 (EVar 40);
   KRange (EVar 40) 4096 140737488355328].
Definition ss0 : sym_state := SS 141312 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-232), ELit 16)].
Definition F0L : list SR.region := [(EVar 2, (-232), 16)].
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
  (SS 141348 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 40; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 70; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -224 |} 8 (EVar 70); KWord {| a_base := EVar 2; a_off := -232 |} 8 (EVar 40); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 35; a_off := 0 |} 1 (EVar 69); KRange (EVar 69) 0 255; KWord {| a_base := EVar 35; a_off := 8 |} 8 (EVar 70); KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 1 1; KRange (EVar 70) 0 300; KWord {| a_base := EVar 35; a_off := 24 |} 8 (EVar 40); KRange (EVar 40) 4096 140737488355328] 80).

(* [comment removed for export] *)
Definition ce2 : expr := EVar 70.
Definition arms2 := Eval vm_compute in (SGP.case_arms s1 ce2 (0)).
Definition lo2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition hi2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

(* [comment removed for export] *)
Definition ex3 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141360; 141384])], (93, SS 141384 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 40; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 70; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 70) 0 0; KWord {| a_base := EVar 2; a_off := -224 |} 8 (EVar 70); KWord {| a_base := EVar 2; a_off := -232 |} 8 (EVar 40); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 35; a_off := 0 |} 1 (EVar 69); KRange (EVar 69) 0 255; KWord {| a_base := EVar 35; a_off := 8 |} 8 (EVar 70); KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 1 1; KRange (EVar 70) 0 300; KWord {| a_base := EVar 35; a_off := 24 |} 8 (EVar 40); KRange (EVar 40) 4096 140737488355328] 80))).
Definition s3 : sym_state := snd (snd ex3).

(* [comment removed for export] *)
Definition ex4 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141360; 141384])], (93, SS 141360 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 40; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 18446744073709551615; EVar 20; EVar 21; EAlu Instr.ALU_ADD (EVar 70) (ELit (-1)); EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 70) 1 300; KWord {| a_base := EVar 2; a_off := -224 |} 8 (EVar 70); KWord {| a_base := EVar 2; a_off := -232 |} 8 (EVar 40); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 35; a_off := 0 |} 1 (EVar 69); KRange (EVar 69) 0 255; KWord {| a_base := EVar 35; a_off := 8 |} 8 (EVar 70); KRange (EAlu Instr.ALU_AND (EVar 69) (ELit 1)) 1 1; KRange (EVar 70) 0 300; KWord {| a_base := EVar 35; a_off := 24 |} 8 (EVar 40); KRange (EVar 40) 4096 140737488355328] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141360 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 141384 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141312 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141312 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug5d.

Module LibSegZ_d5ug6.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [136232].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16].
Definition ss0 : sym_state := SS 141384 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 136232])], (93, SS 136232 [ELit 0; ELit 141396; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 36; EAlu Instr.ALU_ADD (EVar 2) (ELit (-184)); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 136232 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141384 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141384 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug6.

Module LibSegZ_d5ug7nd0.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141596; 141488].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 67; EVar 22; EVar 37; EVar 65; EVar 62; EVar 61; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-120)) 8 (EVar 74);
   KWord (SA (EVar 2) (-152)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)));
   KWord (SA (EVar 2) (-144)) 8 (EVar 67);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 36) 1048576 140737488355296;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 36) 0) (ELit 32);
   KWord (SA (EVar 36) 0) 1 (EVar 71);
   KRange (EVar 71) 0 255;
   KWord (SA (EVar 36) 8) 8 (EVar 65);
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1;
   KWord (SA (EVar 36) 24) 8 (EVar 72);
   KRange (EVar 72) 4096 140737488355328;
   KAlign (EVar 72) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 72) 0) (ELit 64);
   KWord (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72)) (-8)) 8 (EVar 73);
   KRange (EVar 73) 0 18446744073709551615;
   KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 1 1;
   KRange (EVar 65) 1 7;
   KRange (EVar 67) 1 1;
   KRange (EVar 61) 0 1;
   KRange (EVar 62) 0 2;
   KRange (EVar 37) 0 1].
Definition ss0 : sym_state := SS 141396 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-336), ELit 24); (EVar 2, (-304), ELit 16)].
Definition F0L : list SR.region := [(EVar 2, (-336), 24); (EVar 2, (-304), 16)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141596; 141488])], (93, SS 141596 [ELit 0; ELit 141480; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 74; ELit 0; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); ELit 1152921504606846976; ELit 0; EVar 15; EVar 16; EVar 17; EVar 18; EVar 73; EVar 20; EVar 67; ELit 0; EAlu Instr.ALU_ADD (EVar 65) (ELit (-1)); EVar 65; EVar 62; EVar 61; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -296 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -304 |} 8 (EVar 72); KWord {| a_base := EVar 2; a_off := -320 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -328 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -336 |} 8 (EVar 37); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 74); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 67); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 36) 1048576 140737488355296; KAlign (EVar 36) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 36; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 36; a_off := 0 |} 1 (EVar 71); KRange (EVar 71) 0 255; KWord {| a_base := EVar 36; a_off := 8 |} 8 (EVar 65); KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1; KWord {| a_base := EVar 36; a_off := 24 |} 8 (EVar 72); KRange (EVar 72) 4096 140737488355328; KAlign (EVar 72) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 72; a_off := 0 |} (ELit 64); KWord {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72); a_off := -8 |} 8 (EVar 73); KRange (EVar 73) 0 18446744073709551615; KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 1 1; KRange (EVar 65) 1 7; KRange (EVar 67) 1 1; KRange (EVar 61) 0 1; KRange (EVar 62) 0 2; KRange (EVar 37) 0 1] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141396 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141396 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug7nd0.

Module LibSegZ_d5ug7nd1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141596; 141488].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 67; EVar 22; EVar 37; EVar 65; EVar 62; EVar 61; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-120)) 8 (EVar 74);
   KWord (SA (EVar 2) (-152)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)));
   KWord (SA (EVar 2) (-144)) 8 (EVar 67);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 36) 1048576 140737488355296;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 36) 0) (ELit 32);
   KWord (SA (EVar 36) 0) 1 (EVar 71);
   KRange (EVar 71) 0 255;
   KWord (SA (EVar 36) 8) 8 (EVar 65);
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1;
   KWord (SA (EVar 36) 24) 8 (EVar 72);
   KRange (EVar 72) 4096 140737488355328;
   KAlign (EVar 72) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 72) 0) (ELit 64);
   KWord (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72)) (-8)) 8 (EVar 73);
   KRange (EVar 73) 0 18446744073709551615;
   KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 0 0;
   KRange (EVar 65) 1 7;
   KRange (EVar 67) 1 1;
   KRange (EVar 61) 0 1;
   KRange (EVar 62) 0 2;
   KRange (EVar 37) 0 1].
Definition ss0 : sym_state := SS 141396 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-336), ELit 24); (EVar 2, (-304), ELit 16)].
Definition F0L : list SR.region := [(EVar 2, (-336), 24); (EVar 2, (-304), 16)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141596; 141488])], (93, SS 141488 [ELit 0; ELit 141480; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 74; ELit 0; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); ELit 1152921504606846976; ELit 0; EVar 15; EVar 16; EVar 17; EVar 18; EVar 73; EVar 20; EVar 67; ELit 0; EAlu Instr.ALU_ADD (EVar 65) (ELit (-1)); EVar 65; EVar 62; EVar 61; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -296 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -304 |} 8 (EVar 72); KWord {| a_base := EVar 2; a_off := -320 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -328 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -336 |} 8 (EVar 37); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 74); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 67); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 36) 1048576 140737488355296; KAlign (EVar 36) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 36; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 36; a_off := 0 |} 1 (EVar 71); KRange (EVar 71) 0 255; KWord {| a_base := EVar 36; a_off := 8 |} 8 (EVar 65); KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1; KWord {| a_base := EVar 36; a_off := 24 |} 8 (EVar 72); KRange (EVar 72) 4096 140737488355328; KAlign (EVar 72) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 72; a_off := 0 |} (ELit 64); KWord {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 65)) (EVar 72); a_off := -8 |} 8 (EVar 73); KRange (EVar 73) 0 18446744073709551615; KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 0 0; KRange (EVar 65) 1 7; KRange (EVar 67) 1 1; KRange (EVar 61) 0 1; KRange (EVar 62) 0 2; KRange (EVar 37) 0 1] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141488 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141396 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141396 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug7nd1.

Module LibSegZ_d5ug7ni0.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141596; 141488].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 67; EVar 22; EVar 37; EVar 65; EVar 62; EVar 61; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-120)) 8 (EVar 74);
   KWord (SA (EVar 2) (-152)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)));
   KWord (SA (EVar 2) (-144)) 8 (EVar 67);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 36) 1048576 140737488355296;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 36) 0) (ELit 32);
   KWord (SA (EVar 36) 0) 1 (EVar 71);
   KRange (EVar 71) 0 255;
   KWord (SA (EVar 36) 8) 8 (EVar 65);
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0;
   KWord (SA (EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65))) 8) 8 (EVar 73);
   KRange (EVar 73) 0 18446744073709551615;
   KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 1 1;
   KRange (EVar 65) 1 2;
   KRange (EVar 67) 1 1;
   KRange (EVar 61) 0 1;
   KRange (EVar 62) 0 2;
   KRange (EVar 37) 0 1].
Definition ss0 : sym_state := SS 141396 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-336), ELit 24); (EVar 2, (-304), ELit 16)].
Definition F0L : list SR.region := [(EVar 2, (-336), 24); (EVar 2, (-304), 16)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141596; 141488])], (93, SS 141596 [ELit 0; ELit 141480; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 74; ELit 0; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); ELit 1152921504606846976; ELit 0; EVar 15; EVar 16; EVar 17; EVar 18; EVar 73; EVar 20; EVar 67; ELit 0; EAlu Instr.ALU_ADD (EVar 65) (ELit (-1)); EVar 65; EVar 62; EVar 61; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -296 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -304 |} 8 (EAlu Instr.ALU_ADD (EVar 36) (ELit 16)); KWord {| a_base := EVar 2; a_off := -320 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -328 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -336 |} 8 (EVar 37); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 74); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 67); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 36) 1048576 140737488355296; KAlign (EVar 36) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 36; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 36; a_off := 0 |} 1 (EVar 71); KRange (EVar 71) 0 255; KWord {| a_base := EVar 36; a_off := 8 |} 8 (EVar 65); KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65)); a_off := 8 |} 8 (EVar 73); KRange (EVar 73) 0 18446744073709551615; KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 1 1; KRange (EVar 65) 1 2; KRange (EVar 67) 1 1; KRange (EVar 61) 0 1; KRange (EVar 62) 0 2; KRange (EVar 37) 0 1] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141396 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141396 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug7ni0.

Module LibSegZ_d5ug7ni1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141596; 141488].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 67; EVar 22; EVar 37; EVar 65; EVar 62; EVar 61; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-120)) 8 (EVar 74);
   KWord (SA (EVar 2) (-152)) 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)));
   KWord (SA (EVar 2) (-144)) 8 (EVar 67);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EVar 36) 1048576 140737488355296;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 36) 0) (ELit 32);
   KWord (SA (EVar 36) 0) 1 (EVar 71);
   KRange (EVar 71) 0 255;
   KWord (SA (EVar 36) 8) 8 (EVar 65);
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0;
   KWord (SA (EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65))) 8) 8 (EVar 73);
   KRange (EVar 73) 0 18446744073709551615;
   KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 0 0;
   KRange (EVar 65) 1 2;
   KRange (EVar 67) 1 1;
   KRange (EVar 61) 0 1;
   KRange (EVar 62) 0 2;
   KRange (EVar 37) 0 1].
Definition ss0 : sym_state := SS 141396 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-336), ELit 24); (EVar 2, (-304), ELit 16)].
Definition F0L : list SR.region := [(EVar 2, (-336), 24); (EVar 2, (-304), 16)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141596; 141488])], (93, SS 141488 [ELit 0; ELit 141480; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 74; ELit 0; EAlu Instr.ALU_ADD (EVar 2) (ELit (-120)); ELit 1152921504606846976; ELit 0; EVar 15; EVar 16; EVar 17; EVar 18; EVar 73; EVar 20; EVar 67; ELit 0; EAlu Instr.ALU_ADD (EVar 65) (ELit (-1)); EVar 65; EVar 62; EVar 61; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -296 |} 8 (EVar 65); KWord {| a_base := EVar 2; a_off := -304 |} 8 (EAlu Instr.ALU_ADD (EVar 36) (ELit 16)); KWord {| a_base := EVar 2; a_off := -320 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -328 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -336 |} 8 (EVar 37); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 74); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-120))); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 67); KRange (EVar 74) 0 18446744073709551615; KRange (EVar 36) 1048576 140737488355296; KAlign (EVar 36) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 36; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 36; a_off := 0 |} 1 (EVar 71); KRange (EVar 71) 0 255; KWord {| a_base := EVar 36; a_off := 8 |} 8 (EVar 65); KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit 8) (EVar 65)); a_off := 8 |} 8 (EVar 73); KRange (EVar 73) 0 18446744073709551615; KRange (EAlu Instr.ALU_SLTU (EVar 73) (EVar 74)) 0 0; KRange (EVar 65) 1 2; KRange (EVar 67) 1 1; KRange (EVar 61) 0 1; KRange (EVar 62) 0 2; KRange (EVar 37) 0 1] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141488 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141396 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141396 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug7ni1.

Module LibSegZ_d5ug8.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [136420].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-296)) 8 (EVar 65);
   KRange (EVar 65) 0 300].
Definition ss0 : sym_state := SS 141488 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 136420])], (93, SS 136420 [ELit 0; ELit 141504; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 9; EVar 36; EAlu Instr.ALU_ADD (EVar 65) (ELit 1); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -296 |} 8 (EVar 65); KRange (EVar 65) 0 300] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 136420 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141488 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141488 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug8.

Module LibSegZ_d5ug9.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [136420].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-224)) 8 (EVar 70);
   KRange (EVar 36) 1048576 140737488355296;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 36) 0) (ELit 32);
   KWord (SA (EVar 36) 0) 1 (EVar 71);
   KRange (EVar 71) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1;
   KWord (SA (EVar 36) 24) 8 (EVar 72);
   KWord (SA (EVar 36) 8) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit (1)));
   KRange (EVar 70) 0 300;
   KRange (EVar 65) 0 300;
   KRange (EVar 72) 4096 140737488355328].
Definition ss0 : sym_state := SS 141504 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-304), ELit 16)].
Definition F0L : list SR.region := [(EVar 2, (-304), 16)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 136420])], (93, SS 136420 [ELit 0; ELit 141556; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 35; EVar 35; EAlu Instr.ALU_ADD (EVar 70) (ELit 1); EVar 70; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -296 |} 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 1)); KWord {| a_base := EVar 2; a_off := -304 |} 8 (EVar 72); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -224 |} 8 (EVar 70); KRange (EVar 36) 1048576 140737488355296; KAlign (EVar 36) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 36; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 36; a_off := 0 |} 1 (EVar 71); KRange (EVar 71) 0 255; KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 1 1; KWord {| a_base := EVar 36; a_off := 24 |} 8 (EVar 72); KWord {| a_base := EVar 36; a_off := 8 |} 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 1)); KRange (EVar 70) 0 300; KRange (EVar 65) 0 300; KRange (EVar 72) 4096 140737488355328] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 136420 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141504 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141504 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug9.

Module LibSegZ_d5ug9i.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [136420].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-224)) 8 (EVar 70);
   KRange (EVar 36) 1048576 140737488355296;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 36) 0) (ELit 32);
   KWord (SA (EVar 36) 0) 1 (EVar 71);
   KRange (EVar 71) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0;
   KWord (SA (EVar 36) 8) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit (1)));
   KRange (EVar 70) 0 300;
   KRange (EVar 65) 0 300].
Definition ss0 : sym_state := SS 141504 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-304), ELit 16)].
Definition F0L : list SR.region := [(EVar 2, (-304), 16)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 136420])], (93, SS 136420 [ELit 0; ELit 141556; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 36; EVar 35; EVar 35; EAlu Instr.ALU_ADD (EVar 70) (ELit 1); EVar 70; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -296 |} 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 1)); KWord {| a_base := EVar 2; a_off := -304 |} 8 (EAlu Instr.ALU_ADD (EVar 36) (ELit 16)); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -224 |} 8 (EVar 70); KRange (EVar 36) 1048576 140737488355296; KAlign (EVar 36) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 36; a_off := 0 |} (ELit 32); KWord {| a_base := EVar 36; a_off := 0 |} 1 (EVar 71); KRange (EVar 71) 0 255; KRange (EAlu Instr.ALU_AND (EVar 71) (ELit 1)) 0 0; KWord {| a_base := EVar 36; a_off := 8 |} 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 1)); KRange (EVar 70) 0 300; KRange (EVar 65) 0 300] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 136420 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141504 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141504 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ug9i.

Module LibSegZ_d5ul1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142956].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 67; EVar 22; (EAlu Instr.ALU_ADD (EVar 67) (EVar 77)); EVar 74; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-304)) 8 (EVar 79);
   KRange (EVar 79) 4096 140737488355328;
   KAlign (EVar 79) 8;
   KWord (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 67)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 77)) (EVar 79))) 0) 8 (EVar 73);
   KWord (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 67)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 77)) (EVar 79))) (-8)) 8 (EVar 76);
   KRange (EVar 67) 1 301;
   KRange (EVar 77) 0 299;
   KRange (EVar 73) 0 18446744073709551615;
   KRange (EVar 76) 0 18446744073709551615;
   KRange (EVar 74) 0 18446744073709551615].
Definition ss0 : sym_state := SS 141644 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 142956])], (93, SS 142956 [ELit 0; ELit 141696; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 73; EVar 76; EVar 74; ELit 0; EVar 15; EVar 16; EVar 17; EVar 33; EVar 19; EVar 20; EVar 67; EVar 22; EAlu Instr.ALU_ADD (EVar 67) (EVar 77); EVar 74; EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 67) (EVar 77)) (ELit (-1)); EVar 73; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -304 |} 8 (EVar 79); KRange (EVar 79) 4096 140737488355328; KAlign (EVar 79) 8; KWord {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 67)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 77)) (EVar 79)); a_off := 0 |} 8 (EVar 73); KWord {| a_base := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 67)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 77)) (EVar 79)); a_off := -8 |} 8 (EVar 76); KRange (EVar 67) 1 301; KRange (EVar 77) 0 299; KRange (EVar 73) 0 18446744073709551615; KRange (EVar 76) 0 18446744073709551615; KRange (EVar 74) 0 18446744073709551615] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 142956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141644 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141644 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ul1.

Module LibSegZ_d5ul2.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [143208].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 76; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 33; (EMd Instr.M_MUL (ELit 8) (EVar 77)); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 67)) (ELit 1152921504606846976)); EVar 67; EVar 22; (EAlu Instr.ALU_ADD (EVar 67) (EVar 77)); EVar 24; EVar 25; EVar 26; (EMd Instr.M_MUL (ELit (-1)) (EVar 67)); EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-304)) 8 (EVar 79);
   KWord (SA (EVar 2) (-152)) 8 (EVar 66);
   KWord (SA (EVar 2) (-144)) 8 (EVar 67);
   KRange (EVar 79) 4096 140737488355328;
   KAlign (EVar 79) 8;
   KRange (EVar 67) 1 301;
   KRange (EVar 77) 0 299;
   KRange (EVar 76) 0 18446744073709551615].
Definition ss0 : sym_state := SS 141696 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-312), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-312), 8)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 143208])], (93, SS 143208 [ELit 0; ELit 141760; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 77)) (EVar 79); EVar 66; EVar 67; EAlu Instr.ALU_ADD (EVar 2) (ELit (-312)); EVar 15; EVar 16; EVar 17; EVar 33; EMd Instr.M_MUL (ELit 8) (EVar 77); EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 67)) (ELit 1152921504606846976); EVar 67; EVar 22; EVar 77; EVar 24; EVar 25; EVar 26; EMd Instr.M_MUL (ELit (-1)) (EVar 67); EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -312 |} 8 (EVar 76); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -304 |} 8 (EVar 79); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 67); KRange (EVar 79) 4096 140737488355328; KAlign (EVar 79) 8; KRange (EVar 67) 1 301; KRange (EVar 77) 0 299; KRange (EVar 76) 0 18446744073709551615] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 143208 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141696 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141696 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ul2.

Module LibSegZ_d5ul3c.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141644; 141792].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; (EMd Instr.M_MUL (ELit 8) (EVar 77)); EVar 20; EVar 21; EVar 78; EVar 77; EVar 24; EVar 75; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-312)) 8 (EVar 76);
   KWord (SA (EVar 2) (-232)) 8 (EVar 68);
   KRange (EVar 68) 4096 140737488355328;
   KAlign (EVar 68) 8;
   KWr (SA (EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77))) 0) (ELit 8);
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77))) 0) (ELit 8);
   KRange (EAlu Instr.ALU_SLTU (EVar 78) (EVar 75)) 1 1;
   KRange (EVar 78) 0 300;
   KRange (EVar 75) 0 300;
   KRange (EVar 77) 0 299;
   KRange (EVar 76) 0 18446744073709551615].
Definition ss0 : sym_state := SS 141760 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77))), (0), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77))), (0), 8)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141644; 141792])], (93, SS 141644 [ELit 0; ELit 141776; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77)); ELit 0; EVar 68; ELit 1152921504606846976; ELit 0; EVar 15; EVar 16; EVar 17; EVar 18; EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 77)) (ELit (-8)); EVar 20; EVar 21; EVar 78; EVar 75; EVar 24; EVar 75; EVar 76; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77)); a_off := 0 |} 8 (EVar 76); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -312 |} 8 (EVar 76); KWord {| a_base := EVar 2; a_off := -232 |} 8 (EVar 68); KRange (EVar 68) 4096 140737488355328; KAlign (EVar 68) 8; KWr {| a_base := EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77)); a_off := 0 |} (ELit 8); KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77)); a_off := 0 |} (ELit 8); KRange (EAlu Instr.ALU_SLTU (EVar 78) (EVar 75)) 1 1; KRange (EVar 78) 0 300; KRange (EVar 75) 0 300; KRange (EVar 77) 0 299; KRange (EVar 76) 0 18446744073709551615] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141644 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141760 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141760 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ul3c.

Module LibSegZ_d5ul3x.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141644; 141792].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; (EMd Instr.M_MUL (ELit 8) (EVar 77)); EVar 20; EVar 21; EVar 78; EVar 77; EVar 24; EVar 75; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-312)) 8 (EVar 76);
   KWord (SA (EVar 2) (-232)) 8 (EVar 68);
   KRange (EVar 68) 4096 140737488355328;
   KAlign (EVar 68) 8;
   KWr (SA (EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77))) 0) (ELit 8);
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77))) 0) (ELit 8);
   KRange (EAlu Instr.ALU_SLTU (EVar 78) (EVar 75)) 0 0;
   KRange (EVar 78) 0 300;
   KRange (EVar 75) 0 300;
   KRange (EVar 77) 0 299;
   KRange (EVar 76) 0 18446744073709551615].
Definition ss0 : sym_state := SS 141760 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77))), (0), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77))), (0), 8)].
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141644; 141792])], (93, SS 141792 [ELit 0; ELit 141776; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77)); ELit 0; EVar 68; ELit 1152921504606846976; ELit 0; EVar 15; EVar 16; EVar 17; EVar 18; EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 77)) (ELit (-8)); EVar 20; EVar 21; EVar 78; EVar 75; EVar 24; EVar 75; EVar 76; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77)); a_off := 0 |} 8 (EVar 76); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -312 |} 8 (EVar 76); KWord {| a_base := EVar 2; a_off := -232 |} 8 (EVar 68); KRange (EVar 68) 4096 140737488355328; KAlign (EVar 68) 8; KWr {| a_base := EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77)); a_off := 0 |} (ELit 8); KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EAlu Instr.ALU_ADD (EVar 68) (EMd Instr.M_MUL (ELit 8) (EVar 77)); a_off := 0 |} (ELit 8); KRange (EAlu Instr.ALU_SLTU (EVar 78) (EVar 75)) 0 0; KRange (EVar 78) 0 300; KRange (EVar 75) 0 300; KRange (EVar 77) 0 299; KRange (EVar 76) 0 18446744073709551615] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141792 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141760 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141760 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ul3x.

Module LibSegZ_d5upre.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141644; 141792].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 67; EVar 78; EVar 75; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-152)) 8 (EVar 66);
   KWord (SA (EVar 2) (-144)) 8 (EVar 67);
   KRange (EVar 66) 4096 140737488355328;
   KAlign (EVar 66) 8;
   KWord (SA (EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 78))) 0) 8 (EVar 74);
   KRange (EVar 74) 0 18446744073709551615;
   KRange (EAlu Instr.ALU_SLTU (EVar 78) (EVar 75)) 1 1;
   KRange (EVar 78) 0 300;
   KRange (EVar 75) 0 300;
   KRange (EVar 67) 1 301].
Definition ss0 : sym_state := SS 141596 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141644; 141792])], (93, SS 141644 [ELit 0; ELit 141608; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 1152921504606846976; EMd Instr.M_MUL (ELit 8) (EVar 75); EMd Instr.M_MUL (ELit 8) (EVar 67); ELit 1152921504606846976; ELit 0; EVar 15; EVar 16; EVar 17; EVar 18; EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-8)) (EVar 67)) (EMd Instr.M_MUL (ELit 8) (EVar 75)); EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 67)) (ELit 1152921504606846976); EVar 67; EVar 78; EVar 75; EVar 74; EVar 25; EVar 26; EMd Instr.M_MUL (ELit (-1)) (EVar 67); EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 67); KRange (EVar 66) 4096 140737488355328; KAlign (EVar 66) 8; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 78)); a_off := 0 |} 8 (EVar 74); KRange (EVar 74) 0 18446744073709551615; KRange (EAlu Instr.ALU_SLTU (EVar 78) (EVar 75)) 1 1; KRange (EVar 78) 0 300; KRange (EVar 75) 0 300; KRange (EVar 67) 1 301] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141644 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141596 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5upre.

Module LibSegZ_d5uprx.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141644; 141792].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 67; EVar 78; EVar 75; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-152)) 8 (EVar 66);
   KWord (SA (EVar 2) (-144)) 8 (EVar 67);
   KRange (EVar 66) 4096 140737488355328;
   KAlign (EVar 66) 8;
   KRange (EAlu Instr.ALU_SLTU (EVar 78) (EVar 75)) 0 0;
   KRange (EVar 78) 0 300;
   KRange (EVar 75) 0 300;
   KRange (EVar 67) 1 301].
Definition ss0 : sym_state := SS 141596 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141644; 141792])], (93, SS 141792 [ELit 0; ELit 141608; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 66) (EMd Instr.M_MUL (ELit 8) (EVar 78)); ELit 0; EVar 66; ELit 1152921504606846976; ELit 0; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 67; EVar 78; EVar 75; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EVar 66); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 67); KRange (EVar 66) 4096 140737488355328; KAlign (EVar 66) 8; KRange (EAlu Instr.ALU_SLTU (EVar 78) (EVar 75)) 0 0; KRange (EVar 78) 0 300; KRange (EVar 75) 0 300; KRange (EVar 67) 1 301] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141792 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141596 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5uprx.

Module LibSegZ_d5ut0d.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141904; 259876].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-280)) 1 (EVar 41);
   KWord (SA (EVar 2) (-264)) 8 (EVar 42);
   KWord (SA (EVar 2) (-256)) 8 (EVar 43);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1;
   KRange (EVar 42) 1 4096;
   KRange (EVar 43) 4096 140737488355328].
Definition ss0 : sym_state := SS 141872 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141904; 259876])], (93, SS 259876 [ELit 0; ELit 141904; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 43; EMd Instr.M_MUL (ELit 8) (EVar 42); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -280 |} 1 (EVar 41); KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -256 |} 8 (EVar 43); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1; KRange (EVar 42) 1 4096; KRange (EVar 43) 4096 140737488355328] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 259876 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141872 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141872 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ut0d.

Module LibSegZ_d5ut0i.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141904; 259876].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-280)) 1 (EVar 41);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0].
Definition ss0 : sym_state := SS 141872 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141904; 259876])], (93, SS 141904 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 0; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -280 |} 1 (EVar 41); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141904 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141872 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141872 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ut0i.

Module LibSegZ_d5ut1d.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142208; 259876].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-216)) 1 (EVar 41);
   KWord (SA (EVar 2) (-200)) 8 (EVar 42);
   KWord (SA (EVar 2) (-192)) 8 (EVar 43);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1;
   KRange (EVar 42) 1 4096;
   KRange (EVar 43) 4096 140737488355328].
Definition ss0 : sym_state := SS 141904 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 142208; 259876])], (93, SS 259876 [ELit 0; ELit 141936; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 43; EMd Instr.M_MUL (ELit 8) (EVar 42); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -216 |} 1 (EVar 41); KWord {| a_base := EVar 2; a_off := -200 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -192 |} 8 (EVar 43); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1; KRange (EVar 42) 1 4096; KRange (EVar 43) 4096 140737488355328] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 259876 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141904 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141904 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ut1d.

Module LibSegZ_d5ut1i.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142208; 259876].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-216)) 1 (EVar 41);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0].
Definition ss0 : sym_state := SS 141904 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 142208; 259876])], (93, SS 142208 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 0; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -216 |} 1 (EVar 41); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 142208 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141904 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141904 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ut1i.

Module LibSegZ_d5ut1j.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142208].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16].
Definition ss0 : sym_state := SS 141936 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 142208])], (93, SS 142208 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 142208 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141936 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141936 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ut1j.

Module LibSegZ_d5ut2d.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142240; 259876].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-184)) 1 (EVar 41);
   KWord (SA (EVar 2) (-168)) 8 (EVar 42);
   KWord (SA (EVar 2) (-160)) 8 (EVar 43);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1;
   KRange (EVar 42) 1 4096;
   KRange (EVar 43) 4096 140737488355328].
Definition ss0 : sym_state := SS 142208 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 142240; 259876])], (93, SS 259876 [ELit 0; ELit 142240; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 43; EMd Instr.M_MUL (ELit 8) (EVar 42); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -184 |} 1 (EVar 41); KWord {| a_base := EVar 2; a_off := -168 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 43); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1; KRange (EVar 42) 1 4096; KRange (EVar 43) 4096 140737488355328] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 259876 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 142208 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 142208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ut2d.

Module LibSegZ_d5ut2i.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142240; 259876].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-184)) 1 (EVar 41);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0].
Definition ss0 : sym_state := SS 142208 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 142240; 259876])], (93, SS 142240 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 0; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -184 |} 1 (EVar 41); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 142240 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 142208 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 142208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ut2i.

Module LibSegZ_d5ut3d.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142272; 259876].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-136)) 1 (EVar 41);
   KWord (SA (EVar 2) (-120)) 8 (EVar 42);
   KWord (SA (EVar 2) (-112)) 8 (EVar 43);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1;
   KRange (EVar 42) 1 4096;
   KRange (EVar 43) 4096 140737488355328].
Definition ss0 : sym_state := SS 142240 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 142272; 259876])], (93, SS 259876 [ELit 0; ELit 142272; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 43; EMd Instr.M_MUL (ELit 8) (EVar 42); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -136 |} 1 (EVar 41); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 42); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 43); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 1 1; KRange (EVar 42) 1 4096; KRange (EVar 43) 4096 140737488355328] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 259876 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 142240 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 142240 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ut3d.

Module LibSegZ_d5ut3i.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [142272; 259876].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-136)) 1 (EVar 41);
   KRange (EVar 41) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0].
Definition ss0 : sym_state := SS 142240 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 142272; 259876])], (93, SS 142272 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 0; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -136 |} 1 (EVar 41); KRange (EVar 41) 0 255; KRange (EAlu Instr.ALU_AND (EVar 41) (ELit 1)) 0 0] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 142272 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 142240 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 142240 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ut3i.

Module LibSegZ_d5ux1.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [137916].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16].
Definition ss0 : sym_state := SS 141792 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 137916])], (93, SS 137916 [ELit 0; ELit 141800; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 35; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 137916 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141792 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141792 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ux1.

Module LibSegZ_d5ux2n.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141872; 143680].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-320)) 8 (EVar 62);
   KWord (SA (EVar 2) (-328)) 8 (EVar 61);
   KWord (SA (EVar 2) (-336)) 8 (ELit 0);
   KRange (EVar 35) 1048576 140737488355296;
   KAlign (EVar 35) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 35) 0) (ELit 32);
   KWord (SA (EVar 35) 0) 1 (EVar 69);
   KRange (EVar 69) 0 255;
   KWr (SA (EVar 35) 0) (ELit 32);
   KRange (EVar 61) 0 1;
   KRange (EVar 62) 0 2].
Definition ss0 : sym_state := SS 141800 regs0 [] kn0 NX0.
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
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141872; 143680])], (93, SS 141872 [ELit 0; EVar 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 35; ELit 0; EMd Instr.M_MUL (ELit 2) (EVar 61); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 62; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 35; a_off := 0 |} 1 (EAlu Instr.ALU_OR (EAlu Instr.ALU_AND (EVar 69) (ELit 253)) (EMd Instr.M_MUL (ELit 2) (EVar 61))); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -320 |} 8 (EVar 62); KWord {| a_base := EVar 2; a_off := -328 |} 8 (EVar 61); KWord {| a_base := EVar 2; a_off := -336 |} 8 (ELit 0); KRange (EVar 35) 1048576 140737488355296; KAlign (EVar 35) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 35; a_off := 0 |} (ELit 32); KRange (EVar 69) 0 255; KWr {| a_base := EVar 35; a_off := 0 |} (ELit 32); KRange (EVar 61) 0 1; KRange (EVar 62) 0 2] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141872 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141800 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141800 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5ux2n.

Module LibSegZ_d5uzln.
(* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(140532, 526%nat) ; (137848, 17%nat) ; (139480, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [141360; 141384].
Definition STOPS1 : list Z := [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; (EAlu Instr.ALU_ADD (EVar 2) (ELit (-352))); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 18446744073709551615; EVar 20; EVar 21; EVar 75; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 1048928 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-232)) 8 (EVar 40);
   KWord (SA (EVar 2) (-224)) 8 (EVar 70);
   KRange (EVar 40) 4096 140737488355328;
   KAlign (EVar 40) 8;
   KDisj (SA (EVar 2) (-352)) (ELit 352) (SA (EVar 40) 0) (ELit 64);
   KWr (SA (EVar 40) 0) (ELit 64);
   KRange (EVar 75) 0 7;
   KRange (EVar 70) 0 300].
Definition ss0 : sym_state := SS 141360 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 40, (0), ELit 64)].
Definition F0L : list SR.region := [(EVar 40, (0), 64)].
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
  (SS 141380 [ELit 0; ELit 141372; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 40) (EMd Instr.M_MUL (ELit 8) (EVar 75)); ELit 0; EVar 40; ELit 1152921504606846976; ELit 0; EVar 15; EVar 16; EVar 17; EVar 18; ELit 18446744073709551615; EVar 20; EVar 21; EAlu Instr.ALU_ADD (EVar 75) (ELit (-1)); EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EAlu Instr.ALU_ADD (EVar 40) (EMd Instr.M_MUL (ELit 8) (EVar 75)); a_off := 0 |} 8 (ELit 0); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -232 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -224 |} 8 (EVar 70); KRange (EVar 40) 4096 140737488355328; KAlign (EVar 40) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 40; a_off := 0 |} (ELit 64); KWr {| a_base := EVar 40; a_off := 0 |} (ELit 64); KRange (EVar 75) 0 7; KRange (EVar 70) 0 300] 80).

(* [comment removed for export] *)
Definition ce2 : expr := EVar 75.
Definition arms2 := Eval vm_compute in (SGP.case_arms s1 ce2 (0)).
Definition lo2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition hi2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

(* [comment removed for export] *)
Definition ex3 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141360; 141384])], (93, SS 141384 [ELit 0; ELit 141372; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 40) (EMd Instr.M_MUL (ELit 8) (EVar 75)); ELit 0; EVar 40; ELit 1152921504606846976; ELit 0; EVar 15; EVar 16; EVar 17; EVar 18; ELit 18446744073709551615; EVar 20; EVar 21; EAlu Instr.ALU_ADD (EVar 75) (ELit (-1)); EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 75) 0 0; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 40) (EMd Instr.M_MUL (ELit 8) (EVar 75)); a_off := 0 |} 8 (ELit 0); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -232 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -224 |} 8 (EVar 70); KRange (EVar 40) 4096 140737488355328; KAlign (EVar 40) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 40; a_off := 0 |} (ELit 64); KWr {| a_base := EVar 40; a_off := 0 |} (ELit 64); KRange (EVar 75) 0 7; KRange (EVar 70) 0 300] 80))).
Definition s3 : sym_state := snd (snd ex3).

(* [comment removed for export] *)
Definition ex4 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [143880; 139548; 136232; 136420; 259876; 142636; 142956; 143208; 137916; 143680; 260020; 142328; 141596; 141644; 141360; 141384; 141360; 141384])], (93, SS 141360 [ELit 0; ELit 141372; EAlu Instr.ALU_ADD (EVar 2) (ELit (-352)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EAlu Instr.ALU_ADD (EVar 40) (EMd Instr.M_MUL (ELit 8) (EVar 75)); ELit 0; EVar 40; ELit 1152921504606846976; ELit 0; EVar 15; EVar 16; EVar 17; EVar 18; ELit 18446744073709551615; EVar 20; EVar 21; EAlu Instr.ALU_ADD (EVar 75) (ELit (-1)); EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KRange (EVar 75) 1 7; KWord {| a_base := EAlu Instr.ALU_ADD (EVar 40) (EMd Instr.M_MUL (ELit 8) (EVar 75)); a_off := 0 |} 8 (ELit 0); KRange (EVar 2) 1048928 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -352 |} (ELit 352); KWord {| a_base := EVar 2; a_off := -232 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -224 |} 8 (EVar 70); KRange (EVar 40) 4096 140737488355328; KAlign (EVar 40) 8; KDisj {| a_base := EVar 2; a_off := -352 |} (ELit 352) {| a_base := EVar 40; a_off := 0 |} (ELit 64); KWr {| a_base := EVar 40; a_off := 0 |} (ELit 64); KRange (EVar 75) 0 7; KRange (EVar 70) 0 300] 80))).
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
Definition ps0 : SR.post_spec := SR.PS 141360 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 141384 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 141360 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := ub0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 141360 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegZ_d5uzln.
