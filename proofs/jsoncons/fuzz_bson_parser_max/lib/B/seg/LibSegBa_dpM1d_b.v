(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_5a10ba_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_5a10ba_b.ITR.
Definition IT : itab := SegItab_Ba_5a10ba_b.IT.
Definition ENDS : list Z := [687352].
Definition STOPS1 : list Z := [687352] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 31; ELit 1293512; EVar 110; EVar 111; EVar 112; EVar 113; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6896960; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-16)) (ELit 16);
   KUnk (SA (EVar 2) (-16)) (ELit 16);
   KImg 65536 1282048;
   KRange (EVar 33) 140735332552704 140737488355311;
   KRange (EVar 34) 0 131071;
   KDisj (SA (EVar 2) (-16)) (ELit 16) (SA (EVar 33) 0) (EAlu Instr.ALU_ADD (EVar 34) (ELit 1));
   KWord (SA (ELit 0) (2147468024)) 8 (ELit 0);
   KWr (SA (ELit 0) (1293544)) (ELit 8);
   KWr (SA (ELit 0) (1293552)) (ELit 8);
   KWr (SA (ELit 0) (1293568)) (ELit 8);
   KWord (SA (ELit 0) (1293600)) 8 (ELit 6898968);
   KWord (SA (ELit 0) (1293608)) 8 (ELit 0);
   KWord (SA (ELit 0) (6896960)) 8 (EVar 40);
   KWord (SA (EVar 2) (40)) 8 (EVar 40);
   KWord (SA (EVar 2) (104)) 8 (ELit 1183112);
   KWord (SA (EVar 2) (96)) 8 (ELit 1);
   KWord (SA (EVar 2) (88)) 8 (ELit 31);
   KWord (SA (EVar 2) (80)) 8 (ELit 31);
   KWord (SA (EVar 2) (72)) 8 (ELit 1293512);
   KWord (SA (EVar 2) (64)) 8 (ELit 1);
   KWord (SA (EVar 2) (56)) 8 (ELit 1);
   KWord (SA (EVar 2) (48)) 8 (EVar 22);
   KWord (SA (EVar 2) (168)) 8 (ELit 415800);
   KWord (SA (EVar 2) (160)) 8 ((EAlu Instr.ALU_ADD (EVar 2) (ELit (2304))));
   KWord (SA (EVar 2) (152)) 8 (ELit 31);
   KWord (SA (EVar 2) (144)) 8 (ELit 137179);
   KWord (SA (EVar 2) (136)) 8 (ELit 1293512);
   KWord (SA (EVar 2) (128)) 8 (ELit 1);
   KWord (SA (EVar 2) (120)) 8 (ELit 1);
   KWord (SA (ELit 0) (1309752)) 8 (ELit 2147450880);
   KWord (SA (EVar 2) (2296)) 8 (ELit 687352);
   KWord (SA (EVar 2) (2288)) 8 (EVar 8);
   KWord (SA (EVar 2) (2280)) 8 (EVar 9);
   KWord (SA (EVar 2) (2272)) 8 (EVar 18);
   KWord (SA (EVar 2) (2264)) 8 (EVar 19);
   KWord (SA (EVar 2) (2256)) 8 (EVar 20);
   KWord (SA (EVar 2) (2248)) 8 (EVar 21)].
Definition ss0 : sym_state := SS 1180260 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1293544), ELit 8); (ELit 0, (1293552), ELit 8); (ELit 0, (1293568), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1293544), 8); (ELit 0, (1293552), 8); (ELit 0, (1293568), 8)].
Definition BF : nat := 200000.
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
  (([SGA.AStep (SR.SBlock [687352; 687352])], (93, SS 687352 [ELit 0; ELit 687352; EAlu Instr.ALU_ADD (EVar 2) (ELit 2304); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 1; ELit 2147468027; ELit 2147468031; ELit 137209; ELit 0; ELit 0; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := ELit 0; a_off := 1293568 |} 8 (ELit 6898968); KWord {| a_base := ELit 0; a_off := 1293552 |} 8 (ELit 6898968); KWord {| a_base := ELit 0; a_off := 1293544 |} 8 (ELit 6898968); KRange (EVar 2) 140735332552704 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -16 |} (ELit 16); KUnk {| a_base := EVar 2; a_off := -16 |} (ELit 16); KImg 65536 1282048; KRange (EVar 33) 140735332552704 140737488355311; KRange (EVar 34) 0 131071; KDisj {| a_base := EVar 2; a_off := -16 |} (ELit 16) {| a_base := EVar 33; a_off := 0 |} (EAlu Instr.ALU_ADD (EVar 34) (ELit 1)); KWord {| a_base := ELit 0; a_off := 2147468024 |} 8 (ELit 0); KWr {| a_base := ELit 0; a_off := 1293544 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293552 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293568 |} (ELit 8); KWord {| a_base := ELit 0; a_off := 1293600 |} 8 (ELit 6898968); KWord {| a_base := ELit 0; a_off := 1293608 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6896960 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := 40 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := 104 |} 8 (ELit 1183112); KWord {| a_base := EVar 2; a_off := 96 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := 88 |} 8 (ELit 31); KWord {| a_base := EVar 2; a_off := 80 |} 8 (ELit 31); KWord {| a_base := EVar 2; a_off := 72 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := 64 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := 56 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := 48 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := 168 |} 8 (ELit 415800); KWord {| a_base := EVar 2; a_off := 160 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 2304)); KWord {| a_base := EVar 2; a_off := 152 |} 8 (ELit 31); KWord {| a_base := EVar 2; a_off := 144 |} 8 (ELit 137179); KWord {| a_base := EVar 2; a_off := 136 |} 8 (ELit 1293512); KWord {| a_base := EVar 2; a_off := 128 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := 120 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 1309752 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := 2296 |} 8 (ELit 687352); KWord {| a_base := EVar 2; a_off := 2288 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := 2280 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := 2272 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := 2264 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := 2256 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := 2248 |} 8 (EVar 21)] 140))).
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
Definition ps0 : SR.post_spec := SR.PS 687352 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_5a10ba_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1180260 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_5a10ba_b.IT SegItab_Ba_5a10ba_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 1180260 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
