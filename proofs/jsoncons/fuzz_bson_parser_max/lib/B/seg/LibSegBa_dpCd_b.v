(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_757f31_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_757f31_b.ITR.
Definition IT : itab := SegItab_Ba_757f31_b.IT.
Definition ENDS : list Z := [688024].
Definition STOPS1 : list Z := [688024] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1; ELit 1293752; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6896960; EVar 122; ELit 85516; ELit 1; EVar 125; ELit 1; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-2016)) (ELit 2160);
   KUnk (SA (EVar 2) (-2016)) (ELit 2160);
   KImg 65536 1282048;
   KWr (SA (ELit 0) (1293752)) (ELit 4);
   KWr (SA (ELit 0) (1293784)) (ELit 8);
   KWr (SA (ELit 0) (1293792)) (ELit 8);
   KWr (SA (ELit 0) (1293808)) (ELit 8);
   KWord (SA (ELit 0) (1293840)) 8 (ELit 6898976);
   KWord (SA (ELit 0) (1293848)) 8 (ELit 1024);
   KWord (SA (ELit 0) (6896960)) 8 (EVar 40);
   KWord (SA (EVar 2) (40)) 8 (EVar 40);
   KWord (SA (EVar 2) (104)) 8 (ELit 1183548);
   KWord (SA (EVar 2) (96)) 8 (ELit 6896960);
   KWord (SA (EVar 2) (88)) 8 (ELit 1);
   KWord (SA (EVar 2) (80)) 8 (ELit 85516);
   KWord (SA (EVar 2) (72)) 8 (ELit 1);
   KWord (SA (EVar 2) (64)) 8 (ELit 0);
   KWord (SA (EVar 2) (56)) 8 (ELit 85517);
   KWord (SA (EVar 2) (48)) 8 (ELit 1);
   KWord (SA (EVar 2) (120)) 8 (EVar 40);
   KWord (SA (EVar 2) (136)) 8 (ELit 1182896);
   KWord (SA (EVar 2) (128)) 8 (ELit 1293752);
   KWord (SA (ELit 0) (1313049)) 1 (ELit 1);
   KWord (SA (ELit 0) (1283272)) 8 (ELit 1218816);
   KWord (SA (EVar 2) (200)) 8 (ELit 1184784);
   KWord (SA (EVar 2) (192)) 8 (ELit 37);
   KWord (SA (EVar 2) (184)) 8 (ELit 2147483647);
   KWord (SA (EVar 2) (176)) 8 (ELit 2147483646);
   KWord (SA (EVar 2) (168)) 8 (ELit 1);
   KWord (SA (EVar 2) (160)) 8 (ELit 1293752);
   KWord (SA (EVar 2) (152)) 8 (ELit 85517);
   KWord (SA (EVar 2) (304)) 8 (ELit 6896960);
   KWord (SA (EVar 2) (640)) 8 (EVar 40);
   KWord (SA (EVar 2) (744)) 8 (ELit 1184288);
   KWord (SA (EVar 2) (736)) 8 (ELit 1293752);
   KWord (SA (EVar 2) (728)) 8 (ELit 85514);
   KWord (SA (EVar 2) (720)) 8 (ELit 6896960);
   KWord (SA (EVar 2) (712)) 8 (ELit 1);
   KWord (SA (EVar 2) (704)) 8 (ELit 0);
   KWord (SA (EVar 2) (696)) 8 (ELit 5);
   KWord (SA (EVar 2) (688)) 8 (EVar 22);
   KWord (SA (EVar 2) (680)) 8 (EVar 23);
   KWord (SA (EVar 2) (672)) 8 (EVar 24);
   KWord (SA (EVar 2) (664)) 8 (EVar 25);
   KWord (SA (EVar 2) (656)) 8 (EVar 26);
   KWord (SA (EVar 2) (648)) 8 (EVar 27);
   KWord (SA (ELit 0) (1293752)) 4 (ELit 5);
   KWord (SA (EVar 2) (1056)) 8 (EVar 40);
   KWord (SA (EVar 2) (1112)) 8 (ELit 424640);
   KWord (SA (EVar 2) (1104)) 8 (ELit 85514);
   KWord (SA (EVar 2) (1096)) 8 (ELit 1293752);
   KWord (SA (EVar 2) (1088)) 8 ((EAlu Instr.ALU_ADD (EVar 2) (ELit (1240))));
   KWord (SA (EVar 2) (1080)) 8 (EVar 19);
   KWord (SA (EVar 2) (1072)) 8 (EVar 20);
   KWord (SA (EVar 2) (1064)) 8 (EVar 21);
   KWord (SA (EVar 2) (1160)) 8 (ELit 421712);
   KWord (SA (EVar 2) (1152)) 8 (ELit 85514);
   KWord (SA (EVar 2) (1144)) 8 ((EAlu Instr.ALU_ADD (EVar 2) (ELit (1240))));
   KWord (SA (EVar 2) (1136)) 8 (EVar 18);
   KWord (SA (EVar 2) (1208)) 8 (ELit 688024);
   KWord (SA (EVar 2) (1200)) 8 (EVar 8);
   KWord (SA (EVar 2) (1192)) 8 (EVar 9)].
Definition ss0 : sym_state := SS 1180260 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-2016), ELit 2160); (ELit 0, (1293752), ELit 4); (ELit 0, (1293784), ELit 8); (ELit 0, (1293792), ELit 8); (ELit 0, (1293808), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-2016), 2160); (ELit 0, (1293752), 4); (ELit 0, (1293784), 8); (ELit 0, (1293792), 8); (ELit 0, (1293808), 8)].
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
  (([SGA.AStep (SR.SBlock [688024; 688024])], (93, SS 688024 [ELit 0; ELit 688024; EAlu Instr.ALU_ADD (EVar 2) (ELit 1216); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 2; EVar 40; EVar 40; ELit 6898976; ELit 0; ELit 0; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := ELit 0; a_off := 1293752 |} 4 (ELit 5); KWord {| a_base := ELit 0; a_off := 1293792 |} 8 (ELit 6898976); KWord {| a_base := EVar 2; a_off := 64 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := 72 |} 8 (ELit 85516); KWord {| a_base := EVar 2; a_off := 80 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := 88 |} 8 (ELit 85517); KWord {| a_base := EVar 2; a_off := 96 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 104 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := 112 |} 8 (ELit 85517); KWord {| a_base := EVar 2; a_off := 120 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 128 |} 8 (ELit 1293752); KWord {| a_base := EVar 2; a_off := 136 |} 8 (ELit 1182924); KWord {| a_base := ELit 0; a_off := 1293808 |} 8 (ELit 6898976); KWord {| a_base := ELit 0; a_off := 1293784 |} 8 (ELit 6900000); KRange (EVar 2) 140735332552704 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -2016 |} (ELit 2160); KUnk {| a_base := EVar 2; a_off := -2016 |} (ELit 2080); KImg 65536 1282048; KWr {| a_base := ELit 0; a_off := 1293752 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 1293784 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293792 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1293808 |} (ELit 8); KWord {| a_base := ELit 0; a_off := 1293840 |} 8 (ELit 6898976); KWord {| a_base := ELit 0; a_off := 1293848 |} 8 (ELit 1024); KWord {| a_base := ELit 0; a_off := 6896960 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := 40 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := 56 |} 8 (ELit 85517); KWord {| a_base := EVar 2; a_off := 48 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 1313049 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1283272 |} 8 (ELit 1218816); KWord {| a_base := EVar 2; a_off := 200 |} 8 (ELit 1184784); KWord {| a_base := EVar 2; a_off := 192 |} 8 (ELit 37); KWord {| a_base := EVar 2; a_off := 184 |} 8 (ELit 2147483647); KWord {| a_base := EVar 2; a_off := 176 |} 8 (ELit 2147483646); KWord {| a_base := EVar 2; a_off := 168 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := 160 |} 8 (ELit 1293752); KWord {| a_base := EVar 2; a_off := 152 |} 8 (ELit 85517); KWord {| a_base := EVar 2; a_off := 304 |} 8 (ELit 6896960); KWord {| a_base := EVar 2; a_off := 640 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := 744 |} 8 (ELit 1184288); KWord {| a_base := EVar 2; a_off := 736 |} 8 (ELit 1293752); KWord {| a_base := EVar 2; a_off := 728 |} 8 (ELit 85514); KWord {| a_base := EVar 2; a_off := 720 |} 8 (ELit 6896960); KWord {| a_base := EVar 2; a_off := 712 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := 704 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := 696 |} 8 (ELit 5); KWord {| a_base := EVar 2; a_off := 688 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := 680 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := 672 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := 664 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := 656 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := 648 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := 1056 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := 1112 |} 8 (ELit 424640); KWord {| a_base := EVar 2; a_off := 1104 |} 8 (ELit 85514); KWord {| a_base := EVar 2; a_off := 1096 |} 8 (ELit 1293752); KWord {| a_base := EVar 2; a_off := 1088 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 1240)); KWord {| a_base := EVar 2; a_off := 1080 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := 1072 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := 1064 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := 1160 |} 8 (ELit 421712); KWord {| a_base := EVar 2; a_off := 1152 |} 8 (ELit 85514); KWord {| a_base := EVar 2; a_off := 1144 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit 1240)); KWord {| a_base := EVar 2; a_off := 1136 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := 1208 |} 8 (ELit 688024); KWord {| a_base := EVar 2; a_off := 1200 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := 1192 |} 8 (EVar 9)] 140))).
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
Definition ps0 : SR.post_spec := SR.PS 688024 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_757f31_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1180260 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_757f31_b.IT SegItab_Ba_757f31_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 1180260 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
