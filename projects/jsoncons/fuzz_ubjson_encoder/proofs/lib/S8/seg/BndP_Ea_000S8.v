(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ea0PlanKit Ea0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndT_Ea_000S8 BndT_Ea_001S8.

Module LibSegEa_aapL0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_583ad2.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_583ad2.IT.
Definition ENDS : list Z := [880420; 880460].
Definition STOPS1 : list Z := [880420; 880460] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 43; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$24'&9$24#1#1#1'$24#1;#8000001!$:#8,8$22'$22##8000000'$2;#1#4004000"%pstring).
Definition ss0 : sym_state := SS 880320 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-80), ELit 80)].
Definition F0L : list SR.region := [((EVar 2), (-80), 80)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=6?24#=6?4<#=6?24#=6?4<#5;#=6?48,20#$1+$2-50$3$4$5$6$7$:$2;#1++@-1$22@#2&6$24#1-1$<$=$>$?$10$11$22$13$14$15$16+@#2&6$24#1-1$18$19$1:$1;$1<$1=$1>$1?,,1:!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$24'&9$24#1#1#1'$24#1;#8000001!$:#8,8$22'$22##8000000'$2;#1#4004000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=6?24#=6?4<#=6?24#=6?4<#5:#=6?4<,20#$1+$2-50$3$4$5$6$7$:$2;#1++@-1$22@#2&6$24#1-1$<$=$>$?$10$11$22$13$14$15$16+@#2&6$24#1-1$18$19$1:$1;$1<$1=$1>$1?,,1;'&4++@-1$22@#2&6$24#1-1$2;#1#1!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$24'&9$24#1#1#1'$24#1;#8000001!$:#8,8$22'$22##8000000'$2;#1#4004000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=6?24#=6?4<#=6?24#=6?4<#5:#=6?24,20#$1+$2-50$3$4$5$6$7$:$2;#1++@-1$22@#2&6$24#1-1$<$=$>$?$10$11$22$13$14$15$16+@#2&6$24#1-1$18$19$1:$1;$1<$1=$1>$1?,,1;'&4++@-1$22@#2&6$24#1-1$2;##!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$24'&9$24#1#1#1'$24#1;#8000001!$:#8,8$22'$22##8000000'$2;#1#4004000,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PEnd 0))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 880420 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 880460 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_583ad2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 880320 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_583ad2.IT BndT_Ea_000S8.SegItab_Ea_583ad2.IT_sound BF NX0 BR XSTEP F0 PSS plan 880320 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aapL0.

Module LibSegEa_aapML.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_583ad2.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_583ad2.IT.
Definition ENDS : list Z := [880784].
Definition STOPS1 : list Z := [880784] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$:$9$36$;$<$=$>$?$10$11$12$13$23$15$26$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34!$2-50,8$35!$:#,1$21'$21##??'&9$21#1#1#1'$26#1#4004000'$23#1000#800000000000(+$23$26##1)+$23$26##1$:##18)+$23$26##1$2-50#50"%pstring).
Definition ss0 : sym_state := SS 880700 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (8), ELit 8); ((EAlu Instr.ALU_ADD (EVar 35) (EVar 38)), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 10), (8), 8); ((EAlu Instr.ALU_ADD (EVar 35) (EVar 38)), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=7090#=7090#5=#=7090,20#$2<$2$3$4$5$6$7$2=$2>$:$;$<$=$>$?$10$11$2?$30$31$32$33$34$35$19$1:$1;$1<$1=$1>$1?,,1;!+$23$26#,1#!$:#8,8$26'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34!$2-50,8$35!$:#,1$21'$21##??'&9$21#1#1#1'$26#1#4004000'$23#1000#800000000000(+$23$26##1)+$23$26##1$:##18)+$23$26##1$2-50#50,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 880784 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_583ad2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 880700 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_583ad2.IT BndT_Ea_000S8.SegItab_Ea_583ad2.IT_sound BF NX0 BR XSTEP F0 PSS plan 880700 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aapML.

Module LibSegEa_aapMS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_583ad2.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_583ad2.IT.
Definition ENDS : list Z := [880784].
Definition STOPS1 : list Z := [880784] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$:$9$36$;$<$=$>$?$10$11$12$13+$:#1$15$26$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34!$2-50,8$35!$:#,1$21'$21##??'&9$21#1##'$26#1#16"%pstring).
Definition ss0 : sym_state := SS 880700 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 10), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=7090#=7090#5=#=7090,20#$2<$2$3$4$5$6$7$2=$2>$:$;$<$=$>$?$10$11$2?$30$31$32$33$34$35$19$1:$1;$1<$1=$1>$1?,,16!+$:$26#1,1#!$:#,1@#2$26'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34!$2-50,8$35'$21##??'&9$21#1##'$26#1#16,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 880784 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_583ad2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 880700 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_583ad2.IT BndT_Ea_000S8.SegItab_Ea_583ad2.IT_sound BF NX0 BR XSTEP F0 PSS plan 880700 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aapMS.

Module LibSegEa_aapS0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_583ad2.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_583ad2.IT.
Definition ENDS : list Z := [880420; 880460].
Definition STOPS1 : list Z := [880420; 880460] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 43; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##2<'&9$21#1##!$:#,8$24'&9$24#1##'&6@#100000000000000$24#39##16'$2;#1#4004000"%pstring).
Definition ss0 : sym_state := SS 880320 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-80), ELit 80)].
Definition F0L : list SR.region := [((EVar 2), (-80), 80)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=6?24#=6?4<#=6?24#=6?4<#5;#=6?20,20#$1+$2-50$3$4$5$6$7$:$2;#+@-1&6@#100000000000000$24#39#16$<$=$>$?$10$11&6@#100000000000000$24#39$13$14$15$16#16$18$19$1:$1;$1<$1=$1>$1?,,18!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##2<'&9$21#1##!$:#,8$24'&9$24#1##'&6@#100000000000000$24#39##16'$2;#1#4004000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=6?24#=6?4<#=6?24#=6?4<#5:#=6?4<,20#$1+$2-50$3$4$5$6$7$:$2;#+@-1&6@#100000000000000$24#39#16$<$=$>$?$10$11&6@#100000000000000$24#39$13$14$15$16#16$18$19$1:$1;$1<$1=$1>$1?,,19'&4+@-1&6@#100000000000000$24#39#16$2;#1#1!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##2<'&9$21#1##!$:#,8$24'&9$24#1##'&6@#100000000000000$24#39##16'$2;#1#4004000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=6?24#=6?4<#=6?24#=6?4<#5:#=6?24,20#$1+$2-50$3$4$5$6$7$:$2;#+@-1&6@#100000000000000$24#39#16$<$=$>$?$10$11&6@#100000000000000$24#39$13$14$15$16#16$18$19$1:$1;$1<$1=$1>$1?,,19'&4+@-1&6@#100000000000000$24#39#16$2;##!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##2<'&9$21#1##!$:#,8$24'&9$24#1##'&6@#100000000000000$24#39##16'$2;#1#4004000,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PEnd 0))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 880420 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 880460 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_583ad2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 880320 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_583ad2.IT BndT_Ea_000S8.SegItab_Ea_583ad2.IT_sound BF NX0 BR XSTEP F0 PSS plan 880320 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aapS0.

Module LibSegEa_ab10BZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_e1a828.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_e1a828.IT.
Definition ENDS : list Z := [747732; 747800; 747640].
Definition STOPS1 : list Z := [747732; 747800; 747640] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KRange (EVar 36) 0 18446744073709551615;
   KWord (SA (EVar 33) 0) 1 (EVar 37);
   KRange (EVar 37) 0 255;
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 1)].
Definition ss0 : sym_state := SS 747576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4+$25-30#:#1#1'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4+$25-30#:##'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;683<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'&4+$25-30#:#1#1'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'&4+$25-30#:##'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6840,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6860,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,9'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;686<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,:'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,;'&4&1&9&6#1??9+$25-2=#1##1#1#1'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6878,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+@#4&9+$25-2=#??#23;40$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,;'&4&1&9&6#1??9+$25-2=#1##1##'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,:'&4&9+$25-2=#??#=##'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'&4&1$24##1##'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PEnd 1)))) (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 2)) (SGA.mkplan (fst ex11) (SGP.PEnd 3)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 4)) (SGA.mkplan (fst ex19) (SGP.PEnd 5)))) (SGA.mkplan (fst ex20) (SGP.PEnd 6)))) (SGA.mkplan (fst ex21) (SGP.PEnd 7)))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s5).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s5).
Definition ps1 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s11).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s11).
Definition ps3 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s18).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s18).
Definition ps4 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s19).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s19).
Definition ps5 : SR.post_spec := SR.PS 747640 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s20).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s20).
Definition ps6 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s21).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s21).
Definition ps7 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_e1a828.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747576 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_e1a828.IT BndT_Ea_001S8.SegItab_Ea_e1a828.IT_sound BF NX0 BR XSTEP F0 PSS plan 747576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ab10BZ.

Module LibSegEa_ab10E.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_e1a828.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_e1a828.IT.
Definition ENDS : list Z := [747800; 747576].
Definition STOPS1 : list Z := [747800; 747576] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); EVar 35; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1286144;
   KWord (SA (ELit 0) 1317368) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1317376) 4 (ELit 1);
   KRange (EVar 2) 140735332487184 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-16)) (ELit 16);
   KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 0 67108863].
Definition ss0 : sym_state := SS 747508 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;6918#;6838#;6918#;6838#5;#;67?<,20#$1+$2-10$3$4$5$6$7$8$9$21$23$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9!$2-8,8$1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$21##800000000000'$23##3??????,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;6918#;6838#;6918#;6838#5=#;6918,20#$1+$2-10$3$4$5$6$7$8$9#$23$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$23##1#1#1!$2-8,8$1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$21##800000000000'$23##3??????,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;6918#;6838#;6918#;6838#5=#;6838,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21#+$21$23#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$23##1##!$2-8,8$1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$21##800000000000'$23##3??????,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 747576 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_e1a828.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747508 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_e1a828.IT BndT_Ea_001S8.SegItab_Ea_e1a828.IT_sound BF NX0 BR XSTEP F0 PSS plan 747508 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ab10E.

Module LibSegEa_ab10F.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_e1a828.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_e1a828.IT.
Definition ENDS : list Z := [747576; 747800].
Definition STOPS1 : list Z := [747576; 747800] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KRange (EVar 36) 0 18446744073709551615].
Definition ss0 : sym_state := SS 747732 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;6838#;6918#;6838#;6918#5=#;6838,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'&4$21$22#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;6838#;6918#;6838#;6918#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9&4+$24-5#1$21+$24-5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'&4$21$22##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PEnd 0)) (SGA.mkplan (fst ex3) (SGP.PEnd 1)).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s2).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s2).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s2 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s2 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s2).
Definition ps0 : SR.post_spec := SR.PS 747576 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_e1a828.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747732 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_e1a828.IT BndT_Ea_001S8.SegItab_Ea_e1a828.IT_sound BF NX0 BR XSTEP F0 PSS plan 747732 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ab10F.

Module LibSegEa_ab10P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_e1a828.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_e1a828.IT.
Definition ENDS : list Z := [747732; 747800; 747640].
Definition STOPS1 : list Z := [747732; 747800; 747640] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##"%pstring).
Definition ss0 : sym_state := SS 747576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;#$1=$1>$1?,,8'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;#$1=$1>$1?,,9'&4+$25-30#:#1#1'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;#$1=$1>$1?,,9'&4+$25-30#:##'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;683<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;#$1=$1>$1?,,9'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;#$1=$1>$1?,,:'&4+$25-30#:#1#1'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;#$1=$1>$1?,,:'&4+$25-30#:##'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6840,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6860,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,:'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;686<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,;'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1#1#1'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6878,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+@#4&9+$25-2=#??#23;40$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1##'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,;'&4&9+$25-2=#??#=##'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$24##1##'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PEnd 1)))) (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 2)) (SGA.mkplan (fst ex11) (SGP.PEnd 3)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 4)) (SGA.mkplan (fst ex19) (SGP.PEnd 5)))) (SGA.mkplan (fst ex20) (SGP.PEnd 6)))) (SGA.mkplan (fst ex21) (SGP.PEnd 7)))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s5).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s5).
Definition ps1 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s11).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s11).
Definition ps3 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s18).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s18).
Definition ps4 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s19).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s19).
Definition ps5 : SR.post_spec := SR.PS 747640 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s20).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s20).
Definition ps6 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s21).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s21).
Definition ps7 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_e1a828.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747576 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_e1a828.IT BndT_Ea_001S8.SegItab_Ea_e1a828.IT_sound BF NX0 BR XSTEP F0 PSS plan 747576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ab10P1.

Module LibSegEa_ab10P2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_e1a828.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_e1a828.IT.
Definition ENDS : list Z := [747732; 747800; 747640].
Definition STOPS1 : list Z := [747732; 747800; 747640] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1"%pstring).
Definition ss0 : sym_state := SS 747576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,8'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:#1#1'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:##'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;683<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:#1#1'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:##'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6840,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6860,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,:'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;686<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,;'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1#1#1'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6878,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+@#4&9+$25-2=#??#23;40$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1##'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,;'&4&9+$25-2=#??#=##'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$24##1##'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PEnd 1)))) (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 2)) (SGA.mkplan (fst ex11) (SGP.PEnd 3)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 4)) (SGA.mkplan (fst ex19) (SGP.PEnd 5)))) (SGA.mkplan (fst ex20) (SGP.PEnd 6)))) (SGA.mkplan (fst ex21) (SGP.PEnd 7)))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s5).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s5).
Definition ps1 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s11).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s11).
Definition ps3 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s18).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s18).
Definition ps4 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s19).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s19).
Definition ps5 : SR.post_spec := SR.PS 747640 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s20).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s20).
Definition ps6 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s21).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s21).
Definition ps7 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_e1a828.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747576 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_e1a828.IT BndT_Ea_001S8.SegItab_Ea_e1a828.IT_sound BF NX0 BR XSTEP F0 PSS plan 747576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ab10P2.

Module LibSegEa_ab10P3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_e1a828.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_e1a828.IT.
Definition ENDS : list Z := [747732; 747800; 747640].
Definition STOPS1 : list Z := [747732; 747800; 747640] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2"%pstring).
Definition ss0 : sym_state := SS 747576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,8'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:#1#1'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:##'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;683<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:#1#1'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:##'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6840,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6860,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,:'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;686<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,;'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1#1#1'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6878,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+@#4&9+$25-2=#??#23;40$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1##'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,;'&4&9+$25-2=#??#=##'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$24##1##'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PEnd 1)))) (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 2)) (SGA.mkplan (fst ex11) (SGP.PEnd 3)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 4)) (SGA.mkplan (fst ex19) (SGP.PEnd 5)))) (SGA.mkplan (fst ex20) (SGP.PEnd 6)))) (SGA.mkplan (fst ex21) (SGP.PEnd 7)))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s5).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s5).
Definition ps1 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s11).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s11).
Definition ps3 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s18).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s18).
Definition ps4 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s19).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s19).
Definition ps5 : SR.post_spec := SR.PS 747640 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s20).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s20).
Definition ps6 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s21).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s21).
Definition ps7 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_e1a828.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747576 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_e1a828.IT BndT_Ea_001S8.SegItab_Ea_e1a828.IT_sound BF NX0 BR XSTEP F0 PSS plan 747576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ab10P3.

Module LibSegEa_ab10P4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_e1a828.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_e1a828.IT.
Definition ENDS : list Z := [747732; 747800; 747640].
Definition STOPS1 : list Z := [747732; 747800; 747640] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3"%pstring).
Definition ss0 : sym_state := SS 747576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,8'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:#1#1'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:##'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;683<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:#1#1'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:##'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6840,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6860,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,:'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;686<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,;'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1#1#1'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6878,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+@#4&9+$25-2=#??#23;40$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1##'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,;'&4&9+$25-2=#??#=##'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$24##1##'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PEnd 1)))) (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 2)) (SGA.mkplan (fst ex11) (SGP.PEnd 3)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 4)) (SGA.mkplan (fst ex19) (SGP.PEnd 5)))) (SGA.mkplan (fst ex20) (SGP.PEnd 6)))) (SGA.mkplan (fst ex21) (SGP.PEnd 7)))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s5).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s5).
Definition ps1 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s11).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s11).
Definition ps3 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s18).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s18).
Definition ps4 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s19).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s19).
Definition ps5 : SR.post_spec := SR.PS 747640 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s20).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s20).
Definition ps6 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s21).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s21).
Definition ps7 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_e1a828.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747576 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_e1a828.IT BndT_Ea_001S8.SegItab_Ea_e1a828.IT_sound BF NX0 BR XSTEP F0 PSS plan 747576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ab10P4.

Module LibSegEa_ab10P5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_e1a828.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_e1a828.IT.
Definition ENDS : list Z := [747732; 747800; 747640].
Definition STOPS1 : list Z := [747732; 747800; 747640] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4"%pstring).
Definition ss0 : sym_state := SS 747576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,8'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:#1#1'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:##'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;683<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:#1#1'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:##'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6840,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6860,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,:'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;686<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,;'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1#1#1'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6878,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+@#4&9+$25-2=#??#23;40$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1##'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,;'&4&9+$25-2=#??#=##'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$24##1##'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PEnd 1)))) (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 2)) (SGA.mkplan (fst ex11) (SGP.PEnd 3)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 4)) (SGA.mkplan (fst ex19) (SGP.PEnd 5)))) (SGA.mkplan (fst ex20) (SGP.PEnd 6)))) (SGA.mkplan (fst ex21) (SGP.PEnd 7)))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s5).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s5).
Definition ps1 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s11).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s11).
Definition ps3 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s18).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s18).
Definition ps4 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s19).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s19).
Definition ps5 : SR.post_spec := SR.PS 747640 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s20).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s20).
Definition ps6 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s21).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s21).
Definition ps7 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_e1a828.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747576 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_e1a828.IT BndT_Ea_001S8.SegItab_Ea_e1a828.IT_sound BF NX0 BR XSTEP F0 PSS plan 747576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ab10P5.

Module LibSegEa_ab10P6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_e1a828.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_e1a828.IT.
Definition ENDS : list Z := [747732; 747800; 747640].
Definition STOPS1 : list Z := [747732; 747800; 747640] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5"%pstring).
Definition ss0 : sym_state := SS 747576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,8'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:#1#1'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:##'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;683<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:#1#1'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:##'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6840,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6860,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,:'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;686<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,;'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1#1#1'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6878,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+@#4&9+$25-2=#??#23;40$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1##'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,;'&4&9+$25-2=#??#=##'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$24##1##'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PEnd 1)))) (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 2)) (SGA.mkplan (fst ex11) (SGP.PEnd 3)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 4)) (SGA.mkplan (fst ex19) (SGP.PEnd 5)))) (SGA.mkplan (fst ex20) (SGP.PEnd 6)))) (SGA.mkplan (fst ex21) (SGP.PEnd 7)))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s5).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s5).
Definition ps1 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s11).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s11).
Definition ps3 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s18).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s18).
Definition ps4 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s19).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s19).
Definition ps5 : SR.post_spec := SR.PS 747640 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s20).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s20).
Definition ps6 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s21).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s21).
Definition ps7 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_e1a828.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747576 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_e1a828.IT BndT_Ea_001S8.SegItab_Ea_e1a828.IT_sound BF NX0 BR XSTEP F0 PSS plan 747576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ab10P6.

Module LibSegEa_ab10P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_e1a828.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_e1a828.IT.
Definition ENDS : list Z := [747732; 747800; 747640].
Definition STOPS1 : list Z := [747732; 747800; 747640] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6"%pstring).
Definition ss0 : sym_state := SS 747576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,8'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:#1#1'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:##'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;683<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;68<4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:#1#1'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:##'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6840,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;6860,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,:'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5;#;686<,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,;'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1#1#1'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6878,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9$21$21+@#4&9+$25-2=#??#23;40$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1##'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;6918,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,;'&4&9+$25-2=#??#=##'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;68=4#;6918#;6878#;68=4#;6918#;6878#5=#;68=4,20#$1+$2-10$3$4#7???8000#1??9#23;40$8$9+$21#1+$21#1$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$24##1##'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PEnd 1)))) (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 2)) (SGA.mkplan (fst ex11) (SGP.PEnd 3)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 4)) (SGA.mkplan (fst ex19) (SGP.PEnd 5)))) (SGA.mkplan (fst ex20) (SGP.PEnd 6)))) (SGA.mkplan (fst ex21) (SGP.PEnd 7)))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s5).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s5).
Definition ps1 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s11).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s11).
Definition ps3 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s18).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s18).
Definition ps4 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s19).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s19).
Definition ps5 : SR.post_spec := SR.PS 747640 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s20).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s20).
Definition ps6 : SR.post_spec := SR.PS 747800 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s21).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s21).
Definition ps7 : SR.post_spec := SR.PS 747732 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_e1a828.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747576 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_e1a828.IT BndT_Ea_001S8.SegItab_Ea_e1a828.IT_sound BF NX0 BR XSTEP F0 PSS plan 747576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ab10P7.
