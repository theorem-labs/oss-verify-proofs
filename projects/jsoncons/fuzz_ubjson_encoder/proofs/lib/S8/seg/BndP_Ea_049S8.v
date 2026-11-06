(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ea0PlanKit Ea0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndT_Ea_001S8.

Module LibSegEa_askAS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_bcf571.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_bcf571.IT.
Definition ENDS : list Z := [717104].
Definition STOPS1 : list Z := [717104] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8$21!$:#8,8+$21$22!$:#10,8+$21$22'$21##800000000000'$22##400000000'$23##400000000'+$21$23##800000000000"%pstring).
Definition ss0 : sym_state := SS 716844 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?130#:?130#5=#:?130,20##:?0<<+$2-30$3$4$5$6$7+$:#8$;$:$;#$=$>$?$10$11+$21$22+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,20!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8$21!$:#8,8+$21$22!$:#10,8+$21$22'$21##800000000000'$22##400000000'$23##400000000'+$21$23##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 717104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_bcf571.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 716844 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_bcf571.IT BndT_Ea_001S8.SegItab_Ea_bcf571.IT_sound BF NX0 BR XSTEP F0 PSS plan 716844 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askAS.

Module LibSegEa_askB7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_bcf571.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_bcf571.IT.
Definition ENDS : list Z := [717044].
Definition STOPS1 : list Z := [717044] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7+$:#8$24$37$38$39$=$>$?$10$11+$21$22+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$21#1000#800000000000&$21#10'$22##400000000'$23##400000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#688000$21#$23!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31(+$21$22##1)##7???7000#100000001000+$21$22##1)+$21$22##1$2-100#100)+$21$22##1$:##18)+$21$22##1$24##1#&6+$21$22#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 716948 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 33) (EVar 34)), (0), ELit 1); ((EVar 10), (8), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 33) (EVar 34)), (0), 1); ((EVar 10), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?0?4#:?0?4#5=#:?0?4,20#$2<$2$3$4$5$6$7$2=$2>++$21$22#1#$39$=$>$?$10$11$2?$30$31$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,24!$:#8,8++$21$22#1!+$21$22#,1$28'$2#7???7?801030#800000000000&$2#10($2-30#30'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$21#1000#800000000000&$21#10'$22##400000000'$23##400000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#688000$21#$23!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31(+$21$22##1)##7???7000#100000001000+$21$22##1)+$21$22##1$2-100#100)+$21$22##1$:##18)+$21$22##1$24##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 717044 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_bcf571.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 716948 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_bcf571.IT BndT_Ea_001S8.SegItab_Ea_bcf571.IT_sound BF NX0 BR XSTEP F0 PSS plan 716948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askB7.

Module LibSegEa_askBp.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_bcf571.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_bcf571.IT.
Definition ENDS : list Z := [717044].
Definition STOPS1 : list Z := [717044] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7+$:#8$24$37$38$39$=$>$?$10$11+$21$22+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$21#1000#800000000000&$21#10'$22##400000000'$23##400000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#688000$21#$23!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31(+$21$22##1)##7???7000#100000001000+$21$22##1)+$21$22##1$2-100#100)+$21$22##1$:##18)+$21$22##1$24##1!&6+$21$22#3#7???8000,1+&9$22#7#1"%pstring).
Definition ss0 : sym_state := SS 716948 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 33) (EVar 34)), (0), ELit 1); ((EVar 10), (8), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 33) (EVar 34)), (0), 1); ((EVar 10), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?0?4#:?0?4#5=#:?0?4,20#$2<$2$3$4$5$6$7$2=$2>++$21$22#1#&9$22#7$=$>$?$10$11$2?$30$31$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,24!$:#8,8++$21$22#1!+$21$22#,1$28'$2#7???7?801030#800000000000&$2#10($2-30#30'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$21#1000#800000000000&$21#10'$22##400000000'$23##400000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#688000$21#$23!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31(+$21$22##1)##7???7000#100000001000+$21$22##1)+$21$22##1$2-100#100)+$21$22##1$:##18)+$21$22##1$24##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 717044 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_bcf571.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 716948 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_bcf571.IT BndT_Ea_001S8.SegItab_Ea_bcf571.IT_sound BF NX0 BR XSTEP F0 PSS plan 716948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askBp.

Module LibSegEa_askR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_bcf571.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_bcf571.IT.
Definition ENDS : list Z := [717044].
Definition STOPS1 : list Z := [717044] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7+$:#8$24$29$38$39$=$>$?$10$11+$21$22+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31"%pstring).
Definition ss0 : sym_state := SS 717004 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 10), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?0?4#:?0?4#5=#:?0?4,20#$2<$2$3$4$5$6$7$2=$2>$29#$39$=$>$?$10$11$2?$30$31$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13!$:#8,8$29%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 717044 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_bcf571.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 717004 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_bcf571.IT BndT_Ea_001S8.SegItab_Ea_bcf571.IT_sound BF NX0 BR XSTEP F0 PSS plan 717004 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askR.

Module LibSegEa_askS1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_baaeb0.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_baaeb0.IT.
Definition ENDS : list Z := [1253056].
Definition STOPS1 : list Z := [1253056] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:?0<<+$2-30$3$4$5$6$7+$:#8$;$:$;$39$=$>$?$10$11+$21$23+&6+$:#8#3#7???8000#7???8000$32$33$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8$21!$:#8,8+$21$23!$:#10,8+$21$23'$21#1000#800000000000&$21#10'$22##400000000'$23#2#200000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#688000$21#$23"%pstring).
Definition ss0 : sym_state := SS 717104 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 112)].
Definition F0L : list SR.region := [((EVar 2), (-160), 112)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#131><0#131><0#5=#131><0,20##:?1>8+$2-:0$3$4$5$6$7+$:#8$:@#2$23^#?#???????????????^#3#???????????????#$>$?$10$11$;@#2$23+&6+$:#8#3#7???8000#7???8000$23$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-78,8$:!$2-70,8$33!$2-68,8$32!$2-60,8#7???8000!$2-58,8+&6+$:#8#3#7???8000!$2-50,8+$21$23!$2-48,8$;!$2-40,8+$:#8!$2-38,8#:?0<<%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8$21!$:#8,8+$21$23!$:#10,8+$21$23'$21#1000#800000000000&$21#10'$22##400000000'$23#2#200000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#688000$21#$23,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 1253056 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_baaeb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 717104 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_baaeb0.IT BndT_Ea_001S8.SegItab_Ea_baaeb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 717104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askS1.

Module LibSegEa_askS1o.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_baaeb0.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_baaeb0.IT.
Definition ENDS : list Z := [1253056].
Definition STOPS1 : list Z := [1253056] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:?0<<+$2-30$3$4$5$6$7+$:#8$;$:$;$39$=$>$?$10$11+$21#1+&6+$:#8#3#7???8000#7???8000$32$33$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8$21!$:#8,8+$21#1!$:#10,8+$21#1'$21#1000#7???????????&$21#10)##10000#688000$21##1)##7???7000#100000001000$21##1"%pstring).
Definition ss0 : sym_state := SS 717104 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 112)].
Definition F0L : list SR.region := [((EVar 2), (-160), 112)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#131><0#131><0#5=#131><0,20##:?1>8+$2-:0$3$4$5$6$7+$:#8$:#2^#?#???????????????^#3#???????????????#$>$?$10$11$;#2+&6+$:#8#3#7???8000#7???8000#1$17$18$19$1:$1;$1<$1=$1>$1?,,24!$2-78,8$:!$2-70,8$33!$2-68,8$32!$2-60,8#7???8000!$2-58,8+&6+$:#8#3#7???8000!$2-50,8+$21#1!$2-48,8$;!$2-40,8+$:#8!$2-38,8#:?0<<%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8$21!$:#8,8+$21#1!$:#10,8+$21#1'$21#1000#7???????????&$21#10)##10000#688000$21##1)##7???7000#100000001000$21##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 1253056 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_baaeb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 717104 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_baaeb0.IT BndT_Ea_001S8.SegItab_Ea_baaeb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 717104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askS1o.

Module LibSegEa_askS1z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_baaeb0.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_baaeb0.IT.
Definition ENDS : list Z := [1253056].
Definition STOPS1 : list Z := [1253056] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:?0<<+$2-30$3$4$5$6$7+$:#8$;$:$;$39$=$>$?$10$11#+&6+$:#8#3#7???8000#7???8000$32$33$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8#!$:#8,8#!$:#10,8#"%pstring).
Definition ss0 : sym_state := SS 717104 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 112)].
Definition F0L : list SR.region := [((EVar 2), (-160), 112)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#131><0#131><0#5=#131><0,20##:?1>8+$2-:0$3$4$5$6$7+$:#8$:#1^#?#???????????????^#3#???????????????#$>$?$10$11$;#1+&6+$:#8#3#7???8000#7???8000#$17$18$19$1:$1;$1<$1=$1>$1?,,20!$2-78,8$:!$2-70,8$33!$2-68,8$32!$2-60,8#7???8000!$2-58,8+&6+$:#8#3#7???8000!$2-50,8#!$2-48,8$;!$2-40,8+$:#8!$2-38,8#:?0<<%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8#!$:#8,8#!$:#10,8#,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 1253056 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_baaeb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 717104 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_baaeb0.IT BndT_Ea_001S8.SegItab_Ea_baaeb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 717104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askS1z.

Module LibSegEa_askS2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_baaeb0.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_baaeb0.IT.
Definition ENDS : list Z := [698092].
Definition STOPS1 : list Z := [698092] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$:#8$:$25$38$39$=$>$?$10$11$24$26+&6+$:#8#3#7???8000#7???8000$22$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25$26#1000#800000000000)##7???7000#100000001000$25#$26)##10000#688000$25#$26($25#$26)$2-100#100$25#$26)$:##18$25#$26)$24##1$25#$26'$22#4#200000000'$26#8#400000000'&1$26$22#4#400000000#&6+$22$25#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 717288 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-152), ELit 32); ((EAlu Instr.ALU_ADD (EVar 34) (EVar 37)), (0), ELit 1); ((EVar 2), (-208), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-152), 32); ((EAlu Instr.ALU_ADD (EVar 34) (EVar 37)), (0), 1); ((EVar 2), (-208), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#::6><#::6><#5=#::6><,20##:?3>4+$2-=0$3$4$5$6$7+$2-98$:$:#1419?8#$=$>$?$10$11$24#7???8000+&6+$:#8#3#7???8000#7???8000$22$17$18$19$1:$1;$1<$1=$1>$1?,,2:!$2-<8,8+$25$26!$2-<0,8$24!$2-;8,8$:!$2-;0,8+$:#8!$2-:8,8#:?244!$2-88,8++$22$25#1!+$22$25#,1$28!$2-80,8+$25$26!$2-90,8+$22$25!$2-98,8$25%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25$26#1000#800000000000)##7???7000#100000001000$25#$26)##10000#688000$25#$26($25#$26)$2-100#100$25#$26)$:##18$25#$26)$24##1$25#$26'$22#4#200000000'$26#8#400000000'&1$26$22#4#400000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 698092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_baaeb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 717288 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_baaeb0.IT BndT_Ea_001S8.SegItab_Ea_baaeb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 717288 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askS2.

Module LibSegEa_askS2o.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_baaeb0.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_baaeb0.IT.
Definition ENDS : list Z := [698092].
Definition STOPS1 : list Z := [698092] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$:#8$:$25$38$39$=$>$?$10$11$24#2+&6+$:#8#3#7???8000#7???8000#1$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#2#1000#800000000000)##7???7000#100000001000$25##2)##10000#688000$25##2($25##2)$2-100#100$25##2)$:##18$25##2)$24##1$25##2!&6+$25#1#3#7???8000,1#2"%pstring).
Definition ss0 : sym_state := SS 717288 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-152), ELit 32); ((EVar 37), (1), ELit 1); ((EVar 2), (-208), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-152), 32); ((EVar 37), (1), 1); ((EVar 2), (-208), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#::6><#::6><#5=#::6><,20##:?3>4+$2-=0$3$4$5$6$7+$2-98$:$:#1419?8#2#1$>$?$10$11$24#7???8000+&6+$:#8#3#7???8000#7???8000#1$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-<8,8+$25#2!$2-<0,8$24!$2-;8,8$:!$2-;0,8+$:#8!$2-:8,8#:?244!$2-88,8+$25#2!$25#1,1$28!$2-80,8+$25#2!$2-90,8+$25#1!$2-98,8$25%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#2#1000#800000000000)##7???7000#100000001000$25##2)##10000#688000$25##2($25##2)$2-100#100$25##2)$:##18$25##2)$24##1$25##2,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 698092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_baaeb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 717288 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_baaeb0.IT BndT_Ea_001S8.SegItab_Ea_baaeb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 717288 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askS2o.

Module LibSegEa_askS2t.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_baaeb0.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_baaeb0.IT.
Definition ENDS : list Z := [698092].
Definition STOPS1 : list Z := [698092] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$:#8$:$25$38$39$=$>$?$10$11$24#4+&6+$:#8#3#7???8000#7???8000#2$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#4#1000#800000000000)##7???7000#100000001000$25##4)##10000#688000$25##4($25##4)$2-100#100$25##4)$:##18$25##4)$24##1$25##4!&6+$25#2#3#7???8000,1#4"%pstring).
Definition ss0 : sym_state := SS 717288 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-152), ELit 32); ((EVar 37), (2), ELit 1); ((EVar 2), (-208), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-152), 32); ((EVar 37), (2), 1); ((EVar 2), (-208), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#::6><#::6><#5=#::6><,20##:?3>4+$2-=0$3$4$5$6$7+$2-98$:$:#1419?8#4#2$>$?$10$11$24#7???8000+&6+$:#8#3#7???8000#7???8000#2$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-<8,8+$25#4!$2-<0,8$24!$2-;8,8$:!$2-;0,8+$:#8!$2-:8,8#:?244!$2-88,8+$25#3!$25#2,1$28!$2-80,8+$25#4!$2-90,8+$25#2!$2-98,8$25%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#4#1000#800000000000)##7???7000#100000001000$25##4)##10000#688000$25##4($25##4)$2-100#100$25##4)$:##18$25##4)$24##1$25##4,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 698092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_baaeb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 717288 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_baaeb0.IT BndT_Ea_001S8.SegItab_Ea_baaeb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 717288 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askS2t.

Module LibSegEa_askS2z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_baaeb0.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_baaeb0.IT.
Definition ENDS : list Z := [698092].
Definition STOPS1 : list Z := [698092] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$:#8$:$25$38$39$=$>$?$10$11$24#1+&6+$:#8#3#7???8000#7???8000#$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#1#1000#800000000000)##7???7000#100000001000$25##1)##10000#688000$25##1($25##1)$2-100#100$25##1)$:##18$25##1)$24##1$25##1!&6$25#3#7???8000,1#1"%pstring).
Definition ss0 : sym_state := SS 717288 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-152), ELit 32); ((EVar 37), (0), ELit 1); ((EVar 2), (-208), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-152), 32); ((EVar 37), (0), 1); ((EVar 2), (-208), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#::6><#::6><#5=#::6><,20##:?3>4+$2-=0$3$4$5$6$7+$2-98$:$:#1419?8#1#$>$?$10$11$24#7???8000+&6+$:#8#3#7???8000#7???8000#$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-<8,8+$25#1!$2-<0,8$24!$2-;8,8$:!$2-;0,8+$:#8!$2-:8,8#:?244!$2-88,8+$25#1!$25#,1$28!$2-80,8+$25#1!$2-90,8$25!$2-98,8$25%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#1#1000#800000000000)##7???7000#100000001000$25##1)##10000#688000$25##1($25##1)$2-100#100$25##1)$:##18$25##1)$24##1$25##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 698092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_baaeb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 717288 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_baaeb0.IT BndT_Ea_001S8.SegItab_Ea_baaeb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 717288 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askS2z.

Module LibSegEa_askS3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_baaeb0.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_baaeb0.IT.
Definition ENDS : list Z := [871008].
Definition STOPS1 : list Z := [871008] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$:#8$:$37$38$39$=$>$?$10$11$24$13+&6+$:#8#3#7???8000#7???8000$22$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$:#8,8++$22$25#1!$2-98,8$21!$2-90,8$21!$2-88,8$21!$2-80,8+$21$23'$21#1000#800000000000&$21#10'$22##400000000'$23##400000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#688000$21#$23'$25#1000#800000000000'+$22$25#1000#7???????????'+$25$26#1000#800000000000"%pstring).
Definition ss0 : sym_state := SS 717380 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-136), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-136), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=4:60#=4:60#5=#=4:60,20##:?274+$2-:0$3$4$5$6$7++$22$25#1$:$21$23$39$=$>$?$10$11$24$13+&6+$:#8#3#7???8000#7???8000$22$17$18$19$1:$1;$1<$1=$1>$1?,,1<%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$:#8,8++$22$25#1!$2-98,8$21!$2-90,8$21!$2-88,8$21!$2-80,8+$21$23'$21#1000#800000000000&$21#10'$22##400000000'$23##400000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#688000$21#$23'$25#1000#800000000000'+$22$25#1000#7???????????'+$25$26#1000#800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 871008 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_baaeb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 717380 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_baaeb0.IT BndT_Ea_001S8.SegItab_Ea_baaeb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 717380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askS3.

Module LibSegEa_askS3n.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_baaeb0.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_baaeb0.IT.
Definition ENDS : list Z := [717468].
Definition STOPS1 : list Z := [717468] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$:#8$:$37$38$39$=$>$?$10$11$24$13+&6+$:#8#3#7???8000#7???8000#$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$:#8,8+$25#1!$2-98,8#!$2-90,8#!$2-88,8#!$2-80,8#!$2-38,8#:?0<<!$2-40,8+$:#8!$2-48,8$24!$2-50,8#!$2-58,8+&6+$:#8#3#7???8000!$2-60,8#7???8000!$2-68,8$32!$2-70,8$33'$25#1000#7???????????"%pstring).
Definition ss0 : sym_state := SS 717380 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-136), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-136), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?29<#:?29<#5=#:?29<,20##:?0<<+$2-30$3$4$5$6$7+$:#8$24+$25#1#$39$=$>$?$10$11#+&6+$:#8#3#7???8000#7???8000$32$33$17$18$19$1:$1;$1<$1=$1>$1?,,1;%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$:#8,8+$25#1!$2-98,8#!$2-90,8#!$2-88,8#!$2-80,8#!$2-38,8#:?0<<!$2-40,8+$:#8!$2-48,8$24!$2-50,8#!$2-58,8+&6+$:#8#3#7???8000!$2-60,8#7???8000!$2-68,8$32!$2-70,8$33'$25#1000#7???????????,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 717468 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_baaeb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 717380 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_baaeb0.IT BndT_Ea_001S8.SegItab_Ea_baaeb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 717380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askS3n.

Module LibSegEa_askS4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_baaeb0.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_baaeb0.IT.
Definition ENDS : list Z := [717468].
Definition STOPS1 : list Z := [717468] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$29$:$37$38$39$=$>$?$10$11$24$13+&6+$:#8#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$2-38,8#:?0<<!$2-40,8+$:#8!$2-48,8$24!$2-50,8+$21$22!$2-58,8+&6+$:#8#3#7???8000!$2-60,8#7???8000!$2-68,8$32!$2-70,8$33'$21##800000000000'$22##400000000'$23##400000000'+$21$23##800000000000"%pstring).
Definition ss0 : sym_state := SS 717428 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?29<#:?29<#5=#:?29<,20##:?0<<+$2-30$3$4$5$6$7+$:#8$24$29$38$39$=$>$?$10$11+$21$22+&6+$:#8#3#7???8000#7???8000$32$33$17$18$19$1:$1;$1<$1=$1>$1?,,19%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#698000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$2-38,8#:?0<<!$2-40,8+$:#8!$2-48,8$24!$2-50,8+$21$22!$2-58,8+&6+$:#8#3#7???8000!$2-60,8#7???8000!$2-68,8$32!$2-70,8$33'$21##800000000000'$22##400000000'$23##400000000'+$21$23##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
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
Definition ps0 : SR.post_spec := SR.PS 717468 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_baaeb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 717428 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_baaeb0.IT BndT_Ea_001S8.SegItab_Ea_baaeb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 717428 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_askS4.
