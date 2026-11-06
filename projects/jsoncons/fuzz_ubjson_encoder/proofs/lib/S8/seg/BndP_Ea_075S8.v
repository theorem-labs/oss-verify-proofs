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

Module LibSegEa_srdDS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_b1b975.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_b1b975.IT.
Definition ENDS : list Z := [881996].
Definition STOPS1 : list Z := [881996] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$:$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000#4000$27$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2=%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1##"%pstring).
Definition ss0 : sym_state := SS 751676 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=754<#=754<#5=#=754<,20##;787<+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$25+&6$28#1#4000#$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000#4000$27$1:&6$28#1$1<$1=$1>$1?,,2=%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1##,46!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 881996 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_b1b975.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 751676 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_b1b975.IT BndT_Ea_001S8.SegItab_Ea_b1b975.IT_sound BF NX0 BR XSTEP F0 PSS plan 751676 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_srdDS.

Module LibSegEa_srdE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_b1b975.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_b1b975.IT.
Definition ENDS : list Z := [881996; 751380; 752004].
Definition STOPS1 : list Z := [881996; 751380; 752004] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$2<$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:$2>$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18'$2<##4000'$2;#1#4000'$2>##8000000'$27#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 751660 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",#5;#;782<,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$2<$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:$2>$1<$1=$1>$1?,,2>%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18'$2<##4000'$2;#1#4000'$2>##8000000'$27#1^#?#???????????????,46!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=754<#;7714#;7984#=754<#;7714#;7984#5;#;7834,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$2<$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;+$27@-1$2;$1:$2>$1<$1=$1>$1?,,2?'&4&1$2<$2;#1#1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18'$2<##4000'$2;#1#4000'$2>##8000000'$27#1^#?#???????????????,46!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=754<#;7714#;7984#=754<#;7714#;7984#5=#;7984,20#$30$2$3$4$5$6$7$31$32+$26+@-1$27$2;$;$<$=$>$?$10$11$33$34$35$36$37$38$39$3:$3;$3<$1<$1=$1>$1?,,30'&4&1+$27@-1$2;##1#1#1'&4&1$2<$2;#1#1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18'$2<##4000'$2;#1#4000'$2>##8000000'$27#1^#?#???????????????,46!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=754<#;7714#;7984#=754<#;7714#;7984#5=#;7714,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$2<$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;+$27@-1$2;$1:$2>$1<$1=$1>$1?,,30'&4&1+$27@-1$2;##1##'&4&1$2<$2;#1#1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18'$2<##4000'$2;#1#4000'$2>##8000000'$27#1^#?#???????????????,46!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=754<#;7714#;7984#=754<#;7714#;7984#5=#=754<,20##;78?4+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$25+$2<$2>#$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$2<$2>$1<$1=$1>$1?,,2?'&4&1$2<$2;#1##%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18'$2<##4000'$2;#1#4000'$2>##8000000'$27#1^#?#???????????????,46!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 2)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s7).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s7).
Definition ps0 : SR.post_spec := SR.PS 881996 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 751380 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s5).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s5).
Definition ps2 : SR.post_spec := SR.PS 752004 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_b1b975.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 751660 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_b1b975.IT BndT_Ea_001S8.SegItab_Ea_b1b975.IT_sound BF NX0 BR XSTEP F0 PSS plan 751660 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_srdE.

Module LibSegEa_srdF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_b1b975.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_b1b975.IT.
Definition ENDS : list Z := [751380; 752004].
Definition STOPS1 : list Z := [751380; 752004] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$:$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$18$27$2<$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2<%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18'$2<##4000'$27#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 751860 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;7714#;7984#;7714#;7984#5;#;7834,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$:$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2<+$27@-1$2<$2<$1;$1<$1=$1>$1?,,2<%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18'$2<##4000'$27#1^#?#???????????????,46!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;7714#;7984#;7714#;7984#5=#;7984,20#$30$2$3$4$5$6$7$31$32+$26+@-1$27$2<$;$<$=$>$?$10$11$33$34$35$36$37$38$39$3:$3;$3<$1<$1=$1>$1?,,2='&4&1+$27@-1$2<##1#1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18'$2<##4000'$27#1^#?#???????????????,46!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;7714#;7984#;7714#;7984#5=#;7714,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$:$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2<+$27@-1$2<$2<$1;$1<$1=$1>$1?,,2='&4&1+$27@-1$2<##1##%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18'$2<##4000'$27#1^#?#???????????????,46!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 751380 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 752004 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_b1b975.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 751860 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_b1b975.IT BndT_Ea_001S8.SegItab_Ea_b1b975.IT_sound BF NX0 BR XSTEP F0 PSS plan 751860 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_srdF.

Module LibSegEa_srdH0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_b1b975.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_b1b975.IT.
Definition ENDS : list Z := [751536; 751676; 752004].
Definition STOPS1 : list Z := [751536; 751676; 752004] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$:$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$18$27$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$24#120,8#!$24#110,8#4000'$2=#698000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$2-<0#<0$2=##110)$24##128$2=##110)$25##18$2=##110!$24#?0,8$2=!$2=#,8#136>28!$2=#98,1$3>'$3>##2###8001>=<2#1'$27#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 751380 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;77;0#;783<#;7984#;77;0#;783<#;7984#5;#;7784,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25@#2&6$3>#1##$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$18$27$1:$1;$1<$1=$1>$1?,,3:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$24#120,8#!$24#110,8#4000'$2=#698000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$2-<0#<0$2=##110)$24##128$2=##110)$25##18$2=##110!$24#?0,8$2=!$2=#,8#136>28!$2=#98,1$3>'$3>##2###8001>=<2#1'$27#1^#?#???????????????,46!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;77;0#;783<#;7984#;77;0#;783<#;7984#5;#;7794,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25###$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000#4000$27$1:$1;$1<$1=$1>$1?,,3;'&4&1@#2&6$3>#1##1#1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$24#120,8#!$24#110,8#4000'$2=#698000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$2-<0#<0$2=##110)$24##128$2=##110)$25##18$2=##110!$24#?0,8$2=!$2=#,8#136>28!$2=#98,1$3>'$3>##2###8001>=<2#1'$27#1^#?#???????????????,46!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;77;0#;783<#;7984#;77;0#;783<#;7984#5=#;77;0,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25#4000##$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$27$27$1:$1;$1<$1=$1>$1?,,3<'&4$27#4000#1#1'&4&1@#2&6$3>#1##1#1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$24#120,8#!$24#110,8#4000'$2=#698000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$2-<0#<0$2=##110)$24##128$2=##110)$25##18$2=##110!$24#?0,8$2=!$2=#,8#136>28!$2=#98,1$3>'$3>##2###8001>=<2#1'$27#1^#?#???????????????,46!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;77;0#;783<#;7984#;77;0#;783<#;7984#5=#;783<,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25###$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000#4000$27$1:$1;$1<$1=$1>$1?,,3<'&4$27#4000##'&4&1@#2&6$3>#1##1#1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$24#120,8#!$24#110,8#4000'$2=#698000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$2-<0#<0$2=##110)$24##128$2=##110)$25##18$2=##110!$24#?0,8$2=!$2=#,8#136>28!$2=#98,1$3>'$3>##2###8001>=<2#1'$27#1^#?#???????????????,46!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;77;0#;783<#;7984#;77;0#;783<#;7984#5=#;7984,20#$30$2$3$4$5$6$7$31$32+$26@-1$27##$=$>$?$10$11$33$34$35$36$37$38$39$3:$3;$3<$1<$1=$1>$1?,,3;'&4&1@#2&6$3>#1##1##%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$24#120,8#!$24#110,8#4000'$2=#698000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$2-<0#<0$2=##110)$24##128$2=##110)$25##18$2=##110!$24#?0,8$2=!$2=#,8#136>28!$2=#98,1$3>'$3>##2###8001>=<2#1'$27#1^#?#???????????????,46!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 0)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 2))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s5).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s5).
Definition ps0 : SR.post_spec := SR.PS 751536 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 751676 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 752004 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_b1b975.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 751380 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_b1b975.IT BndT_Ea_001S8.SegItab_Ea_b1b975.IT_sound BF NX0 BR XSTEP F0 PSS plan 751380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_srdH0.

Module LibSegEa_srdH1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_b1b975.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_b1b975.IT.
Definition ENDS : list Z := [751536].
Definition STOPS1 : list Z := [751536] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$:$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$18$27$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$24#120,8$21'$21#1#4000!$24#110,8#4000'$27#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 751380 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;77;0#;77;0#5;#;77:8,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25#4000$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$27$27$1:$1;$1<$1=$1>$1?,,2>%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$24#120,8$21'$21#1#4000!$24#110,8#4000'$27#1^#?#???????????????,46!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;77;0#;77;0#5=#;77;0,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25#4000$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$27$27$1:$1;$1<$1=$1>$1?,,2?'&4$27#4000#1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$24#120,8$21'$21#1#4000!$24#110,8#4000'$27#1^#?#???????????????,46!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;77;0#;77;0#5=#;77;0,20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25#4000$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000#4000$27$1:$1;$1<$1=$1>$1?,,2?'&4$27#4000##%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$24#120,8$21'$21#1#4000!$24#110,8#4000'$27#1^#?#???????????????,46!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 751536 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 751536 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_b1b975.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 751380 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_b1b975.IT BndT_Ea_001S8.SegItab_Ea_b1b975.IT_sound BF NX0 BR XSTEP F0 PSS plan 751380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_srdH1.

Module LibSegEa_srdQL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_b1b975.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_b1b975.IT.
Definition ENDS : list Z := [742412].
Definition STOPS1 : list Z := [742412] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$:$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:$2>$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",31%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1#1#1!$25#10,8$2:'$2:#1000#800000000000'$2;#1#4000'$2>##8000000"%pstring).
Definition ss0 : sym_state := SS 751600 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;540<#;540<#5=#;540<,20##;782<+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$24+$2:$2>$2;$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:$2>$1<$1=$1>$1?,,31%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1#1#1!$25#10,8$2:'$2:#1000#800000000000'$2;#1#4000'$2>##8000000,46!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 742412 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_b1b975.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 751600 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_b1b975.IT BndT_Ea_001S8.SegItab_Ea_b1b975.IT_sound BF NX0 BR XSTEP F0 PSS plan 751600 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_srdQL.

Module LibSegEa_srdQS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_b1b975.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_b1b975.IT.
Definition ENDS : list Z := [742412].
Definition STOPS1 : list Z := [742412] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$:$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:$2>$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2?%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1##'$2;#1#4000'$2>##8000000"%pstring).
Definition ss0 : sym_state := SS 751600 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;540<#;540<#5=#;540<,20##;782<+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$24++$25$2>#1$2;$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:$2>$1<$1=$1>$1?,,2?%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1##'$2;#1#4000'$2>##8000000,46!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 742412 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_b1b975.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 751600 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_b1b975.IT BndT_Ea_001S8.SegItab_Ea_b1b975.IT_sound BF NX0 BR XSTEP F0 PSS plan 751600 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_srdQS.

Module LibSegEa_srdRL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_b1b975.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_b1b975.IT.
Definition ENDS : list Z := [881996].
Definition STOPS1 : list Z := [881996] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$:$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",30%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1#1#1!$25#8,8$29'$29##8000000'$2;#1#4000"%pstring).
Definition ss0 : sym_state := SS 751536 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=754<#=754<#5=#=754<,20##;77?0+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$25+$29$2;#$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:$29$1<$1=$1>$1?,,30%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1#1#1!$25#8,8$29'$29##8000000'$2;#1#4000,46!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 881996 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_b1b975.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 751536 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_b1b975.IT BndT_Ea_001S8.SegItab_Ea_b1b975.IT_sound BF NX0 BR XSTEP F0 PSS plan 751536 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_srdRL.

Module LibSegEa_srdRS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_b1b975.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_b1b975.IT.
Definition ENDS : list Z := [881996].
Definition STOPS1 : list Z := [881996] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$:$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1##'$2;#1#4000"%pstring).
Definition ss0 : sym_state := SS 751536 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=754<#=754<#5=#=754<,20##;77?0+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$25+$2;&6$28#1#$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:&6$28#1$1<$1=$1>$1?,,2>%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#698000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1##'$2;#1#4000,46!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 881996 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_b1b975.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 751536 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_b1b975.IT BndT_Ea_001S8.SegItab_Ea_b1b975.IT_sound BF NX0 BR XSTEP F0 PSS plan 751536 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_srdRS.
