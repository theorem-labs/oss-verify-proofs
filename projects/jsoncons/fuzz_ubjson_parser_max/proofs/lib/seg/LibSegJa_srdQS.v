(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ja0PlanKit Ja0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Ja_f5412e.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ja_f5412e.ITR.
Definition IT : itab := SegItab_Ja_f5412e.IT.
Definition ENDS : list Z := [717620].
Definition STOPS1 : list Z := [717620] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$:$;$<$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:$2>$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",2?%#10000#134000!##13:<?8,8#7???8000!##13:=00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#691000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#691000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1##'$2;#1#4000'$2>##8000000"%pstring).
Definition ss0 : sym_state := SS 726808 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#:?334#:?334#5=#:?334,20##;1754+$2-<0$3$4$5$6$7+&6$25#3#7???8000$25$24++$25$2>#1$2;$=$>$?$10$11$24+$24#110#7???8000+&6+$24#110#3#7???8000+$24#120+&6+$24#120#3#7???8000$2;$27$1:$2>$1<$1=$1>$1?,,2?%#10000#134000!##13:<?8,8#7???8000!##13:=00,4#1'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0!$2-8,8$30!$2-10,8$31!$2-18,8$32!$2-20,8$33!$2-28,8$34!$2-30,8$35!$2-38,8$36!$2-40,8$37!$2-48,8$38!$2-50,8$39!$2-58,8$3:!$2-60,8$3;!$2-68,8$3<!$2-;8,8$26!$2-;0,8+&6+$24#100#3#7???8000!$2-:8,8+$24#100!$2-:0,8+&6+$24#?0#3#7???8000!$2-98,8+$24#?0!$2-90,8+&6+$25#8#3#7???8000!$2-88,8+&6+$25#10#3#7???8000!$2-80,8+$25#10!$2-78,8+$25#8!$2-70,8+$25#1'$24#691000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-<0#<0$24##128'$25#691000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-<0#<0$25##18)$24##128$25##18!$25#,1$28'$28##??'&9$28#1##'$2;#1#4000'$2>##8000000,46!"%pstring).
Definition s1 : sym_state := snd (snd ex1).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool := SegFn.in_foot_f F0L b k w.
Definition in_kn0 (K : kentry) : bool := SegFn.in_kn_f kn0 K.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := SegFn.live_f SPV spoff b k.
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry := SegFn.cells_of_f live in_foot in_kn0 sF spoff.
Definition spoff_of (sF : sym_state) : Z := SegFn.spoff_of_f SPV sF.
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SegFn.ps_f 717620 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Ja_f5412e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726808 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ja_f5412e.IT SegItab_Ja_f5412e.IT_sound BF NX0 BR XSTEP F0 PSS plan 726808 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
