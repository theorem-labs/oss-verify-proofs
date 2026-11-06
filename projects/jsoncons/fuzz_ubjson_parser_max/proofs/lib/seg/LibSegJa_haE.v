(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ja0PlanKit Ja0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Ja_03d1de.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ja_03d1de.ITR.
Definition IT : itab := SegItab_Ja_03d1de.IT.
Definition ENDS : list Z := [869816].
Definition STOPS1 : list Z := [869816] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$3:+$2-80$3$4$5$6$7$8+$2-80$:$;$<$=$>$?$10$11$28+&6$28#3#7???8000+$28#20+$28#60$22+$28#1=0$28#7???8000+$28#1;0$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",11'$2#7???7?8010<0#800000000000&$2#20($2-80#80'$28#1000#7????????<00&$28#20,$28##400($28##400)##7???7000#100000001000$28##400(&6$28#3#7???8000#80!$28#3?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##400$29##1)$2-80#90$28##400)$2-80#90$29##1#&6$28#3#7???806:#1"%pstring).
Definition ss0 : sym_state := SS 686856 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",4$28#350#8$28#3>0#4&6$28#3#7???8074#4&6$28#3#7???807<#2"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",4$28#350#8$28#3>0#4&6$28#3#7???8074#4&6$28#3#7???807<#2"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#=45;8#=45;8#5=#=45;8,20##:7;48+$2-80$3$4$5$6$7$8+$2-80+$28#350#$<$=$>$?$10$11$28+&6$28#3#7???8000+$28#20+$28#60+$28#3>0+$28#1=0$28#7???8000^#?#??????????????8$1;$1<$1=$1>$1?,,1;!$28#3>0,4#!&6$28#3#7???8077,1^#?#??????????????8!&6$28#3#7???8076,1^#?#??????????????8!&6$28#3#7???8075,1^#?#??????????????8!&6$28#3#7???8074,1^#?#??????????????8!&6$28#3#7???807=,1#!&6$28#3#7???807<,1#!$28#350,8+$28#1;0'$2#7???7?8010<0#800000000000&$2#20($2-80#80'$28#1000#7????????<00&$28#20,$28##350,$28#358#88,$28#3>4#1<($28##400)##7???7000#100000001000$28##400(&6$28#3#7???8000#80!$28#3?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##400$29##1)$2-80#90$28##400)$2-80#90$29##1#&6$28#3#7???806:#1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 869816 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Ja_03d1de.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 686856 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ja_03d1de.IT SegItab_Ja_03d1de.IT_sound BF NX0 BR XSTEP F0 PSS plan 686856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
