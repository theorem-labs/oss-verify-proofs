(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ja0PlanKit Ja0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Ja_65c305.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ja_65c305.ITR.
Definition IT : itab := SegItab_Ja_65c305.IT.
Definition ENDS : list Z := [725872].
Definition STOPS1 : list Z := [725872] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",53%#10000#134000!##13:<?8,8#7???8000!##13:=00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#691000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#691000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#691000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#691000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124000!$2?#,8#41;58:;3!$2?#8,8#132:5!$2?#10,8#;0><4!$2-80,8$2?!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45!&6$2?#3#7???8000,1#?1!&6$2?#3#7???8001,1#?1!&6$2?#3#7???8002,1#?1!&6$2?#3#7???8003,1#?1!&6$2?#3#7???8004,1#?8!&6$2?#3#7???8005,1#?3!&6$2?#3#7???8006,1#?3!&6$2?#3#7???8007,1#?3!$25#,8#12<940###8001=930#1###8001=931#1!$24#10,1#!$2-70,8$32'$32##1000000"%pstring).
Definition ss0 : sym_state := SS 725592 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",5$24#8#1$2-:0#20$2?##8+&6$2?#3#7???8000##8$30##1"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",5$24#8#1$2-:0#20$2?##8+&6$2?#3#7???8000##8$30##1"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#;1370#;1370#5=#;1370,20#$39$2$3$4$5$6$7$3:$3;$30#1#$26$26#:8774#25930$11$3<$3=$3>$3?$40$41$42$43$44$45$1<$1=$1>$1?,,53!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#1!$2-88,8#;129<'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#691000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#691000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#691000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#691000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124000!$2?#8,8#132:5!$2?#10,8#;0><4!$2-80,8$2?!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45!$25#,8#12<940###8001=930#1###8001=931#1!$24#10,1#!$2-70,8$32'$32##1000000,48!"%pstring).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 725872 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Ja_65c305.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725592 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ja_65c305.IT SegItab_Ja_65c305.IT_sound BF NX0 BR XSTEP F0 PSS plan 725592 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
