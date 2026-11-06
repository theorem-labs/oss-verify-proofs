(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ja0PlanKit Ja0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Ja_4fc8d2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ja_4fc8d2.ITR.
Definition IT : itab := SegItab_Ja_4fc8d2.IT.
Definition ENDS : list Z := [708964].
Definition STOPS1 : list Z := [708964] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-100$3$4$5$6$7$2+$2-100$37$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#22?0<$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",59%#10000#134000!##13:<?8,8#7???8000!##13:=00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#691000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#691000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#691000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#12<940###8001=928#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#691000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124000)&6$2?#3#7???8000#10##8001=928#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#681000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#3!$22#18,8$27'$27##??????'$37#5>#??"%pstring).
Definition ss0 : sym_state := SS 705908 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",1$22#18#8"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",1$22#18#8"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#:=164#:=164#5=#:=164,20##:<93<+$2-100$3$4$5$6$7$2+$2-100$24$25$26$=$>$?$10$11+&6+$24#170#3#7???8000$26#22?0<$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,59!$22#18,8+$27#1%#10000#134000!##13:<?8,8#7???8000!##13:=00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#691000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#691000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#691000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#12<940###8001=928#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#691000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124000)&6$2?#3#7???8000#10##8001=928#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#681000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#3'$27##??????'$37#5>#??,48!"%pstring).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 708964 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Ja_4fc8d2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 705908 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ja_4fc8d2.IT SegItab_Ja_4fc8d2.IT_sound BF NX0 BR XSTEP F0 PSS plan 705908 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
