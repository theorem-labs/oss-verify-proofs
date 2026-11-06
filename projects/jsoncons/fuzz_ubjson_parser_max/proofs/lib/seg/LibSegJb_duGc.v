(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Jb0PlanKit Jb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Jb_7e70c6.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Jb_7e70c6.ITR.
Definition IT : itab := SegItab_Jb_7e70c6.IT.
Definition ENDS : list Z := [1136476].
Definition STOPS1 : list Z := [1136476] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1$2$3$4$5$6$7##138;:8$:$;$<$=$>$?$10$11$76$77$78#690;00$7:$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",30'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#136000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-10#10$21#+$22#1(##138;:8#4(##138;<8#8(##138;=0#8(##138;>0#8(##138<00#8(##138<08#8!##138<00,8+$2#80!##138<08,8#50!##690;00,8$28!$2#28,8$28!$2#68,8#11>124!$2#60,8#138;:8!$2#58,8+$22#>!$2#50,8#690;00!$2#48,8#1!$2#40,8#6912=8!$2#38,8#!$2#30,8$16!##138;:8,4#5!$2#1:0,8$28!$2#1=8,8#67<>8!$2#1=0,8#16222!$2#1<8,8#138;:8!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:7630!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#114?94!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30"%pstring).
Definition ss0 : sym_state := SS 1167688 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",7$2-10#10##138;:8#4##138;<8#8##138;=0#8##138;>0#8##138<00#8##138<08#8"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",7$2-10#10##138;:8#4##138;<8#8##138;=0#8##138;>0#8##138<00#8##138<08#8"%pstring).
Definition BF : nat := 200000.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#11575<#11575<#5=#11575<,20##114?98+$2#2:0$3$4$5$6$7$29$2:$8$28$28$=$>$?$10$11$2;$2<$2=$2>$2?$30$18$19$1:$1;$1<$1=$1>$1?,,33!##138;:8,4#5!##138<08,8#!##138<00,8#6912=8!##138;>0,8#!##138;=0,8#!##138;<8,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#136000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-10#10$21#+$22#1(##138;:8#4(##138;<8#8(##138;=0#8(##138;>0#8(##138<00#8(##138<08#8!##690;00,8$28!$2#28,8$28!$2#68,8#11>124!$2#60,8#138;:8!$2#58,8+$22#>!$2#50,8#690;00!$2#48,8#1!$2#40,8#6912=8!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#67<>8!$2#1=0,8#16222!$2#1<8,8#138;:8!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:7630!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#114?94!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30,8<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool := SegFn.in_foot_f F0L b k w.
Definition in_kn0 (K : kentry) : bool := SegFn.in_kn_f kn0 K.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := SegFn.live_f SPV spoff b k.
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry := SegFn.cells_of_f live in_foot in_kn0 sF spoff.
Definition spoff_of (sF : sym_state) : Z := SegFn.spoff_of_f SPV sF.
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SegFn.ps_f 1136476 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Jb_7e70c6.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1167688 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Jb_7e70c6.IT SegItab_Jb_7e70c6.IT_sound BF NX0 BR XSTEP F0 PSS plan 1167688 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
