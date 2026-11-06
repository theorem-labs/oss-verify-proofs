(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Jb0PlanKit Jb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Jb_fbbef6.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Jb_fbbef6.ITR.
Definition IT : itab := SegItab_Jb_fbbef6.IT.
Definition ENDS : list Z := [723772].
Definition STOPS1 : list Z := [723772] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1$32$3$4$5$6$7$2$32$33$;$<$=$>$?$10$11+&6+$24#120#3#7???8000$24#$15+$24#?0+$24#120+&6+$24#?0#3#7???8000+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",3>%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#693000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8#'$2?#693000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#126000!$2?#20,8#4000'$2=#693000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$24##128$2=##110)$32##38$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#132010!$2=#10,8#131?20!$2=#98,4#!$2=#9<,4#!$2=#:0,8+$2=#10###8001>3??#1###8001>3><#1)$2=##110$2?##80)$2=##110$30##1)&6$2?#3#7???8000#10&6$2=#3#7???8000#22)&6$2?#3#7???8000#10##8001>3??#1)&6$2?#3#7???8000#10##8001>3><#1'$33##3???"%pstring).
Definition ss0 : sym_state := SS 723580 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",2$24#100#28$2=#98#4"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",2$24#100#28$2=#98#4"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#;0;3<#;0;3<#5=#;0;3<,20##;0:?<$32$3$4$5$6$7$2$32+$24#100+$33$50##$>$?$10$11$33$24#$15$33+$24#120+&6+$24#?0#3#7???8000+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,3>!$24#100,8+$33$50!$2=#98,4#2%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#693000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#'$2?#693000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#126000!$2?#20,8#4000'$2=#693000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$24##128$2=##110)$32##38$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#132010!$2=#10,8#131?20!$2=#9<,4#!$2=#:0,8+$2=#10###8001>3??#1###8001>3><#1)$2=##110$2?##80)$2=##110$30##1)&6$2?#3#7???8000#10&6$2=#3#7???8000#22)&6$2?#3#7???8000#10##8001>3??#1)&6$2?#3#7???8000#10##8001>3><#1'$33##3???,51!"%pstring).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 723772 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Jb_fbbef6.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723580 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Jb_fbbef6.IT SegItab_Jb_fbbef6.IT_sound BF NX0 BR XSTEP F0 PSS plan 723580 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
