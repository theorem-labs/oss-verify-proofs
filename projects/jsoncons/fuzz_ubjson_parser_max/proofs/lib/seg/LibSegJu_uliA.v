(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ju0PlanKit Ju0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Ju_61aa9b.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ju_61aa9b.ITR.
Definition IT : itab := SegItab_Ju_61aa9b.IT.
Definition ENDS : list Z := [526700].
Definition STOPS1 : list Z := [526700] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1$2$3$4$5$6$7$8$9$21$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",?'$2#7???7?800400#800000000000&$2#10($2-400#400'$21#7???7?800400#7??????????8&$21#8)$2-400#400$21##8($21##8%#10000#;7120%#<74>2#<7<20(##<74>2#73>%#<8348#<83:0(##<8348#58%#>8?43#>8?44%#>9018#>901<!##>8?20,8$22"%pstring).
Definition ss0 : sym_state := SS 526608 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",4$2-400#400$21##8##<74>2#73>##<8348#58"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",4$2-400#400$21##8##<74>2#73>##<8348#58"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",40!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<!$!!,2#8096<#8096<#5=#8096<,20#$1$2$3$4$211$212$213$8$9#<7:?0#<7:?0$216$217$218$219$21:$21;$12$13$14$15$16$17$18$19$1:$1;$21<$21=$21>$21?,,11>!$21#,8#<7:?0!##<76>1,1#1!##<76>0,1#1!##<76=8,8#<7:?0!##<76=1,1#1!##<76=0,1#1!##<76<8,8#<7:?0!##<7<00,8#<7928!##<7;08,8#<7<08!$2-110,8$18!$2-108,8$17!$2-100,8$16!$2-?8,8$15!$2-?0,8#<7930!$2->8,8#1=!$2->0,8#<7:?0!$2-=8,8#<7;00!$2-=0,8#<7928!$2-<8,8#7:2>0!##<7930,8#1!##<8390,4#!##<8398,8#!##<8378,8#!$2-144,4#!$2-140,8$22!$2-138,8#1!$2-130,8$14!$2-128,8#<8348!$2-120,8+$2-;0!$2-118,8#<8348!##<834<,4#!$2-158,8$19!$2-150,8$18!##<7620,8^#?#???????????????!##<7628,4#1>!##<7630,4#1>!$2-;0,8+$2-:8!$2-:8,8+$2-;8!$2-;8,8#<7620!$2-:0,8$14!$2-98,8#<76;8!$2-90,8#<76<0!$2-88,8#;3?58!$2-80,8#<7:?0!$2-78,8#77<40!##<7928,8#;5710!##<7;?8,8#<7918!##<7920,8#1!##<7610,8^#?#???????????????!##<7618,4#1=!##<7918,8#;5688!##<7;?0,8#<79?8!##<7:00,8#1!##<7580,8^#?#???????????????!##<7588,4#1<!##<7:08,8#1:=28!##<79?8,8#;4><0!##<7;>8,8#<79>0!##<79>8,8#1!##<7570,8^#?#???????????????!##<7578,4#1;!##<79?0,8#1:=28!##<79>0,8#;4>48!##<7;>0,8#<79<8!##<79=0,8#1!##<7560,8^#?#???????????????!##<7568,4#1:!##<79=8,8#;4;38!##<79<8,8#;4:=8!##<7;=8,8#<79;0!##<79;8,8#1!##<7550,8^#?#???????????????!##<7558,4#19!##<79<0,8#;4:28!##<79;0,8#;49<8!##<7;=0,8#<7908!##<7910,8#1!##<7600,8^#?#???????????????!##<7608,4#18!##<7908,8#;5608!##<7;<8,8#<78?8!##<7900,8#1!##<75?0,8^#?#???????????????!##<75?8,4#17!##<78?8,8#;5588!##<7;<0,8#<78>8!##<78?0,8#1!##<75>0,8^#?#???????????????!##<75>8,4#16!##<78>8,8#;5508!##<7;;8,8#<78=8!##<78>0,8#1!##<75=0,8^#?#???????????????!##<75=8,4#15!##<78=8,8#;5488!##<7;;0,8#<78<8!##<78=0,8#1!##<75<0,8^#?#???????????????!##<75<8,4#14!##<78<8,8#;51<0!##<7;:8,8#<78;8!##<78<0,8#1!##<75;0,8^#?#???????????????!##<75;8,4#13!##<78;8,8#;5118!##<7;:0,8#<78:8!##<78;0,8#1!##<75:0,8^#?#???????????????!##<75:8,4#12!##<78:8,8#;5070!##<7;98,8#<7898!##<78:0,8#1!##<7590,8^#?#???????????????!##<7598,4#11!##<7898,8#;4?;8!##<7;90,8#<7888!##<7890,8#1!##<7540,8^#?#???????????????!##<7548,4#10!##<7888,8#;4900!##<7;88,8#<7878!##<7880,8#1!##<7530,8^#?#???????????????!##<7538,4#?!##<7878,8#;4828!##<7;80,8#<7868!##<7870,8#1!##<7520,8^#?#???????????????!##<7528,4#>!##<7868,8#;4748!##<7;78,8#<7858!##<7860,8#1!##<7510,8^#?#???????????????!##<7518,4#=!##<7858,8#;4658!##<7;70,8#<7:<0!##<7:<8,8#1!##<77<8,8^#?#???????????????!##<77=0,4#<!##<7:>8,8#!##<7:>0,8#!##<7:=8,8#!##<7:=0,8#2<0000002>!##<7:<0,8#;3>68!##<7;68,8#<7:90!##<7:98,8#1!##<77;8,8^#?#???????????????!##<77<0,4#;!##<7:;8,8#!##<7:;0,8#!##<7::8,8#!##<7::0,2#2<2>!##<7:90,8#;3>18!##<7;60,8#<7848!##<7850,8#1!##<7688,8^#?#???????????????!##<7690,4#:!##<7848,8#;42=8!##<7;58,8#<7838!##<7840,8#1!##<7668,8^#?#???????????????!##<7670,4#9!##<7838,8#;41:8!##<7;50,8#<7828!##<7830,8#1!##<7678,8^#?#???????????????!##<7680,4#8!##<7828,8#;4240!##<7;48,8#<7818!##<7820,8#1!##<7658,8^#?#???????????????!##<7660,4#7!##<7818,8#;4110!##<7;40,8#<7998!##<79:0,8#1!##<7648,8^#?#???????????????!##<7650,4#6!##<79:8,8#1:=28!##<76<1,1#1!##<76<0,1#1!##<76;8,8#1:=28!$2-<0,8#!##<7998,8#;3=;8!##<7;38,8#<7808!##<7810,8#1!##<7638,8^#?#???????????????!##<7640,4#5!##<7808,8#;4068!##<7;30,8#<77?8!##<7800,8#1!##<7798,8^#?#???????????????!##<77:0,4#4!##<77?8,8#;3?98!##<7;28,8#<7:10!##<7:18,8#1!##<77:8,8^#?#???????????????!##<77;0,4#3!##<7:28,1#!##<7:20,8#160=0!##<7:10,8#;3<60!##<7;20,8#<77>8!##<77?0,8#1!##<7500,8^#?#???????????????!##<7508,4#2!##<77>8,8#;4618!##<7;18,8#<77=8!##<77>0,8#1!##<74?0,8^#?#???????????????!##<74?8,4#1!##<77=8,8#;45=8!##<7<12,1#!##<7<10,2#4302!##<7;10,8#<7<08!##<7;00,8#<7;18!##<7:?8,8#!##<7:?0,8#;3;;8!##<7<08,8#1!$2-68,8$13!$2-60,8#<76;8!$2-58,8#<7:?0!$2-50,8#<76=0!$2-48,8#7:;64!$2-40,8#<76;8!$2-38,8#<76>0!$2-30,8$21!$2-28,8#80988!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800400#800000000000&$2#10($2-400#400'$21#7???7?800400#7??????????8&$21#8)$2-400#400$21##8($21##8%#10000#;7120%#<74>2#<74?0%#<74?<#<7500%#<750<#<7510%#<751<#<7520%#<752<#<7530%#<753<#<7540%#<754<#<7550%#<755<#<7560%#<756<#<7570%#<757<#<7580%#<758<#<7590%#<759<#<75:0%#<75:<#<75;0%#<75;<#<75<0%#<75<<#<75=0%#<75=<#<75>0%#<75><#<75?0%#<75?<#<7600%#<760<#<7610%#<761<#<7620%#<762<#<7630%#<7634#<7638%#<7644#<7648%#<7654#<7658%#<7664#<7668%#<7674#<7678%#<7684#<7688%#<7694#<76;8%#<76<2#<76<8%#<76=2#<76=8%#<76>2#<7798%#<77:4#<77:8%#<77;4#<77;8%#<77<4#<77<8%#<77=4#<77=8%#<7938#<7998%#<7:29#<7:90%#<7::2#<7::8%#<7<13#<7<20(##<74>2#73>%#<8348#<834<%#<8350#<8378%#<8380#<8390%#<8394#<8398(##<8348#58%#>8?43#>8?44%#>9018#>901<!##>8?20,8$22,220!"%pstring).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 526700 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Ju_61aa9b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 526608 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := ub0_plan_sound_it SegItab_Ju_61aa9b.IT SegItab_Ju_61aa9b.IT_sound BF NX0 BR XSTEP F0 PSS plan 526608 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
