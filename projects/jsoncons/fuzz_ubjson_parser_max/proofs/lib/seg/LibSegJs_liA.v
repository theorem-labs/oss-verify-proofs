(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Js0PlanKit Js0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Js_a45200.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Js_a45200.ITR.
Definition IT : itab := SegItab_Js_a45200.IT.
Definition ENDS : list Z := [522520].
Definition STOPS1 : list Z := [522520] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1$2$3$4$5$6$7$8$9$21$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",?'$2#7???7?800400#800000000000&$2#10($2-400#400'$21#7???7?800400#7??????????8&$21#8)$2-400#400$21##8($21##8%#10000#;60=0%#<6492#<6;=0(##<6492#73>%#<72?8#<7350(##<72?8#58%#>7>?3#>7>?4%#>7?<8#>7?<<!##>7>=0,8$22"%pstring).
Definition ss0 : sym_state := SS 522428 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",4$2-400#400$21##8##<6492#73>##<72?8#58"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",4$2-400#400$21##8##<6492#73>##<72?8#58"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",40!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918!$!!,2#7?918#7?918#5=#7?918,20#$1$2$3$4$211$212$213$8$9#<6::0#<6::0$216$217$218$219$21:$21;$12$13$14$15$16$17$18$19$1:$1;$21<$21=$21>$21?,,11>!$21#,8#<6::0!##<6691,1#1!##<6690,1#1!##<6688,8#<6::0!##<6681,1#1!##<6680,1#1!##<6678,8#<6::0!##<6;;0,8#<68=8!##<6:;8,8#<6;;8!$2-110,8$18!$2-108,8$17!$2-100,8$16!$2-?8,8$15!$2-?0,8#<68>0!$2->8,8#1=!$2->0,8#<6::0!$2-=8,8#<6:;0!$2-=0,8#<68=8!$2-<8,8#7928<!##<68>0,8#1!##<7340,4#!##<7348,8#!##<7328,8#!$2-144,4#!$2-140,8$22!$2-138,8#1!$2-130,8$14!$2-128,8#<72?8!$2-120,8+$2-;0!$2-118,8#<72?8!##<72?<,4#!$2-158,8$19!$2-150,8$18!##<65=0,8^#?#???????????????!##<65=8,4#1>!##<65>0,4#1>!$2-;0,8+$2-:8!$2-:8,8+$2-;8!$2-;8,8#<65=0!$2-:0,8$14!$2-98,8#<6668!$2-90,8#<6670!$2-88,8#;2?08!$2-80,8#<6::0!$2-78,8#76;><!##<68=8,8#;46<0!##<6;:8,8#<68<8!##<68=0,8#1!##<65<0,8^#?#???????????????!##<65<8,4#1=!##<68<8,8#;4638!##<6;:0,8#<69:8!##<69;0,8#1!##<6530,8^#?#???????????????!##<6538,4#1<!##<69;8,8#1:=28!##<69:8,8#;3>70!##<6;98,8#<6990!##<6998,8#1!##<6520,8^#?#???????????????!##<6528,4#1;!##<69:0,8#1:=28!##<6990,8#;3=?8!##<6;90,8#<6978!##<6980,8#1!##<6510,8^#?#???????????????!##<6518,4#1:!##<6988,8#;3:>8!##<6978,8#;3:88!##<6;88,8#<6960!##<6968,8#1!##<6500,8^#?#???????????????!##<6508,4#19!##<6970,8#;39=8!##<6960,8#;3978!##<6;80,8#<68;8!##<68<0,8#1!##<65;0,8^#?#???????????????!##<65;8,4#18!##<68;8,8#;45;8!##<6;78,8#<68:8!##<68;0,8#1!##<65:0,8^#?#???????????????!##<65:8,4#17!##<68:8,8#;4538!##<6;70,8#<6898!##<68:0,8#1!##<6590,8^#?#???????????????!##<6598,4#16!##<6898,8#;44;8!##<6;68,8#<6888!##<6890,8#1!##<6580,8^#?#???????????????!##<6588,4#15!##<6888,8#;4438!##<6;60,8#<6878!##<6880,8#1!##<6570,8^#?#???????????????!##<6578,4#14!##<6878,8#;4170!##<6;58,8#<6868!##<6870,8#1!##<6560,8^#?#???????????????!##<6568,4#13!##<6868,8#;40<8!##<6;50,8#<6858!##<6860,8#1!##<6550,8^#?#???????????????!##<6558,4#12!##<6858,8#;4020!##<6;48,8#<6848!##<6850,8#1!##<6540,8^#?#???????????????!##<6548,4#11!##<6848,8#;3?68!##<6;40,8#<6838!##<6840,8#1!##<64?0,8^#?#???????????????!##<64?8,4#10!##<6838,8#;38;0!##<6;38,8#<6828!##<6830,8#1!##<64>0,8^#?#???????????????!##<64>8,4#?!##<6828,8#;37=8!##<6;30,8#<6818!##<6820,8#1!##<64=0,8^#?#???????????????!##<64=8,4#>!##<6818,8#;36?8!##<6;28,8#<6808!##<6810,8#1!##<64<0,8^#?#???????????????!##<64<8,4#=!##<6808,8#;3608!##<6;20,8#<6:70!##<6:78,8#1!##<6778,8^#?#???????????????!##<6780,4#<!##<6:98,8#!##<6:90,8#!##<6:88,8#!##<6:80,8#2<0000002>!##<6:70,8#;2>18!##<6;18,8#<6:40!##<6:48,8#1!##<6768,8^#?#???????????????!##<6770,4#;!##<6:68,8#!##<6:60,8#!##<6:58,8#!##<6:50,2#2<2>!##<6:40,8#;2=<8!##<6;10,8#<67?8!##<6800,8#1!##<6638,8^#?#???????????????!##<6640,4#:!##<67?8,8#;3288!##<6;08,8#<67>8!##<67?0,8#1!##<6618,8^#?#???????????????!##<6620,4#9!##<67>8,8#;3158!##<6;00,8#<67=8!##<67>0,8#1!##<6628,8^#?#???????????????!##<6630,4#8!##<67=8,8#;31?0!##<6:?8,8#<67<8!##<67=0,8#1!##<6608,8^#?#???????????????!##<6610,4#7!##<67<8,8#;30<0!##<6:?0,8#<6948!##<6950,8#1!##<65?8,8^#?#???????????????!##<6600,4#6!##<6958,8#1:=28!##<6671,1#1!##<6670,1#1!##<6668,8#1:=28!$2-<0,8#!##<6948,8#;2=68!##<6:>8,8#<67;8!##<67<0,8#1!##<65>8,8^#?#???????????????!##<65?0,4#5!##<67;8,8#;3018!##<6:>0,8#<67:8!##<67;0,8#1!##<6748,8^#?#???????????????!##<6750,4#4!##<67:8,8#;2?48!##<6:=8,8#<69<0!##<69<8,8#1!##<6758,8^#?#???????????????!##<6760,4#3!##<69=8,1#!##<69=0,8#160=0!##<69<0,8#;2<10!##<6:=0,8#<6798!##<67:0,8#1!##<64;0,8^#?#???????????????!##<64;8,4#2!##<6798,8#;35<8!##<6:<8,8#<6788!##<6790,8#1!##<64:0,8^#?#???????????????!##<64:8,4#1!##<6788,8#;3588!##<6;<2,1#!##<6;<0,2#4302!##<6:<0,8#<6;;8!##<6:;0,8#<6:<8!##<6::8,8#!##<6::0,8#;2;68!##<6;;8,8#1!$2-68,8$13!$2-60,8#<6668!$2-58,8#<6::0!$2-50,8#<6680!$2-48,8#79;10!$2-40,8#<6668!$2-38,8#<6690!$2-30,8$21!$2-28,8#7?934!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800400#800000000000&$2#10($2-400#400'$21#7???7?800400#7??????????8&$21#8)$2-400#400$21##8($21##8%#10000#;60=0%#<6492#<64:0%#<64:<#<64;0%#<64;<#<64<0%#<64<<#<64=0%#<64=<#<64>0%#<64><#<64?0%#<64?<#<6500%#<650<#<6510%#<651<#<6520%#<652<#<6530%#<653<#<6540%#<654<#<6550%#<655<#<6560%#<656<#<6570%#<657<#<6580%#<658<#<6590%#<659<#<65:0%#<65:<#<65;0%#<65;<#<65<0%#<65<<#<65=0%#<65=<#<65>0%#<65>4#<65>8%#<65?4#<65?8%#<6604#<6608%#<6614#<6618%#<6624#<6628%#<6634#<6638%#<6644#<6668%#<6672#<6678%#<6682#<6688%#<6692#<6748%#<6754#<6758%#<6764#<6768%#<6774#<6778%#<6784#<6788%#<68>8#<6948%#<69=9#<6:40%#<6:52#<6:58%#<6;<3#<6;=0(##<6492#73>%#<72?8#<72?<%#<7300#<7328%#<7330#<7340%#<7344#<7348(##<72?8#58%#>7>?3#>7>?4%#>7?<8#>7?<<!##>7>=0,8$22,220!"%pstring).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 522520 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Js_a45200.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 522428 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := src0_plan_sound_it SegItab_Js_a45200.IT SegItab_Js_a45200.IT_sound BF NX0 BR XSTEP F0 PSS plan 522428 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
