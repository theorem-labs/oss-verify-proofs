(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ja0PlanKit Ja0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Ja_e52b2a.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ja_e52b2a.ITR.
Definition IT : itab := SegItab_Ja_e52b2a.IT.
Definition ENDS : list Z := [1163204].
Definition STOPS1 : list Z := [1163204] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20##:7640$2$3$4$5$6$7$8$9#14><<+$2#18$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",24'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#<:0%#10000#134000#&6$2#3#7???7?8:#18!##7???:9=8,8#!##800<9>;0,8#(##136?30#4(##136?38#8(##136?40#8(##136?50#8(##136?58#8(##136?68#8(##136?78#8(##136?;8#4(##68?5:0#1!##13;9=8,1#1!##1<<87<,1#1!##13:<?8,8#7???8000!##1344<0,8#1224:8!##1344<8,8#11<1<4!##68>=<0,8$28!##136?;<,4#????????!##136?30,4#5!##136?90,8#400!##136?50,8#!##136?;8,4#!##136?88,8#68?5:0!##136?<0,4#:!##13;9=9,1#1!##134640,8#1249:<!$2#18,4#!##134648,8#124=;0!##136?78,8#11;?68!##136?:8,4#1"%pstring).
Definition ss0 : sym_state := SS 404052 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",:$2-<:0#<:0##136?30#4##136?38#8##136?40#8##136?50#8##136?58#8##136?68#8##136?78#8##136?;8#4##68?5:0#1"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",:$2-<:0#<:0##136?30#4##136?38#8##136?40#8##136?50#8##136?58#8##136?68#8##136?78#8##136?;8#4##68?5:0#1"%pstring).
Definition BF : nat := 200000.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#11;?<4#11;?<4#5=#11;?<4,20##11;=5<+$2-450$3$4#$6$7#68>=<0#1#1#5413+$2-450#14><>#5413#1#136?30#1=#14><>#1##14><?#1#14><>#1##1#1$1<$1=$1>$1?,,<2!##136?78,8#11;27<!$2-448,8$28!$2-440,8#136?30!$2-438,8#11;=5<!$2-428,8#14><?!$2-420,8#136?30!$2-418,8#1!$2-410,8#7??????>!$2-408,8#7???????!$2-400,8#25!$2-3?8,8#11<4;<!##136?58,8#68?5:1!$2-480,8#1!$2-478,8+$2-340!$2-470,8#!$2-468,8#14><>!$2-460,8#136?30!$2-458,8#!$2-450,8+$2-340!##68?5:0,1#30!$2-340,1#30!$2-430,8#!$2-3>8,8#!$2-3=0,8#1!$2-3>0,8#!$2-3?0,8#10=<3!$2-3=8,8#!$2-380,8#!$2-1=0,8+$2#20!$2-3<8,8^#?#???????<<<<<<<=!$2-3<0,8^#?#??????????>????!$2-388,8#<<<<<<<!$2-3:0,8#12889!$2-240,8$28!$2-390,8#68>=<0!$2-398,8#!$2-3:8,8+$2-1=0!$2-3;8,8+$2-170!$2-3;0,8+$2-<8!$2-238,8$1;!$2-230,8$1:!$2-228,8$19!$2-220,8$18!$2-218,8$17!$2-210,8$16!$2-208,8#5!$2-200,8#!$2-1?8,8#1!$2-1?0,8#68>=<0!$2-1>8,8#14><<!$2-1>0,8#136?30!$2-1=8,8#11<2<<!##136?50,8#68?9:0!##136?40,8#!##136?38,8#!##136?68,8#68?5:0!##136?;8,4^#?#???????????????!##136?30,4#5!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,8#!$2-:8,8#!$2-1<8,8+$2#18!$2-:0,8$28!$2-98,8$15!$2-90,8$14!$2-88,8$13!$2-80,8+$2#18!$2-78,8#136?30!$2-70,8#14><<!$2-68,8#67168!$2-900,8^#?#???????????????!$2-8>1,1#!$2-8>2,1#!$2-8>3,1#!$2-8>4,1#!$2-8>5,1#!$2-8>6,1#!$2-8>7,1#!$2-8>8,1#!$2-8>9,1#!$2-8>:,1#!$2-8>;,1#!$2-8><,1#!$2-8>=,1#!$2-8>>,1#!$2-8>?,1#!$2-8?0,1#!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?4,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-8?8,1#!$2-901,1#!$2-902,1#!$2-903,1#!$2-904,1#!$2-905,1#!$2-906,1#!$2-907,1#!$2-908,1#!$2-940,8#:!$2-938,8#14><<!$2-930,8+$2-60!$2-928,8#669;<!$2-918,8+$2-=8!$2-910,8#207;0!$2-60,8+$2#18!$2-58,8+$2#18!$2-50,8$12!$2-48,8+$2#18!$2-40,8#14><<!$2-38,8#665?8!$2-8=0,8^#?#???????????????!$2-8;1,1#!$2-8;2,1#!$2-8;3,1#!$2-8;4,1#!$2-8;5,1#!$2-8;6,1#!$2-8;7,1#!$2-8;8,1#!$2-8;9,1#!$2-8;:,1#!$2-8;;,1#!$2-8;<,1#!$2-8;=,1#!$2-8;>,1#!$2-8;?,1#!$2-8<0,1#!$2-8<1,1#!$2-8<2,1#!$2-8<3,1#!$2-8<4,1#!$2-8<5,1#!$2-8<6,1#!$2-8<7,1#!$2-8<8,1#!$2-8=1,1#!$2-8=2,1#!$2-8=3,1#!$2-8=4,1#!$2-8=5,1#!$2-8=6,1#!$2-8=7,1#!$2-8=8,1#!$2-8>0,8#14746!$2-28,8+$2#18!$2-20,8+$2#18!$2-18,8$9!$2-10,8$8!$2-8,8#:7640'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#360,$2-920#8,$2-8;0#430,$2-378#38,$2-33?#??,$2-1<0#?8,$2-30#8%#10000#134000#&6$2#3#7???7?8:#18!##7???:9=8,8#!##800<9>;0,8#(##136?30#4(##136?38#8(##136?40#8(##136?50#8(##136?58#8(##136?68#8(##136?78#8(##136?;8#4(##68?5:0#1!##13;9=8,1#1!##1<<87<,1#1!##13:<?8,8#7???8000!##1344<0,8#1224:8!##1344<8,8#11<1<4!##68>=<0,8$28!##136?;<,4#????????!##136?90,8#400!##136?88,8#68?5:0!##136?<0,4#:!##13;9=9,1#1!##134640,8#1249:<!$2#18,4#!##134648,8#124=;0!##136?:8,4#1,38!"%pstring).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 1163204 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Ja_e52b2a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 404052 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ja_e52b2a.IT SegItab_Ja_e52b2a.IT_sound BF NX0 BR XSTEP F0 PSS plan 404052 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
