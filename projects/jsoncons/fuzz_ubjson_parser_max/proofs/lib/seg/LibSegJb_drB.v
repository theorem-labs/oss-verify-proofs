(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Jb0PlanKit Jb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Jb_624cf6.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Jb_624cf6.ITR.
Definition IT : itab := SegItab_Jb_624cf6.IT.
Definition ENDS : list Z := [404712].
Definition STOPS1 : list Z := [404712] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1$2$3$4$5$6$7+$2#8<0$9$:$;$<$=$>$?$10$11$12#1?0>:$78$79$7:$7;+$2#38^#:#:::::::::::::::^#?#???????????????#25$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",2='$2#7???7?811000#800000000000&$2#10($2-380#<40,$2-380#<40%#10000#136000'$21#7???7?811000#7?????????>?'$22#1#1)$2-380#<40$21#+$22#1#&6$2#3#7???80=>#20!##7???;>18,8#(##138;:8#4(##138;;0#8(##138;;8#8(##138;<8#8(##138;=0#8(##138;>0#8(##138<00#8(##138<08#8(##138<30#4!$2#8;8,8#67<:8!$2#8;0,8#1?0=5!$2#8:8,8#138;:8!$2#8:0,8+$2#900!$2#898,8$13!$2#890,8$14!$2#888,8$15!$2#880,8$16!$2#878,8$17!$2#870,8$18!$2#868,8$19!$2#860,8$1:!$2#858,8$1;!##136230,8#11=??<!$2#8=8,8+$2#900!##690;00,8$28!##138<34,4#????????!##138;:8,4#5!##138<08,8#!##138<00,8#6912=8!##138<30,4#!##138<38,4#????????!##13=719,1#1!##13<:38,8#7???8000!##1363:8,8#1267>4!$2#900,8$21"%pstring).
Definition ss0 : sym_state := SS 421260 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",:$2-380#<40##138;:8#4##138;;0#8##138;;8#8##138;<8#8##138;=0#8##138;>0#8##138<00#8##138<08#8##138<30#4"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",:$2-380#<40##138;:8#4##138;;0#8##138;;8#8##138;<8#8##138;=0#8##138;>0#8##138<00#8##138<08#8##138<30#4"%pstring).
Definition BF : nat := 200000.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#62<>8#62<>8#5=#62<>8,20##11>7<4+$2#530$3$4##6?#6>#25#7???????$21#7???????+$2#750+$2#908#1?^#?#?????????????<6#73#8#7?????><#13#138;:8#1?0>:#$21#^#?#???????????????###20$1=$1>$1?,,96!$2#5:0,8$21!$2#750,8+$2#908!##138;=0,8+$2#773!$2#4:0,8$18!$2#4:8,8#1?0>8!$2#4;0,8#!$2#4;8,8#1?0>8!$2#4<0,8#138;:8!$2#4<8,8#!$2#4=0,8#1?0>8!$2#4=8,8#!$2#4>0,8#138;:8!$2#4>8,8#11=;;0!$2#4?8,8#1?0>8!$2#500,8#138;:8!$2#508,8#13!$2#510,8#7?????><!$2#518,8#7???????!$2#520,8#25!$2#528,8#11>2?4!$2#772,1#20!$2#771,1#6>!$2#770,1#6?!$2#76?,1#20!$2#76>,1#72!$2#76=,1#6?!$2#76<,1#72!$2#76;,1#72!$2#76:,1#65!$2#769,1#20!$2#768,1#64!$2#767,1#61!$2#766,1#65!$2#765,1#72!$2#764,1#20!$2#763,1#3:!$2#762,1#69!$2#761,1#6<!$2#760,1#63!$2#558,8^#?#???????<<<<<<<=!$2#560,8^#?#??????????>????!$2#598,8#<<<<<<<!$2#580,8#12889!$2#6>0,8$28!$2#590,8#690;00!$2#588,8#!$2#578,8+$2#750!$2#568,8+$2#7;0!$2#570,8+$2#858!$2#6>8,8$1;!$2#6?0,8$1:!$2#6?8,8$19!$2#700,8$18!$2#708,8$17!$2#710,8$16!$2#718,8#5!$2#720,8#6912=8!$2#728,8#1!$2#730,8#690;00!$2#738,8#1?0=5!$2#740,8#138;:8!$2#748,8#11>104!##138;<8,8+$2#7;0!##138;;8,8#!##138;;0,8#!##138;>0,8+$2#760!##138<30,4^#?#???????????????!##138<08,8#50!##138<00,8+$2#760!##138;:8,4#5!$2#870,8#!$2#868,8#!$2#860,8#!$2#858,8#!$2#878,8#!$2#758,8+$2#900!$2#880,8$28!$2#888,8$15!$2#890,8$14!$2#898,8$13!$2#8:0,8+$2#900!$2#8:8,8#138;:8!$2#8;0,8#1?0=5!$2#8;8,8#67<>8!$2#20,8^#?#???????????????!$2#3?,1#!$2#3>,1#!$2#3=,1#!$2#3<,1#!$2#3;,1#!$2#3:,1#!$2#39,1#!$2#38,1#!$2#37,1#!$2#36,1#!$2#35,1#!$2#34,1#!$2#33,1#!$2#32,1#!$2#31,1#!$2#30,1#!$2#2?,1#!$2#2>,1#!$2#2=,1#!$2#2<,1#!$2#2;,1#!$2#2:,1#!$2#29,1#!$2#28,1#!$2#1?,1#!$2#1>,1#!$2#1=,1#!$2#1<,1#!$2#1;,1#!$2#1:,1#!$2#19,1#!$2#18,1#'$2#7???7?811000#800000000000&$2#10($2-380#<40,$2-380#398,$2#40#460,$2#4?0#8,$2#530#28,$2#5:8#138,$2#773#>5%#10000#136000'$21#7???7?811000#7?????????>?'$22#1#1)$2-380#<40$21#+$22#1#&6$2#3#7???80=>#20!##7???;>18,8#(##138;:8#4(##138;;0#8(##138;;8#8(##138;<8#8(##138;=0#8(##138;>0#8(##138<00#8(##138<08#8(##138<30#4!##136230,8#11=??<!$2#8=8,8+$2#900!##690;00,8$28!##138<34,4#????????!##138<38,4#????????!##13=719,1#1!##13<:38,8#7???8000!##1363:8,8#1267>4!$2#900,8$21,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 404712 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Jb_624cf6.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 421260 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Jb_624cf6.IT SegItab_Jb_624cf6.IT_sound BF NX0 BR XSTEP F0 PSS plan 421260 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
