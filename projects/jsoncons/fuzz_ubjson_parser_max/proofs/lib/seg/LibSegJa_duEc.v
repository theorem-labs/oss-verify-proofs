(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ja0PlanKit Ja0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Ja_b2efcd.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ja_b2efcd.ITR.
Definition IT : itab := SegItab_Ja_b2efcd.IT.
Definition ENDS : list Z := [1159864].
Definition STOPS1 : list Z := [1159864] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1$2$3$4$5$6$7$22#136>40$:$;$<$=$>$?$10$11$12$13$14#68>=<0$7:$7;#$7=$22$7?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",2?'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#:?0%#10000#134000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???:<30,8#!##7???:<38,8#(##136>60#8(##136>68#8(##136>78#8!##136>98,8+$2#2:0!##136>:0,8#50!##68>=<0,8$28!$2#28,8$28!$2#68,8#11<>=<!$2#60,8#25!$2#58,8#7???????!$2#50,8#!$2#48,8#7!$2#40,8#136>40!$2#38,8#161;>!$2#30,8#!##136>40,1#5!##136>=0,4#????????!##13;9=9,1#1!##13:<?8,8#7???8000!##134640,8#1249:<!$2#=0,8#68>=<0!$2#220,8$28!$2#288,8#11<2<<!$2#280,8#136>40!$2#278,8#161;5!$2#270,8#68>=<0!$2#268,8#1!$2#260,8#68?598!$2#258,8#5!$2#250,8$16!$2#248,8$17!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##136>88,8#11;27<"%pstring).
Definition ss0 : sym_state := SS 1159952 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",4$2-840#:?0##136>60#8##136>68#8##136>78#8"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",4$2-840#:?0##136>60#8##136>68#8##136>78#8"%pstring).
Definition BF : nat := 200000.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#11;2;8#11;2;8#5=#11;2;8,20##11<2><+$2#220$3$4+$2#2:6$6$7##136>40$28###11;27<##50#55#54#68>=<0#1#68?598#68>=<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,46!$2#248,8$28!$2#250,8$16!$2#258,8#!$2#260,8#68?598!$2#268,8#1!$2#270,8#68>=<0!$2#278,8+$22#>!$2#280,8#136>40!$2#288,8#11<2><!##136>68,8+$2#2:7!$2#2:6,1#:!$2#2:5,1#54!$2#2:4,1#55!$2#2:3,1#50!$2#2:2,1#4>!$2#2:1,1#49!$2#2:0,1#20!$2-20,8#!$2-18,8#161;>!$2-10,8#7!$2-8,8#161<5!$2#,8#136>40!$2#8,8#!$2#10,8#161;>!$2#18,8#7!$2#20,8#136>40!$2#28,8#11;=78!$2#38,8#161<5!$2#40,8#136>40!$2#48,8+$22#7!$2#50,8+@-1$22#7??????8!$2#58,8#7???????!$2#60,8#25!$2#68,8#11<4;<!##136>78,8+$2#2:0!##136>60,8+$2#2?0'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#820,$2#30#8,$2#70#1=8,$2#290#10,$2#2:7#9%#10000#134000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???:<30,8#!##7???:<38,8#(##136>60#8(##136>68#8(##136>78#8!##136>98,8+$2#2:0!##136>:0,8#50!##68>=<0,8$28!$2#30,8#!##136>40,1#5!##136>=0,4#????????!##13;9=9,1#1!##13:<?8,8#7???8000!##134640,8#1249:<!$2#=0,8#68>=<0!$2#220,8$28!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##136>88,8#11;27<,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 1159864 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Ja_b2efcd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1159952 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ja_b2efcd.IT SegItab_Ja_b2efcd.IT_sound BF NX0 BR XSTEP F0 PSS plan 1159952 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
