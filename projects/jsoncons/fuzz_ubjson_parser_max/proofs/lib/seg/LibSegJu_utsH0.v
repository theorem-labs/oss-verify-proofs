(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ju0PlanKit Ju0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Ju_1f1841.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ju_1f1841.ITR.
Definition IT : itab := SegItab_Ju_1f1841.IT.
Definition ENDS : list Z := ltac:(SegCodec.D ",3#38858#388<4#38974"%pstring).
Definition STOPS1 : list Z := [231512; 231620; 231796] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-50$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$13$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",1:'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;7120!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;3:>8!$26#98,1$36'$36##2'$24#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 231468 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#38858#388<4#38974#38858#388<4#38974#5;#38834,20##38834+$2-50$3$4$5$6$7$23$22&6@^#4#$36#3?#$<$=$>$?$10$11$21$13$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?,,1:'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;7120!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;3:>8!$26#98,1$36'$36##2'$24#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).
Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.
Definition ex3 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#38858#388<4#38974#38858#388<4#38974#5;#38844,20##38834+$2-50$3$4$5$6$7$23$22##$<$=$>$?$10$11$21#4000$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?,,1;'&4&1&6@^#4#$36#3?##1#1#1'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;7120!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;3:>8!$26#98,1$36'$36##2'$24#1^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).
Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.
Definition ex5 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#38858#388<4#38974#38858#388<4#38974#5=#38858,20##38834+$2-50$3$4$5$6$7$23$22#4000#$<$=$>$?$10$11$21$24$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?,,1<'&4$24#4000#1#1'&4&1&6@^#4#$36#3?##1#1#1'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;7120!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;3:>8!$26#98,1$36'$36##2'$24#1^#?#???????????????,38!"%pstring).
Definition s5 : sym_state := snd (snd ex5).
Definition ex6 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#38858#388<4#38974#38858#388<4#38974#5:#388<4,20##38834+$2-50$3$4$5$6$7$23$22##$<$=$>$?$10$11$21#4000$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?,,1<'&4$24#4000##'&4&1&6@^#4#$36#3?##1#1#1'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;7120!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;3:>8!$26#98,1$36'$36##2'$24#1^#?#???????????????,38!"%pstring).
Definition s6 : sym_state := snd (snd ex6).
Definition ex7 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#38858#388<4#38974#38858#388<4#38974#5=#38974,20#$2<$2$3$4$5$6$7$2=$2>+$23@-1$24#$<$=$>$?$10$11$2?$30$31$32$33$34$18$19$1:$1;$1<$1=$1>$1?,,1;'&4&1&6@^#4#$36#3?##1##'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;7120!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;3:>8!$26#98,1$36'$36##2'$24#1^#?#???????????????,38!"%pstring).
Definition s7 : sym_state := snd (snd ex7).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 0)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 2))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool := SegFn.in_foot_f F0L b k w.
Definition in_kn0 (K : kentry) : bool := SegFn.in_kn_f kn0 K.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := SegFn.live_f SPV spoff b k.
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry := SegFn.cells_of_f live in_foot in_kn0 sF spoff.
Definition spoff_of (sF : sym_state) : Z := SegFn.spoff_of_f SPV sF.
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s5).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s5).
Definition ps0 : SR.post_spec := SegFn.ps_f 231512 regs_out0 F0L cells0.
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SegFn.ps_f 231620 regs_out1 F0L cells1.
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SegFn.ps_f 231796 regs_out2 F0L cells2.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Ju_1f1841.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 231468 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := ub0_plan_sound_it SegItab_Ju_1f1841.IT SegItab_Ju_1f1841.IT_sound BF NX0 BR XSTEP F0 PSS plan 231468 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
