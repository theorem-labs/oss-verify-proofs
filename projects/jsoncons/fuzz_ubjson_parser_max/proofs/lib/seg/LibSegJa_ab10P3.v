(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ja0PlanKit Ja0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Ja_bb8283.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ja_bb8283.ITR.
Definition IT : itab := SegItab_Ja_bb8283.IT.
Definition ENDS : list Z := ltac:(SegCodec.D ",3#;07?<#;0840#;07:0"%pstring).
Definition STOPS1 : list Z := [722940; 723008; 722848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-10$3$4#7???8000#1??9#23880$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",7'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2"%pstring).
Definition ss0 : sym_state := SS 722784 regs0 [] kn0 NX0.
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
Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.
Definition ex2 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5;#;07><,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,8'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).
Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.
Definition ex4 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5=#;07?<,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:#1#1'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).
Definition ex5 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5=#;0840,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4+$25-30#:##'&4&1$24#5#1#1#1'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).
Definition ex6 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5;#;0764,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).
Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.
Definition ex8 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5;#;07><,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9$21$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,9'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).
Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.
Definition ex10 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5=#;07?<,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9+$21#1+$21#1#5$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:#1#1'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).
Definition ex11 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5=#;0840,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9#$21+$25-30$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9$21#7$1=$1>$1?,,:'&4+$25-30#:##'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).
Definition ex12 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5;#;0768,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9$21$21$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).
Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.
Definition ex14 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5;#;0788,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,:'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).
Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.
Definition ex16 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5;#;0794,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9$21$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,;'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).
Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.
Definition ex18 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5=#;0840,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1#1#1'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).
Definition ex19 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5=#;07:0,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9$21$21+@#4&9+$25-2=#??#23880$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;&9&6#1??9+$25-2=#1$1=$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1##'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).
Definition ex20 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5=#;0840,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9#$21&9+$25-2=#??$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;+$25-2=$1=$1>$1?,,;'&4&9+$25-2=#??#=##'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).
Definition ex21 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,6#;07?<#;0840#;07:0#;07?<#;0840#;07:0#5=#;07?<,20#$1+$2-10$3$4#7???8000#1??9#23880$8$9+$21#1+$21#1$24$22#5#:#1#=$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$24##1##'&4&1$24#1#1##'&4&1$24#5#1##'$21##800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).
Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PEnd 1)))) (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 2)) (SGA.mkplan (fst ex11) (SGP.PEnd 3)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 4)) (SGA.mkplan (fst ex19) (SGP.PEnd 5)))) (SGA.mkplan (fst ex20) (SGP.PEnd 6)))) (SGA.mkplan (fst ex21) (SGP.PEnd 7)))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool := SegFn.in_foot_f F0L b k w.
Definition in_kn0 (K : kentry) : bool := SegFn.in_kn_f kn0 K.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := SegFn.live_f SPV spoff b k.
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry := SegFn.cells_of_f live in_foot in_kn0 sF spoff.
Definition spoff_of (sF : sym_state) : Z := SegFn.spoff_of_f SPV sF.
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SegFn.ps_f 722940 regs_out0 F0L cells0.
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s5).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s5).
Definition ps1 : SR.post_spec := SegFn.ps_f 723008 regs_out1 F0L cells1.
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SegFn.ps_f 722940 regs_out2 F0L cells2.
Definition regs_out3 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s11).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s11).
Definition ps3 : SR.post_spec := SegFn.ps_f 723008 regs_out3 F0L cells3.
Definition regs_out4 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s18).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s18).
Definition ps4 : SR.post_spec := SegFn.ps_f 723008 regs_out4 F0L cells4.
Definition regs_out5 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s19).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s19).
Definition ps5 : SR.post_spec := SegFn.ps_f 722848 regs_out5 F0L cells5.
Definition regs_out6 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s20).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s20).
Definition ps6 : SR.post_spec := SegFn.ps_f 723008 regs_out6 F0L cells6.
Definition regs_out7 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s21).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s21).
Definition ps7 : SR.post_spec := SegFn.ps_f 722940 regs_out7 F0L cells7.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Ja_bb8283.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 722784 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ja_bb8283.IT SegItab_Ja_bb8283.IT_sound BF NX0 BR XSTEP F0 PSS plan 722784 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
