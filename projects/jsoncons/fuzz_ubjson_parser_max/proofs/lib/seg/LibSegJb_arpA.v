(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Jb0PlanKit Jb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Jb_2b70ad.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Jb_2b70ad.ITR.
Definition IT : itab := SegItab_Jb_2b70ad.IT.
Definition ENDS : list Z := ltac:(SegCodec.D ",4#;1>64#;1=28#;1<>4#;1<68"%pstring).
Definition STOPS1 : list Z := [728676; 728360; 728292; 728168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1$2$3$4$5$6$7$8$9$24$26$25$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",?%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#693000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 728072 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",1$2-50#50"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",1$2-50#50"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,8#;1>64#;1=28#;1<>4#;1<68#;1>64#;1=28#;1<>4#;1<68#5;#;1<30,20#$1+$2-50$3$4$5$6$7$8$9$24$26$25$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#693000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).
Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.
Definition ex3 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,8#;1>64#;1=28#;1<>4#;1<68#;1>64#;1=28#;1<>4#;1<68#5=#;1>64,20#$1$2$3$4$5$6$7$8$9##$25$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,19'&4&1$26##1#1#1!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#693000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).
Definition ex4 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,8#;1>64#;1=28#;1<>4#;1<68#;1>64#;1=28#;1<>4#;1<68#5;#;1<64,20#$1+$2-50$3$4$5$6$7$26$25$21$26$25$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,19'&4&1$26##1##!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#693000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).
Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.
Definition ex6 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,8#;1>64#;1=28#;1<>4#;1<68#;1>64#;1=28#;1<>4#;1<68#5=#;1<68,20#$1+$2-50$3$4$5$6$7$26$25$21$26$25$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1:'&4&1$21##1#1#1'&4&1$26##1##!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#693000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).
Definition ex7 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,8#;1>64#;1=28#;1<>4#;1<68#;1>64#;1=28#;1<>4#;1<68#5;#;1<>0,20#$1+$2-50$3$4$5$6$7$26$25#$26$21$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1:'&4&1$21##1##'&4&1$26##1##!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#693000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).
Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.
Definition ex9 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,8#;1>64#;1=28#;1<>4#;1<68#;1>64#;1=28#;1<>4#;1<68#5=#;1<>4,20#$1+$2-50$3$4$5$6$7$26$25#$26$21$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1;'&4$21$26#1#1'&4&1$21##1##'&4&1$26##1##!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#693000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s9 : sym_state := snd (snd ex9).
Definition ex10 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,8#;1>64#;1=28#;1<>4#;1<68#;1>64#;1=28#;1<>4#;1<68#5=#;1=28,20#$1+$2-50$3$4$5$6$7$26$25#$26$21$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1;'&4$21$26##'&4&1$21##1##'&4&1$26##1##!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#693000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 3)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 2)) (SGA.mkplan (fst ex10) (SGP.PEnd 1))))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool := SegFn.in_foot_f F0L b k w.
Definition in_kn0 (K : kentry) : bool := SegFn.in_kn_f kn0 K.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := SegFn.live_f SPV spoff b k.
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry := SegFn.cells_of_f live in_foot in_kn0 sF spoff.
Definition spoff_of (sF : sym_state) : Z := SegFn.spoff_of_f SPV sF.
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SegFn.ps_f 728676 regs_out0 F0L cells0.
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s10).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s10).
Definition ps1 : SR.post_spec := SegFn.ps_f 728360 regs_out1 F0L cells1.
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s9).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s9).
Definition ps2 : SR.post_spec := SegFn.ps_f 728292 regs_out2 F0L cells2.
Definition regs_out3 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s6).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s6).
Definition ps3 : SR.post_spec := SegFn.ps_f 728168 regs_out3 F0L cells3.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Jb_2b70ad.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 728072 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Jb_2b70ad.IT SegItab_Jb_2b70ad.IT_sound BF NX0 BR XSTEP F0 PSS plan 728072 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
