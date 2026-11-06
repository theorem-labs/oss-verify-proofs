(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Js0PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := ltac:(SegCodec.D ",1#36?04,3?"%pstring).
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := ltac:(SegCodec.D ",2#36?80#36?34"%pstring).
Definition STOPS1 : list Z := [225152; 225076] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-20$3$4$5$6$7$23$22$2;$;$<$=$>$?$10$11$21$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",:'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800000#7????????>=8&$21#8)$2-20#20$21##128!$21#108,8$2:($21#118#10'$2;##4000'$23#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 225132 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",1$21#118#10"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",1$21#118#10"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36?80#36?34#36?80#36?34#5;#36?7<,20#$1+$2-20$3$4$5$6$7$23$22$2:$2;$<$=$>$?$10$11$21$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,<!$21#120,8$2;!$21#118,8$2:'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800000#7????????>=8&$21#8)$2-20#20$21##128!$21#108,8$2:($21#118#10'$2;##4000'$23#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).
Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.
Definition ex3 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36?80#36?34#36?80#36?34#5:#36?80,20#$1+$2-20$3$4$5$6$7$23$22$2:$2;$<$=$>$?$10$11$21$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,='&4$2;$23#1#1!$21#120,8$2;!$21#118,8$2:'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800000#7????????>=8&$21#8)$2-20#20$21##128!$21#108,8$2:($21#118#10'$2;##4000'$23#1^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).
Definition ex4 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36?80#36?34#36?80#36?34#5:#36?34,20#$1+$2-20$3$4$5$6$7$23$22$2:$2;$<$=$>$?$10$11$21$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,='&4$2;$23##!$21#120,8$2;!$21#118,8$2:'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800000#7????????>=8&$21#8)$2-20#20$21##128!$21#108,8$2:($21#118#10'$2;##4000'$23#1^#?#???????????????,38!"%pstring).
Definition s4 : sym_state := snd (snd ex4).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 225152 regs_out0 F0L cells0.
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SegFn.ps_f 225076 regs_out1 F0L cells1.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 225132 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 225132 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
