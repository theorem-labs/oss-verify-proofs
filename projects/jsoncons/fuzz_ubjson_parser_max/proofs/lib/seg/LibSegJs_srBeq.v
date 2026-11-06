(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Js0PlanKit Js0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Js_c2742f.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Js_c2742f.ITR.
Definition IT : itab := SegItab_Js_c2742f.IT.
Definition ENDS : list Z := [223660].
Definition STOPS1 : list Z := [223660] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-30$3$4$5$6$7$24$27$:$;$<$=$>$?$10$11$25$27$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355328;
KAlign (EVar 2) 16;
KWr (SA (EVar 2) (-48)) (ELit 48);
KRange (EVar 36) 140735332483120 140737488355032;
KAlign (EVar 36) 8;
KDisj (SA (EVar 2) (-48)) (ELit 48) (SA (EVar 36) 0) (ELit 296);
KWord (SA (EVar 36) (264)) 8 (EVar 34);
KWord (SA (EVar 36) (272)) 8 (ELit 16384);
KWord (SA (EVar 36) (280)) 8 (EVar 35);
KWord (SA (EVar 36) (288)) 8 (EVar 33);
KUnk (SA (EVar 36) 256) (ELit 8);
KWr (SA (EVar 36) 256) (ELit 40);
KWord (SA (EVar 2) (-8)) 8 (EVar 40);
KWord (SA (EVar 2) (-16)) 8 (EVar 41);
KWord (SA (EVar 2) (-24)) 8 (EVar 42);
KWord (SA (EVar 2) (-32)) 8 (EVar 43);
KWord (SA (EVar 2) (-40)) 8 (EVar 44);
KRange (EVar 33) 1 16384;
KRange (EVar 39) 1 16384;
KRange (APC.esub (EVar 33) (EVar 39)) 0 16383;
KRange (EVar 35) 4096 140737488338944].
Definition ss0 : sym_state := SS 223352 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",2$2-30#30$24#100#28"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",2$2-30#30$24#100#28"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#369:<#369:<#5=#369:<,20#$28$2$3$4$5$6$7$29$2:$27+$21@-1$27+$27$30$=$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$24#120,8+$21@-1$27!$24#118,8+$23$27!$24#100,8+$27$30'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000($24#100#28!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<'$21#1#4000'$27#1#4000'+$21@-1$27##3???'$23#1000#7???????<000,31!"%pstring).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 223660 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Js_c2742f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 223352 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := src0_plan_sound_it SegItab_Js_c2742f.IT SegItab_Js_c2742f.IT_sound BF NX0 BR XSTEP F0 PSS plan 223352 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
