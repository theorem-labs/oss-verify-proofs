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
Definition ENDS : list Z := [728676].
Definition STOPS1 : list Z := [728676] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-50$3$4$5$6$7$26$25$:$;$21$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1269760;
KWord (SA (ELit 0) 1296952) 8 (ELit 2147450880);
KWord (SA (ELit 0) 1296960) 4 (ELit 1);
KRange (EVar 2) 140735332487248 140737488355328;
KAlign (EVar 2) 16;
KWr (SA (EVar 2) (-80)) (ELit 80);
KWord (SA (EVar 2) (-8)) 8 (EVar 44);
KWord (SA (EVar 2) (-16)) 8 (EVar 45);
KWord (SA (EVar 2) (-24)) 8 (EVar 46);
KWord (SA (EVar 2) (-32)) 8 (EVar 47);
KWord (SA (EVar 2) (-40)) 8 (EVar 48);
KWord (SA (EVar 2) (-48)) 8 (EVar 49);
KWord (SA (EVar 2) (-56)) 8 (EVar 50);
KWord (SA (EVar 2) (-64)) 8 (EVar 51);
KWord (SA (EVar 2) (-72)) 8 (EVar 52);
KRange (EVar 36) 6893568 140737488355032;
KAlign (EVar 36) 8;
KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
KWr (SA (EVar 36) 0) (ELit 296);
KDisj (SA (EVar 2) (-80)) (ELit 80) (SA (EVar 36) 0) (ELit 296);
KWord (SA (EVar 36) (280)) 8 (EVar 35);
KRange (EVar 35) 1 140737488355328;
KUnk (SA (EVar 36) 256) (ELit 8);
KRange (EVar 33) 1 16384;
KRange (EVar 38) 1 16384;
KRange (APC.esub (EVar 33) (EVar 38)) 0 16383].
Definition ss0 : sym_state := SS 728360 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",2$24#100#8$24#118#10"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",2$24#100#8$24#118#10"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,2#;1>64#;1>64#5=#;1>64,20#$2<$2$3$4$5$6$7$2=$2>$23$26+$26$3<#+$23$26$?$10$11$2?$30$31$32$33$34$18$19$1:$1;$1<$1=$1>$1?,,1<!$24#100,8+$26$3<!$24#120,8+$21@-1$26!$24#118,8+$23$26%#10000#136000!##13<:38,8#7???8000!##13<:40,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$24#693000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128'$23#1#800000000000'$21#1#4000'$26#1#4000'+$21@-1$26##3???,3=!"%pstring).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 728676 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Jb_2b70ad.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 728360 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Jb_2b70ad.IT SegItab_Jb_2b70ad.IT_sound BF NX0 BR XSTEP F0 PSS plan 728360 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
