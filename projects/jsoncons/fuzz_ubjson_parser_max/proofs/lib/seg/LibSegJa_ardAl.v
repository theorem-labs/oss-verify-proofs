(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin SegPlanAutoX Ja0PlanKit Ja0PlanKitIt asan.XIcptA asan.XIcptAs0Kit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Ja_2188d5.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast XIcptAFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ja_2188d5.ITR.
Definition IT : itab := SegItab_Ja_2188d5.IT.
Definition ENDS : list Z := [1023764].
Definition STOPS1 : list Z := [1023764; 488240; 488248] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1$2$3$4$5$6$7$8$9$21+$21-170+$21#1=0$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",1>'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#12<000#134000!##13:<?8,8#7???8000!##13:=00,4#1'+$21-170#691000#7???6<:0&+$21-170#8)##7???7000#100000001000+$21-170##360)$2-1000#1000+$21-170##360)##10000#681000+$21-170##360#&6+$21-170#3#7???8000#22#&6+$21#1=0#3#7???8000#4&$21#8($21##180#&6$21#3#7???8000#30!##132638,8#13:<?8!##13:<?8,8#7???8000!##132640,8#13;9>8!##13;9>8,8#!##132648,8#13;9?0!##13;9?0,8#!##132650,8#13;9>0!##13;9>0,8#7???????????!##1331:0,8#13;9=9!##13;9=9,1#1!##134648,8#124=;0!##134640,8#1249:<###8001=94<#40###8001>04<#20"%pstring).
Definition ss0 : sym_state := SS 700860 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",2$2-1000#1000$21##180"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",2$2-1000#1000$21##180"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := ltac:(SegCodec.D ",2#77330,#77338,1"%pstring).
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
(([SGAX.AStep (SR.SBlock [1023764; 488240; 488248; 1023764]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1023764; 488240; 488248; 1023764])], (93, SS 1023764 [ELit 0; ELit 703012; EAlu Instr.ALU_ADD (EVar 2) (ELit (-192)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EAlu Instr.ALU_ADD (EVar 33) (ELit 32); EAlu Instr.ALU_ADD (EVar 33) (ELit 48); EAlu Instr.ALU_ADD (EVar 33) (ELit 160); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; EAlu Instr.ALU_ADD (EVar 33) (ELit 112); ELit 2147450880; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 112)) (ELit 3)) (ELit 2147450880); EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 168 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 144 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 128 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 120 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 48)); KWord {| a_base := EVar 33; a_off := 148 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -208 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 703012); KWord {| a_base := EVar 33; a_off := 40 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 112 |} 8 (ELit 1231912); KWord {| a_base := EVar 33; a_off := 32 |} 8 (ELit 1231872); KWord {| a_base := EVar 33; a_off := 160 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -168 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit (-368))); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 701632); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 464)); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -88 |} 8 (ELit 701080); KWord {| a_base := EVar 33; a_off := 20 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 16 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 12 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 9 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 8 |} 1 (ELit 1); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1231640); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1228800 1261568; KWord {| a_base := ELit 0; a_off := 1289464 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1289472 |} 4 (ELit 1); KRange (EAlu Instr.ALU_ADD (EVar 33) (ELit (-368))) 6885376 2147445920; KAlign (EAlu Instr.ALU_ADD (EVar 33) (ELit (-368))) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-368)); a_off := 0 |} (ELit 864); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-368)); a_off := 0 |} (ELit 864); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6819840) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-368)); a_off := 0 |} (ELit 864); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (-368))) (ELit 3); a_off := 2147450880 |} (ELit 34); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 464)) (ELit 3); a_off := 2147450880 |} (ELit 4); KAlign (EVar 33) 8; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 384); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 48); KWord {| a_base := ELit 0; a_off := 1254968 |} 8 (ELit 1289464); KWord {| a_base := ELit 0; a_off := 1289464 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1254976 |} 8 (ELit 1292776); KWord {| a_base := ELit 0; a_off := 1292776 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1254984 |} 8 (ELit 1292784); KWord {| a_base := ELit 0; a_off := 1292784 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1254992 |} 8 (ELit 1292768); KWord {| a_base := ELit 0; a_off := 1292768 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1257888 |} 8 (ELit 1292761); KWord {| a_base := ELit 0; a_off := 1292761 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1263176 |} 8 (ELit 1199536); KWord {| a_base := ELit 0; a_off := 1263168 |} 8 (ELit 1198508); KZero {| a_base := ELit 0; a_off := 2147604812 |} (ELit 64); KZero {| a_base := ELit 0; a_off := 2147606604 |} (ELit 32)] 76))).
Definition s1 : sym_state := snd (snd ex1).
Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 1023764 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Ja_2188d5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 700860 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.
Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ja_2188d5.IT SegItab_Ja_2188d5.IT_sound BF NX0 BR XSTEP F0 PSS plan 700860 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
