(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin SegPlanAutoX Jb0PlanKit Jb0PlanKitIt asan.XIcptAB0 asan.XIcptAs0KitB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Jb_e95983.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast XIcptAFastB0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Jb_e95983.ITR.
Definition IT : itab := SegItab_Jb_e95983.IT.
Definition ENDS : list Z := [1031500].
Definition STOPS1 : list Z := [1031500; 488960; 488968] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1$2$3$4$5$6$7$8$9$21+$21-40#8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",1='$2#7???7?802000#800000000000&$2#10($2-1000#1000%#12=000#136000!##13<:38,8#7???8000!##13<:40,4#1'$21#693040#7???6>?0&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#683000$21##110)$2-1000#1000$21-40#18)##10000#683000$21-40#18!##1343:0,8#13<:38!##13<:38,8#7???8000!##1343:8,8#13=728!##13=728,8#!##1343;0,8#13=730!##13=730,8#!##1343;8,8#13=720!##13=720,8#7???????????!##134?08,8#13=719!##13=719,1#1!##1363;0,8#126;>8!##1363:8,8#1267>4###8001>3?9#20#&6$2#3#7???7>00#200"%pstring).
Definition ss0 : sym_state := SS 689300 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := ltac:(SegCodec.D ",3$2-1000#1000$21##10$21#78#88"%pstring).
Definition F0L : list SR.region := ltac:(SegCodec.D ",3$2-1000#1000$21##10$21#78#88"%pstring).
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := ltac:(SegCodec.D ",2#77600,#77608,1"%pstring).
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
(([SGAX.AStep (SR.SBlock [1031500; 488960; 488968; 1031500]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1031500; 488960; 488968; 1031500])], (93, SS 1031500 [ELit 0; ELit 689644; EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EVar 33; EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EVar 33) (ELit 168); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; ELit 8; EAlu Instr.ALU_ADD (EVar 33) (ELit (-64)); ELit 1253456; EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880); ELit 2147450880; ELit 1253392; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)) (ELit 3)) (ELit 2147450880); ELit 1253432; EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 176 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 152 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 144 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 128 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 16)); KWord {| a_base := EVar 33; a_off := 156 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 689644); KWord {| a_base := EVar 33; a_off := 8 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 120 |} 8 (ELit 1253544); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1253504); KWord {| a_base := EVar 33; a_off := 168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1232896 1269760; KWord {| a_base := ELit 0; a_off := 1296952 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1296960 |} 4 (ELit 1); KRange (EVar 33) 6893632 2147446512; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 34); KWr {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6828032) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6828032) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KWord {| a_base := ELit 0; a_off := 1262496 |} 8 (ELit 1296952); KWord {| a_base := ELit 0; a_off := 1296952 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1262504 |} 8 (ELit 1300264); KWord {| a_base := ELit 0; a_off := 1300264 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1262512 |} 8 (ELit 1300272); KWord {| a_base := ELit 0; a_off := 1300272 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1262520 |} 8 (ELit 1300256); KWord {| a_base := ELit 0; a_off := 1300256 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1265416 |} 8 (ELit 1300249); KWord {| a_base := ELit 0; a_off := 1300249 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1270704 |} 8 (ELit 1207272); KWord {| a_base := ELit 0; a_off := 1270696 |} 8 (ELit 1206244); KZero {| a_base := ELit 0; a_off := 2147607545 |} (ELit 32); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512)] 76))).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 1031500 regs_out0 F0L cells0.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Jb_e95983.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 689300 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFastB0.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.
Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Jb_e95983.IT SegItab_Jb_e95983.IT_sound BF NX0 BR XSTEP F0 PSS plan 689300 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
