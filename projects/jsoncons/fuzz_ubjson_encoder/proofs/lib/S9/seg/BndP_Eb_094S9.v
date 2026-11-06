(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin SegPlanAutoX Eb0PlanKit Eb0PlanKitIt asan.XIcptAB0S9 asan.XIcptAs0KitB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegPlanFast XIcptAFastB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndT_Eb_002S9 BndT_Eb_000S9.

Module LibSegEb_aicAh.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_debb71.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_debb71.IT.
Definition ENDS : list Z := [1069460].
Definition STOPS1 : list Z := [1069460; 495156; 495164] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-40#8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?802000#800000000000&$2#10($2-1000#1000%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#10007???8040#7????????>>7&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#68<000$21##110)$2-1000#1000$21-40#18)##10000#68<000$21-40#18!##13=8<8,8#1460?8!##1460?8,8#7???8000!##13=8=0,8#146=>8!##146=>8,8#!##13=8=8,8#146=?0!##146=?0,8#!##13=8>0,8#146=>0!##146=>0,8#7???????????!##13>430,8#146==9!##146==9,1#1!##13?8=8,8#130034!##13?8=0,8#12?<30###8001?69>#20#&6$2#3#7???7>00#200"%pstring).
Definition ss0 : sym_state := SS 695816 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 16); ((EVar 33), (120), ELit 136)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 16); ((EVar 33), (120), 136)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(495156, 0%nat); (495164, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1069460; 495156; 495164; 1069460]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069460; 495156; 495164; 1069460])], (93, SS 1069460 [ELit 0; ELit 696160; EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EVar 33; EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EVar 33) (ELit 168); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; ELit 8; EAlu Instr.ALU_ADD (EVar 33) (ELit (-64)); ELit 1291640; EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880); ELit 2147450880; ELit 1291576; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)) (ELit 3)) (ELit 2147450880); ELit 1291616; EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 176 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 152 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 144 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 128 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 16)); KWord {| a_base := EVar 33; a_off := 156 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 696160); KWord {| a_base := EVar 33; a_off := 8 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 120 |} 8 (ELit 1291728); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1291688); KWord {| a_base := EVar 33; a_off := 168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1273856 1306624; KWord {| a_base := ELit 0; a_off := 1335544 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1335552 |} 4 (ELit 1); KRange (EVar 33) 17594333495360 140737488355047; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 34); KWr {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6864896) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6864896) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KWord {| a_base := ELit 0; a_off := 1300680 |} 8 (ELit 1335544); KWord {| a_base := ELit 0; a_off := 1335544 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1300688 |} 8 (ELit 1338856); KWord {| a_base := ELit 0; a_off := 1338856 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1300696 |} 8 (ELit 1338864); KWord {| a_base := ELit 0; a_off := 1338864 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1300704 |} 8 (ELit 1338848); KWord {| a_base := ELit 0; a_off := 1338848 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1303600 |} 8 (ELit 1338841); KWord {| a_base := ELit 0; a_off := 1338841 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1308888 |} 8 (ELit 1245236); KWord {| a_base := ELit 0; a_off := 1308880 |} 8 (ELit 1244208); KZero {| a_base := ELit 0; a_off := 2147612318 |} (ELit 32); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512)] 76))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1069460 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_debb71.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 695816 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFastB0S9.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_debb71.IT BndT_Eb_002S9.SegItab_Eb_debb71.IT_sound BF NX0 BR XSTEP F0 PSS plan 695816 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegEb_aicAh.

Module LibSegEb_aicAl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_debb71.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_debb71.IT.
Definition ENDS : list Z := [1069460].
Definition STOPS1 : list Z := [1069460; 495156; 495164] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-40#8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?802000#800000000000&$2#10($2-1000#1000%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<040#7???6>?0&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#68<000$21##110)$2-1000#1000$21-40#18)##10000#68<000$21-40#18!##13=8<8,8#1460?8!##1460?8,8#7???8000!##13=8=0,8#146=>8!##146=>8,8#!##13=8=8,8#146=?0!##146=?0,8#!##13=8>0,8#146=>0!##146=>0,8#7???????????!##13>430,8#146==9!##146==9,1#1!##13?8=8,8#130034!##13?8=0,8#12?<30###8001?69>#20#&6$2#3#7???7>00#200"%pstring).
Definition ss0 : sym_state := SS 695816 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 16); ((EVar 33), (120), ELit 136)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 16); ((EVar 33), (120), 136)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(495156, 0%nat); (495164, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1069460; 495156; 495164; 1069460]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069460; 495156; 495164; 1069460])], (93, SS 1069460 [ELit 0; ELit 696160; EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EVar 33; EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EVar 33) (ELit 168); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; ELit 8; EAlu Instr.ALU_ADD (EVar 33) (ELit (-64)); ELit 1291640; EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880); ELit 2147450880; ELit 1291576; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)) (ELit 3)) (ELit 2147450880); ELit 1291616; EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 176 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 152 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 144 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 128 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 16)); KWord {| a_base := EVar 33; a_off := 156 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 696160); KWord {| a_base := EVar 33; a_off := 8 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 120 |} 8 (ELit 1291728); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1291688); KWord {| a_base := EVar 33; a_off := 168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1273856 1306624; KWord {| a_base := ELit 0; a_off := 1335544 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1335552 |} 4 (ELit 1); KRange (EVar 33) 6930496 2147446512; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 34); KWr {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6864896) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6864896) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KWord {| a_base := ELit 0; a_off := 1300680 |} 8 (ELit 1335544); KWord {| a_base := ELit 0; a_off := 1335544 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1300688 |} 8 (ELit 1338856); KWord {| a_base := ELit 0; a_off := 1338856 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1300696 |} 8 (ELit 1338864); KWord {| a_base := ELit 0; a_off := 1338864 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1300704 |} 8 (ELit 1338848); KWord {| a_base := ELit 0; a_off := 1338848 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1303600 |} 8 (ELit 1338841); KWord {| a_base := ELit 0; a_off := 1338841 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1308888 |} 8 (ELit 1245236); KWord {| a_base := ELit 0; a_off := 1308880 |} 8 (ELit 1244208); KZero {| a_base := ELit 0; a_off := 2147612318 |} (ELit 32); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512)] 76))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1069460 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_debb71.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 695816 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFastB0S9.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_debb71.IT BndT_Eb_002S9.SegItab_Eb_debb71.IT_sound BF NX0 BR XSTEP F0 PSS plan 695816 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegEb_aicAl.

Module LibSegEb_aliA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_284f5f.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_284f5f.IT.
Definition ENDS : list Z := [1069552].
Definition STOPS1 : list Z := [1069552; 495156] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26'$2#7???7?802000#800000000000&$2#10($2-1000#1000'$21#69<000#7??????????8&$21#8)##7???7000#100000001000$21##8)$2-1000#1000$21##8($21##8%#10000#13?000!##1460?8,8#7???8000!##146100,4#1%#6789;2#6790?0(##6789;2#73>%#679818#679870(##679818#58!##69:413,1#!##69:4?0,4#!##69:1<0,8$22!##13=8<8,8#1460?8!##1460?8,8#7???8000!##13=8=0,8#146=>8!##146=>8,8#!##13=8=8,8#146=?0!##146=?0,8#!##13=8>0,8#146=>0!##146=>0,8#7???????????!##13>430,8#146==9!##146==9,1#1!##13?8=8,8#130034!##13?8=0,8#12?<30!##146==8,1#1!##13?700,8#12?<00!##1=7=26,1#1!##1=7=27,1#1###800<712>#?8###800<72?;#1;###7???=70=#4>#&6$2#3#7???7>00#200"%pstring).
Definition ss0 : sym_state := SS 1069460 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 8); ((ELit 0), (6785458), ELit 1854); ((ELit 0), (6789144), ELit 88)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 8); ((ELit 0), (6785458), 1854); ((ELit 0), (6789144), 88)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(495156, 0%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069552; 495156; 1069552])], (93, SS 1069552 [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 529; EVar 530; EVar 531; EVar 8; EVar 9; ELit 6787008; ELit 6787008; EVar 534; EVar 535; EVar 536; EVar 537; EVar 538; EVar 539; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 540; EVar 541; EVar 542; EVar 543] [] [KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 6787008); KWord {| a_base := ELit 0; a_off := 6785969 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785968 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785960 |} 8 (ELit 6787008); KWord {| a_base := ELit 0; a_off := 6785953 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785952 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785944 |} 8 (ELit 6787008); KWord {| a_base := ELit 0; a_off := 6787280 |} 8 (ELit 6786552); KWord {| a_base := ELit 0; a_off := 6787032 |} 8 (ELit 6787288); KWord {| a_base := EVar 2; a_off := -272 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -256 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -248 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -240 |} 8 (ELit 6786560); KWord {| a_base := EVar 2; a_off := -232 |} 8 (ELit 29); KWord {| a_base := EVar 2; a_off := -224 |} 8 (ELit 6787008); KWord {| a_base := EVar 2; a_off := -216 |} 8 (ELit 6787024); KWord {| a_base := EVar 2; a_off := -208 |} 8 (ELit 6786552); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 1043300); KWord {| a_base := ELit 0; a_off := 6786560 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6789216 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6789224 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6789192 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6789148 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6785776 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785784 |} 4 (ELit 30); KWord {| a_base := ELit 0; a_off := 6785792 |} 4 (ELit 30); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-168))); KWord {| a_base := EVar 2; a_off := -168 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-184))); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 6785776); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -152 |} 8 (ELit 6785928); KWord {| a_base := EVar 2; a_off := -144 |} 8 (ELit 6785936); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 1292712); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 6787008); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 1033412); KWord {| a_base := ELit 0; a_off := 6786552 |} 8 (ELit 1298784); KWord {| a_base := ELit 0; a_off := 6787272 |} 8 (ELit 6786536); KWord {| a_base := ELit 0; a_off := 6786544 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785760 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785768 |} 4 (ELit 29); KWord {| a_base := ELit 0; a_off := 6786536 |} 8 (ELit 1298648); KWord {| a_base := ELit 0; a_off := 6787264 |} 8 (ELit 6786760); KWord {| a_base := ELit 0; a_off := 6786768 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785616 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785624 |} 4 (ELit 28); KWord {| a_base := ELit 0; a_off := 6786776 |} 8 (ELit 178536); KWord {| a_base := ELit 0; a_off := 6786760 |} 8 (ELit 1296656); KWord {| a_base := ELit 0; a_off := 6787256 |} 8 (ELit 6786736); KWord {| a_base := ELit 0; a_off := 6786744 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785600 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785608 |} 4 (ELit 27); KWord {| a_base := ELit 0; a_off := 6786752 |} 8 (ELit 178536); KWord {| a_base := ELit 0; a_off := 6786736 |} 8 (ELit 1296536); KWord {| a_base := ELit 0; a_off := 6787248 |} 8 (ELit 6786712); KWord {| a_base := ELit 0; a_off := 6786720 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785584 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785592 |} 4 (ELit 26); KWord {| a_base := ELit 0; a_off := 6786728 |} 8 (ELit 1295752); KWord {| a_base := ELit 0; a_off := 6786712 |} 8 (ELit 1295656); KWord {| a_base := ELit 0; a_off := 6787240 |} 8 (ELit 6786688); KWord {| a_base := ELit 0; a_off := 6786696 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785568 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785576 |} 4 (ELit 25); KWord {| a_base := ELit 0; a_off := 6786704 |} 8 (ELit 1295480); KWord {| a_base := ELit 0; a_off := 6786688 |} 8 (ELit 1295384); KWord {| a_base := ELit 0; a_off := 6787232 |} 8 (ELit 6786520); KWord {| a_base := ELit 0; a_off := 6786528 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785744 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785752 |} 4 (ELit 24); KWord {| a_base := ELit 0; a_off := 6786520 |} 8 (ELit 1298520); KWord {| a_base := ELit 0; a_off := 6787224 |} 8 (ELit 6786504); KWord {| a_base := ELit 0; a_off := 6786512 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785728 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785736 |} 4 (ELit 23); KWord {| a_base := ELit 0; a_off := 6786504 |} 8 (ELit 1298392); KWord {| a_base := ELit 0; a_off := 6787216 |} 8 (ELit 6786488); KWord {| a_base := ELit 0; a_off := 6786496 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785712 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785720 |} 4 (ELit 22); KWord {| a_base := ELit 0; a_off := 6786488 |} 8 (ELit 1298264); KWord {| a_base := ELit 0; a_off := 6787208 |} 8 (ELit 6786472); KWord {| a_base := ELit 0; a_off := 6786480 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785696 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785704 |} 4 (ELit 21); KWord {| a_base := ELit 0; a_off := 6786472 |} 8 (ELit 1298136); KWord {| a_base := ELit 0; a_off := 6787200 |} 8 (ELit 6786456); KWord {| a_base := ELit 0; a_off := 6786464 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785680 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785688 |} 4 (ELit 20); KWord {| a_base := ELit 0; a_off := 6786456 |} 8 (ELit 1297424); KWord {| a_base := ELit 0; a_off := 6787192 |} 8 (ELit 6786440); KWord {| a_base := ELit 0; a_off := 6786448 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785664 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785672 |} 4 (ELit 19); KWord {| a_base := ELit 0; a_off := 6786440 |} 8 (ELit 1297256); KWord {| a_base := ELit 0; a_off := 6787184 |} 8 (ELit 6786424); KWord {| a_base := ELit 0; a_off := 6786432 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785648 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785656 |} 4 (ELit 18); KWord {| a_base := ELit 0; a_off := 6786424 |} 8 (ELit 1297088); KWord {| a_base := ELit 0; a_off := 6787176 |} 8 (ELit 6786408); KWord {| a_base := ELit 0; a_off := 6786416 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785632 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785640 |} 4 (ELit 17); KWord {| a_base := ELit 0; a_off := 6786408 |} 8 (ELit 1296904); KWord {| a_base := ELit 0; a_off := 6787168 |} 8 (ELit 6786392); KWord {| a_base := ELit 0; a_off := 6786400 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785552 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785560 |} 4 (ELit 16); KWord {| a_base := ELit 0; a_off := 6786392 |} 8 (ELit 1295184); KWord {| a_base := ELit 0; a_off := 6787160 |} 8 (ELit 6786376); KWord {| a_base := ELit 0; a_off := 6786384 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785536 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785544 |} 4 (ELit 15); KWord {| a_base := ELit 0; a_off := 6786376 |} 8 (ELit 1294968); KWord {| a_base := ELit 0; a_off := 6787152 |} 8 (ELit 6786360); KWord {| a_base := ELit 0; a_off := 6786368 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785520 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785528 |} 4 (ELit 14); KWord {| a_base := ELit 0; a_off := 6786360 |} 8 (ELit 1294744); KWord {| a_base := ELit 0; a_off := 6787144 |} 8 (ELit 6786344); KWord {| a_base := ELit 0; a_off := 6786352 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785504 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785512 |} 4 (ELit 13); KWord {| a_base := ELit 0; a_off := 6786344 |} 8 (ELit 1294504); KWord {| a_base := ELit 0; a_off := 6787136 |} 8 (ELit 6786960); KWord {| a_base := ELit 0; a_off := 6786968 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6786200 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6786208 |} 4 (ELit 12); KWord {| a_base := ELit 0; a_off := 6787000 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6786992 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6786984 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6786976 |} 8 (ELit 188978561070); KWord {| a_base := ELit 0; a_off := 6786960 |} 8 (ELit 1292472); KWord {| a_base := ELit 0; a_off := 6787128 |} 8 (ELit 6786912); KWord {| a_base := ELit 0; a_off := 6786920 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6786184 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6786192 |} 4 (ELit 11); KWord {| a_base := ELit 0; a_off := 6786952 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6786944 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6786936 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6786928 |} 2 (ELit 11310); KWord {| a_base := ELit 0; a_off := 6786912 |} 8 (ELit 1292392); KWord {| a_base := ELit 0; a_off := 6787120 |} 8 (ELit 6786328); KWord {| a_base := ELit 0; a_off := 6786336 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785880 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785888 |} 4 (ELit 10); KWord {| a_base := ELit 0; a_off := 6786328 |} 8 (ELit 1293608); KWord {| a_base := ELit 0; a_off := 6787112 |} 8 (ELit 6786312); KWord {| a_base := ELit 0; a_off := 6786320 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785848 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785856 |} 4 (ELit 9); KWord {| a_base := ELit 0; a_off := 6786312 |} 8 (ELit 1293304); KWord {| a_base := ELit 0; a_off := 6787104 |} 8 (ELit 6786296); KWord {| a_base := ELit 0; a_off := 6786304 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785864 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785872 |} 4 (ELit 8); KWord {| a_base := ELit 0; a_off := 6786296 |} 8 (ELit 1293456); KWord {| a_base := ELit 0; a_off := 6787096 |} 8 (ELit 6786280); KWord {| a_base := ELit 0; a_off := 6786288 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785832 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785840 |} 4 (ELit 7); KWord {| a_base := ELit 0; a_off := 6786280 |} 8 (ELit 1293152); KWord {| a_base := ELit 0; a_off := 6787088 |} 8 (ELit 6786664); KWord {| a_base := ELit 0; a_off := 6786672 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785816 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785824 |} 4 (ELit 6); KWord {| a_base := ELit 0; a_off := 6786680 |} 8 (ELit 178536); KWord {| a_base := ELit 0; a_off := 6785937 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785936 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785928 |} 8 (ELit 178536); KWord {| a_base := EVar 2; a_off := -192 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6786664 |} 8 (ELit 1292296); KWord {| a_base := ELit 0; a_off := 6787080 |} 8 (ELit 6786264); KWord {| a_base := ELit 0; a_off := 6786272 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785800 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785808 |} 4 (ELit 5); KWord {| a_base := ELit 0; a_off := 6786264 |} 8 (ELit 1292984); KWord {| a_base := ELit 0; a_off := 6787072 |} 8 (ELit 6786248); KWord {| a_base := ELit 0; a_off := 6786256 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6786152 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6786160 |} 4 (ELit 4); KWord {| a_base := ELit 0; a_off := 6786248 |} 8 (ELit 1292776); KWord {| a_base := ELit 0; a_off := 6787064 |} 8 (ELit 6786784); KWord {| a_base := ELit 0; a_off := 6786792 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6786168 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6786176 |} 4 (ELit 3); KWord {| a_base := ELit 0; a_off := 6786808 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6786800 |} 8 (ELit 156536); KWord {| a_base := ELit 0; a_off := 6786784 |} 8 (ELit 1291952); KWord {| a_base := ELit 0; a_off := 6787056 |} 8 (ELit 6786232); KWord {| a_base := ELit 0; a_off := 6786240 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785488 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785496 |} 4 (ELit 2); KWord {| a_base := ELit 0; a_off := 6786232 |} 8 (ELit 1294440); KWord {| a_base := ELit 0; a_off := 6787048 |} 8 (ELit 6786216); KWord {| a_base := ELit 0; a_off := 6786224 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6785472 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6785480 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 6786216 |} 8 (ELit 1294376); KWord {| a_base := ELit 0; a_off := 6787298 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6787296 |} 2 (ELit 17154); KWord {| a_base := ELit 0; a_off := 6787040 |} 8 (ELit 6787288); KWord {| a_base := ELit 0; a_off := 6787024 |} 8 (ELit 6787048); KWord {| a_base := ELit 0; a_off := 6787016 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6787008 |} 8 (ELit 1291784); KWord {| a_base := ELit 0; a_off := 6787288 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -96 |} 8 (ELit 6785928); KWord {| a_base := EVar 2; a_off := -88 |} 8 (ELit 6787008); KWord {| a_base := EVar 2; a_off := -80 |} 8 (ELit 6785952); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 1045480); KWord {| a_base := EVar 2; a_off := -64 |} 8 (ELit 6785928); KWord {| a_base := EVar 2; a_off := -56 |} 8 (ELit 6785968); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -40 |} 8 (ELit 1069580); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KRange (EVar 33) 6930432 140737488355320; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 8); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := 0 |} (ELit 8); KWr {| a_base := EVar 33; a_off := 0 |} (ELit 8); KImg 65536 1306624; KWord {| a_base := ELit 0; a_off := 1335544 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1335552 |} 4 (ELit 1); KImg 6785458 6785472; KImg 6785484 6785488; KImg 6785500 6785504; KImg 6785516 6785520; KImg 6785532 6785536; KImg 6785548 6785552; KImg 6785564 6785568; KImg 6785580 6785584; KImg 6785596 6785600; KImg 6785612 6785616; KImg 6785628 6785632; KImg 6785644 6785648; KImg 6785660 6785664; KImg 6785676 6785680; KImg 6785692 6785696; KImg 6785708 6785712; KImg 6785724 6785728; KImg 6785740 6785744; KImg 6785756 6785760; KImg 6785772 6785776; KImg 6785788 6785792; KImg 6785796 6785800; KImg 6785812 6785816; KImg 6785828 6785832; KImg 6785844 6785848; KImg 6785860 6785864; KImg 6785876 6785880; KImg 6785892 6785928; KImg 6785938 6785944; KImg 6785954 6785960; KImg 6785970 6786152; KImg 6786164 6786168; KImg 6786180 6786184; KImg 6786196 6786200; KImg 6786212 6786216; KImg 6786568 6786664; KImg 6786809 6786912; KImg 6786930 6786936; KImg 6787299 6787312; KWr {| a_base := ELit 0; a_off := 6785458 |} (ELit 1854); KImg 6789144 6789148; KImg 6789152 6789192; KImg 6789200 6789216; KImg 6789220 6789224; KWr {| a_base := ELit 0; a_off := 6789144 |} (ELit 88); KWord {| a_base := ELit 0; a_off := 6923283 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6923504 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6922688 |} 8 (EVar 34); KWord {| a_base := ELit 0; a_off := 1300680 |} 8 (ELit 1335544); KWord {| a_base := ELit 0; a_off := 1335544 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1300688 |} 8 (ELit 1338856); KWord {| a_base := ELit 0; a_off := 1338856 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1300696 |} 8 (ELit 1338864); KWord {| a_base := ELit 0; a_off := 1338864 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1300704 |} 8 (ELit 1338848); KWord {| a_base := ELit 0; a_off := 1338848 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1303600 |} 8 (ELit 1338841); KWord {| a_base := ELit 0; a_off := 1338841 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1308888 |} 8 (ELit 1245236); KWord {| a_base := ELit 0; a_off := 1308880 |} 8 (ELit 1244208); KWord {| a_base := ELit 0; a_off := 1338840 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1308416 |} 8 (ELit 1244160); KWord {| a_base := ELit 0; a_off := 1932582 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1932583 |} 1 (ELit 1); KZero {| a_base := ELit 0; a_off := 2148299054 |} (ELit 248); KZero {| a_base := ELit 0; a_off := 2148299515 |} (ELit 27); KZero {| a_base := ELit 0; a_off := 2147473165 |} (ELit 78); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512)] 544))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1069552 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_284f5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1069460 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFastB0S9.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_284f5f.IT BndT_Eb_000S9.SegItab_Eb_284f5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 1069460 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegEb_aliA.

Module LibSegEb_ardAh.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_6b3691.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_6b3691.IT.
Definition ENDS : list Z := [1069460].
Definition STOPS1 : list Z := [1069460; 495156; 495164] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-1?0+$21#1=0$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'+$21-1?0#10007???8000#7????????<17&+$21-1?0#8)##7???7000#100000001000+$21-1?0##3>0)$2-1000#1000+$21-1?0##3>0)##10000#68<000+$21-1?0##3>0#&6+$21-1?0#3#7???8000#22#&6+$21#1=0#3#7???8000#4&$21#8($21##180#&6$21#3#7???8000#30!##13=8<8,8#1460?8!##1460?8,8#7???8000!##13=8=0,8#146=>8!##146=>8,8#!##13=8=8,8#146=?0!##146=?0,8#!##13=8>0,8#146=>0!##146=>0,8#7???????????!##13>430,8#146==9!##146==9,1#1!##13?8=8,8#130034!##13?8=0,8#12?<30###8001>?70#40###8001?69>#20"%pstring).
Definition ss0 : sym_state := SS 739668 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 384)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 384)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(495156, 0%nat); (495164, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1069460; 495156; 495164; 1069460]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069460; 495156; 495164; 1069460])], (93, SS 1069460 [ELit 0; ELit 741172; EAlu Instr.ALU_ADD (EVar 2) (ELit (-224)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EAlu Instr.ALU_ADD (EVar 33) (ELit 32); EAlu Instr.ALU_ADD (EVar 33) (ELit 112); EAlu Instr.ALU_ADD (EVar 33) (ELit 160); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; EAlu Instr.ALU_ADD (EVar 33) (ELit 48); ELit 2147450880; ELit 1277080; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)) (ELit 3)) (ELit 2147450880); ELit 1277104; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 112)) (ELit 3)) (ELit 2147450880); EVar 24; EVar 25; EVar 26; EVar 27; EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 168 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 144 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 128 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 120 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 48)); KWord {| a_base := EVar 33; a_off := 148 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -240 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -232 |} 8 (ELit 741172); KWord {| a_base := EVar 33; a_off := 40 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 112 |} 8 (ELit 1277256); KWord {| a_base := EVar 33; a_off := 32 |} 8 (ELit 1277216); KWord {| a_base := EVar 33; a_off := 160 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -216 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -208 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -192 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))); KWord {| a_base := EVar 2; a_off := -168 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -152 |} 8 (ELit 740628); KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 464)); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -104 |} 8 (ELit 739896); KWord {| a_base := EVar 33; a_off := 20 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 16 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 12 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 9 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 8 |} 1 (ELit 1); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1276984); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1273856 1306624; KWord {| a_base := ELit 0; a_off := 1335544 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1335552 |} 4 (ELit 1); KRange (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 17594333495296 140737488354327; KAlign (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6864896) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) (ELit 3); a_off := 2147450880 |} (ELit 34); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 464)) (ELit 3); a_off := 2147450880 |} (ELit 4); KAlign (EVar 33) 8; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 384); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 48); KWord {| a_base := ELit 0; a_off := 1300680 |} 8 (ELit 1335544); KWord {| a_base := ELit 0; a_off := 1335544 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1300688 |} 8 (ELit 1338856); KWord {| a_base := ELit 0; a_off := 1338856 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1300696 |} 8 (ELit 1338864); KWord {| a_base := ELit 0; a_off := 1338864 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1300704 |} 8 (ELit 1338848); KWord {| a_base := ELit 0; a_off := 1338848 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1303600 |} 8 (ELit 1338841); KWord {| a_base := ELit 0; a_off := 1338841 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1308888 |} 8 (ELit 1245236); KWord {| a_base := ELit 0; a_off := 1308880 |} 8 (ELit 1244208); KZero {| a_base := ELit 0; a_off := 2147610480 |} (ELit 64); KZero {| a_base := ELit 0; a_off := 2147612318 |} (ELit 32)] 76))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1069460 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_6b3691.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 739668 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFastB0S9.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_6b3691.IT BndT_Eb_000S9.SegItab_Eb_6b3691.IT_sound BF NX0 BR XSTEP F0 PSS plan 739668 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegEb_ardAh.

Module LibSegEb_ardAl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_6b3691.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_6b3691.IT.
Definition ENDS : list Z := [1069460].
Definition STOPS1 : list Z := [1069460; 495156; 495164] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-1?0+$21#1=0$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'+$21-1?0#69<000#7???6<20&+$21-1?0#8)##7???7000#100000001000+$21-1?0##3>0)$2-1000#1000+$21-1?0##3>0)##10000#68<000+$21-1?0##3>0#&6+$21-1?0#3#7???8000#22#&6+$21#1=0#3#7???8000#4&$21#8($21##180#&6$21#3#7???8000#30!##13=8<8,8#1460?8!##1460?8,8#7???8000!##13=8=0,8#146=>8!##146=>8,8#!##13=8=8,8#146=?0!##146=?0,8#!##13=8>0,8#146=>0!##146=>0,8#7???????????!##13>430,8#146==9!##146==9,1#1!##13?8=8,8#130034!##13?8=0,8#12?<30###8001>?70#40###8001?69>#20"%pstring).
Definition ss0 : sym_state := SS 739668 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 384)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 384)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(495156, 0%nat); (495164, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1069460; 495156; 495164; 1069460]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1069460; 495156; 495164; 1069460])], (93, SS 1069460 [ELit 0; ELit 741172; EAlu Instr.ALU_ADD (EVar 2) (ELit (-224)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EAlu Instr.ALU_ADD (EVar 33) (ELit 32); EAlu Instr.ALU_ADD (EVar 33) (ELit 112); EAlu Instr.ALU_ADD (EVar 33) (ELit 160); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; EAlu Instr.ALU_ADD (EVar 33) (ELit 48); ELit 2147450880; ELit 1277080; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)) (ELit 3)) (ELit 2147450880); ELit 1277104; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 112)) (ELit 3)) (ELit 2147450880); EVar 24; EVar 25; EVar 26; EVar 27; EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 168 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 144 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 128 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 120 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 48)); KWord {| a_base := EVar 33; a_off := 148 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -240 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -232 |} 8 (ELit 741172); KWord {| a_base := EVar 33; a_off := 40 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 112 |} 8 (ELit 1277256); KWord {| a_base := EVar 33; a_off := 32 |} 8 (ELit 1277216); KWord {| a_base := EVar 33; a_off := 160 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -216 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -208 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -192 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))); KWord {| a_base := EVar 2; a_off := -168 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -152 |} 8 (ELit 740628); KWord {| a_base := EVar 2; a_off := -136 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 464)); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -104 |} 8 (ELit 739896); KWord {| a_base := EVar 33; a_off := 20 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 16 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 12 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 9 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 8 |} 1 (ELit 1); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1276984); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1273856 1306624; KWord {| a_base := ELit 0; a_off := 1335544 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1335552 |} 4 (ELit 1); KRange (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 6930432 2147445792; KAlign (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6864896) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) (ELit 3); a_off := 2147450880 |} (ELit 34); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 464)) (ELit 3); a_off := 2147450880 |} (ELit 4); KAlign (EVar 33) 8; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 384); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 48); KWord {| a_base := ELit 0; a_off := 1300680 |} 8 (ELit 1335544); KWord {| a_base := ELit 0; a_off := 1335544 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1300688 |} 8 (ELit 1338856); KWord {| a_base := ELit 0; a_off := 1338856 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1300696 |} 8 (ELit 1338864); KWord {| a_base := ELit 0; a_off := 1338864 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1300704 |} 8 (ELit 1338848); KWord {| a_base := ELit 0; a_off := 1338848 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1303600 |} 8 (ELit 1338841); KWord {| a_base := ELit 0; a_off := 1338841 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1308888 |} 8 (ELit 1245236); KWord {| a_base := ELit 0; a_off := 1308880 |} 8 (ELit 1244208); KZero {| a_base := ELit 0; a_off := 2147610480 |} (ELit 64); KZero {| a_base := ELit 0; a_off := 2147612318 |} (ELit 32)] 76))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1069460 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_6b3691.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 739668 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFastB0S9.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_6b3691.IT BndT_Eb_000S9.SegItab_Eb_6b3691.IT_sound BF NX0 BR XSTEP F0 PSS plan 739668 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegEb_ardAl.
