(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin SegPlanAutoX Ea0PlanKit Ea0PlanKitIt asan.XIcptA asan.XIcptAs0Kit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegPlanFast XIcptAFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Ea_001.

Module LibSegEa_aicAh.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_f67af8.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_f67af8.IT.
Definition ENDS : list Z := [1051116].
Definition STOPS1 : list Z := [1051116; 493068; 493076] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-40#8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?802000#800000000000&$2#10($2-1000#1000%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#10007???8040#7????????>>7&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#688000$21##110)$2-1000#1000$21-40#18)##10000#688000$21-40#18!##1391;8,8#1419?8!##1419?8,8#7???8000!##1391<0,8#1426>8!##1426>8,8#!##1391<8,8#1426?0!##1426?0,8#!##1391=0,8#1426>0!##1426>0,8#7???????????!##139=20,8#1426=9!##1426=9,1#1!##13;1<8,8#12;88<!##13;1<0,8#12;488###8001>=;<#20#&6$2#3#7???7>00#200"%pstring).
Definition ss0 : sym_state := SS 693724 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 16); ((EVar 33), (120), ELit 136)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 16); ((EVar 33), (120), 136)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(493068, 0%nat); (493076, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1051116; 493068; 493076; 1051116]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051116; 493068; 493076; 1051116])], (93, SS 1051116 [ELit 0; ELit 694060; EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EVar 33; EAlu Instr.ALU_ADD (EVar 33) (ELit 168); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; ELit 8; EAlu Instr.ALU_ADD (EVar 33) (ELit (-64)); ELit 1273448; EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)) (ELit 3)) (ELit 2147450880); ELit 1273424; ELit 2147450880; ELit 1273360; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880); EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 176 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 152 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 144 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 128 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 16)); KWord {| a_base := EVar 33; a_off := 156 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 694060); KWord {| a_base := EVar 33; a_off := 8 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 120 |} 8 (ELit 1273536); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1273496); KWord {| a_base := EVar 33; a_off := 168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1253376 1286144; KWord {| a_base := ELit 0; a_off := 1317368 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1317376 |} 4 (ELit 1); KRange (EVar 33) 17594333495360 140737488355047; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 34); KWr {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6848512) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6848512) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KWord {| a_base := ELit 0; a_off := 1282488 |} 8 (ELit 1317368); KWord {| a_base := ELit 0; a_off := 1317368 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1282496 |} 8 (ELit 1320680); KWord {| a_base := ELit 0; a_off := 1320680 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1282504 |} 8 (ELit 1320688); KWord {| a_base := ELit 0; a_off := 1320688 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1282512 |} 8 (ELit 1320672); KWord {| a_base := ELit 0; a_off := 1320672 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1285408 |} 8 (ELit 1320665); KWord {| a_base := ELit 0; a_off := 1320665 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1290696 |} 8 (ELit 1226892); KWord {| a_base := ELit 0; a_off := 1290688 |} 8 (ELit 1225864); KZero {| a_base := ELit 0; a_off := 2147610044 |} (ELit 32); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512)] 76))).
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
Definition ps0 : SR.post_spec := SR.PS 1051116 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_f67af8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 693724 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_f67af8.IT BndT_Ea_001.SegItab_Ea_f67af8.IT_sound BF NX0 BR XSTEP F0 PSS plan 693724 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegEa_aicAh.

Module LibSegEa_aicAl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_f67af8.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_f67af8.IT.
Definition ENDS : list Z := [1051116].
Definition STOPS1 : list Z := [1051116; 493068; 493076] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-40#8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?802000#800000000000&$2#10($2-1000#1000%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698040#7???6>?0&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#688000$21##110)$2-1000#1000$21-40#18)##10000#688000$21-40#18!##1391;8,8#1419?8!##1419?8,8#7???8000!##1391<0,8#1426>8!##1426>8,8#!##1391<8,8#1426?0!##1426?0,8#!##1391=0,8#1426>0!##1426>0,8#7???????????!##139=20,8#1426=9!##1426=9,1#1!##13;1<8,8#12;88<!##13;1<0,8#12;488###8001>=;<#20#&6$2#3#7???7>00#200"%pstring).
Definition ss0 : sym_state := SS 693724 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 16); ((EVar 33), (120), ELit 136)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 16); ((EVar 33), (120), 136)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(493068, 0%nat); (493076, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1051116; 493068; 493076; 1051116]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051116; 493068; 493076; 1051116])], (93, SS 1051116 [ELit 0; ELit 694060; EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EVar 33; EAlu Instr.ALU_ADD (EVar 33) (ELit 168); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; ELit 8; EAlu Instr.ALU_ADD (EVar 33) (ELit (-64)); ELit 1273448; EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)) (ELit 3)) (ELit 2147450880); ELit 1273424; ELit 2147450880; ELit 1273360; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880); EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 176 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 152 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 144 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 128 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 16)); KWord {| a_base := EVar 33; a_off := 156 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 694060); KWord {| a_base := EVar 33; a_off := 8 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 120 |} 8 (ELit 1273536); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1273496); KWord {| a_base := EVar 33; a_off := 168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1253376 1286144; KWord {| a_base := ELit 0; a_off := 1317368 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1317376 |} 4 (ELit 1); KRange (EVar 33) 6914112 2147446512; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 34); KWr {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6848512) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6848512) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KWord {| a_base := ELit 0; a_off := 1282488 |} 8 (ELit 1317368); KWord {| a_base := ELit 0; a_off := 1317368 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1282496 |} 8 (ELit 1320680); KWord {| a_base := ELit 0; a_off := 1320680 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1282504 |} 8 (ELit 1320688); KWord {| a_base := ELit 0; a_off := 1320688 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1282512 |} 8 (ELit 1320672); KWord {| a_base := ELit 0; a_off := 1320672 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1285408 |} 8 (ELit 1320665); KWord {| a_base := ELit 0; a_off := 1320665 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1290696 |} 8 (ELit 1226892); KWord {| a_base := ELit 0; a_off := 1290688 |} 8 (ELit 1225864); KZero {| a_base := ELit 0; a_off := 2147610044 |} (ELit 32); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512)] 76))).
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
Definition ps0 : SR.post_spec := SR.PS 1051116 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_f67af8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 693724 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_f67af8.IT BndT_Ea_001.SegItab_Ea_f67af8.IT_sound BF NX0 BR XSTEP F0 PSS plan 693724 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegEa_aicAl.

Module LibSegEa_aliA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ced162.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ced162.IT.
Definition ENDS : list Z := [1051208].
Definition STOPS1 : list Z := [1051208; 493068] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26'$2#7???7?802000#800000000000&$2#10($2-1000#1000'$21#698000#7??????????8&$21#8)##7???7000#100000001000$21##8)$2-1000#1000$21##8($21##8%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1%#6742;2#6749?0(##6742;2#73>%#675118#675170(##675118#58!##695=13,1#!##695=?0,4#!##695:<0,8$22!##1391;8,8#1419?8!##1419?8,8#7???8000!##1391<0,8#1426>8!##1426>8,8#!##1391<8,8#1426?0!##1426?0,8#!##1391=0,8#1426>0!##1426>0,8#7???????????!##139=20,8#1426=9!##1426=9,1#1!##13;1<8,8#12;88<!##13;1<0,8#12;488!##1426=8,1#1!##13:??0,8#12;458!##1=3626,1#1!##1=3627,1#1###800<684>#?8###800<6:1;#1;###7???=6?9#41#&6$2#3#7???7>00#200"%pstring).
Definition ss0 : sym_state := SS 1051116 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 8); ((ELit 0), (6767282), ELit 1854); ((ELit 0), (6770968), ELit 88)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 8); ((ELit 0), (6767282), 1854); ((ELit 0), (6770968), 88)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(493068, 0%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051208; 493068; 1051208])], (93, SS 1051208 [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 529; EVar 530; EVar 531; EVar 8; EVar 9; ELit 6768832; ELit 6768832; EVar 534; EVar 535; EVar 536; EVar 537; EVar 538; EVar 539; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 540; EVar 541; EVar 542; EVar 543] [] [KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 6768832); KWord {| a_base := ELit 0; a_off := 6767793 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767792 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767784 |} 8 (ELit 6768832); KWord {| a_base := ELit 0; a_off := 6767777 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767776 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767768 |} 8 (ELit 6768832); KWord {| a_base := ELit 0; a_off := 6769104 |} 8 (ELit 6768376); KWord {| a_base := ELit 0; a_off := 6768856 |} 8 (ELit 6769112); KWord {| a_base := EVar 2; a_off := -272 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -256 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -248 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -240 |} 8 (ELit 6768384); KWord {| a_base := EVar 2; a_off := -232 |} 8 (ELit 29); KWord {| a_base := EVar 2; a_off := -224 |} 8 (ELit 6768832); KWord {| a_base := EVar 2; a_off := -216 |} 8 (ELit 6768848); KWord {| a_base := EVar 2; a_off := -208 |} 8 (ELit 6768376); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 1024956); KWord {| a_base := ELit 0; a_off := 6768384 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6771040 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6771048 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6771016 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6770972 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6767600 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767608 |} 4 (ELit 30); KWord {| a_base := ELit 0; a_off := 6767616 |} 4 (ELit 30); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-168))); KWord {| a_base := EVar 2; a_off := -168 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-184))); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 6767600); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -152 |} 8 (ELit 6767752); KWord {| a_base := EVar 2; a_off := -144 |} 8 (ELit 6767760); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 1274520); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 6768832); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 1015068); KWord {| a_base := ELit 0; a_off := 6768376 |} 8 (ELit 1280592); KWord {| a_base := ELit 0; a_off := 6769096 |} 8 (ELit 6768360); KWord {| a_base := ELit 0; a_off := 6768368 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767584 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767592 |} 4 (ELit 29); KWord {| a_base := ELit 0; a_off := 6768360 |} 8 (ELit 1280456); KWord {| a_base := ELit 0; a_off := 6769088 |} 8 (ELit 6768584); KWord {| a_base := ELit 0; a_off := 6768592 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767440 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767448 |} 4 (ELit 28); KWord {| a_base := ELit 0; a_off := 6768600 |} 8 (ELit 178280); KWord {| a_base := ELit 0; a_off := 6768584 |} 8 (ELit 1278464); KWord {| a_base := ELit 0; a_off := 6769080 |} 8 (ELit 6768560); KWord {| a_base := ELit 0; a_off := 6768568 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767424 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767432 |} 4 (ELit 27); KWord {| a_base := ELit 0; a_off := 6768576 |} 8 (ELit 178280); KWord {| a_base := ELit 0; a_off := 6768560 |} 8 (ELit 1278344); KWord {| a_base := ELit 0; a_off := 6769072 |} 8 (ELit 6768536); KWord {| a_base := ELit 0; a_off := 6768544 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767408 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767416 |} 4 (ELit 26); KWord {| a_base := ELit 0; a_off := 6768552 |} 8 (ELit 1277560); KWord {| a_base := ELit 0; a_off := 6768536 |} 8 (ELit 1277464); KWord {| a_base := ELit 0; a_off := 6769064 |} 8 (ELit 6768512); KWord {| a_base := ELit 0; a_off := 6768520 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767392 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767400 |} 4 (ELit 25); KWord {| a_base := ELit 0; a_off := 6768528 |} 8 (ELit 1277288); KWord {| a_base := ELit 0; a_off := 6768512 |} 8 (ELit 1277192); KWord {| a_base := ELit 0; a_off := 6769056 |} 8 (ELit 6768344); KWord {| a_base := ELit 0; a_off := 6768352 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767568 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767576 |} 4 (ELit 24); KWord {| a_base := ELit 0; a_off := 6768344 |} 8 (ELit 1280328); KWord {| a_base := ELit 0; a_off := 6769048 |} 8 (ELit 6768328); KWord {| a_base := ELit 0; a_off := 6768336 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767552 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767560 |} 4 (ELit 23); KWord {| a_base := ELit 0; a_off := 6768328 |} 8 (ELit 1280200); KWord {| a_base := ELit 0; a_off := 6769040 |} 8 (ELit 6768312); KWord {| a_base := ELit 0; a_off := 6768320 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767536 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767544 |} 4 (ELit 22); KWord {| a_base := ELit 0; a_off := 6768312 |} 8 (ELit 1280072); KWord {| a_base := ELit 0; a_off := 6769032 |} 8 (ELit 6768296); KWord {| a_base := ELit 0; a_off := 6768304 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767520 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767528 |} 4 (ELit 21); KWord {| a_base := ELit 0; a_off := 6768296 |} 8 (ELit 1279944); KWord {| a_base := ELit 0; a_off := 6769024 |} 8 (ELit 6768280); KWord {| a_base := ELit 0; a_off := 6768288 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767504 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767512 |} 4 (ELit 20); KWord {| a_base := ELit 0; a_off := 6768280 |} 8 (ELit 1279232); KWord {| a_base := ELit 0; a_off := 6769016 |} 8 (ELit 6768264); KWord {| a_base := ELit 0; a_off := 6768272 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767488 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767496 |} 4 (ELit 19); KWord {| a_base := ELit 0; a_off := 6768264 |} 8 (ELit 1279064); KWord {| a_base := ELit 0; a_off := 6769008 |} 8 (ELit 6768248); KWord {| a_base := ELit 0; a_off := 6768256 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767472 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767480 |} 4 (ELit 18); KWord {| a_base := ELit 0; a_off := 6768248 |} 8 (ELit 1278896); KWord {| a_base := ELit 0; a_off := 6769000 |} 8 (ELit 6768232); KWord {| a_base := ELit 0; a_off := 6768240 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767456 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767464 |} 4 (ELit 17); KWord {| a_base := ELit 0; a_off := 6768232 |} 8 (ELit 1278712); KWord {| a_base := ELit 0; a_off := 6768992 |} 8 (ELit 6768216); KWord {| a_base := ELit 0; a_off := 6768224 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767376 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767384 |} 4 (ELit 16); KWord {| a_base := ELit 0; a_off := 6768216 |} 8 (ELit 1276992); KWord {| a_base := ELit 0; a_off := 6768984 |} 8 (ELit 6768200); KWord {| a_base := ELit 0; a_off := 6768208 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767360 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767368 |} 4 (ELit 15); KWord {| a_base := ELit 0; a_off := 6768200 |} 8 (ELit 1276776); KWord {| a_base := ELit 0; a_off := 6768976 |} 8 (ELit 6768184); KWord {| a_base := ELit 0; a_off := 6768192 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767344 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767352 |} 4 (ELit 14); KWord {| a_base := ELit 0; a_off := 6768184 |} 8 (ELit 1276552); KWord {| a_base := ELit 0; a_off := 6768968 |} 8 (ELit 6768168); KWord {| a_base := ELit 0; a_off := 6768176 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767328 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767336 |} 4 (ELit 13); KWord {| a_base := ELit 0; a_off := 6768168 |} 8 (ELit 1276312); KWord {| a_base := ELit 0; a_off := 6768960 |} 8 (ELit 6768784); KWord {| a_base := ELit 0; a_off := 6768792 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6768024 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6768032 |} 4 (ELit 12); KWord {| a_base := ELit 0; a_off := 6768824 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6768816 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6768808 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6768800 |} 8 (ELit 188978561070); KWord {| a_base := ELit 0; a_off := 6768784 |} 8 (ELit 1274280); KWord {| a_base := ELit 0; a_off := 6768952 |} 8 (ELit 6768736); KWord {| a_base := ELit 0; a_off := 6768744 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6768008 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6768016 |} 4 (ELit 11); KWord {| a_base := ELit 0; a_off := 6768776 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6768768 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6768760 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6768752 |} 2 (ELit 11310); KWord {| a_base := ELit 0; a_off := 6768736 |} 8 (ELit 1274200); KWord {| a_base := ELit 0; a_off := 6768944 |} 8 (ELit 6768152); KWord {| a_base := ELit 0; a_off := 6768160 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767704 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767712 |} 4 (ELit 10); KWord {| a_base := ELit 0; a_off := 6768152 |} 8 (ELit 1275416); KWord {| a_base := ELit 0; a_off := 6768936 |} 8 (ELit 6768136); KWord {| a_base := ELit 0; a_off := 6768144 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767672 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767680 |} 4 (ELit 9); KWord {| a_base := ELit 0; a_off := 6768136 |} 8 (ELit 1275112); KWord {| a_base := ELit 0; a_off := 6768928 |} 8 (ELit 6768120); KWord {| a_base := ELit 0; a_off := 6768128 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767688 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767696 |} 4 (ELit 8); KWord {| a_base := ELit 0; a_off := 6768120 |} 8 (ELit 1275264); KWord {| a_base := ELit 0; a_off := 6768920 |} 8 (ELit 6768104); KWord {| a_base := ELit 0; a_off := 6768112 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767656 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767664 |} 4 (ELit 7); KWord {| a_base := ELit 0; a_off := 6768104 |} 8 (ELit 1274960); KWord {| a_base := ELit 0; a_off := 6768912 |} 8 (ELit 6768488); KWord {| a_base := ELit 0; a_off := 6768496 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767640 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767648 |} 4 (ELit 6); KWord {| a_base := ELit 0; a_off := 6768504 |} 8 (ELit 178280); KWord {| a_base := ELit 0; a_off := 6767761 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767760 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767752 |} 8 (ELit 178280); KWord {| a_base := EVar 2; a_off := -192 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6768488 |} 8 (ELit 1274104); KWord {| a_base := ELit 0; a_off := 6768904 |} 8 (ELit 6768088); KWord {| a_base := ELit 0; a_off := 6768096 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767624 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767632 |} 4 (ELit 5); KWord {| a_base := ELit 0; a_off := 6768088 |} 8 (ELit 1274792); KWord {| a_base := ELit 0; a_off := 6768896 |} 8 (ELit 6768072); KWord {| a_base := ELit 0; a_off := 6768080 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767976 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767984 |} 4 (ELit 4); KWord {| a_base := ELit 0; a_off := 6768072 |} 8 (ELit 1274584); KWord {| a_base := ELit 0; a_off := 6768888 |} 8 (ELit 6768608); KWord {| a_base := ELit 0; a_off := 6768616 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767992 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6768000 |} 4 (ELit 3); KWord {| a_base := ELit 0; a_off := 6768632 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6768624 |} 8 (ELit 156280); KWord {| a_base := ELit 0; a_off := 6768608 |} 8 (ELit 1273760); KWord {| a_base := ELit 0; a_off := 6768880 |} 8 (ELit 6768056); KWord {| a_base := ELit 0; a_off := 6768064 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767312 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767320 |} 4 (ELit 2); KWord {| a_base := ELit 0; a_off := 6768056 |} 8 (ELit 1276248); KWord {| a_base := ELit 0; a_off := 6768872 |} 8 (ELit 6768040); KWord {| a_base := ELit 0; a_off := 6768048 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6767296 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6767304 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 6768040 |} 8 (ELit 1276184); KWord {| a_base := ELit 0; a_off := 6769122 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6769120 |} 2 (ELit 17154); KWord {| a_base := ELit 0; a_off := 6768864 |} 8 (ELit 6769112); KWord {| a_base := ELit 0; a_off := 6768848 |} 8 (ELit 6768872); KWord {| a_base := ELit 0; a_off := 6768840 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6768832 |} 8 (ELit 1273592); KWord {| a_base := ELit 0; a_off := 6769112 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -96 |} 8 (ELit 6767752); KWord {| a_base := EVar 2; a_off := -88 |} 8 (ELit 6768832); KWord {| a_base := EVar 2; a_off := -80 |} 8 (ELit 6767776); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 1027136); KWord {| a_base := EVar 2; a_off := -64 |} 8 (ELit 6767752); KWord {| a_base := EVar 2; a_off := -56 |} 8 (ELit 6767792); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -40 |} 8 (ELit 1051236); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KRange (EVar 33) 6914048 140737488355320; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 8); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := 0 |} (ELit 8); KWr {| a_base := EVar 33; a_off := 0 |} (ELit 8); KImg 65536 1286144; KWord {| a_base := ELit 0; a_off := 1317368 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1317376 |} 4 (ELit 1); KImg 6767282 6767296; KImg 6767308 6767312; KImg 6767324 6767328; KImg 6767340 6767344; KImg 6767356 6767360; KImg 6767372 6767376; KImg 6767388 6767392; KImg 6767404 6767408; KImg 6767420 6767424; KImg 6767436 6767440; KImg 6767452 6767456; KImg 6767468 6767472; KImg 6767484 6767488; KImg 6767500 6767504; KImg 6767516 6767520; KImg 6767532 6767536; KImg 6767548 6767552; KImg 6767564 6767568; KImg 6767580 6767584; KImg 6767596 6767600; KImg 6767612 6767616; KImg 6767620 6767624; KImg 6767636 6767640; KImg 6767652 6767656; KImg 6767668 6767672; KImg 6767684 6767688; KImg 6767700 6767704; KImg 6767716 6767752; KImg 6767762 6767768; KImg 6767778 6767784; KImg 6767794 6767976; KImg 6767988 6767992; KImg 6768004 6768008; KImg 6768020 6768024; KImg 6768036 6768040; KImg 6768392 6768488; KImg 6768633 6768736; KImg 6768754 6768760; KImg 6769123 6769136; KWr {| a_base := ELit 0; a_off := 6767282 |} (ELit 1854); KImg 6770968 6770972; KImg 6770976 6771016; KImg 6771024 6771040; KImg 6771044 6771048; KWr {| a_base := ELit 0; a_off := 6770968 |} (ELit 88); KWord {| a_base := ELit 0; a_off := 6905107 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6905328 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6904512 |} 8 (EVar 34); KWord {| a_base := ELit 0; a_off := 1282488 |} 8 (ELit 1317368); KWord {| a_base := ELit 0; a_off := 1317368 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1282496 |} 8 (ELit 1320680); KWord {| a_base := ELit 0; a_off := 1320680 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1282504 |} 8 (ELit 1320688); KWord {| a_base := ELit 0; a_off := 1320688 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1282512 |} 8 (ELit 1320672); KWord {| a_base := ELit 0; a_off := 1320672 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1285408 |} 8 (ELit 1320665); KWord {| a_base := ELit 0; a_off := 1320665 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1290696 |} 8 (ELit 1226892); KWord {| a_base := ELit 0; a_off := 1290688 |} 8 (ELit 1225864); KWord {| a_base := ELit 0; a_off := 1320664 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1290224 |} 8 (ELit 1225816); KWord {| a_base := ELit 0; a_off := 1914406 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1914407 |} 1 (ELit 1); KZero {| a_base := ELit 0; a_off := 2148296782 |} (ELit 248); KZero {| a_base := ELit 0; a_off := 2148297243 |} (ELit 27); KZero {| a_base := ELit 0; a_off := 2147473145 |} (ELit 65); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512)] 544))).
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
Definition ps0 : SR.post_spec := SR.PS 1051208 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ced162.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1051116 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ced162.IT BndT_Ea_001.SegItab_Ea_ced162.IT_sound BF NX0 BR XSTEP F0 PSS plan 1051116 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegEa_aliA.

Module LibSegEa_ardAh.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_aba155.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_aba155.IT.
Definition ENDS : list Z := [1051116].
Definition STOPS1 : list Z := [1051116; 493068; 493076] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-1?0+$21#1=0$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'+$21-1?0#10007???8000#7????????<17&+$21-1?0#8)##7???7000#100000001000+$21-1?0##3>0)$2-1000#1000+$21-1?0##3>0)##10000#688000+$21-1?0##3>0#&6+$21-1?0#3#7???8000#22#&6+$21#1=0#3#7???8000#4&$21#8($21##180#&6$21#3#7???8000#30!##1391;8,8#1419?8!##1419?8,8#7???8000!##1391<0,8#1426>8!##1426>8,8#!##1391<8,8#1426?0!##1426?0,8#!##1391=0,8#1426>0!##1426>0,8#7???????????!##139=20,8#1426=9!##1426=9,1#1!##13;1<8,8#12;88<!##13;1<0,8#12;488###8001>67>#40###8001>=;<#20"%pstring).
Definition ss0 : sym_state := SS 726332 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 384)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 384)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(493068, 0%nat); (493076, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1051116; 493068; 493076; 1051116]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051116; 493068; 493076; 1051116])], (93, SS 1051116 [ELit 0; ELit 728484; EAlu Instr.ALU_ADD (EVar 2) (ELit (-192)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EAlu Instr.ALU_ADD (EVar 33) (ELit 32); EAlu Instr.ALU_ADD (EVar 33) (ELit 48); EAlu Instr.ALU_ADD (EVar 33) (ELit 160); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; EAlu Instr.ALU_ADD (EVar 33) (ELit 112); ELit 2147450880; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 112)) (ELit 3)) (ELit 2147450880); EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 168 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 144 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 128 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 120 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 48)); KWord {| a_base := EVar 33; a_off := 148 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -208 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 728484); KWord {| a_base := EVar 33; a_off := 40 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 112 |} 8 (ELit 1258936); KWord {| a_base := EVar 33; a_off := 32 |} 8 (ELit 1258896); KWord {| a_base := EVar 33; a_off := 160 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -168 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 727104); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 464)); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -88 |} 8 (ELit 726552); KWord {| a_base := EVar 33; a_off := 20 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 16 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 12 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 9 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 8 |} 1 (ELit 1); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1258664); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1253376 1286144; KWord {| a_base := ELit 0; a_off := 1317368 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1317376 |} 4 (ELit 1); KRange (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 17594333495296 140737488354327; KAlign (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6848512) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) (ELit 3); a_off := 2147450880 |} (ELit 34); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 464)) (ELit 3); a_off := 2147450880 |} (ELit 4); KAlign (EVar 33) 8; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 384); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 48); KWord {| a_base := ELit 0; a_off := 1282488 |} 8 (ELit 1317368); KWord {| a_base := ELit 0; a_off := 1317368 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1282496 |} 8 (ELit 1320680); KWord {| a_base := ELit 0; a_off := 1320680 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1282504 |} 8 (ELit 1320688); KWord {| a_base := ELit 0; a_off := 1320688 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1282512 |} 8 (ELit 1320672); KWord {| a_base := ELit 0; a_off := 1320672 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1285408 |} 8 (ELit 1320665); KWord {| a_base := ELit 0; a_off := 1320665 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1290696 |} 8 (ELit 1226892); KWord {| a_base := ELit 0; a_off := 1290688 |} 8 (ELit 1225864); KZero {| a_base := ELit 0; a_off := 2147608190 |} (ELit 64); KZero {| a_base := ELit 0; a_off := 2147610044 |} (ELit 32)] 76))).
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
Definition ps0 : SR.post_spec := SR.PS 1051116 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_aba155.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726332 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_aba155.IT BndT_Ea_001.SegItab_Ea_aba155.IT_sound BF NX0 BR XSTEP F0 PSS plan 726332 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegEa_ardAh.

Module LibSegEa_ardAl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_aba155.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_aba155.IT.
Definition ENDS : list Z := [1051116].
Definition STOPS1 : list Z := [1051116; 493068; 493076] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-1?0+$21#1=0$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'+$21-1?0#698000#7???6<20&+$21-1?0#8)##7???7000#100000001000+$21-1?0##3>0)$2-1000#1000+$21-1?0##3>0)##10000#688000+$21-1?0##3>0#&6+$21-1?0#3#7???8000#22#&6+$21#1=0#3#7???8000#4&$21#8($21##180#&6$21#3#7???8000#30!##1391;8,8#1419?8!##1419?8,8#7???8000!##1391<0,8#1426>8!##1426>8,8#!##1391<8,8#1426?0!##1426?0,8#!##1391=0,8#1426>0!##1426>0,8#7???????????!##139=20,8#1426=9!##1426=9,1#1!##13;1<8,8#12;88<!##13;1<0,8#12;488###8001>67>#40###8001>=;<#20"%pstring).
Definition ss0 : sym_state := SS 726332 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 384)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 384)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(493068, 0%nat); (493076, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1051116; 493068; 493076; 1051116]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1051116; 493068; 493076; 1051116])], (93, SS 1051116 [ELit 0; ELit 728484; EAlu Instr.ALU_ADD (EVar 2) (ELit (-192)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EAlu Instr.ALU_ADD (EVar 33) (ELit 32); EAlu Instr.ALU_ADD (EVar 33) (ELit 48); EAlu Instr.ALU_ADD (EVar 33) (ELit 160); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; EAlu Instr.ALU_ADD (EVar 33) (ELit 112); ELit 2147450880; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 112)) (ELit 3)) (ELit 2147450880); EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 168 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 144 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 128 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 120 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 48)); KWord {| a_base := EVar 33; a_off := 148 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -208 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 728484); KWord {| a_base := EVar 33; a_off := 40 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 112 |} 8 (ELit 1258936); KWord {| a_base := EVar 33; a_off := 32 |} 8 (ELit 1258896); KWord {| a_base := EVar 33; a_off := 160 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -168 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 727104); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 464)); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -88 |} 8 (ELit 726552); KWord {| a_base := EVar 33; a_off := 20 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 16 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 12 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 9 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 8 |} 1 (ELit 1); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1258664); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1253376 1286144; KWord {| a_base := ELit 0; a_off := 1317368 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1317376 |} 4 (ELit 1); KRange (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 6914048 2147445792; KAlign (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6848512) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 992); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) (ELit 3); a_off := 2147450880 |} (ELit 34); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 464)) (ELit 3); a_off := 2147450880 |} (ELit 4); KAlign (EVar 33) 8; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 384); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 48); KWord {| a_base := ELit 0; a_off := 1282488 |} 8 (ELit 1317368); KWord {| a_base := ELit 0; a_off := 1317368 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1282496 |} 8 (ELit 1320680); KWord {| a_base := ELit 0; a_off := 1320680 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1282504 |} 8 (ELit 1320688); KWord {| a_base := ELit 0; a_off := 1320688 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1282512 |} 8 (ELit 1320672); KWord {| a_base := ELit 0; a_off := 1320672 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1285408 |} 8 (ELit 1320665); KWord {| a_base := ELit 0; a_off := 1320665 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1290696 |} 8 (ELit 1226892); KWord {| a_base := ELit 0; a_off := 1290688 |} 8 (ELit 1225864); KZero {| a_base := ELit 0; a_off := 2147608190 |} (ELit 64); KZero {| a_base := ELit 0; a_off := 2147610044 |} (ELit 32)] 76))).
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
Definition ps0 : SR.post_spec := SR.PS 1051116 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_aba155.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726332 regs0 kn0 = true.
Proof. apply (SegPlanFast.SGF.cert_by_fast _ _ XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_aba155.IT BndT_Ea_001.SegItab_Ea_aba155.IT_sound BF NX0 BR XSTEP F0 PSS plan 726332 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegEa_ardAl.
