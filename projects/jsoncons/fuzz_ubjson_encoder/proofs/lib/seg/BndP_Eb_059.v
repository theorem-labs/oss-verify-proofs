(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Eb0PlanKit Eb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Eb_001.

Module LibSegEb_bstG1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-50#4$28$;$<$=$>$?$10$11+$2-68#2+&6+$2-50#3#7???8000#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#40!$21#10,8+$24#40'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7?????????80&$28#10(+$28#40##20#&6+$28#40#3#7???8000#4)##7???7000#100000001000+$28#40##20'+$28#40#1000#7?????????>0)$2-1000#1000+$28#40##20)$21##18+$28#40##20)$22##4+$28#40##20)$23##8+$28#40##20)##10000#68<000+$28#40##20)$34##1+$28#40##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<334!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (64))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-240), 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (64))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-=0$3$4$5$6$7+$2-68$21$24+$24#40+$24#40+$24#40#1#&6+$21#10#3$11$34$23$22#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,54!$2-=8,8#::9:0!$2-=0,8+$2-68!$2-<8,8#;57>0!$2-<0,8$18!$2-;8,8$17!$2-;0,8#7???8000!$2-:8,8+&6+$21#8#3#7???8000!$2-:0,8$22!$2-98,8$23!$2-90,8$34!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;<3?8!$2-58,8+$28#60!$28#58,8#!$28#50,1$35!$28#48,8$27!$28#40,4$26!$2-50,8+$28#80!$2-60,8+$28#40!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#40!$21#10,8+$24#40'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7?????????80&$28#10(+$28#40##20#&6+$28#40#3#7???8000#4)##7???7000#100000001000+$28#40##20'+$28#40#1000#7?????????>0)$2-1000#1000+$28#40##20)$21##18+$28#40##20)$22##4+$28#40##20)$23##8+$28#40##20)##10000#68<000+$28#40##20)$34##1+$28#40##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstG1.

Module LibSegEb_bstG10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-50#800$28$;$<$=$>$?$10$11+$2-68#400+&6+$2-50#3#7???8000#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#8000!$21#10,8+$24#8000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7???????0000&$28#10(+$28#8000##20#&6+$28#8000#3#7???8000#4)##7???7000#100000001000+$28#8000##20'+$28#8000#1000#7?????????>0)$2-1000#1000+$28#8000##20)$21##18+$28#8000##20)$22##4+$28#8000##20)$23##8+$28#8000##20)##10000#68<000+$28#8000##20)$34##1+$28#8000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<334!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (32768))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-240), 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (32768))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-=0$3$4$5$6$7+$2-68$21$24+$24#8000+$24#8000+$24#8000#1#&6+$21#10#3$11$34$23$22#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,54!$2-=8,8#::9:0!$2-=0,8+$2-68!$2-<8,8#;57>0!$2-<0,8$18!$2-;8,8$17!$2-;0,8#7???8000!$2-:8,8+&6+$21#8#3#7???8000!$2-:0,8$22!$2-98,8$23!$2-90,8$34!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;<3?8!$2-58,8+$28#8020!$28#8018,8#!$28#8010,1$35!$28#8008,8$27!$28#8000,4$26!$2-50,8+$28#10000!$2-60,8+$28#8000!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#8000!$21#10,8+$24#8000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7???????0000&$28#10(+$28#8000##20#&6+$28#8000#3#7???8000#4)##7???7000#100000001000+$28#8000##20'+$28#8000#1000#7?????????>0)$2-1000#1000+$28#8000##20)$21##18+$28#8000##20)$22##4+$28#8000##20)$23##8+$28#8000##20)##10000#68<000+$28#8000##20)$34##1+$28#8000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstG10.

Module LibSegEb_bstG2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-50#8$28$;$<$=$>$?$10$11+$2-68#4+&6+$2-50#3#7???8000#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#80!$21#10,8+$24#80'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7?????????00&$28#10(+$28#80##20#&6+$28#80#3#7???8000#4)##7???7000#100000001000+$28#80##20'+$28#80#1000#7?????????>0)$2-1000#1000+$28#80##20)$21##18+$28#80##20)$22##4+$28#80##20)$23##8+$28#80##20)##10000#68<000+$28#80##20)$34##1+$28#80##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<334!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (128))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-240), 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (128))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-=0$3$4$5$6$7+$2-68$21$24+$24#80+$24#80+$24#80#1#&6+$21#10#3$11$34$23$22#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,54!$2-=8,8#::9:0!$2-=0,8+$2-68!$2-<8,8#;57>0!$2-<0,8$18!$2-;8,8$17!$2-;0,8#7???8000!$2-:8,8+&6+$21#8#3#7???8000!$2-:0,8$22!$2-98,8$23!$2-90,8$34!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;<3?8!$2-58,8+$28#:0!$28#98,8#!$28#90,1$35!$28#88,8$27!$28#80,4$26!$2-50,8+$28#100!$2-60,8+$28#80!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#80!$21#10,8+$24#80'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7?????????00&$28#10(+$28#80##20#&6+$28#80#3#7???8000#4)##7???7000#100000001000+$28#80##20'+$28#80#1000#7?????????>0)$2-1000#1000+$28#80##20)$21##18+$28#80##20)$22##4+$28#80##20)$23##8+$28#80##20)##10000#68<000+$28#80##20)$34##1+$28#80##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstG2.

Module LibSegEb_bstG3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-50#10$28$;$<$=$>$?$10$11+$2-68#8+&6+$2-50#3#7???8000#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#100!$21#10,8+$24#100'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7????????>00&$28#10(+$28#100##20#&6+$28#100#3#7???8000#4)##7???7000#100000001000+$28#100##20'+$28#100#1000#7?????????>0)$2-1000#1000+$28#100##20)$21##18+$28#100##20)$22##4+$28#100##20)$23##8+$28#100##20)##10000#68<000+$28#100##20)$34##1+$28#100##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<334!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (256))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-240), 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (256))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-=0$3$4$5$6$7+$2-68$21$24+$24#100+$24#100+$24#100#1#&6+$21#10#3$11$34$23$22#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,54!$2-=8,8#::9:0!$2-=0,8+$2-68!$2-<8,8#;57>0!$2-<0,8$18!$2-;8,8$17!$2-;0,8#7???8000!$2-:8,8+&6+$21#8#3#7???8000!$2-:0,8$22!$2-98,8$23!$2-90,8$34!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;<3?8!$2-58,8+$28#120!$28#118,8#!$28#110,1$35!$28#108,8$27!$28#100,4$26!$2-50,8+$28#200!$2-60,8+$28#100!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#100!$21#10,8+$24#100'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7????????>00&$28#10(+$28#100##20#&6+$28#100#3#7???8000#4)##7???7000#100000001000+$28#100##20'+$28#100#1000#7?????????>0)$2-1000#1000+$28#100##20)$21##18+$28#100##20)$22##4+$28#100##20)$23##8+$28#100##20)##10000#68<000+$28#100##20)$34##1+$28#100##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstG3.

Module LibSegEb_bstG4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-50#20$28$;$<$=$>$?$10$11+$2-68#10+&6+$2-50#3#7???8000#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#200!$21#10,8+$24#200'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7????????<00&$28#10(+$28#200##20#&6+$28#200#3#7???8000#4)##7???7000#100000001000+$28#200##20'+$28#200#1000#7?????????>0)$2-1000#1000+$28#200##20)$21##18+$28#200##20)$22##4+$28#200##20)$23##8+$28#200##20)##10000#68<000+$28#200##20)$34##1+$28#200##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<334!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (512))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-240), 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (512))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-=0$3$4$5$6$7+$2-68$21$24+$24#200+$24#200+$24#200#1#&6+$21#10#3$11$34$23$22#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,54!$2-=8,8#::9:0!$2-=0,8+$2-68!$2-<8,8#;57>0!$2-<0,8$18!$2-;8,8$17!$2-;0,8#7???8000!$2-:8,8+&6+$21#8#3#7???8000!$2-:0,8$22!$2-98,8$23!$2-90,8$34!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;<3?8!$2-58,8+$28#220!$28#218,8#!$28#210,1$35!$28#208,8$27!$28#200,4$26!$2-50,8+$28#400!$2-60,8+$28#200!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#200!$21#10,8+$24#200'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7????????<00&$28#10(+$28#200##20#&6+$28#200#3#7???8000#4)##7???7000#100000001000+$28#200##20'+$28#200#1000#7?????????>0)$2-1000#1000+$28#200##20)$21##18+$28#200##20)$22##4+$28#200##20)$23##8+$28#200##20)##10000#68<000+$28#200##20)$34##1+$28#200##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstG4.

Module LibSegEb_bstG5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-50#40$28$;$<$=$>$?$10$11+$2-68#20+&6+$2-50#3#7???8000#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#400!$21#10,8+$24#400'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7????????800&$28#10(+$28#400##20#&6+$28#400#3#7???8000#4)##7???7000#100000001000+$28#400##20'+$28#400#1000#7?????????>0)$2-1000#1000+$28#400##20)$21##18+$28#400##20)$22##4+$28#400##20)$23##8+$28#400##20)##10000#68<000+$28#400##20)$34##1+$28#400##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<334!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (1024))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-240), 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (1024))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-=0$3$4$5$6$7+$2-68$21$24+$24#400+$24#400+$24#400#1#&6+$21#10#3$11$34$23$22#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,54!$2-=8,8#::9:0!$2-=0,8+$2-68!$2-<8,8#;57>0!$2-<0,8$18!$2-;8,8$17!$2-;0,8#7???8000!$2-:8,8+&6+$21#8#3#7???8000!$2-:0,8$22!$2-98,8$23!$2-90,8$34!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;<3?8!$2-58,8+$28#420!$28#418,8#!$28#410,1$35!$28#408,8$27!$28#400,4$26!$2-50,8+$28#800!$2-60,8+$28#400!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#400!$21#10,8+$24#400'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7????????800&$28#10(+$28#400##20#&6+$28#400#3#7???8000#4)##7???7000#100000001000+$28#400##20'+$28#400#1000#7?????????>0)$2-1000#1000+$28#400##20)$21##18+$28#400##20)$22##4+$28#400##20)$23##8+$28#400##20)##10000#68<000+$28#400##20)$34##1+$28#400##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstG5.

Module LibSegEb_bstG6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-50#80$28$;$<$=$>$?$10$11+$2-68#40+&6+$2-50#3#7???8000#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#800!$21#10,8+$24#800'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7????????000&$28#10(+$28#800##20#&6+$28#800#3#7???8000#4)##7???7000#100000001000+$28#800##20'+$28#800#1000#7?????????>0)$2-1000#1000+$28#800##20)$21##18+$28#800##20)$22##4+$28#800##20)$23##8+$28#800##20)##10000#68<000+$28#800##20)$34##1+$28#800##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<334!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (2048))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-240), 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (2048))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-=0$3$4$5$6$7+$2-68$21$24+$24#800+$24#800+$24#800#1#&6+$21#10#3$11$34$23$22#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,54!$2-=8,8#::9:0!$2-=0,8+$2-68!$2-<8,8#;57>0!$2-<0,8$18!$2-;8,8$17!$2-;0,8#7???8000!$2-:8,8+&6+$21#8#3#7???8000!$2-:0,8$22!$2-98,8$23!$2-90,8$34!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;<3?8!$2-58,8+$28#820!$28#818,8#!$28#810,1$35!$28#808,8$27!$28#800,4$26!$2-50,8+$28#1000!$2-60,8+$28#800!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#800!$21#10,8+$24#800'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7????????000&$28#10(+$28#800##20#&6+$28#800#3#7???8000#4)##7???7000#100000001000+$28#800##20'+$28#800#1000#7?????????>0)$2-1000#1000+$28#800##20)$21##18+$28#800##20)$22##4+$28#800##20)$23##8+$28#800##20)##10000#68<000+$28#800##20)$34##1+$28#800##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstG6.

Module LibSegEb_bstG7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-50#100$28$;$<$=$>$?$10$11+$2-68#80+&6+$2-50#3#7???8000#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#1000!$21#10,8+$24#1000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7???????>000&$28#10(+$28#1000##20#&6+$28#1000#3#7???8000#4)##7???7000#100000001000+$28#1000##20'+$28#1000#1000#7?????????>0)$2-1000#1000+$28#1000##20)$21##18+$28#1000##20)$22##4+$28#1000##20)$23##8+$28#1000##20)##10000#68<000+$28#1000##20)$34##1+$28#1000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<334!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (4096))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-240), 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (4096))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-=0$3$4$5$6$7+$2-68$21$24+$24#1000+$24#1000+$24#1000#1#&6+$21#10#3$11$34$23$22#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,54!$2-=8,8#::9:0!$2-=0,8+$2-68!$2-<8,8#;57>0!$2-<0,8$18!$2-;8,8$17!$2-;0,8#7???8000!$2-:8,8+&6+$21#8#3#7???8000!$2-:0,8$22!$2-98,8$23!$2-90,8$34!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;<3?8!$2-58,8+$28#1020!$28#1018,8#!$28#1010,1$35!$28#1008,8$27!$28#1000,4$26!$2-50,8+$28#2000!$2-60,8+$28#1000!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#1000!$21#10,8+$24#1000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7???????>000&$28#10(+$28#1000##20#&6+$28#1000#3#7???8000#4)##7???7000#100000001000+$28#1000##20'+$28#1000#1000#7?????????>0)$2-1000#1000+$28#1000##20)$21##18+$28#1000##20)$22##4+$28#1000##20)$23##8+$28#1000##20)##10000#68<000+$28#1000##20)$34##1+$28#1000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstG7.

Module LibSegEb_bstG8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-50#200$28$;$<$=$>$?$10$11+$2-68#100+&6+$2-50#3#7???8000#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#2000!$21#10,8+$24#2000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7???????<000&$28#10(+$28#2000##20#&6+$28#2000#3#7???8000#4)##7???7000#100000001000+$28#2000##20'+$28#2000#1000#7?????????>0)$2-1000#1000+$28#2000##20)$21##18+$28#2000##20)$22##4+$28#2000##20)$23##8+$28#2000##20)##10000#68<000+$28#2000##20)$34##1+$28#2000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<334!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (8192))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-240), 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (8192))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-=0$3$4$5$6$7+$2-68$21$24+$24#2000+$24#2000+$24#2000#1#&6+$21#10#3$11$34$23$22#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,54!$2-=8,8#::9:0!$2-=0,8+$2-68!$2-<8,8#;57>0!$2-<0,8$18!$2-;8,8$17!$2-;0,8#7???8000!$2-:8,8+&6+$21#8#3#7???8000!$2-:0,8$22!$2-98,8$23!$2-90,8$34!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;<3?8!$2-58,8+$28#2020!$28#2018,8#!$28#2010,1$35!$28#2008,8$27!$28#2000,4$26!$2-50,8+$28#4000!$2-60,8+$28#2000!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#2000!$21#10,8+$24#2000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7???????<000&$28#10(+$28#2000##20#&6+$28#2000#3#7???8000#4)##7???7000#100000001000+$28#2000##20'+$28#2000#1000#7?????????>0)$2-1000#1000+$28#2000##20)$21##18+$28#2000##20)$22##4+$28#2000##20)$23##8+$28#2000##20)##10000#68<000+$28#2000##20)$34##1+$28#2000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstG8.

Module LibSegEb_bstG9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-50#400$28$;$<$=$>$?$10$11+$2-68#200+&6+$2-50#3#7???8000#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#4000!$21#10,8+$24#4000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7???????8000&$28#10(+$28#4000##20#&6+$28#4000#3#7???8000#4)##7???7000#100000001000+$28#4000##20'+$28#4000#1000#7?????????>0)$2-1000#1000+$28#4000##20)$21##18+$28#4000##20)$22##4+$28#4000##20)$23##8+$28#4000##20)##10000#68<000+$28#4000##20)$34##1+$28#4000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<334!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (16384))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-240), 240); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (16384))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-=0$3$4$5$6$7+$2-68$21$24+$24#4000+$24#4000+$24#4000#1#&6+$21#10#3$11$34$23$22#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,54!$2-=8,8#::9:0!$2-=0,8+$2-68!$2-<8,8#;57>0!$2-<0,8$18!$2-;8,8$17!$2-;0,8#7???8000!$2-:8,8+&6+$21#8#3#7???8000!$2-:0,8$22!$2-98,8$23!$2-90,8$34!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;<3?8!$2-58,8+$28#4020!$28#4018,8#!$28#4010,1$35!$28#4008,8$27!$28#4000,4$26!$2-50,8+$28#8000!$2-60,8+$28#4000!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#4000!$21#10,8+$24#4000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$34#69<000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$34##1'$35##??'$28#1000#7???????8000&$28#10(+$28#4000##20#&6+$28#4000#3#7???8000#4)##7???7000#100000001000+$28#4000##20'+$28#4000#1000#7?????????>0)$2-1000#1000+$28#4000##20)$21##18+$28#4000##20)$22##4+$28#4000##20)$23##8+$28#4000##20)##10000#68<000+$28#4000##20)$34##1+$28#4000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 511016 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstG9.

Module LibSegEb_bstH0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-=0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$34$23$22#7???8000#7???8000$33$36$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#20!$21#10,8+$24#20'$24#1000#7?????????>0&$24#10'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<3?8!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-;0,8#7???8000!$2-;8,8$33!$2-<0,8$36!$2-68,8$28!$2-60,8+$28#20!$2-58,8+$28#40!$2-50,8+$28#40!$2-48,8$21!$2-<8,8#;57>0!$2-=0,8+$2-68"%pstring).
Definition ss0 : sym_state := SS 698784 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;5880+$2-<0$3$4$5$6$7+$2-68$21$28$24#20^#?#?????????????>0#1$?$10$11+$21#8+$2-60$28#7???8000+&6+$21#8#3#7???8000+&6+$2-60#3#7???8000+&6$21#3#7???8000$19$1:$1;$1<$1=$1>$1?,,2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#20!$21#10,8+$24#20'$24#1000#7?????????>0&$24#10'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<3?8!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-;0,8#7???8000!$2-;8,8$33!$2-<0,8$36!$2-68,8$28!$2-60,8+$28#20!$2-58,8+$28#40!$2-50,8+$28#40!$2-48,8$21!$2-<8,8#;57>0!$2-=0,8+$2-68,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 495168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 698784 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 698784 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstH0.

Module LibSegEb_bstH1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-=0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$34$23$22#7???8000#7???8000$33$36$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#40!$21#10,8+$24#40'$24#1000#7?????????>0&$24#10'$28#1000#7?????????80&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<3?8!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-;0,8#7???8000!$2-;8,8$33!$2-<0,8$36!$2-68,8$28!$2-60,8+$28#40!$2-58,8+$28#60!$2-50,8+$28#80!$2-48,8$21!$2-<8,8#;57>0!$2-=0,8+$2-68"%pstring).
Definition ss0 : sym_state := SS 698784 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;5880+$2-<0$3$4$5$6$7+$2-68$21$28$24#40^#?#?????????????<0#1$?$10$11+$21#8+$2-60$28#7???8000+&6+$21#8#3#7???8000+&6+$2-60#3#7???8000+&6$21#3#7???8000$19$1:$1;$1<$1=$1>$1?,,2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#40!$21#10,8+$24#40'$24#1000#7?????????>0&$24#10'$28#1000#7?????????80&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<3?8!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-;0,8#7???8000!$2-;8,8$33!$2-<0,8$36!$2-68,8$28!$2-60,8+$28#40!$2-58,8+$28#60!$2-50,8+$28#80!$2-48,8$21!$2-<8,8#;57>0!$2-=0,8+$2-68,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 495168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 698784 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 698784 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstH1.

Module LibSegEb_bstH10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-=0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$34$23$22#7???8000#7???8000$33$36$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#8000!$21#10,8+$24#8000'$24#1000#7?????????>0&$24#10'$28#1000#7???????0000&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<3?8!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-;0,8#7???8000!$2-;8,8$33!$2-<0,8$36!$2-68,8$28!$2-60,8+$28#8000!$2-58,8+$28#8020!$2-50,8+$28#10000!$2-48,8$21!$2-<8,8#;57>0!$2-=0,8+$2-68"%pstring).
Definition ss0 : sym_state := SS 698784 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;5880+$2-<0$3$4$5$6$7+$2-68$21$28$24#8000^#?#???????????8000#1$?$10$11+$21#8+$2-60$28#7???8000+&6+$21#8#3#7???8000+&6+$2-60#3#7???8000+&6$21#3#7???8000$19$1:$1;$1<$1=$1>$1?,,2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#8000!$21#10,8+$24#8000'$24#1000#7?????????>0&$24#10'$28#1000#7???????0000&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<3?8!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-;0,8#7???8000!$2-;8,8$33!$2-<0,8$36!$2-68,8$28!$2-60,8+$28#8000!$2-58,8+$28#8020!$2-50,8+$28#10000!$2-48,8$21!$2-<8,8#;57>0!$2-=0,8+$2-68,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 495168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 698784 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 698784 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstH10.

Module LibSegEb_bstH2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_858036.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_858036.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-=0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$34$23$22#7???8000#7???8000$33$36$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#80!$21#10,8+$24#80'$24#1000#7?????????>0&$24#10'$28#1000#7?????????00&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<3?8!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-;0,8#7???8000!$2-;8,8$33!$2-<0,8$36!$2-68,8$28!$2-60,8+$28#80!$2-58,8+$28#:0!$2-50,8+$28#100!$2-48,8$21!$2-<8,8#;57>0!$2-=0,8+$2-68"%pstring).
Definition ss0 : sym_state := SS 698784 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;5880+$2-<0$3$4$5$6$7+$2-68$21$28$24#80^#?#?????????????80#1$?$10$11+$21#8+$2-60$28#7???8000+&6+$21#8#3#7???8000+&6+$2-60#3#7???8000+&6$21#3#7???8000$19$1:$1;$1<$1=$1>$1?,,2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#80!$21#10,8+$24#80'$24#1000#7?????????>0&$24#10'$28#1000#7?????????00&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;<3?8!$2-80,8+$21#8!$2-88,8$21!$2-90,8$34!$2-98,8$23!$2-:0,8$22!$2-:8,8+&6+$21#8#3#7???8000!$2-;0,8#7???8000!$2-;8,8$33!$2-<0,8$36!$2-68,8$28!$2-60,8+$28#80!$2-58,8+$28#:0!$2-50,8+$28#100!$2-48,8$21!$2-<8,8#;57>0!$2-=0,8+$2-68,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 495168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_858036.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 698784 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_858036.IT BndT_Eb_001.SegItab_Eb_858036.IT_sound BF NX0 BR XSTEP F0 PSS plan 698784 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bstH2.
