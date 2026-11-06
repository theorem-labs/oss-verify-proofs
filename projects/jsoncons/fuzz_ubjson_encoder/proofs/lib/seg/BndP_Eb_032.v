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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Eb_000.

Module LibSegEb_bpqG11.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#800$28$;$<$=$>$?$10$11+$2-60#400+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#6000!$21#28,8+$24#6000'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7???????4000&$28#10(+$28#6000##18#&6+$28#6000#3#7???8000#3)##7???7000#100000001000+$28#6000##18'+$28#6000#1000#7?????????>8)$2-1000#1000+$28#6000##18)$21##38+$28#6000##18)$22##4+$28#6000##18)$23##8+$28#6000##18)##10000#68<000+$28#6000##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (24576))), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (24576))), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;1110+$2-<0$3$4$5$6$7+$2-60+$21#18$24+$24#6000+$24#6000+$24#6000#1#&6+$21#28#3$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,49!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#6018!$28#6010,8#!$28#6008,8$27!$28#6000,4$26!$2-48,8+$28#<000!$2-58,8+$28#6000!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#6000!$21#28,8+$24#6000'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7???????4000&$28#10(+$28#6000##18#&6+$28#6000#3#7???8000#3)##7???7000#100000001000+$28#6000##18'+$28#6000#1000#7?????????>8)$2-1000#1000+$28#6000##18)$21##38+$28#6000##18)$22##4+$28#6000##18)$23##8+$28#6000##18)##10000#68<000+$28#6000##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqG11.

Module LibSegEb_bpqG2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#4$28$;$<$=$>$?$10$11+$2-60#2+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#30!$21#28,8+$24#30'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7?????????:0&$28#10(+$28#30##18#&6+$28#30#3#7???8000#3)##7???7000#100000001000+$28#30##18'+$28#30#1000#7?????????>8)$2-1000#1000+$28#30##18)$21##38+$28#30##18)$22##4+$28#30##18)$23##8+$28#30##18)##10000#68<000+$28#30##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (48))), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (48))), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;1110+$2-<0$3$4$5$6$7+$2-60+$21#18$24+$24#30+$24#30+$24#30#1#&6+$21#28#3$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,49!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#48!$28#40,8#!$28#38,8$27!$28#30,4$26!$2-48,8+$28#60!$2-58,8+$28#30!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#30!$21#28,8+$24#30'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7?????????:0&$28#10(+$28#30##18#&6+$28#30#3#7???8000#3)##7???7000#100000001000+$28#30##18'+$28#30#1000#7?????????>8)$2-1000#1000+$28#30##18)$21##38+$28#30##18)$22##4+$28#30##18)$23##8+$28#30##18)##10000#68<000+$28#30##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqG2.

Module LibSegEb_bpqG3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#8$28$;$<$=$>$?$10$11+$2-60#4+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#60!$21#28,8+$24#60'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7?????????40&$28#10(+$28#60##18#&6+$28#60#3#7???8000#3)##7???7000#100000001000+$28#60##18'+$28#60#1000#7?????????>8)$2-1000#1000+$28#60##18)$21##38+$28#60##18)$22##4+$28#60##18)$23##8+$28#60##18)##10000#68<000+$28#60##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (96))), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (96))), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;1110+$2-<0$3$4$5$6$7+$2-60+$21#18$24+$24#60+$24#60+$24#60#1#&6+$21#28#3$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,49!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#78!$28#70,8#!$28#68,8$27!$28#60,4$26!$2-48,8+$28#<0!$2-58,8+$28#60!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#60!$21#28,8+$24#60'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7?????????40&$28#10(+$28#60##18#&6+$28#60#3#7???8000#3)##7???7000#100000001000+$28#60##18'+$28#60#1000#7?????????>8)$2-1000#1000+$28#60##18)$21##38+$28#60##18)$22##4+$28#60##18)$23##8+$28#60##18)##10000#68<000+$28#60##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqG3.

Module LibSegEb_bpqG4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#10$28$;$<$=$>$?$10$11+$2-60#8+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#<0!$21#28,8+$24#<0'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7????????>80&$28#10(+$28#<0##18#&6+$28#<0#3#7???8000#3)##7???7000#100000001000+$28#<0##18'+$28#<0#1000#7?????????>8)$2-1000#1000+$28#<0##18)$21##38+$28#<0##18)$22##4+$28#<0##18)$23##8+$28#<0##18)##10000#68<000+$28#<0##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (192))), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (192))), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;1110+$2-<0$3$4$5$6$7+$2-60+$21#18$24+$24#<0+$24#<0+$24#<0#1#&6+$21#28#3$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,49!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#=8!$28#=0,8#!$28#<8,8$27!$28#<0,4$26!$2-48,8+$28#180!$2-58,8+$28#<0!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#<0!$21#28,8+$24#<0'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7????????>80&$28#10(+$28#<0##18#&6+$28#<0#3#7???8000#3)##7???7000#100000001000+$28#<0##18'+$28#<0#1000#7?????????>8)$2-1000#1000+$28#<0##18)$21##38+$28#<0##18)$22##4+$28#<0##18)$23##8+$28#<0##18)##10000#68<000+$28#<0##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqG4.

Module LibSegEb_bpqG5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#20$28$;$<$=$>$?$10$11+$2-60#10+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#180!$21#28,8+$24#180'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7????????=00&$28#10(+$28#180##18#&6+$28#180#3#7???8000#3)##7???7000#100000001000+$28#180##18'+$28#180#1000#7?????????>8)$2-1000#1000+$28#180##18)$21##38+$28#180##18)$22##4+$28#180##18)$23##8+$28#180##18)##10000#68<000+$28#180##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (384))), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (384))), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;1110+$2-<0$3$4$5$6$7+$2-60+$21#18$24+$24#180+$24#180+$24#180#1#&6+$21#28#3$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,49!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#198!$28#190,8#!$28#188,8$27!$28#180,4$26!$2-48,8+$28#300!$2-58,8+$28#180!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#180!$21#28,8+$24#180'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7????????=00&$28#10(+$28#180##18#&6+$28#180#3#7???8000#3)##7???7000#100000001000+$28#180##18'+$28#180#1000#7?????????>8)$2-1000#1000+$28#180##18)$21##38+$28#180##18)$22##4+$28#180##18)$23##8+$28#180##18)##10000#68<000+$28#180##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqG5.

Module LibSegEb_bpqG6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#40$28$;$<$=$>$?$10$11+$2-60#20+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#300!$21#28,8+$24#300'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7????????:00&$28#10(+$28#300##18#&6+$28#300#3#7???8000#3)##7???7000#100000001000+$28#300##18'+$28#300#1000#7?????????>8)$2-1000#1000+$28#300##18)$21##38+$28#300##18)$22##4+$28#300##18)$23##8+$28#300##18)##10000#68<000+$28#300##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (768))), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (768))), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;1110+$2-<0$3$4$5$6$7+$2-60+$21#18$24+$24#300+$24#300+$24#300#1#&6+$21#28#3$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,49!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#318!$28#310,8#!$28#308,8$27!$28#300,4$26!$2-48,8+$28#600!$2-58,8+$28#300!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#300!$21#28,8+$24#300'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7????????:00&$28#10(+$28#300##18#&6+$28#300#3#7???8000#3)##7???7000#100000001000+$28#300##18'+$28#300#1000#7?????????>8)$2-1000#1000+$28#300##18)$21##38+$28#300##18)$22##4+$28#300##18)$23##8+$28#300##18)##10000#68<000+$28#300##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqG6.

Module LibSegEb_bpqG7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#80$28$;$<$=$>$?$10$11+$2-60#40+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#600!$21#28,8+$24#600'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7????????400&$28#10(+$28#600##18#&6+$28#600#3#7???8000#3)##7???7000#100000001000+$28#600##18'+$28#600#1000#7?????????>8)$2-1000#1000+$28#600##18)$21##38+$28#600##18)$22##4+$28#600##18)$23##8+$28#600##18)##10000#68<000+$28#600##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (1536))), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (1536))), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;1110+$2-<0$3$4$5$6$7+$2-60+$21#18$24+$24#600+$24#600+$24#600#1#&6+$21#28#3$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,49!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#618!$28#610,8#!$28#608,8$27!$28#600,4$26!$2-48,8+$28#<00!$2-58,8+$28#600!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#600!$21#28,8+$24#600'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7????????400&$28#10(+$28#600##18#&6+$28#600#3#7???8000#3)##7???7000#100000001000+$28#600##18'+$28#600#1000#7?????????>8)$2-1000#1000+$28#600##18)$21##38+$28#600##18)$22##4+$28#600##18)$23##8+$28#600##18)##10000#68<000+$28#600##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqG7.

Module LibSegEb_bpqG8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#100$28$;$<$=$>$?$10$11+$2-60#80+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#<00!$21#28,8+$24#<00'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7???????>800&$28#10(+$28#<00##18#&6+$28#<00#3#7???8000#3)##7???7000#100000001000+$28#<00##18'+$28#<00#1000#7?????????>8)$2-1000#1000+$28#<00##18)$21##38+$28#<00##18)$22##4+$28#<00##18)$23##8+$28#<00##18)##10000#68<000+$28#<00##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (3072))), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (3072))), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;1110+$2-<0$3$4$5$6$7+$2-60+$21#18$24+$24#<00+$24#<00+$24#<00#1#&6+$21#28#3$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,49!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#<18!$28#<10,8#!$28#<08,8$27!$28#<00,4$26!$2-48,8+$28#1800!$2-58,8+$28#<00!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#<00!$21#28,8+$24#<00'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7???????>800&$28#10(+$28#<00##18#&6+$28#<00#3#7???8000#3)##7???7000#100000001000+$28#<00##18'+$28#<00#1000#7?????????>8)$2-1000#1000+$28#<00##18)$21##38+$28#<00##18)$22##4+$28#<00##18)$23##8+$28#<00##18)##10000#68<000+$28#<00##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqG8.

Module LibSegEb_bpqG9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#200$28$;$<$=$>$?$10$11+$2-60#100+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#1800!$21#28,8+$24#1800'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7???????=000&$28#10(+$28#1800##18#&6+$28#1800#3#7???8000#3)##7???7000#100000001000+$28#1800##18'+$28#1800#1000#7?????????>8)$2-1000#1000+$28#1800##18)$21##38+$28#1800##18)$22##4+$28#1800##18)$23##8+$28#1800##18)##10000#68<000+$28#1800##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;0720!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 723940 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (6144))), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (6144))), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;1110+$2-<0$3$4$5$6$7+$2-60+$21#18$24+$24#1800+$24#1800+$24#1800#1#&6+$21#28#3$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,49!$2-<8,8#;1110!$2-<0,8+$2-60!$2-;8,8#;0=40!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#20#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8+$21#18!$2-70,8+$21#20!$2-68,8#;07;8!$2-50,8+$28#1818!$28#1810,8#!$28#1808,8$27!$28#1800,4$26!$2-48,8+$28#3000!$2-58,8+$28#1800!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#1800!$21#28,8+$24#1800'$24#1000#7?????????>8&$24#8'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##38$22##4'$26##3'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##38$23##8'$27##1000000'$28#1000#7???????=000&$28#10(+$28#1800##18#&6+$28#1800#3#7???8000#3)##7???7000#100000001000+$28#1800##18'+$28#1800#1000#7?????????>8)$2-1000#1000+$28#1800##18)$21##38+$28#1800##18)$22##4+$28#1800##18)$23##8+$28#1800##18)##10000#68<000+$28#1800##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 723940 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 723940 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqG9.

Module LibSegEb_bpqH1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$2-60+$21#18$:$;$<$=$>$?$10$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#18!$21#28,8+$24#18'$24#1000#7?????????>8&$24#8'$28#1000#7?????????=0&$28#10'+$28#18#1000#7?????????>8!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-;8,8#;0=40!$2-<0,8+$2-60!$2-60,8$28!$2-58,8+$28#18!$2-50,8+$28#30!$2-48,8+$28#30!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 725264 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;0==<+$2-;0$3$4$5$6$7+$2-60+$21#18$28$24#18^#?#??????????????8#$?$10$11+$21#20+$2-58$28#7???8000+&6+$21#20#3#7???8000+&6+$2-58#3#7???8000+&6+$21#18#3#7???8000$19$1:$1;$1<$1=$1>$1?,,2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#18!$21#28,8+$24#18'$24#1000#7?????????>8&$24#8'$28#1000#7?????????=0&$28#10'+$28#18#1000#7?????????>8!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-;8,8#;0=40!$2-<0,8+$2-60!$2-60,8$28!$2-58,8+$28#18!$2-50,8+$28#30!$2-48,8+$28#30!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725264 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 725264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqH1.

Module LibSegEb_bpqH10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$2-60+$21#18$:$;$<$=$>$?$10$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#3000!$21#28,8+$24#3000'$24#1000#7?????????>8&$24#8'$28#1000#7???????:000&$28#10'+$28#3000#1000#7?????????>8!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-;8,8#;0=40!$2-<0,8+$2-60!$2-60,8$28!$2-58,8+$28#3000!$2-50,8+$28#3018!$2-48,8+$28#6000!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 725264 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;0==<+$2-;0$3$4$5$6$7+$2-60+$21#18$28$24#3000^#?#????????????000#$?$10$11+$21#20+$2-58$28#7???8000+&6+$21#20#3#7???8000+&6+$2-58#3#7???8000+&6+$21#18#3#7???8000$19$1:$1;$1<$1=$1>$1?,,2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#3000!$21#28,8+$24#3000'$24#1000#7?????????>8&$24#8'$28#1000#7???????:000&$28#10'+$28#3000#1000#7?????????>8!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-;8,8#;0=40!$2-<0,8+$2-60!$2-60,8$28!$2-58,8+$28#3000!$2-50,8+$28#3018!$2-48,8+$28#6000!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725264 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 725264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqH10.

Module LibSegEb_bpqH11.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$2-60+$21#18$:$;$<$=$>$?$10$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#6000!$21#28,8+$24#6000'$24#1000#7?????????>8&$24#8'$28#1000#7???????4000&$28#10'+$28#6000#1000#7?????????>8!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-;8,8#;0=40!$2-<0,8+$2-60!$2-60,8$28!$2-58,8+$28#6000!$2-50,8+$28#6018!$2-48,8+$28#<000!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 725264 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;0==<+$2-;0$3$4$5$6$7+$2-60+$21#18$28$24#6000^#?#???????????>000#$?$10$11+$21#20+$2-58$28#7???8000+&6+$21#20#3#7???8000+&6+$2-58#3#7???8000+&6+$21#18#3#7???8000$19$1:$1;$1<$1=$1>$1?,,2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#6000!$21#28,8+$24#6000'$24#1000#7?????????>8&$24#8'$28#1000#7???????4000&$28#10'+$28#6000#1000#7?????????>8!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-;8,8#;0=40!$2-<0,8+$2-60!$2-60,8$28!$2-58,8+$28#6000!$2-50,8+$28#6018!$2-48,8+$28#<000!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725264 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 725264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqH11.

Module LibSegEb_bpqH2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$2-60+$21#18$:$;$<$=$>$?$10$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#30!$21#28,8+$24#30'$24#1000#7?????????>8&$24#8'$28#1000#7?????????:0&$28#10'+$28#30#1000#7?????????>8!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-;8,8#;0=40!$2-<0,8+$2-60!$2-60,8$28!$2-58,8+$28#30!$2-50,8+$28#48!$2-48,8+$28#60!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 725264 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;0==<+$2-;0$3$4$5$6$7+$2-60+$21#18$28$24#30^#?#??????????????0#$?$10$11+$21#20+$2-58$28#7???8000+&6+$21#20#3#7???8000+&6+$2-58#3#7???8000+&6+$21#18#3#7???8000$19$1:$1;$1<$1=$1>$1?,,2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#30!$21#28,8+$24#30'$24#1000#7?????????>8&$24#8'$28#1000#7?????????:0&$28#10'+$28#30#1000#7?????????>8!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-;8,8#;0=40!$2-<0,8+$2-60!$2-60,8$28!$2-58,8+$28#30!$2-50,8+$28#48!$2-48,8+$28#60!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725264 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 725264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqH2.

Module LibSegEb_bpqH3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_24db52.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_24db52.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$2-60+$21#18$:$;$<$=$>$?$10$11$23$22+&6+$21#20#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#60!$21#28,8+$24#60'$24#1000#7?????????>8&$24#8'$28#1000#7?????????40&$28#10'+$28#60#1000#7?????????>8!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-;8,8#;0=40!$2-<0,8+$2-60!$2-60,8$28!$2-58,8+$28#60!$2-50,8+$28#78!$2-48,8+$28#<0!$2-40,8+$21#18"%pstring).
Definition ss0 : sym_state := SS 725264 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;0==<+$2-;0$3$4$5$6$7+$2-60+$21#18$28$24#60^#?#?????????????>0#$?$10$11+$21#20+$2-58$28#7???8000+&6+$21#20#3#7???8000+&6+$2-58#3#7???8000+&6+$21#18#3#7???8000$19$1:$1;$1<$1=$1>$1?,,2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#68<000$21##38!$21#18,8$24!$21#20,8+$24#60!$21#28,8+$24#60'$24#1000#7?????????>8&$24#8'$28#1000#7?????????40&$28#10'+$28#60#1000#7?????????>8!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;07;8!$2-70,8+$21#20!$2-78,8+$21#18!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#20#3#7???8000!$2-98,8#7???8000!$2-:0,8$16!$2-:8,8$17!$2-;0,8$18!$2-;8,8#;0=40!$2-<0,8+$2-60!$2-60,8$28!$2-58,8+$28#60!$2-50,8+$28#78!$2-48,8+$28#<0!$2-40,8+$21#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_24db52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725264 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_24db52.IT BndT_Eb_000.SegItab_Eb_24db52.IT_sound BF NX0 BR XSTEP F0 PSS plan 725264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bpqH3.
