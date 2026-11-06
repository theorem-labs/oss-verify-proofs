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

Module LibSegEb_bskC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_95e256.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_95e256.IT.
Definition ENDS : list Z := [725876].
Definition STOPS1 : list Z := [725876] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$8$9$37$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200!$2-28,8#;1264!$2-30,8$2=!$2-38,8$2>"%pstring).
Definition ss0 : sym_state := SS 725860 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;1374#;1374#5=#;1374,20##;1264+$2-20$3$4$5$6$7$2=$2>$37$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200!$2-28,8#;1264!$2-30,8$2=!$2-38,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 725876 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_95e256.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725860 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_95e256.IT BndT_Eb_001.SegItab_Eb_95e256.IT_sound BF NX0 BR XSTEP F0 PSS plan 725860 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskC.

Module LibSegEb_bskD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_95e256.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_95e256.IT.
Definition ENDS : list Z := [725664].
Definition STOPS1 : list Z := [725664] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7+$:#8+&6+$:#8#3#7???8000$37$38$39$=$>$?$10$11+$21$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801020#800000000000&$2#10($2-20#20'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?'$21#1000#800000000000&$21#10'$22##80000000'$23##80000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#68<000$21#$23"%pstring).
Definition ss0 : sym_state := SS 725604 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 10), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;12:0#;12:0#5=#;12:0,20#$2<$2$3$4$5$6$7$2=$2>++$21$22#1#2$39$=$>$?$10$11$2?$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18!$:#8,8++$21$22#1%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801020#800000000000&$2#10($2-20#20'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?'$21#1000#800000000000&$21#10'$22##80000000'$23##80000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#68<000$21#$23,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 725664 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_95e256.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725604 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_95e256.IT BndT_Eb_001.SegItab_Eb_95e256.IT_sound BF NX0 BR XSTEP F0 PSS plan 725604 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskD.

Module LibSegEb_bskR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_95e256.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_95e256.IT.
Definition ENDS : list Z := [725664].
Definition STOPS1 : list Z := [725664] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7+$:#8+&6+$:#8#3#7???8000$29$38$39$=$>$?$10$11+$21$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801020#800000000000&$2#10($2-20#20'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?'$21##800000000000'$22##80000000'$23##80000000'+$21$23##800000000000'$29#2#800000000000"%pstring).
Definition ss0 : sym_state := SS 725624 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 10), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;12:0#;12:0#5=#;12:0,20#$2<$2$3$4$5$6$7$2=$2>$29#2$39$=$>$?$10$11$2?$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$:#8,8$29%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801020#800000000000&$2#10($2-20#20'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?'$21##800000000000'$22##80000000'$23##80000000'+$21$23##800000000000'$29#2#800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 725664 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_95e256.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725624 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_95e256.IT BndT_Eb_001.SegItab_Eb_95e256.IT_sound BF NX0 BR XSTEP F0 PSS plan 725624 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskR.

Module LibSegEb_bskS1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9c4373.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9c4373.IT.
Definition ENDS : list Z := [1271400].
Definition STOPS1 : list Z := [1271400] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##;1278+$2-20$3$4$5$6$7+$:#8+&6+$:#8#3#7???8000$:$;$39$=$>$?$10$11+$21$23$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8$21!$:#8,8+$21$23!$:#10,8+$21$23'$21#1000#800000000000&$21#10'$22##80000000'$23#2#40000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#68<000$21#$23"%pstring).
Definition ss0 : sym_state := SS 725920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 160)].
Definition F0L : list SR.region := [((EVar 2), (-192), 160)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#136668#136668#5=#136668,20##;1728+$2-<0$3$4$5$6$7+$2-60@#2$23@#2$23##1460?8$:^#3#???????????????$?$10$11+$2-78$23+&6+$2-60#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,2=!$2-58,8$:!$2-60,8#!$2-;8,8$15!$2-;0,8#7???8000!$2-:8,8+&6+$:#8#3#7???8000!$2-:0,8$;!$2-98,8$:!$2-90,8+$:#8!$2-88,8#;144<!$2-50,8$14!$2-48,8$13!$2-40,8+$21$23!$2-38,8+&6+$:#8#3#7???8000!$2-30,8+$:#8!$2-28,8#;1278%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8$21!$:#8,8+$21$23!$:#10,8+$21$23'$21#1000#800000000000&$21#10'$22##80000000'$23#2#40000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#68<000$21#$23,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1271400 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9c4373.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725920 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9c4373.IT BndT_Eb_001.SegItab_Eb_9c4373.IT_sound BF NX0 BR XSTEP F0 PSS plan 725920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskS1.

Module LibSegEb_bskS1o.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9c4373.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9c4373.IT.
Definition ENDS : list Z := [1271400].
Definition STOPS1 : list Z := [1271400] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##;1278+$2-20$3$4$5$6$7+$:#8+&6+$:#8#3#7???8000$:$;$39$=$>$?$10$11+$21#1$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8$21!$:#8,8+$21#1!$:#10,8+$21#1'$21#1000#7???????????&$21#10)##10000#68<000$21##1)##7???7000#100000001000$21##1"%pstring).
Definition ss0 : sym_state := SS 725920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 160)].
Definition F0L : list SR.region := [((EVar 2), (-192), 160)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#136668#136668#5=#136668,20##;1728+$2-<0$3$4$5$6$7+$2-60#2#2##1460?8$:^#3#???????????????$?$10$11+$2-78#1+&6+$2-60#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!$2-58,8$:!$2-60,8#!$2-;8,8$15!$2-;0,8#7???8000!$2-:8,8+&6+$:#8#3#7???8000!$2-:0,8$;!$2-98,8$:!$2-90,8+$:#8!$2-88,8#;144<!$2-50,8$14!$2-48,8$13!$2-40,8+$21#1!$2-38,8+&6+$:#8#3#7???8000!$2-30,8+$:#8!$2-28,8#;1278%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8$21!$:#8,8+$21#1!$:#10,8+$21#1'$21#1000#7???????????&$21#10)##10000#68<000$21##1)##7???7000#100000001000$21##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1271400 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9c4373.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725920 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9c4373.IT BndT_Eb_001.SegItab_Eb_9c4373.IT_sound BF NX0 BR XSTEP F0 PSS plan 725920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskS1o.

Module LibSegEb_bskS1z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9c4373.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9c4373.IT.
Definition ENDS : list Z := [1271400].
Definition STOPS1 : list Z := [1271400] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##;1278+$2-20$3$4$5$6$7+$:#8+&6+$:#8#3#7???8000$:$;$39$=$>$?$10$11#$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8#!$:#8,8#!$:#10,8#"%pstring).
Definition ss0 : sym_state := SS 725920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 160)].
Definition F0L : list SR.region := [((EVar 2), (-192), 160)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#136668#136668#5=#136668,20##;1728+$2-<0$3$4$5$6$7+$2-60#1#1##1460?8$:^#3#???????????????$?$10$11+$2-78#+&6+$2-60#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,26!$2-58,8$:!$2-60,8#!$2-;8,8$15!$2-;0,8#7???8000!$2-:8,8+&6+$:#8#3#7???8000!$2-:0,8$;!$2-98,8$:!$2-90,8+$:#8!$2-88,8#;144<!$2-50,8$14!$2-48,8$13!$2-40,8#!$2-38,8+&6+$:#8#3#7???8000!$2-30,8+$:#8!$2-28,8#;1278%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$;#1000#7???????????)##7???7000#100000001000$;##1#&6$;#3#7???8000#1!$;#,1$28'$28##??)$;##1$2-100#100)$;##1$:##18!$:#,8#!$:#8,8#!$:#10,8#,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1271400 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9c4373.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 725920 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9c4373.IT BndT_Eb_001.SegItab_Eb_9c4373.IT_sound BF NX0 BR XSTEP F0 PSS plan 725920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskS1z.

Module LibSegEb_bskS3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9c4373.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9c4373.IT.
Definition ENDS : list Z := [889352].
Definition STOPS1 : list Z := [889352] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$:#8$:$37$38$39$=$>$?$10$11$24+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$:#8,8++$22$25#1!$2-78,8$21!$2-70,8$21!$2-68,8$21!$2-60,8+$21$23'$21#1000#800000000000&$21#10'$22##80000000'$23#1#80000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#68<000$21#$23'$25#1000#800000000000'+$22$25#1000#7???????????'+$25$26#1000#800000000000'$26#1#80000000!$2-58,8$:"%pstring).
Definition ss0 : sym_state := SS 726172 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-144), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-144), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=9208#=9208#5=#=9208,20##;14;0+$2-80$3$4$5$6$7++$22$25#1$:$21$23$21#7???8000#+&6+$2-68#3#7???8000$21$21$24+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1?!$2-88,8#;14;0%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$:#8,8++$22$25#1!$2-78,8$21!$2-70,8$21!$2-68,8$21!$2-60,8+$21$23'$21#1000#800000000000&$21#10'$22##80000000'$23#1#80000000'+$21$23#1000#800000000000)##7???7000#100000001000$21#$23)##10000#68<000$21#$23'$25#1000#800000000000'+$22$25#1000#7???????????'+$25$26#1000#800000000000'$26#1#80000000!$2-58,8$:,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 889352 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9c4373.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726172 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9c4373.IT BndT_Eb_001.SegItab_Eb_9c4373.IT_sound BF NX0 BR XSTEP F0 PSS plan 726172 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskS3.

Module LibSegEb_bskS3n.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9c4373.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9c4373.IT.
Definition ENDS : list Z := [727756].
Definition STOPS1 : list Z := [727756] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$:#8$:$37$38$39$=$>$?$10$11$24+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$:#8,8+$25#1!$2-78,8#!$2-70,8#!$2-68,8#!$2-60,8#!$2-58,8$:'$25#1000#7???????????"%pstring).
Definition ss0 : sym_state := SS 726172 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-144), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-144), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;1:<<#;1:<<#5=#;1:<<,20##;14;0+$2-80$3$4$5$6$7+$25#1$:+$2-78+$2-58##7???8000&6+$2-58#3+&6+$2-68#3#7???8000##$24+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-88,8#;14;0%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$:#8,8+$25#1!$2-78,8#!$2-70,8#!$2-68,8#!$2-60,8#!$2-58,8$:'$25#1000#7???????????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 727756 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9c4373.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726172 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9c4373.IT BndT_Eb_001.SegItab_Eb_9c4373.IT_sound BF NX0 BR XSTEP F0 PSS plan 726172 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskS3n.

Module LibSegEb_bskS4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9c4373.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9c4373.IT.
Definition ENDS : list Z := [726224].
Definition STOPS1 : list Z := [726224] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$29$:$37$38$39$=$>$?$10$11$24+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$2-28,8#;1278!$2-30,8+$:#8!$2-38,8+&6+$:#8#3#7???8000!$2-40,8+$21$22!$2-48,8$32!$2-50,8$33'$21##800000000000'$22##80000000'$23##80000000'+$21$23##800000000000'$29##800000000000"%pstring).
Definition ss0 : sym_state := SS 726192 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;14=0#;14=0#5=#;14=0,20##;1278+$2-20$3$4$5$6$7+$:#8+&6+$:#8#3#7???8000$29$38$39$=$>$?$10$11+$21$22$32$33$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18!$2-28,8#;1278!$2-30,8+$:#8!$2-38,8+&6+$:#8#3#7???8000!$2-40,8+$21$22!$2-48,8$32!$2-50,8$33'$21##800000000000'$22##80000000'$23##80000000'+$21$23##800000000000'$29##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 726224 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9c4373.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726192 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9c4373.IT BndT_Eb_001.SegItab_Eb_9c4373.IT_sound BF NX0 BR XSTEP F0 PSS plan 726192 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskS4.

Module LibSegEb_bskT.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9c4373.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9c4373.IT.
Definition ENDS : list Z := [726988].
Definition STOPS1 : list Z := [726988] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$2-60$26$25$38$39$=$>$?$10$11+$2-78$22+&6+$2-60#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$25#1000#800000000000'$22##80000000'$26#1#80000000'+$25$26#1000#800000000000'+$22$25#1000#800000000000!$2-88,8#;144<!$2-90,8$27!$2-98,8$2:!$2-:0,8$2;!$2-:8,8$30!$2-;0,8$31!$2-;8,8$34"%pstring).
Definition ss0 : sym_state := SS 726824 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-120), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-120), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;17<<#;17<<#5=#;17<<,20##;144<+$2-80$3$4$5$6$7$27$2:###1#$>$?$10$11$2;$30$31$34$16$17$18$19$1:$1;$1<$1=$1>$1?,,17!$2-60,8+$25$26!$2-70,8+$22$25!$2-68,8+$22$25!$2-78,8$25%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$25#1000#800000000000'$22##80000000'$26#1#80000000'+$25$26#1000#800000000000'+$22$25#1000#800000000000!$2-88,8#;144<!$2-90,8$27!$2-98,8$2:!$2-:0,8$2;!$2-:8,8$30!$2-;0,8$31!$2-;8,8$34,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 726988 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9c4373.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726824 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9c4373.IT BndT_Eb_001.SegItab_Eb_9c4373.IT_sound BF NX0 BR XSTEP F0 PSS plan 726824 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskT.

Module LibSegEb_bskU.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9c4373.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9c4373.IT.
Definition ENDS : list Z := [700816].
Definition STOPS1 : list Z := [700816] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$:#8$:$37$38$39$=$>$?$10$11$24+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25$26#1000#800000000000)##7???7000#100000001000$25#$26)##10000#68<000$25#$26($25#$26)$2-100#100$25#$26)$:##18$25#$26)$24##1$25#$26!$2-78,8$25!$2-70,8+$22$25!$2-68,8+$22$25!$2-60,8+$25$26!$2-58,8$:'$22#4#40000000'$26#8#80000000'&1$26$22#4#80000000#&6+$22$25#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 726092 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 34) (EVar 37)), (0), ELit 1); ((EVar 2), (-104), ELit 8); ((EVar 2), (-208), ELit 80)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 34) (EVar 37)), (0), 1); ((EVar 2), (-104), 8); ((EVar 2), (-208), 80)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:;190#:;190#5=#:;190,20##;1844+$2-=0$3$4$5$6$7+$2-78$:$:#1460?8#$=$>$?$10$11$24+&6+$:#8#3#7???8000#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,30!$2-=0,8$18!$2-<8,8$17!$2-<0,8$16!$2-;8,8$15!$2-;0,8#7???8000!$2-:8,8+&6+$:#8#3#7???8000!$2-:0,8$24!$2-98,8$:!$2-90,8+$:#8!$2-88,8#;149<!$2-68,8++$22$25#1!+$22$25#,1$28%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25$26#1000#800000000000)##7???7000#100000001000$25#$26)##10000#68<000$25#$26($25#$26)$2-100#100$25#$26)$:##18$25#$26)$24##1$25#$26!$2-78,8$25!$2-70,8+$22$25!$2-60,8+$25$26!$2-58,8$:'$22#4#40000000'$26#8#80000000'&1$26$22#4#80000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 700816 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9c4373.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726092 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9c4373.IT BndT_Eb_001.SegItab_Eb_9c4373.IT_sound BF NX0 BR XSTEP F0 PSS plan 726092 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskU.

Module LibSegEb_bskUo.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9c4373.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9c4373.IT.
Definition ENDS : list Z := [700816].
Definition STOPS1 : list Z := [700816] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$:#8$:$37$38$39$=$>$?$10$11$24+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#2#1000#800000000000)##7???7000#100000001000$25##2)##10000#68<000$25##2($25##2)$2-100#100$25##2)$:##18$25##2)$24##1$25##2!$2-78,8$25!$2-70,8+$25#1!$2-68,8+$25#1!$2-60,8+$25#2!$2-58,8$:!&6+$25#1#3#7???8000,1#2"%pstring).
Definition ss0 : sym_state := SS 726092 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 37), (1), ELit 1); ((EVar 2), (-104), ELit 8); ((EVar 2), (-208), ELit 80)].
Definition F0L : list SR.region := [((EVar 37), (1), 1); ((EVar 2), (-104), 8); ((EVar 2), (-208), 80)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:;190#:;190#5=#:;190,20##;1844+$2-=0$3$4$5$6$7+$2-78$:$:#1460?8#2#1$>$?$10$11$24+&6+$:#8#3#7???8000#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,2=!$2-=0,8$18!$2-<8,8$17!$2-<0,8$16!$2-;8,8$15!$2-;0,8#7???8000!$2-:8,8+&6+$:#8#3#7???8000!$2-:0,8$24!$2-98,8$:!$2-90,8+$:#8!$2-88,8#;149<!$2-68,8+$25#2!$25#1,1$28%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#2#1000#800000000000)##7???7000#100000001000$25##2)##10000#68<000$25##2($25##2)$2-100#100$25##2)$:##18$25##2)$24##1$25##2!$2-78,8$25!$2-70,8+$25#1!$2-60,8+$25#2!$2-58,8$:,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 700816 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9c4373.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726092 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9c4373.IT BndT_Eb_001.SegItab_Eb_9c4373.IT_sound BF NX0 BR XSTEP F0 PSS plan 726092 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskUo.

Module LibSegEb_bskUt.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9c4373.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9c4373.IT.
Definition ENDS : list Z := [700816].
Definition STOPS1 : list Z := [700816] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$:#8$:$37$38$39$=$>$?$10$11$24+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#4#1000#800000000000)##7???7000#100000001000$25##4)##10000#68<000$25##4($25##4)$2-100#100$25##4)$:##18$25##4)$24##1$25##4!$2-78,8$25!$2-70,8+$25#2!$2-68,8+$25#2!$2-60,8+$25#4!$2-58,8$:!&6+$25#2#3#7???8000,1#4"%pstring).
Definition ss0 : sym_state := SS 726092 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 37), (2), ELit 1); ((EVar 2), (-104), ELit 8); ((EVar 2), (-208), ELit 80)].
Definition F0L : list SR.region := [((EVar 37), (2), 1); ((EVar 2), (-104), 8); ((EVar 2), (-208), 80)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:;190#:;190#5=#:;190,20##;1844+$2-=0$3$4$5$6$7+$2-78$:$:#1460?8#4#2$>$?$10$11$24+&6+$:#8#3#7???8000#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,2=!$2-=0,8$18!$2-<8,8$17!$2-<0,8$16!$2-;8,8$15!$2-;0,8#7???8000!$2-:8,8+&6+$:#8#3#7???8000!$2-:0,8$24!$2-98,8$:!$2-90,8+$:#8!$2-88,8#;149<!$2-68,8+$25#3!$25#2,1$28%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#4#1000#800000000000)##7???7000#100000001000$25##4)##10000#68<000$25##4($25##4)$2-100#100$25##4)$:##18$25##4)$24##1$25##4!$2-78,8$25!$2-70,8+$25#2!$2-60,8+$25#4!$2-58,8$:,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 700816 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9c4373.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726092 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9c4373.IT BndT_Eb_001.SegItab_Eb_9c4373.IT_sound BF NX0 BR XSTEP F0 PSS plan 726092 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskUt.

Module LibSegEb_bskUz.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9c4373.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9c4373.IT.
Definition ENDS : list Z := [700816].
Definition STOPS1 : list Z := [700816] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$:#8$:$37$38$39$=$>$?$10$11$24+&6+$:#8#3#7???8000#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#1#1000#800000000000)##7???7000#100000001000$25##1)##10000#68<000$25##1($25##1)$2-100#100$25##1)$:##18$25##1)$24##1$25##1!$2-78,8$25!$2-70,8$25!$2-68,8$25!$2-60,8+$25#1!$2-58,8$:!&6$25#3#7???8000,1#1"%pstring).
Definition ss0 : sym_state := SS 726092 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 37), (0), ELit 1); ((EVar 2), (-104), ELit 8); ((EVar 2), (-208), ELit 80)].
Definition F0L : list SR.region := [((EVar 37), (0), 1); ((EVar 2), (-104), 8); ((EVar 2), (-208), 80)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:;190#:;190#5=#:;190,20##;1844+$2-=0$3$4$5$6$7+$2-78$:$:#1460?8#1#$>$?$10$11$24+&6+$:#8#3#7???8000#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,2=!$2-=0,8$18!$2-<8,8$17!$2-<0,8$16!$2-;8,8$15!$2-;0,8#7???8000!$2-:8,8+&6+$:#8#3#7???8000!$2-:0,8$24!$2-98,8$:!$2-90,8+$:#8!$2-88,8#;149<!$2-68,8+$25#1!$25#,1$28%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801100#800000000000&$2#10($2-100#100#&6$2#3#7???7>00#200'$:#69<000#7?????????>8&$:#8)##7???7000#100000001000$:##18#&6$:#3#7???8000#3($:##18)$2-100#100$:##18'$24#1000#7???????????)##7???7000#100000001000$24##1#&6$24#3#7???8000#1!$24#,1$28'$28##??)$24##1$2-100#100)$24##1$:##18'$25#1000#800000000000&$25#10'+$25#1#1000#800000000000)##7???7000#100000001000$25##1)##10000#68<000$25##1($25##1)$2-100#100$25##1)$:##18$25##1)$24##1$25##1!$2-78,8$25!$2-70,8$25!$2-60,8+$25#1!$2-58,8$:,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 700816 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9c4373.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726092 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9c4373.IT BndT_Eb_001.SegItab_Eb_9c4373.IT_sound BF NX0 BR XSTEP F0 PSS plan 726092 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bskUz.
