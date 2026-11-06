(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ea0PlanKit Ea0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Ea_000 BndT_Ea_001.

Module LibSegEa_aeqS8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_1e7eb8.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_1e7eb8.IT.
Definition ENDS : list Z := [1253056].
Definition STOPS1 : list Z := [1253056] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9+$21#18$22$23$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#688000$21##38!$21#18,8$24!$21#20,8+$24#<00!$21#28,8+$24#<00'$24#1000#7?????????>8&$24#8"%pstring).
Definition ss0 : sym_state := SS 713708 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#131><0#131><0#5=#131><0,20##:>>=<+$2-80$3$4$5$6$7#100+$21#18#1800#2000#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#<00+&6+$21#20#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#20!$2-78,8#:>55<!$2-48,8+$21#18!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#688000$21##38!$21#18,8$24!$21#20,8+$24#<00!$21#28,8+$24#<00'$24#1000#7?????????>8&$24#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1253056 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_1e7eb8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 713708 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_1e7eb8.IT BndT_Ea_000.SegItab_Ea_1e7eb8.IT_sound BF NX0 BR XSTEP F0 PSS plan 713708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aeqS8.

Module LibSegEa_aeqS9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_1e7eb8.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_1e7eb8.IT.
Definition ENDS : list Z := [1253056].
Definition STOPS1 : list Z := [1253056] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9+$21#18$22$23$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#688000$21##38!$21#18,8$24!$21#20,8+$24#1800!$21#28,8+$24#1800'$24#1000#7?????????>8&$24#8"%pstring).
Definition ss0 : sym_state := SS 713708 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#131><0#131><0#5=#131><0,20##:>>=<+$2-80$3$4$5$6$7#200+$21#18#3000#4000#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#1800+&6+$21#20#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#20!$2-78,8#:>55<!$2-48,8+$21#18!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????;?&$21#8)##7???7000#100000001000$21##38#&6$21#3#7???8000#7)$2-1000#1000$21##38)##10000#688000$21##38!$21#18,8$24!$21#20,8+$24#1800!$21#28,8+$24#1800'$24#1000#7?????????>8&$24#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1253056 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_1e7eb8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 713708 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_1e7eb8.IT BndT_Ea_000.SegItab_Ea_1e7eb8.IT_sound BF NX0 BR XSTEP F0 PSS plan 713708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aeqS9.

Module LibSegEa_aerB1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_1adbd2.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_1adbd2.IT.
Definition ENDS : list Z := [451484].
Definition STOPS1 : list Z := [451484] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 34; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?801080#800000000000&$2#10($2-80#80%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#1000#7??????????0&$21#8)##7???7000#100000001000$21##10#&6$21#3#7???8000#2($21##10)$2-80#80$21##10'$22#1#40%#674080#674082(##674080#2"%pstring).
Definition ss0 : sym_state := SS 713488 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-32), ELit 32); ((ELit 0), (6766720), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-32), 32); ((ELit 0), (6766720), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6>39<#6>39<#5=#6>39<,20##:>3=0+$2-20$3$4$5$6$7$21$22#=61=8#13=8?0#13:?<8$=$>$?$10$11#7???8000$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!##674081,1#2!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801080#800000000000&$2#10($2-80#80%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#1000#7??????????0&$21#8)##7???7000#100000001000$21##10#&6$21#3#7???8000#2($21##10)$2-80#80$21##10'$22#1#40%#674080#674081(##674080#2,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 451484 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_1adbd2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 713488 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_1adbd2.IT BndT_Ea_000.SegItab_Ea_1adbd2.IT_sound BF NX0 BR XSTEP F0 PSS plan 713488 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aerB1.

Module LibSegEa_aesE0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ee7ce7.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ee7ce7.IT.
Definition ENDS : list Z := [1253056].
Definition STOPS1 : list Z := [1253056] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); (EVar 52); EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8#!$21#8,8#!$21#10,8#"%pstring).
Definition ss0 : sym_state := SS 752120 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#131><0#131><0#5=#131><0,20##;225<+$2-80$3$4$5$6$7#1$34#20#1^#7#?????????????>0#$>$?$10$11$21$23$22#+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?,,1;!$2-80,8+$21#8!$2-78,8#;7;84!$2-50,8$21!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8#!$21#8,8#!$21#10,8#,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1253056 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ee7ce7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 752120 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ee7ce7.IT BndT_Ea_001.SegItab_Ea_ee7ce7.IT_sound BF NX0 BR XSTEP F0 PSS plan 752120 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aesE0.

Module LibSegEa_aesE1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ee7ce7.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ee7ce7.IT.
Definition ENDS : list Z := [493080].
Definition STOPS1 : list Z := [493080] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7#1$34$28$;$<$=$>$?$10$11$21$23$22#+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3?'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8#!$21#8,8#!$21#10,8#'$22#698000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#698000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8'$34#698000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$22##4)$21##18$23##8)$21##18$34##1'$26##7???????'$27#^#?#???????????????'$35##??'$28#1000#7?????????>0&$28#10)##7???7000#100000001000$28##20#&6$28#3#7???8000#4($28##20)$2-1000#1000$28##20)$21##18$28##20)$22##4$28##20)$23##8$28##20)$34##1$28##20)##10000#688000$28##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-80,8+$21#8!$2-78,8#;7;84!$2-50,8$21"%pstring).
Definition ss0 : sym_state := SS 729692 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 40), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 40), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78618#78618#5=#78618,20##;2068+$2-:0$3$4$5$6$7+$2-70$21$28###7???8000#$?$10$11$28#7???8000$22#+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?,,4<!$2-;0,8+$2-70!$2-:8,8#;2014!$2-98,8$23!$2-90,8$21!$2-88,8$34!$2-80,8+$21#8!$2-78,8#;7<54!$2-60,8+$28#20!$28#18,8#!$28#10,1$35!$28#8,8$27!$28#,4$26!$2-58,8+$28#20!$2-68,8$28!$2-70,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8#!$21#8,8#!$21#10,8#'$22#698000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#698000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8'$34#698000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$22##4)$21##18$23##8)$21##18$34##1'$26##7???????'$27#^#?#???????????????'$35##??'$28#1000#7?????????>0&$28#10)##7???7000#100000001000$28##20#&6$28#3#7???8000#4($28##20)$2-1000#1000$28##20)$21##18$28##20)$22##4$28##20)$23##8$28##20)$34##1$28##20)##10000#688000$28##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-50,8$21,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 493080 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ee7ce7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 729692 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ee7ce7.IT BndT_Ea_001.SegItab_Ea_ee7ce7.IT_sound BF NX0 BR XSTEP F0 PSS plan 729692 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aesE1.

Module LibSegEa_aesE2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ee7ce7.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ee7ce7.IT.
Definition ENDS : list Z := [508928].
Definition STOPS1 : list Z := [508928] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-70$21$:$;$<$=$>$?$10$11$28#7???8000$22#+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2?'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18!$21#,8#!$21#8,8#!$21#10,8#'$28#1000#7?????????>0&$28#10)##7???7000#100000001000$28##20#&6$28#3#7???8000#4($28##20)$2-1000#1000$28##20)$21##18$28##20)$22##4$28##20)$23##8$28##20)$34##1$28##20)##10000#688000$28##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-78,8#;7<54!$2-80,8+$21#8!$2-88,8$34!$2-90,8$21!$2-98,8$23!$2-70,8$28!$2-68,8$28!$2-60,8+$28#20!$2-58,8+$28#20!$2-50,8$21"%pstring).
Definition ss0 : sym_state := SS 729192 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<400#7<400#5=#7<400,20##;22=4+$2-80$3$4$5$6$7+$21#8$34$28+$28#20+$28#20+$28#20&6+$21#10#3$?$10$11$21$23$22#+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?,,2?!$2-80,8+$21#8!$2-78,8#;7<54!$2-70,8#!$2-58,8#!$21#10,8+$28#20!$2-60,8#!$21#8,8+$28#20!$2-68,8#!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18'$28#1000#7?????????>0&$28#10)##7???7000#100000001000$28##20#&6$28#3#7???8000#4($28##20)$2-1000#1000$28##20)$21##18$28##20)$22##4$28##20)$23##8$28##20)$34##1$28##20)##10000#688000$28##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-88,8$34!$2-90,8$21!$2-98,8$23!$2-50,8$21,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 508928 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ee7ce7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 729192 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ee7ce7.IT BndT_Ea_001.SegItab_Ea_ee7ce7.IT_sound BF NX0 BR XSTEP F0 PSS plan 729192 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aesE2.

Module LibSegEa_aesE3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ee7ce7.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ee7ce7.IT.
Definition ENDS : list Z := [752800].
Definition STOPS1 : list Z := [752800] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$21#8$34$:$;$<$=$>$?$10$11$21$23$22#+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18!$21#,8$28!$21#8,8+$28#20!$21#10,8+$28#20'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-78,8#;7<54!$2-80,8+$21#8!$2-70,8#!$2-68,8#!$2-60,8#!$2-58,8#!$2-50,8$21"%pstring).
Definition ss0 : sym_state := SS 729812 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;7<:0#;7<:0#5=#;7<:0,20#$2;$2$3$4$5$6$7$2<$2=$28###7???8000+&6+$2-60#3#7???8000#$10$11$2>$2?$30$31$32$33$18$19$1:$1;$1<$1=$1>$1?,,23!$21#8,8+$28#20!$2-78,8#;7<68'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18!$21#,8$28!$21#10,8+$28#20'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-80,8+$21#8!$2-70,8#!$2-68,8#!$2-60,8#!$2-58,8#!$2-50,8$21,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 752800 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ee7ce7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 729812 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ee7ce7.IT BndT_Ea_001.SegItab_Ea_ee7ce7.IT_sound BF NX0 BR XSTEP F0 PSS plan 729812 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aesE3.

Module LibSegEa_aesF1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ee7ce7.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ee7ce7.IT.
Definition ENDS : list Z := [508928].
Definition STOPS1 : list Z := [508928] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); (EVar 52); EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8$29'$24#1000#7?????????>0&$24#10'$25##??>0&$25#20'$29#1020#7???????????'&1$29+$24$25#20#10000"%pstring).
Definition ss0 : sym_state := SS 752120 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<400#7<400#5=#7<400,20##;1?;0+$2-80$3$4$5$6$7+$21#8$34$24$29+$24$25++$24$25#20$24$29$10$11$21$23$22+$24$25+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?,,21!$2-80,8+$21#8!$2-78,8#;7:7<!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8$29'$24#1000#7?????????>0&$24#10'$25##??>0&$25#20'$29#1020#7???????????'&1$29+$24$25#20#10000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 508928 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ee7ce7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 752120 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ee7ce7.IT BndT_Ea_001.SegItab_Ea_ee7ce7.IT_sound BF NX0 BR XSTEP F0 PSS plan 752120 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aesF1.

Module LibSegEa_aesF2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ee7ce7.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ee7ce7.IT.
Definition ENDS : list Z := [752800].
Definition STOPS1 : list Z := [752800] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$21#8$34$:$;$<$=$>$?$10$11$21$23$22+$24$25+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8$29'$24#1000#7?????????>0&$24#10'$22#698000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#698000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8'$34#698000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$22##4)$21##18$23##8)$21##18$34##1'$26##7???????'$27#^#?#???????????????'$35##??!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-78,8#;7:7<!$2-80,8+$21#8'$25##??>0&$25#20'$29#1020#7???????????'&1$29+$24$25#20#10000#&6+$24$25#3#7???8000#4(+$24$25##20)##7???7000#100000001000+$24$25##20)##10000#688000+$24$25##20'+$24$25#1000#7?????????>0)$2-1000#1000+$24$25##20)$21##18+$24$25##20)$22##4+$24$25##20)$23##8+$24$25##20)$34##1+$24$25##20"%pstring).
Definition ss0 : sym_state := SS 729008 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 36) (EVar 37)), (0), ELit 32); ((EVar 33), (8), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 36) (EVar 37)), (0), 32); ((EVar 33), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;7<:0#;7<:0#5=#;7<:0,20#$2;$2$3$4$5$6$7$2<$2=+$24$25#$35#$>$?$10$11$2>$2?$30$31$32$33$18$19$1:$1;$1<$1=$1>$1?,,48!$21#8,8++$24$25#20!+$24$25#18,8#!+$24$25#10,1$35!+$24$25#8,8$27!+$24$25#,4$26'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18!$21#,8$24!$21#10,8$29'$24#1000#7?????????>0&$24#10'$22#698000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#698000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8'$34#698000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$22##4)$21##18$23##8)$21##18$34##1'$26##7???????'$27#^#?#???????????????'$35##??!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-78,8#;7:7<!$2-80,8+$21#8'$25##??>0&$25#20'$29#1020#7???????????'&1$29+$24$25#20#10000#&6+$24$25#3#7???8000#4(+$24$25##20)##7???7000#100000001000+$24$25##20)##10000#688000+$24$25##20'+$24$25#1000#7?????????>0)$2-1000#1000+$24$25##20)$21##18+$24$25##20)$22##4+$24$25##20)$23##8+$24$25##20)$34##1+$24$25##20,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 752800 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ee7ce7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 729008 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ee7ce7.IT BndT_Ea_001.SegItab_Ea_ee7ce7.IT_sound BF NX0 BR XSTEP F0 PSS plan 729008 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aesF2.

Module LibSegEa_aesG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ee7ce7.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ee7ce7.IT.
Definition ENDS : list Z := [508928].
Definition STOPS1 : list Z := [508928] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2:$34$28$;$<$=$>$?$10$11$21$23$22$25+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",45'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8+$24$25'$24#1000#7?????????>0&$24#10'$25#20#8000&$25#20'$2:#2#800'$22#698000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#698000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8'$34#698000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$22##4)$21##18$23##8)$21##18$34##1'$26##7???????'$27#^#?#???????????????'$35##??'$28#1000#7?????????<0&$28#10(+$28$25##20#&6+$28$25#3#7???8000#4)##7???7000#100000001000+$28$25##20'+$28$25#1000#7?????????>0)$2-1000#1000+$28$25##20)$21##18+$28$25##20)$22##4+$28$25##20)$23##8+$28$25##20)$34##1+$28$25##20)##10000#688000+$28$25##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-80,8+$21#8!$2-78,8#;7;84!$2-50,8$21"%pstring).
Definition ss0 : sym_state := SS 729692 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EAlu Instr.ALU_ADD (EVar 40) (EVar 37)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EAlu Instr.ALU_ADD (EVar 40) (EVar 37)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",4!!,2#7<400#7<400!!,2#7<400#7<400!!,2#7<400#7<400!!,2#7<400#7<400#5=#7<400,20##::050+$2-;0$3$4$5$6$7+$2-70$21$24+$24$25+$24$25+$24$25&6+$21#8#3$?$10$11$21#7???8000$22$25+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?,,52!$2-;0,8+$2-70!$2-:8,8#;2014!$2-98,8$23!$2-90,8$21!$2-88,8$34!$2-80,8+$21#8!$2-78,8#;7<54!$2-60,8++$25$28#20!+$25$28#18,8#!+$25$28#10,1$35!+$25$28#8,8$27!+$25$28#,4$26!$2-58,8+$28@#20$2:!$2-68,8+$25$28!$2-70,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8+$24$25'$24#1000#7?????????>0&$24#10'$25#20#8000&$25#20'$2:#2#800'$22#698000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#698000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8'$34#698000#7???????????)##7???7000#100000001000$34##1!$34#,1$35)$2-1000#1000$34##1&$34#8!&6$34#3#7???8000,1#1)$21##18$22##4)$21##18$23##8)$21##18$34##1'$26##7???????'$27#^#?#???????????????'$35##??'$28#1000#7?????????<0&$28#10(+$28$25##20#&6+$28$25#3#7???8000#4)##7???7000#100000001000+$28$25##20'+$28$25#1000#7?????????>0)$2-1000#1000+$28$25##20)$21##18+$28$25##20)$22##4+$28$25##20)$23##8+$28$25##20)$34##1+$28$25##20)##10000#688000+$28$25##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-50,8$21,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 508928 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ee7ce7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 729692 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ee7ce7.IT BndT_Ea_001.SegItab_Ea_ee7ce7.IT_sound BF NX0 BR XSTEP F0 PSS plan 729692 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aesG.

Module LibSegEa_aesH.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ee7ce7.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ee7ce7.IT.
Definition ENDS : list Z := [493080].
Definition STOPS1 : list Z := [493080] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-70$21$:$;$<$=$>$?$10$11$21#7???8000$22$25+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",36'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8+$24$25'$24#1000#7?????????>0&$24#10'$25#20#8000&$25#20'$2:#2#800'$28#1000#7?????????<0&$28#10(+$28$25##20#&6+$28$25#3#7???8000#4)##7???7000#100000001000+$28$25##20'+$28$25#1000#7?????????>0)$2-1000#1000+$28$25##20)$21##18+$28$25##20)$22##4+$28$25##20)$23##8+$28$25##20)$34##1+$28$25##20)##10000#688000+$28$25##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-78,8#;7<54!$2-80,8+$21#8!$2-88,8$34!$2-90,8$21!$2-98,8$23!$2-70,8$28!$2-68,8+$28$25!$2-60,8++$28$25#20!$2-58,8+$28@#20$2:!$2-50,8$21!$2-:8,8#;2014!$2-;0,8+$2-70"%pstring).
Definition ss0 : sym_state := SS 696400 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78618#78618#5=#78618,20##;2068+$2-:0$3$4$5$6$7+$2-70$21$28$24$25$=$>$?$10$11$28#7???8000$22$25+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?,,36'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8+$24$25'$24#1000#7?????????>0&$24#10'$25#20#8000&$25#20'$2:#2#800'$28#1000#7?????????<0&$28#10(+$28$25##20#&6+$28$25#3#7???8000#4)##7???7000#100000001000+$28$25##20'+$28$25#1000#7?????????>0)$2-1000#1000+$28$25##20)$21##18+$28$25##20)$22##4+$28$25##20)$23##8+$28$25##20)$34##1+$28$25##20)##10000#688000+$28$25##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-78,8#;7<54!$2-80,8+$21#8!$2-88,8$34!$2-90,8$21!$2-98,8$23!$2-70,8$28!$2-68,8+$28$25!$2-60,8++$28$25#20!$2-58,8+$28@#20$2:!$2-50,8$21!$2-:8,8#;2014!$2-;0,8+$2-70,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 493080 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ee7ce7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 696400 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ee7ce7.IT BndT_Ea_001.SegItab_Ea_ee7ce7.IT_sound BF NX0 BR XSTEP F0 PSS plan 696400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aesH.

Module LibSegEa_aesI0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ee7ce7.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ee7ce7.IT.
Definition ENDS : list Z := [508928].
Definition STOPS1 : list Z := [508928] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-70$21$:$;$<$=$>$?$10$11$28#7???8000$22#20+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18!$21#,8$24!$21#8,8+$24#20!$21#10,8+$24#20'$24#1000#7?????????>0&$24#10'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-78,8#;7<54!$2-80,8+$21#8!$2-88,8$34!$2-90,8$21!$2-98,8$23!$2-70,8$28!$2-68,8+$28#20!$2-60,8+$28#40!$2-58,8+$28#40!$2-50,8$21"%pstring).
Definition ss0 : sym_state := SS 729192 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<400#7<400#5=#7<400,20##;22=4+$2-80$3$4$5$6$7+$21#8$34$28+$28#40+$28#40+$28#40&6+$21#10#3$?$10$11$21$23$22#20+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?,,28!$2-80,8+$21#8!$2-78,8#;7<54!$2-70,8$24!$2-58,8+$24#20!$21#10,8+$28#40!$2-60,8$24!$21#8,8+$28#40!$2-68,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18'$24#1000#7?????????>0&$24#10'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-88,8$34!$2-90,8$21!$2-98,8$23!$2-50,8$21,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 508928 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ee7ce7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 729192 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ee7ce7.IT BndT_Ea_001.SegItab_Ea_ee7ce7.IT_sound BF NX0 BR XSTEP F0 PSS plan 729192 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aesI0.

Module LibSegEa_aesI1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ee7ce7.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ee7ce7.IT.
Definition ENDS : list Z := [508928].
Definition STOPS1 : list Z := [508928] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-70$21$:$;$<$=$>$?$10$11$28#7???8000$22#40+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18!$21#,8$24!$21#8,8+$24#40!$21#10,8+$24#40'$24#1000#7?????????>0&$24#10'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-78,8#;7<54!$2-80,8+$21#8!$2-88,8$34!$2-90,8$21!$2-98,8$23!$2-70,8$28!$2-68,8+$28#40!$2-60,8+$28#60!$2-58,8+$28#80!$2-50,8$21"%pstring).
Definition ss0 : sym_state := SS 729192 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<400#7<400#5=#7<400,20##;22=4+$2-80$3$4$5$6$7+$21#8$34$28+$28#80+$28#80+$28#60&6+$21#10#3$?$10$11$21$23$22#40+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?,,28!$2-80,8+$21#8!$2-78,8#;7<54!$2-70,8$24!$2-58,8+$24#40!$21#10,8+$28#80!$2-60,8$24!$21#8,8+$28#60!$2-68,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18'$24#1000#7?????????>0&$24#10'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-88,8$34!$2-90,8$21!$2-98,8$23!$2-50,8$21,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 508928 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ee7ce7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 729192 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ee7ce7.IT BndT_Ea_001.SegItab_Ea_ee7ce7.IT_sound BF NX0 BR XSTEP F0 PSS plan 729192 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aesI1.

Module LibSegEa_aesI10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_ee7ce7.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_ee7ce7.IT.
Definition ENDS : list Z := [508928].
Definition STOPS1 : list Z := [508928] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-70$21$:$;$<$=$>$?$10$11$28#7???8000$22#8000+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18!$21#,8$24!$21#8,8+$24#8000!$21#10,8+$24#8000'$24#1000#7?????????>0&$24#10'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-78,8#;7<54!$2-80,8+$21#8!$2-88,8$34!$2-90,8$21!$2-98,8$23!$2-70,8$28!$2-68,8+$28#8000!$2-60,8+$28#8020!$2-58,8+$28#10000!$2-50,8$21"%pstring).
Definition ss0 : sym_state := SS 729192 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<400#7<400#5=#7<400,20##;22=4+$2-80$3$4$5$6$7+$21#8$34$28+$28#10000+$28#10000+$28#8020&6+$21#10#3$?$10$11$21$23$22#8000+&6+$21#8#3#7???8000#7???8000$18$19$1:$1;$1<$1=$1>$1?,,28!$2-80,8+$21#8!$2-78,8#;7<54!$2-70,8$24!$2-58,8+$24#8000!$21#10,8+$28#10000!$2-60,8$24!$21#8,8+$28#8020!$2-68,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18($21##18'$24#1000#7?????????>0&$24#10'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-88,8$34!$2-90,8$21!$2-98,8$23!$2-50,8$21,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 508928 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_ee7ce7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 729192 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_ee7ce7.IT BndT_Ea_001.SegItab_Ea_ee7ce7.IT_sound BF NX0 BR XSTEP F0 PSS plan 729192 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aesI10.
