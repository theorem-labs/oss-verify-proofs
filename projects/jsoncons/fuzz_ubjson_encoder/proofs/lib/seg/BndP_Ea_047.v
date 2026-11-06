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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Ea_001.

Module LibSegEa_arvZH3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [738448].
Definition STOPS1 : list Z := [738448] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25+$24#8+$24#10$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 739244 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (36), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (37), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (36), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (37), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4490#;4490#5=#;4490,20#$1+$2-80$3$4$5$6$7$2+$2-80+$24#8#1$<#$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25+$24#8+$24#10$19#7???8000$2?$1<$1=$1>$1?,,2=!$24#8,1#1!&6$2?#3#7???8025,1^#?#??????????????8!&6$2?#3#7???8024,1^#?#??????????????8%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 738448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 739244 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 739244 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvZH3.

Module LibSegEa_arvZI.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [738448].
Definition STOPS1 : list Z := [738448] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 737208 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (8), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (8), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4490#;4490#5=#;4490,20#$1+$2-80$3$4$5$6$7$2+$2-80^#?#??????????????8#1#$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?,,2<!&6$2?#3#7???8008,1^#?#??????????????8!$24#8,1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 738448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 737208 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 737208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvZI.

Module LibSegEa_arvZL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [738448].
Definition STOPS1 : list Z := [738448] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 737476 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (12), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (12), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4490#;4490#5=#;4490,20#$1+$2-80$3$4$5$6$7$2+$2-80^#?#??????????????8#1#$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?,,2<!&6$2?#3#7???800<,1^#?#??????????????8!$24#8,1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 738448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 737476 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 737476 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvZL.

Module LibSegEa_arvZS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [738448].
Definition STOPS1 : list Z := [738448] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 739564 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (28), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (29), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (28), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (29), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4490#;4490#5=#;4490,20#$1+$2-80$3$4$5$6$7$2+$2-80+$24#8#1#$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?,,2=!$24#8,1#1!&6$2?#3#7???801=,1^#?#??????????????8!&6$2?#3#7???801<,1^#?#??????????????8%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 738448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 739564 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 739564 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvZS.

Module LibSegEa_arvZT.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [738448].
Definition STOPS1 : list Z := [738448] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 737032 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4490#;4490#5=#;4490,20#$1+$2-80$3$4$5$6$7$2+$2-80+$24#8#1#$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?,,17!$24#8,1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10!$24#10,1#,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 738448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 737032 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 737032 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvZT.

Module LibSegEa_arvZU.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [738448].
Definition STOPS1 : list Z := [738448] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 737936 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (6), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (6), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4490#;4490#5=#;4490,20#$1+$2-80$3$4$5$6$7$2+$2-80^#?#??????????????8#1#$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?,,2<!&6$2?#3#7???8006,1^#?#??????????????8!$24#8,1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 738448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 737936 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 737936 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvZU.

Module LibSegEa_arvZZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [738448].
Definition STOPS1 : list Z := [738448] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 736908 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4490#;4490#5=#;4490,20#$1+$2-80$3$4$5$6$7$2+$2-80+$24#8#1#$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?,,17!$24#8,1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10!$24#10,1#,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 738448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 736908 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 736908 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvZZ.

Module LibSegEa_arvZd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [738448].
Definition STOPS1 : list Z := [738448] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 738156 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (16), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (16), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4490#;4490#5=#;4490,20#$1+$2-80$3$4$5$6$7$2+$2-80^#?#??????????????8#1#$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?,,2<!&6$2?#3#7???8010,1^#?#??????????????8!$24#8,1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 738448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 738156 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 738156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvZd.

Module LibSegEa_arvZi.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [738448].
Definition STOPS1 : list Z := [738448] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 736264 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (4), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (4), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4490#;4490#5=#;4490,20#$1+$2-80$3$4$5$6$7$2+$2-80^#?#??????????????8#1#$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?,,2<!&6$2?#3#7???8004,1^#?#??????????????8!$24#8,1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 738448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 736264 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 736264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvZi.

Module LibSegEa_arvZl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [738448].
Definition STOPS1 : list Z := [738448] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 738368 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (10), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (10), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4490#;4490#5=#;4490,20#$1+$2-80$3$4$5$6$7$2+$2-80^#?#??????????????8#1#$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25$17$18$19#7???8000$2?$1<$1=$1>$1?,,2<!&6$2?#3#7???800:,1^#?#??????????????8!$24#8,1#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000!$24#10,1#,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 738448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 738368 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 738368 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvZl.

Module LibSegEa_arviN.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [713488].
Definition STOPS1 : list Z := [713488] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$23$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25+$2?#20#1$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$23##"%pstring).
Definition ss0 : sym_state := SS 736184 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>310#:>310#5=#:>310,20##;4700+$2-80$3$4$5$6$7$2+$2-80$26#1$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25+$2?#20#1$19#7???8000$2?$1<$1=$1>$1?,,16%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$23##,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 713488 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 736184 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 736184 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arviN.

Module LibSegEa_arviV.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [701788].
Definition STOPS1 : list Z := [701788] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80#1$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25+$2?#20#1$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",38%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-80#80$25##8!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$2?##200$25##8)$30##1$25##8)&6$2?#3#7???8000#40&6$25#3#7???8000#1)&6$2?#3#7???8000#40##8001>6;>#10!$2?#20,8$32"%pstring).
Definition ss0 : sym_state := SS 736184 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:;55<#:;55<#5=#:;55<,20##;3<08+$2-80$3$4$5$6$7$2+$2-80$25],,1$32#$24$26#:;55<$10$11+&6$2?#3#7???8000$2?$24$26$25+$2?#20#1$19#7???8000$2?$1<$1=$1>$1?,,38%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-80#80$25##8!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$2?##200$25##8)$30##1$25##8)&6$2?#3#7???8000#40&6$25#3#7???8000#1)&6$2?#3#7???8000#40##8001>6;>#10!$2?#20,8$32,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 701788 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 736184 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 736184 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arviV.

Module LibSegEa_arvlN.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [713488].
Definition STOPS1 : list Z := [713488] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$23$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25+$2?#50#4$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$23##3"%pstring).
Definition ss0 : sym_state := SS 738252 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>310#:>310#5=#:>310,20##;46=0+$2-80$3$4$5$6$7$2+$2-80$26#1$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25+$2?#50#4$19#7???8000$2?$1<$1=$1>$1?,,16%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$23##3,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 713488 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 738252 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 738252 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvlN.

Module LibSegEa_arvlV.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_fccf9e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_fccf9e.IT.
Definition ENDS : list Z := [701788].
Definition STOPS1 : list Z := [701788] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80#4$;$<$=$>$?$10$11+&6$2?#3#7???8000$2?$24$26$25+$2?#50#4$19#7???8000$2?$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",38%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-80#80$25##8!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$2?##200$25##8)$30##1$25##8)&6$2?#3#7???8000#40&6$25#3#7???8000#1)&6$2?#3#7???8000#40##8001>6;>#10!$2?#50,8$32"%pstring).
Definition ss0 : sym_state := SS 738252 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:;55<#:;55<#5=#:;55<,20##;4440+$2-80$3$4$5$6$7$2+$2-80$25&8&8%2],,4$32#18@#100&9],,4$32#??00&8&9&6],,4$32#8#??00%6],,4$32#18#$24$26#:;55<$10$11+&6$2?#3#7???8000$2?$24$26$25+$2?#50#4$19#7???8000$2?$1<$1=$1>$1?,,38%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-80#80$26##10)$24##180$26##10'$2?#698000#7????????>00&$2?#20,$2?##200($2?##200)##7???7000#100000001000$2?##200(&6$2?#3#7???8000#40!$2?#1?8,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##200$30##1)$2-80#80$2?##200)$2-80#80$30##1)$24##180$2?##200)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#40)$26##10$2?##200)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#40)$2?##200##10000#12:000'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-80#80$25##8!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$2?##200$25##8)$30##1$25##8)&6$2?#3#7???8000#40&6$25#3#7???8000#1)&6$2?#3#7???8000#40##8001>6;>#10!$2?#50,8$32,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
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
Definition ps0 : SR.post_spec := SR.PS 701788 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_fccf9e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 738252 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_fccf9e.IT BndT_Ea_001.SegItab_Ea_fccf9e.IT_sound BF NX0 BR XSTEP F0 PSS plan 738252 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_arvlV.
