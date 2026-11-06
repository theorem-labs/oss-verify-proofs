(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ea0PlanKit Ea0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndT_Ea_001S8.

Module LibSegEa_alpK9e.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [730656].
Definition STOPS1 : list Z := [730656] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100$:$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",49%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$26#,4$38'$38#1#40"%pstring).
Definition ss0 : sym_state := SS 732200 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;2620#;2620#5=#;2620,20#$1+$2-100$3$4$5$6$7$2+$2-100$38$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,49%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$26#,4$38'$38#1#40,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 730656 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 732200 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 732200 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpK9e.

Module LibSegEa_alpM0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [730912].
Definition STOPS1 : list Z := [730912] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100$:$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",48%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#9,1#"%pstring).
Definition ss0 : sym_state := SS 732112 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;2720#;2720#5=#;2720,20#$1+$2-100$3$4$5$6$7$2+$2-100#$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,48%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#9,1#,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 730912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 732112 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 732112 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpM0.

Module LibSegEa_alpMd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [730656].
Definition STOPS1 : list Z := [730656] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100$:$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",48%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#9,1#1"%pstring).
Definition ss0 : sym_state := SS 732112 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;2620#;2620#5=#;2620,20#$1+$2-100$3$4$5$6$7$2+$2-100#1$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,48%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#9,1#1,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 730656 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 732112 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 732112 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpMd.

Module LibSegEa_alpN0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [730912].
Definition STOPS1 : list Z := [730912] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100$:$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",48%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#9,1#"%pstring).
Definition ss0 : sym_state := SS 731612 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;2720#;2720#5=#;2720,20#$1+$2-100$3$4$5$6$7$2+$2-100#$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,48%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#9,1#,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 730912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 731612 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 731612 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpN0.

Module LibSegEa_alpNd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [730656].
Definition STOPS1 : list Z := [730656] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100$:$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",48%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#9,1#1"%pstring).
Definition ss0 : sym_state := SS 731612 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;2620#;2620#5=#;2620,20#$1+$2-100$3$4$5$6$7$2+$2-100#1$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,48%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#9,1#1,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 730656 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 731612 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 731612 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpNd.

Module LibSegEa_alpP3c.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [740596].
Definition STOPS1 : list Z := [740596] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100#5=$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?"%pstring).
Definition ss0 : sym_state := SS 731380 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4<?4#;4<?4#5=#;4<?4,20##;2914+$2-100$3$4$5$6$7$2+$2-100+$24#18#1$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,47%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 740596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 731380 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 731380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpP3c.

Module LibSegEa_alpP3e.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [713488].
Definition STOPS1 : list Z := [713488] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100#100$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?"%pstring).
Definition ss0 : sym_state := SS 731380 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>310#:>310#5=#:>310,20##;2>58+$2-100$3$4$5$6$7$2+$2-100$26#1$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,47%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?,48!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 731380 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 731380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpP3e.

Module LibSegEa_alpP3h.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [734436].
Definition STOPS1 : list Z := [734436] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100$37$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",59%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#3!$22#18,8$27'$27##??????'$37#5>#??"%pstring).
Definition ss0 : sym_state := SS 731380 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 34), (24), ELit 8)].
Definition F0L : list SR.region := [((EVar 34), (24), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;34>4#;34>4#5=#;34>4,20##;2<;<+$2-100$3$4$5$6$7$2+$2-100$24$25$26$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,59!$22#18,8+$27#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#3'$27##??????'$37#5>#??,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 734436 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 731380 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 731380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpP3h.

Module LibSegEa_alpP3hx.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [713488].
Definition STOPS1 : list Z := [713488] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100$37$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",58%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#3!$22#18,8#1000000'$37#5>#??"%pstring).
Definition ss0 : sym_state := SS 731380 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 34), (24), ELit 8)].
Definition F0L : list SR.region := [((EVar 34), (24), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>310#:>310#5=#:>310,20##;2>58+$2-100$3$4$5$6$7$2+$2-100$26#=#1000001$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,58!$22#18,8#1000001%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#3'$37#5>#??,48!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 731380 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 731380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpP3hx.

Module LibSegEa_alpP3l.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [734436].
Definition STOPS1 : list Z := [734436] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100$37$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",59%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#3!$22#18,8$27'$27##??????'$37##5<"%pstring).
Definition ss0 : sym_state := SS 731380 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 34), (24), ELit 8)].
Definition F0L : list SR.region := [((EVar 34), (24), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;34>4#;34>4#5=#;34>4,20##;2<;<+$2-100$3$4$5$6$7$2+$2-100$24$25$26$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,59!$22#18,8+$27#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#3'$27##??????'$37##5<,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 734436 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 731380 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 731380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpP3l.

Module LibSegEa_alpP3lx.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [713488].
Definition STOPS1 : list Z := [713488] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100$37$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",58%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#3!$22#18,8#1000000'$37##5<"%pstring).
Definition ss0 : sym_state := SS 731380 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 34), (24), ELit 8)].
Definition F0L : list SR.region := [((EVar 34), (24), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>310#:>310#5=#:>310,20##;2>58+$2-100$3$4$5$6$7$2+$2-100$26#=#1000001$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,58!$22#18,8#1000001%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#3'$37##5<,48!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 731380 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 731380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpP3lx.

Module LibSegEa_alpP9c.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [740596].
Definition STOPS1 : list Z := [740596] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100#7=$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?"%pstring).
Definition ss0 : sym_state := SS 731192 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4<?4#;4<?4#5=#;4<?4,20##;2858+$2-100$3$4$5$6$7$2+$2-100+$24#18#1$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,47%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 740596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 731192 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 731192 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpP9c.

Module LibSegEa_alpP9e.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [713488].
Definition STOPS1 : list Z := [713488] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100#100$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?"%pstring).
Definition ss0 : sym_state := SS 731192 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>310#:>310#5=#:>310,20##;2>58+$2-100$3$4$5$6$7$2+$2-100$26#1$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,47%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?,48!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 731192 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 731192 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpP9e.

Module LibSegEa_alpP9h.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [741136].
Definition STOPS1 : list Z := [741136] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100$37$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",59%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#9!$22#18,8$27'$27##??????'$37#7>#??"%pstring).
Definition ss0 : sym_state := SS 731192 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 34), (24), ELit 8)].
Definition F0L : list SR.region := [((EVar 34), (24), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4?10#;4?10#5=#;4?10,20##;2<28+$2-100$3$4$5$6$7$2+$2-100$24$25$26$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,59!$22#18,8+$27#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#9'$27##??????'$37#7>#??,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 741136 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 731192 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 731192 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpP9h.
