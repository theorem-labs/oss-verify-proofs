(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ea0PlanKit Ea0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndT_Ea_001S8 BndT_Ea_000S8.

Module LibSegEa_alpP9hx.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",58%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#9!$22#18,8#1000000'$37#7>#??"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>310#:>310#5=#:>310,20##;2>58+$2-100$3$4$5$6$7$2+$2-100$26#=#1000001$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,58!$22#18,8#1000001%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#9'$37#7>#??,48!"%pstring).
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
End LibSegEa_alpP9hx.

Module LibSegEa_alpP9l.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",59%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#9!$22#18,8$27'$27##??????'$37##7<"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4?10#;4?10#5=#;4?10,20##;2<28+$2-100$3$4$5$6$7$2+$2-100$24$25$26$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,59!$22#18,8+$27#1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#9'$27##??????'$37##7<,48!"%pstring).
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
End LibSegEa_alpP9l.

Module LibSegEa_alpP9lx.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",58%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#9!$22#18,8#1000000'$37##7<"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>310#:>310#5=#:>310,20##;2>58+$2-100$3$4$5$6$7$2+$2-100$26#=#1000001$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,58!$22#18,8#1000001%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$24#148,8#1000000'$22#1000#7?????????<0)$22##20##10000#688000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-100#100$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#9'$37##7<,48!"%pstring).
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
End LibSegEa_alpP9lx.

Module LibSegEa_alpR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001S8.SegItab_Ea_f9ff03.ITR.
Definition IT : itab := BndT_Ea_001S8.SegItab_Ea_f9ff03.IT.
Definition ENDS : list Z := [732744].
Definition STOPS1 : list Z := [732744] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$2+$2-100$:$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",54%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<"%pstring).
Definition ss0 : sym_state := SS 730656 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 47), (0), ELit 8); ((EVar 48), (0), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16)].
Definition F0L : list SR.region := [((EVar 47), (0), 8); ((EVar 48), (0), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;2>48#;2>48#5=#;2>48,20#$40$2$3$4$5$6$7$41$42$30$2?$<$=$>$?$10$11$43$44$45$46$47$48$49$4:$4;$4<$1<$1=$1>$1?,,63!$30#,1#!&6$2?#3#7???800;,1^#?#??????????????5!&6$2?#3#7???800:,1^#?#??????????????5!&6$2?#3#7???8009,1^#?#??????????????5!&6$2?#3#7???8008,1^#?#??????????????5!&6$2?#3#7???800?,1^#?#??????????????5!&6$2?#3#7???800>,1^#?#??????????????5!&6$2?#3#7???800=,1^#?#??????????????5!&6$2?#3#7???800<,1^#?#??????????????5!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?#8#78($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 732744 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 730656 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 730656 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpR.

Module LibSegEa_alpZ.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?"%pstring).
Definition ss0 : sym_state := SS 732760 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;2620#;2620#5=#;2620,20#$1+$2-100$3$4$5$6$7$2+$2-100#$;$<$=$>$?$10$11+&6+$24#170#3#7???8000$26#23050$24#7???8000+$24#8+$24#9+$24#170+&6+$24#9#3#7???8000+&6$2?#3#7???8000$1<$1=$1>$1?,,48!$24#8,1#%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801100#800000000000&$2#20($2-100#100'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-100#100$24##180'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-100#100$25##8'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-100#100$26##10!$25#,8#1335?0###8001>6;>#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#698000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-100#100$2?##80)$2-100#100$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#124060)&6$2?#3#7???8000#10##8001>6;>#10!$2-?8,8+$2?#20!$2-?0,8#3!$2->8,8#1!$2->0,8#!$2-=8,8+&6+$24#148#3#7???8000!$2-=0,8+$24#148!$2-<8,8+&6$25#3#7???8000!$2-<0,8+&6+$24#168#3#7???8000!$2-;8,8+$24#168!$2-;0,8$2?!$2-:8,8+$24#18!$2-:0,8$2?!$2-98,8+&6$26#3#7???8000!$2-90,8$25!$2-88,8+&6+$24#8#3#7???8000!$2-70,8$2?,48!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001S8.SegItab_Ea_f9ff03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 732760 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001S8.SegItab_Ea_f9ff03.IT BndT_Ea_001S8.SegItab_Ea_f9ff03.IT_sound BF NX0 BR XSTEP F0 PSS plan 732760 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_alpZ.

Module LibSegEa_apDL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_583ad2.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_583ad2.IT.
Definition ENDS : list Z := [871008].
Definition STOPS1 : list Z := [871008] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$2:$14$15$16$25$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487248 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-80)) (ELit 80);
   KRange (EVar 37) 25 134217728;
   KRange (EVar 42) 4096 140737488355328].
Definition ss0 : sym_state := SS 880644 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=4:60#=4:60#5=#=4:60,20##=7018+$2-50$3$4$5$6$7$8$9$2:+$25#1$<$=$>$?$10$11$12$2:$14$15$16$25$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?801050#800000000000&$2#10($2-50#50'$25#19#8000000'$2:#1000#800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 871008 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_583ad2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 880644 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_583ad2.IT BndT_Ea_000S8.SegItab_Ea_583ad2.IT_sound BF NX0 BR XSTEP F0 PSS plan 880644 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_apDL.

Module LibSegEa_apDS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_583ad2.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_583ad2.IT.
Definition ENDS : list Z := [493068].
Definition STOPS1 : list Z := [493068] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$:$2;$29$;$<$=$>$?$10$11$22$13$29$28$26#16$38$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18'$22##16'$29#1000#800000000000'$28#30#8000000"%pstring).
Definition ss0 : sym_state := SS 880644 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 10), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7860<#7860<#5=#7860<,20##=703<+$2-50$3$4$5$6$7$:$2;+$22$29$38$2;$=$>$?$10$11$22$13$29$28$26#16$38$19$1:$1;$1<$1=$1>$1?,,=!$:#10,8$29!$:#8,8$22!$:#,8+@#2&6$28#1#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18'$22##16'$29#1000#800000000000'$28#30#8000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 493068 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_583ad2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 880644 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_583ad2.IT BndT_Ea_000S8.SegItab_Ea_583ad2.IT_sound BF NX0 BR XSTEP F0 PSS plan 880644 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_apDS.

Module LibSegEa_apF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_583ad2.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_583ad2.IT.
Definition ENDS : list Z := [493068].
Definition STOPS1 : list Z := [493068] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$:$2;$37$;$<$=$>$?$10$11$22$13$29$28$26$17$38$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18'$22##8000000'$29#1000#800000000000'$28#30#8000000"%pstring).
Definition ss0 : sym_state := SS 880664 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 10), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7860<#7860<#5=#7860<,20##=703<+$2-50$3$4$5$6$7$:$2;+$22$29$38$2;$=$>$?$10$11$22$13$29$28$26$17$38$19$1:$1;$1<$1=$1>$1?,,=!$:#10,8$29!$:#8,8$22!$:#,8+@#2&6$28#1#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18'$22##8000000'$29#1000#800000000000'$28#30#8000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 493068 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_583ad2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 880664 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_583ad2.IT BndT_Ea_000S8.SegItab_Ea_583ad2.IT_sound BF NX0 BR XSTEP F0 PSS plan 880664 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_apF.

Module LibSegEa_apN.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_583ad2.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_583ad2.IT.
Definition ENDS : list Z := [493072; 880644].
Definition STOPS1 : list Z := [493072; 880644] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$8$9$29$;$<$=$>$?$10$11$22$2:$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487248 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-80)) (ELit 80);
   KRange (EVar 34) 0 134217728;
   KRange (EVar 41) 4096 140737488355328;
   KRange (EVar 42) 4096 140737488355328].
Definition ss0 : sym_state := SS 880620 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#78610#=7004#78610#=7004#5;#=6??0,20#$1+$2-50$3$4$5$6$7$8$9$29$;$<$=$>$?$10$11$22$2:$29$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6'$2#7???7?801050#800000000000&$2#10($2-50#50'$22##8000000'$29#1000#800000000000'$2:#1000#800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#78610#=7004#78610#=7004#5:#=7004,20#$1+$2-50$3$4$5$6$7$8$9$29$;$<$=$>$?$10$11$22$2:$29$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7'&4&1$22##1#1#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$22##8000000'$29#1000#800000000000'$2:#1000#800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#78610#=7004#78610#=7004#5=#78610,20##=7004+$2-50$3$4$5$6$7$8$9$29$2:$22$=$>$?$10$11$22$2:$29$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7'&4&1$22##1##'$2#7???7?801050#800000000000&$2#10($2-50#50'$22##8000000'$29#1000#800000000000'$2:#1000#800000000000,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 493072 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 880644 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_583ad2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 880620 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_583ad2.IT BndT_Ea_000S8.SegItab_Ea_583ad2.IT_sound BF NX0 BR XSTEP F0 PSS plan 880620 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_apN.

Module LibSegEa_apcapMS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_583ad2.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_583ad2.IT.
Definition ENDS : list Z := [880784].
Definition STOPS1 : list Z := [880784] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$:$9$36$;$<$=$>$?$10$11$12$13+$:#1$15$26$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34!$2-50,8$35!$:#,1$21'$21##??'&9$21#1##'$26#1#16"%pstring).
Definition ss0 : sym_state := SS 880700 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (0), ELit 1); ((EAlu Instr.ALU_ADD (EVar 10) (EVar 38)), (1), ELit 1)].
Definition F0L : list SR.region := [((EVar 10), (0), 1); ((EAlu Instr.ALU_ADD (EVar 10) (EVar 38)), (1), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=7090#=7090#5=#=7090,20#$2<$2$3$4$5$6$7$2=$2>$:$;$<$=$>$?$10$11$2?$30$31$32$33$34$35$19$1:$1;$1<$1=$1>$1?,,16!+$:$26#1,1#!$:#,1@#2$26'$2#7???7?801050#800000000000&$2#10($2-50#50'$:#698000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34!$2-50,8$35'$21##??'&9$21#1##'$26#1#16,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 880784 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_583ad2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 880700 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_583ad2.IT BndT_Ea_000S8.SegItab_Ea_583ad2.IT_sound BF NX0 BR XSTEP F0 PSS plan 880700 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_apcapMS.

Module LibSegEa_apkA0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_568966.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_568966.IT.
Definition ENDS : list Z := [743624].
Definition STOPS1 : list Z := [743624] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#,$24#100#8"%pstring).
Definition ss0 : sym_state := SS 740304 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;58<8#;58<8#5=#;58<8,20##;4<5<+$2-30$3$4$5$6$7+$24#118+$24#120$24$22#4000#$>$?$10$11#7???8000+&6+$24#120#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$24#118,8$22!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#120,8#,$24#100#8,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 743624 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_568966.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 740304 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_568966.IT BndT_Ea_000S8.SegItab_Ea_568966.IT_sound BF NX0 BR XSTEP F0 PSS plan 740304 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_apkA0.

Module LibSegEa_apkA1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_568966.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_568966.IT.
Definition ENDS : list Z := [740496].
Definition STOPS1 : list Z := [740496] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8$21,$24#100#8'$21#1#4000'$23#1000#7???????<000,$23##1)##7???7000#100000001000$23##1#&6$23#3#7???8000#1)$2-30#30$23##1)$24##128$23##1"%pstring).
Definition ss0 : sym_state := SS 740304 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4<90#;4<90#5=#;4<90,20#$1+$2-30$3$4$5$6$7+$24#118+$24#120$23#$<$=$>$?$10$11#7???8000+&6+$24#120#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8$21,$24#100#8'$21#1#4000'$23#1000#7???????<000,$23##1)##7???7000#100000001000$23##1#&6$23#3#7???8000#1)$2-30#30$23##1)$24##128$23##1,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 740496 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_568966.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 740304 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_568966.IT BndT_Ea_000S8.SegItab_Ea_568966.IT_sound BF NX0 BR XSTEP F0 PSS plan 740304 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_apkA1.

Module LibSegEa_apkB0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_568966.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_568966.IT.
Definition ENDS : list Z := [740524].
Definition STOPS1 : list Z := [740524] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7+$24#118+$24#120#$;$<$=$>$?$10$11#7???8000+&6+$24#120#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$22!$24#120,8#,$24#100#8!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<"%pstring).
Definition ss0 : sym_state := SS 740444 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4<:<#;4<:<#5=#;4<:<,20#$28$2$3$4$5$6$7$29$2:#100#$<$=$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$24#120,8#%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$22,$24#100#8!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 740524 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_568966.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 740444 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_568966.IT BndT_Ea_000S8.SegItab_Ea_568966.IT_sound BF NX0 BR XSTEP F0 PSS plan 740444 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_apkB0.

Module LibSegEa_apkB1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_568966.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_568966.IT.
Definition ENDS : list Z := [740496].
Definition STOPS1 : list Z := [740496] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7+$24#118+$24#120$21$;$<$=$>$?$10$11#7???8000+&6+$24#120#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1=%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$22!$24#120,8#,$24#100#8'$21#1#4000'$22#1000#7???????<000,$22##1)##7???7000#100000001000$22##1#&6$22#3#7???8000#1)$2-30#30$22##1)$24##128$22##1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<"%pstring).
Definition ss0 : sym_state := SS 740444 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;4<90#;4<90#5=#;4<90,20#$1+$2-30$3$4$5$6$7+$24#118+$24#120$22#$<$=$>$?$10$11#7???8000+&6+$24#120#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$24#120,8$21%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$22,$24#100#8'$21#1#4000'$22#1000#7???????<000,$22##1)##7???7000#100000001000$22##1#&6$22#3#7???8000#1)$2-30#30$22##1)$24##128$22##1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 740496 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_568966.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 740444 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_568966.IT BndT_Ea_000S8.SegItab_Ea_568966.IT_sound BF NX0 BR XSTEP F0 PSS plan 740444 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_apkB1.
