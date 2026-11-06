(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ea0PlanKit Ea0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.seg Require BndT_Ea_000S8.

Module LibSegEa_aboT3l.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [713488].
Definition STOPS1 : list Z := [713488] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$27$;$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",35%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060'$27##22"%pstring).
Definition ss0 : sym_state := SS 749872 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>310#:>310#5=#:>310,20##;72?4+$2-80$3$4$5$6$7$2+$2-80$26#3$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#3$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,35%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060'$27##22,48!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 749872 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 749872 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboT3l.

Module LibSegEa_aboT3u.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [713488].
Definition STOPS1 : list Z := [713488] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$27$;$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",35%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060'$27#24#??"%pstring).
Definition ss0 : sym_state := SS 749872 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>310#:>310#5=#:>310,20##;72?4+$2-80$3$4$5$6$7$2+$2-80$26#3$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#3$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,35%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060'$27#24#??,48!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 749872 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 749872 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboT3u.

Module LibSegEa_aboT4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [745220].
Definition STOPS1 : list Z := [745220] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",34%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060"%pstring).
Definition ss0 : sym_state := SS 749904 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;5?04#;5?04#5=#;5?04,20##;715<+$2-80$3$4$5$6$7$2+$2-80$24$26$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,34%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 745220 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 749904 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 749904 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboT4.

Module LibSegEa_aboTT.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [702952].
Definition STOPS1 : list Z := [702952] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$25#,8#1335?0###8001>6<6#1###8001>6<7#1!$24#10,1#!$2-70,8$32'$32##1000000"%pstring).
Definition ss0 : sym_state := SS 750696 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:;9>8#:;9>8#5=#:;9>8,20##;74:<+$2-80$3$4$5$6$7$2+$2-80$25$32#$24$26#:;9>8$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3:%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$25#,8#1335?0###8001>6<6#1###8001>6<7#1!$24#10,1#!$2-70,8$32'$32##1000000,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 702952 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 750696 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 750696 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboTT.

Module LibSegEa_aboTTr.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [750664].
Definition STOPS1 : list Z := [750664] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45!$25#,8#1335?0###8001>6<6#1###8001>6<7#1!$24#10,1#!$2-70,8$32'$32##1000000"%pstring).
Definition ss0 : sym_state := SS 750764 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EVar 47), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 8); ((EVar 48), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EVar 47), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 8); ((EVar 48), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;7448#;7448#5=#;7448,20#$39$2$3$4$5$6$7$3:$3;$30#1#$=$>$?$10$11$3<$3=$3>$3?$40$41$42$43$44$45$1<$1=$1>$1?,,4?!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45!$25#,8#1335?0###8001>6<6#1###8001>6<7#1!$24#10,1#!$2-70,8$32'$32##1000000,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 750664 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 750764 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 750764 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboTTr.

Module LibSegEa_aboTe.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [750664].
Definition STOPS1 : list Z := [750664] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$32$;$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",43%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45!$26#,4$31'$31#1#40"%pstring).
Definition ss0 : sym_state := SS 749916 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 8); ((EVar 47), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 8); ((EVar 48), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-112), 8); ((EVar 47), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 8); ((EVar 48), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;7448#;7448#5=#;7448,20#$39$2$3$4$5$6$7$3:$3;$30$31$<$=$>$?$10$11$3<$3=$3>$3?$40$41$42$43$44$45$1<$1=$1>$1?,,4;!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$2-70,8$32'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45!$26#,4$31'$31#1#40,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 750664 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 749916 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 749916 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboTe.

Module LibSegEa_aboTf.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [752120].
Definition STOPS1 : list Z := [752120] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$32$;$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",37%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$26#,4#!$24#148,8#1000000'$32##1000000"%pstring).
Definition ss0 : sym_state := SS 749916 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-116), ELit 12)].
Definition F0L : list SR.region := [((EVar 2), (-116), 12)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;79?8#;79?8#5=#;79?8,20##;7468+$2-80$3$4$5$6$7$2+$2-80+$24#168+$2-74+$2-70+$2?#20$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,39!$2-74,4#7!$2-70,8$32%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$26#,4#!$24#148,8#1000000'$32##1000000,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 752120 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 749916 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 749916 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboTf.

Module LibSegEa_aboTx.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [713488].
Definition STOPS1 : list Z := [713488] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$32$;$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",37%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$26#,4#!$24#148,8#1000000'$32#1000001^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 749916 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-112), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>310#:>310#5=#:>310,20##;71:0+$2-80$3$4$5$6$7$2+$2-80$26#=#$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,38!$2-70,8$32%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$26#,4#!$24#148,8#1000000'$32#1000001^#?#???????????????,48!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 749916 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 749916 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboTx.

Module LibSegEa_aboZ1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [750664].
Definition STOPS1 : list Z := [750664] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",41%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45"%pstring).
Definition ss0 : sym_state := SS 750880 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EVar 47), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 8); ((EVar 48), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EVar 47), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 8); ((EVar 48), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;7448#;7448#5=#;7448,20#$39$2$3$4$5$6$7$3:$3;$30#$<$=$>$?$10$11$3<$3=$3>$3?$40$41$42$43$44$45$1<$1=$1>$1?,,49!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 750664 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 750880 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 750880 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboZ1.

Module LibSegEa_aboZ11.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [750664].
Definition STOPS1 : list Z := [750664] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25$16$17$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",41%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45"%pstring).
Definition ss0 : sym_state := SS 750836 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EVar 47), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 8); ((EVar 48), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EVar 47), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 8); ((EVar 48), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;7448#;7448#5=#;7448,20#$39$2$3$4$5$6$7$3:$3;$30#$<$=$>$?$10$11$3<$3=$3>$3?$40$41$42$43$44$45$1<$1=$1>$1?,,49!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 750664 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 750836 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 750836 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboZ11.

Module LibSegEa_aboZ2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [750664].
Definition STOPS1 : list Z := [750664] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",41%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45"%pstring).
Definition ss0 : sym_state := SS 750924 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EVar 47), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 8); ((EVar 48), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EVar 47), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 8); ((EVar 48), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;7448#;7448#5=#;7448,20#$39$2$3$4$5$6$7$3:$3;$30#$<$=$>$?$10$11$3<$3=$3>$3?$40$41$42$43$44$45$1<$1=$1>$1?,,49!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 750664 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 750924 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 750924 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboZ2.

Module LibSegEa_aboZc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [750664].
Definition STOPS1 : list Z := [750664] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",41%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45"%pstring).
Definition ss0 : sym_state := SS 750136 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EVar 47), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 8); ((EVar 48), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EVar 47), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 8); ((EVar 48), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;7448#;7448#5=#;7448,20#$39$2$3$4$5$6$7$3:$3;$30#$<$=$>$?$10$11$3<$3=$3>$3?$40$41$42$43$44$45$1<$1=$1>$1?,,49!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 750664 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 750136 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 750136 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboZc.

Module LibSegEa_aboZt.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [750664].
Definition STOPS1 : list Z := [750664] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",41%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45"%pstring).
Definition ss0 : sym_state := SS 750324 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EVar 47), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 8); ((EVar 48), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EVar 47), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 8); ((EVar 48), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;7448#;7448#5=#;7448,20#$39$2$3$4$5$6$7$3:$3;$30#$<$=$>$?$10$11$3<$3=$3>$3?$40$41$42$43$44$45$1<$1=$1>$1?,,49!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 750664 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 750324 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 750324 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboZt.

Module LibSegEa_aboZt13.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_08753c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_08753c.IT.
Definition ENDS : list Z := [750664].
Definition STOPS1 : list Z := [750664] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",41%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45"%pstring).
Definition ss0 : sym_state := SS 749984 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EVar 47), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 8); ((EVar 48), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EVar 47), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 8); ((EVar 48), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;7448#;7448#5=#;7448,20#$39$2$3$4$5$6$7$3:$3;$30#$<$=$>$?$10$11$3<$3=$3>$3?$40$41$42$43$44$45$1<$1=$1>$1?,,49!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0'$24#698000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-:0#:0$24##180'$26#698000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-:0#:0$26##10'$25#698000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-:0#:0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#698000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-:0#:0$2?##40)$2-:0#:0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#124060!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 750664 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_08753c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 749984 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_08753c.IT BndT_Ea_000S8.SegItab_Ea_08753c.IT_sound BF NX0 BR XSTEP F0 PSS plan 749984 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aboZt13.
