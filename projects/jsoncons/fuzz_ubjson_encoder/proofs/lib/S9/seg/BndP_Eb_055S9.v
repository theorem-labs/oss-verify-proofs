(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Eb0PlanKit Eb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndT_Eb_000S9 BndT_Eb_001S9.

Module LibSegEb_bsrXlt.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_566b32.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_566b32.IT.
Definition ENDS : list Z := [759336].
Definition STOPS1 : list Z := [759336] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32$33$;$<$=$>$?$10$11+&6+$24#120#3#7???8000$24#$15+$24#?0+$24#120+&6+$24#?0#3#7???8000+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3>%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8#4000'$2=#69<000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$24##128$2=##110)$32##38$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#13;538!$2=#10,8#13;448!$2=#98,4#!$2=#9<,4#!$2=#:0,8+$2=#10###8001?6:4#1###8001?691#1)$2=##110$2?##80)$2=##110$30##1)&6$2?#3#7???8000#10&6$2=#3#7???8000#22)&6$2?#3#7???8000#10##8001?6:4#1)&6$2?#3#7???8000#10##8001?691#1'$33##3???"%pstring).
Definition ss0 : sym_state := SS 759144 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (256), ELit 40); ((EVar 45), (152), ELit 4)].
Definition F0L : list SR.region := [((EVar 36), (256), 40); ((EVar 45), (152), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9628#;9628#5=#;9628,20##;95>8$32$3$4$5$6$7$2$32+$24#100+$33$50##$>$?$10$11$33$24#$15$33+$24#120+&6+$24#?0#3#7???8000+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,3>!$24#100,8+$33$50!$2=#98,4#2%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8#4000'$2=#69<000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$24##128$2=##110)$32##38$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#13;538!$2=#10,8#13;448!$2=#9<,4#!$2=#:0,8+$2=#10###8001?6:4#1###8001?691#1)$2=##110$2?##80)$2=##110$30##1)&6$2?#3#7???8000#10&6$2=#3#7???8000#22)&6$2?#3#7???8000#10##8001?6:4#1)&6$2?#3#7???8000#10##8001?691#1'$33##3???,51!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 759336 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 759144 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 759144 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrXlt.

Module LibSegEb_bssE0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [1271400].
Definition STOPS1 : list Z := [1271400] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8#!$21#8,8#!$21#10,8#"%pstring).
Definition ss0 : sym_state := SS 771660 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#136668#136668#5=#136668,20##;56:4+$2-:0$3$4$5$6$7+$2-48#1#20#1#1460?8$21#$?$10$11+$2-60#+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,21!$2-:8,8#;56:4!$2-40,8$21!$2-48,8#!$2-98,8#7???8000!$2-90,8+&6+$21#8#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8$21!$2-70,8+$21#8!$2-68,8#;<70<!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8#!$21#8,8#!$21#10,8#,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 771660 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 771660 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssE0.

Module LibSegEb_bssE1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#1$28$;$<$=$>$?$10$11+$2-60#+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3:'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8#!$21#8,8#!$21#10,8#'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7?????????>0&$28#10)##7???7000#100000001000$28##20#&6$28#3#7???8000#4($28##20)$2-1000#1000$28##20)$21##18$28##20)$22##4$28##20)$23##8$28##20)##10000#68<000$28##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<70<!$2-70,8+$21#8!$2-78,8$21!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EVar 40), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EVar 40), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;5880+$2-;0$3$4$5$6$7+$2-60$21$28#####1&6+$21#10#3$11+$21#8+$2-58$28#7???8000+&6+$21#8#3#7???8000+&6+$2-58#3#7???8000+&6$21#3#7???8000$19$1:$1;$1<$1=$1>$1?,,47!$2-<8,8#::9:0!$2-<0,8+$2-60!$2-;8,8#;57>0!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#8#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8$21!$2-70,8+$21#8!$2-68,8#;<7;<!$2-50,8+$28#20!$28#18,8#!$28#10,1#!$28#8,8$27!$28#,4$26!$2-48,8+$28#20!$2-58,8$28!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8#!$21#8,8#!$21#10,8#'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7?????????>0&$28#10)##7???7000#100000001000$28##20#&6$28#3#7???8000#4($28##20)$2-1000#1000$28##20)$21##18$28##20)$22##4$28##20)$23##8$28##20)##10000#68<000$28##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$21,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssE1.

Module LibSegEb_bssE2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-60$21$:$;$<$=$>$?$10$11+$21#8+$2-58$28#7???8000+&6+$21#8#3#7???8000+&6+$2-58#3#7???8000+&6$21#3#7???8000$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",31'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18($21##18!$21#,8#!$21#8,8#!$21#10,8#'$28#1000#7?????????>0&$28#10)##7???7000#100000001000$28##20#&6$28#3#7???8000#4($28##20)$2-1000#1000$28##20)$21##18$28##20)$22##4$28##20)$23##8$28##20)##10000#68<000$28##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<7;<!$2-70,8+$21#8!$2-78,8$21!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-:0,8$32!$2-:8,8$33!$2-;0,8$34!$2-60,8$28!$2-58,8$28!$2-50,8+$28#20!$2-48,8+$28#20!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 743552 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##;5;:0+$2-70$3$4$5$6$7+$21#8$21$28+$28#20+$28#20+$28#20#1##$11$23$22+&6+$21#8#3#7???8000#7???8000$32$33$34$19$1:$1;$1<$1=$1>$1?,,31!$2-78,8#;5;:0!$2-70,8+$21#8!$2-68,8#;<7;<!$2-60,8#!$2-48,8#!$21#10,8+$28#20!$2-50,8#!$21#8,8+$28#20!$2-58,8#!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18($21##18'$28#1000#7?????????>0&$28#10)##7???7000#100000001000$28##20#&6$28#3#7???8000#4($28##20)$2-1000#1000$28##20)$21##18$28##20)$22##4$28##20)$23##8$28##20)##10000#68<000$28##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-:0,8$32!$2-:8,8$33!$2-;0,8$34!$2-40,8$21,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743552 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 743552 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssE2.

Module LibSegEb_bssE3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [772084].
Definition STOPS1 : list Z := [772084] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7+$21#8$21$:$;$<$=$>$?$10$11$23$22+&6+$21#8#3#7???8000#7???8000$32$33$34$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18($21##18!$21#,8$28!$21#8,8+$28#20!$21#10,8+$28#20'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<7;<!$2-70,8+$21#8!$2-60,8#!$2-58,8#!$2-50,8#!$2-48,8#!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 744352 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;<7?4#;<7?4#5=#;<7?4,20#$2;$2$3$4$5$6$7$2<$2=+$28#20+$2-40##7???8000&6+$2-40#3+&6+$2-50#3#7???8000##$2>$2?$30$31$32$33$34$19$1:$1;$1<$1=$1>$1?,,21!$2-68,8#;<7=0'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18($21##18!$21#,8$28!$21#8,8+$28#20!$21#10,8+$28#20'$28#1000#7?????????<0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-70,8+$21#8!$2-60,8#!$2-58,8#!$2-50,8#!$2-48,8#!$2-40,8$21,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 772084 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 744352 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 744352 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssE3.

Module LibSegEb_bssG0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#2$28$;$<$=$>$?$10$11+$2-60#1+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#20!$21#10,8+$24#20'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7?????????<0&$28#10(+$28#20##20#&6+$28#20#3#7???8000#4)##7???7000#100000001000+$28#20##20'+$28#20#1000#7?????????>0)$2-1000#1000+$28#20##20)$21##18+$28#20##20)$22##4+$28#20##20)$23##8+$28#20##20)##10000#68<000+$28#20##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<70<!$2-70,8+$21#8!$2-78,8$21!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (32))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (32))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-<0$3$4$5$6$7+$2-60$21$24+$24#20+$24#20+$24#20#1#&6+$21#10#3$11$23$22+&6+$21#8#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,4:!$2-<8,8#::9:0!$2-<0,8+$2-60!$2-;8,8#;57>0!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#8#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8$21!$2-70,8+$21#8!$2-68,8#;<7;<!$2-50,8+$28#40!$28#38,8#!$28#30,1#!$28#28,8$27!$28#20,4$26!$2-48,8+$28#40!$2-58,8+$28#20!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#20!$21#10,8+$24#20'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7?????????<0&$28#10(+$28#20##20#&6+$28#20#3#7???8000#4)##7???7000#100000001000+$28#20##20'+$28#20#1000#7?????????>0)$2-1000#1000+$28#20##20)$21##18+$28#20##20)$22##4+$28#20##20)$23##8+$28#20##20)##10000#68<000+$28#20##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$21,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssG0.

Module LibSegEb_bssG1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#4$28$;$<$=$>$?$10$11+$2-60#2+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#40!$21#10,8+$24#40'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7?????????80&$28#10(+$28#40##20#&6+$28#40#3#7???8000#4)##7???7000#100000001000+$28#40##20'+$28#40#1000#7?????????>0)$2-1000#1000+$28#40##20)$21##18+$28#40##20)$22##4+$28#40##20)$23##8+$28#40##20)##10000#68<000+$28#40##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<70<!$2-70,8+$21#8!$2-78,8$21!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (64))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (64))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-<0$3$4$5$6$7+$2-60$21$24+$24#40+$24#40+$24#40#1#&6+$21#10#3$11$23$22+&6+$21#8#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,4:!$2-<8,8#::9:0!$2-<0,8+$2-60!$2-;8,8#;57>0!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#8#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8$21!$2-70,8+$21#8!$2-68,8#;<7;<!$2-50,8+$28#60!$28#58,8#!$28#50,1#!$28#48,8$27!$28#40,4$26!$2-48,8+$28#80!$2-58,8+$28#40!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#40!$21#10,8+$24#40'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7?????????80&$28#10(+$28#40##20#&6+$28#40#3#7???8000#4)##7???7000#100000001000+$28#40##20'+$28#40#1000#7?????????>0)$2-1000#1000+$28#40##20)$21##18+$28#40##20)$22##4+$28#40##20)$23##8+$28#40##20)##10000#68<000+$28#40##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$21,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssG1.

Module LibSegEb_bssG10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#800$28$;$<$=$>$?$10$11+$2-60#400+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#8000!$21#10,8+$24#8000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7???????0000&$28#10(+$28#8000##20#&6+$28#8000#3#7???8000#4)##7???7000#100000001000+$28#8000##20'+$28#8000#1000#7?????????>0)$2-1000#1000+$28#8000##20)$21##18+$28#8000##20)$22##4+$28#8000##20)$23##8+$28#8000##20)##10000#68<000+$28#8000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<70<!$2-70,8+$21#8!$2-78,8$21!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (32768))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (32768))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-<0$3$4$5$6$7+$2-60$21$24+$24#8000+$24#8000+$24#8000#1#&6+$21#10#3$11$23$22+&6+$21#8#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,4:!$2-<8,8#::9:0!$2-<0,8+$2-60!$2-;8,8#;57>0!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#8#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8$21!$2-70,8+$21#8!$2-68,8#;<7;<!$2-50,8+$28#8020!$28#8018,8#!$28#8010,1#!$28#8008,8$27!$28#8000,4$26!$2-48,8+$28#10000!$2-58,8+$28#8000!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#8000!$21#10,8+$24#8000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7???????0000&$28#10(+$28#8000##20#&6+$28#8000#3#7???8000#4)##7???7000#100000001000+$28#8000##20'+$28#8000#1000#7?????????>0)$2-1000#1000+$28#8000##20)$21##18+$28#8000##20)$22##4+$28#8000##20)$23##8+$28#8000##20)##10000#68<000+$28#8000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$21,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssG10.

Module LibSegEb_bssG2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#8$28$;$<$=$>$?$10$11+$2-60#4+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#80!$21#10,8+$24#80'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7?????????00&$28#10(+$28#80##20#&6+$28#80#3#7???8000#4)##7???7000#100000001000+$28#80##20'+$28#80#1000#7?????????>0)$2-1000#1000+$28#80##20)$21##18+$28#80##20)$22##4+$28#80##20)$23##8+$28#80##20)##10000#68<000+$28#80##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<70<!$2-70,8+$21#8!$2-78,8$21!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (128))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (128))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-<0$3$4$5$6$7+$2-60$21$24+$24#80+$24#80+$24#80#1#&6+$21#10#3$11$23$22+&6+$21#8#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,4:!$2-<8,8#::9:0!$2-<0,8+$2-60!$2-;8,8#;57>0!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#8#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8$21!$2-70,8+$21#8!$2-68,8#;<7;<!$2-50,8+$28#:0!$28#98,8#!$28#90,1#!$28#88,8$27!$28#80,4$26!$2-48,8+$28#100!$2-58,8+$28#80!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#80!$21#10,8+$24#80'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7?????????00&$28#10(+$28#80##20#&6+$28#80#3#7???8000#4)##7???7000#100000001000+$28#80##20'+$28#80#1000#7?????????>0)$2-1000#1000+$28#80##20)$21##18+$28#80##20)$22##4+$28#80##20)$23##8+$28#80##20)##10000#68<000+$28#80##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$21,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssG2.

Module LibSegEb_bssG3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#10$28$;$<$=$>$?$10$11+$2-60#8+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#100!$21#10,8+$24#100'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7????????>00&$28#10(+$28#100##20#&6+$28#100#3#7???8000#4)##7???7000#100000001000+$28#100##20'+$28#100#1000#7?????????>0)$2-1000#1000+$28#100##20)$21##18+$28#100##20)$22##4+$28#100##20)$23##8+$28#100##20)##10000#68<000+$28#100##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<70<!$2-70,8+$21#8!$2-78,8$21!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (256))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (256))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-<0$3$4$5$6$7+$2-60$21$24+$24#100+$24#100+$24#100#1#&6+$21#10#3$11$23$22+&6+$21#8#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,4:!$2-<8,8#::9:0!$2-<0,8+$2-60!$2-;8,8#;57>0!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#8#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8$21!$2-70,8+$21#8!$2-68,8#;<7;<!$2-50,8+$28#120!$28#118,8#!$28#110,1#!$28#108,8$27!$28#100,4$26!$2-48,8+$28#200!$2-58,8+$28#100!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#100!$21#10,8+$24#100'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7????????>00&$28#10(+$28#100##20#&6+$28#100#3#7???8000#4)##7???7000#100000001000+$28#100##20'+$28#100#1000#7?????????>0)$2-1000#1000+$28#100##20)$21##18+$28#100##20)$22##4+$28#100##20)$23##8+$28#100##20)##10000#68<000+$28#100##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$21,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssG3.

Module LibSegEb_bssG4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#20$28$;$<$=$>$?$10$11+$2-60#10+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#200!$21#10,8+$24#200'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7????????<00&$28#10(+$28#200##20#&6+$28#200#3#7???8000#4)##7???7000#100000001000+$28#200##20'+$28#200#1000#7?????????>0)$2-1000#1000+$28#200##20)$21##18+$28#200##20)$22##4+$28#200##20)$23##8+$28#200##20)##10000#68<000+$28#200##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<70<!$2-70,8+$21#8!$2-78,8$21!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (512))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (512))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-<0$3$4$5$6$7+$2-60$21$24+$24#200+$24#200+$24#200#1#&6+$21#10#3$11$23$22+&6+$21#8#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,4:!$2-<8,8#::9:0!$2-<0,8+$2-60!$2-;8,8#;57>0!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#8#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8$21!$2-70,8+$21#8!$2-68,8#;<7;<!$2-50,8+$28#220!$28#218,8#!$28#210,1#!$28#208,8$27!$28#200,4$26!$2-48,8+$28#400!$2-58,8+$28#200!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#200!$21#10,8+$24#200'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7????????<00&$28#10(+$28#200##20#&6+$28#200#3#7???8000#4)##7???7000#100000001000+$28#200##20'+$28#200#1000#7?????????>0)$2-1000#1000+$28#200##20)$21##18+$28#200##20)$22##4+$28#200##20)$23##8+$28#200##20)##10000#68<000+$28#200##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$21,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssG4.

Module LibSegEb_bssG5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#40$28$;$<$=$>$?$10$11+$2-60#20+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#400!$21#10,8+$24#400'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7????????800&$28#10(+$28#400##20#&6+$28#400#3#7???8000#4)##7???7000#100000001000+$28#400##20'+$28#400#1000#7?????????>0)$2-1000#1000+$28#400##20)$21##18+$28#400##20)$22##4+$28#400##20)$23##8+$28#400##20)##10000#68<000+$28#400##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<70<!$2-70,8+$21#8!$2-78,8$21!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (1024))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (1024))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-<0$3$4$5$6$7+$2-60$21$24+$24#400+$24#400+$24#400#1#&6+$21#10#3$11$23$22+&6+$21#8#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,4:!$2-<8,8#::9:0!$2-<0,8+$2-60!$2-;8,8#;57>0!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#8#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8$21!$2-70,8+$21#8!$2-68,8#;<7;<!$2-50,8+$28#420!$28#418,8#!$28#410,1#!$28#408,8$27!$28#400,4$26!$2-48,8+$28#800!$2-58,8+$28#400!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#400!$21#10,8+$24#400'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7????????800&$28#10(+$28#400##20#&6+$28#400#3#7???8000#4)##7???7000#100000001000+$28#400##20'+$28#400#1000#7?????????>0)$2-1000#1000+$28#400##20)$21##18+$28#400##20)$22##4+$28#400##20)$23##8+$28#400##20)##10000#68<000+$28#400##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$21,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssG5.

Module LibSegEb_bssG6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#80$28$;$<$=$>$?$10$11+$2-60#40+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#800!$21#10,8+$24#800'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7????????000&$28#10(+$28#800##20#&6+$28#800#3#7???8000#4)##7???7000#100000001000+$28#800##20'+$28#800#1000#7?????????>0)$2-1000#1000+$28#800##20)$21##18+$28#800##20)$22##4+$28#800##20)$23##8+$28#800##20)##10000#68<000+$28#800##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<70<!$2-70,8+$21#8!$2-78,8$21!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (2048))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (2048))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-<0$3$4$5$6$7+$2-60$21$24+$24#800+$24#800+$24#800#1#&6+$21#10#3$11$23$22+&6+$21#8#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,4:!$2-<8,8#::9:0!$2-<0,8+$2-60!$2-;8,8#;57>0!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#8#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8$21!$2-70,8+$21#8!$2-68,8#;<7;<!$2-50,8+$28#820!$28#818,8#!$28#810,1#!$28#808,8$27!$28#800,4$26!$2-48,8+$28#1000!$2-58,8+$28#800!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#800!$21#10,8+$24#800'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7????????000&$28#10(+$28#800##20#&6+$28#800#3#7???8000#4)##7???7000#100000001000+$28#800##20'+$28#800#1000#7?????????>0)$2-1000#1000+$28#800##20)$21##18+$28#800##20)$22##4+$28#800##20)$23##8+$28#800##20)##10000#68<000+$28#800##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$21,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssG6.

Module LibSegEb_bssG7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_992b82.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_992b82.IT.
Definition ENDS : list Z := [511016].
Definition STOPS1 : list Z := [511016] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-48#100$28$;$<$=$>$?$10$11+$2-60#80+&6+$2-48#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#1000!$21#10,8+$24#1000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7???????>000&$28#10(+$28#1000##20#&6+$28#1000#3#7???8000#4)##7???7000#100000001000+$28#1000##20'+$28#1000#1000#7?????????>0)$2-1000#1000+$28#1000##20)$21##18+$28#1000##20)$22##4+$28#1000##20)$23##8+$28#1000##20)##10000#68<000+$28#1000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-68,8#;<70<!$2-70,8+$21#8!$2-78,8$21!$2-80,8$23!$2-88,8$22!$2-90,8+&6+$21#8#3#7???8000!$2-98,8#7???8000!$2-48,8#!$2-40,8$21"%pstring).
Definition ss0 : sym_state := SS 743076 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (4096))), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EAlu Instr.ALU_ADD (EVar 40) (ELit (4096))), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<<28#7<<28#5=#7<<28,20##::9:0+$2-<0$3$4$5$6$7+$2-60$21$24+$24#1000+$24#1000+$24#1000#1#&6+$21#10#3$11$23$22+&6+$21#8#3#7???8000#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,4:!$2-<8,8#::9:0!$2-<0,8+$2-60!$2-;8,8#;57>0!$2-;0,8$18!$2-:8,8$17!$2-:0,8$16!$2-98,8#7???8000!$2-90,8+&6+$21#8#3#7???8000!$2-88,8$22!$2-80,8$23!$2-78,8$21!$2-70,8+$21#8!$2-68,8#;<7;<!$2-50,8+$28#1020!$28#1018,8#!$28#1010,1#!$28#1008,8$27!$28#1000,4$26!$2-48,8+$28#2000!$2-58,8+$28#1000!$2-60,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$21#69<000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#68<000$21##18!$21#,8$24!$21#8,8+$24#1000!$21#10,8+$24#1000'$24#1000#7?????????>0&$24#10'$22#69<000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4'$23#69<000#7??????????8&$23#8)##7???7000#100000001000$23##8#&6$23#3#7???8000#1!$23#,8$27)$2-1000#1000$23##8)$21##18$22##4)$21##18$23##8'$26##7???????'$27#^#?#???????????????'$28#1000#7???????>000&$28#10(+$28#1000##20#&6+$28#1000#3#7???8000#4)##7???7000#100000001000+$28#1000##20'+$28#1000#1000#7?????????>0)$2-1000#1000+$28#1000##20)$21##18+$28#1000##20)$22##4+$28#1000##20)$23##8+$28#1000##20)##10000#68<000+$28#1000##20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$21,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_992b82.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743076 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_992b82.IT BndT_Eb_001S9.SegItab_Eb_992b82.IT_sound BF NX0 BR XSTEP F0 PSS plan 743076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bssG7.
