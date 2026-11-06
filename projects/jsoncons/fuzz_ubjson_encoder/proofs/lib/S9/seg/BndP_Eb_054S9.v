(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Eb0PlanKit Eb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndT_Eb_000S9.

Module LibSegEb_bsrB0f.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_566b32.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_566b32.IT.
Definition ENDS : list Z := [760132].
Definition STOPS1 : list Z := [760132] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 50; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EVar 50; EVar 47; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 36; EVar 20; EVar 21; EVar 38; EVar 23; EVar 24; EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044'$26#1#3???"%pstring).
Definition ss0 : sym_state := SS 758208 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (0), ELit 56); ((EVar 47), (0), ELit 24); ((EVar 47), (32), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 50), (0), 56); ((EVar 47), (0), 24); ((EVar 47), (32), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9944#;9944#5=#;9944,20##;9398$32$3$4$5$6$7$2$32$24$22#4000#4000^#?#??????????????1^#?#??????????????3$2?$11+&6+$24#120#3#7???8000$24#+&6+$24#118#3#7???8000+$24#118+$24#120$18+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,3:!$24#118,8$22!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?!$2?#20,8$26!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!&6$2?#3#7???8007,1^#?#??????????????2!&6$2?#3#7???8006,1^#?#??????????????2!&6$2?#3#7???8005,1^#?#??????????????2!&6$2?#3#7???8004,1#!$2?#10,8#;9148!$2?#8,8#1?29=!$2?#,8#41;58:;3%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?#18#8,$2?#28#58($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044'$26#1#3???,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 760132 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758208 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrB0f.

Module LibSegEb_bsrB0x.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_566b32.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_566b32.IT.
Definition ENDS : list Z := [920364].
Definition STOPS1 : list Z := [920364] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 50; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EVar 50; EVar 47; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 36; EVar 20; EVar 21; ELit 16384; EVar 23; EVar 24; EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3:%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044'$2=#69<000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$24##128$2=##110)$32##38$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#13;538!$2=#10,8#13;448!$2=#98,4#!$2=#9<,4#!$2=#:0,8+$2=#10###8001?6:4#1###8001?691#1)$2=##110$2?##80)$2=##110$30##1)&6$2?#3#7???8000#10&6$2=#3#7???8000#22)&6$2?#3#7???8000#10##8001?6:4#1)&6$2?#3#7???8000#10##8001?691#1"%pstring).
Definition ss0 : sym_state := SS 758208 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (0), ELit 56); ((EVar 47), (0), ELit 24); ((EVar 47), (32), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 50), (0), 56); ((EVar 47), (0), 24); ((EVar 47), (32), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#>0;2<#>0;2<#5=#>0;2<,20##;9568$32$3$4$5$6$7$2$32+$2=#10$25#4000#>0;2<#^#?#??????????????3$2?$11+&6+$24#120#3#7???8000$24#$15+$24#?0+$24#120+&6+$24#?0#3#7???8000+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,4>!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?!$2?#20,8#4000!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!&6$2?#3#7???8007,1^#?#??????????????2!&6$2?#3#7???8006,1^#?#??????????????2!&6$2?#3#7???8005,1^#?#??????????????2!&6$2?#3#7???8004,1#!$2?#10,8#;9148!$2?#8,8#1?29=!$2?#,8#41;58:;3%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?#18#8,$2?#28#58($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044'$2=#69<000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$24##128$2=##110)$32##38$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#13;538!$2=#10,8#13;448!$2=#98,4#!$2=#9<,4#!$2=#:0,8+$2=#10###8001?6:4#1###8001?691#1)$2=##110$2?##80)$2=##110$30##1)&6$2?#3#7???8000#10&6$2=#3#7???8000#22)&6$2?#3#7???8000#10##8001?6:4#1)&6$2?#3#7???8000#10##8001?691#1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 920364 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758208 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrB0x.

Module LibSegEb_bsrB1ge.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_566b32.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_566b32.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 50; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EVar 50; EVar 47; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 36; EVar 20; EVar 21; EVar 38; EVar 23; EVar 24; EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 50) 140735332487168 140737488355168;
   KAlign (EVar 50) 32;
   KWr (SA (EVar 50) 0) (ELit 56);
   KWord (SA (EVar 50) 24) 8 (EVar 37);
   KRange (EVar 37) 4096 140737488338944;
   KRange (EVar 36) 6930432 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KWr (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWord (SA (EVar 36) (280)) 8 (EVar 35);
   KWord (SA (EVar 36) (288)) 8 (EVar 33);
   KRange (EVar 47) 6930432 140737488355200;
   KAlign (EVar 47) 32;
   KUnk (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KWord (SA (EVar 47) 120) 8 (EVar 48);
   KRange (EVar 48) 4096 140737488355327;
   KWr (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit 37) (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (ELit 0) 65536) (ELit 1200196);
   KRange (EVar 33) 1 16384;
   KRange (EVar 38) 1 16384;
   KRange (APC.esub (EVar 38) (EVar 33)) 0 16383;
   KRange (EVar 35) 4096 140737488338944].
Definition ss0 : sym_state := SS 758208 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (0), ELit 56); ((EVar 47), (0), ELit 24); ((EVar 47), (32), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 50), (0), 56); ((EVar 47), (0), 24); ((EVar 47), (32), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;92=0$32$3$4$5$6$7$2$32$25$23$21^#?#??????????????2^#?#??????????????1^#?#??????????????3$2?$11+&6+$24#120#3#7???8000$24$21+&6+$24#118#3#7???8000$26+$24#120+$24#118+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,3=!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?!$2?#20,8$26!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!&6$2?#3#7???8007,1^#?#??????????????2!&6$2?#3#7???8006,1^#?#??????????????2!&6$2?#3#7???8005,1^#?#??????????????2!&6$2?#3#7???8004,1#!$2?#10,8#;9148!$2?#8,8#1?29=!$2?#,8#41;58:;3%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8$21'$2?#69<000#7?????????80&$2?#20,$2?#18#8,$2?#28#58($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044'$21#1#4000'$26#1#4000'+@-1$21$26##3???'$23#1000#7???????<000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 495168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758208 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrB1ge.

Module LibSegEb_bsrB1lt.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_566b32.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_566b32.IT.
Definition ENDS : list Z := [758424].
Definition STOPS1 : list Z := [758424] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 50; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EVar 50; EVar 47; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 36; EVar 20; EVar 21; EVar 38; EVar 23; EVar 24; EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 50) 140735332487168 140737488355168;
   KAlign (EVar 50) 32;
   KWr (SA (EVar 50) 0) (ELit 56);
   KWord (SA (EVar 50) 24) 8 (EVar 37);
   KRange (EVar 37) 4096 140737488338944;
   KRange (EVar 36) 6930432 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KWr (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWord (SA (EVar 36) (280)) 8 (EVar 35);
   KWord (SA (EVar 36) (288)) 8 (EVar 33);
   KRange (EVar 47) 6930432 140737488355200;
   KAlign (EVar 47) 32;
   KUnk (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KWord (SA (EVar 47) 120) 8 (EVar 48);
   KRange (EVar 48) 4096 140737488355327;
   KWr (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit 37) (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (ELit 0) 65536) (ELit 1200196);
   KRange (EVar 33) 2 16384;
   KRange (EVar 38) 1 16383;
   KRange (APC.esub (EVar 33) (EVar 38)) 1 16383;
   KRange (EVar 35) 4096 140737488338944].
Definition ss0 : sym_state := SS 758208 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (0), ELit 56); ((EVar 47), (0), ELit 24); ((EVar 47), (32), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 50), (0), 56); ((EVar 47), (0), 24); ((EVar 47), (32), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9298#;9298#5=#;9298,20#$1$32$3$4$5$6$7$2$32+$2?#20$21+$2?#20^#?#??????????????2^#?#??????????????1^#?#??????????????3$2?$11+&6+$24#120#3#7???8000$24$14$15$26+$24#120$18+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,3=!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?!$2?#20,8$26!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!&6$2?#3#7???8007,1^#?#??????????????2!&6$2?#3#7???8006,1^#?#??????????????2!&6$2?#3#7???8005,1^#?#??????????????2!&6$2?#3#7???8004,1#!$2?#10,8#;9148!$2?#8,8#1?29=!$2?#,8#41;58:;3%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8$21'$2?#69<000#7?????????80&$2?#20,$2?#18#8,$2?#28#58($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044'$21#2#4000'$26#1#3???'+$21@-1$26#1#3???'$23#1000#7???????<000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 758424 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758208 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrB1lt.

Module LibSegEb_bsrB1lt2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_566b32.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_566b32.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32+$2?#20$21$<$=$>$?$10$11+&6+$24#120#3#7???8000$24$14$15$26+$24#120$18+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 50) 140735332487168 140737488355168;
   KAlign (EVar 50) 32;
   KWr (SA (EVar 50) 0) (ELit 56);
   KWord (SA (EVar 50) 24) 8 (EVar 37);
   KRange (EVar 37) 4096 140737488338944;
   KWord (SA (EVar 50) 8) 8 (EAlu Instr.ALU_ADD (EVar 47) (ELit 32));
   KWord (SA (EVar 50) 16) 8 (EVar 47);
   KWord (SA (EVar 50) 48) 8 (EVar 47);
   KRange (EVar 36) 6930432 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KWr (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWord (SA (EVar 36) (280)) 8 (EVar 35);
   KWord (SA (EVar 36) (288)) 8 (EVar 33);
   KRange (EVar 47) 6930432 140737488355200;
   KAlign (EVar 47) 32;
   KUnk (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KWord (SA (EVar 47) 120) 8 (EVar 48);
   KRange (EVar 48) 4096 140737488355327;
   KWr (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit 37) (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (ELit 0) 65536) (ELit 1200196);
   KWord (SA (EVar 47) (32)) 8 (EVar 38);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 47) (ELit (32))) (ELit 3)) 2147450880) (ELit 1);
   KRange (EVar 33) 2 16384;
   KRange (EVar 38) 1 16383;
   KRange (APC.esub (EVar 33) (EVar 38)) 1 16383;
   KRange (EVar 35) 4096 140737488338944].
Definition ss0 : sym_state := SS 758424 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;92=0$32$3$4$5$6$7$2$32$25$23$26$=$>$?$10$11+&6+$24#120#3#7???8000$24$26+&6+$24#118#3#7???8000$26+$24#120+$24#118+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,2=%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8$21'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8$26#&6+$2?#20#3#7???8000#1'$21#2#4000'$26#1#3???'+$21@-1$26#1#3???'$23#1000#7???????<000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 495168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758424 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758424 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrB1lt2.

Module LibSegEb_bsrF0.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32#$;$<$=$>$?$10$11+&6+$24#120#3#7???8000$24$27+&6+$24#118#3#7???8000+$24#118+$24#120$18+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2<%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$22!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8+$28$27!&6$2?#3#7???8004,1#!&6$2?#3#7???8008,1#?8'$27##3???'$28#1#4000"%pstring).
Definition ss0 : sym_state := SS 758680 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9628#;9628#5=#;9628,20#$1$32$3$4$5$6$7$2$32##$<$=$>$?$10$11+&6+$24#120#3#7???8000$24$27+&6+$24#118#3#7???8000$27+$24#120$18+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,2<!$24#120,8#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$22'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8+$28$27!&6$2?#3#7???8004,1#!&6$2?#3#7???8008,1#?8'$27##3???'$28#1#4000,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758680 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758680 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrF0.

Module LibSegEb_bsrFge.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_566b32.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_566b32.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32$21$;$<$=$>$?$10$11+&6+$24#120#3#7???8000$24$27+&6+$24#118#3#7???8000+$24#118+$24#120$18+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 50) 140735332487168 140737488355168;
   KAlign (EVar 50) 32;
   KWr (SA (EVar 50) 0) (ELit 56);
   KWord (SA (EVar 50) 24) 8 (EVar 37);
   KRange (EVar 37) 4096 140737488338944;
   KWord (SA (EVar 50) 8) 8 (EAlu Instr.ALU_ADD (EVar 47) (ELit 32));
   KWord (SA (EVar 50) 16) 8 (EVar 47);
   KWord (SA (EVar 50) 48) 8 (EVar 47);
   KRange (EVar 36) 6930432 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KWr (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWord (SA (EVar 36) (280)) 8 (EVar 34);
   KWord (SA (EVar 36) (288)) 8 (ELit 0);
   KRange (EVar 47) 6930432 140737488355200;
   KAlign (EVar 47) 32;
   KUnk (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KWord (SA (EVar 47) 120) 8 (EVar 48);
   KRange (EVar 48) 4096 140737488355327;
   KWr (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit 37) (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (ELit 0) 65536) (ELit 1200196);
   KWord (SA (EVar 47) (32)) 8 ((EAlu Instr.ALU_ADD (EVar 40) (EVar 39)));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450884) 1 (ELit 0);
   KWord (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450888) 1 (ELit 248);
   KRange (EVar 33) 1 16384;
   KRange (EVar 39) 0 16383;
   KRange (EVar 40) 1 16384;
   KRange (APC.esub (EVar 40) (EVar 33)) 0 16383;
   KRange (EVar 34) 4096 140737488338944].
Definition ss0 : sym_state := SS 758680 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 47), (64), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (8), ELit 1); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 47), (64), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (8), 1); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;9418$32$3$4$5$6$7$2$32+$25$27$22$21$=$>$?$10$11+&6+$24#120#3#7???8000$24$27+&6+$24#118#3#7???8000+$24#118+$24#120$21+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,31!&6$2?#3#7???8008,1^#?#??????????????8!$2?#40,8$28!$24#120,8$21%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$22'$2?#69<000#7?????????80&$2?#20,$2?##40,$2?#48#38($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8+$28$27!&6$2?#3#7???8004,1#'$21#1#4000'$27##3???'$28#1#4000'+@-1$21$28##3???'$22#1000#7???????<000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 495168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758680 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758680 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrFge.

Module LibSegEb_bsrFlt.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_566b32.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_566b32.IT.
Definition ENDS : list Z := [758728].
Definition STOPS1 : list Z := [758728] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32$21$;$<$=$>$?$10$11+&6+$24#120#3#7???8000$24$27+&6+$24#118#3#7???8000+$24#118+$24#120$18+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 50) 140735332487168 140737488355168;
   KAlign (EVar 50) 32;
   KWr (SA (EVar 50) 0) (ELit 56);
   KWord (SA (EVar 50) 24) 8 (EVar 37);
   KRange (EVar 37) 4096 140737488338944;
   KWord (SA (EVar 50) 8) 8 (EAlu Instr.ALU_ADD (EVar 47) (ELit 32));
   KWord (SA (EVar 50) 16) 8 (EVar 47);
   KWord (SA (EVar 50) 48) 8 (EVar 47);
   KRange (EVar 36) 6930432 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KWr (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWord (SA (EVar 36) (280)) 8 (EVar 34);
   KWord (SA (EVar 36) (288)) 8 (ELit 0);
   KRange (EVar 47) 6930432 140737488355200;
   KAlign (EVar 47) 32;
   KUnk (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KWord (SA (EVar 47) 120) 8 (EVar 48);
   KRange (EVar 48) 4096 140737488355327;
   KWr (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit 37) (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (ELit 0) 65536) (ELit 1200196);
   KWord (SA (EVar 47) (32)) 8 ((EAlu Instr.ALU_ADD (EVar 40) (EVar 39)));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450884) 1 (ELit 0);
   KWord (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450888) 1 (ELit 248);
   KRange (EVar 33) 2 16384;
   KRange (EVar 39) 0 16383;
   KRange (EVar 40) 1 16383;
   KRange (APC.esub (EVar 33) (EVar 40)) 1 16383].
Definition ss0 : sym_state := SS 758680 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 47), (64), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (8), ELit 1); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 47), (64), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (8), 1); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;93<8#;93<8#5=#;93<8,20#$1$32$3$4$5$6$7$2$32$21+$2?#40$28$=$>$?$10$11+&6+$24#120#3#7???8000$24$27+&6+$24#118#3#7???8000+$24#118+$24#120$18+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,30!$2?#40,8$28!&6$2?#3#7???8008,1#!$24#120,8$21%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$22'$2?#69<000#7?????????80&$2?#20,$2?##40,$2?#48#38($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8+$28$27!&6$2?#3#7???8004,1#'$21#2#4000'$27##3???'$28#1#3???'+$21@-1$28#1#3???,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 758728 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758680 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758680 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrFlt.

Module LibSegEb_bsrFlt2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_566b32.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_566b32.IT.
Definition ENDS : list Z := [495168].
Definition STOPS1 : list Z := [495168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32$21+$2?#40$28$=$>$?$10$11+&6+$24#120#3#7???8000$24$27+&6+$24#118#3#7???8000+$24#118+$24#120$18+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 50) 140735332487168 140737488355168;
   KAlign (EVar 50) 32;
   KWr (SA (EVar 50) 0) (ELit 56);
   KWord (SA (EVar 50) 24) 8 (EVar 37);
   KRange (EVar 37) 4096 140737488338944;
   KWord (SA (EVar 50) 8) 8 (EAlu Instr.ALU_ADD (EVar 47) (ELit 32));
   KWord (SA (EVar 50) 16) 8 (EVar 47);
   KWord (SA (EVar 50) 48) 8 (EVar 47);
   KRange (EVar 36) 6930432 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KWr (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWord (SA (EVar 36) (280)) 8 (EVar 34);
   KWord (SA (EVar 36) (288)) 8 (EVar 33);
   KRange (EVar 47) 6930432 140737488355200;
   KAlign (EVar 47) 32;
   KUnk (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KWord (SA (EVar 47) 120) 8 (EVar 48);
   KRange (EVar 48) 4096 140737488355327;
   KWr (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit 37) (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (ELit 0) 65536) (ELit 1200196);
   KWord (SA (EVar 47) (32)) 8 ((EAlu Instr.ALU_ADD (EVar 40) (EVar 39)));
   KWord (SA (EVar 47) (64)) 8 (EVar 40);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 47) (ELit (64))) (ELit 3)) 2147450880) (ELit 1);
   KRange (EVar 33) 2 16384;
   KRange (EVar 39) 0 16383;
   KRange (EVar 40) 1 16383;
   KRange (APC.esub (EVar 33) (EVar 40)) 1 16383;
   KRange (EVar 34) 4096 140737488338944].
Definition ss0 : sym_state := SS 758728 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 47), (64), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (8), ELit 1); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 47), (64), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (8), 1); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78>40#78>40#5=#78>40,20##;9418$32$3$4$5$6$7$2$32+$25$27$22$28$=$>$?$10$11+&6+$24#120#3#7???8000$24$27+&6+$24#118#3#7???8000+$24#118+$24#120$28+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,30!&6$2?#3#7???8008,1^#?#??????????????8%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$22!$24#120,8$21'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8+$28$27!$2?#40,8$28#&6$2?#3#7???8009++@-1&6$2?#3&6+$2?#40#3-8'$21#2#4000'$27##3???'$28#1#3???'+$21@-1$28#1#3???'$22#1000#7???????<000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 495168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758728 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758728 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrFlt2.

Module LibSegEb_bsrM1eq.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32$:$;$<$=$>$?$10$11+&6+$24#120#3#7???8000$24$26+&6+$24#118#3#7???8000$26+$24#120+$24#118+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 50) 140735332487168 140737488355168;
   KAlign (EVar 50) 32;
   KWr (SA (EVar 50) 0) (ELit 56);
   KWord (SA (EVar 50) 24) 8 (EVar 37);
   KRange (EVar 37) 4096 140737488338944;
   KWord (SA (EVar 50) 8) 8 (EAlu Instr.ALU_ADD (EVar 47) (ELit 32));
   KWord (SA (EVar 50) 16) 8 (EVar 47);
   KWord (SA (EVar 50) 48) 8 (EVar 47);
   KRange (EVar 36) 6930432 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KWr (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWord (SA (EVar 36) (280)) 8 (EVar 35);
   KWord (SA (EVar 36) (288)) 8 (EVar 33);
   KRange (EVar 47) 6930432 140737488355200;
   KAlign (EVar 47) 32;
   KUnk (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KWord (SA (EVar 47) 120) 8 (EVar 48);
   KRange (EVar 48) 4096 140737488355327;
   KWr (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit 37) (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (ELit 0) 65536) (ELit 1200196);
   KWord (SA (EVar 47) (32)) 8 (EVar 38);
   KWord (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450884) 1 (ELit 0);
   KWord (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450888) 1 (ELit 248);
   KRange (EVar 33) 1 16384;
   KRange (EVar 38) 1 16384;
   KRange (APC.esub (EVar 33) (EVar 38)) 0 16383;
   KRange (EVar 35) 4096 140737488338944].
Definition ss0 : sym_state := SS 758480 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9628#;9628#5=#;9628,20#$1$32$3$4$5$6$7$2$32+$24#100+$26$50#$=$>$?$10$11+&6+$24#120#3#7???8000$24$26+&6+$24#118#3#7???8000$26+$24#120+$24#118+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,2>!$24#100,8+$26$50!$24#120,8+$21@-1$26!$24#118,8+$23$26%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8$26!&6$2?#3#7???8004,1#!&6$2?#3#7???8008,1#?8'$21#1#4000'$26#1#4000'+$21@-1$26##3???'$23#1000#7???????<000,51!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758480 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758480 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrM1eq.

Module LibSegEb_bsrM1ne.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_566b32.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_566b32.IT.
Definition ENDS : list Z := [760132].
Definition STOPS1 : list Z := [760132] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32$:$;$<$=$>$?$10$11+&6+$24#120#3#7???8000$24$21+&6+$24#118#3#7???8000$26+$24#120+$24#118+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 50) 140735332487168 140737488355168;
   KAlign (EVar 50) 32;
   KWr (SA (EVar 50) 0) (ELit 56);
   KWord (SA (EVar 50) 24) 8 (EVar 37);
   KRange (EVar 37) 4096 140737488338944;
   KWord (SA (EVar 50) 8) 8 (EAlu Instr.ALU_ADD (EVar 47) (ELit 32));
   KWord (SA (EVar 50) 16) 8 (EVar 47);
   KWord (SA (EVar 50) 48) 8 (EVar 47);
   KRange (EVar 36) 6930432 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KWr (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWord (SA (EVar 36) (280)) 8 (EVar 35);
   KWord (SA (EVar 36) (288)) 8 (EVar 33);
   KRange (EVar 47) 6930432 140737488355200;
   KAlign (EVar 47) 32;
   KUnk (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KWord (SA (EVar 47) 120) 8 (EVar 48);
   KRange (EVar 48) 4096 140737488355327;
   KWr (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit 37) (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (ELit 0) 65536) (ELit 1200196);
   KWord (SA (EVar 47) (32)) 8 (EVar 38);
   KWord (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450884) 1 (ELit 0);
   KWord (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450888) 1 (ELit 248);
   KRange (EVar 33) 1 16383;
   KRange (EVar 38) 2 16384;
   KRange (APC.esub (EVar 38) (EVar 33)) 1 16383;
   KRange (EVar 35) 4096 140737488338944].
Definition ss0 : sym_state := SS 758480 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9944#;9944#5=#;9944,20##;9398$32$3$4$5$6$7$2$32$24$22#4000#4000$>$?$10$11+&6+$24#120#3#7???8000$24$21+&6+$24#118#3#7???8000+$24#118+$24#120+$24#118+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,2>!$24#118,8$22!$24#100,8+$21$50!$24#120,8#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8$26!&6$2?#3#7???8004,1#!&6$2?#3#7???8008,1#?8'$21#1#3???'$26#2#4000'+@-1$21$26#1#3???'$23#1000#7???????<000,51!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 760132 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758480 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758480 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrM1ne.

Module LibSegEb_bsrM2.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32$:$;$<$=$>$?$10$11+&6+$24#120#3#7???8000$24$27+&6+$24#118#3#7???8000+$24#118+$24#120$28+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 50) 140735332487168 140737488355168;
   KAlign (EVar 50) 32;
   KWr (SA (EVar 50) 0) (ELit 56);
   KWord (SA (EVar 50) 24) 8 (EVar 37);
   KRange (EVar 37) 4096 140737488338944;
   KWord (SA (EVar 50) 8) 8 (EAlu Instr.ALU_ADD (EVar 47) (ELit 32));
   KWord (SA (EVar 50) 16) 8 (EVar 47);
   KWord (SA (EVar 50) 48) 8 (EVar 47);
   KRange (EVar 36) 6930432 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KWr (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWord (SA (EVar 36) (280)) 8 (EVar 34);
   KWord (SA (EVar 36) (288)) 8 (EVar 33);
   KRange (EVar 47) 6930432 140737488355200;
   KAlign (EVar 47) 32;
   KUnk (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 47) 0) (ELit 128);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KWord (SA (EVar 47) 120) 8 (EVar 48);
   KRange (EVar 48) 4096 140737488355327;
   KWr (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 36) 0) (ELit 296) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit 37) (SA (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) 2147450880) (ELit 16);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 47) 0) (ELit 128);
   KDisj (SA (EVar 50) 0) (ELit 56) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 47) 0) (ELit 128) (SA (ELit 0) 65536) (ELit 1200196);
   KRange (EVar 33) 1 16384;
   KRange (EVar 39) 0 16383;
   KRange (EVar 40) 1 16384;
   KRange (APC.esub (EVar 33) (EVar 40)) 0 16383;
   KRange (EVar 34) 4096 140737488338944].
Definition ss0 : sym_state := SS 758808 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9628#;9628#5=#;9628,20#$1$32$3$4$5$6$7$2$32+$24#100+$28$50#$=$>$?$10$11+&6+$24#120#3#7???8000$24$27+&6+$24#118#3#7???8000+$27$28+$24#120$28+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,2<!$24#100,8+$28$50!$24#120,8+$21@-1$28!$24#118,8+$22$28%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044'$21#1#4000'$27##3???'$28#1#4000'+$21@-1$28##3???'$22#1000#7???????<000,51!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 758808 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 758808 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrM2.

Module LibSegEb_bsrR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_566b32.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_566b32.IT.
Definition ENDS : list Z := [759548].
Definition STOPS1 : list Z := [759548] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32$:$;$<$=$>$?$10$11$12$13$14$15$29$17$18+&6$2?#3#7???8000$2?$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",28'$2#7???7?8010:0#800000000000&$2#10($2-:0#:0'$32#7???7?801000#7?????????60&$32#20($32##38!$32#10,8$2?'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<)$2-68#68$2?##80)$2-68#68$30##1)$2-68#68&6$2?#3#7???8000#10"%pstring).
Definition ss0 : sym_state := SS 759336 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 47), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16); ((EVar 48), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 47), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16); ((EVar 48), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;96?<#;96?<#5=#;96?<,20#$40$2$3$4$5$6$7$41$42$29$2?$<$=$>$?$10$11$43$44$45$46$47$48$49$4:$4;$4<$1<$1=$1>$1?,,3:!$30#,1#!&6$2?#3#7???800;,1^#?#??????????????5!&6$2?#3#7???800:,1^#?#??????????????5!&6$2?#3#7???8009,1^#?#??????????????5!&6$2?#3#7???8008,1^#?#??????????????5!&6$2?#3#7???800?,1^#?#??????????????5!&6$2?#3#7???800>,1^#?#??????????????5!&6$2?#3#7???800=,1^#?#??????????????5!&6$2?#3#7???800<,1^#?#??????????????5!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>'$2#7???7?8010:0#800000000000&$2#10($2-:0#:0'$32#7???7?801000#7?????????60&$32#20($32##38!$32#10,8$2?'$2?#69<000#7?????????80&$2?#20,$2?#8#78($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<)$2-68#68$2?##80)$2-68#68$30##1)$2-68#68&6$2?#3#7???8000#10,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 759548 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_566b32.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 759336 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_566b32.IT BndT_Eb_000S9.SegItab_Eb_566b32.IT_sound BF NX0 BR XSTEP F0 PSS plan 759336 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bsrR.

Module LibSegEb_bsrXge.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32#4000$;$<$=$>$?$10$11+&6+$24#120#3#7???8000$24#$15+$24#?0+$24#120+&6+$24#?0#3#7???8000+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3=%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8#4000'$2=#69<000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$24##128$2=##110)$32##38$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#13;538!$2=#10,8#13;448!$2=#98,4#!$2=#9<,4#!$2=#:0,8+$2=#10###8001?6:4#1###8001?691#1)$2=##110$2?##80)$2=##110$30##1)&6$2?#3#7???8000#10&6$2=#3#7???8000#22)&6$2?#3#7???8000#10##8001?6:4#1)&6$2?#3#7???8000#10##8001?691#1"%pstring).
Definition ss0 : sym_state := SS 759144 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9628#;9628#5=#;9628,20#$1$32$3$4$5$6$7$2$32+$24#100+$50#4000$<$=$>$?$10$11#4000$24#$15#4000+$24#120+&6+$24#?0#3#7???8000+&6$2?#3#7???8000$2?#7???8000$1<$1=$1>$1?,,3=!$24#100,8+$50#4000%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????60&$32#20($32##38!$32#18,8$25'$25#1000#7???????<000!$32#8,8+$2?#20!$32#10,8$2?!$32#30,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##38$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##38$2?##80)$32##38$30##1)$2?##80##10000#125044!$2?#20,8#4000'$2=#69<000#7????????>?0&$2=#8)##7???7000#100000001000$2=##110#&6$2=#3#7???8000#22($2=##110)$24##128$2=##110)$32##38$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#13;538!$2=#10,8#13;448!$2=#98,4#!$2=#9<,4#!$2=#:0,8+$2=#10###8001?6:4#1###8001?691#1)$2=##110$2?##80)$2=##110$30##1)&6$2?#3#7???8000#10&6$2=#3#7???8000#22)&6$2?#3#7???8000#10##8001?6:4#1)&6$2?#3#7???8000#10##8001?691#1,51!"%pstring).
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
End LibSegEb_bsrXge.
