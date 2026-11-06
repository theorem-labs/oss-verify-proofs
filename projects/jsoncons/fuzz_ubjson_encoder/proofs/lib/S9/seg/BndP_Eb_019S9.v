(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Eb0PlanKit Eb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndT_Eb_001S9.

Module LibSegEb_bigB0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bf3e62.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bf3e62.IT.
Definition ENDS : list Z := [760132].
Definition STOPS1 : list Z := [760132] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 50; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EVar 50; EVar 47; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 36; EVar 20; EVar 21; EVar 22; ELit 1; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",24%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044"%pstring).
Definition ss0 : sym_state := SS 755764 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (0), ELit 88); ((EVar 47), (0), ELit 24); ((EVar 47), (32), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 50), (0), 88); ((EVar 47), (0), 24); ((EVar 47), (32), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9944#;9944#5=#;9944,20##;8:1<$32$3$4$2?$6$7$2$32$24$22#4000^#?#??????????????2^#?#??????????????1^#?#??????????????3$2?#7???8000+$2?#20$24+$24#120+$24#118+$24#100+&6+$24#118#3#7???8000+$2?#40+&6+$24#120#3#7???8000+&6$2?#3#7???8000#$1<$1=$1>$1?,,3=!$24#118,8$22!$32#18,8+&6+$24#100#3#7???8000!$32#20,8+&6+$24#110#3#7???8000!$32#28,8+&6+$24#108#3#7???8000!$32#,8+$24#110!$32#30,8+$24#108!$32#10,8$2?!$32#8,8$2?!$32#50,8$2?!$2?#20,8#1!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!&6$2?#3#7???8007,1^#?#??????????????2!&6$2?#3#7???8006,1^#?#??????????????2!&6$2?#3#7???8005,1^#?#??????????????2!&6$2?#3#7???8004,1#!$2?#10,8#;87;<!$2?#8,8#20?4<!$2?#,8#41;58:;3%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?#18#8,$2?#28#58($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bf3e62.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 755764 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bf3e62.IT BndT_Eb_001S9.SegItab_Eb_bf3e62.IT_sound BF NX0 BR XSTEP F0 PSS plan 755764 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bigB0.

Module LibSegEb_bigB1a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bf3e62.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bf3e62.IT.
Definition ENDS : list Z := [756428].
Definition STOPS1 : list Z := [756428] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 50; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EVar 50; EVar 47; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 36; EVar 20; EVar 21; EVar 22; ELit 1; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",25%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8#1'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044'$23#1000#7???????<000"%pstring).
Definition ss0 : sym_state := SS 755764 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (0), ELit 88); ((EVar 47), (0), ELit 24); ((EVar 47), (32), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 50), (0), 88); ((EVar 47), (0), 24); ((EVar 47), (32), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8:<<#;8:<<#5=#;8:<<,20#$1$32$3$4$2?$6$7$2$32#1#1+$23#1#1#^#?#??????????????3$2?#7???8000+$2?#20$24+$24#120+$24#118+$24#100#1$18+&6+$24#120#3#7???8000+&6$2?#3#7???8000#1$1<$1=$1>$1?,,39!$24#120,8#!$24#118,8+$23#1!$24#100,8+$50#1!$32#10,8$2?!$32#8,8$2?!$32#50,8$2?!$2?#20,8#1!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!&6$2?#3#7???8007,1^#?#??????????????2!&6$2?#3#7???8006,1^#?#??????????????2!&6$2?#3#7???8005,1^#?#??????????????2!&6$2?#3#7???8004,1#!$2?#10,8#;87;<!$2?#8,8#20?4<!$2?#,8#41;58:;3%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000'$2?#69<000#7?????????80&$2?#20,$2?#18#8,$2?#28#58($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044'$23#1000#7???????<000,51!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 756428 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bf3e62.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 755764 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bf3e62.IT BndT_Eb_001S9.SegItab_Eb_bf3e62.IT_sound BF NX0 BR XSTEP F0 PSS plan 755764 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bigB1a.

Module LibSegEb_bigB1b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bf3e62.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bf3e62.IT.
Definition ENDS : list Z := [755992].
Definition STOPS1 : list Z := [755992] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 50; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 2; EVar 50; EVar 47; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 36; EVar 20; EVar 21; EVar 22; ELit 1; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8$21'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044'$21#2#4000'$23#1000#7???????<000"%pstring).
Definition ss0 : sym_state := SS 755764 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (0), ELit 88); ((EVar 47), (0), ELit 24); ((EVar 47), (32), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 50), (0), 88); ((EVar 47), (0), 24); ((EVar 47), (32), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8918#;8918#5=#;8918,20#$1$32$3$4$2?$6$7$2$32+$2?#20$21#;87;<^#?#??????????????2^#?#??????????????1^#?#??????????????3$2?#7???8000+$2?#20$24+$24#120+$24#118+$24#100#1$18+&6+$24#120#3#7???8000+&6$2?#3#7???8000$1;$1<$1=$1>$1?,,3:!$32#10,8$2?!$32#8,8$2?!$32#50,8$2?!$2?#20,8#1!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!&6$2?#3#7???8007,1^#?#??????????????2!&6$2?#3#7???8006,1^#?#??????????????2!&6$2?#3#7???8005,1^#?#??????????????2!&6$2?#3#7???8004,1#!$2?#10,8#;87;<!$2?#8,8#20?4<!$2?#,8#41;58:;3%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8$21'$2?#69<000#7?????????80&$2?#20,$2?#18#8,$2?#28#58($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044'$21#2#4000'$23#1000#7???????<000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 755992 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bf3e62.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 755764 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bf3e62.IT BndT_Eb_001S9.SegItab_Eb_bf3e62.IT_sound BF NX0 BR XSTEP F0 PSS plan 755764 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bigB1b.

Module LibSegEb_bigB1b2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bf3e62.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bf3e62.IT.
Definition ENDS : list Z := [756428].
Definition STOPS1 : list Z := [756428] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32+$2?#20$21$<$=$>$?$10#7???8000+$2?#20$24+$24#120+$24#118+$24#100#1$18+&6+$24#120#3#7???8000+&6$2?#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$23!$24#120,8$21'$21#2#4000'$23#1000#7???????<000'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2?#20,8#1#&6+$2?#20#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 755992 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8:<<#;8:<<#5=#;8:<<,20#$1$32$3$4$5$6$7$2$32#1$21+$23#1#1#$?$10#7???8000+$2?#20$24+$24#120+$24#118+$24#100#1$18+&6+$24#120#3#7???8000+&6$2?#3#7???8000#1$1<$1=$1>$1?,,26!$24#120,8+$21-1!$24#118,8+$23#1!$24#100,8+$50#1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000'$21#2#4000'$23#1000#7???????<000'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2?#20,8#1#&6+$2?#20#3#7???8000#1,51!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 756428 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bf3e62.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 755992 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bf3e62.IT BndT_Eb_001S9.SegItab_Eb_bf3e62.IT_sound BF NX0 BR XSTEP F0 PSS plan 755992 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bigB1b2.

Module LibSegEb_bigC0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bf3e62.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bf3e62.IT.
Definition ENDS : list Z := [756428].
Definition STOPS1 : list Z := [756428] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32#$;$<$=$>$?$10$11+$2?#20$24+$24#120+$24#118+$24#100+&6+$24#118#3#7???8000+$2?#40+&6+$24#120#3#7???8000+&6$2?#3#7???8000#$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000!$32#,8+$24#110!$32#8,8$2?!$32#10,8$2?!$32#18,8+&6+$24#100#3#7???8000!$32#20,8+&6+$24#110#3#7???8000!$32#28,8+&6+$24#108#3#7???8000!$32#30,8+$24#108!$32#50,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$22!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2?#20,8#1!&6$2?#3#7???8004,1#!&6$2?#3#7???8008,1#?8"%pstring).
Definition ss0 : sym_state := SS 756252 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8:<<#;8:<<#5=#;8:<<,20#$1$32$3$4$5$6$7$2$32##$<#7???8000$>$?$10$11+$2?#20$24+$24#120+$24#118+$24#100+&6+$24#118#3#7???8000+$2?#40+&6+$24#120#3#7???8000+&6$2?#3#7???8000#$1<$1=$1>$1?,,2>!$24#120,8#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000!$32#,8+$24#110!$32#8,8$2?!$32#10,8$2?!$32#18,8+&6+$24#100#3#7???8000!$32#20,8+&6+$24#110#3#7???8000!$32#28,8+&6+$24#108#3#7???8000!$32#30,8+$24#108!$32#50,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$22'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2?#20,8#1!&6$2?#3#7???8004,1#!&6$2?#3#7???8008,1#?8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 756428 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bf3e62.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756252 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bf3e62.IT BndT_Eb_001S9.SegItab_Eb_bf3e62.IT_sound BF NX0 BR XSTEP F0 PSS plan 756252 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bigC0.

Module LibSegEb_bigC1a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bf3e62.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bf3e62.IT.
Definition ENDS : list Z := [756428].
Definition STOPS1 : list Z := [756428] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32#1$;$<$=$>$?$10$11+$2?#20$24+$24#120+$24#118+$24#100+&6+$24#118#3#7???8000+$2?#40+&6+$24#120#3#7???8000+&6$2?#3#7???8000#$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2?%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000!$32#,8+$24#110!$32#8,8$2?!$32#10,8$2?!$32#18,8+&6+$24#100#3#7???8000!$32#20,8+&6+$24#110#3#7???8000!$32#28,8+&6+$24#108#3#7???8000!$32#30,8+$24#108!$32#50,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$22!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2?#20,8#1!&6$2?#3#7???8004,1#!&6$2?#3#7???8008,1#?8'$22#1000#7???????<000"%pstring).
Definition ss0 : sym_state := SS 756252 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8:<<#;8:<<#5=#;8:<<,20#$1$32$3$4$5$6$7$2$32#1#1###$?$10$11+$2?#20$24+$24#120+$24#118+$24#100+&6+$24#118#3#7???8000+$2?#40+&6+$24#120#3#7???8000+&6$2?#3#7???8000#1$1<$1=$1>$1?,,31!$24#120,8#!$24#118,8+$22#1!$24#100,8+$50#1!&6$2?#3#7???8008,1^#?#??????????????8!$2?#40,8#1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000!$32#,8+$24#110!$32#8,8$2?!$32#10,8$2?!$32#18,8+&6+$24#100#3#7???8000!$32#20,8+&6+$24#110#3#7???8000!$32#28,8+&6+$24#108#3#7???8000!$32#30,8+$24#108!$32#50,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000'$2?#69<000#7?????????80&$2?#20,$2?##40,$2?#48#38($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2?#20,8#1!&6$2?#3#7???8004,1#'$22#1000#7???????<000,51!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 756428 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bf3e62.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756252 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bf3e62.IT BndT_Eb_001S9.SegItab_Eb_bf3e62.IT_sound BF NX0 BR XSTEP F0 PSS plan 756252 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bigC1a.

Module LibSegEb_bigC1b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bf3e62.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bf3e62.IT.
Definition ENDS : list Z := [756300].
Definition STOPS1 : list Z := [756300] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32$33$;$<$=$>$?$10$11+$2?#20$24+$24#120+$24#118+$24#100+&6+$24#118#3#7???8000+$2?#40+&6+$24#120#3#7???8000+&6$2?#3#7???8000#$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",30%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000!$32#,8+$24#110!$32#8,8$2?!$32#10,8$2?!$32#18,8+&6+$24#100#3#7???8000!$32#20,8+&6+$24#110#3#7???8000!$32#28,8+&6+$24#108#3#7???8000!$32#30,8+$24#108!$32#50,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$22!$24#120,8#'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2?#20,8#1!&6$2?#3#7???8004,1#!&6$2?#3#7???8008,1#?8'$33#2#4000'$22#1000#7???????<000"%pstring).
Definition ss0 : sym_state := SS 756252 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8:4<#;8:4<#5=#;8:4<,20#$1$32$3$4$5$6$7$2$32$33+$2?#40#1#7???8000$>$?$10$11+$2?#20$24+$24#120+$24#118+$24#100+&6+$24#118#3#7???8000+$2?#40+&6+$24#120#3#7???8000+&6$2?#3#7???8000#$1<$1=$1>$1?,,32!$2?#40,8#1!&6$2?#3#7???8008,1#!$24#120,8$33%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000!$32#,8+$24#110!$32#8,8$2?!$32#10,8$2?!$32#18,8+&6+$24#100#3#7???8000!$32#20,8+&6+$24#110#3#7???8000!$32#28,8+&6+$24#108#3#7???8000!$32#30,8+$24#108!$32#50,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$22'$2?#69<000#7?????????80&$2?#20,$2?##40,$2?#48#38($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2?#20,8#1!&6$2?#3#7???8004,1#'$33#2#4000'$22#1000#7???????<000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 756300 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bf3e62.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756252 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bf3e62.IT BndT_Eb_001S9.SegItab_Eb_bf3e62.IT_sound BF NX0 BR XSTEP F0 PSS plan 756252 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bigC1b.

Module LibSegEb_bigC1b2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bf3e62.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bf3e62.IT.
Definition ENDS : list Z := [756428].
Definition STOPS1 : list Z := [756428] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32$33+$2?#40#1#7???8000$>$?$10$11+$2?#20$24+$24#120+$24#118+$24#100+&6+$24#118#3#7???8000+$2?#40+&6+$24#120#3#7???8000+&6$2?#3#7???8000#$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",30%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000!$32#,8+$24#110!$32#8,8$2?!$32#10,8$2?!$32#18,8+&6+$24#100#3#7???8000!$32#20,8+&6+$24#110#3#7???8000!$32#28,8+&6+$24#108#3#7???8000!$32#30,8+$24#108!$32#50,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000,$24#100#8!$24#118,8$22!$24#120,8$33'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2?#20,8#1!$2?#40,8#1#&6+$2?#40#3#7???8000#1'$33#2#4000'$22#1000#7???????<000"%pstring).
Definition ss0 : sym_state := SS 756300 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8:<<#;8:<<#5=#;8:<<,20#$1$32$3$4$5$6$7$2$32#1#1###$?$10$11+$2?#20$24+$24#120+$24#118+$24#100+&6+$24#118#3#7???8000+$2?#40+&6+$24#120#3#7???8000+&6$2?#3#7???8000#1$1<$1=$1>$1?,,31!$24#120,8+$33-1!$24#118,8+$22#1!$24#100,8+$50#1!&6$2?#3#7???8008,1^#?#??????????????8%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$32#7???7?801000#7?????????40&$32#20($32##60!$32#38,8#7???8000!$32#,8+$24#110!$32#8,8$2?!$32#10,8$2?!$32#18,8+&6+$24#100#3#7???8000!$32#20,8+&6+$24#110#3#7???8000!$32#28,8+&6+$24#108#3#7???8000!$32#30,8+$24#108!$32#50,8$2?'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$32##60$24##128!$24#108,8$22!$24#110,8#4000'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2?#20,8#1!$2?#40,8#1#&6$2?#3#7???8009++@-1&6$2?#3&6+$2?#40#3-8'$33#2#4000'$22#1000#7???????<000,51!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 756428 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bf3e62.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756300 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bf3e62.IT BndT_Eb_001S9.SegItab_Eb_bf3e62.IT_sound BF NX0 BR XSTEP F0 PSS plan 756300 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bigC1b2.

Module LibSegEb_bigR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bf3e62.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bf3e62.IT.
Definition ENDS : list Z := [756640].
Definition STOPS1 : list Z := [756640] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$32$3$4$5$6$7$2$32$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19+&6$2?#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",29'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0'$32#7???7?801000#7?????????40&$32#20($32##60!$32#8,8$2?!$32#10,8$2?'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<)$2-68#68$2?##80)$2-68#68$30##1)$2-68#68&6$2?#3#7???8000#10"%pstring).
Definition ss0 : sym_state := SS 756428 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8;:0#;8;:0#5=#;8;:0,20#$40$2$3$4$5$6$7$41$42$30$2?$<$=$>$?$10$11$43$44$45$46$47$48$49$4:$4;$4<$1<$1=$1>$1?,,3;!$30#,1#!&6$2?#3#7???800;,1^#?#??????????????5!&6$2?#3#7???800:,1^#?#??????????????5!&6$2?#3#7???8009,1^#?#??????????????5!&6$2?#3#7???8008,1^#?#??????????????5!&6$2?#3#7???800?,1^#?#??????????????5!&6$2?#3#7???800>,1^#?#??????????????5!&6$2?#3#7???800=,1^#?#??????????????5!&6$2?#3#7???800<,1^#?#??????????????5!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>'$2#7???7?8010<0#800000000000&$2#10($2-<0#<0'$32#7???7?801000#7?????????40&$32#20($32##60!$32#8,8$2?!$32#10,8$2?'$2?#69<000#7?????????80&$2?#20,$2?#8#78($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$24##128$2?##80)$24##128$30##1)&6$24#3#7???8000#25&6$2?#3#7???8000#10)$32##60$2?##80)$32##60$30##1)$2?##80##10000#126044!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<)$2-68#68$2?##80)$2-68#68$30##1)$2-68#68&6$2?#3#7???8000#10,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 756640 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bf3e62.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756428 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bf3e62.IT BndT_Eb_001S9.SegItab_Eb_bf3e62.IT_sound BF NX0 BR XSTEP F0 PSS plan 756428 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bigR.

Module LibSegEb_blpA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [388528].
Definition STOPS1 : list Z := [388528] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; EVar 38; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1?%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10"%pstring).
Definition ss0 : sym_state := SS 745004 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-288), ELit 288)].
Definition F0L : list SR.region := [((EVar 2), (-288), 288)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#5>=;0#5>=;0#5=#5>=;0,20##;5>:4+$2-120$3$4$5$6$7$2+$2-120#60#1460?8#1$=$>$?$10$11$12$26$14$15$16$17$18$19$1:#7???8000$1<$1=$1>$1?,,2?!$2-98,8$24!$2-90,8$25!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1!$2-120,8#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 388528 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745004 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_c40876.IT BndT_Eb_001S9.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745004 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpA.

Module LibSegEb_blpB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [745500].
Definition STOPS1 : list Z := [745500] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$2?$;$<$=$>$?$10$11$12$26$14$15$16$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",48%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<!$24#9,1#!$2-90,8$25!$2-98,8$24"%pstring).
Definition ss0 : sym_state := SS 745124 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-288), ELit 288); ((EVar 47), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-288), 288); ((EVar 47), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;601<#;601<#5=#;601<,20#$1+$2-120$3$4$5$6$7$2+$2-120#+&6+$24#168#3#7???8000+&6+$24#148#3#7???8000+&6$26#3#7???8000#3+&6$25#3#7???8000+$24#168+$24#148#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,67!$2->0,8+&6+$24#148#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<0,8+$24#168!$2-100,8#3!$2-:0,8+&6$26#3#7???8000!$2-?0,8#!$2-;0,8#?>00!$2-?8,8#1!$2-:8,8+$24#18!$2-108,8+$2?#20!$2-70,8$2?!$2-;8,8$2?!$2-88,8+&6+$24#9#3#7???8000!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????3!&6$2?#3#7???8007,1^#?#??????????????3!&6$2?#3#7???8006,1^#?#??????????????8!&6$2?#3#7???8005,1^#?#??????????????8!&6$2?#3#7???8004,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!$2?#10,8#;5>2<!$2?#8,8#17<:?!$2?#,8#41;58:;3!$2->8,8$2?%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?#18#68($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<!$24#9,1#!$2-90,8$25!$2-98,8$24,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 745500 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745124 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_c40876.IT BndT_Eb_001S9.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745124 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpB.

Module LibSegEb_blpCE3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [747060].
Definition STOPS1 : list Z := [747060] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",49%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?"%pstring).
Definition ss0 : sym_state := SS 746064 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;6634#;6634#5=#;6634,20#$1+$2-120$3$4$5$6$7$2+$2-120#$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,49%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 747060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 746064 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_c40876.IT BndT_Eb_001S9.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 746064 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpCE3.

Module LibSegEb_blpCE9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [747060].
Definition STOPS1 : list Z := [747060] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",49%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?"%pstring).
Definition ss0 : sym_state := SS 745864 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;6634#;6634#5=#;6634,20#$1+$2-120$3$4$5$6$7$2+$2-120#$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,49%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 747060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745864 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_c40876.IT BndT_Eb_001S9.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745864 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpCE9.

Module LibSegEb_blpCR0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [747060].
Definition STOPS1 : list Z := [747060] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",49%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?"%pstring).
Definition ss0 : sym_state := SS 745640 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;6634#;6634#5=#;6634,20#$1+$2-120$3$4$5$6$7$2+$2-120#$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,49%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 747060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745640 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_c40876.IT BndT_Eb_001S9.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpCR0.
