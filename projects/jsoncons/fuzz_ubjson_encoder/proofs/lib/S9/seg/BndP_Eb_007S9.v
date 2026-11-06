(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Eb0PlanKit Eb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndT_Eb_001S9 BndT_Eb_000S9.

Module LibSegEb_arkK2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_917df8.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_917df8.IT.
Definition ENDS : list Z := [757332].
Definition STOPS1 : list Z := [757332] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25$16$17$2?+&6$2?#3#7???8000#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2;'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 757416 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8>54#;8>54#5=#;8>54,20#$40$2$3$4$5$6$7$41$42$30#1#$=$>$?$10$11$43$44$45$46$47$48$49$4:$4;$1;$1<$1=$1>$1?,,36!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8'$2?#69<000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$24#10,1#,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 757332 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_917df8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 757416 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_917df8.IT BndT_Eb_001S9.SegItab_Eb_917df8.IT_sound BF NX0 BR XSTEP F0 PSS plan 757416 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arkK2.

Module LibSegEb_arkW.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_917df8.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_917df8.IT.
Definition ENDS : list Z := [757336; 720296].
Definition STOPS1 : list Z := [757336; 720296] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$35$<$=$>$?$10$11$2?$24$26$25$31$33$2?+&6$2?#3#7???8000#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 53) 0 6].
Definition ss0 : sym_state := SS 757092 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;8>58#:?=:8#;8>58#:?=:8#5;#;8=68,20#$1+$2-80$3$4$5$6$7$2+$2-80$:$35$<$=$>$?$10$11$2?$24$26$25$31$33$2?+&6$2?#3#7???8000#7???8000$1;$1<$1=$1>$1?,,1'$35##6,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;8>58#:?=:8#;8>58#:?=:8#5=#;8>58,20#$1+$2-80$3$4$5$6$7$2+$2-80$:$35$<$=$>$?$10$11$2?$24$26$25$31$33$2?+&6$2?#3#7???8000#7???8000$1;$1<$1=$1>$1?,,2'&4&1$35##1#1#1'$35##6,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;8>58#:?=:8#;8>58#:?=:8#5=#:?=:8,20##;8=78+$2-80$3$4$5$6$7$2+$2-80$26#7$<$=$>$?$10$11$2?$24$26$25$31$33$2?+&6$2?#3#7???8000#7???8000$1;$1<$1=$1>$1?,,2'&4&1$35##1##'$35##6,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 757336 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 720296 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_917df8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 757092 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_917df8.IT BndT_Eb_001S9.SegItab_Eb_917df8.IT_sound BF NX0 BR XSTEP F0 PSS plan 757092 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arkW.

Module LibSegEb_arkZ1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_917df8.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_917df8.IT.
Definition ENDS : list Z := [757332].
Definition STOPS1 : list Z := [757332] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25$16$17$2?+&6$2?#3#7???8000#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;"%pstring).
Definition ss0 : sym_state := SS 757156 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8>54#;8>54#5=#;8>54,20#$40$2$3$4$5$6$7$41$42$30#$<$=$>$?$10$11$43$44$45$46$47$48$49$4:$4;$1;$1<$1=$1>$1?,,35!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8'$2?#69<000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 757332 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_917df8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 757156 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_917df8.IT BndT_Eb_001S9.SegItab_Eb_917df8.IT_sound BF NX0 BR XSTEP F0 PSS plan 757156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arkZ1.

Module LibSegEb_arkZ12.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_917df8.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_917df8.IT.
Definition ENDS : list Z := [757332].
Definition STOPS1 : list Z := [757332] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25$16$17$2?+&6$2?#3#7???8000#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;"%pstring).
Definition ss0 : sym_state := SS 757508 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8>54#;8>54#5=#;8>54,20#$40$2$3$4$5$6$7$41$42$30#$<$=$>$?$10$11$43$44$45$46$47$48$49$4:$4;$1;$1<$1=$1>$1?,,35!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8'$2?#69<000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 757332 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_917df8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 757508 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_917df8.IT BndT_Eb_001S9.SegItab_Eb_917df8.IT_sound BF NX0 BR XSTEP F0 PSS plan 757508 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arkZ12.

Module LibSegEb_arkZ7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_917df8.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_917df8.IT.
Definition ENDS : list Z := [757332].
Definition STOPS1 : list Z := [757332] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$:$;$<$=$>$?$10$11$2?$24$26$25$16$17$2?+&6$2?#3#7???8000#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;"%pstring).
Definition ss0 : sym_state := SS 757112 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8>54#;8>54#5=#;8>54,20#$40$2$3$4$5$6$7$41$42$30#$<$=$>$?$10$11$43$44$45$46$47$48$49$4:$4;$1;$1<$1=$1>$1?,,35!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#'$2#7???7?801080#800000000000&$2#20($2-80#80'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-80#80$24##180)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8'$2?#69<000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-80#80$2?##40)$2-80#80$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 757332 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_917df8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 757112 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_917df8.IT BndT_Eb_001S9.SegItab_Eb_917df8.IT_sound BF NX0 BR XSTEP F0 PSS plan 757112 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arkZ7.

Module LibSegEb_arpA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bd2b13.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bd2b13.IT.
Definition ENDS : list Z := [764240; 763924; 763856; 763732].
Definition STOPS1 : list Z := [764240; 763924; 763856; 763732] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 38; EVar 37; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 763636 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-80), ELit 80)].
Definition F0L : list SR.region := [((EVar 2), (-80), 80)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#;:950#;:814#;:7=0#;:754#;:950#;:814#;:7=0#;:754#5;#;:71<,20#$1+$2-50$3$4$5$6$7$8$9$24$26$25$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#;:950#;:814#;:7=0#;:754#;:950#;:814#;:7=0#;:754#5=#;:950,20#$1$2$3$4$5$6$7$8$9##$25$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,19'&4&1$26##1#1#1!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#;:950#;:814#;:7=0#;:754#;:950#;:814#;:7=0#;:754#5;#;:750,20#$1+$2-50$3$4$5$6$7$26$25$21$26$25$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,19'&4&1$26##1##!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#;:950#;:814#;:7=0#;:754#;:950#;:814#;:7=0#;:754#5=#;:754,20#$1+$2-50$3$4$5$6$7$26$25$21$26$25$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1:'&4&1$21##1#1#1'&4&1$26##1##!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#;:950#;:814#;:7=0#;:754#;:950#;:814#;:7=0#;:754#5;#;:7<<,20#$1+$2-50$3$4$5$6$7$26$25#$26$21$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1:'&4&1$21##1##'&4&1$26##1##!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.

Definition ex9 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#;:950#;:814#;:7=0#;:754#;:950#;:814#;:7=0#;:754#5=#;:7=0,20#$1+$2-50$3$4$5$6$7$26$25#$26$21$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1;'&4$21$26#1#1'&4&1$21##1##'&4&1$26##1##!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s9 : sym_state := snd (snd ex9).

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#;:950#;:814#;:7=0#;:754#;:950#;:814#;:7=0#;:754#5=#;:814,20#$1+$2-50$3$4$5$6$7$26$25#$26$21$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1;'&4$21$26##'&4&1$21##1##'&4&1$26##1##!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8$21'$21##4000'$26#^#?#???????????????,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 3)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 2)) (SGA.mkplan (fst ex10) (SGP.PEnd 1))))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 764240 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s10).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s10).
Definition ps1 : SR.post_spec := SR.PS 763924 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s9).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s9).
Definition ps2 : SR.post_spec := SR.PS 763856 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s6).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s6).
Definition ps3 : SR.post_spec := SR.PS 763732 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bd2b13.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 763636 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bd2b13.IT BndT_Eb_001S9.SegItab_Eb_bd2b13.IT_sound BF NX0 BR XSTEP F0 PSS plan 763636 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arpA.

Module LibSegEb_arpB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bd2b13.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bd2b13.IT.
Definition ENDS : list Z := [763856; 763924].
Definition STOPS1 : list Z := [763856; 763924] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$26$25$2;$;$<$=$>$?$10$11$24+$24#120+$24#108#7???8000+&6+$24#120#3#7???8000+&6+$24#108#3#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#108,8$22'$2;##4000'$26#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 763792 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (280), ELit 16)].
Definition F0L : list SR.region := [((EVar 36), (280), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;:7=0#;:814#;:7=0#;:814#5;#;:7<<,20#$1+$2-50$3$4$5$6$7$26$25#$22$2;$=$>$?$10$11$24+$24#120+$24#108#7???8000+&6+$24#120#3#7???8000+&6+$24#108#3#7???8000$18$19$1:$1;$1<$1=$1>$1?,,11!$24#118,8$22!$24#120,8$2;%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#108,8$22'$2;##4000'$26#1^#?#???????????????,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;:7=0#;:814#;:7=0#;:814#5=#;:7=0,20#$1+$2-50$3$4$5$6$7$26$25#$22$2;$=$>$?$10$11$24+$24#120+$24#108#7???8000+&6+$24#120#3#7???8000+&6+$24#108#3#7???8000$18$19$1:$1;$1<$1=$1>$1?,,12'&4$2;$26#1#1!$24#118,8$22!$24#120,8$2;%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#108,8$22'$2;##4000'$26#1^#?#???????????????,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;:7=0#;:814#;:7=0#;:814#5=#;:814,20#$1+$2-50$3$4$5$6$7$26$25#$22$2;$=$>$?$10$11$24+$24#120+$24#108#7???8000+&6+$24#120#3#7???8000+&6+$24#108#3#7???8000$18$19$1:$1;$1<$1=$1>$1?,,12'&4$2;$26##!$24#118,8$22!$24#120,8$2;%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#108,8$22'$2;##4000'$26#1^#?#???????????????,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 763856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 763924 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bd2b13.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 763792 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bd2b13.IT BndT_Eb_001S9.SegItab_Eb_bd2b13.IT_sound BF NX0 BR XSTEP F0 PSS plan 763792 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arpB.

Module LibSegEb_arpEL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bd2b13.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bd2b13.IT.
Definition ENDS : list Z := [764240].
Definition STOPS1 : list Z := [764240] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$26$25$:$;$<$=$>$?$10$11$24+&6$25#3#7???8000$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128'$25#69<000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-50#50$25##18)$24##128$25##18!$25#,1$27'$27##??'&9$27#1#1#1!$25#8,8$28!$25#10,8$29'$26#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 764116 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:950#;:950#5=#;:950,20#$2<$2$3$4$5$6$7$2=$2>$29$28$<$=$>$?$10$11$2?$30$31$32$33$34$18$19$1:$1;$1<$1=$1>$1?,,22%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128'$25#69<000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-50#50$25##18)$24##128$25##18!$25#,1$27'$27##??'&9$27#1#1#1!$25#8,8$28!$25#10,8$29'$26#1^#?#???????????????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764240 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bd2b13.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764116 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bd2b13.IT BndT_Eb_001S9.SegItab_Eb_bd2b13.IT_sound BF NX0 BR XSTEP F0 PSS plan 764116 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arpEL.

Module LibSegEb_arpES.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bd2b13.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bd2b13.IT.
Definition ENDS : list Z := [764240].
Definition STOPS1 : list Z := [764240] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$26$25$:$;$<$=$>$?$10$11$24+&6$25#3#7???8000$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128'$25#69<000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-50#50$25##18)$24##128$25##18!$25#,1$27'$27##??'&9$27#1##'$26#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 764116 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:950#;:950#5=#;:950,20#$2<$2$3$4$5$6$7$2=$2>+$25#1&6$27#1$<$=$>$?$10$11$2?$30$31$32$33$34$18$19$1:$1;$1<$1=$1>$1?,,20%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128'$25#69<000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-50#50$25##18)$24##128$25##18!$25#,1$27'$27##??'&9$27#1##'$26#1^#?#???????????????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764240 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bd2b13.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764116 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bd2b13.IT BndT_Eb_001S9.SegItab_Eb_bd2b13.IT_sound BF NX0 BR XSTEP F0 PSS plan 764116 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arpES.

Module LibSegEb_arpF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bd2b13.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bd2b13.IT.
Definition ENDS : list Z := [764240].
Definition STOPS1 : list Z := [764240] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$26$25$:$;$21$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 2) 140735332487248 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-80)) (ELit 80);
   KWord (SA (EVar 2) (-8)) 8 (EVar 44);
   KWord (SA (EVar 2) (-16)) 8 (EVar 45);
   KWord (SA (EVar 2) (-24)) 8 (EVar 46);
   KWord (SA (EVar 2) (-32)) 8 (EVar 47);
   KWord (SA (EVar 2) (-40)) 8 (EVar 48);
   KWord (SA (EVar 2) (-48)) 8 (EVar 49);
   KWord (SA (EVar 2) (-56)) 8 (EVar 50);
   KWord (SA (EVar 2) (-64)) 8 (EVar 51);
   KWord (SA (EVar 2) (-72)) 8 (EVar 52);
   KRange (EVar 36) 6930432 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) 0) (ELit 296);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 36) (ELit (8))) (ELit 3)) 2147450880) (ELit 36);
   KWr (SA (EVar 36) 0) (ELit 296);
   KDisj (SA (EVar 2) (-80)) (ELit 80) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (280)) 8 (EVar 35);
   KRange (EVar 35) 1 140737488355328;
   KUnk (SA (EVar 36) 256) (ELit 8);
   KRange (EVar 33) 1 16384;
   KRange (EVar 38) 1 16384;
   KRange (APC.esub (EVar 33) (EVar 38)) 0 16383].
Definition ss0 : sym_state := SS 763924 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (256), ELit 8); ((EVar 36), (280), ELit 16)].
Definition F0L : list SR.region := [((EVar 36), (256), 8); ((EVar 36), (280), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:950#;:950#5=#;:950,20#$2<$2$3$4$5$6$7$2=$2>$23$26+$26$3<#+$23$26$?$10$11$2?$30$31$32$33$34$18$19$1:$1;$1<$1=$1>$1?,,1<!$24#100,8+$26$3<!$24#120,8+$21@-1$26!$24#118,8+$23$26%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128'$23#1#800000000000'$21#1#4000'$26#1#4000'+$21@-1$26##3???,3=!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764240 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bd2b13.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 763924 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bd2b13.IT BndT_Eb_001S9.SegItab_Eb_bd2b13.IT_sound BF NX0 BR XSTEP F0 PSS plan 763924 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arpF.

Module LibSegEb_arpR0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bd2b13.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bd2b13.IT.
Definition ENDS : list Z := [763856; 760132].
Definition STOPS1 : list Z := [763856; 760132] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$26$25$:$;$<$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8#!$24#110,8#4000!$24#108,8$22'$26#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 763732 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;:7=0#;9944#;:7=0#;9944#5;#;:76<,20#$1+$2-50$3$4$5$6$7$26$25+$24#110##4000$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,10%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8#!$24#110,8#4000!$24#108,8$22'$26#1^#?#???????????????,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;:7=0#;9944#;:7=0#;9944#5=#;:7=0,20#$1+$2-50$3$4$5$6$7$26$25###$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,11'&4#4000$26#1#1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8#!$24#110,8#4000!$24#108,8$22'$26#1^#?#???????????????,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;:7=0#;9944#;:7=0#;9944#5=#;9944,20##;:790+$2-50$3$4$5$6$7$26$25$24$22#4000$=$>$?$10$11$24+$24#120+$24#108#7???8000+&6+$24#120#3#7???8000+&6+$24#108#3#7???8000$18$19$1:$1;$1<$1=$1>$1?,,11'&4#4000$26##%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128!$24#120,8#!$24#110,8#4000!$24#108,8$22'$26#1^#?#???????????????,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 763856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 760132 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bd2b13.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 763732 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bd2b13.IT BndT_Eb_001S9.SegItab_Eb_bd2b13.IT_sound BF NX0 BR XSTEP F0 PSS plan 763732 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arpR0.

Module LibSegEb_arpSL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bd2b13.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bd2b13.IT.
Definition ENDS : list Z := [769184].
Definition STOPS1 : list Z := [769184] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$26$25$:$;$<$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128'$25#69<000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-50#50$25##18)$24##128$25##18!$25#,1$27'$27##??'&9$27#1#1#1!$25#8,8$28!$25#10,8$29'$29#1000#7??????????8&$29#8)##7???7000#100000001000$29##1#&6$29#3#7???8000#1($29##1)$2-50#50$29##1)$29##1$25##18)$29##1$24##128'$26#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 763856 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 41), (0), ELit 1); ((EVar 37), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 41), (0), 1); ((EVar 37), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;;<:0#;;<:0#5=#;;<:0,20##;:8=4+$2-50$3$4$5$6$7$26$25$24$25$26$=$>$?$10$11$24+&6$25#3#7???8000$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1?!$25#8,8#!$29#,1#'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128'$25#69<000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-50#50$25##18)$24##128$25##18!$25#,1$27'$27##??'&9$27#1#1#1!$25#10,8$29'$29#1000#7??????????8&$29#8)##7???7000#100000001000$29##1#&6$29#3#7???8000#1($29##1)$2-50#50$29##1)$29##1$25##18)$29##1$24##128'$26#1^#?#???????????????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 769184 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bd2b13.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 763856 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bd2b13.IT BndT_Eb_001S9.SegItab_Eb_bd2b13.IT_sound BF NX0 BR XSTEP F0 PSS plan 763856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arpSL.

Module LibSegEb_arpSS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001S9.SegItab_Eb_bd2b13.ITR.
Definition IT : itab := BndT_Eb_001S9.SegItab_Eb_bd2b13.IT.
Definition ENDS : list Z := [769184].
Definition STOPS1 : list Z := [769184] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$26$25$:$;$<$=$>$?$10$11$24+$24#120$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128'$25#69<000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-50#50$25##18)$24##128$25##18!$25#,1$27'$27##??'&9$27#1###&6+$25#1#3#7???8000#1'$26#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 763856 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 37), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 37), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;;<:0#;;<:0#5=#;;<:0,20##;:8=4+$2-50$3$4$5$6$7$26$25$24$25$26$=$>$?$10$11$24+&6$25#3#7???8000$14#7???8000+&6+$24#120#3#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,19!$25#,1#!$25#1,1#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$24#69<000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-50#50$24##128'$25#69<000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-50#50$25##18)$24##128$25##18'$27##??'&9$27#1###&6+$25#1#3#7???8000#1'$26#1^#?#???????????????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 769184 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001S9.SegItab_Eb_bd2b13.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 763856 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001S9.SegItab_Eb_bd2b13.IT BndT_Eb_001S9.SegItab_Eb_bd2b13.IT_sound BF NX0 BR XSTEP F0 PSS plan 763856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_arpSS.

Module LibSegEb_artA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_163e40.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_163e40.IT.
Definition ENDS : list Z := [388156].
Definition STOPS1 : list Z := [388156] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; EVar 38; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 2) 140735332487264 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-96)) (ELit 96)].
Definition ss0 : sym_state := SS 749324 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-96), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-96), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#5><3<#5><3<#5=#5><3<,20##;6?7<+$2-60$3$4$5$6$7$2+$2-60#40#1460?8#1$=$>$?$10$11$12$26$24$25$16$17$18#7???8000$1:$1;$1<$1=$1>$1?,,12!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1!$2-60,8#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801060#800000000000&$2#20($2-60#60,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 388156 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_163e40.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 749324 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_163e40.IT BndT_Eb_000S9.SegItab_Eb_163e40.IT_sound BF NX0 BR XSTEP F0 PSS plan 749324 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_artA.
