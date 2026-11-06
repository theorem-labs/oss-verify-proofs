(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Eb0PlanKit Eb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndT_Eb_002S9 BndT_Eb_000S9.

Module LibSegEb_bqNaR0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_e4ea5f.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT.
Definition ENDS : list Z := [704116].
Definition STOPS1 : list Z := [704116] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$37$38$39$=$>$?$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",30%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#18,8$26'$26#1000#800000000000!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<!$:#20,8$26"%pstring).
Definition ss0 : sym_state := SS 703824 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:;>74#:;>74#5=#:;>74,20#$40$2$3$4$5$6$7$41$42#1$26$39$=$>$?$10$11$43$44$45$46$47$48$49$4:$4;$4<$1<$1=$1>$1?,,3?!$30#,1#!&6$2?#3#7???800;,1^#?#??????????????5!&6$2?#3#7???800:,1^#?#??????????????5!&6$2?#3#7???8009,1^#?#??????????????5!&6$2?#3#7???8008,1^#?#??????????????5!&6$2?#3#7???800?,1^#?#??????????????5!&6$2?#3#7???800>,1^#?#??????????????5!&6$2?#3#7???800=,1^#?#??????????????5!&6$2?#3#7???800<,1^#?#??????????????5!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#8#78($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#18,8$26'$26#1000#800000000000!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<!$:#20,8$26,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 704116 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 703824 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 703824 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNaR0.

Module LibSegEb_bqNaR1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_e4ea5f.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT.
Definition ENDS : list Z := [704116].
Definition STOPS1 : list Z := [704116] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$37$38$39$=$>$?$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3=%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#18,8$26'$26#1000#800000000000!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<!$:#20,8$33'$33#1018#800000000000&$33#8'+$33@-1$26#18#186:0($33-8#8)##7???7000#100000001000+$33-8##8#&6+$33-8#3#7???8000#1)$33-8#8$2-80#80)$33-8#8$:##38)$33-8#8$2?##80)$33-8#8$30##1)&6+$33-8#3#7???8000#1&6$2?#3#7???8000#10!$33-8,8$2:'$2:#^#?#??????????????>"%pstring).
Definition ss0 : sym_state := SS 703824 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 51), (-8), ELit 8); ((EVar 47), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16); ((EVar 48), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 51), (-8), 8); ((EVar 47), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16); ((EVar 48), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:;>74#:;>74#5=#:;>74,20#$40$2$3$4$5$6$7$41$42#1+$2:#1$39$=$>$?$10$11$43$44$45$46$47$48$49$4:$4;$4<$1<$1=$1>$1?,,4<!$30#,1#!&6$2?#3#7???800;,1^#?#??????????????5!&6$2?#3#7???800:,1^#?#??????????????5!&6$2?#3#7???8009,1^#?#??????????????5!&6$2?#3#7???8008,1^#?#??????????????5!&6$2?#3#7???800?,1^#?#??????????????5!&6$2?#3#7???800>,1^#?#??????????????5!&6$2?#3#7???800=,1^#?#??????????????5!&6$2?#3#7???800<,1^#?#??????????????5!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$33-8,8+$2:#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#8#78($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#18,8$26'$26#1000#800000000000!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<!$:#20,8$33'$33#1018#800000000000&$33#8'+$33@-1$26#18#186:0($33-8#8)##7???7000#100000001000+$33-8##8#&6+$33-8#3#7???8000#1)$33-8#8$2-80#80)$33-8#8$:##38)$33-8#8$2?##80)$33-8#8$30##1)&6+$33-8#3#7???8000#1&6$2?#3#7???8000#10'$2:#^#?#??????????????>,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 704116 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 703824 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 703824 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNaR1.

Module LibSegEb_bqNaR1w.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_e4ea5f.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT.
Definition ENDS : list Z := [704116].
Definition STOPS1 : list Z := [704116] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$37$38$39$=$>$?$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3<%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#18,8$26'$26#1000#800000000000!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<!$:#20,8$33'$33#1018#800000000000&$33#8'+$33@-1$26#18#186:0($33-8#8)##7???7000#100000001000+$33-8##8#&6+$33-8#3#7???8000#1)$33-8#8$2-80#80)$33-8#8$:##38)$33-8#8$2?##80)$33-8#8$30##1)&6+$33-8#3#7???8000#1&6$2?#3#7???8000#10!$33-8,8^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 703824 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 51), (-8), ELit 8); ((EVar 47), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 16); ((EVar 48), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 51), (-8), 8); ((EVar 47), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 16); ((EVar 48), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:;>74#:;>74#5=#:;>74,20#$40$2$3$4$5$6$7$41$42#1#$39$=$>$?$10$11$43$44$45$46$47$48$49$4:$4;$4<$1<$1=$1>$1?,,4;!$30#,1#!&6$2?#3#7???800;,1^#?#??????????????5!&6$2?#3#7???800:,1^#?#??????????????5!&6$2?#3#7???8009,1^#?#??????????????5!&6$2?#3#7???8008,1^#?#??????????????5!&6$2?#3#7???800?,1^#?#??????????????5!&6$2?#3#7???800>,1^#?#??????????????5!&6$2?#3#7???800=,1^#?#??????????????5!&6$2?#3#7???800<,1^#?#??????????????5!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$33-8,8#'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#8#78($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#18,8$26'$26#1000#800000000000!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<!$:#20,8$33'$33#1018#800000000000&$33#8'+$33@-1$26#18#186:0($33-8#8)##7???7000#100000001000+$33-8##8#&6+$33-8#3#7???8000#1)$33-8#8$2-80#80)$33-8#8$:##38)$33-8#8$2?##80)$33-8#8$30##1)&6+$33-8#3#7???8000#1&6$2?#3#7???8000#10,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 704116 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 703824 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 703824 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNaR1w.

Module LibSegEb_bqNaX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_002S9.SegItab_Eb_e4ea5f.ITR.
Definition IT : itab := BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT.
Definition ENDS : list Z := [704116].
Definition STOPS1 : list Z := [704116] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$37$38$39$=$>$?$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",25%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<"%pstring).
Definition ss0 : sym_state := SS 703784 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:;>74#:;>74#5=#:;>74,20#$40$2$3$4$5$6$7$41$42#1$38$39$=$>$?$10$11$43$44$45$46$47$48$49$4:$4;$4<$1<$1=$1>$1?,,34!$30#,1#!&6$2?#3#7???800;,1^#?#??????????????5!&6$2?#3#7???800:,1^#?#??????????????5!&6$2?#3#7???8009,1^#?#??????????????5!&6$2?#3#7???8008,1^#?#??????????????5!&6$2?#3#7???800?,1^#?#??????????????5!&6$2?#3#7???800>,1^#?#??????????????5!&6$2?#3#7???800=,1^#?#??????????????5!&6$2?#3#7???800<,1^#?#??????????????5!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#8#78($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8!$2-8,8$40!$2-10,8$41!$2-18,8$42!$2-20,8$43!$2-28,8$44!$2-30,8$45!$2-38,8$46!$2-40,8$47!$2-48,8$48!$2-50,8$49!$2-58,8$4:!$2-60,8$4;!$2-68,8$4<,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 704116 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 703784 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT BndT_Eb_002S9.SegItab_Eb_e4ea5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 703784 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNaX.

Module LibSegEb_bqNoA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_51cd55.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_51cd55.IT.
Definition ENDS : list Z := [388528].
Definition STOPS1 : list Z := [388528] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 1273856 1306624;
   KWord (SA (ELit 0) 1335544) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1335552) 4 (ELit 1);
   KRange (EVar 2) 140735332487296 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-128)) (ELit 128)].
Definition ss0 : sym_state := SS 707852 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#5>=;0#5>=;0#5=#5>=;0,20##:<=80+$2-80$3$4$5$6$7$2+$2-80#60#1460?8#1$=$>$?$10$11$12$<$14$:$16$17$18#7???8000$1:$1;$1<$1=$1>$1?,,14!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1!$2-80,8#%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 388528 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_51cd55.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 707852 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_51cd55.IT BndT_Eb_000S9.SegItab_Eb_51cd55.IT_sound BF NX0 BR XSTEP F0 PSS plan 707852 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNoA.

Module LibSegEb_bqNoDeq0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_51cd55.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_51cd55.IT.
Definition ENDS : list Z := [708412].
Definition STOPS1 : list Z := [708412] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$2?$38$39$=$>$?$10$11$12$<$14$:$16$17$18#7???8000$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",39%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8!$:#30,4$2;'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#!$27-10,8$2>'$2>##1000000!$27-8,8$2>"%pstring).
Definition ss0 : sym_state := SS 707968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-120), ELit 8); ((EVar 47), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 12); ((EVar 10), (48), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-120), 8); ((EVar 47), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 12); ((EVar 10), (48), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:<?3<#:<?3<#5=#:<?3<,20#$1+$2-80$3$4$5$6$7$2+$2-80$2>$2>##$2;^#?#??????????????1$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?,,46!$:#30,4+$2;-1!$2-78,8$2?!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????3!&6$2?#3#7???8007,1^#?#??????????????3!&6$2?#3#7???8006,1^#?#??????????????8!&6$2?#3#7???8005,1^#?#??????????????8!&6$2?#3#7???8004,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!$2?#10,8#:<=0<!$2?#8,8#126?7!$2?#,8#41;58:;3'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#18#68($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#!$27-10,8$2>'$2>##1000000!$27-8,8$2>,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 708412 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_51cd55.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 707968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_51cd55.IT BndT_Eb_000S9.SegItab_Eb_51cd55.IT_sound BF NX0 BR XSTEP F0 PSS plan 707968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNoDeq0.

Module LibSegEb_bqNoDeq2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_51cd55.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_51cd55.IT.
Definition ENDS : list Z := [708412].
Definition STOPS1 : list Z := [708412] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$2?$38$39$=$>$?$10$11$12$<$14$:$16$17$18#7???8000$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",39%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8!$:#30,4$2;'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#2!$27-10,8$2>'$2>##1000000!$27-8,8$2>"%pstring).
Definition ss0 : sym_state := SS 707968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-120), ELit 8); ((EVar 47), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 12); ((EVar 10), (48), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-120), 8); ((EVar 47), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 12); ((EVar 10), (48), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:<?3<#:<?3<#5=#:<?3<,20#$1+$2-80$3$4$5$6$7$2+$2-80$2>$2>##$2;^#?#??????????????1$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?,,46!$:#30,4+$2;-1!$2-78,8$2?!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????3!&6$2?#3#7???8007,1^#?#??????????????3!&6$2?#3#7???8006,1^#?#??????????????8!&6$2?#3#7???8005,1^#?#??????????????8!&6$2?#3#7???8004,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!$2?#10,8#:<=0<!$2?#8,8#126?7!$2?#,8#41;58:;3'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#18#68($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#2!$27-10,8$2>'$2>##1000000!$27-8,8$2>,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 708412 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_51cd55.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 707968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_51cd55.IT BndT_Eb_000S9.SegItab_Eb_51cd55.IT_sound BF NX0 BR XSTEP F0 PSS plan 707968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNoDeq2.

Module LibSegEb_bqNoDgt0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_51cd55.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_51cd55.IT.
Definition ENDS : list Z := [720296].
Definition STOPS1 : list Z := [720296] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$2?$38$39$=$>$?$10$11$12$<$14$:$16$17$18#7???8000$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3:%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8!$:#30,4$2;'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#!$27-10,8$2>'$2>##1000000!$27-8,8+$2>$34'$34#1^#?#????????>??????"%pstring).
Definition ss0 : sym_state := SS 707968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-120), ELit 8); ((EVar 47), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 12); ((EVar 10), (48), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-120), 8); ((EVar 47), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 12); ((EVar 10), (48), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?=:8#:?=:8#5=#:?=:8,20##:<?38+$2-80$3$4$5$6$7$2+$2-80$<#8##$2;^#?#??????????????1$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?,,47!$:#30,4+$2;-1!$2-78,8$2?!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????3!&6$2?#3#7???8007,1^#?#??????????????3!&6$2?#3#7???8006,1^#?#??????????????8!&6$2?#3#7???8005,1^#?#??????????????8!&6$2?#3#7???8004,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!$2?#10,8#:<=0<!$2?#8,8#126?7!$2?#,8#41;58:;3'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#18#68($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#!$27-10,8$2>'$2>##1000000!$27-8,8+$2>$34'$34#1^#?#????????>??????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 720296 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_51cd55.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 707968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_51cd55.IT BndT_Eb_000S9.SegItab_Eb_51cd55.IT_sound BF NX0 BR XSTEP F0 PSS plan 707968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNoDgt0.

Module LibSegEb_bqNoDgt2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_51cd55.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_51cd55.IT.
Definition ENDS : list Z := [720296].
Definition STOPS1 : list Z := [720296] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$2?$38$39$=$>$?$10$11$12$<$14$:$16$17$18#7???8000$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3:%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8!$:#30,4$2;'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#2!$27-10,8$2>'$2>##1000000!$27-8,8+$2>$34'$34#1^#?#????????>??????"%pstring).
Definition ss0 : sym_state := SS 707968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-120), ELit 8); ((EVar 47), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 12); ((EVar 10), (48), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-120), 8); ((EVar 47), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 12); ((EVar 10), (48), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?=:8#:?=:8#5=#:?=:8,20##:<?38+$2-80$3$4$5$6$7$2+$2-80$<#8##$2;^#?#??????????????1$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?,,47!$:#30,4+$2;-1!$2-78,8$2?!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????3!&6$2?#3#7???8007,1^#?#??????????????3!&6$2?#3#7???8006,1^#?#??????????????8!&6$2?#3#7???8005,1^#?#??????????????8!&6$2?#3#7???8004,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!$2?#10,8#:<=0<!$2?#8,8#126?7!$2?#,8#41;58:;3'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#18#68($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#2!$27-10,8$2>'$2>##1000000!$27-8,8+$2>$34'$34#1^#?#????????>??????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 720296 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_51cd55.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 707968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_51cd55.IT BndT_Eb_000S9.SegItab_Eb_51cd55.IT_sound BF NX0 BR XSTEP F0 PSS plan 707968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNoDgt2.

Module LibSegEb_bqNoDgth0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_51cd55.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_51cd55.IT.
Definition ENDS : list Z := [720296].
Definition STOPS1 : list Z := [720296] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$2?$38$39$=$>$?$10$11$12$<$14$:$16$17$18#7???8000$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3:%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8!$:#30,4$2;'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#!$27-10,8$2>'$2>##1000000!$27-8,8$2:'$2:^#?#?????????000000^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 707968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-120), ELit 8); ((EVar 47), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 12); ((EVar 10), (48), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-120), 8); ((EVar 47), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 12); ((EVar 10), (48), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?=:8#:?=:8#5=#:?=:8,20##:<?38+$2-80$3$4$5$6$7$2+$2-80$<#8##$2;^#?#??????????????1$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?,,47!$:#30,4+$2;-1!$2-78,8$2?!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????3!&6$2?#3#7???8007,1^#?#??????????????3!&6$2?#3#7???8006,1^#?#??????????????8!&6$2?#3#7???8005,1^#?#??????????????8!&6$2?#3#7???8004,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!$2?#10,8#:<=0<!$2?#8,8#126?7!$2?#,8#41;58:;3'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#18#68($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#!$27-10,8$2>'$2>##1000000!$27-8,8$2:'$2:^#?#?????????000000^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 720296 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_51cd55.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 707968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_51cd55.IT BndT_Eb_000S9.SegItab_Eb_51cd55.IT_sound BF NX0 BR XSTEP F0 PSS plan 707968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNoDgth0.

Module LibSegEb_bqNoDgth2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_51cd55.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_51cd55.IT.
Definition ENDS : list Z := [720296].
Definition STOPS1 : list Z := [720296] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$2?$38$39$=$>$?$10$11$12$<$14$:$16$17$18#7???8000$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3:%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8!$:#30,4$2;'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#2!$27-10,8$2>'$2>##1000000!$27-8,8$2:'$2:^#?#?????????000000^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 707968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-120), ELit 8); ((EVar 47), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 12); ((EVar 10), (48), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-120), 8); ((EVar 47), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 12); ((EVar 10), (48), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?=:8#:?=:8#5=#:?=:8,20##:<?38+$2-80$3$4$5$6$7$2+$2-80$<#8##$2;^#?#??????????????1$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?,,47!$:#30,4+$2;-1!$2-78,8$2?!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????3!&6$2?#3#7???8007,1^#?#??????????????3!&6$2?#3#7???8006,1^#?#??????????????8!&6$2?#3#7???8005,1^#?#??????????????8!&6$2?#3#7???8004,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!$2?#10,8#:<=0<!$2?#8,8#126?7!$2?#,8#41;58:;3'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#18#68($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#2!$27-10,8$2>'$2>##1000000!$27-8,8$2:'$2:^#?#?????????000000^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 720296 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_51cd55.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 707968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_51cd55.IT BndT_Eb_000S9.SegItab_Eb_51cd55.IT_sound BF NX0 BR XSTEP F0 PSS plan 707968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNoDgth2.

Module LibSegEb_bqNoDi1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_51cd55.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_51cd55.IT.
Definition ENDS : list Z := [725516].
Definition STOPS1 : list Z := [725516] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$2?$38$39$=$>$?$10$11$12$<$14$:$16$17$18#7???8000$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",36%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8!$:#30,4$2;'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#1"%pstring).
Definition ss0 : sym_state := SS 707968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-120), ELit 8); ((EVar 47), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 12); ((EVar 10), (48), ELit 4); ((EVar 2), (-105), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-120), 8); ((EVar 47), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 12); ((EVar 10), (48), 4); ((EVar 2), (-105), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;120<#;120<#5=#;120<,20##:<>>8+$2-80$3$4$5$6$7$2+$2-80$29+$2-69#1#$2;^#?#??????????????1$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?,,44!$2-69,1#7=!$:#30,4+$2;-1!$2-78,8$2?!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????3!&6$2?#3#7???8007,1^#?#??????????????3!&6$2?#3#7???8006,1^#?#??????????????8!&6$2?#3#7???8005,1^#?#??????????????8!&6$2?#3#7???8004,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!$2?#10,8#:<=0<!$2?#8,8#126?7!$2?#,8#41;58:;3'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#18#68($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 725516 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_51cd55.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 707968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_51cd55.IT BndT_Eb_000S9.SegItab_Eb_51cd55.IT_sound BF NX0 BR XSTEP F0 PSS plan 707968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNoDi1.

Module LibSegEb_bqNoDi3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_51cd55.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_51cd55.IT.
Definition ENDS : list Z := [725516].
Definition STOPS1 : list Z := [725516] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$2?$38$39$=$>$?$10$11$12$<$14$:$16$17$18#7???8000$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",36%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8!$:#30,4$2;'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#3"%pstring).
Definition ss0 : sym_state := SS 707968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-120), ELit 8); ((EVar 47), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 12); ((EVar 10), (48), ELit 4); ((EVar 2), (-105), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-120), 8); ((EVar 47), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 12); ((EVar 10), (48), 4); ((EVar 2), (-105), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;120<#;120<#5=#;120<,20##:<>>8+$2-80$3$4$5$6$7$2+$2-80$29+$2-69#1#$2;^#?#??????????????1$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?,,44!$2-69,1#7=!$:#30,4+$2;-1!$2-78,8$2?!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????3!&6$2?#3#7???8007,1^#?#??????????????3!&6$2?#3#7???8006,1^#?#??????????????8!&6$2?#3#7???8005,1^#?#??????????????8!&6$2?#3#7???8004,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!$2?#10,8#:<=0<!$2?#8,8#126?7!$2?#,8#41;58:;3'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#18#68($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#3,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 725516 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_51cd55.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 707968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_51cd55.IT BndT_Eb_000S9.SegItab_Eb_51cd55.IT_sound BF NX0 BR XSTEP F0 PSS plan 707968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNoDi3.

Module LibSegEb_bqNoDlt0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000S9.SegItab_Eb_51cd55.ITR.
Definition IT : itab := BndT_Eb_000S9.SegItab_Eb_51cd55.IT.
Definition ENDS : list Z := [720296].
Definition STOPS1 : list Z := [720296] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2+$2-80$2?$38$39$=$>$?$10$11$12$<$14$:$16$17$18#7???8000$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3;%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8!$:#30,4$2;'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#!$27-10,8$2>'$2>##1000000!$27-8,8$2:'$2:##??????'+$2>@-1$2:#1#1000000"%pstring).
Definition ss0 : sym_state := SS 707968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-120), ELit 8); ((EVar 47), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), ELit 12); ((EVar 10), (48), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-120), 8); ((EVar 47), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (0), 12); ((EVar 10), (48), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?=:8#:?=:8#5=#:?=:8,20##:<?38+$2-80$3$4$5$6$7$2+$2-80$<#9##$2;^#?#??????????????1$10$11$2?$<+$:#18$:+$:#20+&6$2?#3#7???8000$2?#7???8000+&6+$:#18#3#7???8000+&6+$:#20#3#7???8000$1<$1=$1>$1?,,48!$:#30,4+$2;-1!$2-78,8$2?!&6$2?#3#7???800;,1^#?#??????????????3!&6$2?#3#7???800:,1^#?#??????????????3!&6$2?#3#7???8009,1^#?#??????????????3!&6$2?#3#7???8008,1^#?#??????????????3!&6$2?#3#7???8007,1^#?#??????????????3!&6$2?#3#7???8006,1^#?#??????????????8!&6$2?#3#7???8005,1^#?#??????????????8!&6$2?#3#7???8004,1^#?#??????????????8!&6$2?#3#7???8003,1^#?#??????????????1!&6$2?#3#7???8002,1^#?#??????????????1!&6$2?#3#7???8001,1^#?#??????????????1!&6$2?#3#7???8000,1^#?#??????????????1!$2?#10,8#:<=0<!$2?#8,8#126?7!$2?#,8#41;58:;3'$2#7???7?801080#800000000000&$2#20($2-80#80'$2?#1000#7?????????80&$2?#20,$2?#18#68($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10#&6$2?#3#7???800<#4!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-80#80$2?##80)$2-80#80$30##1)$:##38$2?##80)$:##38$30##1)&6$:#3#7???8000#7&6$2?#3#7???8000#10'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-80#80$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1#&6+$:#30#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8'$2;#1#400!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8&$26#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-18#3#7???8000#3)$27-18#18$2-80#80)$27-18#18$:##38)$27-18#18$2?##80)$27-18#18$30##1)&6+$27-18#3#7???8000#3&6$2?#3#7???8000#10!$27-18,4#!$27-10,8$2>'$2>##1000000!$27-8,8$2:'$2:##??????'+$2>@-1$2:#1#1000000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 720296 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000S9.SegItab_Eb_51cd55.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 707968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000S9.SegItab_Eb_51cd55.IT BndT_Eb_000S9.SegItab_Eb_51cd55.IT_sound BF NX0 BR XSTEP F0 PSS plan 707968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bqNoDlt0.
