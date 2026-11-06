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

Module LibSegEa_ahnJs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [692020].
Definition STOPS1 : list Z := [692020; 871008] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$28#3:0,1$24'$24##??'&9$24#1##"%pstring).
Definition ss0 : sym_state := SS 691992 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#:8?34#=4:60#:8?34#5=#:8?34,20#$3:+$2-:0$3$4$5$6$7$8+$2-:0#$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,13'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$28#3:0,1$24'$24##??'&9$24#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 692020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 691992 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 691992 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnJs.

Module LibSegEa_ahnK.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [695384].
Definition STOPS1 : list Z := [695384] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1"%pstring).
Definition ss0 : sym_state := SS 692020 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:9<58#:9<58#5=#:9<58,20##:8?3<+$2-:0$3$4$5$6$7$8+$2-:0+$28#268$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 695384 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692020 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692020 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnK.

Module LibSegEa_ahnL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [726028].
Definition STOPS1 : list Z := [726028] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1"%pstring).
Definition ss0 : sym_state := SS 692028 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450954), ELit 49); ((EVar 2), (-112), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450954), 49); ((EVar 2), (-112), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;140<#;140<#5=#;140<,20##:900<+$2-:0$3$4$5$6$7$8+$2-:0+$2-70$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,42!$2-70,8+$28#208!&6$28#3#7???807:,1^#?#??????????????8!&6$28#3#7???8075,1^#?#??????????????8!&6$28#3#7???8074,1^#?#??????????????8!&6$28#3#7???8073,1^#?#??????????????8!&6$28#3#7???8072,1^#?#??????????????8!&6$28#3#7???8079,1^#?#??????????????8!&6$28#3#7???8078,1^#?#??????????????8!&6$28#3#7???8077,1^#?#??????????????8!&6$28#3#7???8076,1^#?#??????????????8!&6$28#3#7???806=,1^#?#??????????????8!&6$28#3#7???806<,1^#?#??????????????8!&6$28#3#7???806;,1^#?#??????????????8!&6$28#3#7???806:,1^#?#??????????????8!&6$28#3#7???8071,1^#?#??????????????8!&6$28#3#7???8070,1^#?#??????????????8!&6$28#3#7???806?,1^#?#??????????????8!&6$28#3#7???806>,1^#?#??????????????8!&6$28#3#7???8065,1^#?#??????????????8!&6$28#3#7???8064,1^#?#??????????????8!&6$28#3#7???8063,1^#?#??????????????8!&6$28#3#7???8062,1^#?#??????????????8!&6$28#3#7???8069,1^#?#??????????????8!&6$28#3#7???8068,1^#?#??????????????8!&6$28#3#7???8067,1^#?#??????????????8!&6$28#3#7???8066,1^#?#??????????????8!&6$28#3#7???805=,1^#?#??????????????8!&6$28#3#7???805<,1^#?#??????????????8!&6$28#3#7???805;,1^#?#??????????????8!&6$28#3#7???805:,1^#?#??????????????8!&6$28#3#7???8061,1^#?#??????????????8!&6$28#3#7???8060,1^#?#??????????????8!&6$28#3#7???805?,1^#?#??????????????8!&6$28#3#7???805>,1^#?#??????????????8!&6$28#3#7???8055,1^#?#??????????????8!&6$28#3#7???8054,1^#?#??????????????8!&6$28#3#7???8053,1^#?#??????????????8!&6$28#3#7???8052,1^#?#??????????????8!&6$28#3#7???8059,1^#?#??????????????8!&6$28#3#7???8058,1^#?#??????????????8!&6$28#3#7???8057,1^#?#??????????????8!&6$28#3#7???8056,1^#?#??????????????8!&6$28#3#7???804=,1^#?#??????????????8!&6$28#3#7???804<,1^#?#??????????????8!&6$28#3#7???804;,1^#?#??????????????8!&6$28#3#7???804:,1^#?#??????????????8!&6$28#3#7???8051,1^#?#??????????????8!&6$28#3#7???8050,1^#?#??????????????8!&6$28#3#7???804?,1^#?#??????????????8!&6$28#3#7???804>,1^#?#??????????????8'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 726028 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692028 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692028 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnL.

Module LibSegEa_ahnM.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [697804].
Definition STOPS1 : list Z := [697804] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1"%pstring).
Definition ss0 : sym_state := SS 692236 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450942), ELit 7); ((EVar 2), (-112), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450942), 7); ((EVar 2), (-112), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#::5<<#::5<<#5=#::5<<,20##:9034+$2-:0$3$4$5$6$7$8+$2-:0+$2-70$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,18!$2-70,8+$28#1;0!&6$28#3#7???8044,1^#?#??????????????8!&6$28#3#7???8043,1^#?#??????????????8!&6$28#3#7???8042,1^#?#??????????????8!&6$28#3#7???8041,1^#?#??????????????8!&6$28#3#7???8040,1^#?#??????????????8!&6$28#3#7???803?,1^#?#??????????????8!&6$28#3#7???803>,1^#?#??????????????8'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 697804 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692236 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692236 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnM.

Module LibSegEa_ahnNl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [871008].
Definition STOPS1 : list Z := [871008; 692436] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1?'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1)##10000#688000$28##800)##10000#688000$29##1)&6$28#3#7???8000#100##7???:000#<=000#&6$28#3#7???800<#22###8001>=<<#1###8001>=<?#1###8001>=<2#1!$28#;0,1$24'$24##??'&9$24#1#1#1!$28#;0,8$25!$28#<0,8$26"%pstring).
Definition ss0 : sym_state := SS 692276 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450934), ELit 3); ((EVar 40), (96), ELit 8); ((EVar 40), (112), ELit 8); ((EVar 40), (216), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450934), 3); ((EVar 40), (96), 8); ((EVar 40), (112), 8); ((EVar 40), (216), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",2!!,3#=4:60#:90=4#=4:60!!,3#=4:60#:90=4#=4:60#5=#=4:60,20##:90=4+$2-:0$3$4$5$6$7$8+$2-:0$26@#2&6$25#1#$=$>$?$10$11#136>60+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,28!$28#70,8#136=38!$28#=8,8#136>50!$28#60,8#136>28!&6$28#3#7???8038,1^#?#??????????????8!&6$28#3#7???8037,1^#?#??????????????8!&6$28#3#7???8036,1^#?#??????????????8'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$28#1000#7????????800&$28#20,$28##60,$28#68#8,$28#78#60,$28#>0#720($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1)##10000#688000$28##800)##10000#688000$29##1)&6$28#3#7???8000#100##7???:000#<=000#&6$28#3#7???800<#22###8001>=<<#1###8001>=<?#1###8001>=<2#1!$28#;0,1$24'$24##??'&9$24#1#1#1!$28#;0,8$25!$28#<0,8$26,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692276 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692276 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnNl.

Module LibSegEa_ahnNs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [692436].
Definition STOPS1 : list Z := [692436; 871008] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11+$28#208+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?8010>0#800000000000&$2#20($2-:0#:0%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1)##10000#688000$28##800)##10000#688000$29##1)&6$28#3#7???8000#100##7???:000#<=000#&6$28#3#7???800<#22###8001>=<<#1###8001>=<?#1###8001>=<2#1!$28#;0,1$24'$24##??'&9$24#1##"%pstring).
Definition ss0 : sym_state := SS 692276 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450934), ELit 3); ((EVar 40), (96), ELit 8); ((EVar 40), (112), ELit 8); ((EVar 40), (216), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450934), 3); ((EVar 40), (96), 8); ((EVar 40), (112), 8); ((EVar 40), (216), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",2!!,3#:90=4#=4:60#:90=4!!,3#:90=4#=4:60#:90=4#5=#:90=4,20#$3:+$2-:0$3$4$5$6$7$8+$2-:0#136=38##$=$>$?$10$11#136>60+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,26!$28#70,8#136=38!$28#=8,8#136>50!$28#60,8#136>28!&6$28#3#7???8038,1^#?#??????????????8!&6$28#3#7???8037,1^#?#??????????????8!&6$28#3#7???8036,1^#?#??????????????8'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$28#1000#7????????800&$28#20,$28##60,$28#68#8,$28#78#60,$28#>0#720($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1)##10000#688000$28##800)##10000#688000$29##1)&6$28#3#7???8000#100##7???:000#<=000#&6$28#3#7???800<#22###8001>=<<#1###8001>=<?#1###8001>=<2#1!$28#;0,1$24'$24##??'&9$24#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 692436 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692276 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692276 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnNs.

Module LibSegEa_ahnO.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [1051332].
Definition STOPS1 : list Z := [1051332] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11#136>60+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1)##10000#688000$28##800)##10000#688000$29##1"%pstring).
Definition ss0 : sym_state := SS 692436 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 40), (112), ELit 8)].
Definition F0L : list SR.region := [((EVar 40), (112), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#100:<4#100:<4#5=#100:<4,20##:90><+$2-:0$3$4$5$6$7$8+$2-:0+$28#78$;$<$=$>$?$10$11#136>60+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,17!$28#70,8#136<;8'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$28#1000#7????????800&$28#20,$28##70,$28#78#788($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1)##10000#688000$28##800)##10000#688000$29##1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1051332 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692436 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692436 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnO.

Module LibSegEa_ahnP.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [901856].
Definition STOPS1 : list Z := [901856] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11#136>60+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1"%pstring).
Definition ss0 : sym_state := SS 692460 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=<2>0#=<2>0#5=#=<2>0,20##:9100+$2-:0$3$4$5$6$7$8+$2-:0+$28#=8#136>68$<$=$>$?$10$11#136>60+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 901856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692460 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692460 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnP.

Module LibSegEa_ahnQl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [871008].
Definition STOPS1 : list Z := [871008; 692652] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11#136>60+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$2-90,8+$28#20!$28#20,1$24'$24##??'&9$24#1#1#1!$28#20,8$25!$28#30,8$26"%pstring).
Definition ss0 : sym_state := SS 692480 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450892), ELit 34)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450892), 34)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=4:60#:91:<#=4:60#5=#=4:60,20##:91:<+$2-:0$3$4$5$6$7$8+$2-:0$26@#2&6$25#1+$28#20$=$>$?$10$11^#?#??????????????8+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,38!&6$28#3#7???802=,1^#?#??????????????8!&6$28#3#7???802<,1^#?#??????????????8!&6$28#3#7???8027,1^#?#??????????????8!&6$28#3#7???8026,1^#?#??????????????8!&6$28#3#7???8025,1^#?#??????????????8!&6$28#3#7???8024,1^#?#??????????????8!&6$28#3#7???802;,1^#?#??????????????8!&6$28#3#7???802:,1^#?#??????????????8!&6$28#3#7???8029,1^#?#??????????????8!&6$28#3#7???8028,1^#?#??????????????8!&6$28#3#7???801?,1^#?#??????????????8!&6$28#3#7???801>,1^#?#??????????????8!&6$28#3#7???801=,1^#?#??????????????8!&6$28#3#7???801<,1^#?#??????????????8!&6$28#3#7???8023,1^#?#??????????????8!&6$28#3#7???8022,1^#?#??????????????8!&6$28#3#7???8021,1^#?#??????????????8!&6$28#3#7???8020,1^#?#??????????????8!&6$28#3#7???8017,1^#?#??????????????8!&6$28#3#7???8016,1^#?#??????????????8!&6$28#3#7???8015,1^#?#??????????????8!&6$28#3#7???8014,1^#?#??????????????8!&6$28#3#7???801;,1^#?#??????????????8!&6$28#3#7???801:,1^#?#??????????????8!&6$28#3#7???8019,1^#?#??????????????8!&6$28#3#7???8018,1^#?#??????????????8!&6$28#3#7???800?,1^#?#??????????????8!&6$28#3#7???800>,1^#?#??????????????8!&6$28#3#7???800=,1^#?#??????????????8!&6$28#3#7???800<,1^#?#??????????????8!&6$28#3#7???8013,1^#?#??????????????8!&6$28#3#7???8012,1^#?#??????????????8!&6$28#3#7???8011,1^#?#??????????????8!&6$28#3#7???8010,1^#?#??????????????8'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$2-90,8+$28#20!$28#20,1$24'$24##??'&9$24#1#1#1!$28#20,8$25!$28#30,8$26,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692480 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692480 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnQl.

Module LibSegEa_ahnQs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [692652].
Definition STOPS1 : list Z := [692652; 871008] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11#136>60+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$2-90,8+$28#20!$28#20,1$24'$24##??'&9$24#1##"%pstring).
Definition ss0 : sym_state := SS 692480 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450892), ELit 34)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450892), 34)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#:91:<#=4:60#:91:<#5=#:91:<,20#$3:+$2-:0$3$4$5$6$7$8+$2-:0#$;+$28#20$=$>$?$10$11^#?#??????????????8+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,36!&6$28#3#7???802=,1^#?#??????????????8!&6$28#3#7???802<,1^#?#??????????????8!&6$28#3#7???8027,1^#?#??????????????8!&6$28#3#7???8026,1^#?#??????????????8!&6$28#3#7???8025,1^#?#??????????????8!&6$28#3#7???8024,1^#?#??????????????8!&6$28#3#7???802;,1^#?#??????????????8!&6$28#3#7???802:,1^#?#??????????????8!&6$28#3#7???8029,1^#?#??????????????8!&6$28#3#7???8028,1^#?#??????????????8!&6$28#3#7???801?,1^#?#??????????????8!&6$28#3#7???801>,1^#?#??????????????8!&6$28#3#7???801=,1^#?#??????????????8!&6$28#3#7???801<,1^#?#??????????????8!&6$28#3#7???8023,1^#?#??????????????8!&6$28#3#7???8022,1^#?#??????????????8!&6$28#3#7???8021,1^#?#??????????????8!&6$28#3#7???8020,1^#?#??????????????8!&6$28#3#7???8017,1^#?#??????????????8!&6$28#3#7???8016,1^#?#??????????????8!&6$28#3#7???8015,1^#?#??????????????8!&6$28#3#7???8014,1^#?#??????????????8!&6$28#3#7???801;,1^#?#??????????????8!&6$28#3#7???801:,1^#?#??????????????8!&6$28#3#7???8019,1^#?#??????????????8!&6$28#3#7???8018,1^#?#??????????????8!&6$28#3#7???800?,1^#?#??????????????8!&6$28#3#7???800>,1^#?#??????????????8!&6$28#3#7???800=,1^#?#??????????????8!&6$28#3#7???800<,1^#?#??????????????8!&6$28#3#7???8013,1^#?#??????????????8!&6$28#3#7???8012,1^#?#??????????????8!&6$28#3#7???8011,1^#?#??????????????8!&6$28#3#7???8010,1^#?#??????????????8'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$2-90,8+$28#20!$28#20,1$24'$24##??'&9$24#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 692652 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692480 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692480 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnQs.

Module LibSegEa_ahnR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [388204].
Definition STOPS1 : list Z := [388204] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11^#?#??????????????8+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28##800($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$2-88,8$28"%pstring).
Definition ss0 : sym_state := SS 692652 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450884), ELit 3); ((EVar 40), (0), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_SRL (EVar 40) (ELit 3)), (2147450884), 3); ((EVar 40), (0), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#5><6<#5><6<#5=#5><6<,20##:91=4+$2-:0$3$4$5$6$7$8+$2-:0$28#480$<$=$>$?$10$11^#?#??????????????8+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?,,15!$28#,8#45>0360>!&6$28#3#7???8006,1^#?#??????????????8!&6$28#3#7???8005,1^#?#??????????????8!&6$28#3#7???8004,1^#?#??????????????8'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0'$28#1000#7????????800&$28#20,$28#8#7?8($28##800)##7???7000#100000001000$28##800(&6$28#3#7???8000#100!$28#7?8,8$29'$29#1000#7???????????($29##1)##7???7000#100000001000$29##1)$28##800$29##1)$2-:0#;0$28##800)$2-:0#;0$29##1!$2-88,8$28,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 388204 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692652 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692652 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnR.

Module LibSegEa_ahnS0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [692772].
Definition STOPS1 : list Z := [692772] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7$2+$2-:0$:$;$<$=$>$?$10$11^#?#??????????????8+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0!$2-8,8$2:!$2-10,8$2;!$2-18,8$2<!$2-20,8$2=!$2-28,8$2>!$2-30,8$2?!$2-38,8$30!$2-40,8$31!$2-48,8$32!$2-50,8$33!$2-58,8$34!$2-60,8$35!$2-68,8$36"%pstring).
Definition ss0 : sym_state := SS 692692 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:9224#:9224#5=#:9224,20#$2:$2$3$4$5$6$7$2;$2<#$;$<$=$>$?$10$11$2=$2>$2?$30$31$32$33$34$35$36$1<$1=$1>$1?,,10'$2#7???7?8010>0#800000000000&$2#20($2-:0#:0!$2-8,8$2:!$2-10,8$2;!$2-18,8$2<!$2-20,8$2=!$2-28,8$2>!$2-30,8$2?!$2-38,8$30!$2-40,8$31!$2-48,8$32!$2-50,8$33!$2-58,8$34!$2-60,8$35!$2-68,8$36,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 692772 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692692 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692692 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnS0.

Module LibSegEa_ahnS16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6ae78c.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6ae78c.IT.
Definition ENDS : list Z := [692772].
Definition STOPS1 : list Z := [692772] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$3:+$2-:0$3$4$5$6$7+$2#10+$2-:0$:$;$<$=$>$?$10$11^#?#??????????????8+&6$28#3#7???8000^#?#??????????????8+$28#60+$28#1;0^#?#??????????????8+$28#460+$28#250$28#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8010>0#7??????????0&$2#20($2-:0#;0!$2#8,8$2:!$2#,8$2;!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34!$2-50,8$35!$2-58,8$36"%pstring).
Definition ss0 : sym_state := SS 692692 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:9224#:9224#5=#:9224,20#$2:+$2#10$3$4$5$6$7$2;$2<#$;$<$=$>$?$10$11$2=$2>$2?$30$31$32$33$34$35$36$1<$1=$1>$1?,,10'$2#7???7?8010>0#7??????????0&$2#20($2-:0#;0!$2#8,8$2:!$2#,8$2;!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34!$2-50,8$35!$2-58,8$36,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 692772 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6ae78c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 692692 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6ae78c.IT BndT_Ea_000S8.SegItab_Ea_6ae78c.IT_sound BF NX0 BR XSTEP F0 PSS plan 692692 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_ahnS16.

Module LibSegEa_aigA0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000S8.SegItab_Ea_6b5dd2.ITR.
Definition IT : itab := BndT_Ea_000S8.SegItab_Ea_6b5dd2.IT.
Definition ENDS : list Z := [743624].
Definition STOPS1 : list Z := [743624] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; ELit 1; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801070#800000000000&$2#10($2-70#70'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-70#70$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#,$24#100#8"%pstring).
Definition ss0 : sym_state := SS 740596 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;58<8#;58<8#5=#;58<8,20##;4>20+$2-70$3$4$5$6$7+$24#120$24$24$22#4000$=$>$?$10$11+$24#118#1+$24#100+$24#108+&6+$24#100#3#7???8000+&6+$24#120#3#7???8000#+&6+$24#118#3#7???8000+&6+$24#108#3#7???8000+&6+$24#110#3#7???8000$1<$1=$1>$1?,,1?!$24#118,8$22!$2-70,8+$24#110!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801070#800000000000&$2#10($2-70#70'$24#698000#7????????>=8&$24#8)##7???7000#100000001000$24##128#&6+$24#8#3#7???8000#24($24##128)$2-70#70$24##128!$24#108,8$22!$24#110,8#4000!$24#120,8#,$24#100#8,30!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000S8.SegItab_Ea_6b5dd2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 740596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000S8.SegItab_Ea_6b5dd2.IT BndT_Ea_000S8.SegItab_Ea_6b5dd2.IT_sound BF NX0 BR XSTEP F0 PSS plan 740596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_aigA0.
