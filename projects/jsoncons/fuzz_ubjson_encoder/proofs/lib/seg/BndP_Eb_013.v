(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Eb0PlanKit Eb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Eb_001.

Module LibSegEb_bboCf.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [771280; 771660].
Definition STOPS1 : list Z := [771280; 771660] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0$32$;$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3;%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000!$26#,4#!$24#148,8#1000000'$32##1000000"%pstring).
Definition ss0 : sym_state := SS 767608 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;<4=0#;<64<#;<4=0#;<64<#5;#;;85<,20#$1+$2-:0$3$4$5$6$7$2+$2-:0+$24#168$36#$=$>$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3=!$2-74,4#5!$2-70,8$32%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000!$26#,4#!$24#148,8#1000000'$32##1000000,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;<4=0#;<64<#;<4=0#;<64<#5=#;<4=0,20##;;86<+$2-:0$3$4$5$6$7$2+$2-:0+$24#168+$2-74+$2-70$=$>$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3>'&4$35$36#1#1!$2-74,4#5!$2-70,8$32%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000!$26#,4#!$24#148,8#1000000'$32##1000000,48!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;<4=0#;<64<#;<4=0#;<64<#5=#;<64<,20##;;8?0+$2-:0$3$4$5$6$7$2+$2-:0+$24#168+$2-74+$2-70$=$>$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3>'&4$35$36##!$2-74,4#5!$2-70,8$32%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000!$26#,4#!$24#148,8#1000000'$32##1000000,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 771280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 771660 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767608 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767608 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboCf.

Module LibSegEb_bboCx.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [720296].
Definition STOPS1 : list Z := [720296] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0$32$;$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",37%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$26#,4#!$24#148,8#1000000'$32#1000001^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 767608 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?=:8#:?=:8#5=#:?=:8,20##;;6;<+$2-:0$3$4$5$6$7$2+$2-:0$26#=#$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,38!$2-70,8$32%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$26#,4#!$24#148,8#1000000'$32#1000001^#?#???????????????,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 720296 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767608 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767608 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboCx.

Module LibSegEb_bboITc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [706916].
Definition STOPS1 : list Z := [706916] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0$:$;$<$=$>$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3;%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$2-88,8$25!$25#,8#137=80###8001>?;8#1###8001>?;9#1!$24#10,1#'$35#1000#7?????????>0&$35#8"%pstring).
Definition ss0 : sym_state := SS 767784 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (368), ELit 8)].
Definition F0L : list SR.region := [((EVar 36), (368), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:<964#:<964#5=#:<964,20##;;7>0+$2-:0$3$4$5$6$7$2+$2-:0$25#$24$26#:<964$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3<!$24#170,8+$35#20%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$2-88,8$25!$25#,8#137=80###8001>?;8#1###8001>?;9#1!$24#10,1#'$35#1000#7?????????>0&$35#8,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 706916 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767784 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767784 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboITc.

Module LibSegEb_bboITr.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [768568].
Definition STOPS1 : list Z := [768568] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0$:$;$<$=$>$?$10$11$2?$24$26$15+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",46%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45!$2-88,8$25!$25#,8#137=80###8001>?;8#1###8001>?;9#1!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 767968 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;;:38#;;:38#5=#;;:38,20#$39$2$3$4$5$6$7$3:$3;$30#1#$=$>$?$10$11$3<$3=$3>$3?$40$41$42$43$44$45$1<$1=$1>$1?,,4>!$30#,1#!&6$2?#3#7???8003,1^#?#??????????????5!&6$2?#3#7???8002,1^#?#??????????????5!&6$2?#3#7???8001,1^#?#??????????????5!&6$2?#3#7???8000,1^#?#??????????????5!&6$2?#3#7???8007,1^#?#??????????????5!&6$2?#3#7???8006,1^#?#??????????????5!&6$2?#3#7???8005,1^#?#??????????????5!&6$2?#3#7???8004,1^#?#??????????????5!$2?#,8#45>0360>!$24#8,1#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?#8#38($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$2-8,8$39!$2-10,8$3:!$2-18,8$3;!$2-20,8$3<!$2-28,8$3=!$2-30,8$3>!$2-38,8$3?!$2-40,8$40!$2-48,8$41!$2-50,8$42!$2-58,8$43!$2-60,8$44!$2-68,8$45!$2-88,8$25!$25#,8#137=80###8001>?;8#1###8001>?;9#1!$24#10,1#,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 768568 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767968 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboITr.

Module LibSegEb_bboITs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [706916].
Definition STOPS1 : list Z := [706916] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0$37$;$<$=$>$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3;%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$2-88,8$25!$25#,8#137=80###8001>?;8#1###8001>?;9#1!$24#10,1#'$37#1020#800000000000&$37#8"%pstring).
Definition ss0 : sym_state := SS 767868 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (368), ELit 8)].
Definition F0L : list SR.region := [((EVar 36), (368), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:<964#:<964#5=#:<964,20##;;7>0+$2-:0$3$4$5$6$7$2+$2-:0$25#$24$26#:<964$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3<!$24#170,8$37%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$2-88,8$25!$25#,8#137=80###8001>?;8#1###8001>?;9#1!$24#10,1#'$37#1020#800000000000&$37#8,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 706916 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767868 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767868 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboITs.

Module LibSegEb_bboK2e.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [720296].
Definition STOPS1 : list Z := [720296] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0#100$;$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",34%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044"%pstring).
Definition ss0 : sym_state := SS 767556 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?=:8#:?=:8#5=#:?=:8,20##;;;60+$2-:0$3$4$5$6$7$2+$2-:0$26#1$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,34%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 720296 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767556 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767556 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboK2e.

Module LibSegEb_bboK2h.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [755644].
Definition STOPS1 : list Z := [755644] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0#23$;$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",34%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044"%pstring).
Definition ss0 : sym_state := SS 767556 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;87;<#;87;<#5=#;87;<,20##;;66<+$2-:0$3$4$5$6$7$2+$2-:0+$24#18#1$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,34%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 755644 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767556 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767556 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboK2h.

Module LibSegEb_bboK2l.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [741576; 741968].
Definition STOPS1 : list Z := [741576; 741968] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0$27$;$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",39%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000'$27##22"%pstring).
Definition ss0 : sym_state := SS 767556 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-116), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-116), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;50<8#;5250#;50<8#;5250#5;#;;718,20#$1+$2-:0$3$4$5$6$7$2+$2-:0+$24#168$36$<$=$>$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3;!$2-70,4#9!$2-74,4#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000'$27##22,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;50<8#;5250#;50<8#;5250#5=#;50<8,20##;;728+$2-:0$3$4$5$6$7$2+$2-:0+$24#168+$2-70+$2-74$=$>$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3<'&4$35$36#1#1!$2-70,4#9!$2-74,4#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000'$27##22,48!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;50<8#;5250#;50<8#;5250#5=#;5250,20##;;77<+$2-:0$3$4$5$6$7$2+$2-:0+$24#168+$2-70+$2-74$=$>$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3<'&4$35$36##!$2-70,4#9!$2-74,4#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000'$27##22,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 741576 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 741968 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767556 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767556 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboK2l.

Module LibSegEb_bboK2u.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [741576; 741968].
Definition STOPS1 : list Z := [741576; 741968] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0$27$;$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",39%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000'$27#24#??"%pstring).
Definition ss0 : sym_state := SS 767556 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-116), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-116), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;50<8#;5250#;50<8#;5250#5;#;;718,20#$1+$2-:0$3$4$5$6$7$2+$2-:0+$24#168$36$<$=$>$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3;!$2-70,4#9!$2-74,4#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000'$27#24#??,48!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;50<8#;5250#;50<8#;5250#5=#;50<8,20##;;728+$2-:0$3$4$5$6$7$2+$2-:0+$24#168+$2-70+$2-74$=$>$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3<'&4$35$36#1#1!$2-70,4#9!$2-74,4#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000'$27#24#??,48!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;50<8#;5250#;50<8#;5250#5=#;5250,20##;;77<+$2-:0$3$4$5$6$7$2+$2-:0+$24#168+$2-70+$2-74$=$>$?$10$11$2?$24$26$35+$24#170+&6+$24#170#3#7???8000$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,3<'&4$35$36##!$2-70,4#9!$2-74,4#%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044!$24#170,8$35!$24#178,8$36'$35##800000000000'$36##800000000000'$27#24#??,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 741576 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 741968 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767556 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767556 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboK2u.

Module LibSegEb_bboKd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [755644].
Definition STOPS1 : list Z := [755644] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0#24$;$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",34%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044"%pstring).
Definition ss0 : sym_state := SS 767316 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;87;<#;87;<#5=#;87;<,20##;;584+$2-:0$3$4$5$6$7$2+$2-:0+$24#18#1$<$=$>$?$10$11$2?$24$26#?>00+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,34%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 755644 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767316 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767316 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboKd.

Module LibSegEb_bboKe.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [720296].
Definition STOPS1 : list Z := [720296] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0#100$;$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",34%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044"%pstring).
Definition ss0 : sym_state := SS 767316 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?=:8#:?=:8#5=#:?=:8,20##;;;34+$2-:0$3$4$5$6$7$2+$2-:0$26#1$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,34%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 720296 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767316 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767316 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboKe.

Module LibSegEb_bboKl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [755344].
Definition STOPS1 : list Z := [755344] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0$27$;$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",35%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044'$27##23"%pstring).
Definition ss0 : sym_state := SS 767316 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8690#;8690#5=#;8690,20##;;644+$2-:0$3$4$5$6$7$2+$2-:0+$24#18#24$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,35%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044'$27##23,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 755344 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767316 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767316 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboKl.

Module LibSegEb_bboKu.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [755344].
Definition STOPS1 : list Z := [755344] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0$27$;$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",35%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044'$27#25#??"%pstring).
Definition ss0 : sym_state := SS 767316 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8690#;8690#5=#;8690,20##;;644+$2-:0$3$4$5$6$7$2+$2-:0+$24#18#24$<$=$>$?$10$11$2?$24$26#?>00$16+$24#18$18$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,35%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044'$27#25#??,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 755344 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767316 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767316 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboKu.

Module LibSegEb_bboT1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_cd79fd.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_cd79fd.IT.
Definition ENDS : list Z := [758088].
Definition STOPS1 : list Z := [758088] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$2+$2-:0$:$;$<$=$>$?$10$11$2?$24$26#?>00+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",34%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044"%pstring).
Definition ss0 : sym_state := SS 767364 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (4), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 47) (ELit 3)) (ELit (2147450880))), (4), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9148#;9148#5=#;9148,20##;;598+$2-:0$3$4$5$6$7$2+$2-:0+$24#18+$2?#20#1$=$>$?$10$11$2?$24$26#?>00+$2?#20+$24#18#1$2?+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,35!&6$2?#3#7???8004,1#1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#<0'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-<0#<0$24##180'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-<0#<0$26##10'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-<0#<0$25##8)$24##180$26##10)$24##180$25##8)$26##10$25##8'$2?#69<000#7?????????<0&$2?#20,$2?##40($2?##40)##7???7000#100000001000$2?##40(&6$2?#3#7???8000#8!$2?#38,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##40$30##1)$2-<0#<0$2?##40)$2-<0#<0$30##1)$24##180$2?##40)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#8)$26##10$2?##40)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#8)$25##8$2?##40)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#8)$2?##40##10000#126044,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 758088 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_cd79fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 767364 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_cd79fd.IT BndT_Eb_001.SegItab_Eb_cd79fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 767364 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_bboT1.
