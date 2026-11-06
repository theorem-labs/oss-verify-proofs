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

Module LibSegEb_blpH4b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [750048].
Definition STOPS1 : list Z := [750048] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",5<%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#4!$22#8,8$27!$22#18,8$27'$27##1000000"%pstring).
Definition ss0 : sym_state := SS 745500 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;71>0#;71>0#5=#;71>0,20##;6318+$2-120$3$4$5$6$7$2+$2-120$24$25$26+&6+$22#18#3#7???8000$27#:$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,5<%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#4!$22#8,8$27!$22#18,8$27'$27##1000000,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 750048 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745500 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpH4b.

Module LibSegEb_blpH5a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [756764].
Definition STOPS1 : list Z := [756764] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",5=%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#5!$22#8,8+$27$36'$36#1#1000000!$22#18,8$27'$27##??????"%pstring).
Definition ss0 : sym_state := SS 745500 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8<1<#;8<1<#5=#;8<1<,20##;63>8+$2-120$3$4$5$6$7$2+$2-120$24$25$26+&6+$22#18#3#7???8000##:$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,5=!$22#18,8+$27#1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#5!$22#8,8+$27$36'$36#1#1000000'$27##??????,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 756764 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745500 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpH5a.

Module LibSegEb_blpH5b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [757612].
Definition STOPS1 : list Z := [757612] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",5<%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#5!$22#8,8$27!$22#18,8$27'$27##1000000"%pstring).
Definition ss0 : sym_state := SS 745500 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8?6<#;8?6<#5=#;8?6<,20##;6504+$2-120$3$4$5$6$7$2+$2-120$24$25$26+&6+$22#18#3#7???8000##:$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,5<%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#5!$22#8,8$27!$22#18,8$27'$27##1000000,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 757612 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745500 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpH5b.

Module LibSegEb_blpH6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [749324].
Definition STOPS1 : list Z := [749324] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",59%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#6"%pstring).
Definition ss0 : sym_state := SS 745500 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 34), (0), ELit 4)].
Definition F0L : list SR.region := [((EVar 34), (0), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;6?0<#;6?0<#5=#;6?0<,20##;6454+$2-120$3$4$5$6$7$2+$2-120$24$25$26+&6$22#3#7???8000#;6434#:$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,59!$22#,4#5%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 749324 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745500 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpH6.

Module LibSegEb_blpH7a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [756764].
Definition STOPS1 : list Z := [756764] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",5=%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#7!$22#8,8+$27$36'$36#1#1000000!$22#18,8$27'$27##??????"%pstring).
Definition ss0 : sym_state := SS 745500 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8<1<#;8<1<#5=#;8<1<,20##;62;<+$2-120$3$4$5$6$7$2+$2-120$24$25$26+&6+$22#18#3#7???8000##:$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,5=!$22#18,8+$27#1%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#7!$22#8,8+$27$36'$36#1#1000000'$27##??????,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 756764 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745500 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpH7a.

Module LibSegEb_blpH7b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [757612].
Definition STOPS1 : list Z := [757612] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",5<%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#7!$22#8,8$27!$22#18,8$27'$27##1000000"%pstring).
Definition ss0 : sym_state := SS 745500 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8?6<#;8?6<#5=#;8?6<,20##;6504+$2-120$3$4$5$6$7$2+$2-120$24$25$26+&6+$22#18#3#7???8000##:$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,5<%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#7!$22#8,8$27!$22#18,8$27'$27##1000000,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 757612 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745500 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpH7b.

Module LibSegEb_blpH8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [750524].
Definition STOPS1 : list Z := [750524] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",5;%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#8!$22#10,1$35'$35##??"%pstring).
Definition ss0 : sym_state := SS 745500 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 34), (0), ELit 4)].
Definition F0L : list SR.region := [((EVar 34), (0), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;73;<#;73;<#5=#;73;<,20##;64=<+$2-120$3$4$5$6$7$2+$2-120$24$25$35$26#;64:4#:$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,5;!$22#,4#7%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#10,1$35'$35##??,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 750524 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745500 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpH8.

Module LibSegEb_blpH9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [755344].
Definition STOPS1 : list Z := [755344] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",59%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#9"%pstring).
Definition ss0 : sym_state := SS 745500 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8690#;8690#5=#;8690,20##;614<+$2-120$3$4$5$6$7$2+$2-120+$24#18#+$22#20+&6$22#3#7???8000#;6144#:$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,59%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#1!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#9,48!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745500 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpH9.

Module LibSegEb_blpHm.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [747336].
Definition STOPS1 : list Z := [747336] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",4:%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#"%pstring).
Definition ss0 : sym_state := SS 745500 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;6748#;6748#5=#;6748,20#$1+$2-120$3$4$5$6$7$2+$2-120##1$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,4:%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$24#8,1#,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 747336 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745500 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpHm.

Module LibSegEb_blpI3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [750048].
Definition STOPS1 : list Z := [750048] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",49%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?"%pstring).
Definition ss0 : sym_state := SS 746048 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;71>0#;71>0#5=#;71>0,20##;6250+$2-120$3$4$5$6$7$2+$2-120$24$25$26$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,49%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 750048 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 746048 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 746048 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpI3.

Module LibSegEb_blpI9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [757612].
Definition STOPS1 : list Z := [757612] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",49%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?"%pstring).
Definition ss0 : sym_state := SS 745848 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;8?6<#;8?6<#5=#;8?6<,20##;6188+$2-120$3$4$5$6$7$2+$2-120$24$25$26$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,49%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 757612 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 745848 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 745848 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpI9.

Module LibSegEb_blpJ0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [745500].
Definition STOPS1 : list Z := [745500] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",4;%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$26#,4#!$24#9,1#"%pstring).
Definition ss0 : sym_state := SS 747060 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;601<#;601<#5=#;601<,20#$1+$2-120$3$4$5$6$7$2+$2-120##2$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,4;%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$26#,4#!$24#9,1#,48!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747060 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 747060 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpJ0.

Module LibSegEb_blpJe.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [747336].
Definition STOPS1 : list Z := [747336] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",4;%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$26#,4$38'$38#1#40"%pstring).
Definition ss0 : sym_state := SS 747060 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;6748#;6748#5=#;6748,20#$1+$2-120$3$4$5$6$7$2+$2-120$38$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,4;%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$26#,4$38'$38#1#40,48!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 747336 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 747060 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 747060 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpJe.

Module LibSegEb_blpK50.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_c40876.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_c40876.IT.
Definition ENDS : list Z := [745500].
Definition STOPS1 : list Z := [745500] ++ ENDS.
Definition NX0 : nat := 72.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-120$3$4$5$6$7$2+$2-120$:$;$<$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",59%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$26#,4#!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4!$22#,4#5"%pstring).
Definition ss0 : sym_state := SS 746472 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 34), (0), ELit 4)].
Definition F0L : list SR.region := [((EVar 34), (0), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;601<#;601<#5=#;601<,20#$1+$2-120$3$4$5$6$7$2+$2-120##2#$=$>$?$10$11#20$26+&6+$24#8#3#7???8000#23144+&6+$24#170#3#7???8000+$24#8+$24#9+$24#170+&6$2?#3#7???8000#7???8000$1<$1=$1>$1?,,59!$22#,4#6%#10000#13?000!##1460?8,8#7???8000!##146100,4#1'$2#7???7?801120#800000000000&$2#20($2-120#120'$24#69<000#7????????>80&$24#8)##7???7000#100000001000$24##180#&6$24#3#7???8000#3#&6+$24#20#3#7???8000#2<#&6+$24#14#3#7???8000#1($24##180)$2-120#120$24##180'$25#69<000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1($25##8)$2-120#120$25##8'$26#69<000#7??????????0&$26#8)##7???7000#100000001000$26##10#&6$26#3#7???8000#2($26##10)$2-120#120$26##10!$25#,8#137=80###8001>?;0#10)$24##180$25##8)$26##10$25##8)$24##180$26##10'$2?#69<000#7?????????80&$2?#20,$2?##80($2?##80)##7???7000#100000001000$2?##80(&6$2?#3#7???8000#10!$2?#78,8$30'$30#1000#7???????????($30##1)##7???7000#100000001000$30##1)$2?##80$30##1)$2-120#120$2?##80)$2-120#120$30##1)$24##180$2?##80)$24##180$30##1)&6$24#3#7???8000#30&6$2?#3#7???8000#10)$26##10$2?##80)$26##10$30##1)&6$26#3#7???8000#2&6$2?#3#7???8000#10)$25##8$2?##80)$25##8$30##1)&6$25#3#7???8000#1&6$2?#3#7???8000#10)$2?##80##10000#126044)&6$2?#3#7???8000#10##8001>?;0#10!$2-108,8+$2?#20!$2-100,8#3!$2-?8,8#1!$2-?0,8#!$2->8,8$2?!$2->0,8+&6+$24#148#3#7???8000!$2-=8,8+$24#148!$2-=0,8+&6$25#3#7???8000!$2-<8,8+&6+$24#168#3#7???8000!$2-<0,8+$24#168!$2-;8,8$2?!$2-;0,8#?>00!$2-:8,8+$24#18!$2-:0,8+&6$26#3#7???8000!$2-98,8$24!$2-90,8$25!$2-88,8+&6+$24#9#3#7???8000!$2-70,8$2?!$26#,4#!$24#9,1#'$22#1000#7?????????<0)$22##20##10000#68<000&$22#10($22##20)##7???7000#100000001000$22##20#&6$22#3#7???8000#4!$24#170,8+$22#20)$2-120#120$22##20)$24##180$22##20)$26##10$22##20)$25##8$22##20)$2?##80$22##20)&6$2?#3#7???8000#10&6$22#3#7???8000#4,48!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_c40876.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 746472 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_c40876.IT BndT_Eb_001.SegItab_Eb_c40876.IT_sound BF NX0 BR XSTEP F0 PSS plan 746472 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_blpK50.
