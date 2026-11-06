(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Eu0PlanKit Eu0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Eu_000.

Module LibSegEu_uboC1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [241580].
Definition STOPS1 : list Z := [241580] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25+$24#18$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18"%pstring).
Definition ss0 : sym_state := SS 244096 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3:?:<#3:?:<#5=#3:?:<,20##3;98<+$2-70$3$4$5$6$7$24$26$24$26$<$=$>$?$10$11$25+$24#18$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,='$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 241580 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 244096 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 244096 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboC1.

Module LibSegEu_uboCG0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7#2#1$34$;$<$=$>$?$10$11$25$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#20!$24#178,8+$22#20'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##40)$2-:0#:0$34##40)$24##180$34##40)$26##10$34##40)$25##38$34##40!$2-98,8#398:<!$2-:0,8+$2-60!$2-78,8#3;;64!$2-80,8$24!$2-88,8$26!$2-40,8+$24#168!$2-48,8#'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 236176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 64); ((EVar 2), (-96), ELit 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 32)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-160), 64); ((EVar 2), (-96), 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 32)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##399:<+$2-90$3$4$5$6$7+$2-60+$24#168$34$22#20^#?#?????????????>0#1+$34#40#$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$2-90,8$25!$2-88,8$26!$2-80,8$24!$2-78,8#3;;:4!$2-50,8+$34#40!$34#38,8#!$34#30,1#!$34#28,8$30!$34#20,4#5!$2-48,8+$34#40!$2-58,8+$34#20!$2-60,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#20!$24#178,8+$22#20'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##40)$2-:0#:0$34##40)$24##180$34##40)$26##10$34##40)$25##38$34##40!$2-98,8#398:<!$2-:0,8+$2-60!$2-40,8+$24#168'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 236176 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 236176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCG0.

Module LibSegEu_uboCG1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7#4#2$34$;$<$=$>$?$10$11$25$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#40!$24#178,8+$22#40'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##80)$2-:0#:0$34##80)$24##180$34##80)$26##10$34##80)$25##38$34##80!$2-98,8#398:<!$2-:0,8+$2-60!$2-78,8#3;;64!$2-80,8$24!$2-88,8$26!$2-40,8+$24#168!$2-48,8#'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 236176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 64); ((EVar 2), (-96), ELit 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 64)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-160), 64); ((EVar 2), (-96), 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 64)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##399:<+$2-90$3$4$5$6$7+$2-60+$24#168$34$22#40^#?#?????????????<0#1+$34#80#$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$2-90,8$25!$2-88,8$26!$2-80,8$24!$2-78,8#3;;:4!$2-50,8+$34#60!$34#58,8#!$34#50,1#!$34#48,8$30!$34#40,4#5!$2-48,8+$34#80!$2-58,8+$34#40!$2-60,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#40!$24#178,8+$22#40'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##80)$2-:0#:0$34##80)$24##180$34##80)$26##10$34##80)$25##38$34##80!$2-98,8#398:<!$2-:0,8+$2-60!$2-40,8+$24#168'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 236176 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 236176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCG1.

Module LibSegEu_uboCG10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7#800#400$34$;$<$=$>$?$10$11$25$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#8000!$24#178,8+$22#8000'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##10000)$2-:0#:0$34##10000)$24##180$34##10000)$26##10$34##10000)$25##38$34##10000!$2-98,8#398:<!$2-:0,8+$2-60!$2-78,8#3;;64!$2-80,8$24!$2-88,8$26!$2-40,8+$24#168!$2-48,8#'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 236176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 64); ((EVar 2), (-96), ELit 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 32768)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-160), 64); ((EVar 2), (-96), 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 32768)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##399:<+$2-90$3$4$5$6$7+$2-60+$24#168$34$22#8000^#?#???????????8000#1+$34#10000#$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$2-90,8$25!$2-88,8$26!$2-80,8$24!$2-78,8#3;;:4!$2-50,8+$34#8020!$34#8018,8#!$34#8010,1#!$34#8008,8$30!$34#8000,4#5!$2-48,8+$34#10000!$2-58,8+$34#8000!$2-60,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#8000!$24#178,8+$22#8000'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##10000)$2-:0#:0$34##10000)$24##180$34##10000)$26##10$34##10000)$25##38$34##10000!$2-98,8#398:<!$2-:0,8+$2-60!$2-40,8+$24#168'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 236176 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 236176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCG10.

Module LibSegEu_uboCG2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7#8#4$34$;$<$=$>$?$10$11$25$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#80!$24#178,8+$22#80'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##100)$2-:0#:0$34##100)$24##180$34##100)$26##10$34##100)$25##38$34##100!$2-98,8#398:<!$2-:0,8+$2-60!$2-78,8#3;;64!$2-80,8$24!$2-88,8$26!$2-40,8+$24#168!$2-48,8#'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 236176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 64); ((EVar 2), (-96), ELit 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 128)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-160), 64); ((EVar 2), (-96), 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 128)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##399:<+$2-90$3$4$5$6$7+$2-60+$24#168$34$22#80^#?#?????????????80#1+$34#100#$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$2-90,8$25!$2-88,8$26!$2-80,8$24!$2-78,8#3;;:4!$2-50,8+$34#:0!$34#98,8#!$34#90,1#!$34#88,8$30!$34#80,4#5!$2-48,8+$34#100!$2-58,8+$34#80!$2-60,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#80!$24#178,8+$22#80'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##100)$2-:0#:0$34##100)$24##180$34##100)$26##10$34##100)$25##38$34##100!$2-98,8#398:<!$2-:0,8+$2-60!$2-40,8+$24#168'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 236176 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 236176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCG2.

Module LibSegEu_uboCG3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7#10#8$34$;$<$=$>$?$10$11$25$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#100!$24#178,8+$22#100'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##200)$2-:0#:0$34##200)$24##180$34##200)$26##10$34##200)$25##38$34##200!$2-98,8#398:<!$2-:0,8+$2-60!$2-78,8#3;;64!$2-80,8$24!$2-88,8$26!$2-40,8+$24#168!$2-48,8#'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 236176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 64); ((EVar 2), (-96), ELit 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 256)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-160), 64); ((EVar 2), (-96), 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 256)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##399:<+$2-90$3$4$5$6$7+$2-60+$24#168$34$22#100^#?#?????????????00#1+$34#200#$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$2-90,8$25!$2-88,8$26!$2-80,8$24!$2-78,8#3;;:4!$2-50,8+$34#120!$34#118,8#!$34#110,1#!$34#108,8$30!$34#100,4#5!$2-48,8+$34#200!$2-58,8+$34#100!$2-60,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#100!$24#178,8+$22#100'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##200)$2-:0#:0$34##200)$24##180$34##200)$26##10$34##200)$25##38$34##200!$2-98,8#398:<!$2-:0,8+$2-60!$2-40,8+$24#168'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 236176 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 236176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCG3.

Module LibSegEu_uboCG4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7#20#10$34$;$<$=$>$?$10$11$25$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#200!$24#178,8+$22#200'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##400)$2-:0#:0$34##400)$24##180$34##400)$26##10$34##400)$25##38$34##400!$2-98,8#398:<!$2-:0,8+$2-60!$2-78,8#3;;64!$2-80,8$24!$2-88,8$26!$2-40,8+$24#168!$2-48,8#'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 236176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 64); ((EVar 2), (-96), ELit 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 512)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-160), 64); ((EVar 2), (-96), 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 512)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##399:<+$2-90$3$4$5$6$7+$2-60+$24#168$34$22#200^#?#????????????>00#1+$34#400#$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$2-90,8$25!$2-88,8$26!$2-80,8$24!$2-78,8#3;;:4!$2-50,8+$34#220!$34#218,8#!$34#210,1#!$34#208,8$30!$34#200,4#5!$2-48,8+$34#400!$2-58,8+$34#200!$2-60,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#200!$24#178,8+$22#200'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##400)$2-:0#:0$34##400)$24##180$34##400)$26##10$34##400)$25##38$34##400!$2-98,8#398:<!$2-:0,8+$2-60!$2-40,8+$24#168'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 236176 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 236176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCG4.

Module LibSegEu_uboCG5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7#40#20$34$;$<$=$>$?$10$11$25$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#400!$24#178,8+$22#400'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##800)$2-:0#:0$34##800)$24##180$34##800)$26##10$34##800)$25##38$34##800!$2-98,8#398:<!$2-:0,8+$2-60!$2-78,8#3;;64!$2-80,8$24!$2-88,8$26!$2-40,8+$24#168!$2-48,8#'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 236176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 64); ((EVar 2), (-96), ELit 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 1024)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-160), 64); ((EVar 2), (-96), 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 1024)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##399:<+$2-90$3$4$5$6$7+$2-60+$24#168$34$22#400^#?#????????????<00#1+$34#800#$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$2-90,8$25!$2-88,8$26!$2-80,8$24!$2-78,8#3;;:4!$2-50,8+$34#420!$34#418,8#!$34#410,1#!$34#408,8$30!$34#400,4#5!$2-48,8+$34#800!$2-58,8+$34#400!$2-60,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#400!$24#178,8+$22#400'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##800)$2-:0#:0$34##800)$24##180$34##800)$26##10$34##800)$25##38$34##800!$2-98,8#398:<!$2-:0,8+$2-60!$2-40,8+$24#168'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 236176 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 236176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCG5.

Module LibSegEu_uboCG6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7#80#40$34$;$<$=$>$?$10$11$25$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#800!$24#178,8+$22#800'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##1000)$2-:0#:0$34##1000)$24##180$34##1000)$26##10$34##1000)$25##38$34##1000!$2-98,8#398:<!$2-:0,8+$2-60!$2-78,8#3;;64!$2-80,8$24!$2-88,8$26!$2-40,8+$24#168!$2-48,8#'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 236176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 64); ((EVar 2), (-96), ELit 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 2048)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-160), 64); ((EVar 2), (-96), 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 2048)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##399:<+$2-90$3$4$5$6$7+$2-60+$24#168$34$22#800^#?#????????????800#1+$34#1000#$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$2-90,8$25!$2-88,8$26!$2-80,8$24!$2-78,8#3;;:4!$2-50,8+$34#820!$34#818,8#!$34#810,1#!$34#808,8$30!$34#800,4#5!$2-48,8+$34#1000!$2-58,8+$34#800!$2-60,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#800!$24#178,8+$22#800'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##1000)$2-:0#:0$34##1000)$24##180$34##1000)$26##10$34##1000)$25##38$34##1000!$2-98,8#398:<!$2-:0,8+$2-60!$2-40,8+$24#168'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 236176 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 236176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCG6.

Module LibSegEu_uboCG7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7#100#80$34$;$<$=$>$?$10$11$25$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#1000!$24#178,8+$22#1000'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##2000)$2-:0#:0$34##2000)$24##180$34##2000)$26##10$34##2000)$25##38$34##2000!$2-98,8#398:<!$2-:0,8+$2-60!$2-78,8#3;;64!$2-80,8$24!$2-88,8$26!$2-40,8+$24#168!$2-48,8#'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 236176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 64); ((EVar 2), (-96), ELit 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 4096)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-160), 64); ((EVar 2), (-96), 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 4096)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##399:<+$2-90$3$4$5$6$7+$2-60+$24#168$34$22#1000^#?#????????????000#1+$34#2000#$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$2-90,8$25!$2-88,8$26!$2-80,8$24!$2-78,8#3;;:4!$2-50,8+$34#1020!$34#1018,8#!$34#1010,1#!$34#1008,8$30!$34#1000,4#5!$2-48,8+$34#2000!$2-58,8+$34#1000!$2-60,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#1000!$24#178,8+$22#1000'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##2000)$2-:0#:0$34##2000)$24##180$34##2000)$26##10$34##2000)$25##38$34##2000!$2-98,8#398:<!$2-:0,8+$2-60!$2-40,8+$24#168'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 236176 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 236176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCG7.

Module LibSegEu_uboCG8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7#200#100$34$;$<$=$>$?$10$11$25$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#2000!$24#178,8+$22#2000'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##4000)$2-:0#:0$34##4000)$24##180$34##4000)$26##10$34##4000)$25##38$34##4000!$2-98,8#398:<!$2-:0,8+$2-60!$2-78,8#3;;64!$2-80,8$24!$2-88,8$26!$2-40,8+$24#168!$2-48,8#'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 236176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 64); ((EVar 2), (-96), ELit 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 8192)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-160), 64); ((EVar 2), (-96), 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 8192)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##399:<+$2-90$3$4$5$6$7+$2-60+$24#168$34$22#2000^#?#???????????>000#1+$34#4000#$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$2-90,8$25!$2-88,8$26!$2-80,8$24!$2-78,8#3;;:4!$2-50,8+$34#2020!$34#2018,8#!$34#2010,1#!$34#2008,8$30!$34#2000,4#5!$2-48,8+$34#4000!$2-58,8+$34#2000!$2-60,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#2000!$24#178,8+$22#2000'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##4000)$2-:0#:0$34##4000)$24##180$34##4000)$26##10$34##4000)$25##38$34##4000!$2-98,8#398:<!$2-:0,8+$2-60!$2-40,8+$24#168'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 236176 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 236176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCG8.

Module LibSegEu_uboCG9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7#400#200$34$;$<$=$>$?$10$11$25$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#4000!$24#178,8+$22#4000'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##8000)$2-:0#:0$34##8000)$24##180$34##8000)$26##10$34##8000)$25##38$34##8000!$2-98,8#398:<!$2-:0,8+$2-60!$2-78,8#3;;64!$2-80,8$24!$2-88,8$26!$2-40,8+$24#168!$2-48,8#'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 236176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 64); ((EVar 2), (-96), ELit 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 16384)), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-160), 64); ((EVar 2), (-96), 40); ((EAlu Instr.ALU_ADD (EVar 52) (ELit 16384)), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##399:<+$2-90$3$4$5$6$7+$2-60+$24#168$34$22#4000^#?#???????????<000#1+$34#8000#$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$2-90,8$25!$2-88,8$26!$2-80,8$24!$2-78,8#3;;:4!$2-50,8+$34#4020!$34#4018,8#!$34#4010,1#!$34#4008,8$30!$34#4000,4#5!$2-48,8+$34#8000!$2-58,8+$34#4000!$2-60,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22#4000!$24#178,8+$22#4000'$22#1000#7??????00000&$22#10'$34#1000#7??????00000&$34#10($34##8000)$2-:0#:0$34##8000)$24##180$34##8000)$26##10$34##8000)$25##38$34##8000!$2-98,8#398:<!$2-:0,8+$2-60!$2-40,8+$24#168'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 236176 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 236176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCG9.

Module LibSegEu_uboCH.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [362452].
Definition STOPS1 : list Z := [362452] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7+$2-60+$24#168$:$;$<$=$>$?$10$11$34$30+$24#168$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18!$24#168,8$22!$24#170,8+$22$23!$24#178,8+$22$23'$22#1000#7??????00000&$22#10'$23#20#8000&$23#20'$34#1000#7??????00000&$34#10!$2-60,8$34!$2-58,8+$34$23!$2-50,8++$34$23#20!$2-48,8+$34@#2$23!$2-40,8+$24#168!$2-78,8#3;;:4!$2-80,8$24!$2-88,8$26!$2-90,8$25'$30##1000000"%pstring).
Definition ss0 : sym_state := SS 235948 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (360), ELit 24); ((EVar 2), (-144), ELit 88)].
Definition F0L : list SR.region := [((EVar 36), (360), 24); ((EVar 2), (-144), 88)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#587=4#587=4#5=#587=4,20##3;<44+$2-70$3$4$5$6$7$24$26$22$23$22$22$>$?$10$11$25$30++$34$23#20$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,20!$2-48,8+$22$23!$2-60,8$22!$24#178,8+$34@#2$23!$2-50,8$22!$24#170,8++$34$23#20!$2-58,8$22!$24#168,8$34'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18'$22#1000#7??????00000&$22#10'$23#20#8000&$23#20'$34#1000#7??????00000&$34#10!$2-40,8+$24#168!$2-78,8#3;;:4!$2-80,8$24!$2-88,8$26!$2-90,8$25'$30##1000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 362452 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 235948 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 235948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCH.

Module LibSegEu_uboCT.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_f30027.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_f30027.IT.
Definition ENDS : list Z := [222284].
Definition STOPS1 : list Z := [222284] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$30$37$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18'$25#7???7?8000:0#7?????????<8&$25#8)$2-:0#:0$25##38!$25#,8#;4260)$24##180$25##38)$26##10$25##38'$30##1000000'$37#1020#7??????00000&$37#10"%pstring).
Definition ss0 : sym_state := SS 244804 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3644<#3644<#5=#3644<,20##3;<80+$2-70$3$4$5$6$7$24$26$25$30#$24$26#3644<$10$11$25$30+$37-20$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17!$24#170,8$37'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$24#7???7?8000:0#7????????>80&$24#8)$2-:0#:0$24##180'$26#7???7?8000:0#7??????????0&$26#8)$2-:0#:0$26##10%#10000#;;028)$24##180$26##10($24#8#8($24#168#18'$25#7???7?8000:0#7?????????<8&$25#8)$2-:0#:0$25##38!$25#,8#;4260)$24##180$25##38)$26##10$25##38'$30##1000000'$37#1020#7??????00000&$37#10,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 222284 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_f30027.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 244804 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_f30027.IT BndT_Eu_000.SegItab_Eu_f30027.IT_sound BF NX0 BR XSTEP F0 PSS plan 244804 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uboCT.
