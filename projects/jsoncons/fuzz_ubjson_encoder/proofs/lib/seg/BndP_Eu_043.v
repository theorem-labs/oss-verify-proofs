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

Module LibSegEu_uhnMl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_c66d42.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_c66d42.IT.
Definition ENDS : list Z := [362452].
Definition STOPS1 : list Z := [362452] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-340$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$2#7???7?800340#800000000000&$2#10($2-340#340!$2-30,1$23'$23##??'&9$23#1#1#1,$2-2?#7!$2-20,8$25"%pstring).
Definition ss0 : sym_state := SS 217228 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#587=4#587=4#5=#587=4,20##350:8+$2-340$3$4$5$6$7$8$9$25@#2&6$30#1$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'$2#7???7?800340#800000000000&$2#10($2-340#340!$2-30,1$23'$23##??'&9$23#1#1#1,$2-2?#7!$2-20,8$25,31!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_c66d42.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 217228 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_c66d42.IT BndT_Eu_000.SegItab_Eu_c66d42.IT_sound BF NX0 BR XSTEP F0 PSS plan 217228 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uhnMl.

Module LibSegEu_uhnMs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_c66d42.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_c66d42.IT.
Definition ENDS : list Z := [217276].
Definition STOPS1 : list Z := [217276] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-340$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800340#800000000000&$2#10($2-340#340!$2-30,1$23'$23##??'&9$23#1##!$2-8,8$26!$2-10,8$27!$2-18,8$2="%pstring).
Definition ss0 : sym_state := SS 217228 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#350;<#350;<#5=#350;<,20#$26$2$3$4$5$6$7$27$2=#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800340#800000000000&$2#10($2-340#340!$2-30,1$23'$23##??'&9$23#1##!$2-8,8$26!$2-10,8$27!$2-18,8$2=,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 217276 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_c66d42.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 217228 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_c66d42.IT BndT_Eu_000.SegItab_Eu_c66d42.IT_sound BF NX0 BR XSTEP F0 PSS plan 217228 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uhnMs.

Module LibSegEu_uhnN.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_c66d42.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_c66d42.IT.
Definition ENDS : list Z := [217276].
Definition STOPS1 : list Z := [217276] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-340$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483904 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-832)) (ELit 832);
   KWord (SA (EVar 2) (-8)) 8 (EVar 38);
   KWord (SA (EVar 2) (-16)) 8 (EVar 39);
   KWord (SA (EVar 2) (-24)) 8 (EVar 45)].
Definition ss0 : sym_state := SS 217256 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#350;<#350;<#5=#350;<,20#$26$2$3$4$5$6$7$27$2=#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6'$2#7???7?800340#800000000000&$2#10($2-340#340!$2-8,8$26!$2-10,8$27!$2-18,8$2=,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 217276 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_c66d42.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 217256 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_c66d42.IT BndT_Eu_000.SegItab_Eu_c66d42.IT_sound BF NX0 BR XSTEP F0 PSS plan 217256 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uhnN.

Module LibSegEu_uicA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_bd4e09.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_bd4e09.IT.
Definition ENDS : list Z := [542560].
Definition STOPS1 : list Z := [542560] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21$27#8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#;;028"%pstring).
Definition ss0 : sym_state := SS 217580 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EVar 33), (0), ELit 16); ((EVar 33), (120), ELit 136)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EVar 33), (0), 16); ((EVar 33), (120), 136)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#84760#84760!$!!,2#84760#84760#5=#84760,20##35274+$2-50$3$4$35$36$37$21+$21$27+$21#:8$39$3:$3;$3<$3=$3>$3?#8+$21#10+$21#78#;7:28#;7:18#;79=8$18$19$1:$1;$40$41$42$43,,20#$21#;0#50!$21#98,4#!$21#90,8#!$21#88,8#6!$21#80,4#1002!$21#:0,8+$21#10!$21#9<,4#!$2-60,8$21!$2-58,8#35274!$21#8,8#!$21#78,8#;7:88!$21#,8#;7:60!$21#:8,8#!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#;;028,44!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 542560 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_bd4e09.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 217580 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_bd4e09.IT BndT_Eu_000.SegItab_Eu_bd4e09.IT_sound BF NX0 BR XSTEP F0 PSS plan 217580 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uicA.

Module LibSegEu_uicB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_bd4e09.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_bd4e09.IT.
Definition ENDS : list Z := [542560].
Definition STOPS1 : list Z := [542560] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$21+$21$27$:$;$<$=$>$?$10$11#8+$21#10+$21#78#;7:28#;7:18#;79=8$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#;;028"%pstring).
Definition ss0 : sym_state := SS 217716 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-144), ELit 64); ((EVar 33), (0), ELit 8); ((EVar 33), (16), ELit 8); ((EVar 33), (120), ELit 8); ((EVar 33), (256), ELit 12)].
Definition F0L : list SR.region := [((EVar 2), (-144), 64); ((EVar 33), (0), 8); ((EVar 33), (16), 8); ((EVar 33), (120), 8); ((EVar 33), (256), 12)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#84760#84760#5=#84760,20##359?4+$2-90$3$4$5$6$7+$21#10+$21#18+$21#18+$21$27#8$=$>$?$10$11#8#8+$21$27#;7880#;7:18#;79?0$18$19$1:$1;$1<$1=$1>$1?,,19!$21#10,8#;7880!$2-88,8#;7:28!$2-80,8+$21#78!$2-78,8+$21#10!$2-70,8#8!$2-68,8+$21$27!$2-60,8$21!$2-58,8#352:8!$21#78,8#;7:18!$21#,8#;79?0!$21#10:,1^#?#???????????????!$21#109,1^#?#???????????????!$21#108,1^#?#???????????????!$21#100,8#!$21#10;,1^#?#???????????????'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#;;028,34!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 542560 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_bd4e09.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 217716 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_bd4e09.IT BndT_Eu_000.SegItab_Eu_bd4e09.IT_sound BF NX0 BR XSTEP F0 PSS plan 217716 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uicB.

Module LibSegEu_uicCl1a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_bd4e09.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_bd4e09.IT.
Definition ENDS : list Z := [732992].
Definition STOPS1 : list Z := [732992] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7+$21#10+$21#18$:$;$<$=$>$?$10$11$12#8+$21$27#;7880$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#;;028!+$21$27#,1$26'$26##??'&9$26#1#1#1!+$21$27#8,8$28!+$21$27#10,8$24'$28#17#2<"%pstring).
Definition ss0 : sym_state := SS 219636 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 48); ((EVar 33), (16), ELit 8); ((EVar 33), (32), ELit 84)].
Definition F0L : list SR.region := [((EVar 2), (-192), 48); ((EVar 33), (16), 8); ((EVar 33), (32), 84)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#;2?40#;2?40!$!!,2#;2?40#;2?40#5=#;2?40,20##5;004+$2-<0$3$4$35$36$37$28+$21#50#30#2<#1>##1$3=$3>$3?+$21#50$24#2?#;7880$16$17$18$19$1:$1;$40$41$42$43,,1:!$2-<0,8+$21$27!$2-;8,8#8!$2-;0,8+$21#50!$2-:8,8+$21#18!$2-:0,8+$21#10!$2-98,8#35:38!$21#70,4#8!$21#68,8#!$21#60,8#!$21#58,8#!$21#50,8#!$21#10,8#;7900#$21#20#30'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#;;028'$26##??'&9$26#1#1#1'$28#17#2<,44!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 732992 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_bd4e09.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 219636 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_bd4e09.IT BndT_Eu_000.SegItab_Eu_bd4e09.IT_sound BF NX0 BR XSTEP F0 PSS plan 219636 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uicCl1a.

Module LibSegEu_uicCl1b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_bd4e09.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_bd4e09.IT.
Definition ENDS : list Z := [732992].
Definition STOPS1 : list Z := [732992] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7+$21#10+$21#18$:$;$<$=$>$?$10$11$12#8+$21$27#;7880$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#;;028!+$21$27#,1$26'$26##??'&9$26#1#1#1!+$21$27#8,8$28!+$21$27#10,8$24'$28#2=#3??????'&8$28#7#2?#4000007"%pstring).
Definition ss0 : sym_state := SS 219636 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 48); ((EVar 33), (16), ELit 8); ((EVar 33), (32), ELit 84)].
Definition F0L : list SR.region := [((EVar 2), (-192), 48); ((EVar 33), (16), 8); ((EVar 33), (32), 84)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#;2?40#;2?40!$!!,2#;2?40#;2?40#5=#;2?40,20##5;004+$2-<0$3$4$35$36$37$28+$21#50+@#8&6$28#3#8#2<#1>##1$3=$3>$3?+$21#50$24+@#8&6$28#3#7#;7880$16$17$18$19$1:$1;$40$41$42$43,,1;!$2-<0,8+$21$27!$2-;8,8#8!$2-;0,8+$21#50!$2-:8,8+$21#18!$2-:0,8+$21#10!$2-98,8#35:38!$21#70,4#8!$21#68,8#!$21#60,8#!$21#58,8#!$21#50,8#!$21#10,8#;7900#$21#20#30'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#;;028'$26##??'&9$26#1#1#1'$28#2=#3??????'&8$28#7#2?#4000007,44!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 732992 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_bd4e09.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 219636 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_bd4e09.IT BndT_Eu_000.SegItab_Eu_bd4e09.IT_sound BF NX0 BR XSTEP F0 PSS plan 219636 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uicCl1b.

Module LibSegEu_uicCl2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_bd4e09.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_bd4e09.IT.
Definition ENDS : list Z := [712712].
Definition STOPS1 : list Z := [712712] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$28$9$29$;$<$=$>$?$10$11$12$24$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 372740 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>008#:>008#5=#:>008,20##5;014+$2-<0$3$4$5$6$7$28$9$29$24$28$=$>$?$10$11$29$24$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,,34!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 712712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_bd4e09.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 372740 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_bd4e09.IT BndT_Eu_000.SegItab_Eu_bd4e09.IT_sound BF NX0 BR XSTEP F0 PSS plan 372740 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uicCl2.

Module LibSegEu_uicCl3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_bd4e09.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_bd4e09.IT.
Definition ENDS : list Z := [219704].
Definition STOPS1 : list Z := [219704] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$28+$21#50$:$;$<$=$>$?$10$11$29$13$2:$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-98,8#35:38!$2-:0,8+$21#10!$2-:8,8+$21#18!$2-;0,8+$21#50!$2-;8,8#8!$2-<0,8+$21$27'$29#1000#800000000000'$28#17#3??????'$2:#2?#4000007(+$29$28##1)$2-=0#=0+$29$28##1)$21##110+$29$28##1"%pstring).
Definition ss0 : sym_state := SS 372756 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (80), ELit 24); ((EAlu Instr.ALU_ADD (EVar 41) (EVar 40)), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (80), 24); ((EAlu Instr.ALU_ADD (EVar 41) (EVar 40)), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#35:38#35:38#5=#35:38,20##35:38+$2-90$3$4$5$6$7+$21#10+$21#18+$21#50$;$<$=$>$?$10$11+$21#50#8+$21$27$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,19!+$28$29#,1#!$21#60,8$29!$21#58,8$28!$21#50,8+$2:#2'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-98,8#35:38!$2-:0,8+$21#10!$2-:8,8+$21#18!$2-;0,8+$21#50!$2-;8,8#8!$2-<0,8+$21$27'$29#1000#800000000000'$28#17#3??????'$2:#2?#4000007(+$29$28##1)$2-=0#=0+$29$28##1)$21##110+$29$28##1,34!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 219704 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_bd4e09.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 372756 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_bd4e09.IT BndT_Eu_000.SegItab_Eu_bd4e09.IT_sound BF NX0 BR XSTEP F0 PSS plan 372756 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uicCl3.

Module LibSegEu_uicCl4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_bd4e09.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_bd4e09.IT.
Definition ENDS : list Z := [217808].
Definition STOPS1 : list Z := [217808] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7+$21#10$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-58,8#352:8!$2-60,8$21!$2-68,8+$21$27!$2-70,8#8!$2-78,8+$21#10!$2-80,8+$21#78!$2-88,8#;7:28!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$21#50,1$26'$26##??'&9$26#1#1#1!$21#58,8$28!$21#60,8$29!$21#70,4#8'$29#1000#800000000000'$28#17#3??????"%pstring).
Definition ss0 : sym_state := SS 219704 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 48); ((EVar 33), (32), ELit 24); ((EVar 33), (104), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-192), 48); ((EVar 33), (32), 24); ((EVar 33), (104), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#352=0#352=0#5=#352=0,20#$2;$2$3$4$5$6$7$2<$2=##1+$28$29#1#$?$10$11$2>$2?$30$31$32$33$18$19$1:$1;$1<$1=$1>$1?,,2:!$21#68,8+$28$29!$21#30,8+$28$29!$21#28,8$29!$21#20,8$29!$2-;8,8$13!$2-;0,8$12!$2-:8,8$9!$2-:0,8+$21#10!$2-98,8#35:40'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-58,8#352:8!$2-60,8$21!$2-68,8+$21$27!$2-70,8#8!$2-78,8+$21#10!$2-80,8+$21#78!$2-88,8#;7:28!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$21#50,1$26'$26##??'&9$26#1#1#1!$21#58,8$28!$21#60,8$29!$21#70,4#8'$29#1000#800000000000'$28#17#3??????,34!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 217808 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_bd4e09.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 219704 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_bd4e09.IT BndT_Eu_000.SegItab_Eu_bd4e09.IT_sound BF NX0 BR XSTEP F0 PSS plan 219704 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uicCl4.

Module LibSegEu_uicCs1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_bd4e09.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_bd4e09.IT.
Definition ENDS : list Z := [219704].
Definition STOPS1 : list Z := [219704] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7+$21#10+$21#18$:$;$<$=$>$?$10$11$12#8+$21$27#;7880$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#;;028!+$21$27#,1$26'$26##??'&9$26#1##!+$21$27#,8$23!+$21$27#8,8$24!+$21$27#10,8$25"%pstring).
Definition ss0 : sym_state := SS 219636 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (16), ELit 8); ((EVar 33), (32), ELit 84)].
Definition F0L : list SR.region := [((EVar 33), (16), 8); ((EVar 33), (32), 84)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#35:38#35:38!$!!,2#35:38#35:38#5=#35:38,20##35:38+$2-90$3$4$35$36$37+$21#10+$21#18+$21#50$23$24##$3=$3>$3?+$21#50#8+$21$27#;7880$16$17$18$19$1:$1;$40$41$42$43,,17!$21#50,8$23!$21#58,8$24!$21#60,8$25!$21#70,4#8!$21#68,8#!$21#10,8#;7900#$21#20#30'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#;;028!+$21$27#,1$26'$26##??'&9$26#1##!+$21$27#,8$23!+$21$27#8,8$24!+$21$27#10,8$25,44!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 219704 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_bd4e09.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 219636 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_bd4e09.IT BndT_Eu_000.SegItab_Eu_bd4e09.IT_sound BF NX0 BR XSTEP F0 PSS plan 219636 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uicCs1.

Module LibSegEu_uicCs2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_bd4e09.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_bd4e09.IT.
Definition ENDS : list Z := [217808].
Definition STOPS1 : list Z := [217808] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7+$21#10$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-58,8#352:8!$2-60,8$21!$2-68,8+$21$27!$2-70,8#8!$2-78,8+$21#10!$2-80,8+$21#78!$2-88,8#;7:28!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$21#50,1$26'$26##2<'&9$26#1##!$21#70,4#8"%pstring).
Definition ss0 : sym_state := SS 219704 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 48); ((EVar 33), (32), ELit 24); ((EVar 33), (104), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-192), 48); ((EVar 33), (32), 24); ((EVar 33), (104), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#352=0#352=0#5=#352=0,20#$2;$2$3$4$5$6$7$2<$2=##++$21&6$26#1#51#1#$?$10$11$2>$2?$30$31$32$33$18$19$1:$1;$1<$1=$1>$1?,,26!$21#68,8++$21&6$26#1#51!$21#30,8++$21&6$26#1#51!$21#28,8+$21#51!$21#20,8+$21#51!$2-;8,8$13!$2-;0,8$12!$2-:8,8$9!$2-:0,8+$21#10!$2-98,8#35:40'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-58,8#352:8!$2-60,8$21!$2-68,8+$21$27!$2-70,8#8!$2-78,8+$21#10!$2-80,8+$21#78!$2-88,8#;7:28!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$21#50,1$26'$26##2<'&9$26#1##!$21#70,4#8,34!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 217808 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_bd4e09.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 219704 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_bd4e09.IT BndT_Eu_000.SegItab_Eu_bd4e09.IT_sound BF NX0 BR XSTEP F0 PSS plan 219704 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uicCs2.

Module LibSegEu_uliA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_33b84d.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_33b84d.IT.
Definition ENDS : list Z := [542652].
Definition STOPS1 : list Z := [542652] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?800400#800000000000&$2#10($2-400#400'$21#7???7?800400#7??????????8&$21#8)$2-400#400$21##8($21##8%#10000#;;028%#<;3?2#<;;30(##<;3?2#73>%#<<258#<<2;0(##<<258#58%#><>53#><>54%#><?28#><?2<!##><>30,8$22"%pstring).
Definition ss0 : sym_state := SS 542560 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-1024), ELit 1024); ((EVar 33), (0), ELit 8); ((ELit 0), (832498), ELit 1854); ((ELit 0), (836184), ELit 88)].
Definition F0L : list SR.region := [((EVar 2), (-1024), 1024); ((EVar 33), (0), 8); ((ELit 0), (832498), 1854); ((ELit 0), (836184), 88)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",40!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<!$!!,2#847;<#847;<#5=#847;<,20#$1$2$3$4$211$212$213$8$9#<;:00#<;:00$216$217$218$219$21:$21;$12$13$14$15$16$17$18$19$1:$1;$21<$21=$21>$21?,,11>!$21#,8#<;:00!##<;5?1,1#1!##<;5?0,1#1!##<;5>8,8#<;:00!##<;5>1,1#1!##<;5>0,1#1!##<;5=8,8#<;:00!##<;;10,8#<;838!##<;:18,8#<;;18!$2-110,8$18!$2-108,8$17!$2-100,8$16!$2-?8,8$15!$2-?0,8#<;840!$2->8,8#1=!$2->0,8#<;:00!$2-=8,8#<;:10!$2-=0,8#<;838!$2-<8,8#7>130!##<;840,8#1!##<<2:0,4#!##<<2:8,8#!##<<288,8#!$2-144,4#!$2-140,8$22!$2-138,8#1!$2-130,8$14!$2-128,8#<<258!$2-120,8+$2-;0!$2-118,8#<<258!##<<25<,4#!$2-158,8$19!$2-150,8$18!##<;530,8^#?#???????????????!##<;538,4#1>!##<;540,4#1>!$2-;0,8+$2-:8!$2-:8,8+$2-;8!$2-;8,8#<;530!$2-:0,8$14!$2-98,8#<;5<8!$2-90,8#<;5=0!$2-88,8#;7>60!$2-80,8#<;:00!$2-78,8#7;:90!##<;838,8#;9618!##<;;08,8#<;828!##<;830,8#1!##<;520,8^#?#???????????????!##<;528,4#1=!##<;828,8#;9590!##<;;00,8#<;908!##<;910,8#1!##<;490,8^#?#???????????????!##<;498,4#1<!##<;918,8#1:?08!##<;908,8#;8=<8!##<;:?8,8#<;8?0!##<;8?8,8#1!##<;480,8^#?#???????????????!##<;488,4#1;!##<;900,8#1:?08!##<;8?0,8#;8=50!##<;:?0,8#<;8=8!##<;8>0,8#1!##<;470,8^#?#???????????????!##<;478,4#1:!##<;8>8,8#;8:40!##<;8=8,8#;89>0!##<;:>8,8#<;8<0!##<;8<8,8#1!##<;460,8^#?#???????????????!##<;468,4#19!##<;8=0,8#;8930!##<;8<0,8#;88=0!##<;:>0,8#<;818!##<;820,8#1!##<;510,8^#?#???????????????!##<;518,4#18!##<;818,8#;9510!##<;:=8,8#<;808!##<;810,8#1!##<;500,8^#?#???????????????!##<;508,4#17!##<;808,8#;9490!##<;:=0,8#<;7?8!##<;800,8#1!##<;4?0,8^#?#???????????????!##<;4?8,4#16!##<;7?8,8#;9410!##<;:<8,8#<;7>8!##<;7?0,8#1!##<;4>0,8^#?#???????????????!##<;4>8,4#15!##<;7>8,8#;9390!##<;:<0,8#<;7=8!##<;7>0,8#1!##<;4=0,8^#?#???????????????!##<;4=8,4#14!##<;7=8,8#;90<8!##<;:;8,8#<;7<8!##<;7=0,8#1!##<;4<0,8^#?#???????????????!##<;4<8,4#13!##<;7<8,8#;9020!##<;:;0,8#<;7;8!##<;7<0,8#1!##<;4;0,8^#?#???????????????!##<;4;8,4#12!##<;7;8,8#;8?78!##<;::8,8#<;7:8!##<;7;0,8#1!##<;4:0,8^#?#???????????????!##<;4:8,4#11!##<;7:8,8#;8><0!##<;::0,8#<;798!##<;7:0,8#1!##<;450,8^#?#???????????????!##<;458,4#10!##<;798,8#;8808!##<;:98,8#<;788!##<;790,8#1!##<;440,8^#?#???????????????!##<;448,4#?!##<;788,8#;8730!##<;:90,8#<;778!##<;780,8#1!##<;430,8^#?#???????????????!##<;438,4#>!##<;778,8#;8650!##<;:88,8#<;768!##<;770,8#1!##<;420,8^#?#???????????????!##<;428,4#=!##<;768,8#;8560!##<;:80,8#<;9=0!##<;9=8,8#1!##<;6=8,8^#?#???????????????!##<;6>0,4#<!##<;9?8,8#!##<;9?0,8#!##<;9>8,8#!##<;9>0,8#2<0000002>!##<;9=0,8#;7=70!##<;:78,8#<;9:0!##<;9:8,8#1!##<;6<8,8^#?#???????????????!##<;6=0,4#;!##<;9<8,8#!##<;9<0,8#!##<;9;8,8#!##<;9;0,2#2<2>!##<;9:0,8#;7=20!##<;:70,8#<;758!##<;760,8#1!##<;598,8^#?#???????????????!##<;5:0,4#:!##<;758,8#;81>0!##<;:68,8#<;748!##<;750,8#1!##<;578,8^#?#???????????????!##<;580,4#9!##<;748,8#;80;0!##<;:60,8#<;738!##<;740,8#1!##<;588,8^#?#???????????????!##<;590,4#8!##<;738,8#;8148!##<;:58,8#<;728!##<;730,8#1!##<;568,8^#?#???????????????!##<;570,4#7!##<;728,8#;8018!##<;:50,8#<;8:8!##<;8;0,8#1!##<;558,8^#?#???????????????!##<;560,4#6!##<;8;8,8#1:?08!##<;5=1,1#1!##<;5=0,1#1!##<;5<8,8#1:?08!$2-<0,8#!##<;8:8,8#;7<<0!##<;:48,8#<;718!##<;720,8#1!##<;548,8^#?#???????????????!##<;550,4#5!##<;718,8#;7?70!##<;:40,8#<;708!##<;710,8#1!##<;6:8,8^#?#???????????????!##<;6;0,4#4!##<;708,8#;7>:0!##<;:38,8#<;920!##<;928,8#1!##<;6;8,8^#?#???????????????!##<;6<0,4#3!##<;938,1#!##<;930,8#162;0!##<;920,8#;7;68!##<;:30,8#<;6?8!##<;700,8#1!##<;410,8^#?#???????????????!##<;418,4#2!##<;6?8,8#;8520!##<;:28,8#<;6>8!##<;6?0,8#1!##<;400,8^#?#???????????????!##<;408,4#1!##<;6>8,8#;84>0!##<;;22,1#!##<;;20,2#4302!##<;:20,8#<;;18!##<;:10,8#<;:28!##<;:08,8#!##<;:00,8#;7:<0!##<;;18,8#1!$2-68,8$13!$2-60,8#<;5<8!$2-58,8#<;:00!$2-50,8#<;5>0!$2-48,8#7>9;4!$2-40,8#<;5<8!$2-38,8#<;5?0!$2-30,8$21!$2-28,8#847=8!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800400#800000000000&$2#10($2-400#400'$21#7???7?800400#7??????????8&$21#8)$2-400#400$21##8($21##8%#10000#;;028%#<;3?2#<;400%#<;40<#<;410%#<;41<#<;420%#<;42<#<;430%#<;43<#<;440%#<;44<#<;450%#<;45<#<;460%#<;46<#<;470%#<;47<#<;480%#<;48<#<;490%#<;49<#<;4:0%#<;4:<#<;4;0%#<;4;<#<;4<0%#<;4<<#<;4=0%#<;4=<#<;4>0%#<;4><#<;4?0%#<;4?<#<;500%#<;50<#<;510%#<;51<#<;520%#<;52<#<;530%#<;53<#<;540%#<;544#<;548%#<;554#<;558%#<;564#<;568%#<;574#<;578%#<;584#<;588%#<;594#<;598%#<;5:4#<;5<8%#<;5=2#<;5=8%#<;5>2#<;5>8%#<;5?2#<;6:8%#<;6;4#<;6;8%#<;6<4#<;6<8%#<;6=4#<;6=8%#<;6>4#<;6>8%#<;848#<;8:8%#<;939#<;9:0%#<;9;2#<;9;8%#<;;23#<;;30(##<;3?2#73>%#<<258#<<25<%#<<260#<<288%#<<290#<<2:0%#<<2:4#<<2:8(##<<258#58%#><>53#><>54%#><?28#><?2<!##><>30,8$22,220!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 542652 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_33b84d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 542560 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_33b84d.IT BndT_Eu_000.SegItab_Eu_33b84d.IT_sound BF NX0 BR XSTEP F0 PSS plan 542560 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uliA.

Module LibSegEu_upDL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_ecf45c.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_ecf45c.IT.
Definition ENDS : list Z := [362452].
Definition STOPS1 : list Z := [362452] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$2:$14$15$16$25$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483152 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-80)) (ELit 80);
   KRange (EVar 37) 25 134217728;
   KRange (EVar 42) 4096 140737488355328].
Definition ss0 : sym_state := SS 372088 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#587=4#587=4#5=#587=4,20##5:=8<+$2-50$3$4$5$6$7$8$9$2:+$25#1$<$=$>$?$10$11$12$2:$14$15$16$25$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?800050#800000000000&$2#10($2-50#50'$25#19#8000000'$2:#1000#800000000000,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_ecf45c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 372088 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_ecf45c.IT BndT_Eu_000.SegItab_Eu_ecf45c.IT_sound BF NX0 BR XSTEP F0 PSS plan 372088 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_upDL.
