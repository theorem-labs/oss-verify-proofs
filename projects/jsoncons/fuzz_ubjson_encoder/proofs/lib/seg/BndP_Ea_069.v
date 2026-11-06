(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ea0PlanKit Ea0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Ea_001 BndT_Ea_000.

Module LibSegEa_doDl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_b90e0e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_b90e0e.IT.
Definition ENDS : list Z := [1187220].
Definition STOPS1 : list Z := [1187220] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$21$22#13=9<0$=$>$?$10$11##11#13=9<0#1?161#$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?811000#800000000000&$2#10($2-70#70,$2-70#70%#10000#13:000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-70#70$21#+$22#1!##13=9>0,8+$2#280!##13=9>8,8+$2#241!##13=:08,8#121=58!##695:<0,8$28"%pstring).
Definition ss0 : sym_state := SS 1194420 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-112), ELit 112)].
Definition F0L : list SR.region := [(EVar 2, (-112), 112)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#121=94#121=94#5=#121=94,20##1239;8+$2-70$3$4$5#121=58$7$22#13=9<0$28$21$22$=$>$?$10$11##11#13=9<0#695:<0#$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-48,8$28!$2-40,8#!$2-38,8#1?161!$2-30,8#13=9<0!$2-28,8#11!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#1239;8'$2#7???7?811000#800000000000&$2#10($2-70#70,$2-70#28%#10000#13:000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-70#70$21#+$22#1!##13=9>0,8+$2#280!##13=9>8,8+$2#241!##13=:08,8#121=58!##695:<0,8$28,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1187220 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_b90e0e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1194420 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_b90e0e.IT BndT_Ea_001.SegItab_Ea_b90e0e.IT_sound BF NX0 BR XSTEP F0 PSS plan 1194420 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_doDl.

Module LibSegEa_doDs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_af9a5d.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_af9a5d.IT.
Definition ENDS : list Z := [493076].
Definition STOPS1 : list Z := [493076] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$21$22#13=9<0$=$>$?$10$11##11#13=9<0#1?161$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#40%#10000#13:000'$21#7???7?811000#7?????????>?'$22##3?)$2-40#40$21#+$22#1!##13=9>0,8+$2#280!##13=9>8,8+$2#241!##13=:50,4#????????"%pstring).
Definition ss0 : sym_state := SS 1194420 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-64), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (-64), 64)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78614#78614#5=#78614,20##122854+$2-40$3$4$5$6$7#13=9<0$22+$2#241$21$22$=$>$?$10$11$21##13=9<0#1?161$16$17$18$19$1:$1;$1<$1=$1>$1?,,12!$2-38,8#1?161!$2-30,8#13=9<0!$2-28,8#11!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#1239;8'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#8%#10000#13:000'$21#7???7?811000#7?????????>?'$22##3?)$2-40#40$21#+$22#1!##13=9>0,8+$2#280!##13=9>8,8+$2#241!##13=:50,4#????????,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 493076 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_af9a5d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1194420 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_af9a5d.IT BndT_Ea_001.SegItab_Ea_af9a5d.IT_sound BF NX0 BR XSTEP F0 PSS plan 1194420 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_doDs.

Module LibSegEa_doEa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_af9a5d.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_af9a5d.IT.
Definition ENDS : list Z := [493076].
Definition STOPS1 : list Z := [493076] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1300928; (EVar 34); EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; (EVar 34); EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#50%#10000#13:000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#50$21#+$22#1(##13=9>8#8!##13=9>8,8+$2#281!$2#38,8#1239;8!$2#30,8#25!$2#28,8#7???????!$2#20,8#!$2#18,8#11!$2#10,8#13=9<0!$2#8,8#1?161!##13=9<0,1#5!##13=9>0,8+$2#2<0!##13=:50,4#????????"%pstring).
Definition ss0 : sym_state := SS 1189972 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 80); (ELit 0, (1300968), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 80); (ELit 0, (1300968), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78614#78614#5=#78614,20##122854$2$3$4$5$6$7#13=9<0#1++$2$22#281#1?161#1$=$>$?$10$11#1?161##13=9<0#1?162#1#1?161$18$19#1$1;$1<$1=$1>$1?,,14!$2#8,8#1?162!$2#10,8#13=9<0!$2#18,8+$22#11!$2#20,8+@-1$22#7?????>>!$2#28,8#7???????!$2#30,8#25!$2#38,8#122?98!##13=9>8,8++$2$22#281'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#18%#10000#13:000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#50$21#+$22#1(##13=9>8#8!##13=9<0,1#5!##13=9>0,8+$2#2<0!##13=:50,4#????????,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 493076 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_af9a5d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1189972 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_af9a5d.IT BndT_Ea_001.SegItab_Ea_af9a5d.IT_sound BF NX0 BR XSTEP F0 PSS plan 1189972 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_doEa.

Module LibSegEa_doEb.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_b90e0e.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_b90e0e.IT.
Definition ENDS : list Z := [1187220].
Definition STOPS1 : list Z := [1187220] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1300928; ELit 63; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; ELit 63; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?811000#800000000000&$2#10($2-30#70,$2-30#70%#10000#13:000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-30#70$21#+$22#1(##13=9>8#8!##13=9>8,8+$2#281!$2#38,8#1239;8!$2#30,8#25!$2#28,8#7???????!$2#20,8#!$2#18,8#11!$2#10,8#13=9<0!$2#8,8#1?161!##13=9<0,1#5!##13=9>0,8+$2#2<0!##13=:08,8#121=58!##695:<0,8$28"%pstring).
Definition ss0 : sym_state := SS 1189972 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-48), ELit 112); (ELit 0, (1300968), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-48), 112); (ELit 0, (1300968), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#121=94#121=94#5=#121=94,20##122?98+$2-30$3$4$5#121=58$7#1#13=9<0$28#1?161#1$=$>$?$10$11#7?????:?#50#13=9<0#695:<0#1#1?161$18$19#1$1;$1<$1=$1>$1?,,17!$2-8,8$28!$2#,8#1!$2#8,8#1?162!$2#10,8#13=9<0!$2#18,8#50!$2#20,8#7?????:?!$2#28,8#7???????!$2#30,8#25!$2#38,8#122?98!##13=9>8,8+$2#2<0'$2#7???7?811000#800000000000&$2#10($2-30#70,$2-30#28%#10000#13:000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-30#70$21#+$22#1(##13=9>8#8!##13=9<0,1#5!##13=9>0,8+$2#2<0!##13=:08,8#121=58!##695:<0,8$28,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1187220 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_b90e0e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1189972 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_b90e0e.IT BndT_Ea_001.SegItab_Ea_b90e0e.IT_sound BF NX0 BR XSTEP F0 PSS plan 1189972 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_doEb.

Module LibSegEa_doEc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_77b57d.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_77b57d.IT.
Definition ENDS : list Z := [1187220].
Definition STOPS1 : list Z := [1187220] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (EVar 34); ELit 1300928; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; ELit 6904512; EVar 122; EVar 123; ELit 0; EVar 125; (EVar 34); EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#:?0%#10000#13:000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???;>28,8#(##13=9>0#8(##13=9>8#8(##13=9?8#8!##13=:18,8+$2#2:0!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#1239;8!$2#60,8#25!$2#58,8#7???????!$2#50,8#!$2#48,8#11!$2#40,8#13=9<0!$2#38,8#1?161!$2#30,8#!##13=9<0,1#5!##13=:50,4#????????!##1426=9,1#1!##1419?8,8#7???8000!##13;1<0,8#12;488!$2#=0,8#695:<0!$2#220,8$28!$2#288,8#122=:8!$2#280,8#13=9<0!$2#278,8#1?14>!$2#270,8#695:<0!$2#268,8#1!$2#260,8#696298!$2#258,8#5!$2#250,8$16!$2#248,8$17!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##13=:08,8#121=58"%pstring).
Definition ss0 : sym_state := SS 1187308 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-2112), ELit 2800); (ELit 0, (1300960), ELit 8); (ELit 0, (1300968), ELit 8); (ELit 0, (1300984), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-2112), 2800); (ELit 0, (1300960), 8); (ELit 0, (1300968), 8); (ELit 0, (1300984), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#121=94#121=94#5=#121=94,20##122=<8+$2#220$3$4#2$6$7##13=9<0$28###121=58##1#1#:#695:<0#1#696298#695:<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,3?!$2#248,8$28!$2#250,8$16!$2#258,8#!$2#260,8#696298!$2#268,8#1!$2#270,8#695:<0!$2#278,8+$22#12!$2#280,8#13=9<0!$2#288,8#122=<8!##13=9>8,8+$2#2:1!$2#2:0,1#:!$2-20,8#!$2-18,8#1?161!$2-10,8#1!$2-8,8#1?162!$2#,8#13=9<0!$2#8,8#!$2#10,8#1?161!$2#18,8#1!$2#20,8#13=9<0!$2#28,8#122854!$2#38,8#1?162!$2#40,8#13=9<0!$2#48,8+$22#11!$2#50,8+@-1$22#7?????>>!$2#58,8#7???????!$2#60,8#25!$2#68,8#122?98!##13=9?8,8+$2#2:0!##13=9>0,8+$2#2?0'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#820,$2#30#8,$2#70#1=8,$2#290#10,$2#2:1#?%#10000#13:000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???;>28,8#(##13=9>0#8(##13=9>8#8(##13=9?8#8!##13=:18,8+$2#2:0!##13=:20,8#50!##695:<0,8$28!$2#30,8#!##13=9<0,1#5!##13=:50,4#????????!##1426=9,1#1!##1419?8,8#7???8000!##13;1<0,8#12;488!$2#=0,8#695:<0!$2#220,8$28!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##13=:08,8#121=58,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1187220 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_77b57d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1187308 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_77b57d.IT BndT_Ea_000.SegItab_Ea_77b57d.IT_sound BF NX0 BR XSTEP F0 PSS plan 1187308 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_doEc.

Module LibSegEa_doFa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_397977.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_397977.IT.
Definition ENDS : list Z := [1187220].
Definition STOPS1 : list Z := [1187220] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1300928; ELit 1; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; ELit 1; EVar 123; EVar 124; EVar 125; ELit 1; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#270%#10000#13:000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#270$21#+$22#1(##13=9>8#8!##13=9>8,8++$2$22#281!$2#38,8#122?98!$2#30,8#25!$2#28,8#7???????!$2#20,8&1#7?????>>$22!$2#18,8+$22#11!$2#10,8#13=9<0!$2#8,8#1?162!$2#:0,8#695:<0!##695:<0,8$28!$2#1?0,8$28!$2#258,8#122=:8!$2#250,8#13=9<0!$2#248,8#1?14>!$2#240,8#695:<0!$2#238,8#1!$2#230,8#696298!$2#228,8#5!$2#220,8$16!$2#218,8$17!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##13=:08,8#121=58"%pstring).
Definition ss0 : sym_state := SS 1189972 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 624); (ELit 0, (1300968), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 624); (ELit 0, (1300968), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#121=94#121=94#5=#121=94,20##122=<8+$2#1?0$3$4$5$6$7##13=9<0$28###121=58$>$?$10$11#695:<0#1#696298#695:<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,22!$2#218,8$28!$2#220,8$16!$2#228,8#!$2#230,8#696298!$2#238,8#1!$2#240,8#695:<0!$2#248,8+$22#12!$2#250,8#13=9<0!$2#258,8#122=<8!##13=9>8,8++$2$22#282'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#228%#10000#13:000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#270$21#+$22#1(##13=9>8#8!$2#38,8#122?98!$2#30,8#25!$2#28,8#7???????!$2#20,8&1#7?????>>$22!$2#18,8+$22#11!$2#10,8#13=9<0!$2#8,8#1?162!$2#:0,8#695:<0!##695:<0,8$28!$2#1?0,8$28!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##13=:08,8#121=58,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1187220 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_397977.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1189972 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_397977.IT BndT_Ea_000.SegItab_Ea_397977.IT_sound BF NX0 BR XSTEP F0 PSS plan 1189972 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_doFa.

Module LibSegEa_doGa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_87af9b.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_87af9b.IT.
Definition ENDS : list Z := [1156092].
Definition STOPS1 : list Z := [1156092] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1300928; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6904512; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##13=:18,8+$2#80!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8+$22#12!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!##13=9<0,4#5!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#1?14>!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:86><!$2#210,8$8!$2#208,8$9!$2#200,8$12"%pstring).
Definition ss0 : sym_state := SS 1187308 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1300928), ELit 4); (ELit 0, (1300960), ELit 8); (ELit 0, (1300968), ELit 8); (ELit 0, (1300984), ELit 8); (ELit 0, (1301016), ELit 8); (ELit 0, (1301024), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1300928), 4); (ELit 0, (1300960), 8); (ELit 0, (1300968), 8); (ELit 0, (1300984), 8); (ELit 0, (1301016), 8); (ELit 0, (1301024), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11:3?<#11:3?<#5=#11:3?<,20##:8718+$2#250$3$4$5$6$7$8$9#2$28$28$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!##13=9<0,4#5!##13=:20,8#!##13=:18,8#696298!##13=9?8,8#!##13=9>8,8#!##13=9>0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8+$22#12!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#1?14>!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:86><!$2#210,8$8!$2#208,8$9!$2#200,8$12,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1156092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_87af9b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1187308 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_87af9b.IT BndT_Ea_000.SegItab_Ea_87af9b.IT_sound BF NX0 BR XSTEP F0 PSS plan 1187308 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_doGa.

Module LibSegEa_doGb1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_d2d119.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_d2d119.IT.
Definition ENDS : list Z := [1187220].
Definition STOPS1 : list Z := [1187220] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1; ELit 1300928; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; ELit 6904512; EVar 122; EVar 123; EVar 124; EVar 125; ELit 1; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#2:0,$2-10#2:0%#10000#13:000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#2:0$21#+$22#1(##13=9>0#8(##13=9>8#8(##13=9?8#8!##13=:18,8+$2#2:0!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#122?98!$2#60,8#25!$2#58,8#7???????!$2#50,8#7?????:?!$2#48,8#50!$2#40,8#13=9<0!$2#38,8#1?162!$2#30,8#1!$2#=0,8#695:<0!$2#220,8$28!$2#288,8#122=:8!$2#280,8#13=9<0!$2#278,8#1?14>!$2#270,8#695:<0!$2#268,8#1!$2#260,8#696298!$2#258,8#5!$2#250,8$16!$2#248,8$17!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##13=:08,8#121=58"%pstring).
Definition ss0 : sym_state := SS 1187308 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 672); (ELit 0, (1300960), ELit 8); (ELit 0, (1300968), ELit 8); (ELit 0, (1300984), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 672); (ELit 0, (1300960), 8); (ELit 0, (1300968), 8); (ELit 0, (1300984), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#121=94#121=94#5=#121=94,20##122=<8+$2#220$3$4$5$6$7##13=9<0$28###121=58$>$?$10$11#695:<0#1#696298#695:<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!$2#248,8$28!$2#250,8$16!$2#258,8#!$2#260,8#696298!$2#268,8#1!$2#270,8#695:<0!$2#278,8#51!$2#280,8#13=9<0!$2#288,8#122=<8!##13=9?8,8+$2#2:0!##13=9>8,8+$2#2:0!##13=9>0,8+$2#2?0'$2#7???7?811000#800000000000&$2#10($2-10#2:0,$2-10#258%#10000#13:000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#2:0$21#+$22#1(##13=9>0#8(##13=9>8#8(##13=9?8#8!##13=:18,8+$2#2:0!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#122?98!$2#60,8#25!$2#58,8#7???????!$2#50,8#7?????:?!$2#48,8#50!$2#40,8#13=9<0!$2#38,8#1?162!$2#30,8#1!$2#=0,8#695:<0!$2#220,8$28!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##13=:08,8#121=58,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1187220 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_d2d119.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1187308 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_d2d119.IT BndT_Ea_001.SegItab_Ea_d2d119.IT_sound BF NX0 BR XSTEP F0 PSS plan 1187308 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_doGb1.

Module LibSegEa_doGb2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_87af9b.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_87af9b.IT.
Definition ENDS : list Z := [1156092].
Definition STOPS1 : list Z := [1156092] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1300928; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6904512; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##13=:18,8+$2#80!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8#51!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!##13=9<0,4#5!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#1?14>!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:86><!$2#210,8$8!$2#208,8$9!$2#200,8$12"%pstring).
Definition ss0 : sym_state := SS 1187308 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1300928), ELit 4); (ELit 0, (1300960), ELit 8); (ELit 0, (1300968), ELit 8); (ELit 0, (1300984), ELit 8); (ELit 0, (1301016), ELit 8); (ELit 0, (1301024), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1300928), 4); (ELit 0, (1300960), 8); (ELit 0, (1300968), 8); (ELit 0, (1300984), 8); (ELit 0, (1301016), 8); (ELit 0, (1301024), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11:3?<#11:3?<#5=#11:3?<,20##:8718+$2#250$3$4$5$6$7$8$9#2$28$28$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!##13=9<0,4#5!##13=:20,8#!##13=:18,8#696298!##13=9?8,8#!##13=9>8,8#!##13=9>0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8#51!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#1?14>!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:86><!$2#210,8$8!$2#208,8$9!$2#200,8$12,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1156092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_87af9b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1187308 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_87af9b.IT BndT_Ea_000.SegItab_Ea_87af9b.IT_sound BF NX0 BR XSTEP F0 PSS plan 1187308 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_doGb2.

Module LibSegEa_doGc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_87af9b.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_87af9b.IT.
Definition ENDS : list Z := [1156092].
Definition STOPS1 : list Z := [1156092] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1300928; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6904512; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##13=:18,8+$2#80!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8+$22#12!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!##13=9<0,4#5!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#1?14>!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:86><!$2#210,8$8!$2#208,8$9!$2#200,8$12"%pstring).
Definition ss0 : sym_state := SS 1187308 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1300928), ELit 4); (ELit 0, (1300960), ELit 8); (ELit 0, (1300968), ELit 8); (ELit 0, (1300984), ELit 8); (ELit 0, (1301016), ELit 8); (ELit 0, (1301024), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1300928), 4); (ELit 0, (1300960), 8); (ELit 0, (1300968), 8); (ELit 0, (1300984), 8); (ELit 0, (1301016), 8); (ELit 0, (1301024), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11:3?<#11:3?<#5=#11:3?<,20##:8718+$2#250$3$4$5$6$7$8$9#2$28$28$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!##13=9<0,4#5!##13=:20,8#!##13=:18,8#696298!##13=9?8,8#!##13=9>8,8#!##13=9>0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8+$22#12!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#1?14>!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:86><!$2#210,8$8!$2#208,8$9!$2#200,8$12,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1156092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_87af9b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1187308 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_87af9b.IT BndT_Ea_000.SegItab_Ea_87af9b.IT_sound BF NX0 BR XSTEP F0 PSS plan 1187308 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_doGc.

Module LibSegEa_dpA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_6094a6.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_6094a6.IT.
Definition ENDS : list Z := [1190560].
Definition STOPS1 : list Z := [1190560] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:891<$2$3$4$5$6$7$8$9#14?;7+$2#18$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",24'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#<:0%#10000#13:000#&6$2#3#7???7?8<#18!##7???:9?0,8#!##800<:<50,8#(##13=:;0#4(##13=:;8#8(##13=:<0#8(##13=:=0#8(##13=:=8#8(##13=:>8#8(##13=:?8#8(##13=;38#4(##6962:0#1!##1426=8,1#1!##1=357<,1#1!##1419?8,8#7???8000!##13;040,8#128?84!##13;048,8#122<:0!##695:<0,8$28!##13=;3<,4#????????!##13=:;0,4#5!##13=;10,8#400!##13=:=0,8#!##13=;38,4#!##13=;08,8#6962:0!##13=;40,4#:!##1426=9,1#1!##13;1<0,8#12;488!$2#18,4#!##13;1<8,8#12;88<!##13=:?8,8#122:44!##13=;28,4#1"%pstring).
Definition ss0 : sym_state := SS 408880 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1301168), ELit 4); (ELit 0, (1301176), ELit 8); (ELit 0, (1301184), ELit 8); (ELit 0, (1301200), ELit 8); (ELit 0, (1301208), ELit 8); (ELit 0, (1301224), ELit 8); (ELit 0, (1301240), ELit 8); (ELit 0, (1301304), ELit 4); (ELit 0, (6906528), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1301168), 4); (ELit 0, (1301176), 8); (ELit 0, (1301184), 8); (ELit 0, (1301200), 8); (ELit 0, (1301208), 8); (ELit 0, (1301224), 8); (ELit 0, (1301240), 8); (ELit 0, (1301304), 4); (ELit 0, (6906528), 1)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#122::0#122::0#5=#122::0,20##122838+$2-450$3$4#$6$7#695:<0#1#1#5413+$2-450#14?;9#5413#1#13=:;0#1=#14?;9#1##14?;:#1#14?;9#1##1#1$1<$1=$1>$1?,,<2!##13=:?8,8#121=58!$2-448,8$28!$2-440,8#13=:;0!$2-438,8#122838!$2-428,8#14?;:!$2-420,8#13=:;0!$2-418,8#1!$2-410,8#7??????>!$2-408,8#7???????!$2-400,8#25!$2-3?8,8#122?98!##13=:=8,8#6962:1!$2-480,8#1!$2-478,8+$2-340!$2-470,8#!$2-468,8#14?;9!$2-460,8#13=:;0!$2-458,8#!$2-450,8+$2-340!##6962:0,1#30!$2-340,1#30!$2-430,8#!$2-3>8,8#!$2-3=0,8#1!$2-3>0,8#!$2-3?0,8#10=?3!$2-3=8,8#!$2-380,8#!$2-1=0,8+$2#20!$2-3<8,8^#?#???????<<<<<<<=!$2-3<0,8^#?#??????????>????!$2-388,8#<<<<<<<!$2-3:0,8#12889!$2-240,8$28!$2-390,8#695:<0!$2-398,8#!$2-3:8,8+$2-1=0!$2-3;8,8+$2-170!$2-3;0,8+$2-<8!$2-238,8$1;!$2-230,8$1:!$2-228,8$19!$2-220,8$18!$2-218,8$17!$2-210,8$16!$2-208,8#5!$2-200,8#!$2-1?8,8#1!$2-1?0,8#695:<0!$2-1>8,8#14?;7!$2-1>0,8#13=:;0!$2-1=8,8#122=:8!##13=:=0,8#6966:0!##13=:<0,8#!##13=:;8,8#!##13=:>8,8#6962:0!##13=;38,4^#?#???????????????!##13=:;0,4#5!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,8#!$2-:8,8#!$2-1<8,8+$2#18!$2-:0,8$28!$2-98,8$15!$2-90,8$14!$2-88,8$13!$2-80,8+$2#18!$2-78,8#13=:;0!$2-70,8#14?;7!$2-68,8#68444!$2-900,8^#?#???????????????!$2-8>1,1#!$2-8>2,1#!$2-8>3,1#!$2-8>4,1#!$2-8>5,1#!$2-8>6,1#!$2-8>7,1#!$2-8>8,1#!$2-8>9,1#!$2-8>:,1#!$2-8>;,1#!$2-8><,1#!$2-8>=,1#!$2-8>>,1#!$2-8>?,1#!$2-8?0,1#!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?4,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-8?8,1#!$2-901,1#!$2-902,1#!$2-903,1#!$2-904,1#!$2-905,1#!$2-906,1#!$2-907,1#!$2-908,1#!$2-940,8#:!$2-938,8#14?;7!$2-930,8+$2-60!$2-928,8#67<98!$2-918,8+$2-=8!$2-910,8#208<?!$2-60,8+$2#18!$2-58,8+$2#18!$2-50,8$12!$2-48,8+$2#18!$2-40,8#14?;7!$2-38,8#678=4!$2-8=0,8^#?#???????????????!$2-8;1,1#!$2-8;2,1#!$2-8;3,1#!$2-8;4,1#!$2-8;5,1#!$2-8;6,1#!$2-8;7,1#!$2-8;8,1#!$2-8;9,1#!$2-8;:,1#!$2-8;;,1#!$2-8;<,1#!$2-8;=,1#!$2-8;>,1#!$2-8;?,1#!$2-8<0,1#!$2-8<1,1#!$2-8<2,1#!$2-8<3,1#!$2-8<4,1#!$2-8<5,1#!$2-8<6,1#!$2-8<7,1#!$2-8<8,1#!$2-8=1,1#!$2-8=2,1#!$2-8=3,1#!$2-8=4,1#!$2-8=5,1#!$2-8=6,1#!$2-8=7,1#!$2-8=8,1#!$2-8>0,8#14831!$2-28,8+$2#18!$2-20,8+$2#18!$2-18,8$9!$2-10,8$8!$2-8,8#:891<'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#360,$2-920#8,$2-8;0#430,$2-378#38,$2-33?#??,$2-1<0#?8,$2-30#8%#10000#13:000#&6$2#3#7???7?8<#18!##7???:9?0,8#!##800<:<50,8#(##13=:;0#4(##13=:;8#8(##13=:<0#8(##13=:=0#8(##13=:=8#8(##13=:>8#8(##13=:?8#8(##13=;38#4(##6962:0#1!##1426=8,1#1!##1=357<,1#1!##1419?8,8#7???8000!##13;040,8#128?84!##13;048,8#122<:0!##695:<0,8$28!##13=;3<,4#????????!##13=;10,8#400!##13=;08,8#6962:0!##13=;40,4#:!##1426=9,1#1!##13;1<0,8#12;488!$2#18,4#!##13;1<8,8#12;88<!##13=;28,4#1,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1190560 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_6094a6.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 408880 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_6094a6.IT BndT_Ea_000.SegItab_Ea_6094a6.IT_sound BF NX0 BR XSTEP F0 PSS plan 408880 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_dpA.

Module LibSegEa_dpA2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_614795.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_614795.IT.
Definition ENDS : list Z := [690460].
Definition STOPS1 : list Z := [690460] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:891<$2$3$4$5$6$7$8$9#14?;7+$2#18$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#<:0%#10000#13:000#&6$2#3#7???7?8<#18!##7???:9?0,8#!##800<:<50,8#(##13=:;0#4(##13=:=8#8(##6962:0#1(##6962:1#1!##1426=8,1#1!##1=357<,1#1!##1419?8,8#7???8000!##13;040,8#128?84!##13;048,8#122<:0!##695:<0,8$28!##13=;3<,4#????????!##13=:;0,4#5!##13=;10,8#400!##13=:=0,8#6966:0!##13=:=8,8#6962:0!##13=;40,4#????????!##1426=9,1#1!##13;1<0,8#12;488!$2#18,4#!##13;1<8,8#12;88<"%pstring).
Definition ss0 : sym_state := SS 408880 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1301168), ELit 4); (ELit 0, (1301208), ELit 8); (ELit 0, (6906528), ELit 1); (ELit 0, (6906529), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1301168), 4); (ELit 0, (1301208), 8); (ELit 0, (6906528), 1); (ELit 0, (6906529), 1)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:891<#:891<#5=#:891<,20##:891<$2$3$4#2$6$7$8$9#2$28$28#6962:2##2#1#:$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;7!##13=:;0,4#5!##13=:=8,8#6962:2!##6962:1,1#:!$2-480,8#1!$2-478,8#14?;9!$2-470,8#1!$2-468,8#14?;:!$2-460,8#13=:;0!$2-458,8#!$2-450,8#14?;9!$2-448,8#1!$2-440,8#13=:;0!$2-438,8#122854!$2-428,8#14?;:!$2-420,8#13=:;0!$2-418,8#1!$2-410,8#7??????>!$2-408,8#7???????!$2-400,8#25!$2-3?8,8#122?98!##6962:0,1#30!$2-340,1#30!$2-430,8#!$2-3>8,8#!$2-3=0,8#1!$2-3>0,8#!$2-3?0,8#10=?3!$2-3=8,8#!$2-380,8#!$2-1=0,8+$2#20!$2-3<8,8^#?#???????<<<<<<<=!$2-3<0,8^#?#??????????>????!$2-388,8#<<<<<<<!$2-3:0,8#12889!$2-240,8$28!$2-390,8#695:<0!$2-398,8#!$2-3:8,8+$2-1=0!$2-3;8,8+$2-170!$2-3;0,8+$2-<8!$2-238,8$1;!$2-230,8$1:!$2-228,8$19!$2-220,8$18!$2-218,8$17!$2-210,8$16!$2-208,8#5!$2-200,8#!$2-1?8,8#1!$2-1?0,8#695:<0!$2-1>8,8#14?;7!$2-1>0,8#13=:;0!$2-1=8,8#122=:8!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,8#!$2-:8,8#!$2-1<8,8+$2#18!$2-:0,8$28!$2-98,8$15!$2-90,8$14!$2-88,8$13!$2-80,8+$2#18!$2-78,8#13=:;0!$2-70,8#14?;7!$2-68,8#68444!$2-900,8^#?#???????????????!$2-8>1,1#!$2-8>2,1#!$2-8>3,1#!$2-8>4,1#!$2-8>5,1#!$2-8>6,1#!$2-8>7,1#!$2-8>8,1#!$2-8>9,1#!$2-8>:,1#!$2-8>;,1#!$2-8><,1#!$2-8>=,1#!$2-8>>,1#!$2-8>?,1#!$2-8?0,1#!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?4,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-8?8,1#!$2-901,1#!$2-902,1#!$2-903,1#!$2-904,1#!$2-905,1#!$2-906,1#!$2-907,1#!$2-908,1#!$2-940,8#:!$2-938,8#14?;7!$2-930,8+$2-60!$2-928,8#67<98!$2-918,8+$2-=8!$2-910,8#208<?!$2-60,8+$2#18!$2-58,8+$2#18!$2-50,8$12!$2-48,8+$2#18!$2-40,8#14?;7!$2-38,8#678=4!$2-8=0,8^#?#???????????????!$2-8;1,1#!$2-8;2,1#!$2-8;3,1#!$2-8;4,1#!$2-8;5,1#!$2-8;6,1#!$2-8;7,1#!$2-8;8,1#!$2-8;9,1#!$2-8;:,1#!$2-8;;,1#!$2-8;<,1#!$2-8;=,1#!$2-8;>,1#!$2-8;?,1#!$2-8<0,1#!$2-8<1,1#!$2-8<2,1#!$2-8<3,1#!$2-8<4,1#!$2-8<5,1#!$2-8<6,1#!$2-8<7,1#!$2-8<8,1#!$2-8=1,1#!$2-8=2,1#!$2-8=3,1#!$2-8=4,1#!$2-8=5,1#!$2-8=6,1#!$2-8=7,1#!$2-8=8,1#!$2-8>0,8#14831!$2-28,8+$2#18!$2-20,8+$2#18!$2-18,8$9!$2-10,8$8!$2-8,8#:891<'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#360,$2-920#8,$2-8;0#430,$2-378#38,$2-33?#??,$2-1<0#?8,$2-30#8%#10000#13:000#&6$2#3#7???7?8<#18!##7???:9?0,8#!##800<:<50,8#(##13=:;0#4(##13=:=8#8(##6962:0#1(##6962:1#1!##1426=8,1#1!##1=357<,1#1!##1419?8,8#7???8000!##13;040,8#128?84!##13;048,8#122<:0!##695:<0,8$28!##13=;3<,4#????????!##13=;10,8#400!##13=:=0,8#6966:0!##13=;40,4#????????!##1426=9,1#1!##13;1<0,8#12;488!$2#18,4#!##13;1<8,8#12;88<,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 690460 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_614795.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 408880 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_614795.IT BndT_Ea_000.SegItab_Ea_614795.IT_sound BF NX0 BR XSTEP F0 PSS plan 408880 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_dpA2.

Module LibSegEa_dpA3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_614795.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_614795.IT.
Definition ENDS : list Z := [690460].
Definition STOPS1 : list Z := [690460] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:891<$2$3$4$5$6$7$8$9#14?;7+$2#18$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#<:0%#10000#13:000#&6$2#3#7???7?8<#18!##7???:9?0,8#!##800<:<50,8#(##13=:;0#4(##13=:=8#8(##6962:2#1(##6962:3#1!##1426=8,1#1!##1=357<,1#1!##1419?8,8#7???8000!##13;040,8#128?84!##13;048,8#122<:0!##695:<0,8$28!##13=;3<,4#????????!##13=:;0,4#5!##13=;10,8#400!##13=:=0,8#6966:0!##13=:=8,8#6962:2!##13=;40,4#????????!##1426=9,1#1!##13;1<0,8#12;488!$2#18,4#!##13;1<8,8#12;88<"%pstring).
Definition ss0 : sym_state := SS 408880 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1301168), ELit 4); (ELit 0, (1301208), ELit 8); (ELit 0, (6906530), ELit 1); (ELit 0, (6906531), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1301168), 4); (ELit 0, (1301208), 8); (ELit 0, (6906530), 1); (ELit 0, (6906531), 1)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:891<#:891<#5=#:891<,20##:891<$2$3$4#2$6$7$8$9#2$28$28#6962:4###1#:$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;7!##13=:;0,4#5!##13=:=8,8#6962:4!##6962:3,1#:!$2-480,8#1!$2-478,8#14?;9!$2-470,8#1!$2-468,8#14?;:!$2-460,8#13=:;0!$2-458,8#!$2-450,8#14?;9!$2-448,8#1!$2-440,8#13=:;0!$2-438,8#122854!$2-428,8#14?;:!$2-420,8#13=:;0!$2-418,8#1!$2-410,8#7??????>!$2-408,8#7???????!$2-400,8#25!$2-3?8,8#122?98!##6962:2,1#30!$2-340,1#30!$2-430,8#!$2-3>8,8#!$2-3=0,8#1!$2-3>0,8#!$2-3?0,8#10=?3!$2-3=8,8#!$2-380,8#!$2-1=0,8+$2#20!$2-3<8,8^#?#???????<<<<<<<=!$2-3<0,8^#?#??????????>????!$2-388,8#<<<<<<<!$2-3:0,8#12889!$2-240,8$28!$2-390,8#695:<0!$2-398,8#!$2-3:8,8+$2-1=0!$2-3;8,8+$2-170!$2-3;0,8+$2-<8!$2-238,8$1;!$2-230,8$1:!$2-228,8$19!$2-220,8$18!$2-218,8$17!$2-210,8$16!$2-208,8#5!$2-200,8#!$2-1?8,8#1!$2-1?0,8#695:<0!$2-1>8,8#14?;7!$2-1>0,8#13=:;0!$2-1=8,8#122=:8!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,8#!$2-:8,8#!$2-1<8,8+$2#18!$2-:0,8$28!$2-98,8$15!$2-90,8$14!$2-88,8$13!$2-80,8+$2#18!$2-78,8#13=:;0!$2-70,8#14?;7!$2-68,8#68444!$2-900,8^#?#???????????????!$2-8>1,1#!$2-8>2,1#!$2-8>3,1#!$2-8>4,1#!$2-8>5,1#!$2-8>6,1#!$2-8>7,1#!$2-8>8,1#!$2-8>9,1#!$2-8>:,1#!$2-8>;,1#!$2-8><,1#!$2-8>=,1#!$2-8>>,1#!$2-8>?,1#!$2-8?0,1#!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?4,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-8?8,1#!$2-901,1#!$2-902,1#!$2-903,1#!$2-904,1#!$2-905,1#!$2-906,1#!$2-907,1#!$2-908,1#!$2-940,8#:!$2-938,8#14?;7!$2-930,8+$2-60!$2-928,8#67<98!$2-918,8+$2-=8!$2-910,8#208<?!$2-60,8+$2#18!$2-58,8+$2#18!$2-50,8$12!$2-48,8+$2#18!$2-40,8#14?;7!$2-38,8#678=4!$2-8=0,8^#?#???????????????!$2-8;1,1#!$2-8;2,1#!$2-8;3,1#!$2-8;4,1#!$2-8;5,1#!$2-8;6,1#!$2-8;7,1#!$2-8;8,1#!$2-8;9,1#!$2-8;:,1#!$2-8;;,1#!$2-8;<,1#!$2-8;=,1#!$2-8;>,1#!$2-8;?,1#!$2-8<0,1#!$2-8<1,1#!$2-8<2,1#!$2-8<3,1#!$2-8<4,1#!$2-8<5,1#!$2-8<6,1#!$2-8<7,1#!$2-8<8,1#!$2-8=1,1#!$2-8=2,1#!$2-8=3,1#!$2-8=4,1#!$2-8=5,1#!$2-8=6,1#!$2-8=7,1#!$2-8=8,1#!$2-8>0,8#14831!$2-28,8+$2#18!$2-20,8+$2#18!$2-18,8$9!$2-10,8$8!$2-8,8#:891<'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#360,$2-920#8,$2-8;0#430,$2-378#38,$2-33?#??,$2-1<0#?8,$2-30#8%#10000#13:000#&6$2#3#7???7?8<#18!##7???:9?0,8#!##800<:<50,8#(##13=:;0#4(##13=:=8#8(##6962:2#1(##6962:3#1!##1426=8,1#1!##1=357<,1#1!##1419?8,8#7???8000!##13;040,8#128?84!##13;048,8#122<:0!##695:<0,8$28!##13=;3<,4#????????!##13=;10,8#400!##13=:=0,8#6966:0!##13=;40,4#????????!##1426=9,1#1!##13;1<0,8#12;488!$2#18,4#!##13;1<8,8#12;88<,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 690460 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_614795.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 408880 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_614795.IT BndT_Ea_000.SegItab_Ea_614795.IT_sound BF NX0 BR XSTEP F0 PSS plan 408880 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_dpA3.

Module LibSegEa_dpA4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_614795.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_614795.IT.
Definition ENDS : list Z := [690460].
Definition STOPS1 : list Z := [690460] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:891<$2$3$4$5$6$7$8$9#14?;7+$2#18$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#<:0%#10000#13:000#&6$2#3#7???7?8<#18!##7???:9?0,8#!##800<:<50,8#(##13=:;0#4(##13=:=8#8(##6962:4#1(##6962:5#1!##1426=8,1#1!##1=357<,1#1!##1419?8,8#7???8000!##13;040,8#128?84!##13;048,8#122<:0!##695:<0,8$28!##13=;3<,4#????????!##13=:;0,4#5!##13=;10,8#400!##13=:=0,8#6966:0!##13=:=8,8#6962:4!##13=;40,4#????????!##1426=9,1#1!##13;1<0,8#12;488!$2#18,4#!##13;1<8,8#12;88<"%pstring).
Definition ss0 : sym_state := SS 408880 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1301168), ELit 4); (ELit 0, (1301208), ELit 8); (ELit 0, (6906532), ELit 1); (ELit 0, (6906533), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1301168), 4); (ELit 0, (1301208), 8); (ELit 0, (6906532), 1); (ELit 0, (6906533), 1)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:891<#:891<#5=#:891<,20##:891<$2$3$4#2$6$7$8$9#2$28$28#6962:6##2#1#:$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;7!##13=:;0,4#5!##13=:=8,8#6962:6!##6962:5,1#:!$2-480,8#1!$2-478,8#14?;9!$2-470,8#1!$2-468,8#14?;:!$2-460,8#13=:;0!$2-458,8#!$2-450,8#14?;9!$2-448,8#1!$2-440,8#13=:;0!$2-438,8#122854!$2-428,8#14?;:!$2-420,8#13=:;0!$2-418,8#1!$2-410,8#7??????>!$2-408,8#7???????!$2-400,8#25!$2-3?8,8#122?98!##6962:4,1#30!$2-340,1#30!$2-430,8#!$2-3>8,8#!$2-3=0,8#1!$2-3>0,8#!$2-3?0,8#10=?3!$2-3=8,8#!$2-380,8#!$2-1=0,8+$2#20!$2-3<8,8^#?#???????<<<<<<<=!$2-3<0,8^#?#??????????>????!$2-388,8#<<<<<<<!$2-3:0,8#12889!$2-240,8$28!$2-390,8#695:<0!$2-398,8#!$2-3:8,8+$2-1=0!$2-3;8,8+$2-170!$2-3;0,8+$2-<8!$2-238,8$1;!$2-230,8$1:!$2-228,8$19!$2-220,8$18!$2-218,8$17!$2-210,8$16!$2-208,8#5!$2-200,8#!$2-1?8,8#1!$2-1?0,8#695:<0!$2-1>8,8#14?;7!$2-1>0,8#13=:;0!$2-1=8,8#122=:8!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,8#!$2-:8,8#!$2-1<8,8+$2#18!$2-:0,8$28!$2-98,8$15!$2-90,8$14!$2-88,8$13!$2-80,8+$2#18!$2-78,8#13=:;0!$2-70,8#14?;7!$2-68,8#68444!$2-900,8^#?#???????????????!$2-8>1,1#!$2-8>2,1#!$2-8>3,1#!$2-8>4,1#!$2-8>5,1#!$2-8>6,1#!$2-8>7,1#!$2-8>8,1#!$2-8>9,1#!$2-8>:,1#!$2-8>;,1#!$2-8><,1#!$2-8>=,1#!$2-8>>,1#!$2-8>?,1#!$2-8?0,1#!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?4,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-8?8,1#!$2-901,1#!$2-902,1#!$2-903,1#!$2-904,1#!$2-905,1#!$2-906,1#!$2-907,1#!$2-908,1#!$2-940,8#:!$2-938,8#14?;7!$2-930,8+$2-60!$2-928,8#67<98!$2-918,8+$2-=8!$2-910,8#208<?!$2-60,8+$2#18!$2-58,8+$2#18!$2-50,8$12!$2-48,8+$2#18!$2-40,8#14?;7!$2-38,8#678=4!$2-8=0,8^#?#???????????????!$2-8;1,1#!$2-8;2,1#!$2-8;3,1#!$2-8;4,1#!$2-8;5,1#!$2-8;6,1#!$2-8;7,1#!$2-8;8,1#!$2-8;9,1#!$2-8;:,1#!$2-8;;,1#!$2-8;<,1#!$2-8;=,1#!$2-8;>,1#!$2-8;?,1#!$2-8<0,1#!$2-8<1,1#!$2-8<2,1#!$2-8<3,1#!$2-8<4,1#!$2-8<5,1#!$2-8<6,1#!$2-8<7,1#!$2-8<8,1#!$2-8=1,1#!$2-8=2,1#!$2-8=3,1#!$2-8=4,1#!$2-8=5,1#!$2-8=6,1#!$2-8=7,1#!$2-8=8,1#!$2-8>0,8#14831!$2-28,8+$2#18!$2-20,8+$2#18!$2-18,8$9!$2-10,8$8!$2-8,8#:891<'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#360,$2-920#8,$2-8;0#430,$2-378#38,$2-33?#??,$2-1<0#?8,$2-30#8%#10000#13:000#&6$2#3#7???7?8<#18!##7???:9?0,8#!##800<:<50,8#(##13=:;0#4(##13=:=8#8(##6962:4#1(##6962:5#1!##1426=8,1#1!##1=357<,1#1!##1419?8,8#7???8000!##13;040,8#128?84!##13;048,8#122<:0!##695:<0,8$28!##13=;3<,4#????????!##13=;10,8#400!##13=:=0,8#6966:0!##13=;40,4#????????!##1426=9,1#1!##13;1<0,8#12;488!$2#18,4#!##13;1<8,8#12;88<,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 690460 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_614795.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 408880 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_614795.IT BndT_Ea_000.SegItab_Ea_614795.IT_sound BF NX0 BR XSTEP F0 PSS plan 408880 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_dpA4.
