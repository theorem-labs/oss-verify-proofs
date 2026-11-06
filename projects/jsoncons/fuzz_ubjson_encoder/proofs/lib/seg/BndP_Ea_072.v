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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Ea_000 BndT_Ea_001.

Module LibSegEa_duD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_0ba9bc.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_0ba9bc.IT.
Definition ENDS : list Z := [1194420].
Definition STOPS1 : list Z := [1194420] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$22$;$<$=$>$?$10$11#7??????8#7#13=9<0#162;1#$21$18^#?#???????????????#$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?811000#800000000000&$2#10($2-8;0#8>0,$2-8;0#8>0%#10000#13:000'$21#7???7?811000#7?????????>?'$22##1????)$2-8;0#8>0$21#+$22#1(##13=9>8#8!##13=9<0,1#5!##13=9>0,8+$2#280!##13=9>8,8+$2#237!##13=:50,4#????????!##1426=9,1#1!##13;1<0,8#12;488!+$21$22#,1#"%pstring).
Definition ss0 : sym_state := SS 1193064 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-2224), ELit 2272); (ELit 0, (1300968), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-2224), 2272); (ELit 0, (1300968), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#1239;4#1239;4#5=#1239;4,20##123890$2$3$4$5$6$7#25#7???????$21$22#13=9<0+$2#237##3$10$11##7#13=9<0#162;1#$21#$22$22$22$1<$1=$1>$1?,,28!##13=9>8,8+$2#237!$2-90,8#!$2-88,8$21!$2-80,8#!$2-78,8#162;1!$2-70,8#13=9<0!$2-68,8#!$2-60,8#10=?3!$2-58,8#!$2-50,8#13=9<0!$2-48,8#122854!$2-38,8#162;1!$2-30,8#13=9<0!$2-28,8#7!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#123890!$2#8,8#!$2#20,8$22!$2#10,8$22!$2#,8#10=?3!$2#18,8#'$2#7???7?811000#800000000000&$2#10($2-8;0#8>0,$2-8;0#820,$2-40#8,$2#28#8%#10000#13:000'$21#7???7?811000#7?????????>?'$22##1????)$2-8;0#8>0$21#+$22#1(##13=9>8#8!##13=9<0,1#5!##13=9>0,8+$2#280!##13=:50,4#????????!##1426=9,1#1!##13;1<0,8#12;488!+$21$22#,1#,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1194420 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_0ba9bc.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1193064 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_0ba9bc.IT BndT_Ea_000.SegItab_Ea_0ba9bc.IT_sound BF NX0 BR XSTEP F0 PSS plan 1193064 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_duD.

Module LibSegEa_duDl.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$21$22#13=9<0$=$>$?$10$11##7#13=9<0#162;1#$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?811000#800000000000&$2#10($2-70#70,$2-70#70%#10000#13:000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-70#70$21#+$22#1!##13=9>0,8+$2#280!##13=9>8,8+$2#237!##13=:08,8#121=58!##695:<0,8$28"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#121=94#121=94#5=#121=94,20##1239;8+$2-70$3$4$5#121=58$7$22#13=9<0$28$21$22$=$>$?$10$11##7#13=9<0#695:<0#$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-48,8$28!$2-40,8#!$2-38,8#162;1!$2-30,8#13=9<0!$2-28,8#7!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#1239;8'$2#7???7?811000#800000000000&$2#10($2-70#70,$2-70#28%#10000#13:000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-70#70$21#+$22#1!##13=9>0,8+$2#280!##13=9>8,8+$2#237!##13=:08,8#121=58!##695:<0,8$28,8<!"%pstring).
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
End LibSegEa_duDl.

Module LibSegEa_duDs.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$21$22#13=9<0$=$>$?$10$11##7#13=9<0#162;1$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#40%#10000#13:000'$21#7???7?811000#7?????????>?'$22##49)$2-40#40$21#+$22#1!##13=9>0,8+$2#280!##13=9>8,8+$2#237!##13=:50,4#????????"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78614#78614#5=#78614,20##122854+$2-40$3$4$5$6$7#13=9<0$22+$2#237$21$22$=$>$?$10$11$21##13=9<0#162;1$16$17$18$19$1:$1;$1<$1=$1>$1?,,12!$2-38,8#162;1!$2-30,8#13=9<0!$2-28,8#7!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#1239;8'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#8%#10000#13:000'$21#7???7?811000#7?????????>?'$22##49)$2-40#40$21#+$22#1!##13=9>0,8+$2#280!##13=9>8,8+$2#237!##13=:50,4#????????,8<!"%pstring).
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
End LibSegEa_duDs.

Module LibSegEa_duEa.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#50%#10000#13:000'$21#7???7?811000#7?????????>?'$22##42)$2-10#50$21#+$22#1(##13=9>8#8!##13=9>8,8+$2#277!$2#38,8#1239;8!$2#30,8#25!$2#28,8#7???????!$2#20,8#!$2#18,8#7!$2#10,8#13=9<0!$2#8,8#162;1!##13=9<0,1#5!##13=9>0,8+$2#2<0!##13=:50,4#????????"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#78614#78614#5=#78614,20##122854$2$3$4$5$6$7#13=9<0#7++$2$22#277#162;1#7$=$>$?$10$11#162;1##13=9<0#162;8#7#162;1$18$19#7$1;$1<$1=$1>$1?,,14!$2#8,8#162;8!$2#10,8#13=9<0!$2#18,8+$22#7!$2#20,8+@-1$22#7??????8!$2#28,8#7???????!$2#30,8#25!$2#38,8#122?98!##13=9>8,8++$2$22#277'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#18%#10000#13:000'$21#7???7?811000#7?????????>?'$22##42)$2-10#50$21#+$22#1(##13=9>8#8!##13=9<0,1#5!##13=9>0,8+$2#2<0!##13=:50,4#????????,8<!"%pstring).
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
End LibSegEa_duEa.

Module LibSegEa_duEb.
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
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1300928; (EVar 34); EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; (EVar 34); EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?811000#800000000000&$2#10($2-30#70,$2-30#70%#10000#13:000'$21#7???7?811000#7?????????>?'$22#43#49)$2-30#70$21#+$22#1(##13=9>8#8!##13=9>8,8+$2#277!$2#38,8#1239;8!$2#30,8#25!$2#28,8#7???????!$2#20,8#!$2#18,8#7!$2#10,8#13=9<0!$2#8,8#162;1!##13=9<0,1#5!##13=9>0,8+$2#2<0!##13=:08,8#121=58!##695:<0,8$28"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#121=94#121=94#5=#121=94,20##122?98+$2-30$3$4$5#121=58$7#7#13=9<0$28#162;1#7$=$>$?$10$11+@-1$22#7??????8+$22#7#13=9<0#695:<0#7#162;1$18$19#7$1;$1<$1=$1>$1?,,17!$2-8,8$28!$2#,8#7!$2#8,8#162;8!$2#10,8#13=9<0!$2#18,8+$22#7!$2#20,8+@-1$22#7??????8!$2#28,8#7???????!$2#30,8#25!$2#38,8#122?98!##13=9>8,8++$2$22#277'$2#7???7?811000#800000000000&$2#10($2-30#70,$2-30#28%#10000#13:000'$21#7???7?811000#7?????????>?'$22#43#49)$2-30#70$21#+$22#1(##13=9>8#8!##13=9<0,1#5!##13=9>0,8+$2#2<0!##13=:08,8#121=58!##695:<0,8$28,8<!"%pstring).
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
End LibSegEa_duEb.

Module LibSegEa_duEc.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#:?0%#10000#13:000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???:<50,8#(##13=9>0#8(##13=9>8#8(##13=9?8#8!##13=:18,8+$2#2:0!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#1239;8!$2#60,8#25!$2#58,8#7???????!$2#50,8#!$2#48,8#7!$2#40,8#13=9<0!$2#38,8#162;1!$2#30,8#!##13=9<0,1#5!##13=:50,4#????????!##1426=9,1#1!##1419?8,8#7???8000!##13;1<0,8#12;488!$2#=0,8#695:<0!$2#220,8$28!$2#288,8#122=:8!$2#280,8#13=9<0!$2#278,8#162:8!$2#270,8#695:<0!$2#268,8#1!$2#260,8#696298!$2#258,8#5!$2#250,8$16!$2#248,8$17!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##13=:08,8#121=58"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#121=94#121=94#5=#121=94,20##122=<8+$2#220$3$4+$2#2:7$6$7##13=9<0$28###121=58##55#54#:#695:<0#1#696298#695:<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,45!$2#248,8$28!$2#250,8$16!$2#258,8#!$2#260,8#696298!$2#268,8#1!$2#270,8#695:<0!$2#278,8+$22#>!$2#280,8#13=9<0!$2#288,8#122=<8!##13=9>8,8+$2#2:7!$2#2:6,1#:!$2#2:5,1#54!$2#2:4,1#55!$2#2:3,1#50!$2#2:2,1#4>!$2#2:1,1#49!$2#2:0,1#20!$2-20,8#!$2-18,8#162;1!$2-10,8#7!$2-8,8#162;8!$2#,8#13=9<0!$2#8,8#!$2#10,8#162;1!$2#18,8#7!$2#20,8#13=9<0!$2#28,8#122854!$2#38,8#162;8!$2#40,8#13=9<0!$2#48,8+$22#7!$2#50,8+@-1$22#7??????8!$2#58,8#7???????!$2#60,8#25!$2#68,8#122?98!##13=9?8,8+$2#2:0!##13=9>0,8+$2#2?0'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#820,$2#30#8,$2#70#1=8,$2#290#10,$2#2:7#9%#10000#13:000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???:<50,8#(##13=9>0#8(##13=9>8#8(##13=9?8#8!##13=:18,8+$2#2:0!##13=:20,8#50!##695:<0,8$28!$2#30,8#!##13=9<0,1#5!##13=:50,4#????????!##1426=9,1#1!##1419?8,8#7???8000!##13;1<0,8#12;488!$2#=0,8#695:<0!$2#220,8$28!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##13=:08,8#121=58,8<!"%pstring).
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
End LibSegEa_duEc.

Module LibSegEa_duFa.
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
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1300928; ELit 7; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; ELit 7; EVar 123; EVar 124; EVar 125; ELit 7; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#270%#10000#13:000'$21#7???7?811000#7?????????>?'$22##42)$2-10#270$21#+$22#1(##13=9>8#8!##13=9>8,8++$2$22#277!$2#38,8#122?98!$2#30,8#25!$2#28,8#7???????!$2#20,8&1#7??????8$22!$2#18,8+$22#7!$2#10,8#13=9<0!$2#8,8#162;8!$2#:0,8#695:<0!##695:<0,8$28!$2#1?0,8$28!$2#258,8#122=:8!$2#250,8#13=9<0!$2#248,8#162:8!$2#240,8#695:<0!$2#238,8#1!$2#230,8#696298!$2#228,8#5!$2#220,8$16!$2#218,8$17!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##13=:08,8#121=58"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#121=94#121=94#5=#121=94,20##122=<8+$2#1?0$3$4$5$6$7##13=9<0$28###121=58$>$?$10$11#695:<0#1#696298#695:<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,22!$2#218,8$28!$2#220,8$16!$2#228,8#!$2#230,8#696298!$2#238,8#1!$2#240,8#695:<0!$2#248,8+$22#>!$2#250,8#13=9<0!$2#258,8#122=<8!##13=9>8,8++$2$22#27>'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#228%#10000#13:000'$21#7???7?811000#7?????????>?'$22##42)$2-10#270$21#+$22#1(##13=9>8#8!$2#38,8#122?98!$2#30,8#25!$2#28,8#7???????!$2#20,8&1#7??????8$22!$2#18,8+$22#7!$2#10,8#13=9<0!$2#8,8#162;8!$2#:0,8#695:<0!##695:<0,8$28!$2#1?0,8$28!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##13=:08,8#121=58,8<!"%pstring).
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
End LibSegEa_duFa.

Module LibSegEa_duGa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_9fa7c1.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_9fa7c1.IT.
Definition ENDS : list Z := [1156092].
Definition STOPS1 : list Z := [1156092] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1300928; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6904512; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",30'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22##42)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##13=:18,8+$2#80!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8+$22#>!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!##13=9<0,4#5!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#162:8!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:863<!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#119<34!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11:3?<#11:3?<#5=#11:3?<,20##119<38+$2#2:0$3$4$5$6$7$29$2:$8$28$28$=$>$?$10$11$2;$2<$2=$2>$2?$30$18$19$1:$1;$1<$1=$1>$1?,,33!##13=9<0,4#5!##13=:20,8#!##13=:18,8#696298!##13=9?8,8#!##13=9>8,8#!##13=9>0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22##42)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8+$22#>!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#162:8!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:863<!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#119<34!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30,8<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_9fa7c1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1187308 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_9fa7c1.IT BndT_Ea_001.SegItab_Ea_9fa7c1.IT_sound BF NX0 BR XSTEP F0 PSS plan 1187308 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_duGa.

Module LibSegEa_duGb1.
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
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 7; ELit 1300928; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; ELit 6904512; EVar 122; EVar 123; EVar 124; EVar 125; ELit 7; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#2:0,$2-10#2:0%#10000#13:000'$21#7???7?811000#7?????????>?'$22#43#49)$2-10#2:0$21#+$22#1(##13=9>0#8(##13=9>8#8(##13=9?8#8!##13=:18,8+$2#2:0!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#122?98!$2#60,8#25!$2#58,8#7???????!$2#50,8&1#7??????8$22!$2#48,8+$22#7!$2#40,8#13=9<0!$2#38,8#162;8!$2#30,8#7!$2#=0,8#695:<0!$2#220,8$28!$2#288,8#122=:8!$2#280,8#13=9<0!$2#278,8#162:8!$2#270,8#695:<0!$2#268,8#1!$2#260,8#696298!$2#258,8#5!$2#250,8$16!$2#248,8$17!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##13=:08,8#121=58"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#121=94#121=94#5=#121=94,20##122=<8+$2#220$3$4$5$6$7##13=9<0$28###121=58$>$?$10$11#695:<0#1#696298#695:<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!$2#248,8$28!$2#250,8$16!$2#258,8#!$2#260,8#696298!$2#268,8#1!$2#270,8#695:<0!$2#278,8+$22#>!$2#280,8#13=9<0!$2#288,8#122=<8!##13=9?8,8+$2#2:0!##13=9>8,8+$2#2:0!##13=9>0,8+$2#2?0'$2#7???7?811000#800000000000&$2#10($2-10#2:0,$2-10#258%#10000#13:000'$21#7???7?811000#7?????????>?'$22#43#49)$2-10#2:0$21#+$22#1(##13=9>0#8(##13=9>8#8(##13=9?8#8!##13=:18,8+$2#2:0!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#122?98!$2#60,8#25!$2#58,8#7???????!$2#50,8&1#7??????8$22!$2#48,8+$22#7!$2#40,8#13=9<0!$2#38,8#162;8!$2#30,8#7!$2#=0,8#695:<0!$2#220,8$28!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##13=:08,8#121=58,8<!"%pstring).
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
End LibSegEa_duGb1.

Module LibSegEa_duGb2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_9fa7c1.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_9fa7c1.IT.
Definition ENDS : list Z := [1156092].
Definition STOPS1 : list Z := [1156092] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1300928; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6904512; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",30'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22#43#49)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##13=:18,8+$2#80!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8+$22#>!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!##13=9<0,4#5!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#162:8!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:863<!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#119<34!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11:3?<#11:3?<#5=#11:3?<,20##119<38+$2#2:0$3$4$5$6$7$29$2:$8$28$28$=$>$?$10$11$2;$2<$2=$2>$2?$30$18$19$1:$1;$1<$1=$1>$1?,,33!##13=9<0,4#5!##13=:20,8#!##13=:18,8#696298!##13=9?8,8#!##13=9>8,8#!##13=9>0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22#43#49)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8+$22#>!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#162:8!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:863<!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#119<34!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30,8<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_9fa7c1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1187308 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_9fa7c1.IT BndT_Ea_001.SegItab_Ea_9fa7c1.IT_sound BF NX0 BR XSTEP F0 PSS plan 1187308 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_duGb2.

Module LibSegEa_duGc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_9fa7c1.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_9fa7c1.IT.
Definition ENDS : list Z := [1156092].
Definition STOPS1 : list Z := [1156092] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1300928; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 6904512; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",30'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##13=:18,8+$2#80!##13=:20,8#50!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8+$22#>!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!##13=9<0,4#5!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#162:8!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:863<!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#119<34!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11:3?<#11:3?<#5=#11:3?<,20##119<38+$2#2:0$3$4$5$6$7$29$2:$8$28$28$=$>$?$10$11$2;$2<$2=$2>$2?$30$18$19$1:$1;$1<$1=$1>$1?,,33!##13=9<0,4#5!##13=:20,8#!##13=:18,8#696298!##13=9?8,8#!##13=9>8,8#!##13=9>0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#13:000'$21#7???7?811000#7?????????>?'$22#4:#1????)$2-10#10$21#+$22#1(##13=9<0#4(##13=9>0#8(##13=9>8#8(##13=9?8#8(##13=:18#8(##13=:20#8!##695:<0,8$28!$2#28,8$28!$2#68,8#122=<8!$2#60,8#13=9<0!$2#58,8+$22#>!$2#50,8#695:<0!$2#48,8#1!$2#40,8#696298!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#68<?4!$2#1=0,8#162:8!$2#1<8,8#13=9<0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:863<!$2#210,8$8!$2#208,8$9!$2#200,8$12!$2#298,8#119<34!$2#290,8$29!$2#288,8$2:!$2#280,8$2;!$2#278,8$2<!$2#270,8$2=!$2#268,8$2>!$2#260,8$2?!$2#258,8$30,8<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_9fa7c1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1187308 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_9fa7c1.IT BndT_Ea_001.SegItab_Ea_9fa7c1.IT_sound BF NX0 BR XSTEP F0 PSS plan 1187308 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_duGc.

Module LibSegEa_hkdA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_b94b52.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_b94b52.IT.
Definition ENDS : list Z := [508928].
Definition STOPS1 : list Z := [508928] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8$29'$24#1000#7???????????&$24#10'$25##800000000000'$29#1001#7???????????'&1$29+$24$25##800000000000"%pstring).
Definition ss0 : sym_state := SS 698092 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-16), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-16), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7<400#7<400#5=#7<400,20##::758+$2-10$3$4$5$6$7$8$9$24$29+$24$25$29&6+$21#8#3$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#132000#13:000!##1419?8,8#7???8000!##141:00,4#1'$21#698000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#688000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8$29'$24#1000#7???????????&$24#10'$25##800000000000'$29#1001#7???????????'&1$29+$24$25##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 508928 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_b94b52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 698092 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_b94b52.IT BndT_Ea_001.SegItab_Ea_b94b52.IT_sound BF NX0 BR XSTEP F0 PSS plan 698092 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_hkdA.

Module LibSegEa_hkdB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_001.SegItab_Ea_b94b52.ITR.
Definition IT : itab := BndT_Ea_001.SegItab_Ea_b94b52.IT.
Definition ENDS : list Z := [698212].
Definition STOPS1 : list Z := [698212] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332491264 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-4096)) (ELit 4096);
   KWord (SA (EVar 2) (-8)) 8 (EVar 43);
   KWord (SA (EVar 2) (-16)) 8 (EVar 44)].
Definition ss0 : sym_state := SS 698200 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#::764#::764#5=#::764,20#$2;$2$3$4$5$6$7$2<$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?802000#800000000000&$2#10($2-1000#1000!$2-8,8$2;!$2-10,8$2<,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 698212 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_001.SegItab_Ea_b94b52.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 698200 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_001.SegItab_Ea_b94b52.IT BndT_Ea_001.SegItab_Ea_b94b52.IT_sound BF NX0 BR XSTEP F0 PSS plan 698200 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_hkdB.

Module LibSegEa_hkeA1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ea_000.SegItab_Ea_36e79a.ITR.
Definition IT : itab := BndT_Ea_000.SegItab_Ea_36e79a.IT.
Definition ENDS : list Z := [726144].
Definition STOPS1 : list Z := [726144] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801020#800000000000&$2#10($2-20#20'$:#698000#7??????????8&$:#8)##7???7000#100000001000$:##8#&6$:#3#7???8000#1)$2-20#20$:##8!$:#,8$21'$21#698000#7?????????>8&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-20#20$21##18)$:##8$21##18!$21#,8$22'$22#1000#7???????????&$22#10!$21#8,8$24'&1$24$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 726028 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-32), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-32), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;1480#;1480#5=#;1480,20#$1+$2-20$3$4$5$6$7$:#7???8000$21+@-1$22$24$22^#:#::::::::::::::;$>$?$10$11+&6$:#3#7???8000$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1;!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#13:000!##1419?8,8#7???8000!##141:00,4#1'$2#7???7?801020#800000000000&$2#10($2-20#20'$:#698000#7??????????8&$:#8)##7???7000#100000001000$:##8#&6$:#3#7???8000#1)$2-20#20$:##8!$:#,8$21'$21#698000#7?????????>8&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-20#20$21##18)$:##8$21##18!$21#,8$22'$22#1000#7???????????&$22#10!$21#8,8$24'&1$24$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 726144 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ea_000.SegItab_Ea_36e79a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726028 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Ea_000.SegItab_Ea_36e79a.IT BndT_Ea_000.SegItab_Ea_36e79a.IT_sound BF NX0 BR XSTEP F0 PSS plan 726028 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEa_hkeA1.
