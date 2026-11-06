(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Es0PlanKit Es0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require SegPlanFast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Es_000.

Module LibSegEs_vgS1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_cf1b47.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_cf1b47.IT.
Definition ENDS : list Z := [234752].
Definition STOPS1 : list Z := [234752] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$17$18$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328].
Definition ss0 : sym_state := SS 234744 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#39500#39500#5=#39500,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21+&9$24#??#13:81+$21$23#8#1-3>#?5-41#2#13:81#3$24$16&9$24#??$18$19$1:$1;#>=#9?#?0#90,,3'$21##800000000000'$23#1#4000000'+$21$23#1#800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 234752 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_cf1b47.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234744 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_cf1b47.IT BndT_Es_000.SegItab_Es_cf1b47.IT_sound BF NX0 BR XSTEP F0 PSS plan 234744 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_vgS1.

Module LibSegEs_vgS2_0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_cf1b47.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_cf1b47.IT.
Definition ENDS : list Z := [234916; 234956].
Definition STOPS1 : list Z := [234916; 234956] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25#$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 234756 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#3958<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#1$25#$21$1:$1;#>=#9?#?0#90,,4'$21##800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#1$25#$21$1:$1;#>=#9?#?0#90,,5'&3&7@#100000000000000$24#38-3>#1#1'$21##800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39590,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#1$25#$21$1:$1;#>=#9?#?0#90,,5'&3&7@#100000000000000$24#38-3>##'$21##800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#1$25#$21$1:$1;#>=#9?#?0#90,,6'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'$21##800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#1$25#$21$1:$1;#>=#9?#?0#90,,6'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'$21##800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PEnd 2))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_cf1b47.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234756 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_cf1b47.IT BndT_Es_000.SegItab_Es_cf1b47.IT_sound BF NX0 BR XSTEP F0 PSS plan 234756 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_vgS2_0.

Module LibSegEs_vgS2_1a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_cf1b47.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_cf1b47.IT.
Definition ENDS : list Z := [234916; 234956].
Definition STOPS1 : list Z := [234916; 234956] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25#1$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 1;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 234756 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#5+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25#1$19$1:$1;#>=#9?#?0#90,,4'$21##800000000000'$23#1#1'+$21$23#1#800000000000'$25##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_cf1b47.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234756 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_cf1b47.IT BndT_Es_000.SegItab_Es_cf1b47.IT_sound BF NX0 BR XSTEP F0 PSS plan 234756 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_vgS2_1a.

Module LibSegEs_vgS2_1b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_cf1b47.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_cf1b47.IT.
Definition ENDS : list Z := [234916; 234956].
Definition STOPS1 : list Z := [234916; 234956] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25#1$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 2 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KWord (SA (EVar 33) 1) 1 (EVar 39);
   KRange (EVar 39) 0 255;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 234756 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39554,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21],,1$27+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,6'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#2+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,7'&3-41],,1$27#1#1'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#3955<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,7'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39570,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,8'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#395:0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,9'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,:'&4&9],,1$27#??#90#1#1'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,:'&4&9],,1$27#??#90##'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39574,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,9'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39578,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,:'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,;'&4#8?&9],,1$27#??#1#1'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition ex17 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,;'&4#8?&9],,1$27#??##'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s17 : sym_state := snd (snd ex17).

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#3958<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,:'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition arms19 := Eval vm_compute in (match SGP.branch_probe IT s18 with Some e => SGP.case_arms s18 e 0 | None => None end).
Definition f19 : sym_state := match arms19 with Some (Some s, _) => s | _ => s18 end.
Definition t19 : sym_state := match arms19 with Some (_, Some s) => s | _ => s18 end.

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,;'&3&7@#100000000000000$24#38-3>#1#1'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39590,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,;'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition arms22 := Eval vm_compute in (match SGP.branch_probe IT s21 with Some e => SGP.case_arms s21 e 0 | None => None end).
Definition f22 : sym_state := match arms22 with Some (Some s, _) => s | _ => s21 end.
Definition t22 : sym_state := match arms22 with Some (_, Some s) => s | _ => s21 end.

Definition ex23 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,<'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s23 : sym_state := snd (snd ex23).

Definition ex24 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,<'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s24 : sym_state := snd (snd ex24).

Definition ex25 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39560,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,8'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s25 : sym_state := snd (snd ex25).

Definition arms26 := Eval vm_compute in (match SGP.branch_probe IT s25 with Some e => SGP.case_arms s25 e 0 | None => None end).
Definition f26 : sym_state := match arms26 with Some (Some s, _) => s | _ => s25 end.
Definition t26 : sym_state := match arms26 with Some (_, Some s) => s | _ => s25 end.

Definition ex27 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39598,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,9'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s27 : sym_state := snd (snd ex27).

Definition arms28 := Eval vm_compute in (match SGP.branch_probe IT s27 with Some e => SGP.case_arms s27 e 0 | None => None end).
Definition f28 : sym_state := match arms28 with Some (Some s, _) => s | _ => s27 end.
Definition t28 : sym_state := match arms28 with Some (_, Some s) => s | _ => s27 end.

Definition ex29 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,:'&4&9],,1$27#??#:0#1#1'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s29 : sym_state := snd (snd ex29).

Definition ex30 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,:'&4&9],,1$27#??#:0##'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s30 : sym_state := snd (snd ex30).

Definition ex31 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39564,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,9'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s31 : sym_state := snd (snd ex31).

Definition arms32 := Eval vm_compute in (match SGP.branch_probe IT s31 with Some e => SGP.case_arms s31 e 0 | None => None end).
Definition f32 : sym_state := match arms32 with Some (Some s, _) => s | _ => s31 end.
Definition t32 : sym_state := match arms32 with Some (_, Some s) => s | _ => s31 end.

Definition ex33 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39568,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,:'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s33 : sym_state := snd (snd ex33).

Definition arms34 := Eval vm_compute in (match SGP.branch_probe IT s33 with Some e => SGP.case_arms s33 e 0 | None => None end).
Definition f34 : sym_state := match arms34 with Some (Some s, _) => s | _ => s33 end.
Definition t34 : sym_state := match arms34 with Some (_, Some s) => s | _ => s33 end.

Definition ex35 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,;'&4#9?&9],,1$27#??#1#1'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s35 : sym_state := snd (snd ex35).

Definition ex36 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,;'&4#9?&9],,1$27#??##'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s36 : sym_state := snd (snd ex36).

Definition ex37 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#3958<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,:'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s37 : sym_state := snd (snd ex37).

Definition arms38 := Eval vm_compute in (match SGP.branch_probe IT s37 with Some e => SGP.case_arms s37 e 0 | None => None end).
Definition f38 : sym_state := match arms38 with Some (Some s, _) => s | _ => s37 end.
Definition t38 : sym_state := match arms38 with Some (_, Some s) => s | _ => s37 end.

Definition ex39 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,;'&3&7@#100000000000000$24#38-3>#1#1'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s39 : sym_state := snd (snd ex39).

Definition ex40 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39590,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,;'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s40 : sym_state := snd (snd ex40).

Definition arms41 := Eval vm_compute in (match SGP.branch_probe IT s40 with Some e => SGP.case_arms s40 e 0 | None => None end).
Definition f41 : sym_state := match arms41 with Some (Some s, _) => s | _ => s40 end.
Definition t41 : sym_state := match arms41 with Some (_, Some s) => s | _ => s40 end.

Definition ex42 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,<'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s42 : sym_state := snd (snd ex42).

Definition ex43 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#2$25#1+$21#1+$21#2$1;#>=#9?#?0#90,,<'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'$21##800000000000'$23#2#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??'$25##??,3<!"%pstring).
Definition s43 : sym_state := snd (snd ex43).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 1)) (SGA.mkplan (fst ex11) (SGP.PEnd 2)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PEnd 3)) (SGA.mkplan (fst ex17) (SGP.PEnd 4)))) (SGA.mkplan (fst ex18) (SGP.PBranch (SGA.mkplan (fst ex20) (SGP.PEnd 5)) (SGA.mkplan (fst ex21) (SGP.PBranch (SGA.mkplan (fst ex23) (SGP.PEnd 6)) (SGA.mkplan (fst ex24) (SGP.PEnd 7)))))))))) (SGA.mkplan (fst ex25) (SGP.PBranch (SGA.mkplan (fst ex27) (SGP.PBranch (SGA.mkplan (fst ex29) (SGP.PEnd 8)) (SGA.mkplan (fst ex30) (SGP.PEnd 9)))) (SGA.mkplan (fst ex31) (SGP.PBranch (SGA.mkplan (fst ex33) (SGP.PBranch (SGA.mkplan (fst ex35) (SGP.PEnd 10)) (SGA.mkplan (fst ex36) (SGP.PEnd 11)))) (SGA.mkplan (fst ex37) (SGP.PBranch (SGA.mkplan (fst ex39) (SGP.PEnd 12)) (SGA.mkplan (fst ex40) (SGP.PBranch (SGA.mkplan (fst ex42) (SGP.PEnd 13)) (SGA.mkplan (fst ex43) (SGP.PEnd 14))))))))))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s10).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s10).
Definition ps1 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s11).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s11).
Definition ps2 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s16).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s16).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s16 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s16 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s16).
Definition ps3 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s17).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s17).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s17 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s17 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s17).
Definition ps4 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s20).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s20).
Definition ps5 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s23).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s23).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s23 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s23 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s23).
Definition ps6 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s24).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s24).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s24 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s24 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s24).
Definition ps7 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition regs_out8 : list expr := Eval vm_compute in (s_regs s29).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s29).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s29 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s29 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s29).
Definition ps8 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out8 (ELit 0))) (seq 1 31)) F0L cells8.

Definition regs_out9 : list expr := Eval vm_compute in (s_regs s30).
Definition exit_sp_off9 : Z := Eval vm_compute in (spoff_of s30).
Definition cells9 : list kentry := Eval vm_compute in (cells_of s30 exit_sp_off9).
Definition nfresh9 : nat := Eval vm_compute in (s_next s30 - NX0)%nat.
Definition exit_pc9 : Z := Eval vm_compute in (s_pc s30).
Definition ps9 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out9 (ELit 0))) (seq 1 31)) F0L cells9.

Definition regs_out10 : list expr := Eval vm_compute in (s_regs s35).
Definition exit_sp_off10 : Z := Eval vm_compute in (spoff_of s35).
Definition cells10 : list kentry := Eval vm_compute in (cells_of s35 exit_sp_off10).
Definition nfresh10 : nat := Eval vm_compute in (s_next s35 - NX0)%nat.
Definition exit_pc10 : Z := Eval vm_compute in (s_pc s35).
Definition ps10 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out10 (ELit 0))) (seq 1 31)) F0L cells10.

Definition regs_out11 : list expr := Eval vm_compute in (s_regs s36).
Definition exit_sp_off11 : Z := Eval vm_compute in (spoff_of s36).
Definition cells11 : list kentry := Eval vm_compute in (cells_of s36 exit_sp_off11).
Definition nfresh11 : nat := Eval vm_compute in (s_next s36 - NX0)%nat.
Definition exit_pc11 : Z := Eval vm_compute in (s_pc s36).
Definition ps11 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out11 (ELit 0))) (seq 1 31)) F0L cells11.

Definition regs_out12 : list expr := Eval vm_compute in (s_regs s39).
Definition exit_sp_off12 : Z := Eval vm_compute in (spoff_of s39).
Definition cells12 : list kentry := Eval vm_compute in (cells_of s39 exit_sp_off12).
Definition nfresh12 : nat := Eval vm_compute in (s_next s39 - NX0)%nat.
Definition exit_pc12 : Z := Eval vm_compute in (s_pc s39).
Definition ps12 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out12 (ELit 0))) (seq 1 31)) F0L cells12.

Definition regs_out13 : list expr := Eval vm_compute in (s_regs s42).
Definition exit_sp_off13 : Z := Eval vm_compute in (spoff_of s42).
Definition cells13 : list kentry := Eval vm_compute in (cells_of s42 exit_sp_off13).
Definition nfresh13 : nat := Eval vm_compute in (s_next s42 - NX0)%nat.
Definition exit_pc13 : Z := Eval vm_compute in (s_pc s42).
Definition ps13 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out13 (ELit 0))) (seq 1 31)) F0L cells13.

Definition regs_out14 : list expr := Eval vm_compute in (s_regs s43).
Definition exit_sp_off14 : Z := Eval vm_compute in (spoff_of s43).
Definition cells14 : list kentry := Eval vm_compute in (cells_of s43 exit_sp_off14).
Definition nfresh14 : nat := Eval vm_compute in (s_next s43 - NX0)%nat.
Definition exit_pc14 : Z := Eval vm_compute in (s_pc s43).
Definition ps14 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out14 (ELit 0))) (seq 1 31)) F0L cells14.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8; ps9; ps10; ps11; ps12; ps13; ps14] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_cf1b47.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234756 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_cf1b47.IT BndT_Es_000.SegItab_Es_cf1b47.IT_sound BF NX0 BR XSTEP F0 PSS plan 234756 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_vgS2_1b.

Module LibSegEs_vgS2_2a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_cf1b47.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_cf1b47.IT.
Definition ENDS : list Z := [234916; 234956].
Definition STOPS1 : list Z := [234916; 234956] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25#2$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 2;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 234756 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#5+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25#2$19$1:$1;#>=#9?#?0#90,,4'$21##800000000000'$23#1#2'+$21$23#1#800000000000'$25##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_cf1b47.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234756 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_cf1b47.IT BndT_Es_000.SegItab_Es_cf1b47.IT_sound BF NX0 BR XSTEP F0 PSS plan 234756 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_vgS2_2a.

Module LibSegEs_vgS2_2b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_cf1b47.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_cf1b47.IT.
Definition ENDS : list Z := [234916; 234956].
Definition STOPS1 : list Z := [234916; 234956] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25#2$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 3 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KWord (SA (EVar 33) 1) 1 (EVar 39);
   KRange (EVar 39) 0 255;
   KWord (SA (EVar 33) 2) 1 (EVar 40);
   KRange (EVar 40) 0 255;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 234756 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39548,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21],,1$28+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#3$1;#>=#9?#?0#90,,8'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#2+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#3$1;#>=#9?#?0#90,,9'&3-41],,1$28#1#1'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39554,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21],,1$27+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,9'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#2+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,:'&3-41],,1$27#1#1'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#3955<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,:'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.

Definition ex9 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39570,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,;'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s9 : sym_state := snd (snd ex9).

Definition arms10 := Eval vm_compute in (match SGP.branch_probe IT s9 with Some e => SGP.case_arms s9 e 0 | None => None end).
Definition f10 : sym_state := match arms10 with Some (Some s, _) => s | _ => s9 end.
Definition t10 : sym_state := match arms10 with Some (_, Some s) => s | _ => s9 end.

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#395:0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,<'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition arms12 := Eval vm_compute in (match SGP.branch_probe IT s11 with Some e => SGP.case_arms s11 e 0 | None => None end).
Definition f12 : sym_state := match arms12 with Some (Some s, _) => s | _ => s11 end.
Definition t12 : sym_state := match arms12 with Some (_, Some s) => s | _ => s11 end.

Definition ex13 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,='&4&9],,1$27#??#90#1#1'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s13 : sym_state := snd (snd ex13).

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,='&4&9],,1$27#??#90##'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition ex15 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39574,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,<'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s15 : sym_state := snd (snd ex15).

Definition arms16 := Eval vm_compute in (match SGP.branch_probe IT s15 with Some e => SGP.case_arms s15 e 0 | None => None end).
Definition f16 : sym_state := match arms16 with Some (Some s, _) => s | _ => s15 end.
Definition t16 : sym_state := match arms16 with Some (_, Some s) => s | _ => s15 end.

Definition ex17 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39578,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,='&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s17 : sym_state := snd (snd ex17).

Definition arms18 := Eval vm_compute in (match SGP.branch_probe IT s17 with Some e => SGP.case_arms s17 e 0 | None => None end).
Definition f18 : sym_state := match arms18 with Some (Some s, _) => s | _ => s17 end.
Definition t18 : sym_state := match arms18 with Some (_, Some s) => s | _ => s17 end.

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,>'&4#8?&9],,1$27#??#1#1'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,>'&4#8?&9],,1$27#??##'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#3958<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,='&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition arms22 := Eval vm_compute in (match SGP.branch_probe IT s21 with Some e => SGP.case_arms s21 e 0 | None => None end).
Definition f22 : sym_state := match arms22 with Some (Some s, _) => s | _ => s21 end.
Definition t22 : sym_state := match arms22 with Some (_, Some s) => s | _ => s21 end.

Definition ex23 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,>'&3&7@#100000000000000$24#38-3>#1#1'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s23 : sym_state := snd (snd ex23).

Definition ex24 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39590,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,>'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s24 : sym_state := snd (snd ex24).

Definition arms25 := Eval vm_compute in (match SGP.branch_probe IT s24 with Some e => SGP.case_arms s24 e 0 | None => None end).
Definition f25 : sym_state := match arms25 with Some (Some s, _) => s | _ => s24 end.
Definition t25 : sym_state := match arms25 with Some (_, Some s) => s | _ => s24 end.

Definition ex26 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,?'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s26 : sym_state := snd (snd ex26).

Definition ex27 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,?'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s27 : sym_state := snd (snd ex27).

Definition ex28 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39560,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,;'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s28 : sym_state := snd (snd ex28).

Definition arms29 := Eval vm_compute in (match SGP.branch_probe IT s28 with Some e => SGP.case_arms s28 e 0 | None => None end).
Definition f29 : sym_state := match arms29 with Some (Some s, _) => s | _ => s28 end.
Definition t29 : sym_state := match arms29 with Some (_, Some s) => s | _ => s28 end.

Definition ex30 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39598,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,<'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s30 : sym_state := snd (snd ex30).

Definition arms31 := Eval vm_compute in (match SGP.branch_probe IT s30 with Some e => SGP.case_arms s30 e 0 | None => None end).
Definition f31 : sym_state := match arms31 with Some (Some s, _) => s | _ => s30 end.
Definition t31 : sym_state := match arms31 with Some (_, Some s) => s | _ => s30 end.

Definition ex32 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,='&4&9],,1$27#??#:0#1#1'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s32 : sym_state := snd (snd ex32).

Definition ex33 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,='&4&9],,1$27#??#:0##'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s33 : sym_state := snd (snd ex33).

Definition ex34 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39564,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,<'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s34 : sym_state := snd (snd ex34).

Definition arms35 := Eval vm_compute in (match SGP.branch_probe IT s34 with Some e => SGP.case_arms s34 e 0 | None => None end).
Definition f35 : sym_state := match arms35 with Some (Some s, _) => s | _ => s34 end.
Definition t35 : sym_state := match arms35 with Some (_, Some s) => s | _ => s34 end.

Definition ex36 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39568,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,='&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s36 : sym_state := snd (snd ex36).

Definition arms37 := Eval vm_compute in (match SGP.branch_probe IT s36 with Some e => SGP.case_arms s36 e 0 | None => None end).
Definition f37 : sym_state := match arms37 with Some (Some s, _) => s | _ => s36 end.
Definition t37 : sym_state := match arms37 with Some (_, Some s) => s | _ => s36 end.

Definition ex38 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,>'&4#9?&9],,1$27#??#1#1'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s38 : sym_state := snd (snd ex38).

Definition ex39 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,>'&4#9?&9],,1$27#??##'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s39 : sym_state := snd (snd ex39).

Definition ex40 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#3958<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,='&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s40 : sym_state := snd (snd ex40).

Definition arms41 := Eval vm_compute in (match SGP.branch_probe IT s40 with Some e => SGP.case_arms s40 e 0 | None => None end).
Definition f41 : sym_state := match arms41 with Some (Some s, _) => s | _ => s40 end.
Definition t41 : sym_state := match arms41 with Some (_, Some s) => s | _ => s40 end.

Definition ex42 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,>'&3&7@#100000000000000$24#38-3>#1#1'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s42 : sym_state := snd (snd ex42).

Definition ex43 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39590,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,>'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s43 : sym_state := snd (snd ex43).

Definition arms44 := Eval vm_compute in (match SGP.branch_probe IT s43 with Some e => SGP.case_arms s43 e 0 | None => None end).
Definition f44 : sym_state := match arms44 with Some (Some s, _) => s | _ => s43 end.
Definition t44 : sym_state := match arms44 with Some (_, Some s) => s | _ => s43 end.

Definition ex45 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,?'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s45 : sym_state := snd (snd ex45).

Definition ex46 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#3$25#2+$21#2+$21#2$1;#>=#9?#?0#90,,?'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'$21##800000000000'$23#3#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??'$25##??,3<!"%pstring).
Definition s46 : sym_state := snd (snd ex46).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PBranch (SGA.mkplan (fst ex11) (SGP.PBranch (SGA.mkplan (fst ex13) (SGP.PEnd 2)) (SGA.mkplan (fst ex14) (SGP.PEnd 3)))) (SGA.mkplan (fst ex15) (SGP.PBranch (SGA.mkplan (fst ex17) (SGP.PBranch (SGA.mkplan (fst ex19) (SGP.PEnd 4)) (SGA.mkplan (fst ex20) (SGP.PEnd 5)))) (SGA.mkplan (fst ex21) (SGP.PBranch (SGA.mkplan (fst ex23) (SGP.PEnd 6)) (SGA.mkplan (fst ex24) (SGP.PBranch (SGA.mkplan (fst ex26) (SGP.PEnd 7)) (SGA.mkplan (fst ex27) (SGP.PEnd 8)))))))))) (SGA.mkplan (fst ex28) (SGP.PBranch (SGA.mkplan (fst ex30) (SGP.PBranch (SGA.mkplan (fst ex32) (SGP.PEnd 9)) (SGA.mkplan (fst ex33) (SGP.PEnd 10)))) (SGA.mkplan (fst ex34) (SGP.PBranch (SGA.mkplan (fst ex36) (SGP.PBranch (SGA.mkplan (fst ex38) (SGP.PEnd 11)) (SGA.mkplan (fst ex39) (SGP.PEnd 12)))) (SGA.mkplan (fst ex40) (SGP.PBranch (SGA.mkplan (fst ex42) (SGP.PEnd 13)) (SGA.mkplan (fst ex43) (SGP.PBranch (SGA.mkplan (fst ex45) (SGP.PEnd 14)) (SGA.mkplan (fst ex46) (SGP.PEnd 15))))))))))))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s13).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s13).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s13 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s13 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s13).
Definition ps2 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s14).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s14).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s14 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s14 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s14).
Definition ps3 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s19).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s19).
Definition ps4 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s20).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s20).
Definition ps5 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s23).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s23).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s23 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s23 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s23).
Definition ps6 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s26).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s26).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s26 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s26 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s26).
Definition ps7 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition regs_out8 : list expr := Eval vm_compute in (s_regs s27).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s27).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s27 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s27 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s27).
Definition ps8 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out8 (ELit 0))) (seq 1 31)) F0L cells8.

Definition regs_out9 : list expr := Eval vm_compute in (s_regs s32).
Definition exit_sp_off9 : Z := Eval vm_compute in (spoff_of s32).
Definition cells9 : list kentry := Eval vm_compute in (cells_of s32 exit_sp_off9).
Definition nfresh9 : nat := Eval vm_compute in (s_next s32 - NX0)%nat.
Definition exit_pc9 : Z := Eval vm_compute in (s_pc s32).
Definition ps9 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out9 (ELit 0))) (seq 1 31)) F0L cells9.

Definition regs_out10 : list expr := Eval vm_compute in (s_regs s33).
Definition exit_sp_off10 : Z := Eval vm_compute in (spoff_of s33).
Definition cells10 : list kentry := Eval vm_compute in (cells_of s33 exit_sp_off10).
Definition nfresh10 : nat := Eval vm_compute in (s_next s33 - NX0)%nat.
Definition exit_pc10 : Z := Eval vm_compute in (s_pc s33).
Definition ps10 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out10 (ELit 0))) (seq 1 31)) F0L cells10.

Definition regs_out11 : list expr := Eval vm_compute in (s_regs s38).
Definition exit_sp_off11 : Z := Eval vm_compute in (spoff_of s38).
Definition cells11 : list kentry := Eval vm_compute in (cells_of s38 exit_sp_off11).
Definition nfresh11 : nat := Eval vm_compute in (s_next s38 - NX0)%nat.
Definition exit_pc11 : Z := Eval vm_compute in (s_pc s38).
Definition ps11 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out11 (ELit 0))) (seq 1 31)) F0L cells11.

Definition regs_out12 : list expr := Eval vm_compute in (s_regs s39).
Definition exit_sp_off12 : Z := Eval vm_compute in (spoff_of s39).
Definition cells12 : list kentry := Eval vm_compute in (cells_of s39 exit_sp_off12).
Definition nfresh12 : nat := Eval vm_compute in (s_next s39 - NX0)%nat.
Definition exit_pc12 : Z := Eval vm_compute in (s_pc s39).
Definition ps12 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out12 (ELit 0))) (seq 1 31)) F0L cells12.

Definition regs_out13 : list expr := Eval vm_compute in (s_regs s42).
Definition exit_sp_off13 : Z := Eval vm_compute in (spoff_of s42).
Definition cells13 : list kentry := Eval vm_compute in (cells_of s42 exit_sp_off13).
Definition nfresh13 : nat := Eval vm_compute in (s_next s42 - NX0)%nat.
Definition exit_pc13 : Z := Eval vm_compute in (s_pc s42).
Definition ps13 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out13 (ELit 0))) (seq 1 31)) F0L cells13.

Definition regs_out14 : list expr := Eval vm_compute in (s_regs s45).
Definition exit_sp_off14 : Z := Eval vm_compute in (spoff_of s45).
Definition cells14 : list kentry := Eval vm_compute in (cells_of s45 exit_sp_off14).
Definition nfresh14 : nat := Eval vm_compute in (s_next s45 - NX0)%nat.
Definition exit_pc14 : Z := Eval vm_compute in (s_pc s45).
Definition ps14 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out14 (ELit 0))) (seq 1 31)) F0L cells14.

Definition regs_out15 : list expr := Eval vm_compute in (s_regs s46).
Definition exit_sp_off15 : Z := Eval vm_compute in (spoff_of s46).
Definition cells15 : list kentry := Eval vm_compute in (cells_of s46 exit_sp_off15).
Definition nfresh15 : nat := Eval vm_compute in (s_next s46 - NX0)%nat.
Definition exit_pc15 : Z := Eval vm_compute in (s_pc s46).
Definition ps15 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out15 (ELit 0))) (seq 1 31)) F0L cells15.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8; ps9; ps10; ps11; ps12; ps13; ps14; ps15] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_cf1b47.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234756 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_cf1b47.IT BndT_Es_000.SegItab_Es_cf1b47.IT_sound BF NX0 BR XSTEP F0 PSS plan 234756 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_vgS2_2b.

Module LibSegEs_vgS2_3a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_cf1b47.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_cf1b47.IT.
Definition ENDS : list Z := [234916; 234956].
Definition STOPS1 : list Z := [234916; 234956] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25#3$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 3;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 234756 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#5+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25#3$19$1:$1;#>=#9?#?0#90,,4'$21##800000000000'$23#1#3'+$21$23#1#800000000000'$25##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_cf1b47.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234756 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_cf1b47.IT BndT_Es_000.SegItab_Es_cf1b47.IT_sound BF NX0 BR XSTEP F0 PSS plan 234756 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_vgS2_3a.

Module LibSegEs_vgS2_3b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_cf1b47.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_cf1b47.IT.
Definition ENDS : list Z := [234916; 234956].
Definition STOPS1 : list Z := [234916; 234956] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25#3$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??"%pstring).
Definition ss0 : sym_state := SS 234756 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39540,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21],,1$29+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#3$1;#>=#9?#?0#90,,:'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#2+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#3$1;#>=#9?#?0#90,,;'&3-41],,1$29#1#1'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39548,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21],,1$28+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#3$1;#>=#9?#?0#90,,;'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#2+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#3$1;#>=#9?#?0#90,,<'&3-41],,1$28#1#1'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39554,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21],,1$27+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,<'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.

Definition ex9 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#2+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,='&3-41],,1$27#1#1'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s9 : sym_state := snd (snd ex9).

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#3955<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,='&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition arms11 := Eval vm_compute in (match SGP.branch_probe IT s10 with Some e => SGP.case_arms s10 e 0 | None => None end).
Definition f11 : sym_state := match arms11 with Some (Some s, _) => s | _ => s10 end.
Definition t11 : sym_state := match arms11 with Some (_, Some s) => s | _ => s10 end.

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39570,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,>'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#395:0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,?'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&9],,1$27#??#90#1#1'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition ex17 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&9],,1$27#??#90##'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s17 : sym_state := snd (snd ex17).

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39574,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,?'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition arms19 := Eval vm_compute in (match SGP.branch_probe IT s18 with Some e => SGP.case_arms s18 e 0 | None => None end).
Definition f19 : sym_state := match arms19 with Some (Some s, _) => s | _ => s18 end.
Definition t19 : sym_state := match arms19 with Some (_, Some s) => s | _ => s18 end.

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39578,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition arms21 := Eval vm_compute in (match SGP.branch_probe IT s20 with Some e => SGP.case_arms s20 e 0 | None => None end).
Definition f21 : sym_state := match arms21 with Some (Some s, _) => s | _ => s20 end.
Definition t21 : sym_state := match arms21 with Some (_, Some s) => s | _ => s20 end.

Definition ex22 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&4#8?&9],,1$27#??#1#1'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s22 : sym_state := snd (snd ex22).

Definition ex23 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&4#8?&9],,1$27#??##'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s23 : sym_state := snd (snd ex23).

Definition ex24 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#3958<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s24 : sym_state := snd (snd ex24).

Definition arms25 := Eval vm_compute in (match SGP.branch_probe IT s24 with Some e => SGP.case_arms s24 e 0 | None => None end).
Definition f25 : sym_state := match arms25 with Some (Some s, _) => s | _ => s24 end.
Definition t25 : sym_state := match arms25 with Some (_, Some s) => s | _ => s24 end.

Definition ex26 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&3&7@#100000000000000$24#38-3>#1#1'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s26 : sym_state := snd (snd ex26).

Definition ex27 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39590,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s27 : sym_state := snd (snd ex27).

Definition arms28 := Eval vm_compute in (match SGP.branch_probe IT s27 with Some e => SGP.case_arms s27 e 0 | None => None end).
Definition f28 : sym_state := match arms28 with Some (Some s, _) => s | _ => s27 end.
Definition t28 : sym_state := match arms28 with Some (_, Some s) => s | _ => s27 end.

Definition ex29 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,12'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s29 : sym_state := snd (snd ex29).

Definition ex30 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,12'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s30 : sym_state := snd (snd ex30).

Definition ex31 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39560,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,>'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s31 : sym_state := snd (snd ex31).

Definition arms32 := Eval vm_compute in (match SGP.branch_probe IT s31 with Some e => SGP.case_arms s31 e 0 | None => None end).
Definition f32 : sym_state := match arms32 with Some (Some s, _) => s | _ => s31 end.
Definition t32 : sym_state := match arms32 with Some (_, Some s) => s | _ => s31 end.

Definition ex33 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39598,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,?'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s33 : sym_state := snd (snd ex33).

Definition arms34 := Eval vm_compute in (match SGP.branch_probe IT s33 with Some e => SGP.case_arms s33 e 0 | None => None end).
Definition f34 : sym_state := match arms34 with Some (Some s, _) => s | _ => s33 end.
Definition t34 : sym_state := match arms34 with Some (_, Some s) => s | _ => s33 end.

Definition ex35 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&9],,1$27#??#:0#1#1'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s35 : sym_state := snd (snd ex35).

Definition ex36 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&9],,1$27#??#:0##'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s36 : sym_state := snd (snd ex36).

Definition ex37 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39564,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,?'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s37 : sym_state := snd (snd ex37).

Definition arms38 := Eval vm_compute in (match SGP.branch_probe IT s37 with Some e => SGP.case_arms s37 e 0 | None => None end).
Definition f38 : sym_state := match arms38 with Some (Some s, _) => s | _ => s37 end.
Definition t38 : sym_state := match arms38 with Some (_, Some s) => s | _ => s37 end.

Definition ex39 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39568,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s39 : sym_state := snd (snd ex39).

Definition arms40 := Eval vm_compute in (match SGP.branch_probe IT s39 with Some e => SGP.case_arms s39 e 0 | None => None end).
Definition f40 : sym_state := match arms40 with Some (Some s, _) => s | _ => s39 end.
Definition t40 : sym_state := match arms40 with Some (_, Some s) => s | _ => s39 end.

Definition ex41 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&4#9?&9],,1$27#??#1#1'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s41 : sym_state := snd (snd ex41).

Definition ex42 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#13:81#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&4#9?&9],,1$27#??##'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s42 : sym_state := snd (snd ex42).

Definition ex43 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#3958<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s43 : sym_state := snd (snd ex43).

Definition arms44 := Eval vm_compute in (match SGP.branch_probe IT s43 with Some e => SGP.case_arms s43 e 0 | None => None end).
Definition f44 : sym_state := match arms44 with Some (Some s, _) => s | _ => s43 end.
Definition t44 : sym_state := match arms44 with Some (_, Some s) => s | _ => s43 end.

Definition ex45 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&3&7@#100000000000000$24#38-3>#1#1'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s45 : sym_state := snd (snd ex45).

Definition ex46 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39590,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s46 : sym_state := snd (snd ex46).

Definition arms47 := Eval vm_compute in (match SGP.branch_probe IT s46 with Some e => SGP.case_arms s46 e 0 | None => None end).
Definition f47 : sym_state := match arms47 with Some (Some s, _) => s | _ => s46 end.
Definition t47 : sym_state := match arms47 with Some (_, Some s) => s | _ => s46 end.

Definition ex48 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395:4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,12'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s48 : sym_state := snd (snd ex48).

Definition ex49 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#13:81#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,12'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s49 : sym_state := snd (snd ex49).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 2)) (SGA.mkplan (fst ex10) (SGP.PBranch (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PEnd 3)) (SGA.mkplan (fst ex17) (SGP.PEnd 4)))) (SGA.mkplan (fst ex18) (SGP.PBranch (SGA.mkplan (fst ex20) (SGP.PBranch (SGA.mkplan (fst ex22) (SGP.PEnd 5)) (SGA.mkplan (fst ex23) (SGP.PEnd 6)))) (SGA.mkplan (fst ex24) (SGP.PBranch (SGA.mkplan (fst ex26) (SGP.PEnd 7)) (SGA.mkplan (fst ex27) (SGP.PBranch (SGA.mkplan (fst ex29) (SGP.PEnd 8)) (SGA.mkplan (fst ex30) (SGP.PEnd 9)))))))))) (SGA.mkplan (fst ex31) (SGP.PBranch (SGA.mkplan (fst ex33) (SGP.PBranch (SGA.mkplan (fst ex35) (SGP.PEnd 10)) (SGA.mkplan (fst ex36) (SGP.PEnd 11)))) (SGA.mkplan (fst ex37) (SGP.PBranch (SGA.mkplan (fst ex39) (SGP.PBranch (SGA.mkplan (fst ex41) (SGP.PEnd 12)) (SGA.mkplan (fst ex42) (SGP.PEnd 13)))) (SGA.mkplan (fst ex43) (SGP.PBranch (SGA.mkplan (fst ex45) (SGP.PEnd 14)) (SGA.mkplan (fst ex46) (SGP.PBranch (SGA.mkplan (fst ex48) (SGP.PEnd 15)) (SGA.mkplan (fst ex49) (SGP.PEnd 16))))))))))))))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s9).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s9).
Definition ps2 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s16).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s16).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s16 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s16 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s16).
Definition ps3 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s17).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s17).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s17 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s17 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s17).
Definition ps4 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s22).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s22).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s22 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s22 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s22).
Definition ps5 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s23).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s23).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s23 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s23 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s23).
Definition ps6 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s26).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s26).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s26 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s26 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s26).
Definition ps7 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition regs_out8 : list expr := Eval vm_compute in (s_regs s29).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s29).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s29 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s29 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s29).
Definition ps8 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out8 (ELit 0))) (seq 1 31)) F0L cells8.

Definition regs_out9 : list expr := Eval vm_compute in (s_regs s30).
Definition exit_sp_off9 : Z := Eval vm_compute in (spoff_of s30).
Definition cells9 : list kentry := Eval vm_compute in (cells_of s30 exit_sp_off9).
Definition nfresh9 : nat := Eval vm_compute in (s_next s30 - NX0)%nat.
Definition exit_pc9 : Z := Eval vm_compute in (s_pc s30).
Definition ps9 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out9 (ELit 0))) (seq 1 31)) F0L cells9.

Definition regs_out10 : list expr := Eval vm_compute in (s_regs s35).
Definition exit_sp_off10 : Z := Eval vm_compute in (spoff_of s35).
Definition cells10 : list kentry := Eval vm_compute in (cells_of s35 exit_sp_off10).
Definition nfresh10 : nat := Eval vm_compute in (s_next s35 - NX0)%nat.
Definition exit_pc10 : Z := Eval vm_compute in (s_pc s35).
Definition ps10 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out10 (ELit 0))) (seq 1 31)) F0L cells10.

Definition regs_out11 : list expr := Eval vm_compute in (s_regs s36).
Definition exit_sp_off11 : Z := Eval vm_compute in (spoff_of s36).
Definition cells11 : list kentry := Eval vm_compute in (cells_of s36 exit_sp_off11).
Definition nfresh11 : nat := Eval vm_compute in (s_next s36 - NX0)%nat.
Definition exit_pc11 : Z := Eval vm_compute in (s_pc s36).
Definition ps11 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out11 (ELit 0))) (seq 1 31)) F0L cells11.

Definition regs_out12 : list expr := Eval vm_compute in (s_regs s41).
Definition exit_sp_off12 : Z := Eval vm_compute in (spoff_of s41).
Definition cells12 : list kentry := Eval vm_compute in (cells_of s41 exit_sp_off12).
Definition nfresh12 : nat := Eval vm_compute in (s_next s41 - NX0)%nat.
Definition exit_pc12 : Z := Eval vm_compute in (s_pc s41).
Definition ps12 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out12 (ELit 0))) (seq 1 31)) F0L cells12.

Definition regs_out13 : list expr := Eval vm_compute in (s_regs s42).
Definition exit_sp_off13 : Z := Eval vm_compute in (spoff_of s42).
Definition cells13 : list kentry := Eval vm_compute in (cells_of s42 exit_sp_off13).
Definition nfresh13 : nat := Eval vm_compute in (s_next s42 - NX0)%nat.
Definition exit_pc13 : Z := Eval vm_compute in (s_pc s42).
Definition ps13 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out13 (ELit 0))) (seq 1 31)) F0L cells13.

Definition regs_out14 : list expr := Eval vm_compute in (s_regs s45).
Definition exit_sp_off14 : Z := Eval vm_compute in (spoff_of s45).
Definition cells14 : list kentry := Eval vm_compute in (cells_of s45 exit_sp_off14).
Definition nfresh14 : nat := Eval vm_compute in (s_next s45 - NX0)%nat.
Definition exit_pc14 : Z := Eval vm_compute in (s_pc s45).
Definition ps14 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out14 (ELit 0))) (seq 1 31)) F0L cells14.

Definition regs_out15 : list expr := Eval vm_compute in (s_regs s48).
Definition exit_sp_off15 : Z := Eval vm_compute in (spoff_of s48).
Definition cells15 : list kentry := Eval vm_compute in (cells_of s48 exit_sp_off15).
Definition nfresh15 : nat := Eval vm_compute in (s_next s48 - NX0)%nat.
Definition exit_pc15 : Z := Eval vm_compute in (s_pc s48).
Definition ps15 : SR.post_spec := SR.PS 234916 (map (fun i => (i, nth i regs_out15 (ELit 0))) (seq 1 31)) F0L cells15.

Definition regs_out16 : list expr := Eval vm_compute in (s_regs s49).
Definition exit_sp_off16 : Z := Eval vm_compute in (spoff_of s49).
Definition cells16 : list kentry := Eval vm_compute in (cells_of s49 exit_sp_off16).
Definition nfresh16 : nat := Eval vm_compute in (s_next s49 - NX0)%nat.
Definition exit_pc16 : Z := Eval vm_compute in (s_pc s49).
Definition ps16 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out16 (ELit 0))) (seq 1 31)) F0L cells16.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8; ps9; ps10; ps11; ps12; ps13; ps14; ps15; ps16] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_cf1b47.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234756 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_cf1b47.IT BndT_Es_000.SegItab_Es_cf1b47.IT_sound BF NX0 BR XSTEP F0 PSS plan 234756 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_vgS2_3b.

Module LibSegEs_vgS2_big.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_cf1b47.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_cf1b47.IT.
Definition ENDS : list Z := [234916; 234956].
Definition STOPS1 : list Z := [234916; 234956] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25$26$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 38) 4 255;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 234756 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5;#39508,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25$26$19$1:$1;#>=#9?#?0#90,,5'$21##800000000000'$23#1#4000000'+$21$23#1#800000000000'$26#4#??'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#1+$21$23#8#1-3>#?5-41#2#13:81#3$24++$21$26#1$25$26+$21$26++$21$26#1$1;#>=#9?#?0#90,,6'&4$26$23#1#1'$21##800000000000'$23#1#4000000'+$21$23#1#800000000000'$26#4#??'$25##??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#395:4#395<<#395:4#395<<#5=#395<<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#5+$21$23#8#1-3>#?5-41#2#13:81#3$24$16$25$26$19$1:$1;#>=#9?#?0#90,,6'&4$26$23##'$21##800000000000'$23#1#4000000'+$21$23#1#800000000000'$26#4#??'$25##??,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 234956 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_cf1b47.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234756 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_cf1b47.IT BndT_Es_000.SegItab_Es_cf1b47.IT_sound BF NX0 BR XSTEP F0 PSS plan 234756 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_vgS2_big.

Module LibSegEs_vgX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_cf1b47.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_cf1b47.IT.
Definition ENDS : list Z := [235004].
Definition STOPS1 : list Z := [235004] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800060#800000000000&$2#10($2-60#60!$2-8,8$2=!$2-10,8$2>!$2-18,8$2?!$2-20,8$30!$2-28,8$31!$2-30,8$32!$2-38,8$33!$2-40,8$34!$2-48,8$35!$2-50,8$36!$2-58,8$37"%pstring).
Definition ss0 : sym_state := SS 234956 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#395?<#395?<#5=#395?<,20#$1$2$3$4$5$6$7$2=$2>$:$;$<$=$>$?$10$11$2?$30$31$32$33$34$35$36$37$1;$1<$1=$1>$1?,,>'$2#7???7?800060#800000000000&$2#10($2-60#60!$2-8,8$2=!$2-10,8$2>!$2-18,8$2?!$2-20,8$30!$2-28,8$31!$2-30,8$32!$2-38,8$33!$2-40,8$34!$2-48,8$35!$2-50,8$36!$2-58,8$37,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 235004 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_cf1b47.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234956 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_cf1b47.IT BndT_Es_000.SegItab_Es_cf1b47.IT_sound BF NX0 BR XSTEP F0 PSS plan 234956 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_vgX.

Module LibSegEs_viAn16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_b26f93.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_b26f93.IT.
Definition ENDS : list Z := [226008].
Definition STOPS1 : list Z := [226008] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;^#?#???????????8000^#?#?????????????7?"%pstring).
Definition ss0 : sym_state := SS 219640 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#372=8#372=8#5=#372=8,20##35;04+$2-30$3$4$5$6$7$:$;$29+$2-23$<$=$>$?$10$11+$:#8$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,10!$2-23,1#49!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;^#?#???????????8000^#?#?????????????7?,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 226008 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_b26f93.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 219640 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_b26f93.IT BndT_Es_000.SegItab_Es_b26f93.IT_sound BF NX0 BR XSTEP F0 PSS plan 219640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_viAn16.

Module LibSegEs_viAn32.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_b26f93.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_b26f93.IT.
Definition ENDS : list Z := [226008].
Definition STOPS1 : list Z := [226008] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;^#?#???????80000000^#?#???????????7???"%pstring).
Definition ss0 : sym_state := SS 219640 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#372=8#372=8#5=#372=8,20##35;34+$2-30$3$4$5$6$7$:$;$29+$2-22$<$=$>$?$10$11+$:#8$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,10!$2-22,1#6<!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;^#?#???????80000000^#?#???????????7???,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 226008 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_b26f93.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 219640 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_b26f93.IT BndT_Es_000.SegItab_Es_b26f93.IT_sound BF NX0 BR XSTEP F0 PSS plan 219640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_viAn32.

Module LibSegEs_viAn64.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_b26f93.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_b26f93.IT.
Definition ENDS : list Z := [226008].
Definition STOPS1 : list Z := [226008] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;^#8#^#?#???????7???????"%pstring).
Definition ss0 : sym_state := SS 219640 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#372=8#372=8#5=#372=8,20##35:78+$2-30$3$4$5$6$7$:$;$29+$2-21$<$=$>$?$10$11+$:#8$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,10!$2-21,1#4<!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;^#8#^#?#???????7???????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 226008 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_b26f93.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 219640 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_b26f93.IT BndT_Es_000.SegItab_Es_b26f93.IT_sound BF NX0 BR XSTEP F0 PSS plan 219640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_viAn64.

Module LibSegEs_viAn8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Es_000.SegItab_Es_b26f93.ITR.
Definition IT : itab := BndT_Es_000.SegItab_Es_b26f93.IT.
Definition ENDS : list Z := [226008].
Definition STOPS1 : list Z := [226008] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;^#?#?????????????80^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 219640 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#372=8#372=8#5=#372=8,20##35:<0+$2-30$3$4$5$6$7$:$;$29+$2-25$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,10!$2-25,1#69!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;^#?#?????????????80^#?#???????????????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 226008 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Es_000.SegItab_Es_b26f93.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 219640 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Es_000.SegItab_Es_b26f93.IT BndT_Es_000.SegItab_Es_b26f93.IT_sound BF NX0 BR XSTEP F0 PSS plan 219640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEs_viAn8.
