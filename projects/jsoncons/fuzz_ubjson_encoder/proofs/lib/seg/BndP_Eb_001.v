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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.seg Require BndT_Eb_001 BndT_Eb_000.

Module LibSegEb_ab10P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700; 764768; 764596].
Definition STOPS1 : list Z := [764700; 764768; 764596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21$24$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6"%pstring).
Definition ss0 : sym_state := SS 764528 regs0 [] kn0 NX0.
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

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5;#;:;08,20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21+$25-30$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40&9$21#7$1>$1?,,8'&4&1$24#5#1#1#1'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40&9$21#7$1>$1?,,9'&4+$25-30#:#1#1'&4&1$24#5#1#1#1'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5=#;:;60,20#$1+$2-10$3$4#=#7???8000#1??9$8$9#$21+$25-30$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40&9$21#7$1>$1?,,9'&4+$25-30#:##'&4&1$24#5#1#1#1'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5;#;::74,20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21$24$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?,,8'&4&1$24#5#1##'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition arms7 := Eval vm_compute in (match SGP.branch_probe IT s6 with Some e => SGP.case_arms s6 e 0 | None => None end).
Definition f7 : sym_state := match arms7 with Some (Some s, _) => s | _ => s6 end.
Definition t7 : sym_state := match arms7 with Some (_, Some s) => s | _ => s6 end.

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5;#;:;08,20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21+$25-30$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40&9$21#7$1>$1?,,9'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition arms9 := Eval vm_compute in (match SGP.branch_probe IT s8 with Some e => SGP.case_arms s8 e 0 | None => None end).
Definition f9 : sym_state := match arms9 with Some (Some s, _) => s | _ => s8 end.
Definition t9 : sym_state := match arms9 with Some (_, Some s) => s | _ => s8 end.

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40&9$21#7$1>$1?,,:'&4+$25-30#:#1#1'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5=#;:;60,20#$1+$2-10$3$4#=#7???8000#1??9$8$9#$21+$25-30$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40&9$21#7$1>$1?,,:'&4+$25-30#:##'&4&1$24#1#1#1#1'&4&1$24#5#1##'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5;#;::78,20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21$24$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?,,9'&4&1$24#1#1##'&4&1$24#5#1##'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5;#;::9<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21&9+$25-2=#??$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40+$25-2=$1>$1?,,:'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5;#;:::8,20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21&9+$25-2=#??$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40&9&6#1??9+$25-2=#1$1>$1?,,;'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5=#;:;60,20#$1+$2-10$3$4#=#7???8000#1??9$8$9#$21&9+$25-2=#??$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40&9&6#1??9+$25-2=#1$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1#1#1'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5=#;::;4,20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21+@#4&9+$25-2=#??#23<40$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40&9&6#1??9+$25-2=#1$1>$1?,,<'&4&1&9&6#1??9+$25-2=#1##1##'&4&9+$25-2=#??#=#1#1'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5=#;:;60,20#$1+$2-10$3$4#=#7???8000#1??9$8$9#$21&9+$25-2=#??$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40+$25-2=$1>$1?,,;'&4&9+$25-2=#??#=##'&4&1$24##1#1#1'&4&1$24#1#1##'&4&1$24#5#1##'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#;:;1<#;:;60#;::;4#;:;1<#;:;60#;::;4#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1$24$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?,,:'&4&1$24##1##'&4&1$24#1#1##'&4&1$24#5#1##'$21#1#800000000000'$22#1#800000000000'$24#^#?#???????????????!$21#,1$25'$25##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PEnd 1)))) (SGA.mkplan (fst ex6) (SGP.PBranch (SGA.mkplan (fst ex8) (SGP.PBranch (SGA.mkplan (fst ex10) (SGP.PEnd 2)) (SGA.mkplan (fst ex11) (SGP.PEnd 3)))) (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 4)) (SGA.mkplan (fst ex19) (SGP.PEnd 5)))) (SGA.mkplan (fst ex20) (SGP.PEnd 6)))) (SGA.mkplan (fst ex21) (SGP.PEnd 7)))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s5).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s5).
Definition ps1 : SR.post_spec := SR.PS 764768 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s11).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s11).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s11 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s11 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s11).
Definition ps3 : SR.post_spec := SR.PS 764768 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s18).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s18).
Definition ps4 : SR.post_spec := SR.PS 764768 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s19).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s19).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s19 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s19 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s19).
Definition ps5 : SR.post_spec := SR.PS 764596 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s20).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s20).
Definition ps6 : SR.post_spec := SR.PS 764768 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s21).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s21).
Definition ps7 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764528 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764528 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10P7.

Module LibSegEb_ab10T0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700].
Definition STOPS1 : list Z := [764700] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21#23<40$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KZero (SA (ELit 0) 2147469192) (ELit 1)].
Definition ss0 : sym_state := SS 764596 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;1<#;:;1<#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#1$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40#$1>$1?,,4%#10000#13?000'$21#1#800000000000'$22#1#800000000000###7???<788#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10T0.

Module LibSegEb_ab10T10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700].
Definition STOPS1 : list Z := [764700] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21#23<68$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KZero (SA (ELit 0) 2147469197) (ELit 1)].
Definition ss0 : sym_state := SS 764596 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;1<#;:;1<#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40#$1>$1?,,4%#10000#13?000'$21#1#800000000000'$22#1#800000000000###7???<78=#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10T10.

Module LibSegEb_ab10T11.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700].
Definition STOPS1 : list Z := [764700] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21#23<6<$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KZero (SA (ELit 0) 2147469197) (ELit 1)].
Definition ss0 : sym_state := SS 764596 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;1<#;:;1<#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40#$1>$1?,,4%#10000#13?000'$21#1#800000000000'$22#1#800000000000###7???<78=#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10T11.

Module LibSegEb_ab10T12.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700].
Definition STOPS1 : list Z := [764700] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21#23<70$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KWord (SA (ELit 0) 2147469198) 1 (ELit 4)].
Definition ss0 : sym_state := SS 764596 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;1<#;:;1<#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40#4#3$1?,,4%#10000#13?000'$21#1#800000000000'$22#1#800000000000!##7???<78>,1#4,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10T12.

Module LibSegEb_ab10T3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700].
Definition STOPS1 : list Z := [764700] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21#23<4<$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KZero (SA (ELit 0) 2147469193) (ELit 1)].
Definition ss0 : sym_state := SS 764596 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;1<#;:;1<#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40#$1>$1?,,4%#10000#13?000'$21#1#800000000000'$22#1#800000000000###7???<789#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10T3.

Module LibSegEb_ab10T4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700].
Definition STOPS1 : list Z := [764700] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21#23<50$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KZero (SA (ELit 0) 2147469194) (ELit 1)].
Definition ss0 : sym_state := SS 764596 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;1<#;:;1<#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40#$1>$1?,,4%#10000#13?000'$21#1#800000000000'$22#1#800000000000###7???<78:#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10T4.

Module LibSegEb_ab10T5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700].
Definition STOPS1 : list Z := [764700] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21#23<54$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KZero (SA (ELit 0) 2147469194) (ELit 1)].
Definition ss0 : sym_state := SS 764596 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;1<#;:;1<#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40#$1>$1?,,4%#10000#13?000'$21#1#800000000000'$22#1#800000000000###7???<78:#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10T5.

Module LibSegEb_ab10T6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700].
Definition STOPS1 : list Z := [764700] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21#23<58$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KZero (SA (ELit 0) 2147469195) (ELit 1)].
Definition ss0 : sym_state := SS 764596 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;1<#;:;1<#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40#$1>$1?,,4%#10000#13?000'$21#1#800000000000'$22#1#800000000000###7???<78;#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10T6.

Module LibSegEb_ab10T7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700].
Definition STOPS1 : list Z := [764700] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21#23<5<$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KZero (SA (ELit 0) 2147469195) (ELit 1)].
Definition ss0 : sym_state := SS 764596 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;1<#;:;1<#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40#$1>$1?,,4%#10000#13?000'$21#1#800000000000'$22#1#800000000000###7???<78;#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10T7.

Module LibSegEb_ab10T8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700].
Definition STOPS1 : list Z := [764700] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21#23<60$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KZero (SA (ELit 0) 2147469196) (ELit 1)].
Definition ss0 : sym_state := SS 764596 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;1<#;:;1<#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40#$1>$1?,,4%#10000#13?000'$21#1#800000000000'$22#1#800000000000###7???<78<#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10T8.

Module LibSegEb_ab10T9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764700].
Definition STOPS1 : list Z := [764700] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4#=#7???8000#1??9$8$9$21$21#23<64$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1306624;
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 34) 1 140737488355328;
   KZero (SA (ELit 0) 2147469196) (ELit 1)].
Definition ss0 : sym_state := SS 764596 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;1<#;:;1<#5=#;:;1<,20#$1+$2-10$3$4#=#7???8000#1??9$8$9+$21#1+$21#1#5$22#5#:#2#1$12$13$14$15$16$17$18$19$1:$1;#23<40#$1>$1?,,4%#10000#13?000'$21#1#800000000000'$22#1#800000000000###7???<78<#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764596 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764596 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10T9.

Module LibSegEb_ab10X.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_001.SegItab_Eb_9a0502.ITR.
Definition IT : itab := BndT_Eb_001.SegItab_Eb_9a0502.IT.
Definition ENDS : list Z := [764776].
Definition STOPS1 : list Z := [764776] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487184 140737488355328;
   KAlign (EVar 2) 16;
   KWord (SA (EVar 2) (-8)) 8 (EVar 40)].
Definition ss0 : sym_state := SS 764768 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;:;68#;:;68#5=#;:;68,20#$28$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?801010#800000000000&$2#10!$2-8,8$28,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 764776 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_001.SegItab_Eb_9a0502.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 764768 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_001.SegItab_Eb_9a0502.IT BndT_Eb_001.SegItab_Eb_9a0502.IT_sound BF NX0 BR XSTEP F0 PSS plan 764768 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_ab10X.

Module LibSegEb_acxA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eb_000.SegItab_Eb_601554.ITR.
Definition IT : itab := BndT_Eb_000.SegItab_Eb_601554.IT.
Definition ENDS : list Z := [453700].
Definition STOPS1 : list Z := [453700] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; ELit 6791552; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 34; EVar 36; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?801400#800000000000&$2#10($2-400#400%#137000#13?000!##1460?8,8#7???8000!##146100,4#1!##67:190,4$23'$23##7??????>(##67:190#4!##146==8,1#1!##13?878,8#11>9<4!##69:1=0,1#!##69:1=4,4#!##69:1=8,4#2!##69:1>0,8#69:1>8(##69:1=0#220!##69:413,1#"%pstring).
Definition ss0 : sym_state := SS 453572 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-1024), ELit 1024); ((ELit 0), (6791568), ELit 4); ((ELit 0), (6922712), ELit 4); ((ELit 0), (6922752), ELit 16); ((ELit 0), (6923008), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-1024), 1024); ((ELit 0), (6791568), 4); ((ELit 0), (6922712), 4); ((ELit 0), (6922752), 16); ((ELit 0), (6923008), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6><44#6><44#5=#6><44,20#$1$2$3#67:180$5$6$7$8$9###18#$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,20!##67:190,4$23!$2-40,8#!$2-38,8#6><28!##69:1=8,4#4!##69:308,8#!##69:208,8#6><48!$2-60,8$14!$2-58,8#13?;>8!$2-50,8$21!$2-48,8$22!##69:300,8$22!##69:200,8$21!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801400#800000000000&$2#10($2-400#400%#137000#13?000!##1460?8,8#7???8000!##146100,4#1'$23##7??????>(##67:190#4!##146==8,1#1!##13?878,8#11>9<4!##69:1=0,1#!##69:1=4,4#!##69:1>0,8#69:1>8(##69:1=0#220!##69:413,1#,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 453700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eb_000.SegItab_Eb_601554.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 453572 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Eb_000.SegItab_Eb_601554.IT BndT_Eb_000.SegItab_Eb_601554.IT_sound BF NX0 BR XSTEP F0 PSS plan 453572 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEb_acxA.
