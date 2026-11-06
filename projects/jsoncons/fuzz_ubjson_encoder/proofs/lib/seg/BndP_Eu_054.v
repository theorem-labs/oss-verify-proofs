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

Module LibSegEu_utsH0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_c252e0.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_c252e0.IT.
Definition ENDS : list Z := [245088; 245196; 245372].
Definition STOPS1 : list Z := [245088; 245196; 245372] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$13$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;;028!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;79?0!$26#98,1$36'$36##2'$24#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 245044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3;=60#3;=<<#3;>7<#3;=60#3;=<<#3;>7<#5;#3;=3<,20##3;=3<+$2-50$3$4$5$6$7$23$22&6@^#4#$36#3?#$<$=$>$?$10$11$21$13$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?,,1:'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;;028!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;79?0!$26#98,1$36'$36##2'$24#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3;=60#3;=<<#3;>7<#3;=60#3;=<<#3;>7<#5;#3;=4<,20##3;=3<+$2-50$3$4$5$6$7$23$22##$<$=$>$?$10$11$21#4000$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?,,1;'&4&1&6@^#4#$36#3?##1#1#1'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;;028!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;79?0!$26#98,1$36'$36##2'$24#1^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3;=60#3;=<<#3;>7<#3;=60#3;=<<#3;>7<#5=#3;=60,20##3;=3<+$2-50$3$4$5$6$7$23$22#4000#$<$=$>$?$10$11$21$24$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?,,1<'&4$24#4000#1#1'&4&1&6@^#4#$36#3?##1#1#1'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;;028!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;79?0!$26#98,1$36'$36##2'$24#1^#?#???????????????,38!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3;=60#3;=<<#3;>7<#3;=60#3;=<<#3;>7<#5:#3;=<<,20##3;=3<+$2-50$3$4$5$6$7$23$22##$<$=$>$?$10$11$21#4000$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?,,1<'&4$24#4000##'&4&1&6@^#4#$36#3?##1#1#1'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;;028!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;79?0!$26#98,1$36'$36##2'$24#1^#?#???????????????,38!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3;=60#3;=<<#3;>7<#3;=60#3;=<<#3;>7<#5=#3;>7<,20#$2<$2$3$4$5$6$7$2=$2>+$23@-1$24#$<$=$>$?$10$11$2?$30$31$32$33$34$18$19$1:$1;$1<$1=$1>$1?,,1;'&4&1&6@^#4#$36#3?##1##'$2#7???7?800050#800000000000&$2#10($2-50#50!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128%#10000#;;028!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800000#7????????>?0&$26#8)$2-50#50$26##110!$26#,8#;79?0!$26#98,1$36'$36##2'$24#1^#?#???????????????,38!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 0)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 2))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s5).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s5).
Definition ps0 : SR.post_spec := SR.PS 245088 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 245196 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 245372 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_c252e0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 245044 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_c252e0.IT BndT_Eu_000.SegItab_Eu_c252e0.IT_sound BF NX0 BR XSTEP F0 PSS plan 245044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_utsH0.

Module LibSegEu_utsH1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_c252e0.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_c252e0.IT.
Definition ENDS : list Z := [245088].
Definition STOPS1 : list Z := [245088] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$13$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800050#800000000000&$2#10($2-50#50'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128!$21#120,8$25'$25#1#4000!$21#110,8#4000'$24#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 245044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;=60#3;=60#5;#3;=58,20##3;=3<+$2-50$3$4$5$6$7$23$22#4000$25$<$=$>$?$10$11$21$24$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?800050#800000000000&$2#10($2-50#50'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128!$21#120,8$25'$25#1#4000!$21#110,8#4000'$24#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;=60#3;=60#5:#3;=60,20##3;=3<+$2-50$3$4$5$6$7$23$22#4000$25$<$=$>$?$10$11$21$24$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?,,;'&4$24#4000#1#1'$2#7???7?800050#800000000000&$2#10($2-50#50'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128!$21#120,8$25'$25#1#4000!$21#110,8#4000'$24#1^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;=60#3;=60#5=#3;=60,20##3;=3<+$2-50$3$4$5$6$7$23$22#4000$25$<$=$>$?$10$11$21#4000$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?,,;'&4$24#4000##'$2#7???7?800050#800000000000&$2#10($2-50#50'$21#7???7?800000#7????????>=8&$21#8)$2-50#50$21##128!$21#120,8$25'$25#1#4000!$21#110,8#4000'$24#1^#?#???????????????,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 245088 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 245088 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_c252e0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 245044 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_c252e0.IT BndT_Eu_000.SegItab_Eu_c252e0.IT_sound BF NX0 BR XSTEP F0 PSS plan 245044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_utsH1.

Module LibSegEu_utsQL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_c252e0.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_c252e0.IT.
Definition ENDS : list Z := [240064].
Definition STOPS1 : list Z := [240064] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$2:$14$24+$22#1$2;$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?800050#800000000000&$2#10($2-50#50'$22#7???7?800000#7?????????>8&$22#8)$2-50#50$22##18!$22#,1$27'$27##??'&9$27#1#1#1!$22#10,8$29'$29#1000#800000000000'$2:#1#4000'$2;##8000000"%pstring).
Definition ss0 : sym_state := SS 245128 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3:9<0#3:9<0#5=#3:9<0,20##3;=;8+$2-50$3$4$5$6$7$23$22$21+$29$2;$2:$=$>$?$10$11$21$2:$14$24+$22#1$2;$18$19$1:$1;$1<$1=$1>$1?,,='$2#7???7?800050#800000000000&$2#10($2-50#50'$22#7???7?800000#7?????????>8&$22#8)$2-50#50$22##18!$22#,1$27'$27##??'&9$27#1#1#1!$22#10,8$29'$29#1000#800000000000'$2:#1#4000'$2;##8000000,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 240064 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_c252e0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 245128 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_c252e0.IT BndT_Eu_000.SegItab_Eu_c252e0.IT_sound BF NX0 BR XSTEP F0 PSS plan 245128 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_utsQL.

Module LibSegEu_utsQS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_c252e0.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_c252e0.IT.
Definition ENDS : list Z := [240064].
Definition STOPS1 : list Z := [240064] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$2:$14$24+$22#1$2;$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800050#800000000000&$2#10($2-50#50'$22#7???7?800000#7?????????>8&$22#8)$2-50#50$22##18!$22#,1$27'$27##2<'&9$27#1##'$2:#1#4000'$2;##16"%pstring).
Definition ss0 : sym_state := SS 245128 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3:9<0#3:9<0#5=#3:9<0,20##3;=;8+$2-50$3$4$5$6$7$23$22$21++$22$2;#1$2:$=$>$?$10$11$21$2:$14$24+$22#1$2;$18$19$1:$1;$1<$1=$1>$1?,,;'$2#7???7?800050#800000000000&$2#10($2-50#50'$22#7???7?800000#7?????????>8&$22#8)$2-50#50$22##18!$22#,1$27'$27##2<'&9$27#1##'$2:#1#4000'$2;##16,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 240064 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_c252e0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 245128 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_c252e0.IT BndT_Eu_000.SegItab_Eu_c252e0.IT_sound BF NX0 BR XSTEP F0 PSS plan 245128 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_utsQS.

Module LibSegEu_utsRL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_c252e0.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_c252e0.IT.
Definition ENDS : list Z := [373440].
Definition STOPS1 : list Z := [373440] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$2:$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800050#800000000000&$2#10($2-50#50'$22#7???7?800000#7?????????>8&$22#8)$2-50#50$22##18!$22#,1$27'$27##??'&9$27#1#1#1!$22#8,8$28'$28##8000000'$2:#1#4000"%pstring).
Definition ss0 : sym_state := SS 245088 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#5;2<0#5;2<0#5=#5;2<0,20##3;=88+$2-50$3$4$5$6$7$23$22$22+$28$2:#$=$>$?$10$11$21$2:$14$24+$22#1$28$18$19$1:$1;$1<$1=$1>$1?,,<'$2#7???7?800050#800000000000&$2#10($2-50#50'$22#7???7?800000#7?????????>8&$22#8)$2-50#50$22##18!$22#,1$27'$27##??'&9$27#1#1#1!$22#8,8$28'$28##8000000'$2:#1#4000,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 373440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_c252e0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 245088 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_c252e0.IT BndT_Eu_000.SegItab_Eu_c252e0.IT_sound BF NX0 BR XSTEP F0 PSS plan 245088 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_utsRL.

Module LibSegEu_utsRS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_c252e0.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_c252e0.IT.
Definition ENDS : list Z := [373440].
Definition STOPS1 : list Z := [373440] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$2:$14$24+$22#1$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800050#800000000000&$2#10($2-50#50'$22#7???7?800000#7?????????>8&$22#8)$2-50#50$22##18!$22#,1$27'$27##2<'&9$27#1##'$2:#1#4000"%pstring).
Definition ss0 : sym_state := SS 245088 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#5;2<0#5;2<0#5=#5;2<0,20##3;=88+$2-50$3$4$5$6$7$23$22$22+$2:&6$27#1#$=$>$?$10$11$21$2:$14$24+$22#1&6$27#1$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?800050#800000000000&$2#10($2-50#50'$22#7???7?800000#7?????????>8&$22#8)$2-50#50$22##18!$22#,1$27'$27##2<'&9$27#1##'$2:#1#4000,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 373440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_c252e0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 245088 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_c252e0.IT BndT_Eu_000.SegItab_Eu_c252e0.IT_sound BF NX0 BR XSTEP F0 PSS plan 245088 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_utsRS.

Module LibSegEu_uvaB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_ce2798.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_ce2798.IT.
Definition ENDS : list Z := [234712; 234324].
Definition STOPS1 : list Z := [234712; 234324] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#2-41#>?#?0#90$25$;+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$21$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 1 140737488355328;
   KRange (EVar 35) 0 140737488355328;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328].
Definition ss0 : sym_state := SS 234672 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394=8#39354#394=8#39354#5;#394;4,20#$1+$2-60$3$4#2-41#>?#?0#90$21$;+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$21$18$19$1:$1;#>0#:0#>=#9?,,3'$21#1#800000000000'$23##800000000000'+$21$23#1#800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394=8#39354#394=8#39354#5=#394=8,20#$1+$2-60$3$4#2-41#>?#?0#90+$21$23#+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$21$18$19$1:$1;#>0#:0#>=#9?,,4'&4&1$21+$21$23#1#1#1'$21#1#800000000000'$23##800000000000'+$21$23#1#800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394=8#39354#394=8#39354#5=#39354,20#$1+$2-60$3$4#2-41#>?#?0#90$21$;+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$21$18$19$1:$1;#>0#:0#>=#9?,,4'&4&1$21+$21$23#1##'$21#1#800000000000'$23##800000000000'+$21$23#1#800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 234712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 234324 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_ce2798.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234672 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_ce2798.IT BndT_Eu_000.SegItab_Eu_ce2798.IT_sound BF NX0 BR XSTEP F0 PSS plan 234672 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uvaB.

Module LibSegEu_uvaE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_ce2798.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_ce2798.IT.
Definition ENDS : list Z := [234712; 234324].
Definition STOPS1 : list Z := [234712; 234324] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 35); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483168 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-96)) (ELit 96);
   KRange (EVar 33) 1 140737488355328;
   KRange (EVar 35) 0 67108863].
Definition ss0 : sym_state := SS 234164 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-96), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-96), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394=8#39354#394=8#39354#5;#39300,20#$1+$2-60$3$4$5$6$7$8$9$21$23+$21$23#1#$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-60,8$1;!$2-58,8$1:!$2-50,8$19!$2-48,8$18!$2-40,8$17!$2-38,8$16!$2-30,8$15!$2-28,8$14!$2-20,8$13!$2-18,8$12!$2-10,8$9!$2-8,8$8'$2#7???7?800060#800000000000&$2#10($2-60#60'$21#1#800000000000'$23##3??????,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394=8#39354#394=8#39354#5=#394=8,20#$1+$2-60$3$4$5$6$7$8$9$21$23+$21$23#1#$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'&4&1$23##1#1#1!$2-60,8$1;!$2-58,8$1:!$2-50,8$19!$2-48,8$18!$2-40,8$17!$2-38,8$16!$2-30,8$15!$2-28,8$14!$2-20,8$13!$2-18,8$12!$2-10,8$9!$2-8,8$8'$2#7???7?800060#800000000000&$2#10($2-60#60'$21#1#800000000000'$23##3??????,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394=8#39354#394=8#39354#5=#39354,20#$1+$2-60$3$4#2^#?#?????????????;?#>?#?0#90$21#1330<+$21$23#8^#?#???????????????#1^#?#?????????????<2#?5#?4#8?#13:;=^#?#??????????><542#3$17$18$19$1:$1;#>0#:0#>=#9?,,12'&4&1$23##1##!$2-60,8$1;!$2-58,8$1:!$2-50,8$19!$2-48,8$18!$2-40,8$17!$2-38,8$16!$2-30,8$15!$2-28,8$14!$2-20,8$13!$2-18,8$12!$2-10,8$9!$2-8,8$8'$2#7???7?800060#800000000000&$2#10($2-60#60'$21#1#800000000000'$23##3??????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 234712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 234324 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_ce2798.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234164 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_ce2798.IT BndT_Eu_000.SegItab_Eu_ce2798.IT_sound BF NX0 BR XSTEP F0 PSS plan 234164 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uvaE.

Module LibSegEu_uvaEz.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_ce2798.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_ce2798.IT.
Definition ENDS : list Z := [234712].
Definition STOPS1 : list Z := [234712] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 0; ELit 0; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483168 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-96)) (ELit 96)].
Definition ss0 : sym_state := SS 234164 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-96), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-96), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#394=8#394=8#5=#394=8,20#$1+$2-60$3$4$5$6$7$8$9####1#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?!$2-60,8$1;!$2-58,8$1:!$2-50,8$19!$2-48,8$18!$2-40,8$17!$2-38,8$16!$2-30,8$15!$2-28,8$14!$2-20,8$13!$2-18,8$12!$2-10,8$9!$2-8,8$8'$2#7???7?800060#800000000000&$2#10($2-60#60,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 234712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_ce2798.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234164 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_ce2798.IT BndT_Eu_000.SegItab_Eu_ce2798.IT_sound BF NX0 BR XSTEP F0 PSS plan 234164 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uvaEz.

Module LibSegEu_uvaF1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_ce2798.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_ce2798.IT.
Definition ENDS : list Z := [234472].
Definition STOPS1 : list Z := [234472] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#2-41#>?#?0#90$21$;+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 1 140737488355328;
   KRange (EVar 35) 1 7;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328].
Definition ss0 : sym_state := SS 234324 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#393>8#393>8#5=#393>8,20#$1+$2-60$3$4#2-41#>?#?0#90$21$23+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$17$18$19$1:$1;#>0#:0#>=#9?,,3'$21#1#800000000000'$23#1#7'+$21$23#1#800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 234472 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_ce2798.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234324 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_ce2798.IT BndT_Eu_000.SegItab_Eu_ce2798.IT_sound BF NX0 BR XSTEP F0 PSS plan 234324 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uvaF1.

Module LibSegEu_uvaF8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_ce2798.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_ce2798.IT.
Definition ENDS : list Z := [234472; 234672].
Definition STOPS1 : list Z := [234472; 234672] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#2-41#>?#?0#90$21$;+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??"%pstring).
Definition ss0 : sym_state := SS 234324 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5;#39364,20#$1+$2-60$3$4#2-41#>?#?0#90$21],,1$24+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$17$18$19$1:$1;#>0#:0#>=#9?,,13'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5=#393>8,20#$1+$2-60$3$4#2-41#>?#?0#90$21],,1$24+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$17$18$19$1:$1;#>0#:0#>=#9?,,14'&3],,1$24##1#1'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5;#39374,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#1+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$25$18$19$1:$1;#>0#:0#>=#9?,,14'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5=#393>8,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#1+$21#1+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$25$18$19$1:$1;#>0#:0#>=#9?,,15'&3],,1$25##1#1'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5;#39384,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#2+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$26$18$19$1:$1;#>0#:0#>=#9?,,15'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.

Definition ex9 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5=#393>8,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#2+$21#2+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$26$18$19$1:$1;#>0#:0#>=#9?,,16'&3],,1$26##1#1'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s9 : sym_state := snd (snd ex9).

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5;#39394,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#3+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$27$18$19$1:$1;#>0#:0#>=#9?,,16'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition arms11 := Eval vm_compute in (match SGP.branch_probe IT s10 with Some e => SGP.case_arms s10 e 0 | None => None end).
Definition f11 : sym_state := match arms11 with Some (Some s, _) => s | _ => s10 end.
Definition t11 : sym_state := match arms11 with Some (_, Some s) => s | _ => s10 end.

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5=#393>8,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#3+$21#3+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$27$18$19$1:$1;#>0#:0#>=#9?,,17'&3],,1$27##1#1'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition ex13 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5;#393:4,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#4+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$28$18$19$1:$1;#>0#:0#>=#9?,,17'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s13 : sym_state := snd (snd ex13).

Definition arms14 := Eval vm_compute in (match SGP.branch_probe IT s13 with Some e => SGP.case_arms s13 e 0 | None => None end).
Definition f14 : sym_state := match arms14 with Some (Some s, _) => s | _ => s13 end.
Definition t14 : sym_state := match arms14 with Some (_, Some s) => s | _ => s13 end.

Definition ex15 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5=#393>8,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#4+$21#4+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$28$18$19$1:$1;#>0#:0#>=#9?,,18'&3],,1$28##1#1'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s15 : sym_state := snd (snd ex15).

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5;#393;4,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#5+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$29$18$19$1:$1;#>0#:0#>=#9?,,18'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5=#393>8,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#5+$21#5+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$29$18$19$1:$1;#>0#:0#>=#9?,,19'&3],,1$29##1#1'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5;#393<4,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#6+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$2:$18$19$1:$1;#>0#:0#>=#9?,,19'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition arms20 := Eval vm_compute in (match SGP.branch_probe IT s19 with Some e => SGP.case_arms s19 e 0 | None => None end).
Definition f20 : sym_state := match arms20 with Some (Some s, _) => s | _ => s19 end.
Definition t20 : sym_state := match arms20 with Some (_, Some s) => s | _ => s19 end.

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5=#393>8,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#6+$21#6+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$2:$18$19$1:$1;#>0#:0#>=#9?,,1:'&3],,1$2:##1#1'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition ex22 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5;#393=4,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#7+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$2;$18$19$1:$1;#>0#:0#>=#9?,,1:'&3],,1$2:###'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s22 : sym_state := snd (snd ex22).

Definition arms23 := Eval vm_compute in (match SGP.branch_probe IT s22 with Some e => SGP.case_arms s22 e 0 | None => None end).
Definition f23 : sym_state := match arms23 with Some (Some s, _) => s | _ => s22 end.
Definition t23 : sym_state := match arms23 with Some (_, Some s) => s | _ => s22 end.

Definition ex24 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5=#393>8,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#7+$21#7+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3],,1$2;$18$19$1:$1;#>0#:0#>=#9?,,1;'&3],,1$2;##1#1'&3],,1$2:###'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s24 : sym_state := snd (snd ex24).

Definition ex25 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#393>8#394;0#393>8#394;0#5=#394;0,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#7+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3+$21#8$18$19$1:$1;#>0#:0#>=#9?,,1;'&3],,1$2;###'&3],,1$2:###'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s25 : sym_state := snd (snd ex25).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 2)) (SGA.mkplan (fst ex10) (SGP.PBranch (SGA.mkplan (fst ex12) (SGP.PEnd 3)) (SGA.mkplan (fst ex13) (SGP.PBranch (SGA.mkplan (fst ex15) (SGP.PEnd 4)) (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 5)) (SGA.mkplan (fst ex19) (SGP.PBranch (SGA.mkplan (fst ex21) (SGP.PEnd 6)) (SGA.mkplan (fst ex22) (SGP.PBranch (SGA.mkplan (fst ex24) (SGP.PEnd 7)) (SGA.mkplan (fst ex25) (SGP.PEnd 8))))))))))))))))).
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
Definition ps0 : SR.post_spec := SR.PS 234472 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 234472 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s9).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s9).
Definition ps2 : SR.post_spec := SR.PS 234472 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s12).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s12).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s12 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s12 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s12).
Definition ps3 : SR.post_spec := SR.PS 234472 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s15).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s15).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s15 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s15 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s15).
Definition ps4 : SR.post_spec := SR.PS 234472 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s18).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s18).
Definition ps5 : SR.post_spec := SR.PS 234472 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s21).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s21).
Definition ps6 : SR.post_spec := SR.PS 234472 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s24).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s24).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s24 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s24 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s24).
Definition ps7 : SR.post_spec := SR.PS 234472 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition regs_out8 : list expr := Eval vm_compute in (s_regs s25).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s25).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s25 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s25 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s25).
Definition ps8 : SR.post_spec := SR.PS 234672 (map (fun i => (i, nth i regs_out8 (ELit 0))) (seq 1 31)) F0L cells8.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_ce2798.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234324 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_ce2798.IT BndT_Eu_000.SegItab_Eu_ce2798.IT_sound BF NX0 BR XSTEP F0 PSS plan 234324 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uvaF8.

Module LibSegEu_uvaS1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_ce2798.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_ce2798.IT.
Definition ENDS : list Z := [234488].
Definition STOPS1 : list Z := [234488] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#2-41#>?#?0#90$21$;+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 1 140737488355328;
   KRange (EVar 35) 1 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KWord (SA (EVar 33) 0) 1 (EVar 36);
   KRange (EVar 36) 0 255].
Definition ss0 : sym_state := SS 234472 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#393?8#393?8#5=#393?8,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$24#13:;=+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$17$24$19$1:$1;#>0#:0#>=#9?,,5'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 234488 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_ce2798.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234472 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_ce2798.IT BndT_Eu_000.SegItab_Eu_ce2798.IT_sound BF NX0 BR XSTEP F0 PSS plan 234472 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uvaS1.

Module LibSegEu_uvaS2_0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_ce2798.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_ce2798.IT.
Definition ENDS : list Z := [234672; 234712].
Definition STOPS1 : list Z := [234672; 234712] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#2-41#>?#?0#90$21$;+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$17$24#$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 1 140737488355328;
   KRange (EVar 35) 1 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 36) 0 255].
Definition ss0 : sym_state := SS 234492 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394;0#394=8#394;0#394=8#5;#39498,20#$1+$2-60$3$4#2-41#>?#?0#90$21#6+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3+$21#1$24&7@#100000000000000$24#38$21$1;#>0#:0#>=#9?,,4'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$24##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394;0#394=8#394;0#394=8#5=#394=8,20#$1+$2-60$3$4#2-41#>?#?0#90$21#6+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3+$21#1$24&7@#100000000000000$24#38$21$1;#>0#:0#>=#9?,,5'&3&7@#100000000000000$24#38-3>#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$24##??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394;0#394=8#394;0#394=8#5;#3949<,20#$1+$2-60$3$4#2-41#>?#?0#90$21#6+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3+$21#1$24&7@#100000000000000$24#38$21$1;#>0#:0#>=#9?,,5'&3&7@#100000000000000$24#38-3>##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$24##??,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394;0#394=8#394;0#394=8#5=#394;0,20#$1+$2-60$3$4#2-41#>?#?0#90$21#6+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3+$21#1$24&7@#100000000000000$24#38$21$1;#>0#:0#>=#9?,,6'&4$24#?5#1#1'&3&7@#100000000000000$24#38-3>##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$24##??,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394;0#394=8#394;0#394=8#5=#394=8,20#$1+$2-60$3$4#2-41#>?#?0#90$21#6+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3+$21#1$24&7@#100000000000000$24#38$21$1;#>0#:0#>=#9?,,6'&4$24#?5##'&3&7@#100000000000000$24#38-3>##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$24##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 234712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 234672 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 234712 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_ce2798.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234492 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_ce2798.IT BndT_Eu_000.SegItab_Eu_ce2798.IT_sound BF NX0 BR XSTEP F0 PSS plan 234492 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uvaS2_0.

Module LibSegEu_uvaS2_1a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Eu_000.SegItab_Eu_ce2798.ITR.
Definition IT : itab := BndT_Eu_000.SegItab_Eu_ce2798.IT.
Definition ENDS : list Z := [234672; 234712].
Definition STOPS1 : list Z := [234672; 234712] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#2-41#>?#?0#90$21$;+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$17$24#1$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 1 140737488355328;
   KRange (EVar 35) 1 1;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 36) 0 255].
Definition ss0 : sym_state := SS 234492 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#394;0#394=8#394;0#394=8#5=#394=8,20#$1+$2-60$3$4#2-41#>?#?0#90$21#5+$21$23#8-1#1-3>#?5#?4#8?#13:;=^#?#??????????><542#3$17$24#1$1:$1;#>0#:0#>=#9?,,4'$21#1#800000000000'$23#1#1'+$21$23#1#800000000000'$24##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 234712 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Eu_000.SegItab_Eu_ce2798.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234492 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := ub0_plan_sound_it BndT_Eu_000.SegItab_Eu_ce2798.IT BndT_Eu_000.SegItab_Eu_ce2798.IT_sound BF NX0 BR XSTEP F0 PSS plan 234492 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegEu_uvaS2_1a.
