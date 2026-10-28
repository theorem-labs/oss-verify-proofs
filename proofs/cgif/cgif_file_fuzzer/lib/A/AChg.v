(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACkc ACj4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section d.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis TLF : PALibF B.
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Variable wfn : Z.
Variable KS : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B KS.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Variable XN : xnums.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Ltac joinB2 RB2 gtac :=
lazymatch goal with HS0 : st_ok_pi _ _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end;
lazymatch goal with HS : st_ok_pi _ _ ?Ev ?ssv _, AG : forall n, (n < 33)%nat -> _ |- _ =>
let rs := eval vm_compute in (ss_mem ssv) in
let i := idx_of_base rs 11%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let cs := eval vm_compute in (YP09.r_chunks r) in
let j := idx_of_off cs 20 in let j := eval vm_compute in j in
lazymatch (eval vm_compute in (nth_error cs j)) with Some (YP09.mkChunk 20 (CVal 4 ?e)) =>
let E531 := fresh "E591" in let HEv := fresh "HEv" in
add_atom HS 591%nat (sv_denot Ev e) E531;
rechunk HS i j (SOff 591 0) ltac:(rewrite sv_denot_SOff0, E531; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity);
ra_join HS ss_B2 592%nat ra_deads_B2 ltac:(idtac; ra_join_fact HS 591%nat (mkAF 0 4294967295 0)
ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite E531; rewrite Z.pow_0_r, Z.mod_1_r;
rewrite (denot_lit_U Ev e), unsigned_lit_small by (pose proof (U_range Ev e); rewrite M64_val in *; lia);
let HHH := fresh "HHH" in enough (HHH : 0 <= U Ev e <= 4294967295) by (clear - HHH; lia); gtac));
fl_handX RB2 HS end end.
Lemma fl_B1X_aux : fl_fromX0 KS MT XN B CTX wfn ss_B2 (INV_B2X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_B (INV_0X MT B 0).
Proof.
intros RB2. fl_preludeX.
pose proof HINV as ((Hk3 & Eab3) & MLE0).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n.
fs_roF HS. reshok HS.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E10n E32n Hing3).
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
assert (HpBef : frame_ptr (nth (i - 1) (cg_frames s) None) <> 0).
{ intros Hb0. rewrite branch_eq_U, U_lit in Hc by lia. apply Z.eqb_eq in Hc. apply (U_front_isfirst _ _ Hc).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rewrite (U_atom Ev 12 _ ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 12%nat) by lia; exact E12)); [exact Hb0 | rewrite Hb0; lia] | st_ok _ ?Ev _ _ =>
rewrite (U_atom Ev 12 _ ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 12%nat) by lia; exact E12)); [exact Hb0 | rewrite Hb0; lia]  end. }
assert (XT1 : (frame_ptr (nth (i - 1) (cg_frames s) None) =? 0) || negb ((Z.land (cg_attr s) 8 =? 0) && (Z.land (fr_attr f) 2 =? 0)) = false).
{ pose proof Hc as T1. rewrite branch_eq_U, U_lit in T1 by lia. apply Z.eqb_eq in T1.
lazymatch type of T1 with U ?Ev _ = 0 =>
rewrite (U_front1 Ev (frame_ptr (nth (i - 1) (cg_frames s) None)) (cg_attr s) (fr_attr f)) in T1 end;
[ exact (if01_zero _ T1)
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 12%nat) by lia; exact E12
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E52
| apply (fptr_range s i Hi R0 R1) | exact R5 | exact Q2 ]. }
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan. 1: awrFL AG fpos F EFA3. clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
+ idtac.
assert (XT2 : Z.land (fr_attr f) 4 = 0).
{ pose proof Hc0 as T2. rewrite branch_eq_U, U_lit in T2 by lia. apply Z.eqb_eq in T2.
lazymatch type of T2 with U ?Ev _ = 0 => rewrite (U_and_atom Ev 52 (fr_attr f) 4) in T2 end;
[ exact T2 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E52 | clear - Q2; lia | clear; lia ]. }
paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x197c. 1: awrFL AG fpos F EFA3. clear_frames.
joinB2 RB2 ltac:(idtac; rewrite (U_atom _ 53 (fr_gen f) E53) by lia; clear - Q3 Hob241 Hob242 Hob253 Huar; lia).
split.
split; [exact Hk3|]. split; [exact Eab3|]. exists (fr_gen f).
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E591, sv_denot_SOff0; exact E53|]. split; [clear - Q3 Hob241 Hob242 Hob253 Huar; lia|].
intros Hb0. exfalso. exact (HpBef Hb0).
split; [| exact MLE0].
rewrite !ew_havoc_old by (clear - PBASE PBLO; lia). rewrite E591, sv_denot_SOff0, E53 by lia. f_equal.
unfold ACj6.fl_gen2, ACj6.fl_gen1, fl_isfirst, fl_hasalpha, fl_settr. cbn [c_i c_s c_f].
rewrite XT1, XT2. reflexivity.
+ idtac.
assert (XT2 : Z.land (fr_attr f) 4 <> 0).
{ pose proof Hc0 as T2. rewrite branch_eq_U, U_lit in T2 by lia. apply Z.eqb_neq in T2.
lazymatch type of T2 with U ?Ev _ <> 0 => rewrite (U_and_atom Ev 52 (fr_attr f) 4) in T2 end;
[ exact T2 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E52 | clear - Q2; lia | clear; lia ]. }
paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x197c.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3. clear_frames.
joinB2 RB2 ltac:(idtac; rewrite U_and_m2, (U_atom _ 53 (fr_gen f) E53) by lia; pose proof (clr2_rng (fr_gen f) ltac:(clear - Q3 Hob241 Hob242 Hob253 Huar; lia)); clear - Q3 H Hob241 Hob242 Hob253 Huar; lia).
split.
split; [exact Hk3|]. split; [exact Eab3|]. exists (2 * (fr_gen f / 2)).
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E591, denot_lit_U, U_and_m2, (U_atom _ 53 (fr_gen f) E53) by lia; reflexivity|].
split; [pose proof (clr2_rng (fr_gen f) ltac:(clear - Q3 Hob241 Hob242 Hob253 Huar; lia)); clear - Q3 H Hob241 Hob242 Hob253 Huar; lia|]. intros Hb0. exfalso. exact (HpBef Hb0).
split; [| exact MLE0].
rewrite !ew_havoc_old by (clear - PBASE PBLO; lia). rewrite E591, denot_lit_U, U_and_m2, (U_atom _ 53 (fr_gen f) E53) by lia. f_equal.
unfold ACj6.fl_gen2, ACj6.fl_gen1, fl_isfirst, fl_hasalpha, fl_settr. cbn [c_i c_s c_f].
rewrite XT1, (proj2 (Z.eqb_neq _ _) XT2). cbn [negb orb]. unfold clr2. pose proof (Z.div_mod (fr_gen f) 2 ltac:(lia)) as D2. clear - D2. lia.
-
assert (XT1 : (frame_ptr (nth (i - 1) (cg_frames s) None) =? 0) || negb ((Z.land (cg_attr s) 8 =? 0) && (Z.land (fr_attr f) 2 =? 0)) = true).
{ pose proof Hc as T1. rewrite branch_eq_U, U_lit in T1 by lia. apply Z.eqb_neq in T1.
lazymatch type of T1 with U ?Ev _ <> 0 =>
rewrite (U_front1 Ev (frame_ptr (nth (i - 1) (cg_frames s) None)) (cg_attr s) (fr_attr f)) in T1 end;
[ exact (if01_nonzero _ T1)
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 12%nat) by lia; exact E12
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E52
| apply (fptr_range s i Hi R0 R1) | exact R5 | exact Q2 ]. }
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3. clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
+ idtac.
assert (XT2 : Z.land (fr_attr f) 4 = 0).
{ pose proof Hc0 as T2. rewrite branch_eq_U, U_lit in T2 by lia. apply Z.eqb_eq in T2.
lazymatch type of T2 with U ?Ev _ = 0 => rewrite (U_and_atom Ev 52 (fr_attr f) 4) in T2 end;
[ exact T2 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E52 | clear - Q2; lia | clear; lia ]. }
paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x197c. 1: awrFL AG fpos F EFA3. clear_frames.
joinB2 RB2 ltac:(idtac; rewrite U_and_m4, (U_atom _ 53 (fr_gen f) E53) by lia; pose proof (clr4_rng (fr_gen f) ltac:(clear - Q3 Hob241 Hob242 Hob253 Huar; lia)); clear - Q3 H Hob241 Hob242 Hob253 Huar; lia).
split.
split; [exact Hk3|]. split; [exact Eab3|]. exists (4 * (fr_gen f / 4)).
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E591, denot_lit_U, U_and_m4, (U_atom _ 53 (fr_gen f) E53) by lia; reflexivity|].
split; [pose proof (clr4_rng (fr_gen f) ltac:(clear - Q3 Hob241 Hob242 Hob253 Huar; lia)); clear - Q3 H Hob241 Hob242 Hob253 Huar; lia|]. intros _. rewrite Z.mul_comm. apply Z_mod_mult.
split; [| exact MLE0].
rewrite !ew_havoc_old by (clear - PBASE PBLO; lia). rewrite E591, denot_lit_U, U_and_m4, (U_atom _ 53 (fr_gen f) E53) by lia. f_equal.
unfold ACj6.fl_gen2, ACj6.fl_gen1, fl_isfirst, fl_hasalpha, fl_settr. cbn [c_i c_s c_f].
rewrite XT1, XT2, Z.eqb_refl. cbn [negb orb]. unfold clr4. pose proof (Z.div_mod (fr_gen f) 4 ltac:(lia)) as D4. clear - D4. lia.
+ idtac.
assert (XT2 : Z.land (fr_attr f) 4 <> 0).
{ pose proof Hc0 as T2. rewrite branch_eq_U, U_lit in T2 by lia. apply Z.eqb_neq in T2.
lazymatch type of T2 with U ?Ev _ <> 0 => rewrite (U_and_atom Ev 52 (fr_attr f) 4) in T2 end;
[ exact T2 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E52 | clear - Q2; lia | clear; lia ]. }
paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x197c.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3. clear_frames.
joinB2 RB2 ltac:(idtac; rewrite U_and_m2, U_and_m4, (U_atom _ 53 (fr_gen f) E53) by lia; rewrite clr42 by (clear - Q3 Hob241 Hob242 Hob253 Huar; lia);
pose proof (clr4_rng (fr_gen f) ltac:(clear - Q3 Hob241 Hob242 Hob253 Huar; lia)); clear - Q3 H Hob241 Hob242 Hob253 Huar; lia).
split.
split; [exact Hk3|]. split; [exact Eab3|]. exists (4 * (fr_gen f / 4)).
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E591, denot_lit_U, U_and_m2, U_and_m4, (U_atom _ 53 (fr_gen f) E53) by lia; rewrite clr42 by (clear - Q3 Hob241 Hob242 Hob253 Huar; lia); reflexivity|].
split; [pose proof (clr4_rng (fr_gen f) ltac:(clear - Q3 Hob241 Hob242 Hob253 Huar; lia)); clear - Q3 H Hob241 Hob242 Hob253 Huar; lia|]. intros _. rewrite Z.mul_comm. apply Z_mod_mult.
split; [| exact MLE0].
rewrite !ew_havoc_old by (clear - PBASE PBLO; lia). rewrite E591, denot_lit_U, U_and_m2, U_and_m4, (U_atom _ 53 (fr_gen f) E53) by lia. f_equal.
unfold ACj6.fl_gen2, ACj6.fl_gen1, fl_isfirst, fl_hasalpha, fl_settr. cbn [c_i c_s c_f].
rewrite clr42 by (clear - Q3; lia).
rewrite XT1, (proj2 (Z.eqb_neq _ _) XT2). cbn [negb orb]. unfold clr2, clr4.
pose proof (Z.div_mod (fr_gen f) 4 ltac:(lia)) as D4.
replace ((fr_gen f - fr_gen f mod 4) mod 2) with 0; [clear - D4; lia|].
replace (fr_gen f - fr_gen f mod 4) with ((2 * (fr_gen f / 4)) * 2) by (clear - D4; lia). symmetry. apply Z_mod_mult.
Qed.
Lemma fl_B1X : fl_fromX0 KS MT XN B CTX wfn ss_B2 (INV_B2X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_B (INV_0X MT B 0).
Proof. exact fl_B1X_aux. Qed.
End d.
End b.
End a.
