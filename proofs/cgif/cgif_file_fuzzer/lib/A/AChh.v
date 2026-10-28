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
Lemma clr2_mod4 : forall x, x mod 4 = 0 -> (2 * (x / 2)) mod 4 = 0.
Proof.
intros x Hx. assert (E : x = 2 * (2 * (x / 4))).
{ pose proof (Z.div_mod x 4 ltac:(lia)). lia. }
rewrite E at 1. rewrite (Z.mul_comm 2 (2 * (x / 4))), Z_div_mult by lia.
replace (2 * (2 * (x / 4))) with (x / 4 * 4) by lia. apply Z_mod_mult.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section h.
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
Lemma fl_B2X_aux : fl_fromX0 KS MT XN B CTX wfn ss_B3 (INV_B3X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_B2 (INV_B2X MT B).
Proof.
intros RB3. fl_preludeX.
pose proof HINV as ((Hk3 & Eab3 & gen & E591 & Rgen & Hgen4) & E591X & MLE0).
lazymatch type of E591X with _ = Z_to_bv 64 (ACj6.fl_gen2 ?cx) =>
assert (RgenX : 0 <= ACj6.fl_gen2 cx < 2 ^ 32)
by (pose proof (fl_gen123_range cx ltac:(cbn [c_f]; clear - Q3; lia)) as G; cbn [c_f] in G; clear - G Q3; lia) end.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E10n E32n Hing3).
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
Local Ltac joinB3 RB3 gtac ntac :=
lazymatch goal with HS0 : st_ok_pi _ _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end;
lazymatch goal with HS : st_ok_pi _ _ ?Ev ?ssv _, AG : forall n, (n < 33)%nat -> _ |- _ =>
let rs := eval vm_compute in (ss_mem ssv) in
let i := idx_of_base rs 11%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let cs := eval vm_compute in (YP09.r_chunks r) in
let j := idx_of_off cs 20 in let j := eval vm_compute in j in
lazymatch (eval vm_compute in (nth_error cs j)) with Some (YP09.mkChunk 20 (CVal 4 ?e)) =>
let E621 := fresh "E621" in let Qa4 := fresh "Qa4" in let E625 := fresh "E625" in
prreg HS (14%bv : bv 5) Qa4;
add_atom HS 621%nat (sv_denot Ev e) E621;
rechunk HS i j (SOff 621 0) ltac:(rewrite sv_denot_SOff0, E621; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity);
ra_join HS ss_B3 622%nat ra_deads_B3 ltac:(idtac;
ra_join_val HS 622%nat 3%nat Qa4 E625;
ra_join_fact HS 621%nat (mkAF 0 4294967295 0)
ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite E621; rewrite Z.pow_0_r, Z.mod_1_r;
rewrite (denot_lit_U Ev e), unsigned_lit_small by (pose proof (U_range Ev e); rewrite M64_val in *; lia);
let HHH := fresh "HHH" in enough (HHH : 0 <= U Ev e <= 4294967295) by (clear - HHH; lia); gtac);
ra_join_fact HS 625%nat (mkAF 0 65535 0) ltac:(rewrite E625; rewrite Z.pow_0_r, Z.mod_1_r; ntac));
fl_handX RB3 HS end end.
Local Ltac tailB3 RB3 ntac :=
lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _, HJ3 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, AG : forall n, (n < 33)%nat -> _,
Hing3 : In (_, CGIF_SIZE) (ablocks _ _ _), Hcur3 : In (_, FRAME_SIZE) (ablocks _ _ _),
E10n : ew _ 10 = _, E11n : ew _ 11 = _, E32n : ew _ 32 = _, EFA3 : forall c p, frame_addr _ c p = _ |- _ =>
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan;
[   xt_npal;
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x19dc;
[ try (oblG HJ3 E11n E32n Hcur3) .. | ];
[ lazymatch goal with F0 := frame_addr _ 2 ?fp |- _ => awrFL AG fp F0 EFA3 end | ];
clear_frames;
joinB3 RB3 ltac:(idtac; lazymatch goal with E591 : ew ?Ev 591 = Z_to_bv 64 ?gen, Rgen : 0 <= ?gen < _ |- _ => rewrite (U_atom Ev 591 gen E591) by lia; clear - Rgen; lia end) ntac
| xt_npal;
paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x19dc;
[ try (oblG HJ3 E11n E32n Hcur3) .. | ];
[ lazymatch goal with F0 := frame_addr _ 2 ?fp |- _ => awrFL AG fp F0 EFA3 end | ];
clear_frames;
joinB3 RB3 ltac:(idtac; lazymatch goal with E591 : ew ?Ev 591 = Z_to_bv 64 ?gen, Rgen : 0 <= ?gen < _ |- _ =>
rewrite U_and_m2, (U_atom Ev 591 gen E591) by lia; let Hclr := fresh "Hclr" in pose proof (clr2_rng gen ltac:(clear - Rgen; lia)) as Hclr; clear - Rgen Hclr; lia end) ntac ] end.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3. clear_frames.
hc_bool Hc ltac:(fun H => rewrite (U_atom _ 52 (fr_attr f) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E52)) in H by lia).
tailB3 RB3 ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E55, unsigned_lit_small by (clear - Q5 Hob241 Hob242 Hob253 Huar; lia); clear - Q5 Hob241 Hob242 Hob253 Huar; lia).
+   split. { split; [exact Hk3|]. split; [exact Eab3|]. split.
* exists gen. split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E621, sv_denot_SOff0; exact E591|]. split; [exact Rgen|]. exact Hgen4.
* rewrite E625. unfold ACj6.fl_npal, fl_uselct; cbn [c_f c_s]. rewrite Hc. cbn [negb]. exact E55. }
split; [| exact MLE0].
rewrite !ew_havoc_old by (clear - PBASE PBLO; lia). rewrite E621, sv_denot_SOff0.
lazymatch type of E591X with _ = ?r => transitivity r; [exact E591X|] end. f_equal.
unfold ACj6.fl_gen3, ACj6.fl_npal, fl_uselct. cbn [c_f c_s]. rewrite Hc. cbn [negb]. cbn in XT3.
lazymatch goal with |- context [if ?b then _ else _] => destruct b; [discriminate XT3 | reflexivity] end.
+   split. { split; [exact Hk3|]. split; [exact Eab3|]. split.
* exists (2 * (gen / 2)). split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E621, denot_lit_U, U_and_m2, (U_atom _ 591 gen E591) by lia; reflexivity|].
split; [pose proof (clr2_rng gen ltac:(clear - Rgen Hob241 Hob242 Hob253 Huar; lia)); clear - Rgen H Hob241 Hob242 Hob253 Huar; lia|]. intros Hb0. apply clr2_mod4. exact (Hgen4 Hb0).
* rewrite E625. unfold ACj6.fl_npal, fl_uselct; cbn [c_f c_s]. rewrite Hc. cbn [negb]. exact E55. }
split; [| exact MLE0].
rewrite !ew_havoc_old by (clear - PBASE PBLO; lia). rewrite E621, denot_lit_U, U_and_m2.
lazymatch goal with |- context [U ?Ev (SOff 591 0)] =>
lazymatch type of E591X with _ = Z_to_bv 64 ?v => rewrite (U_atom Ev 591 v E591X) by (clear - RgenX; lia) end end. f_equal.
unfold ACj6.fl_gen3, ACj6.fl_npal, fl_uselct. cbn [c_f c_s]. rewrite Hc. cbn [negb]. cbn in XT3.
lazymatch goal with |- context [if ?b then _ else _] => destruct b; [| discriminate XT3] end.
unfold clr2. lazymatch goal with |- 2 * (?v / 2) = _ => pose proof (Z.div_mod v 2 ltac:(lia)) as D2; clear - D2; lia end.
-
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E10n E32n Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3. clear_frames.
hc_bool Hc ltac:(fun H => rewrite (U_atom _ 52 (fr_attr f) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E52)) in H by lia).
tailB3 RB3 ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E42, unsigned_lit_small by (clear - R9 Hob241 Hob242 Hob253 Huar; lia); clear - R9 Hob241 Hob242 Hob253 Huar; lia).
+   split. { split; [exact Hk3|]. split; [exact Eab3|]. split.
* exists gen. split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E621, sv_denot_SOff0; exact E591|]. split; [exact Rgen|]. exact Hgen4.
* rewrite E625. unfold ACj6.fl_npal, fl_uselct; cbn [c_f c_s]. rewrite Hc. cbn [negb]. exact E42. }
split; [| exact MLE0].
rewrite !ew_havoc_old by (clear - PBASE PBLO; lia). rewrite E621, sv_denot_SOff0.
lazymatch type of E591X with _ = ?r => transitivity r; [exact E591X|] end. f_equal.
unfold ACj6.fl_gen3, ACj6.fl_npal, fl_uselct. cbn [c_f c_s]. rewrite Hc. cbn [negb]. cbn in XT3.
lazymatch goal with |- context [if ?b then _ else _] => destruct b; [discriminate XT3 | reflexivity] end.
+   split. { split; [exact Hk3|]. split; [exact Eab3|]. split.
* exists (2 * (gen / 2)). split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E621, denot_lit_U, U_and_m2, (U_atom _ 591 gen E591) by lia; reflexivity|].
split; [pose proof (clr2_rng gen ltac:(clear - Rgen Hob241 Hob242 Hob253 Huar; lia)); clear - Rgen H Hob241 Hob242 Hob253 Huar; lia|]. intros Hb0. apply clr2_mod4. exact (Hgen4 Hb0).
* rewrite E625. unfold ACj6.fl_npal, fl_uselct; cbn [c_f c_s]. rewrite Hc. cbn [negb]. exact E42. }
split; [| exact MLE0].
rewrite !ew_havoc_old by (clear - PBASE PBLO; lia). rewrite E621, denot_lit_U, U_and_m2.
lazymatch goal with |- context [U ?Ev (SOff 591 0)] =>
lazymatch type of E591X with _ = Z_to_bv 64 ?v => rewrite (U_atom Ev 591 v E591X) by (clear - RgenX; lia) end end. f_equal.
unfold ACj6.fl_gen3, ACj6.fl_npal, fl_uselct. cbn [c_f c_s]. rewrite Hc. cbn [negb]. cbn in XT3.
lazymatch goal with |- context [if ?b then _ else _] => destruct b; [| discriminate XT3] end.
unfold clr2. lazymatch goal with |- 2 * (?v / 2) = _ => pose proof (Z.div_mod v 2 ltac:(lia)) as D2; clear - D2; lia end.
Qed.
Lemma fl_B2X : fl_fromX0 KS MT XN B CTX wfn ss_B3 (INV_B3X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_B2 (INV_B2X MT B).
Proof. exact fl_B2X_aux. Qed.
End h.
End d.
End a.
