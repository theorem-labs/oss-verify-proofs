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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACkc ACj4 ACj3 ACj9.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACih.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
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
Lemma fl_R2X_aux : fl_fromX0 KS MT XN B CTX wfn ss_R3 (INV_R3X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_R2 (INV_R2X MT B).
Proof.
intros RR3. fl_preludeX.
pose proof HINV as ((gen & E621 & Rgen) & E625 & (pt & w & h & top & left & tidx & img & E892 & E844 & E845 & E841 & E846 & E842 & E891 & Hrpt & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & Htidx & Hpt & XD & XTI & XI & XI0 & XLEN & XMLE) & E621X).
pose proof HCUR as (XCa & XCg & XCd & XCn & XCct & XCdisp & XCt & XCimg & XClen & XClp). cbn in XCg.
assert (XFBNZ : forall fb, nth (i - 1) (cg_frames s) None = Some fb -> fr_ptr fb <> 0).
{ intros fb' Hfb'. destruct (fl_bef_in s i fb' Hi Hlen3 Hfb') as [_ Hfbi'].
destruct (fl_bef_blocks B ly S g s N rest fb' HPerm Hfbi') as (Hbin' & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb') FRAME_SIZE HAR Hbin') as (_ & Hb4096' & _). clear - Hb4096'. lia. }
destruct (fl_front_model (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) GPAL cur bef XCa XCg XCn ltac:(cbn [c_f]; clear - Q3; lia)
ltac:(unfold ACj6.fl_isfirst; cbn [c_i c_s]; apply (isfirst_of_opt _ bef);
[clear - HBEF; unfold oframe_relbA in HBEF; destruct (nth (i - 1) (cg_frames s) None), bef; first [exact I | destruct HBEF] | exact XFBNZ]))
as (XNPAL & XULCT & XALPHA & XSET & XGEN3).
cbn [c_s c_f c_i] in XNPAL, XULCT, XALPHA, XSET, XGEN3. clear XFBNZ.
assert (Hgen : gen = YI0f.fl_gen3 (gcfg_of s GPAL) cur bef).
{ apply zbv_inj64; [rewrite <- E621; exact E621X | clear - Rgen; lia |].
pose proof (fl_gen3_range (gcfg_of s GPAL) cur bef ltac:(rewrite <- XCg; clear - Q3; lia)) as G; clear - G Q3 XCg; lia. }
clear XNPAL XULCT XGEN3.
xpt_facts Hpt XPT.
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)).
{ intros x Hx. destruct Hpt as [(_ & _ & _ & Eab3) | (_ & _ & _ & (_ & _ & _ & Eab3 & _))]; rewrite Eab3; [exact Hx | apply in_app_iff; left; exact Hx]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (apply Hsub3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch. clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
assert (XT1 : negb ((Z.land (cg_attr s) 8 =? 0) && (Z.land (fr_attr f) 2 =? 0)) = true).
{ pose proof Hc as T1. rewrite branch_ne_U, U_lit in T1 by lia.
lazymatch type of T1 with negb (U ?Ev _ =? _) = _ => rewrite (U_hasalpha Ev (cg_attr s) (fr_attr f)) in T1 end;
[ destruct ((Z.land (cg_attr s) 8 =? 0) && (Z.land (fr_attr f) 2 =? 0)); first [discriminate T1 | reflexivity]
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E52
| exact R5 | exact Q2 ]. }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x2384.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch. clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 901%nat (sv_denot Ev (SLit 1)) E901;
rechunk_off HS 516%nat 48 (SOff 901 0) ltac:(rewrite sv_denot_SOff0, E901; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
ra_join HS ss_R3 902%nat fl_R3_deads_bv ltac:(idtac;
ra_join_fact HS 901%nat (mkAF 0 1 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E901; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 1)), U_lit, unsigned_lit_small by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia));
fl_handX RR3 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists 1; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E901; reflexivity | split; [clear; lia|]];
unfold xhastr, xG; cbn [c_s x_GPAL x_cur x_bef]; rewrite <- XALPHA; unfold ACj6.fl_hasalpha; cbn [c_s c_f]; rewrite XT1; reflexivity|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X].
exists pt, w, h, top, left, tidx, img. cbn [c_s c_f c_ly c_S].
rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
split; [exact E892|]. split; [exact E844|]. split; [exact E845|]. split; [exact E841|]. split; [exact E846|]. split; [exact E842|]. split; [exact E891|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|]. split; [exact Htidx|].
split; [exact Hpt|].
split; [exact XD|]. split; [exact XTI|]. split; [exact XI|]. split; [exact XI0|]. split; [exact XLEN|]. exact XMLE.
-
assert (XT1 : negb ((Z.land (cg_attr s) 8 =? 0) && (Z.land (fr_attr f) 2 =? 0)) = false).
{ pose proof Hc as T1. rewrite branch_ne_U, U_lit in T1 by lia.
lazymatch type of T1 with negb (U ?Ev _ =? _) = _ => rewrite (U_hasalpha Ev (cg_attr s) (fr_attr f)) in T1 end;
[ destruct ((Z.land (cg_attr s) 8 =? 0) && (Z.land (fr_attr f) 2 =? 0)); first [discriminate T1 | reflexivity]
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E52
| exact R5 | exact Q2 ]. }
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch. clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
+
assert (XT2 : Z.lor (Z.land gen 1) (Z.land (fr_attr f) 4) = 0).
{ pose proof Hc0 as T2. rewrite branch_eq_U, U_lit in T2 by lia. apply Z.eqb_eq in T2.
lazymatch type of T2 with U ?Ev _ = _ => rewrite (U_transtest Ev gen (fr_attr f)) in T2 end;
[ exact T2
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E621
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E52
| exact Rgen | exact Q2 ]. }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x2384.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch. clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 901%nat (sv_denot Ev (SLit 0)) E901;
rechunk_off HS 516%nat 48 (SOff 901 0) ltac:(rewrite sv_denot_SOff0, E901; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
ra_join HS ss_R3 902%nat fl_R3_deads_bv ltac:(idtac;
ra_join_fact HS 901%nat (mkAF 0 1 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E901; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 0)), U_lit, unsigned_lit_small by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia));
fl_handX RR3 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists 0; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E901; reflexivity | split; [clear; lia|]];
unfold xhastr, xG; cbn [c_s x_GPAL x_cur x_bef]; rewrite <- XALPHA, (fl_trans_on_flag _ _ _ ltac:(rewrite <- XCg; clear - Q3; lia)), <- XSET, <- Hgen; unfold ACj6.fl_hasalpha, ACj6.fl_settr, YO07.flag; cbn [c_s c_f]; rewrite XT1; apply Z.lor_eq_0_iff in XT2; destruct XT2 as [X1 X4]; rewrite X1, X4; reflexivity|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X].
exists pt, w, h, top, left, tidx, img. cbn [c_s c_f c_ly c_S].
rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
split; [exact E892|]. split; [exact E844|]. split; [exact E845|]. split; [exact E841|]. split; [exact E846|]. split; [exact E842|]. split; [exact E891|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|]. split; [exact Htidx|].
split; [exact Hpt|].
split; [exact XD|]. split; [exact XTI|]. split; [exact XI|]. split; [exact XI0|]. split; [exact XLEN|]. exact XMLE.
+
assert (XT2 : Z.lor (Z.land gen 1) (Z.land (fr_attr f) 4) <> 0).
{ pose proof Hc0 as T2. rewrite branch_eq_U, U_lit in T2 by lia. apply Z.eqb_neq in T2.
lazymatch type of T2 with U ?Ev _ <> _ => rewrite (U_transtest Ev gen (fr_attr f)) in T2 end;
[ exact T2
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E621
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E52
| exact Rgen | exact Q2 ]. }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x2384.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch. clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 901%nat (sv_denot Ev (SLit 1)) E901;
rechunk_off HS 516%nat 48 (SOff 901 0) ltac:(rewrite sv_denot_SOff0, E901; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
ra_join HS ss_R3 902%nat fl_R3_deads_bv ltac:(idtac;
ra_join_fact HS 901%nat (mkAF 0 1 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E901; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 1)), U_lit, unsigned_lit_small by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia));
fl_handX RR3 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists 1; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E901; reflexivity | split; [clear; lia|]];
unfold xhastr, xG; cbn [c_s x_GPAL x_cur x_bef]; rewrite <- XALPHA, (fl_trans_on_flag _ _ _ ltac:(rewrite <- XCg; clear - Q3; lia)), <- XSET, <- Hgen; unfold ACj6.fl_hasalpha, ACj6.fl_settr, YO07.flag; cbn [c_s c_f]; rewrite XT1; destruct (Z.eqb_spec (Z.land gen 1) 0) as [X1|X1]; destruct (Z.eqb_spec (Z.land (fr_attr f) 4) 0) as [X4|X4]; cbn [orb negb]; try reflexivity;
exfalso; apply XT2; rewrite X1, X4; reflexivity|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X].
exists pt, w, h, top, left, tidx, img. cbn [c_s c_f c_ly c_S].
rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
split; [exact E892|]. split; [exact E844|]. split; [exact E845|]. split; [exact E841|]. split; [exact E846|]. split; [exact E842|]. split; [exact E891|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|]. split; [exact Htidx|].
split; [exact Hpt|].
split; [exact XD|]. split; [exact XTI|]. split; [exact XI|]. split; [exact XI0|]. split; [exact XLEN|]. exact XMLE.
Qed.
Lemma fl_R2X : fl_fromX0 KS MT XN B CTX wfn ss_R3 (INV_R3X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_R2 (INV_R2X MT B).
Proof. exact fl_R2X_aux. Qed.
End d.
End b.
End a.
