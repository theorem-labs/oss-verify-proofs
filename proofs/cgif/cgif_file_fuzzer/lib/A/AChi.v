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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACkc ACj4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACi4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma mod4_land2 : forall x, 0 <= x -> x mod 4 = 0 -> Z.land x 2 = 0.
Proof.
intros x Hx H4. replace x with ((x / 4) * 2 ^ 2) by (pose proof (Z.div_mod x 4 ltac:(lia)); lia).
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n 2) as [Hl|Hge].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 2 n) with false; [apply andb_false_r|]. symmetry. change 2 with (2 ^ 1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma mod4_land1 : forall x, 0 <= x -> x mod 4 = 0 -> Z.land x 1 = 0.
Proof.
intros x Hx H4. replace x with ((x / 4) * 2 ^ 2) by (pose proof (Z.div_mod x 4 ltac:(lia)); lia).
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n 2) as [Hl|Hge].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 1 n) with false; [apply andb_false_r|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
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
Ltac bef_facts fb :=
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
assert (E651 : ew Ev 651 = Z_to_bv 64 (fr_lpal fb)) by reflexivity;
assert (E652 : ew Ev 652 = Z_to_bv 64 (fr_img fb)) by reflexivity;
assert (E653 : ew Ev 653 = Z_to_bv 64 (fr_attr fb)) by reflexivity;
assert (E654 : ew Ev 654 = Z_to_bv 64 (fr_gen fb)) by reflexivity;
assert (E655 : ew Ev 655 = Z_to_bv 64 (fr_delay fb)) by reflexivity;
assert (E656 : ew Ev 656 = Z_to_bv 64 (fr_nlp fb)) by reflexivity;
assert (E657 : ew Ev 657 = Z_to_bv 64 (fr_ctidx fb)) by reflexivity;
assert (E658 : ew Ev 658 = Z_to_bv 64 (fr_disp fb)) by reflexivity;
assert (E659 : ew Ev 659 = Z_to_bv 64 (fr_tidx fb)) by reflexivity end.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Lemma fl_CX_aux : fl_fromX0 KS MT XN B CTX wfn ss_R (INV_RX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_T0 (INV_T0X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIFF (INV_DIFFX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_B3 (INV_B3X MT B).
Proof.
intros RR RT RD. fl_preludeX.
pose proof HINV as ((Hk3 & Eab3 & (gen & E621 & Rgen & Hgen4) & E625) & E621X & MLE0).
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
{ rewrite <- XGEN3. apply zbv_inj64; [rewrite <- E621; exact E621X | clear - Rgen; lia |].
pose proof (fl_gen123_range (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) ltac:(cbn [c_f]; clear - Q3; lia)) as G; cbn [c_f] in G; clear - G Q3; lia. }
clear XNPAL XULCT XALPHA XSET XGEN3 E621X.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
hc_bool Hc ltac:(fun H => lazymatch type of H with context [U ?Ev (SExt false 8 (SOff 621 0))] => rewrite (gen_test8 Ev 621 gen 2 ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E621) ltac:(clear - Rgen Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia)) in H end).
destruct (nth (i - 1) (cg_frames s) None) as [fb|] eqn:Hfb.
2:{ exfalso. pose proof (mod4_land2 gen ltac:(lia) (Hgen4 eq_refl)) as X. rewrite X in Hc. discriminate Hc. }
cbn [frame_ptr] in E12.
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
pose proof (Ofr fb Hfbi) as Ob.
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & Hbpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hbef_in) as Hbh_img.
destruct (al_blocks _ _ LAWS ly S W mem md (fr_img fb) N HAR Hbimg_in) as (Hbi16 & Hbi4096 & Hbiceil & [Hbih1 Hbih2] & _ & _).
change (req_size FRAME_SIZE) with 40 in *.
assert (Hqi : 1 <= req_size N) by (unfold req_size; destruct (Z.eqb_spec N 0); lia).
pose proof (fl_bef_sep B LAWS ly S W mem md g s N rest i f fb HAR HPerm Hf Hfbe Hi) as Hsep_cb.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ g CGIF_SIZE (fr_ptr fb) FRAME_SIZE HAR Hing Hbef_in ltac:(unfold CGIF_SIZE, FRAME_SIZE; intros X; injection X; lia)) as Hsep_gb.
unfold zdisjoint in Hsep_gb. cbn [fst snd] in Hsep_gb. change (req_size CGIF_SIZE) with 96 in Hsep_gb. change (req_size FRAME_SIZE) with 40 in Hsep_gb.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr fb) FRAME_SIZE HAR Hraw_in Hbef_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as Hsep_rb.
unfold zdisjoint in Hsep_rb. cbn [fst snd] in Hsep_rb. change (req_size RAW_SIZE) with 48 in Hsep_rb. change (req_size FRAME_SIZE) with 40 in Hsep_rb.
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hbef_in).
pose proof (sep_block_frame SEGS _ LAWS ly3 S3 _ _ _ (fr_ptr fb) FRAME_SIZE 2 fpos HAR3 Hbef3 Hfin3) as HdFB.
unfold zdisjoint in HdFB; cbn [fst snd] in HdFB; change (req_size FRAME_SIZE) with 40 in HdFB; change (fs_frame_bytes 2) with 256 in HdFB; rewrite EFA3 in HdFB. fold F in HdFB.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (Ob3 : obj_at SEGS (mrestrict (w_H Wx) (ms_mem msx)) (fr_ptr fb) LAY_Frame (frame_vals fb)) | st_ok _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (Ob3 : obj_at SEGS (mrestrict (w_H Wx) (ms_mem msx)) (fr_ptr fb) LAY_Frame (frame_vals fb))  end.
{ eapply (aj_obj_kept B); [exact HJ3 | exact Hbef_in | exact Hbef3 | exact Ob | vm_compute; reflexivity |].
change (req_size FRAME_SIZE) with 40. intros j Hj. apply fl_fp0_out_frame; [clear - Hsep_cb Hob241 Hob242 Hob253 Huar; lia | exact Hj]. }
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict ?Hh ?msv) =>
assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by lia; exact E12);
pose proof (st_ok_pi_add_bef Ev ssv Hh msv fb HS ltac:(vm_compute; reflexivity)
ltac:(rewrite E12n; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbh1 Hbceil Hb16 Hbih1 ltac:(clear - Hbih2 Hqi Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbi16 Ob3
ltac:(unfold fl_Ebef, fl_bef_region; cbn [map frame_vals]; lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE, FRAME_SIZE;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 Hbh1 Hbh2 Hbh_img HF8hi HF8lo HF8c HFceil HdFB Hsep_gb Hsep_cb Hob241 Hob242 Hob253 Huar; ceil; unfold off_img, ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kHighMemBeg in *; repeat split; try lia;
match goal with |- ?g => idtac "DISJ-LEFT" g end)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) =>
assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by lia; exact E12);
pose proof (st_ok_add_bef Ev ssv Hh msv fb HS ltac:(vm_compute; reflexivity)
ltac:(rewrite E12n; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbh1 Hbceil Hb16 Hbih1 ltac:(clear - Hbih2 Hqi Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbi16 Ob3
ltac:(unfold fl_Ebef, fl_bef_region; cbn [map frame_vals]; lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE, FRAME_SIZE;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 Hbh1 Hbh2 Hbh_img HF8hi HF8lo HF8c HFceil HdFB Hsep_gb Hsep_cb Hob241 Hob242 Hob253 Huar; ceil; unfold off_img, ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kHighMemBeg in *; repeat split; try lia;
match goal with |- ?g => idtac "DISJ-LEFT" g end)) as HS3;
clear HS; rename HS3 into HS  end.
unfold fl_Ebef in HS. cbn [map frame_vals] in HS. norm_ss HS. hei_havoc HS.
bef_facts fb.
reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x1a74.
all: try (oblG HJ3 E11n E32n Hcur3).
all: try (oblG HJ3 E12n E32n Hbef3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => ra_join HS ss_DIFF 681%nat ra_deads_DIFF ltac:(idtac); fl_handX RD HS end.
split.
{ split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|]; split; [exact Rgen|]; apply Z.eqb_neq; exact Hc|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
exists fb. apply fl_bef_havoc; [clear; lia|]. split; [exact Hfb|]. cbn [c_i c_s]. bef_EB. }
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); lazymatch goal with H : ew ?Ev 621 = Z_to_bv 64 gen |- ew ?Ev 621 = _ => rewrite H, Hgen; reflexivity end|].
split; [unfold YO07.flag; change (xgen3 _ _) with (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef); rewrite <- Hgen, Hc; reflexivity|].
exact MLE0.
-
hc_bool Hc ltac:(fun H => lazymatch type of H with context [U ?Ev (SExt false 8 (SOff 621 0))] => rewrite (gen_test8 Ev 621 gen 2 ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E621) ltac:(clear - Rgen Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia)) in H end).
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x20a4.
all: try (oblG HJ3 E10n E32n Hing3).
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
destruct (Z.eqb_spec (Z.land gen 1) 0) as [Hg1|Hg1].
+
reshok HS.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E10n E32n Hing3).
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
*
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x22f0.
all: try (oblG HJ3 E10n E32n Hing3).
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
prreg HS (23%bv : bv 5) Q23; prreg HS (27%bv : bv 5) Q27;
add_atom HS 839%nat (sv_denot Ev (SOff 40 0)) E839;
rechunk_off HS 60%nat 168 (SOff 839 0) ltac:(rewrite sv_denot_SOff0, E839; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 840%nat (sv_denot Ev (SLit 0)) E840;
rechunk_off HS 60%nat 144 (SOff 840 0) ltac:(rewrite sv_denot_SOff0, E840; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 841%nat (sv_denot Ev (SLit 0)) E841;
rechunk_off HS 60%nat 152 (SOff 841 0) ltac:(rewrite sv_denot_SOff0, E841; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 842%nat (sv_denot Ev (SOff 58 0)) E842;
rechunk_off HS 60%nat 232 (SOff 842 0) ltac:(rewrite sv_denot_SOff0, E842; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
ra_join HS ss_R 843%nat fl_R_deads_bv ltac:(idtac;
ra_join_val HS 843%nat 0%nat Q23 E843; ra_join_val HS 843%nat 2%nat Q27 E845;
ra_join_fact HS 839%nat (mkAF 1 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E839, sv_denot_SOff0; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E40, unsigned_lit_small by (clear - R7 HW1 Hob241 Hob242 Hob253 Huar; lia); clear - R7 HW1 Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 840%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E840; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 0)), U_lit, unsigned_lit_small by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 841%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E841; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 0)), U_lit, unsigned_lit_small by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 845%nat (mkAF 1 65535 0) ltac:(rewrite E845; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E41, unsigned_lit_small by (clear - R8 HH1 Hob241 Hob242 Hob253 Huar; lia); clear - R8 HH1 Hob241 Hob242 Hob253 Huar; lia));
fl_handX RR HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); lazymatch goal with H : ew ?Ev 621 = Z_to_bv 64 gen |- ew ?Ev 621 = _ => rewrite H, Hgen; reflexivity end].
exists 0, (cg_W s), (cg_H s), 0, 0, (fr_tidx f). cbn [c_s c_ly c_S].
split; [rewrite E843; reflexivity|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E839, sv_denot_SOff0; exact E40|].
split; [rewrite E845; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; exact E41|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E841; reflexivity|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E840; reflexivity|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E842, sv_denot_SOff0; rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E58|].
split; [clear; lia|].
split; [exact HW1|]. split; [clear; lia|]. split; [clear; lia|]. split; [exact HH1|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear - Q8 Hob241 Hob242 Hob253 Huar; lia|].
split. { left. split; [reflexivity|]. split; [exact Hk3 | exact Eab3]. }
assert (XF2f : YO07.flag (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef) 2 = false) by (unfold YO07.flag; rewrite <- Hgen, Hc; reflexivity).
assert (XF1f : YO07.flag (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef) 1 = false) by (unfold YO07.flag; rewrite <- Hgen, Hg1; reflexivity).
unfold xdims, xtidx, ximg, xmacc, xG. cbn [c_s c_S x_GPAL x_cur x_bef].
split; [rewrite (fl_dims_nodiff _ _ _ XF2f); reflexivity|].
split; [rewrite (fl_tidx_notrans _ _ _ XF1f), <- XCt; apply Z.mod_small; clear - Q8; lia|].
split; [intros Hpt; exfalso; exact (Hpt eq_refl)|].
split; [intros _; rewrite (fl_img_notrans _ _ _ XF1f); exact (fl_tmp_nodiff _ _ _ XF2f)|].
split; [rewrite (fl_img_notrans _ _ _ XF1f), (fl_tmp_nodiff _ _ _ XF2f), XClen; exact HN|].
rewrite Z.eqb_refl. exact MLE0.
* hc_bool Hc0 ltac:(fun H => lazymatch type of H with context [U ?Ev (SExt false 8 (SOff 621 0))] => rewrite (gen_test8 Ev 621 gen 1 ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E621) ltac:(clear - Rgen Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia)) in H end).
exfalso. rewrite Hg1 in Hc0. cbn in Hc0. discriminate Hc0.
+
destruct (nth (i - 1) (cg_frames s) None) as [fb|] eqn:Hfb.
2:{ exfalso. exact (Hg1 (mod4_land1 gen ltac:(lia) (Hgen4 eq_refl))). }
cbn [frame_ptr] in E12.
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
pose proof (Ofr fb Hfbi) as Ob.
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & Hbpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hbef_in) as Hbh_img.
destruct (al_blocks _ _ LAWS ly S W mem md (fr_img fb) N HAR Hbimg_in) as (Hbi16 & Hbi4096 & Hbiceil & [Hbih1 Hbih2] & _ & _).
change (req_size FRAME_SIZE) with 40 in *.
assert (Hqi : 1 <= req_size N) by (unfold req_size; destruct (Z.eqb_spec N 0); lia).
pose proof (fl_bef_sep B LAWS ly S W mem md g s N rest i f fb HAR HPerm Hf Hfbe Hi) as Hsep_cb.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ g CGIF_SIZE (fr_ptr fb) FRAME_SIZE HAR Hing Hbef_in ltac:(unfold CGIF_SIZE, FRAME_SIZE; intros X; injection X; lia)) as Hsep_gb.
unfold zdisjoint in Hsep_gb. cbn [fst snd] in Hsep_gb. change (req_size CGIF_SIZE) with 96 in Hsep_gb. change (req_size FRAME_SIZE) with 40 in Hsep_gb.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr fb) FRAME_SIZE HAR Hraw_in Hbef_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as Hsep_rb.
unfold zdisjoint in Hsep_rb. cbn [fst snd] in Hsep_rb. change (req_size RAW_SIZE) with 48 in Hsep_rb. change (req_size FRAME_SIZE) with 40 in Hsep_rb.
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hbef_in).
pose proof (sep_block_frame SEGS _ LAWS ly3 S3 _ _ _ (fr_ptr fb) FRAME_SIZE 2 fpos HAR3 Hbef3 Hfin3) as HdFB.
unfold zdisjoint in HdFB; cbn [fst snd] in HdFB; change (req_size FRAME_SIZE) with 40 in HdFB; change (fs_frame_bytes 2) with 256 in HdFB; rewrite EFA3 in HdFB. fold F in HdFB.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (Ob3 : obj_at SEGS (mrestrict (w_H Wx) (ms_mem msx)) (fr_ptr fb) LAY_Frame (frame_vals fb)) | st_ok _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (Ob3 : obj_at SEGS (mrestrict (w_H Wx) (ms_mem msx)) (fr_ptr fb) LAY_Frame (frame_vals fb))  end.
{ eapply (aj_obj_kept B); [exact HJ3 | exact Hbef_in | exact Hbef3 | exact Ob | vm_compute; reflexivity |].
change (req_size FRAME_SIZE) with 40. intros j Hj. apply fl_fp0_out_frame; [clear - Hsep_cb Hob241 Hob242 Hob253 Huar; lia | exact Hj]. }
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict ?Hh ?msv) =>
assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by lia; exact E12);
pose proof (st_ok_pi_add_bef Ev ssv Hh msv fb HS ltac:(vm_compute; reflexivity)
ltac:(rewrite E12n; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbh1 Hbceil Hb16 Hbih1 ltac:(clear - Hbih2 Hqi Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbi16 Ob3
ltac:(unfold fl_Ebef, fl_bef_region; cbn [map frame_vals]; lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE, FRAME_SIZE;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 Hbh1 Hbh2 Hbh_img HF8hi HF8lo HF8c HFceil HdFB Hsep_gb Hsep_cb Hob241 Hob242 Hob253 Huar; ceil; unfold off_img, ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kHighMemBeg in *; repeat split; try lia;
match goal with |- ?g => idtac "DISJ-LEFT" g end)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) =>
assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by lia; exact E12);
pose proof (st_ok_add_bef Ev ssv Hh msv fb HS ltac:(vm_compute; reflexivity)
ltac:(rewrite E12n; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbh1 Hbceil Hb16 Hbih1 ltac:(clear - Hbih2 Hqi Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbi16 Ob3
ltac:(unfold fl_Ebef, fl_bef_region; cbn [map frame_vals]; lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE, FRAME_SIZE;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 Hbh1 Hbh2 Hbh_img HF8hi HF8lo HF8c HFceil HdFB Hsep_gb Hsep_cb Hob241 Hob242 Hob253 Huar; ceil; unfold off_img, ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kHighMemBeg in *; repeat split; try lia;
match goal with |- ?g => idtac "DISJ-LEFT" g end)) as HS3;
clear HS; rename HS3 into HS  end.
unfold fl_Ebef in HS. cbn [map frame_vals] in HS. norm_ss HS. hei_havoc HS. bef_facts fb.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
prreg HS (23%bv : bv 5) Q23; prreg HS (27%bv : bv 5) Q27;
add_atom HS 679%nat (sv_denot Ev (SOff 40 0)) E679;
rechunk_off HS 60%nat 168 (SOff 679 0) ltac:(rewrite sv_denot_SOff0, E679; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 680%nat (sv_denot Ev (SLit 0)) E680;
rechunk_off HS 60%nat 144 (SOff 680 0) ltac:(rewrite sv_denot_SOff0, E680; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 681%nat (sv_denot Ev (SLit 0)) E681;
rechunk_off HS 60%nat 152 (SOff 681 0) ltac:(rewrite sv_denot_SOff0, E681; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
ra_join HS ss_T0 682%nat fl_T0_deads_bv ltac:(idtac;
ra_join_val HS 682%nat 0%nat Q23 E682; ra_join_val HS 682%nat 2%nat Q27 E684;
ra_join_fact HS 679%nat (mkAF 1 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E679, sv_denot_SOff0; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E40, unsigned_lit_small by (clear - R7 HW1 Hob241 Hob242 Hob253 Huar; lia); clear - R7 HW1 Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 680%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E680; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 0)), U_lit, unsigned_lit_small by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 681%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E681; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 0)), U_lit, unsigned_lit_small by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 684%nat (mkAF 1 65535 0) ltac:(rewrite E684; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E41, unsigned_lit_small by (clear - R8 HH1 Hob241 Hob242 Hob253 Huar; lia); clear - R8 HH1 Hob241 Hob242 Hob253 Huar; lia));
fl_handX RT HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists fb; do 4 (apply fl_bef_havoc; [clear; lia|]); split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); lazymatch goal with H : ew ?Ev 621 = Z_to_bv 64 gen |- ew ?Ev 621 = _ => rewrite H, Hgen; reflexivity end].
exists 0, (cg_W s), (cg_H s), 0, 0. cbn [c_s c_ly c_S].
split; [rewrite E682; reflexivity|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E679, sv_denot_SOff0; exact E40|].
split; [rewrite E684; exact E41|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E681; reflexivity|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E680; reflexivity|].
split; [clear; lia|].
split; [exact HW1|]. split; [clear; lia|]. split; [clear; lia|]. split; [exact HH1|]. split; [clear; lia|]. split; [clear; lia|].
split. { left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hk3 | exact Eab3]. }
assert (XF2f : YO07.flag (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef) 2 = false) by (unfold YO07.flag; rewrite <- Hgen, Hc; reflexivity).
unfold xdims, xtmp, xmacc, xG. cbn [c_s c_S x_GPAL x_cur x_bef].
split; [rewrite (fl_dims_nodiff _ _ _ XF2f); reflexivity|].
split; [intros Hpt; exfalso; exact (Hpt eq_refl)|].
split; [intros _; exact (fl_tmp_nodiff _ _ _ XF2f)|].
split; [rewrite (fl_tmp_nodiff _ _ _ XF2f), XClen; exact HN|].
rewrite Z.eqb_refl. exact MLE0.
Qed.
Lemma fl_CX : fl_fromX0 KS MT XN B CTX wfn ss_R (INV_RX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_T0 (INV_T0X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_DIFF (INV_DIFFX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_B3 (INV_B3X MT B).
Proof. exact fl_CX_aux. Qed.
End d.
End b.
End a.
