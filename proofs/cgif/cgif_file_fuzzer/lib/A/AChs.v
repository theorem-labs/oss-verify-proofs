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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACkc ACj4 ACj9 ACjn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7 ACj3 ACj5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACih ACij ACi4.
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
Lemma denot_add_lit0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0.
rewrite Z.add_0_r. apply zcanon_id. pose proof (U_range E e). rewrite M64_val in *. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section l.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section m.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
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
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis HXM : forall N M, 1 <= M <= N -> N <= 100000000 -> mo_malloc MT M + xm_rawadd XN M + mo_free MT <= xm_flush XN N.
Hypothesis HXMN : forall M, 1 <= M <= 100000000 -> 0 <= xn_rawadd XN M <= xm_rawadd XN M.
Hypothesis HTR : forall (pcf ra : Z) (regsT regs : bvmap 5 word) ch,
In (raZ regs :: spine ch) CTX -> raZ regsT = ra ->
((pcf = pc_free_ra0 (as_code B) /\ ra = BASE + 0x2448) \/ (pcf = pc_malloc_ra0 (as_code B) /\ ra = BASE + 0x1fd4) \/
(pcf = pc_malloc_ra0 (as_code B) /\ ra = BASE + 0x2124)) ->
In (call_trace0 pcf regsT ((spZ regs, raZ regs, s0Z regs) :: ch)) (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Lemma fl_T2X_aux : fl_fromX0 KS MT XN B CTX wfn ss_T3 (INV_T3X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_T1x (INV_T1xX MT B).
Proof.
intros RT3. fl_preludeX.
pose proof HINV as (((gen & E621 & Rgen) & E625 & (fb & Hfb & EB) & (pt & w & h & top & left & E682 & E683 & E684 & E681 & E685 & Hrpt & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & Hpt & (XD & XI & XI0 & XLEN & XMLE)) & E621X) & XF1 & (tv & E741 & Rtv & Xtv)).
xpt_facts Hpt XPT.
pose proof HCUR as (_ & _ & _ & _ & _ & _ & _ & XCimg & XClen & _).
cbn [c_i c_s] in Hfb. pose proof Hpt as Hpt0. unfold fl_tmpblkX, fl_FP0 in Hpt. cbn [c_ly c_S c_regs c_f c_s] in Hpt.
pose proof (EB 0%nat _ eq_refl) as E651. pose proof (EB 1%nat _ eq_refl) as E652. pose proof (EB 2%nat _ eq_refl) as E653.
pose proof (EB 3%nat _ eq_refl) as E654. pose proof (EB 4%nat _ eq_refl) as E655. pose proof (EB 5%nat _ eq_refl) as E656.
pose proof (EB 6%nat _ eq_refl) as E657. pose proof (EB 7%nat _ eq_refl) as E658. pose proof (EB 8%nat _ eq_refl) as E659.
cbn [Nat.add] in E651, E652, E653, E654, E655, E656, E657, E658, E659.
rewrite Hfb in E12. cbn [frame_ptr] in E12.
assert (Hwh0 : 0 <= w * h) by (apply Z.mul_nonneg_nonneg; clear - Hw1 Hh1 Hob241 Hob242 Hob253 Huar; lia).
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & _ & _). change (req_size FRAME_SIZE) with 40 in Hbceil, Hbh2.
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)).
{ intros x Hx. destruct Hpt as [(_ & _ & _ & _ & Eab3) | (_ & _ & (_ & _ & _ & Eab3 & _))]; rewrite Eab3; [exact Hx | apply in_app_iff; left; exact Hx]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
assert (Himg3 : In (fr_img f, N) (ablocks B ly3 S3)) by (apply Hsub3; exact Himg_in).
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hbef_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (apply Hsub3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK FLBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
first [ clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia | revert Hrg; evalE AG; intros Hrg; clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia ] |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
hc_bool Hc ltac:(fun H => hc_atom H 682%nat pt E682 ltac:(clear - Hrpt Hob241 Hob242 Hob253 Huar; lia)).
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x2160.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
prreg HS (@BV 5 23 I) Q23;
ra_join HS ss_T3 801%nat fl_T3_deads_bv ltac:(idtac; ra_join_val HS 801%nat 0%nat Q23 E761;
ra_join_fact HS 801%nat (HPTR 4) ltac:(rewrite E761; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E682, unsigned_lit_small by (clear - Hrpt Hob241 Hob242 Hob253 Huar; lia); unfold HPTR; cbn [af_lo af_hi af_al2]; change (2 ^ 4) with 16;
destruct Hpt as [(Hp0 & _) | (_ & _ & (Hq1 & Hq2 & Hq16 & _))]; [exfalso; clear - Hp0 Hc Hob241 Hob242 Hob253 Huar; hc_prop Hc; exact (Hc Hp0)|]; clear - Hq1 Hq2 Hq16 Hwh0 Hob241 Hob242 Hob253 Huar; ceil; lia));
fl_handX RT3 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
split; [| split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X | split; [exact XF1 |
exists tv; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E741 | split; [exact Rtv | exact Xtv]]]]].
exists pt, w, h, top, left. cbn [c_s c_ly c_S c_regs c_f].
split; [rewrite E761; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E682|]. rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia). split; [exact E683|]. split; [exact E684|]. split; [exact E681|]. split; [exact E685|].
split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
hc_prop Hc. destruct Hpt0 as [(Hp0 & _) | (_ & Hk2 & Htb)]; [exfalso; exact (Hc Hp0)|]. split; [exact Hk2|]. split; [exact Htb|].
split; [exact XD|]. split; [exact (XI Hc)|]. split; [exact XLEN|].
unfold xmacc in XMLE. rewrite (proj2 (Z.eqb_neq pt 0) Hc) in XMLE. exact XMLE.
-
hc_bool Hc ltac:(fun H => hc_atom H 682%nat pt E682 ltac:(clear - Hrpt Hob241 Hob242 Hob253 Huar; lia)). hc_prop Hc.
destruct Hpt as [(_ & Ew & Eh & Hk0 & Eab3) | (Hp1 & _)]; [|exfalso; exact (Hp1 Hc)].
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x528cc.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
first [ clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia | revert Hrg; evalE AG; intros Hrg; clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia ] |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
clear_frames.
prreg HS (@BV 5 1 I) Rra. prreg HS (@BV 5 2 I) Rsp. prreg HS (@BV 5 3 I) Rgp. prreg HS (@BV 5 4 I) Rtp. prreg HS (@BV 5 8 I) Rs0.
lazymatch type of AG with forall n, _ -> ew ?Ebase n = _ => assert (Usp3 : bv_unsigned (ew Ebase 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia);
assert (EraX : raZ rg = (BASE + 0x2124)) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (HWH : 1 <= cg_H s * cg_W s <= 100000000) by (split; [clear - HW1 HH1 Hob241 Hob242 Hob253 Huar; nia | rewrite Z.mul_comm, <- HN; exact HNle]).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 (cg_H s * cg_W s))
(eq_trans (denot_add_lit0 Ev _) (denot_mul_hw Ev 41 40 (cg_H s) (cg_W s) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E41) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40)
ltac:(clear - R8 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - R7 Hob241 Hob242 Hob253 Huar; lia))) Ra0 | st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 (cg_H s * cg_W s))
(eq_trans (denot_add_lit0 Ev _) (denot_mul_hw Ev 41 40 (cg_H s) (cg_W s) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E41) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40)
ltac:(clear - R8 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - R7 Hob241 Hob242 Hob253 Huar; lia))) Ra0  end.
replace (cg_H s * cg_W s) with N in Ra0 by (rewrite HN; apply Z.mul_comm). replace (cg_H s * cg_W s) with N in HWH by (rewrite HN; apply Z.mul_comm).
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi Hob241 Hob242 Hob253 Huar; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS Hob241 Hob242 Hob253 Huar; lia) Qal8
ltac:(clear - Htop32 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia))
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS Hob241 Hob242 Hob253 Huar; lia) Qal8
ltac:(clear - Htop32 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia))
| ]  end.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3' & _).
assert (HEVc : st_nev S3 < EV_MAX) by (rewrite HEV in Hev; clear - Hnev3 Hev Hk0 Hob241 Hob242 Hob253 Huar; lia).
pmkst HS.
ppcs.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (AMALLOC4 W3 (ms_regs msX) (ms_mem msX) TFLUSH_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly3 S3 mdX k N (sp1 - spZ regs) (Z_to_bv 64 (BASE + 0x2124)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ra0.
- unfold MALLOC_MAX. clear - HWH. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_FLUSH in Hlive. clear - Hlive HWH. lia.
- rewrite EspX. clear; lia.
- rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
- clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia.
- rewrite FFS. unfold ASTACK. clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia.
- rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
- rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- exact HEVc.
- apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | exact Es0X | rewrite EraX; clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia].
- apply (HTR (pc_malloc_ra0 (as_code B)) (BASE + 0x2124)); [exact Hctx | exact EraX | right; right; split; reflexivity].
-
unfold xmacc in XMLE. rewrite Hc in XMLE. cbn [Z.eqb] in XMLE.
eapply (mok_station MT S S3 (xm_flush XN N) 0 _ MLAW HMOK XMLE); [apply (mo_malloc_nonneg MT MLAW); clear - HWH; lia|].
pose proof (HXM N N ltac:(clear - HWH; lia) ltac:(clear - HWH; lia)) as BM. pose proof (HXMN N ltac:(clear - HWH; lia)) as BMN. pose proof (mo_free_nonneg MT MLAW) as F0.
clear - BM BMN F0. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hnz4 & Eab4x & HK4x & MLE4).
mresX Hnz4 Eab4x HK4x Hres. clear Eab4x HK4x.
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hres by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
pose proof (proj1 HJ4) as HAR4.
clear HUP. assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (2, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
destruct Hres as [(Hres0 & Eab4 & HK) | (Hres4096 & Eab4 & HK)].
+   exfalso. clear - Hres0 Hnz4. lia.
+
assert (Hrq : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0); [exfalso; clear - HWH e Hob241 Hob242 Hob253 Huar; lia | reflexivity]).
assert (Hres_in : In (res, N) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hing3).
assert (Hcur4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hcur3).
assert (Hbef4 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hbef3).
assert (Himg4 : In (fr_img f, N) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Himg3).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res N HAR4 Hres_in) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & Hnpres & _). pose proof (proj1 Hnh_ia) as Hnh. rewrite Hrq in Hnceil, Hnpres.
pose proof (blk_off_imgP _ _ _ _ _ _ res N HAR4 Hres_in) as Hnh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N HAR4 Himg4) as (_ & _ & _ & _ & Hipres4 & _). rewrite Hrq in Hipres4.
pose proof (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res N HJ3 HAR4 Eab4 ltac:(clear - HWH Hob241 Hob242 Hob253 Huar; lia)) as Tres.
assert (Ares : forall blc lyq ownq i, In (res, N) blc -> 0 <= i < N ->
awr_byte TFLUSH_STK (spZ regs) [(fr_ptr f + 20, fr_ptr f + 24)] (ablocks B ly S) blc lyq ownq (res + i)).
{ intros blc lyq ownq ii Hbl Hiq. exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res N blc ii lyq ownq HJ3 HAR4 Eab4 ltac:(clear - HWH Hob241 Hob242 Hob253 Huar; lia) Hbl ltac:(rewrite Hrq; exact Hiq)). }
assert (HPerm4 : Permutation (ablocks B ly4 S4) (ablocks B ly S ++ [(res, N)])) by (rewrite Eab4, Eab3; apply Permutation_refl).
pose proof (sep_block_frame SEGS B LAWS ly4 S4 _ _ _ res N 2 fpos HAR4 Hres_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Hrq in HdPF. change (fs_frame_bytes 2) with 256 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res N g CGIF_SIZE HAR4 HPerm4 Hing) as HdPG. change (req_size CGIF_SIZE) with 96 in HdPG. rewrite Hrq in HdPG.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res N (fr_ptr f) FRAME_SIZE HAR4 HPerm4 Hcur_in) as HdPC. change (req_size FRAME_SIZE) with 40 in HdPC. rewrite Hrq in HdPC.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res N (fr_ptr fb) FRAME_SIZE HAR4 HPerm4 Hbef_in) as HdPB. change (req_size FRAME_SIZE) with 40 in HdPB. rewrite Hrq in HdPB.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res N (fr_img f) N HAR4 HPerm4 Himg_in) as HdPI. rewrite Hrq in HdPI.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS _); [exact HK | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E12; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia
| exact Hbef3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPB Hrq Hob241 Hob242 Hob253 Huar; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj SEGS _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hn; clear - Ha Hn Hnh Hnh_ia Hrq HF8lo HF8c HFceil C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold SB in *; zone_lia
| intros a Ha; exfalso; clear - Ha Hob241 Hob242 Hob253 Huar; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj SEGS _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hn; clear - Ha Hn HdPF Hrq Hob241 Hob242 Hob253 Huar; lia
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha Hob241 Hob242 Hob253 Huar; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj SEGS _); [exact HK | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj SEGS _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgot3 | exact Kgot4 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kcell3 | exact Kcell4 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kguar3 | exact Kguar4 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 59%nat) _ _ _ _ _) =>
let AGx := lazymatch goal with A : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => A end in
let Bv := rnB in apply (region_kept_val_at Ex _ _ 59%nat (as_uar_cell Bv) 4 1); [evalE AGx | exact Kuar3 | exact Kuar4 | lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS _); [exact HK | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPG Hrq Hob241 Hob242 Hob253 Huar; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 SEGS B LAWS); [exact HK | exact HAR4 | exact Hcur4 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPC Hrq Hob241 Hob242 Hob253 Huar; lia ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
prreg HS (@BV 5 10 I) Rres. rewrite Ha04 in Rres. symmetry in Rres.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (HPTR 4) HS
ltac:(clear HS; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rres; unfold w64; rewrite unsigned_lit_small by (clear - Hnh Hnceil HWH C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia);
change (2 ^ 4) with 16; clear - Hnh Hnceil Hn16 HWH C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ4 SHOK FLBspan 0x51578.
all: try (oblG HJ4 E11n E32n Hcur4).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
first [ clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia | revert Hrg; evalE AG; intros Hrg; clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia ] |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
clear_frames.
prreg HS (@BV 5 10 I) Ra0. prreg HS (@BV 5 11 I) Ra1. prreg HS (@BV 5 1 I) Rra. prreg HS (@BV 5 2 I) Rsp. prreg HS (@BV 5 3 I) Rgp. prreg HS (@BV 5 4 I) Rtp.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (@BV 5 12 I) (Z_to_bv 64 (cg_H s * cg_W s))
(eq_trans (denot_add_lit0 Ev _) (denot_mul_hw Ev 41 40 (cg_H s) (cg_W s) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E41) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40)
ltac:(clear - R8 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - R7 Hob241 Hob242 Hob253 Huar; lia))) Ra2 | st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 12 I) (Z_to_bv 64 (cg_H s * cg_W s))
(eq_trans (denot_add_lit0 Ev _) (denot_mul_hw Ev 41 40 (cg_H s) (cg_W s) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E41) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40)
ltac:(clear - R8 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - R7 Hob241 Hob242 Hob253 Huar; lia))) Ra2  end.
replace (cg_H s * cg_W s) with N in Ra2 by (rewrite HN; apply Z.mul_comm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N (proj1 HJ4) Himg4) as (_ & _ & _ & _ & HipresT & _). rewrite Hrq in HipresT.
pmkst HS.
change (Z_to_bv 64 333176) with (Z_to_bv 64 (SIGMA AS_asan_memcpy)).
clear Kgot4 Kcell4 Kguar4 Kuar4. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AMEMCPY W4 (ms_regs msX) (ms_mem msX) TFLUSH_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly4 S4 _ (k + 1) res (fr_img f) N (sp1 - spZ regs) (Z_to_bv 64 (BASE + 0x2158)) HJ4) end.
- rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Rres. reflexivity.
- rewrite Ra1, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite E51. reflexivity.
- exact Ra2.
- clear - HWH Hob241 Hob242 Hob253 Huar; lia. - clear - Hn4096 Hob241 Hob242 Hob253 Huar; lia. - clear - Hnceil C1 Hob241 Hob242 Hob253 Huar; lia.
- unfold spZ at 1. rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite E60, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia). clear; lia.
- rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
- clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia.
- rewrite FFS. unfold ESTACK. clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia.
- rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 3%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia). rewrite (EE 3%nat (@BV 5 3 I) eq_refl). exact Hgp.
- rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 4%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia). rewrite (EE 4%nat (@BV 5 4 I) eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- intros a Ha. split; [replace a with (res + (a - res)) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); apply Ares; [exact Hres_in | clear - Ha Hob241 Hob242 Hob253 Huar; lia] | unfold ESTACK; clear - Ha Hnceil Hceil Hslo Hsp1 FFS C1 Hob241 Hob242 Hob253 Huar; lia].
- apply (amem_range_of_block SEGS B LAWS ly4 S4 _ _ _ res N _ _ HAR4 Hres_in); rewrite ?Hrq; clear - HWH Hob241 Hob242 Hob253 Huar; lia.
- apply (range_addressable_of_block SEGS B LAWS ly4 S4 _ _ _ res N _ _ (proj1 HJ4) Hres_in); rewrite ?Hrq; clear - HWH Hob241 Hob242 Hob253 Huar; lia.
- intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly4 S4 _ _ _ res N _ _ (proj1 HJ4) Hres_in); rewrite ?Hrq; clear - HWH Hob241 Hob242 Hob253 Huar; lia.
- split; [clear - Hi4096 Hob241 Hob242 Hob253 Huar; lia|]. split; [clear - Hiceil Hrq C1 Hob241 Hob242 Hob253 Huar; lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HipresT a ltac:(clear - Ha Hob241 Hob242 Hob253 Huar; lia)))|].
unfold spZ. rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite E60, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia).
unfold ESTACK. clear - Ha Hiceil Hrq Hceil Hslo Hsp1 FFS C1 Hob241 Hob242 Hob253 Huar; lia. }
split; [clear - HdPI Hob241 Hob242 Hob253 Huar; lia|].
split; [apply (amem_range_of_block SEGS B LAWS ly4 S4 _ _ _ (fr_img f) N _ _ HAR4 Himg4); rewrite ?Hrq; clear - HWH Hob241 Hob242 Hob253 Huar; lia|]. split.
+ apply (range_addressable_of_block SEGS B LAWS ly4 S4 _ _ _ (fr_img f) N _ _ (proj1 HJ4) Himg4); rewrite ?Hrq; clear - HWH Hob241 Hob242 Hob253 Huar; lia.
+ intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly4 S4 _ _ _ (fr_img f) N _ _ (proj1 HJ4) Himg4); rewrite ?Hrq; clear - HWH Hob241 Hob242 Hob253 Huar; lia. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff & Hfr5 & Hpres5).
assert (HdCI : fr_ptr f + 40 <= fr_img f \/ fr_img f + req_size N <= fr_ptr f).
{ destruct (frame_blocks_front g s N rest i f Hf) as (rci & HPci).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR (Permutation_trans HPerm HPci)) as Hd.
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd. change (req_size FRAME_SIZE) with 40 in Hd. exact Hd. }
assert (XG5 : garr8 SEGS (mrestrict (w_H W4) mem5) res (YO07.f_img cur)).
{ lazymatch type of Heff with forall i, _ -> _ = aview _ _ ?m1 _ =>
apply (garr8_aview SEGS (w_H W4) (w_H W4) m1 mem5 (fr_img f) res); [rewrite XClen; exact Heff|] end.
eapply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fr_img f) N (fr_img f) (YO07.f_img cur) HJ4);
[ exact Himg_in | exact Himg4 | clear; lia | rewrite XClen, Hrq; clear; lia
| intros a Ha (r & Hr0 & Hr); cbn [In] in Hr0; destruct Hr0 as [<- | []]; cbn [fst snd] in Hr; rewrite XClen in Ha; rewrite Hrq in HdCI; clear - Ha Hr HdCI; lia
| exact XCimg ]. }
clear HdCI. xnew_facts F (fr_ptr f) res N Hnh_ia Hnh_img Hrq Hn4096 Hnceil HdPF HdPC HWH XBBr.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp HipresT.
aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5.
reseat HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply region_kept_aview; [rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E12; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia
| intros a Ha; apply Hfr5; [clear - Ha Hbh1 Hbh2 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia | clear - Ha HdPB Hrq Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hbceil Hceil Hslo Hsp1 FFS C1 Hob241 Hob242 Hob253 Huar; unfold ESTACK; lia]
| exact Hpres5] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply region_kept_aview; [first [evalE AG | match goal with |- ?g => idtac "K88-base" g end; fail]
| intros a Ha; apply Hfr5; [first [clear - Ha HF8lo HF8hi Hob241 Hob242 Hob253 Huar; unfold SB in *; lia | match goal with |- ?g => idtac "K88-r64" g end; fail]
| first [clear - Ha Hnh Hnh_ia Hrq HF8lo HF8c HFceil C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold SB in *; zone_lia | match goal with |- ?g => idtac "K88-ndest" g end; fail]
| first [clear - Ha HF8c HFceil Hceil Hslo Hsp1 FFS C1 Hob241 Hob242 Hob253 Huar; unfold SB, ESTACK in *; lia | match goal with |- ?g => idtac "K88-nscr" g end; fail]]
| first [exact Hpres5 | match goal with |- ?g => idtac "K88-pres" g end; fail]] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr5; [clear - Ha HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia | clear - Ha HdPF Hrq Hob241 Hob242 Hob253 Huar; lia | clear - Ha HFceil Hceil Hslo Hsp1 FFS C1 Hob241 Hob242 Hob253 Huar; unfold ESTACK; lia]
| exact Hpres5] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr5; [clear - Ha Hsp1 Hshi H47 Hslo Hstk0 Hceil C1 FFS Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hnceil Hceil Hslo Hsp1 FFS C1 Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hob241 Hob242 Hob253 Huar; unfold ESTACK; lia]
| exact Hpres5] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr5; [clear - Ha Hslo Hstk0 Hshi H47 Hceil C1 FFS Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hnceil Hceil Hslo FFS C1 Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hsp1 Hob241 Hob242 Hob253 Huar; unfold ESTACK; lia]
| exact Hpres5] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgot4 | exact Kgot5 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kcell4 | exact Kcell5 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kguar4 | exact Kguar5 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 59%nat) _ _ _ _ _) =>
let AGx := lazymatch goal with A : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => A end in
let Bv := rnB in apply (region_kept_val_at Ex _ _ 59%nat (as_uar_cell Bv) 4 1); [evalE AGx | exact Kuar4 | exact Kuar5 | lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr5; [clear - Ha Hg4096 Hgceil C1 Hob241 Hob242 Hob253 Huar; lia | clear - Ha HdPG Hrq Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hgceil Hceil Hslo Hsp1 FFS C1 Hob241 Hob242 Hob253 Huar; unfold ESTACK; lia]
| exact Hpres5] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr5; [clear - Ha Hc4096 Hcceil C1 Hob241 Hob242 Hob253 Huar; lia | clear - Ha HdPC Hrq Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hcceil Hceil Hslo Hsp1 FFS C1 Hob241 Hob242 Hob253 Huar; unfold ESTACK; lia]
| exact Hpres5] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ5 SHOK FLBspan 0x2160.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
lazymatch goal with HFr : frame_of _ _ _ _ |- SRr _ _ (mkCfg ?msn _) _ => xblk_move HFr XG5 msn end.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
prreg HS (@BV 5 23 I) Q23;
ra_join HS ss_T3 801%nat fl_T3_deads_bv ltac:(idtac; ra_join_val HS 801%nat 0%nat Q23 E761;
ra_join_fact HS 801%nat (HPTR 4) ltac:(rewrite E761; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite Rres; unfold w64; rewrite unsigned_lit_small by (clear - Hnh Hnceil HWH C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia); unfold HPTR; cbn [af_lo af_hi af_al2]; change (2 ^ 4) with 16;
clear - Hnh Hnceil Hn16 HWH C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia));
fl_handX RT3 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
split; [| split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X | split; [exact XF1 |
exists tv; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E741 | split; [exact Rtv | exact Xtv]]]]].
exists res, w, h, top, left. cbn [c_s c_ly c_S c_regs c_f].
split; [rewrite E761; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite Rres; reflexivity|]. rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia).
split; [exact E683|]. split; [exact E684|]. split; [exact E681|]. split; [exact E685|].
split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
split; [clear - Hk0 Hob241 Hob242 Hob253 Huar; lia|].
assert (ENwh : w * h = N) by (rewrite Ew, Eh; symmetry; exact HN).
split.
{ rewrite Ew, Eh. replace (cg_W s * cg_H s) with N by (exact HN).
unfold fl_tmpblkX, fl_FP0. cbn [c_ly c_S c_regs c_f c_s].
split; [split; [exact Hnh | rewrite <- Hrq; exact (zone2_of_app _ _ Hnh_ia Hnh_img)]|]. split; [clear - Hnceil C1 Hob241 Hob242 Hob253 Huar; lia|]. split; [exact Hn16|].
split; [first [rewrite Eab4, Eab3; reflexivity | match goal with |- ?g => idtac "T2-ABL" g end]|].
split; [exact Ares | exact Tres]. }
split; [exact XD|]. split; [rewrite (XI0 Hc); exact XG5|]. split; [exact XLEN|].
rewrite ENwh. unfold xmacc in XMLE. rewrite Hc in XMLE. cbn [Z.eqb] in XMLE.
exact (mle_station MT S S3 S4 0 _ MLAW XMLE MLE4).
Qed.
Lemma fl_T2X : fl_fromX0 KS MT XN B CTX wfn ss_T3 (INV_T3X MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_T1x (INV_T1xX MT B).
Proof. exact fl_T2X_aux. Qed.
End m.
End l.
End d.
