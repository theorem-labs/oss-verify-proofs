(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20 YI1k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCgl YCfu YCft YCrb YCez YCev YCf6 YCf2 YCf7 YCet YCf3 YCey YCf5 YCew YCf0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma denot_add_lit0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0.
rewrite Z.add_0_r. apply zcanon_id. pose proof (U_range E e). rewrite M64_val in *. lia.
Qed.
Lemma denot_mul_hw : forall E nh nw h w, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w ->
0 <= h < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> sv_denot E (SMd M_MUL (SOff nh 0) (SOff nw 0)) = Z_to_bv 64 (h * w).
Proof.
intros E nh nw h w Hh Hw Rh Rw. assert (0 <= h * w) by (apply Z.mul_nonneg_nonneg; lia).
assert (h * w <= (2 ^ 32 - 1) * (2 ^ 32 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E nh h Hh) by lia. rewrite (U_atom E nw w Hw) by lia.
apply zcanon_id. rewrite M64_val. lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Lemma fl_T2_aux : fl_from B ss_X (INV_X B) -> fl_from B ss_T3 (INV_T3 B) -> fl_from B ss_T1x (INV_T0 B).
Proof.
intros RX RT3. fl_prelude.
pose proof HINV as ((gen & E180 & Rgen) & E184 & (fb & Hfb & EB) & (pt & w & h & top & left & E241 & E242 & E243 & E240 & E244 & Hrpt & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & Hpt)).
cbn [c_i c_s] in Hfb. pose proof Hpt as Hpt0. unfold fl_tmpblk, fl_FP in Hpt. cbn [c_ly c_S c_regs c_f c_s] in Hpt.
pose proof (EB 0%nat _ eq_refl) as E210. pose proof (EB 1%nat _ eq_refl) as E211. pose proof (EB 2%nat _ eq_refl) as E212.
pose proof (EB 3%nat _ eq_refl) as E213. pose proof (EB 4%nat _ eq_refl) as E214. pose proof (EB 5%nat _ eq_refl) as E215.
pose proof (EB 6%nat _ eq_refl) as E216. pose proof (EB 7%nat _ eq_refl) as E217. pose proof (EB 8%nat _ eq_refl) as E218.
cbn [Nat.add] in E210, E211, E212, E213, E214, E215, E216, E217, E218.
rewrite Hfb in E12. cbn [frame_ptr] in E12.
assert (Hwh0 : 0 <= w * h) by (apply Z.mul_nonneg_nonneg; clear - Hw1 Hh1; lia).
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & _ & _). change (req_size FRAME_SIZE) with 40 in Hbceil, Hbh2.
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)).
{ intros x Hx. destruct Hpt as [(_ & _ & _ & _ & Eab3) | (_ & _ & (_ & _ & _ & Eab3 & _))]; rewrite Eab3; [exact Hx | apply in_app_iff; left; exact Hx]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
assert (Himg3 : In (fr_img f, N) (ablocks B ly3 S3)) by (apply Hsub3; exact Himg_in).
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hbef_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
-
hc_bool Hc ltac:(fun H => hc_atom H 241%nat pt E241 ltac:(clear - Hrpt; lia)).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan 0x88470.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
rreg HS (@BV 5 24 I) Q23;
ra_join HS ss_T3 360%nat fl_T3_deads_bv ltac:(idtac; ra_join_val HS 360%nat 0%nat Q23 E320;
ra_join_fact HS 360%nat (HPTR 4) ltac:(rewrite E320; rewrite ?ew_havoc_old by (clear; lia); rewrite E241, unsigned_lit_small by (clear - Hrpt; lia); unfold HPTR; cbn [af_lo af_hi af_al2]; change (2 ^ 4) with 16;
destruct Hpt as [(Hp0 & _) | (_ & _ & (Hq1 & Hq2 & Hq16 & _))]; [exfalso; clear - Hp0 Hc; hc_prop Hc; exact (Hc Hp0)|]; clear - Hq1 Hq2 Hq16 Hwh0; ceil; lia));
fl_hand RT3 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists pt, w, h, top, left. cbn [c_s c_ly c_S c_regs c_f].
split; [rewrite E320; rewrite ?ew_havoc_old by (clear; lia); exact E241|]. rewrite !ew_havoc_old by (clear; lia). split; [exact E242|]. split; [exact E243|]. split; [exact E240|]. split; [exact E244|].
split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
hc_prop Hc. destruct Hpt0 as [(Hp0 & _) | (_ & Hk2 & Htb)]; [exfalso; exact (Hc Hp0)|]. split; [exact Hk2 | exact Htb].
-
hc_bool Hc ltac:(fun H => hc_atom H 241%nat pt E241 ltac:(clear - Hrpt; lia)). hc_prop Hc.
destruct Hpt as [(_ & Ew & Eh & Hk0 & Eab3) | (Hp1 & _)]; [|exfalso; exact (Hp1 Hc)].
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan 0x533c8.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
clear_frames.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x8842c) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (HWH : 1 <= cg_H s * cg_W s <= 100000000) by (split; [clear - HW1 HH1; nia | rewrite Z.mul_comm, <- HN; exact HNle]).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 (cg_H s * cg_W s))
(eq_trans (denot_add_lit0 Ev _) (denot_mul_hw Ev 41 40 (cg_H s) (cg_W s) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E41) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40)
ltac:(clear - R8; lia) ltac:(clear - R7; lia))) Ra0 end.
replace (cg_H s * cg_W s) with N in Ra0 by (rewrite HN; apply Z.mul_comm). replace (cg_H s * cg_W s) with N in HWH by (rewrite HN; apply Z.mul_comm).
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview trbsegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Htop32; lia) ltac:(clear - Hsp1; lia))
| ] end.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3' & _).
assert (HEVc : vev S3 < VEV_MAX) by (rewrite HEV in Hev; clear - Hnev3 Hev Hk0; lia).
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340936 with (pc_wrap_malloc (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_malloc_at trbsegs B LAWS trb_segs_low errno_low ML AMALLOC W3 (ms_regs msX) (ms_mem msX) TFLUSH_STK (spZ regs) _ ly S W mem md [(1, fpos)]
ly3 S3 mdX k N (sp1 - spZ regs) (Z_to_bv 64 0x8842c) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ra0.
- unfold MALLOC_MAX. clear - HWH. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_FLUSH in Hlive. clear - Hlive HWH. lia.
- rewrite EspX. clear; lia.
- rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
- clear - Hsp1; lia.
- rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
- rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
- rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
- exact Rra.
- apply ret_ok_even. vm_compute. reflexivity.
- exact HEVc.
- apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
- replace (pc_malloc_ra0 (as_code B)) with 0x53668 by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (fl_trace_in 0x53668 0x8842c); [exact Hctx | exact EraX | right; right; split; reflexivity]. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hres by (clear; lia).
pose proof (proj1 HJ4) as HAR4.
clear HUP. assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W4) mem4 a = aview trbsegs (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (1, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4. change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
destruct Hres as [(Hres0 & Eab4 & HK) | (Hres4096 & Eab4 & HK)].
+
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hing3).
assert (Hcur4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hcur3).
assert (Hbef4 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hbef3).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trbsegs _); [exact HK | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear; lia); rewrite E12; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia
| exact Hbef3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; unfold SB; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trbsegs _); [exact HK | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trbsegs _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trbsegs _); [exact HK | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs B LAWS); [exact HK | exact HAR4 | exact Hcur4 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rewrite Hres0 in Ha04.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pin_reg' trbsegs Ev ssv msv (@BV 5 10 I) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha04; reflexivity) eq_refl) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS. reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK FLBspan 0x887a4.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
rreg HS (@BV 5 19 I) Q19;
ra_join HS ss_X 520%nat fl_X_deads_bv ltac:(idtac; ra_join_val HS 520%nat 0%nat Q19 E520); fl_hand RX HS end.
split; [rewrite HEV; clear - Hk0; lia|].
split; [exists 2; split; [exact E520 | clear; lia]|].
cbn [c_ly c_S]. rewrite Eab4, Eab3. apply Permutation_refl.
+
assert (Hrq : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0); [exfalso; clear - HWH e; lia | reflexivity]).
assert (Hres_in : In (res, N) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hing3).
assert (Hcur4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hcur3).
assert (Hbef4 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hbef3).
assert (Himg4 : In (fr_img f, N) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Himg3).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res N HAR4 Hres_in) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph. rewrite Hrq in Hpceil, Hppres.
pose proof (blk_off_img _ _ _ _ _ _ res N HAR4 Hres_in) as Hph_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N HAR4 Himg4) as (_ & _ & _ & _ & Hipres4 & _). rewrite Hrq in Hipres4.
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res N HJ3 HAR4 Eab4 ltac:(clear - HWH; lia)) as Tres.
assert (Ares : forall blc lyq ownq i, In (res, N) blc -> 0 <= i < N ->
awr_byte TFLUSH_STK (spZ regs) [(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s + 40, cg_raw s + 44)] (ablocks B ly S) blc lyq ownq (res + i)).
{ intros blc lyq ownq ii Hbl Hiq. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res N blc ii lyq ownq HJ3 HAR4 Eab4 ltac:(clear - HWH; lia) Hbl ltac:(rewrite Hrq; exact Hiq)). }
assert (HPerm4 : Permutation (ablocks B ly4 S4) (ablocks B ly S ++ [(res, N)])) by (rewrite Eab4, Eab3; apply Permutation_refl).
pose proof (sep_block_frame trbsegs B LAWS ly4 S4 _ _ _ res N 1 fpos HAR4 Hres_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Hrq in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res N g CGIF_SIZE HAR4 HPerm4 Hing) as HdPG. change (req_size CGIF_SIZE) with 96 in HdPG. rewrite Hrq in HdPG.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res N (fr_ptr f) FRAME_SIZE HAR4 HPerm4 Hcur_in) as HdPC. change (req_size FRAME_SIZE) with 40 in HdPC. rewrite Hrq in HdPC.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res N (fr_ptr fb) FRAME_SIZE HAR4 HPerm4 Hbef_in) as HdPB. change (req_size FRAME_SIZE) with 40 in HdPB. rewrite Hrq in HdPB.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res N (fr_img f) N HAR4 HPerm4 Himg_in) as HdPI. rewrite Hrq in HdPI.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trbsegs _); [exact HK | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear; lia); rewrite E12; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia
| exact Hbef3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPB Hrq; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; unfold SB; clear; lia
| intros a Ha Hn; clear - Ha Hn Hph Hph_ia Hrq HF8lo HF8c HFceil C1 C3; ceil; unfold SB in *; zone_lia
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear; lia
| intros a Ha Hn; clear - Ha Hn HdPF Hrq; lia
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trbsegs _); [exact HK | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trbsegs _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trbsegs _); [exact HK | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPG Hrq; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs B LAWS); [exact HK | exact HAR4 | exact Hcur4 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPC Hrq; lia ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (@BV 5 10 I) Rres. rewrite Ha04 in Rres. symmetry in Rres.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (HPTR 4) HS
ltac:(clear HS; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rres; unfold w64; rewrite unsigned_lit_small by (clear - Hph Hpceil HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia);
change (2 ^ 4) with 16; clear - Hph Hpceil Hp16 HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK FLBspan 0x52074.
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
[ cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
clear_frames.
rreg HS (@BV 5 10 I) Ra0. rreg HS (@BV 5 11 I) Ra1. rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 12 I) (Z_to_bv 64 (cg_H s * cg_W s))
(eq_trans (denot_add_lit0 Ev _) (denot_mul_hw Ev 41 40 (cg_H s) (cg_W s) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E41) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40)
ltac:(clear - R8; lia) ltac:(clear - R7; lia))) Ra2 end.
replace (cg_H s * cg_W s) with N in Ra2 by (rewrite HN; apply Z.mul_comm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N (proj1 HJ4) Himg4) as (_ & _ & _ & _ & HipresT & _). rewrite Hrq in HipresT.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
clear Kgot4 Kcell4 Kguar4 Kuar4. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W4 (ms_regs msX) (ms_mem msX) TFLUSH_STK (spZ regs) _ ly S W mem md [(1, fpos)]
ly4 S4 _ (k + 1) res (fr_img f) N (sp1 - spZ regs) (Z_to_bv 64 0x88460) HJ4) end.
- rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Rres. reflexivity.
- rewrite Ra1, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite E51. reflexivity.
- exact Ra2.
- clear - HWH; lia. - clear - Hp4096; lia. - clear - Hpceil C1; lia.
- unfold spZ at 1. rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite E70, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia). clear; lia.
- rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
- clear - Hsp1; lia.
- rewrite FFS. unfold ESTACK. clear - Hsp1; lia.
- rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 3%nat) by (clear; lia). rewrite (EE 3%nat (@BV 5 3 I) eq_refl). exact Hgp.
- rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 4%nat) by (clear; lia). rewrite (EE 4%nat (@BV 5 4 I) eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even. vm_compute. reflexivity.
- intros a Ha. split; [replace a with (res + (a - res)) by (clear; lia); apply Ares; [exact Hres_in | clear - Ha; lia] | unfold ESTACK; clear - Ha Hpceil Hceil Hslo Hsp1 FFS C1; lia].
- apply (amem_range_of_block trbsegs B LAWS ly4 S4 _ _ _ res N _ _ HAR4 Hres_in); rewrite ?Hrq; clear - HWH; lia.
- apply (range_addressable_of_block trbsegs B LAWS ly4 S4 _ _ _ res N _ _ (proj1 HJ4) Hres_in); rewrite ?Hrq; clear - HWH; lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly4 S4 _ _ _ res N _ _ (proj1 HJ4) Hres_in); rewrite ?Hrq; clear - HWH; lia.
- split; [clear - Hi4096; lia|]. split; [clear - Hiceil Hrq C1; lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (proj1 (HipresT a ltac:(clear - Ha; lia)))|].
unfold spZ. rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite E70, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia).
unfold ESTACK. clear - Ha Hiceil Hrq Hceil Hslo Hsp1 FFS C1; lia. }
split; [clear - HdPI; lia|].
split; [apply (amem_range_of_block trbsegs B LAWS ly4 S4 _ _ _ (fr_img f) N _ _ HAR4 Himg4); rewrite ?Hrq; clear - HWH; lia|]. split.
+ apply (range_addressable_of_block trbsegs B LAWS ly4 S4 _ _ _ (fr_img f) N _ _ (proj1 HJ4) Himg4); rewrite ?Hrq; clear - HWH; lia.
+ intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly4 S4 _ _ _ (fr_img f) N _ _ (proj1 HJ4) Himg4); rewrite ?Hrq; clear - HWH; lia. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff & Hfr5 & Hpres5).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp HipresT.
aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5.
reseat HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply region_kept_aview; [rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear; lia); rewrite E12; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia
| intros a Ha; apply Hfr5; [clear - Ha Hbh1 Hbh2 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia | clear - Ha HdPB Hrq; lia | clear - Ha Hbceil Hceil Hslo Hsp1 FFS C1; unfold ESTACK; lia]
| exact Hpres5] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply region_kept_aview; [first [evalE AG | match goal with |- ?g => idtac "K88-base" g end; fail]
| intros a Ha; apply Hfr5; [first [clear - Ha HF8lo HF8hi; unfold SB in *; lia | match goal with |- ?g => idtac "K88-r64" g end; fail]
| first [clear - Ha Hph Hph_ia Hrq HF8lo HF8c HFceil C1 C3; ceil; unfold SB in *; zone_lia | match goal with |- ?g => idtac "K88-ndest" g end; fail]
| first [clear - Ha HF8c HFceil Hceil Hslo Hsp1 FFS C1; unfold SB, ESTACK in *; lia | match goal with |- ?g => idtac "K88-nscr" g end; fail]]
| first [exact Hpres5 | match goal with |- ?g => idtac "K88-pres" g end; fail]] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr5; [clear - Ha HF4096 HFceil C1; lia | clear - Ha HdPF Hrq; lia | clear - Ha HFceil Hceil Hslo Hsp1 FFS C1; unfold ESTACK; lia]
| exact Hpres5] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr5; [clear - Ha Hsp1 Hshi H47 Hslo Hstk0 Hceil C1 FFS; lia | clear - Ha Hpceil Hceil Hslo Hsp1 FFS C1; lia | clear - Ha; unfold ESTACK; lia]
| exact Hpres5] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr5; [clear - Ha Hslo Hstk0 Hshi H47 Hceil C1 FFS; lia | clear - Ha Hpceil Hceil Hslo FFS C1; lia | clear - Ha Hsp1; unfold ESTACK; lia]
| exact Hpres5] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot4 | exact Kgot5 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell4 | exact Kcell5 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar4 | exact Kguar5 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar4 | exact Kuar5 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr5; [clear - Ha Hg4096 Hgceil C1; lia | clear - Ha HdPG Hrq; lia | clear - Ha Hgceil Hceil Hslo Hsp1 FFS C1; unfold ESTACK; lia]
| exact Hpres5] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr5; [clear - Ha Hc4096 Hcceil C1; lia | clear - Ha HdPC Hrq; lia | clear - Ha Hcceil Hceil Hslo Hsp1 FFS C1; unfold ESTACK; lia]
| exact Hpres5] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK FLBspan 0x88470.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
rreg HS (@BV 5 24 I) Q23;
ra_join HS ss_T3 360%nat fl_T3_deads_bv ltac:(idtac; ra_join_val HS 360%nat 0%nat Q23 E320;
ra_join_fact HS 360%nat (HPTR 4) ltac:(rewrite E320; rewrite ?ew_havoc_old by (clear; lia); rewrite Rres; unfold w64; rewrite unsigned_lit_small by (clear - Hph Hpceil HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia); unfold HPTR; cbn [af_lo af_hi af_al2]; change (2 ^ 4) with 16;
clear - Hph Hpceil Hp16 HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia));
fl_hand RT3 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists res, w, h, top, left. cbn [c_s c_ly c_S c_regs c_f].
split; [rewrite E320; rewrite ?ew_havoc_old by (clear; lia); rewrite Rres; reflexivity|]. rewrite !ew_havoc_old by (clear; lia).
split; [exact E242|]. split; [exact E243|]. split; [exact E240|]. split; [exact E244|].
split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
split; [clear - Hk0; lia|].
rewrite Ew, Eh. replace (cg_W s * cg_H s) with N by (exact HN).
unfold fl_tmpblk, fl_FP. cbn [c_ly c_S c_regs c_f c_s].
split; [split; [exact Hph | rewrite <- Hrq; exact (zone2_of_app _ _ Hph_ia Hph_img)]|]. split; [clear - Hpceil C1; lia|]. split; [exact Hp16|].
split; [first [rewrite Eab4, Eab3; reflexivity | match goal with |- ?g => idtac "T2-ABL" g end]|].
split; [exact Ares | exact Tres].
Qed.
Lemma fl_T2 : fl_from B ss_X (INV_X B) -> fl_from B ss_T3 (INV_T3 B) -> fl_from B ss_T1x (INV_T0 B).
Proof. exact fl_T2_aux. Qed.
End d.
End c.
