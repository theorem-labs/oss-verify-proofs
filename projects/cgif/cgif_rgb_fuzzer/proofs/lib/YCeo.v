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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCgl YCfu YCft YCfx YCex YCrb YCez YCev YCf6 YCf2 YCf7 YCet YCf3 YCey YCf5 YCf0 YCe5 YCf8 YCf9.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
Fixpoint trim_base (rs : smem) (n : nat) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YQ0b.r_base r with
| Some b => if Nat.eqb b n then trim_region r lo hi :: t else r :: trim_base t n lo hi
| None => r :: trim_base t n lo hi end end.
Lemma extent_disjoint_sym : forall E a b, extent_disjoint E a b -> extent_disjoint E b a.
Proof. intros E a b [H|H]; [right | left]; exact H. Qed.
Lemma all_disjoint_app : forall E r l1 l2, all_disjoint E r (l1 ++ l2) <-> all_disjoint E r l1 /\ all_disjoint E r l2.
Proof.
intros E r l1 l2. induction l1 as [|x l1 IH]; cbn; [tauto|]. rewrite IH. tauto.
Qed.
Lemma pairwise_disjoint_remove : forall E l1 x l2, pairwise_disjoint E (l1 ++ x :: l2) -> pairwise_disjoint E (l1 ++ l2) /\ all_disjoint E x l2 /\ (forall y, In y l1 -> extent_disjoint E y x).
Proof.
intros E l1 x l2. induction l1 as [|y l1 IH]; cbn; intros H.
- destruct H as [Hx Hp]. repeat split; try assumption. intros z [].
- destruct H as [Hy Hp]. apply all_disjoint_app in Hy as [Hy1 [Hyx Hy2]]. destruct (IH Hp) as (P1 & P2 & P3).
split; [split; [apply all_disjoint_app; split; assumption | exact P1]|]. split; [exact P2|].
intros z [<- | Hz]; [exact Hyx | exact (P3 z Hz)].
Qed.
Lemma pairwise_disjoint_insert : forall E l1 x l2, pairwise_disjoint E (l1 ++ l2) -> all_disjoint E x (l1 ++ l2) -> pairwise_disjoint E (l1 ++ x :: l2).
Proof.
intros E l1 x l2. induction l1 as [|y l1 IH]; cbn; intros Hp Hx.
- split; [exact Hx | exact Hp].
- destruct Hp as [Hy Hp]. destruct Hx as [Hxy Hx]. apply all_disjoint_app in Hy as [Hy1 Hy2].
split; [apply all_disjoint_app; split; [exact Hy1 | cbn; split; [apply extent_disjoint_sym; exact Hxy | exact Hy2]] | exact (IH Hp Hx)].
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ast_ok_replace_region : forall E ss ms l1 r r' l2,
st_ok trbsegs E ss ms -> ss_mem ss = l1 ++ r :: l2 ->
regions_wf (l1 ++ r' :: l2) = true -> region_ok trbsegs E (ms_mem ms) r' -> all_disjoint E r' (l1 ++ l2) ->
st_ok trbsegs E (mkSS (ss_pc ss) (ss_regs ss) (l1 ++ r' :: l2) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms l1 r r' l2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hrs Hwf' Hr' Hd.
rewrite Hrs in Hok, Hpd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf'|]. split.
- apply Forall_app in Hok as [Ha Hb]. inversion Hb; subst. apply Forall_app. split; [exact Ha | constructor; assumption].
- destruct (pairwise_disjoint_remove E l1 r l2 Hpd) as (P1 & _ & _). exact (pairwise_disjoint_insert E l1 r' l2 P1 Hd).
Qed.
Lemma denot_mul_add : forall E nh nw na h w a, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w -> ew E na = Z_to_bv 64 a ->
0 <= h < 2 ^ 16 -> 0 <= w < 2 ^ 16 -> 0 <= a < 2 ^ 16 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff nh 0) (SOff nw 0)) (SOff na 0)) = Z_to_bv 64 (h * w + a).
Proof.
intros E nh nw na h w a Hh Hw Ha Rh Rw Ra. assert (0 <= h * w) by (apply Z.mul_nonneg_nonneg; lia).
assert (h * w <= (2 ^ 16 - 1) * (2 ^ 16 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E nh h Hh), (U_atom E nw w Hw), (U_atom E na a Ha) by lia.
rewrite (zcanon_id (h * w)) by (rewrite M64_val; lia). apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma denot_and_ffff : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 16 -> sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 65535)) = Z_to_bv 64 x.
Proof.
intros E n x Hn Rx. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
change (zcanon 65535) with (Z.ones 16). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_and_ffff : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 16 -> U E (SAlu ALU_AND (SOff n 0) (SLit 65535)) = x.
Proof.
intros E n x Hn Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
change (zcanon 65535) with (Z.ones 16). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma denot_mul_and_add : forall E nh nw na h w a, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w -> ew E na = Z_to_bv 64 a ->
0 <= h < 2 ^ 16 -> 0 <= w < 2 ^ 16 -> 0 <= a < 2 ^ 16 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff nh 0) (SLit 65535)) (SOff nw 0)) (SAlu ALU_AND (SOff na 0) (SLit 65535))) = Z_to_bv 64 (h * w + a).
Proof.
intros E nh nw na h w a Hh Hw Ha Rh Rw Ra. assert (0 <= h * w) by (apply Z.mul_nonneg_nonneg; lia).
assert (h * w <= (2 ^ 16 - 1) * (2 ^ 16 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_and_ffff E nh h Hh Rh), (U_atom E nw w Hw), (U_and_ffff E na a Ha Ra) by lia.
rewrite (zcanon_id (h * w)) by (rewrite M64_val; lia). apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma denot_sll48 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 16 -> sv_denot E (SAlu ALU_SLL (SOff n 0) (SLit 48)) = Z_to_bv 64 (x * 2 ^ 48).
Proof.
intros E n x Hn Rx. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
rewrite (zcanon_id 48) by (rewrite M64_val; lia). change (Z.land 48 63) with 48.
rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. rewrite M64_val. change (2 ^ 48) with 281474976710656 in *. lia.
Qed.
Lemma region_kept_eq : forall E (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview trbsegs H2 m2 a = aview trbsegs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept trbsegs E (mrestrict H m) (mrestrict H2 m2) (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview trbsegs). apply Hav. exact Ha.
- intros _. apply (apresent_writable trbsegs). apply Hp. exact Ha.
Qed.
Lemma fl_gpal_block : forall (B : asyms) ly S g s N rest,
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) -> Z.land (cg_attr s) 4 = 0 -> In (cg_pal s, 3 * cg_ngp s) (ablocks B ly S).
Proof.
intros B ly S g s N rest HP Ha. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left.
unfold cgif_blocks. right. right. apply in_app_iff. left. unfold pal_blocks. rewrite (proj2 (Z.eqb_eq _ _) Ha). left. reflexivity.
Qed.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis TCMP : tcmp_spec B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Ltac upd_aboveF HUP HFr AG ltac :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; ltac Hb Hrg|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Lemma fl_T3_aux : fl_from B ss_R (INV_R B) -> fl_from B ss_T3 (INV_T3 B).
Proof.
intros RR. fl_prelude.
pose proof HINV as ((gen & E180 & Rgen) & E184 & (fb & Hfb & EB) & (pt & w & h & top & left & E360 & E242 & E243 & E240 & E244 & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & Hk2 & Htb)).
cbn [c_i c_s] in Hfb. pose proof Htb as Htb0. unfold fl_tmpblk, fl_FP in Htb. cbn [c_ly c_S c_regs c_f c_s] in Htb.
destruct Htb as (Hph & Hpce & Hp16 & Eab3 & Ares & Tres).
pose proof (EB 0%nat _ eq_refl) as E210. pose proof (EB 1%nat _ eq_refl) as E211. pose proof (EB 2%nat _ eq_refl) as E212.
pose proof (EB 3%nat _ eq_refl) as E213. pose proof (EB 4%nat _ eq_refl) as E214. pose proof (EB 5%nat _ eq_refl) as E215.
pose proof (EB 6%nat _ eq_refl) as E216. pose proof (EB 7%nat _ eq_refl) as E217. pose proof (EB 8%nat _ eq_refl) as E218.
cbn [Nat.add] in E210, E211, E212, E213, E214, E215, E216, E217, E218.
rewrite Hfb in E12. cbn [frame_ptr] in E12.
assert (E300 : ew E 300 = Z_to_bv 64 (bv_unsigned (ew E 300))) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (Hwh0 : 1 <= w * h) by (clear - Hw1 Hh1; nia).
assert (Hwh : w * h <= N) by (rewrite HN; apply Z.mul_le_mono_nonneg; clear - Hw1 Hh1 Hlw Hl0 Hth Ht0; lia).
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & _ & _). change (req_size FRAME_SIZE) with 40 in Hbceil, Hbh2.
destruct (al_blocks _ _ LAWS ly S W mem md (fr_img fb) N HAR Hbimg_in) as (Hbi16 & Hbi4096 & Hbiceil & Hbih_ia & _ & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hbimg_in) as Hbih_img.
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)) by (intros x Hx; rewrite Eab3; apply in_app_iff; left; exact Hx).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
assert (Himg3 : In (fr_img f, N) (ablocks B ly3 S3)) by (apply Hsub3; exact Himg_in).
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hbef_in).
assert (Hbimg3 : In (fr_img fb, N) (ablocks B ly3 S3)) by (apply Hsub3; exact Hbimg_in).
assert (Hpt3 : In (pt, w * h) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n.
lazymatch type of HS with st_ok _ ?Ev _ _ => assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by (clear; lia); exact E12) end.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan 0x884fc.
all: try (oblG HJ3 E12n E32n Hbef3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia). clear_frames.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0.
rreg HS (@BV 5 29 I) Rr29. rreg HS (@BV 5 9 I) Rr9. rreg HS (@BV 5 15 I) Rr15. rreg HS (@BV 5 16 I) Rr16. rreg HS (@BV 5 17 I) Rr17.
rreg HS (@BV 5 18 I) Rr18. rreg HS (@BV 5 19 I) Rr19. rreg HS (@BV 5 21 I) Rr21. rreg HS (@BV 5 23 I) Rr23.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (F240 : ew Ev 240 = Z_to_bv 64 top) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E240);
assert (F242 : ew Ev 242 = Z_to_bv 64 w) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E242);
assert (F243 : ew Ev 243 = Z_to_bv 64 h) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E243);
assert (F244 : ew Ev 244 = Z_to_bv 64 left) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E244);
assert (F40 : ew Ev 40 = Z_to_bv 64 (cg_W s)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40);
assert (F360 : ew Ev 360 = Z_to_bv 64 pt) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E360);
assert (F211 : ew Ev 211 = Z_to_bv 64 (fr_img fb)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E211);
rreg_by HS (@BV 5 22 I) (Z_to_bv 64 (top * cg_W s + left)) (denot_mul_and_add Ev 240 40 244 top (cg_W s) left F240 F40 F244 ltac:(clear - Ht0 Hth Hh1 R8; lia) ltac:(clear - R7; lia) ltac:(clear - Hl0 Hlw Hw1 R7; lia)) Rr22 end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
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
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 70%nat in let il := eval vm_compute in il in
let rl := eval vm_compute in (nth il rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) il rl HS ltac:(vm_compute; reflexivity)) as HRloc; cbn [ms_mem restrict] in HRloc;
lazymatch type of HRloc with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v dtac rtac Hn :=
pose proof (field_of_region Ex _ 70 sp1 cs lo hi wlo whi off 8%N e v HRloc
ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia)
ltac:(cbn; tauto) ltac:(dtac) ltac:(rtac) ltac:(cbn; lia)) as Hn in
slot 184 (SOff 300 0) (bv_unsigned (ew Ex 300)) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (ew Ex 300)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) V184t;
slot 216 (SOff 32 0) SB ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E32n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(unfold SB; cbn; lia) V216;
slot 192 (SOff 12 0) (fr_ptr fb) ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E12n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hbh1 Hbh2 C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V192;
slot 200 (SOff 10 0) g ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E10n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hgh Hgceil C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V200;
slot 208 (SOff 11 0) (fr_ptr f) ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E11n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hcrh Hcceil C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V208;
slot 240 (SOff 75 0) F ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1; lia) V240;
slot 136 (SAlu ALU_SLL (SOff 242 0) (SLit 48)) (w * 2 ^ 48) ltac:(apply (denot_sll48 Ex 242 w F242); clear - Hw1 Hlw Hl0 R7; lia) ltac:(cbn [Z.of_N Z.mul]; change (2 ^ 48) with 281474976710656; clear - Hw1 Hlw Hl0 R7; lia) V136;
slot 144 (SOff 243 0) h ltac:(cbn [sv_denot]; rewrite F243, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hh1 Hth Ht0 R8; lia) V144;
slot 160 (SAlu ALU_AND (SOff 242 0) (SLit 65535)) w ltac:(apply (denot_and_ffff Ex 242 w F242); clear - Hw1 Hlw Hl0 R7; lia) ltac:(cbn [Z.of_N Z.mul]; clear - Hw1 Hlw Hl0 R7; lia) V160;
slot 168 (SLit 0) 0 ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear; lia) V168;
slot 176 (SOff 40 0) (cg_W s) ltac:(cbn [sv_denot]; rewrite F40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - R7; lia) V176 end;
clear HRloc end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V184t, V216, V192, V200, V208, V240, V136, V144, V160, V168, V176.
assert (HPerm3 : Permutation (ablocks B ly3 S3) (ablocks B ly S ++ [(pt, w * h)])) by (rewrite Eab3; apply Permutation_refl).
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt (w * h) g CGIF_SIZE HAR3 HPerm3 Hing) as HdPG. change (req_size CGIF_SIZE) with 96 in HdPG.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt (w * h) (fr_ptr f) FRAME_SIZE HAR3 HPerm3 Hcur_in) as HdPC. change (req_size FRAME_SIZE) with 40 in HdPC.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt (w * h) (fr_ptr fb) FRAME_SIZE HAR3 HPerm3 Hbef_in) as HdPB. change (req_size FRAME_SIZE) with 40 in HdPB.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt (w * h) (fr_img fb) N HAR3 HPerm3 Hbimg_in) as HdPI.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ pt (w * h) 1 fpos HAR3 Hpt3 Hfin3) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA3 in HdPF. fold F in HdPF.
pose proof (fl_bef_sep B LAWS ly S W mem md g s N rest i f fb HAR HPerm Hf Hfbe Hi) as HdCB.
assert (Hrq : req_size (w * h) = w * h) by (unfold req_size; destruct (Z.eqb_spec (w * h) 0); [exfalso; clear - Hwh0 e; lia | reflexivity]).
rewrite Hrq in HdPG, HdPC, HdPB, HdPI, HdPF.
pose proof (sep_blocks trbsegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE g CGIF_SIZE HAR Hraw_in Hing ltac:(unfold RAW_SIZE, CGIF_SIZE; intros X; injection X; lia)) as HdRG.
unfold zdisjoint in HdRG; cbn [fst snd] in HdRG; change (req_size RAW_SIZE) with 48 in HdRG; change (req_size CGIF_SIZE) with 96 in HdRG.
pose proof (sep_blocks trbsegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr fb) FRAME_SIZE HAR Hraw_in Hbef_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRB.
unfold zdisjoint in HdRB; cbn [fst snd] in HdRB; change (req_size RAW_SIZE) with 48 in HdRB; change (req_size FRAME_SIZE) with 40 in HdRB.
pose proof (sep_blocks trbsegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr f) FRAME_SIZE HAR Hraw_in Hcur_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRC.
unfold zdisjoint in HdRC; cbn [fst snd] in HdRC; change (req_size RAW_SIZE) with 48 in HdRC; change (req_size FRAME_SIZE) with 40 in HdRC.
assert (Og3 : obj_at trbsegs (mrestrict (w_H W3) (ms_mem ms)) g LAY_CGIF (tcgif_vals s)).
{ lazymatch goal with |- obj_at _ (mrestrict _ (ms_mem ?msX)) _ _ _ =>
eapply (aj_obj_kept B); [exact HJ3 | exact Hing | exact Hing3 | exact Og | vm_compute; reflexivity |] end.
change (req_size CGIF_SIZE) with 96. intros j Hj (rr & Hrr & Ha). cbn [In] in Hrr.
unbox. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Ha; [clear - Ha Hj HdGC; lia | clear - Ha Hj HdRG; lia]. }
assert (Ob3 : obj_at trbsegs (mrestrict (w_H W3) (ms_mem ms)) (fr_ptr fb) LAY_Frame (frame_vals fb)).
{ eapply (aj_obj_kept B); [exact HJ3 | exact Hbef_in | exact Hbef3 | exact (Ofr fb Hfbi) | vm_compute; reflexivity |].
change (req_size FRAME_SIZE) with 40. intros j Hj. apply fl_fp_out_frame; [clear - HdCB; lia | clear - HdRB; lia | exact Hj]. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE (proj1 HJ3) Hcur3) as (_ & _ & _ & _ & HcpresX & _). change (req_size FRAME_SIZE) with 40 in HcpresX.
destruct (obj_at_hole4 (mrestrict (w_H W) mem) (mrestrict (w_H W3) (ms_mem ms)) (fr_ptr f) LAY_Frame 40 (frame_vals f) 3 20
Oc ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
ltac:(intros j Hj Hnj; apply (mbyte_of_aview trbsegs); pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
apply (F2 (fr_ptr f) FRAME_SIZE j Hcur_in Hcur3 ltac:(change (req_size FRAME_SIZE) with 40; exact Hj));
intros (rr & Hrr & Ha); cbn [In] in Hrr; destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Ha; [clear - Ha Hj Hnj; lia | clear - Ha Hj HdRC; lia])
ltac:(intros j Hj; destruct (proj1 (HcpresX (fr_ptr f + 20 + j) ltac:(clear - Hj; lia))) as [Hh [b Hb]];
unfold mbyte, mrestrict; cbn [ms_mem]; rewrite Hh; cbn; rewrite Hb; eexists; reflexivity))
as (genC & HgenC & Oc3).
destruct (fl_bef_blocks B ly S g s N rest f HPerm Hfi) as (_ & _ & Hclpal).
pose proof (Hfwf f Hfi) as [Hfgp _]. pose proof (Hfwf fb Hfbi) as [Hbgp _].
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HCTX : tin_ctx B W3 (ms_regs msX) (ms_mem msX) mdX (spZ regs) sp1 [(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s + 40, cg_raw s + 44)] ly S W mem md ly3 S3 k fpos
((spZ regs, raZ regs, s0Z regs) :: ch) pt (w * h) (fr_img fb) N g (fr_ptr f) (fr_ptr fb) (bv_unsigned (ew E 300))
(tcgif_vals s) (list_set (frame_vals f) 3 genC) (frame_vals fb)
(cg_pal s) (cg_ngp s) (fr_lpal f) (fr_attr f) (fr_nlp f) (fr_ctidx f) (fr_lpal fb) (fr_attr fb) (fr_nlp fb) (fr_ctidx fb)) end.
{ split; [exact HJ3|]. split; [exact Hpt3|].
split; [intros blc lyq ownq a Hbl Ha; replace a with (pt + (a - pt)) by (clear; lia); apply (Ares blc lyq ownq (a - pt) Hbl); clear - Ha; lia|].
split; [exact Hbimg3|]. split; [clear - HNle; lia|]. split; [clear - HdPI Hrq; lia|].
split; [exact Hing3|]. split; [exact Hcur3|]. split; [exact Hbef3|]. split; [clear - HdCB; lia|].
split; [clear - HdPG Hrq; lia|]. split; [clear - HdPC Hrq; lia|]. split; [clear - HdPB Hrq; lia|].
split; [exact Og3|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Oc3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Ob3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros Ha1; exists (3 * fr_nlp f); split; [apply Hsub3; apply Hclpal; exact Ha1 | clear; lia]|].
split; [intros Ha1; exists (3 * fr_nlp fb); split; [apply Hsub3; apply Hblpal; exact Ha1 | clear; lia]|].
split; [intros Hor; exists (3 * cg_ngp s); split; [apply Hsub3; apply (fl_gpal_block B ly S g s N rest HPerm); destruct Hor as [H0 | H0]; [exact (Hfgp H0) | exact (Hbgp H0)] | clear; lia]|].
split; [exact EspX|]. split; [exact Hsp1|]. split; [exact Hsp1al16|].
split; [rewrite Rr9, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E70|].
split; [rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 3%nat) by (clear; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp|].
split; [rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 4%nat) by (clear; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp|].
split; [rewrite Es0X; exact Hch1|]. split; [exact Es0X|].
split; [exact V184t|]. split; [pose proof (bv_unsigned_in_range 64 (ew E 300)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq|].
split; [exact V216|]. split; [exact V192|]. split; [exact V200|]. split; [exact V208|].
split; [clear - Hwh HNle; lia|].
split; [rewrite Rr18, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E211|]. split; [exact Rr19|].
rewrite Rr21, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E360. }
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HOUT : tout_ctx W3 (ms_mem msX) sp1 w h top left (cg_W s) N) end.
{ split; [clear - Hw1 Hlw Hl0 R7; lia|]. split; [clear - Hh1 Hth Ht0 R8; lia|]. split; [exact Ht0|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [clear - R7; lia|].
split; [rewrite HN, (Z.mul_comm (cg_W s) (cg_H s)); apply Z.mul_le_mono_nonneg_r; clear - Hth R7; lia|].
split; [exact V136|]. split; [exact V144|]. split; [exact V160 | exact V176]. }
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ pose proof (fl_tout B LAWS TCMP (Z.to_nat h)) as TOUT. unfold tout_stmt in TOUT.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (TOUT 0 W3 (ms_regs msX) (ms_mem msX) mdX (spZ regs) sp1 _ ly S W mem md ly3 S3 k fpos _ pt w h top left (cg_W s) (fr_img fb) N g (fr_ptr f) (fr_ptr fb) (bv_unsigned (ew E 300))
(tcgif_vals s) (list_set (frame_vals f) 3 genC) (frame_vals fb) (cg_pal s) (cg_ngp s) (fr_lpal f) (fr_attr f) (fr_nlp f) (fr_ctidx f) (fr_lpal fb) (fr_attr fb) (fr_nlp fb) (fr_ctidx fb)) end;
[ rewrite Z2Nat.id by (clear - Hh1; lia); clear; lia | clear - Hh1; lia | exact HCTX | exact HOUT
| first [replace (0 * w) with 0 by (clear; lia); exact V168 | match goal with |- ?g => idtac "TO168" g end]
| first [rewrite Rr29, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E32n | match goal with |- ?g => idtac "TO29" g end]
| first [rewrite Rr15, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E10n | match goal with |- ?g => idtac "TO15" g end]
| first [rewrite Rr16, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E11n | match goal with |- ?g => idtac "TO16" g end]
| first [rewrite Rr17, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E12n | match goal with |- ?g => idtac "TO17" g end]
| first [exact Rr23 | rewrite Rr23; reflexivity | match goal with |- ?g => idtac "TO23" g end]
| first [rewrite Rr22; f_equal; clear; lia | match goal with |- ?g => idtac "TO22" g end] ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HK5 & H295 & H155 & H165 & H175 & K5 & X5).
clear Rra Rsp Rgp Rtp Rs0 Rr29 Rr9 Rr15 Rr16 Rr17 Rr18 Rr19 Rr21 Rr22 Rr23 Vra Vs0 V136 V144 V160 V168 HCTX HOUT.
pose proof (proj1 HJ5) as HAR5.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR5 Hfin3) as (_ & _ & HFpres5 & HFSpres5).
change (fs_frame_bytes 1) with 128 in HFpres5, HFSpres5. change (128 / 8) with 16 in HFSpres5. rewrite !EFA3 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5.
assert (HSpres5 : forall a, spZ regs - TFLUSH_STK <= a < spZ regs -> apresent (w_H W3) mem5 a) by (pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _); exact HSp).
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let rs' := eval vm_compute in (trim_base (ss_mem ssx) 70 0 168) in
pose proof (st_ok_submem trbsegs Ev ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch_keep HS kk regs5 (mrestrict (w_H W3) mem5) TOUT_CLOB 0x885fc [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2 end.
lazymatch type of HS2 with _ -> ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil
| specialize (HS2 HK5 HQ); clear HQ ] end.
all: try (idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact K5 | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; unfold SB; clear; lia
| intros a Ha Hn; clear - Ha Hn Hph HF8lo HF8c HFceil C1 C3; ceil; unfold SB in *; zone_lia
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact K5 | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear; lia
| intros a Ha Hn; clear - Ha Hn HdPF; lia
| intros a Ha; apply (proj1 (HFpres5 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply region_kept_eq; [evalE AG | intros a Ha; apply X5; clear - Ha; lia | intros a Ha; apply HSpres5; rewrite FFS; clear - Ha Hsp1; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trbsegs _); [exact K5 | exact HJ5 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot5 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell5 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar5 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar5 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trbsegs _); [exact K5 | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPG; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs B LAWS); [exact K5 | exact HAR5 | exact Hcur3 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPC; lia ] end
| match goal with |- region_kept _ _ _ _ ?r => idtac "KEPTFAIL" r end ]).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
assert (HUP5 : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W3) mem5 a = aview trbsegs (w_H W) mem a).
{ intros a Ha. pose proof K5 as (K51 & _). rewrite (K51 a) by (first [clear - Ha Hceil Hslo Hstk0 FFS C1; lia | clear - Ha Hsp1; lia]). apply HUP. exact Ha. }
clear HUP. rename HUP5 into HUP.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with ?r0 :: ?r1 :: ?rt :: ?l2 =>
lazymatch rt with YQ0b.mkRegion (Some 70%nat) 0 168 0 168 ?cst =>
pose proof (st_ok_region_nth Ev ssx msv 2 rt HS ltac:(vm_compute; reflexivity)) as HRt; cbn [ms_mem restrict mkst] in HRt;
unfold region_ok in HRt; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in HRt;
destruct HRt as (HRt1 & HRt2 & HRt3 & HRt4);
pose proof (ast_ok_replace_region Ev ssx msv [r0; r1] rt
(YQ0b.mkRegion (Some 70%nat) 0 248 0 248 (cst ++ [YQ0b.mkChunk 176 (CVal 8 (SOff 40 0)); YQ0b.mkChunk 184 (CVal 8 (SOff 300 0)); YQ0b.mkChunk 192 (CVal 8 (SOff 12 0));
YQ0b.mkChunk 200 (CVal 8 (SOff 10 0)); YQ0b.mkChunk 208 (CVal 8 (SOff 11 0)); YQ0b.mkChunk 216 (CVal 8 (SOff 32 0));
YQ0b.mkChunk 240 (CVal 8 (SOff 75 0))])) l2
HS eq_refl ltac:(vm_compute; reflexivity)
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks ms_mem restrict mkst];
lazymatch goal with |- context [base_val ?Ex (Some 70%nat)] =>
replace (base_val Ex (Some 70%nat)) with sp1 in HRt4 |- * by (cbn [base_val]; symmetry; evalE AG) end;
split; [clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia|]; split; [clear - Hsp1 Hshi H47; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply HSpres5; rewrite FFS; clear - Ho Hsp1; lia|];
apply Forall_app; split; [exact HRt4|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ sp1 176 8 _ (cg_W s));
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - R7; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47; lia | left; cbn [Z.of_nat]; clear; lia | exact V176] ]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ sp1 184 8 _ (bv_unsigned (ew E 300)));
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E300, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (bv_unsigned_in_range 64 (ew E 300)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47; lia | left; cbn [Z.of_nat]; clear; lia | exact V184t] ]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ sp1 192 8 _ (fr_ptr fb));
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear; lia); rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hbh1 Hbh2 C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47; lia | left; cbn [Z.of_nat]; clear; lia | exact V192] ]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ sp1 200 8 _ g);
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 10%nat) by (clear; lia); rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hgh Hgceil C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47; lia | left; cbn [Z.of_nat]; clear; lia | exact V200] ]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ sp1 208 8 _ (fr_ptr f));
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 11%nat) by (clear; lia); rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hcrh Hcceil C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47; lia | left; cbn [Z.of_nat]; clear; lia | exact V208] ]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ sp1 216 8 _ SB);
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 32%nat) by (clear; lia); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47; lia | left; cbn [Z.of_nat]; clear; lia | exact V216] ]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ sp1 240 8 _ F);
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - HF4096 HFceil C1; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47; lia | left; cbn [Z.of_nat]; clear; lia | exact V240] ]|];
apply Forall_nil)
ltac:(cbn [all_disjoint app]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
evalE AG; change (fs_frame_bytes 1) with 128; change (fs_frame_bytes 1 / 8) with 16;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, CGIF_SIZE, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C2 C3 HF4096 HFceil HFhigh HF8lo HF8hi HF8c Hgh Hgceil Hcrh Hcceil;
repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ-FAIL" g end])) as HS3;
clear HS; rename HS3 into HS end end end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv 29%bv (SOff 32 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite H295; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 32%nat) by (clear; lia); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv 15%bv (SOff 10 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite H155; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 10%nat) by (clear; lia); rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv 16%bv (SOff 11 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite H165; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 11%nat) by (clear; lia); rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv 17%bv (SOff 12 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite H175; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear; lia); rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS. clear_frames.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK FLBspan 0x8862c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia). clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
rreg HS (24%bv : bv 5) QXp; rreg HS (21%bv : bv 5) QXw; rreg HS (23%bv : bv 5) QXh; rreg HS (22%bv : bv 5) QXl; rreg HS (6%bv : bv 5) QXt;
add_atom HS 400%nat (sv_denot Ev (SOff 240 0)) E400;
ws_pin HS (6%bv : bv 5) (SOff 400 0) QXt ltac:(rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E400; rewrite ?sv_denot_SOff0, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
add_atom HS 401%nat (sv_denot Ev (SOff 300 0)) E401;
rechunk_off HS 70%nat 184 (SOff 401 0) ltac:(rewrite sv_denot_SOff0, E401; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join HS ss_R 402%nat fl_R_deads_bv ltac:(idtac;
ra_join_val HS 402%nat 0%nat QXp E402; ra_join_val HS 402%nat 1%nat QXw E403; ra_join_val HS 402%nat 2%nat QXh E404; ra_join_val HS 402%nat 3%nat QXl E405;
ra_join_fact HS 400%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E400; rewrite Z.pow_0_r, Z.mod_1_r; rewrite sv_denot_SOff0, E240, unsigned_lit_small by (clear - Ht0 Hth Hh1 R8; lia); clear - Ht0 Hth Hh1 R8; lia);
ra_join_fact HS 403%nat (mkAF 1 65535 0) ltac:(rewrite E403; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E242, unsigned_lit_small by (clear - Hw1 Hlw Hl0 R7; lia); clear - Hw1 Hlw Hl0 R7; lia);
ra_join_fact HS 404%nat (mkAF 1 65535 0) ltac:(rewrite E404; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E243, unsigned_lit_small by (clear - Hh1 Hth Ht0 R8; lia); clear - Hh1 Hth Ht0 R8; lia);
ra_join_fact HS 405%nat (mkAF 0 65535 0) ltac:(rewrite E405; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E244, unsigned_lit_small by (clear - Hl0 Hlw Hw1 R7; lia); clear - Hl0 Hlw Hw1 R7; lia));
fl_hand RR HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
exists pt, w, h, top, left, (bv_unsigned (ew E 300)). cbn [c_s c_ly c_S].
split; [rewrite E402; exact E360|].
split; [rewrite E403; exact E242|].
split; [rewrite E404; exact E243|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E400, sv_denot_SOff0; exact E240|].
split; [rewrite E405; exact E244|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E401, sv_denot_SOff0; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E300|].
split; [clear - Hph Hpce Hwh0; ceil; lia|].
split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
split; [pose proof (bv_unsigned_in_range 64 (ew E 300)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq|].
right. split; [clear - Hph; lia|]. split; [exact Hk2 | exact Htb0].
Qed.
Lemma fl_T3 : fl_from B ss_R (INV_R B) -> fl_from B ss_T3 (INV_T3 B).
Proof. exact fl_T3_aux. Qed.
End d.
End c.
