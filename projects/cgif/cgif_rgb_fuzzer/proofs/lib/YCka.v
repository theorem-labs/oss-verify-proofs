(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YCpm YCpo YCpq YClz YCqd YCqe YCpy YCq3 YCq4 YCq6 YCq5 YP14 YP15 YI0d YI0h YChh YCia YCm1 YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCop.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YCqg.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClc YCld YCkr YCks YCkt YCku YCkv YClv.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gP4 : forall n : nat, rga_fromA B ss_M2 (fun _ => INV_M2 B (S n)) -> rga_from B ss_M1 (INV_M1 B (S n)).
Proof.
intros n RM2. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & pc0 & js & HTRIP & (R480 & Hpix3) & Hjs & Huz & R521 & R522).
unfold g_trip in HTRIP. rga_cbn_cx HTRIP. rga_cbn_cx R480. rga_cbn_cx Hpix3.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav)).
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_M1 in HS.
change CHT_SIZE with 48 in *.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hrin]).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
pose proof Hwf as Hwf0. destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as ([_ R0v] & [_ R8v] & [_ R16v] & [_ R24v] & [_ R32v] & [_ R36v] & [_ R40v] & [_ R42v] & [_ R44v] & [_ R48v] & [_ R56v] & [_ R60v] & _).
cbn [fst snd N.to_nat Z.of_N] in R0v, R8v, R16v, R24v, R32v, R36v, R40v, R42v, R44v, R48v, R56v, R60v.
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (Hcnt0 & _) & _).
assert (HT24 : 524309 <= ht_T Ht <= 16777216) by (clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia).
assert (Hcnt64 : 0 <= ht_cnt Ht < 2 ^ 64) by (clear - Hcnt0 HT24; lia).
assert (Himg_in : In (img, fmt * N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. apply in_or_app. left.
unfold timg_block. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Himg_in3 : In (img, fmt * N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Himg_in]).
destruct (g_blk B LAWS ly3 S3 W3 (ms_mem ms3) md3 img _ HAR3 Himg_in3 ltac:(clear - HfN; lia)) as (Himg4096 & Himgceil & Himg16 & Himgpres).
assert (Bimg : 0 <= img < 2 ^ 64) by (clear - Himg4096 Himgceil HfN C1; lia).
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx (ht_T Ht)).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest; YI0g.perm_tac).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
assert (Hcht_l : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> In (b, sz) lrest)
by (intros b sz Hb; subst lrest; apply in_or_app; right; right; right; exact Hb).
assert (Himg_l : In (img, fmt * N) lrest).
{ subst lrest. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. unfold timg_block. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Hpxoff : forall kk, 0 <= kk < fmt -> 0 <= img + fmt * ix + kk < 2 ^ 64 /\ ~ (m_ZsP F r (img + fmt * ix + kk) \/ tb <= img + fmt * ix + kk < tb + 48)).
{ intros kk Hkk. apply (Hoff3 img (fmt * N) Himg_l). pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as [_ Hrq]. clear - Hkk Hfmt Hix Hrq. nia. }
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) (ms_mem ms3) a = aview trbsegs (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
idtac "OK-B".
assert (Hcht_in3 : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> In (b, sz) (ablocks B ly3 S3)).
{ intros b sz Hb. eapply Permutation_in; [apply Permutation_sym; exact HPm3|]. apply in_or_app. right. apply in_or_app. right. right. exact Hb. }
assert (Hfq_in3 : In (fq, 4 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Hhh_in3 : In (hh, 3 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Huu_in3 : In (uu, ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Hpp_in3 : In (pp, 3 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
assert (Hxx_in3 : In (xx, 4 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; cbn [cht_blocks In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ fq _ HAR3 Hfq_in3 ltac:(clear - HT24; lia)) as (Hfq4096 & Hfqceil & Hfq16 & Hfqpres).
destruct (g_blk B LAWS _ _ _ _ _ hh _ HAR3 Hhh_in3 ltac:(clear - HT24; lia)) as (Hhh4096 & Hhhceil & Hhh16 & Hhhpres).
destruct (g_blk B LAWS _ _ _ _ _ uu _ HAR3 Huu_in3 ltac:(clear - HT24; lia)) as (Huu4096 & Huuceil & Huu16 & Huupres).
destruct (g_blk B LAWS _ _ _ _ _ pp _ HAR3 Hpp_in3 ltac:(clear - HT24; lia)) as (Hpp4096 & Hppceil & Hpp16 & Hpppres).
destruct (g_blk B LAWS _ _ _ _ _ xx _ HAR3 Hxx_in3 ltac:(clear - HT24; lia)) as (Hxx4096 & Hxxceil & Hxx16 & Hxxpres).
assert (Bfq : 0 <= fq < 2 ^ 64) by (clear - Hfq4096 Hfqceil HT24 C1; lia).
assert (Bhh : 0 <= hh < 2 ^ 64) by (clear - Hhh4096 Hhhceil HT24 C1; lia).
assert (Buu : 0 <= uu < 2 ^ 64) by (clear - Huu4096 Huuceil HT24 C1; lia).
assert (Bpp : 0 <= pp < 2 ^ 64) by (clear - Hpp4096 Hppceil HT24 C1; lia).
assert (Bxx : 0 <= xx < 2 ^ 64) by (clear - Hxx4096 Hxxceil HT24 C1; lia).
assert (Bix : 0 <= ix < 2 ^ 64) by (clear - Hix HN; unfold RGB_NMAX in HN; lia).
assert (BT : 0 <= ht_T Ht < 2 ^ 64) by (clear - HT24; lia).
idtac "OK-BLK".
pose proof (inv_T_pos Ht ent Hinv) as HTpos.
set (hs := cyc (ht_T Ht) (hash0 (ht_T Ht) pc0) js) in *.
assert (Hhs : 0 <= hs < ht_T Ht) by (subst hs; apply cyc_range; exact HTpos).
set (uv := usedz Ht hs).
assert (Huv : uv = 0 \/ uv = 1) by (subst uv; exact (inv_used01 Ht ent Hinv hs Hhs)).
destruct Harr as (Af & Ak & Au & Ap & Ax).
assert (Vuv : mbyte trbsegs (mrestrict (w_H W3) (ms_mem ms3)) (uu + hs) = Some (Z_to_bv 8 uv)).
{ destruct (Au (Z.to_nat hs) ltac:(clear - Hhs L1; unfold zlen in L1; lia)) as [Vb _]. rewrite Z2Nat.id in Vb by (clear - Hhs; lia). exact Vb. }
idtac "OK-PRE".
assert (Hhs64 : 0 <= hs < 2 ^ 64) by (clear - Hhs HT24; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) HAR3 Hhh_in3) as (_ & Hhhzone & _ & _).
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq3T].
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as [_ HrqfN].
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) 7 fpos HAR3 Hhh_in3 Hfin3) as HdF_hh.
unfold zdisjoint in HdF_hh. cbn [fst snd] in HdF_hh. change (fs_frame_bytes 7) with 8192 in HdF_hh. rewrite EFA3 in HdF_hh. fold F in HdF_hh.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) cid pos HAR3 Hhh_in3 HfinS3) as HdC_hh.
unfold zdisjoint in HdC_hh. cbn [fst snd] in HdC_hh. rewrite EFA3 in HdC_hh.
assert (Hhh_l : In (hh, 3 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (hh, 3 * ht_T Ht) HAR3 HPrt3 ltac:(right; exact Hhh_l)) as HzR_hh.
unfold zdisjoint, block_rng in HzR_hh. cbn [fst snd] in HzR_hh. change (req_size RGB_SIZE) with 64 in HzR_hh.
assert (HPtb3 : Permutation (ablocks B ly3 S3) ((tb, 48) :: (r, RGB_SIZE) :: lrest)) by (eapply Permutation_trans; [exact HPrt3 | apply perm_swap]).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (hh, 3 * ht_T Ht) HAR3 HPtb3 ltac:(right; exact Hhh_l)) as HzT_hh.
unfold zdisjoint, block_rng in HzT_hh. cbn [fst snd] in HzT_hh. change (req_size 48) with 48 in HzT_hh.
assert (HzI_hh : hh + req_size (3 * ht_T Ht) <= img \/ img + req_size (fmt * N) <= hh).
{ assert (HPx : Permutation (ablocks B ly3 S3) (cht_blocks fq hh uu pp xx (ht_T Ht) ++ ((r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (hh, 3 * ht_T Ht) (img, fmt * N) HAR3 HPx ltac:(cbn [cht_blocks In]; tauto)
ltac:(right; right; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; unfold timg_block; destruct Hfmt as [-> | ->]; left; reflexivity)) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. exact Dd. }
assert (SEP5 : g_sep5 fq hh uu pp xx (ht_T Ht)).
{ apply (g_sep5_of_AR B LAWS ly3 S3 _ _ _ (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ [(tb, 48)]) fq hh uu pp xx (ht_T Ht) HAR3); [|exact HTpos].
eapply Permutation_trans; [exact HPm3|]. rewrite <- !app_assoc. reflexivity. }
idtac "OK-SEP".
assert (Bpx : 0 <= img + fmt * ix < 2 ^ 64) by (clear - Himg4096 Himgceil Hfmt Hix HfN C1; nia).
assert (Hpx : 0 <= fmt * ix /\ fmt * ix + fmt <= fmt * N) by (clear - Hfmt Hix; nia).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) (hh + hs * 3)
ltac:(apply (U_add_small_q _ _ _ hh (hs * 3) (U_atom _ 474 hh Rhh Bhh));
[ apply (g_U_mul_small _ (SOff 521 0) (SLit 3) hs 3 (U_atom _ 521 hs R521 Hhs64) ltac:(reflexivity)); clear - Hhs HT24; lia | clear - Bhh; lia | clear - Hhs; lia | clear - Hhhceil Hhs HT24 C1; lia ]) Ha0.
rregU HS (11%bv : bv 5) (img + fmt * ix) ltac:(apply (U_atom _ 480 _ R480 Bpx)) Ha1.
rregU HS (12%bv : bv 5) 3 ltac:(reflexivity) Ha2.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img (fmt * N) (proj1 HJ3) Himg_in3) as (_ & _ & _ & _ & HimgP & _).
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
idtac "OK-C0".
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W3 (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k (hh + hs * 3) (img + fmt * ix) 3 (-576) (Z_to_bv 64 0x82848) HJ3) end.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- clear; lia.
- clear - Hhh4096 Hhs; lia.
- clear - Hhhceil Hrq3T Hhs C1; lia.
- exact HspT.
- reflexivity.
- clear; lia.
- rewrite FFS, Hes. clear. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even; vm_compute; reflexivity.
- intros a Ha. split; [| rewrite Hes; clear - Ha Hhhceil Hrq3T Hhs Hceil Hslo FFS; lia].
replace a with (hh + (a - hh)) by (clear; lia). apply Ahh; [exact Hhh_in3 | clear - Ha Hrq3T Hhs; lia].
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) (hh + hs * 3) 3 (proj1 HJ3) Hhh_in3); [clear - Hhs; lia | clear - Hrq3T Hhs; lia].
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) (hh + hs * 3) 3 (proj1 HJ3) Hhh_in3); [clear - Hhs; lia | clear - Hrq3T Hhs; lia].
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) (hh + hs * 3) 3 (proj1 HJ3) Hhh_in3); [clear - Hhs; lia | clear - Hrq3T Hhs; lia | clear; lia].
- split; [clear - Bpx; lia|]. split; [clear - Himgceil HrqfN Hpx Hfmt C1; lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent trbsegs); exact (proj1 (HimgP a ltac:(clear - Ha Hpx HrqfN Hfmt; lia)))
| rewrite HspT, Hes; clear - Ha Himgceil HrqfN Hpx Hfmt Hceil Hslo FFS C1; lia]. }
split; [clear - HzI_hh Hrq3T HrqfN Hhs Hpx Hfmt; lia|]. split.
{ apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ img (fmt * N) (img + fmt * ix) 3 (proj1 HJ3) Himg_in3); [clear - Hpx; lia | clear - Hpx HrqfN Hfmt; lia]. }
split; [apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ img (fmt * N) (img + fmt * ix) 3 (proj1 HJ3) Himg_in3); [clear - Hpx; lia | clear - Hpx HrqfN Hfmt; lia]|].
intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ img (fmt * N) (img + fmt * ix) 3 (proj1 HJ3) Himg_in3); [clear - Hpx; lia | clear - Hpx HrqfN Hfmt; lia | clear; lia]. }
idtac "OK-C1".
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5).
clear Ha0 Ha1 Ha2 Rra Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
ga_aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
assert (Hfr3 : forall a, 0 <= a < 2 ^ 64 -> ~ (hh + hs * 3 <= a < hh + hs * 3 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576) ->
aview trbsegs (w_H W3) mem5 a = aview trbsegs (w_H W3) (ms_mem ms3) a)
by (intros a Ha1 Ha2; apply Hfr5; [exact Ha1 | intros Hq; apply Ha2; left; exact Hq | intros Hq; apply Ha2; right; exact Hq]).
assert (HWIN3 : forall a, 0 <= a < alloc_ceiling -> ~ (hh <= a < hh + 3 * ht_T Ht) ->
0 <= a < 2 ^ 64 /\ ~ (hh + hs * 3 <= a < hh + hs * 3 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hn Hhs Hceil Hslo FFS C1; lia).
assert (HWSTc3 : forall a, spZ regs + -576 <= a < spZ regs + 0 -> ~ (spZ regs + 0 <= a < spZ regs + 0) ->
0 <= a < 2 ^ 64 /\ ~ (hh + hs * 3 <= a < hh + hs * 3 + 3 \/ spZ regs + -576 - ESTACK <= a < spZ regs + -576))
by (intros a Ha Hn; rewrite Hes; clear - Ha Hhhceil Hrq3T Hhs Hceil Hslo Hshi H47 FFS C1; lia).
assert (HRNG8 : ((4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (F + 8192 <= 2147446784 \/ 17594333495296 <= F)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (r + 64 <= 2147446784 \/ 17594333495296 <= r)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (cfp + 24 <= 2147446784 \/ 17594333495296 <= cfp)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25152 /\ SB = 2147450880) /\
(3 * ht_T Ht <= req_size (3 * ht_T Ht) /\ (hh + req_size (3 * ht_T Ht) <= 2147446784 \/ 17594333495296 <= hh) /\ (hh + req_size (3 * ht_T Ht) <= F \/ F + 8192 <= hh) /\
(r + 64 <= hh \/ hh + req_size (3 * ht_T Ht) <= r) /\
(hh + req_size (3 * ht_T Ht) <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= hh) /\
frame_addr ly cid pos <= cfp /\ cfp + 24 <= frame_addr ly cid pos + fs_frame_bytes cid)).
{ unfold gbox, in_app in HFhigh, Hrapp, Hfhigh. unfold kLowShadowBeg, kHighMemBeg in HFhigh, Hrapp, Hfhigh. unfold gbox in Hhhzone.
split; [|clear - Hrq3T Hhhzone HdF_hh HzR_hh HdC_hh Hflo Hfhi; lia].
split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HFhigh; lia|]. split; [clear - Hr4096 Hrceil Hrapp; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi Hfhigh; lia|]. split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
assert (HRtb8 : ((4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ (tb + 48 <= 2147446784 \/ 17594333495296 <= tb)) /\
(F + 8192 <= alloc_ceiling /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ 512 <= F / 8) /\ SB = 2147450880) /\
3 * ht_T Ht <= req_size (3 * ht_T Ht) /\ (tb + 48 <= hh \/ hh + req_size (3 * ht_T Ht) <= tb)).
{ unfold gbox in Htbzone. change (req_size 48) with 48 in Htbzone.
split; [|clear - Hrq3T HzT_hh; lia]. split; [clear - Htb4096 Htbceil Hrqtb Htbzone C1; lia|]. split; [clear - HFceil HFq HF8 HF8lo; lia | reflexivity]. }
idtac "OK-P0".
m_reseatF HS HJ5 fx regs5 CLOB 534600 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG (m_same_of_preserved _ _ HP5)
ltac:(idtac; first
[ m_keptWc Hfr3 Hpres5 HJ5 HWIN3 HWSTc3 HRNG8 AG Usp RF E67 E10n E11n 0 0
ltac:(idtac; first [ m_keptW_blk Hfr3 Hpres5 HWIN3 AG 305%nat tb Rtb HRtb8
| ga_kept_consts Kgot0 Kgot5 Kcell0 Kcell5 Kguar0 Kguar5 Kuar0 Kuar5 Vgr0 Vgr5 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
idtac "OK-RS".
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot5 into Kgot0. rename Kcell5 into Kcell0. rename Kguar5 into Kguar0. rename Kuar5 into Kuar0. rename Vgr5 into Vgr0.
clear KP.
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) mem5 a = aview trbsegs (w_H W3) mem5 a) by (intros; reflexivity).
assert (Hkey5 : col3 trbsegs (mrestrict (w_H W3) mem5) (hh + hs * 3) pc0) by (exact (g_col3_copy (w_H W3) (ms_mem ms3) mem5 _ _ pc0 (proj1 Hpix3) Heff5)).
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ5 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE5 end.
norm_ss HS.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK GBspan A_asan_memcpy.
idtac "OK-R0".
all: try (lazymatch goal with |- range_addressable _ (U ?Ev _) _ _ =>
assert (Rtbv : ew Ev 305 = Z_to_bv 64 tb) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb);
assert (E44v : ew Ev 44 = Z_to_bv 64 SB) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E44) | _ => idtac end).
all: try (ga_obl_blk HJ5 Rtbv E44v Htb_in3).
idtac "OK-R1".
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-R2".
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rppx : ew Ex 476 = Z_to_bv 64 pp) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp);
assert (Rcntx : ew Ex 478 = Z_to_bv 64 (ht_cnt Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt) end.
g_cond HS BC_GEU (SAlu ALU_ADD (SOff 476 0) (SMd M_MUL (SOff 478 0) (SLit 3))) (SOff 476 0)
ltac:(apply (g_ptr_geu _ _ _ pp (ht_cnt Ht * 3) (U_atom _ 476 pp Rppx Bpp));
[ apply (g_U_mul_small _ (SOff 478 0) (SLit 3) (ht_cnt Ht) 3 (U_atom _ 478 _ Rcntx Hcnt64) ltac:(reflexivity)); clear - Hcnt0 HT24; lia | clear - Bpp; lia | clear - Hcnt0; lia | clear - Hppceil Hcnt0 HT24 C1; lia ]).
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK GBspan A_asan_memcpy.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-R3".
ga_join HS ss_M2 640%nat rga_deads_M2 ltac:(idtac).
idtac "OK-J".
assert (Hfq_l : In (fq, 4 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
assert (Huu_l : In (uu, ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
assert (Hpp_l : In (pp, 3 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
assert (Hxx_l : In (xx, 4 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
pose proof (req_size_pos (4 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq4T].
pose proof (req_size_pos (ht_T Ht) ltac:(clear - HT24; lia)) as [_ HrqT].
assert (SEPK : forall a, g_in5 fq hh uu pp xx (ht_T Ht) a -> (0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)) /\ 0 <= a < alloc_ceiling).
{ intros a Ha. split.
- destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ apply (Hoff3 fq (4 * ht_T Ht) Hfq_l) | apply (Hoff3 hh (3 * ht_T Ht) Hhh_l) | apply (Hoff3 uu (ht_T Ht) Huu_l) | apply (Hoff3 pp (3 * ht_T Ht) Hpp_l) | apply (Hoff3 xx (4 * ht_T Ht) Hxx_l) ];
clear - Ha Hrq4T Hrq3T HrqT; lia.
- clear - Ha Hfq4096 Hfqceil Hhh4096 Hhhceil Huu4096 Huuceil Hpp4096 Hppceil Hxx4096 Hxxceil Hrq4T Hrq3T HrqT. unfold g_in5 in Ha. lia. }
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Harr1 : g_arrs (mrestrict (w_H W3) mF) fq hh uu pp xx (ht_frequ Ht) (set_col (ht_keys Ht) hs pc0) (ht_used Ht) (ht_pal Ht) (ht_colidx Ht));
[ apply (g_arrs_keys (w_H W3) (ms_mem ms3) mF fq hh uu pp xx (ht_T Ht) _ _ _ _ _ hs pc0 (g_arrs_of_cht _ _ _ _ _ _ Ht (conj Af (conj Ak (conj Au (conj Ap Ax))))) (conj L1 (conj L2 (conj L3 (conj L4 L5)))) SEP5 Hhs);
[ replace (hh + 3 * hs) with (hh + hs * 3) by (clear; lia); apply (g_col3_kept (w_H W3) mem5 mF _ _ Hkey5); intros kk Hkk;
destruct (Hoff3 hh (3 * ht_T Ht) Hhh_l (hh + hs * 3 + kk) ltac:(clear - Hkk Hhs Hrq3T; lia)) as [Hq1 Hq2]; exact (KP _ Hq1 Hq2)
| intros a Ha Hn; destruct (SEPK a Ha) as [[Hq1 Hq2] Hq3]; rewrite (KP a Hq1 Hq2); apply (Hfr3 a Hq1);
intros [Hx | Hx]; [apply Hn; clear - Hx; lia | rewrite Hes in Hx; clear - Hx Hq3 Hceil Hslo FFS; lia] ]
| assert (Hpix1 : pixel_at trbsegs (mrestrict (w_H W3) mF) (img + fmt * ix) fmt pc0 true);
[ apply (g_pixel_at_kept (w_H W3) (ms_mem ms3) mF _ _ _ _ Hpix3 Hfmt); intros kk Hkk; destruct (Hpxoff kk Hkk) as [Hq1 Hq2]; rewrite (KP _ Hq1 Hq2); apply (Hfr3 _ Hq1);
intros [Hx | Hx]; [clear - Hx Hkk HzI_hh Hrq3T HrqfN Hhs Hpx Hfmt; lia | rewrite Hes in Hx; clear - Hx Hkk Himgceil HrqfN Hpx Hfmt Hceil Hslo FFS; lia] | ] ] end.
idtac "OK-M".
rga_hand RM2 HS HJ5 k; [rga_E_tac HEE5 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, pc0, js.
rga_cbn_cx_goal. fold hs.
assert (Hgp1 : g_pix {| c_ly := ly; c_S := S; c_W := W; c_regs := regs; c_mem := mem; c_md := md; c_ch := ch; c_r := r; c_cfp := cfp; c_g := g; c_wfn := wfn; c_ctx := ctx; c_path := path; c_attr := attr; c_gen := gen; c_loops := loops; c_Wd := Wd; c_Hd := Hd; c_bef := bef; c_beffmt := beffmt; c_cur := cur; c_s := s; c_N := N; c_img := img; c_fmt := fmt; c_fattr := fattr; c_fgen := fgen; c_delay := delay; c_rest := rest; c_cid := cid; c_pos := pos; c_fpos := fpos; c_E0 := E0 |} _ W3 _ ix pc0)
by (unfold g_pix; rga_cbn_cx_goal; split; [m_ewT | exact Hpix1]).
m_inv_auto.
Qed.
End d.
End c.
