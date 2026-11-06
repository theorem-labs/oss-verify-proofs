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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c YCbe YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i YC8j YC8k YC8l YC8m YC9t YC9u YC9v YC8n YC9w YC9g YC9i YC9j YC9h YC9k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC4b.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis COLHASH : tcolhash_spec B.
Hypothesis ABCMP : abcmp_realizes trasegs B A_bcmp_tra.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_SM_colhash : forall n, rga_from B ss_SMS (INV_SM B (S n)) -> rga_from B ss_SMC (INV_SM B (S n)).
Proof.
intros n RSMS.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & Hcnt & Hix & Hnix & R715 & R716 & R717 & R718 & R719).
destruct Hk0 as [Hk0 Hbud].
unfold ss_SMC in HS.
change CHT_SIZE with 48 in *.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hrin]).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
pose proof Hwf as Hwf0. destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x81368 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x80ea8])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (Hcnt0 & _) & _).
assert (HT24 : 0 < ht_T Ht <= 16777216) by (clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia).
assert (Hcnt64 : 0 <= ht_cnt Ht < 2 ^ 64) by (clear - Hcnt0 HT24; lia).
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx (ht_T Ht)).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest; YI0g.perm_tac).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
assert (Hcht_l : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> In (b, sz) lrest)
by (intros b sz Hb; subst lrest; apply in_or_app; right; right; right; exact Hb).
assert (Hcht_sz : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> 0 <= sz)
by (intros b sz Hb; cbn [cht_blocks In] in Hb; clear - Hb HT24; destruct Hb as [Hq | [Hq | [Hq | [Hq | [Hq | []]]]]]; injection Hq as _ <-; lia).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan A_col_hash.
all: try (unfold GBx; ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN0.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HKr0 : forall b sz, In (b, sz) lrest -> rg_blk_kept (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem msX) b (req_size sz)) end.
{ intros b sz Hb i Hi. destruct (Hoff3 b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN0; assumption. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Harr1 : cht_arrays trasegs (mrestrict (w_H W3) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) _ fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5). intros b sz Hb.
apply (rg_blk_kept_sub _ _ _ _ b (req_size sz)); [exact (HKr0 b sz (Hcht_l b sz Hb)) | clear; lia | pose proof (req_size_pos sz (Hcht_sz b sz Hb)); lia]. }
destruct Harr1 as (Af & Ak & Au & Ap & Ax).
assert (Himg_l : In (img, fmt * N) lrest)
by (subst lrest; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; unfold timg_block; clear - Hfmt; destruct Hfmt as [-> | ->]; left; reflexivity).
assert (Himg_in3 : In (img, fmt * N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Himg_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ img (fmt * N) HAR3 Himg_in3) as (Himg4096 & _ & Himgceil & _).
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as HrqfN.
assert (Hpx : 0 <= fmt * ix < 2 ^ 31 /\ fmt * ix + fmt <= fmt * N /\ fmt * N < 2 ^ 31) by (clear - Hfmt Hix HN; unfold RGB_NMAX in HN; nia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ img (fmt * N) (proj1 HJ3) Himg_in3) as (_ & _ & _ & _ & HimgP & _).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
destruct (m_pixel_of_present trasegs (mrestrict (w_H W3) (ms_mem msX)) (img + fmt * ix) fmt
ltac:(intros q Hq; apply m_mbyte_of_apresent; apply (proj1 (HimgP (img + fmt * ix + q) ltac:(clear - Hq Hpx HrqfN; lia)))) Hfmt) as (pxc & op & Hpix) end.
destruct (find_slot_exists Ht ent Hinv pxc) as (hs & Hfs & Rhs).
assert (Hprobe : op = true -> probe (ht_T Ht) (ht_used Ht) (ht_keys Ht) pxc = Some hs) by (intros _; rewrite <- probe_of_htab; exact Hfs).
assert (Hhh_in3 : In (hh, 3 * ht_T Ht) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; apply Hcht_l; cbn [cht_blocks In]; tauto]).
assert (Huu_in3 : In (uu, ht_T Ht) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; apply Hcht_l; cbn [cht_blocks In]; tauto]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) HAR3 Hhh_in3) as (Hhh4096 & _ & Hhhceil & _).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ uu (ht_T Ht) HAR3 Huu_in3) as (Huu4096 & _ & Huuceil & _).
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as Hrq3T.
pose proof (req_size_pos (ht_T Ht) ltac:(clear - HT24; lia)) as HrqT.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rregU HS (10%bv : bv 5) (img + fmt * ix)
ltac:(apply m_U_add0; apply U_add_small_q; [apply (U_atom _ 45 img E45); clear - Himg4096 Himgceil HrqfN C1; lia
| apply U_zext32_shifts; [apply (U_atom _ 716 (fmt * ix) R716); clear - Hpx; lia | clear - Hpx; lia]
| clear - Himg4096; lia | clear - Hpx; lia | clear - Himgceil HrqfN Hpx C1; lia]) Ha0.
rregU HS (11%bv : bv 5) hh ltac:(apply (U_atom _ 616 hh); [exact Rhh | clear - Hhh4096 Hhhceil Hrq3T C1; lia]) Ha1.
rregU HS (12%bv : bv 5) uu ltac:(apply (U_atom _ 617 uu); [exact Ruu | clear - Huu4096 Huuceil HrqT C1; lia]) Ha2.
rregU HS (13%bv : bv 5) (ht_T Ht) ltac:(apply (U_sext32_small _ 621 (ht_T Ht)); [exact RT | clear - HT24; lia]) Ha3.
rregU HS (14%bv : bv 5) fmt ltac:(apply (U_sext32_small _ 46 fmt); [exact E46 | clear - Hfmt; lia]) Ha4.
assert (R717x : exists w, ew E 717 = w /\ (bef <> 0 -> w = Z_to_bv 64 (beffmt * ix))) by (eexists; split; [reflexivity | exact R717]).
destruct R717x as (w717 & R717w & Hw717). clear R717.
rga_chain HS HJ3 AG EE.
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call trasegs B LAWS Hsegs W3 Ex ssX msX TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k
TCOLHASH_STK [] 0
(-512) (ew Ex 2) (Z_to_bv 64 0x83430) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\ getr regs2 10 = w64 (if op then hs else 2 ^ 64 - 1)) HS eq_refl HJ3);
[ rewrite Rsp; cbn [sv_denot]; reflexivity
| reflexivity
| ga_evalE AG
| reflexivity
| clear; lia
| vm_compute; discriminate
| rewrite FFS; vm_compute; discriminate
| rewrite Rgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| rewrite unsigned_lit_small by (clear; lia); clear; lia
| unfold s0Z; rewrite Rs0; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
replace (spZ regs + -512) with (spZ regs - 512) by (clear; lia); exact (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1)
| intros HPRE1; eapply SRr_mono;
[ pose proof (COLHASH ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch) img (fmt * N) (fmt * ix) hh (3 * ht_T Ht) uu (ht_T Ht) (ht_T Ht) fmt
(ht_used Ht) (ht_keys Ht) pxc op hs HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc];
let v := eval vm_compute in A_col_hash in change (w64 A_col_hash) with (Z_to_bv 64 v) in CALL;
apply CALL; clear CALL
| cbv beta; intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HJc & HPc & HK7);
exists ly7, S7, regs7, mem7, md7; split; [rewrite Rra; reflexivity|]; split; [exact HJc|]; split; [exact HPc | exact HK7] ]
| intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end end.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- exact Ha3.
- exact Ha4.
- exact Himg_in3.
- clear - Hpx. lia.
- clear - Hpx. lia.
- exact Hhh_in3.
- clear. lia.
- exact Huu_in3.
- clear. lia.
- exact Hpix.
- exact Au.
- exact Ak.
- exact L1.
- exact L2.
- clear - HT24. lia.
- exact Hprobe.
-       cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HJc & HP7 & (-> & -> & -> & Ha07)).
pose proof HJc as (_ & _ & _ & _ & _ & _ & (_ & Hd7) & _).
clear Ha0 Ha1 Ha2 Ha3 Ha4 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof HJ7 as (HAR7 & Hly7 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin3) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA3 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (HnoFP : forall a : Z, ~ inFP [] a) by (intros a Ha; exact (inFP_nil a Ha)).
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG
ltac:(idtac; first
[ m_keptJ HJc HJ7 AG Usp FFS RF E67 E10n E11n Hfin3 HfinS3 Hrin3 Hrin3 EFA3 F HFpres7 (fun (a : Z) (_ : F <= a < F + 8192) => HnoFP a)
(fun (a : Z) (_ : 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024) => HnoFP a) (fun (a : Z) (_ : r <= a < r + 64) => HnoFP a) (fun (a : Z) (_ : cfp <= a < cfp + 24) => HnoFP a) LAWS
ltac:(idtac; first [ m_keptJ_blk HJc AG 305%nat Rtb Htb_in3 Htb_in3 48 (fun (a : Z) (_ : tb <= a < tb + 48) => HnoFP a) LAWS
| ga_kept_consts Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
rreg HS (10%bv : bv 5) Rhsa. cbn [ms_regs] in Rhsa. rewrite Ha07 in Rhsa. symmetry in Rhsa. unfold w64 in Rhsa.
norm_ss HS.
reshok_bx HS 44%nat.
aj_run_to_tok tratbl_lib_ok HS HJ7 SHOK GBspan 0x83440.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HKr1 : forall b sz, In (b, sz) lrest -> rg_blk_kept (w_H W3) (w_H W3) (ms_mem ms) (ms_mem msX) b (req_size sz)) end.
{ intros b sz Hb. assert (Hb3 : In (b, sz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hb]).
eapply rg_blk_kept_trans; [exact (m_blk_kept_call0 B _ _ _ _ _ _ _ _ _ _ _ _ _ b sz HJc Hb3 Hb3)|].
intros i Hi. destruct (Hoff3 b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN1; assumption. }
reshok_bx HS 44%nat.
srr_branch_tok tratbl_lib_ok HS SHOK GBspan.
+
aj_run_to_tok tratbl_lib_ok HS HJ7 SHOK GBspan 0x8347c.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HarrC : cht_arrays trasegs (mrestrict (w_H W3) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) _ fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5). intros b sz Hb i Hi.
pose proof (req_size_pos sz (Hcht_sz b sz Hb)) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
rewrite (UN2 (b + i) Hq1 Hq2). rewrite (HKr1 b sz (Hcht_l b sz Hb) i ltac:(clear - Hi Hrqb; lia)). exact (HKr0 b sz (Hcht_l b sz Hb) i ltac:(clear - Hi Hrqb; lia)). }
ga_join HS ss_SMS 790%nat rga_deads_SMS ltac:(idtac).
m_hand_ih RSMS HS HJ7 (k + 0); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent. rewrite Z.add_0_r. m_inv_auto.
+
destruct op; [| exfalso; rewrite YO3v.branch_eq_U in Hc; apply Z.eqb_neq in Hc; apply Hc;
rewrite (U_atom _ 758 (2 ^ 64 - 1)) by first [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhsa | clear; lia]; reflexivity].
aj_run_to_tok tratbl_lib_ok HS HJ7 SHOK GBspan 0x83468.
1: unfold GBx; ga_obl_blk HJ7 Rtb E44 Htb_in3.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HKr2 : forall b sz, In (b, sz) lrest -> rg_blk_kept (w_H W3) (w_H W3) (ms_mem ms) (ms_mem msX) b (req_size sz)) end.
{ intros b sz Hb. eapply rg_blk_kept_trans; [exact (HKr1 b sz Hb)|].
intros i Hi. destruct (Hoff3 b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN2; assumption. }
set (xv := getz (ht_colidx Ht) hs) in *.
lazymatch type of Ax with arr32 _ ?mm _ _ =>
assert (Vxv : val_mem trasegs mm (xx + 4 * hs) 4 xv /\ 0 <= xv < 2 ^ 32)
by (subst xv; exact (arr32_getz _ _ _ _ hs Ax ltac:(rewrite L4; exact Rhs))) end.
assert (Hxx_l : In (xx, 4 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
assert (Hxx_in3 : In (xx, 4 * ht_T Ht) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hxx_l]).
pose proof (req_size_pos (4 * ht_T Ht) ltac:(clear - HT24; lia)) as Hrq4T.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Vxv1 : val_mem trasegs (mrestrict (w_H W3) (ms_mem msX)) (xx + 4 * hs) 4 xv) end.
{ apply (rg_val_mem_blk_kept (w_H W3) (w_H W3) (ms_mem ms) _ xx (req_size (4 * ht_T Ht)) (xx + 4 * hs) 4 xv (proj1 Vxv) (HKr2 xx _ Hxx_l)); [clear - Rhs; lia | clear - Rhs Hrq4T; cbn; lia]. }
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ xx (4 * ht_T Ht) HAR3 Hxx_in3) as (Hxx4096 & Hxxzone & Hxxceil & Hxx16).
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ xx (4 * ht_T Ht) 7 fpos HAR3 Hxx_in3 Hfin3) as HdF_xx.
unfold zdisjoint in HdF_xx. cbn [fst snd] in HdF_xx. change (fs_frame_bytes 7) with 8192 in HdF_xx. rewrite EFA3 in HdF_xx. fold F in HdF_xx.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ xx (4 * ht_T Ht) cid pos HAR3 Hxx_in3 HfinS3) as HdC_xx.
unfold zdisjoint in HdC_xx. cbn [fst snd] in HdC_xx. rewrite EFA3 in HdC_xx.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (xx, 4 * ht_T Ht) HAR3 HPrt3 ltac:(right; exact Hxx_l)) as HzR_xx.
unfold zdisjoint, block_rng in HzR_xx. cbn [fst snd] in HzR_xx. change (req_size RGB_SIZE) with 64 in HzR_xx.
assert (HPtb3 : Permutation (ablocks B ly3 S3) ((tb, 48) :: (r, RGB_SIZE) :: lrest)) by (eapply Permutation_trans; [exact HPrt3 | apply perm_swap]).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (xx, 4 * ht_T Ht) HAR3 HPtb3 ltac:(right; exact Hxx_l)) as HzT_xx.
unfold zdisjoint, block_rng in HzT_xx. cbn [fst snd] in HzT_xx. change (req_size 48) with 48 in HzT_xx.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_havoc trasegs 780%nat Ex ssx msx [Z_to_bv 64 (xx + 4 * hs); Z_to_bv 64 xv] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ (havoc ?E0v _ ?vals) _ _ =>
assert (E780 : ew (havoc E0v 780 vals) 780 = Z_to_bv 64 (xx + 4 * hs))
by (change 780%nat with (780 + 0)%nat at 2; rewrite (ew_havoc_new _ 780%nat vals 0%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E781 : ew (havoc E0v 780 vals) 781 = Z_to_bv 64 xv)
by (change 781%nat with (780 + 1)%nat; rewrite (ew_havoc_new _ 780%nat vals 1%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity) end.
assert (Hxv32 : 0 <= xv < 2 ^ 32) by (exact (proj2 Vxv)).
assert (Hcell_rng : 4096 <= xx + 4 * hs /\ xx + 4 * hs + 4 <= alloc_ceiling) by (clear - Hxx4096 Hxxceil Hrq4T Rhs; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _
(YQ0b.mkRegion (Some 780%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 781 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E780, unsigned_lit_small by (clear - Hcell_rng C1; lia);
split; [clear - Hcell_rng; lia|]; split; [clear - Hcell_rng C1; lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| apply Forall_cons; [eapply (chunk_ok_val trasegs Ev _ (xx + 4 * hs) _ _ (SOff 781 0) xv);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E781 | exact Hxv32 | cbn; clear; lia
| rewrite Z.add_0_r; exact Vxv1] | apply Forall_nil] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ clear - Hcell_rng Hceil Hslo FFS Rhs Hrq4T; lia
| destruct Hxxzone as [Hz1 Hz2]; clear - Hz1 Hz2 Rhs Hrq4T HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_xx Rhs Hrq4T; lia
| clear - HdC_xx Rhs Hrq4T Hflo Hfhi; lia
| clear - HzR_xx Rhs Hrq4T; lia
| clear - HzT_xx Rhs Hrq4T; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HUA : U Ev (SAlu ALU_ADD (SOff 619 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 758 0) (SLit 32)) (SLit 30))) = U Ev (SOff 780 0)) end.
{ lazymatch goal with |- U ?Ev _ = _ =>
rewrite (U_atom Ev 780 (xx + 4 * hs) E780) by (clear - Hcell_rng C1; lia);
apply (m_U_elem4 Ev 619 xx (SOff 758 0) hs);
[ repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | clear - Hxx4096; lia | clear - Hcell_rng C1; lia
| apply (U_atom Ev 758 hs); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhsa | clear - Rhs HT24; lia]
| clear - Rhs HT24; lia ] end. }
lazymatch type of HS with st_ok ?segs ?Ev ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
pose proof (ast_ok_set_reg_fp segs Ev ssx (restrict Hh msx) (10%bv : bv 5) (SOff 780 0) HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg segs Hh Ev ssx msx (10%bv : bv 5) HS); change (sv_denot Ev (SOff 780 0) = sv_denot Ev e);
apply U_inj; symmetry; exact HUA)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 780%nat (mkAF 4096 140737479966720 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?ew_ewset_other by lia; rewrite E780, unsigned_lit_small by (clear - Hcell_rng C1; lia); change (2 ^ 2) with 4;
split; [clear - Hcell_rng C1; lia|]; split; [rewrite Z.add_mod, (Z.mul_comm 4 hs), Z_mod_mult, Z.add_0_r, Z.mod_mod by lia; clear - Hxx16; pose proof (Z.div_mod xx 16 ltac:(lia)) as D; rewrite Hxx16, Z.add_0_r in D; rewrite D; replace (16 * (xx / 16)) with ((4 * (xx / 16)) * 4) by lia; apply Z_mod_mult | clear; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok_bx HS 44%nat.
aj_run_to_tok tratbl_lib_ok HS HJ7 SHOK GBspan 0x8347c.
all: try (m_obl_cell HJ7 E780 E44 Hxx_in3 ltac:(idtac; first [clear - Hcell_rng C1; lia | clear - Rhs Hrq4T; lia])).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HarrC : cht_arrays trasegs (mrestrict (w_H W3) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) _ fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5). intros b sz Hb i Hi.
pose proof (req_size_pos sz (Hcht_sz b sz Hb)) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
rewrite (UN3 (b + i) Hq1 Hq2). rewrite (HKr2 b sz (Hcht_l b sz Hb) i ltac:(clear - Hi Hrqb; lia)). exact (HKr0 b sz (Hcht_l b sz Hb) i ltac:(clear - Hi Hrqb; lia)). }
ga_join HS ss_SMS 790%nat rga_deads_SMS ltac:(idtac).
m_hand_ih RSMS HS HJ7 (k + 0); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent. rewrite Z.add_0_r. m_inv_auto.
Qed.
End d.
End c.
