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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i YC8j YC8k YC8l YC8m YC9t YC9u YC9v YC92 YC93 YC94 YC8z.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis COLHASH : tcolhash_spec B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Ltac m_hand_ih IH HS HJx kx :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (rga_post ?B ?cxv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
eapply (IH cxv Ev kx lyx Sx W3 ms3 md3);
[ lazymatch goal with H0 : rga_base _ _ |- _ => exact H0 end
| idtac
| first [eassumption | idtac]
| first [exact HJx | unfold rgc_FP, rgc_FPs; rga_cbn_cx_goal; cbn [ms_mem]; exact HJx | idtac]
| first [eassumption | idtac]
| red; rga_cbn_cx_goal
| exact HS ] end end end.
Lemma rga_DL_loop : rga_fromA B ss_CR0 (fun _ => INV_CR0 B) -> forall n, rga_from B ss_DLH (INV_DLH B n).
Proof.
intros RCR. induction n as [|n IH].
{
intros cx E k ly3 S3 W3 ms3 md3 _ _ _ _ _ HINV _. exfalso.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & ix & Ht & ent & HINV).
repeat (destruct HINV as [? HINV]). lia. }
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & ix & Ht & ent & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Rcnt & RT & Rha & Hha & Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & Hcnt & Hix & Hnix & R716 & R717 & R718 & R719 & Hdense).
destruct Hk0 as [Hk0 Hbud].
unfold ss_DLH in HS.
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
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan A_col_hash.
all: try (unfold GBx; ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN0.
clear HF HFr HG.
norm_ss HS.
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx (ht_T Ht) ++ [(dn, 4 * ht_cnt Ht)]).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest; YI0g.perm_tac).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
assert (Hcht_l : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> In (b, sz) lrest)
by (intros b sz Hb; subst lrest; apply in_or_app; right; right; right; apply (in_or_app (cht_blocks fq hh uu pp xx (ht_T Ht))); left; exact Hb).
assert (Hdn_l : In (dn, 4 * ht_cnt Ht) lrest)
by (subst lrest; apply in_or_app; right; right; right; apply (in_or_app (cht_blocks fq hh uu pp xx (ht_T Ht))); right; left; reflexivity).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HKr0 : forall b sz, In (b, sz) lrest -> rg_blk_kept (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem msX) b (req_size sz)) end.
{ intros b sz Hb i Hi. destruct (Hoff3 b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN0; assumption. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Harr1 : cht_arrays trasegs (mrestrict (w_H W3) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) _ fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5). intros b sz Hb.
assert (Hsz : 0 <= sz) by (cbn [cht_blocks In] in Hb; clear - Hb HT24; destruct Hb as [Hq | [Hq | [Hq | [Hq | [Hq | []]]]]]; injection Hq as _ <-; lia).
apply (rg_blk_kept_sub _ _ _ _ b (req_size sz)); [exact (HKr0 b sz (Hcht_l b sz Hb)) | clear; lia | pose proof (req_size_pos sz Hsz); lia]. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Hdense1 : forall j, 0 <= j < ix -> val_mem trasegs (mrestrict (w_H W3) (ms_mem msX)) (dn + 4 * j) 4 (getz (map snd ent) j)) end.
{ intros j Hj. apply (rg_val_mem_blk_kept (w_H W3) (w_H W3) (ms_mem ms3) _ dn (req_size (4 * ht_cnt Ht)) (dn + 4 * j) 4 _ (Hdense j Hj) (HKr0 dn _ Hdn_l)); [clear - Hj; lia|].
pose proof (req_size_pos (4 * ht_cnt Ht) ltac:(clear - Hcnt0; lia)). clear - Hj Hix H. cbn. lia. }
destruct (ent_slot Ht ent Hinv ix Hix) as (hs & Hin_s & Hci & He & Hpc & Hf1).
pose proof Hin_s as [Rhs Huse].
set (fv := freq Ht hs) in *.
assert (Hfvx : getz (map snd ent) ix = fv) by (unfold getz; apply nth_error_nth; rewrite nth_error_map, He; reflexivity).
assert (Hprobe : probe (ht_T Ht) (ht_used Ht) (ht_keys Ht) (palc Ht ix) = Some hs)
by (rewrite Hpc, <- probe_of_htab; apply (find_present Ht ent Hinv hs Hin_s)).
destruct Harr1 as (Af & Ak & Au & Ap & Ax).
lazymatch type of Af with arr32 _ ?mm _ _ =>
assert (Vfv : val_mem trasegs mm (fq + 4 * hs) 4 fv /\ 0 <= fv < 2 ^ 32)
by (subst fv; unfold freq; exact (arr32_getz _ _ _ _ hs Af ltac:(rewrite L3; exact Rhs))) end.
assert (Hpix : pixel_at trasegs (mrestrict (w_H W3) (ms_mem ms)) (pp + 3 * ix) 3 (palc Ht ix) true)
by (split; [unfold palc; apply (arr8_col3 trasegs _ pp (ht_pal Ht) ix Ap); [clear - Hix; lia | rewrite L5; clear - Hix Hcnt0; lia] | left; split; reflexivity]).
assert (Hpp_in3 : In (pp, 3 * ht_T Ht) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; apply Hcht_l; cbn [cht_blocks In]; tauto]).
assert (Hhh_in3 : In (hh, 3 * ht_T Ht) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; apply Hcht_l; cbn [cht_blocks In]; tauto]).
assert (Huu_in3 : In (uu, ht_T Ht) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; apply Hcht_l; cbn [cht_blocks In]; tauto]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) HAR3 Hpp_in3) as (Hpp4096 & _ & Hppceil & _).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ hh (3 * ht_T Ht) HAR3 Hhh_in3) as (Hhh4096 & _ & Hhhceil & _).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ uu (ht_T Ht) HAR3 Huu_in3) as (Huu4096 & _ & Huuceil & _).
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as Hrq3T.
pose proof (req_size_pos (ht_T Ht) ltac:(clear - HT24; lia)) as HrqT.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rregU HS (10%bv : bv 5) (pp + 3 * ix)
ltac:(apply U_add_small_q; [apply (U_atom _ 618 pp); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | clear - Hpp4096 Hppceil Hrq3T C1; lia]
| rewrite U_and_lit by (clear; lia); rewrite (U_atom _ 716 (3 * ix)) by first [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R716 | clear - Hix Hcnt0 HT24; lia];
change 4294967295 with (Z.ones 32); rewrite Z.land_ones by (clear; lia); apply Z.mod_small; clear - Hix Hcnt0 HT24; lia
| clear - Hpp4096; lia | clear - Hix; lia | clear - Hppceil Hrq3T C1 Hix Hcnt0; lia]) Ha0.
rregU HS (11%bv : bv 5) hh ltac:(apply (U_atom _ 616 hh); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | clear - Hhh4096 Hhhceil Hrq3T C1; lia]) Ha1.
rregU HS (12%bv : bv 5) uu ltac:(apply (U_atom _ 617 uu); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | clear - Huu4096 Huuceil HrqT C1; lia]) Ha2.
rregU HS (13%bv : bv 5) (ht_T Ht) ltac:(apply (U_sext32_small _ 621 (ht_T Ht)); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT | clear - HT24; lia]) Ha3.
rregU HS (14%bv : bv 5) 3 ltac:(reflexivity) Ha4.
rga_chain HS HJ3 AG EE.
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call trasegs B LAWS Hsegs W3 Ex ssX msX TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k
TCOLHASH_STK [] 0
(-512) (ew Ex 2) (Z_to_bv 64 0x832a8) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\ getr regs2 10 = w64 hs) HS eq_refl HJ3);
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
[ pose proof (COLHASH ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch) pp (3 * ht_T Ht) (3 * ix) hh (3 * ht_T Ht) uu (ht_T Ht) (ht_T Ht) 3
(ht_used Ht) (ht_keys Ht) (palc Ht ix) true hs HPRE1) as CALL;
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
- exact Hpp_in3.
- clear - Hix. lia.
- clear - Hix Hcnt0. lia.
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
- intros _. exact Hprobe.
- cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HJc & HP7 & (-> & -> & -> & Ha07)).
pose proof HJc as (_ & _ & _ & _ & _ & _ & (_ & Hd7) & _).
clear Ha0 Ha1 Ha2 Ha3 Ha4 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof HJ7 as (HAR7 & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by (exact EFA3).
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
aj_run_to_tok tratbl_lib_ok HS HJ7 SHOK GBspan 0x832c8.
all: try (unfold GBx; ga_obl_blk HJ7 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN1.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HKr1 : forall b sz, In (b, sz) lrest -> rg_blk_kept (w_H W3) (w_H W3) (ms_mem ms) (ms_mem msX) b (req_size sz)) end.
{ intros b sz Hb. assert (Hb3 : In (b, sz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hb]).
eapply rg_blk_kept_trans; [exact (m_blk_kept_call0 B _ _ _ _ _ _ _ _ _ _ _ _ _ b sz HJc Hb3 Hb3)|].
intros i Hi. destruct (Hoff3 b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN1; assumption. }
assert (Hfq_l : In (fq, 4 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
assert (Hfq_in3 : In (fq, 4 * ht_T Ht) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hfq_l]).
pose proof (req_size_pos (4 * ht_T Ht) ltac:(clear - HT24; lia)) as Hrq4T.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Vfv1 : val_mem trasegs (mrestrict (w_H W3) (ms_mem msX)) (fq + 4 * hs) 4 fv) end.
{ apply (rg_val_mem_blk_kept (w_H W3) (w_H W3) (ms_mem ms) _ fq (req_size (4 * ht_T Ht)) (fq + 4 * hs) 4 fv (proj1 Vfv) (HKr1 fq _ Hfq_l)); [clear - Rhs; lia | clear - Rhs Hrq4T; cbn; lia]. }
norm_ss HS.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) HAR3 Hfq_in3) as (Hfq4096 & Hfqzone & Hfqceil & Hfq16).
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) 7 fpos HAR3 Hfq_in3 Hfin3) as HdF_fq.
unfold zdisjoint in HdF_fq. cbn [fst snd] in HdF_fq. change (fs_frame_bytes 7) with 8192 in HdF_fq. rewrite EFA3 in HdF_fq. fold F in HdF_fq.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ fq (4 * ht_T Ht) cid pos HAR3 Hfq_in3 HfinS3) as HdC_fq.
unfold zdisjoint in HdC_fq. cbn [fst snd] in HdC_fq. rewrite EFA3 in HdC_fq.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (fq, 4 * ht_T Ht) HAR3 HPrt3 ltac:(right; exact Hfq_l)) as HzR_fq.
unfold zdisjoint, block_rng in HzR_fq. cbn [fst snd] in HzR_fq. change (req_size RGB_SIZE) with 64 in HzR_fq.
assert (HPtb3 : Permutation (ablocks B ly3 S3) ((tb, 48) :: (r, RGB_SIZE) :: lrest)) by (eapply Permutation_trans; [exact HPrt3 | apply perm_swap]).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (fq, 4 * ht_T Ht) HAR3 HPtb3 ltac:(right; exact Hfq_l)) as HzT_fq.
unfold zdisjoint, block_rng in HzT_fq. cbn [fst snd] in HzT_fq. change (req_size 48) with 48 in HzT_fq.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_havoc trasegs 760%nat Ex ssx msx [Z_to_bv 64 (fq + 4 * hs); Z_to_bv 64 fv] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ (havoc ?E0v _ ?vals) _ _ =>
assert (E760 : ew (havoc E0v 760 vals) 760 = Z_to_bv 64 (fq + 4 * hs))
by (change 760%nat with (760 + 0)%nat at 2; rewrite (ew_havoc_new _ 760%nat vals 0%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity);
assert (E761 : ew (havoc E0v 760 vals) 761 = Z_to_bv 64 fv)
by (change 761%nat with (760 + 1)%nat; rewrite (ew_havoc_new _ 760%nat vals 1%nat (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity) end.
assert (Hfv32 : 0 <= fv < 2 ^ 32) by (exact (proj2 Vfv)).
assert (Hcell_rng : 4096 <= fq + 4 * hs /\ fq + 4 * hs + 4 <= alloc_ceiling) by (clear - Hfq4096 Hfqceil Hrq4T Rhs; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _
(YQ0b.mkRegion (Some 760%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 761 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E760, unsigned_lit_small by (clear - Hcell_rng C1; lia);
split; [clear - Hcell_rng; lia|]; split; [clear - Hcell_rng C1; lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| apply Forall_cons; [eapply (chunk_ok_val trasegs Ev _ (fq + 4 * hs) _ _ (SOff 761 0) fv);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E761 | exact Hfv32 | cbn; clear; lia
| rewrite Z.add_0_r; exact Vfv1] | apply Forall_nil] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ clear - Hcell_rng Hceil Hslo FFS Rhs Hrq4T; lia
| destruct Hfqzone as [Hz1 Hz2]; clear - Hz1 Hz2 Rhs Hrq4T HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_fq Rhs Hrq4T; lia
| clear - HdC_fq Rhs Hrq4T Hflo Hfhi; lia
| clear - HzR_fq Rhs Hrq4T; lia
| clear - HzT_fq Rhs Hrq4T; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
assert (Hdn_in3 : In (dn, 4 * ht_cnt Ht) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hdn_l]).
pose proof (req_size_pos (4 * ht_cnt Ht) ltac:(clear - Hcnt0; lia)) as Hrq4c.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ dn (4 * ht_cnt Ht) HAR3 Hdn_in3) as (Hdn4096 & Hdnzone & Hdnceil & Hdn16).
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ dn (4 * ht_cnt Ht) 7 fpos HAR3 Hdn_in3 Hfin3) as HdF_dn.
unfold zdisjoint in HdF_dn. cbn [fst snd] in HdF_dn. change (fs_frame_bytes 7) with 8192 in HdF_dn. rewrite EFA3 in HdF_dn. fold F in HdF_dn.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ dn (4 * ht_cnt Ht) cid pos HAR3 Hdn_in3 HfinS3) as HdC_dn.
unfold zdisjoint in HdC_dn. cbn [fst snd] in HdC_dn. rewrite EFA3 in HdC_dn.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (dn, 4 * ht_cnt Ht) HAR3 HPrt3 ltac:(right; exact Hdn_l)) as HzR_dn.
unfold zdisjoint, block_rng in HzR_dn. cbn [fst snd] in HzR_dn. change (req_size RGB_SIZE) with 64 in HzR_dn.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (dn, 4 * ht_cnt Ht) HAR3 HPtb3 ltac:(right; exact Hdn_l)) as HzT_dn.
unfold zdisjoint, block_rng in HzT_dn. cbn [fst snd] in HzT_dn. change (req_size 48) with 48 in HzT_dn.
assert (HzA_dn : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> b + req_size sz <= dn \/ dn + req_size (4 * ht_cnt Ht) <= b).
{ intros b sz Hb.
assert (HPx : Permutation (ablocks B ly3 S3) (cht_blocks fq hh uu pp xx (ht_T Ht) ++ ((dn, 4 * ht_cnt Ht) :: (r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (b, sz) (dn, 4 * ht_cnt Ht) HAR3 HPx Hb ltac:(left; reflexivity)) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. exact Dd. }
pose proof (HzA_dn fq (4 * ht_T Ht) ltac:(cbn [cht_blocks In]; tauto)) as HzQ_dn.
assert (Hdcell_rng : 4096 <= dn + 4 * ix /\ dn + 4 * ix + 4 <= alloc_ceiling) by (clear - Hdn4096 Hdnceil Hrq4c Hix; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ dn (4 * ht_cnt Ht) (proj1 HJ7) Hdn_in3) as (_ & _ & _ & _ & Hdnpres & _).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E719c : ew Ev 719 = Z_to_bv 64 (dn + 4 * ix)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R719);
assert (E718c : ew Ev 718 = Z_to_bv 64 (dn + 4 * ix)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R718);
pose proof (ast_ok_add_region trasegs Ev _ _
(YQ0b.mkRegion (Some 719%nat) 0 4 0 4 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite E719c, unsigned_lit_small by (clear - Hdcell_rng C1; lia);
split; [clear - Hdcell_rng; lia|]; split; [clear - Hdcell_rng C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); apply (proj1 (Hdnpres (dn + 4 * ix + o) ltac:(clear - Ho Hix Hrq4c; lia)))
| apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ clear - Hdcell_rng Hceil Hslo FFS Hix Hrq4c; lia
| destruct Hdnzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hix Hrq4c HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_dn Hix Hrq4c; lia
| clear - HdC_dn Hix Hrq4c Hflo Hfhi; lia
| clear - HzR_dn Hix Hrq4c; lia
| clear - HzT_dn Hix Hrq4c; lia
| clear - HzQ_dn Hix Hrq4c Rhs Hrq4T; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HUA : U Ev (SAlu ALU_ADD (SOff 615 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 724 0) (SLit 32)) (SLit 30))) = U Ev (SOff 760 0)) end.
{ lazymatch goal with |- U ?Ev _ = _ =>
rewrite (U_atom Ev 760 (fq + 4 * hs) E760) by (clear - Hcell_rng C1; lia);
apply (m_U_elem4 Ev 615 fq (SOff 724 0) hs);
[ repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | clear - Hfq4096; lia | clear - Hcell_rng C1; lia
| apply (U_atom Ev 724 hs); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhsa | clear - Rhs HT24; lia]
| clear - Rhs HT24; lia ] end. }
lazymatch type of HS with st_ok ?segs ?Ev ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
pose proof (ast_ok_set_reg_fp segs Ev ssx (restrict Hh msx) (10%bv : bv 5) (SOff 760 0) HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg segs Hh Ev ssx msx (10%bv : bv 5) HS); change (sv_denot Ev (SOff 760 0) = sv_denot Ev e);
apply U_inj; symmetry; exact HUA)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok ?segs ?Ev ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (23%bv : bv 5)) in
pose proof (ast_ok_set_reg_fp segs Ev ssx (restrict Hh msx) (23%bv : bv 5) (SOff 719 0) HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg segs Hh Ev ssx msx (23%bv : bv 5) HS); change (sv_denot Ev (SOff 719 0) = sv_denot Ev e);
cbn [sv_denot]; rewrite E718c, E719c; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 760%nat (mkAF 4096 140737479966720 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?ew_ewset_other by lia; rewrite E760, unsigned_lit_small by (clear - Hcell_rng C1; lia); change (2 ^ 2) with 4;
split; [clear - Hcell_rng C1; lia|]; split; [rewrite Z.add_mod, (Z.mul_comm 4 hs), Z_mod_mult, Z.add_0_r, Z.mod_mod by lia; clear - Hfq16; pose proof (Z.div_mod fq 16 ltac:(lia)) as D; rewrite Hfq16, Z.add_0_r in D; rewrite D; replace (16 * (fq / 16)) with ((4 * (fq / 16)) * 4) by lia; apply Z_mod_mult | clear; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 719%nat (mkAF 4096 140737479966720 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?ew_ewset_other by lia; rewrite E719c, unsigned_lit_small by (clear - Hdcell_rng C1; lia); change (2 ^ 2) with 4;
split; [clear - Hdcell_rng C1; lia|]; split; [rewrite Z.add_mod, (Z.mul_comm 4 ix), Z_mod_mult, Z.add_0_r, Z.mod_mod by lia; clear - Hdn16; pose proof (Z.div_mod dn 16 ltac:(lia)) as D; rewrite Hdn16, Z.add_0_r in D; rewrite D; replace (16 * (dn / 16)) with ((4 * (dn / 16)) * 4) by lia; apply Z_mod_mult | clear; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok_bx HS 44%nat.
aj_run_to_tok tratbl_lib_ok HS HJ7 SHOK GBspan 0x83314.
all: try (unfold GBx; ga_obl_blk HJ7 Rtb E44 Htb_in3).
all: try (m_obl_cell HJ7 E719c E44 Hdn_in3 ltac:(idtac; first [clear - Hdcell_rng C1; lia | clear - Hix Hrq4c; lia])).
all: try (m_obl_cell HJ7 E760 E44 Hfq_in3 ltac:(idtac; first [clear - Hcell_rng C1; lia | clear - Rhs Hrq4T; lia])).
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(m_awr_cell 719%nat R719 dn Adn Hdn_in3 ltac:(idtac; first [clear - Hdcell_rng C1; lia | lazymatch goal with Ha : _ <= _ < _ |- _ => clear - Ha Hix Hrq4c; lia end])).
m_run_keptG HFr AG (fun a : Z => (m_ZsP F r a \/ tb <= a < tb + 48) \/ dn + 4 * ix <= a < dn + 4 * ix + 4) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HB719 : bv_unsigned (ew Ex 719) = dn + 4 * ix) by (rewrite ?ew_ewset_other by lia; rewrite E719c; apply unsigned_lit_small; clear - Hdcell_rng C1; lia);
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 0 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 719%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (rg_field_of_region_any Ex _ 719 (dn + 4 * ix) cs lo hi wlo whi 0 4%N (SExt true 32 (SOff 761 0)) HRc HB719 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vnew;
change (bv_unsigned (sv_denot Ex (SExt true 32 (SOff 761 0)))) with (U Ex (SExt true 32 (SOff 761 0))) in Vnew; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Vnew;
rewrite (U_sext32_low Ex 761 fv ltac:(rewrite ?ew_ewset_other by lia; exact E761) Hfv32) in Vnew
end; clear HRc end.
rewrite Z.add_0_r in Vnew. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HKr2 : forall b sz, In (b, sz) lrest -> forall i, 0 <= i < req_size sz -> ~ (dn + 4 * ix <= b + i < dn + 4 * ix + 4) ->
aview trasegs (w_H W3) (ms_mem msX) (b + i) = aview trasegs (w_H W3) (ms_mem ms) (b + i)) end.
{ intros b sz Hb i Hi Hnc. destruct (Hoff3 b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2).
rewrite (UN2 (b + i) Hq1 ltac:(intros [Hz | Hz]; [exact (Hq2 Hz) | exact (Hnc Hz)])). exact (HKr1 b sz Hb i Hi). }
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (tl (tl (ss_mem ssx))) in
pose proof (st_ok_submem trasegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; ga_submem_to) ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
reshok_bx HS 44%nat.
srr_branch_tok tratbl_lib_ok HS SHOK GBspan.
+
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (Rx5 : ew Ex 717 = Z_to_bv 64 ix) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R717);
assert (Rxc : ew Ex 620 = Z_to_bv 64 (ht_cnt Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt) end.
rewrite branch_ltu_U in Hc. rewrite (U_atom_off _ 717 ix 1 Rx5), (U_atom _ 620 _ Rxc) in Hc by (clear - Hix Hcnt0 HT24; lia). apply Z.ltb_lt in Hc. clear Rx5 Rxc.
aj_run_to_tok tratbl_lib_ok HS HJ7 SHOK GBspan 0x8327c.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rx4 : ew Ex 716 = Z_to_bv 64 (3 * ix)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R716);
assert (Rx5 : ew Ex 717 = Z_to_bv 64 ix) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R717);
assert (Rx8 : ew Ex 719 = Z_to_bv 64 (dn + 4 * ix)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R719) end.
rregU HS (20%bv : bv 5) (3 * (ix + 1)) ltac:(rewrite (U_atom_off _ 716 (3 * ix) 3 Rx4) by (clear - Hix Hcnt0 HT24; lia); clear; lia) Q20.
rregU HS (21%bv : bv 5) (ix + 1) ltac:(rewrite (U_atom_off _ 717 ix 1 Rx5) by (clear - Hix Hcnt0 HT24; lia); reflexivity) Q21.
rregU HS (23%bv : bv 5) (dn + 4 * (ix + 1)) ltac:(rewrite (U_atom_off _ 719 (dn + 4 * ix) 4 Rx8) by (clear - Hdcell_rng C1; lia); clear; lia) Q23.
rregU HS (24%bv : bv 5) (dn + 4 * (ix + 1)) ltac:(rewrite (U_atom_off _ 719 (dn + 4 * ix) 4 Rx8) by (clear - Hdcell_rng C1; lia); clear; lia) Q24.
ga_join HS ss_DLH2 800%nat rga_deads_DLH
ltac:(idtac; ga_join_val HS 800%nat 16%nat Q20 E816; ga_join_val HS 800%nat 17%nat Q21 E817; ga_join_val HS 800%nat 18%nat Q23 E818; ga_join_val HS 800%nat 19%nat Q24 E819).
rregU HS (20%bv : bv 5) (3 * (ix + 1)) ltac:(apply (U_atom _ 816 _ E816); clear - Hix Hcnt0 HT24; lia) P20.
rregU HS (21%bv : bv 5) (ix + 1) ltac:(apply (U_atom _ 817 _ E817); clear - Hix Hcnt0 HT24; lia) P21.
rregU HS (23%bv : bv 5) (dn + 4 * (ix + 1)) ltac:(apply (U_atom _ 818 _ E818); clear - Hdcell_rng C1; lia) P23.
rregU HS (24%bv : bv 5) (dn + 4 * (ix + 1)) ltac:(apply (U_atom _ 819 _ E819); clear - Hdcell_rng C1; lia) P24.
m_join_win HS ss_DLH 700%nat rga_deads_DLH
ltac:(idtac; ga_join_val HS 700%nat 16%nat P20 E716; ga_join_val HS 700%nat 17%nat P21 E717; ga_join_val HS 700%nat 18%nat P23 E718; ga_join_val HS 700%nat 19%nat P24 E719).
assert (Hfrs7' : frames S3 = (7, fpos) :: frames S) by (exact Hfrs3).
m_hand_ih IH HS HJ7 (k + 0); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, (ix + 1), Ht, ent. split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Tfq | exact Afq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Thh | exact Ahh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Tuu | exact Auu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Tpp | exact App]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Txx | exact Axx]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rdn | split; [exact Tdn | exact Adn]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rha|].
split; [exact Hha|].
split. { lazymatch type of UN3 with forall a, _ -> _ -> aview _ _ ?mF a = aview _ _ ?mP a =>
apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms) mF fq hh uu pp xx Ht (conj Af (conj Ak (conj Au (conj Ap Ax)))) L1 L2 L3 L4 L5) end.
intros b sz Hb i Hi.
assert (Hsz : 0 <= sz) by (clear - Hi; lia). pose proof (req_size_pos sz Hsz) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
rewrite (UN3 (b + i) Hq1 Hq2). apply (HKr2 b sz (Hcht_l b sz Hb) i ltac:(clear - Hi Hrqb; lia)).
pose proof (HzA_dn b sz Hb) as Dz. clear - Dz Hi Hrqb Hix Hrq4c. lia. }
split; [exact Hinv|]. split; [exact HTch|]. split; [exact Hsum|].
split; [exists av; split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rav | exact Hav]|].
split; [exact Hcnt|]. split; [clear - Hix Hc; lia|]. split; [clear - Hnix; lia|].
split; [exact E716|]. split; [exact E717|]. split; [exact E718|]. split; [exact E719|].
intros j Hj. destruct (Z.eq_dec j ix) as [-> | Hne].
* rewrite Hfvx. intros q Hq. pose proof (Vnew q Hq) as Vq. change (N.to_nat 4) with 4%nat in Vq.
destruct (Hoff3 dn _ Hdn_l (dn + 4 * ix + Z.of_nat q) ltac:(clear - Hq Hix Hrq4c; lia)) as (Hq1 & Hq2).
rewrite <- Vq. apply (mbyte_of_aview trasegs). exact (UN3 _ Hq1 Hq2).
* intros q Hq. pose proof (Hdense1 j ltac:(clear - Hj Hne; lia) q Hq) as Vq. rewrite <- Vq. apply (mbyte_of_aview trasegs).
destruct (Hoff3 dn _ Hdn_l (dn + 4 * j + Z.of_nat q) ltac:(clear - Hq Hj Hix Hrq4c; lia)) as (Hq1 & Hq2).
rewrite (UN3 _ Hq1 Hq2). replace (dn + 4 * j + Z.of_nat q) with (dn + (4 * j + Z.of_nat q)) by (clear; lia).
apply (HKr2 dn _ Hdn_l (4 * j + Z.of_nat q) ltac:(clear - Hq Hj Hix Hrq4c; lia)). clear - Hq Hj Hne. lia.
+
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (Rx5 : ew Ex 717 = Z_to_bv 64 ix) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R717);
assert (Rxc : ew Ex 620 = Z_to_bv 64 (ht_cnt Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt) end.
rewrite branch_ltu_U in Hc. rewrite (U_atom_off _ 717 ix 1 Rx5), (U_atom _ 620 _ Rxc) in Hc by (clear - Hix Hcnt0 HT24; lia). apply Z.ltb_ge in Hc. clear Rx5 Rxc.
aj_run_to_tok tratbl_lib_ok HS HJ7 SHOK GBspan 0x83540.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
assert (Hfrs7' : frames S3 = (7, fpos) :: frames S) by (exact Hfrs3).
rga_hand RCR HS HJ7 (k + 0); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, Ht, ent. split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Tfq | exact Afq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Thh | exact Ahh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Tuu | exact Auu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Tpp | exact App]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Txx | exact Axx]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rdn | split; [exact Tdn | exact Adn]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rha|].
split; [exact Hha|].
split. { lazymatch type of UN3 with forall a, _ -> _ -> aview _ _ ?mF a = aview _ _ ?mP a =>
apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms) mF fq hh uu pp xx Ht (conj Af (conj Ak (conj Au (conj Ap Ax)))) L1 L2 L3 L4 L5) end.
intros b sz Hb i Hi.
assert (Hsz : 0 <= sz) by (clear - Hi; lia). pose proof (req_size_pos sz Hsz) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
rewrite (UN3 (b + i) Hq1 Hq2). apply (HKr2 b sz (Hcht_l b sz Hb) i ltac:(clear - Hi Hrqb; lia)).
pose proof (HzA_dn b sz Hb) as Dz. clear - Dz Hi Hrqb Hix Hrq4c. lia. }
split; [exact Hinv|]. split; [exact HTch|]. split; [exact Hsum|].
split; [exists av; split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rav | exact Hav]|].
split; [exact Hcnt|].
assert (Hlast : ht_cnt Ht = ix + 1) by (clear - Hc Hix; lia). rewrite Hlast.
intros j Hj. destruct (Z.eq_dec j ix) as [-> | Hne].
* rewrite Hfvx. intros q Hq. pose proof (Vnew q Hq) as Vq. change (N.to_nat 4) with 4%nat in Vq.
destruct (Hoff3 dn _ Hdn_l (dn + 4 * ix + Z.of_nat q) ltac:(clear - Hq Hix Hrq4c; lia)) as (Hq1 & Hq2).
rewrite <- Vq. apply (mbyte_of_aview trasegs). exact (UN3 _ Hq1 Hq2).
* intros q Hq. pose proof (Hdense1 j ltac:(clear - Hj Hne; lia) q Hq) as Vq. rewrite <- Vq. apply (mbyte_of_aview trasegs).
destruct (Hoff3 dn _ Hdn_l (dn + 4 * j + Z.of_nat q) ltac:(clear - Hq Hj Hix Hrq4c; lia)) as (Hq1 & Hq2).
rewrite (UN3 _ Hq1 Hq2). replace (dn + 4 * j + Z.of_nat q) with (dn + (4 * j + Z.of_nat q)) by (clear; lia).
apply (HKr2 dn _ Hdn_l (4 * j + Z.of_nat q) ltac:(clear - Hq Hj Hix Hrq4c; lia)). clear - Hq Hj Hne. lia.
Qed.
Lemma rga_DL : rga_fromA B ss_CR0 (fun _ => INV_CR0 B) -> rga_from B ss_DL0 (INV_DL0 B).
Proof.
intros RCR. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & Ht & ent & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Rcnt & RT & Rha & Hha & Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & Hcnt).
destruct Hk0 as [Hk0 Hbud].
unfold ss_DL0 in HS.
pose proof Hinv as (_ & (Hcnt0 & _) & _).
assert (HT24 : 0 < ht_T Ht <= 16777216) by (clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia).
assert (Hdn_in3 : In (dn, 4 * ht_cnt Ht) (ablocks B ly3 S3))
by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ dn (4 * ht_cnt Ht) HAR3 Hdn_in3) as (Hdn4096 & _ & Hdnceil & _).
pose proof (req_size_pos (4 * ht_cnt Ht) ltac:(clear - Hcnt0; lia)) as Hrq4c.
rregU HS (20%bv : bv 5) (3 * 0) ltac:(reflexivity) Q20.
rregU HS (21%bv : bv 5) 0 ltac:(reflexivity) Q21.
rregU HS (23%bv : bv 5) (dn + 4 * 0) ltac:(rewrite (U_atom _ 626 dn Rdn) by (clear - Hdn4096 Hdnceil Hrq4c C1; lia); clear; lia) Q23.
rregU HS (24%bv : bv 5) (dn + 4 * 0) ltac:(rewrite (U_atom _ 626 dn Rdn) by (clear - Hdn4096 Hdnceil Hrq4c C1; lia); clear; lia) Q24.
ga_join HS ss_DLH 700%nat rga_deads_DLH
ltac:(idtac; ga_join_val HS 700%nat 16%nat Q20 E716; ga_join_val HS 700%nat 17%nat Q21 E717; ga_join_val HS 700%nat 18%nat Q23 E718; ga_join_val HS 700%nat 19%nat Q24 E719).
pose proof (rga_DL_loop RCR (Z.to_nat (ht_cnt Ht))) as LOOP.
m_hand_ih LOOP HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, 0, Ht, ent. split; [split; [exact Hk0 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm3|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Tfq | exact Afq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Thh | exact Ahh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Tuu | exact Auu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Tpp | exact App]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Txx | exact Axx]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rdn | split; [exact Tdn | exact Adn]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rha|].
split; [exact Hha|]. split; [exact Harr|]. split; [exact Hinv|]. split; [exact HTch|]. split; [exact Hsum|].
split; [exists av; split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rav | exact Hav]|].
split; [exact Hcnt|]. split; [clear - Hcnt; lia|]. split; [rewrite Z2Nat.id by (clear - Hcnt0; lia); clear; lia|].
split; [exact E716|]. split; [exact E717|]. split; [exact E718|]. split; [exact E719|].
intros j Hj. exfalso. clear - Hj. lia.
Qed.
End f.
End d.
