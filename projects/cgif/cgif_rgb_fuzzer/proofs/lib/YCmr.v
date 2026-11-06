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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCoi YCoj YCok YCn9 YCol YCo5 YCo4 YCo7.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCqh YCo8.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis COLHASH : tcolhash_spec B.
Hypothesis ABCMP : abcmp_realizes trbsegs B A_bcmp_tra.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_SM_head : forall n, rga_from B ss_SMC (INV_SM B (S n)) -> rga_from B ss_SMSe (INV_SM B (S n)) -> rga_from B ss_SMH (INV_SM B (S n)).
Proof.
intros n RSMC RSMS.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & Hcnt & Hix & Hnix & R715 & R716 & R717 & R718 & R719).
destruct Hk0 as [Hk0 Hbud].
unfold ss_SMH in HS.
change CHT_SIZE with 48 in *.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hrin]).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
pose proof Hwf as Hwf0. destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x814c8 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
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
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x83588.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN0.
clear HF HFr HG.
norm_ss HS.
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
+
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x835d4.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) _ fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5). intros b sz Hb i Hi.
pose proof (req_size_pos sz (Hcht_sz b sz Hb)) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
rewrite (UN1 (b + i) Hq1 Hq2). exact (UN0 (b + i) Hq1 Hq2). }
ga_join HS ss_SMC 740%nat rga_deads_SMC ltac:(idtac).
m_hand_ih RSMC HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent. m_inv_auto.
+
destruct (Z.eq_dec bef 0) as [Hb0 | Hb0]; [exfalso; rewrite Hb0 in E41; rewrite (m_s11_nobef E 604 41 E41) in Hc; discriminate|].
destruct Hbef as [Hq | Hbf]; [exfalso; exact (Hb0 Hq)|].
specialize (R717 Hb0).
assert (Himg_l : In (img, fmt * N) lrest)
by (subst lrest; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; unfold timg_block; clear - Hfmt; destruct Hfmt as [-> | ->]; left; reflexivity).
assert (Hbef_l : In (bef, beffmt * N) lrest)
by (subst lrest; apply in_or_app; left; apply in_or_app; left; apply in_or_app; right; unfold optb; rewrite (proj2 (Z.eqb_neq bef 0) Hb0); left; reflexivity).
assert (Himg_in3 : In (img, fmt * N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Himg_l]).
assert (Hbef_in3 : In (bef, beffmt * N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hbef_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ img (fmt * N) HAR3 Himg_in3) as (Himg4096 & _ & Himgceil & _).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ bef (beffmt * N) HAR3 Hbef_in3) as (Hbef4096 & _ & Hbefceil & _).
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as HrqfN.
assert (HbN : 3 <= beffmt * N <= 4 * RGB_NMAX) by (clear - Hbf HN1 HN; unfold RGB_NMAX in *; nia).
pose proof (req_size_pos (beffmt * N) ltac:(clear - HbN; lia)) as HrqbN.
assert (Hpx : 0 <= fmt * ix < 2 ^ 31 /\ fmt * ix + fmt <= fmt * N /\ fmt * N < 2 ^ 31) by (clear - Hfmt Hix HN; unfold RGB_NMAX in HN; nia).
assert (Hpy : 0 <= beffmt * ix < 2 ^ 31 /\ beffmt * ix + 3 <= beffmt * N /\ beffmt * N < 2 ^ 31) by (clear - Hbf Hix HN; unfold RGB_NMAX in HN; nia).
assert (HU45 : U E (SOff 45 0) = img) by (apply (U_atom _ 45 img E45); clear - Himg4096 Himgceil HrqfN C1; lia).
assert (HU41 : U E (SOff 41 0) = bef) by (apply (U_atom _ 41 bef E41); clear - Hbef4096 Hbefceil HrqbN C1; lia).
assert (HUs6 : U E (SAlu ALU_ADD (SOff 45 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 718 0) (SLit 32)) (SLit 32))) = img + fmt * ix)
by (apply U_add_small_q; [exact HU45 | apply U_zext32_shifts; [apply (U_atom _ 718 (fmt * ix) R716); clear - Hpx; lia | clear - Hpx; lia]
| clear - Himg4096; lia | clear - Hpx; lia | clear - Himgceil HrqfN Hpx C1; lia]).
assert (HUbz : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 719 0) (SLit 32)) (SLit 32)) = beffmt * ix) by (apply U_zext32_shifts; [apply (U_atom _ 719 (beffmt * ix) R717); clear - Hpy; lia | clear - Hpy; lia]).
m_add_cond HS BC_GEU (SAlu ALU_ADD (SOff 45 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 718 0) (SLit 32)) (SLit 32))) (SOff 45 0) ltac:(eapply (ub_geu_cond _ _ _ _ _ HUs6 HU45); clear - Hpx; lia).
m_add_cond HS BC_NE (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 45 0)) (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 45 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 718 0) (SLit 32)) (SLit 32))) (SLit 1))) (SLit 0)
ltac:(eapply (ub_nz2_cond _ _ _ _ _ HU45 HUs6); [clear - Himg4096; lia | clear - Himg4096 Hpx; lia]).
m_add_cond HS BC_GEU (SAlu ALU_XOR (SOff 41 0) (SLit (-1))) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 719 0) (SLit 32)) (SLit 32))
ltac:(eapply (ub_room_cond _ _ _ _ _ HU41 HUbz); [clear - Hbef4096 Hbefceil HrqbN C1; lia | clear - Hpy; lia | clear - Hbefceil HrqbN Hpy C1; lia]).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_bcmp_tra.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) (img + fmt * ix)
ltac:(apply m_U_add0; apply U_add_small_q; [apply (U_atom _ 45 img E45); clear - Himg4096 Himgceil HrqfN C1; lia
| apply U_zext32_shifts; [apply (U_atom _ 718 (fmt * ix) R716); clear - Hpx; lia | clear - Hpx; lia]
| clear - Himg4096; lia | clear - Hpx; lia | clear - Himgceil HrqfN Hpx C1; lia]) Ha0.
rregU HS (11%bv : bv 5) (bef + beffmt * ix)
ltac:(apply U_add_small_q; [apply (U_atom _ 41 bef E41); clear - Hbef4096 Hbefceil HrqbN C1; lia
| apply U_zext32_shifts; [apply (U_atom _ 719 (beffmt * ix) R717); clear - Hpy; lia | clear - Hpy; lia]
| clear - Hbef4096; lia | clear - Hpy; lia | clear - Hbefceil HrqbN Hpy C1; lia]) Ha1.
rregU HS (12%bv : bv 5) 3 ltac:(reflexivity) Ha2.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img (fmt * N) (proj1 HJ3) Himg_in3) as (_ & _ & _ & _ & HimgP & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bef (beffmt * N) (proj1 HJ3) Hbef_in3) as (_ & _ & _ & _ & HbefP & _).
assert (HWIN : forall a, 0 <= a < alloc_ceiling -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs + -576 - 2 * ESTACK <= a < spZ regs + -576))
by (intros a Ha; rewrite Hes; clear - Ha Hceil Hslo FFS C1; lia).
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_bcmp_at trbsegs B LAWS Hsegs A_bcmp_tra ABCMP W3 (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 mdX k (img + fmt * ix) (bef + beffmt * ix) 3 (-576) (Z_to_bv 64 0x835cc) HJ3) end.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- clear; lia.
- clear - Himg4096 Hpx; lia.
- clear - Himgceil HrqfN Hpx C1; lia.
- clear - Hbef4096 Hpy; lia.
- clear - Hbefceil HrqbN Hpy C1; lia.
- exact HspT.
- reflexivity.
- clear; lia.
- rewrite FFS, Hes. clear. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even; vm_compute; reflexivity.
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (proj1 (HimgP a ltac:(clear - Ha Hpx HrqfN Hfmt; lia)))|].
intros Hw. rewrite HspT, Hes in Hw. clear - Hw Ha Himgceil HrqfN Hpx Hfmt Hceil Hslo FFS C1. lia.
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (proj1 (HbefP a ltac:(clear - Ha Hpy HrqbN; lia)))|].
intros Hw. rewrite HspT, Hes in Hw. clear - Hw Ha Hbefceil HrqbN Hpy Hceil Hslo FFS C1. lia.
- intros a Ha. apply (HWIN a). clear - Ha Himg4096 Himgceil HrqfN Hpx Hfmt. lia.
- intros a Ha. apply (HWIN a). clear - Ha Hbef4096 Hbefceil HrqbN Hpy. lia.
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 W3 _ _ img (fmt * N) _ _ (proj1 HJ3) Himg_in3); clear - Hpx HrqfN Hfmt; lia.
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 W3 _ _ bef (beffmt * N) _ _ (proj1 HJ3) Hbef_in3); clear - Hpy HrqbN; lia.
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 W3 _ _ img (fmt * N) _ _ (proj1 HJ3) Himg_in3); clear - Hpx HrqfN Hfmt; lia.
- intros _; apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 W3 _ _ img (fmt * N) _ _ (proj1 HJ3) Himg_in3); clear - Hpx HrqfN Hfmt; lia.
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 W3 _ _ bef (beffmt * N) _ _ (proj1 HJ3) Hbef_in3); clear - Hpy HrqbN; lia.
- intros _; apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 W3 _ _ bef (beffmt * N) _ _ (proj1 HJ3) Hbef_in3); clear - Hpy HrqbN; lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
clear Ha0 Ha1 Ha2 Rra Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
ga_aconsts HROD HJ2 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (HWST : forall a, spZ regs + -576 <= a < spZ regs + 0 -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs + -576 - 2 * ESTACK <= a < spZ regs + -576))
by (intros a Ha; rewrite Hes; clear - Ha Hceil Hslo Hshi H47 FFS C1; lia).
assert (HRNG : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17592186044416) /\ (4096 <= r /\ r + 64 <= alloc_ceiling) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling) /\ 140735332483072 <= alloc_ceiling <= 140737479966720)
by (clear - HF4096 HFceil HF8lo HF8hi Hr4096 Hrceil Hf4096 Hfceil Hflo Hfhi C1; lia).
assert (HRtb : 4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG
ltac:(idtac; first
[ m_keptW Hfr2 Hpres2 HWIN HWST HRNG AG Usp RF E67 E10n E11n
ltac:(idtac; first [ m_keptW_blk Hfr2 Hpres2 HWIN AG 305%nat tb Rtb HRtb
| ga_kept_consts Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ2 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
norm_ss HS.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK GBspan 0x835d0.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
*
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK GBspan 0x83720.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) _ fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5). intros b sz Hb i Hi.
pose proof (req_size_pos sz (Hcht_sz b sz Hb)) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
assert (Hb3 : In (b, sz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact (Hcht_l b sz Hb)]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ b sz HAR3 Hb3) as (Hb4096 & _ & Hbceil & _).
destruct (HWIN (b + i) ltac:(clear - Hi Hrqb Hb4096 Hbceil; lia)) as (Hw1 & Hw2).
rewrite (UN3 (b + i) Hq1 Hq2), (UN2 (b + i) Hq1 Hq2), (Hfr2 (b + i) Hw1 Hw2), (UN1 (b + i) Hq1 Hq2). exact (UN0 (b + i) Hq1 Hq2). }
ga_join HS ss_SMSe 790%nat rga_deads_SMSe ltac:(idtac).
m_hand_ih RSMS HS HJ2 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent. m_inv_auto.
*
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK GBspan 0x835d4.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) _ fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5). intros b sz Hb i Hi.
pose proof (req_size_pos sz (Hcht_sz b sz Hb)) as [_ Hrqb].
destruct (Hoff3 b sz (Hcht_l b sz Hb) (b + i) ltac:(clear - Hi Hrqb; lia)) as (Hq1 & Hq2).
assert (Hb3 : In (b, sz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact (Hcht_l b sz Hb)]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ b sz HAR3 Hb3) as (Hb4096 & _ & Hbceil & _).
destruct (HWIN (b + i) ltac:(clear - Hi Hrqb Hb4096 Hbceil; lia)) as (Hw1 & Hw2).
rewrite (UN3 (b + i) Hq1 Hq2), (UN2 (b + i) Hq1 Hq2), (Hfr2 (b + i) Hw1 Hw2), (UN1 (b + i) Hq1 Hq2). exact (UN0 (b + i) Hq1 Hq2). }
ga_join HS ss_SMC 740%nat rga_deads_SMC ltac:(idtac).
m_hand_ih RSMC HS HJ2 k; [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent. m_inv_auto.
Qed.
End d.
End c.
