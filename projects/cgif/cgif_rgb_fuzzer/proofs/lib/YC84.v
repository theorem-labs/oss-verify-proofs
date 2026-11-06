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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i YC8j YC8k YC8l YC8m YC9t YC9u YC9v YC8n YC8o YC9w YC9g YC9i YC9j YC9h YC9l YC9m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC4b.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis COLHASH : tcolhash_spec B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_SMT1 : rga_fromA B ss_SMTa (fun _ => INV_SMTa B) -> rga_from B ss_SMT (INV_SMT B).
Proof.
intros RC.
rga_prelude. unfold INV_SMT, INV_HDx in HINV. rga_cbn_cx HINV.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & Ht & ent & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & Hcnt).
destruct Hk0 as [Hk0 Hbud].
unfold ss_SMT in HS.
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
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK GBspan A_asan_memcpy.
all: try (unfold GBx; ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN0.
clear HF HFr HG.
norm_ss HS.
ga_ra_frame HS AG HFq F 532 532 96 HRApal.
assert (Hpp_l : In (pp, 3 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
assert (Hpp_in3 : In (pp, 3 * ht_T Ht) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hpp_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) HAR3 Hpp_in3) as (Hpp4096 & _ & Hppceil & _).
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as Hrq3T.
assert (HT768 : 768 <= 3 * ht_T Ht) by (clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp (3 * ht_T Ht) (proj1 HJ3) Hpp_in3) as (_ & _ & _ & _ & HppP & _).
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) 7 fpos HAR3 Hpp_in3 Hfin3) as HdF_pp.
unfold zdisjoint in HdF_pp. cbn [fst snd] in HdF_pp. change (fs_frame_bytes 7) with 8192 in HdF_pp. rewrite EFA3 in HdF_pp. fold F in HdF_pp.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) (F + 4256) ltac:(rewrite (U_atom_off _ 54 F 4256) by first [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RF | clear - HF4096 HFceil C1; lia]; reflexivity) Ha0.
rregU HS (11%bv : bv 5) pp ltac:(apply (U_atom _ 618 pp); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | clear - Hpp4096 Hppceil Hrq3T C1; lia]) Ha1.
rregU HS (12%bv : bv 5) 768 ltac:(reflexivity) Ha2.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT : spZ rg = spZ regs + -512) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335280) with (Z_to_bv 64 A_asan_memcpy).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W3 (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k (F + 4256) pp 768 (-512) (Z_to_bv 64 0x83508) HJ3) end.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- clear; lia.
- clear - HF4096; lia.
- clear - HFceil C1; lia.
- exact HspT.
- reflexivity.
- clear; lia.
- rewrite FFS, Hes. clear. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even; vm_compute; reflexivity.
- intros a Ha. split; [| rewrite Hes; clear - Ha HFceil Hceil Hslo FFS; lia]. right. right. right. exists 7, fpos. split; [left; reflexivity|]. left.
unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 7) with 8192. rewrite ?EFA3. fold F. clear - Ha. lia.
- apply amem_range_high; [clear; lia | unfold gbox in HFhigh; destruct HFhigh as [_ HFz]; unfold kLowShadowBeg, kHighMemBeg in HFz; clear - HFz; lia | clear - HFceil; lia].
- replace (F + 4256) with (F + 8 * 532) by (clear; lia). replace 768 with (8 * 96) by (clear; lia). exact HRApal.
- intros _. eapply (shadow_hull_vis_of_frame trasegs B LAWS ly3 S3 _ _ _ 7 fpos (F + 4256) 768 (proj1 HJ3) Hfin3);
[rewrite ?EFA3; fold F; clear; lia | rewrite ?EFA3; fold F; change (fs_frame_bytes 7) with 8192; clear; lia | clear; lia].
- split; [clear - Hpp4096; lia|]. split; [clear - Hppceil Hrq3T HT768 C1; lia|]. split.
{ intros a Ha. split; [apply (aview_some_of_apresent trasegs); exact (proj1 (HppP a ltac:(clear - Ha Hrq3T HT768; lia)))
| rewrite HspT, Hes; clear - Ha Hppceil Hrq3T HT768 Hceil Hslo FFS; lia]. }
split; [clear - HdF_pp Hrq3T HT768; lia|]. split.
{ apply (amem_range_of_block trasegs B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) pp 768 (proj1 HJ3) Hpp_in3); [clear; lia | clear - Hrq3T HT768; lia]. }
split; [apply (range_addressable_of_block trasegs B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) pp 768 (proj1 HJ3) Hpp_in3); [clear; lia | clear - Hrq3T HT768; lia]|].
intros _. apply (shadow_hull_vis_of_block trasegs B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) pp 768 (proj1 HJ3) Hpp_in3); [clear; lia | clear - Hrq3T HT768; lia | clear; lia]. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Ha06 & Heff6 & Hfr6 & Hpres6).
clear Ha0 Ha1 Ha2 Rra Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
ga_aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
assert (Hfr2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 4256 <= a < F + 4256 + 768 \/ spZ regs + -512 - ESTACK <= a < spZ regs + -512) ->
aview trasegs (w_H W3) mem6 a = aview trasegs (w_H W3) (ms_mem ms) a)
by (intros a Ha1 Ha2; apply Hfr6; [exact Ha1 | intros Hq; apply Ha2; left; exact Hq | intros Hq; apply Ha2; right; exact Hq]).
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ r 64 7 fpos HAR3 Hrin3 Hfin3) as HdF_r.
unfold zdisjoint in HdF_r. cbn [fst snd] in HdF_r. change (fs_frame_bytes 7) with 8192 in HdF_r. change (req_size 64) with 64 in HdF_r. rewrite EFA3 in HdF_r. fold F in HdF_r.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ tb 48 7 fpos HAR3 Htb_in3 Hfin3) as HdF_tb.
unfold zdisjoint in HdF_tb. cbn [fst snd] in HdF_tb. change (fs_frame_bytes 7) with 8192 in HdF_tb. change (req_size 48) with 48 in HdF_tb. rewrite EFA3 in HdF_tb. fold F in HdF_tb.
assert (HWIN : forall a, 0 <= a < alloc_ceiling -> ~ (F + 4256 <= a < F + 4256 + 768) ->
0 <= a < 2 ^ 64 /\ ~ (F + 4256 <= a < F + 4256 + 768 \/ spZ regs + -512 - ESTACK <= a < spZ regs + -512))
by (intros a Ha Hnd; rewrite Hes; clear - Ha Hnd Hceil Hslo FFS C1; lia).
assert (HWST : forall a, spZ regs + -512 <= a < spZ regs + 0 -> 0 <= a < 2 ^ 64 /\ ~ (F + 4256 <= a < F + 4256 + 768 \/ spZ regs + -512 - ESTACK <= a < spZ regs + -512))
by (intros a Ha; rewrite Hes; clear - Ha HFceil Hceil Hslo Hshi H47 FFS C1; lia).
assert (HRNG : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (F + 8192 <= 2147446784 \/ 17594333495296 <= F)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (r + 64 <= F \/ F + 8192 <= r)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (cfp + 24 <= F \/ F + 8192 <= cfp)) /\ 140735332483072 <= alloc_ceiling <= 140737479966720).
{ unfold gbox in HFhigh, HdFC. destruct HFhigh as [_ HFz]. unfold kLowShadowBeg, kHighMemBeg in HFz.
clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HFz Hr4096 Hrceil HdF_r Hf4096 Hfceil Hflo Hfhi HdFC C1. lia. }
assert (HRtb : 4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ (tb + 48 <= F \/ F + 8192 <= tb)) by (clear - Htb4096 Htbceil Hrqtb HdF_tb C1; lia).
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG
ltac:(idtac; first
[ m_keptW Hfr2 Hpres6 HWIN HWST HRNG AG Usp RF E67 E10n E11n
ltac:(idtac; first [ m_keptW_blk Hfr2 Hpres6 HWIN AG 305%nat tb Rtb HRtb
| ga_kept_consts Kgot0 Kgot6 Kcell0 Kcell6 Kguar0 Kguar6 Kuar0 Kuar6 Vgr0 Vgr6 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot6 into Kgot0. rename Kcell6 into Kcell0. rename Kguar6 into Kguar0. rename Kuar6 into Kuar0. rename Vgr6 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ6 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE6 end.
norm_ss HS.
reshok_bx HS 44%nat.
aj_run_to_tok tratbl_lib_ok HS HJ6 SHOK GBspan A_free_col_hash_table.
all: try (unfold GBx; ga_obl_blk HJ6 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
ga_join0 HS ss_SMTa.
rga_hand RC HS HJ6 k; [rga_E_tac HEE6 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, (ht_T Ht), (ht_cnt Ht).
split; [split; [unfold EV_HD, EV_FREECHT, EV_RGBADD in *; clear - Hk0; lia | rga_bud_tac Hbud]|].
split; [exact Hfmt|]. split; [clear - HT24; lia|]. split; [exact HPm3|].
split; [split; [m_ewT | split; [exact Tblk | exact Ablk]]|].
split; [split; [m_ewT | split; [exact Tfim | exact Afim]]|].
split; [split; [m_ewT | split; [exact Ttb | exact Atb]]|].
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT | exact Hcnt].
Qed.
End d.
End c.
