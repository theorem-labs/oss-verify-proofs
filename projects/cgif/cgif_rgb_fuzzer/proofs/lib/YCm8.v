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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YCq5 YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCnd YCnm YCni YCnb YCoh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCqk.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis NTN2 : tntn_spec2V B.
Hypothesis ASS00 : forall fy : YK11.FPState, @aset_shadow_realizes fy rc trbsegs B A_set_shadow_00 0.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_CR1 : rga_fromA B ss_XD (fun _ => INV_XD B) -> (forall n, rga_fromA B ss_CL (fun _ => INV_CL B n)) -> rga_from B ss_CR0 (INV_CR0 B).
Proof.
intros RXD RCL.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & Ht & ent & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Rcnt & RT & Rha & Hha & Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & Hcnt & Hdense).
destruct Hk0 as [Hk0 Hbud].
unfold ss_CR0 in HS.
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
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_new_tree_node.
all: try (unfold GBx; ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN0.
clear HF HFr HG.
norm_ss HS.
destruct (inv_cnt Ht ent Hinv) as [Hlen_ent _].
pose proof (m_ent_ok Ht ent Hinv) as HentOk.
pose proof (ent_NoDup Ht ent Hinv) as HentND.
pose proof (m_pal_agrees Ht ent Hinv) as Hpag.
assert (Hsum' : zsum (fr_vals ent) <= N) by (exact Hsum).
assert (Hcnt10000 : ht_cnt Ht <= 10000) by (pose proof (zsum_ge_length ent (ent_freq_pos Ht ent Hinv)) as Hz; clear - Hz Hlen_ent Hsum HN; unfold RGB_NMAX in HN; lia).
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
assert (Hcht_sz : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> 0 <= sz)
by (intros b sz Hb; cbn [cht_blocks In] in Hb; clear - Hb HT24; destruct Hb as [Hq | [Hq | [Hq | [Hq | [Hq | []]]]]]; injection Hq as _ <-; lia).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HKr0 : forall b sz, In (b, sz) lrest -> rg_blk_kept (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem msX) b (req_size sz)) end.
{ intros b sz Hb i Hi. destruct (Hoff3 b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2). apply UN0; assumption. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Harr1 : cht_arrays trbsegs (mrestrict (w_H W3) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W3) (w_H W3) (ms_mem ms3) _ fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5). intros b sz Hb.
apply (rg_blk_kept_sub _ _ _ _ b (req_size sz)); [exact (HKr0 b sz (Hcht_l b sz Hb)) | clear; lia | pose proof (req_size_pos sz (Hcht_sz b sz Hb)); lia]. }
pose proof (req_size_pos (4 * ht_cnt Ht) ltac:(clear - Hcnt0; lia)) as Hrq4c.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Hdense1 : arr32 trbsegs (mrestrict (w_H W3) (ms_mem msX)) dn (fr_vals ent)) end.
{ apply m_arr32_of_vals.
- intros j Hj. unfold fr_vals in Hj |- *. unfold zlen in Hj. rewrite length_map in Hj. fold (elen ent) in Hj. rewrite Hlen_ent in Hj.
apply (rg_val_mem_blk_kept (w_H W3) (w_H W3) (ms_mem ms3) _ dn (req_size (4 * ht_cnt Ht)) (dn + 4 * j) 4 _ (Hdense j Hj) (HKr0 dn _ Hdn_l)); [clear - Hj; lia | clear - Hj Hrq4c; cbn; lia].
- intros j Hj. unfold zlen, fr_vals in Hj. rewrite length_map in Hj. fold (elen ent) in Hj.
pose proof (m_fr_bounds ent N j HentOk Hsum' Hj) as Hb. clear - Hb HN. unfold RGB_NMAX in HN. lia. }
assert (HB2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
assert (HB2x : bv_unsigned (ew Ex 2) = spZ regs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact HB2);
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W3) msX) 8 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-134) 2%N (SLit 0) 0 HRc HB2x ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnln
end; clear HRc end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnln.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (map (fun r0 => if YQ0b.obase_eqb (YQ0b.r_base r0) (Some 2%nat)
then YQ0b.mkRegion (YQ0b.r_base r0) (YQ0b.r_lo r0) (YQ0b.r_hi r0) (YQ0b.r_wlo r0) (YQ0b.r_whi r0)
(filter (fun c => negb (Z.eqb (YQ0b.c_off c) (-134))) (YQ0b.r_chunks r0))
else r0) (ss_mem ssx)) in
pose proof (st_ok_submem trbsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; ga_submem_to) ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
assert (Hpp_l : In (pp, 3 * ht_T Ht) lrest) by (apply Hcht_l; cbn [cht_blocks In]; tauto).
assert (Hpp_in3 : In (pp, 3 * ht_T Ht) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hpp_l]).
assert (Hdn_in3 : In (dn, 4 * ht_cnt Ht) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hdn_l]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ pp (3 * ht_T Ht) HAR3 Hpp_in3) as (Hpp4096 & _ & Hppceil & _).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ dn (4 * ht_cnt Ht) HAR3 Hdn_in3) as (Hdn4096 & _ & Hdnceil & Hdn16).
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as Hrq3T.
assert (Hpd : pp + req_size (3 * ht_T Ht) <= dn \/ dn + req_size (4 * ht_cnt Ht) <= pp).
{ assert (HPx : Permutation (ablocks B ly3 S3) (cht_blocks fq hh uu pp xx (ht_T Ht) ++ ((dn, 4 * ht_cnt Ht) :: (r, RGB_SIZE) :: (tb, 48) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)])))
by (eapply Permutation_trans; [exact HPrt3|]; subst lrest; YI0g.perm_tac).
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (pp, 3 * ht_T Ht) (dn, 4 * ht_cnt Ht) HAR3 HPx ltac:(cbn [cht_blocks In]; tauto) ltac:(left; reflexivity)) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. exact Dd. }
destruct Harr1 as (Af & Ak & Au & Ap & Ax).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregU HS (10%bv : bv 5) pp ltac:(apply (U_atom _ 618 pp); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | clear - Hpp4096 Hppceil Hrq3T C1; lia]) Ha0.
rregU HS (11%bv : bv 5) dn ltac:(apply (U_atom _ 626 dn); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rdn | clear - Hdn4096 Hdnceil Hrq4c C1; lia]) Ha1.
rregU HS (12%bv : bv 5) (spZ regs - 134) ltac:(rewrite (U_atom_off _ 2 (spZ regs) (-134)) by first [exact HB2x | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite (AG 2%nat) by lia; rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned | clear - Hceil Hslo Hshi H47 FFS C1; lia]; clear; lia) Ha2.
rregU HS (13%bv : bv 5) 0 ltac:(reflexivity) Ha3.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rc' : ew Ex 620 = Z_to_bv 64 (ht_cnt Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt) end.
m_rregD HS (14%bv : bv 5) (ht_cnt Ht - 1)
ltac:(apply lg_subw1_succ; [replace (ht_cnt Ht - 1 + 1) with (ht_cnt Ht) by (clear; lia); apply lg_denot_of_U; apply (U_sext32_small _ 620 _ Rc'); clear - Hcnt Hcnt10000; lia
| clear - Hcnt Hcnt10000; lia]) Ha4.
rregU HS (15%bv : bv 5) 0 ltac:(reflexivity) Ha5.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
change (Z_to_bv 64 545716) with (Z_to_bv 64 A_new_tree_node).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (NTN2 fx TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
pp dn (spZ regs - 134) 0 (ht_cnt Ht - 1) 0 0 (ht_pal Ht) (fr_vals ent) pp (3 * ht_T Ht) dn (4 * ht_cnt Ht) HJ3) end.
- rewrite Rra. apply ret_ok_even; vm_compute; reflexivity.
- unfold raZ. rewrite Rra, unsigned_lit_small by (clear; lia). clear; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- rewrite HspT. clear - Hal32. pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D. replace (32 * (spZ regs / 32) + -576) with ((2 * (spZ regs / 32) - 36) * 16) by lia. apply Z_mod_mult.
- rewrite HspT, FFS. unfold TNTN_STK, NTN_FRAME, ASTACK. clear. lia.
- rewrite HspT. clear. lia.
- exact Hfrm.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- exact Ha3.
- exact Ha4.
- exact Ha5.
- exact Hpp_in3.
- clear; lia.
- rewrite L5. clear; lia.
- exact Hdn_in3.
- clear; lia.
- unfold fr_vals, zlen. rewrite length_map. fold (elen ent). rewrite Hlen_ent. clear; lia.
- clear - Hdn16. pose proof (Z.div_mod dn 16 ltac:(lia)) as D. rewrite Hdn16, Z.add_0_r in D. rewrite D. replace (16 * (dn / 16)) with ((4 * (dn / 16)) * 4) by lia. apply Z_mod_mult.
- intros Heq. injection Heq as Hq1 Hq2. clear - Hq1 Hpd Hrq3T Hrq4c. lia.
- exact Ap.
- exact Hdense1.
- clear - Hcnt. lia.
- clear - Hcnt10000. lia.
- rewrite L5. clear - Hcnt0. lia.
- unfold fr_vals, zlen. rewrite length_map. fold (elen ent). rewrite Hlen_ent. clear; lia.
- clear; lia.
- intros i Hi. exact (proj1 (m_fr_bounds ent N i HentOk Hsum' ltac:(rewrite Hlen_ent; clear - Hi; lia))).
- rewrite (node_list_dseg (ht_pal Ht) ent 0 (ht_cnt Ht - 1) 0 Hpag) by (rewrite ?Hlen_ent; clear - Hcnt; lia).
pose proof (root_segment ent 0 HentOk ltac:(rewrite Hlen_ent; clear - Hcnt; lia)) as (_ & _ & Rw & _). rewrite Hlen_ent in Rw. rewrite Rw. clear - Hsum' HN. lia.
- rewrite HspT. clear; lia.
- clear; lia.
- clear - Hal32. pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D. replace (32 * (spZ regs / 32) - 134) with (2 + (4 * (spZ regs / 32) - 17) * 8) by lia. rewrite Z_mod_plus_full. reflexivity.
- replace (spZ regs - 134) with (spZ regs + -134) by (clear; lia). exact Vnln.
- clear; lia.
- rga_room Hev Hbud; (try (unfold EV_NTN); clear - Hk0 HEVv; try (unfold EV_HD in Hk0); rga_lia).
- rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPm3), !bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd cht_blocks].
clear - Hlive HfN HN1 HN HT24 Hcnt10000 Hcnt0. unfold LIVE_RGBADD, LIVE_MAX, RGB_NMAX, NODE_SIZE in *. lia. }
cbv beta. intros W7 c7 Hwle7 (fx7 & ly7 & S7 & regs7 & mem7 & md7 & res & -> & Hfrm7 & HJ7 & HP7 & Hfrs7 & Hd7 & Ha07 & HK7 & Hres7).
rewrite Rra.
clear Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Rsp Rgp Rtp Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof HJ7 as (HAR7 & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin7 : In (7, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin3).
assert (HfinS7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact HfinS3).
assert (HBin7 : forall b m, In (b, m) (ablocks B ly3 S3) -> In (b, m) (ablocks B ly7 S7))
by (intros b m Hb; destruct Hres7 as [(_ & -> & _) | (_ & -> & _)]; [exact Hb | apply in_or_app; left; exact Hb]).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA7 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 HAR7 (HBin7 _ _ Hrin3)) as (_ & _ & _ & _ & Hrpres7 & _). change (req_size 64) with 64 in Hrpres7.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 HAR7 (HBin7 _ _ Htb_in3)) as (_ & _ & _ & _ & Htbpres7 & _). change (req_size 48) with 48 in Htbpres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (HRNG : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling) /\ (4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ frame_addr ly cid pos <= cfp /\ cfp + 24 <= frame_addr ly cid pos + fs_frame_bytes cid) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\
spZ (ms_regs ms) = spZ regs + -576 /\ TNTN_STK = 16576 /\ TRGBADD_STK = 25152).
{ split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8; lia|]. split; [clear - Hr4096 Hrceil; lia|]. split; [clear - Hf4096 Hfceil Hflo Hfhi; lia|].
split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; [exact HspT | split; reflexivity]. }
assert (HRtb : 4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs) by (clear - Htb4096 Htbceil Hrqtb Hceil Hslo FFS C1; lia).
assert (HRr : 4096 <= r /\ r + 64 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs) by (clear - Hr4096 Hrceil Hceil Hslo FFS C1; lia).
m_reseatF HS HJ7 fx7 regs7 CLOB 538712 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG (m_same_of_preserved _ _ HP7)
ltac:(idtac; first
[ m_keptE HK7 HJ7 HRNG AG Usp RF E67 E10n E11n Hfin3 HfinS3 EFA3 F (-134) (-132) HFpres7 HFSpres7
ltac:(idtac; first [ m_keptE_blk HK7 AG 305%nat tb 48 Rtb Htb_in3 Htbpres7 HRtb
| m_keptE_blk HK7 AG 10%nat r 64 E10n Hrin3 Hrpres7 HRr
| m_keptE_consts Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
rreg HS (10%bv : bv 5) Rres. cbn [ms_regs] in Rres. rewrite Ha07 in Rres. symmetry in Rres. unfold w64 in Rres.
norm_ss HS.
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
1: {
destruct Hres7 as [(Hz & _) | (Hres4096 & Ebl7 & Vnln7 & nd0 & Hnd_addr & Hnd_imin & Hnd_imax & Hnd_cidx & Hnd_tree & Hnd_wf & Hnd_quot & Hnd_split)];
[exfalso; rewrite YO3v.branch_ne_U in Hc; apply (proj1 (Bool.negb_true_iff _)) in Hc; apply Z.eqb_neq in Hc; apply Hc; rewrite (U_atom _ 767 res Rres) by (clear - Hz; lia); rewrite Hz; reflexivity|].
change (0 + 1) with 1 in Vnln7.
m_add_chunk HS 2%nat (-134) 2%N (SLit 1) (spZ regs) 1
ltac:(repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite (AG 2%nat) by lia; exact Usp)
ltac:(reflexivity) ltac:(cbn; clear; lia) Vnln7.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan A_set_shadow_00.
assert (Htb_in7 : In (tb, 48) (ablocks B ly7 S7)) by (exact (HBin7 _ _ Htb_in3)).
assert (Hrin7 : In (r, 64) (ablocks B ly7 S7)) by (exact (HBin7 _ _ Hrin3)).
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra2.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 348796) with (Z_to_bv 64 A_set_shadow_00).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ7 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
lazymatch type of Rsp with getr ?rg _ = _ => assert (HspT2 : spZ rg = spZ regs + -576) by (unfold spZ; rewrite Rsp; ga_evalE AG) end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_set_shadow_at trbsegs B LAWS Hsegs A_set_shadow_00 0 (ASS00 fx7) W7 (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly7 S7 mdX (k + EV_NTN) 7 fpos (SB + F / 8 + 4) 512 (-576) (Z_to_bv 64 538740) HJ7) end.
- left; reflexivity.
- rewrite Ra0. f_equal. repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]. rewrite E67. rewrite unsigned_lit_small by (unfold SB; clear - HF8lo HF8hi; lia). reflexivity.
- exact Ra1.
- clear; lia.
- rewrite EFA7. fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. unfold SB. clear; lia.
- rewrite EFA7. fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. change (fs_frame_bytes 7 / 8) with 1024. unfold SB. clear; lia.
- exact HspT2.
- reflexivity.
- clear; lia.
- rewrite FFS, Hes. clear; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite ?ew_havoc_old by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra2.
- apply ret_ok_even; vm_compute; reflexivity. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Heff6 & Hfr6 & Hoff6).
clear Ra0 Ra1 Rra2 Rsp Rgp Rtp.
ga_aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos (proj1 HJ6) Hfin7) as (_ & _ & HFpres6 & HFSpres6). change (fs_frame_bytes 7) with 8192 in HFpres6, HFSpres6.
change (8192 / 8) with 1024 in HFSpres6. rewrite EFA7 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
assert (Htb_in7 : In (tb, 48) (ablocks B ly7 S7)) by (exact (HBin7 _ _ Htb_in3)).
assert (Hrin7 : In (r, 64) (ablocks B ly7 S7)) by (exact (HBin7 _ _ Hrin3)).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r 64 (proj1 HJ6) Hrin7) as (_ & _ & _ & _ & Hrpres6 & _). change (req_size 64) with 64 in Hrpres6.
destruct (al_blocks _ _ LAWS _ _ _ _ _ tb 48 (proj1 HJ6) Htb_in7) as (_ & _ & _ & _ & Htbpres6 & _). change (req_size 48) with 48 in Htbpres6.
assert (HWIN6 : forall a, 0 <= a < alloc_ceiling -> ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 4 + 512) -> 0 <= a < 2 ^ 64 /\ ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 4 + 512))
by (intros a Ha Hn; split; [clear - Ha C1; lia | exact Hn]).
assert (HWST6 : forall a, spZ regs + -576 <= a < spZ regs + 0 -> 0 <= a < 2 ^ 64 /\ ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 4 + 512))
by (intros a Ha; unfold SB; clear - Ha HF8lo HF8hi Hceil Hslo Hshi H47 FFS C1; lia).
assert (HRNG6 : (4096 <= F /\ F + 8192 <= alloc_ceiling /\ 512 <= F / 8 < 17594333495296 /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ (F + 8192 <= 2147446784 \/ 17594333495296 <= F)) /\
(4096 <= r /\ r + 64 <= alloc_ceiling /\ (r + 64 <= 2147446784 \/ 17594333495296 <= r)) /\
(4096 <= cfp /\ cfp + 24 <= alloc_ceiling /\ (cfp + 24 <= 2147446784 \/ 17594333495296 <= cfp)) /\
(140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 25152 <= spZ regs /\ spZ regs <= 2 ^ 47) /\ TRGBADD_STK = 25152 /\ SB = 2147450880).
{ unfold gbox, in_app in HFhigh, Hrapp, Hfhigh. unfold kLowShadowBeg, kHighMemBeg in HFhigh, Hrapp, Hfhigh.
split; [clear - HF4096 HFceil HF8lo HF8hi HFq HF8 HFhigh; lia|]. split; [clear - Hr4096 Hrceil Hrapp; lia|].
split; [clear - Hf4096 Hfceil Hflo Hfhi Hfhigh; lia|]. split; [clear - Hceil Hslo Hshi H47 FFS C1; lia|]. split; reflexivity. }
assert (HRtb6 : (4096 <= tb /\ tb + 48 <= alloc_ceiling /\ alloc_ceiling <= 140737479966720 /\ (tb + 48 <= 2147446784 \/ 17594333495296 <= tb)) /\
(F + 8192 <= alloc_ceiling /\ F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\ 512 <= F / 8) /\ SB = 2147450880).
{ unfold gbox in Htbzone. change (req_size 48) with 48 in Htbzone. split; [clear - Htb4096 Htbceil Hrqtb Htbzone C1; lia|]. split; [clear - HFceil HFq HF8 HF8lo; lia | reflexivity]. }
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG
ltac:(idtac; first
[ m_keptA Hfr6 HWIN6 HWST6 HRNG6 HJ6 AG Usp RF E67 E10n E11n F HFpres6 Hrpres6
ltac:(idtac; first [ m_keptA_blk Hfr6 HWIN6 AG 305%nat tb Rtb Htbpres6 HRtb6
| ga_kept_consts Kgot0 Kgot6 Kcell0 Kcell6 Kguar0 Kguar6 Kuar0 Kuar6 Vgr0 Vgr6 ])
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot6 into Kgot0. rename Kcell6 into Kcell0. rename Kguar6 into Kguar0. rename Kuar6 into Kuar0. rename Vgr6 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ6 end.
ga_relow HS AG E10 E11 E10n E11n.
clear HEE7. lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
norm_ss HS.
assert (ZS6 : forall j, 0 <= j < 64 -> val_mem trbsegs (mrestrict (w_H W7) mem6) (SB + F / 8 + (4 + 8 * j)) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi.
replace (SB + F / 8 + (4 + 8 * j) + i) with (SB + F / 8 + 4 + (8 * j + i)) by (clear; lia). apply Heff6. clear - Hj Hi. lia. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 67%nat) 4 516 0 0
[YQ0b.mkChunk 4 (CVal 8 (SLit 0)); YQ0b.mkChunk 12 (CVal 8 (SLit 0)); YQ0b.mkChunk 20 (CVal 8 (SLit 0)); YQ0b.mkChunk 28 (CVal 8 (SLit 0)); YQ0b.mkChunk 36 (CVal 8 (SLit 0)); YQ0b.mkChunk 44 (CVal 8 (SLit 0)); YQ0b.mkChunk 52 (CVal 8 (SLit 0)); YQ0b.mkChunk 60 (CVal 8 (SLit 0)); YQ0b.mkChunk 68 (CVal 8 (SLit 0)); YQ0b.mkChunk 76 (CVal 8 (SLit 0)); YQ0b.mkChunk 84 (CVal 8 (SLit 0)); YQ0b.mkChunk 92 (CVal 8 (SLit 0)); YQ0b.mkChunk 100 (CVal 8 (SLit 0)); YQ0b.mkChunk 108 (CVal 8 (SLit 0)); YQ0b.mkChunk 116 (CVal 8 (SLit 0)); YQ0b.mkChunk 124 (CVal 8 (SLit 0)); YQ0b.mkChunk 132 (CVal 8 (SLit 0)); YQ0b.mkChunk 140 (CVal 8 (SLit 0)); YQ0b.mkChunk 148 (CVal 8 (SLit 0)); YQ0b.mkChunk 156 (CVal 8 (SLit 0)); YQ0b.mkChunk 164 (CVal 8 (SLit 0)); YQ0b.mkChunk 172 (CVal 8 (SLit 0)); YQ0b.mkChunk 180 (CVal 8 (SLit 0)); YQ0b.mkChunk 188 (CVal 8 (SLit 0)); YQ0b.mkChunk 196 (CVal 8 (SLit 0)); YQ0b.mkChunk 204 (CVal 8 (SLit 0)); YQ0b.mkChunk 212 (CVal 8 (SLit 0)); YQ0b.mkChunk 220 (CVal 8 (SLit 0)); YQ0b.mkChunk 228 (CVal 8 (SLit 0)); YQ0b.mkChunk 236 (CVal 8 (SLit 0)); YQ0b.mkChunk 244 (CVal 8 (SLit 0)); YQ0b.mkChunk 252 (CVal 8 (SLit 0)); YQ0b.mkChunk 260 (CVal 8 (SLit 0)); YQ0b.mkChunk 268 (CVal 8 (SLit 0)); YQ0b.mkChunk 276 (CVal 8 (SLit 0)); YQ0b.mkChunk 284 (CVal 8 (SLit 0)); YQ0b.mkChunk 292 (CVal 8 (SLit 0)); YQ0b.mkChunk 300 (CVal 8 (SLit 0)); YQ0b.mkChunk 308 (CVal 8 (SLit 0)); YQ0b.mkChunk 316 (CVal 8 (SLit 0)); YQ0b.mkChunk 324 (CVal 8 (SLit 0)); YQ0b.mkChunk 332 (CVal 8 (SLit 0)); YQ0b.mkChunk 340 (CVal 8 (SLit 0)); YQ0b.mkChunk 348 (CVal 8 (SLit 0)); YQ0b.mkChunk 356 (CVal 8 (SLit 0)); YQ0b.mkChunk 364 (CVal 8 (SLit 0)); YQ0b.mkChunk 372 (CVal 8 (SLit 0)); YQ0b.mkChunk 380 (CVal 8 (SLit 0)); YQ0b.mkChunk 388 (CVal 8 (SLit 0)); YQ0b.mkChunk 396 (CVal 8 (SLit 0)); YQ0b.mkChunk 404 (CVal 8 (SLit 0)); YQ0b.mkChunk 412 (CVal 8 (SLit 0)); YQ0b.mkChunk 420 (CVal 8 (SLit 0)); YQ0b.mkChunk 428 (CVal 8 (SLit 0)); YQ0b.mkChunk 436 (CVal 8 (SLit 0)); YQ0b.mkChunk 444 (CVal 8 (SLit 0)); YQ0b.mkChunk 452 (CVal 8 (SLit 0)); YQ0b.mkChunk 460 (CVal 8 (SLit 0)); YQ0b.mkChunk 468 (CVal 8 (SLit 0)); YQ0b.mkChunk 476 (CVal 8 (SLit 0)); YQ0b.mkChunk 484 (CVal 8 (SLit 0)); YQ0b.mkChunk 492 (CVal 8 (SLit 0)); YQ0b.mkChunk 500 (CVal 8 (SLit 0)); YQ0b.mkChunk 508 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
ga_evalE0 AG; split; [unfold SB; clear - HF8lo; lia|]; split; [unfold SB; clear - HF8hi; lia|]; split; [intros o Ho; exfalso; clear - Ho; lia|];
repeat (apply Forall_cons; [
lazymatch goal with |- YQ0b.chunk_ok _ _ _ _ (YQ0b.mkChunk ?off _) =>
apply (chunk_ok_val trbsegs Ev _ (SB + F / 8) off 8 _ 0); [reflexivity | cbn; clear; lia | cbn; clear; lia |
let j := eval vm_compute in ((off - 4) / 8) in
replace (SB + F / 8 + off) with (SB + F / 8 + (4 + 8 * j)) by (clear; lia); apply ZS6; clear; lia] end |]);
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split;
first [ unfold SB; clear - HF8lo HF8hi Hceil Hslo FFS C1; lia
| clear - HRNG6; lia
| clear - HRtb6; lia
| unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; clear - HF8lo HF8hi; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ6 SHOK GBspan 0x838ac.
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
assert (HPrt7 : Permutation (ablocks B ly7 S7) ((r, RGB_SIZE) :: (tb, 48) :: (lrest ++ [(res, NODE_SIZE)])))
by (rewrite Ebl7; eapply Permutation_trans; [apply Permutation_app_tail; exact HPrt3|]; cbn [app]; apply Permutation_refl).
assert (Hoff7 : forall b sz, In (b, sz) (lrest ++ [(res, NODE_SIZE)]) -> forall a, b <= a < b + req_size sz ->
0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48) /\ ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 4 + 512)).
{ intros b sz Hb a Ha.
pose proof (m_blk_off_zs2 B LAWS ly7 S7 _ _ _ b sz r tb _ fpos HAR7 HPrt7 Hb Hfin7 a Ha) as Hq. rewrite EFA7 in Hq. fold F in Hq.
destruct Hq as [Hq1 Hq2]. split; [exact Hq1|]. split; [exact Hq2|].
assert (Hb7 : In (b, sz) (ablocks B ly7 S7)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt7 | right; right; exact Hb]).
destruct (rga_blk_range B LAWS ly7 S7 _ _ _ b sz HAR7 Hb7) as (Hb4096 & (_ & Hbz) & Hbceil & _).
unfold SB. clear - Ha Hbz Hbceil HFceil HFq HF8 HF8lo C1. lia. }
assert (HK71 : forall b sz, In (b, sz) (lrest ++ [(res, NODE_SIZE)]) -> rg_blk_kept (w_H W7) (w_H W7) mem7 (ms_mem ms1) b (req_size sz)).
{ intros b sz Hb i Hi. destruct (Hoff7 b sz Hb (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2 & Hq3).
rewrite (UN3 (b + i) Hq1 Hq2), (Hfr6 (b + i) Hq1 Hq3). exact (UN2 (b + i) Hq1 Hq2). }
assert (HK37 : forall b sz, In (b, sz) lrest -> rg_blk_kept (w_H W3) (w_H W7) (ms_mem ms) mem7 b (req_size sz)).
{ intros b sz Hb i Hi.
assert (Hb3 : In (b, sz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrt3 | right; right; exact Hb]).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ b sz HAR3 Hb3) as (_ & _ & Hbceil & _).
apply (proj1 (proj2 HK7) b sz i Hb3 Hi). clear - Hi Hbceil Hceil Hslo FFS. lia. }
assert (HKA : forall b sz, In (b, sz) lrest -> rg_blk_kept (w_H W3) (w_H W7) (ms_mem ms) (ms_mem ms1) b (req_size sz))
by (intros b sz Hb; eapply rg_blk_kept_trans; [exact (HK37 b sz Hb) | apply HK71; apply in_or_app; left; exact Hb]).
set (tail := skipn (Z.to_nat (3 * ht_cnt Ht)) (ht_pal Ht)).
assert (Hsplit : pal_bytes ent ++ tail = ht_pal Ht) by (exact (m_pal_split Ht ent Hinv)).
assert (Hres_in7 : In (res, NODE_SIZE) (lrest ++ [(res, NODE_SIZE)])) by (apply in_or_app; right; left; reflexivity).
assert (Hres_b7 : In (res, NODE_SIZE) (ablocks B ly7 S7)) by (rewrite Ebl7; apply in_or_app; right; left; reflexivity).
destruct (rga_blk_range B LAWS ly7 S7 _ _ _ res NODE_SIZE HAR7 Hres_b7) as (_ & _ & Hresceil & Hres16).
assert (Hrq56 : req_size NODE_SIZE = 56) by reflexivity.
lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
assert (HB54 : bv_unsigned (ew Ex 54) = F) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite RF; apply unsigned_lit_small; exact HFrng);
assert (R765 : ew Ex 767 = Z_to_bv 64 res) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rres);
pose proof (st_ok_region_nth Ex ssX (restrict (w_H W7) msX) 6 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 54%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 54 F cs lo hi wlo whi 32 8%N (SOff 767 0) res HRc HB54 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R765) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hres4096 Hresceil Hrq56 C1; lia) ltac:(cbn; lia)) as Vnl0
end; clear HRc end.
assert (HCLm : m_CLmem (w_H W7) (ms_mem ms1) pp dn F tail (cinit ent) [nd0]).
{ unfold m_CLmem. cbn [cinit c_E c_ns]. split; [|split; [|split]].
- rewrite Hsplit. apply (arr8_frame trbsegs _ _ pp _ Ap). intros a Ha. apply (mbyte_of_aview trbsegs). replace a with (pp + (a - pp)) by (clear; lia).
apply (HKA pp _ Hpp_l). rewrite L5 in Ha. clear - Ha Hrq3T. lia.
- apply (arr32_frame trbsegs _ _ dn _ Hdense1). intros a Ha. apply (mbyte_of_aview trbsegs). replace a with (dn + (a - dn)) by (clear; lia).
apply (HKA dn _ Hdn_l). rewrite zlen_fr_vals, Hlen_ent in Ha. clear - Ha Hrq4c. lia.
- intros j Hj. change (elen [nd0]) with 1 in Hj. assert (j = 0) by (clear - Hj; lia). subst j.
unfold node_mem. cbn. destruct Hnd_tree as (_ & _ & (c0 & c1 & Hobj)). exists c0, c1.
apply (rg_obj_at_blk_kept (w_H W7) (w_H W7) mem7 (ms_mem ms1) _ _ _ NODE_SIZE Hobj (proj1 lay_inside_Node)).
rewrite Hnd_addr. apply (rg_blk_kept_sub _ _ _ _ res (req_size NODE_SIZE)); [exact (HK71 res NODE_SIZE Hres_in7) | clear; lia | rewrite Hrq56; unfold NODE_SIZE; clear; lia].
- intros j Hj. change (elen [nd0]) with 1 in Hj. assert (j = 0) by (clear - Hj; lia). subst j.
cbn. change (F + 32 + 8 * 0) with (F + 32 + 0). rewrite Z.add_0_r. change (Z.to_nat 0) with 0%nat. cbv iota. rewrite Hnd_addr. exact Vnl0. }
rregU HS (11%bv : bv 5) 0 ltac:(reflexivity) Q12.
slot_val HS (Some 2%nat) (-576) (-134) (Z_to_bv 64 1) ltac:(reflexivity) QS.
ra_join_slots HS ss_CL 799%nat rga_deads_CL [(Some 2%nat, (-576), (-134))]
ltac:(idtac; ga_join_val HS 799%nat 18%nat Q12 N817; ga_join_val HS 799%nat 19%nat QS N818;
c_pin HS (12%bv : bv 5) (SOff 818 0) ltac:(apply U_inj; transitivity 1; [apply (U_atom _ 818 1 N818); clear; lia | reflexivity])).
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
rga_hand (RCL 510%nat) HS HJ6 (k + EV_NTN); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, (ht_T Ht), (ht_cnt Ht), ent, tail, (cinit ent), [nd0].
split; [split; [unfold EV_NTN; change (elen [nd0]) with 1; clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split. { rewrite Ebl7. unfold m_node_blocks. cbn [map]. rewrite Hnd_addr. eapply Permutation_trans; [apply Permutation_app_tail; exact HPm3|].
change CHT_SIZE with 48. rewrite <- !app_assoc. cbn [app]. apply Permutation_refl. }
do 9 (split; [split; [m_ewT | split; eassumption]|]).
split. { intros t [<- | []]. rewrite Hnd_addr. split.
- exact (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res NODE_SIZE HJ3 HAR7 Ebl7 ltac:(unfold NODE_SIZE; clear; lia)).
- intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res NODE_SIZE blc i lyq ownq HJ3 HAR7 Ebl7 ltac:(unfold NODE_SIZE; clear; lia) Hbl Hi). }
split; [m_ewT|]. split; [m_ewT|]. split; [m_ewT|]. split; [exact Hha|].
split; [exists av; split; [m_ewT | exact Hav]|].
split; [exact HTch|]. split; [clear - Hcnt Hcnt0; lia|].
split; [exact HentOk|]. split; [exact HentND|]. split; [exact Hsum'|]. split; [exact Hlen_ent|].
split; [rewrite <- Hlen_ent; apply cinit_inv; rewrite Hlen_ent; clear - Hcnt; lia|].
split; [vm_compute; discriminate|].
split. { subst tail. unfold zlen in *. rewrite length_skipn. clear - L5 Hcnt0. lia. }
split; [exact HCLm|]. split; [reflexivity|].
split. { intros j Hj. change (elen [nd0]) with 1 in Hj. assert (j = 0) by (clear - Hj; lia). subst j.
unfold tn_matches, tnth, node, znth, cinit. cbn [c_ns]. change (Z.to_nat 0) with 0%nat. cbn [nth n_lo n_hi n_col]. split; [exact Hnd_imin|]. split; [rewrite Hnd_imax, Hlen_ent; reflexivity|]. split; [exact Hnd_cidx|]. split; [exact Hnd_wf|].
rewrite Hnd_addr. clear - Hres4096. lia. }
split. { intros j Hj. change (elen [nd0]) with 1 in Hj. cbn [cinit c_q] in Hj. assert (j = 0) by (clear - Hj; lia). subst j.
unfold tnth, node, znth, cinit. cbn [c_ns]. change (Z.to_nat 0) with 0%nat. cbn [nth].
apply (tn_facts_intro (ht_pal Ht) ent 0 (ht_cnt Ht - 1) nd0 _ Hpag HentOk HentND); cbn [n_lo n_hi n_seg];
[ clear; lia | clear - Hcnt; lia | rewrite Hlen_ent; clear; lia | reflexivity | rewrite Hlen_ent; reflexivity
| unfold zsub; change (Z.to_nat 0) with 0%nat; cbn [skipn]; replace (Z.to_nat (ht_cnt Ht - 1 - 0 + 1)) with (length ent) by (unfold elen in Hlen_ent; clear - Hlen_ent Hcnt; lia); symmetry; apply firstn_all
| exact (proj1 Hnd_wf) | exact Hnd_quot | exact Hnd_split ]. }
split. {
intros j Hj. change (elen [nd0]) with 1 in Hj. assert (j = 0) by (clear - Hj; lia). subst j.
unfold tnth, znth. change (Z.to_nat 0) with 0%nat. cbn [nth].
apply (c_means_ok_of_facts nd0 (node (c_ns (cinit ent)) 0) ent 0 (ht_cnt Ht - 1) HentOk ltac:(clear; lia) ltac:(rewrite Hlen_ent; clear; lia));
[ unfold node, znth, cinit; cbn [c_ns]; change (Z.to_nat 0) with 0%nat; cbn [nth n_seg];
unfold zsub; change (Z.to_nat 0) with 0%nat; cbn [skipn]; replace (Z.to_nat (ht_cnt Ht - 1 - 0 + 1)) with (length ent) by (unfold elen in Hlen_ent; clear - Hlen_ent Hcnt; lia); symmetry; apply firstn_all
| exact (proj1 (proj2 (proj2 (proj2 (proj2 Hnd_wf)))))
| unfold node, znth, cinit; cbn [c_ns]; change (Z.to_nat 0) with 0%nat; cbn [nth];
apply (tn_facts_intro (ht_pal Ht) ent 0 (ht_cnt Ht - 1) nd0 _ Hpag HentOk HentND); cbn [n_lo n_hi n_seg];
[ clear; lia | clear - Hcnt; lia | rewrite Hlen_ent; clear; lia | reflexivity | rewrite Hlen_ent; reflexivity
| unfold zsub; change (Z.to_nat 0) with 0%nat; cbn [skipn]; replace (Z.to_nat (ht_cnt Ht - 1 - 0 + 1)) with (length ent) by (unfold elen in Hlen_ent; clear - Hlen_ent Hcnt; lia); symmetry; apply firstn_all
| exact (proj1 Hnd_wf) | exact Hnd_quot | exact Hnd_split ] ]. }
split; [unfold tnth, znth; change (Z.to_nat 0) with 0%nat; cbn [nth]; rewrite Hnd_addr; m_ewT|].
split; [exact N817|]. split; [exact N818|].
cbn [cinit c_q]. clear. lia. }
destruct Hres7 as [(Hz & Ebl7 & Vnln7) | (Hres4096 & Ebl7 & _)].
2: { exfalso. assert (Hb7 : In (res, NODE_SIZE) (ablocks B ly7 S7)) by (rewrite Ebl7; apply in_or_app; right; left; reflexivity).
destruct (rga_blk_range B LAWS ly7 S7 _ _ _ res NODE_SIZE HAR7 Hb7) as (_ & _ & Hrc & _). change (req_size NODE_SIZE) with 56 in Hrc.
rewrite YO3v.branch_ne_U in Hc. apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc. rewrite (U_atom _ 767 res Rres) in Hc by (clear - Hres4096 Hrc C1; lia).
rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc. clear - Hc Hres4096. lia. }
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x848fc.
1: { assert (Htb_in7 : In (tb, 48) (ablocks B ly7 S7)) by (rewrite Ebl7; exact Htb_in3). assert (Hrin7 : In (r, 64) (ablocks B ly7 S7)) by (rewrite Ebl7; exact Hrin3). ga_awrR AG fpos F EFA7 54%nat 67%nat. }
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
ga_join HS ss_XD 2600%nat rga_deads_XD ltac:(idtac).
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
assert (HEA : 0 <= EV_ADDFRAME) by (vm_compute; discriminate).
rga_hand RXD HS HJ7 (k + EV_NTN); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, (ht_T Ht), dn, (4 * ht_cnt Ht).
split; [split; [unfold EV_NTN, EV_FREECHT, EV_RGBADD, EV_HD in *; clear - Hk0 HEA; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [clear - HT24; lia|]. split; [clear - Hcnt0; lia|].
split; [rewrite Ebl7; change CHT_SIZE with 48; exact HPm3|].
do 3 (split; [split; [m_ewT | split; eassumption]|]).
do 5 (split; [m_ewT|]).
split; [m_ewT | split; eassumption].
Qed.
End e.
End d.
