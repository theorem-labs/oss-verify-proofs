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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0f YCd3.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP15.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl3 YCl4 YCl5 YCl0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClr YCls YClg YClh YCli YClj YClk YCll YClp YClm YCln YCkr YCks YCkt YCku YCkv YCkw YCkx YClv.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gX3 : forall n : nat, rga_fromA B ss_TL (fun _ => INV_TL B (S n)) -> rga_from B ss_GX2 (INV_GX2 B (S n)).
Proof.
intros n RNX. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & ha & ix & Ht & ent & p1 & p2 & hn & un & fn & K & HTRIP).
rga_cbn_cx HTRIP.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & Rhh & Ruu & Rp1 & Hp1_gp & Rp2 & Hp2_gp & Rhn & Hhn_gp & Run & Hun_gp & Rfn & Hfn_gp & RT & Rha & Hha & Rix & Hix & Hnix &
Hinv & HTch & Hsum & (av & Rav & Hav) & R755 & HTlt & HTK & HinvK & HarrK & RcntK).
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_GX2 in HS.
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
assert (BT : 0 <= ht_T Ht < 2 ^ 64) by (clear - HT24; lia).
set (Tn := getNextPrimePower2 (ht_T Ht)) in *.
pose proof (ts_chain_next _ HTch HTlt) as HTnch. fold Tn in HTnch.
pose proof (ts_chain_next_gt _ HTch HTlt) as HTngt. fold Tn in HTngt.
assert (HTn24 : 1048583 <= Tn <= 16777216) by (clear - HTnch HTngt HT24; unfold ts_chain in HTnch; cbn [In] in HTnch; lia).
assert (BTn : 0 <= Tn < 2 ^ 64) by (clear - HTn24; lia).
assert (Hra88 : 0x814c8 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
pose proof (g_ts_rank_range (ht_T Ht)) as Hrk.
assert (Hrk4 : g_ts_rank (ht_T Ht) <= 4).
{ clear - HTch HTlt. unfold ts_chain in HTch. cbn [In] in HTch. unfold MAX_TABLE_SIZE in HTlt.
destruct HTch as [H|[H|[H|[H|[H|[H|[]]]]]]]; rewrite <- H in *; first [ vm_compute; discriminate | lia ]. }
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (TBL := [(fq, 4 * ht_T Ht); (p1, 3 * Tn); (p2, 4 * Tn); (hn, 3 * Tn); (un, Tn); (fn, 4 * Tn)]).
set (lrest := ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ TBL).
assert (HPrt3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (tb, 48) :: lrest))
by (eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst lrest TBL; YI0g.perm_tac).
assert (HPtb3 : Permutation (ablocks B ly3 S3) ((tb, 48) :: (r, RGB_SIZE) :: lrest)) by (eapply Permutation_trans; [exact HPrt3 | apply perm_swap]).
assert (Hoff3 : forall b sz, In (b, sz) lrest -> forall a, b <= a < b + req_size sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. pose proof (m_blk_off_zs2 B LAWS ly3 S3 _ _ _ b sz r tb _ fpos HAR3 HPrt3 Hb Hfin3 a Ha) as Hq. rewrite EFA3 in Hq. fold F in Hq. exact Hq. }
assert (Hcht_l : forall b sz, In (b, sz) TBL -> In (b, sz) lrest) by (intros b sz Hb; subst lrest; apply in_or_app; right; right; right; exact Hb).
assert (Hcht_in3 : forall b sz, In (b, sz) TBL -> In (b, sz) (ablocks B ly3 S3)).
{ intros b sz Hb. eapply Permutation_in; [apply Permutation_sym; exact HPrt3|]. right. right. exact (Hcht_l b sz Hb). }
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) (ms_mem ms3) a = aview trbsegs (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
idtac "OK-B".
assert (Hfq_in3 : In (fq, 4 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hfq_l : In (fq, 4 * ht_T Ht) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ fq _ HAR3 Hfq_in3 ltac:(clear - HT24; lia)) as (Hfq4096 & Hfqceil & Hfq16 & Hfqpres).
pose proof (req_size_pos (4 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_fq].
assert (Bfq : 0 <= fq < 2 ^ 64) by (clear - Hfq4096 Hfqceil HT24 C1; lia).
assert (Hp1_in3 : In (p1, 3 * Tn) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hp1_l : In (p1, 3 * Tn) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ p1 _ HAR3 Hp1_in3 ltac:(clear - HTn24; lia)) as (Hp14096 & Hp1ceil & Hp116 & Hp1pres).
pose proof (req_size_pos (3 * Tn) ltac:(clear - HTn24; lia)) as [_ Hrq_p1].
assert (Bp1 : 0 <= p1 < 2 ^ 64) by (clear - Hp14096 Hp1ceil HTn24 C1; lia).
assert (Hp2_in3 : In (p2, 4 * Tn) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hp2_l : In (p2, 4 * Tn) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ p2 _ HAR3 Hp2_in3 ltac:(clear - HTn24; lia)) as (Hp24096 & Hp2ceil & Hp216 & Hp2pres).
pose proof (req_size_pos (4 * Tn) ltac:(clear - HTn24; lia)) as [_ Hrq_p2].
assert (Bp2 : 0 <= p2 < 2 ^ 64) by (clear - Hp24096 Hp2ceil HTn24 C1; lia).
assert (Hhn_in3 : In (hn, 3 * Tn) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hhn_l : In (hn, 3 * Tn) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ hn _ HAR3 Hhn_in3 ltac:(clear - HTn24; lia)) as (Hhn4096 & Hhnceil & Hhn16 & Hhnpres).
pose proof (req_size_pos (3 * Tn) ltac:(clear - HTn24; lia)) as [_ Hrq_hn].
assert (Bhn : 0 <= hn < 2 ^ 64) by (clear - Hhn4096 Hhnceil HTn24 C1; lia).
assert (Hun_in3 : In (un, Tn) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hun_l : In (un, Tn) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ un _ HAR3 Hun_in3 ltac:(clear - HTn24; lia)) as (Hun4096 & Hunceil & Hun16 & Hunpres).
pose proof (req_size_pos (Tn) ltac:(clear - HTn24; lia)) as [_ Hrq_un].
assert (Bun : 0 <= un < 2 ^ 64) by (clear - Hun4096 Hunceil HTn24 C1; lia).
assert (Hfn_in3 : In (fn, 4 * Tn) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hfn_l : In (fn, 4 * Tn) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ fn _ HAR3 Hfn_in3 ltac:(clear - HTn24; lia)) as (Hfn4096 & Hfnceil & Hfn16 & Hfnpres).
pose proof (req_size_pos (4 * Tn) ltac:(clear - HTn24; lia)) as [_ Hrq_fn].
assert (Bfn : 0 <= fn < 2 ^ 64) by (clear - Hfn4096 Hfnceil HTn24 C1; lia).
assert (Bix : 0 <= ix < 2 ^ 64) by (clear - Hix HN; unfold RGB_NMAX in HN; lia).
idtac "OK-BLK".
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rregU HS (10%bv : bv 5) fq ltac:(apply (U_atom _ 473 fq Rfq Bfq)) Ra0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
set (nfr := 4 * ht_T Ht).
assert (Hnfr : 64513 <= nfr <= 67108864) by (subst nfr; clear - HT24; lia).
set (Er := fun a : Z => fq <= a < fq + req_size nfr).
set (bl8 := ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ (tb, 48) :: [(p1, 3 * Tn); (p2, 4 * Tn); (hn, 3 * Tn); (un, Tn); (fn, 4 * Tn)]).
assert (HPv3 : Permutation (ablocks B ly3 S3) ((fq, nfr) :: bl8)) by (eapply Permutation_trans; [exact HPm3|]; subst bl8 nfr; YI0g.perm_tac).
assert (HvIn3 : In (fq, nfr) (ablocks B ly3 S3)) by (exact Hfq_in3).
assert (Hbl8_in3 : forall b z, In (b, z) bl8 -> In (b, z) (ablocks B ly3 S3)) by (intros b z Hb; eapply Permutation_in; [apply Permutation_sym; exact HPv3 | right; exact Hb]).
assert (HnO : forall b z a, In (b, z) bl8 -> b <= a < b + req_size z -> ~ Er a).
{ intros b z a Hb Ha Hin. pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (fq, nfr) bl8 (b, z) HAR3 HPv3 Hb) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. subst Er. cbv beta in Hin. clear - Dd Ha Hin. lia. }
assert (Hr_bl8 : In (r, 64) bl8) by (subst bl8; apply in_or_app; left; exact Hrin).
assert (Htb_bl8 : In (tb, 48) bl8) by (subst bl8; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (HnR : forall a, r <= a < r + 64 -> ~ Er a) by (intros a Ha; apply (HnO r 64 a Hr_bl8); change (req_size 64) with 64; exact Ha).
assert (HnT : forall a, tb <= a < tb + 48 -> ~ Er a) by (intros a Ha; apply (HnO tb 48 a Htb_bl8); change (req_size 48) with 48; exact Ha).
assert (HnC : forall a, cfp <= a < cfp + 24 -> ~ Er a).
{ intros a Ha Hb. pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fq nfr cid pos HAR3 HvIn3 HfinS3) as Dd.
rewrite EFA3 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. subst Er. cbv beta in Hb. clear - Dd Ha Hb Hflo Hfhi. lia. }
assert (HnF : forall a, F <= a < F + 8192 -> ~ Er a).
{ intros a Ha Hb. pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fq nfr 7 fpos HAR3 HvIn3 Hfin3) as Dd.
rewrite EFA3 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. subst Er. cbv beta in Hb. clear - Dd Ha Hb. lia. }
assert (HnS : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ Er a).
{ intros a Ha Hb. destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fq nfr HAR3 HvIn3) as (_ & (_ & Hbz) & _).
subst Er. cbv beta in Hb. clear - Ha Hb Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
idtac "OK-S0".
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_atD trbsegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 _ k fq nfr (-576) (Z_to_bv 64 536584) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 HvIn3) end.
- exact Ra0.
- unfold spZ. rewrite Rsp. ga_evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rga_room Hev Hbud; (clear - Hk0 Hrk Hrk4 HEVv HTlt; rga_lia).
- apply (achain_chain_pre ly3 _ (spZ regs - 576) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity.
- exact Tfq. }
idtac "OK-CALL".
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & (l1_8 & l2_8 & El8 & Eab8) & Hfrs8 & Hd8 & HK8).
assert (HPm8 : Permutation (ablocks B ly8 S8) bl8).
{ rewrite Eab8. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1_8 l2_8 (fq, nfr)). rewrite <- El8. apply Permutation_sym. exact HPv3. }
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof HJ8 as (HAR8 & Hly8 & _).
assert (EFA8 : forall c p, frame_addr ly8 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly8 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin8 : In (7, fpos) (frames S8)) by (rewrite Hfrs8; exact Hfin3).
assert (HfinS8 : In (cid, pos) (frames S8)) by (rewrite Hfrs8; exact HfinS3).
assert (Hrin8 : In (r, 64) (ablocks B ly8 S8)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm8 | exact Hr_bl8]).
assert (Htb_in8 : In (tb, 48) (ablocks B ly8 S8)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm8 | exact Htb_bl8]).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR8 Hfin8) as (_ & _ & HFpres8 & HFSpres8). change (fs_frame_bytes 7) with 8192 in HFpres8, HFSpres8.
change (8192 / 8) with 1024 in HFSpres8. rewrite EFA8 in HFpres8, HFSpres8. fold F in HFpres8, HFSpres8.
ga_aconsts HROD HJ8 Kgot8 Kcell8 Kguar8 Kuar8 Vgr8.
reseat HS HJ8 HP8 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG
ltac:(idtac; first [ ga_keptK HK8 HJ8 AG Usp Hrin3 Hrin8 HfinS3 Hfin3 HFpres8 HFSpres8 HnR HnC HnF HnS EFA3 F Kgot0 Kgot8 Kcell0 Kcell8 Kguar0 Kguar8 Kuar0 Kuar8 Vgr0 Vgr8
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 305%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs _ LAWS); [exact HK8 | exact (proj1 HJ8) | exact Htb_in8 | ga_evalE AG | exact Htb_in3 | lia | change (req_size 48) with 48; lia | lia | lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnT; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot8 into Kgot0. rename Kcell8 into Kcell0. rename Kguar8 into Kguar0. rename Kuar8 into Kuar0. rename Vgr8 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ8 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE8 end.
norm_ss HS.
idtac "OK-S1".
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ8 SHOK GBspan 0x83054.
idtac "OK-RUN2".
all: try (ga_obl_blk HJ8 Rtb E44 Htb_in8).
idtac "OK-OBL2a".
1: m_awrR AG fpos F EFA8 54%nat 67%nat ltac:(fail).
idtac "OK-OBL2".
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG. norm_ss HS.
idtac "OK-KEPT2".
assert (Bha : 0 <= ha < 2 ^ 64) by (clear - Hha; lia).
assert (BF : 0 <= F < 2 ^ 64) by (clear - HF4096 HFceil C1; lia).
pose proof HinvK as (_ & (Hcnt0K & _) & _).
assert (HcntK64 : 0 <= ht_cnt K < 2 ^ 64) by (clear - Hcnt0K HTK HTn24; fold Tn in HTK; lia).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rhaz : ew Ex 458 = Z_to_bv 64 ha) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rha);
assert (Rixz : ew Ex 456 = Z_to_bv 64 ix) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rix);
assert (Rtbz : ew Ex 305 = Z_to_bv 64 tb) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb);
assert (RFz : ew Ex 54 = Z_to_bv 64 F) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RF);
assert (Rfnz : ew Ex 824 = Z_to_bv 64 fn) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfn);
assert (Rhnz : ew Ex 792 = Z_to_bv 64 hn) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhn);
assert (Runz : ew Ex 808 = Z_to_bv 64 un) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Run);
assert (Rp1z : ew Ex 760 = Z_to_bv 64 p1) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rp1);
assert (Rp2z : ew Ex 776 = Z_to_bv 64 p2) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rp2);
assert (RcKz : ew Ex 1421 = Z_to_bv 64 (ht_cnt K)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RcntK);
assert (RTnz : ew Ex 755 = Z_to_bv 64 Tn) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact R755) end.
rregU HS (12%bv : bv 5) ha ltac:(apply (U_atom _ 458 ha Rhaz Bha)) Q12.
rregU HS (21%bv : bv 5) (tb + 40) ltac:(apply (U_atom_off _ 305 tb 40 Rtbz); clear - Htb4096 Htbceil Hrqtb C1; lia) Q21.
rregU HS (24%bv : bv 5) F ltac:(apply (U_atom _ 54 F RFz BF)) Q24.
slot_val HS (Some 305%nat) 0 0 (Z_to_bv 64 fn) ltac:(exact (g_denot_off0 _ 824 fn Rfnz Bfn)) QF.
slot_val HS (Some 305%nat) 0 8 (Z_to_bv 64 hn) ltac:(exact (g_denot_off0 _ 792 hn Rhnz Bhn)) QH.
slot_val HS (Some 305%nat) 0 16 (Z_to_bv 64 un) ltac:(exact (g_denot_off0 _ 808 un Runz Bun)) QU.
slot_val HS (Some 305%nat) 0 24 (Z_to_bv 64 p1) ltac:(exact (g_denot_off0 _ 760 p1 Rp1z Bp1)) QP.
slot_val HS (Some 305%nat) 0 32 (Z_to_bv 64 p2) ltac:(exact (g_denot_off0 _ 776 p2 Rp2z Bp2)) QX.
slot_val HS (Some 305%nat) 0 40 (Z_to_bv 64 (ht_cnt K)) ltac:(exact (g_denot_off0 _ 1421 _ RcKz HcntK64)) QC.
slot_val HS (Some 305%nat) 0 44 (Z_to_bv 64 Tn) ltac:(exact (g_denot_off0 _ 755 _ RTnz BTn)) QT.
slot_val HS (Some 2%nat) (-576) (-392) (Z_to_bv 64 ix) ltac:(exact (g_denot_off0 _ 456 ix Rixz Bix)) QI.
idtac "OK-T1".
m_join_slots_win HS ss_TL 1000%nat rga_deads_TL
[(Some 305%nat, 0, 0); (Some 305%nat, 0, 8); (Some 305%nat, 0, 16); (Some 305%nat, 0, 24); (Some 305%nat, 0, 32); (Some 305%nat, 0, 40); (Some 305%nat, 0, 44); (Some 2%nat, (-576), (-392))]
ltac:(idtac; ga_join_val HS 1000%nat 14%nat Q12 N1014; ga_join_val HS 1000%nat 13%nat Q21 N1013; ga_join_val HS 1000%nat 17%nat Q24 N1017;
ga_join_val HS 1000%nat 23%nat QF N1023; ga_join_val HS 1000%nat 24%nat QH N1024; ga_join_val HS 1000%nat 25%nat QU N1025;
ga_join_val HS 1000%nat 26%nat QP N1026; ga_join_val HS 1000%nat 27%nat QX N1027; ga_join_val HS 1000%nat 28%nat QC N1028; ga_join_val HS 1000%nat 29%nat QT N1029;
ga_join_val HS 1000%nat 30%nat QI N1030;
ga_join_fact HS 1014%nat (mkAF 0 1 0) ltac:(rewrite N1014; rewrite unsigned_lit_small by exact Bha; change (2 ^ 0) with 1; split; [clear - Hha; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 1030%nat (mkAF 0 10000 0) ltac:(rewrite N1030; rewrite unsigned_lit_small by exact Bix; change (2 ^ 0) with 1; split; [clear - Hix HN; unfold RGB_NMAX in HN; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 1023%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1023; rewrite unsigned_lit_small by exact Bfn; change (2 ^ 4) with 16; split; [clear - Hfn4096 Hfnceil HTn24 C1; lia|]; split; [exact Hfn16 | clear; lia]);
ga_join_fact HS 1024%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1024; rewrite unsigned_lit_small by exact Bhn; change (2 ^ 4) with 16; split; [clear - Hhn4096 Hhnceil HTn24 C1; lia|]; split; [exact Hhn16 | clear; lia]);
ga_join_fact HS 1025%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1025; rewrite unsigned_lit_small by exact Bun; change (2 ^ 4) with 16; split; [clear - Hun4096 Hunceil HTn24 C1; lia|]; split; [exact Hun16 | clear; lia]);
ga_join_fact HS 1026%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1026; rewrite unsigned_lit_small by exact Bp1; change (2 ^ 4) with 16; split; [clear - Hp14096 Hp1ceil HTn24 C1; lia|]; split; [exact Hp116 | clear; lia]);
ga_join_fact HS 1027%nat (mkAF 4096 140737479966720 4) ltac:(rewrite N1027; rewrite unsigned_lit_small by exact Bp2; change (2 ^ 4) with 16; split; [clear - Hp24096 Hp2ceil HTn24 C1; lia|]; split; [exact Hp216 | clear; lia]);
ga_join_fact HS 1028%nat (mkAF 0 16777216 0) ltac:(rewrite N1028; rewrite unsigned_lit_small by exact HcntK64; change (2 ^ 0) with 1; split; [clear - Hcnt0K HTK HTn24; fold Tn in HTK; lia|]; split; [apply Z.mod_1_r | clear; lia]);
ga_join_fact HS 1029%nat (mkAF 524309 16777216 0) ltac:(rewrite N1029; rewrite unsigned_lit_small by exact BTn; change (2 ^ 0) with 1; split; [clear - HTn24; lia|]; split; [apply Z.mod_1_r | clear; lia])).
idtac "OK-T2".
pose proof (g_lens_of_inv K _ HinvK) as HlensK. rewrite HTK in HlensK.
assert (KB8 : forall b z, In (b, z) bl8 -> In (b, z) lrest -> forall i, 0 <= i < z ->
aview trbsegs (w_H W8) (ms_mem ms) (b + i) = aview trbsegs (w_H W3) (ms_mem ms3) (b + i)).
{ intros b z Hb Hl i Hi. pose proof (req_size_pos z ltac:(clear - Hi; lia)) as [_ Hrqb].
destruct (Hoff3 b z Hl (b + i) ltac:(clear - Hi Hrqb; lia)) as [Hq1 Hq2]. rewrite (UN2 (b + i) Hq1 Hq2).
destruct HK8 as (_ & K2 & _). apply (K2 b z i (Hbl8_in3 b z Hb)); [clear - Hi Hrqb; lia|]. apply (HnO b z (b + i) Hb). clear - Hi Hrqb. lia. }
assert (Hin5 : forall b z, In (b, z) [(p1, 3 * Tn); (p2, 4 * Tn); (hn, 3 * Tn); (un, Tn); (fn, 4 * Tn)] -> In (b, z) bl8)
by (intros b z Hb; subst bl8; apply in_or_app; right; apply in_or_app; right; right; cbn [In] in Hb |- *; tauto).
assert (HarrK8 : g_arrs (mrestrict (w_H W8) (ms_mem ms)) fn hn un p1 p2 (ht_frequ K) (ht_keys K) (ht_used K) (ht_pal K) (ht_colidx K)).
{ apply (g_arrs_move (w_H W3) (w_H W8) (ms_mem ms3) (ms_mem ms) fn hn un p1 p2 p1 p2 Tn _ _ _ _ _ HarrK HlensK).
- intros i Hi. apply (KB8 fn _ (Hin5 fn (4 * Tn) ltac:(cbn [In]; tauto)) Hfn_l i Hi).
- intros i Hi. apply (KB8 hn _ (Hin5 hn (3 * Tn) ltac:(cbn [In]; tauto)) Hhn_l i Hi).
- intros i Hi. apply (KB8 un _ (Hin5 un Tn ltac:(cbn [In]; tauto)) Hun_l i Hi).
- intros i Hi. apply (KB8 p1 _ (Hin5 p1 (3 * Tn) ltac:(cbn [In]; tauto)) Hp1_l i Hi).
- intros i Hi. apply (KB8 p2 _ (Hin5 p2 (4 * Tn) ltac:(cbn [In]; tauto)) Hp2_l i Hi). }
assert (HchtK : cht_arrays trbsegs (mrestrict (w_H W8) (ms_mem ms)) fn hn un p1 p2 K) by (apply g_cht_of_arrs; exact HarrK8).
idtac "OK-ARR".
assert (HrkK : g_ts_rank Tn = g_ts_rank (ht_T Ht) + 1) by (exact (g_ts_rank_next _ HTch HTlt)).
assert (Hk1 : k + 1 <= 8 + 12 * g_ts_rank Tn) by (rewrite HrkK; clear - Hk0; lia).
assert (HsumK : zsum (map snd (ents_below Ht (ht_T Ht))) <= ix + 1) by (rewrite (g_rehash_zsum Ht ent Hinv); exact Hsum).
assert (HPmK : Permutation (ablocks B ly8 S8) (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ (tb, 48) :: cht_blocks fn hn un p1 p2 Tn))
by (eapply Permutation_trans; [exact HPm8|]; subst bl8; unfold cht_blocks; YI0g.perm_tac).
unfold g_perm in Hp1_gp, Hp2_gp, Hhn_gp, Hun_gp, Hfn_gp. rga_cbn_cx Hp1_gp. rga_cbn_cx Hp2_gp. rga_cbn_cx Hhn_gp. rga_cbn_cx Hun_gp. rga_cbn_cx Hfn_gp.
destruct Hp1_gp as [Tp1 Ap1]. destruct Hp2_gp as [Tp2 Ap2]. destruct Hhn_gp as [Thn Ahn]. destruct Hun_gp as [Tun Aun]. destruct Hfn_gp as [Tfn Afn].
assert (Hfrs8' : frames S8 = (7, fpos) :: frames S) by (rewrite Hfrs8; exact Hfrs3).
idtac "OK-PRE".
rga_hand RNX HS HJ8 (k + 1); [rga_E_tac HEE8 | ].
exists blk, fim, tb, fn, hn, un, p1, p2, ha, ix, K, (ents_below Ht (ht_T Ht)).
rga_cbn_cx_goal. change CHT_SIZE with 48. rewrite HTK. m_inv_auto.
Qed.
End e.
End d.
