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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClr YCls YClg YClh YCli YClj YClk YCkr YCks YCkt YCku YCkv YCkw YCkx YClv YClp YCl2 YCky YClq YClb YCl6.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCkz YCl7.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis COLHASH : tcolhash_spec B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gH2 : forall (n : nat) (m : nat), rga_fromA B ss_H2 (fun _ => INV_H2 B (S n) m) -> rga_from B ss_H1 (INV_H1 B (S n) m).
Proof.
intros n m RH2. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & ha & ix & Ht & ent & p1 & p2 & hn & un & fn & K & j & HTRIP).
rga_cbn_cx HTRIP.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & Rp1 & Hp1_gp & Rp2 & Hp2_gp & Rhn & Hhn_gp & Run & Hun_gp & Rfn & Hfn_gp & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & R755 & HTlt & HKT & HKarr & HKinv & Rj & Rj4 & Rj3 & Hj & Hmj & Huv1).
pose proof Hp1_gp as Hp1_perm. pose proof Hp2_gp as Hp2_perm. pose proof Hhn_gp as Hhn_perm. pose proof Hun_gp as Hun_perm. pose proof Hfn_gp as Hfn_perm.
unfold g_perm in Hp1_perm, Hp2_perm, Hhn_perm, Hun_perm, Hfn_perm. rga_cbn_cx Hp1_perm. rga_cbn_cx Hp2_perm. rga_cbn_cx Hhn_perm. rga_cbn_cx Hun_perm. rga_cbn_cx Hfn_perm.
destruct Hp1_perm as [Tp1 Ap1]. destruct Hp2_perm as [Tp2 Ap2]. destruct Hhn_perm as [Thn Ahn]. destruct Hun_perm as [Tun Aun]. destruct Hfn_perm as [Tfn Afn].
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_H1 in HS.
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
set (TBL := [(fq, 4 * ht_T Ht); (hh, 3 * ht_T Ht); (uu, ht_T Ht); (p1, 3 * Tn); (p2, 4 * Tn); (hn, 3 * Tn); (un, Tn); (fn, 4 * Tn)]).
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
assert (Hhh_in3 : In (hh, 3 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Hhh_l : In (hh, 3 * ht_T Ht) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ hh _ HAR3 Hhh_in3 ltac:(clear - HT24; lia)) as (Hhh4096 & Hhhceil & Hhh16 & Hhhpres).
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_hh].
assert (Bhh : 0 <= hh < 2 ^ 64) by (clear - Hhh4096 Hhhceil HT24 C1; lia).
assert (Huu_in3 : In (uu, ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; cbn [In]; tauto).
assert (Huu_l : In (uu, ht_T Ht) lrest) by (apply Hcht_l; subst TBL; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ uu _ HAR3 Huu_in3 ltac:(clear - HT24; lia)) as (Huu4096 & Huuceil & Huu16 & Huupres).
pose proof (req_size_pos (ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_uu].
assert (Buu : 0 <= uu < 2 ^ 64) by (clear - Huu4096 Huuceil HT24 C1; lia).
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
assert (HcT : ht_cnt Ht < ht_T K) by (rewrite HKT; clear - Hcnt0 HTngt; lia).
destruct (rehash_step_used Ht ent Hinv K j HKinv Hj ltac:(rewrite Huv1; clear; lia) HcT) as (hs & Hfs & Hhs & HKfree & HKcnt1 & HKins).
rewrite HKT in Hhs.
assert (Hprobe : probe Tn (ht_used K) (ht_keys K) (key Ht j) = Some hs) by (rewrite <- HKT, <- probe_of_htab; exact Hfs).
pose proof HKinv as ((LK1 & LK2 & LK3 & LK4 & LK5) & (HcntK0 & _) & _). rewrite HKT in LK1, LK2, LK3, LK4, LK5, HcntK0.
pose proof Harr as (Af & Ak & Au).
pose proof HKarr as (AKf & AKk & AKu & AKp & AKx).
assert (Hpix : pixel_at trbsegs (mrestrict (w_H W3) (ms_mem ms3)) (hh + 3 * j) 3 (key Ht j) true)
by (split; [unfold key; apply (arr8_col3 trbsegs _ hh (ht_keys Ht) j Ak); [clear - Hj; lia | rewrite L2; clear - Hj; lia] | left; split; reflexivity]).
assert (Bj : 0 <= j < 2 ^ 64) by (clear - Hj HT24; lia).
idtac "OK-G0".
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rregU HS (10%bv : bv 5) (hh + 3 * j)
ltac:(rewrite (Z.add_comm hh);
apply U_add_small_q; [ rewrite U_and_lit by (clear; lia); rewrite (U_atom _ 1102 (3 * j) Rj3 ltac:(clear - Hj HT24; lia));
change 4294967295 with (Z.ones 32); rewrite Z.land_ones by (clear; lia); apply Z.mod_small; clear - Hj HT24; lia
| exact (U_atom _ 474 hh Rhh Bhh) | clear - Hj; lia | clear - Bhh; lia | clear - Hhhceil Hj C1; lia ]) Ha0.
rregU HS (11%bv : bv 5) hn ltac:(exact (U_atom _ 792 hn Rhn Bhn)) Ha1.
rregU HS (12%bv : bv 5) un ltac:(exact (U_atom _ 808 un Run Bun)) Ha2.
rregU HS (13%bv : bv 5) Tn ltac:(exact (U_atom _ 755 Tn R755 BTn)) Ha3.
rregU HS (14%bv : bv 5) 3 ltac:(reflexivity) Ha4.
rga_chain HS HJ3 AG EE.
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
idtac "OK-C0".
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call trbsegs B LAWS Hsegs W3 Ex ssX msX TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly3 S3 mdX k
TCOLHASH_STK [] 0
(-576) (ew Ex 2) (Z_to_bv 64 0x82c98) ((spZ regs, raZ regs, s0Z regs) :: ch)
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
replace (spZ regs + -576) with (spZ regs - 576) by (clear; lia); exact (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1)
| intros HPRE1; eapply SRr_mono;
[ pose proof (COLHASH ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch) hh (3 * ht_T Ht) (3 * j) hn (3 * Tn) un Tn Tn 3
(ht_used K) (ht_keys K) (key Ht j) true hs HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc];
let v := eval vm_compute in A_col_hash in change (w64 A_col_hash) with (Z_to_bv 64 v) in CALL;
apply CALL; clear CALL
| cbv beta; intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HJc & HPc & HK7);
exists ly7, S7, regs7, mem7, md7; split; [rewrite Rra; reflexivity|]; split; [exact HJc|]; split; [exact HPc | exact HK7] ]
| intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end end.
idtac "OK-C1".
- exact Ha0.
- exact Ha1.
- exact Ha2.
- exact Ha3.
- exact Ha4.
- exact Hhh_in3.
- clear - Hj. lia.
- clear - Hj. lia.
- exact Hhn_in3.
- clear. lia.
- exact Hun_in3.
- clear. lia.
- exact Hpix.
- exact AKu.
- exact AKk.
- exact LK1.
- exact LK2.
- clear - HTn24. lia.
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
idtac "OK-P0".
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
idtac "OK-RS".
destruct (g_rh_kept_blk (w_H W3) (ms_mem ms3) mem7 fq hh uu fn hn un p1 p2 Ht ent K _ Tn Harr Hinv HKarr HKinv HKT) as [Hold7 HKarr7].
{ intros b sz Hb.
assert (Hsz : 0 < sz) by (cbn [In] in Hb; clear - Hb HT24 HTn24; repeat (destruct Hb as [Hb | Hb]; [injection Hb as _ <-; lia|]); destruct Hb).
apply (rg_blk_kept_sub _ _ _ _ b (req_size sz));
[ exact (m_blk_kept_call0 B _ _ _ _ _ _ _ _ _ _ _ _ _ b sz HJc (Hcht_in3 b sz Hb) (Hcht_in3 b sz Hb)) | clear; lia | pose proof (req_size_pos sz ltac:(clear - Hsz; lia)) as Hrq; clear - Hrq; lia ]. }
clear KP.
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) mem7 a = aview trbsegs (w_H W3) mem7 a) by (intros; reflexivity).
idtac "OK-K7".
assert (Bhs : 0 <= hs < 2 ^ 64) by (clear - Hhs HTn24; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Rhnv : ew Ev 792 = Z_to_bv 64 hn) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhn) end.
g_cond HS BC_GEU (SAlu ALU_XOR (SOff 792 0) (SLit (-1))) (SAlu ALU_SRL (SMd M_MUL (SOff 1125 0) (SLit 12884901888)) (SLit 32))
ltac:(apply (YCqg.ub_room_cond _ _ _ hn (3 * hs) (U_atom _ 792 hn Rhnv Bhn) (g_U_zext3 _ _ hs (U_atom _ 1125 hs Rhsa Bhs) ltac:(clear - Hhs HTn24; lia)));
[clear - Bhn; lia | clear - Hhs; lia | clear - Hhnceil Hhs C1; lia]).
reshok_bx HS 44%nat.
idtac "OK-C7".
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan A_asan_memcpy.
idtac "OK-R7".
all: try (lazymatch goal with |- range_addressable _ (U ?Ev _) _ _ =>
assert (Rtbv : ew Ev 305 = Z_to_bv 64 tb) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb);
assert (E44v : ew Ev 44 = Z_to_bv 64 SB) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E44) | _ => idtac end).
all: try (ga_obl_blk HJ7 Rtbv E44v Htb_in3).
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-K8".
assert (KOFF : forall b sz, In (b, sz) TBL -> forall a, b <= a < b + sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. apply (Hoff3 b sz (Hcht_l b sz Hb) a).
assert (Hsz : 0 < sz) by (subst TBL; cbn [In] in Hb; clear - Hb HT24 HTn24;
repeat (destruct Hb as [Hb | Hb]; [injection Hb as _ <-; lia|]); destruct Hb).
pose proof (req_size_pos sz ltac:(clear - Hsz; lia)) as [_ Hrq]. clear - Ha Hrq. lia. }
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
destruct (g_rh_kept (w_H W3) mem7 mF (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) fq hh uu fn hn un p1 p2 Ht ent K _ Tn Hold7 Hinv HKarr7 HKinv HKT KOFF KP) as [Hold9 HKarr9] end.
lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
assert (Rhsz : ew Ev 1125 = Z_to_bv 64 hs) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhsa);
first [change ssx with ss_H2 in HS | idtac "STATE-MISMATCH"] end.
idtac "OK-H8".
rga_hand RH2 HS HJ7 (k + 0); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, ha, ix, Ht, ent, p1, p2, hn, un, fn, K, j, hs.
rga_cbn_cx_goal. change CHT_SIZE with 48. fold Tn. m_inv_auto.
Qed.
End e.
End d.
