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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClr YCls YClg YClh YCli YClj YClk YCkr YCks YCkt YCku YCkv YCkw YCkx YClv YClp YCl2 YCky YClq.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YClb YCl6.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gH1 : forall (n : nat) (m : nat), rga_fromA B ss_HT (fun _ => INV_HT B (S n) m) -> rga_fromA B ss_H1 (fun _ => INV_H1 B (S n) m) -> rga_from B ss_RH (INV_RH B (S n) m).
Proof.
intros n m RHT RH1. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & ha & ix & Ht & ent & p1 & p2 & hn & un & fn & K & j & HTRIP).
rga_cbn_cx HTRIP.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & Rp1 & Hp1_gp & Rp2 & Hp2_gp & Rhn & Hhn_gp & Run & Hun_gp & Rfn & Hfn_gp & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & R755 & HTlt & HKT & HKarr & HKinv & Rj & Rj4 & Rj3 & Hj & Hmj).
pose proof Hp1_gp as Hp1_perm. pose proof Hp2_gp as Hp2_perm. pose proof Hhn_gp as Hhn_perm. pose proof Hun_gp as Hun_perm. pose proof Hfn_gp as Hfn_perm.
unfold g_perm in Hp1_perm, Hp2_perm, Hhn_perm, Hun_perm, Hfn_perm. rga_cbn_cx Hp1_perm. rga_cbn_cx Hp2_perm. rga_cbn_cx Hhn_perm. rga_cbn_cx Hun_perm. rga_cbn_cx Hfn_perm.
destruct Hp1_perm as [Tp1 Ap1]. destruct Hp2_perm as [Tp2 Ap2]. destruct Hhn_perm as [Thn Ahn]. destruct Hun_perm as [Tun Aun]. destruct Hfn_perm as [Tfn Afn].
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_RH in HS.
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
pose proof (inv_T_pos Ht ent Hinv) as HTpos.
set (uv := usedz Ht j).
assert (Huv : uv = 0 \/ uv = 1) by (subst uv; exact (inv_used01 Ht ent Hinv j Hj)).
destruct Harr as (Af & Ak & Au).
assert (Vuv : mbyte trbsegs (mrestrict (w_H W3) (ms_mem ms3)) (uu + j) = Some (Z_to_bv 8 uv)).
{ destruct (Au (Z.to_nat j) ltac:(clear - Hj L1; unfold zlen in L1; lia)) as [Vb _]. rewrite Z2Nat.id in Vb by (clear - Hj; lia). exact Vb. }
idtac "OK-CELL1".
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ uu (ht_T Ht) HAR3 Huu_in3) as (_ & Huuzone & _ & _).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ uu (ht_T Ht) 7 fpos HAR3 Huu_in3 Hfin3) as HdF_uu.
unfold zdisjoint in HdF_uu. cbn [fst snd] in HdF_uu. change (fs_frame_bytes 7) with 8192 in HdF_uu. rewrite EFA3 in HdF_uu. fold F in HdF_uu.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ uu (ht_T Ht) cid pos HAR3 Huu_in3 HfinS3) as HdC_uu.
unfold zdisjoint in HdC_uu. cbn [fst snd] in HdC_uu. rewrite EFA3 in HdC_uu.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (uu, ht_T Ht) HAR3 HPrt3 ltac:(right; exact Huu_l)) as HzR_uu.
unfold zdisjoint, block_rng in HzR_uu. cbn [fst snd] in HzR_uu. change (req_size RGB_SIZE) with 64 in HzR_uu.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (tb, 48) _ (uu, ht_T Ht) HAR3 HPtb3 ltac:(right; exact Huu_l)) as HzT_uu.
unfold zdisjoint, block_rng in HzT_uu. cbn [fst snd] in HzT_uu. change (req_size 48) with 48 in HzT_uu.
assert (Hcell_rng : 4096 <= uu + j /\ uu + j + 1 <= alloc_ceiling) by (clear - Huu4096 Huuceil Hj; lia).
g_havoc HS 1130%nat [Z_to_bv 64 (uu + j); Z_to_bv 64 uv].
g_havoc_val HS 1130%nat 0%nat (Z_to_bv 64 (uu + j)) E1130.
g_havoc_val HS 1130%nat 1%nat (Z_to_bv 64 uv) E1131.
m_env_fold HS AG.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE1 end.
idtac "OK-CELL2".
assert (Huv8 : 0 <= uv < 256) by (clear - Huv; lia).
g_region HS AG (YQ0b.mkRegion (Some 1130%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 1131 0))])
ltac:(rewrite E1130, unsigned_lit_small by (clear - Hcell_rng C1; lia);
split; [clear - Hcell_rng; lia|]; split; [clear - Hcell_rng C1; lia|]; split;
[ intros o Ho; exfalso; clear - Ho; lia
| apply Forall_cons; [eapply (chunk_ok_val trbsegs _ _ (uu + j) _ _ (SOff 1131 0) uv);
[cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E1131 | clear - Huv8; lia | cbn; clear; lia
| apply (YI0d.val_mem_byte trbsegs); [rewrite Z.add_0_r; exact Vuv | exact Huv8]] | apply Forall_nil] ])
ltac:(first [ clear - Hcell_rng Hceil Hslo FFS Hj Hrq_uu; lia
| destruct Huuzone as [Hz1 Hz2]; clear - Hz1 Hz2 Hj Hrq_uu HF8lo HF8hi HFq HF8 HFceil C1; unfold SB, A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rgb_addframe in *; lia
| clear - HdF_uu Hj Hrq_uu; lia
| clear - HdC_uu Hj Hrq_uu Hflo Hfhi; lia
| clear - HzR_uu Hj Hrq_uu; lia
| clear - HzT_uu Hj Hrq_uu; lia
| match goal with |- ?g => idtac "DISJ-FAIL" g end; fail ]).
idtac "OK-CELL3".
assert (Bj : 0 <= j < 2 ^ 64) by (clear - Hj HT24; lia).
assert (Bcell : 0 <= uu + j < 2 ^ 64) by (clear - Hcell_rng C1; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_alias trbsegs Ev _ _ (SAlu ALU_ADD (SOff 475 0) (SOff 1100 0)) (SOff 1130 0) HS
ltac:(apply U_inj; rewrite (U_atom _ 1130 _ E1130 Bcell); apply (U_add_small_q _ _ _ uu j (U_atom _ 475 uu Ruu Buu) (U_atom _ 1100 j Rj Bj)); [clear - Buu; lia | clear - Bj; lia | clear - Bcell; lia])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
g_fact HS 1130%nat (mkAF 4096 140737479966720 0)
ltac:(rewrite E1130, unsigned_lit_small by exact Bcell; change (2 ^ 0) with 1; split; [clear - Hcell_rng C1; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_fact HS 1131%nat (mkAF 0 1 0)
ltac:(rewrite E1131, unsigned_lit_small by (clear - Huv; lia); change (2 ^ 0) with 1; split; [clear - Huv; lia|]; split; [apply Z.mod_1_r | clear; lia]).
g_cond HS BC_GEU (SOff 1130 0) (SOff 475 0)
ltac:(apply (YCqg.ub_geu_cond _ (SOff 1130 0) (SOff 475 0) (uu + j) uu (U_atom _ 1130 _ E1130 Bcell) (U_atom _ 475 uu Ruu Buu)); clear - Hj; lia).
reshok_bx HS 44%nat.
idtac "OK-AL1".
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x82c40.
idtac "OK-AL2".
all: try (m_obl_cell HJ3 E1130 E44 Huu_in3 ltac:(idtac; first [clear - Hcell_rng C1; lia | clear - Hj Hrq_uu; lia])).
all: try (ga_obl_blk HJ3 Rtb E44 Htb_in3).
idtac "OK-OBL0".
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-KEPT0".
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
idtac "OK-BR".
1: {
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (E1131x : ew Ex 1131 = Z_to_bv 64 uv) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E1131) end.
rewrite branch_ne_U, (U_atom _ 1131 uv E1131x ltac:(clear - Huv; lia)) in Hc. change (U _ (SLit 1)) with 1 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. clear E1131x.
assert (Huv0 : usedz Ht j = 0) by (fold uv; clear - Huv Hc; lia).
idtac "OK-U0".
norm_ss HS.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x82ef0.
idtac "OK-U1".
all: try (m_obl_cell HJ3 E1130 E44 Huu_in3 ltac:(idtac; first [clear - Hcell_rng C1; lia | clear - Hj Hrq_uu; lia])).
all: try (ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-U2".
pose proof HKinv as (_ & (HcntK0 & _) & _).
assert (HcntK64 : 0 <= ht_cnt K < 2 ^ 64) by (clear - HcntK0 HKT HTn24; lia).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rjz : ew Ex 1100 = Z_to_bv 64 j) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rj);
assert (Rj4z : ew Ex 1101 = Z_to_bv 64 (4 * j)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rj4);
assert (Rj3z : ew Ex 1102 = Z_to_bv 64 (3 * j)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rj3);
assert (Rcntz : ew Ex 1120 = Z_to_bv 64 (ht_cnt K)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt) end.
rregU HS (23%bv : bv 5) j ltac:(exact (U_atom _ 1100 j Rjz Bj)) Q23.
rregU HS (26%bv : bv 5) (4 * j) ltac:(exact (U_atom _ 1101 (4 * j) Rj4z ltac:(clear - Hj HT24; lia))) Q26.
rregU HS (20%bv : bv 5) (3 * j) ltac:(exact (U_atom _ 1102 (3 * j) Rj3z ltac:(clear - Hj HT24; lia))) Q20.
slot_val HS (Some 305%nat) 0 40 (Z_to_bv 64 (ht_cnt K)) ltac:(exact (g_denot_off0 _ 1120 _ Rcntz HcntK64)) QC.
ra_join_slots HS ss_HT 1300%nat rga_deads_HT [(Some 305%nat, 0, 40)]
ltac:(idtac; ga_join_val HS 1300%nat 0%nat Q23 N1300; ga_join_val HS 1300%nat 1%nat Q26 N1301; ga_join_val HS 1300%nat 2%nat Q20 N1302; ga_join_val HS 1300%nat 21%nat QC N1321).
idtac "OK-U3".
assert (KOFF : forall b sz, In (b, sz) TBL -> forall a, b <= a < b + sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. apply (Hoff3 b sz (Hcht_l b sz Hb) a).
assert (Hsz : 0 < sz) by (subst TBL; cbn [In] in Hb; clear - Hb HT24 HTn24;
repeat (destruct Hb as [Hb | Hb]; [injection Hb as _ <-; lia|]); destruct Hb).
pose proof (req_size_pos sz ltac:(clear - Hsz; lia)) as [_ Hrq]. clear - Ha Hrq. lia. }
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Hold9 : g_old3 (mrestrict (w_H W3) mF) fq hh uu Ht);
[ apply (g_old3_kept (w_H W3) (ms_mem ms3) mF fq hh uu Ht ent (conj Af (conj Ak Au)) Hinv); intros a Ha;
destruct Ha as [Ha | [Ha | Ha]];
[ destruct (KOFF fq (4 * ht_T Ht) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF hh (3 * ht_T Ht) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF uu (ht_T Ht) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2] ]; exact (KP a Hq1 Hq2)
| assert (HKarr9 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fn hn un p1 p2 K);
[ apply g_cht_of_arrs;
apply (g_arrs_kept (w_H W3) (ms_mem ms3) mF fn hn un p1 p2 Tn _ _ _ _ _ (g_arrs_of_cht _ _ _ _ _ _ _ HKarr) ltac:(rewrite <- HKT; exact (g_lens_of_inv K _ HKinv)));
intros a Ha; unfold g_in5 in Ha;
destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ destruct (KOFF fn (4 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF hn (3 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF un Tn ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF p1 (3 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF p2 (4 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2] ]; exact (KP a Hq1 Hq2)
| ] ] end.
pose proof (rehash_step_unused Ht K j HKinv ltac:(clear - Hj; lia) Huv0) as HKinv9.
idtac "OK-U4".
rga_hand RHT HS HJ3 k; [rga_E_tac HEE1 | ].
exists blk, fim, tb, fq, hh, uu, ha, ix, Ht, ent, p1, p2, hn, un, fn, K, j.
rga_cbn_cx_goal. change CHT_SIZE with 48. fold Tn. m_inv_auto.
}
idtac "OK-U5".
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (E1131x : ew Ex 1131 = Z_to_bv 64 uv) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E1131) end.
rewrite branch_ne_U, (U_atom _ 1131 uv E1131x ltac:(clear - Huv; lia)) in Hc. change (U _ (SLit 1)) with 1 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. clear E1131x.
assert (Huv1 : usedz Ht j = 1) by (fold uv; exact Hc).
norm_ss HS.
idtac "OK-V0".
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Rj3v : ew Ev 1102 = Z_to_bv 64 (3 * j)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rj3);
assert (Rhhv : ew Ev 474 = Z_to_bv 64 hh) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh);
assert (HUkey : U Ev (SAlu ALU_ADD (SAlu ALU_AND (SOff 1102 0) (SLit 4294967295)) (SOff 474 0)) = 3 * j + hh);
[ apply U_add_small_q;
[ rewrite U_and_lit by (clear; lia); rewrite (U_atom _ 1102 (3 * j) Rj3v ltac:(clear - Hj HT24; lia));
change 4294967295 with (Z.ones 32); rewrite Z.land_ones by (clear; lia); apply Z.mod_small; clear - Hj HT24; lia
| exact (U_atom _ 474 hh Rhhv Bhh) | clear - Hj; lia | clear - Bhh; lia | clear - Hhhceil Hj C1; lia ]
| ] end.
g_cond HS BC_GEU (SAlu ALU_ADD (SAlu ALU_AND (SOff 1102 0) (SLit 4294967295)) (SOff 474 0)) (SOff 474 0)
ltac:(apply (YCqg.ub_geu_cond _ _ _ (3 * j + hh) hh HUkey (U_atom _ 474 hh Rhhv Bhh)); clear - Hj; lia).
g_cond HS BC_NE (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU (SAlu ALU_ADD (SAlu ALU_AND (SOff 1102 0) (SLit 4294967295)) (SOff 474 0)) (SLit 1))) (SLit 0)
ltac:(apply (YCqg.ub_nz_cond _ _ (3 * j + hh) HUkey); clear - Hhh4096 Hj; lia).
reshok_bx HS 44%nat.
idtac "OK-V1".
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_col_hash.
idtac "OK-V2".
all: try (m_obl_cell HJ3 E1130 E44 Huu_in3 ltac:(idtac; first [clear - Hcell_rng C1; lia | clear - Hj Hrq_uu; lia])).
all: try (ga_obl_blk HJ3 Rtb E44 Htb_in3).
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-V3".
m_join_slots_win HS ss_H1 1200%nat rga_deads_H1 (@nil (option nat * Z * Z)) ltac:(idtac).
idtac "OK-V4".
assert (KOFF : forall b sz, In (b, sz) TBL -> forall a, b <= a < b + sz -> 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ intros b sz Hb a Ha. apply (Hoff3 b sz (Hcht_l b sz Hb) a).
assert (Hsz : 0 < sz) by (subst TBL; cbn [In] in Hb; clear - Hb HT24 HTn24;
repeat (destruct Hb as [Hb | Hb]; [injection Hb as _ <-; lia|]); destruct Hb).
pose proof (req_size_pos sz ltac:(clear - Hsz; lia)) as [_ Hrq]. clear - Ha Hrq. lia. }
lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mF a = _ =>
assert (Hold9 : g_old3 (mrestrict (w_H W3) mF) fq hh uu Ht);
[ apply (g_old3_kept (w_H W3) (ms_mem ms3) mF fq hh uu Ht ent (conj Af (conj Ak Au)) Hinv); intros a Ha;
destruct Ha as [Ha | [Ha | Ha]];
[ destruct (KOFF fq (4 * ht_T Ht) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF hh (3 * ht_T Ht) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF uu (ht_T Ht) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2] ]; exact (KP a Hq1 Hq2)
| assert (HKarr9 : cht_arrays trbsegs (mrestrict (w_H W3) mF) fn hn un p1 p2 K);
[ apply g_cht_of_arrs;
apply (g_arrs_kept (w_H W3) (ms_mem ms3) mF fn hn un p1 p2 Tn _ _ _ _ _ (g_arrs_of_cht _ _ _ _ _ _ _ HKarr) ltac:(rewrite <- HKT; exact (g_lens_of_inv K _ HKinv)));
intros a Ha; unfold g_in5 in Ha;
destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ destruct (KOFF fn (4 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF hn (3 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF un Tn ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF p1 (3 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2]
| destruct (KOFF p2 (4 * Tn) ltac:(subst TBL; cbn [In]; tauto) a Ha) as [Hq1 Hq2] ]; exact (KP a Hq1 Hq2)
| ] ] end.
idtac "OK-V5".
rga_hand RH1 HS HJ3 k; [rga_E_tac HEE1 | ].
exists blk, fim, tb, fq, hh, uu, ha, ix, Ht, ent, p1, p2, hn, un, fn, K, j.
rga_cbn_cx_goal. change CHT_SIZE with 48. fold Tn. m_inv_auto.
Qed.
End d.
End c.
