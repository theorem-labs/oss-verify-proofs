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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCps YCq7.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0f YCd3.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClr YCls YClg YClh YCli YClj YClk YCll YClp YClm YCln YClo YCkr YCks YCkt YCku YCkv YCkw YCkx YClv.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gF4 : forall n : nat, rga_fromA B ss_X38b (fun _ => INV_X38b B) -> rga_from B ss_RF3 (INV_RF3 B (S n)).
Proof.
intros n RX38b. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & p1 & ppc & npc & p2 & xxc & nxc & fn & HTRIP).
rga_cbn_cx HTRIP.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & Rpp & Rxx & Hppc_perm & Hxxc_perm & Rp1 & Hcase1 & Rp2 & Hcase2 & Rfn & Hfn01 & Hfn_gp & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & R755 & HTlt).
pose proof Hppc_perm as Hppc_gp. pose proof Hxxc_perm as Hxxc_gp.
unfold g_perm in Hppc_perm, Hxxc_perm. rga_cbn_cx Hppc_perm. rga_cbn_cx Hxxc_perm. destruct Hppc_perm as [Tppc Appc]. destruct Hxxc_perm as [Txxc Axxc].
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_RF3 in HS.
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
assert (Hnpc : npc = 3 * ht_T Ht \/ npc = 3 * Tn) by (destruct Hcase1 as [(_ & _ & Hx) | (_ & _ & Hx)]; [left | right]; exact Hx).
assert (Hnpc0 : 1572927 <= npc <= 50331648) by (clear - Hnpc HT24 HTn24; lia).
assert (Hnxc : nxc = 4 * ht_T Ht \/ nxc = 4 * Tn) by (destruct Hcase2 as [(_ & _ & Hx) | (_ & _ & Hx)]; [left | right]; exact Hx).
assert (Hnxc0 : 2097236 <= nxc <= 67108864) by (clear - Hnxc HT24 HTn24; lia).
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
set (TBL := [(fq, 4 * ht_T Ht); (hh, 3 * ht_T Ht); (uu, ht_T Ht); (ppc, npc); (xxc, nxc)] ++ optb fn (4 * Tn)).
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
assert (Hfq_in3 : In (fq, 4 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; apply in_or_app; left; cbn [In]; tauto).
assert (Hfq_l : In (fq, 4 * ht_T Ht) lrest) by (apply Hcht_l; subst TBL; apply in_or_app; left; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ fq _ HAR3 Hfq_in3 ltac:(clear - HT24; lia)) as (Hfq4096 & Hfqceil & Hfq16 & Hfqpres).
pose proof (req_size_pos (4 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_fq].
assert (Bfq : 0 <= fq < 2 ^ 64) by (clear - Hfq4096 Hfqceil HT24 C1; lia).
assert (Hhh_in3 : In (hh, 3 * ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; apply in_or_app; left; cbn [In]; tauto).
assert (Hhh_l : In (hh, 3 * ht_T Ht) lrest) by (apply Hcht_l; subst TBL; apply in_or_app; left; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ hh _ HAR3 Hhh_in3 ltac:(clear - HT24; lia)) as (Hhh4096 & Hhhceil & Hhh16 & Hhhpres).
pose proof (req_size_pos (3 * ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_hh].
assert (Bhh : 0 <= hh < 2 ^ 64) by (clear - Hhh4096 Hhhceil HT24 C1; lia).
assert (Huu_in3 : In (uu, ht_T Ht) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; apply in_or_app; left; cbn [In]; tauto).
assert (Huu_l : In (uu, ht_T Ht) lrest) by (apply Hcht_l; subst TBL; apply in_or_app; left; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ uu _ HAR3 Huu_in3 ltac:(clear - HT24; lia)) as (Huu4096 & Huuceil & Huu16 & Huupres).
pose proof (req_size_pos (ht_T Ht) ltac:(clear - HT24; lia)) as [_ Hrq_uu].
assert (Buu : 0 <= uu < 2 ^ 64) by (clear - Huu4096 Huuceil HT24 C1; lia).
assert (Hppc_in3 : In (ppc, npc) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; apply in_or_app; left; cbn [In]; tauto).
assert (Hppc_l : In (ppc, npc) lrest) by (apply Hcht_l; subst TBL; apply in_or_app; left; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ ppc _ HAR3 Hppc_in3 ltac:(clear - Hnpc0; lia)) as (Hppc4096 & Hppcceil & Hppc16 & Hppcpres).
pose proof (req_size_pos (npc) ltac:(clear - Hnpc0; lia)) as [_ Hrq_ppc].
assert (Bppc : 0 <= ppc < 2 ^ 64) by (clear - Hppc4096 Hppcceil Hnpc0 C1; lia).
assert (Hxxc_in3 : In (xxc, nxc) (ablocks B ly3 S3)) by (apply Hcht_in3; subst TBL; apply in_or_app; left; cbn [In]; tauto).
assert (Hxxc_l : In (xxc, nxc) lrest) by (apply Hcht_l; subst TBL; apply in_or_app; left; cbn [In]; tauto).
destruct (g_blk B LAWS _ _ _ _ _ xxc _ HAR3 Hxxc_in3 ltac:(clear - Hnxc0; lia)) as (Hxxc4096 & Hxxcceil & Hxxc16 & Hxxcpres).
pose proof (req_size_pos (nxc) ltac:(clear - Hnxc0; lia)) as [_ Hrq_xxc].
assert (Bxxc : 0 <= xxc < 2 ^ 64) by (clear - Hxxc4096 Hxxcceil Hnxc0 C1; lia).
assert (Bix : 0 <= ix < 2 ^ 64) by (clear - Hix HN; unfold RGB_NMAX in HN; lia).
idtac "OK-BLK".
assert (Bfn : 0 <= fn < 2 ^ 64).
{ destruct Hfn01 as [Hz | Hz]; [rewrite Hz; clear; lia|].
assert (Hin : In (fn, 4 * Tn) (ablocks B ly3 S3)).
{ apply Hcht_in3. subst TBL. apply in_or_app. right. unfold optb. replace (fn =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hz; lia). left. reflexivity. }
destruct (g_blk B LAWS _ _ _ _ _ fn _ HAR3 Hin ltac:(clear - HTn24; lia)) as (Hq1 & Hq2 & _). clear - Hq1 Hq2 HTn24 C1. lia. }
idtac "OK-W".
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rregU HS (10%bv : bv 5) fn ltac:(apply (U_atom _ 824 fn Rfn Bfn)) Ra0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
set (nfr := 4 * Tn).
assert (Hnfr : 64513 <= nfr <= 67108864) by (subst nfr; clear - HTn24; lia).
set (Er := fun a : Z => fn <> 0 /\ fn <= a < fn + req_size nfr).
set (bl8 := ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ (tb, 48) :: [(fq, 4 * ht_T Ht); (hh, 3 * ht_T Ht); (uu, ht_T Ht); (ppc, npc); (xxc, nxc)]).
assert (HPv3 : fn <> 0 -> Permutation (ablocks B ly3 S3) ((fn, nfr) :: bl8)).
{ intros Hnz. eapply Permutation_trans; [exact HPm3|]. subst bl8 TBL nfr. replace (optb fn (4 * Tn)) with [(fn, 4 * Tn)] by (unfold optb; replace (fn =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz); reflexivity). YI0g.perm_tac. }
assert (HPz3 : fn = 0 -> Permutation (ablocks B ly3 S3) bl8).
{ intros Hz. eapply Permutation_trans; [exact HPm3|]. subst bl8 TBL. replace (optb fn (4 * Tn)) with (@nil (Z * Z)) by (rewrite Hz; reflexivity). YI0g.perm_tac. }
assert (HvIn3 : fn <> 0 -> In (fn, nfr) (ablocks B ly3 S3)) by (intros Hnz; eapply Permutation_in; [apply Permutation_sym; exact (HPv3 Hnz) | left; reflexivity]).
assert (Hbl8_in3 : forall b z, In (b, z) bl8 -> In (b, z) (ablocks B ly3 S3)).
{ intros b z Hb. destruct (Z.eq_dec fn 0) as [Hz | Hnz]; (eapply Permutation_in; [apply Permutation_sym; first [exact (HPz3 Hz) | exact (HPv3 Hnz)] | first [exact Hb | right; exact Hb]]). }
assert (HnO : forall b z a, In (b, z) bl8 -> b <= a < b + req_size z -> ~ Er a).
{ intros b z a Hb Ha [Hnz Hin]. pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (fn, nfr) bl8 (b, z) HAR3 (HPv3 Hnz) Hb) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hin. lia. }
assert (Hr_bl8 : In (r, 64) bl8) by (subst bl8; apply in_or_app; left; exact Hrin).
assert (Htb_bl8 : In (tb, 48) bl8) by (subst bl8; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (HnR : forall a, r <= a < r + 64 -> ~ Er a) by (intros a Ha; apply (HnO r 64 a Hr_bl8); change (req_size 64) with 64; exact Ha).
assert (HnT : forall a, tb <= a < tb + 48 -> ~ Er a) by (intros a Ha; apply (HnO tb 48 a Htb_bl8); change (req_size 48) with 48; exact Ha).
assert (HnC : forall a, cfp <= a < cfp + 24 -> ~ Er a).
{ intros a Ha [Hnz Hb]. pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fn nfr cid pos HAR3 (HvIn3 Hnz) HfinS3) as Dd.
rewrite EFA3 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hb Hflo Hfhi. lia. }
assert (HnF : forall a, F <= a < F + 8192 -> ~ Er a).
{ intros a Ha [Hnz Hb]. pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fn nfr 7 fpos HAR3 (HvIn3 Hnz) Hfin3) as Dd.
rewrite EFA3 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. clear - Dd Ha Hb. lia. }
assert (HnS : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ Er a).
{ intros a Ha [Hnz Hb]. destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fn nfr HAR3 (HvIn3 Hnz)) as (_ & (_ & Hbz) & _).
clear - Ha Hb Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
idtac "OK-S0".
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) =>
assert (CONT : forall (W8 : world trbsegs) ly8 S8 regs8 mem8 md8,
ajournal trbsegs B TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)] ly8 S8 W8 mem8 md8 (k + 1) ->
aregs_preserved (ms_regs ms3) regs8 ->
Permutation (ablocks B ly8 S8) bl8 ->
frames S8 = frames S3 -> bud_le S3 S8 1 0 0 0 ->
acall_kept trbsegs B ly3 S3 W3 (ms_mem ms3) W8 mem8 (spZ regs + -576 - ASTACK) (spZ regs + -576) Er ->
SRr trbsegs W8 (mkCfg (mkst regs8 (Z_to_bv 64 541684) mem8 (seg_rom trbsegs)) md8) (rga_post B cxv)) end.
{ intros W8 ly8 S8 regs8 mem8 md8 HJ8 HP8 HPm8 Hfrs8 Hd8 HK8.
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
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Rfqz : ew Ex 473 = Z_to_bv 64 fq) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq);
assert (Rhhz : ew Ex 474 = Z_to_bv 64 hh) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh);
assert (Ruuz : ew Ex 475 = Z_to_bv 64 uu) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu);
assert (Rppz : ew Ex 900 = Z_to_bv 64 ppc) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp);
assert (Rxxz : ew Ex 901 = Z_to_bv 64 xxc) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx) end.
slot_val HS (Some 305%nat) 0 0 (Z_to_bv 64 fq) ltac:(exact (g_denot_off0 _ 473 fq Rfqz Bfq)) QF.
slot_val HS (Some 305%nat) 0 8 (Z_to_bv 64 hh) ltac:(exact (g_denot_off0 _ 474 hh Rhhz Bhh)) QH.
slot_val HS (Some 305%nat) 0 16 (Z_to_bv 64 uu) ltac:(exact (g_denot_off0 _ 475 uu Ruuz Buu)) QU.
slot_val HS (Some 305%nat) 0 24 (Z_to_bv 64 ppc) ltac:(exact (g_denot_off0 _ 900 ppc Rppz Bppc)) QP.
slot_val HS (Some 305%nat) 0 32 (Z_to_bv 64 xxc) ltac:(exact (g_denot_off0 _ 901 xxc Rxxz Bxxc)) QX.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let fa := eval vm_compute in (filter (fun p : nat * afact => negb (Nat.leb 500 (fst p) && Nat.ltb (fst p) 600)) (f_atoms (ss_facts ssx))) in
let cs := eval vm_compute in (f_conds (ss_facts ssx)) in
let al := eval vm_compute in (f_alias (ss_facts ssx)) in
let HS3 := fresh "HS3" in
pose proof (st_ok_facts_incl3 trbsegs Ex ssx msx fa cs al HS ltac:(ga_incl_lit_tac) ltac:(ga_incl_lit_tac) ltac:(ga_incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
idtac "OK-X0".
m_join_slots_win HS ss_X38b 500%nat rga_deads_X38 [(Some 305%nat, 0, 0); (Some 305%nat, 0, 8); (Some 305%nat, 0, 16); (Some 305%nat, 0, 24); (Some 305%nat, 0, 32)]
ltac:(idtac; ga_join_val HS 500%nat 19%nat QF N519; ga_join_val HS 500%nat 20%nat QH N520; ga_join_val HS 500%nat 21%nat QU N521;
ga_join_val HS 500%nat 22%nat QP N522; ga_join_val HS 500%nat 23%nat QX N523).
idtac "OK-X1".
assert (Hnz5 : fq <> 0 /\ hh <> 0 /\ uu <> 0 /\ ppc <> 0 /\ xxc <> 0) by (clear - Hfq4096 Hhh4096 Huu4096 Hppc4096 Hxxc4096; lia).
assert (HPm8' : Permutation (ablocks B ly8 S8)
(ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++
(tb, 48) :: optb fq (4 * ht_T Ht) ++ optb hh (3 * ht_T Ht) ++ optb uu (ht_T Ht) ++ optb ppc npc ++ optb xxc nxc)).
{ eapply Permutation_trans; [exact HPm8|]. subst bl8. unfold optb. destruct Hnz5 as (Z1 & Z2 & Z3 & Z4 & Z5).
rewrite (proj2 (Z.eqb_neq fq 0) Z1), (proj2 (Z.eqb_neq hh 0) Z2), (proj2 (Z.eqb_neq uu 0) Z3), (proj2 (Z.eqb_neq ppc 0) Z4), (proj2 (Z.eqb_neq xxc 0) Z5).
cbn [app]. apply Permutation_refl. }
assert (Hk9 : k + 1 + 8 <= EV_RGBADD) by (rewrite HEVv; clear - Hk0 Hrk4; lia).
assert (Hfrs8' : frames S8 = (7, fpos) :: frames S) by (rewrite Hfrs8; exact Hfrs3).
rga_hand RX38b HS HJ8 (k + 1); [rga_E_tac HEE8 | ].
exists blk, fim, tb, fq, hh, uu, ppc, xxc, (4 * ht_T Ht), (3 * ht_T Ht), (ht_T Ht), npc, nxc.
rga_cbn_cx_goal.
split; [split; [exact Hk9 | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact HPm8'|].
split; [split; [m_ewT | split; [exact Tblk | exact Ablk]]|].
split; [split; [m_ewT | split; [exact Tfim | exact Afim]]|].
split; [split; [m_ewT | split; [exact Ttb | exact Atb]]|].
unfold rga_optblk. rga_cbn_cx_goal.
split; [split; [exact N519 | split; [exact Bfq | intros _; split; [exact Tfq | exact Afq]]]|].
split; [split; [exact N520 | split; [exact Bhh | intros _; split; [exact Thh | exact Ahh]]]|].
split; [split; [exact N521 | split; [exact Buu | intros _; split; [exact Tuu | exact Auu]]]|].
split; [split; [exact N522 | split; [exact Bppc | intros _; split; [exact Tppc | exact Appc]]]|].
split; [exact N523 | split; [exact Bxxc | intros _; split; [exact Txxc | exact Axxc]]]. }
idtac "OK-CONT".
destruct (Z.eq_dec fn 0) as [Hvz | Hvnz].
-
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_null_atD trbsegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 _ k (-576) (Z_to_bv 64 541684) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- rewrite Ra0, Hvz. reflexivity.
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
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & HPm8 & Hfrs8 & Hd8 & HK8).
apply (CONT W8 ly8 S8 regs8 mem8 md8 HJ8 HP8); [| exact Hfrs8 | exact Hd8 | eapply acall_kept_mono_E; [exact HK8 | intros a []]].
eapply Permutation_trans; [exact HPm8|]. exact (HPz3 Hvz).
-
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_atD trbsegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 _ k fn nfr (-576) (Z_to_bv 64 541684) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 (HvIn3 Hvnz)) end.
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
- pose proof (Hfn_gp Hvnz) as Hgq. unfold g_perm in Hgq. rga_cbn_cx Hgq. exact (proj1 Hgq). }
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & (l1_8 & l2_8 & El8 & Eab8) & Hfrs8 & Hd8 & HK8).
apply (CONT W8 ly8 S8 regs8 mem8 md8 HJ8 HP8); [| exact Hfrs8 | exact Hd8 | eapply acall_kept_mono_E; [exact HK8 | intros a Ha; split; [exact Hvnz | exact Ha]]].
rewrite Eab8. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1_8 l2_8 (fn, nfr)). rewrite <- El8. apply Permutation_sym. exact (HPv3 Hvnz).
Qed.
End e.
End d.
