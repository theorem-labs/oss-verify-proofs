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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCl9 YCla YClu YCle YClf YCl1 YClt YClr YCls YClg YClh YCli YClj YClk YCll YClp YCkr YCks YCkt YCku YCkv YCkw YCkx YClv.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_gR6 : forall n : nat, rga_fromA B ss_RF (fun _ => INV_R5 B (S n)) -> rga_fromA B ss_RG (fun _ => INV_RG B (S n)) -> rga_from B ss_R5 (INV_R5 B (S n)).
Proof.
intros n RRF RRG. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & ix & Ht & ent & p1 & ppc & npc & p2 & xxc & nxc & hn & un & fn & HTRIP).
rga_cbn_cx HTRIP.
destruct HTRIP as (Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & Rpp & Rxx & Hppc_perm & Hxxc_perm & Rp1 & Hcase1 & Rp2 & Hcase2 & Rhn & Hhn01 & Hhn_gp & Run & Hun01 & Hun_gp & Rfn & Hfn01 & Hfn_gp & Rcnt & RT & Rha & Hha & Rix & Hix & Hnix &
Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & R755 & HTlt).
pose proof Hppc_perm as Hppc_gp. pose proof Hxxc_perm as Hxxc_gp.
unfold g_perm in Hppc_perm, Hxxc_perm. rga_cbn_cx Hppc_perm. rga_cbn_cx Hxxc_perm. destruct Hppc_perm as [Tppc Appc]. destruct Hxxc_perm as [Txxc Axxc].
destruct Hk0 as [Hk0 Hbud].
idtac "OK-A".
unfold ss_R5 in HS.
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
set (TBL := [(fq, 4 * ht_T Ht); (hh, 3 * ht_T Ht); (uu, ht_T Ht); (ppc, npc); (xxc, nxc)] ++ optb hn (3 * Tn) ++ optb un (Tn) ++ optb fn (4 * Tn)).
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
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x82b50.
idtac "OK-R0".
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
assert (Bp1 : 0 <= p1 < 2 ^ 64) by (destruct Hcase1 as [(Hz & _) | (_ & Hz & _)]; [rewrite Hz; clear; lia | rewrite <- Hz; exact Bppc]).
assert (Bp2 : 0 <= p2 < 2 ^ 64) by (destruct Hcase2 as [(Hz & _) | (_ & Hz & _)]; [rewrite Hz; clear; lia | rewrite <- Hz; exact Bxxc]).
assert (Bhn : 0 <= hn < 2 ^ 64).
{ destruct Hhn01 as [Hz | Hz]; [rewrite Hz; clear; lia|].
assert (Hin : In (hn, 3 * Tn) (ablocks B ly3 S3)).
{ apply Hcht_in3. subst TBL. apply in_or_app. right. apply in_or_app. left. unfold optb. replace (hn =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hz; lia). left. reflexivity. }
destruct (g_blk B LAWS _ _ _ _ _ hn _ HAR3 Hin ltac:(clear - HTn24; lia)) as (Hq1 & Hq2 & _). clear - Hq1 Hq2 HTn24 C1. lia. }
assert (Bun : 0 <= un < 2 ^ 64).
{ destruct Hun01 as [Hz | Hz]; [rewrite Hz; clear; lia|].
assert (Hin : In (un, Tn) (ablocks B ly3 S3)).
{ apply Hcht_in3. subst TBL. apply in_or_app. right. apply in_or_app. right; apply in_or_app; left. unfold optb. replace (un =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hz; lia). left. reflexivity. }
destruct (g_blk B LAWS _ _ _ _ _ un _ HAR3 Hin ltac:(clear - HTn24; lia)) as (Hq1 & Hq2 & _). clear - Hq1 Hq2 HTn24 C1. lia. }
assert (Bfn : 0 <= fn < 2 ^ 64).
{ destruct Hfn01 as [Hz | Hz]; [rewrite Hz; clear; lia|].
assert (Hin : In (fn, 4 * Tn) (ablocks B ly3 S3)).
{ apply Hcht_in3. subst TBL. apply in_or_app. right. apply in_or_app. right; apply in_or_app; right. unfold optb. replace (fn =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hz; lia). left. reflexivity. }
destruct (g_blk B LAWS _ _ _ _ _ fn _ HAR3 Hin ltac:(clear - HTn24; lia)) as (Hq1 & Hq2 & _). clear - Hq1 Hq2 HTn24 C1. lia. }
idtac "OK-W".
assert (Hn3T : 3 * ht_T Ht <= npc) by (clear - Hnpc HTngt; lia).
assert (Hn4T : 4 * ht_T Ht <= nxc) by (clear - Hnxc HTngt; lia).
assert (HARRK : forall mF : word -> option byte,
(forall a, 0 <= a < 2 ^ 64 -> ~ (m_ZsP F r a \/ tb <= a < tb + 48) -> aview trbsegs (w_H W3) mF a = aview trbsegs (w_H W3) (ms_mem ms3) a) ->
g_arrs (mrestrict (w_H W3) mF) fq hh uu ppc xxc (ht_frequ Ht) (ht_keys Ht) (ht_used Ht) (ht_pal Ht) (ht_colidx Ht)).
{ intros mF KPF. apply (g_arrs_kept (w_H W3) (ms_mem ms3) mF fq hh uu ppc xxc (ht_T Ht) _ _ _ _ _ Harr (g_lens_of_inv Ht ent Hinv)).
intros a Ha. unfold g_in5 in Ha.
assert (Hq : 0 <= a < 2 ^ 64 /\ ~ (m_ZsP F r a \/ tb <= a < tb + 48)).
{ destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ apply (Hoff3 fq (4 * ht_T Ht) Hfq_l) | apply (Hoff3 hh (3 * ht_T Ht) Hhh_l) | apply (Hoff3 uu (ht_T Ht) Huu_l) | apply (Hoff3 ppc npc Hppc_l) | apply (Hoff3 xxc nxc Hxxc_l) ];
clear - Ha Hrq_fq Hrq_hh Hrq_uu Hrq_ppc Hrq_xxc Hn3T Hn4T; lia. }
exact (KPF a (proj1 Hq) (proj2 Hq)). }
idtac "OK-K".
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
all: match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb1 end.
2: {
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x843a0.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
ga_join HS ss_RF 880%nat rga_deads_RF ltac:(idtac).
pose proof (HARRK _ KP) as Harr1.
rga_hand RRF HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, p1, ppc, npc, p2, xxc, nxc, hn, un, fn.
rga_cbn_cx_goal. change CHT_SIZE with 48. fold Tn. m_inv_auto. }
lazymatch type of Hb1 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (Rx : ew Ex 760 = Z_to_bv 64 p1) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rp1) end.
rewrite branch_ne_U, (U_atom _ 760 p1 Rx Bp1) in Hb1. change (U _ (SLit 0)) with 0 in Hb1. apply Bool.negb_true_iff, Z.eqb_neq in Hb1. clear Rx.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x82b50.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-T1".
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
all: match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb2 end.
2: {
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x843a0.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
ga_join HS ss_RF 880%nat rga_deads_RF ltac:(idtac).
pose proof (HARRK _ KP) as Harr1.
rga_hand RRF HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, p1, ppc, npc, p2, xxc, nxc, hn, un, fn.
rga_cbn_cx_goal. change CHT_SIZE with 48. fold Tn. m_inv_auto. }
lazymatch type of Hb2 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (Rx : ew Ex 776 = Z_to_bv 64 p2) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rp2) end.
rewrite branch_ne_U, (U_atom _ 776 p2 Rx Bp2) in Hb2. change (U _ (SLit 0)) with 0 in Hb2. apply Bool.negb_true_iff, Z.eqb_neq in Hb2. clear Rx.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x82b50.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-T2".
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
all: match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb3 end.
2: {
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x843a0.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
ga_join HS ss_RF 880%nat rga_deads_RF ltac:(idtac).
pose proof (HARRK _ KP) as Harr1.
rga_hand RRF HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, p1, ppc, npc, p2, xxc, nxc, hn, un, fn.
rga_cbn_cx_goal. change CHT_SIZE with 48. fold Tn. m_inv_auto. }
lazymatch type of Hb3 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (Rx : ew Ex 792 = Z_to_bv 64 hn) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhn) end.
rewrite branch_ne_U, (U_atom _ 792 hn Rx Bhn) in Hb3. change (U _ (SLit 0)) with 0 in Hb3. apply Bool.negb_true_iff, Z.eqb_neq in Hb3. clear Rx.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x82b50.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-T3".
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
all: match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb4 end.
2: {
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x843a0.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
ga_join HS ss_RF 880%nat rga_deads_RF ltac:(idtac).
pose proof (HARRK _ KP) as Harr1.
rga_hand RRF HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, p1, ppc, npc, p2, xxc, nxc, hn, un, fn.
rga_cbn_cx_goal. change CHT_SIZE with 48. fold Tn. m_inv_auto. }
lazymatch type of Hb4 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (Rx : ew Ex 808 = Z_to_bv 64 un) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Run) end.
rewrite branch_ne_U, (U_atom _ 808 un Rx Bun) in Hb4. change (U _ (SLit 0)) with 0 in Hb4. apply Bool.negb_true_iff, Z.eqb_neq in Hb4. clear Rx.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x82b50.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-T4".
reshok_bx HS 44%nat.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
all: match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb5 end.
2: {
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x843a0.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
ga_join HS ss_RF 880%nat rga_deads_RF ltac:(idtac).
pose proof (HARRK _ KP) as Harr1.
rga_hand RRF HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, p1, ppc, npc, p2, xxc, nxc, hn, un, fn.
rga_cbn_cx_goal. change CHT_SIZE with 48. fold Tn. m_inv_auto. }
lazymatch type of Hb5 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (Rx : ew Ex 824 = Z_to_bv 64 fn) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfn) end.
rewrite branch_ne_U, (U_atom _ 824 fn Rx Bfn) in Hb5. change (U _ (SLit 0)) with 0 in Hb5. apply Bool.negb_true_iff, Z.eqb_neq in Hb5. clear Rx.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan 0x82b50.
1: m_awrR AG fpos F EFA3 54%nat 67%nat ltac:(fail).
g_kept_run HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS KP.
clear HF HFr HG. norm_ss HS.
idtac "OK-T5".
ga_join HS ss_RG 900%nat rga_deads_RG ltac:(idtac).
pose proof (HARRK _ KP) as Harr1.
rga_hand RRG HS HJ3 k; [rga_E_tac HEE0 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, ix, Ht, ent, p1, ppc, npc, p2, xxc, nxc, hn, un, fn.
rga_cbn_cx_goal. change CHT_SIZE with 48. fold Tn. m_inv_auto.
Qed.
End d.
End c.
