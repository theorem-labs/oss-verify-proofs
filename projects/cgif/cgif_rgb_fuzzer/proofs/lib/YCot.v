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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCn8 YCn9 YCna YCnf YCoi YCoj YCok YCol YCom YCon YCoo YCnd YCnb.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCil YCim YCin YP16 YI0f YI09 YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YChh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCpg YCnn YCp7 YCp8.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_q3 : rga_fromA B ss_Q3 (fun _ => INV_Q3 B) -> rga_from B ss_Q2 (INV_CX B).
Proof.
intros RC. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & dn & Tt & cnt & tr & Hk0 & Hnodes & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & (Rdn & Tdn & Adn) & Rcnt & RT & Rha & Hha &
(av & Rav & Hav) & HTch & Hcnt & Rroot & Htree & Hfull & Hth & Hwft & Hmok).
destruct Hk0 as [Hk0 Hbud].
unfold ss_Q2 in HS.
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
assert (Hcnt0 : 0 <= 4 * cnt) by (clear - Hcnt; lia).
pose proof (req_size_pos (4 * cnt) Hcnt0) as Hrqdn.
assert (Hdn_in3 : In (dn, 4 * cnt) (ablocks B ly3 S3)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPm3|]. apply in_or_app; right. cbn [cht_blocks app]. do 8 right. left. reflexivity. }
set (Er := fun a : Z => dn <= a < dn + req_size (4 * cnt)).
set (news3 := [(blk, fmt * N); (fim, N)] ++ ((tb, 48) :: cht_blocks fq hh uu pp xx Tt) ++ [(dn, 4 * cnt)] ++ tree_blocks tr) in *.
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
assert (HPr3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: ((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ news3))
by (eapply Permutation_trans; [exact HPm3|]; exact (Permutation_app_tail news3 HPerm')).
assert (Hdn_l : In (dn, 4 * cnt) (((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ news3))
by (apply in_or_app; right; subst news3; cbn [cht_blocks app]; do 8 right; left; reflexivity).
assert (HnR : forall a, r <= a < r + 64 -> ~ Er a).
{ intros a Ha Hb. pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (dn, 4 * cnt) HAR3 HPr3 Hdn_l) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. change (req_size RGB_SIZE) with 64 in Dd. unfold Er in Hb. clear - Dd Ha Hb. lia. }
assert (HnC : forall a, cfp <= a < cfp + 24 -> ~ Er a).
{ intros a Ha Hb. pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ dn (4 * cnt) cid pos HAR3 Hdn_in3 HfinS3) as Dd.
rewrite EFA3 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. unfold Er in Hb. clear - Dd Ha Hb Hflo Hfhi. lia. }
assert (HnF : forall a, F <= a < F + 8192 -> ~ Er a).
{ intros a Ha Hb. pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ dn (4 * cnt) 7 fpos HAR3 Hdn_in3 Hfin3) as Dd.
rewrite EFA3 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. unfold Er in Hb. clear - Dd Ha Hb. lia. }
assert (HnS : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ Er a).
{ intros a Ha Hb. destruct (rga_blk_range B LAWS ly3 S3 _ _ _ dn (4 * cnt) HAR3 Hdn_in3) as (_ & (_ & Hbz) & _).
unfold Er in Hb. clear - Ha Hb Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_atD trbsegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 _ k dn (4 * cnt) (-576) (Z_to_bv 64 540120) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 Hdn_in3) end.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. first [reflexivity | exact Rdn | rewrite Rdn; reflexivity].
- unfold spZ. rewrite Rsp. ga_evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rga_room Hev Hbud; (try (unfold EV_HD in Hk0); clear - Hk0 HEVv Hnodes; rga_lia).
- apply (achain_chain_pre ly3 _ (spZ regs - 576) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity.
- exact Tdn. }
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & (l1_8 & l2_8 & El8 & Eab8) & Hfrs8 & Hd8 & HK8).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
set (news8 := [(blk, fmt * N); (fim, N)] ++ ((tb, 48) :: cht_blocks fq hh uu pp xx Tt) ++ tree_blocks tr).
assert (HPm8 : Permutation (ablocks B ly8 S8) (ablocks B ly S ++ news8)).
{ rewrite Eab8. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1_8 l2_8 (dn, 4 * cnt)). rewrite <- El8.
eapply Permutation_trans; [|apply Permutation_sym; exact HPm3]. subst news3 news8. YI0g.perm_tac. }
pose proof HJ8 as (HAR8 & Hly8 & _).
assert (EFA8 : forall c p, frame_addr ly8 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly8 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin8 : In (7, fpos) (frames S8)) by (rewrite Hfrs8; exact Hfin3).
assert (HfinS8 : In (cid, pos) (frames S8)) by (rewrite Hfrs8; exact HfinS3).
assert (Hrin8 : In (r, 64) (ablocks B ly8 S8)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm8 | apply in_or_app; left; exact Hrin]).
assert (Htb_in8 : In (tb, 48) (ablocks B ly8 S8)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm8 | apply in_or_app; right; subst news8; right; right; left; reflexivity]).
assert (HnO8 : forall b sz i, In (b, sz) (ablocks B ly8 S8) -> 0 <= i < req_size sz -> ~ Er (b + i)).
{ intros b sz i Hb Hi Hbb. rewrite Eab8 in Hb.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (dn, 4 * cnt) (l1_8 ++ l2_8) (b, sz) HAR3 ltac:(rewrite El8; apply Permutation_sym; apply Permutation_middle) Hb) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. unfold Er in Hbb. clear - Dd Hi Hbb. lia. }
assert (HnT : forall a, tb <= a < tb + 48 -> ~ Er a).
{ intros a Ha Hb. apply (HnO8 tb 48 (a - tb) Htb_in8 ltac:(change (req_size 48) with 48; clear - Ha; lia)). replace (tb + (a - tb)) with a by (clear; lia). exact Hb. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR8 Hfin8) as (_ & _ & HFpres8 & HFSpres8). change (fs_frame_bytes 7) with 8192 in HFpres8, HFSpres8.
change (8192 / 8) with 1024 in HFSpres8. rewrite EFA8 in HFpres8, HFSpres8. fold F in HFpres8, HFSpres8.
ga_aconsts HROD HJ8 Kgot8 Kcell8 Kguar8 Kuar8 Vgr8.
reseat HS HJ8 HP8 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ ga_keptK HK8 HJ8 AG Usp Hrin3 Hrin8 HfinS3 Hfin3 HFpres8 HFSpres8 HnR HnC HnF HnS EFA3 F Kgot0 Kgot8 Kcell0 Kcell8 Kguar0 Kguar8 Kuar0 Kuar8 Vgr0 Vgr8
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 305%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs _ LAWS); [exact HK8 | exact (proj1 HJ8) | exact Htb_in8 | ga_evalE AG | exact Htb_in3 | lia | change (req_size 48) with 48; lia | lia | lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnT; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot8 into Kgot0. rename Kcell8 into Kcell0. rename Kguar8 into Kguar0. rename Kuar8 into Kuar0. rename Vgr8 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ8 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE8 end.
pose proof (EFA8 7 fpos) as EFA87. fold F in EFA87.
assert (Htr_in8 : forall b sz, In (b, sz) (tree_blocks tr) -> In (b, sz) (ablocks B ly8 S8))
by (intros b sz Hb; eapply Permutation_in; [apply Permutation_sym; exact HPm8 | apply in_or_app; right; subst news8; cbn [cht_blocks app]; do 8 right; exact Hb]).
assert (Htree8 : tree_at trbsegs (mrestrict (w_H W8) mem8) tr).
{ apply (rg_tree_at_kept (w_H W3) (w_H W8) (ms_mem ms3) mem8 tr Htree). intros b sz Hb i Hi.
destruct HK8 as (_ & K2 & _). apply (K2 b sz i); [|exact Hi | exact (HnO8 b sz i (Htr_in8 b sz Hb) Hi)].
rewrite El8. pose proof (Htr_in8 b sz Hb) as Hq0. rewrite Eab8 in Hq0. apply in_app_or in Hq0. apply in_or_app. destruct Hq0 as [Hq | Hq]; [left; exact Hq | right; right; exact Hq]. }
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ8 SHOK GBspan A_wrap_malloc.
1: ga_awrR AG fpos F EFA8 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
assert (HPrt8 : Permutation (ablocks B ly8 S8) ((r, RGB_SIZE) :: (tb, 48) :: (((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx Tt ++ tree_blocks tr)))
by (eapply Permutation_trans; [exact HPm8|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; subst news8; YI0g.perm_tac).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Htree9 : tree_at trbsegs (mrestrict (w_H W8) (ms_mem msX)) tr) end.
{ apply (rg_tree_at_kept (w_H W8) (w_H W8) mem8 _ tr Htree8). intros b sz Hb i Hi.
pose proof (m_blk_off_zs2 B LAWS ly8 S8 _ _ _ b sz r tb _ fpos HAR8 HPrt8 ltac:(apply in_or_app; right; cbn [cht_blocks app]; do 7 right; exact Hb) Hfin8 (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2).
rewrite EFA8 in Hq2. fold F in Hq2. apply UN2; assumption. }
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with ss_Q3 in HS | idtac "STATE-MISMATCH"] end.
assert (Hfrs8' : frames S8 = (7, fpos) :: frames S) by (rewrite Hfrs8; exact Hfrs3).
rga_hand RC HS HJ8 (k + 1); [rga_E_tac HEE8 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, Tt, cnt, tr.
split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hnodes|]. split; [exact Hfmt|]. split; [exact HPm8|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Tfq | exact Afq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Thh | exact Ahh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Tuu | exact Auu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Tpp | exact App]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Txx | exact Axx]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rha|].
split; [exact Hha|].
split; [exists av; split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rav | exact Hav]|].
split; [exact HTch|]. split; [exact Hcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rroot|].
split; [exact Htree9|]. split; [exact Hfull|]. split; [exact Hth | exact Hwft].
Qed.
End e.
End d.
