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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCpg YCp3 YCp8 YCpe YCp9.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_q4 : rga_fromA B ss_XT2 (fun _ => INV_XT2 B) -> rga_fromA B ss_Q4 (fun _ => INV_Q4 B) -> rga_from B ss_Q3 (INV_Q3 B).
Proof.
intros RXT2 RC. rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & Tt & cnt & tr & Hk0 & Hnodes & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha &
(av & Rav & Hav) & HTch & Hcnt & Rroot & Htree & Hfull & Hth & Hwft).
destruct Hk0 as [Hk0 Hbud].
unfold ss_Q3 in HS.
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
pose proof Hrgb as Hrgb'. cbn [obj_at LAY_Rgb] in Hrgb'.
destruct Hrgb' as (_ & _ & _ & _ & _ & _ & _ & [_ R42v] & [_ R44v] & _).
cbn [fst snd N.to_nat Z.of_N] in R42v, R44v.
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
assert (HN31 : 0 <= Hd * Wd < 2 ^ 31) by (rewrite <- HNhw; clear - HN1 HN; unfold RGB_NMAX in *; lia).
set (nflt := 4 * (fmt * N)).
assert (Hnflt : 12 <= nflt <= 160000) by (subst nflt; clear - HfN; unfold RGB_NMAX in HfN; lia).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
assert (UfN : U E (SMdw M_MUL (SExt true 32 (SOff 46 0)) (SMdw M_MUL (SOff 40 0) (SOff 39 0))) = fmt * N).
{ rewrite HNhw. apply U_mulw_small; [apply (U_sext32_small E 46 fmt E46); clear - Hfmt; lia | apply (U_HW E 40 39 Hd Wd E40 E39); [clear - R44v; cbn in R44v; lia | clear - R42v; cbn in R42v; lia | exact HN31]
| clear - Hfmt; lia | clear - HN31; lia | rewrite <- HNhw; clear - HfN; unfold RGB_NMAX in HfN; lia]. }
rregU HS (10%bv : bv 5) nflt ltac:(subst nflt; apply m_U_idx4; [exact UfN | clear - HfN; unfold RGB_NMAX in HfN; lia]) Ha0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340936) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (HEVhd : EV_HD = 68) by reflexivity.
assert (HT24 : 0 < Tt <= 16777259) by (clear - HTch; unfold ts_chain in HTch; cbn [In] in HTch; lia).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_atD trbsegs B LAWS Hsegs errno_low ML AMALLOC _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 _ k nflt (-576) (Z_to_bv 64 540144) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ha0.
- unfold MALLOC_MAX. clear - Hnflt. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPm3), !bsum_app, <- (blocks_bytes_bsum B ly S), q_bsum_tree_blocks. cbn [bsum fold_right snd cht_blocks].
clear - Hlive HfN HN1 HN Hnflt HT24 Hnodes. unfold LIVE_RGBADD, LIVE_MAX, RGB_NMAX, NODE_SIZE in *. lia.
- unfold spZ. rewrite Rsp. ga_evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rga_room Hev Hbud; (clear - Hk0 HEVv HEVhd Hnodes; rga_lia).
- assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
apply (achain_chain_pre ly3 _ (spZ regs - 576) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & flt & -> & HJ7 & HP7 & Ha07 & Hfrs7 & Hd7 & Hres7).
apply rga_d_malloc in Hd7; [|clear - Hnflt; lia].
clear Ha0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
destruct (mres_kept B ly3 S3 W3 _ W7 mem7 ly7 S7 _ _ flt nflt Hres7) as (HK7 & HBin7 & HfltIn).
pose proof (mres_range B LAWS ly7 S7 W7 mem7 md7 ly3 S3 flt nflt _ _ (proj1 HJ7) Hres7) as Hrng7.
pose proof HJ7 as (HAR7 & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin7 : In (7, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin3).
assert (HfinS7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact HfinS3).
assert (Hrin7 : In (r, 64) (ablocks B ly7 S7)) by (apply HBin7; exact Hrin3).
assert (Htb_in7 : In (tb, 48) (ablocks B ly7 S7)) by (apply HBin7; exact Htb_in3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA7 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
assert (HnF7 : forall a, F <= a < F + 8192 -> ~ (flt <> 0 /\ flt <= a < flt + req_size nflt)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ flt nflt 7 fpos HAR7 (HfltIn Hnz) Hfin7) as Dd.
rewrite EFA7 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. clear - Dd Ha Hin. lia. }
assert (HnC7 : forall a, cfp <= a < cfp + 24 -> ~ (flt <> 0 /\ flt <= a < flt + req_size nflt)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ flt nflt cid pos HAR7 (HfltIn Hnz) HfinS7) as Dd.
rewrite EFA7 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hin Hflo Hfhi. lia. }
assert (HnO7 : forall b sz a, In (b, sz) (ablocks B ly3 S3) -> b <= a < b + req_size sz -> ~ (flt <> 0 /\ flt <= a < flt + req_size nflt)).
{ intros b sz a Hb Ha [Hnz Hin]. destruct Hres7 as [(Hz & _) | (_ & Ebl7 & _)]; [exact (Hnz Hz)|].
pose proof (rg_sep_head_in B LAWS ly7 S7 _ _ _ (flt, nflt) (ablocks B ly3 S3) (b, sz) HAR7 ltac:(rewrite Ebl7; apply Permutation_sym; apply Permutation_cons_append) Hb) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hin. lia. }
assert (HnR7 : forall a, r <= a < r + 64 -> ~ (flt <> 0 /\ flt <= a < flt + req_size nflt))
by (intros a Ha; apply (HnO7 r 64 a Hrin3); change (req_size 64) with 64; exact Ha).
assert (HnT7 : forall a, tb <= a < tb + 48 -> ~ (flt <> 0 /\ flt <= a < flt + req_size nflt))
by (intros a Ha; apply (HnO7 tb 48 a Htb_in3); change (req_size 48) with 48; exact Ha).
assert (HnS7 : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ (flt <> 0 /\ flt <= a < flt + req_size nflt)).
{ intros a Ha [Hnz Hin]. destruct Hrng7 as [Hz | (Hb4096' & [_ Hbz] & _)]; [exact (Hnz Hz)|]. clear - Ha Hin Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (Htr_in3 : forall b sz, In (b, sz) (tree_blocks tr) -> In (b, sz) (ablocks B ly3 S3))
by (intros b sz Hb; eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; cbn [cht_blocks app]; do 8 right; exact Hb]).
assert (Htree7 : tree_at trbsegs (mrestrict (w_H W7) mem7) tr).
{ apply (rg_tree_at_kept (w_H W3) (w_H W7) (ms_mem ms3) mem7 tr Htree). intros b sz Hb i Hi.
destruct HK7 as (_ & K2 & _). apply (K2 b sz i (Htr_in3 b sz Hb)); [exact Hi|]. apply (HnO7 b sz (b + i) (Htr_in3 b sz Hb)). clear - Hi. lia. }
destruct Hrng7 as [Hflt0 | (Hflt4096 & Hfltzone & Hfltceil & Hflt16 & HfltiIn)].
{
subst flt.
assert (Ebl7 : ablocks B ly7 S7 = ablocks B ly3 S3) by (destruct Hres7 as [(_ & Eb & _) | (Hnz & _)]; [exact Eb | exfalso; clear - Hnz; lia]).
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ ga_keptK HK7 HJ7 AG Usp Hrin3 Hrin7 HfinS3 Hfin3 HFpres7 HFSpres7 HnR7 HnC7 HnF7 HnS7 EFA3 F Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 305%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs _ LAWS); [exact HK7 | exact (proj1 HJ7) | exact Htb_in7 | ga_evalE AG | exact Htb_in3 | lia | change (req_size 48) with 48; lia | lia | lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnT7; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
pose proof (st_ok_pin_reg' trbsegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha07; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
pose proof (EFA7 7 fpos) as EFA77. fold F in EFA77.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x844c8.
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
assert (HPrt7 : Permutation (ablocks B ly7 S7) ((r, RGB_SIZE) :: (tb, 48) :: (((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx Tt ++ tree_blocks tr))).
{ rewrite Ebl7. pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
eapply Permutation_trans; [exact HPm3|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; YI0g.perm_tac. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Htree9 : tree_at trbsegs (mrestrict (w_H W7) (ms_mem msX)) tr) end.
{ apply (rg_tree_at_kept (w_H W7) (w_H W7) mem7 _ tr Htree7). intros b sz Hb i Hi.
pose proof (m_blk_off_zs2 B LAWS ly7 S7 _ _ _ b sz r tb _ fpos HAR7 HPrt7 ltac:(apply in_or_app; right; cbn [cht_blocks app]; do 7 right; exact Hb) Hfin7 (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2).
rewrite EFA7 in Hq2. fold F in Hq2. apply UN2; assumption. }
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with ss_XT2 in HS | idtac "STATE-MISMATCH"] end.
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
rga_hand RXT2 HS HJ7 (k + 1); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, Tt, tr.
split; [split; [unfold EV_FREECHT; clear - Hk0 HEVv HEVhd Hnodes; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [clear - HT24; lia|].
split; [rewrite Ebl7; exact HPm3|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rroot|].
split; [exact Htree9 | exact Hth]. }
destruct Hres7 as [(Hz7 & _) | (_ & Ebl7 & _)]; [exfalso; clear - Hz7 Hflt4096; lia|].
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ flt nflt HJ3 HAR7 Ebl7 ltac:(clear - Hnflt; lia)) as Tflt.
assert (Aflt : forall blc lyq ownq i, In (flt, nflt) blc -> 0 <= i < req_size nflt ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (flt + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ flt nflt blc i lyq ownq HJ3 HAR7 Ebl7 ltac:(clear - Hnflt; lia) Hbl Hi). }
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14]%nat AG
ltac:(idtac; first [ ga_keptK HK7 HJ7 AG Usp Hrin3 Hrin7 HfinS3 Hfin3 HFpres7 HFSpres7 HnR7 HnC7 HnF7 HnS7 EFA3 F Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 305%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs _ LAWS); [exact HK7 | exact (proj1 HJ7) | exact Htb_in7 | ga_evalE AG | exact Htb_in3 | lia | change (req_size 48) with 48; lia | lia | lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnT7; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
rreg HS (10%bv : bv 5) Rflt. cbn [ms_regs] in Rflt. rewrite Ha07 in Rflt. symmetry in Rflt. unfold w64 in Rflt.
pose proof (req_size_pos nflt ltac:(clear - Hnflt; lia)) as Hrqflt.
assert (Hflt_rng : 4096 <= flt <= 140737479966720) by (clear - Hflt4096 Hfltceil C1 Hrqflt; lia).
lazymatch type of Rflt with ew ?Ex ?nx = _ =>
idtac "NEWBLK-ATOM flt" nx;
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rflt, unsigned_lit_small by (clear - Hflt_rng; lia); change (2 ^ 4) with 16;
clear - Hflt_rng Hflt16; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
pose proof (EFA7 7 fpos) as EFA77. fold F in EFA77.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x83e04.
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
-
exfalso. rewrite YO3v.branch_eq_U in Hc. apply Z.eqb_eq in Hc.
lazymatch type of Hc with U ?Ex _ = _ =>
assert (UfN1 : U Ex (SMdw M_MUL (SExt true 32 (SOff 46 0)) (SMdw M_MUL (SOff 40 0) (SOff 39 0))) = fmt * N);
[ rewrite HNhw; apply U_mulw_small; [apply (U_sext32_small Ex 46 fmt); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E46 | clear - Hfmt; lia]
| apply (U_HW Ex 40 39 Hd Wd); [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E40 | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E39
| clear - R44v; cbn in R44v; lia | clear - R42v; cbn in R42v; lia | exact HN31]
| clear - Hfmt; lia | clear - HN31; lia | rewrite <- HNhw; clear - HfN; unfold RGB_NMAX in HfN; lia]
| rewrite UfN1 in Hc; assert (H0 : U Ex (SLit 0) = 0) by reflexivity; rewrite H0 in Hc; clear - Hc HfN; lia ] end.
- aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x83e2c.
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
assert (HPm7 : Permutation (ablocks B ly7 S7) (ablocks B ly S ++ [(blk, fmt * N); (fim, N)] ++ ((tb, 48) :: cht_blocks fq hh uu pp xx Tt) ++ tree_blocks tr ++ [(flt, nflt)]))
by (rewrite Ebl7; eapply Permutation_trans; [apply Permutation_app_tail; exact HPm3|]; YI0g.perm_tac).
assert (HPrt7 : Permutation (ablocks B ly7 S7) ((r, RGB_SIZE) :: (tb, 48) :: (((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx Tt ++ tree_blocks tr ++ [(flt, nflt)]))).
{ pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
eapply Permutation_trans; [exact HPm7|]; eapply Permutation_trans; [exact (Permutation_app_tail _ HPerm')|]; YI0g.perm_tac. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Htree9 : tree_at trbsegs (mrestrict (w_H W7) (ms_mem msX)) tr) end.
{ apply (rg_tree_at_kept (w_H W7) (w_H W7) mem7 _ tr Htree7). intros b sz Hb i Hi.
pose proof (m_blk_off_zs2 B LAWS ly7 S7 _ _ _ b sz r tb _ fpos HAR7 HPrt7 ltac:(apply in_or_app; right; cbn [cht_blocks app]; do 7 right; apply in_or_app; left; exact Hb) Hfin7 (b + i) ltac:(clear - Hi; lia)) as (Hq1 & Hq2).
rewrite EFA7 in Hq2. fold F in Hq2. rewrite (UN3 _ Hq1 Hq2). apply UN2; assumption. }
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with ss_Q4 in HS | idtac "STATE-MISMATCH"] end.
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
rga_hand RC HS HJ7 (k + 1); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, Tt, cnt, flt, tr.
split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hnodes|]. split; [exact Hfmt|]. split; [exact HPm7|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Tfq | exact Afq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Thh | exact Ahh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Tuu | exact Auu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Tpp | exact App]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Txx | exact Axx]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rflt | split; [exact Tflt | exact Aflt]]|].
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
