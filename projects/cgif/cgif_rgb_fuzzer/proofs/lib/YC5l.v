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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk
YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCb2 YCb3.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_E2d : rga_fromA B ss_A5 (fun _ => INV_NO B 5 news_A2 opts_2) -> rga_from B ss_A4 (INV_NO B 4 news_A2 opts_1).
Proof.
intros RC. rga_prelude. unfold ss_A4 in HS.
destruct HINV as (bs & os & Hk0 & Hfmt & Eab3 & Hnews & Hopts & av & E300 & Hav).
destruct Hk0 as [Hk0 Hbud].
try unfold news_A2 in Eab3. try unfold news_A2 in Hnews. try unfold news_A2 in Hopts. try unfold news_A1 in Eab3. try unfold news_A1 in Hnews. try unfold news_A1 in Hopts. try unfold opts_1 in Eab3. try unfold opts_1 in Hnews. try unfold opts_1 in Hopts.
rga_cbn_cx Eab3. rga_cbn_cx Hnews. rga_cbn_cx Hopts. cbn [app] in Eab3, Hnews, Hopts.
cbn [rga_news] in Hnews. destruct bs as [|blk bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rblk & Tblk & Ablk) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|fim bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rfim & Tfim & Afim) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|tb bs]; [contradiction|]. cbn [rga_news] in Hnews. destruct Hnews as ((Rtb & Ttb & Atb) & Hnews).
cbn [rga_news] in Hnews. destruct bs as [|? ?]; [|contradiction]. clear Hnews. cbn [combine map snd] in Eab3.
cbn [rga_opts] in Hopts. destruct os as [|fq os]; [contradiction|]. cbn [rga_opts] in Hopts. destruct Hopts as ((Rfq & Hrfq & Hcfq) & Hopts).
cbn [rga_opts] in Hopts. destruct os as [|? ?]; [|contradiction]. clear Hopts. cbn [optl map snd app] in Eab3. rewrite ?app_nil_r in Eab3.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hrin).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x81368 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x80ea8])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
assert (Htb_in3 : In (tb, 48) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; right; right; left; reflexivity).
assert (Hrqtb : 48 <= req_size 48 <= 48) by (change (req_size 48) with 48; clear; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ tb 48 HAR3 Htb_in3) as (Htb4096 & Htbzone & Htbceil & Htb16). gboxh Htbzone.
assert (Htb_rng : 0 <= tb < 2 ^ 64) by (clear - Htb4096 Htbceil Hrqtb C1; lia).
assert (Atb' : forall blc lyq ownq i, In (tb, 48) blc -> 0 <= i < 48 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (tb + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; apply Atb; [exact Hb0 | change (req_size 48) with 48; exact Hi0]).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rreg HS (10%bv : bv 5) Ha0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340228) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_atD trasegs B LAWS Hsegs errno_low ML AMALLOC _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 _ k (1572927) (-512) (Z_to_bv 64 0x82450) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ha0.
- unfold MALLOC_MAX. clear. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, bsum_app, !bsum_cons, ?bsum_app, <- (blocks_bytes_bsum B ly S). cbn [snd]. try change (bsum (@nil (Z * Z))) with 0. pose proof (bsum_optb_le fq 2097236 ltac:(clear; lia)) as Hbo0. remember (bsum (optb fq 2097236)) as zo0 eqn:Ezo0 in *. clear Ezo0. cbn [bsum fold_right snd]. clear - Hlive HfN HN1 HN Hbo0. unfold LIVE_RGBADD, LIVE_MAX, RGB_NMAX in *. lia.
- unfold spZ. rewrite Rsp. ga_evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rga_room Hev Hbud; (clear - Hk0 HEVv; rga_lia).
- assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
apply (achain_chain_pre ly3 _ (spZ regs - 512) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. apply (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & hh & -> & HJ7 & HP7 & Ha07 & Hfrs7 & Hd7 & Hres7).
apply rga_d_malloc in Hd7; [|clear; lia].
clear Ha0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
destruct (mres_kept B ly3 S3 W3 _ W7 mem7 ly7 S7 _ _ hh (1572927) Hres7) as (HK7 & HBin7 & HhhIn).
pose proof (mres_range B LAWS ly7 S7 W7 mem7 md7 ly3 S3 hh (1572927) _ _ (proj1 HJ7) Hres7) as Hrng7.
pose proof HJ7 as (HAR7 & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (EFL7 : forall c p, flag_addr ly7 c p = flag_addr ly c p)
by (intros c p; unfold flag_addr; pose proof (EFA7 c p) as X; unfold frame_addr in X; lia).
assert (Hfin7 : In (7, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin3).
assert (HfinS7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact HfinS3).
assert (Hrin7 : In (r, 64) (ablocks B ly7 S7)) by (apply HBin7; exact Hrin3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA7 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
assert (HnF7 : forall a, F <= a < F + 8192 -> ~ (hh <> 0 /\ hh <= a < hh + req_size (1572927))).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ hh (1572927) 7 fpos HAR7 (HhhIn Hnz) Hfin7) as Dd.
rewrite EFA7 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. clear - Dd Ha Hin. lia. }
assert (HnC7 : forall a, cfp <= a < cfp + 24 -> ~ (hh <> 0 /\ hh <= a < hh + req_size (1572927))).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ hh (1572927) cid pos HAR7 (HhhIn Hnz) HfinS7) as Dd.
rewrite EFA7 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hin Hflo Hfhi. lia. }
assert (HnR7 : forall a, r <= a < r + 64 -> ~ (hh <> 0 /\ hh <= a < hh + req_size (1572927))).
{ intros a Ha [Hnz Hin].
assert (Hne : (hh, (1572927)) <> (r, 64)).
{ intros Heq. injection Heq as Hb1 Hb2. destruct Hres7 as [(Hz & _) | (_ & Ebl7 & _)]; [exact (Hnz Hz)|].
pose proof (sep_blocks_pos trasegs B LAWS ly7 S7 W7 mem7 md7 (r, 64) (hh, (1572927))) as Hsp.
pose proof Hrin3 as Hrin3c. apply in_split in Hrin3c as (l1 & l2 & El). rewrite El, <- app_assoc in Ebl7. cbn [app] in Ebl7.
specialize (Hsp l1 l2 [] HAR7 Ebl7). unfold zdisjoint, block_rng in Hsp. cbn [fst snd] in Hsp. change (req_size 64) with 64 in Hsp. rewrite Hb1 in Hsp. clear - Hsp Ha Hin. lia. }
pose proof (sep_blocks trasegs B LAWS ly7 S7 W7 mem7 md7 hh (1572927) r 64 HAR7 (HhhIn Hnz) Hrin7 Hne) as Dd.
unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (req_size 64) with 64 in Dd. clear - Dd Ha Hin. lia. }
assert (HnS7 : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ (hh <> 0 /\ hh <= a < hh + req_size (1572927))).
{ intros a Ha [Hnz Hin]. destruct Hrng7 as [Hz | (Hb4096' & [_ Hbz] & _)]; [exact (Hnz Hz)|]. clear - Ha Hin Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (Htb_in7 : In (tb, 48) (ablocks B ly7 S7)) by (apply HBin7; exact Htb_in3).
assert (HnT7 : forall a, tb <= a < tb + 48 -> ~ (hh <> 0 /\ hh <= a < hh + req_size (1572927))).
{ intros a Ha [Hnz Hin]. destruct Hres7 as [(Hz & _) | (_ & Ebl7 & _)]; [exact (Hnz Hz)|].
pose proof (rga_perm_sep B LAWS ly7 S7 _ _ _ _ _ (tb, 48) (hh, 1572927) HAR7 ltac:(rewrite Ebl7; apply Permutation_refl) Htb_in3 ltac:(left; reflexivity)) as Hsp.
unfold zdisjoint, block_rng in Hsp. cbn [fst snd] in Hsp. change (req_size 48) with 48 in Hsp. clear - Hsp Ha Hin. lia. }
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG
ltac:(idtac; first [ ga_keptK HK7 HJ7 AG Usp Hrin3 Hrin7 HfinS3 Hfin3 HFpres7 HFSpres7 HnR7 HnC7 HnF7 HnS7 EFA3 F Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 305%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trasegs _ LAWS); [exact HK7 | exact (proj1 HJ7) | exact Htb_in7 | ga_evalE AG | exact Htb_in3 | lia | change (req_size 48) with 48; lia | lia | lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnT7; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
rreg HS (10%bv : bv 5) Rhh. cbn [ms_regs] in Rhh. rewrite Ha07 in Rhh. symmetry in Rhh. unfold w64 in Rhh.
lazymatch type of Rhh with ew ?Ex ?nx = _ => idtac "NEWBLK-ATOM hh" nx end.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
pose proof (EFA7 7 fpos) as EFA77. fold F in EFA77.
reshok_bx HS 44%nat.
aj_run_to_tok tratbl_lib_ok HS HJ7 SHOK GBspan A_wrap_malloc.
all: try (unfold GBx; ga_obl_blk HJ7 Rtb E44 Htb_in7).
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
clear HF HFr HG.
ga_join HS ss_A5 400%nat (@nil (bv 5)) ltac:(idtac).
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
rga_hand RC HS HJ7 (k + 1); [rga_E_tac HEE7 | ].
exists [blk; fim; tb], [fq; hh]. split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [unfold news_A2, news_A1, opts_2, opts_1; rga_cbn_cx_goal; cbn [app combine map snd optl];
rewrite (mres_optb B ly7 S7 ly3 S3 hh (1572927) _ _ Hres7), Eab3, <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc, ?app_nil_r; cbn [app]; reflexivity|].
split; [ unfold news_A2, news_A1; rga_cbn_cx_goal; cbn [app rga_news];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]] |];
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]] | exact I] |].
split; [ unfold opts_2, opts_1; rga_cbn_cx_goal; cbn [app rga_opts]
| exists av; split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact E300 | exact Hav] ].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Hrfq | exact Hcfq]] |].
split; [|exact I]. split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh|]. split.
- destruct Hrng7 as [-> | (Hq4096 & _ & Hqceil & _)]; [clear; lia | pose proof (req_size_pos (1572927) ltac:(clear; lia)) as Hq; clear - Hq4096 Hqceil Hq C1; lia].
- intros Hnz. destruct Hres7 as [(Hz & _) | (_ & Ebl7 & _)]; [exfalso; exact (Hnz Hz)|].
split; [exact (aftok_new_block trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh (1572927) HJ3 HAR7 Ebl7 ltac:(clear; lia))|].
intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh (1572927) blc i lyq ownq HJ3 HAR7 Ebl7 ltac:(clear; lia) Hbl Hi).
Qed.
End d.
End b.
