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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCn6 YCn7 YCoi YCo3 YCnz YCog YCnp.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_Q1 : rga_fromA B ss_XC (fun _ => INV_XC B) -> rga_fromA B ss_DL0 (fun _ => INV_DL0 B) -> rga_from B ss_Q0m (INV_HDx B 256 (2 ^ 32)).
Proof.
intros RXC RC.
rga_prelude.
destruct HINV as (blk & fim & tb & fq & hh & uu & pp & xx & ha & Ht & ent & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & (Rtb & Ttb & Atb) &
(Rfq & Tfq & Afq) & (Rhh & Thh & Ahh) & (Ruu & Tuu & Auu) & (Rpp & Tpp & App) & (Rxx & Txx & Axx) & Rcnt & RT & Rha & Hha & Harr & Hinv & HTch & Hsum & (av & Rav & Hav) & Hcnt).
destruct Hk0 as [Hk0 Hbud].
unfold ss_Q0m in HS.
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
set (nd := 4 * ht_cnt Ht).
assert (Hnd : 1024 <= nd < 67108864) by (subst nd; clear - Hcnt Hcnt0 HT24; lia).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rregU HS (10%bv : bv 5) nd
ltac:(subst nd; replace (4 * ht_cnt Ht) with (ht_cnt Ht * 2 ^ 2) by (clear; lia);
apply (U_sll_small_q _ (SOff 620 0) (ht_cnt Ht) 2); [apply (U_atom _ 620 _ Rcnt Hcnt64) | clear - Hcnt0; lia | clear; lia | clear - Hcnt0 HT24; lia]) Ha0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340936) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (HEVhd : EV_HD = 68) by reflexivity.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_atD trbsegs B LAWS Hsegs errno_low ML AMALLOC _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 _ k nd (-576) (Z_to_bv 64 0x83318) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ha0.
- unfold MALLOC_MAX. clear - Hnd. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPm3), !bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd cht_blocks].
clear - Hlive HfN HN1 HN Hnd HT24. unfold LIVE_RGBADD, LIVE_MAX, RGB_NMAX in *. lia.
- unfold spZ. rewrite Rsp. ga_evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rga_room Hev Hbud; (clear - Hk0 HEVv HEVhd; rga_lia).
- assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
apply (achain_chain_pre ly3 _ (spZ regs - 576) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & dn & -> & HJ7 & HP7 & Ha07 & Hfrs7 & Hd7 & Hres7).
apply rga_d_malloc in Hd7; [|clear - Hnd; lia].
clear Ha0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
destruct (mres_kept B ly3 S3 W3 _ W7 mem7 ly7 S7 _ _ dn nd Hres7) as (HK7 & HBin7 & HdnIn).
pose proof (mres_range B LAWS ly7 S7 W7 mem7 md7 ly3 S3 dn nd _ _ (proj1 HJ7) Hres7) as Hrng7.
pose proof HJ7 as (HAR7 & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin7 : In (7, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin3).
assert (HfinS7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact HfinS3).
assert (Hrin7 : In (r, 64) (ablocks B ly7 S7)) by (apply HBin7; exact Hrin3).
assert (Htb_in7 : In (tb, 48) (ablocks B ly7 S7)) by (apply HBin7; exact Htb_in3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7). change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7. rewrite EFA7 in HFpres7, HFSpres7. fold F in HFpres7, HFSpres7.
assert (HnF7 : forall a, F <= a < F + 8192 -> ~ (dn <> 0 /\ dn <= a < dn + req_size nd)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ dn nd 7 fpos HAR7 (HdnIn Hnz) Hfin7) as Dd.
rewrite EFA7 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. clear - Dd Ha Hin. lia. }
assert (HnC7 : forall a, cfp <= a < cfp + 24 -> ~ (dn <> 0 /\ dn <= a < dn + req_size nd)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ dn nd cid pos HAR7 (HdnIn Hnz) HfinS7) as Dd.
rewrite EFA7 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hin Hflo Hfhi. lia. }
assert (HnO7 : forall b sz a, In (b, sz) (ablocks B ly3 S3) -> b <= a < b + req_size sz -> ~ (dn <> 0 /\ dn <= a < dn + req_size nd)).
{ intros b sz a Hb Ha [Hnz Hin]. destruct Hres7 as [(Hz & _) | (_ & Ebl7 & _)]; [exact (Hnz Hz)|].
pose proof (rg_sep_head_in B LAWS ly7 S7 _ _ _ (dn, nd) (ablocks B ly3 S3) (b, sz) HAR7 ltac:(rewrite Ebl7; apply Permutation_sym; apply Permutation_cons_append) Hb) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hin. lia. }
assert (HnR7 : forall a, r <= a < r + 64 -> ~ (dn <> 0 /\ dn <= a < dn + req_size nd))
by (intros a Ha; apply (HnO7 r 64 a Hrin3); change (req_size 64) with 64; exact Ha).
assert (HnT7 : forall a, tb <= a < tb + 48 -> ~ (dn <> 0 /\ dn <= a < dn + req_size nd))
by (intros a Ha; apply (HnO7 tb 48 a Htb_in3); change (req_size 48) with 48; exact Ha).
assert (HnS7 : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ (dn <> 0 /\ dn <= a < dn + req_size nd)).
{ intros a Ha [Hnz Hin]. destruct Hrng7 as [Hz | (Hb4096' & [_ Hbz] & _)]; [exact (Hnz Hz)|]. clear - Ha Hin Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (Harr7 : cht_arrays trbsegs (mrestrict (w_H W7) mem7) fq hh uu pp xx Ht).
{ apply (m_cht_arrays_kept (w_H W3) (w_H W7) (ms_mem ms3) mem7 fq hh uu pp xx Ht Harr L1 L2 L3 L4 L5). intros b sz Hb i Hi.
assert (Hsz : 0 <= sz) by (clear - Hi; lia). pose proof (req_size_pos sz Hsz) as [_ Hrq].
assert (Hb3 : In (b, sz) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; apply in_or_app; right; right; exact Hb]).
destruct HK7 as (_ & K2 & _). apply (K2 b sz i Hb3); [clear - Hi Hrq; lia|]. apply (HnO7 b sz (b + i) Hb3). clear - Hi Hrq. lia. }
destruct Hrng7 as [Hdn0 | (Hdni4096 & Hdnizone & Hdniceil & Hdni16 & HdniIn)].
{
subst dn.
assert (Ebl7 : ablocks B ly7 S7 = ablocks B ly3 S3) by (destruct Hres7 as [(_ & Eb & _) | (Hnz & _)]; [exact Eb | exfalso; clear - Hnz; lia]).
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG
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
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x84904.
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
clear HF HFr HG.
ga_join HS ss_XC 1000%nat rga_deads_XC ltac:(idtac).
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
rga_hand RXC HS HJ7 (k + 1); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, (ht_T Ht). split; [split; [unfold EV_FREECHT; clear - Hk0 HEVv HEVhd; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [clear - HT24; lia|].
split; [rewrite Ebl7; exact HPm3|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp|].
repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx. }
destruct Hres7 as [(Hz7 & _) | (_ & Ebl7 & _)]; [exfalso; clear - Hz7 Hdni4096; lia|].
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dn nd HJ3 HAR7 Ebl7 ltac:(clear - Hnd; lia)) as Tdn.
assert (Adn : forall blc lyq ownq i, In (dn, nd) blc -> 0 <= i < req_size nd ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) (ablocks B ly S) blc lyq ownq (dn + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dn nd blc i lyq ownq HJ3 HAR7 Ebl7 ltac:(clear - Hnd; lia) Hbl Hi). }
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG
ltac:(idtac; first [ ga_keptK HK7 HJ7 AG Usp Hrin3 Hrin7 HfinS3 Hfin3 HFpres7 HFSpres7 HnR7 HnC7 HnF7 HnS7 EFA3 F Kgot0 Kgot7 Kcell0 Kcell7 Kguar0 Kguar7 Kuar0 Kuar7 Vgr0 Vgr7
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 305%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs _ LAWS); [exact HK7 | exact (proj1 HJ7) | exact Htb_in7 | ga_evalE AG | exact Htb_in3 | lia | change (req_size 48) with 48; lia | lia | lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnT7; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot7 into Kgot0. rename Kcell7 into Kcell0. rename Kguar7 into Kguar0. rename Kuar7 into Kuar0. rename Vgr7 into Vgr0.
rreg HS (10%bv : bv 5) Rdn. cbn [ms_regs] in Rdn. rewrite Ha07 in Rdn. symmetry in Rdn. unfold w64 in Rdn.
pose proof (req_size_pos nd ltac:(clear - Hnd; lia)) as Hrqdn.
assert (Hdn_rng : 4096 <= dn <= 140737479966720) by (clear - Hdni4096 Hdniceil C1 Hrqdn; lia).
lazymatch type of Rdn with ew ?Ex ?nx = _ =>
idtac "NEWBLK-ATOM dn" nx;
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rdn, unsigned_lit_small by (clear - Hdn_rng; lia); change (2 ^ 4) with 16;
clear - Hdn_rng Hdni16; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
pose proof (EFA7 7 fpos) as EFA77. fold F in EFA77.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x8338c.
all: try (unfold GBx; ga_obl_blk HJ7 Rtb E44 Htb_in7).
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
pose proof HPerm as HPerm'. unfold trgb_own in HPerm'. cbn [app] in HPerm'.
assert (HPrt7 : Permutation (ablocks B ly7 S7) ((r, RGB_SIZE) :: (tb, 48) :: (((cgif_blocks g s N ++ optb bef (beffmt * N)) ++ timg_block img fmt N ++ rest) ++ [(blk, fmt * N); (fim, N)] ++ cht_blocks fq hh uu pp xx (ht_T Ht) ++ [(dn, nd)])))
by (rewrite Ebl7; eapply Permutation_trans; [apply Permutation_app_tail; exact HPm3|]; eapply Permutation_trans; [apply Permutation_app_tail; exact (Permutation_app_tail _ HPerm')|]; YI0g.perm_tac).
assert (HoffA : forall b sz, In (b, sz) (cht_blocks fq hh uu pp xx (ht_T Ht)) -> forall i, 0 <= i < sz ->
0 <= b + i < 2 ^ 64 /\ ~ (m_ZsP F r (b + i) \/ tb <= b + i < tb + 48)).
{ intros b sz Hb i Hi.
assert (Hsz : 0 <= sz) by (clear - Hi; lia). pose proof (req_size_pos sz Hsz) as [_ Hrq].
pose proof (m_blk_off_zs2 B LAWS ly7 S7 _ _ _ b sz r tb _ fpos HAR7 HPrt7 ltac:(apply in_or_app; right; right; right; apply (in_or_app (cht_blocks fq hh uu pp xx (ht_T Ht))); left; exact Hb) Hfin7 (b + i) ltac:(clear - Hi Hrq; lia)) as Hq.
rewrite EFA7 in Hq. fold F in Hq. exact Hq. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Harr8 : cht_arrays trbsegs (mrestrict (w_H W7) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ apply (m_cht_arrays_kept (w_H W7) (w_H W7) mem7 _ fq hh uu pp xx Ht Harr7 L1 L2 L3 L4 L5). intros b sz Hb i Hi.
destruct (HoffA b sz Hb i Hi) as (Hq1 & Hq2). apply UN2; assumption. }
srr_branch_tok trbtbl_lib_ok HS SHOK GBspan.
{
exfalso.
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
assert (Rx : ew Ex 620 = Z_to_bv 64 (ht_cnt Ht)) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt) end.
rewrite branch_eq_U in Hc. rewrite (U_sext32_small _ 620 _ Rx ltac:(clear - Hcnt0 HT24; lia)) in Hc. change (U _ (SLit 0)) with 0 in Hc.
apply Z.eqb_eq in Hc. clear - Hc Hcnt. lia. }
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan 0x8338c.
all: try (unfold GBx; ga_obl_blk HJ7 Rtb E44 Htb_in7).
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
m_run_keptG HFr AG (fun a : Z => m_ZsP F r a \/ tb <= a < tb + 48) Hceil Hslo FFS UN3.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Harr9 : cht_arrays trbsegs (mrestrict (w_H W7) (ms_mem msX)) fq hh uu pp xx Ht) end.
{ lazymatch type of Harr8 with cht_arrays _ (mrestrict _ ?m1) _ _ _ _ _ _ => apply (m_cht_arrays_kept (w_H W7) (w_H W7) m1 _ fq hh uu pp xx Ht Harr8 L1 L2 L3 L4 L5) end.
intros b sz Hb i Hi. destruct (HoffA b sz Hb i Hi) as (Hq1 & Hq2). apply UN3; assumption. }
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
rga_hand RC HS HJ7 (k + 1); [rga_E_tac HEE7 | ].
exists blk, fim, tb, fq, hh, uu, pp, xx, ha, dn, Ht, ent. split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split; [rewrite Ebl7; subst nd; eapply Permutation_trans; [apply Permutation_app_tail; exact HPm3|]; change CHT_SIZE with 48; rewrite <- !app_assoc; apply Permutation_refl|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rtb | split; [exact Ttb | exact Atb]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfq | split; [exact Tfq | exact Afq]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rhh | split; [exact Thh | exact Ahh]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Ruu | split; [exact Tuu | exact Auu]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rpp | split; [exact Tpp | exact App]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rxx | split; [exact Txx | exact Axx]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rdn | split; [exact Tdn | exact Adn]]|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rcnt|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact RT|].
split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rha|].
split; [exact Hha|]. split; [exact Harr9|]. split; [exact Hinv|]. split; [exact HTch|]. split; [exact Hsum|].
split; [exists av; split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rav | exact Hav]|].
clear - Hcnt; lia.
Qed.
End e.
End d.
