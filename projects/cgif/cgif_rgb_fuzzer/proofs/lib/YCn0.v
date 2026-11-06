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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCq8 YCqb YClx YCm2 YCqc YCjo YCly YCpp YClz YCqd YCqe YCq9 YCqf YCea.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCog.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_XC2 : rga_fromFA B ss_EPI2 (fun _ => INV_X B) -> rga_from B ss_XCa (INV_XB B).
Proof.
intros RX. rga_prelude.
destruct HINV as (blk & fim & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim)).
destruct Hk0 as [Hk0 Hbud].
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hrin]).
assert (Hblk_in3 : In (blk, fmt * N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; left; reflexivity]).
assert (Hfim_in3 : In (fim, N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; right; left; reflexivity]).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x814c8 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
assert (HNhw : N = Hd * Wd) by (rewrite HNWH, HcW, HcH; lia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as Hrq.
pose proof (req_size_pos N ltac:(clear - HN1; lia)) as HrqN.
pose proof (rga_perm_sep B LAWS ly3 S3 _ _ _ _ _ (r, 64) (blk, fmt * N) HAR3 HPm3 Hrin ltac:(left; reflexivity)) as HzR_blk.
pose proof (rga_perm_sep B LAWS ly3 S3 _ _ _ _ _ (r, 64) (fim, N) HAR3 HPm3 Hrin ltac:(right; left; reflexivity)) as HzR_fim.
pose proof (rga_perm_sep2 B LAWS ly3 S3 _ _ _ _ (blk, fmt * N) (fim, N) HAR3 HPm3) as HzBF.
unfold zdisjoint, block_rng in HzR_blk, HzR_fim, HzBF. cbn [fst snd] in HzR_blk, HzR_fim, HzBF. change (req_size 64) with 64 in HzR_blk, HzR_fim.
assert (Hne_br : (blk, fmt * N) <> (r, 64)) by (intros Heq; injection Heq as Hb1 Hb2; clear - Hb1 HzR_blk Hrq; lia).
assert (Hne_fr : (fim, N) <> (r, 64)) by (intros Heq; injection Heq as Hb1 Hb2; clear - Hb1 HzR_fim HrqN; lia).
assert (Hne_fb : (fim, N) <> (blk, fmt * N)) by (intros Heq; injection Heq as Hb1 Hb2; clear - Hb1 HzBF Hrq HrqN; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ blk (fmt * N) HAR3 Hblk_in3) as (Hblk4096 & Hblkzone & Hblkceil & Hblk16).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ blk (fmt * N) 7 fpos HAR3 Hblk_in3 Hfin3) as HdF_blk.
unfold zdisjoint in HdF_blk. cbn [fst snd] in HdF_blk. change (fs_frame_bytes 7) with 8192 in HdF_blk. rewrite EFA3 in HdF_blk. fold F in HdF_blk.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ blk (fmt * N) cid pos HAR3 Hblk_in3 HfinS3) as HdC_blk.
unfold zdisjoint in HdC_blk. cbn [fst snd] in HdC_blk. rewrite EFA3 in HdC_blk.
assert (HnR_blk : forall a, r <= a < r + 64 -> ~ (blk <= a < blk + req_size (fmt * N))) by (intros a Ha Hin; clear - HzR_blk Ha Hin; lia).
assert (HnC_blk : forall a, cfp <= a < cfp + 24 -> ~ (blk <= a < blk + req_size (fmt * N))) by (intros a Ha Hin; clear - HdC_blk Ha Hin Hflo Hfhi; lia).
assert (HnF_blk : forall a, F <= a < F + 8192 -> ~ (blk <= a < blk + req_size (fmt * N))) by (intros a Ha Hin; clear - HdF_blk Ha Hin; lia).
assert (HnS_blk : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ (blk <= a < blk + req_size (fmt * N)))
by (intros a Ha Hin; destruct Hblkzone as [_ Hbz]; clear - Ha Hin Hbz HF8lo HF8hi HFq HF8 HFceil C1; lia).
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fim (N) HAR3 Hfim_in3) as (Hfim4096 & Hfimzone & Hfimceil & Hfim16).
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fim (N) 7 fpos HAR3 Hfim_in3 Hfin3) as HdF_fim.
unfold zdisjoint in HdF_fim. cbn [fst snd] in HdF_fim. change (fs_frame_bytes 7) with 8192 in HdF_fim. rewrite EFA3 in HdF_fim. fold F in HdF_fim.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fim (N) cid pos HAR3 Hfim_in3 HfinS3) as HdC_fim.
unfold zdisjoint in HdC_fim. cbn [fst snd] in HdC_fim. rewrite EFA3 in HdC_fim.
assert (HnR_fim : forall a, r <= a < r + 64 -> ~ (fim <= a < fim + req_size (N))) by (intros a Ha Hin; clear - HzR_fim Ha Hin; lia).
assert (HnC_fim : forall a, cfp <= a < cfp + 24 -> ~ (fim <= a < fim + req_size (N))) by (intros a Ha Hin; clear - HdC_fim Ha Hin Hflo Hfhi; lia).
assert (HnF_fim : forall a, F <= a < F + 8192 -> ~ (fim <= a < fim + req_size (N))) by (intros a Ha Hin; clear - HdF_fim Ha Hin; lia).
assert (HnS_fim : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ (fim <= a < fim + req_size (N)))
by (intros a Ha Hin; destruct Hfimzone as [_ Hbz]; clear - Ha Hin Hbz HF8lo HF8hi HFq HF8 HFceil C1; lia).
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_wrap_free.
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_atD trbsegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly3 S3 _ k blk (fmt * N) (-576) (Z_to_bv 64 0x84404) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 Hblk_in3) end.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. first [reflexivity | exact Rblk | rewrite Rblk; reflexivity].
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
apply (achain_chain_pre ly3 _ (spZ regs - 576) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity.
- exact Tblk. }
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & (l1_8 & l2_8 & El8 & Eab8) & Hfrs8 & Hd8 & HK8).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof HJ8 as (HAR8 & Hly8 & _).
assert (EFA8 : forall c p, frame_addr ly8 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly8 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin8 : In (7, fpos) (frames S8)) by (rewrite Hfrs8; exact Hfin3).
assert (HfinS8 : In (cid, pos) (frames S8)) by (rewrite Hfrs8; exact HfinS3).
assert (Hrin8 : In (r, 64) (ablocks B ly8 S8)).
{ rewrite Eab8. apply (in_app_remove _ (r, 64) (blk, fmt * N)); [rewrite <- El8; exact Hrin3 | intros Heq; apply Hne_br; symmetry; exact Heq]. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR8 Hfin8) as (_ & _ & HFpres8 & HFSpres8). change (fs_frame_bytes 7) with 8192 in HFpres8, HFSpres8.
change (8192 / 8) with 1024 in HFSpres8. rewrite EFA8 in HFpres8, HFSpres8. fold F in HFpres8, HFSpres8.
ga_aconsts HROD HJ8 Kgot8 Kcell8 Kguar8 Kuar8 Vgr8.
assert (Hfim_in8 : In (fim, N) (ablocks B ly8 S8)).
{ rewrite Eab8. apply (in_app_remove _ (fim, N) (blk, fmt * N)); [rewrite <- El8; exact Hfim_in3 | exact Hne_fb]. }
reseat HS HJ8 HP8 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [ ga_keptK HK8 HJ8 AG Usp Hrin3 Hrin8 HfinS3 Hfin3 HFpres8 HFSpres8 HnR_blk HnC_blk HnF_blk HnS_blk EFA3 F Kgot0 Kgot8 Kcell0 Kcell8 Kguar0 Kguar8 Kuar0 Kuar8 Vgr0 Vgr8
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot8 into Kgot0. rename Kcell8 into Kcell0. rename Kguar8 into Kguar0. rename Kuar8 into Kuar0. rename Vgr8 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ8 end.
ga_relow HS AG E10 E11 E10n E11n.
try clear HEEc. lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEEc end.
pose proof (EFA8 7 fpos) as EFA87. fold F in EFA87.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ8 SHOK GBspan A_wrap_free.
1: ga_awrR AG fpos F EFA8 54%nat 67%nat.
clear HF HFr HG.
lazymatch goal with |- ?g => idtac "OK-SECOND-FREE" end.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rga_chain HS HJ8 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ8 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ8 as (_ & _ & _ & _ & _ & _ & Hnev8 & _).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_atD trbsegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp [(r, RGB_SIZE)]) ly S W mem md [(7, fpos)]
ly8 S8 _ (k + 1) fim (N) (-576) (Z_to_bv 64 0x84414) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ8 Hfim_in8) end.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. first [reflexivity | exact Rfim | rewrite Rfim; reflexivity].
- unfold spZ. rewrite Rsp. ga_evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rga_room Hev Hbud; (clear - Hk0 HEVv; rga_lia).
- assert (Etop8 : ly_top ly8 = ly_top ly) by (destruct (proj1 (proj2 HJ8)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
apply (achain_chain_pre ly8 _ (spZ regs - 576) (spZ regs) _ _ (achain_ly_top ly ly8 _ _ _ _ Etop8 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity.
- exact Tfim. }
cbv beta. intros W9 c9 Hwle9 (ly9 & S9 & regs9 & mem9 & md9 & -> & HJ9 & HP9 & (l1_9 & l2_9 & El9 & Eab9) & Hfrs9 & Hd9 & HK9).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof HJ9 as (HAR9 & Hly9 & _).
assert (EFA9 : forall c p, frame_addr ly9 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly9 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin9 : In (7, fpos) (frames S9)) by (rewrite Hfrs9; exact Hfin8).
assert (HfinS9 : In (cid, pos) (frames S9)) by (rewrite Hfrs9; exact HfinS8).
assert (Hrin9 : In (r, 64) (ablocks B ly9 S9)).
{ rewrite Eab9. apply (in_app_remove _ (r, 64) (fim, N)); [rewrite <- El9; exact Hrin8 | intros Heq; apply Hne_fr; symmetry; exact Heq]. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR9 Hfin9) as (_ & _ & HFpres9 & HFSpres9). change (fs_frame_bytes 7) with 8192 in HFpres9, HFSpres9.
change (8192 / 8) with 1024 in HFSpres9. rewrite EFA9 in HFpres9, HFSpres9. fold F in HFpres9, HFSpres9.
ga_aconsts HROD HJ9 Kgot9 Kcell9 Kguar9 Kuar9 Vgr9.
reseat HS HJ9 HP9 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [ ga_keptK HK9 HJ9 AG Usp Hrin8 Hrin9 HfinS8 Hfin8 HFpres9 HFSpres9 HnR_fim HnC_fim HnF_fim HnS_fim EFA8 F Kgot0 Kgot9 Kcell0 Kcell9 Kguar0 Kguar9 Kuar0 Kuar9 Vgr0 Vgr9
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot9 into Kgot0. rename Kcell9 into Kcell0. rename Kguar9 into Kguar0. rename Kuar9 into Kuar0. rename Vgr9 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ9 end.
ga_relow HS AG E10 E11 E10n E11n.
try clear HEEc. lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEEc end.
pose proof (EFA9 7 fpos) as EFA97. fold F in EFA97.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ9 SHOK GBspan 0x84428.
all: try (unfold GBx; ga_obl_blk HJ9 E10n E44 Hrin9).
1: ga_awrR AG fpos F EFA9 54%nat 67%nat.
clear HF HFr HG.
assert (HkX9 : k + 1 + 1 <= EV_RGBADD) by (clear - Hk0; lia).
assert (Hfrs9' : frames S9 = (7, fpos) :: frames S) by (rewrite Hfrs9, Hfrs8; exact Hfrs3).
assert (HP9' : Permutation (ablocks B ly9 S9) (ablocks B ly S)).
{ rewrite Eab9. apply (perm_two_frees (blk, fmt * N) (fim, N) (ablocks B ly3 S3) (ablocks B ly S) l1_8 l2_8 l1_9 l2_9 HPm3 El8). rewrite <- Eab8. exact El9. }
lazymatch goal with |- ?g => idtac "OK-BEFORE-EXIT" end.
rga_exit_same2 RX HS HJ9 (k + 1 + 1) HkX9 HP9' HEEc HBASE0 LAWS.
Qed.
End d.
End b.
