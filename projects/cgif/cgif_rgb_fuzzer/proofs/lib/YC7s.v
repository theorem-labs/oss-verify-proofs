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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i YC97 YC98.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_FIN2 : rga_fromFA B ss_FINc (fun _ => INV_FINc B) -> rga_fromF B ss_FINb (INV_FINb B).
Proof.
intros RC.
rga_prelude.
destruct HINV as (blk & fim & s7 & Hk0 & Hfmt & Hcg7 & Hwf7 & HcW7 & HcH7 & Hattr7 & Hraw7 & HPr3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & Hnew7).
destruct Hk0 as [Hk0 Hbud].
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPr3 | left; reflexivity]).
pose proof (EFA3 7 fpos) as EFA37. fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
pose proof Hwf as Hwf0. destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x81368 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x80ea8])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
unfold ss_FINb in HS.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340224) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
set (Er := fun a : Z => bef <> 0 /\ bef <= a < bef + req_size (beffmt * N)).
set (bl8 := (r, RGB_SIZE) :: (cgif_blocks g s7 N ++ (fim, N) :: timg_block img fmt N ++ rest ++ [(blk, fmt * N)])).
assert (HbefIn : bef <> 0 -> In (bef, beffmt * N) (cgif_blocks g s7 N ++ (fim, N) :: optb bef (beffmt * N) ++ timg_block img fmt N ++ rest ++ [(blk, fmt * N)]))
by (intros Hnz; apply in_or_app; right; right; apply in_or_app; left; apply rg_optb_in; exact Hnz).
assert (HbefIn3 : bef <> 0 -> In (bef, beffmt * N) (ablocks B ly3 S3))
by (intros Hnz; eapply Permutation_in; [apply Permutation_sym; exact HPr3 | right; exact (HbefIn Hnz)]).
assert (HnR : forall a, r <= a < r + 64 -> ~ Er a).
{ intros a Ha [Hnz Hb]. pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (bef, beffmt * N) HAR3 HPr3 (HbefIn Hnz)) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. change (req_size RGB_SIZE) with 64 in Dd. clear - Dd Ha Hb. lia. }
assert (HnC : forall a, cfp <= a < cfp + 24 -> ~ Er a).
{ intros a Ha [Hnz Hb]. pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ bef (beffmt * N) cid pos HAR3 (HbefIn3 Hnz) HfinS3) as Dd.
rewrite EFA3 in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. clear - Dd Ha Hb Hflo Hfhi. lia. }
assert (HnF : forall a, F <= a < F + 8192 -> ~ Er a).
{ intros a Ha [Hnz Hb]. pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ bef (beffmt * N) 7 fpos HAR3 (HbefIn3 Hnz) Hfin3) as Dd.
rewrite EFA3 in Dd. fold F in Dd. unfold zdisjoint in Dd. cbn [fst snd] in Dd. change (fs_frame_bytes 7) with 8192 in Dd. clear - Dd Ha Hb. lia. }
assert (HnS : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ Er a).
{ intros a Ha [Hnz Hb]. destruct (rga_blk_range B LAWS ly3 S3 _ _ _ bef (beffmt * N) HAR3 (HbefIn3 Hnz)) as (_ & (_ & Hbz) & _).
clear - Ha Hb Hbz HF8lo HF8hi HFq HF8 HFceil C1. lia. }
assert (HnG : forall b sz i, In (b, sz) (cgif_blocks g s7 N) -> 0 <= i < req_size sz -> ~ Er (b + i)).
{ intros b sz i Hb Hi [Hnz Hbb].
assert (HPx : Permutation (ablocks B ly3 S3) (cgif_blocks g s7 N ++ ((r, RGB_SIZE) :: (fim, N) :: optb bef (beffmt * N) ++ timg_block img fmt N ++ rest ++ [(blk, fmt * N)])))
by (eapply Permutation_trans; [exact HPr3|]; YI0g.perm_tac).
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (b, sz) (bef, beffmt * N) HAR3 HPx Hb
ltac:(right; right; apply in_or_app; left; apply rg_optb_in; exact Hnz)) as Dd.
unfold zdisjoint, block_rng in Dd. cbn [fst snd] in Dd. clear - Dd Hi Hbb. lia. }
assert (HFPapp : forall x, inFP (ablocks_fp (trgb_own r g s N bef beffmt)) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x).
{ intros x Hx. destruct (inFP_ablocks_fp_inv _ _ Hx) as (b0 & n0 & Hbn0 & Hrg0).
assert (Hin0 : In (b0, n0) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | apply in_or_app; left; exact Hbn0]).
destruct (rga_blk_range B LAWS ly S _ _ _ b0 n0 HAR Hin0) as (_ & (_ & Hbz) & _).
unfold kLowShadowBeg, kHighShadowEnd. clear - Hbz Hrg0. lia. }
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) =>
assert (CONT : forall (W8 : world trasegs) ly8 S8 regs8 mem8 md8,
ajournal trasegs B TRGBADD_STK (spZ regs) (ablocks_fp (trgb_own r g s N bef beffmt)) ly S W mem md [(7, fpos)] ly8 S8 W8 mem8 md8 (k + 1) ->
aregs_preserved (ms_regs ms3) regs8 ->
Permutation (ablocks B ly8 S8) bl8 ->
frames S8 = frames S3 -> bud_le S3 S8 1 0 0 0 ->
acall_kept trasegs B ly3 S3 W3 (ms_mem ms3) W8 mem8 (spZ regs + -512 - ASTACK) (spZ regs + -512) Er ->
SRr trasegs W8 (mkCfg (mkst regs8 (Z_to_bv 64 541844) mem8 (seg_rom trasegs)) md8) (rga_post B cxv)) end.
{ intros W8 ly8 S8 regs8 mem8 md8 HJ8 HP8 HPm8 Hfrs8 Hd8 HK8.
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof HJ8 as (HAR8 & Hly8 & _).
assert (EFA8 : forall c p, frame_addr ly8 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly8 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin8 : In (7, fpos) (frames S8)) by (rewrite Hfrs8; exact Hfin3).
assert (HfinS8 : In (cid, pos) (frames S8)) by (rewrite Hfrs8; exact HfinS3).
assert (Hrin8 : In (r, 64) (ablocks B ly8 S8)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm8 | left; reflexivity]).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR8 Hfin8) as (_ & _ & HFpres8 & HFSpres8). change (fs_frame_bytes 7) with 8192 in HFpres8, HFSpres8.
change (8192 / 8) with 1024 in HFSpres8. rewrite EFA8 in HFpres8, HFSpres8. fold F in HFpres8, HFSpres8.
ga_aconsts HROD HJ8 Kgot8 Kcell8 Kguar8 Kuar8 Vgr8.
reseat HS HJ8 HP8 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first [ ga_keptK HK8 HJ8 AG Usp Hrin3 Hrin8 HfinS3 Hfin3 HFpres8 HFSpres8 HnR HnC HnF HnS EFA3 F Kgot0 Kgot8 Kcell0 Kcell8 Kguar0 Kguar8 Kuar0 Kuar8 Vgr0 Vgr8
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot8 into Kgot0. rename Kcell8 into Kcell0. rename Kguar8 into Kguar0. rename Kuar8 into Kuar0. rename Vgr8 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ8 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE8 end.
pose proof (EFA8 7 fpos) as EFA87. fold F in EFA87.
assert (Hcg8 : tcgif_at (mrestrict (w_H W8) mem8) g s7).
{ apply (rg_tcgif_at_blocks_kept (w_H W3) (w_H W8) (ms_mem ms3) mem8 g s7 N Hcg7). intros b sz Hb i Hi.
destruct HK8 as (_ & K2 & _). apply (K2 b sz i); [|exact Hi | exact (HnG b sz i Hb Hi)].
eapply Permutation_in; [apply Permutation_sym; exact HPr3 | right; apply in_or_app; left; exact Hb]. }
reshok_bx HS 44%nat.
aj_run_to_tok tratbl_lib_ok HS HJ8 SHOK GBspan A_wrap_free.
all: try (unfold GBx; ga_obl_blk HJ8 E10n E44 Hrin8).
all: try (unfold GBx; m_obl_cfp HJ8 E11n E44 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal HFPapp).
1: ga_awrR AG fpos F EFA8 54%nat 67%nat.
m_run_kept HFr AG (m_ZsP F r) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Hcg9 : tcgif_at (mrestrict (w_H W8) (ms_mem msX)) g s7) end.
{ apply (rg_tcgif_at_blocks_kept (w_H W8) (w_H W8) mem8 _ g s7 N Hcg8). intros b sz Hb i Hi.
destruct (m_blk_off_zs B LAWS ly8 S8 _ _ _ b sz r _ fpos HAR8 HPm8 ltac:(apply in_or_app; left; exact Hb) Hfin8 (b + i) ltac:(clear - Hi; lia)) as (Hr1 & Hr2).
rewrite EFA8 in Hr2. fold F in Hr2. apply UN2; assumption. }
assert (Hfrs8' : frames S8 = (7, fpos) :: frames S) by (rewrite Hfrs8; exact Hfrs3).
rga_hand RC HS HJ8 (k + 1); [rga_E_tac HEE8 | ].
exists blk, fim, s7. split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|]. split; [exact Hcg9|].
split; [exact Hwf7|]. split; [exact HcW7|]. split; [exact HcH7|]. split; [exact Hattr7|]. split; [exact Hraw7|].
split; [exact HPm8|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk | split; [exact Tblk | exact Ablk]]|].
split; [split; [repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim | split; [exact Tfim | exact Afim]]|].
exact Hnew7. }
destruct (Z.eq_dec bef 0) as [Hb0 | Hbnz].
-
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_null_atD trasegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp (trgb_own r g s N bef beffmt)) ly S W mem md [(7, fpos)]
ly3 S3 _ k (-512) (Z_to_bv 64 541844) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- rewrite Ra0, E41, Hb0. reflexivity.
- unfold spZ. rewrite Rsp. ga_evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rga_room Hev Hbud; (clear - Hk0 HEVv; rga_lia).
- apply (achain_chain_pre ly3 _ (spZ regs - 512) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. apply (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & HPm8 & Hfrs8 & Hd8 & HK8).
apply (CONT W8 ly8 S8 regs8 mem8 md8 HJ8 HP8); [| exact Hfrs8 | exact Hd8 | eapply acall_kept_mono_E; [exact HK8 | intros a []]].
eapply Permutation_trans; [exact HPm8|]. eapply Permutation_trans; [exact HPr3|]. subst bl8. rewrite Hb0. cbn [optb Z.eqb app]. apply Permutation_refl.
-
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_atD trasegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp (trgb_own r g s N bef beffmt)) ly S W mem md [(7, fpos)]
ly3 S3 _ k bef (beffmt * N) (-512) (Z_to_bv 64 541844) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 (HbefIn3 Hbnz)) end.
- rewrite Ra0, E41. reflexivity.
- unfold spZ. rewrite Rsp. ga_evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rga_room Hev Hbud; (clear - Hk0 HEVv; rga_lia).
- apply (achain_chain_pre ly3 _ (spZ regs - 512) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode. apply (tl_universe B TL). apply TRACES_cgif_rgb_addframe_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity.
- intros _ i Hi. apply (inFP_ablocks_fp _ bef (beffmt * N)); [unfold trgb_own; right; apply in_or_app; right; apply rg_optb_in; exact Hbnz | exact Hi]. }
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & (l1_8 & l2_8 & El8 & Eab8) & Hfrs8 & Hd8 & HK8).
apply (CONT W8 ly8 S8 regs8 mem8 md8 HJ8 HP8); [| exact Hfrs8 | exact Hd8 | eapply acall_kept_mono_E; [exact HK8 | intros a Ha; split; [exact Hbnz | exact Ha]]].
rewrite Eab8. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1_8 l2_8 (bef, beffmt * N)). rewrite <- El8.
eapply Permutation_trans; [|apply Permutation_sym; exact HPr3]. subst bl8. unfold optb. rewrite (proj2 (Z.eqb_neq bef 0) Hbnz). YI0g.perm_tac.
Qed.
End e.
End d.
