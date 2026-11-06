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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCq8 YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCq9 YCqf YCea.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCn5 YCnv.
Section d.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Let HBcode := tl_code B TL.
Let errno_low := tl_env B TL.
Lemma rga_FIN3 : rga_fromFA B ss_EPI2 (fun _ => INV_X B) -> rga_fromF B ss_FINc (INV_FINc B).
Proof.
intros RX.
rga_prelude.
destruct HINV as (blk & fim & s7 & Hk0 & Hfmt & Hcg7 & Hwf7 & HcW7 & HcH7 & Hattr7 & Hraw7 & HPr3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim) & Hnew7).
destruct Hk0 as [Hk0 Hbud].
unfold ss_FINc in HS.
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPr3 | left; reflexivity]).
assert (Hfim_in3 : In (fim, N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPr3 | right; apply in_or_app; right; left; reflexivity]).
pose proof (EFA3 7 fpos) as EFA37.
fold F in EFA37.
assert (Hfb7 : fs_frame_bytes 7 = 8192) by reflexivity.
assert (E10n : ew E 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E11n : ew E 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11).
pose proof Hwf as Hwf0.
destruct Hwf as (Hwf1 & HW1 & HH1 & HNWH & HNmax & Hwf6).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hra88 : 0x814c8 = raZ regs) by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [] \/ spine ch = [0x8116c])
by (cbn [CTX_cgif_rgb_addframe In] in Hctx; destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (HfN : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HN; unfold RGB_NMAX in *; nia).
let v := eval vm_compute in EV_RGBADD in assert (HEVv : EV_RGBADD = v) by reflexivity.
pose proof (req_size_pos N ltac:(clear - HN1; lia)) as HrqN.
set (Er := fun a : Z => fim <= a < fim + req_size N).
assert (HnR : forall a, r <= a < r + 64 -> ~ Er a).
{
intros a Ha Hb.
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (fim, N) HAR3 HPr3 ltac:(apply in_or_app; right; left; reflexivity)) as Dd.
unfold zdisjoint, block_rng in Dd.
cbn [fst snd] in Dd.
change (req_size RGB_SIZE) with 64 in Dd.
unfold Er in Hb.
clear - Dd Ha Hb.
lia.
}
assert (HnC : forall a, cfp <= a < cfp + 24 -> ~ Er a).
{
intros a Ha Hb.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fim N cid pos HAR3 Hfim_in3 HfinS3) as Dd.
rewrite EFA3 in Dd.
unfold zdisjoint in Dd.
cbn [fst snd] in Dd.
unfold Er in Hb.
clear - Dd Ha Hb Hflo Hfhi.
lia.
}
assert (HnF : forall a, F <= a < F + 8192 -> ~ Er a).
{
intros a Ha Hb.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ fim N 7 fpos HAR3 Hfim_in3 Hfin3) as Dd.
rewrite EFA3 in Dd.
fold F in Dd.
unfold zdisjoint in Dd.
cbn [fst snd] in Dd.
change (fs_frame_bytes 7) with 8192 in Dd.
unfold Er in Hb.
clear - Dd Ha Hb.
lia.
}
assert (HnS : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ Er a).
{
intros a Ha Hb.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fim N HAR3 Hfim_in3) as (_ & (_ & Hbz) & _).
unfold Er in Hb.
clear - Ha Hb Hbz HF8lo HF8hi HFq HF8 HFceil C1.
lia.
}
assert (HnG : forall b sz i, In (b, sz) (cgif_blocks g s7 N) -> 0 <= i < req_size sz -> ~ Er (b + i)).
{
intros b sz i Hb Hi Hbb.
assert (HPx : Permutation (ablocks B ly3 S3) (cgif_blocks g s7 N ++ ((r, RGB_SIZE) :: (fim, N) :: timg_block img fmt N ++ rest ++ [(blk, fmt * N)])))
by (eapply Permutation_trans; [exact HPr3|]; YI0g.perm_tac).
pose proof (rg_sep_app_in B LAWS ly3 S3 _ _ _ _ _ (b, sz) (fim, N) HAR3 HPx Hb ltac:(right; left; reflexivity)) as Dd.
unfold zdisjoint, block_rng in Dd.
cbn [fst snd] in Dd.
unfold Er in Hbb.
clear - Dd Hi Hbb.
lia.
}
rreg HS (10%bv : bv 5) Ra0.
rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp.
rreg HS (3%bv : bv 5) Rgp.
rreg HS (4%bv : bv 5) Rtp.
rreg HS (8%bv : bv 5) Rs0.
rga_chain HS HJ3 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl).
cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
eapply SRr_bind.
{
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_atD trbsegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs) (ablocks_fp (trgb_own r g s N bef beffmt)) ly S W mem md [(7, fpos)]
ly3 S3 _ k fim N (-576) (Z_to_bv 64 541716) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 Hfim_in3) end.
-
rewrite Ra0.
cbn [sv_denot].
ga_evalE0 AG.
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
first [reflexivity | exact Rfim | rewrite Rfim; reflexivity].
-
unfold spZ.
rewrite Rsp.
ga_evalE AG.
-
reflexivity.
-
lia.
-
rewrite FFS.
unfold ASTACK.
lia.
-
rewrite Rgp.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub].
rewrite ?ew_ewset_other by lia.
rewrite (AG 3%nat) by lia.
rewrite (EE 3%nat 3%bv eq_refl).
exact Hgp.
-
rewrite Rtp.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub].
rewrite ?ew_ewset_other by lia.
rewrite (AG 4%nat) by lia.
rewrite (EE 4%nat 4%bv eq_refl).
exact Htp.
-
exact Rra.
-
vm_compute.
reflexivity.
-
rga_room Hev Hbud; (clear - Hk0 HEVv; rga_lia).
-
apply (achain_chain_pre ly3 _ (spZ regs - 576) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; ga_evalE AG
| unfold s0Z; rewrite Rs0; ga_evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
-
rewrite call_trace_of_spine.
cbn [spine map fst snd].
fold (spine ch).
unfold raZ at 1.
rewrite Rra, unsigned_lit_small by lia.
rewrite <- Hra88.
rewrite HBcode. rewrite (tl_universe B TL).
apply TRACES_cgif_rgb_addframe_U.
apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity.
-
exact Tfim.
}
cbv beta.
intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & (l1_8 & l2_8 & El8 & Eab8) & Hfrs8 & Hd8 & HK8).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
set (bl8 := (r, RGB_SIZE) :: (cgif_blocks g s7 N ++ timg_block img fmt N ++ rest ++ [(blk, fmt * N)])).
assert (HPm8 : Permutation (ablocks B ly8 S8) bl8).
{
rewrite Eab8.
apply Permutation_sym.
apply (@Permutation_cons_app_inv _ _ l1_8 l2_8 (fim, N)).
rewrite <- El8.
eapply Permutation_trans; [|apply Permutation_sym; exact HPr3].
subst bl8.
YI0g.perm_tac.
}
pose proof HJ8 as (HAR8 & Hly8 & _).
assert (EFA8 : forall c p, frame_addr ly8 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly8 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (Hfin8 : In (7, fpos) (frames S8)) by (rewrite Hfrs8; exact Hfin3).
assert (HfinS8 : In (cid, pos) (frames S8)) by (rewrite Hfrs8; exact HfinS3).
assert (Hrin8 : In (r, 64) (ablocks B ly8 S8)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm8 | left; reflexivity]).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR8 Hfin8) as (_ & _ & HFpres8 & HFSpres8).
change (fs_frame_bytes 7) with 8192 in HFpres8, HFSpres8.
change (8192 / 8) with 1024 in HFSpres8.
rewrite EFA8 in HFpres8, HFSpres8.
fold F in HFpres8, HFSpres8.
ga_aconsts HROD HJ8 Kgot8 Kcell8 Kguar8 Kuar8 Vgr8.
reseat HS HJ8 HP8 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first [ ga_keptK HK8 HJ8 AG Usp Hrin3 Hrin8 HfinS3 Hfin3 HFpres8 HFSpres8 HnR HnC HnF HnS EFA3 F Kgot0 Kgot8 Kcell0 Kcell8 Kguar0 Kguar8 Kuar0 Kuar8 Vgr0 Vgr8
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
rename Kgot8 into Kgot0.
rename Kcell8 into Kcell0.
rename Kguar8 into Kguar0.
rename Kuar8 into Kuar0.
rename Vgr8 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ8 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE8 end.
pose proof (EFA8 7 fpos) as EFA87.
fold F in EFA87.
assert (Hcg8 : tcgif_at (mrestrict (w_H W8) mem8) g s7).
{
apply (rg_tcgif_at_blocks_kept (w_H W3) (w_H W8) (ms_mem ms3) mem8 g s7 N Hcg7).
intros b sz Hb i Hi.
destruct HK8 as (_ & K2 & _).
apply (K2 b sz i); [|exact Hi | exact (HnG b sz i Hb Hi)].
eapply Permutation_in; [apply Permutation_sym; exact HPr3 | right; apply in_or_app; left; exact Hb].
}
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ8 SHOK GBspan 0x84428.
all: try (unfold GBx; ga_obl_blk HJ8 E10n E44 Hrin8).
1: ga_awrR AG fpos F EFA8 54%nat 67%nat.
m_run_kept HFr AG (m_ZsP F r) Hceil Hslo FFS UN2.
clear HF HFr HG.
norm_ss HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Hcg9 : tcgif_at (mrestrict (w_H W8) (ms_mem msX)) g s7) end.
{
apply (rg_tcgif_at_blocks_kept (w_H W8) (w_H W8) mem8 _ g s7 N Hcg8).
intros b sz Hb i Hi.
destruct (m_blk_off_zs B LAWS ly8 S8 _ _ _ b sz r _ fpos HAR8 HPm8 ltac:(apply in_or_app; left; exact Hb) Hfin8 (b + i) ltac:(clear - Hi; lia)) as (Hr1 & Hr2).
rewrite EFA8 in Hr2.
fold F in Hr2.
apply UN2; assumption.
}
assert (Hfrs8' : frames S8 = (7, fpos) :: frames S) by (rewrite Hfrs8; exact Hfrs3).
assert (Hblk_in8 : In (blk, fmt * N) (ablocks B ly8 S8)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm8 | subst bl8; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; left; reflexivity]).
destruct (rga_blk_range B LAWS ly8 S8 _ _ _ blk (fmt * N) HAR8 Hblk_in8) as (Hblk4096 & _ & Hblkceil & _).
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as Hrq.
assert (Hblk_rng : 0 <= blk < 2 ^ 64) by (clear - Hblk4096 Hblkceil Hrq C1; lia).
lazymatch goal with |- SRr _ _ _ (rga_post ?Bv ?cxv) =>
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?W3x) ?msX) =>
assert (HEEv : rga_E cxv Ex) by (rga_E_tac HEE8);
let rs := eval vm_compute in (ss_mem ssx) in
let idx := ga_idx_of_base rs 10%nat in let idx := eval vm_compute in idx in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3x) msX) idx _ HS eq_refl) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YQ0b.mkRegion _ _ _ _ _ ?cs) =>
let ecur := ga_chunk_sv cs 60 4%N in
assert (Hobj : obj_at trbsegs (mrestrict (w_H W3x) (ms_mem msX)) r LAY_Rgb
([g; wfn; ctx; path; attr; gen; loops; Wd; Hd] ++ [blk; fmt; bv_unsigned (sv_denot Ex ecur) mod 2 ^ 32]));
[ let AGv := fresh "AGv" in let EXv := fresh "EXv" in
pose proof HEEv as (AGv & EXv & _); unfold rgc_vals in EXv; rga_cbn_cx EXv; rga_cbn_cx AGv;
pose proof (EXv 0%nat ltac:(lia)) as X0; pose proof (EXv 1%nat ltac:(lia)) as X1; pose proof (EXv 2%nat ltac:(lia)) as X2;
pose proof (EXv 3%nat ltac:(lia)) as X3; pose proof (EXv 4%nat ltac:(lia)) as X4; pose proof (EXv 5%nat ltac:(lia)) as X5;
pose proof (EXv 6%nat ltac:(lia)) as X6; pose proof (EXv 7%nat ltac:(lia)) as X7; pose proof (EXv 8%nat ltac:(lia)) as X8;
pose proof (EXv 14%nat ltac:(lia)) as X14;
cbn [Nat.add nth rga_vals] in X0, X1, X2, X3, X4, X5, X6, X7, X8, X14;
pose proof Hrgb as Hq; cbn [obj_at LAY_Rgb] in Hq;
destruct Hq as ([_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & _);
cbn [fst snd N.to_nat Z.of_N] in * |-;
eapply (m_obj_r_of_region_new _ _ r _ _ _ _ _ _ (SOff 152 0) (SExt true 32 (SOff 46 0)) ecur blk fmt HRr);
[ rewrite (AGv 10%nat) by lia; rewrite E10; apply unsigned_lit_small; clear - Hr4096 Hrceil C1; lia
| reflexivity
| let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj;
do 9 (destruct j as [|j]; [injection Hj as <-; split; [cbn [Nat.add]; assumption|]; split; [cbn [nth LAY_Rgb snd fst Z.of_N]; assumption | cbn; tauto]|]);
destruct j; discriminate Hj
| cbn; tauto
| cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rblk
| exact Hblk_rng
| cbn; tauto
| apply (U_sext32_low _ 46 fmt X14); clear - Hfmt; lia
| cbn; tauto ]
| cbn [app] in Hobj; clear HRr ] end end end.
assert (Hblknz : blk <> 0) by (clear - Hblk4096; lia).
ga_join HS ss_EPI2 3000%nat rga_deads_X ltac:(idtac).
lazymatch goal with |- SRr _ ?W3y (mkCfg ?msy ?mdy) (rga_post _ ?cxv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HX : INV_X B cxv Ev (k + 1) ly8 S8 W3y msy mdy) end end.
{
split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|].
rga_cbn_cx_goal.
eexists s7, blk, fmt, _.
split; [exact Hobj|].
split; [exact Hcg9|].
split; [exact Hwf7|].
split; [exact HcW7|].
split; [exact HcH7|].
split; [exact Hattr7|].
split; [exact Hraw7|].
split; [right; exact Hfmt|].
split.
{
eapply Permutation_trans; [exact HPm8|].
subst bl8.
unfold trgb_own.
rewrite (optb_nz blk _ Hblknz).
YI0g.perm_tac.
}
intros b Hb.
unfold rgc_FP.
rga_cbn_cx_goal.
unfold trgb_own in Hb.
destruct Hb as [<- | Hb].
-
split.
+
intros _ i Hi.
cbn [fst snd] in *.
apply (inFP_ablocks_fp _ r RGB_SIZE); [left; reflexivity | exact Hi].
+
intros blc lyq i Hbl Hi.
cbn [fst snd] in *.
apply Ar; [exact Hbl | change (req_size RGB_SIZE) with 64 in Hi; exact Hi].
-
apply in_app_or in Hb.
destruct Hb as [Hb | Hb].
+
exact (Hnew7 b Hb).
+
rewrite (optb_nz blk _ Hblknz) in Hb.
destruct Hb as [<- | []].
split; [exact Tblk | intros blc lyq i Hbl Hi; exact (Ablk blc lyq [] i Hbl Hi)].
}
rga_hand RX HS HJ8 (k + 1); [rga_E_tac HEE8 | exact HX].
Qed.
End e.
End d.
