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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCns YCnt YCnu.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis ADDFRAME : taddframe_specG B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_FIN1 : rga_fromFA B ss_FINb (fun _ => INV_FINb B) -> rga_from B ss_FINa (INV_FIN B).
Proof.
intros RC.
rga_prelude.
destruct HINV as (blk & fim & Hk0 & Hfmt & HPm3 & (Rblk & Tblk & Ablk) & (Rfim & Tfim & Afim)).
destruct Hk0 as [Hk0 Hbud].
assert (Hrin3 : In (r, 64) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hrin]).
pose proof (EFA3 7 fpos) as EFA37.
fold F in EFA37.
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
shok_auto SHOK GBx E (mrestrict (w_H W3) (ms_mem ms3)).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK GBspan A_cgif_addframe.
all: try (unfold GBx; ga_obl_blk HJ3 E10n E44 Hrin3).
1: ga_awrR AG fpos F EFA3 54%nat 67%nat.
clear HF HFr HG.
rreg HS (10%bv : bv 5) Ra0.
rreg HS (11%bv : bv 5) Ra1.
rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp.
rreg HS (3%bv : bv 5) Rgp.
rreg HS (4%bv : bv 5) Rtp.
rreg HS (8%bv : bv 5) Rs0.
rga_chain HS HJ3 AG EE.
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct (proj1 (proj2 HJ3)) as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
m_fact_of HS 1012%nat Hlct.
assert (Hblk_in3 : In (blk, fmt * N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; left; reflexivity]).
assert (Hfim_in3 : In (fim, N) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; right; right; left; reflexivity]).
pose proof (req_size_pos (fmt * N) ltac:(clear - HfN; lia)) as Hrq.
pose proof (req_size_pos N ltac:(clear - HN1; lia)) as HrqN.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ fim N HAR3 Hfim_in3) as (Hfim4096 & Hfimzone & Hfimceil & Hfim16).
assert (Hfim_rng : 0 <= fim < 2 ^ 64) by (clear - Hfim4096 Hfimceil HrqN C1; lia).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HB54 : bv_unsigned (ew Ex 54) = F) by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite RF; apply unsigned_lit_small; exact HFrng);
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 0 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 54%nat) ?lo ?hi ?wlo ?whi ?cs) =>
let e1 := ga_chunk_sv cs 5168 4%N in
pose proof (rg_field_of_region_any Ex _ 54 F cs lo hi wlo whi 5168 4%N e1 HRc HB54 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vattr;
let e2 := ga_chunk_sv cs 5172 4%N in
pose proof (rg_field_of_region_any Ex _ 54 F cs lo hi wlo whi 5172 4%N e2 HRc HB54 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vgen;
let e3 := ga_chunk_sv cs 5176 2%N in
pose proof (rg_field_of_region_any Ex _ 54 F cs lo hi wlo whi 5176 2%N e3 HRc HB54 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vdelay;
let e4 := ga_chunk_sv cs 5178 2%N in
pose proof (rg_field_of_region_any Ex _ 54 F cs lo hi wlo whi 5178 2%N e4 HRc HB54 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vnlp;
let e5 := ga_chunk_sv cs 5180 1%N in
pose proof (rg_field_of_region_any Ex _ 54 F cs lo hi wlo whi 5180 1%N e5 HRc HB54 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vtidx
end; clear HRc;
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) 2 _ HS eq_refl) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YQ0b.mkRegion (Some 54%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 54 F cs lo hi wlo whi 5152 8%N (SOff 54 4256) (F + 4256) HRc HB54 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite HB54; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HF4096 HFceil C1; lia) ltac:(cbn; lia)) as Vlpal;
pose proof (field_of_region Ex _ 54 F cs lo hi wlo whi 5160 8%N (SOff 184 0) fim HRc HB54 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact Rfim) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hfim_rng) ltac:(cbn; lia)) as Vimg
end; clear HRc end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vattr, Vgen, Vdelay, Vnlp, Vtidx, Vlpal, Vimg.
lazymatch type of Vattr with val_mem _ _ _ _ ?v => set (fattrv := v) in * end.
lazymatch type of Vgen with val_mem _ _ _ _ ?v => set (fgenv := v) in * end.
lazymatch type of Vdelay with val_mem _ _ _ _ ?v => set (delayv := v) in * end.
lazymatch type of Vnlp with val_mem _ _ _ _ ?v => set (nlpv := v) in * end.
lazymatch type of Vtidx with val_mem _ _ _ _ ?v => set (tidxv := v) in * end.
assert (Hnlp255 : 0 <= nlpv <= 255).
{
subst nlpv.
cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
change (2 ^ (8 * Z.of_N 2)) with 65536.
destruct Hlct as (Hl1 & _).
rewrite Z.mod_small by (clear - Hl1; lia).
exact Hl1.
}
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Ocfg : obj_at trbsegs (mrestrict (w_H W3) (ms_mem msX)) (F + 5152) LAY_FrameConfig [F + 4256; fim; fattrv; fgenv; delayv; nlpv; tidxv]) end.
{
cbn [obj_at LAY_FrameConfig].
unfold field_ok.
cbn [fst snd N.to_nat Z.of_N Pos.to_nat Pos.iter_op Nat.add].
replace (F + 5152 + 0) with (F + 5152) by lia.
replace (F + 5152 + 8) with (F + 5160) by lia.
replace (F + 5152 + 16) with (F + 5168) by lia.
replace (F + 5152 + 20) with (F + 5172) by lia.
replace (F + 5152 + 24) with (F + 5176) by lia.
replace (F + 5152 + 26) with (F + 5178) by lia.
replace (F + 5152 + 28) with (F + 5180) by lia.
repeat split; try assumption; try (subst fattrv fgenv delayv tidxv; apply Z.mod_pos_bound; reflexivity); try (apply Z.mod_pos_bound; reflexivity).
all: idtac.
all: change (2 ^ (8 * 8)) with (2 ^ 64); first [clear - HF4096 HFceil C1; lia | clear - Hfim_rng; lia].
}
ga_ra_frame HS AG HFq F 644 644 4 HRAcfg.
ga_ra_frame HS AG HFq F 532 532 96 HRApal.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Hcg3 : tcgif_at (mrestrict (w_H W3) (ms_mem msX)) g s) end.
{
apply (rg_tcgif_at_blocks_kept (w_H W) (w_H W3) mem _ g s N Hcg).
intros b sz Hb.
pose proof HPerm as HPerm'.
unfold trgb_own in HPerm'.
cbn [app] in HPerm'.
lazymatch goal with |- rg_blk_kept _ _ _ ?mm _ _ =>
lazymatch type of HBASE0 with rga_base _ ?cxv =>
pose proof (rga_entry_blk_kept B LAWS cxv [(7, fpos)] ly3 S3 W3 mm _ k b sz _ HJ3 HAR HPerm') as HEK end end.
rga_cbn_cx HEK.
apply HEK.
-
apply in_or_app.
left.
apply in_or_app.
left.
exact Hb.
-
eapply Permutation_in; [apply Permutation_sym; exact HPm3|].
apply in_or_app.
left.
eapply Permutation_in; [apply Permutation_sym; exact HPerm|].
right.
apply in_or_app.
left.
apply in_or_app.
left.
exact Hb.
}
assert (HEVc : vev S3 + EV_ADDFRAME <= VEV_MAX) by (rga_room Hev Hbud; (clear - Hk0; rga_lia)).
assert (HLIVEc : blocks_bytes S3 + LIVE_ADDFRAME <= LIVE_MAX).
{
rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPm3), bsum_app, <- (blocks_bytes_bsum B ly S).
cbn [bsum fold_right snd].
clear - Hlive HfN HN1 HN.
unfold LIVE_RGBADD, LIVE_ADDFRAME, LIVE_MAX, RGB_NMAX in *.
lia.
}
assert (HPcall : Permutation (ablocks B ly3 S3) (cgif_blocks g s N ++ (fim, N) :: ((r, RGB_SIZE) :: optb bef (beffmt * N) ++ timg_block img fmt N ++ rest ++ [(blk, fmt * N)]))).
{
eapply Permutation_trans; [exact HPm3|].
eapply Permutation_trans; [apply Permutation_app_tail; exact HPerm|].
unfold trgb_own.
YI0g.perm_tac.
}
assert (Hwf0 : cgif_wf s N) by (exact (conj Hwf1 (conj HW1 (conj HH1 (conj HNWH (conj HNmax Hwf6)))))).
lazymatch type of HBASE0 with rga_base _ ?cxv =>
lazymatch type of HJ3 with ajournal _ _ _ _ ?FPsm _ _ _ _ _ _ _ _ _ _ _ _ =>
pose proof (ajournal_fp_mono B _ _ FPsm (rgc_FP cxv) _ _ _ _ _ _ _ _ _ _ _ _ (m_fps_sub_fp cxv) HJ3) as HJF end end.
unfold rgc_FP in HJF.
rga_cbn_cx HJF.
assert (HF8m : F mod 8 = 0) by (rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult).
set (restc := (r, RGB_SIZE) :: optb bef (beffmt * N) ++ timg_block img fmt N ++ rest ++ [(blk, fmt * N)]) in *.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) => assert (HspX : spZ (ms_regs msX) = spZ regs - 576) by (unfold spZ at 1; rewrite Rsp; ga_evalE AG; clear; lia) end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call trbsegs B LAWS Hsegs W3 Ex ssX msX TRGBADD_STK (spZ regs) (ablocks_fp (trgb_own r g s N bef beffmt)) ly S W mem md [(7, fpos)] ly3 S3 mdX k
TADDFRAME_STK (ablocks_fp (cgif_blocks g s N)) EV_ADDFRAME
(-576) (ew Ex 2) (Z_to_bv 64 0x8488c) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => exists s' : cgif_st,
tcgif_at (mrestrict (w_H W2) mem2) g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
Permutation (ablocks B ly2 S2) (cgif_blocks g s' N ++ (fim, N) :: restc) /\
(forall b, In b (cgif_blocks g s' N) ->
aftok (ablocks_fp (cgif_blocks g s N)) (ablocks B ly3 S3) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TADDFRAME_STK (spZ (ms_regs msX)) (ablocks_fp (cgif_blocks g s N)) (ablocks B ly3 S3) blc ly2 [] (fst b + i))) HS eq_refl HJF);
[ rewrite Rsp; cbn [sv_denot]; reflexivity
| reflexivity
| ga_evalE AG
| reflexivity
| clear; lia
| vm_compute; discriminate
| rewrite FFS; vm_compute; discriminate
| rewrite Rgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| rewrite unsigned_lit_small by (clear; lia); clear; lia
| unfold s0Z; rewrite Rs0; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
replace (spZ regs + -576) with (spZ regs - 576) by (clear; lia); exact (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1)
| intros HPRE1; eapply SRr_mono;
[ pose proof (ADDFRAME ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch) g (F + 5152) s N
(F + 4256) fim fattrv fgenv delayv nlpv tidxv restc HPRE1) as CALL;
unfold cfg_at, apost_base in CALL; cbn [ss_pc];
let v := eval vm_compute in A_cgif_addframe in change (w64 A_cgif_addframe) with (Z_to_bv 64 v) in CALL;
apply CALL; clear CALL
| cbv beta; intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HJc & HPc & HK7);
exists ly7, S7, regs7, mem7, md7; split; [rewrite Rra; reflexivity|]; split; [exact HJc|]; split; [exact HPc | exact HK7] ]
| idtac ]
| ] end end.
-
unfold raZ at 1.
rewrite Rra, unsigned_lit_small by (clear; lia).
cbn [spine map fst snd].
fold (spine ch).
rewrite <- ?Hra88.
destruct Hspine as [Hs | Hs]; rewrite Hs; cbn; rewrite <- ?Hra88; tauto.
-
rewrite Hfrs3.
cbn [length].
clear - Hroom.
lia.
-
eapply arodata_ok_journal; [exact HJ3 | exact HROD].
-
rewrite Ra0.
repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia].
rewrite (AG 32%nat) by lia.
exact E32.
-
rewrite Ra1.
rewrite RF, unsigned_lit_small by exact HFrng.
reflexivity.
-
split; [exists 7, fpos; split; [exact Hfin3 | split; [clear; lia | rewrite EFA3; fold F; split; [exact HF8m | change (fs_frame_bytes 7) with 8192; clear; lia]]]|].
split; [rewrite Z.add_mod, HF8m by lia; reflexivity | exact HRAcfg].
-
exact Ocfg.
-
exact Hcg3.
-
exact Hwf0.
-
intros _.
split; [exists 7, fpos; split; [exact Hfin3 | split; [clear; lia | rewrite EFA3; fold F; split; [exact HF8m | change (fs_frame_bytes 7) with 8192; clear - Hnlp255; lia]]]|].
split; [rewrite Z.add_mod, HF8m by lia; reflexivity | eapply range_addressable_sub; [exact HRApal | clear; lia | clear - Hnlp255; lia]].
-
exact HPcall.
-
exact HEVc.
-
exact HLIVEc.
-
intros a Ha.
left.
destruct (inFP_ablocks_fp_inv _ _ Ha) as (b & n & Hbn & Hrg).
split.
+
replace a with (b + (a - b)) by (clear; lia).
apply (inFP_ablocks_fp _ b n); [unfold trgb_own; right; apply in_or_app; left; exact Hbn | clear - Hrg; lia].
+
exists b, n.
split; [|exact Hrg].
eapply Permutation_in; [apply Permutation_sym; exact HPcall|].
apply in_or_app.
left.
exact Hbn.
-
cbv beta.
intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HJc & HP7 & (s7 & Hcg7 & Hwf7 & HcW7 & HcH7 & Hattr7 & Hraw7 & HK7 & Hnew7)).
pose proof HJc as (_ & _ & _ & _ & _ & _ & (_ & Hd7) & _).
clear Ra0 Ra1 Rra Rsp Rgp Rtp Rs0 Hch1 HUPc Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0 Vattr Vgen Vdelay Vnlp Vtidx Vlpal Vimg Ocfg HRAcfg HRApal.
pose proof HJ7 as (HAR7 & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr ly c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); reflexivity).
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs7 & _).
cbn [app] in Hfrs7.
assert (Hfin7 : In (7, fpos) (frames S7)) by (rewrite Hfrs7; exact Hfin3).
assert (HfinS7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact HfinS3).
assert (Hrin7 : In (r, 64) (ablocks B ly7 S7)) by (eapply Permutation_in; [apply Permutation_sym; exact HK7 | apply in_or_app; right; right; left; reflexivity]).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7).
change (fs_frame_bytes 7) with 8192 in HFpres7, HFSpres7.
change (8192 / 8) with 1024 in HFSpres7.
rewrite EFA7 in HFpres7, HFSpres7.
fold F in HFpres7, HFSpres7.
ga_aconsts HROD HJ7 Kgot7 Kcell7 Kguar7 Kuar7 Vgr7.
assert (HFPlive : forall b n, In (b, n) (cgif_blocks g s N) -> In (b, n) (ablocks B ly3 S3))
by (intros b n Hbn; eapply Permutation_in; [apply Permutation_sym; exact HPcall | apply in_or_app; left; exact Hbn]).
assert (HPr3 : Permutation (ablocks B ly3 S3) ((r, RGB_SIZE) :: (cgif_blocks g s N ++ (fim, N) :: optb bef (beffmt * N) ++ timg_block img fmt N ++ rest ++ [(blk, fmt * N)])))
by (eapply Permutation_trans; [exact HPcall|]; subst restc; YI0g.perm_tac).
assert (HnoF : forall a, F <= a < F + 8192 -> ~ inFP (ablocks_fp (cgif_blocks g s N)) a).
{
intros a Ha Hn.
destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg).
pose proof (HFPlive b n Hbn) as Hlv.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ b n 7 fpos HAR3 Hlv Hfin3) as Dd.
rewrite EFA3 in Dd.
fold F in Dd.
unfold zdisjoint in Dd.
cbn [fst snd] in Dd.
change (fs_frame_bytes 7) with 8192 in Dd.
clear - Dd Ha Hrg.
lia.
}
assert (HnoS : forall a, 2147450880 + F / 8 <= a < 2147450880 + F / 8 + 1024 -> ~ inFP (ablocks_fp (cgif_blocks g s N)) a).
{
intros a Ha Hn.
destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg).
pose proof (HFPlive b n Hbn) as Hlv.
destruct (rga_blk_range B LAWS ly3 S3 _ _ _ b n HAR3 Hlv) as (_ & (_ & Hbz) & _).
clear - Ha Hrg Hbz HF8lo HF8hi HFq HF8 HFceil C1.
lia.
}
assert (HnoR : forall a, r <= a < r + 64 -> ~ inFP (ablocks_fp (cgif_blocks g s N)) a).
{
intros a Ha Hn.
destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg).
pose proof (rg_sep_head_in B LAWS ly3 S3 _ _ _ (r, RGB_SIZE) _ (b, n) HAR3 HPr3 ltac:(apply in_or_app; left; exact Hbn)) as Dd.
unfold zdisjoint, block_rng in Dd.
cbn [fst snd] in Dd.
change (req_size RGB_SIZE) with 64 in Dd.
clear - Dd Ha Hrg.
lia.
}
assert (HnoC : forall a, cfp <= a < cfp + 24 -> ~ inFP (ablocks_fp (cgif_blocks g s N)) a).
{
intros a Ha Hn.
destruct (inFP_ablocks_fp_inv _ _ Hn) as (b & n & Hbn & Hrg).
pose proof (HFPlive b n Hbn) as Hlv.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ b n cid pos HAR3 Hlv HfinS3) as Dd.
rewrite EFA3 in Dd.
unfold zdisjoint in Dd.
cbn [fst snd] in Dd.
clear - Dd Ha Hrg Hflo Hfhi.
lia.
}
idtac "OK-FACTS".
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub trbsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat);
[exact HJc | exact HJ7 | ga_evalE AG; exact Usp | clear; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 54%nat) _ _ _ _ _) =>
eapply (rg_region_kept_frame_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 54%nat); [exact HJc | ga_evalE AG; first [exact RF | rewrite RF; apply unsigned_lit_small; lia] | exact Hfin3
| rewrite ?EFA3; fold F; change (fs_frame_bytes 7) with 8192; lia | rewrite ?EFA3; fold F; change (fs_frame_bytes 7) with 8192; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnoF; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (fun H => proj1 (HFpres7 a H)); lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 67%nat) _ _ _ _ _) =>
eapply (rg_region_kept_fshadow_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 67%nat); [exact HJc | ga_evalE AG; first [exact E67 | rewrite E67; apply unsigned_lit_small; unfold SB; lia] | exact Hfin3
| rewrite ?EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; unfold SB; lia
| rewrite ?EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 7 / 8) with 1024; unfold SB; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnoS; unfold SB in Ha; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exfalso; clear - Ha; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (rg_region_kept_block_subw2 _ LAWS); [exact HJc | ga_evalE AG; first [exact E10n | rewrite E10n; apply unsigned_lit_small; lia] | exact Hrin3 | exact Hrin7
| clear; lia | change (req_size 64) with 64; clear; lia | clear; lia | clear; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnoR; lia ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (rg_region_kept_frame_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 11%nat _ _ _ _ _ _ cid pos); [exact HJc | ga_evalE AG; first [exact E11n | rewrite E11n; apply unsigned_lit_small; lia] | exact HfinS3
| rewrite ?EFA3; clear - Hflo; lia | rewrite ?EFA3; clear - Hfhi; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnoC; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exfalso; clear - Ha; lia ]
end
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
idtac "OK-RESEAT".
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
rename Kgot7 into Kgot0.
rename Kcell7 into Kcell0.
rename Kguar7 into Kguar0.
rename Kuar7 into Kuar0.
rename Vgr7 into Vgr0.
lazymatch type of HS with st_ok _ _ _ (restrict _ (mkst ?rg ?pcx ?mm ?rm)) => change mm with (ms_mem (mkst rg pcx mm rm)) in HJ7 end.
ga_relow HS AG E10 E11 E10n E11n.
lazymatch goal with |- SRr _ _ _ (rga_post _ ?cxv) => rga_E_now cxv HS HEE7 end.
pose proof (EFA7 7 fpos) as EFA77.
fold F in EFA77.
reshok_bx HS 44%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ7 SHOK GBspan A_wrap_free.
all: try (unfold GBx; ga_obl_blk HJ7 E10n E44 Hrin7).
assert (ArF : forall blc (lyq : alayout) (ownq : list (Z * Z)) i, In (r, 64) blc -> 0 <= i < 64 ->
awr_byte TRGBADD_STK (spZ regs) (ablocks_fp (trgb_own r g s N bef beffmt)) (ablocks B ly S) blc lyq ownq (r + i))
by (intros blc0 lyq0 ownq0 i0 Hb0 Hi0; eapply m_awr_mono; [|exact (Ar blc0 lyq0 ownq0 i0 Hb0 Hi0)];
lazymatch type of HBASE0 with rga_base _ ?cxv => exact (m_fps_sub_fp cxv) end).
clear Ar.
1: ga_awrR AG fpos F EFA7 54%nat 67%nat.
m_run_kept HFr AG (m_ZsP F r) Hceil Hslo FFS UN1.
clear HF HFr HG.
norm_ss HS.
assert (Hfrs7' : frames S7 = (7, fpos) :: frames S) by (rewrite Hfrs7; exact Hfrs3).
assert (HPr7 : Permutation (ablocks B ly7 S7) ((r, RGB_SIZE) :: (cgif_blocks g s7 N ++ (fim, N) :: optb bef (beffmt * N) ++ timg_block img fmt N ++ rest ++ [(blk, fmt * N)])))
by (eapply Permutation_trans; [exact HK7|]; subst restc; YI0g.perm_tac).
rga_hand RC HS HJ7 (k + EV_ADDFRAME); [rga_E_tac HEE7 | ].
exists blk, fim, s7. split; [split; [clear - Hk0; lia | rga_bud_tac Hbud]|]. split; [exact Hfmt|].
split.
{ apply (rg_tcgif_at_blocks_kept (w_H W7) (w_H W7) mem7 _ g s7 N Hcg7). intros b sz Hb i Hi.
destruct (m_blk_off_zs B LAWS ly7 S7 _ _ _ b sz r _ fpos HAR7 HPr7 ltac:(apply in_or_app; left; exact Hb) Hfin7 (b + i) ltac:(clear - Hi; lia)) as (Hr1 & Hr2).
rewrite EFA7 in Hr2. fold F in Hr2. apply UN1; assumption. }
split; [exact Hwf7|]. split; [rewrite HcW7; exact HcW|]. split; [rewrite HcH7; exact HcH|]. split; [exact Hattr7|]. split; [exact Hraw7|].
split; [exact HPr7|].
split; [lazymatch type of Rblk with ew ?Ex _ = _ => apply (rga_newblkF_of B _ Ex) end; [split; [exact Rblk | split; [exact Tblk | exact Ablk]] | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; reflexivity]|].
split; [lazymatch type of Rfim with ew ?Ex _ = _ => apply (rga_newblkF_of B _ Ex) end; [split; [exact Rfim | split; [exact Tfim | exact Afim]] | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; reflexivity]|].
intros b Hb. destruct (Hnew7 b Hb) as [Tb Ab]. split.
+ intros Hin0 i Hi. unfold rgc_FP. rga_cbn_cx_goal.
assert (Hin3 : In b (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hin0]).
destruct (inFP_ablocks_fp_inv _ _ (Tb Hin3 i Hi)) as (b1 & n1 & Hbn1 & Hrg1).
replace (fst b + i) with (b1 + (fst b + i - b1)) by (clear; lia).
apply (inFP_ablocks_fp _ b1 n1); [unfold trgb_own; right; apply in_or_app; left; exact Hbn1 | clear - Hrg1; lia].
+ intros blc lyq i Hbl Hi. unfold rgc_FP. rga_cbn_cx_goal.
apply (m_awr_byte_callee TRGBADD_STK TADDFRAME_STK (spZ regs) (spZ regs - 576) _ (ablocks_fp (cgif_blocks g s N)) (ablocks B ly S) (ablocks B ly3 S3) blc lyq ly7 [] (fst b + i));
[ rewrite <- HspX; apply Ab; [exact Hbl | exact Hi]
| assert (FFA : TADDFRAME_STK = 17664) by reflexivity; clear - FFS FFA; lia
| clear; lia
| intros x Hx; destruct (inFP_ablocks_fp_inv _ _ Hx) as (b1 & n1 & Hbn1 & Hrg1); replace x with (b1 + (x - b1)) by (clear; lia);
apply (inFP_ablocks_fp _ b1 n1); [unfold trgb_own; right; apply in_or_app; left; exact Hbn1 | clear - Hrg1; lia]
| intros b0 Hb0; eapply Permutation_in; [apply Permutation_sym; exact HPm3 | apply in_or_app; left; exact Hb0] ].
Qed.
End e.
End d.
