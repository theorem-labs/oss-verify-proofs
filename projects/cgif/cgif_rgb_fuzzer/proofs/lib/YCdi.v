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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20 YI1k YI16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCe9 YCfs YCfu YCe1 YCfq YCe4 YCe0 YCgv YCdq YCdu YCdf YCds YCdt YCdr YCdn YCdp YCdg YCdh.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma af_newcfg_kept0 : forall (m m' : word -> option byte) nw lpal lpal' fattr fgen delay nlp tidx,
af_newcfg m nw lpal fattr fgen delay nlp tidx ->
(forall a, nw + 8 <= a < nw + 40 -> mbyte trbsegs m' a = mbyte trbsegs m a) ->
val_mem trbsegs m' nw 8 lpal' ->
af_newcfg m' nw lpal' fattr fgen delay nlp tidx.
Proof.
intros m m' nw lpal lpal' fattr fgen delay nlp tidx (V0 & V16 & V20 & V24 & V26 & V28) HK V0'.
assert (T : forall a (n : nat) v, val_mem trbsegs m a n v -> nw + 8 <= a -> a + Z.of_nat n <= nw + 40 -> val_mem trbsegs m' a n v).
{ intros a n v Hv H1 H2 j Hj. rewrite (HK (a + Z.of_nat j)) by lia. exact (Hv j Hj). }
split; [exact V0'|]. split; [apply (T _ 4%nat _ V16); cbn; lia|]. split; [apply (T _ 4%nat _ V20); cbn; lia|].
split; [apply (T _ 2%nat _ V24); cbn; lia|]. split; [apply (T _ 2%nat _ V26); cbn; lia|].
intros H6. apply (T _ 1%nat _ (V28 H6)); cbn; lia.
Qed.
Lemma denot_3x : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 -> sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = w64 (3 * v).
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_mul_smallD; rewrite (U_atom E n v Hn), U_lit by lia; lia.
Qed.
Lemma U_mul3h16 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 ->
U E (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff n 0)) (SLit 1)) (SExt false 16 (SOff n 0))) = 3 * v.
Proof.
intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_zext, U_lit, (U_atom E n v Hn) by lia.
change (Z.of_N 16) with 16. rewrite (Z.mod_small v (2 ^ 16)) by lia. change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (v * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma denot_3xz : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff n 0)) (SLit 1)) (SExt false 16 (SOff n 0))) = w64 (3 * v).
Proof. intros E n v Hn Hv. rewrite denot_lit_U. unfold w64. f_equal. exact (U_mul3h16 E n v Hn Hv). Qed.
Lemma val_mem_keptZ : forall (m m' : word -> option byte) a (n : nat) v,
val_mem trbsegs m a n v -> (forall x, a <= x < a + Z.of_nat n -> mbyte trbsegs m' x = mbyte trbsegs m x) -> val_mem trbsegs m' a n v.
Proof. intros m m' a n v Hv HK j Hj. rewrite (HK (a + Z.of_nat j)) by lia. exact (Hv j Hj). Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition regsD3 : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 18 (SOff 32 0)) 8 (SOff 32 88)) 21 (SOff 38 0)) 22 (shq 32 88))
20 (SOff 32 40)) 26 (shq 32 40)) 9 (SOff 46 0)) 19 (SOff 46 16)) 25 (shq 46 16)) 27 (SOff 46 26).
Definition af_nwr3 : YQ0b.region := YQ0b.mkRegion (Some 23%nat) 0 40 0 8 [].
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma regsD3_ok : forall (regs regs1 : bvmap 5 word) g s1 cfp cf more,
af_regs_at B regs regs1 g -> getr regs1 9 = w64 cfp ->
getr regs1 19 = w64 (cfp + 16) -> getr regs1 25 = w64 (SB + (cfp + 16) / 8) -> getr regs1 27 = w64 (cfp + 26) ->
0 <= g -> g + 96 <= alloc_ceiling -> 0 <= cfp -> cfp + 32 <= alloc_ceiling ->
regs_ok (Ereg regs1 (af_extra regs g s1 cfp cf more)) regsD3 regs1.
Proof.
intros regs regs1 g s1 cfp cf more (R2 & R3 & R4 & R18 & R8 & R27 & R26 & R19 & R25) R9 RC16 RSC16 RS11 Hg0 Hgc Hc0 Hcc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Ereg regs1 (af_extra regs g s1 cfp cf more)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
assert (E46 : ew E 46 = Z_to_bv 64 cfp) by (subst E; change 46%nat with (32 + 14)%nat; rewrite (ew_Ereg_extra regs1 _ 14); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [
lazymatch goal with |- getr _ _ = sv_denot _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff ?n ?c) (SLit 3)) (SOff 38 0)) =>
first [ rewrite R26 | rewrite R25 | rewrite RSC16 ]; symmetry; unfold w64;
first [ apply (denot_shx E 32 38 c g SB E32 E38) | apply (denot_shx E 46 38 c cfp SB E46 E38) ]; unfold SB; lia end
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; first [exact R18 | rewrite unsigned_lit_small by lia; first [exact R8 | exact R19]]
| rewrite E38; exact R27
| rewrite E46; first [exact R9 | rewrite unsigned_lit_small by lia; first [exact RC16 | exact RS11]] ] ]
| ]); try (destruct Hr; fail).
Qed.
Lemma af_D3 : AF_RETC_stmt B -> AF_E_stmt B -> AF_D3_stmt B.
Proof.
intros PRC PE ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 i nw nimg
CX MID Hk HBB HR R9 R24i R23 RC16 RSC16 RS11 HL Hft Hi Hnone Hs1 HnwIn HniIn HNC HV8.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew & HnewX).
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
pose proof HR as (Rsp & Rgp & Rtp & R18 & R8 & R27 & R26 & R19 & R25s).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
assert (HEVF : EV_FLUSH = 35) by reflexivity. assert (HEVA : EV_ADDFRAME = 12 + EV_FLUSH) by reflexivity.
assert (HFS : FRAME_SIZE = 40) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trbsegs _ LAWS _ _ _ _ _ _ _ HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
assert (Hcfp : 4096 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
pose proof (in_app_sub _ _ cfp 32 Hfhigh ltac:(clear - Hflo; lia) ltac:(clear; lia) ltac:(clear - Hfhi; lia)) as Hcfp_ia.
clear Hfin Hcid0 Hfal Hflo Hfhi Hf4096 Hfceil Hfhigh Hfhigh_img Hcal HRA cid pos.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
pose proof HWF1 as (_ & HWge & HHge & HNWH & HNmax & _).
assert (HN1 : 1 <= N <= 100000000) by (clear - HWge HHge HNWH HNmax; nia).
assert (HrqN : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0) as [He | Hne]; [exfalso; clear - HN1 He; lia | reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & HnP & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_img _ _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as Hnh_img.
rewrite HFS in Hnceil. rewrite HFS in HnP. change (req_size 40) with 40 in Hnceil, HnP, Hnh_img.
assert (HPn : Permutation (ablocks B lyc Sc) ((nw, FRAME_SIZE) :: (nimg, N) :: cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest)).
{ eapply Permutation_trans; [exact HPerm1|].
apply (Permutation_app_swap_app (cgif_blocks g s1 N) [(nw, FRAME_SIZE); (nimg, N)] (af_cblocks img N fattr lpa nlp rest)). }
assert (SEPw : forall b m, In (b, m) ((nimg, N) :: cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) -> nw + 40 <= b \/ b + req_size m <= nw).
{ intros b m Hb. pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (nw, FRAME_SIZE) (b, m) _ HAR HPn Hb) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (HPi : Permutation (ablocks B lyc Sc) ((nimg, N) :: (nw, FRAME_SIZE) :: cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest)).
{ eapply Permutation_trans; [exact HPn|]. apply perm_swap. }
assert (SEPi : forall b m, In (b, m) ((nw, FRAME_SIZE) :: cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) -> nimg + N <= b \/ b + req_size m <= nimg).
{ intros b m Hb. pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (nimg, N) (b, m) _ HAR HPi Hb) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite HrqN in D. clear - D. lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ nimg N HAR HniIn) as (Hm16 & Hm4096 & Hmceil & Hmh_ia & HmP & _). pose proof (proj1 Hmh_ia) as Hmh. rewrite HrqN in Hmceil. rewrite HrqN in HmP.
pose proof (blk_off_img _ _ _ _ _ _ nimg N HAR HniIn) as Hmh_img.
assert (Dgn : g + 96 <= nw \/ nw + 40 <= g).
{ pose proof (SEPw g CGIF_SIZE ltac:(right; left; reflexivity)) as D. change (req_size CGIF_SIZE) with 96 in D. clear - D. lia. }
assert (Dcn : cfp + 32 <= nw \/ nw + 40 <= cfp).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ nw FRAME_SIZE cid pos HAR HnwIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
pose proof (obj_at_nth trbsegs _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. cbn [snd] in Rlpal.
pose proof (obj_at_nth trbsegs _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rnlp]. cbn [snd] in Rnlp.
assert (Hp3x : 0 <= 3 * nlp < 3 * 65536) by (clear - Rnlp; cbn in Rnlp; lia).
pose proof (req_size_pos (3 * nlp) ltac:(clear - Hp3x; lia)) as [Hrq1 Hrq2].
pose proof (obj_at_nth trbsegs _ _ _ _ 1 (8, 8%N) img HCF eq_refl eq_refl) as [_ Rimg]. cbn [snd] in Rimg.
pose proof (obj_at_nth trbsegs _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr.
set (E := Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [Z.land fattr 4])).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [Z.land fattr 4]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(lia)) as E32. pose proof (ES 36%nat ltac:(lia)) as E36. pose proof (ES 37%nat ltac:(lia)) as E37. pose proof (ES 38%nat ltac:(lia)) as E38.
pose proof (ES 42%nat ltac:(lia)) as E42. pose proof (ES 43%nat ltac:(lia)) as E43. pose proof (ES 46%nat ltac:(lia)) as E46.
pose proof (ES 47%nat ltac:(lia)) as E47. pose proof (ES 48%nat ltac:(lia)) as E48. pose proof (ES 49%nat ltac:(lia)) as E49. pose proof (ES 50%nat ltac:(lia)) as E50.
pose proof (ES 51%nat ltac:(lia)) as E51. pose proof (ES 52%nat ltac:(lia)) as E52. pose proof (ES 53%nat ltac:(lia)) as E53. pose proof (ES 67%nat ltac:(lia)) as E67.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E36, E37, E38, E42, E43, E46, E47, E48, E49, E50, E51, E52, E53, E67.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (Bnw : bv_unsigned (ew E 23) = nw) by (rewrite E23; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
destruct (af_reseedD B TL LAWS AF_D3 regsD3 0 0 [] ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc regs1 memc mdc k s1 [(nw, FRAME_SIZE); (nimg, N)] [] nw
CX MID Rsp R23 HnwIn HL ltac:(apply Forall_nil) ltac:(clear; lia) ltac:(clear; lia)
(regsD3_ok regs regs1 g s1 cfp _ _ HR R9 RC16 RSC16 RS11 ltac:(lia) Hgceil ltac:(lia) (proj2 Hcfp))
ltac:(vm_compute; reflexivity)) as [HS SHOK].
change (Ereg regs1 _) with E in HS, SHOK.
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspanA.
{ awr_a Usp E32u Hing HTS. }
rregD HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp. rreg HS (8%bv : bv 5) Qs0.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340936) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; reflexivity).
pose proof (kept_of_frame _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; clear - Hrr; lia|]); destruct Hin)) as UN1.
cbv beta in UN1. clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (CH : chain_pre lyc (aview trbsegs (w_H Wc) (ms_mem msX)) (ms_regs msX) []) end.
{ eapply (achain_chain_pre lyc _ (sp0 - 224) (g + 88) []).
- apply achain_low; clear - Hgceil; lia.
- unfold spZ; rewrite Qsp, Usp; clear - Hceil Hslo HTS; lia.
- unfold s0Z; rewrite Qs0; cbn [sv_denot]; rewrite E32u; apply unsigned_lit_small; clear - HZg; lia.
- unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
assert (HliveC : blocks_bytes Sc + 3 * nlp <= LIVE_MAX) by (clear - HBB Hlive HN1 HFS Hp3x; unfold LIVE_ADDFRAME in Hlive; lia).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_at trbsegs B LAWS Hsegs errno_low ML AMALLOC Wc (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPa g s N) ly S W mem md []
lyc Sc _ k (3 * nlp) (-224) (Z_to_bv 64 0x86cc4) [] HJ);
[ rewrite Ra0; exact (denot_3xz _ 52 nlp ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E52) ltac:(clear - Rnlp; cbn in Rnlp; lia))
| unfold MALLOC_MAX; clear - Hp3x; lia
| exact HliveC
| unfold spZ; rewrite Qsp, Usp; lia
| reflexivity
| clear; lia
| rewrite HTS, Has; clear; lia
| rewrite Qgp, (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite Qtp, (EEo 4%nat 4%bv eq_refl); exact Rtp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| clear - Hnev Hev Hk HEVF HEVA; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite HBcode, (tl_universe B TL);
apply TRACES_cgif_addframe_U; apply memZL_In; vm_compute; reflexivity ] end. }
cbv beta. clear Ra0 Rra Qsp Qgp Qtp Qs0 CH.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfrs2 & Hres).
pose proof (proj1 HJ2) as HAR2. pose proof HJ2 as (_ & HLY2 & _ & _ & _ & _ & Hnev2 & _).
destruct (mres_kept B lyc Sc Wc _ W2 mem2 ly2 S2 _ _ res (3 * nlp) Hres) as (HK & HBin & HresIn).
pose proof (mres_range B LAWS ly2 S2 W2 mem2 md2 lyc Sc res (3 * nlp) _ _ HAR2 Hres) as Hrng.
pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & _ & _).
assert (EFA2 : frame_addr ly2 cid pos = frame_addr lyc cid pos).
{ unfold frame_addr. destruct HLY2 as (_ & _ & _ & _ & _ & E6 & _). destruct HLY as (_ & _ & _ & _ & _ & E6' & _). rewrite E6, <- E6'. reflexivity. }
assert (SEPn : forall b m ii, In (b, m) (ablocks B lyc Sc) -> 0 <= ii < req_size m -> ~ (res <> 0 /\ res <= b + ii < res + req_size (3 * nlp))).
{ intros b m ii Hb Hii [Hnz Hin]. destruct Hres as [(Habs & _) | (_ & Ebl & _)]; [exact (Hnz Habs)|].
pose proof (sep_tmp_entry B LAWS ly2 S2 W2 mem2 md2 (ablocks B lyc Sc) res (3 * nlp) b m HAR2 ltac:(rewrite Ebl; apply Permutation_refl) Hb) as D.
clear - D Hii Hin. lia. }
assert (HnewG : forall a, g + 0 <= a < g + 96 -> ~ (res <> 0 /\ res <= a < res + req_size (3 * nlp))).
{ intros a Ha. replace a with (g + (a - g)) by (clear; lia). apply (SEPn g CGIF_SIZE (a - g) Hing). change (req_size CGIF_SIZE) with 96. clear - Ha. lia. }
assert (HnewN : forall a, nw + 0 <= a < nw + 40 -> ~ (res <> 0 /\ res <= a < res + req_size (3 * nlp))).
{ intros a Ha. replace a with (nw + (a - nw)) by (clear; lia). apply (SEPn nw FRAME_SIZE (a - nw) HnwIn). rewrite HFS. change (req_size 40) with 40. clear - Ha. lia. }
assert (HnewI : forall a, nimg <= a < nimg + N -> ~ (res <> 0 /\ res <= a < res + req_size (3 * nlp))).
{ intros a Ha. replace a with (nimg + (a - nimg)) by (clear; lia). apply (SEPn nimg N (a - nimg) HniIn). rewrite HrqN. clear - Ha. lia. }
assert (HnewF : forall a, cfp + 0 <= a < cfp + 32 -> ~ (res <> 0 /\ res <= a < res + req_size (3 * nlp))).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ res (3 * nlp) cid pos HAR2 (HresIn Hnz) ltac:(rewrite Hfrs2; exact Hfin)) as D.
rewrite EFA2 in D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D Ha Hin Hflo Hfhi. lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
jafter_call_keep HS 68%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- eapply (region_kept_stack_aj trbsegs B); [exact HK | exact HJ2 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- eapply (region_kept_stack_aj trbsegs B); [exact HK | exact HJ2 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot1) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot2) | clear; lia].
- apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell1) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell2) | clear; lia].
- eapply (region_kept_block_aj trbsegs B); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32u | exact Hing | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia | exact HnewG].
- eapply (region_kept_frame_aj trbsegs B); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E46; apply unsigned_lit_small; clear - Hcfp C1; lia | exact Hfin | clear - Hflo; lia | clear - Hfhi; lia | clear; lia | exact HnewF]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E2 := Ex) in HS end.
assert (OLD2 : forall n, (n < 68)%nat -> ew E2 n = ew E n) by (intros n Hn; subst E2; rewrite YO3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (E2r : ew E2 72 = Z_to_bv 64 res) by (subst E2; change 72%nat with (68 + 4)%nat; rewrite (YO3v.ew_havoc_new _ 68 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Ha0).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0 - 224) by (rewrite OLD2 by lia; exact Usp).
assert (E32u2 : bv_unsigned (ew E2 32) = g) by (rewrite OLD2 by lia; exact E32u).
assert (E32_2 : ew E2 32 = Z_to_bv 64 g) by (rewrite OLD2 by lia; exact E32).
assert (E23_2 : ew E2 23 = Z_to_bv 64 nw) by (rewrite OLD2 by lia; exact E23).
assert (Bnw2 : bv_unsigned (ew E2 23) = nw) by (rewrite OLD2 by lia; exact Bnw).
assert (E37_2 : ew E2 37 = Z_to_bv 64 (cg_cur s1)) by (rewrite OLD2 by lia; exact E37).
assert (E38_2 : ew E2 38 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E38).
assert (E46_2 : ew E2 46 = Z_to_bv 64 cfp) by (rewrite OLD2 by lia; exact E46).
assert (E47_2 : ew E2 47 = Z_to_bv 64 lpal) by (rewrite OLD2 by lia; exact E47).
assert (E48_2 : ew E2 48 = Z_to_bv 64 img) by (rewrite OLD2 by lia; exact E48).
assert (E49_2 : ew E2 49 = Z_to_bv 64 fattr) by (rewrite OLD2 by lia; exact E49).
assert (E67_2 : ew E2 67 = Z_to_bv 64 (Z.land fattr 4)) by (rewrite OLD2 by lia; exact E67).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 68)%nat -> ew E2 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD2 by exact Hn68; exact (EEo n rr Hn)).
assert (Kblk : forall b m, In (b, m) (ablocks B lyc Sc) -> blk_kept (w_H Wc) (w_H W2) memc mem2 b (req_size m)).
{ intros b m Hb ii Hii. pose proof HK as (_ & K2 & _). etransitivity; [exact (K2 b m ii Hb Hii (SEPn b m ii Hb Hii))|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4096 & Hbceil & _). apply UN1; clear - Hii Hb4096 Hbceil C1 Hceil Hslo HTS; lia. }
assert (HT2 : tcgif_at (mrestrict (w_H W2) mem2) g s1).
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- exact (obj_at_blk_kept _ _ _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF (Kblk g CGIF_SIZE Hing)).
- apply (obj_at_blk_kept _ _ _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). apply (Kblk (cg_raw s1) RAW_SIZE).
eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. right. left. reflexivity.
- intros f Hfi. apply (obj_at_blk_kept _ _ _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). apply (Kblk (fr_ptr f) FRAME_SIZE).
eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. left. exact (af_frame_in_blocks g s1 N f Hfi). }
assert (HFR2 : af_frame (mrestrict (w_H W2) mem2) sp0 regs).
{ apply (af_frame_kept _ _ sp0 regs HFR). intros a Ha. pose proof HK as (K1 & _). apply (mbyte_of_aview trbsegs).
etransitivity; [apply (K1 a); clear - Ha Hceil Hslo Hshi H47 HTS Has C1; lia|]. apply UN1; clear - Ha Hceil Hslo Hshi H47 HTS C1; lia. }
assert (HNC2 : af_newcfg (mrestrict (w_H W2) mem2) nw lpal fattr fgen delay nlp tidx).
{ apply (af_newcfg_kept _ _ nw lpal fattr fgen delay nlp tidx HNC). intros a Ha Hn. apply (mbyte_of_aview trbsegs).
replace a with (nw + (a - nw)) by (clear; lia). apply (Kblk nw FRAME_SIZE HnwIn). rewrite HFS. change (req_size 40) with 40. clear - Ha; lia. }
assert (HV8_2 : val_mem trbsegs (mrestrict (w_H W2) mem2) (nw + 8) 8 nimg).
{ apply (val_mem_keptZ _ _ _ 8%nat nimg HV8). intros x Hx. apply (mbyte_of_aview trbsegs).
replace x with (nw + (x - nw)) by (clear; lia). apply (Kblk nw FRAME_SIZE HnwIn). rewrite HFS. change (req_size 40) with 40. clear - Hx; cbn in Hx; lia. }
pose proof (obj_at_nth trbsegs _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT2) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
pose proof (HBin _ HnwIn) as HnwIn2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR2 HnwIn2) as (_ & _ & _ & _ & HnP2 & _). rewrite HFS in HnP2. change (req_size 40) with 40 in HnP2.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw2; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ af_nwr3 HS eq_refl
ltac:(unfold region_ok, af_nwr3; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw2; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HnP2 (nw + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, af_nwr3; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Bnw2, Usp2, E32u2, E46_2, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
clear SHOK. assert (SHOK : sh_ok trbsegs Bxa af_SH23 E2 (mrestrict (w_H W2) mem2)).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly2 S2 W2 _ _ _ g s N _ cfp 32 HJ2 HAR0 HPerm HFO) as (_ & _ & HRA2).
unfold sh_ok, af_SH23, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 (HBin _ Hing)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u2.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trbsegs (w_H W2) mem2 E2 Bxa 46 cfp 32 cfp 0 32 HRA2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 23 nw FRAME_SIZE 0 FRAME_SIZE HAR2 (HBin _ HnwIn)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bnw2.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
assert (Anw : forall blc ii lyq ownq, In (nw, FRAME_SIZE) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPa g s N) (ablocks B ly S) blc lyq ownq (nw + ii)).
{ intros blc ii lyq ownq Hbl Hii. exact (proj2 (HnewX _ (or_introl eq_refl)) blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
pose proof (HBin _ HniIn) as HniIn2.
destruct Hrng as [Hres0 | (Hr4096 & HrHi & HrCeil & Hr16 & HrIn)].
{
destruct Hres as [(_ & Ebl & _) | (Habs & _)]; [| exfalso; clear - Habs Hres0; lia].
pose proof (st_ok_pin_reg' trbsegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0, Hres0; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (List.filter (fun r => match YQ0b.r_base r with Some 23%nat => false | _ => true end) (ss_mem ssx)) in
pose proof (st_ok_submem trbsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_havoc trbsegs 84 Ex ssx msx [Z_to_bv 64 nimg] HS ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 23%nat) 0 40 0 8 [YQ0b.mkChunk 8 (CVal 8 (SOff 84 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite Bnw2; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HnP2 (nw + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs Ex _ nw 8 8 (SOff 84 0) nimg);
[ cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite unsigned_lit_small by (clear - Hm4096 Hmceil C1 HN1; lia); rewrite Z.add_0_r; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hm4096 Hmceil C1 HN1; lia | cbn; clear; lia | exact HV8_2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite Bnw2, Usp2, E32u2, E46_2, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
let HAGh := fresh "HAGh" in
assert (HAGh : env_agree 84 E2 Ex) by (apply env_agree_havoc_ge; [clear; lia | split; [intros; reflexivity | reflexivity]]);
pose proof (sh_ok_agree trbsegs Bxa af_SH23 84 E2 Ex _ HAGh eq_refl SHOK) as SHOK'; clear SHOK HAGh; rename SHOK' into SHOK end.
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK RBspanA.
{ awr_x Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS Bnw2 Anw HnwIn2. }
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw <= a < nw + 8)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bnw2 in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2b & _ & Kgot2b & _). rewrite HBgot, HBcell in Kgot2b. rewrite HBcell in Kcell2b.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp. rreg HS (8%bv : bv 5) Qs0.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (CH : chain_pre ly2 (aview trbsegs (w_H W2) (ms_mem msX)) (ms_regs msX) []) end.
{ eapply (achain_chain_pre ly2 _ (sp0 - 224) (g + 88) []).
- apply achain_low; clear - Hgceil; lia.
- unfold spZ; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp2; clear - Hceil Hslo HTS; lia.
- unfold s0Z; rewrite Qs0; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E32u2; apply unsigned_lit_small; clear - HZg; lia.
- unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_at trbsegs B LAWS Hsegs errno_low ML AFREE W2 (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPa g s N) ly S W mem md []
ly2 S2 _ (k + 1) nimg N (-224) (Z_to_bv 64 0x86fcc) [] HJ2 HniIn2);
[ rewrite Ra0; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| unfold spZ; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp2; lia
| reflexivity
| clear; lia
| rewrite HTS, Has; clear; lia
| rewrite Qgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo2 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite Qtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo2 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| clear - Hnev2 Hev Hk HEVF HEVA; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite HBcode, (tl_universe B TL);
apply TRACES_cgif_addframe_U; apply memZL_In; vm_compute; reflexivity
| intros HniOld ii Hii; exact (proj1 (HnewX _ (or_intror (or_introl eq_refl))) HniOld ii Hii) ] end. }
cbv beta. clear Ra0 Rra Qsp Qgp Qtp Qs0 CH.
intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1 & l2 & El1 & Eab3) & Hfrs3 & HK3).
pose proof (proj1 HJ3) as HAR3. pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _).
rewrite HrqN in HK3.
replace (sp0 + -224 - ASTACK) with (sp0 - 224 - ASTACK) in HK3 by (clear; lia). replace (sp0 + -224) with (sp0 - 224) in HK3 by (clear; lia).
assert (HPerm3 : Permutation (ablocks B ly3 S3) ((nw, FRAME_SIZE) :: cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest)).
{ rewrite Eab3. apply Permutation_sym. apply (Permutation_cons_app_inv l1 l2 (a := (nimg, N))). apply Permutation_sym. rewrite <- El1, Ebl. exact HPi. }
assert (HBl3 : forall b m, In (b, m) (ablocks B lyc Sc) -> (b, m) <> (nimg, N) -> In (b, m) (ablocks B ly3 S3)).
{ intros b m Hb Hne. rewrite Eab3. rewrite <- Ebl, El1 in Hb. apply in_app_iff in Hb. apply in_app_iff.
destruct Hb as [Hb | [Hb | Hb]]; [left; exact Hb | exfalso; exact (Hne (eq_sym Hb)) | right; exact Hb]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)).
{ apply (HBl3 _ _ Hing). intros Hq. pose proof (f_equal fst Hq) as Hq1. cbn [fst] in Hq1.
pose proof (SEPi g CGIF_SIZE ltac:(right; left; reflexivity)) as D. change (req_size CGIF_SIZE) with 96 in D. clear - Hq1 D HN1. lia. }
assert (HnwIn3 : In (nw, FRAME_SIZE) (ablocks B ly3 S3)).
{ apply (HBl3 _ _ HnwIn). intros Hq. pose proof (f_equal fst Hq) as Hq1. cbn [fst] in Hq1.
pose proof (SEPi nw FRAME_SIZE ltac:(left; reflexivity)) as D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - Hq1 D HN1. lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
assert (EFA3 : frame_addr ly3 cid pos = frame_addr lyc cid pos).
{ unfold frame_addr. destruct HLY3 as (_ & _ & _ & _ & _ & E6 & _). destruct HLY as (_ & _ & _ & _ & _ & E6' & _). rewrite E6, <- E6'. reflexivity. }
assert (Dni : nimg + N <= nw \/ nw + 40 <= nimg).
{ pose proof (SEPi nw FRAME_SIZE ltac:(left; reflexivity)) as D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 Bxa af_SH23 ss) end in
jafter_call_keep HS K regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | apply Forall_nil].
- eapply (region_kept_block_ajw2 trbsegs _ LAWS); [exact HK3 | exact HAR3 | exact HnwIn3
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Bnw2
| exact HnwIn2 | clear; lia | rewrite HFS; change (req_size 40) with 40; clear; lia | clear; lia | clear; lia | intros a Ha Hc; clear - Ha Hc Dni; lia].
- eapply (region_kept_stack_aj trbsegs B); [exact HK3 | exact HJ3 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Usp2 | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- eapply (region_kept_stack_aj trbsegs B); [exact HK3 | exact HJ3 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Usp2 | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot2b) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot3) | clear; lia].
- apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell2b) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell3) | clear; lia].
- eapply (region_kept_block_aj trbsegs B); [exact HK3 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32u2 | exact (HBin _ Hing) | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hc; pose proof (SEPi g CGIF_SIZE ltac:(right; left; reflexivity)) as D; change (req_size CGIF_SIZE) with 96 in D; clear - Ha Hc D; lia].
- eapply (region_kept_frame_aj trbsegs B); [exact HK3 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E46_2; apply unsigned_lit_small; clear - Hcfp C1; lia
| rewrite Hfrs2; exact Hfin | rewrite EFA2; clear - Hflo; lia | rewrite EFA2; clear - Hfhi; lia | clear; lia
| intros a Ha Hc; pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ nimg N cid pos HAR HniIn Hfin) as D;
unfold zdisjoint in D; cbn [fst snd] in D; rewrite HrqN in D; clear - Ha Hc D Hflo Hfhi; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E3 := Ex) in HS end.
assert (OLD3 : forall n, (n < 84)%nat -> ew E3 n = ew E2 n) by (intros n Hn; subst E3; rewrite YO3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite ?YO3v.ew_havoc_old by lia; reflexivity).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0 - 224) by (rewrite OLD3 by lia; exact Usp2).
assert (E32u3 : bv_unsigned (ew E3 32) = g) by (rewrite OLD3 by lia; exact E32u2).
assert (E32_3 : ew E3 32 = Z_to_bv 64 g) by (rewrite OLD3 by lia; exact E32_2).
assert (E38_3 : ew E3 38 = Z_to_bv 64 SB) by (rewrite OLD3 by lia; exact E38_2).
assert (E46_3 : ew E3 46 = Z_to_bv 64 cfp) by (rewrite OLD3 by lia; exact E46_2).
assert (E23_3 : ew E3 23 = Z_to_bv 64 nw) by (rewrite OLD3 by lia; exact E23_2).
assert (Bnw3 : bv_unsigned (ew E3 23) = nw) by (rewrite OLD3 by lia; exact Bnw2).
assert (EEo3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 68)%nat -> ew E3 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD3 by lia; exact (EEo2 n rr Hn Hn68)).
clear SHOK. assert (SHOK : sh_ok trbsegs Bxa af_SH23 E3 (mrestrict (w_H W3) mem3)).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly3 S3 W3 _ _ _ g s N _ cfp 32 HJ3 HAR0 HPerm HFO) as (_ & _ & HRA3).
unfold sh_ok, af_SH23, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block trbsegs B LAWS ly3 S3 W3 mem3 md3 E3 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR3 Hing3).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u3.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trbsegs (w_H W3) mem3 E3 Bxa 46 cfp 32 cfp 0 32 HRA3).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block trbsegs B LAWS ly3 S3 W3 mem3 md3 E3 Bxa 23 nw FRAME_SIZE 0 FRAME_SIZE HAR3 HnwIn3).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bnw3.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RBspanA.
all: try (awr_x Usp3 E32u3 Hing3 HTS Bnw3 Anw HnwIn3).
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw <= a < nw + 8)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bnw2, ?Usp3, ?E32u3, ?Bnw3 in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ3)) as (Kcell3b & _ & Kgot3b & _). rewrite HBgot, HBcell in Kgot3b. rewrite HBcell in Kcell3b.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp. rreg HS (8%bv : bv 5) Qs0.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (CH : chain_pre ly3 (aview trbsegs (w_H W3) (ms_mem msX)) (ms_regs msX) []) end.
{ eapply (achain_chain_pre ly3 _ (sp0 - 224) (g + 88) []).
- apply achain_low; clear - Hgceil; lia.
- unfold spZ; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp3; clear - Hceil Hslo HTS; lia.
- unfold s0Z; rewrite Qs0; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E32u3; apply unsigned_lit_small; clear - HZg; lia.
- unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_at trbsegs B LAWS Hsegs errno_low ML AFREE W3 (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPa g s N) ly S W mem md []
ly3 S3 _ (k + 1 + 1) nw FRAME_SIZE (-224) (Z_to_bv 64 0x86fd4) [] HJ3 HnwIn3);
[ rewrite Ra0; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E23_3
| unfold spZ; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp3; lia
| reflexivity
| clear; lia
| rewrite HTS, Has; clear; lia
| rewrite Qgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo3 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite Qtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo3 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| clear - Hnev3 Hev Hk HEVF HEVA; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite HBcode, (tl_universe B TL);
apply TRACES_cgif_addframe_U; apply memZL_In; vm_compute; reflexivity
| intros HnwOld ii Hii; exact (proj1 (HnewX _ (or_introl eq_refl)) HnwOld ii Hii) ] end. }
cbv beta. clear Ra0 Rra Qsp Qgp Qtp Qs0 CH.
intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l3 & l4 & El3 & Eab4) & Hfrs4 & HK4).
pose proof (proj1 HJ4) as HAR4. pose proof HJ4 as (_ & HLY4 & _).
rewrite HFS in HK4. change (req_size 40) with 40 in HK4.
replace (sp0 + -224 - ASTACK) with (sp0 - 224 - ASTACK) in HK4 by (clear; lia). replace (sp0 + -224) with (sp0 - 224) in HK4 by (clear; lia).
assert (HPerm4 : Permutation (ablocks B ly4 S4) (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest)).
{ rewrite Eab4. apply Permutation_sym. apply (Permutation_cons_app_inv l3 l4 (a := (nw, FRAME_SIZE))). apply Permutation_sym. rewrite <- El3. exact HPerm3. }
assert (HBl4 : forall b m, In (b, m) (ablocks B ly3 S3) -> (b, m) <> (nw, FRAME_SIZE) -> In (b, m) (ablocks B ly4 S4)).
{ intros b m Hb Hne. rewrite Eab4. rewrite El3 in Hb. apply in_app_iff in Hb. apply in_app_iff.
destruct Hb as [Hb | [Hb | Hb]]; [left; exact Hb | exfalso; exact (Hne (eq_sym Hb)) | right; exact Hb]. }
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (apply (HBl4 _ _ Hing3); intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold CGIF_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR4) as (Kcell4 & _ & Kgot4 & _). rewrite HBgot, HBcell in Kgot4. rewrite HBcell in Kcell4.
assert (EFA4 : frame_addr ly4 cid pos = frame_addr lyc cid pos).
{ unfold frame_addr. destruct HLY4 as (_ & _ & _ & _ & _ & E6 & _). destruct HLY as (_ & _ & _ & _ & _ & E6' & _). rewrite E6, <- E6'. reflexivity. }
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 Bxa af_SH23 ss) end in
jafter_call_keep HS K regs4 (mrestrict (w_H W4) mem4) HP4 [1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- eapply (region_kept_stack_aj trbsegs B); [exact HK4 | exact HJ4 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Usp3 | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- eapply (region_kept_stack_aj trbsegs B); [exact HK4 | exact HJ4 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Usp3 | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot3b) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot4) | clear; lia].
- apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell3b) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell4) | clear; lia].
- eapply (region_kept_block_aj trbsegs B); [exact HK4 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32u3 | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hc; clear - Ha Hc Dgn; lia].
- eapply (region_kept_frame_aj trbsegs B); [exact HK4 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E46_3; apply unsigned_lit_small; clear - Hcfp C1; lia
| rewrite Hfrs3, Hfrs2; exact Hfin | rewrite EFA3; clear - Hflo; lia | rewrite EFA3; clear - Hfhi; lia | clear; lia | intros a Ha Hc; clear - Ha Hc Dcn; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E4 := Ex) in HS end.
assert (OLD4 : forall n, (n < 84)%nat -> ew E4 n = ew E2 n) by (intros n Hn; subst E4; rewrite YO3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply OLD3; exact Hn).
assert (Usp4 : bv_unsigned (ew E4 2) = sp0 - 224) by (rewrite OLD4 by lia; exact Usp2).
assert (E32u4 : bv_unsigned (ew E4 32) = g) by (rewrite OLD4 by lia; exact E32u2).
assert (E32_4 : ew E4 32 = Z_to_bv 64 g) by (rewrite OLD4 by lia; exact E32_2).
assert (E38_4 : ew E4 38 = Z_to_bv 64 SB) by (rewrite OLD4 by lia; exact E38_2).
assert (E46_4 : ew E4 46 = Z_to_bv 64 cfp) by (rewrite OLD4 by lia; exact E46_2).
assert (EEo4 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 68)%nat -> ew E4 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD4 by lia; exact (EEo2 n rr Hn Hn68)).
clear SHOK. assert (SHOK : sh_ok trbsegs Bxa af_SH E4 (mrestrict (w_H W4) mem4)).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly4 S4 W4 _ _ _ g s N _ cfp 32 HJ4 HAR0 HPerm HFO) as (_ & _ & HRA4).
unfold sh_ok, af_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_block trbsegs B LAWS ly4 S4 W4 mem4 md4 E4 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR4 Hing4).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_4, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u4.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trbsegs (w_H W4) mem4 E4 Bxa 46 cfp 32 cfp 0 32 HRA4).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_4, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_4, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app. }
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RBspanA AF_RETC; [awr_a Usp4 E32u4 Hing4 HTS |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp4, ?E32u4 in Hrr; clear - Hrr; lia|]); destruct Hin)) as UN4.
cbv beta in UN4. clear HF HFr HG.
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msq) => set (msL := msq) in * end.
assert (K3s : forall a, sp0 - 104 <= a < sp0 -> mbyte trbsegs (mrestrict (w_H W4) (ms_mem msL)) a = mbyte trbsegs (mrestrict (w_H W2) mem2) a).
{ intros a Ha. pose proof HK3 as (K1 & _). pose proof HK4 as (K1' & _). apply (mbyte_of_aview trbsegs).
etransitivity; [apply UN4; clear - Ha Hceil Hslo Hshi H47 HTS C1; lia|].
etransitivity; [apply (K1' a); clear - Ha Hceil Hslo Hshi H47 HTS Has C1; lia|].
etransitivity; [apply UN3; clear - Ha Hceil Hslo Hshi H47 HTS C1 Hnceil; lia|].
etransitivity; [apply (K1 a); clear - Ha Hceil Hslo Hshi H47 HTS Has C1; lia|]. apply UN2; clear - Ha Hceil Hslo Hshi H47 HTS C1 Hnceil; lia. }
assert (K3b : forall b m ii, In (b, m) (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) -> 0 <= ii < req_size m ->
~ (sp0 - 224 <= b + ii < sp0 - 104) ->
mbyte trbsegs (mrestrict (w_H W4) (ms_mem msL)) (b + ii) = mbyte trbsegs (mrestrict (w_H W2) mem2) (b + ii)).
{ intros b m ii Hb Hii Hns. pose proof HK3 as (_ & K2 & _). pose proof HK4 as (_ & K2' & _).
pose proof (SEPw b m ltac:(right; exact Hb)) as Hnn. pose proof (SEPi b m ltac:(right; exact Hb)) as Hni.
assert (Hbc : In (b, m) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPn|]; right; right; exact Hb).
assert (Hb3 : In (b, m) (ablocks B ly3 S3)) by (apply (HBl3 _ _ Hbc); intros Hq; pose proof (f_equal fst Hq) as Hq1; cbn [fst] in Hq1; clear - Hq1 Hni Hii HN1; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbc) as (_ & Hb4096 & Hbceil & _).
apply (mbyte_of_aview trbsegs).
etransitivity; [apply UN4; [clear - Hii Hb4096 Hbceil C1 Hceil Hslo HTS; lia | exact Hns]|].
etransitivity; [apply (K2' b m ii Hb3 Hii); clear - Hnn Hii; lia|].
etransitivity; [apply UN3; [clear - Hii Hb4096 Hbceil C1 Hceil Hslo HTS; lia | clear - Hns Hnn Hii; lia]|].
etransitivity; [apply (K2 b m ii (HBin _ Hbc) Hii); clear - Hni Hii; lia|].
apply UN2; [clear - Hii Hb4096 Hbceil C1 Hceil Hslo HTS; lia | clear - Hns Hnn Hii; lia]. }
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly4 S4 W4 rg mm mdq (k + 3) s1 2 CX) end.
- split; [replace (k + 3) with (k + 1 + 1 + 1) by (clear; lia); exact HJ4|]. split; [clear - Hk0; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR2); exact K3s |].
split.
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii.
apply (K3b g CGIF_SIZE ii ltac:(left; reflexivity) ltac:(change (req_size CGIF_SIZE) with 96; clear - Hii; lia)). clear - Hii HZg; lia.
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. destruct (HZr ii Hii) as [Hb Hn].
apply (K3b (cg_raw s1) RAW_SIZE ii ltac:(right; left; reflexivity) ltac:(change (req_size RAW_SIZE) with 48; clear - Hii; lia) Hn).
- intros f Hfi. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. destruct (HZf f ii Hfi Hii) as [Hb Hn].
apply (K3b (fr_ptr f) FRAME_SIZE ii ltac:(apply in_app_iff; left; exact (af_frame_in_blocks g s1 N f Hfi)) ltac:(rewrite HFS; change (req_size 40) with 40; clear - Hii; lia) Hn). }
split; [exact HOK|]. split; [exact HPerm4 | exact Hnew].
- clear - Hk HEVF HEVA; lia.
- unfold af_regs_ret; change (spZ regs) with sp0.
split; [|split; [|split]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact E32_4 | exact E38_4 | rewrite E32u4; reflexivity
| rewrite (EEo4 2%nat 2%bv eq_refl ltac:(clear; lia)); exact Rsp | rewrite (EEo4 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite (EEo4 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
-   let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; reflexivity. }
destruct Hres as [(Habs & _ & _) | (_ & Ebl & _)]; [exfalso; clear - Habs Hr4096; lia|].
rreg HS (10%bv : bv 5) Rres. rewrite Ha0 in Rres. symmetry in Rres.
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Rres. rewrite ?ew_ewset_other in Rres by lia. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Rres.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 72%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2 ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E2r, unsigned_lit_small by lia; change (2 ^ 4) with 16; clear - Hr4096 HrHi HrCeil Hr16 C1 Hrq1; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (3 * nlp) HAR2 HrIn) as (_ & _ & _ & _ & HrP & _).
assert (Bres : bv_unsigned (ew E2 72) = res) by (rewrite E2r; apply unsigned_lit_small; lia).
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (3 * nlp) HJ HAR2 Ebl ltac:(clear - Hp3x; lia)) as Tnew.
assert (Anew : forall blc ii lyq ownq, In (res, 3 * nlp) blc -> 0 <= ii < req_size (3 * nlp) -> awr_byte TADDFRAME_STK sp0 (FPa g s N) (ablocks B ly S) blc lyq ownq (res + ii)).
{ intros blc ii lyq ownq Hbl Hii. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (3 * nlp) blc ii lyq ownq HJ HAR2 Ebl ltac:(clear - Hp3x; lia) Hbl Hii). }
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK RBspanA.
{ awr_x Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS Bnw2 Anw HnwIn2. }
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw <= a < nw + 8)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bnw2 in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2b & _ & Kgot2b & _). rewrite HBgot, HBcell in Kgot2b. rewrite HBcell in Kcell2b.
pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly2 S2 W2 _ _ _ g s N _ lpal (3 * nlp) HJ2 HAR0 HPerm (HPAL Hft))
as ((cidp & posp & Hfinp & Hcidp & Hfalp & Hflop & Hfhip) & Hpal8 & HRAp).
destruct (frames_bounds trbsegs _ LAWS _ _ _ _ _ _ _ (proj1 HJ2) Hfinp) as (Hpf4096 & Hpfceil & Hpfhigh).
destruct (al_frames _ _ LAWS _ _ _ _ _ cidp posp (proj1 HJ2) Hfinp) as (_ & _ & HiP0 & _).
assert (Dri : res + req_size (3 * nlp) <= lpal \/ lpal + 3 * nlp <= res).
{ pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ res (3 * nlp) cidp posp (proj1 HJ2) HrIn Hfinp) as D.
unfold zdisjoint in D. cbn [fst snd] in D. clear - D Hflop Hfhip. lia. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rregD HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY _ (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPa g s N) ly S W mem md []
ly2 S2 _ (k + 1) res lpal (3 * nlp) (-224) (Z_to_bv 64 0x86d04) HJ2);
[ rewrite Ra0; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E2r
| rewrite Ra1; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E47_2; unfold w64; reflexivity
| rewrite Ra2; exact (denot_3xz _ 52 nlp ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite OLD2 by (clear; lia); exact E52) ltac:(clear - Rnlp; cbn in Rnlp; lia))
| clear - Hp3x; lia | clear - Hr4096; lia | clear - HrCeil Hrq1 C1 Hrq2; lia
| unfold spZ; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp2; lia
| reflexivity
| clear; lia
| rewrite HTS; unfold ESTACK; clear; lia
| rewrite Qgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo2 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite Qtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo2 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| intros a Ha; split; [replace a with (res + (a - res)) by (clear; lia); apply Anew; [exact HrIn | clear - Ha Hrq2; lia] | unfold ESTACK; intro; clear - Ha H Hr4096 HrCeil Hrq1 Hceil Hslo HTS C1 Hrq2; lia]
| apply (amem_range_of_block trbsegs B LAWS ly2 S2 W2 _ _ res (3 * nlp) _ _ (proj1 HJ2) HrIn); clear - Hrq2; lia
| apply (range_addressable_of_block trbsegs B LAWS ly2 S2 W2 _ _ res (3 * nlp) _ _ (proj1 HJ2) HrIn); clear - Hrq2; lia
| intros Hn0; apply (shadow_hull_vis_of_block trbsegs B LAWS ly2 S2 W2 _ _ res (3 * nlp) _ _ (proj1 HJ2) HrIn); clear - Hrq2 Hn0; lia
| split; [clear - Hpf4096 Hflop; lia|]; split; [clear - Hpfceil Hfhip C1; lia|]; split;
[ intros a Ha; split; [| unfold spZ, ESTACK; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp2; intro; clear - Ha H Hpfceil Hfhip Hceil Hslo HTS C1; lia];
apply (aview_some_of_apresent trbsegs); apply (proj1 (HiP0 a ltac:(clear - Ha Hflop Hfhip; lia)))
| split; [clear - Dri Hrq2; lia|];
split; [apply amem_range_high; [clear - Hp3x; lia | destruct Hpfhigh as [_ Hfz]; unfold kLowShadowBeg, kHighMemBeg in Hfz; clear - Hfz Hflop Hfhip; lia | clear - Hpfceil Hfhip; lia]|]; split;
[ exact HRAp
| intros Hn0; apply (shadow_hull_vis_of_frame trbsegs B LAWS ly2 S2 W2 _ _ cidp posp lpal (3 * nlp) (proj1 HJ2) Hfinp); [exact Hflop | exact Hfhip | exact Hn0] ] ] ] end. }
cbv beta. clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3).
replace (sp0 + -224 - ESTACK) with (sp0 - 224 - ESTACK) in Hfr3 by (clear; lia). replace (sp0 + -224) with (sp0 - 224) in Hfr3 by (clear; lia).
assert (HES : ESTACK = 4096) by reflexivity.
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 Bxa af_SH23 ss) end in
jafter_call_keep HS K regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ3)) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | apply Forall_nil];
first
[ eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [exact Bnw2 | exact Usp2 | exact E32u2 | rewrite E46_2; apply unsigned_lit_small; clear - Hcfp C1; lia]
| intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr3;
[ clear - Ha Hn4096 Hnceil HZg Hcfp HrCeil Hrq1 Hceil Hslo Hshi H47 HTS C1; lia
| intros X;
first [ pose proof (HnewN a) as D; clear - Ha X D Hr4096 Hrq2; lia
| pose proof (HnewG a) as D; clear - Ha X D Hr4096 Hrq2; lia
| pose proof (HnewF a) as D; clear - Ha X D Hr4096 Hrq2; lia
| clear - Ha X HrCeil Hrq1 Hceil Hslo HTS C1 Hrq2; lia ]
| rewrite HES; clear - Ha Hn4096 Hnceil HZg Hcfp Hgceil Hceil Hslo Hshi H47 HTS C1; lia ]
| exact Hpres3 ]
| apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot2b) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot3) | clear; lia]
| apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell2b) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell3) | clear; lia]
| match goal with |- ?gg => idtac "KEPTFAIL" gg end ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E3 := Ex) in HS end.
assert (OLD3 : forall n, (n < 84)%nat -> ew E3 n = ew E2 n) by (intros n Hn; subst E3; rewrite YO3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0 - 224) by (rewrite OLD3 by lia; exact Usp2).
assert (E32u3 : bv_unsigned (ew E3 32) = g) by (rewrite OLD3 by lia; exact E32u2).
assert (E32_3 : ew E3 32 = Z_to_bv 64 g) by (rewrite OLD3 by lia; exact E32_2).
assert (E23_3 : ew E3 23 = Z_to_bv 64 nw) by (rewrite OLD3 by lia; exact E23_2).
assert (Bnw3 : bv_unsigned (ew E3 23) = nw) by (rewrite OLD3 by lia; exact Bnw2).
assert (E38_3 : ew E3 38 = Z_to_bv 64 SB) by (rewrite OLD3 by lia; exact E38_2).
assert (E46_3 : ew E3 46 = Z_to_bv 64 cfp) by (rewrite OLD3 by lia; exact E46_2).
assert (E47_3 : ew E3 47 = Z_to_bv 64 lpal) by (rewrite OLD3 by lia; exact E47_2).
assert (E67_3 : ew E3 67 = Z_to_bv 64 (Z.land fattr 4)) by (rewrite OLD3 by lia; exact E67_2).
assert (E49_3 : ew E3 49 = Z_to_bv 64 fattr) by (rewrite OLD3 by lia; exact E49_2).
assert (E72_3 : ew E3 72 = Z_to_bv 64 res) by (rewrite OLD3 by lia; exact E2r).
assert (Bres3 : bv_unsigned (ew E3 72) = res) by (rewrite OLD3 by lia; exact Bres).
assert (EEo3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 68)%nat -> ew E3 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD3 by lia; exact (EEo2 n rr Hn Hn68)).
clear SHOK. assert (SHOK : sh_ok trbsegs Bxa af_SH23 E3 (mrestrict (w_H W2) mem3)).
{ assert (HRA3 : range_addressable (aview trbsegs (w_H W2) mem3) SHADOW_OFF cfp 32).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly2 S2 W2 _ _ _ g s N _ cfp 32 HJ3 HAR0 HPerm HFO) as (_ & _ & HRA3). exact HRA3. }
unfold sh_ok, af_SH23, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem3 md3 E3 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE (proj1 HJ3) (HBin _ Hing)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u3.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trbsegs (w_H W2) mem3 E3 Bxa 46 cfp 32 cfp 0 32 HRA3).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem3 md3 E3 Bxa 23 nw FRAME_SIZE 0 FRAME_SIZE (proj1 HJ3) HnwIn2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bnw3.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RBspanA AF_E; [awr_x Usp3 E32u3 ltac:(exact (HBin _ Hing)) HTS Bnw3 Anw HnwIn2 |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw <= a < nw + 8)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bnw2, ?Usp3, ?E32u3, ?Bnw3 in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN4.
cbv beta in UN4. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (AGx : forall n, (n < 84)%nat -> ew EL n = ew E2 n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; apply OLD3; exact Hn).
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (nw <= a < nw + 8)) -> ~ (res <= a < res + 3 * nlp) -> ~ (sp0 - 224 - ESTACK <= a < sp0 - 224) ->
aview trbsegs (w_H W2) (ms_mem msL) a = aview trbsegs (w_H W2) mem2 a).
{ intros a Ha Hn1 Hn2 Hn3. etransitivity; [exact (UN4 a Ha Hn1)|]. etransitivity; [exact (Hfr3 a Ha Hn2 Hn3)|]. exact (UN2 a Ha Hn1). }
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
cbn [ms_mem restrict mkst] in HR0, HRn end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32_2).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u2).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38_2).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46_2).
assert (X47 : ew EL 47 = Z_to_bv 64 lpal) by (rewrite AGx by lia; exact E47_2).
assert (X67 : ew EL 67 = Z_to_bv 64 (Z.land fattr 4)) by (rewrite AGx by lia; exact E67_2).
assert (X48 : ew EL 48 = Z_to_bv 64 img) by (rewrite AGx by lia; exact E48_2).
assert (X49 : ew EL 49 = Z_to_bv 64 fattr) by (rewrite AGx by lia; exact E49_2).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23_2).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw2).
assert (X72 : ew EL 72 = Z_to_bv 64 res) by (rewrite AGx by lia; exact E2r).
assert (X72u : bv_unsigned (ew EL 72) = res) by (rewrite AGx by lia; exact Bres).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp2).
assert (HX1 : (if Z.land fattr 1 =? 0 then [] else [(res, 3 * nlp)]) = [(res, 3 * nlp)] /\ (if Z.land fattr 1 =? 0 then lpal else res) = res).
{ destruct (Z.land fattr 1 =? 0) eqn:Hb; [exfalso; apply Hft; apply Z.eqb_eq; exact Hb | split; reflexivity]. }
destruct HX1 as [HX1 HX2].
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly2 S2 W2 rg mm mdq (k + 1) s1 i nw nimg res CX) end.
+
split; [exact HJ3|]. split; [clear - Hk0; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR2); intros a Ha; apply (mbyte_of_aview trbsegs); apply K23;
[clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hceil Hslo HTS C1; lia | clear - Ha HrCeil Hrq1 Hceil Hslo HTS C1 Hrq2; lia | rewrite HES; clear - Ha; lia] |].
split.
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview trbsegs). apply K23;
[clear - Hii HZg; lia | clear - Hii HZg Dgn; lia | pose proof (HnewG (g + ii)) as D; clear - Hii D Hr4096 Hrq2; lia | rewrite HES; clear - Hii Hgceil Hceil Hslo HTS C1; lia].
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (_ & _ & Hrc & _). change (req_size RAW_SIZE) with 48 in Hrc.
pose proof (SEPn _ _ ii Hinr ltac:(change (req_size RAW_SIZE) with 48; clear - Hii; lia)) as D.
pose proof (SEPw _ _ ltac:(right; right; left; reflexivity)) as Dw. change (req_size RAW_SIZE) with 48 in Dw.
apply K23; [exact Hb | clear - Hn Dw Hii; lia | clear - D Hr4096 Hrq2; lia | rewrite HES; clear - Hii Hrc Hceil Hslo HTS C1; lia].
- intros f Hfi. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZf f ii Hfi Hii) as [Hb Hn].
assert (Hfb' : In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s1 N)) by exact (af_frame_in_blocks g s1 N f Hfi).
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; exact Hfb').
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfb) as (_ & _ & Hfc & _). rewrite HFS in Hfc. change (req_size 40) with 40 in Hfc.
pose proof (SEPn _ _ ii Hfb ltac:(rewrite HFS; change (req_size 40) with 40; clear - Hii; lia)) as D.
pose proof (SEPw _ _ ltac:(right; apply in_app_iff; left; exact Hfb')) as Dw. rewrite HFS in Dw. change (req_size 40) with 40 in Dw.
apply K23; [exact Hb | clear - Hn Dw Hii; lia | clear - D Hr4096 Hrq2; lia | rewrite HES; clear - Hii Hfc Hceil Hslo HTS C1; lia]. }
split; [exact HOK|]. split.
{ unfold af_newblocks. rewrite HX1, Ebl.
eapply Permutation_trans; [apply Permutation_app; [exact HPerm1 | apply Permutation_refl]|].
rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
apply perm_skip. apply perm_skip. apply Permutation_sym. apply (Permutation_cons_append (af_cblocks img N fattr lpa nlp rest) (res, 3 * nlp)). }
split; [exact Hnew|]. unfold af_newblocks. rewrite HX1.
intros b [<- | [<- | [<- | []]]]; [exact (HnewX _ (or_introl eq_refl)) | exact (HnewX _ (or_intror (or_introl eq_refl))) |].
split; [exact Tnew | intros blc lyq ownq ii Hbl Hii; exact (Anew blc ii lyq ownq Hbl Hii)].
+ clear - Hk HEVF; lia.
+
unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; regvD HS AGx EEo2 X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1.
+   let R := fresh "R" in rreg HS (9%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
+   let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (AGx 24%nat ltac:(clear; lia)), (EEo2 24%nat 24%bv eq_refl ltac:(clear; lia)); exact R24i.
+   let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
+   let R := fresh "R" in rreg HS (17%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
+   let R := fresh "R" in rreg HS (19%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
+   let R := fresh "R" in rreg HS (25%bv : bv 5) R; rewrite R; unfold w64; apply (shq_word EL 46 38 16 _ SB X46 X38); clear - Hcfp C1; unfold SB; lia.
+   change (spZ regs) with sp0.
assert (Ra4 : 0 <= Z.land fattr 4 < 2 ^ (8 * Z.of_N 8)) by (pose proof (land_small_r fattr 4 ltac:(clear - Rfattr; cbn in Rfattr; lia) ltac:(clear; lia)) as Xl; cbn in Xl; cbn; clear - Xl; lia).
af_locsD_tac HR0 Xsp X32 X38 X46 X67 X23 HZg Hgceil Hcfp Hn4096 Hnceil C1 Ra4.
+ clear - Hft; left; exact Hft.
+ exact Hi.
+ exact Hnone.
+ exact Hs1.
+ exact HnwIn2.
+
rewrite HX2.
lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 0 8 (SOff 72 0) res HRn X23u ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite X72, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hr4096 HrCeil Hrq1 C1 Hrq2; lia) ltac:(cbn; lia)) as V0 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0. rewrite Z.add_0_r in V0.
apply (af_newcfg_kept0 _ _ nw lpal res fattr fgen delay nlp tidx HNC2); [| exact V0].
intros a Ha. apply (mbyte_of_aview trbsegs). apply K23;
[clear - Ha Hn4096 Hnceil C1; lia | clear - Ha Hnceil Hceil Hslo HTS C1; lia | pose proof (HnewN a) as D; clear - Ha D Hr4096 Hrq2; lia | rewrite HES; clear - Ha Hnceil Hceil Hslo HTS C1; lia].
+
apply (val_mem_keptZ _ _ _ 8%nat nimg HV8_2). intros x Hx. cbn in Hx. apply (mbyte_of_aview trbsegs). apply K23;
[clear - Hx Hn4096 Hnceil C1; lia | clear - Hx Hnceil Hceil Hslo HTS C1; lia | pose proof (HnewN x) as D; clear - Hx D Hr4096 Hrq2; lia | rewrite HES; clear - Hx Hnceil Hceil Hslo HTS C1; lia].
Qed.
End e.
End d.
