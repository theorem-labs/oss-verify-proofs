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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCe9 YCfs YCfu YCdr YCe1 YCfq YCe4 YCe0 YCgv YCdq YCdu YCdf YCds YCdt YCdn YCdp.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma U_zext_small : forall E w a v, U E a = v -> 0 <= v < 2 ^ Z.of_N w -> Z.of_N w <= 64 -> U E (SExt false w a) = v.
Proof.
intros E w a v Ha Hv Hw. rewrite U_SExt, Ha. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64.
split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hv)|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma U_mul_smallD : forall E a b, U E a * U E b < 2 ^ 64 -> U E (SMd M_MUL a b) = U E a * U E b.
Proof.
intros E a b H. rewrite U_SMd. cbn [zmd_raw]. pose proof (U_range E a). pose proof (U_range E b).
apply zcanon_id. unfold M64. split; [apply Z.mul_nonneg_nonneg; lia | exact H].
Qed.
Lemma U_add0 : forall E x, U E (SAlu ALU_ADD x (SLit 0)) = U E x.
Proof.
intros E x. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.
Lemma land_mod2p : forall x m k, 0 <= x -> 0 <= m < 2 ^ k -> 0 <= k -> Z.land (x mod 2 ^ k) m = Z.land x m.
Proof.
intros x m k Hx Hm Hk. rewrite <- (Z.land_ones x k) by lia. rewrite <- Z.land_assoc. f_equal.
rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Ltac awr_n_rec Usp E32u Hing HTS Bres Anew HrIn :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YQ0b.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |]
| |- awr_ok _ (YQ0b.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32u | exact Hing | cbn [YQ0b.r_wlo]; lia
| cbn [YQ0b.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; unfold FPa, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| ]
| |- awr_ok _ (YQ0b.mkRegion (Some 72%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
lazymatch type of Bres with _ = ?res =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 72%nat res);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact Bres
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; replace a with (res + (a - res)) by lia; apply Anew; [exact HrIn | change (req_size 40) with 40; lia]
| ] end
end
| fail 1 "awr_n: no rule for the head region" ];
awr_n_rec Usp E32u Hing HTS Bres Anew HrIn
end.
Ltac awr_n Usp E32u Hing HTS Bres Anew HrIn :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_n_rec Usp E32u Hing HTS Bres Anew HrIn.
Ltac rregD HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (Hr : getr rg r = sv_denot E e) by (exact (st_ok_restrict_reg segs H E ss ms r HS)) end.
Ltac regvD HS AGx EEo2 X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1 :=
lazymatch goal with |- getr _ ?r = _ =>
let Q := fresh "Q" in rreg HS r Q; rewrite Q; clear Q;
lazymatch goal with
| |- alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (bv_unsigned (ew ?Ex ?n) + ?c)) (Z_to_bv 64 3)) (ew _ 38) = _ =>
unfold w64; apply (shq_word Ex n 38 c _ SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia
| |- context [alu64] => idtac "REGVD-ALU" r; fail
| |- _ =>
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo2 2%nat 2%bv eq_refl ltac:(clear; lia)); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo2 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo2 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| idtac "REGVD-FAIL" r; fail ]
end end.
Section h. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition regsD : list sv := regsFL.
Definition af_SH72 : list shent := af_SH ++ [mkSHE 72 0 FRAME_SIZE].
Section j.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma af_D1 : AF_RETC_stmt B -> AF_D2_stmt B -> AF_D_stmt B.
Proof.
intros PRC PD2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 i
CX MID Hk HBB HR R21 R22 R9 R24i HL HnoTab Hi Hnone Hs1.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew).
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
pose proof HR as (Rsp & Rgp & Rtp & R18 & R8 & R27 & R26 & R19 & R25s).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
assert (HEVF : EV_FLUSH = 35) by reflexivity. assert (HEVA : EV_ADDFRAME = 12 + EV_FLUSH) by reflexivity.
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
clear Hfin Hcid0 Hfal Hflo Hfhi Hf4096 Hfceil Hfhigh Hfhigh_img Hcal HRA cid pos.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
destruct (af_reseed B TL LAWS AF_D regsD 0 0 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 []
CX MID Rsp HL ltac:(clear; lia) ltac:(clear; lia)
(regsFL_ok B regs regs1 g s1 cfp _ _ HR R21 R22 R9 ltac:(lia) Hgceil ltac:(lia) (proj2 Hcfp)) ltac:(vm_compute; reflexivity)) as [HS SHOK].
set (E := Ereg regs1 _) in HS, SHOK.
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
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspanA.
{ awr_a Usp E32u Hing HTS. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp. rreg HS (8%bv : bv 5) Qs0.
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
assert (HliveC : blocks_bytes Sc + 40 <= LIVE_MAX) by (clear - HBB Hlive; unfold LIVE_ADDFRAME in Hlive; lia).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_at trbsegs B LAWS Hsegs errno_low ML AMALLOC Wc (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPa g s N) ly S W mem md []
lyc Sc _ k 40 (-224) (Z_to_bv 64 0x86a78) [] HJ);
[ rewrite Ra0; reflexivity
| unfold MALLOC_MAX; clear; lia
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
pose proof (proj1 HJ2) as HAR2.
destruct (mres_kept B lyc Sc Wc _ W2 mem2 ly2 S2 _ _ res 40 Hres) as (HK & HBin & HresIn).
pose proof (mres_range B LAWS ly2 S2 W2 mem2 md2 lyc Sc res 40 _ _ HAR2 Hres) as Hrng. change (req_size 40) with 40 in Hrng, HK.
pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & _ & _).
assert (HnewG : forall a, g + 0 <= a < g + 96 -> ~ (res <> 0 /\ res <= a < res + 40)).
{ intros a Ha [Hnz Hin]. destruct Hres as [(Habs & _) | (_ & Ebl & _)]; [exact (Hnz Habs)|].
pose proof (Permutation_app HPerm1 (Permutation_refl [(res, 40)])) as P2. rewrite <- Ebl in P2. unfold cgif_blocks in P2. cbn [app] in P2.
pose proof (sep_hd_in B LAWS ly2 S2 W2 mem2 md2 _ (res, 40) _ HAR2 P2 ltac:(right; apply in_or_app; right; left; reflexivity)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size 40) with 40 in D. clear - D Ha Hin. lia. }
assert (HnewF : forall a, cfp + 0 <= a < cfp + 32 -> ~ (res <> 0 /\ res <= a < res + 40)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ res 40 cid pos HAR2 (HresIn Hnz) ltac:(rewrite Hfrs2; exact Hfin)) as D.
pose proof HJ2 as (_ & Hly2' & _). assert (EFA2 : frame_addr ly2 cid pos = frame_addr lyc cid pos).
{ unfold frame_addr. destruct Hly2' as (_ & _ & _ & _ & _ & E6 & _). destruct HLY as (_ & _ & _ & _ & _ & E6' & _). rewrite E6, <- E6'. reflexivity. }
rewrite EFA2 in D. unfold zdisjoint in D. cbn [fst snd] in D. change (req_size 40) with 40 in D. clear - D Ha Hin Hflo Hfhi. lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
jafter_call_keep HS 68%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- eapply (region_kept_stack_aj trbsegs B); [exact HK | exact HJ2 | exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- eapply (region_kept_stack_aj trbsegs B); [exact HK | exact HJ2 | exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- apply (region_kept_val trbsegs E _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot1) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgot2) | clear; lia].
- apply (region_kept_val trbsegs E _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell1) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcell2) | clear; lia].
- eapply (region_kept_block_aj trbsegs B); [exact HK | exact E32u | exact Hing | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia | exact HnewG].
- eapply (region_kept_frame_aj trbsegs B); [exact HK | rewrite E46; apply unsigned_lit_small; clear - Hcfp C1; lia | exact Hfin | clear - Hflo; lia | clear - Hfhi; lia | clear; lia | exact HnewF]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 68 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (OLD2 : forall n, (n < 68)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YO3v.ew_havoc_old; exact Hn).
assert (E2r : ew E2 72 = Z_to_bv 64 res) by (rewrite HE2; change 72%nat with (68 + 4)%nat; rewrite (YO3v.ew_havoc_new E 68 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Ha0).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = sp0 - 224) by (rewrite OLD2 by lia; exact Usp).
assert (E32u2 : bv_unsigned (ew E2 32) = g) by (rewrite OLD2 by lia; exact E32u).
assert (E32_2 : ew E2 32 = Z_to_bv 64 g) by (rewrite OLD2 by lia; exact E32).
assert (E37_2 : ew E2 37 = Z_to_bv 64 (cg_cur s1)) by (rewrite OLD2 by lia; exact E37).
assert (E38_2 : ew E2 38 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E38).
assert (E42_2 : ew E2 42 = Z_to_bv 64 (cg_W s1)) by (rewrite OLD2 by lia; exact E42).
assert (E43_2 : ew E2 43 = Z_to_bv 64 (cg_H s1)) by (rewrite OLD2 by lia; exact E43).
assert (E46_2 : ew E2 46 = Z_to_bv 64 cfp) by (rewrite OLD2 by lia; exact E46).
assert (E47_2 : ew E2 47 = Z_to_bv 64 lpal) by (rewrite OLD2 by lia; exact E47).
assert (E48_2 : ew E2 48 = Z_to_bv 64 img) by (rewrite OLD2 by lia; exact E48).
assert (E49_2 : ew E2 49 = Z_to_bv 64 fattr) by (rewrite OLD2 by lia; exact E49).
assert (E50_2 : ew E2 50 = Z_to_bv 64 fgen) by (rewrite OLD2 by lia; exact E50).
assert (E51_2 : ew E2 51 = Z_to_bv 64 delay) by (rewrite OLD2 by lia; exact E51).
assert (E52_2 : ew E2 52 = Z_to_bv 64 nlp) by (rewrite OLD2 by lia; exact E52).
assert (E53_2 : ew E2 53 = Z_to_bv 64 tidx) by (rewrite OLD2 by lia; exact E53).
assert (E67_2 : ew E2 67 = Z_to_bv 64 (Z.land fattr 4)) by (rewrite OLD2 by lia; exact E67).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 68)%nat -> ew E2 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD2 by exact Hn68; exact (EEo n rr Hn)).
assert (SEPn : forall b m ii, In (b, m) (ablocks B lyc Sc) -> 0 <= ii < req_size m -> ~ (res <> 0 /\ res <= b + ii < res + 40)).
{ intros b m ii Hb Hii [Hnz Hin]. destruct Hres as [(Habs & _) | (_ & Ebl & _)]; [exact (Hnz Habs)|].
pose proof (sep_tmp_entry B LAWS ly2 S2 W2 mem2 md2 (ablocks B lyc Sc) res 40 b m HAR2 ltac:(rewrite Ebl; apply Permutation_refl) Hb) as D.
change (req_size 40) with 40 in D. clear - D Hii Hin. lia. }
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
pose proof (obj_at_nth trbsegs _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT2) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
destruct Hrng as [Hres0 | (Hr4096 & HrHi & HrCeil & Hr16 & HrIn)].
{
clear SHOK. assert (SHOK : sh_ok trbsegs Bxa af_SH E2 (mrestrict (w_H W2) mem2)).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly2 S2 W2 _ _ _ g s N _ cfp 32 HJ2 HAR0 HPerm HFO) as (_ & _ & HRA2).
unfold sh_ok, af_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 (HBin _ Hing)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u2.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trbsegs (w_H W2) mem2 E2 Bxa 46 cfp 32 cfp 0 32 HRA2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app. }
pose proof (st_ok_pin_reg' trbsegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0, Hres0; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspanA AF_RETC; [awr_a Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?E32u2 in Hrr; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly2 S2 W2 rg mm mdq (k + 1) s1 2 CX) end.
- split; [exact HJ2|]. split; [clear - Hk0; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR2); intros a Ha; apply (mbyte_of_aview trbsegs); apply UN2; clear - Ha Hceil Hslo Hshi H47 HTS C1; lia |].
split.
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview trbsegs). apply UN2; clear - Hii HZg; lia.
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hn]. exact (UN2 _ Hb Hn).
- intros f Hfi. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZf f ii Hfi Hii) as [Hb Hn]. exact (UN2 _ Hb Hn). }
split; [exact HOK|]. destruct Hres as [(_ & Ebl & _) | (Habs & _)]; [| exfalso; clear - Habs Hres0; lia].
rewrite Ebl. split; [exact HPerm1 | exact Hnew].
- clear - Hk HEVF HEVA; lia.
- unfold af_regs_ret; change (spZ regs) with sp0.
split; [|split; [|split]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact E32_2 | exact E38_2 | rewrite E32u2; reflexivity
| rewrite (EEo2 2%nat 2%bv eq_refl ltac:(clear; lia)); exact Rsp | rewrite (EEo2 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite (EEo2 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
-   let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; reflexivity. }
destruct Hres as [(Habs & _ & _) | (_ & Ebl & _)]; [exfalso; clear - Habs Hr4096; lia|].
rreg HS (10%bv : bv 5) Rres. rewrite Ha0 in Rres. symmetry in Rres.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ nx hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Rres, unsigned_lit_small by lia;
change (2 ^ 4) with 16; clear - Hr4096 HrHi HrCeil Hr16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 40 HAR2 HrIn) as (_ & _ & _ & _ & HrP & _). change (req_size 40) with 40 in HrP.
assert (Bres : bv_unsigned (ew E2 72) = res) by (rewrite E2r; apply unsigned_lit_small; lia).
assert (Dgn : g + 96 <= res \/ res + 40 <= g).
{ pose proof (sep_tmp_entry B LAWS ly2 S2 W2 mem2 md2 (ablocks B lyc Sc) res 40 g CGIF_SIZE HAR2 ltac:(rewrite Ebl; apply Permutation_refl) Hing) as D.
change (req_size CGIF_SIZE) with 96 in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcn : cfp + 32 <= res \/ res + 40 <= cfp).
{ pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ res 40 cid pos HAR2 HrIn ltac:(rewrite Hfrs2; exact Hfin)) as D.
pose proof HJ2 as (_ & Hly2' & _). assert (EFA2 : frame_addr ly2 cid pos = frame_addr lyc cid pos).
{ unfold frame_addr. destruct Hly2' as (_ & _ & _ & _ & _ & E6 & _). destruct HLY as (_ & _ & _ & _ & _ & E6' & _). rewrite E6, <- E6'. reflexivity. }
rewrite EFA2 in D. unfold zdisjoint in D. cbn [fst snd] in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 72%nat) 0 40 0 40 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Bres; split; [clear - Hr4096 HrCeil C1; lia|]; split; [clear - Hr4096 HrCeil C1; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HrP (res + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Bres, Usp2, E32u2, E46_2, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgn Dcn Hr4096 HrHi HrCeil Hcfp HZg Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
clear SHOK. assert (SHOK : sh_ok trbsegs Bxa af_SH72 E2 (mrestrict (w_H W2) mem2)).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly2 S2 W2 _ _ _ g s N _ cfp 32 HJ2 HAR0 HPerm HFO) as (_ & _ & HRA2).
unfold sh_ok, af_SH72, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 (HBin _ Hing)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u2.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trbsegs (w_H W2) mem2 E2 Bxa 46 cfp 32 cfp 0 32 HRA2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 72 res 40 0 FRAME_SIZE HAR2 HrIn).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bres.
+ lia.
+ change (req_size 40) with 40. unfold FRAME_SIZE. lia. }
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res 40 HJ HAR2 Ebl ltac:(clear; lia)) as Tnew.
assert (Anew : forall blc ii lyq ownq, In (res, 40) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPa g s N) (ablocks B ly S) blc lyq ownq (res + ii)).
{ intros blc ii lyq ownq Hbl Hii. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res 40 blc ii lyq ownq HJ HAR2 Ebl ltac:(clear; lia) Hbl Hii). }
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK RBspanA.
{ awr_n Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS Bres Anew HrIn. }
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (res <= a < res + 40)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bres in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
pose proof (obj_at_nth trbsegs _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr0]. cbn [snd] in Rfattr0.
srr_branch_tok trbtbl_lib_ok HS SHOK RBspanA.
-
lazymatch goal with H : branch_taken _ _ _ = true |- _ => rename H into Hq6 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq6 by (clear; lia). apply (proj1 (Z.eqb_eq _ _)) in Hq6.
lazymatch type of Hq6 with Z.land (U ?Ex (SExt false 8 (SOff 49 0))) 6 = _ =>
rewrite (U_zext Ex 8 (SOff 49 0)), (U_atom Ex 49 fattr ltac:(rewrite ?ew_ewset_other by lia; exact E49_2) ltac:(clear - Rfattr0; cbn in Rfattr0; lia)) in Hq6;
change (Z.of_N 8) with 8 in Hq6; rewrite (land_mod2p fattr 6 8 ltac:(clear - Rfattr0; lia) ltac:(clear; cbn; lia) ltac:(clear; lia)) in Hq6 end.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspanA AF_D2; [awr_n Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS Bres Anew HrIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (res <= a < res + 40)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bres in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (res <= a < res + 40)) -> aview trbsegs (w_H W2) (ms_mem msL) a = aview trbsegs (w_H W2) mem2 a)
by (intros a Ha Hn; etransitivity; [exact (UN3 a Ha Hn) | exact (UN2 a Ha Hn)]).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
cbn [ms_mem restrict mkst] in HR0, HRn end.
assert (AGx : forall n, (n < 84)%nat -> ew EL n = ew E2 n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32_2).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u2).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38_2).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46_2).
assert (X47 : ew EL 47 = Z_to_bv 64 lpal) by (rewrite AGx by lia; exact E47_2).
assert (X48 : ew EL 48 = Z_to_bv 64 img) by (rewrite AGx by lia; exact E48_2).
assert (X49 : ew EL 49 = Z_to_bv 64 fattr) by (rewrite AGx by lia; exact E49_2).
assert (X67 : ew EL 67 = Z_to_bv 64 (Z.land fattr 4)) by (rewrite AGx by lia; exact E67_2).
assert (X72 : ew EL 72 = Z_to_bv 64 res) by (rewrite AGx by lia; exact E2r).
assert (X72u : bv_unsigned (ew EL 72) = res) by (rewrite AGx by lia; exact Bres).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp2).
pose proof (obj_at_nth trbsegs _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. pose proof (obj_at_nth trbsegs _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr].
pose proof (obj_at_nth trbsegs _ _ _ _ 1 (8, 8%N) img HCF eq_refl eq_refl) as [_ Rimg].
pose proof (obj_at_nth trbsegs _ _ _ _ 3 (20, 4%N) fgen HCF eq_refl eq_refl) as [_ Rfgen]. pose proof (obj_at_nth trbsegs _ _ _ _ 4 (24, 2%N) delay HCF eq_refl eq_refl) as [_ Rdelay].
pose proof (obj_at_nth trbsegs _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rnlp]. pose proof (obj_at_nth trbsegs _ _ _ _ 6 (28, 1%N) tidx HCF eq_refl eq_refl) as [_ Rtidx].
pose proof (obj_at_nth trbsegs _ _ _ _ 7 (48, 2%N) (cg_W s1) (proj1 HT1) eq_refl eq_refl) as [_ RW]. pose proof (obj_at_nth trbsegs _ _ _ _ 8 (50, 2%N) (cg_H s1) (proj1 HT1) eq_refl eq_refl) as [_ RH].
cbn [snd] in Rlpal, Rfattr, Rimg, Rfgen, Rdelay, Rnlp, Rtidx, RW, RH.
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PD2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly2 S2 W2 rg mm mdq (k + 1) s1 i res CX) end.
+
split; [exact HJ2|]. split; [clear - Hk0; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR2); intros a Ha; apply (mbyte_of_aview trbsegs); apply K23; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha HrCeil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview trbsegs). apply K23; [clear - Hii HZg; lia | clear - Hii HZg Dgn; lia].
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hn]. apply K23; [exact Hb|].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (SEPn _ _ ii Hinr ltac:(change (req_size RAW_SIZE) with 48; clear - Hii; lia)) as D. clear - Hn D Hr4096. lia.
- intros f Hfi. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZf f ii Hfi Hii) as [Hb Hn]. apply K23; [exact Hb|].
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. left. exact (af_frame_in_blocks g s1 N f Hfi). }
pose proof (SEPn _ _ ii Hfb ltac:(change (req_size FRAME_SIZE) with 40; clear - Hii; lia)) as D. clear - Hn D Hr4096. lia. }
split; [exact HOK|]. split.
{ rewrite Ebl. eapply Permutation_trans; [apply Permutation_app; [exact HPerm1 | apply Permutation_refl]|]. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
split; [exact Hnew|]. intros b [<- | []]. split; [exact Tnew | intros blc lyq ownq ii Hbl Hii; exact (Anew blc ii lyq ownq Hbl Hii)].
+ clear - Hk HEVF; lia.
+ rewrite (blocks_bytes_bsum B ly2 S2), Ebl, bsum_app, <- (blocks_bytes_bsum B lyc Sc). cbn [bsum fold_right snd]. unfold FRAME_SIZE. clear - HBB. lia.
+
unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; regvD HS AGx EEo2 X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1.
+   let R := fresh "R" in rreg HS (9%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
+   let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (AGx 24%nat ltac:(clear; lia)), (EEo2 24%nat 24%bv eq_refl ltac:(clear; lia)); exact R24i.
+   let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X72.
+
assert (UH : U EL (SExt false 16 (SOff 43 0)) = cg_H s1) by (apply (U_zext_small EL 16 _ _ (U_atom EL 43 _ ltac:(rewrite AGx by (clear; lia); exact E43_2) ltac:(clear - RH; lia))); [clear - RH; cbn in RH |- *; lia | cbn; clear; lia]).
assert (UW : U EL (SExt false 16 (SOff 42 0)) = cg_W s1) by (apply (U_zext_small EL 16 _ _ (U_atom EL 42 _ ltac:(rewrite AGx by (clear; lia); exact E42_2) ltac:(clear - RW; lia))); [clear - RW; cbn in RW |- *; lia | cbn; clear; lia]).
let R := fresh "R" in rregD HS (10%bv : bv 5) R; rewrite R; rewrite denot_lit_U; unfold w64; f_equal.
rewrite U_mul_smallD by (rewrite UH, UW; clear - RW RH; nia). rewrite UH, UW. clear - HWF1. destruct HWF1 as (_ & _ & _ & HN & _). lia.
+   let R := fresh "R" in rreg HS (19%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
+   let R := fresh "R" in rreg HS (25%bv : bv 5) R; rewrite R; unfold w64; apply (shq_word EL 46 38 16 _ SB X46 X38); clear - Hcfp C1; unfold SB; lia.
+   let R := fresh "R" in rreg HS (27%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
+
change (spZ regs) with sp0.
assert (Ra4 : 0 <= Z.land fattr 4 < 2 ^ (8 * Z.of_N 8)) by (pose proof (land_small_r fattr 4 ltac:(clear - Rfattr; cbn in Rfattr; lia) ltac:(clear; lia)) as Xl; cbn in Xl; cbn; clear - Xl; lia).
af_locsD_tac HR0 Xsp X32 X38 X46 X67 X72 HZg Hgceil Hcfp Hr4096 HrCeil C1 Ra4.
+ exact HnoTab.
+ exact Hi.
+ exact Hnone.
+ exact Hs1.
+ exact HrIn.
+
pose proof (U_sext32_low EL 49 fattr ltac:(rewrite AGx by (clear; lia); exact E49_2) ltac:(clear - Rfattr; lia)) as Q49. unfold U in Q49.
pose proof (U_sext32_low EL 50 fgen ltac:(rewrite AGx by (clear; lia); exact E50_2) ltac:(clear - Rfgen; lia)) as Q50. unfold U in Q50.
pose proof (U_zext_small EL 16 _ _ (U_atom EL 51 _ ltac:(rewrite AGx by (clear; lia); exact E51_2) ltac:(clear - Rdelay; lia)) ltac:(clear - Rdelay; cbn in Rdelay |- *; lia) ltac:(cbn; clear; lia)) as Q51. unfold U in Q51.
pose proof (U_zext_small EL 16 _ _ (U_atom EL 52 _ ltac:(rewrite AGx by (clear; lia); exact E52_2) ltac:(clear - Rnlp; lia)) ltac:(clear - Rnlp; cbn in Rnlp |- *; lia) ltac:(cbn; clear; lia)) as Q52. unfold U in Q52.
lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 72%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 72 res cs lo hi wlo whi 0 8 (SOff 47 0) lpal HRn X72u ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite X47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rlpal; lia) ltac:(cbn; lia)) as V0;
pose proof (field_of_region_any Ex _ 72 res cs lo hi wlo whi 16 4 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V16;
pose proof (field_of_region_any Ex _ 72 res cs lo hi wlo whi 20 4 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V20;
pose proof (field_of_region_any Ex _ 72 res cs lo hi wlo whi 24 2 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V24;
pose proof (field_of_region_any Ex _ 72 res cs lo hi wlo whi 26 2 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V26 end.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V16, V20. change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16) in V24, V26.
rewrite Q49 in V16. rewrite Q50 in V20. rewrite Q51, Z.mod_small in V24 by (clear - Rdelay; lia). rewrite Q52, Z.mod_small in V26 by (clear - Rnlp; lia).
rewrite Z.add_0_r in V0. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0, V16, V20, V24, V26.
split; [exact V0|]. split; [exact V16|]. split; [exact V20|]. split; [exact V24|]. split; [exact V26|].
intros Hne; exfalso; apply Hne; exact Hq6.
-
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hq6 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq6 by (clear; lia). apply (proj1 (Z.eqb_neq _ _)) in Hq6.
lazymatch type of Hq6 with Z.land (U ?Ex (SExt false 8 (SOff 49 0))) 6 <> _ =>
rewrite (U_zext Ex 8 (SOff 49 0)), (U_atom Ex 49 fattr ltac:(rewrite ?ew_ewset_other by lia; exact E49_2) ltac:(clear - Rfattr0; cbn in Rfattr0; lia)) in Hq6;
change (Z.of_N 8) with 8 in Hq6; rewrite (land_mod2p fattr 6 8 ltac:(clear - Rfattr0; lia) ltac:(clear; cbn; lia) ltac:(clear; lia)) in Hq6 end.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspanA AF_D2; [awr_n Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS Bres Anew HrIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (res <= a < res + 40)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bres in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (res <= a < res + 40)) -> aview trbsegs (w_H W2) (ms_mem msL) a = aview trbsegs (w_H W2) mem2 a)
by (intros a Ha Hn; etransitivity; [exact (UN3 a Ha Hn) | exact (UN2 a Ha Hn)]).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
cbn [ms_mem restrict mkst] in HR0, HRn end.
assert (AGx : forall n, (n < 84)%nat -> ew EL n = ew E2 n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32_2).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u2).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38_2).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46_2).
assert (X47 : ew EL 47 = Z_to_bv 64 lpal) by (rewrite AGx by lia; exact E47_2).
assert (X48 : ew EL 48 = Z_to_bv 64 img) by (rewrite AGx by lia; exact E48_2).
assert (X49 : ew EL 49 = Z_to_bv 64 fattr) by (rewrite AGx by lia; exact E49_2).
assert (X67 : ew EL 67 = Z_to_bv 64 (Z.land fattr 4)) by (rewrite AGx by lia; exact E67_2).
assert (X72 : ew EL 72 = Z_to_bv 64 res) by (rewrite AGx by lia; exact E2r).
assert (X72u : bv_unsigned (ew EL 72) = res) by (rewrite AGx by lia; exact Bres).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp2).
pose proof (obj_at_nth trbsegs _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. pose proof (obj_at_nth trbsegs _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr].
pose proof (obj_at_nth trbsegs _ _ _ _ 1 (8, 8%N) img HCF eq_refl eq_refl) as [_ Rimg].
pose proof (obj_at_nth trbsegs _ _ _ _ 3 (20, 4%N) fgen HCF eq_refl eq_refl) as [_ Rfgen]. pose proof (obj_at_nth trbsegs _ _ _ _ 4 (24, 2%N) delay HCF eq_refl eq_refl) as [_ Rdelay].
pose proof (obj_at_nth trbsegs _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rnlp]. pose proof (obj_at_nth trbsegs _ _ _ _ 6 (28, 1%N) tidx HCF eq_refl eq_refl) as [_ Rtidx].
pose proof (obj_at_nth trbsegs _ _ _ _ 7 (48, 2%N) (cg_W s1) (proj1 HT1) eq_refl eq_refl) as [_ RW]. pose proof (obj_at_nth trbsegs _ _ _ _ 8 (50, 2%N) (cg_H s1) (proj1 HT1) eq_refl eq_refl) as [_ RH].
cbn [snd] in Rlpal, Rfattr, Rimg, Rfgen, Rdelay, Rnlp, Rtidx, RW, RH.
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PD2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly2 S2 W2 rg mm mdq (k + 1) s1 i res CX) end.
+
split; [exact HJ2|]. split; [clear - Hk0; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR2); intros a Ha; apply (mbyte_of_aview trbsegs); apply K23; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha HrCeil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview trbsegs). apply K23; [clear - Hii HZg; lia | clear - Hii HZg Dgn; lia].
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hn]. apply K23; [exact Hb|].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (SEPn _ _ ii Hinr ltac:(change (req_size RAW_SIZE) with 48; clear - Hii; lia)) as D. clear - Hn D Hr4096. lia.
- intros f Hfi. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZf f ii Hfi Hii) as [Hb Hn]. apply K23; [exact Hb|].
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. left. exact (af_frame_in_blocks g s1 N f Hfi). }
pose proof (SEPn _ _ ii Hfb ltac:(change (req_size FRAME_SIZE) with 40; clear - Hii; lia)) as D. clear - Hn D Hr4096. lia. }
split; [exact HOK|]. split.
{ rewrite Ebl. eapply Permutation_trans; [apply Permutation_app; [exact HPerm1 | apply Permutation_refl]|]. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
split; [exact Hnew|]. intros b [<- | []]. split; [exact Tnew | intros blc lyq ownq ii Hbl Hii; exact (Anew blc ii lyq ownq Hbl Hii)].
+ clear - Hk HEVF; lia.
+ rewrite (blocks_bytes_bsum B ly2 S2), Ebl, bsum_app, <- (blocks_bytes_bsum B lyc Sc). cbn [bsum fold_right snd]. unfold FRAME_SIZE. clear - HBB. lia.
+
unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; regvD HS AGx EEo2 X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1.
+   let R := fresh "R" in rreg HS (9%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
+   let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (AGx 24%nat ltac:(clear; lia)), (EEo2 24%nat 24%bv eq_refl ltac:(clear; lia)); exact R24i.
+   let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X72.
+
assert (UH : U EL (SExt false 16 (SOff 43 0)) = cg_H s1) by (apply (U_zext_small EL 16 _ _ (U_atom EL 43 _ ltac:(rewrite AGx by (clear; lia); exact E43_2) ltac:(clear - RH; lia))); [clear - RH; cbn in RH |- *; lia | cbn; clear; lia]).
assert (UW : U EL (SExt false 16 (SOff 42 0)) = cg_W s1) by (apply (U_zext_small EL 16 _ _ (U_atom EL 42 _ ltac:(rewrite AGx by (clear; lia); exact E42_2) ltac:(clear - RW; lia))); [clear - RW; cbn in RW |- *; lia | cbn; clear; lia]).
let R := fresh "R" in rregD HS (10%bv : bv 5) R; rewrite R; rewrite denot_lit_U; unfold w64; f_equal.
rewrite U_mul_smallD by (rewrite UH, UW; clear - RW RH; nia). rewrite UH, UW. clear - HWF1. destruct HWF1 as (_ & _ & _ & HN & _). lia.
+   let R := fresh "R" in rreg HS (19%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
+   let R := fresh "R" in rreg HS (25%bv : bv 5) R; rewrite R; unfold w64; apply (shq_word EL 46 38 16 _ SB X46 X38); clear - Hcfp C1; unfold SB; lia.
+   let R := fresh "R" in rreg HS (27%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
+
change (spZ regs) with sp0.
assert (Ra4 : 0 <= Z.land fattr 4 < 2 ^ (8 * Z.of_N 8)) by (pose proof (land_small_r fattr 4 ltac:(clear - Rfattr; cbn in Rfattr; lia) ltac:(clear; lia)) as Xl; cbn in Xl; cbn; clear - Xl; lia).
af_locsD_tac HR0 Xsp X32 X38 X46 X67 X72 HZg Hgceil Hcfp Hr4096 HrCeil C1 Ra4.
+ exact HnoTab.
+ exact Hi.
+ exact Hnone.
+ exact Hs1.
+ exact HrIn.
+
pose proof (U_sext32_low EL 49 fattr ltac:(rewrite AGx by (clear; lia); exact E49_2) ltac:(clear - Rfattr; lia)) as Q49. unfold U in Q49.
pose proof (U_sext32_low EL 50 fgen ltac:(rewrite AGx by (clear; lia); exact E50_2) ltac:(clear - Rfgen; lia)) as Q50. unfold U in Q50.
pose proof (U_zext_small EL 16 _ _ (U_atom EL 51 _ ltac:(rewrite AGx by (clear; lia); exact E51_2) ltac:(clear - Rdelay; lia)) ltac:(clear - Rdelay; cbn in Rdelay |- *; lia) ltac:(cbn; clear; lia)) as Q51. unfold U in Q51.
pose proof (U_zext_small EL 16 _ _ (U_atom EL 52 _ ltac:(rewrite AGx by (clear; lia); exact E52_2) ltac:(clear - Rnlp; lia)) ltac:(clear - Rnlp; cbn in Rnlp |- *; lia) ltac:(cbn; clear; lia)) as Q52. unfold U in Q52.
lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 72%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 72 res cs lo hi wlo whi 0 8 (SOff 47 0) lpal HRn X72u ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite X47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rlpal; lia) ltac:(cbn; lia)) as V0;
pose proof (field_of_region_any Ex _ 72 res cs lo hi wlo whi 16 4 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V16;
pose proof (field_of_region_any Ex _ 72 res cs lo hi wlo whi 20 4 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V20;
pose proof (field_of_region_any Ex _ 72 res cs lo hi wlo whi 24 2 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V24;
pose proof (field_of_region_any Ex _ 72 res cs lo hi wlo whi 26 2 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V26 end.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V16, V20. change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16) in V24, V26.
rewrite Q49 in V16. rewrite Q50 in V20. rewrite Q51, Z.mod_small in V24 by (clear - Rdelay; lia). rewrite Q52, Z.mod_small in V26 by (clear - Rnlp; lia).
rewrite Z.add_0_r in V0. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0, V16, V20, V24, V26.
split; [exact V0|]. split; [exact V16|]. split; [exact V20|]. split; [exact V24|]. split; [exact V26|].
intros _.
pose proof (U_zext_small EL 8 _ _ (U_atom EL 53 _ ltac:(rewrite AGx by (clear; lia); exact E53_2) ltac:(clear - Rtidx; cbn in Rtidx |- *; lia)) ltac:(clear - Rtidx; cbn in Rtidx |- *; lia) ltac:(cbn; clear; lia)) as Q53. unfold U in Q53.
lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 72%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region_any Ex _ 72 res cs lo hi wlo whi 28 1 _ HRn X72u ltac:(cbn; tauto) ltac:(cbn; lia)) as V28 end.
change (2 ^ (8 * Z.of_N 1)) with (2 ^ 8) in V28. rewrite Q53, Z.mod_small in V28 by (clear - Rtidx; cbn in Rtidx |- *; lia). exact V28.
Qed.
End j.
End h.
