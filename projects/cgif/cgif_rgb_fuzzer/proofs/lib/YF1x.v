(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w YG0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF2d YF0r YF0u YF1f YF1t YF1p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF2h YF1r YF26 YF28 YF2a YF1w YF07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac cs_case HS HEn Htp kb :=
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ => replace (Z_to_bv 5 k) with kb by (img_try (img_apply bv_eq; img_refl)) end;
let RR := fresh "RR" in rreg HS kb RR; rewrite RR;
first [ rewrite HEn by (img_try ((img_case; cbv); img_lia)); first [ refine (YF2h.Er _ _ _ _ _ _ _ _ _ _ _ _ _); img_refl | symmetry; refine (YF2h.Er _ _ _ _ _ _ _ _ _ _ _ _ _); img_refl ]
| rewrite Htp; img_refl | symmetry; rewrite Htp; img_refl ].
Ltac inlist := cbn [In]; repeat (first [ left; img_refl | right ]); fail.
Section e. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (p : sptr) (n : Z) (ch : list (Z * Z * Z)).
Local Notation tr := (call_trace ly (0x53244 + D_2c4) regs ch).
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation pa := (sptr_addr B ly p).
Local Notation nn := (req_size n).
Hypothesis PRE : acall_pre tfxsegs B ly S W regs mem md ch.
Hypothesis HBLK : In (p, n) (blocks S).
Hypothesis HA0 : getr regs 10 = w64 pa.
Hypothesis HU : In tr (as_universe B).
Hypothesis IA1 : tfx_ialloc_spec.
Hypothesis U1 : tfx_unwind_spec.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread S).
Lemma M : ARm B ly S rd0. Proof. img_exact (proj1 (proj1 PRE)). Qed.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 M.
Let LO : layout_ok ly := am_layout B ly S rd0 M.
Local Notation kk := (YF1w.kk S p).
Local Notation kk_facts := (YF1w.kk_facts B ly S W regs mem md p n ch PRE HBLK).
Local Notation Enn := (YF1w.Enn B ly S W regs mem md p n ch PRE HBLK).
Local Notation HB1 := (YF1w.HB1 B ly S W regs mem md p n ch PRE HBLK).
Local Notation HSP := (YF1w.HSP B ly S W regs mem md p n ch PRE).
Local Notation IMG := (YF1w.IMG B ly S W regs mem md ch PRE).
Local Notation p_facts := (YF1w.p_facts B ly S W regs mem md p n ch PRE HBLK).
Local Notation QB_facts := (YF1w.QB_facts B ly S W regs mem md p n ch PRE HBLK).
Local Notation hb1 := (YF1w.hb1 B ly W mem p).
Local Notation j1 := (YF1w.j1 ly W mem).
Local Notation j2 := (YF1w.j2 ly W mem).
Local Notation j3 := (YF1w.j3 B ly W mem p).
Local Notation E0 := (YF2h.E0 ly regs ch pa nn hb1 q j1 j2 j3).
Local Notation LENv := (YF2h.LENv ly regs ch).
Local Notation QBFv := (YF2h.QBFv nn q).
Local Notation E2 := (YF1w.E2 B ly S W regs mem p n ch).
Local Notation EaT := (YF1w.EaT B ly S W regs mem p n ch).
Local Notation EaQBF := (YF1w.EaQBF B ly S W regs mem p n ch).
Local Notation EaLEN := (YF1w.EaLEN B ly S W regs mem p n ch).
Local Notation FH_ok := (YF1w.FH_ok B TB ly S W regs mem md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation CONST_OUT := (YF1w.CONST_OUT B TB ly S W regs mem md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation DFP_RANGE := (YF1w.DFP_RANGE B TB ly S W regs mem md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation DFP_OUT := (YF1w.DFP_OUT B TB ly S W regs mem md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation ENQ_PRE := (YF1w.ENQ_PRE B TB ly S W regs mem md p n ch PRE HBLK HA0 HU IA1 U1 HTSD).
Local Notation MID_AG := (YF1w.MID_AG B TB ly S W regs mem md p n ch PRE HBLK).
Local Notation s1_wf := (YF1w.s1_wf B ly S W regs mem md p n ch PRE).
Local Notation kept_of_aview := (YF1w.kept_of_aview W).
Let s1 : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Let kk' : chunk := mkChunk (ck_beg kk) (ck_req kk) CQuarantined.
Hypothesis NODRAIN : qc_bytes (st_qthread S) + nn + (if need_new_batch (st_qthread S) then kBatchBytes else 0) <= kQuarantineCacheMax.
Hypothesis D1 : tfx_depot_spec B.
Hypothesis Q1 : tfx_enqueue_spec_nb B (need_new_batch (st_qthread S)).
Lemma TAILM : forall z msE matE E5 (W5 : world tfxsegs) regs' mem' md' (X' : astate) nb,
let X := YF1f.S' S kk z tr in let mdE := with_vm_backing (m_vm_lazy md) matE md in
aok s1 (KDepot tr) z ->
msE = mkst (ms_regs msE) (w64 (0x35dd8 + D_150)) (ms_mem msE) (seg_rom tfxsegs) ->
(forall k0, (k0 < aHAVf)%nat -> ew E5 k0 = ew E0 k0) ->
st_ok tfxsegs E5 SS_E (restrict (w_H W) msE) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msE) a) ->
AR tfxsegs B ly X W (ms_mem msE) mdE ->
acall_post tfxsegs B QSTACK ly X W (ms_regs msE) (ms_mem msE) mdE (fun _ => False) ly X' W5 regs' mem' md' ->
st_qthread X' = qc_push (st_qthread X) kk' nb ->
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ ascratch B ASTACK regs a -> ~ (pa <= a < pa + nn) ->
aview tfxsegs (w_H W) (ms_mem msE) a = aview tfxsegs (w_H W) mem a) ->
SRr tfxsegs W5 (cfg_at tfxsegs (0x35dcc + D_150) regs' mem' md') (free_leaf tfxsegs B ly S W regs mem md p n (tt, X')).
Proof.
intros z msE matE E5 W5 regs' mem' md' X' nb X mdE AOK HshE HEn5 HS PRESE ARX (ARX' & LLE & WLE & CS & SIO & FR & PRS) HQ' Hnb HCK' HQG' AGP.
destruct PRE as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT). destruct HAR as (M0 & LED & BUD & MW & HSH).
pose proof kk_facts as (Hf & Hk & Hst & Hu & Hr). pose proof HSP as HSP'. pose proof FH_ok as FH.
pose proof (YF2h.LYB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as LB.
pose proof p_facts as (P1 & P2 & _). pose proof QB_facts as (Qa & Qb & Q8).
pose proof Hwx_tfa as Hwx. assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
rreg HS (2%bv : bv 5) Q2. rewrite (HEn5 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2 in Q2.
assert (SPE : spZ (ms_regs msE) = sp0 - 2208).
{ unfold spZ. rewrite Q2. unfold sp0, w64. rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB; unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; img_lia)). img_refl. }
unfold ascratch in FR. rewrite SPE in FR, PRS.
assert (BV2 : bv_unsigned (ew E5 2) = sp0) by (img_try (rewrite (HEn5 2%nat ltac:((img_case; cbv); img_lia)), E2; img_refl)).
assert (NOWN : forall a, sp0 - ASTACK <= a < sp0 -> ~ aowned B ly X a /\ ~ aowned B ly X' a).
{ intros a Ha. split.
- img_apply (AR_stack_law_ok tfxsegs B ly X W (ms_mem msE) mdE a ARX). clear - Ha Hlo Hhi. unfold spZ, ASTACK in *. unfold sp0 in *. img_lia.
- img_apply (AR_stack_law_ok tfxsegs B ly X' W5 mem' md' a ARX'). clear - Ha Hlo Hhi. unfold spZ, ASTACK in *. unfold sp0 in *. img_lia. }
assert (AGS : forall a, sp0 - 2208 <= a < sp0 -> aview tfxsegs (w_H W5) mem' a = aview tfxsegs (w_H W) (ms_mem msE) a).
{ intros a Ha. destruct (NOWN a ltac:(img_try (clear - Ha; unfold ASTACK; img_lia))) as [N1 N2]. img_apply FR; [img_try (clear - Ha Usp Hlo LB; unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; img_lia) | img_try (img_exact N1) | img_try (img_exact N2) | | img_try (intros [])].
unfold ascratch. rewrite (ts_errno _ TB). unfold TFX_ERRNO, QSTACK. clear - Ha Hlo LB. unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *. unfold sp0 in *. img_lia. }
assert (HP : regs_preserved (ms_regs msE) regs') by (img_try (intros r Hr'; img_apply CS; img_exact Hr')).
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := img_ev (ss_mem ss) in
lazymatch m with ?r0 :: ?r1 :: ?r2 :: ?r3 :: ?r4 :: ?rest =>
pose proof (st_ok_after_call tfxsegs 112 E5 ss ms0 regs' (mrestrict (w_H W5) mem') (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) (0x35dcc + D_150) HS eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try (img_apply submem_keep; [img_try (img_apply subregion_trim_lo)|]; img_apply submem_keep; [img_try (img_apply subregion_refl)|]; img_apply submem_keep; [img_try (img_apply subregion_refl)|];
img_apply submem_drop; img_apply submem_keep; [img_try (img_apply subregion_refl)|]; img_apply submem_nil))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) HP) as HS1;
let rsv := img_ev (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) in
img_change (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) with rsv in HS1;
let ss2 := img_ev (ss_after_call ss rsv 112 (0x35dcc + D_150)) in
change (ss_after_call ss rsv 112 (0x35dcc + D_150)) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ ?L -> _ =>
assert (KEPT : Forall (region_kept tfxsegs E5 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W5) mem')) L);
[ img_try (repeat img_apply Forall_cons; try img_apply Forall_nil;
(img_apply kept_of_aview; cbn [base_val YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi]; rewrite BV2;
[ intros a Ha; img_apply AGS; clear - Ha; img_lia
| intros a Ha; split; [img_apply AGS; clear - Ha; img_lia | clear - Ha Usp Hlo LB; unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFX_IMG_END in *; unfold sp0 in *; img_lia] ]))
| img_try (specialize (HS1 KEPT); clear KEPT) ]
end.
set (En6 := havoc E5 112 (map (getr regs') CLOB)) in HS1.
assert (HEn6 : forall k0, (k0 < aHAVf)%nat -> ew En6 k0 = ew E0 k0) by (img_try (intros k0 Hk0; (subst En6; cbv beta); unfold aHAVf in Hk0; rewrite ew_havoc_old by img_lia; img_apply HEn5; img_exact Hk0)).
assert (QB' : qc_bytes (st_qthread X') = QBFv).
{ rewrite HQ'. (subst X; cbv beta). rewrite (YF1f.S'_qthread S kk z tr) in Hnb |- *. unfold YF2h.QBFv. img_change (st_qthread S) with q in *.
destruct nb; rewrite Hnb; cbn [qc_push qc_bytes]; img_change (ck_n kk') with (ck_n kk); rewrite <- Enn; img_lia. }
assert (RV : val_mem tfxsegs (mrestrict (w_H W5) mem') (ly_T ly + (t_qc + 24)) (N.to_nat 8) QBFv).
{ rewrite <- QB'. destruct ARX' as (MX' & _).
assert (C : cell_holds B ly (aview tfxsegs (w_H W5) mem') (z8 (aoff (AT t_qc) 24) (qc_bytes (st_qthread X')))).
{ img_apply (proj1 (Forall_forall _ _) (am_cells B ly X' _ MX')). unfold acells. rewrite !in_app_iff. do 4 right. left. unfold quar_cells, qc_cells. cbn. tauto. }
replace (ly_T ly + (t_qc + 24)) with (aeval B ly (aoff (AT t_qc) 24)) by (img_try (cbn; img_lia)).
img_exact (cell_holds_val_mem B ly (w_H W5) mem' _ 8 (ANum (qc_bytes (st_qthread X'))) C). }
apply (st_ok_add_region _ _ _ (YQ0b.mkRegion (Some 32%nat) (t_qc + 24) (t_qc + 32) 0 0 [YQ0b.mkChunk (t_qc + 24) (CVal 8 (SOff 50%nat 0))])) in HS1;
[ | img_refl
| img_try (unfold YQ0b.region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem];
rewrite (HEn6 32%nat ltac:((img_case; cbv); img_lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; img_lia);
split; [clear - LB; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; img_lia|]; split; [clear - LB; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; img_lia|]; split; [intros o Ho; img_lia|];
img_apply Forall_cons; [|img_apply Forall_nil];
eapply (chunk_ok_val tfxsegs En6 _ _ _ 8 (SOff 50%nat 0) QBFv);
[ cbn [sv_denot]; rewrite (HEn6 50%nat ltac:((img_case; cbv); img_lia)), EaQBF; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia
| clear - Qa Qb Q8; unfold YF2h.QBFv, YF2h.QBMAX, kQuarantineCacheMax, kBatchBytes in *; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); destruct (need_new_batch q); img_lia
| cbn; img_lia | img_exact RV ])
| img_try (cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite ?(HEn6 32%nat ltac:((img_case; cbv); img_lia)), ?(HEn6 2%nat ltac:((img_case; cbv); img_lia)), ?EaT, ?E2; unfold w64; rewrite unsigned_lit_small by (clear - LB; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; img_lia);
fold sp0; pose proof (YF2h.stack_ivs W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (IT & _);
clear - IT LB; unfold kThreadObjSize, t_qc, ASTACK in *; repeat split; img_lia) ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W5)) in HS1. rename HS1 into HS'. clear HS. rename HS' into HS.
unfold cfg_at. rewrite <- (wvb_self md') at 1. img_change (w64 (0x35dcc + D_150)) with (Z_to_bv 64 (0x35dcc + D_150)).
srr_run_sh tfxtbl_rtF_ok HS.
rename HF into HF0. clear HFr.
srr_branch_sh tfxtbl_rtF_ok HS.
{ exfalso. match goal with H : branch_taken _ _ _ = true |- _ => rewrite branch_ltu_U in H; apply Z.ltb_lt in H; revert H end.
rewrite !U_zev by img_refl. cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn6 50%nat ltac:(img_try ((img_case; cbv); img_lia))), EaQBF, Z.add_0_r.
unfold w64. rewrite unsigned_lit_small by (img_try (clear - Qa Qb Q8; unfold YF2h.QBFv, YF2h.QBMAX, kQuarantineCacheMax, kBatchBytes in *; destruct (need_new_batch q); img_lia)).
rewrite !zcanon_id by (img_try (clear - Qa Qb Q8; unfold YF2h.QBFv, YF2h.QBMAX, kQuarantineCacheMax, kBatchBytes, M64 in *; destruct (need_new_batch q); img_lia)).
pose proof NODRAIN as ND. img_change (st_qthread S) with q in ND. clear - ND. unfold YF2h.QBFv, kQuarantineCacheMax, kBatchBytes in *.
destruct (need_new_batch q); img_lia. }
unfold YQ09.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfxtbl_rtF_ok HS.
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) => set (En7 := E) in HS; rename msx into msR end.
assert (HEn7 : forall k0, (k0 < aHAVf)%nat -> ew En7 k0 = ew E0 k0) by (img_try (intros k0 Hk0; (subst En7; cbv beta); unfold aHAVf in Hk0; rewrite ?ew_havoc_old by img_lia; img_apply HEn6; img_exact Hk0)).
assert (FRT : forall x : word, ~ (sp0 - 2208 <= bv_unsigned x < sp0 - 2128) -> ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem msR x = mem' x).
{ intros x Hx1 Hx2. rewrite (HF x); [img_try (img_apply (HF0 x))|].
all: intros Hw; destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg);
lazymatch type of Hin with In _ (windows ?rs) => let ws := img_ev (windows rs) in img_change (windows rs) with ws in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [Hin|Hin];
[ img_try (injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg; rewrite ?(HEn6 2%nat ltac:((img_case; cbv); img_lia)), ?E2, ?(HEn6 32%nat ltac:((img_case; cbv); img_lia)), ?EaT in Hrg; unfold w64 in Hrg;
rewrite ?unsigned_lit_small in Hrg by (clear - LB; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; img_lia); clear - Hx1 Hx2 Hrg; unfold ASTACK, t_qc in *; unfold sp0 in *; img_lia) |]);
destruct Hin. }
clear HF HFr HF0.
assert (PRES' : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2208 <= a < sp0 - 2128) -> ~ (sp0 - 64 <= a < sp0) -> apresent (w_H W5) mem' a).
{ intros a Ha N1 N2. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L|L]; [img_try (destruct (Z_lt_le_dec a (sp0 - 2208 - QSTACK)) as [L2|L2])|].
2:{ img_apply PRS. clear - L L2. unfold QSTACK in *. img_lia. }
all: assert (EQa : aview tfxsegs (w_H W5) mem' a = aview tfxsegs (w_H W) (ms_mem msE) a)
by (img_try (destruct (NOWN a Ha) as [M1 M2]; img_apply FR; [img_try (clear - Ha Usp Hlo LB; unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; img_lia) | img_try (img_exact M1) | img_try (img_exact M2) | | img_try (intros [])];
unfold ascratch; rewrite (ts_errno _ TB); unfold TFX_ERRNO; first [clear - Ha L L2 N1 N2 Hlo LB | clear - Ha L N1 N2 Hlo LB]; unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, QSTACK in *; unfold sp0 in *; img_lia)).
all: pose proof (PRESE a Ha) as P; apply apresent_mbyte in P as [b Hb];
assert (A : aview tfxsegs (w_H W) (ms_mem msE) a = Some (bv_unsigned b)) by (img_try (unfold aview; rewrite Hb; img_refl));
rewrite <- EQa in A; apply aview_some in A as (b' & Hb' & _);
img_exact (mbyte_high_apresent (w_H W5) mem' a b' ltac:(img_try (clear - Ha Usp Hlo LB; unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFX_IMG_END in *; unfold sp0 in *; img_lia)) Hb'). }
assert (PRESR : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W5) (ms_mem msR) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L1|L1]; [|img_try (destruct (Z_lt_le_dec a (sp0 - 2176)) as [L2|L2]; [|destruct (Z_lt_le_dec a (sp0 - 2128)) as [L3|L3]; [|destruct (Z_lt_le_dec a (sp0 - 64)) as [L4|L4]]])].
- img_apply (apresent_same (w_H W5) mem'); [img_try (img_apply FRT; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; img_lia); clear - L1; img_lia) | img_try (img_apply PRES'; [img_exact Ha | clear - L1; img_lia | clear - L1; img_lia])].
- eapply (st_ok_window_apresent (w_H W5) En7 _ _ 1 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn7 2%nat ltac:((img_case; cbv); img_lia)), E2; clear - L1 L2; unfold sp0; img_lia) | img_try (clear - Ha Usp Hlo LB; unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFX_IMG_END in *; unfold sp0 in *; img_lia)].
- eapply (st_ok_window_apresent (w_H W5) En7 _ _ 3 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn7 2%nat ltac:((img_case; cbv); img_lia)), E2; clear - L2 L3; unfold sp0; img_lia) | img_try (clear - Ha Usp Hlo LB; unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFX_IMG_END in *; unfold sp0 in *; img_lia)].
- img_apply (apresent_same (w_H W5) mem'); [img_try (img_apply FRT; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; img_lia); clear - L3 L4; img_lia) | img_try (img_apply PRES'; [img_exact Ha | clear - L3 L4; img_lia | clear - L3 L4; img_lia])].
- eapply (st_ok_window_apresent (w_H W5) En7 _ _ 4 _ a HS); [img_refl | img_try (cbn [base_val YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite (HEn7 2%nat ltac:((img_case; cbv); img_lia)), E2; clear - L4 Ha; unfold sp0; img_lia) | img_try (clear - Ha Usp Hlo LB; unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFX_IMG_END in *; unfold sp0 in *; img_lia)]. }
eapply (SRr_ret_at tfxsegs tfxtbl_rtF tfxtbl_rtF_ok Hwx W5 En7); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'.
rreg HS (1%bv : bv 5) Q1f. rewrite (HEn7 1%nat ltac:(img_try ((img_case; cbv); img_lia))), (YF2h.E1 ly regs ch pa nn hb1 q j1 j2 j3) in Q1f.
exists ly, (ms_regs msR), (ms_mem msR), (with_vm_backing (m_vm_lazy md') mat' md'). split.
{ unfold cfg_at, raZ, w64. rewrite Q1f, Z_to_bv_bv_unsigned. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split.
2:{
pose proof HQT as (T1 & T2 & T3). pose proof (YF1f.quar_S' B ly S rd0 M kk Hk Hst z tr) as [QX1 QX2].
pose proof (unq_push X X' kk' nb HCK' HQ' HQG' ltac:(img_try (intros ->; img_exact Hnb))) as UQ. unfold unq in UQ.
cbn [snd]. unfold qtight. rewrite QB', HQG'. split; [|img_try (split)].
- clear - NODRAIN. unfold YF2h.QBFv. img_change (st_qthread S) with q in NODRAIN. destruct (need_new_batch q); unfold kBatchBytes in *; img_lia.
- (subst X; cbv beta). rewrite (YF1f.S'_qglobal S kk z tr). img_exact T2.
- assert (QE : quar_n X' = quar_n X) by (img_try (unfold quar_n; rewrite HCK'; img_refl)).
img_change (ck_n kk') with (ck_n kk) in UQ. (subst X; cbv beta). clear - QX1 QX2 UQ QE T3. img_lia. }
assert (AGT : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2208 <= a < sp0 - 2128) -> ~ (sp0 - 64 <= a < sp0) -> aview tfxsegs (w_H W5) (ms_mem msR) a = aview tfxsegs (w_H W5) mem' a).
{ intros a Ha N1 N2. img_apply aview_same. img_apply FRT; rewrite unsigned_lit_small by img_exact Ha; assumption. }
assert (PNN : p <> PNull).
{ intros Hp0. pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) kk Hk) as [_ CK].
assert (HU0 : ck_user kk = PNull) by (img_try (rewrite Hu; img_exact Hp0)). unfold ck_user in HU0. destruct (ck_beg kk); cbn in HU0; try discriminate; destruct CK. }
split; [|img_try (split; [img_apply layout_le_refl | split; [img_exact WLE | split; [|split; [|split]]]])].
-
img_apply (AR_frame_law_ok tfxsegs B ly X' W5 mem' md' (ms_mem msR) _ ARX').
+ intros a Ha HO. img_apply AGT; [img_try (img_exact Ha)| |]; intros Hs; (img_apply (AR_stack_law_ok tfxsegs B ly X' W5 mem' md' a ARX'); [|img_try (img_exact HO)]); clear - Hs Hlo Hhi; unfold spZ, ASTACK in *; unfold sp0 in *; img_lia.
+ intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W5 x) eqn:Hx; [img_try (img_exact (Hv HN))|]. destruct (seg_rom tfxsegs x) eqn:ROM; [img_try (destruct (ms_mem msR x); discriminate)|].
destruct (ms_mem msR x) as [|] eqn:E'; [img_try (discriminate)|]. clear HN. destruct (mem' x) as [b0|] eqn:EE0; [img_try (clear Hv) | img_try (img_exact (Hv eq_refl))].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (img_try ((subst a'; cbv beta); img_apply u64_range)). assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
assert (EM : forall lo hi, (lo <= a' < hi) \/ ~ (lo <= a' < hi)) by (img_try (intros; img_lia)).
destruct (EM (sp0 - 2208) (sp0 - 2128)) as [C1|C1]; [|img_try (destruct (EM (sp0 - 64) sp0) as [C2|C2])].
* destruct (PRESR a' ltac:(img_try (clear - C1; unfold ASTACK; img_lia))) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
* destruct (PRESR a' ltac:(img_try (clear - C2; unfold ASTACK; img_lia))) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
* rewrite (FRT x C1 C2) in E'. congruence.
+ img_refl. + img_refl. + img_refl.
+
intros a Ha Hx. unfold w64 in *. img_apply FRT; rewrite unsigned_lit_small by (img_try (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia));
intros C; (destruct (PRESR a ltac:(img_try (clear - C; unfold ASTACK; img_lia))) as [Hh _]); unfold w64 in Hh; rewrite Hx in Hh; discriminate.
-
intros r Hr'. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
clear Hr'. rewrite (ts_tp _ TB) in Htp.
repeat match type of R with _ \/ _ => destruct R as [R|R] end; (subst r; cbv beta);
[ img_try (cs_case HS HEn7 Htp (2%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (3%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (4%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (8%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (9%bv : bv 5))
| img_try (cs_case HS HEn7 Htp (18%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (19%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (20%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (21%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (22%bv : bv 5))
| img_try (cs_case HS HEn7 Htp (23%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (24%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (25%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (26%bv : bv 5)) | img_try (cs_case HS HEn7 Htp (27%bv : bv 5)) ].
-
clear - SIO. unfold same_io in SIO |- *. destruct md, md'. cbn in SIO |- *.
intuition congruence.
-
intros a Ha NO NO' NS NE.
rewrite AGT; [| img_try (img_exact Ha) | img_try (intros Hs; img_apply NS; unfold ascratch; left; clear - Hs; unfold spZ, ASTACK; unfold sp0 in *; img_lia) | img_try (intros Hs; img_apply NS; unfold ascratch; left; clear - Hs; unfold spZ, ASTACK; unfold sp0 in *; img_lia)].
rewrite FR; [| img_try (img_exact Ha) | | img_try (img_exact NO') | | img_try (intros [])].
+ img_apply AGP; [img_try (img_exact Ha) | img_try (img_exact NO) | img_try (img_exact NS) |]. intros Hb. img_apply NE. img_exact (conj PNN Hb).
+ intros OX. destruct (YF1f.owned_S' B ly S rd0 M kk Hk z tr a OX) as [O|O]; [img_try (img_exact (NO O))|].
img_apply NE. split; [img_try (img_exact PNN)|]. rewrite Hu, <- Enn in O. img_exact O.
+ intros Hs. img_apply NS. unfold ascratch in Hs |- *. destruct Hs as [Hs|Hs]; [img_try (left; clear - Hs; unfold spZ, QSTACK, ASTACK in *; unfold sp0 in *; img_lia) | img_try (right; img_exact Hs)].
-
intros a Ha. img_apply PRESR. unfold spZ in Ha. img_exact Ha.
Qed.
Theorem afree_mid_arm :
amreal tfxsegs (free p tr S) W (cfg_at tfxsegs (0x53100 + D_2c4) regs mem md) (free_leaf tfxsegs B ly S W regs mem md p n).
Proof.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT).
destruct HAR as (M0 & LED & BUD & MW & HSH).
pose proof kk_facts as (Hf & Hk & Hst & Hu & Hr). pose proof FH_ok as FH.
pose proof (YF2h.LYB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as LB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
set (BODY := fun s' : astate =>
(match p with
| PNull => ret ()
| _ => s <- get;;
match find_user (st_chunks s) p with
| Some k0 =>
mcheck match ck_state k0 with CAllocated => true | CQuarantined => false end 201300;;
depot_put tr;;
modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |}) s0);;
enqueue {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |};; maybe_drain
| None => fail (FCheck 201312)
end
end) s').
assert (SPLIT : amreal tfxsegs (BODY s1) W (cfg_at tfxsegs (0x53100 + D_2c4) regs mem md) (free_leaf tfxsegs B ly S W regs mem md p n) ->
amreal tfxsegs (free p tr S) W (cfg_at tfxsegs (0x53100 + D_2c4) regs mem md) (free_leaf tfxsegs B ly S W regs mem md p n)).
{ intros MAIN. unfold free. cbn [bind ret tick modify mcheck ibind get put set_nev set_internal_inited st_internal_inited].
destruct (st_internal_inited S) eqn:E; cbn [ibind ret modify].
- replace (set_nev (st_nev S + 1) S) with s1; [img_try (img_exact MAIN)|]. unfold s1. generalize E. generalize S. clear. intros S0 E0. destruct S0; cbn in E0 |- *. (subst; cbv beta). img_refl.
- img_exact MAIN. }
img_apply SPLIT. clear SPLIT. (subst BODY; cbv beta). cbn beta.
assert (PNN : p <> PNull).
{ intros Hp0. pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) kk Hk) as [_ CK].
assert (HU0 : ck_user kk = PNull) by (img_try (rewrite Hu; img_exact Hp0)). unfold ck_user in HU0. destruct (ck_beg kk); cbn in HU0; try discriminate; destruct CK. }
rewrite (match_nonnull p); [|img_try (img_exact PNN)].
cbn [bind get ret ibind]. img_change (st_chunks s1) with (st_chunks S). rewrite Hf, Hst. cbn [mcheck ret ibind].
img_change {| ck_beg := ck_beg kk; ck_req := ck_req kk; ck_state := CQuarantined |} with kk'.
unfold depot_put. cbn [bind askz ibind].
img_apply amreal_ask_depot.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_bind; [img_try (img_exact (YF26.segA W ly regs mem md ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) (m_vm_materialized md) FH))|].
intros W1 c1 _ HU1.
eapply SRr_bind; [img_try (img_exact (YF28.segB W ly regs mem md ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH W1 c1 HU1))|].
clear HU1. intros W2 c2 _ (-> & msD & matD & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
rewrite HshD. eapply SRr_bind.
{ assert (AGD : forall a, ~ YF2h.WIN ly regs pa a -> ~ YF2h.IZONE a -> 0 <= a < 2 ^ 64 ->
aview tfxsegs (w_H W) (ms_mem msD) a = aview tfxsegs (w_H W) mem a).
{ intros a Hw Hz Ha. img_apply aview_same. img_apply (proj1 MEQD); rewrite unsigned_lit_small by img_exact Ha; assumption. }
rreg HS (2%bv : bv 5) R2. rewrite (HEn3 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2 in R2.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
img_apply (D1 W ly s1 (ms_regs msD) (ms_mem msD) _ (sp0 - 2112) tr LO IMG s1_wf HU).
-
img_apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly (aview tfxsegs (w_H W) mem)).
+ img_exact (proj1 (Forall_forall _ _) (am_const B ly S _ M) c Hc).
+ intros i Hi. destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as (X1 & X2 & X3). img_apply AGD; assumption.
-
assert (DM : depot_mem_ok B ly S (aview tfxsegs (w_H W) mem)).
{ split; [|img_try (split)].
- img_apply Forall_forall. intros c Hc. img_apply (proj1 (Forall_forall _ _) (am_cells B ly S _ M)). unfold acells. rewrite !in_app_iff. tauto.
- img_exact (am_depot B ly S _ M).
- pose proof (am_junk B ly S _ M) as J. pose proof (am_areas B ly S _ M) as A. rewrite Forall_forall in J, A.
repeat img_apply Forall_cons; try img_apply Forall_nil;
first [ img_apply J; unfold ajunk; do 2 right; repeat (img_apply in_or_app; first [ left; inlist | right ]); inlist
| img_apply A; unfold aareas; repeat (img_apply in_or_app; first [ left; inlist | right ]); inlist ]. }
eapply (YF1t.depot_mem_ok_agree B ly S s1); [img_try (img_exact (am_wf B ly S _ M)) | img_try (img_exact (am_universe B ly S _ M)) | img_refl | | img_try (img_exact DM)].
intros a Ha. destruct (DFP_OUT a Ha) as (X1 & X2 & X3). img_apply AGD; [img_try (img_exact X1) | img_try (img_exact X2) | img_try (img_exact (DFP_RANGE a Ha))].
- rreg HS (10%bv : bv 5) R; rewrite R, (HEn3 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2. unfold sp0; f_equal; img_lia.
- rreg HS (11%bv : bv 5) R; rewrite R, (HEn3 36%nat ltac:(img_try ((img_case; cbv); img_lia))), EaLEN. img_refl.
- rreg HS (3%bv : bv 5) R; rewrite R, (HEn3 3%nat ltac:(img_try ((img_case; cbv); img_lia))), (YF2h.Er ly regs ch pa nn hb1 q j1 j2 j3 3 3%bv eq_refl). img_exact Hgp.
- rreg HS (4%bv : bv 5) R; rewrite R. rewrite (ts_tp _ TB) in Htp. img_refl.
- rreg HS (1%bv : bv 5) R; rewrite R. img_apply YK0s.ret_ok_even. img_refl.
- intros i Hi. img_apply (TRQ i Hi).
- unfold sp0. replace (bv_unsigned (getr regs 2) - 2112) with (bv_unsigned (getr regs 2) + (-264) * 8) by img_lia. rewrite Z_mod_plus_full.
img_apply (mod0_factor _ 8 2); [img_lia|]. img_exact Hal.
- unfold spZ, ASTACK in *; unfold sp0; img_lia.
-   unfold spZ, ASTACK in *; unfold sp0; img_lia.
- right. rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)). unfold sp0; img_lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)).
replace (bv_unsigned (getr regs 2) + -2176) with (bv_unsigned (getr regs 2) + (-136) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hal.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)). unfold spZ, ASTACK, DEP_STK in *; img_lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)). unfold spZ in *; img_lia.
- intros a Ha. rewrite R2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)).
img_apply PRESD. unfold DEP_STK, ASTACK, sp0 in *. img_lia. }
intros W3 c3 _ (-> & z & regs4 & mem4 & mat4 & -> & AOK & HP4 & Hfr4 & Hpr4 & DEPOK & HC4). srr_norm_model.
img_apply SRr_ret. exists z. split; [img_try (img_exact AOK)|].
rreg HS (1%bv : bv 5) Q1r. rreg HS (2%bv : bv 5) Q2.
rewrite Q2, (HEn3 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2 in Hfr4.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
rewrite unsigned_lit_small in Hfr4 by (img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; img_lia)). fold sp0 in Hfr4.
assert (Hfr4' : forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) -> ~ depot_footprint B ly (bv_unsigned x) -> mem4 x = ms_mem msD x).
{ intros x Hx Hd. img_apply Hfr4; [img_try (clear - Hx; img_lia) | img_try (img_exact Hd)]. }
assert (DZ : forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) -> ~ YF2h.DZONE ly (bv_unsigned x) -> mem4 x = ms_mem msD x).
{ intros x Hx Hd. img_apply Hfr4'; [img_try (img_exact Hx)|]. intros Hf'. img_apply Hd. img_exact (proj2 (proj2 (DFP_OUT _ Hf'))). }
assert (TAIL : let sd := depot_after z tr s1 in
amreal tfxsegs ((modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) kk') s0);; enqueue kk';; maybe_drain) sd)
W (mkCfg (mkst regs4 (getr (ms_regs msD) 1) mem4 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat4 md))
(free_leaf tfxsegs B ly S W regs mem md p n)).
{ cbn zeta. img_apply amreal_mbind. cbn [modify amreal]. img_apply SRr_ret. cbn [fst snd].
img_change (set_chunks (upd_chunk (st_chunks (depot_after z tr s1)) kk') (depot_after z tr s1)) with (YF1f.S' S kk z tr).
set (X := YF1f.S' S kk z tr).
img_apply amreal_mbind. cbn beta.
rewrite Q1r. img_apply amreal_after_SRr. eapply SRr_mono.
{ img_apply (YF2a.segCm1 W ly regs mem md ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) nil FH msD E3 regs4 mem4 mat4).
split; [img_try (img_exact HshD)|]. split; [img_try (img_exact HEn3)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact HP4)|]. split; [img_try (img_exact DZ)|]. split; [img_try (img_exact Hpr4)|]. split; [img_try (img_exact MEQD) | img_try (img_exact PRESD)]. }
intros W4 c4 _ (-> & msE & matE & E5 & -> & HshE & HEn5 & HS5 & EQE & PRESE).
pose proof (ENQ_PRE z msD mem4 msE matE E5 AOK MEQD Hfr4' DEPOK HC4 HshE HEn5 HS5 EQE PRESE) as EP.
pose proof (proj1 EP) as ARX.
rewrite HshE at 1. img_change (mkCfg (mkst (ms_regs msE) (w64 (0x35dd8 + D_150)) (ms_mem msE) (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) matE md))
with (cfg_at tfxsegs A_Enqueue (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) matE md)).
eapply amreal_mono; [| img_try (img_exact (Q1 ly X W (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) matE md) kk' ltac:((subst X; cbv beta); rewrite (YF1f.S'_qthread S kk z tr); img_refl) EP))].
intros [[] X'] W5 c5 (regs' & mem' & md' & nb & -> & POST & HQ' & Hnb & HCK' & HQG' & HFS'). cbn [fst snd] in HQ', POST, HCK', HQG' |- *.
unfold maybe_drain. cbn [bind get ibind].
replace (qc_bytes (st_qthread X') <=? kQuarantineCacheMax) with true.
2:{ symmetry. img_apply Z.leb_le. rewrite HQ'. (subst X; cbv beta). rewrite (YF1f.S'_qthread S kk z tr) in Hnb |- *.
pose proof NODRAIN as ND. change (st_qthread S) with q in ND |- *.
destruct nb; rewrite Hnb in ND; cbn [qc_push qc_bytes]; img_change (ck_n kk') with (ck_n kk); rewrite <- Enn; clear - ND; img_lia. }
cbn [ret amreal].
rreg HS5 (1%bv : bv 5) Q1e.
unfold raZ. rewrite Q1e. rewrite unsigned_lit_small by img_lia.
img_apply (TAILM z msE matE E5 W5 regs' mem' md' X' nb AOK HshE HEn5 HS5 PRESE ARX POST HQ' Hnb HCK' HQG').
intros a Ha NO NS NB. img_apply (MID_AG msD mem4 (ms_mem msE) MEQD Hfr4' EQE a Ha). intros HD.
destruct (YF1f.D_owned B TB ly S rd0 (aview tfxsegs (w_H W) (ms_mem msE)) M kk hb1 Hk HB1 z tr sp0 (conj Hlo Hhi) IMG (proj1 ARX) a (proj1 Ha) HD) as [O|[O|O]].
- img_exact (NO O).
- destruct (YF1f.owned_S' B ly S rd0 M kk Hk z tr a O) as [O'|O']; [img_try (img_exact (NO O'))|]. img_apply NB. rewrite Hu, <- Enn in O'. img_exact O'.
- img_apply NS. unfold ascratch. left. img_exact O. }
destruct AOK as [-> | [-> _]].
- cbn [Z.eqb ret ibind]. img_exact TAIL.
- cbn [Z.eqb bind get ret ibind].
destruct (depot_ids s1 + 1 <? kDepotIdsPerBlock); cbn [mcheck ret ibind]; [|img_try (img_exact I)].
destruct (kStartFramesMax + depot_frames s1 + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock); cbn [mcheck ret put ibind]; [|img_try (img_exact I)].
img_exact TAIL.
Qed.
End e.
Theorem afree_mid {imgk : img} : forall B, TfxSyms B -> forall ly S W regs mem md p n ch,
acall_pre tfxsegs B ly S W regs mem md ch -> In (p, n) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
In (call_trace ly (0x53244 + D_2c4) regs ch) (as_universe B) ->
qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) <= kQuarantineCacheMax ->
tfx_ialloc_spec -> tfx_unwind_spec -> tfx_depot_spec B -> tfx_enqueue_spec_nb B (need_new_batch (st_qthread S)) -> ly_tsd ly = TFX_TSD ->
amreal tfxsegs (free p (call_trace ly (0x53244 + D_2c4) regs ch) S) W (cfg_at tfxsegs (0x53100 + D_2c4) regs mem md) (free_leaf tfxsegs B ly S W regs mem md p n).
Proof.
intros B TB ly S W regs mem md p n ch PRE HBLK HA0 HU ND IA1 U1 D1 Q1 HTSD.
eapply afree_mid_arm; eassumption.
Qed.
End d.
