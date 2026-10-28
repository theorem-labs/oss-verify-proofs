(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFeq AFgi AFex AFf0 AFfl AFfy AFfu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFgm AFfw AFgb AFgd AFgf AFg1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFeu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac cs_case HS HEn Htp kb :=
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ => replace (Z_to_bv 5 k) with kb by (apply bv_eq; reflexivity) end;
let RR := fresh "RR" in rreg HS kb RR; rewrite RR;
first [ rewrite HEn by (cbv; lia); first [ refine (AFgm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity | symmetry; refine (AFgm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity ]
| rewrite Htp; reflexivity | symmetry; rewrite Htp; reflexivity ].
Ltac inlist := cbn [In]; repeat (first [ left; reflexivity | right ]); fail.
Section e.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (p : sptr) (n : Z) (ch : list (Z * Z * Z)).
Local Notation tr := (call_trace ly 0x52a6c regs ch).
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation pa := (sptr_addr B ly p).
Local Notation nn := (req_size n).
Hypothesis PRE : acall_pre tfibsegs B ly S W regs mem md ch.
Hypothesis HBLK : In (p, n) (blocks S).
Hypothesis HA0 : getr regs 10 = w64 pa.
Hypothesis HU : In tr (as_universe B).
Hypothesis IA1 : tfib_ialloc_spec.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread S).
Lemma M : ARm B ly S rd0. Proof. exact (proj1 (proj1 PRE)). Qed.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 M.
Let LO : layout_ok ly := am_layout B ly S rd0 M.
Local Notation kk := (AFg1.kk S p).
Local Notation kk_facts := (AFg1.kk_facts B ly S W regs mem md p n ch PRE HBLK).
Local Notation Enn := (AFg1.Enn B ly S W regs mem md p n ch PRE HBLK).
Local Notation HB1 := (AFg1.HB1 B ly S W regs mem md p n ch PRE HBLK).
Local Notation HSP := (AFg1.HSP B ly S W regs mem md p n ch PRE).
Local Notation IMG := (AFg1.IMG B ly S W regs mem md ch PRE).
Local Notation p_facts := (AFg1.p_facts B ly S W regs mem md p n ch PRE HBLK).
Local Notation QB_facts := (AFg1.QB_facts B ly S W regs mem md p n ch PRE HBLK).
Local Notation hb1 := (AFg1.hb1 B ly W mem p).
Local Notation j1 := (AFg1.j1 ly W mem).
Local Notation j2 := (AFg1.j2 ly W mem).
Local Notation j3 := (AFg1.j3 B ly W mem p).
Local Notation E0 := (AFgm.E0 ly regs ch pa nn hb1 q j1 j2 j3).
Local Notation LENv := (AFgm.LENv ly regs ch).
Local Notation QBFv := (AFgm.QBFv nn q).
Local Notation E2 := (AFg1.E2 B ly S W regs mem p n ch).
Local Notation EaT := (AFg1.EaT B ly S W regs mem p n ch).
Local Notation EaQBF := (AFg1.EaQBF B ly S W regs mem p n ch).
Local Notation EaLEN := (AFg1.EaLEN B ly S W regs mem p n ch).
Local Notation FH_ok := (AFg1.FH_ok B TB ly S W regs mem md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation CONST_OUT := (AFg1.CONST_OUT B TB ly S W regs mem md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation DFP_RANGE := (AFg1.DFP_RANGE B TB ly S W regs mem md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation DFP_OUT := (AFg1.DFP_OUT B TB ly S W regs mem md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation ENQ_PRE := (AFg1.ENQ_PRE B TB ly S W regs mem md p n ch PRE HBLK HA0 HU IA1 U1 HTSD).
Local Notation MID_AG := (AFg1.MID_AG B TB ly S W regs mem md p n ch PRE HBLK).
Local Notation s1_wf := (AFg1.s1_wf B ly S W regs mem md p n ch PRE).
Local Notation kept_of_aview := (AFg1.kept_of_aview W).
Let s1 : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Let kk' : chunk := mkChunk (ck_beg kk) (ck_req kk) CQuarantined.
Hypothesis DRAIN : kQuarantineCacheMax < qc_bytes (st_qthread S) + nn + (if need_new_batch (st_qthread S) then kBatchBytes else 0).
Hypothesis D1 : tfib_depot_spec B.
Hypothesis Q1 : tfib_enqueue_spec_nb B (need_new_batch (st_qthread S)).
Hypothesis D0 : tfib_drain_spec B.
Lemma TAILD : forall z msE matE E5 (W5 : world tfibsegs) regs' mem' md' (X' : astate) nb,
let X := AFfl.S' S kk z tr in let mdE := with_vm_backing (m_vm_lazy md) matE md in
aok s1 (KDepot tr) z ->
msE = mkst (ms_regs msE) (w64 0x357d0) (ms_mem msE) (seg_rom tfibsegs) ->
(forall k0, (k0 < aHAVf)%nat -> ew E5 k0 = ew E0 k0) ->
st_ok tfibsegs E5 SS_E (restrict (w_H W) msE) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msE) a) ->
AR tfibsegs B ly X W (ms_mem msE) mdE ->
acall_post tfibsegs B QSTACK ly X W (ms_regs msE) (ms_mem msE) mdE (fun _ => False) ly X' W5 regs' mem' md' ->
st_qthread X' = qc_push (st_qthread X) kk' nb ->
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X -> st_fs X' = st_fs X ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ ascratch B ASTACK regs a -> ~ (pa <= a < pa + nn) ->
aview tfibsegs (w_H W) (ms_mem msE) a = aview tfibsegs (w_H W) mem a) ->
amreal tfibsegs (drain_body X' X') W5 (cfg_at tfibsegs 0x357c4 regs' mem' md') (free_leaf tfibsegs B ly S W regs mem md p n).
Proof.
intros z msE matE E5 W5 regs' mem' md' X' nb X mdE AOK HshE HEn5 HS PRESE ARX (ARX' & LLE & WLE & CS & SIO & FR & PRS) HQ' Hnb HCK' HQG' HFS' AGP.
destruct PRE as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT). destruct HAR as (M0 & LED & BUD & MW & HSH).
pose proof kk_facts as (Hf & Hk & Hst & Hu & Hr). pose proof HSP as HSP'. pose proof FH_ok as FH.
pose proof (AFgm.LYB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as LB.
pose proof p_facts as (P1 & P2 & _). pose proof QB_facts as (Qa & Qb & Q8).
pose proof Hwx_tfa as Hwx. assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
rreg HS (2%bv : bv 5) Q2. rewrite (HEn5 2%nat ltac:(cbv; lia)), E2 in Q2.
assert (SPE : spZ (ms_regs msE) = sp0 - 2208).
{ unfold spZ. rewrite Q2. unfold sp0, w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia). reflexivity. }
unfold ascratch in FR. rewrite SPE in FR, PRS.
assert (BV2 : bv_unsigned (ew E5 2) = sp0) by (rewrite (HEn5 2%nat ltac:(cbv; lia)), E2; reflexivity).
assert (NOWN : forall a, sp0 - ASTACK <= a < sp0 -> ~ aowned B ly X a /\ ~ aowned B ly X' a).
{ intros a Ha. split.
- apply (AR_stack_law_ok tfibsegs B ly X W (ms_mem msE) mdE a ARX). clear - Ha Hlo Hhi. unfold spZ, ASTACK in *. unfold sp0 in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly X' W5 mem' md' a ARX'). clear - Ha Hlo Hhi. unfold spZ, ASTACK in *. unfold sp0 in *. lia. }
assert (AGS : forall a, sp0 - 2208 <= a < sp0 -> aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a).
{ intros a Ha. destruct (NOWN a ltac:(clear - Ha; unfold ASTACK; lia)) as [N1 N2]. apply FR; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia | exact N1 | exact N2 | | intros []].
unfold ascratch. rewrite (ts_errno _ TB). unfold TFIB_ERRNO, QSTACK. clear - Ha Hlo LB. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *. unfold sp0 in *. lia. }
assert (HP : regs_preserved (ms_regs msE) regs') by (intros r Hr'; apply CS; exact Hr').
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?r0 :: ?r1 :: ?r2 :: ?r3 :: ?r4 :: ?rest =>
pose proof (st_ok_after_call tfibsegs 112 E5 ss ms0 regs' (mrestrict (w_H W5) mem') (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) 0x357c4 HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_trim_lo|]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_drop; apply submem_keep; [apply subregion_refl|]; apply submem_nil)
ltac:(vm_compute; reflexivity) HP) as HS1;
let rsv := eval vm_compute in (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) in
change (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 112 0x357c4) in
change (ss_after_call ss rsv 112 0x357c4) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ ?L -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E5 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W5) mem')) L);
[ repeat apply Forall_cons; try apply Forall_nil;
(apply kept_of_aview; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite BV2;
[ intros a Ha; apply AGS; clear - Ha; lia
| intros a Ha; split; [apply AGS; clear - Ha; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia] ])
| specialize (HS1 KEPT); clear KEPT ]
end.
set (En6 := havoc E5 112 (map (getr regs') CLOB)) in HS1.
assert (HEn6 : forall k0, (k0 < aHAVf)%nat -> ew En6 k0 = ew E0 k0) by (intros k0 Hk0; subst En6; unfold aHAVf in Hk0; rewrite ew_havoc_old by lia; apply HEn5; exact Hk0).
assert (QB' : qc_bytes (st_qthread X') = QBFv).
{ rewrite HQ'. subst X. rewrite (AFfl.S'_qthread S kk z tr) in Hnb |- *. unfold AFgm.QBFv. change (st_qthread S) with q in *.
destruct nb; rewrite Hnb; cbn [qc_push qc_bytes]; change (ck_n kk') with (ck_n kk); rewrite <- Enn; lia. }
assert (RV : val_mem tfibsegs (mrestrict (w_H W5) mem') (ly_T ly + (t_qc + 24)) (N.to_nat 8) QBFv).
{ rewrite <- QB'. destruct ARX' as (MX' & _).
assert (C : cell_holds B ly (aview tfibsegs (w_H W5) mem') (z8 (aoff (AT t_qc) 24) (qc_bytes (st_qthread X')))).
{ apply (proj1 (Forall_forall _ _) (am_cells B ly X' _ MX')). unfold acells. rewrite !in_app_iff. do 4 right. left. unfold quar_cells, qc_cells. cbn. tauto. }
replace (ly_T ly + (t_qc + 24)) with (aeval B ly (aoff (AT t_qc) 24)) by (cbn; lia).
exact (cell_holds_val_mem B ly (w_H W5) mem' _ 8 (ANum (qc_bytes (st_qthread X'))) C). }
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 32%nat) (t_qc + 24) (t_qc + 32) 0 0 [YP09.mkChunk (t_qc + 24) (CVal 8 (SOff 50%nat 0))])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn6 32%nat ltac:(cbv; lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia);
split; [clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia|]; split; [clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
eapply (chunk_ok_val tfibsegs En6 _ _ _ 8 (SOff 50%nat 0) QBFv);
[ cbn [sv_denot]; rewrite (HEn6 50%nat ltac:(cbv; lia)), EaQBF; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia
| clear - Qa Qb Q8; unfold AFgm.QBFv, AFgm.QBMAX, kQuarantineCacheMax, kBatchBytes in *; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); destruct (need_new_batch q); lia
| cbn; lia | exact RV ]
| cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?(HEn6 32%nat ltac:(cbv; lia)), ?(HEn6 2%nat ltac:(cbv; lia)), ?EaT, ?E2; unfold w64; rewrite unsigned_lit_small by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia);
fold sp0; pose proof (AFgm.stack_ivs W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (IT & _);
clear - IT LB; unfold kThreadObjSize, t_qc, ASTACK in *; repeat split; lia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W5)) in HS1. rename HS1 into HS'. clear HS. rename HS' into HS.
unfold cfg_at. rewrite <- (wvb_self md') at 1. change (w64 0x357c4) with (Z_to_bv 64 0x357c4).
apply amreal_after_SRr.
srr_run_sh tfibtbl_rtF_ok HS.
rename HF into HF0. clear HFr.
srr_branch_sh tfibtbl_rtF_ok HS.
2:{ exfalso. match goal with H : branch_taken _ _ _ = false |- _ => rewrite branch_ltu_U in H; apply Z.ltb_ge in H; revert H end.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn6 50%nat ltac:(cbv; lia)), EaQBF, Z.add_0_r.
unfold w64. rewrite unsigned_lit_small by (clear - Qa Qb Q8; unfold AFgm.QBFv, AFgm.QBMAX, kQuarantineCacheMax, kBatchBytes in *; destruct (need_new_batch q); lia).
rewrite !zcanon_id by (clear - Qa Qb Q8; unfold AFgm.QBFv, AFgm.QBMAX, kQuarantineCacheMax, kBatchBytes, M64 in *; destruct (need_new_batch q); lia).
pose proof DRAIN as ND. change (st_qthread S) with q in ND. clear - ND. unfold AFgm.QBFv, kQuarantineCacheMax, kBatchBytes in *.
destruct (need_new_batch q); lia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtF_ok HS. rename HF into HF1. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing _ ?mx _)) _ => rename mx into matC end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W5) En6 _ _ HS eq_refl) as HshC; cbn [ss_pc] in HshC.
assert (FR1 : forall x : word, ~ (sp0 - 2208 <= bv_unsigned x < sp0 - 2128) -> ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem msC x = mem' x).
{ intros x Hx1 Hx2. rewrite (HF1 x); [apply (HF0 x)|].
all: intros Hw; destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg);
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg; rewrite ?(HEn6 2%nat ltac:(cbv; lia)), ?E2, ?(HEn6 32%nat ltac:(cbv; lia)), ?EaT in Hrg; unfold w64 in Hrg;
rewrite ?unsigned_lit_small in Hrg by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); clear - Hx1 Hx2 Hrg; unfold ASTACK, t_qc in *; unfold sp0 in *; lia |]);
destruct Hin. }
clear HF1 HF0.
assert (PRES' : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2208 <= a < sp0 - 2128) -> ~ (sp0 - 64 <= a < sp0) -> apresent (w_H W5) mem' a).
{ intros a Ha N1 N2. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L|L]; [destruct (Z_lt_le_dec a (sp0 - 2208 - QSTACK)) as [L2|L2]|].
2:{ apply PRS. clear - L L2. unfold QSTACK in *. lia. }
all: assert (EQa : aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a)
by (destruct (NOWN a Ha) as [M1 M2]; apply FR; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia | exact M1 | exact M2 | | intros []];
unfold ascratch; rewrite (ts_errno _ TB); unfold TFIB_ERRNO; first [clear - Ha L L2 N1 N2 Hlo LB | clear - Ha L N1 N2 Hlo LB]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, QSTACK in *; unfold sp0 in *; lia).
all: pose proof (PRESE a Ha) as P; apply apresent_mbyte in P as [b Hb];
assert (A : aview tfibsegs (w_H W) (ms_mem msE) a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity);
rewrite <- EQa in A; apply aview_some in A as (b' & Hb' & _);
exact (mbyte_high_apresent (w_H W5) mem' a b' ltac:(clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia) Hb'). }
assert (PRESC : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W5) (ms_mem msC) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L1|L1]; [|destruct (Z_lt_le_dec a (sp0 - 2176)) as [L2|L2]; [|destruct (Z_lt_le_dec a (sp0 - 2128)) as [L3|L3]; [|destruct (Z_lt_le_dec a (sp0 - 64)) as [L4|L4]]]].
- apply (apresent_same (w_H W5) mem'); [apply FR1; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia); clear - L1; lia | apply PRES'; [exact Ha | clear - L1; lia | clear - L1; lia]].
- eapply (st_ok_window_apresent (w_H W5) En6 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn6 2%nat ltac:(cbv; lia)), E2; clear - L1 L2; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- eapply (st_ok_window_apresent (w_H W5) En6 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn6 2%nat ltac:(cbv; lia)), E2; clear - L2 L3; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- apply (apresent_same (w_H W5) mem'); [apply FR1; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia); clear - L3 L4; lia | apply PRES'; [exact Ha | clear - L3 L4; lia | clear - L3 L4; lia]].
- eapply (st_ok_window_apresent (w_H W5) En6 _ _ 4 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn6 2%nat ltac:(cbv; lia)), E2; clear - L4 Ha; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia]. }
assert (AGC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2208 <= a < sp0 - 2128) -> ~ (sp0 - 64 <= a < sp0) -> aview tfibsegs (w_H W5) (ms_mem msC) a = aview tfibsegs (w_H W5) mem' a).
{ intros a Ha N1 N2. apply aview_same. apply FR1; rewrite unsigned_lit_small by exact Ha; assumption. }
assert (WDEC : forall a, ((sp0 - 2208 <= a < sp0 - 2128) \/ (sp0 - 64 <= a < sp0)) \/ (~ (sp0 - 2208 <= a < sp0 - 2128) /\ ~ (sp0 - 64 <= a < sp0))).
{ intros a. clear. destruct (Z_lt_le_dec a (sp0 - 2208)); [right; lia|]. destruct (Z_lt_le_dec a (sp0 - 2128)); [left; lia|].
destruct (Z_lt_le_dec a (sp0 - 64)); [right; lia|]. destruct (Z_lt_le_dec a sp0); [left; lia | right; lia]. }
assert (VISC : forall a, aview tfibsegs (w_H W5) mem' a <> None -> aview tfibsegs (w_H W5) (ms_mem msC) a <> None).
{ intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W5 x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (ms_mem msC x); discriminate|].
destruct (ms_mem msC x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem' x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (WDEC a') as [C|[C1 C2]].
- destruct (PRESC a' ltac:(clear - C; unfold ASTACK; lia)) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
- rewrite (FR1 x C1 C2) in E'. congruence. }
assert (HSKC : forall a, in_band_rw a -> w_H W5 (w64 a) = true -> ms_mem msC (w64 a) = mem' (w64 a)).
{ intros a Ha Hx. unfold w64 in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
destruct (WDEC a) as [C|[C1 C2]].
- exfalso. destruct (PRESC a ltac:(clear - C; unfold ASTACK; lia)) as [Hh _]. rewrite Hx in Hh. discriminate.
- apply FR1; rewrite unsigned_lit_small by exact Ha'; assumption. }
assert (ARC : AR tfibsegs B ly X' W5 (ms_mem msC) (with_vm_backing (m_vm_lazy md') matC md')).
{ apply (AR_frame_law_ok tfibsegs B ly X' W5 mem' md' (ms_mem msC) _ ARX').
- intros a Ha O. destruct (WDEC a) as [C|[C1 C2]]; [exfalso; exact (proj2 (NOWN a ltac:(clear - C; unfold ASTACK; lia)) O) | exact (AGC a Ha C1 C2)].
- exact VISC.
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- exact HSKC. }
apply SRr_ret. rewrite HshC.
rreg HS (1%bv : bv 5) C1. rreg HS (2%bv : bv 5) C2. rreg HS (3%bv : bv 5) C3. rreg HS (4%bv : bv 5) C4.
rreg HS (10%bv : bv 5) C10. rreg HS (11%bv : bv 5) C11. rreg HS (12%bv : bv 5) C12.
cbn [sv_denot] in C1, C2, C3, C4, C10, C11, C12.
rewrite (HEn6 2%nat ltac:(cbv; lia)), E2 in C2. fold sp0 in C2. rewrite (HEn6 32%nat ltac:(cbv; lia)), EaT in C11, C12. unfold w64 in C11, C12.
rewrite unsigned_lit_small in C11, C12 by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia).
pose proof (qmeter_tight _ HQT) as (T1 & T2 & T3). pose proof (AFfl.quar_S' B ly S rd0 M kk Hk Hst z tr) as [QX1 QX2].
pose proof (unq_push X X' kk' nb HCK' HQ' HQG' ltac:(intros ->; exact Hnb)) as UQ. unfold unq in UQ.
assert (QE : quar_n X' = quar_n X) by (unfold quar_n; rewrite HCK'; reflexivity).
assert (WFX' : Wf (as_universe B) X') by (destruct ARX' as (MX' & _); exact (am_wf B ly X' _ MX')).
assert (DRX' : kQuarantineCacheMax < qc_bytes (st_qthread X')).
{ rewrite QB'. pose proof DRAIN as DR'. change (st_qthread S) with q in DR'. unfold AFgm.QBFv. exact DR'. }
assert (QLX' : qloose X').
{ unfold qloose. rewrite QB', HQG'. split; [|split].
+ clear - Qb. unfold AFgm.QBMAX, kQuarantineCacheMax, kBatchBytes in Qb. lia.
+ subst X. rewrite (AFfl.S'_qglobal S kk z tr). clear - T2. unfold kQuarantineMax in *. lia.
+ change (ck_n kk') with (ck_n kk) in UQ. subst X. clear - QX1 QX2 UQ QE T3. lia. }
eapply amreal_then_SRr.
{ eapply (amreal_apost _ (drain_body X' X') _ W5 _ _ (drain_body_apost (as_universe B) 0 0 0 X' WFX' QLX' DRX')).
apply (D0 ly X' W5 (ms_regs msC) (ms_mem msC) (with_vm_backing (m_vm_lazy md') matC md')).
unfold drain_pre, spZ, raZ. rewrite C1, C2, C3, C4, C10, C11, C12. rewrite !unsigned_lit_small by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia).
splits.
- exact ARC.
- exact DRX'.
- exact QLX'.
- apply YK0s.ret_ok_even. reflexivity.
- clear; lia.
- replace (sp0 + -2208) with (sp0 + (-138) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
- clear - Hlo. unfold DSTACK, spZ, ASTACK in *. unfold sp0 in *. lia.
- clear - Hhi. unfold spZ in *. unfold sp0 in *. lia.
- intros a Ha. apply PRESC. clear - Ha. unfold DSTACK, ASTACK in *. lia.
- rewrite (HEn6 3%nat ltac:(cbv; lia)), (AFgm.Er ly regs ch pa nn hb1 q j1 j2 j3 3 3%bv eq_refl). exact Hgp.
- rewrite (ts_tp _ TB). reflexivity.
- reflexivity.
- reflexivity.
- reflexivity. }
intros [[] X''] W6 c6 [(WX'' & FF6 & QT6 & QG6 & UQ6) (regs6 & mem6 & md6 & -> & POST6)]. cbn [fst snd] in WX'', FF6, QT6, QG6, UQ6, POST6 |- *.
pose proof POST6 as (ARX'' & LLE6 & WLE6 & CS6 & SIO6 & FR6 & PRS6).
unfold ascratch, spZ, raZ in FR6, PRS6 |- *. rewrite C2 in FR6, PRS6. rewrite C1.
rewrite !unsigned_lit_small in FR6, PRS6 |- * by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia).
assert (NOWN6 : forall a, sp0 - ASTACK <= a < sp0 -> ~ aowned B ly X' a /\ ~ aowned B ly X'' a).
{ intros a Ha. split.
- exact (proj2 (NOWN a Ha)).
- apply (AR_stack_law_ok tfibsegs B ly X'' W6 mem6 md6 a ARX''). clear - Ha Hlo Hhi. unfold spZ, ASTACK in *. unfold sp0 in *. lia. }
assert (AGS6 : forall a, sp0 - 2208 <= a < sp0 -> aview tfibsegs (w_H W6) mem6 a = aview tfibsegs (w_H W5) (ms_mem msC) a).
{ intros a Ha. destruct (NOWN6 a ltac:(clear - Ha; unfold ASTACK; lia)) as [N1 N2]. apply FR6; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia | exact N1 | exact N2 | | intros []].
rewrite (ts_errno _ TB). unfold TFIB_ERRNO, DSTACK. clear - Ha Hlo LB. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *. unfold sp0 in *. lia. }
assert (BV2' : bv_unsigned (ew En6 2) = sp0) by (rewrite (HEn6 2%nat ltac:(cbv; lia)), E2; reflexivity).
assert (HP6 : regs_preserved (ms_regs msC) regs6) by (intros r Hr'; apply CS6; exact Hr').
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?r0 :: ?r1 :: ?r2 :: ?r3 :: ?r4 :: ?rest =>
pose proof (st_ok_after_call tfibsegs 128 En6 ss ms0 regs6 (mrestrict (w_H W6) mem6) (r1 :: r2 :: r3 :: r4 :: nil) 0x356fc HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_drop; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_keep; [apply subregion_refl|]; apply submem_nil)
ltac:(vm_compute; reflexivity) HP6) as HS1;
let rsv := eval vm_compute in (r1 :: r2 :: r3 :: r4 :: nil) in
change (r1 :: r2 :: r3 :: r4 :: nil) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 128 0x356fc) in
change (ss_after_call ss rsv 128 0x356fc) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ ?L -> _ =>
assert (KEPT : Forall (region_kept tfibsegs En6 (mrestrict (w_H W5) (ms_mem msC)) (mrestrict (w_H W6) mem6)) L);
[ repeat apply Forall_cons; try apply Forall_nil;
(apply kept_of_aview2; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite BV2';
[ intros a Ha; apply AGS6; clear - Ha; lia
| intros a Ha; split; [apply AGS6; clear - Ha; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia] ])
| specialize (HS1 KEPT); clear KEPT ]
end.
set (En7 := havoc En6 128 (map (getr regs6) CLOB)) in HS1.
assert (HEn7 : forall k0, (k0 < aHAVf)%nat -> ew En7 k0 = ew E0 k0) by (intros k0 Hk0; subst En7; unfold aHAVf in Hk0; rewrite ew_havoc_old by lia; apply HEn6; exact Hk0).
rewrite <- (restrict_mkst_fx (w_H W6)) in HS1. clear HS. rename HS1 into HS.
unfold cfg_at. rewrite <- (wvb_self md6) at 1.
srr_run_sh tfibtbl_rtF_ok HS.
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) => set (En8 := E) in HS; rename msx into msR end.
assert (HEn8 : forall k0, (k0 < aHAVf)%nat -> ew En8 k0 = ew E0 k0) by (intros k0 Hk0; subst En8; unfold aHAVf in Hk0; rewrite ?ew_havoc_old by lia; apply HEn7; exact Hk0).
assert (FRT : forall x : word, ~ (sp0 - 2208 <= bv_unsigned x < sp0 - 2128) -> ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem msR x = mem6 x).
{ intros x Hx1 Hx2. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg; rewrite ?(HEn7 2%nat ltac:(cbv; lia)), ?E2, ?(HEn7 32%nat ltac:(cbv; lia)), ?EaT in Hrg; unfold w64 in Hrg;
rewrite ?unsigned_lit_small in Hrg by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); clear - Hx1 Hx2 Hrg; unfold ASTACK, t_qc in *; unfold sp0 in *; lia |]).
destruct Hin. }
clear HF HFr.
assert (PRES6 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W6) mem6 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L|L]; [destruct (Z_lt_le_dec a (sp0 - 2208 - DSTACK)) as [L2|L2]|].
2:{ apply PRS6. clear - L L2. lia. }
all: assert (EQa : aview tfibsegs (w_H W6) mem6 a = aview tfibsegs (w_H W5) (ms_mem msC) a)
by (first [ exact (AGS6 a ltac:(clear - Ha L; lia))
| destruct (NOWN6 a Ha) as [M1 M2]; apply FR6; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia | exact M1 | exact M2 | | intros []];
rewrite (ts_errno _ TB); unfold TFIB_ERRNO; clear - Ha L L2 Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, DSTACK in *; unfold sp0 in *; lia ]).
all: pose proof (PRESC a Ha) as P; apply apresent_mbyte in P as [b Hb];
assert (A : aview tfibsegs (w_H W5) (ms_mem msC) a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity);
rewrite <- EQa in A; apply aview_some in A as (b' & Hb' & _);
exact (mbyte_high_apresent (w_H W6) mem6 a b' ltac:(clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia) Hb'). }
assert (PRESR : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W6) (ms_mem msR) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L1|L1]; [|destruct (Z_lt_le_dec a (sp0 - 2176)) as [L2|L2]; [|destruct (Z_lt_le_dec a (sp0 - 2128)) as [L3|L3]; [|destruct (Z_lt_le_dec a (sp0 - 64)) as [L4|L4]]]].
- apply (apresent_same (w_H W6) mem6); [apply FRT; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia); clear - L1; lia | apply PRES6; exact Ha].
- eapply (st_ok_window_apresent (w_H W6) En8 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn8 2%nat ltac:(cbv; lia)), E2; clear - L1 L2; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- eapply (st_ok_window_apresent (w_H W6) En8 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn8 2%nat ltac:(cbv; lia)), E2; clear - L2 L3; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- apply (apresent_same (w_H W6) mem6); [apply FRT; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia); clear - L3 L4; lia | apply PRES6; exact Ha].
- eapply (st_ok_window_apresent (w_H W6) En8 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn8 2%nat ltac:(cbv; lia)), E2; clear - L4 Ha; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia]. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W6 En8); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'.
rreg HS (1%bv : bv 5) Q1f. rewrite (HEn8 1%nat ltac:(cbv; lia)), (AFgm.E1 ly regs ch pa nn hb1 q j1 j2 j3) in Q1f.
srr_norm_model.
exists ly, (ms_regs msR), (ms_mem msR), (with_vm_backing (m_vm_lazy md6) mat' md6). split.
{ unfold cfg_at, raZ, w64. rewrite Q1f, Z_to_bv_bv_unsigned. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
2:{
cbn [snd]. unfold qtight. split; [exact QT6 | split].
- eapply Z.le_trans; [exact QG6|]. rewrite HQG'. subst X. rewrite (AFfl.S'_qglobal S kk z tr). clear - T2. unfold kQuarantineMax in *. lia.
- unfold unq in UQ6. change (ck_n kk') with (ck_n kk) in UQ. subst X. clear - QX1 QX2 UQ QE T3 UQ6. lia. }
assert (AGT : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2208 <= a < sp0 - 2128) -> ~ (sp0 - 64 <= a < sp0) -> aview tfibsegs (w_H W6) (ms_mem msR) a = aview tfibsegs (w_H W6) mem6 a).
{ intros a Ha N1 N2. apply aview_same. apply FRT; rewrite unsigned_lit_small by exact Ha; assumption. }
assert (PNN : p <> PNull).
{ intros Hp0. pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) kk Hk) as [_ CK].
assert (HU0 : ck_user kk = PNull) by (rewrite Hu; exact Hp0). unfold ck_user in HU0. destruct (ck_beg kk); cbn in HU0; try discriminate; destruct CK. }
split; [|split; [apply layout_le_refl | split; [eapply wle_trans; [exact WLE | exact WLE6] | split; [|split; [|split]]]]].
-
apply (AR_frame_law_ok tfibsegs B ly X'' W6 mem6 md6 (ms_mem msR) _ ARX'').
+ intros a Ha HO. apply AGT; [exact Ha| |]; intros Hs; (apply (AR_stack_law_ok tfibsegs B ly X'' W6 mem6 md6 a ARX''); [|exact HO]); clear - Hs Hlo Hhi; unfold spZ, ASTACK in *; unfold sp0 in *; lia.
+ intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W6 x) eqn:Hx; [exact (Hv HN)|]. destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (ms_mem msR x); discriminate|].
destruct (ms_mem msR x) as [|] eqn:E'; [discriminate|]. clear HN. destruct (mem6 x) as [b0|] eqn:EE0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (WDEC a') as [C|[C1' C2']].
* destruct (PRESR a' ltac:(clear - C; unfold ASTACK; lia)) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
* rewrite (FRT x C1' C2') in E'. congruence.
+ reflexivity. + reflexivity. + reflexivity.
+
intros a Ha Hx. unfold w64 in *. apply FRT; rewrite unsigned_lit_small by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia);
intros C; (destruct (PRESR a ltac:(clear - C; unfold ASTACK; lia)) as [Hh _]); unfold w64 in Hh; rewrite Hx in Hh; discriminate.
-
intros r Hr'. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr'. rewrite (ts_tp _ TB) in Htp.
repeat match type of R with _ \/ _ => destruct R as [R|R] end; subst r;
[ cs_case HS HEn8 Htp (2%bv : bv 5) | cs_case HS HEn8 Htp (3%bv : bv 5) | cs_case HS HEn8 Htp (4%bv : bv 5) | cs_case HS HEn8 Htp (8%bv : bv 5) | cs_case HS HEn8 Htp (9%bv : bv 5)
| cs_case HS HEn8 Htp (18%bv : bv 5) | cs_case HS HEn8 Htp (19%bv : bv 5) | cs_case HS HEn8 Htp (20%bv : bv 5) | cs_case HS HEn8 Htp (21%bv : bv 5) | cs_case HS HEn8 Htp (22%bv : bv 5)
| cs_case HS HEn8 Htp (23%bv : bv 5) | cs_case HS HEn8 Htp (24%bv : bv 5) | cs_case HS HEn8 Htp (25%bv : bv 5) | cs_case HS HEn8 Htp (26%bv : bv 5) | cs_case HS HEn8 Htp (27%bv : bv 5) ].
-
clear - SIO SIO6. unfold same_io in SIO, SIO6 |- *.
destruct md, md', md6. cbn in SIO, SIO6 |- *.
intuition congruence.
-
intros a Ha NO NO'' NS NE.
assert (NOX : ~ aowned B ly X a).
{ intros OX. destruct (AFfl.owned_S' B ly S rd0 M kk Hk z tr a OX) as [O|O]; [exact (NO O)|]. apply NE. split; [exact PNN|]. rewrite Hu, <- Enn in O. exact O. }
assert (NOX' : ~ aowned B ly X' a) by (intros O; apply NOX; exact (aowned_same_cf B ly X X' a HCK' HFS' O)).
assert (NS1 : ~ (sp0 - 2208 <= a < sp0 - 2128)) by (intros Hs; apply NS; unfold ascratch; left; clear - Hs; unfold spZ, ASTACK; unfold sp0 in *; lia).
assert (NS2 : ~ (sp0 - 64 <= a < sp0)) by (intros Hs; apply NS; unfold ascratch; left; clear - Hs; unfold spZ, ASTACK; unfold sp0 in *; lia).
rewrite (AGT a Ha NS1 NS2).
rewrite FR6; [| exact Ha | exact NOX' | exact NO'' | | intros []].
2:{ intros [Hs|Hs]; apply NS; unfold ascratch; [left; clear - Hs; unfold spZ, DSTACK, ASTACK in *; unfold sp0 in *; lia | right; first [exact Hs | rewrite (ts_errno _ TB); exact Hs | rewrite (ts_errno _ TB) in Hs; exact Hs] ]. }
rewrite (AGC a Ha NS1 NS2).
rewrite FR; [| exact Ha | exact NOX | exact NOX' | | intros []].
2:{ intros [Hs|Hs]; apply NS; unfold ascratch; [left; clear - Hs; unfold spZ, QSTACK, ASTACK in *; unfold sp0 in *; lia | right; first [exact Hs | rewrite (ts_errno _ TB); exact Hs | rewrite (ts_errno _ TB) in Hs; exact Hs] ]. }
apply AGP; [exact Ha | exact NO | exact NS |]. intros Hb. apply NE. exact (conj PNN Hb).
-
intros a Ha. apply PRESR. unfold spZ in Ha. exact Ha.
Qed.
Theorem afree_drn_arm :
amreal tfibsegs (free p tr S) W (cfg_at tfibsegs 0x5292c regs mem md) (free_leaf tfibsegs B ly S W regs mem md p n).
Proof.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT).
destruct HAR as (M0 & LED & BUD & MW & HSH).
pose proof kk_facts as (Hf & Hk & Hst & Hu & Hr). pose proof FH_ok as FH.
pose proof (AFgm.LYB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as LB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
set (BODY := fun s' : astate =>
(match p with
| PNull => ret ()
| _ => s <- get;;
match find_user (st_chunks s) p with
| Some k0 =>
mcheck match ck_state k0 with CAllocated => true | CQuarantined => false end 201364;;
depot_put tr;;
modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |}) s0);;
enqueue {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |};; maybe_drain
| None => fail (FCheck 201376)
end
end) s').
assert (SPLIT : amreal tfibsegs (BODY s1) W (cfg_at tfibsegs 0x5292c regs mem md) (free_leaf tfibsegs B ly S W regs mem md p n) ->
amreal tfibsegs (free p tr S) W (cfg_at tfibsegs 0x5292c regs mem md) (free_leaf tfibsegs B ly S W regs mem md p n)).
{ intros MAIN. unfold free. cbn [bind ret tick modify mcheck ibind get put set_nev set_internal_inited st_internal_inited].
destruct (st_internal_inited S) eqn:E; cbn [ibind ret modify].
- replace (set_nev (st_nev S + 1) S) with s1; [exact MAIN|]. unfold s1. generalize E. generalize S. clear. intros S0 E0. destruct S0; cbn in E0 |- *. subst. reflexivity.
- exact MAIN. }
apply SPLIT. clear SPLIT. subst BODY. cbn beta.
assert (PNN : p <> PNull).
{ intros Hp0. pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) kk Hk) as [_ CK].
assert (HU0 : ck_user kk = PNull) by (rewrite Hu; exact Hp0). unfold ck_user in HU0. destruct (ck_beg kk); cbn in HU0; try discriminate; destruct CK. }
rewrite (match_nonnull p); [|exact PNN].
cbn [bind get ret ibind]. change (st_chunks s1) with (st_chunks S). rewrite Hf, Hst. cbn [mcheck ret ibind].
change {| ck_beg := ck_beg kk; ck_req := ck_req kk; ck_state := CQuarantined |} with kk'.
unfold depot_put. cbn [bind askz ibind].
apply amreal_ask_depot.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_bind; [exact (AFgb.segA W ly regs mem md ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) (m_vm_materialized md) FH)|].
intros W1 c1 _ HU1.
eapply SRr_bind; [exact (AFgd.segB W ly regs mem md ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH W1 c1 HU1)|].
clear HU1. intros W2 c2 _ (-> & msD & matD & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
rewrite HshD. eapply SRr_bind.
{ assert (AGD : forall a, ~ AFgm.WIN ly regs pa a -> ~ AFgm.IZONE a -> 0 <= a < 2 ^ 64 ->
aview tfibsegs (w_H W) (ms_mem msD) a = aview tfibsegs (w_H W) mem a).
{ intros a Hw Hz Ha. apply aview_same. apply (proj1 MEQD); rewrite unsigned_lit_small by exact Ha; assumption. }
rreg HS (2%bv : bv 5) R2. rewrite (HEn3 2%nat ltac:(cbv; lia)), E2 in R2.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
apply (D1 W ly s1 (ms_regs msD) (ms_mem msD) _ (sp0 - 2112) tr LO IMG s1_wf HU).
-
apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly (aview tfibsegs (w_H W) mem)).
+ exact (proj1 (Forall_forall _ _) (am_const B ly S _ M) c Hc).
+ intros i Hi. destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as (X1 & X2 & X3). apply AGD; assumption.
-
assert (DM : depot_mem_ok B ly S (aview tfibsegs (w_H W) mem)).
{ split; [|split].
- apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells B ly S _ M)). unfold acells. rewrite !in_app_iff. tauto.
- exact (am_depot B ly S _ M).
- pose proof (am_junk B ly S _ M) as J. pose proof (am_areas B ly S _ M) as A. rewrite Forall_forall in J, A.
repeat apply Forall_cons; try apply Forall_nil;
first [ apply J; unfold ajunk; do 2 right; repeat (apply in_or_app; first [ left; inlist | right ]); inlist
| apply A; unfold aareas; repeat (apply in_or_app; first [ left; inlist | right ]); inlist ]. }
eapply (AFfy.depot_mem_ok_agree B ly S s1); [exact (am_wf B ly S _ M) | exact (am_universe B ly S _ M) | reflexivity | | exact DM].
intros a Ha. destruct (DFP_OUT a Ha) as (X1 & X2 & X3). apply AGD; [exact X1 | exact X2 | exact (DFP_RANGE a Ha)].
- rreg HS (10%bv : bv 5) R; rewrite R, (HEn3 2%nat ltac:(cbv; lia)), E2. unfold sp0; f_equal; lia.
- rreg HS (11%bv : bv 5) R; rewrite R, (HEn3 36%nat ltac:(cbv; lia)), EaLEN. reflexivity.
- rreg HS (3%bv : bv 5) R; rewrite R, (HEn3 3%nat ltac:(cbv; lia)), (AFgm.Er ly regs ch pa nn hb1 q j1 j2 j3 3 3%bv eq_refl). exact Hgp.
- rreg HS (4%bv : bv 5) R; rewrite R. rewrite (ts_tp _ TB) in Htp. reflexivity.
- rreg HS (1%bv : bv 5) R; rewrite R. apply YK0s.ret_ok_even. reflexivity.
- intros i Hi. apply (TRQ i Hi).
- unfold sp0. replace (bv_unsigned (getr regs 2) - 2112) with (bv_unsigned (getr regs 2) + (-264) * 8) by lia. rewrite Z_mod_plus_full.
apply (mod0_factor _ 8 2); [lia|]. exact Hal.
- unfold spZ, ASTACK in *; unfold sp0; lia.
-   unfold spZ, ASTACK in *; unfold sp0; lia.
- right. rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). unfold sp0; lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia).
replace (bv_unsigned (getr regs 2) + -2176) with (bv_unsigned (getr regs 2) + (-136) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). unfold spZ, ASTACK, DEP_STK in *; lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). unfold spZ in *; lia.
- intros a Ha. rewrite R2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia).
apply PRESD. unfold DEP_STK, ASTACK, sp0 in *. lia. }
intros W3 c3 _ (-> & z & regs4 & mem4 & mat4 & -> & AOK & HP4 & Hfr4 & Hpr4 & DEPOK & HC4). srr_norm_model.
apply SRr_ret. exists z. split; [exact AOK|].
rreg HS (1%bv : bv 5) Q1r. rreg HS (2%bv : bv 5) Q2.
rewrite Q2, (HEn3 2%nat ltac:(cbv; lia)), E2 in Hfr4.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
rewrite unsigned_lit_small in Hfr4 by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). fold sp0 in Hfr4.
assert (Hfr4' : forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) -> ~ depot_footprint B ly (bv_unsigned x) -> mem4 x = ms_mem msD x).
{ intros x Hx Hd. apply Hfr4; [clear - Hx; lia | exact Hd]. }
assert (DZ : forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) -> ~ AFgm.DZONE ly (bv_unsigned x) -> mem4 x = ms_mem msD x).
{ intros x Hx Hd. apply Hfr4'; [exact Hx|]. intros Hf'. apply Hd. exact (proj2 (proj2 (DFP_OUT _ Hf'))). }
assert (TAIL : let sd := depot_after z tr s1 in
amreal tfibsegs ((modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) kk') s0);; enqueue kk';; maybe_drain) sd)
W (mkCfg (mkst regs4 (getr (ms_regs msD) 1) mem4 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat4 md))
(free_leaf tfibsegs B ly S W regs mem md p n)).
{ cbn zeta. apply amreal_mbind. cbn [modify amreal]. apply SRr_ret. cbn [fst snd].
change (set_chunks (upd_chunk (st_chunks (depot_after z tr s1)) kk') (depot_after z tr s1)) with (AFfl.S' S kk z tr).
set (X := AFfl.S' S kk z tr).
apply amreal_mbind. cbn beta.
rewrite Q1r. apply amreal_after_SRr. eapply SRr_mono.
{ apply (AFgf.segCm1 W ly regs mem md ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH msD E3 regs4 mem4 mat4).
split; [exact HshD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact HP4|]. split; [exact DZ|]. split; [exact Hpr4|]. split; [exact MEQD | exact PRESD]. }
intros W4 c4 _ (-> & msE & matE & E5 & -> & HshE & HEn5 & HS5 & EQE & PRESE).
pose proof (ENQ_PRE z msD mem4 msE matE E5 AOK MEQD Hfr4' DEPOK HC4 HshE HEn5 HS5 EQE PRESE) as EP.
pose proof (proj1 EP) as ARX.
rewrite HshE at 1. change (mkCfg (mkst (ms_regs msE) (w64 0x357d0) (ms_mem msE) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) matE md))
with (cfg_at tfibsegs A_Enqueue (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) matE md)).
eapply amreal_mono; [| exact (Q1 ly X W (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) matE md) kk' ltac:(subst X; rewrite (AFfl.S'_qthread S kk z tr); reflexivity) EP)].
intros [[] X'] W5 c5 (regs' & mem' & md' & nb & -> & POST & HQ' & Hnb & HCK' & HQG' & HFS'). cbn [fst snd] in HQ', POST, HCK', HQG', HFS' |- *.
rewrite (maybe_drain_drain X').
2:{ rewrite HQ'. subst X. rewrite (AFfl.S'_qthread S kk z tr) in Hnb |- *.
pose proof DRAIN as DR. change (st_qthread S) with q in DR |- *.
destruct nb; rewrite Hnb in DR; cbn [qc_push qc_bytes]; change (ck_n kk') with (ck_n kk); rewrite <- Enn; clear - DR; lia. }
rreg HS5 (1%bv : bv 5) Q1e.
unfold raZ. rewrite Q1e. rewrite unsigned_lit_small by lia.
apply (TAILD z msE matE E5 W5 regs' mem' md' X' nb AOK HshE HEn5 HS5 PRESE ARX POST HQ' Hnb HCK' HQG' HFS').
intros a Ha NO NS NB. apply (MID_AG msD mem4 (ms_mem msE) MEQD Hfr4' EQE a Ha). intros HD.
destruct (AFfl.D_owned B TB ly S rd0 (aview tfibsegs (w_H W) (ms_mem msE)) M kk hb1 Hk HB1 z tr sp0 (conj Hlo Hhi) IMG (proj1 ARX) a (proj1 Ha) HD) as [O|[O|O]].
- exact (NO O).
- destruct (AFfl.owned_S' B ly S rd0 M kk Hk z tr a O) as [O'|O']; [exact (NO O')|]. apply NB. rewrite Hu, <- Enn in O'. exact O'.
- apply NS. unfold ascratch. left. exact O. }
destruct AOK as [-> | [-> _]].
- cbn [Z.eqb ret ibind]. exact TAIL.
- cbn [Z.eqb bind get ret ibind].
destruct (depot_ids s1 + 1 <? kDepotIdsPerBlock); cbn [mcheck ret ibind]; [|exact I].
destruct (kStartFramesMax + depot_frames s1 + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock); cbn [mcheck ret put ibind]; [|exact I].
exact TAIL.
Qed.
End e.
Theorem afree_drn : forall B, TfibSyms B -> forall ly S W regs mem md p n ch,
acall_pre tfibsegs B ly S W regs mem md ch -> In (p, n) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
In (call_trace ly 0x52a6c regs ch) (as_universe B) ->
kQuarantineCacheMax < qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) ->
tfib_ialloc_spec -> tfib_unwind_spec -> tfib_depot_spec B -> tfib_enqueue_spec_nb B (need_new_batch (st_qthread S)) -> tfib_drain_spec B ->
ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (free p (call_trace ly 0x52a6c regs ch) S) W (cfg_at tfibsegs 0x5292c regs mem md) (free_leaf tfibsegs B ly S W regs mem md p n).
Proof.
intros B TB ly S W regs mem md p n ch PRE HBLK HA0 HU DR IA1 U1 D1 Q1 D0 HTSD.
eapply afree_drn_arm; eassumption.
Qed.
End d.
