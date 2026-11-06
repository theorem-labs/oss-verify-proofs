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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0r YF0w YF1p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF19 YF0o YF0s YF2e YF07.
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
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section g. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : drain_pre B ly X W regs mem md.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation tq := (st_qthread X).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).
Lemma M : ARm B ly X rd0. Proof. img_exact (proj1 (proj1 PRE)). Qed.
Let WF : Wf (as_universe B) X := am_wf B ly X rd0 M.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma HTB : kQuarantineCacheMax < qc_bytes tq. Proof. img_exact (proj1 (proj2 PRE)). Qed.
Lemma HQL : qloose X. Proof. img_exact (proj1 (proj2 (proj2 PRE))). Qed.
Lemma HSP : ly_stk_lo ly + DSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & Hlo & Hhi & _). unfold spZ in *. unfold sp0. img_lia. Qed.
Lemma AQ : A_QUAR = as_inst B + o_quar. Proof. rewrite (ts_inst _ TB). img_refl. Qed.
Lemma IMG : img_cover ly.
Proof. img_exact (img_cover_of_ledger ly X md (proj1 (proj2 (proj1 PRE)))). Qed.
Local Notation GSZv := (YF2e.GSZv gq).
Local Notation GFv := (YF2e.GFv ly gq).
Local Notation GLv := (YF2e.GLv ly gq).
Local Notation GBv := (YF2e.GBv gq).
Local Notation TSZv := (YF2e.TSZv tq).
Local Notation TFv := (YF2e.TFv ly tq).
Local Notation TLv := (YF2e.TLv ly tq).
Local Notation TBv := (YF2e.TBv tq).
Local Notation E0 := (YF2e.E0 ly regs gq tq).
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfx_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfxsegs m0 a w x.
Proof. intros a w x E. img_exact (tfx_const_lookup B TB ly X H0 mem a w x M E). Qed.
Lemma cell_state : forall c e (w : nat) e', In c (acells B ly X) -> c = ACell e w (AV e') -> val_mem tfxsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros c e w e' Hin ->. img_apply (cell_holds_val_mem B ly H0 mem e w e'). img_exact (proj1 (Forall_forall _ _) (am_cells B ly X rd0 M) _ Hin).
Qed.
Lemma cell_stateZ : forall c e (w : nat) x, In c (acells B ly X) -> c = ACell e w (AV (ANum x)) -> val_mem tfxsegs m0 (aeval B ly e) w x.
Proof. intros c e w x Hin E. img_exact (cell_state c e w (ANum x) Hin E). Qed.
Lemma vis_range : forall e len i, In (e, len) (ajunk B ly X) \/ In (e, len) (aareas X) \/ In (e, len) (aclient X) ->
0 <= i < len -> rd0 (aeval B ly e + i) <> None.
Proof.
intros e len i Hin Hi. destruct Hin as [Hin|[Hin|Hin]].
- img_exact (proj1 (Forall_forall _ _) (am_junk B ly X rd0 M) _ Hin i Hi).
- img_exact (proj1 (Forall_forall _ _) (am_areas B ly X rd0 M) _ Hin i Hi).
- img_exact (proj1 (Forall_forall _ _) (am_client B ly X rd0 M) _ Hin i Hi).
Qed.
Lemma rootT_vals : val_mem tfxsegs m0 (T + t_qc) 8 TSZv /\ val_mem tfxsegs m0 (T + t_qc + 8) 8 TFv /\ val_mem tfxsegs m0 (T + t_qc + 16) 8 TLv /\ val_mem tfxsegs m0 (T + t_qc + 24) 8 TBv.
Proof.
assert (IN : forall c, In c (qc_cells (AT t_qc) tq) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. img_apply in_app_iff. left. img_exact Hc. }
unfold YF2e.TSZv, YF2e.TFv, YF2e.TLv, YF2e.TBv. splits.
- img_apply (cell_stateZ _ (AT t_qc) 8 _ (IN _ ltac:(img_try (unfold qc_cells; left; img_refl))) eq_refl).
- replace (T + t_qc + 8) with (aeval B ly (aoff (AT t_qc) 8)) by (img_try (cbn; img_lia)).
replace (match Tq with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match Tq with [] => ANum 0 | b :: _ => batch_exp b end)) by (img_try (destruct Tq; img_refl)).
img_apply (cell_state _ _ 8 _ (IN _ ltac:(img_try (unfold qc_cells; right; left; img_refl))) eq_refl).
- replace (T + t_qc + 16) with (aeval B ly (aoff (AT t_qc) 16)) by (img_try (cbn; img_lia)).
replace (match rev Tq with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match rev Tq with [] => ANum 0 | b :: _ => batch_exp b end)) by (img_try (destruct (rev Tq); img_refl)).
img_apply (cell_state _ _ 8 _ (IN _ ltac:(img_try (unfold qc_cells; right; right; left; img_refl))) eq_refl).
- replace (T + t_qc + 24) with (aeval B ly (aoff (AT t_qc) 24)) by (img_try (cbn; img_lia)).
img_apply (cell_stateZ _ _ 8 _ (IN _ ltac:(img_try (unfold qc_cells; do 3 right; left; img_refl))) eq_refl).
Qed.
Lemma rootG_vals : val_mem tfxsegs m0 (A_QUAR + 160) 8 GSZv /\ val_mem tfxsegs m0 (A_QUAR + 168) 8 GFv /\ val_mem tfxsegs m0 (A_QUAR + 176) 8 GLv /\ val_mem tfxsegs m0 (A_QUAR + 184) 8 GBv.
Proof.
assert (IN : forall c, In c (qc_cells (AInst o_q_size) gq) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. img_apply in_app_iff. right. img_exact Hc. }
rewrite AQ. unfold YF2e.GSZv, YF2e.GFv, YF2e.GLv, YF2e.GBv. splits.
- replace (as_inst B + o_quar + 160) with (aeval B ly (AInst o_q_size)) by (img_try (cbn; unfold o_quar, o_q_size; img_lia)).
img_apply (cell_stateZ _ (AInst o_q_size) 8 _ (IN _ ltac:(img_try (unfold qc_cells; left; img_refl))) eq_refl).
- replace (as_inst B + o_quar + 168) with (aeval B ly (aoff (AInst o_q_size) 8)) by (img_try (cbn; unfold o_quar, o_q_size; img_lia)).
replace (match G with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match G with [] => ANum 0 | b :: _ => batch_exp b end)) by (img_try (destruct G; img_refl)).
img_apply (cell_state _ _ 8 _ (IN _ ltac:(img_try (unfold qc_cells; right; left; img_refl))) eq_refl).
- replace (as_inst B + o_quar + 176) with (aeval B ly (aoff (AInst o_q_size) 16)) by (img_try (cbn; unfold o_quar, o_q_size; img_lia)).
replace (match rev G with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match rev G with [] => ANum 0 | b :: _ => batch_exp b end)) by (img_try (destruct (rev G); img_refl)).
img_apply (cell_state _ _ 8 _ (IN _ ltac:(img_try (unfold qc_cells; right; right; left; img_refl))) eq_refl).
- replace (as_inst B + o_quar + 184) with (aeval B ly (aoff (AInst o_q_size) 24)) by (img_try (cbn; unfold o_quar, o_q_size; img_lia)).
img_apply (cell_stateZ _ _ 8 _ (IN _ ltac:(img_try (unfold qc_cells; do 3 right; left; img_refl))) eq_refl).
Qed.
Lemma mutex_vals : forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfxsegs m0 a = Some (Z_to_bv 8 0).
Proof.
intros a Ha.
assert (C1 : val_mem tfxsegs m0 (as_inst B + o_q_cmutex) 1 0).
{ img_apply (cell_stateZ (z1 (AInst o_q_cmutex) 0) (AInst o_q_cmutex) 1 0); [|img_refl]. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. left. img_refl. }
assert (C2 : val_mem tfxsegs m0 (as_inst B + o_q_rmutex) 1 0).
{ img_apply (cell_stateZ (z1 (AInst o_q_rmutex) 0) (AInst o_q_rmutex) 1 0); [|img_refl]. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; left. img_refl. }
assert (C3 : val_mem tfxsegs m0 (0xa6eca + D_10c0) 2 0) by (img_try (img_apply cell_lit; (img_case; vm_compute); img_refl)).
rewrite AQ in Ha. unfold o_quar, o_q_cmutex, o_q_rmutex in *. rewrite (ts_inst _ TB) in *. unfold TFX_INST in *.
assert (CASES : a = (682840 + D_10c0) + 880 \/ a = (682840 + D_10c0) + 881 \/ a = (683722 + D_10c0) + Z.of_nat 0 \/ a = (683722 + D_10c0) + Z.of_nat 1) by img_lia.
destruct CASES as [-> |[-> |[-> | ->]]].
- pose proof (C1 0%nat ltac:(img_lia)) as E. rewrite Z.add_0_r in E. img_exact E.
- pose proof (C2 0%nat ltac:(img_lia)) as E. rewrite Z.add_0_r in E. img_exact E.
- img_exact (C3 0%nat ltac:(img_lia)).
- img_exact (C3 1%nat ltac:(img_lia)).
Qed.
Lemma const_vals : val_mem tfxsegs m0 (A_QUAR + 64) 8 kQuarantineMax /\ val_mem tfxsegs m0 (A_QUAR + 72) 8 kQuarantineMin.
Proof. split; (img_apply cell_lit; (img_case; vm_compute); img_refl). Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
(forall b2, In b2 (all_batches X) -> ly_prim ly <= SB + b_self b2 /\ SB + b_self b2 + kBatchBytes <= SB + kSpaceSize) /\
4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd.
Proof. img_exact (YF0s.HIGH B ly X rd0 M sp0 HSP IMG). Qed.
Lemma batch_facts : forall b2, In b2 (all_batches X) ->
ly_prim ly <= SB + b_self b2 /\ SB + b_self b2 + kBatchBytes <= SB + kSpaceSize /\ (SB + b_self b2) mod 8192 = 0 /\
kHighMemBeg <= SB + b_self b2 /\ SB + b_self b2 + kBatchBytes <= ASAN_CEIL /\
(forall a, SB + b_self b2 <= a < SB + b_self b2 + kBatchBytes -> apresent H0 mem a) /\ kBatchBytes <= b_bytes b2.
Proof.
intros b2 Hb2. pose proof HI as (P1 & P2 & _ & _ & _ & _ & S1 & S2 & HB & _). destruct (HB b2 Hb2) as [L1 L2].
destruct (YF0s.batch_geom B ly X rd0 M sp0 HSP b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _). unfold YF0s.addr in Eb.
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5).
splits; try img_lia.
- rewrite Eb. unfold kBatchBytes in Ab. img_apply Z.mod_divide; [img_lia|]. apply Z.mod_divide in R3 as [c Hc]; [|img_lia]. apply Z.mod_divide in Ab as [c' Hc']; [|img_lia]. exists (8 * c + c'). img_lia.
- intros a Ha. replace a with (aeval B ly (ASp (region_off kBatchClass)) + (xb + (a - (SB + b_self b2)))) by (img_try (cbn [aeval]; unfold region_base in Eb; img_lia)).
img_apply vis_apresent; [img_try (cbn [aeval]; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, region_base, TFX_IMG_END, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; img_lia)|].
img_apply (vis_range (ASp (region_off kBatchClass)) (rg_mapped_user (reg X kBatchClass))); [img_try (right; left) | img_try (unfold kBatchBytes in *; img_lia)].
unfold aareas. rewrite !in_app_iff. left. img_apply in_flat_map. exists kBatchClass. split; [img_try (img_apply In_zseq; unfold kBatchClass; img_lia) | img_try (left; img_refl)].
- img_exact (YF0s.b_bytes_lb B ly X rd0 M b2 Hb2).
Qed.
Lemma Tq_ne : Tq <> []. Proof. img_exact (YF0s.Tq_ne B ly X rd0 M HTB). Qed.
Lemma g_facts : 0 <= GBv <= 2 ^ 30 /\ GSZv < 2 ^ 40 /\ 0 <= GFv < ASAN_CEIL /\ GFv mod 8192 = 0 /\ 0 <= GLv < ASAN_CEIL /\ GLv mod 8192 = 0 /\ GBv = sum_bytes G.
Proof.
pose proof HQL as (Q1 & Q2 & Q3). pose proof (wq_bytes_g _ (wf_quarantine _ _ _ _ _ WF)) as QE.
pose proof (YF0s.sum_bytes_lb B ly X rd0 M G ltac:(img_try (intros y Hy; unfold all_batches; img_apply in_app_iff; right; img_exact Hy))) as S1.
pose proof (YG0s.batches_len_fuel _ _ _ _ X WF HQL) as BE  . unfold all_batches in BE. rewrite length_app in BE.
unfold YF2e.GBv, YF2e.GSZv, YF2e.GFv, YF2e.GLv, EV_MAX in *. splits; try img_lia.
- destruct G as [|b t] eqn:Eq; [img_lia|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; right; rewrite Eq; left; img_refl))) as (_ & _ & _ & L4 & _). unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in L4. img_lia.
- destruct G as [|b t] eqn:Eq; [img_try (ceil; unfold ASAN_CEIL; img_lia)|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; right; rewrite Eq; left; img_refl))) as (_ & _ & _ & _ & L5 & _). unfold kBatchBytes in L5. img_lia.
- destruct G as [|b t] eqn:Eq; [img_refl|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; right; rewrite Eq; left; img_refl))) as (_ & _ & L3 & _). img_exact L3.
- destruct (rev G) as [|b t] eqn:Eq; [img_lia|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; right; rewrite <- (rev_involutive G), Eq; cbn; img_apply in_app_iff; right; left; img_refl))) as (_ & _ & _ & L4 & _). unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in L4. img_lia.
- destruct (rev G) as [|b t] eqn:Eq; [img_try (ceil; unfold ASAN_CEIL; img_lia)|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; right; rewrite <- (rev_involutive G), Eq; cbn; img_apply in_app_iff; right; left; img_refl))) as (_ & _ & _ & _ & L5 & _). unfold kBatchBytes in L5. img_lia.
- destruct (rev G) as [|b t] eqn:Eq; [img_refl|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; right; rewrite <- (rev_involutive G), Eq; cbn; img_apply in_app_iff; right; left; img_refl))) as (_ & _ & L3 & _). img_exact L3.
Qed.
Lemma t_facts : kQuarantineCacheMax < TBv <= 2 ^ 29 /\ 1 <= TSZv < 2 ^ 40 /\ 0 <= TFv < ASAN_CEIL /\ TFv mod 8192 = 0 /\ 0 <= TLv < ASAN_CEIL /\ TLv mod 8192 = 0 /\ TBv = sum_bytes Tq.
Proof.
pose proof HQL as (Q1 & Q2 & Q3). pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QE. pose proof HTB as TBX. pose proof Tq_ne as NE0.
pose proof (YG0s.batches_len_fuel _ _ _ _ X WF HQL) as BE  . unfold all_batches in BE. rewrite length_app in BE.
unfold YF2e.TBv, YF2e.TSZv, YF2e.TFv, YF2e.TLv, EV_MAX in *. splits; try img_lia.
- destruct Tq; [img_try (exfalso; img_exact (NE0 eq_refl)) | img_try (cbn [length]; img_lia)].
- destruct Tq as [|b t] eqn:Eq; [img_lia|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; left; rewrite Eq; left; img_refl))) as (_ & _ & _ & L4 & _). unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in L4. img_lia.
- destruct Tq as [|b t] eqn:Eq; [img_try (ceil; unfold ASAN_CEIL; img_lia)|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; left; rewrite Eq; left; img_refl))) as (_ & _ & _ & _ & L5 & _). unfold kBatchBytes in L5. img_lia.
- destruct Tq as [|b t] eqn:Eq; [img_refl|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; left; rewrite Eq; left; img_refl))) as (_ & _ & L3 & _). img_exact L3.
- destruct (rev Tq) as [|b t] eqn:Eq; [img_lia|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; left; rewrite <- (rev_involutive Tq), Eq; cbn; img_apply in_app_iff; right; left; img_refl))) as (_ & _ & _ & L4 & _). unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in L4. img_lia.
- destruct (rev Tq) as [|b t] eqn:Eq; [img_try (ceil; unfold ASAN_CEIL; img_lia)|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; left; rewrite <- (rev_involutive Tq), Eq; cbn; img_apply in_app_iff; right; left; img_refl))) as (_ & _ & _ & _ & L5 & _). unfold kBatchBytes in L5. img_lia.
- destruct (rev Tq) as [|b t] eqn:Eq; [img_refl|]. destruct (batch_facts b ltac:(img_try (unfold all_batches; img_apply in_app_iff; left; rewrite <- (rev_involutive Tq), Eq; cbn; img_apply in_app_iff; right; left; img_refl))) as (_ & _ & L3 & _). img_exact L3.
Qed.
Lemma glast_facts : forall lb initr, rev G = lb :: initr ->
In lb (all_batches X) /\ GLv = SB + b_self lb /\ ly_prim ly <= GLv /\ GLv + kBatchBytes <= SB + kSpaceSize /\ GLv mod 8192 = 0 /\
val_mem tfxsegs m0 GLv 8 0 /\ (forall a, GLv <= a < GLv + 8 -> apresent H0 mem a).
Proof.
intros lb initr Hrev.
assert (E0 : G = rev initr ++ [lb]) by (img_try (rewrite <- (rev_involutive G), Hrev; img_refl)).
assert (Hin : In lb (all_batches X)) by (img_try (unfold all_batches; img_apply in_app_iff; right; rewrite E0; img_apply in_app_iff; right; left; img_refl)).
assert (EQ : GLv = SB + b_self lb) by (img_try (unfold YF2e.GLv; rewrite Hrev; img_refl)).
destruct (batch_facts lb Hin) as (L1 & L2 & L3 & L4 & L5 & L6 & _). rewrite EQ. splits; try assumption; try img_refl.
- assert (IN : In (c8 (batch_exp lb) (ANum 0)) (acells B ly X)).
{ unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. img_apply in_app_iff. right. unfold qc_cells. do 4 right.
img_apply In_batch_cells. exists (length (rev initr)), lb. rewrite E0. split; [img_try (rewrite nth_error_app2 by img_lia; rewrite Nat.sub_diag; img_refl)|].
unfold batch_own_cells. left. rewrite next_exp_app_new. img_refl. }
img_exact (cell_state _ (batch_exp lb) 8 (ANum 0) IN eq_refl).
- intros a Ha. img_apply L6. unfold kBatchBytes. img_lia.
Qed.
Lemma E2 : ew E0 2 = getr regs 2. Proof. img_exact (YF2e.E2 ly regs gq tq). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. img_refl. Qed.
Lemma EqSB : ew E0 33 = w64 SB. Proof. img_refl. Qed.
Lemma EqGSZ : ew E0 34 = w64 GSZv. Proof. img_refl. Qed.
Lemma EqGF : ew E0 35 = w64 GFv. Proof. img_refl. Qed.
Lemma EqGL : ew E0 36 = w64 GLv. Proof. img_refl. Qed.
Lemma EqGB : ew E0 37 = w64 GBv. Proof. img_refl. Qed.
Lemma EqTSZ : ew E0 38 = w64 TSZv. Proof. img_refl. Qed.
Lemma EqTF : ew E0 39 = w64 TFv. Proof. img_refl. Qed.
Lemma EqTL : ew E0 40 = w64 TLv. Proof. img_refl. Qed.
Lemma EqTB : ew E0 41 = w64 TBv. Proof. img_refl. Qed.
Lemma chunk_lit : forall a (w : BinNums.N) x, val_mem tfxsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 0 (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (rewrite Z.add_0_l; img_exact Hm)]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k0 d x, ew E0 k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfxsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal w (SOff k0 d))).
Proof.
intros base a w k0 d x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfxsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfxsegs m0 o.
Proof. intros a w v o Hv Ho Ha. img_apply vis_writable_off; [img_try (img_exact Ha)|]. replace o with (a + (o - a)) by img_lia. eapply val_mem_vis; [img_try (img_exact Hv) | img_lia]. Qed.
Ltac offw := first [ img_lia | img_apply off_img_high; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, kHighMemBeg in *; ceil; unfold ASAN_CEIL in *; img_lia
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI)))); unfold kThreadObjSize, t_qc in *; img_lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8 := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Lemma REG0_ok : Forall (region_ok tfxsegs E0 m0) YF2e.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2). pose proof HSP as [S1 S2].
pose proof rootT_vals as (V1 & V2 & V3 & V4). pose proof rootG_vals as (U1 & U2 & U3 & U4). pose proof const_vals as [K1 K2].
pose proof g_facts as (Ga & Gb & Gc & Gd & Ge & Gf & _). pose proof t_facts as (Ta & Tb & Tc & Td & Te & Tf & _).
assert (Gc0 : 0 <= GSZv) by (img_try (unfold YF2e.GSZv; clear; img_lia)).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, DSTACK, kQuarantineCacheMax, kLowMemEnd in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, S1, S2, Ga, Gc, Ge, Ta, Tc, Te, hI1, hI2.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
pose proof AQ as EAQ. unfold o_quar in EAQ.
unfold YF2e.REG0, YF2e.R_QW, YF2e.R_QG, YF2e.R_QT, flit8.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E0 m0 2 sp0 (- 80)); [img_try (rewrite E2; img_refl) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable; [img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia) | img_try (img_apply HPRES; clear -Ha; unfold DSTACK in *; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. split; [img_try (rewrite EAQ; img_lia)|]. split; [img_try (rewrite EAQ; img_lia)|]. split.
{ intros o Ho. img_apply rw_writable. rewrite EAQ, (ts_inst _ TB) in Ho. unfold TFX_INST in Ho. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_lit; [| img_try (cbn; img_lia) | img_try (cbn; img_lia)]. intros k Hk. rewrite le_byte_zero. img_apply mutex_vals. img_lia. }
img_apply Forall_cons.
{   reg_intro. split; [img_try (rewrite EAQ; img_lia)|]. split; [img_try (rewrite EAQ; img_lia)|]. split.
{ intros o Ho. img_apply rw_writable. rewrite EAQ, (ts_inst _ TB) in Ho. unfold TFX_INST in Ho. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
- img_apply (chunk_atom 0 _ 8 34%nat 0 GSZv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact U1) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom 0 _ 8 35%nat 0 GFv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact U2) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom 0 _ 8 36%nat 0 GLv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact U3) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom 0 _ 8 37%nat 0 GBv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_l; img_exact U4) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_qc in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 88); [img_try (img_apply (val_mem_writable _ _ _ _ V1)) | img_try (destruct (Z_lt_le_dec o 96); [img_apply (val_mem_writable _ _ _ _ V2) | destruct (Z_lt_le_dec o 104); [img_apply (val_mem_writable _ _ _ _ V3) | img_apply (val_mem_writable _ _ _ _ V4)]])];
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
- img_apply (chunk_atom _ _ 8 38%nat 0 TSZv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (img_exact V1) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 8 39%nat 0 TFv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V2 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 8 40%nat 0 TLv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V3 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 8 41%nat 0 TBv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V4 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons.
{   reg_intro. split; [img_try (rewrite EAQ; img_lia)|]. split; [img_try (rewrite EAQ; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_lit; [img_try (img_exact K1) | img_try (unfold kQuarantineMax; cbn; img_lia) | img_try (cbn; img_lia)]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
{   reg_intro. split; [img_try (rewrite EAQ; img_lia)|]. split; [img_try (rewrite EAQ; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_lit; [img_try (img_exact K2) | img_try (unfold kQuarantineMin; cbn; img_lia) | img_try (cbn; img_lia)]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 YF2e.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _ & _ & _ & hI1 & hI2). pose proof HSP as [S1 S2].
pose proof (YF0s.SX B ly X rd0 M 2 8 _ _ eq_refl eq_refl ltac:(img_lia)) as DTS. unfold zdisjoint in DTS. cbn [fst snd] in DTS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)). pose proof AQ as EAQ. unfold o_quar in EAQ.
img_apply pairwise_disjoint_of_extents. unfold YF2e.REG0, YF2e.R_QW, YF2e.R_QG, YF2e.R_QT, flit8, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
pose proof (ts_inst _ TB) as EI. unfold TFX_INST in EI.
rewrite E2, EqT. unfold w64. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, DSTACK, kLowMemEnd in *.
fold sp0. rewrite !unsigned_lit_small by img_lia. rewrite EAQ.
unfold t_qc. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in hT1.
repeat split; first [clear hT1; img_lia | clear - hT1 EI CR0; img_lia].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms YF2e.FFD).
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & _). pose proof HSP as [S1 S2].
destruct PRE as (_ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof g_facts as (Ga & Gb & Gc & Gd & Ge & Gf & _). pose proof t_facts as (Ta & Tb & Tc & Td & Te & Tf & _).
assert (Gc0 : 0 <= GSZv) by (img_try (unfold YF2e.GSZv; clear; img_lia)).
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, DSTACK, kQuarantineCacheMax in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, S1, S2, Ga, Gc, Ge, Ta, Tc, Te.
assert (E2' : ew E0 2 = w64 sp0) by (img_try (rewrite E2; unfold sp0, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
cbn [YF2e.FFD f_atoms atoms_ok]. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DSTACK.
split. { img_apply (AF 2%nat sp0); [img_try (img_exact E2')| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 Hal; first [img_lia | img_change (2 ^ 4) with 16; img_exact Hal]. }
split. { img_apply (AF 32%nat T); [img_try (img_exact EqT)| | | |]. all: clear - CR0 hT1 hT2 TAL; first [img_lia | img_exact TAL]. }
split. { img_apply (AF 33%nat SB); [img_try (img_exact EqSB)| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [img_lia | img_exact SAL]. }
split. { img_apply (AF 34%nat GSZv); [img_try (img_exact EqGSZ)| | | |]. all: clear - CR0 Gb Gc0; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 35%nat GFv); [img_try (img_exact EqGF)| | | |]. all: clear - CR0 Gc Gd; first [img_lia | img_change (2 ^ 13) with 8192; img_exact Gd]. }
split. { img_apply (AF 36%nat GLv); [img_try (img_exact EqGL)| | | |]. all: clear - CR0 Ge Gf; first [img_lia | img_change (2 ^ 13) with 8192; img_exact Gf]. }
split. { img_apply (AF 37%nat GBv); [img_try (img_exact EqGB)| | | |]. all: clear - CR0 Ga; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 38%nat TSZv); [img_try (img_exact EqTSZ)| | | |]. all: clear - CR0 Tb; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 39%nat TFv); [img_try (img_exact EqTF)| | | |]. all: clear - CR0 Tc Td; first [img_lia | img_change (2 ^ 13) with 8192; img_exact Td]. }
split. { img_apply (AF 40%nat TLv); [img_try (img_exact EqTL)| | | |]. all: clear - CR0 Te Tf; first [img_lia | img_change (2 ^ 13) with 8192; img_exact Tf]. }
split; [|img_try (img_exact I)]. { img_apply (AF 41%nat TBv); [img_try (img_exact EqTB)| | | |]. all: clear - CR0 Ta; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
Qed.
Lemma SEED_ok : st_ok tfxsegs E0 YF2e.SS0 (restrict (w_H W) (mkst regs (w64 (0x33530 + D_150)) mem (seg_rom tfxsegs))).
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1 & Ha2). rewrite (ts_tp _ TB) in Htp.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & _). ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in hT1, hT2.
rewrite restrict_mkst_fx. unfold YF2e.SS0, YF2e.SR0, sr_set. cbn [bv_eqb]. unfold YF2e.E0, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; img_exact Htp] | intros XX; discriminate | cbn [sv_denot]; img_exact Ha0] | intros XX; discriminate |]) | img_try (intros XX; discriminate) |].
+ cbn [sv_denot]. fold (YF2e.E0 ly regs gq tq). rewrite EqT, Ha1. unfold w64. rewrite Zbv_add_unsigned. img_refl.
+ cbn [sv_denot]. fold (YF2e.E0 ly regs gq tq). rewrite EqT, Ha2. unfold w64. rewrite Zbv_add_unsigned. img_refl.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0_ok.
- img_exact PAIRS_ok.
- split; [img_try (img_exact FACTS_ok) | img_try (split; img_exact I)].
Qed.
Theorem FH_ok : YF2e.free_hyps W ly regs mem gq tq.
Proof.
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof g_facts as (Ga & Gb & Gc & Gd & Ge & Gf & _). pose proof t_facts as (Ta & Tb & Tc & Td & Te & Tf & _).
constructor.
- img_exact LO.
- img_exact IMG.
- rewrite (ts_tp _ TB) in Htp. img_exact Htp.
- img_exact Hra.
- img_exact Hra4.
- split; [img_try (img_exact Hlo) | img_try (img_exact Hhi)].
- img_exact Hal.
- img_exact HPRES.
- clear - Ga Gb Gc Gd. splits; first [assumption | img_lia].
- clear - Ta Tb Tc Td Te Tf. splits; first [assumption | img_lia].
- intros lb initr Hrev. destruct (glast_facts lb initr Hrev) as (_ & _ & L1 & L2 & L3 & L4 & L5). splits; assumption.
- img_exact SEED_ok.
Qed.
Local Notation WINd := (YF2e.WIN ly regs gq).
Lemma GEO :
(ly_prim ly + kPrimResvSize <= T \/ T + kThreadObjSize <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_C ly \/ ly_C ly + 256 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_D ly \/ ly_D ly + 4096 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_prim ly) /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\
(T + kThreadObjSize <= ly_D ly \/ ly_D ly + 4096 <= T) /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= T) /\
(ly_C ly + 256 <= ly_D ly \/ ly_D ly + 4096 <= ly_C ly) /\
(ly_C ly + 256 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_C ly) /\
(ly_D ly + 4096 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_D ly) /\
zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096.
Proof.
pose proof (lo_disj ly LO) as HD.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(img_try (clear; img_lia)) (Forall_nth_f _ _ 6 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
pose proof (zone3_intro ly (ly_D ly) 4096 IMG ltac:(img_try (clear; img_lia)) (Forall_nth_f _ _ 7 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 7 1 _ _ HD eq_refl eq_refl)) as ZD.
unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _ & DT & _ & _ & _ & DC & DD & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [PD DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [TD DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DC as [CD DC]. apply Forall_cons_iff in DC as [CSTK _]. apply Forall_cons_iff in DD as [DSTK _].
unfold zdisjoint in PT, PC, PD, PSTK, TC, TD, TSTK, CD, CSTK, DSTK. cbn [fst snd] in PT, PC, PD, PSTK, TC, TD, TSTK, CD, CSTK, DSTK.
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
Lemma WIN_zone : forall a, WINd a ->
(sp0 - 80 <= a < sp0) \/ (as_inst B + o_q_cmutex <= a < as_inst B + o_q_cmutex + 4 \/ as_inst B + o_q_size <= a < as_inst B + o_q_size + 32) \/
(T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize).
Proof.
intros a Hw. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & _). pose proof AQ as EAQ.
unfold YF2e.WIN, YF2e.WINF, YF2e.WINA in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[Hq Hw]]].
- left. img_exact Hw.
- right; left. rewrite EAQ in Hw. unfold o_quar, o_q_cmutex in *. img_lia.
- right; left. rewrite EAQ in Hw. unfold o_quar, o_q_size in *. img_lia.
- right; right; left. clear - Hw. unfold t_qc, kThreadObjSize in *. img_lia.
- do 3 right. destruct (rev G) as [|lb initr] eqn:Hrev.
+ exfalso. img_apply Hq. rewrite <- (rev_involutive G), Hrev. img_refl.
+ destruct (glast_facts lb initr Hrev) as (_ & EQ & L1 & L2 & _). clear - Hw L1 L2 hSP2 EQ. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. img_lia.
Qed.
Lemma WIN_dec : forall a, WINd a \/ ~ WINd a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (img_try (intros; img_lia)).
assert (LQ : G = [] \/ G <> []) by (img_try (destruct G; [img_try (left; img_refl) | img_try (right; discriminate)])).
unfold YF2e.WIN, YF2e.WINF, YF2e.WINA. fold sp0.
destruct (EM (sp0 - 80) sp0) as [C|C0]; [img_try (left; left; img_exact C)|].
destruct (EM (A_QUAR + 152) (A_QUAR + 156)) as [C|C1]; [img_try (left; right; left; left; img_exact C)|].
destruct (EM (A_QUAR + 160) (A_QUAR + 192)) as [C|C2]; [img_try (left; right; left; right; left; img_exact C)|].
destruct (EM (T + t_qc) (T + t_qc + 32)) as [C|C3]; [img_try (left; right; left; right; right; img_exact C)|].
destruct LQ as [LQ|LQ].
- right. intros [X0|[[X1|[X2|X3]]|[X5 _]]]; [img_try (img_exact (C0 X0)) | img_try (img_exact (C1 X1)) | img_try (img_exact (C2 X2)) | img_try (img_exact (C3 X3)) | img_try (img_exact (X5 LQ))].
- destruct (EM GLv (GLv + 8)) as [C|C6]; [img_try (left; right; right; split; [img_exact LQ | img_exact C])|].
right. intros [X0|[[X1|[X2|X3]]|[_ X5]]]; [img_try (img_exact (C0 X0)) | img_try (img_exact (C1 X1)) | img_try (img_exact (C2 X2)) | img_try (img_exact (C3 X3)) | img_try (img_exact (C6 X5))].
Qed.
Definition low_okd {imgk : img} (a w : Z) : bool :=
(((TFX_IMG_LO <=? a) && (a + w <=? TFX_IMG_END)) || ((SHADOW_OFF + TFX_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFX_IMG_END / 8)))
&& ((a + w <=? TFX_INST + o_q_cmutex) || (TFX_INST + o_q_bytes + 8 <=? a)).
Definition const_loc_okd {imgk : img} (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => low_okd a w || ((a =? (0xa6eca + D_10c0)) && (w =? 2) || (a =? (0xa6ecc + D_10c0)) && (w =? 4))
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okd (TFX_TSD + o) w
| ATp o => low_okd (TFX_TP + o) w
| AInst o => low_okd (TFX_INST + o) w
| _ => false
end.
Lemma Tfx_const_locd : forallb const_loc_okd (Tfx_const ly) = true.
Proof. clear. img_case; vm_compute. all: img_refl. Qed.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Lemma CONST_OUT : Forall (fun c => (c_at c = ANum (0xa6eca + D_10c0) /\ c_w c = 2%nat) \/ (c_at c = ANum (0xa6ecc + D_10c0) /\ c_w c = 4%nat) \/
forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> ~ WINd (aeval B ly (c_at c) + i) /\ 0 <= aeval B ly (c_at c) + i < 2 ^ 64 /\
~ (as_inst B + o_q_cmutex <= aeval B ly (c_at c) + i < as_inst B + o_q_bytes + 8) /\
~ (ly_prim ly <= aeval B ly (c_at c) + i < ly_prim ly + kPrimResvSize)) (as_const B ly).
Proof.
rewrite (ts_const _ TB). img_apply Forall_forall. intros c Hc.
pose proof (proj1 (forallb_forall _ _) Tfx_const_locd c Hc) as K. unfold const_loc_okd in K.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _ & _ & _ & hI1 & hI2). pose proof HSP as [S1 S2].
pose proof GEO as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & ZC & ZD).
assert (ZN : forall a, ~ ((sp0 - 80 <= a < sp0) \/ (as_inst B + o_q_cmutex <= a < as_inst B + o_q_cmutex + 4 \/ as_inst B + o_q_size <= a < as_inst B + o_q_size + 32) \/
(T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINd a).
{ intros a Hn Hw. img_exact (Hn (WIN_zone a Hw)). }
pose proof (ts_inst _ TB) as EI.
assert (LOW : forall a i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> low_okd a (Z.max 1 (Z.of_nat (c_w c))) = true ->
~ WINd (a + i) /\ 0 <= a + i < 2 ^ 64 /\ ~ (as_inst B + o_q_cmutex <= a + i < as_inst B + o_q_bytes + 8) /\ ~ (ly_prim ly <= a + i < ly_prim ly + kPrimResvSize)).
{ intros a i Hi L. unfold low_okd in L. rewrite EI.
split; [img_try (img_apply ZN)|]; clear - L Hi hP1 hT1 hS1 S1 EI; rewrite ?EI; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize, DSTACK, TFX_INST, o_q_cmutex, o_q_size, o_q_bytes in *;
img_change (65536 / 8) with 8192 in *; img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in *; img_lia. }
destruct (c_at c) as [z|z|z|z|z|z|z|z|r z|z|z|z|z|z|z|z|z|z|e] eqn:EC; try discriminate K; cbn [aeval].
- apply Bool.orb_prop in K as [K|K]; [img_try (right; right; intros i Hi; img_apply LOW; [img_exact Hi | img_exact K])|].
apply Bool.orb_prop in K as [K|K]; apply andb_prop in K as [K1 K2]; apply Z.eqb_eq in K1; apply Z.eqb_eq in K2; (subst; cbv beta); [img_try (left) | img_try (right; left)]; split; [img_refl | img_lia | img_refl | img_lia].
- right; right. intros i Hi. rewrite EI. split; [img_try (img_apply ZN)|]; clear - K Hi hT1 hT2 S1 S2 G_PT G_TS hI1 hI2 EI; ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, DSTACK, kLowMemEnd, TFX_INST, o_q_cmutex, o_q_size, o_q_bytes in *; img_lia.
- right; right. intros i Hi. rewrite EI. split; [img_try (img_apply ZN)|]; clear - K Hi ZC S1 S2 G_PC G_TC G_CS hI1 hI2 EI; ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, DSTACK, kLowMemEnd, TFX_INST, o_q_cmutex, o_q_size, o_q_bytes in *; img_lia.
- right; right. intros i Hi. rewrite HTSD. img_apply LOW; [img_try (img_exact Hi) | img_try (img_exact K)].
- right; right. intros i Hi. pose proof (LOW (TFX_INST + z) i Hi K) as L3. rewrite <- EI in L3. img_exact L3.
- right; right. intros i Hi. rewrite (ts_tp _ TB). img_apply LOW; [img_try (img_exact Hi) | img_try (img_exact K)].
- right; right. intros i Hi. rewrite EI. split; [img_try (img_apply ZN)|]; clear - K Hi ZD S1 S2 G_PD G_TD G_DS hI1 hI2 EI; ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, DSTACK, kLowMemEnd, TFX_INST, o_q_cmutex, o_q_size, o_q_bytes in *; img_lia.
Qed.
End g.
End f.
