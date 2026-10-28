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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0l YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFex AFf2 AFfu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFff AFeu AFey AFgj AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : drain_pre B ly X W regs mem md.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation tq := (st_qthread X).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).
Lemma M : ARm B ly X rd0. Proof. exact (proj1 (proj1 PRE)). Qed.
Let WF : Wf (as_universe B) X := am_wf B ly X rd0 M.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma HTB : kQuarantineCacheMax < qc_bytes tq. Proof. exact (proj1 (proj2 PRE)). Qed.
Lemma HQL : qloose X. Proof. exact (proj1 (proj2 (proj2 PRE))). Qed.
Lemma HSP : ly_stk_lo ly + DSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & Hlo & Hhi & _). unfold spZ in *. unfold sp0. lia. Qed.
Lemma AQ : A_QUAR = as_inst B + o_quar. Proof. rewrite (ts_inst _ TB). reflexivity. Qed.
Lemma IMG : img_cover ly.
Proof. exact (img_cover_of_ledger ly X md (proj1 (proj2 (proj1 PRE)))). Qed.
Local Notation GSZv := (AFgj.GSZv gq).
Local Notation GFv := (AFgj.GFv ly gq).
Local Notation GLv := (AFgj.GLv ly gq).
Local Notation GBv := (AFgj.GBv gq).
Local Notation TSZv := (AFgj.TSZv tq).
Local Notation TFv := (AFgj.TFv ly tq).
Local Notation TLv := (AFgj.TLv ly tq).
Local Notation TBv := (AFgj.TBv tq).
Local Notation E0 := (AFgj.E0 ly regs gq tq).
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. intros a w x E. exact (tfib_const_lookup B TB ly X H0 mem a w x M E). Qed.
Lemma cell_state : forall c e (w : nat) e', In c (acells B ly X) -> c = ACell e w (AV e') -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros c e w e' Hin ->. apply (cell_holds_val_mem B ly H0 mem e w e'). exact (proj1 (Forall_forall _ _) (am_cells B ly X rd0 M) _ Hin).
Qed.
Lemma cell_stateZ : forall c e (w : nat) x, In c (acells B ly X) -> c = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. intros c e w x Hin E. exact (cell_state c e w (ANum x) Hin E). Qed.
Lemma vis_range : forall e len i, In (e, len) (ajunk B ly X) \/ In (e, len) (aareas X) \/ In (e, len) (aclient X) ->
0 <= i < len -> rd0 (aeval B ly e + i) <> None.
Proof.
intros e len i Hin Hi. destruct Hin as [Hin|[Hin|Hin]].
- exact (proj1 (Forall_forall _ _) (am_junk B ly X rd0 M) _ Hin i Hi).
- exact (proj1 (Forall_forall _ _) (am_areas B ly X rd0 M) _ Hin i Hi).
- exact (proj1 (Forall_forall _ _) (am_client B ly X rd0 M) _ Hin i Hi).
Qed.
Lemma rootT_vals : val_mem tfibsegs m0 (T + t_qc) 8 TSZv /\ val_mem tfibsegs m0 (T + t_qc + 8) 8 TFv /\ val_mem tfibsegs m0 (T + t_qc + 16) 8 TLv /\ val_mem tfibsegs m0 (T + t_qc + 24) 8 TBv.
Proof.
assert (IN : forall c, In c (qc_cells (AT t_qc) tq) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. apply in_app_iff. left. exact Hc. }
unfold AFgj.TSZv, AFgj.TFv, AFgj.TLv, AFgj.TBv. splits.
- apply (cell_stateZ _ (AT t_qc) 8 _ (IN _ ltac:(unfold qc_cells; left; reflexivity)) eq_refl).
- replace (T + t_qc + 8) with (aeval B ly (aoff (AT t_qc) 8)) by (cbn; lia).
replace (match Tq with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match Tq with [] => ANum 0 | b :: _ => batch_exp b end)) by (destruct Tq; reflexivity).
apply (cell_state _ _ 8 _ (IN _ ltac:(unfold qc_cells; right; left; reflexivity)) eq_refl).
- replace (T + t_qc + 16) with (aeval B ly (aoff (AT t_qc) 16)) by (cbn; lia).
replace (match rev Tq with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match rev Tq with [] => ANum 0 | b :: _ => batch_exp b end)) by (destruct (rev Tq); reflexivity).
apply (cell_state _ _ 8 _ (IN _ ltac:(unfold qc_cells; right; right; left; reflexivity)) eq_refl).
- replace (T + t_qc + 24) with (aeval B ly (aoff (AT t_qc) 24)) by (cbn; lia).
apply (cell_stateZ _ _ 8 _ (IN _ ltac:(unfold qc_cells; do 3 right; left; reflexivity)) eq_refl).
Qed.
Lemma rootG_vals : val_mem tfibsegs m0 (A_QUAR + 160) 8 GSZv /\ val_mem tfibsegs m0 (A_QUAR + 168) 8 GFv /\ val_mem tfibsegs m0 (A_QUAR + 176) 8 GLv /\ val_mem tfibsegs m0 (A_QUAR + 184) 8 GBv.
Proof.
assert (IN : forall c, In c (qc_cells (AInst o_q_size) gq) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. apply in_app_iff. right. exact Hc. }
rewrite AQ. unfold AFgj.GSZv, AFgj.GFv, AFgj.GLv, AFgj.GBv. splits.
- replace (as_inst B + o_quar + 160) with (aeval B ly (AInst o_q_size)) by (cbn; unfold o_quar, o_q_size; lia).
apply (cell_stateZ _ (AInst o_q_size) 8 _ (IN _ ltac:(unfold qc_cells; left; reflexivity)) eq_refl).
- replace (as_inst B + o_quar + 168) with (aeval B ly (aoff (AInst o_q_size) 8)) by (cbn; unfold o_quar, o_q_size; lia).
replace (match G with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match G with [] => ANum 0 | b :: _ => batch_exp b end)) by (destruct G; reflexivity).
apply (cell_state _ _ 8 _ (IN _ ltac:(unfold qc_cells; right; left; reflexivity)) eq_refl).
- replace (as_inst B + o_quar + 176) with (aeval B ly (aoff (AInst o_q_size) 16)) by (cbn; unfold o_quar, o_q_size; lia).
replace (match rev G with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match rev G with [] => ANum 0 | b :: _ => batch_exp b end)) by (destruct (rev G); reflexivity).
apply (cell_state _ _ 8 _ (IN _ ltac:(unfold qc_cells; right; right; left; reflexivity)) eq_refl).
- replace (as_inst B + o_quar + 184) with (aeval B ly (aoff (AInst o_q_size) 24)) by (cbn; unfold o_quar, o_q_size; lia).
apply (cell_stateZ _ _ 8 _ (IN _ ltac:(unfold qc_cells; do 3 right; left; reflexivity)) eq_refl).
Qed.
Lemma mutex_vals : forall a, A_QUAR + 152 <= a < A_QUAR + 156 -> mbyte tfibsegs m0 a = Some (Z_to_bv 8 0).
Proof.
intros a Ha.
assert (C1 : val_mem tfibsegs m0 (as_inst B + o_q_cmutex) 1 0).
{ apply (cell_stateZ (z1 (AInst o_q_cmutex) 0) (AInst o_q_cmutex) 1 0); [|reflexivity]. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. left. reflexivity. }
assert (C2 : val_mem tfibsegs m0 (as_inst B + o_q_rmutex) 1 0).
{ apply (cell_stateZ (z1 (AInst o_q_rmutex) 0) (AInst o_q_rmutex) 1 0); [|reflexivity]. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; left. reflexivity. }
assert (C3 : val_mem tfibsegs m0 0xa2d0a 2 0) by (apply cell_lit; vm_compute; reflexivity).
rewrite AQ in Ha. unfold o_quar, o_q_cmutex, o_q_rmutex in *. rewrite (ts_inst _ TB) in *. unfold TFIB_INST in *.
assert (CASES : a = 666008 + 880 \/ a = 666008 + 881 \/ a = 666890 + Z.of_nat 0 \/ a = 666890 + Z.of_nat 1) by lia.
destruct CASES as [-> |[-> |[-> | ->]]].
- pose proof (C1 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E. exact E.
- pose proof (C2 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E. exact E.
- exact (C3 0%nat ltac:(lia)).
- exact (C3 1%nat ltac:(lia)).
Qed.
Lemma const_vals : val_mem tfibsegs m0 (A_QUAR + 64) 8 kQuarantineMax /\ val_mem tfibsegs m0 (A_QUAR + 72) 8 kQuarantineMin.
Proof. split; (apply cell_lit; vm_compute; reflexivity). Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
(forall b2, In b2 (all_batches X) -> ly_prim ly <= SB + b_self b2 /\ SB + b_self b2 + kBatchBytes <= SB + kSpaceSize) /\
4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd.
Proof. exact (AFey.HIGH B ly X rd0 M sp0 HSP IMG). Qed.
Lemma batch_facts : forall b2, In b2 (all_batches X) ->
ly_prim ly <= SB + b_self b2 /\ SB + b_self b2 + kBatchBytes <= SB + kSpaceSize /\ (SB + b_self b2) mod 8192 = 0 /\
kHighMemBeg <= SB + b_self b2 /\ SB + b_self b2 + kBatchBytes <= ASAN_CEIL /\
(forall a, SB + b_self b2 <= a < SB + b_self b2 + kBatchBytes -> apresent H0 mem a) /\ kBatchBytes <= b_bytes b2.
Proof.
intros b2 Hb2. pose proof HI as (P1 & P2 & _ & _ & _ & _ & S1 & S2 & HB & _). destruct (HB b2 Hb2) as [L1 L2].
destruct (AFey.batch_geom B ly X rd0 M sp0 HSP b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _). unfold AFey.addr in Eb.
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
splits; try lia.
- rewrite Eb. unfold kBatchBytes in Ab. apply Z.mod_divide; [lia|]. apply Z.mod_divide in R3 as [c Hc]; [|lia]. apply Z.mod_divide in Ab as [c' Hc']; [|lia]. exists (8 * c + c'). lia.
- intros a Ha. replace a with (aeval B ly (ASp (region_off kBatchClass)) + (xb + (a - (SB + b_self b2)))) by (cbn [aeval]; unfold region_base in Eb; lia).
apply vis_apresent; [cbn [aeval]; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, region_base, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL, kBatchBytes in *; lia|].
apply (vis_range (ASp (region_off kBatchClass)) (rg_mapped_user (reg X kBatchClass))); [right; left | unfold kBatchBytes in *; lia].
unfold aareas. rewrite !in_app_iff. left. apply in_flat_map. exists kBatchClass. split; [apply In_zseq; unfold kBatchClass; lia | left; reflexivity].
- exact (AFey.b_bytes_lb B ly X rd0 M b2 Hb2).
Qed.
Lemma Tq_ne : Tq <> []. Proof. exact (AFey.Tq_ne B ly X rd0 M HTB). Qed.
Lemma g_facts : 0 <= GBv <= 2 ^ 30 /\ GSZv < 2 ^ 40 /\ 0 <= GFv < ASAN_CEIL /\ GFv mod 8192 = 0 /\ 0 <= GLv < ASAN_CEIL /\ GLv mod 8192 = 0 /\ GBv = sum_bytes G.
Proof.
pose proof HQL as (Q1 & Q2 & Q3). pose proof (wq_bytes_g _ (wf_quarantine _ _ _ _ _ WF)) as QE.
pose proof (AFey.sum_bytes_lb B ly X rd0 M G ltac:(intros y Hy; unfold all_batches; apply in_app_iff; right; exact Hy)) as S1.
pose proof (YG0m.batches_len_fuel _ _ _ _ X WF HQL) as BE  . unfold all_batches in BE. rewrite length_app in BE.
unfold AFgj.GBv, AFgj.GSZv, AFgj.GFv, AFgj.GLv, EV_MAX in *. splits; try lia.
- destruct G as [|b t] eqn:Eq; [lia|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; right; rewrite Eq; left; reflexivity)) as (_ & _ & _ & L4 & _). unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in L4. lia.
- destruct G as [|b t] eqn:Eq; [ceil; unfold ASAN_CEIL; lia|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; right; rewrite Eq; left; reflexivity)) as (_ & _ & _ & _ & L5 & _). unfold kBatchBytes in L5. lia.
- destruct G as [|b t] eqn:Eq; [reflexivity|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; right; rewrite Eq; left; reflexivity)) as (_ & _ & L3 & _). exact L3.
- destruct (rev G) as [|b t] eqn:Eq; [lia|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; right; rewrite <- (rev_involutive G), Eq; cbn; apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & L4 & _). unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in L4. lia.
- destruct (rev G) as [|b t] eqn:Eq; [ceil; unfold ASAN_CEIL; lia|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; right; rewrite <- (rev_involutive G), Eq; cbn; apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & _ & L5 & _). unfold kBatchBytes in L5. lia.
- destruct (rev G) as [|b t] eqn:Eq; [reflexivity|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; right; rewrite <- (rev_involutive G), Eq; cbn; apply in_app_iff; right; left; reflexivity)) as (_ & _ & L3 & _). exact L3.
Qed.
Lemma t_facts : kQuarantineCacheMax < TBv <= 2 ^ 29 /\ 1 <= TSZv < 2 ^ 40 /\ 0 <= TFv < ASAN_CEIL /\ TFv mod 8192 = 0 /\ 0 <= TLv < ASAN_CEIL /\ TLv mod 8192 = 0 /\ TBv = sum_bytes Tq.
Proof.
pose proof HQL as (Q1 & Q2 & Q3). pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QE. pose proof HTB as TBX. pose proof Tq_ne as NE0.
pose proof (YG0m.batches_len_fuel _ _ _ _ X WF HQL) as BE  . unfold all_batches in BE. rewrite length_app in BE.
unfold AFgj.TBv, AFgj.TSZv, AFgj.TFv, AFgj.TLv, EV_MAX in *. splits; try lia.
- destruct Tq; [exfalso; exact (NE0 eq_refl) | cbn [length]; lia].
- destruct Tq as [|b t] eqn:Eq; [lia|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; left; rewrite Eq; left; reflexivity)) as (_ & _ & _ & L4 & _). unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in L4. lia.
- destruct Tq as [|b t] eqn:Eq; [ceil; unfold ASAN_CEIL; lia|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; left; rewrite Eq; left; reflexivity)) as (_ & _ & _ & _ & L5 & _). unfold kBatchBytes in L5. lia.
- destruct Tq as [|b t] eqn:Eq; [reflexivity|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; left; rewrite Eq; left; reflexivity)) as (_ & _ & L3 & _). exact L3.
- destruct (rev Tq) as [|b t] eqn:Eq; [lia|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; left; rewrite <- (rev_involutive Tq), Eq; cbn; apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & L4 & _). unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in L4. lia.
- destruct (rev Tq) as [|b t] eqn:Eq; [ceil; unfold ASAN_CEIL; lia|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; left; rewrite <- (rev_involutive Tq), Eq; cbn; apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & _ & L5 & _). unfold kBatchBytes in L5. lia.
- destruct (rev Tq) as [|b t] eqn:Eq; [reflexivity|]. destruct (batch_facts b ltac:(unfold all_batches; apply in_app_iff; left; rewrite <- (rev_involutive Tq), Eq; cbn; apply in_app_iff; right; left; reflexivity)) as (_ & _ & L3 & _). exact L3.
Qed.
Lemma glast_facts : forall lb initr, rev G = lb :: initr ->
In lb (all_batches X) /\ GLv = SB + b_self lb /\ ly_prim ly <= GLv /\ GLv + kBatchBytes <= SB + kSpaceSize /\ GLv mod 8192 = 0 /\
val_mem tfibsegs m0 GLv 8 0 /\ (forall a, GLv <= a < GLv + 8 -> apresent H0 mem a).
Proof.
intros lb initr Hrev.
assert (E0 : G = rev initr ++ [lb]) by (rewrite <- (rev_involutive G), Hrev; reflexivity).
assert (Hin : In lb (all_batches X)) by (unfold all_batches; apply in_app_iff; right; rewrite E0; apply in_app_iff; right; left; reflexivity).
assert (EQ : GLv = SB + b_self lb) by (unfold AFgj.GLv; rewrite Hrev; reflexivity).
destruct (batch_facts lb Hin) as (L1 & L2 & L3 & L4 & L5 & L6 & _). rewrite EQ. splits; try assumption; try reflexivity.
- assert (IN : In (c8 (batch_exp lb) (ANum 0)) (acells B ly X)).
{ unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. apply in_app_iff. right. unfold qc_cells. do 4 right.
apply In_batch_cells. exists (length (rev initr)), lb. rewrite E0. split; [rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity|].
unfold batch_own_cells. left. rewrite next_exp_app_new. reflexivity. }
exact (cell_state _ (batch_exp lb) 8 (ANum 0) IN eq_refl).
- intros a Ha. apply L6. unfold kBatchBytes. lia.
Qed.
Lemma E2 : ew E0 2 = getr regs 2. Proof. exact (AFgj.E2 ly regs gq tq). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqSB : ew E0 33 = w64 SB. Proof. reflexivity. Qed.
Lemma EqGSZ : ew E0 34 = w64 GSZv. Proof. reflexivity. Qed.
Lemma EqGF : ew E0 35 = w64 GFv. Proof. reflexivity. Qed.
Lemma EqGL : ew E0 36 = w64 GLv. Proof. reflexivity. Qed.
Lemma EqGB : ew E0 37 = w64 GBv. Proof. reflexivity. Qed.
Lemma EqTSZ : ew E0 38 = w64 TSZv. Proof. reflexivity. Qed.
Lemma EqTF : ew E0 39 = w64 TFv. Proof. reflexivity. Qed.
Lemma EqTL : ew E0 40 = w64 TLv. Proof. reflexivity. Qed.
Lemma EqTB : ew E0 41 = w64 TBv. Proof. reflexivity. Qed.
Lemma chunk_lit : forall a (w : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | rewrite Z.add_0_l; exact Hm]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k0 d x, ew E0 k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SOff k0 d))).
Proof.
intros base a w k0 d x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfibsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfibsegs m0 o.
Proof. intros a w v o Hv Ho Ha. apply vis_writable_off; [exact Ha|]. replace o with (a + (o - a)) by lia. eapply val_mem_vis; [exact Hv | lia]. Qed.
Ltac offw := first [ lia | apply off_img_high; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg in *; ceil; unfold ASAN_CEIL in *; lia
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI)))); unfold kThreadObjSize, t_qc in *; lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) AFgj.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & HB & hI1 & hI2). pose proof HSP as [S1 S2].
pose proof rootT_vals as (V1 & V2 & V3 & V4). pose proof rootG_vals as (U1 & U2 & U3 & U4). pose proof const_vals as [K1 K2].
pose proof g_facts as (Ga & Gb & Gc & Gd & Ge & Gf & _). pose proof t_facts as (Ta & Tb & Tc & Td & Te & Tf & _).
assert (Gc0 : 0 <= GSZv) by (unfold AFgj.GSZv; clear; lia).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, DSTACK, kQuarantineCacheMax, kLowMemEnd in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, S1, S2, Ga, Gc, Ge, Ta, Tc, Te, hI1, hI2.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
pose proof AQ as EAQ. unfold o_quar in EAQ.
unfold AFgj.REG0, AFgj.R_QW, AFgj.R_QG, AFgj.R_QT, flit8.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- 80)); [rewrite E2; reflexivity | lia | lia |].
intros a Ha. apply apresent_writable; [unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia | apply HPRES; clear -Ha; unfold DSTACK in *; lia]. }
apply Forall_cons.
{   reg_intro. split; [rewrite EAQ; lia|]. split; [rewrite EAQ; lia|]. split.
{ intros o Ho. apply rw_writable. rewrite EAQ, (ts_inst _ TB) in Ho. unfold TFIB_INST in Ho. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit; [| cbn; lia | cbn; lia]. intros k Hk. rewrite le_byte_zero. apply mutex_vals. lia. }
apply Forall_cons.
{   reg_intro. split; [rewrite EAQ; lia|]. split; [rewrite EAQ; lia|]. split.
{ intros o Ho. apply rw_writable. rewrite EAQ, (ts_inst _ TB) in Ho. unfold TFIB_INST in Ho. lia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom 0 _ 8 34%nat 0 GSZv); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact U1 | r8 | cbn; lia].
- apply (chunk_atom 0 _ 8 35%nat 0 GFv); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact U2 | r8 | cbn; lia].
- apply (chunk_atom 0 _ 8 36%nat 0 GLv); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact U3 | r8 | cbn; lia].
- apply (chunk_atom 0 _ 8 37%nat 0 GBv); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact U4 | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_qc in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 88); [apply (val_mem_writable _ _ _ _ V1) | destruct (Z_lt_le_dec o 96); [apply (val_mem_writable _ _ _ _ V2) | destruct (Z_lt_le_dec o 104); [apply (val_mem_writable _ _ _ _ V3) | apply (val_mem_writable _ _ _ _ V4)]]];
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 38%nat 0 TSZv); [rewrite Z.sub_0_r; reflexivity | lia | exact V1 | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 39%nat 0 TFv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V2 | lia] | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 40%nat 0 TLv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V3 | lia] | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 41%nat 0 TBv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V4 | lia] | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. split; [rewrite EAQ; lia|]. split; [rewrite EAQ; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit; [exact K1 | unfold kQuarantineMax; cbn; lia | cbn; lia]. }
apply Forall_cons; [|apply Forall_nil].
{   reg_intro. split; [rewrite EAQ; lia|]. split; [rewrite EAQ; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit; [exact K2 | unfold kQuarantineMin; cbn; lia | cbn; lia]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 AFgj.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _ & _ & _ & hI1 & hI2). pose proof HSP as [S1 S2].
pose proof (AFey.SX B ly X rd0 M 2 8 _ _ eq_refl eq_refl ltac:(lia)) as DTS. unfold zdisjoint in DTS. cbn [fst snd] in DTS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range). pose proof AQ as EAQ. unfold o_quar in EAQ.
apply pairwise_disjoint_of_extents. unfold AFgj.REG0, AFgj.R_QW, AFgj.R_QG, AFgj.R_QT, flit8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
pose proof (ts_inst _ TB) as EI. unfold TFIB_INST in EI.
rewrite E2, EqT. unfold w64. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, DSTACK, kLowMemEnd in *.
fold sp0. rewrite !unsigned_lit_small by lia. rewrite EAQ.
unfold t_qc. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in hT1.
repeat split; first [clear hT1; lia | clear - hT1 EI CR0; lia].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms AFgj.FFD).
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & _). pose proof HSP as [S1 S2].
destruct PRE as (_ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof g_facts as (Ga & Gb & Gc & Gd & Ge & Gf & _). pose proof t_facts as (Ta & Tb & Tc & Td & Te & Tf & _).
assert (Gc0 : 0 <= GSZv) by (unfold AFgj.GSZv; clear; lia).
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, DSTACK, kQuarantineCacheMax in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, S1, S2, Ga, Gc, Ge, Ta, Tc, Te.
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
cbn [AFgj.FFD f_atoms atoms_ok]. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DSTACK.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 32%nat T); [exact EqT| | | |]. all: clear - CR0 hT1 hT2 TAL; first [lia | exact TAL]. }
split. { apply (AF 33%nat SB); [exact EqSB| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [lia | exact SAL]. }
split. { apply (AF 34%nat GSZv); [exact EqGSZ| | | |]. all: clear - CR0 Gb Gc0; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 35%nat GFv); [exact EqGF| | | |]. all: clear - CR0 Gc Gd; first [lia | change (2 ^ 13) with 8192; exact Gd]. }
split. { apply (AF 36%nat GLv); [exact EqGL| | | |]. all: clear - CR0 Ge Gf; first [lia | change (2 ^ 13) with 8192; exact Gf]. }
split. { apply (AF 37%nat GBv); [exact EqGB| | | |]. all: clear - CR0 Ga; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 38%nat TSZv); [exact EqTSZ| | | |]. all: clear - CR0 Tb; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 39%nat TFv); [exact EqTF| | | |]. all: clear - CR0 Tc Td; first [lia | change (2 ^ 13) with 8192; exact Td]. }
split. { apply (AF 40%nat TLv); [exact EqTL| | | |]. all: clear - CR0 Te Tf; first [lia | change (2 ^ 13) with 8192; exact Tf]. }
split; [|exact I]. { apply (AF 41%nat TBv); [exact EqTB| | | |]. all: clear - CR0 Ta; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
Qed.
Lemma SEED_ok : st_ok tfibsegs E0 AFgj.SS0 (restrict (w_H W) (mkst regs (w64 0x32f28) mem (seg_rom tfibsegs))).
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1 & Ha2). rewrite (ts_tp _ TB) in Htp.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & _). ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in hT1, hT2.
rewrite restrict_mkst_fx. unfold AFgj.SS0, AFgj.SR0, sr_set. cbn [bv_eqb]. unfold AFgj.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Htp] | intros XX; discriminate | cbn [sv_denot]; exact Ha0] | intros XX; discriminate |] | intros XX; discriminate |].
+ cbn [sv_denot]. fold (AFgj.E0 ly regs gq tq). rewrite EqT, Ha1. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (AFgj.E0 ly regs gq tq). rewrite EqT, Ha2. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.
Theorem FH_ok : AFgj.free_hyps W ly regs mem gq tq.
Proof.
pose proof PRE as PRE'. destruct PRE' as (HAR & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof g_facts as (Ga & Gb & Gc & Gd & Ge & Gf & _). pose proof t_facts as (Ta & Tb & Tc & Td & Te & Tf & _).
constructor.
- exact LO.
- exact IMG.
- rewrite (ts_tp _ TB) in Htp. exact Htp.
- exact Hra.
- exact Hra4.
- split; [exact Hlo | exact Hhi].
- exact Hal.
- exact HPRES.
- clear - Ga Gb Gc Gd. splits; first [assumption | lia].
- clear - Ta Tb Tc Td Te Tf. splits; first [assumption | lia].
- intros lb initr Hrev. destruct (glast_facts lb initr Hrev) as (_ & _ & L1 & L2 & L3 & L4 & L5). splits; assumption.
- exact SEED_ok.
Qed.
Local Notation WINd := (AFgj.WIN ly regs gq).
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
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(clear; lia) (Forall_nth_f _ _ 6 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
pose proof (zone3_intro ly (ly_D ly) 4096 IMG ltac:(clear; lia) (Forall_nth_f _ _ 7 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 7 1 _ _ HD eq_refl eq_refl)) as ZD.
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
unfold AFgj.WIN, AFgj.WINF, AFgj.WINA in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[Hq Hw]]].
- left. exact Hw.
- right; left. rewrite EAQ in Hw. unfold o_quar, o_q_cmutex in *. lia.
- right; left. rewrite EAQ in Hw. unfold o_quar, o_q_size in *. lia.
- right; right; left. clear - Hw. unfold t_qc, kThreadObjSize in *. lia.
- do 3 right. destruct (rev G) as [|lb initr] eqn:Hrev.
+ exfalso. apply Hq. rewrite <- (rev_involutive G), Hrev. reflexivity.
+ destruct (glast_facts lb initr Hrev) as (_ & EQ & L1 & L2 & _). clear - Hw L1 L2 hSP2 EQ. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. lia.
Qed.
Lemma WIN_dec : forall a, WINd a \/ ~ WINd a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
assert (LQ : G = [] \/ G <> []) by (destruct G; [left; reflexivity | right; discriminate]).
unfold AFgj.WIN, AFgj.WINF, AFgj.WINA. fold sp0.
destruct (EM (sp0 - 80) sp0) as [C|C0]; [left; left; exact C|].
destruct (EM (A_QUAR + 152) (A_QUAR + 156)) as [C|C1]; [left; right; left; left; exact C|].
destruct (EM (A_QUAR + 160) (A_QUAR + 192)) as [C|C2]; [left; right; left; right; left; exact C|].
destruct (EM (T + t_qc) (T + t_qc + 32)) as [C|C3]; [left; right; left; right; right; exact C|].
destruct LQ as [LQ|LQ].
- right. intros [X0|[[X1|[X2|X3]]|[X5 _]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (X5 LQ)].
- destruct (EM GLv (GLv + 8)) as [C|C6]; [left; right; right; split; [exact LQ | exact C]|].
right. intros [X0|[[X1|[X2|X3]]|[_ X5]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (C6 X5)].
Qed.
Definition low_okd (a w : Z) : bool :=
(((TFIB_IMG_LO <=? a) && (a + w <=? TFIB_IMG_END)) || ((SHADOW_OFF + TFIB_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFIB_IMG_END / 8)))
&& ((a + w <=? TFIB_INST + o_q_cmutex) || (TFIB_INST + o_q_bytes + 8 <=? a)).
Definition const_loc_okd (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => low_okd a w || ((a =? 0xa2d0a) && (w =? 2) || (a =? 0xa2d0c) && (w =? 4))
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okd (TFIB_TSD + o) w
| ATp o => low_okd (TFIB_TP + o) w
| AInst o => low_okd (TFIB_INST + o) w
| _ => false
end.
Lemma Tfib_const_locd : forallb const_loc_okd (Tfib_const ly) = true.
Proof. clear. vm_compute. reflexivity. Qed.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Lemma CONST_OUT : Forall (fun c => (c_at c = ANum 0xa2d0a /\ c_w c = 2%nat) \/ (c_at c = ANum 0xa2d0c /\ c_w c = 4%nat) \/
forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> ~ WINd (aeval B ly (c_at c) + i) /\ 0 <= aeval B ly (c_at c) + i < 2 ^ 64 /\
~ (as_inst B + o_q_cmutex <= aeval B ly (c_at c) + i < as_inst B + o_q_bytes + 8) /\
~ (ly_prim ly <= aeval B ly (c_at c) + i < ly_prim ly + kPrimResvSize)) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc.
pose proof (proj1 (forallb_forall _ _) Tfib_const_locd c Hc) as K. unfold const_loc_okd in K.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _ & _ & _ & hI1 & hI2). pose proof HSP as [S1 S2].
pose proof GEO as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & ZC & ZD).
assert (ZN : forall a, ~ ((sp0 - 80 <= a < sp0) \/ (as_inst B + o_q_cmutex <= a < as_inst B + o_q_cmutex + 4 \/ as_inst B + o_q_size <= a < as_inst B + o_q_size + 32) \/
(T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINd a).
{ intros a Hn Hw. exact (Hn (WIN_zone a Hw)). }
pose proof (ts_inst _ TB) as EI.
assert (LOW : forall a i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> low_okd a (Z.max 1 (Z.of_nat (c_w c))) = true ->
~ WINd (a + i) /\ 0 <= a + i < 2 ^ 64 /\ ~ (as_inst B + o_q_cmutex <= a + i < as_inst B + o_q_bytes + 8) /\ ~ (ly_prim ly <= a + i < ly_prim ly + kPrimResvSize)).
{ intros a i Hi L. unfold low_okd in L. rewrite EI.
split; [apply ZN|]; clear - L Hi hP1 hT1 hS1 S1 EI; rewrite ?EI; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kThreadObjSize, DSTACK, TFIB_INST, o_q_cmutex, o_q_size, o_q_bytes in *;
change (65536 / 8) with 8192 in *; change (6270976 / 8) with 783872 in *; lia. }
destruct (c_at c) as [z|z|z|z|z|z|z|z|r z|z|z|z|z|z|z|z|z|z|e] eqn:EC; try discriminate K; cbn [aeval].
- apply Bool.orb_prop in K as [K|K]; [right; right; intros i Hi; apply LOW; [exact Hi | exact K]|].
apply Bool.orb_prop in K as [K|K]; apply andb_prop in K as [K1 K2]; apply Z.eqb_eq in K1; apply Z.eqb_eq in K2; subst; [left | right; left]; split; [reflexivity | lia | reflexivity | lia].
- right; right. intros i Hi. rewrite EI. split; [apply ZN|]; clear - K Hi hT1 hT2 S1 S2 G_PT G_TS hI1 hI2 EI; ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, DSTACK, kLowMemEnd, TFIB_INST, o_q_cmutex, o_q_size, o_q_bytes in *; lia.
- right; right. intros i Hi. rewrite EI. split; [apply ZN|]; clear - K Hi ZC S1 S2 G_PC G_TC G_CS hI1 hI2 EI; ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, DSTACK, kLowMemEnd, TFIB_INST, o_q_cmutex, o_q_size, o_q_bytes in *; lia.
- right; right. intros i Hi. rewrite HTSD. apply LOW; [exact Hi | exact K].
- right; right. intros i Hi. pose proof (LOW (TFIB_INST + z) i Hi K) as L3. rewrite <- EI in L3. exact L3.
- right; right. intros i Hi. rewrite (ts_tp _ TB). apply LOW; [exact Hi | exact K].
- right; right. intros i Hi. rewrite EI. split; [apply ZN|]; clear - K Hi ZD S1 S2 G_PD G_TD G_DS hI1 hI2 EI; ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, DSTACK, kLowMemEnd, TFIB_INST, o_q_cmutex, o_q_size, o_q_bytes in *; lia.
Qed.
End g.
End f.
