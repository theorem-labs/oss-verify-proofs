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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0r YF0u YF1f YF0w YF2d YF1p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF2l YF07.
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
Lemma combine_seq_last : forall (l0 : list Z) x0, In (length l0, x0) (combine (seq 0 (length (l0 ++ [x0]))) (l0 ++ [x0])).
Proof. intros l0 x0. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, (combine_snoc _ _ _ eq_refl). img_apply in_app_iff. right. left. img_refl. Qed.
Section g. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (W : world tfxsegs) (mem : word -> option byte) (sp0 : Z) (k : chunk).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread X).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Hypothesis M : ARm B ly X rd0.
Hypothesis HSP : ly_stk_lo ly + QSTACK <= sp0 <= ly_stk_hi ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hk : In k (st_chunks X).
Hypothesis HQL : qloose X.
Hypothesis HNB : need_new_batch (st_qthread X) = true.
Definition jw (a : Z) : Z := match rdword rd0 a with Some w => w | None => 0 end.
Definition jst : Z := jw (T + t_cache_stats + 16).
Let WF : Wf (as_universe B) X := am_wf B ly X rd0 M.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma KF : cfacts B ly X k. Proof. img_exact (chunk_facts B ly X rd0 k M Hk). Qed.
Local Notation QSZv := (YF2l.QSZv q).
Local Notation QFv := (YF2l.QFv ly q).
Local Notation QLv := (YF2l.QLv ly q).
Local Notation QBv := (YF2l.QBv q).
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfx_const ly) e = Some (ACell e w (AV e')) -> val_mem tfxsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros e w e' E. img_exact (tfx_const_lookup_sym B TB ly X H0 mem e w e' M E). Qed.
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
Lemma in_thread_junk : forall r, In r thread_junk -> In r (ajunk B ly X).
Proof. intros r Hr. unfold ajunk. right. right. do 5 (img_apply in_or_app; right). img_apply in_or_app. left. img_exact Hr. Qed.
Lemma val_mem_present : forall a (w : nat) v i, val_mem tfxsegs m0 a w v -> 0 <= i < Z.of_nat w -> off_img (a + i) -> apresent H0 mem (a + i).
Proof.
intros a w v i V Hi Hr. img_apply vis_apresent_off; [img_try (img_exact Hr)|]. pose proof (V (Z.to_nat i) ltac:(img_lia)) as E. rewrite Z2Nat.id in E by img_lia.
unfold aview. rewrite E. discriminate.
Qed.
Lemma jst_val : val_mem tfxsegs m0 (T + t_cache_stats + 16) 8 jst /\ 0 <= jst < 2 ^ 64.
Proof.
destruct (vis_word H0 mem (T + t_cache_stats + 16)) as (w & Rw & Vw & Ew).
- intros i Hi. replace (T + t_cache_stats + 16 + i) with (aeval B ly (AT t_cache_stats) + (16 + i)) by (img_try (cbn; img_lia)).
img_apply (vis_range (AT t_cache_stats) (t_stats - t_cache_stats)); [img_try (left; img_apply in_thread_junk; unfold thread_junk; cbn; tauto) | img_try (unfold t_stats, t_cache_stats; img_lia)].
- unfold jst, jw. rewrite Ew. auto.
Qed.
Lemma root_vals : val_mem tfxsegs m0 (T + t_qc) 8 QSZv /\ val_mem tfxsegs m0 (T + t_qc + 8) 8 QFv /\ val_mem tfxsegs m0 (T + t_qc + 16) 8 QLv /\ val_mem tfxsegs m0 (T + t_qc + 24) 8 QBv.
Proof.
assert (IN : forall c, In c (qc_cells (AT t_qc) q) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. img_apply in_app_iff. left. img_exact Hc. }
unfold YF2l.QSZv, YF2l.QFv, YF2l.QLv, YF2l.QBv. splits.
- img_apply (cell_stateZ _ (AT t_qc) 8 _ (IN _ ltac:(img_try (unfold qc_cells; left; img_refl))) eq_refl).
- replace (T + t_qc + 8) with (aeval B ly (aoff (AT t_qc) 8)) by (img_try (cbn; img_lia)).
replace (match qc_list q with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match qc_list q with [] => ANum 0 | b :: _ => batch_exp b end)) by (img_try (destruct (qc_list q); img_refl)).
img_apply (cell_state _ _ 8 _ (IN _ ltac:(img_try (unfold qc_cells; right; left; img_refl))) eq_refl).
- replace (T + t_qc + 16) with (aeval B ly (aoff (AT t_qc) 16)) by (img_try (cbn; img_lia)).
replace (match rev (qc_list q) with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match rev (qc_list q) with [] => ANum 0 | b :: _ => batch_exp b end)) by (img_try (destruct (rev (qc_list q)); img_refl)).
img_apply (cell_state _ _ 8 _ (IN _ ltac:(img_try (unfold qc_cells; right; right; left; img_refl))) eq_refl).
- replace (T + t_qc + 24) with (aeval B ly (aoff (AT t_qc) 24)) by (img_try (cbn; img_lia)).
img_apply (cell_stateZ _ _ 8 _ (IN _ ltac:(img_try (unfold qc_cells; do 3 right; left; img_refl))) eq_refl).
Qed.
Lemma count_val : val_mem tfxsegs m0 (T + t_cache + 1920) 4 (if st_cache_inited X then Z.of_nat (length (pc_chunks (cache X kBatchClass))) else 0).
Proof.
assert (IN : forall c, In c (cache_cells X kBatchClass) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. right; left. img_apply in_flat_map. exists kBatchClass. split; [img_try (img_apply In_zseq; unfold kBatchClass; img_lia) | img_try (img_exact Hc)]. }
unfold cache_cells in IN.
replace (T + t_cache + 1920) with (aeval B ly (AT (t_cache + 80 * kBatchClass))) by (img_try (cbn; unfold kBatchClass; img_lia)).
destruct (st_cache_inited X); img_apply (cell_stateZ _ _ 4 _ (IN _ ltac:(img_try (left; img_refl))) eq_refl).
Qed.
Lemma u_zone : zone3 (u - 16) (nn + 16).
Proof.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof (YF1f.ext_rounded B ly X rd0 M k Hk) as (ER & NN1 & NN2 & NN3).
pose proof (req_size_bounds (ck_req k) ltac:(img_try (clear - G7; img_lia))) as (_ & Q1 & _).
assert (ZK : zone3 (ck_base B ly k) (ck_extent k)).
{ img_apply (zone3_intro ly (ck_base B ly k) (ck_extent k) IMG ltac:(img_try (clear - G5 G8 Q1; img_lia)) G1).
img_apply YF0r.zdisjoint_of_pointwise; [img_try (clear - G5 G8 Q1; img_lia) | img_try (img_exact (proj1 (proj2 (lo_img _ LO)))) |].
intros y Hy. img_exact (proj1 (chunk_apart B ly X rd0 k y M Hk Hy)). }
rewrite G4. clear - G5 ER NN1 NN2 NN3 ZK. ceil. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. img_lia.
Qed.
Lemma u_facts : 4096 + 16 <= u /\ u + nn <= ASAN_CEIL /\ u mod 16 = 0 /\ 1 <= nn < 2 ^ 28.
Proof.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). pose proof (req_size_bounds (ck_req k) ltac:(img_lia)) as (Q1 & Q2 & Q3). unfold ck_n.
assert (LO16 : 4096 <= ck_base B ly k) by (img_try (clear - G1; unfold in_app in G1; img_lia)).
rewrite G4. unfold MALLOC_MAX in G7. splits; try img_lia.
all: apply Z.mod_divide in G3 as [c Hc]; [|img_lia]; apply Z.mod_divide in G6 as [c' Hc']; [|img_lia]; rewrite Hc, Hc'; img_apply Z.mod_divide; [img_lia|]; exists (c + c'); img_lia.
Qed.
Lemma items_n_pos : forall b x, In b (all_batches X) -> In x (b_items b) -> 1 <= ck_n x.
Proof.
intros b x Hb Hx. pose proof (proj1 (Forall_forall _ _) (wq_items _ (wf_quarantine _ _ _ _ _ WF)) x ltac:(img_try (unfold q_items; img_apply in_flat_map; exists b; auto))) as [X1 _].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) x X1) as [N _]. unfold ck_n. pose proof (req_size_bounds (ck_req x) ltac:(img_lia)). img_lia.
Qed.
Lemma b_bytes_ge : forall b, In b (all_batches X) -> kBatchBytes <= b_bytes b.
Proof.
intros b Hb. unfold b_bytes.
assert (G : forall l0, incl l0 (b_items b) -> 0 <= fold_right (fun k0 acc => ck_n k0 + acc) 0 l0).
{ induction l0 as [|x t IH]; intros Hl0; cbn; [img_lia|]. pose proof (items_n_pos b x Hb (Hl0 x (or_introl eq_refl))). pose proof (IH ltac:(img_try (intros y Hy; img_apply Hl0; right; img_exact Hy))). img_lia. }
pose proof (G (b_items b) ltac:(img_try (intros y Hy; img_exact Hy))). img_lia.
Qed.
Lemma sum_bytes_ge : forall l0, incl l0 (all_batches X) -> 0 <= sum_bytes l0.
Proof.
induction l0 as [|b t IH]; intros Hl0; cbn; [img_try (unfold sum_bytes; cbn; img_lia)|]. unfold sum_bytes in *. cbn.
pose proof (b_bytes_ge b (Hl0 b (or_introl eq_refl))). pose proof (IH ltac:(img_try (intros y Hy; img_apply Hl0; right; img_exact Hy))). unfold kBatchBytes in *. img_lia.
Qed.
Lemma q_facts : 0 <= QBv /\ QBv + nn + kBatchBytes <= 2 ^ 48 /\ QSZv < 2 ^ 40 /\ 0 <= QFv < ASAN_CEIL.
Proof.
pose proof (YG0s.batches_len_fuel _ _ _ _ X WF HQL) as BE  .
pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QE. destruct HQL as (T1 & _ & _). pose proof u_facts as (_ & _ & _ & NN).
pose proof (sum_bytes_ge (qc_list q) ltac:(img_try (intros y Hy; unfold all_batches; img_apply in_app_iff; left; img_exact Hy))) as S1.
unfold all_batches in BE. rewrite length_app in BE.
unfold YF2l.QBv, YF2l.QSZv, YF2l.QFv, kBatchBytes, EV_MAX in *. splits; try img_lia.
- destruct (qc_list q) as [|b t] eqn:Eq; [img_lia|]. destruct (YF0w.batch_geom B ly X rd0 M (pc_chunks (cache X kBatchClass)) sp0 HSP b ltac:(img_try (unfold all_batches; img_apply in_app_iff; left; rewrite Eq; left; img_refl))) as (xb & Eb & Pb & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & _ & _ & R4 & _). pose proof (lo_high ly LO) as [P1 _]. unfold kHighMemBeg in R4, P1. img_lia.
- destruct (qc_list q) as [|b t] eqn:Eq; [img_try (ceil; unfold ASAN_CEIL; img_lia)|]. destruct (YF0w.batch_geom B ly X rd0 M (pc_chunks (cache X kBatchClass)) sp0 HSP b ltac:(img_try (unfold all_batches; img_apply in_app_iff; left; rewrite Eq; left; img_refl))) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5). unfold kBatchBytes in *. img_lia.
Qed.
Lemma last_facts : forall lb initr, rev (qc_list q) = lb :: initr ->
ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize /\ QLv mod 8192 = 0 /\
val_mem tfxsegs m0 (QLv + 16) 8 kBatchSlots /\ (forall a, QLv <= a < QLv + 8 -> apresent H0 mem a) /\ In lb (all_batches X) /\ QLv = SB + b_self lb.
Proof.
intros lb initr Hrev.
destruct (YF0w.last_in ly X lb initr Hrev) as [Hin EQ]. img_change (YF0w.QLv ly X) with QLv in EQ.
destruct (YF0w.batch_geom B ly X rd0 M (pc_chunks (cache X kBatchClass)) sp0 HSP lb Hin) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5). pose proof (lo_space_in ly LO) as [SI1 SI2].
pose proof (lo_high ly LO) as [P1 P2].
assert (E0 : qc_list q = rev initr ++ [lb]) by (img_try (rewrite <- (rev_involutive (qc_list q)), Hrev; img_refl)).
assert (IN : forall c, In c (batch_cells (qc_list q)) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. img_apply in_app_iff. left. unfold qc_cells. do 4 right. img_exact Hc. }
assert (CNTc : In (z8 (aoff (batch_exp lb) 16) (Z.of_nat (length (b_items lb)))) (batch_cells (qc_list q))).
{ img_apply In_batch_cells. exists (length (rev initr)), lb. rewrite E0. split; [img_try (rewrite nth_error_app2 by img_lia; rewrite Nat.sub_diag; img_refl)|]. unfold batch_own_cells. right; right; left. img_refl. }
assert (NXc : In (c8 (batch_exp lb) (ANum 0)) (batch_cells (qc_list q))).
{ img_apply In_batch_cells. exists (length (rev initr)), lb. rewrite E0. split; [img_try (rewrite nth_error_app2 by img_lia; rewrite Nat.sub_diag; img_refl)|]. unfold batch_own_cells. left.
rewrite (next_exp_last _ _ (eq_sym (last_length _ _))). img_refl. }
assert (FULL : Z.of_nat (length (b_items lb)) = kBatchSlots).
{ unfold need_new_batch in HNB. rewrite Hrev in HNB. apply Z.eqb_eq in HNB. img_exact HNB. }
assert (L1 : ly_prim ly <= SB + b_self lb) by img_lia.
assert (L2 : SB + b_self lb + kBatchBytes <= SB + kSpaceSize).
{ rewrite Eb. unfold region_base. rewrite region_off_eq by (img_try (unfold kBatchClass; img_lia)). unfold kBatchClass, kBatchBytes, kSpaceSize in *. img_lia. }
rewrite EQ. splits; try img_lia.
- rewrite Eb. img_apply Z.mod_divide; [img_lia|]. apply Z.mod_divide in R3 as [c Hc]; [|img_lia]. apply Z.mod_divide in Ab as [c' Hc']; [|img_try (unfold kBatchBytes; img_lia)]. exists (8 * c + c'). unfold kBatchBytes in Hc'. img_lia.
- replace (SB + b_self lb + 16) with (aeval B ly (aoff (batch_exp lb) 16)) by (img_try (cbn; img_lia)). rewrite <- FULL. img_apply (cell_stateZ _ _ 8 _ (IN _ CNTc) eq_refl).
- intros a Ha. pose proof (cell_state _ _ 8 _ (IN _ NXc) eq_refl) as V. cbn [aeval batch_exp] in V.
replace a with (SB + b_self lb + (a - (SB + b_self lb))) by img_lia. img_apply (val_mem_present _ 8 _ _ V); [img_try (cbn; img_lia) | img_try (img_apply off_img_high; ceil; unfold TFX_IMG_END, kHighMemBeg, kSpaceSize, kBatchBytes, ASAN_CEIL in *; img_lia)].
- img_exact Hin.
Qed.
Lemma chunk_lit : forall (E0 : env) a (w : BinNums.N) x, val_mem tfxsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 0 (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros E0 a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (rewrite Z.add_0_l; img_exact Hm)]. Qed.
Lemma chunk_lit_at : forall (E0 : env) base a (w : BinNums.N) x, val_mem tfxsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros E0 base a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)]. Qed.
Lemma chunk_atom : forall (E0 : env) base a (w : BinNums.N) k0 d x, ew E0 k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfxsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal w (SOff k0 d))).
Proof.
intros E0 base a w k0 d x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfxsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfxsegs m0 o.
Proof. intros a w v o Hv Ho Ha. img_apply vis_writable_off; [img_try (img_exact Ha)|]. replace o with (a + (o - a)) by img_lia. eapply val_mem_vis; [img_try (img_exact Hv) | img_lia]. Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
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
(4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) /\ (4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL).
Proof.
pose proof (Forall_nth_f _ _ 6 _ (lo_app ly LO) eq_refl) as IC. pose proof (Forall_nth_f _ _ 7 _ (lo_app ly LO) eq_refl) as ID.
cbn beta in IC, ID. cbn [fst snd] in IC, ID. unfold in_app in IC, ID.
assert (C12 : 4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) by (img_try (clear - IC; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; img_lia)).
assert (D12 : 4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL) by (img_try (clear - ID; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; img_lia)). clear IC ID.
pose proof (lo_disj ly LO) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _ & DT & _ & _ & _ & DC & DD & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [PD DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [TD DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DC as [CD DC]. apply Forall_cons_iff in DC as [CSTK _]. apply Forall_cons_iff in DD as [DSTK _].
unfold zdisjoint in PT, PC, PD, PSTK, TC, TD, TSTK, CD, CSTK, DSTK. cbn [fst snd] in PT, PC, PD, PSTK, TC, TD, TSTK, CD, CSTK, DSTK.
destruct C12 as [C1 C2]. destruct D12 as [D1 D2]. splits; assumption.
Qed.
Section h.
Variable l : list Z.
Hypothesis Hl : pc_chunks (cache X kBatchClass) = l.
Hypothesis Hlne : l <> [].
Definition cnt : Z := Z.of_nat (length l).
Definition coff : Z := last l 0.
Local Notation CPv := (YF2l.CPv coff).
Local Notation NBv := (YF2l.NBv ly coff).
Local Notation CSLv := (YF2l.CSLv ly cnt).
Lemma Hci : st_cache_inited X = true.
Proof.
pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia)))) as WC. unfold wf_class in WC.
destruct (st_cache_inited X) eqn:E; [img_refl|]. exfalso. img_apply Hlne. rewrite <- Hl, WC. img_refl.
Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
ly_prim ly <= NBv /\ NBv + kBatchBytes <= SB + kSpaceSize /\
(forall lb initr, rev (qc_list q) = lb :: initr -> ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize).
Proof.
pose proof (YF0w.HIGH B ly X rd0 M Hci l Hl Hlne sp0 HSP IMG) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
unfold YF2l.NBv, coff. splits; try img_lia; try img_exact A3. img_exact A11.
Qed.
Lemma NBG : SB + (region_off kBatchClass + coff) = region_base ly kBatchClass + coff /\ 0 <= coff /\ coff mod kBatchBytes = 0 /\
coff + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\ rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= 2 ^ 31 /\
In coff (pc_chunks (cache X kBatchClass)) /\ ~ In coff (batch_offs X kBatchClass) /\ ~ In coff (chunk_offs X kBatchClass).
Proof. img_exact (YF0w.nb_geom B ly X rd0 M Hci l Hl Hlne). Qed.
Lemma cache_vals : val_mem tfxsegs m0 (T + t_cache + 1920) 4 cnt /\ val_mem tfxsegs m0 (T + t_cache + 1928) 8 8192 /\ val_mem tfxsegs m0 CSLv 4 CPv /\ 0 <= cnt <= 16 /\ 1 <= cnt.
Proof.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. rewrite Hci in WC. destruct WC as [PM PL].
pose proof (class_ok kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as (_ & _ & _ & K4 & _). rewrite Hl in PL.
assert (LZ : length l <> 0%nat) by (img_try (intros E0; apply Hlne, length_zero_iff_nil; img_exact E0)).
assert (IN : forall c, In c (cache_cells X kBatchClass) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. right; left. img_apply in_flat_map. exists kBatchClass. split; [img_try (img_apply In_zseq; unfold kBatchClass; img_lia) | img_try (img_exact Hc)]. }
unfold cache_cells in IN. rewrite Hci, Hl in IN.
unfold YF2l.CSLv, YF2l.CPv, cnt. splits; try img_lia.
- replace (T + t_cache + 1920) with (aeval B ly (AT (t_cache + 80 * kBatchClass))) by (img_try (cbn; unfold kBatchClass; img_lia)).
img_apply (cell_stateZ _ _ 4 _ (IN _ ltac:(img_try (left; img_refl))) eq_refl).
- replace (T + t_cache + 1928) with (aeval B ly (aoff (AT (t_cache + 80 * kBatchClass)) 8)) by (img_try (cbn; unfold kBatchClass; img_lia)).
img_apply (cell_stateZ _ _ 8 _ (IN _ ltac:(img_try (right; right; left; img_refl)))). img_refl.
- replace (T + t_cache + 1936 + 4 * (Z.of_nat (length l) - 1)) with (aeval B ly (aoff (AT (t_cache + 80 * kBatchClass)) (16 + 4 * Z.of_nat (length l - 1)))) by (img_try (cbn; unfold kBatchClass; rewrite Nat2Z.inj_sub by img_lia; cbn; img_lia)).
assert (SLOT_IN : In ((length l - 1)%nat, last l 0) (combine (seq 0 (length l)) l)).
{ set (x0 := last l 0). rewrite <- (removelast_app_last l 0 Hlne) at 2 3. fold x0.
replace (length l - 1)%nat with (length (removelast l)) by (img_try (rewrite removelast_length by img_exact Hlne; img_lia)). img_apply combine_seq_last. }
apply (cell_stateZ _ _ 4 _ (IN _ ltac:(img_try (right; right; right; img_apply in_map_iff; exists ((length l - 1)%nat, last l 0); split; [img_refl | img_try (img_exact SLOT_IN)])))).
unfold coff. img_refl.
Qed.
Lemma hit_facts : 0 <= coff /\ coff + kBatchBytes <= 2 ^ 31 /\ coff mod 16 = 0 /\ ly_prim ly <= NBv /\ NBv + kBatchBytes <= SB + kSpaceSize /\ NBv mod 8192 = 0 /\
(forall a, NBv <= a < NBv + 32 -> apresent H0 mem a) /\
(forall lb initr, rev (qc_list q) = lb :: initr -> NBv + kBatchBytes <= QLv \/ QLv + kBatchBytes <= NBv).
Proof.
pose proof NBG as (Eb & Pb & Ab & Ub & [AU MU] & INP & NIB & NIC). pose proof HI as (P1 & P2 & _ & _ & _ & _ & S1 & S2 & N1 & N2 & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5).
unfold YF2l.NBv in *. unfold kBatchBytes in *. splits; try img_lia.
all: try (apply Z.mod_divide in Ab as [c Hc]; [|img_lia]; rewrite Hc; img_apply Z.mod_divide; [img_lia|]; exists (512 * c); img_lia).
all: try (rewrite Eb; img_apply Z.mod_divide; [img_lia|]; apply Z.mod_divide in R3 as [c Hc]; [|img_lia]; apply Z.mod_divide in Ab as [c' Hc']; [|img_lia]; exists (8 * c + c'); img_lia).
- assert (BND : kHighMemBeg <= SB + (region_off kBatchClass + coff) /\ SB + (region_off kBatchClass + coff) + 8192 <= ASAN_CEIL) by (img_try (rewrite Eb; img_lia)).
intros a Ha. replace a with (aeval B ly (ASp (region_off kBatchClass)) + (coff + (a - (SB + (region_off kBatchClass + coff))))) by (img_try (cbn [aeval]; img_lia)).
img_apply vis_apresent_off; [img_try (img_apply off_img_high; cbn [aeval]; ceil; unfold TFX_IMG_END, kHighMemBeg, ASAN_CEIL in *; img_lia)|].
img_apply (vis_range (ASp (region_off kBatchClass)) (rg_mapped_user (reg X kBatchClass))); [img_try (right; left) | img_lia].
unfold aareas. rewrite !in_app_iff. left. img_apply in_flat_map. exists kBatchClass. split; [img_try (img_apply In_zseq; unfold kBatchClass; img_lia) | img_try (left; img_refl)].
- intros lb initr Hrev. destruct (last_facts lb initr Hrev) as (_ & _ & _ & _ & _ & Hin & EQ). rewrite EQ.
pose proof (YF0w.nb_vs_batch B ly X rd0 M Hci l Hl Hlne sp0 HSP lb Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kBatchBytes in D. unfold coff in *. img_lia.
Qed.
End h.
End g.
End f.
