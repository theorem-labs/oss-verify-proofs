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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFex AFf0 AFfl AFf2 AFgi AFfu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFgq AB13.
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
Lemma combine_seq_last : forall (l0 : list Z) x0, In (length l0, x0) (combine (seq 0 (length (l0 ++ [x0]))) (l0 ++ [x0])).
Proof. intros l0 x0. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, (combine_snoc _ _ _ eq_refl). apply in_app_iff. right. left. reflexivity. Qed.
Section g.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (W : world tfibsegs) (mem : word -> option byte) (sp0 : Z) (k : chunk).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
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
Lemma KF : cfacts B ly X k. Proof. exact (chunk_facts B ly X rd0 k M Hk). Qed.
Local Notation QSZv := (AFgq.QSZv q).
Local Notation QFv := (AFgq.QFv ly q).
Local Notation QLv := (AFgq.QLv ly q).
Local Notation QBv := (AFgq.QBv q).
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros e w e' E. exact (tfib_const_lookup_sym B TB ly X H0 mem e w e' M E). Qed.
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
Lemma in_thread_junk : forall r, In r thread_junk -> In r (ajunk B ly X).
Proof. intros r Hr. unfold ajunk. right. right. do 5 (apply in_or_app; right). apply in_or_app. left. exact Hr. Qed.
Lemma val_mem_present : forall a (w : nat) v i, val_mem tfibsegs m0 a w v -> 0 <= i < Z.of_nat w -> off_img (a + i) -> apresent H0 mem (a + i).
Proof.
intros a w v i V Hi Hr. apply vis_apresent_off; [exact Hr|]. pose proof (V (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
unfold aview. rewrite E. discriminate.
Qed.
Lemma jst_val : val_mem tfibsegs m0 (T + t_cache_stats + 16) 8 jst /\ 0 <= jst < 2 ^ 64.
Proof.
destruct (vis_word H0 mem (T + t_cache_stats + 16)) as (w & Rw & Vw & Ew).
- intros i Hi. replace (T + t_cache_stats + 16 + i) with (aeval B ly (AT t_cache_stats) + (16 + i)) by (cbn; lia).
apply (vis_range (AT t_cache_stats) (t_stats - t_cache_stats)); [left; apply in_thread_junk; unfold thread_junk; cbn; tauto | unfold t_stats, t_cache_stats; lia].
- unfold jst, jw. rewrite Ew. auto.
Qed.
Lemma root_vals : val_mem tfibsegs m0 (T + t_qc) 8 QSZv /\ val_mem tfibsegs m0 (T + t_qc + 8) 8 QFv /\ val_mem tfibsegs m0 (T + t_qc + 16) 8 QLv /\ val_mem tfibsegs m0 (T + t_qc + 24) 8 QBv.
Proof.
assert (IN : forall c, In c (qc_cells (AT t_qc) q) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. apply in_app_iff. left. exact Hc. }
unfold AFgq.QSZv, AFgq.QFv, AFgq.QLv, AFgq.QBv. splits.
- apply (cell_stateZ _ (AT t_qc) 8 _ (IN _ ltac:(unfold qc_cells; left; reflexivity)) eq_refl).
- replace (T + t_qc + 8) with (aeval B ly (aoff (AT t_qc) 8)) by (cbn; lia).
replace (match qc_list q with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match qc_list q with [] => ANum 0 | b :: _ => batch_exp b end)) by (destruct (qc_list q); reflexivity).
apply (cell_state _ _ 8 _ (IN _ ltac:(unfold qc_cells; right; left; reflexivity)) eq_refl).
- replace (T + t_qc + 16) with (aeval B ly (aoff (AT t_qc) 16)) by (cbn; lia).
replace (match rev (qc_list q) with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match rev (qc_list q) with [] => ANum 0 | b :: _ => batch_exp b end)) by (destruct (rev (qc_list q)); reflexivity).
apply (cell_state _ _ 8 _ (IN _ ltac:(unfold qc_cells; right; right; left; reflexivity)) eq_refl).
- replace (T + t_qc + 24) with (aeval B ly (aoff (AT t_qc) 24)) by (cbn; lia).
apply (cell_stateZ _ _ 8 _ (IN _ ltac:(unfold qc_cells; do 3 right; left; reflexivity)) eq_refl).
Qed.
Lemma count_val : val_mem tfibsegs m0 (T + t_cache + 1920) 4 (if st_cache_inited X then Z.of_nat (length (pc_chunks (cache X kBatchClass))) else 0).
Proof.
assert (IN : forall c, In c (cache_cells X kBatchClass) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. right; left. apply in_flat_map. exists kBatchClass. split; [apply In_zseq; unfold kBatchClass; lia | exact Hc]. }
unfold cache_cells in IN.
replace (T + t_cache + 1920) with (aeval B ly (AT (t_cache + 80 * kBatchClass))) by (cbn; unfold kBatchClass; lia).
destruct (st_cache_inited X); apply (cell_stateZ _ _ 4 _ (IN _ ltac:(left; reflexivity)) eq_refl).
Qed.
Lemma u_zone : zone3 (u - 16) (nn + 16).
Proof.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof (AFfl.ext_rounded B ly X rd0 M k Hk) as (ER & NN1 & NN2 & NN3).
pose proof (req_size_bounds (ck_req k) ltac:(clear - G7; lia)) as (_ & Q1 & _).
assert (ZK : zone3 (ck_base B ly k) (ck_extent k)).
{ apply (zone3_intro ly (ck_base B ly k) (ck_extent k) IMG ltac:(clear - G5 G8 Q1; lia) G1).
apply AFex.zdisjoint_of_pointwise; [clear - G5 G8 Q1; lia | exact (proj1 (proj2 (lo_img _ LO))) |].
intros y Hy. exact (proj1 (chunk_apart B ly X rd0 k y M Hk Hy)). }
rewrite G4. clear - G5 ER NN1 NN2 NN3 ZK. ceil. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Lemma u_facts : 4096 + 16 <= u /\ u + nn <= ASAN_CEIL /\ u mod 16 = 0 /\ 1 <= nn < 2 ^ 28.
Proof.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3). unfold ck_n.
assert (LO16 : 4096 <= ck_base B ly k) by (clear - G1; unfold in_app in G1; lia).
rewrite G4. unfold MALLOC_MAX in G7. splits; try lia.
all: apply Z.mod_divide in G3 as [c Hc]; [|lia]; apply Z.mod_divide in G6 as [c' Hc']; [|lia]; rewrite Hc, Hc'; apply Z.mod_divide; [lia|]; exists (c + c'); lia.
Qed.
Lemma items_n_pos : forall b x, In b (all_batches X) -> In x (b_items b) -> 1 <= ck_n x.
Proof.
intros b x Hb Hx. pose proof (proj1 (Forall_forall _ _) (wq_items _ (wf_quarantine _ _ _ _ _ WF)) x ltac:(unfold q_items; apply in_flat_map; exists b; auto)) as [X1 _].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) x X1) as [N _]. unfold ck_n. pose proof (req_size_bounds (ck_req x) ltac:(lia)). lia.
Qed.
Lemma b_bytes_ge : forall b, In b (all_batches X) -> kBatchBytes <= b_bytes b.
Proof.
intros b Hb. unfold b_bytes.
assert (G : forall l0, incl l0 (b_items b) -> 0 <= fold_right (fun k0 acc => ck_n k0 + acc) 0 l0).
{ induction l0 as [|x t IH]; intros Hl0; cbn; [lia|]. pose proof (items_n_pos b x Hb (Hl0 x (or_introl eq_refl))). pose proof (IH ltac:(intros y Hy; apply Hl0; right; exact Hy)). lia. }
pose proof (G (b_items b) ltac:(intros y Hy; exact Hy)). lia.
Qed.
Lemma sum_bytes_ge : forall l0, incl l0 (all_batches X) -> 0 <= sum_bytes l0.
Proof.
induction l0 as [|b t IH]; intros Hl0; cbn; [unfold sum_bytes; cbn; lia|]. unfold sum_bytes in *. cbn.
pose proof (b_bytes_ge b (Hl0 b (or_introl eq_refl))). pose proof (IH ltac:(intros y Hy; apply Hl0; right; exact Hy)). unfold kBatchBytes in *. lia.
Qed.
Lemma q_facts : 0 <= QBv /\ QBv + nn + kBatchBytes <= 2 ^ 48 /\ QSZv < 2 ^ 40 /\ 0 <= QFv < ASAN_CEIL.
Proof.
pose proof (YG0m.batches_len_fuel _ _ _ _ X WF HQL) as BE  .
pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QE. destruct HQL as (T1 & _ & _). pose proof u_facts as (_ & _ & _ & NN).
pose proof (sum_bytes_ge (qc_list q) ltac:(intros y Hy; unfold all_batches; apply in_app_iff; left; exact Hy)) as S1.
unfold all_batches in BE. rewrite length_app in BE.
unfold AFgq.QBv, AFgq.QSZv, AFgq.QFv, kBatchBytes, EV_MAX in *. splits; try lia.
- destruct (qc_list q) as [|b t] eqn:Eq; [lia|]. destruct (AFf2.batch_geom B ly X rd0 M (pc_chunks (cache X kBatchClass)) sp0 HSP b ltac:(unfold all_batches; apply in_app_iff; left; rewrite Eq; left; reflexivity)) as (xb & Eb & Pb & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & _ & _ & R4 & _). pose proof (lo_high ly LO) as [P1 _]. unfold kHighMemBeg in R4, P1. lia.
- destruct (qc_list q) as [|b t] eqn:Eq; [ceil; unfold ASAN_CEIL; lia|]. destruct (AFf2.batch_geom B ly X rd0 M (pc_chunks (cache X kBatchClass)) sp0 HSP b ltac:(unfold all_batches; apply in_app_iff; left; rewrite Eq; left; reflexivity)) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5). unfold kBatchBytes in *. lia.
Qed.
Lemma last_facts : forall lb initr, rev (qc_list q) = lb :: initr ->
ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize /\ QLv mod 8192 = 0 /\
val_mem tfibsegs m0 (QLv + 16) 8 kBatchSlots /\ (forall a, QLv <= a < QLv + 8 -> apresent H0 mem a) /\ In lb (all_batches X) /\ QLv = SB + b_self lb.
Proof.
intros lb initr Hrev.
destruct (AFf2.last_in ly X lb initr Hrev) as [Hin EQ]. change (AFf2.QLv ly X) with QLv in EQ.
destruct (AFf2.batch_geom B ly X rd0 M (pc_chunks (cache X kBatchClass)) sp0 HSP lb Hin) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5). pose proof (lo_space_in ly LO) as [SI1 SI2].
pose proof (lo_high ly LO) as [P1 P2].
assert (E0 : qc_list q = rev initr ++ [lb]) by (rewrite <- (rev_involutive (qc_list q)), Hrev; reflexivity).
assert (IN : forall c, In c (batch_cells (qc_list q)) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. apply in_app_iff. left. unfold qc_cells. do 4 right. exact Hc. }
assert (CNTc : In (z8 (aoff (batch_exp lb) 16) (Z.of_nat (length (b_items lb)))) (batch_cells (qc_list q))).
{ apply In_batch_cells. exists (length (rev initr)), lb. rewrite E0. split; [rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity|]. unfold batch_own_cells. right; right; left. reflexivity. }
assert (NXc : In (c8 (batch_exp lb) (ANum 0)) (batch_cells (qc_list q))).
{ apply In_batch_cells. exists (length (rev initr)), lb. rewrite E0. split; [rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity|]. unfold batch_own_cells. left.
rewrite (next_exp_last _ _ (eq_sym (last_length _ _))). reflexivity. }
assert (FULL : Z.of_nat (length (b_items lb)) = kBatchSlots).
{ unfold need_new_batch in HNB. rewrite Hrev in HNB. apply Z.eqb_eq in HNB. exact HNB. }
assert (L1 : ly_prim ly <= SB + b_self lb) by lia.
assert (L2 : SB + b_self lb + kBatchBytes <= SB + kSpaceSize).
{ rewrite Eb. unfold region_base. rewrite region_off_eq by (unfold kBatchClass; lia). unfold kBatchClass, kBatchBytes, kSpaceSize in *. lia. }
rewrite EQ. splits; try lia.
- rewrite Eb. apply Z.mod_divide; [lia|]. apply Z.mod_divide in R3 as [c Hc]; [|lia]. apply Z.mod_divide in Ab as [c' Hc']; [|unfold kBatchBytes; lia]. exists (8 * c + c'). unfold kBatchBytes in Hc'. lia.
- replace (SB + b_self lb + 16) with (aeval B ly (aoff (batch_exp lb) 16)) by (cbn; lia). rewrite <- FULL. apply (cell_stateZ _ _ 8 _ (IN _ CNTc) eq_refl).
- intros a Ha. pose proof (cell_state _ _ 8 _ (IN _ NXc) eq_refl) as V. cbn [aeval batch_exp] in V.
replace a with (SB + b_self lb + (a - (SB + b_self lb))) by lia. apply (val_mem_present _ 8 _ _ V); [cbn; lia | apply off_img_high; ceil; unfold TFIB_IMG_END, kHighMemBeg, kSpaceSize, kBatchBytes, ASAN_CEIL in *; lia].
- exact Hin.
Qed.
Lemma chunk_lit : forall (E0 : env) a (w : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros E0 a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | rewrite Z.add_0_l; exact Hm]. Qed.
Lemma chunk_lit_at : forall (E0 : env) base a (w : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros E0 base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
Lemma chunk_atom : forall (E0 : env) base a (w : BinNums.N) k0 d x, ew E0 k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SOff k0 d))).
Proof.
intros E0 base a w k0 d x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfibsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfibsegs m0 o.
Proof. intros a w v o Hv Ho Ha. apply vis_writable_off; [exact Ha|]. replace o with (a + (o - a)) by lia. eapply val_mem_vis; [exact Hv | lia]. Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
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
assert (C12 : 4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) by (clear - IC; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia).
assert (D12 : 4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL) by (clear - ID; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia). clear IC ID.
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
Local Notation CPv := (AFgq.CPv coff).
Local Notation NBv := (AFgq.NBv ly coff).
Local Notation CSLv := (AFgq.CSLv ly cnt).
Lemma Hci : st_cache_inited X = true.
Proof.
pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia))) as WC. unfold wf_class in WC.
destruct (st_cache_inited X) eqn:E; [reflexivity|]. exfalso. apply Hlne. rewrite <- Hl, WC. reflexivity.
Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
ly_prim ly <= NBv /\ NBv + kBatchBytes <= SB + kSpaceSize /\
(forall lb initr, rev (qc_list q) = lb :: initr -> ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize).
Proof.
pose proof (AFf2.HIGH B ly X rd0 M Hci l Hl Hlne sp0 HSP IMG) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
unfold AFgq.NBv, coff. splits; try lia; try exact A3. exact A11.
Qed.
Lemma NBG : SB + (region_off kBatchClass + coff) = region_base ly kBatchClass + coff /\ 0 <= coff /\ coff mod kBatchBytes = 0 /\
coff + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\ rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= 2 ^ 31 /\
In coff (pc_chunks (cache X kBatchClass)) /\ ~ In coff (batch_offs X kBatchClass) /\ ~ In coff (chunk_offs X kBatchClass).
Proof. exact (AFf2.nb_geom B ly X rd0 M Hci l Hl Hlne). Qed.
Lemma cache_vals : val_mem tfibsegs m0 (T + t_cache + 1920) 4 cnt /\ val_mem tfibsegs m0 (T + t_cache + 1928) 8 8192 /\ val_mem tfibsegs m0 CSLv 4 CPv /\ 0 <= cnt <= 16 /\ 1 <= cnt.
Proof.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. rewrite Hci in WC. destruct WC as [PM PL].
pose proof (class_ok kBatchClass ltac:(unfold kBatchClass; lia)) as (_ & _ & _ & K4 & _). rewrite Hl in PL.
assert (LZ : length l <> 0%nat) by (intros E0; apply Hlne, length_zero_iff_nil; exact E0).
assert (IN : forall c, In c (cache_cells X kBatchClass) -> In c (acells B ly X)).
{ intros c Hc. unfold acells. rewrite !in_app_iff. right; left. apply in_flat_map. exists kBatchClass. split; [apply In_zseq; unfold kBatchClass; lia | exact Hc]. }
unfold cache_cells in IN. rewrite Hci, Hl in IN.
unfold AFgq.CSLv, AFgq.CPv, cnt. splits; try lia.
- replace (T + t_cache + 1920) with (aeval B ly (AT (t_cache + 80 * kBatchClass))) by (cbn; unfold kBatchClass; lia).
apply (cell_stateZ _ _ 4 _ (IN _ ltac:(left; reflexivity)) eq_refl).
- replace (T + t_cache + 1928) with (aeval B ly (aoff (AT (t_cache + 80 * kBatchClass)) 8)) by (cbn; unfold kBatchClass; lia).
apply (cell_stateZ _ _ 8 _ (IN _ ltac:(right; right; left; reflexivity))). reflexivity.
- replace (T + t_cache + 1936 + 4 * (Z.of_nat (length l) - 1)) with (aeval B ly (aoff (AT (t_cache + 80 * kBatchClass)) (16 + 4 * Z.of_nat (length l - 1)))) by (cbn; unfold kBatchClass; rewrite Nat2Z.inj_sub by lia; cbn; lia).
assert (SLOT_IN : In ((length l - 1)%nat, last l 0) (combine (seq 0 (length l)) l)).
{ set (x0 := last l 0). rewrite <- (removelast_app_last l 0 Hlne) at 2 3. fold x0.
replace (length l - 1)%nat with (length (removelast l)) by (rewrite removelast_length by exact Hlne; lia). apply combine_seq_last. }
apply (cell_stateZ _ _ 4 _ (IN _ ltac:(right; right; right; apply in_map_iff; exists ((length l - 1)%nat, last l 0); split; [reflexivity | exact SLOT_IN]))).
unfold coff. reflexivity.
Qed.
Lemma hit_facts : 0 <= coff /\ coff + kBatchBytes <= 2 ^ 31 /\ coff mod 16 = 0 /\ ly_prim ly <= NBv /\ NBv + kBatchBytes <= SB + kSpaceSize /\ NBv mod 8192 = 0 /\
(forall a, NBv <= a < NBv + 32 -> apresent H0 mem a) /\
(forall lb initr, rev (qc_list q) = lb :: initr -> NBv + kBatchBytes <= QLv \/ QLv + kBatchBytes <= NBv).
Proof.
pose proof NBG as (Eb & Pb & Ab & Ub & [AU MU] & INP & NIB & NIC). pose proof HI as (P1 & P2 & _ & _ & _ & _ & S1 & S2 & N1 & N2 & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
unfold AFgq.NBv in *. unfold kBatchBytes in *. splits; try lia.
all: try (apply Z.mod_divide in Ab as [c Hc]; [|lia]; rewrite Hc; apply Z.mod_divide; [lia|]; exists (512 * c); lia).
all: try (rewrite Eb; apply Z.mod_divide; [lia|]; apply Z.mod_divide in R3 as [c Hc]; [|lia]; apply Z.mod_divide in Ab as [c' Hc']; [|lia]; exists (8 * c + c'); lia).
- assert (BND : kHighMemBeg <= SB + (region_off kBatchClass + coff) /\ SB + (region_off kBatchClass + coff) + 8192 <= ASAN_CEIL) by (rewrite Eb; lia).
intros a Ha. replace a with (aeval B ly (ASp (region_off kBatchClass)) + (coff + (a - (SB + (region_off kBatchClass + coff))))) by (cbn [aeval]; lia).
apply vis_apresent_off; [apply off_img_high; cbn [aeval]; ceil; unfold TFIB_IMG_END, kHighMemBeg, ASAN_CEIL in *; lia|].
apply (vis_range (ASp (region_off kBatchClass)) (rg_mapped_user (reg X kBatchClass))); [right; left | lia].
unfold aareas. rewrite !in_app_iff. left. apply in_flat_map. exists kBatchClass. split; [apply In_zseq; unfold kBatchClass; lia | left; reflexivity].
- intros lb initr Hrev. destruct (last_facts lb initr Hrev) as (_ & _ & _ & _ & _ & Hin & EQ). rewrite EQ.
pose proof (AFf2.nb_vs_batch B ly X rd0 M Hci l Hl Hlne sp0 HSP lb Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kBatchBytes in D. unfold coff in *. lia.
Qed.
End h.
End g.
End f.
