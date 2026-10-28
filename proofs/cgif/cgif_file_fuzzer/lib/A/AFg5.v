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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFew AFgq AFh4 AFg3 AB13.
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
Section h.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : chunk).
Hypothesis ENQ : enq_pre B ly X W regs mem md k.
Hypothesis HNB : need_new_batch (st_qthread X) = true.
Variable l : list Z.
Hypothesis Hl : pc_chunks (cache X kBatchClass) = l.
Hypothesis Hlne : l <> [].
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread X).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Definition cnt : Z := Z.of_nat (length l).
Definition coff : Z := last l 0.
Definition jw (a : Z) : Z := match rdword rd0 a with Some w => w | None => 0 end.
Definition jst : Z := jw (T + t_cache_stats + 16).
Lemma M : ARm B ly X rd0. Proof. exact (proj1 (proj1 ENQ)). Qed.
Let WF : Wf (as_universe B) X := am_wf B ly X rd0 M.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma Hk : In k (st_chunks X). Proof. destruct ENQ as (_ & _ & _ & _ & Hk & _). exact Hk. Qed.
Lemma Hst : ck_state k = CQuarantined. Proof. destruct ENQ as (_ & _ & _ & _ & _ & Hst & _). exact Hst. Qed.
Lemma Hnq : ~ In (ck_beg k) (map ck_beg (q_items X)). Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & Hnq & _). exact Hnq. Qed.
Lemma Hci : st_cache_inited X = true.
Proof.
pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia))) as WC. unfold wf_class in WC.
destruct (st_cache_inited X) eqn:E; [reflexivity|]. exfalso. apply Hlne. rewrite <- Hl, WC. reflexivity.
Qed.
Lemma KF : cfacts B ly X k. Proof. exact (chunk_facts B ly X rd0 k M Hk). Qed.
Local Notation E0 := (AFgq.E0 ly regs u nn q cnt coff jst).
Local Notation QSZv := (AFgq.QSZv q).
Local Notation QFv := (AFgq.QFv ly q).
Local Notation QLv := (AFgq.QLv ly q).
Local Notation QBv := (AFgq.QBv q).
Local Notation CPv := (AFgq.CPv coff).
Local Notation NBv := (AFgq.NBv ly coff).
Local Notation CSLv := (AFgq.CSLv ly cnt).
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
Lemma HSP : ly_stk_lo ly + QSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _). unfold spZ in *. unfold sp0. lia. Qed.
Lemma IMG : img_cover ly.
Proof. destruct ENQ as ((_ & LED & _) & _). exact (img_cover_of_ledger ly X md LED). Qed.
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
pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QE. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QL). apply qloosem_loose in QL.
pose proof (YG0m.batches_len_fuel _ _ _ _ X WF QL) as BE  .
destruct QL as (T1 & _ & _). pose proof u_facts as (_ & _ & _ & NN).
pose proof (sum_bytes_ge (qc_list q) ltac:(intros y Hy; unfold all_batches; apply in_app_iff; left; exact Hy)) as S1.
unfold all_batches in BE. rewrite length_app in BE.
unfold AFgq.QBv, AFgq.QSZv, AFgq.QFv, kBatchBytes, EV_MAX in *. splits; try lia.
- destruct (qc_list q) as [|b t] eqn:Eq; [lia|]. destruct (AFf2.batch_geom B ly X rd0 M l sp0 HSP b ltac:(unfold all_batches; apply in_app_iff; left; rewrite Eq; left; reflexivity)) as (xb & Eb & Pb & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & _). pose proof HI as (P1 & _). unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in P1. lia.
- destruct (qc_list q) as [|b t] eqn:Eq; [ceil; unfold ASAN_CEIL; lia|]. destruct (AFf2.batch_geom B ly X rd0 M l sp0 HSP b ltac:(unfold all_batches; apply in_app_iff; left; rewrite Eq; left; reflexivity)) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5). unfold kBatchBytes in *. lia.
Qed.
Lemma last_facts : forall lb initr, rev (qc_list q) = lb :: initr ->
ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize /\ QLv mod 8192 = 0 /\
val_mem tfibsegs m0 (QLv + 16) 8 kBatchSlots /\ (forall a, QLv <= a < QLv + 8 -> apresent H0 mem a) /\ In lb (all_batches X) /\ QLv = SB + b_self lb.
Proof.
intros lb initr Hrev. pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL). pose proof (HL lb initr Hrev) as [L1 L2].
destruct (AFf2.last_in ly X lb initr Hrev) as [Hin EQ]. change (AFf2.QLv ly X) with QLv in EQ.
destruct (AFf2.batch_geom B ly X rd0 M l sp0 HSP lb Hin) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5). pose proof HI as (P1 & P2 & _).
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
rewrite EQ. splits; try lia.
- rewrite Eb. apply Z.mod_divide; [lia|]. apply Z.mod_divide in R3 as [c Hc]; [|lia]. apply Z.mod_divide in Ab as [c' Hc']; [|unfold kBatchBytes; lia]. exists (8 * c + c'). unfold kBatchBytes in Hc'. lia.
- replace (SB + b_self lb + 16) with (aeval B ly (aoff (batch_exp lb) 16)) by (cbn; lia). rewrite <- FULL. apply (cell_stateZ _ _ 8 _ (IN _ CNTc) eq_refl).
- intros a Ha. pose proof (cell_state _ _ 8 _ (IN _ NXc) eq_refl) as V. cbn [aeval batch_exp] in V.
replace a with (SB + b_self lb + (a - (SB + b_self lb))) by lia. apply (val_mem_present _ 8 _ _ V); [cbn; lia | apply off_img_high; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, kSpaceSize, kBatchBytes, ASAN_CEIL in *; lia].
- exact Hin.
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
apply vis_apresent; [cbn [aeval]; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg, ASAN_CEIL in *; lia|].
apply (vis_range (ASp (region_off kBatchClass)) (rg_mapped_user (reg X kBatchClass))); [right; left | lia].
unfold aareas. rewrite !in_app_iff. left. apply in_flat_map. exists kBatchClass. split; [apply In_zseq; unfold kBatchClass; lia | left; reflexivity].
- intros lb initr Hrev. destruct (last_facts lb initr Hrev) as (_ & _ & _ & _ & _ & Hin & EQ). rewrite EQ.
pose proof (AFf2.nb_vs_batch B ly X rd0 M Hci l Hl Hlne sp0 HSP lb Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kBatchBytes in D. unfold coff in *. lia.
Qed.
Lemma E2 : ew E0 2 = getr regs 2. Proof. exact (AFgq.E2 ly regs u nn q cnt coff jst). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EqSB : ew E0 33 = w64 SB. Proof. reflexivity. Qed.
Lemma EqU : ew E0 34 = w64 u. Proof. reflexivity. Qed.
Lemma EqN : ew E0 35 = w64 nn. Proof. reflexivity. Qed.
Lemma EqQSZ : ew E0 36 = w64 QSZv. Proof. reflexivity. Qed.
Lemma EqQF : ew E0 37 = w64 QFv. Proof. reflexivity. Qed.
Lemma EqQL : ew E0 38 = w64 QLv. Proof. reflexivity. Qed.
Lemma EqQB : ew E0 39 = w64 QBv. Proof. reflexivity. Qed.
Lemma EqCNT : ew E0 40 = w64 cnt. Proof. reflexivity. Qed.
Lemma EqCP : ew E0 41 = w64 CPv. Proof. reflexivity. Qed.
Lemma EqJST : ew E0 42 = w64 jst. Proof. reflexivity. Qed.
Lemma EqNB : ew E0 43 = w64 NBv. Proof. reflexivity. Qed.
Lemma EqCSL : ew E0 44 = w64 CSLv. Proof. reflexivity. Qed.
Lemma chunk_lit : forall a (w : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | rewrite Z.add_0_l; exact Hm]. Qed.
Lemma chunk_lit_at : forall base a (w : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
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
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI)))); unfold kThreadObjSize, t_qc, t_cache, t_cache_stats, AFgq.CSLv in *; lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac r4 := change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia.
Local Ltac lit_region :=
reg_intro; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; lia | cbn; lia] |]); apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) AFgq.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & _). pose proof HSP as [S1 S2].
pose proof root_vals as (V1 & V2 & V3 & V4). pose proof cache_vals as (C1 & C2 & C3 & C4 & C5). pose proof jst_val as [J1 J1R]. pose proof q_facts as (Qa & Qb & Qc & Qd). assert (Qc0 : 0 <= QSZv) by (unfold AFgq.QSZv; clear; lia).
assert (QLR : 0 <= QLv < ASAN_CEIL).
{ unfold AFgq.QLv. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [ceil; unfold ASAN_CEIL; lia|].
pose proof (last_facts lb initr Hrev) as (L1 & L2 & _). unfold AFgq.QLv in L1, L2. rewrite Hrev in L1, L2. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. lia. }
pose proof u_facts as (Ua & Ub & Uc & Ud).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hN1, hN2, S1, S2, QLR, Qb, Qd, Ua, Ub.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
unfold AFgq.REG0, AFgq.R_ROOT, AFgq.R_CNT, AFgq.R_JST, flit4, flit8, fatom8.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- 64)); [rewrite E2; reflexivity | lia | lia |].
intros a Ha. apply apresent_writable; [unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia | apply HPRES; clear -Ha; unfold QSTACK in *; lia]. }
apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_qc in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 88); [apply (val_mem_writable _ _ _ _ V1) | destruct (Z_lt_le_dec o 96); [apply (val_mem_writable _ _ _ _ V2) | destruct (Z_lt_le_dec o 104); [apply (val_mem_writable _ _ _ _ V3) | apply (val_mem_writable _ _ _ _ V4)]]];
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 36%nat 0 QSZv); [rewrite Z.sub_0_r; reflexivity | lia | exact V1 | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 37%nat 0 QFv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V2 | lia] | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 38%nat 0 QLv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V3 | lia] | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 39%nat 0 QBv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V4 | lia] | r8 | cbn; lia]. }
apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_cache in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ C1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom _ _ 4 40%nat 0 cnt); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact C1 | lia] | r4 | cbn; lia]. }
apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_cache_stats in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ J1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom _ _ 8 42%nat 0 jst); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact J1 | lia] | r8 | cbn; lia]. }
apply Forall_cons. {   reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 SB); [rewrite Z.sub_0_r; reflexivity | lia | | r8 | cbn; lia].
rewrite Z.add_0_l. replace 666040 with (aeval B ly (AInst o_space)) by (cbn; rewrite (ts_inst B TB); reflexivity).
replace SB with (aeval B ly (ASp 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity. }
do 3 (apply Forall_cons; [lit_region|]). apply Forall_nil.
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 AFgq.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof (AFf2.SX B ly X rd0 M l 2 8 _ _ eq_refl eq_refl ltac:(lia)) as DTS. unfold zdisjoint in DTS. cbn [fst snd] in DTS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply pairwise_disjoint_of_extents. unfold AFgq.REG0, AFgq.R_ROOT, AFgq.R_CNT, AFgq.R_JST, flit4, flit8, fatom8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E2, EqT. unfold w64. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, QSTACK in *.
fold sp0. rewrite !unsigned_lit_small by lia.
unfold t_qc, t_cache, t_cache_stats. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in hT1.
repeat split; first [clear hT1; lia | clear - hT1 CR0; lia].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms AFgq.FFQ).
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & _). pose proof HSP as [S1 S2].
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof q_facts as (Qa & Qb & Qc & Qd). pose proof cache_vals as (_ & _ & _ & C4 & C5). pose proof jst_val as [_ JR].
pose proof hit_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
assert (QLR : 0 <= QLv < ASAN_CEIL /\ QLv mod 8192 = 0).
{ unfold AFgq.QLv. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [ceil; unfold ASAN_CEIL; split; [lia | reflexivity]|].
pose proof (last_facts lb initr Hrev) as (L1 & L2 & L3 & _). unfold AFgq.QLv in L1, L2, L3. rewrite Hrev in L1, L2, L3. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. split; [lia | exact L3]. }
destruct QLR as [QLR QLA].
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hN1, hN2, S1, S2, U1, U2, QLR, F2, F4, F5, Qb, Qd.
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
cbn [AFgq.FFQ f_atoms atoms_ok]. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, QSTACK.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 32%nat T); [exact EqT| | | |]. all: clear - CR0 hT1 hT2 TAL; first [lia | exact TAL]. }
split. { apply (AF 33%nat SB); [exact EqSB| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [lia | exact SAL]. }
split. { apply (AF 34%nat u); [exact EqU| | | |]. all: clear - CR0 U1 U2 U3 U4; first [lia | change (2 ^ 4) with 16; exact U3]. }
split. { apply (AF 35%nat nn); [exact EqN| | | |]. all: clear - CR0 U4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 36%nat QSZv); [exact EqQSZ| | | |]. all: clear - CR0 Qc; unfold AFgq.QSZv in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 37%nat QFv); [exact EqQF| | | |]. all: clear - CR0 Qd; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 38%nat QLv); [exact EqQL| | | |]. all: clear - CR0 QLR QLA; first [lia | change (2 ^ 13) with 8192; exact QLA]. }
split. { apply (AF 39%nat QBv); [exact EqQB| | | |]. all: clear - CR0 Qa Qb U4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 40%nat cnt); [exact EqCNT| | | |]. all: clear - CR0 C4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 41%nat CPv); [exact EqCP| | | |]. all: clear - CR0 F1 F2 F3; unfold AFgq.CPv; first [pose proof (Z.div_pos coff 16); pose proof (Z.div_lt_upper_bound coff 16 (2 ^ 27)); lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 42%nat jst); [exact EqJST| | | |]. all: clear - CR0 JR; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 43%nat NBv); [exact EqNB| | | |]. all: clear - CR0 F4 F5 F6 hP1 hP2 hSP1 hSP2; first [lia | change (2 ^ 13) with 8192; exact F6]. }
split; [|exact I]. { apply (AF 44%nat CSLv); [exact EqCSL| | | |]. all: clear - CR0 C4 C5 hT1 hT2 TAL; unfold AFgq.CSLv, t_cache in *;
first [lia | change (2 ^ 2) with 4; apply Z.mod_divide in TAL as [c Hc]; [|lia]; rewrite Hc; apply Z.mod_divide; [lia|]; exists (1024 * c + 536 + (cnt - 1)); lia]. }
Qed.
Lemma SEED_ok : st_ok tfibsegs E0 AFgq.SS0 (restrict (w_H W) (mkst regs (w64 0x357d0) mem (seg_rom tfibsegs))).
Proof.
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1 & Ha3 & Ha4 & _). rewrite (ts_tp _ TB) in Htp.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof HI as (hP1 & hP2 & hT1 & hT2 & _). ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in hT1, hT2, U1, U2.
rewrite restrict_mkst_fx. unfold AFgq.SS0, AFgq.SR0, sr_set. cbn [bv_eqb]. unfold AFgq.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Htp] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |].
+ cbn [sv_denot]. fold (AFgq.E0 ly regs u nn q cnt coff jst). rewrite EqT, Ha0. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (AFgq.E0 ly regs u nn q cnt coff jst). rewrite EqT, Ha1. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (AFgq.E0 ly regs u nn q cnt coff jst). rewrite EqU, Ha3. unfold w64, kChunkHeaderSize. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (AFgq.E0 ly regs u nn q cnt coff jst). rewrite EqN, Ha4. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.
Theorem FH_ok : AFgq.free_hyps W ly regs mem u nn q cnt coff jst.
Proof.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & QL).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof q_facts as QF. pose proof cache_vals as (C1 & C2 & C3 & C4 & C5). pose proof jst_val as [_ JR].
pose proof hit_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
constructor.
- exact LO.
- rewrite (ts_tp _ TB) in Htp. exact Htp.
- exact Hra.
- exact Hra4.
- split; [exact Hlo | exact Hhi].
- exact Hal.
- exact HPRES.
- split; [exact u_zone | exact U3].
- exact IMG.
- exact U4.
- exact QF.
- exact HNB.
- intros lb initr Hrev. pose proof (last_facts lb initr Hrev) as (L1 & L2 & L3 & L4 & L5 & _). splits; assumption.
- exact C4.
- intros _. splits; assumption.
- exact JR.
- exact SEED_ok.
Qed.
Local Notation WINq := (AFgq.WIN ly regs q cnt coff).
Local Notation S' := (AFf2.S' X k l).
Lemma enqueue_hit_eq : enqueue k X = IRet (tt, S').
Proof.
pose proof Hci as CI. clear - CI HNB Hl Hlne.
unfold enqueue, cache_alloc, init_cache_if_needed, refill_if_empty, get_pc, set_pc, get, put, modify, ret, bind. cbn [ibind].
rewrite HNB. cbn [ibind]. rewrite CI. cbn [ibind].
change (znth pclass0 kBatchClass (st_cache X)) with (cache X kBatchClass). rewrite Hl.
destruct l as [|x t]; [congruence|]. cbn [ibind]. fold (cache X kBatchClass). rewrite Hl. cbn [ibind]. reflexivity.
Qed.
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
destruct C12 as [C1 C2]. destruct D12 as [D1 D2].
unfold zdisjoint in *. cbn [fst snd] in *. repeat match goal with G : _ /\ _ |- _ => destruct G as [? ?] end. splits; assumption.
Qed.
Lemma WIN_zone : forall a, WINq a -> (sp0 - 64 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize).
Proof.
intros a Hw. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & HL).
unfold AFgq.WIN, AFgq.WINT, AFgq.WINA in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[Hw|[[_ Hw]|[Hq Hw]]]].
- left. exact Hw.
- right; left. clear - Hw. unfold t_qc, t_cache, t_cache_stats, kThreadObjSize in *. lia.
- right; right. clear - Hw hN1 hN2 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. lia.
- right; right. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev.
+ exfalso. apply Hq. rewrite <- (rev_involutive (qc_list q)), Hrev. reflexivity.
+ pose proof (HL lb initr eq_refl) as [L1 L2]. unfold AFgq.QLv in Hw, L1, L2. rewrite Hrev in Hw, L1, L2.
clear - Hw L1 L2 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. lia.
Qed.
Lemma WIN_dec : forall a, WINq a \/ ~ WINq a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
pose proof cache_vals as (_ & _ & _ & _ & C5).
assert (LQ : qc_list q = [] \/ qc_list q <> []) by (destruct (qc_list q); [left; reflexivity | right; discriminate]).
unfold AFgq.WIN, AFgq.WINT, AFgq.WINA. fold sp0.
destruct (EM (sp0 - 64) sp0) as [C|C0]; [left; left; exact C|].
destruct (EM (T + t_qc) (T + t_qc + 32)) as [C|C1]; [left; right; left; left; exact C|].
destruct (EM (T + t_cache + 1920) (T + t_cache + 1924)) as [C|C2]; [left; right; left; right; left; exact C|].
destruct (EM (T + t_cache_stats + 16) (T + t_cache_stats + 24)) as [C|C3]; [left; right; left; right; right; exact C|].
destruct (EM NBv (NBv + 32)) as [C|C4]; [left; right; right; left; split; [exact C5 | exact C]|].
destruct LQ as [LQ|LQ].
- right. intros [X0|[[X1|[X2|X3]]|[[_ X4]|[X5 _]]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (C4 X4) | exact (X5 LQ)].
- destruct (EM QLv (QLv + 8)) as [C|C6]; [left; right; right; right; split; [exact LQ | exact C]|].
right. intros [X0|[[X1|[X2|X3]]|[[_ X4]|[_ X5]]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (C4 X4) | exact (C6 X5)].
Qed.
Definition low_okq (a w : Z) : bool :=
((TFIB_IMG_LO <=? a) && (a + w <=? TFIB_IMG_END)) || ((SHADOW_OFF + TFIB_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFIB_IMG_END / 8)).
Definition const_loc_okq (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => low_okq a w
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okq (TFIB_TSD + o) w
| ATp o => low_okq (TFIB_TP + o) w
| AInst o => low_okq (TFIB_INST + o) w
| _ => false
end.
Lemma Tfib_const_locq : forallb const_loc_okq (Tfib_const ly) = true.
Proof. clear. vm_compute. reflexivity. Qed.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Lemma CONST_OUT : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> ~ WINq (aeval B ly (c_at c) + i) /\ 0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) Tfib_const_locq c Hc) as K. unfold const_loc_okq in K.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & [C1 C2] & [D1 D2]).
assert (ZN : forall a, ~ ((sp0 - 64 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINq a).
{ intros a Hn Hw. exact (Hn (WIN_zone a Hw)). }
assert (LOW : forall a, low_okq a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ WINq (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold low_okq in L.
split; [apply ZN|]; clear - L Hi hP1 hT1 hS1 S1; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, QSTACK, kThreadObjSize in *;
change (65536 / 8) with 8192 in *; change (6270976 / 8) with 783872 in *; lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [apply ZN|]; clear - K Hi hT1 hT2 S1 S2 G_PT G_TS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; lia.
- split; [apply ZN|]; clear - K Hi C1 C2 S1 S2 G_PC G_TC G_CS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [apply ZN|]; clear - K Hi D1 D2 S1 S2 G_PD G_TD G_DS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
clear. intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma FINQH : forall W' c', AFh4.at_RETQ W ly regs mem md u nn q cnt coff W' c' -> enq_leaf B ly X W regs mem md k (tt, S') W' c'.
Proof.
intros W' c' HR.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & HQL).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
destruct HR as (-> & regs' & mem' & mat & -> & CS & MEQ' & PRESW & VALS). cbv zeta in VALS.
destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & VL).
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof HSP as HSP'. pose proof cache_vals as (_ & _ & _ & C4 & C5).
assert (ENB : NBv = SB + (region_off kBatchClass + last l 0)) by (unfold AFgq.NBv, coff; lia).
assert (WD : forall a, WINq a -> AFf2.D ly X l sp0 a).
{ intros a Hw. unfold AFf2.D, AFf2.DT, AFf2.DN, AFf2.DL, AFf2.DS.
unfold AFgq.WIN, AFgq.WINT, AFgq.WINA in Hw. fold sp0 in Hw. rewrite ENB in Hw.
destruct Hw as [Hw|[Hw|[[_ Hw]|[Hq Hw]]]].
- do 3 right. clear - Hw. unfold QSTACK. lia.
- left. exact Hw.
- right; left. exact Hw.
- right; right; left. split; [exact Hq|]. unfold AFf2.QLv. unfold AFgq.QLv in Hw. exact Hw. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFf2.D ly X l sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same. apply (MEQ' (Z_to_bv 64 a)). rewrite unsigned_lit_small by exact Ha. intros X'. exact (ND (WD a X')). }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. subst rd rd'. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem' x); discriminate|].
destruct (mem' x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (WIN_dec a') as [C|C].
- destruct (PRESW a' C) as [_ [bb Hb]]. unfold w64 in Hb. rewrite Ex in Hb. congruence.
- rewrite (MEQ' x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
destruct (WIN_dec a) as [C|C].
- exfalso. destruct (PRESW a C) as [Hh _]. unfold w64 in Hh. fold x in Hh. rewrite Hx in Hh. discriminate.
- apply (MEQ' x). rewrite Ux. exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd' (a' + Z.of_nat i) = Some (YG0f.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. subst rd'. exact (val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (NEW_qs : forall i, (i < 8)%nat -> rd' (T + t_qc + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length (qc_list q)) + 1) 8 i)).
{ apply (VM _ _ 8%nat _ _ V1); [reflexivity | unfold AFgq.QSZv; reflexivity]. }
assert (NEW_qf : forall i, (i < 8)%nat -> rd' (T + t_qc + 8 + Z.of_nat i) =
Some (YG0f.le_byte (match qc_list q with [] => SB + (region_off kBatchClass + last l 0) | b0 :: _ => SB + b_self b0 end) 8 i)).
{ apply (VM _ _ 8%nat _ _ V2); [reflexivity|]. unfold AFh4.QF', AFgq.QFv. rewrite ENB. destruct (qc_list q); reflexivity. }
assert (NEW_ql : forall i, (i < 8)%nat -> rd' (T + t_qc + 16 + Z.of_nat i) = Some (YG0f.le_byte (SB + (region_off kBatchClass + last l 0)) 8 i)).
{ apply (VM _ _ 8%nat _ _ V3); [reflexivity | exact ENB]. }
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (T + t_qc + 24 + Z.of_nat i) = Some (YG0f.le_byte (qc_bytes q + nn + kBatchBytes) 8 i)).
{ apply (VM _ _ 8%nat _ _ V4); [reflexivity | unfold AFgq.QBv; reflexivity]. }
assert (NEW_cnt : forall i, (i < 4)%nat -> rd' (T + t_cache + 1920 + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length l) - 1) 4 i)).
{ apply (VM _ _ 4%nat _ _ V5); [reflexivity | unfold cnt; reflexivity]. }
assert (NEW_n0 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + Z.of_nat i) = Some (YG0f.le_byte 0 8 i)).
{ apply (VM _ _ 8%nat _ _ V6); [exact ENB | reflexivity]. }
assert (NEW_n8 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + 8 + Z.of_nat i) = Some (YG0f.le_byte (nn + kBatchBytes) 8 i)).
{ apply (VM _ _ 8%nat _ _ V7); [rewrite ENB; reflexivity | reflexivity]. }
assert (NEW_n16 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + 16 + Z.of_nat i) = Some (YG0f.le_byte 1 8 i)).
{ apply (VM _ _ 8%nat _ _ V8); [rewrite ENB; reflexivity | reflexivity]. }
assert (NEW_n24 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + 24 + Z.of_nat i) = Some (YG0f.le_byte (u - 16) 8 i)).
{ apply (VM _ _ 8%nat _ _ V9); [rewrite ENB; reflexivity | reflexivity]. }
assert (NEW_lnext : forall lb initr, rev (qc_list q) = lb :: initr ->
forall i, (i < 8)%nat -> rd' (SB + b_self lb + Z.of_nat i) = Some (YG0f.le_byte (SB + (region_off kBatchClass + last l 0)) 8 i)).
{ intros lb initr Hrev. apply (VM _ _ 8%nat _ _ (VL lb initr Hrev)); [| exact ENB]. unfold AFgq.QLv. rewrite Hrev. reflexivity. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [exact (proj1 (Forall_forall _ _) (am_const B ly X _ M') c Hc)|].
intros i Hi. subst rd rd'. destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as [X1 X2]. apply aview_same.
apply (MEQ' (Z_to_bv 64 _)). rewrite unsigned_lit_small by exact X2. exact X1. }
pose proof (AFf2.enq_fin_ARm B TB ly X rd rd' M' k Hk Hst Hnq HNB   Hci l Hl Hlne sp0 HSP' IMG AG VIS
NEW_qs NEW_qf NEW_ql NEW_qb NEW_cnt NEW_n0 NEW_n8 NEW_n16 NEW_n24 NEW_lnext CONST' Hbev) as MF.
exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md), (Some (region_off kBatchClass + last l 0)). split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
2:{ split; [reflexivity|]. split; [exact HNB|]. split; [reflexivity|]. split; reflexivity. }
split; [|split; [apply layout_le_refl | split; [apply wle_refl | split; [|split; [|split]]]]].
- split; [exact MF | split; [|split; [|split]]].
+ eapply ALedger_same; [exact (AFf2.ALedger_S' ly X k l tfibsegs md LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
+ destruct BUD as [BUD PIN]. split; [| exact (AFf2.asecA_S' ly X k l _ PIN)].
eapply Z.le_trans; [exact BUD|]. rewrite <- (AFf2.abudget_S' X k l). apply Z.le_refl.
+ eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
+ eapply (ahs_transfer tfibsegs B ly X _ (w_H W) mem mem' (al_img_env tfibsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
* eapply (aclient_band_same_frames B ly X); [exact MF | reflexivity].
*   reflexivity.
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. apply AG; [clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; lia|].
pose proof HI as (hP1 & _ & hT1 & _ & hS1 & _ & _ & _ & hN1 & _ & hL).
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in hP1, hT1, hS1.
unfold AFf2.D, AFf2.DT, AFf2.DN, AFf2.DL, AFf2.DS. change (st_qthread X) with q. intros [Y|[Y|[[Hq Y]|Y]]].
-- clear - Y SBg hT1. unfold t_qc, t_cache, t_cache_stats in Y. lia.
-- rewrite <- ENB in Y. clear - Y SBg hP1 hN1. lia.
-- destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [exfalso; apply Hq; rewrite <- (rev_involutive (qc_list q)), Hrev; reflexivity|].
destruct (hL lb initr eq_refl) as [L1 _]. unfold AFgq.QLv in L1. unfold AFf2.QLv in Y. rewrite Hrev in L1, Y.
clear - Y SBg hP1 L1. lia.
-- clear - Y SBg hS1 HSP'. unfold QSTACK in *. lia.
- intros r Hr'. apply CS. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - R. unfold CALLEE_SAVED.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst r; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
- apply same_io_wvb.
- intros a Ha NO NO' NS NE. apply AG; [exact Ha|]. intros HD.
destruct (AFf2.D_owned B ly X rd M' k Hci l Hl Hlne sp0 HSP' a (proj1 Ha) HD) as [O|O]; [exact (NO O) | apply NS; unfold ascratch, spZ; left; exact O].
- intros a Ha. unfold spZ in Ha. fold sp0 in Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [Hb|Hb].
+ apply (apresent_same (w_H W) mem); [|apply HPRES; exact Ha]. apply MEQ'. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _).
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha Usp HSP' hS1; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; lia). rewrite unsigned_lit_small by exact Ha'.
intros Hw. pose proof (WIN_zone a Hw) as Z3. pose proof GEO as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
clear - Z3 Ha Hb G_PT G_PS G_TS HSP' hT1 hT2 hP1 hP2. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *. lia.
+ apply PRESW. unfold AFgq.WIN. left. fold sp0. lia.
Qed.
Theorem tfib_enqueue_hit_arm :
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (enq_leaf B ly X W regs mem md k).
Proof.
rewrite enqueue_hit_eq. cbn [amreal]. pose proof cache_vals as (_ & _ & _ & _ & C5).
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
eapply SRr_mono.
- exact (AFh4.segQH W ly regs mem md u nn q cnt coff jst (m_vm_materialized md) FH_ok C5).
- intros W' c' _ HR. exact (FINQH W' c' HR).
Qed.
End h.
Theorem tfib_enqueue_hit : forall B, TfibSyms B -> forall ly X W regs mem md k,
enq_pre B ly X W regs mem md k -> need_new_batch (st_qthread X) = true -> pc_chunks (cache X kBatchClass) <> [] ->
ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (enq_leaf B ly X W regs mem md k).
Proof.
intros B TB ly X W regs mem md k ENQ HNB Hne HTSD.
exact (tfib_enqueue_hit_arm B TB ly X W regs mem md k ENQ HNB (pc_chunks (cache X kBatchClass)) eq_refl Hne HTSD).
Qed.
End f.
