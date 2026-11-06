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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF2l YF2z YF1y YF07.
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
Section h. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : chunk).
Hypothesis ENQ : enq_pre B ly X W regs mem md k.
Hypothesis HNB : need_new_batch (st_qthread X) = true.
Variable l : list Z.
Hypothesis Hl : pc_chunks (cache X kBatchClass) = l.
Hypothesis Hlne : l <> [].
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
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
Lemma M : ARm B ly X rd0. Proof. img_exact (proj1 (proj1 ENQ)). Qed.
Let WF : Wf (as_universe B) X := am_wf B ly X rd0 M.
Let LO : layout_ok ly := am_layout B ly X rd0 M.
Lemma Hk : In k (st_chunks X). Proof. destruct ENQ as (_ & _ & _ & _ & Hk & _). img_exact Hk. Qed.
Lemma Hst : ck_state k = CQuarantined. Proof. destruct ENQ as (_ & _ & _ & _ & _ & Hst & _). img_exact Hst. Qed.
Lemma Hnq : ~ In (ck_beg k) (map ck_beg (q_items X)). Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & Hnq & _). img_exact Hnq. Qed.
Lemma Hci : st_cache_inited X = true.
Proof.
pose proof (wr_cache _ _ _ _ _ _ (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia)))) as WC. unfold wf_class in WC.
destruct (st_cache_inited X) eqn:E; [img_refl|]. exfalso. img_apply Hlne. rewrite <- Hl, WC. img_refl.
Qed.
Lemma KF : cfacts B ly X k. Proof. img_exact (chunk_facts B ly X rd0 k M Hk). Qed.
Local Notation E0 := (YF2l.E0 ly regs u nn q cnt coff jst).
Local Notation QSZv := (YF2l.QSZv q).
Local Notation QFv := (YF2l.QFv ly q).
Local Notation QLv := (YF2l.QLv ly q).
Local Notation QBv := (YF2l.QBv q).
Local Notation CPv := (YF2l.CPv coff).
Local Notation NBv := (YF2l.NBv ly coff).
Local Notation CSLv := (YF2l.CSLv ly cnt).
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
Lemma HSP : ly_stk_lo ly + QSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _). unfold spZ in *. unfold sp0. img_lia. Qed.
Lemma IMG : img_cover ly.
Proof. destruct ENQ as ((_ & LED & _) & _). img_exact (img_cover_of_ledger ly X md LED). Qed.
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
pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QE. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QL).
pose proof (YG0s.batches_len_fuel _ _ _ _ X WF QL) as BE  .
destruct QL as (T1 & _ & _). pose proof u_facts as (_ & _ & _ & NN).
pose proof (sum_bytes_ge (qc_list q) ltac:(img_try (intros y Hy; unfold all_batches; img_apply in_app_iff; left; img_exact Hy))) as S1.
unfold all_batches in BE. rewrite length_app in BE.
unfold YF2l.QBv, YF2l.QSZv, YF2l.QFv, kBatchBytes, EV_MAX in *. splits; try img_lia.
- destruct (qc_list q) as [|b t] eqn:Eq; [img_lia|]. destruct (YF0w.batch_geom B ly X rd0 M l sp0 HSP b ltac:(img_try (unfold all_batches; img_apply in_app_iff; left; rewrite Eq; left; img_refl))) as (xb & Eb & Pb & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & _). pose proof HI as (P1 & _). unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg in P1. img_lia.
- destruct (qc_list q) as [|b t] eqn:Eq; [img_try (ceil; unfold ASAN_CEIL; img_lia)|]. destruct (YF0w.batch_geom B ly X rd0 M l sp0 HSP b ltac:(img_try (unfold all_batches; img_apply in_app_iff; left; rewrite Eq; left; img_refl))) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5). unfold kBatchBytes in *. img_lia.
Qed.
Lemma last_facts : forall lb initr, rev (qc_list q) = lb :: initr ->
ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize /\ QLv mod 8192 = 0 /\
val_mem tfxsegs m0 (QLv + 16) 8 kBatchSlots /\ (forall a, QLv <= a < QLv + 8 -> apresent H0 mem a) /\ In lb (all_batches X) /\ QLv = SB + b_self lb.
Proof.
intros lb initr Hrev. pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL). pose proof (HL lb initr Hrev) as [L1 L2].
destruct (YF0w.last_in ly X lb initr Hrev) as [Hin EQ]. img_change (YF0w.QLv ly X) with QLv in EQ.
destruct (YF0w.batch_geom B ly X rd0 M l sp0 HSP lb Hin) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5). pose proof HI as (P1 & P2 & _).
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
rewrite EQ. splits; try img_lia.
- rewrite Eb. img_apply Z.mod_divide; [img_lia|]. apply Z.mod_divide in R3 as [c Hc]; [|img_lia]. apply Z.mod_divide in Ab as [c' Hc']; [|img_try (unfold kBatchBytes; img_lia)]. exists (8 * c + c'). unfold kBatchBytes in Hc'. img_lia.
- replace (SB + b_self lb + 16) with (aeval B ly (aoff (batch_exp lb) 16)) by (img_try (cbn; img_lia)). rewrite <- FULL. img_apply (cell_stateZ _ _ 8 _ (IN _ CNTc) eq_refl).
- intros a Ha. pose proof (cell_state _ _ 8 _ (IN _ NXc) eq_refl) as V. cbn [aeval batch_exp] in V.
replace a with (SB + b_self lb + (a - (SB + b_self lb))) by img_lia. img_apply (val_mem_present _ 8 _ _ V); [img_try (cbn; img_lia) | img_try (img_apply off_img_high; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, kHighMemBeg, kSpaceSize, kBatchBytes, ASAN_CEIL in *; img_lia)].
- img_exact Hin.
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
img_apply vis_apresent; [img_try (cbn [aeval]; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END, kHighMemBeg, ASAN_CEIL in *; img_lia)|].
img_apply (vis_range (ASp (region_off kBatchClass)) (rg_mapped_user (reg X kBatchClass))); [img_try (right; left) | img_lia].
unfold aareas. rewrite !in_app_iff. left. img_apply in_flat_map. exists kBatchClass. split; [img_try (img_apply In_zseq; unfold kBatchClass; img_lia) | img_try (left; img_refl)].
- intros lb initr Hrev. destruct (last_facts lb initr Hrev) as (_ & _ & _ & _ & _ & Hin & EQ). rewrite EQ.
pose proof (YF0w.nb_vs_batch B ly X rd0 M Hci l Hl Hlne sp0 HSP lb Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kBatchBytes in D. unfold coff in *. img_lia.
Qed.
Lemma E2 : ew E0 2 = getr regs 2. Proof. img_exact (YF2l.E2 ly regs u nn q cnt coff jst). Qed.
Lemma EqT : ew E0 32 = w64 T. Proof. img_refl. Qed.
Lemma EqSB : ew E0 33 = w64 SB. Proof. img_refl. Qed.
Lemma EqU : ew E0 34 = w64 u. Proof. img_refl. Qed.
Lemma EqN : ew E0 35 = w64 nn. Proof. img_refl. Qed.
Lemma EqQSZ : ew E0 36 = w64 QSZv. Proof. img_refl. Qed.
Lemma EqQF : ew E0 37 = w64 QFv. Proof. img_refl. Qed.
Lemma EqQL : ew E0 38 = w64 QLv. Proof. img_refl. Qed.
Lemma EqQB : ew E0 39 = w64 QBv. Proof. img_refl. Qed.
Lemma EqCNT : ew E0 40 = w64 cnt. Proof. img_refl. Qed.
Lemma EqCP : ew E0 41 = w64 CPv. Proof. img_refl. Qed.
Lemma EqJST : ew E0 42 = w64 jst. Proof. img_refl. Qed.
Lemma EqNB : ew E0 43 = w64 NBv. Proof. img_refl. Qed.
Lemma EqCSL : ew E0 44 = w64 CSLv. Proof. img_refl. Qed.
Lemma chunk_lit : forall a (w : BinNums.N) x, val_mem tfxsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 0 (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (rewrite Z.add_0_l; img_exact Hm)]. Qed.
Lemma chunk_lit_at : forall base a (w : BinNums.N) x, val_mem tfxsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)]. Qed.
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
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI)))); unfold kThreadObjSize, t_qc, t_cache, t_cache_stats, YF2l.CSLv in *; img_lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8 := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Local Ltac r4 := img_change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); img_lia.
Local Ltac lit_region :=
reg_intro; split; [img_lia|]; split; [img_lia|]; split; [img_try (intros o Ho; img_lia)|];
repeat (img_apply Forall_cons; [img_try (img_apply chunk_lit; [img_apply cell_lit; (img_case; vm_compute); img_refl | cbn; img_lia | cbn; img_lia]) |]); img_apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfxsegs E0 m0) YF2l.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & _). pose proof HSP as [S1 S2].
pose proof root_vals as (V1 & V2 & V3 & V4). pose proof cache_vals as (C1 & C2 & C3 & C4 & C5). pose proof jst_val as [J1 J1R]. pose proof q_facts as (Qa & Qb & Qc & Qd). assert (Qc0 : 0 <= QSZv) by (img_try (unfold YF2l.QSZv; clear; img_lia)).
assert (QLR : 0 <= QLv < ASAN_CEIL).
{ unfold YF2l.QLv. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [img_try (ceil; unfold ASAN_CEIL; img_lia)|].
pose proof (last_facts lb initr Hrev) as (L1 & L2 & _). unfold YF2l.QLv in L1, L2. rewrite Hrev in L1, L2. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. img_lia. }
pose proof u_facts as (Ua & Ub & Uc & Ud).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hN1, hN2, S1, S2, QLR, Qb, Qd, Ua, Ub.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
unfold YF2l.REG0, YF2l.R_ROOT, YF2l.R_CNT, YF2l.R_JST, flit4, flit8, fatom8.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E0 m0 2 sp0 (- 64)); [img_try (rewrite E2; img_refl) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable; [img_try (unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END in *; img_lia) | img_try (img_apply HPRES; clear -Ha; unfold QSTACK in *; img_lia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_qc in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 88); [img_try (img_apply (val_mem_writable _ _ _ _ V1)) | img_try (destruct (Z_lt_le_dec o 96); [img_apply (val_mem_writable _ _ _ _ V2) | destruct (Z_lt_le_dec o 104); [img_apply (val_mem_writable _ _ _ _ V3) | img_apply (val_mem_writable _ _ _ _ V4)]])];
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
- img_apply (chunk_atom _ _ 8 36%nat 0 QSZv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (img_exact V1) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 8 37%nat 0 QFv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V2 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 8 38%nat 0 QLv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V3 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 8 39%nat 0 QBv); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact V4 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_cache in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. img_apply (val_mem_writable _ _ _ _ C1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_atom _ _ 4 40%nat 0 cnt); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact C1 | img_lia]) | img_try (r4) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EqT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_cache_stats in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. img_apply (val_mem_writable _ _ _ _ J1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFX_IMG_LO, kLowShadowBeg, TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_atom _ _ 8 42%nat 0 jst); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact J1 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 33%nat 0 SB); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | | img_try (r8) | img_try (cbn; img_lia)].
rewrite Z.add_0_l. replace (682872 + D_10c0) with (aeval B ly (AInst o_space)) by (img_try (cbn; rewrite (ts_inst B TB); img_refl)).
replace SB with (aeval B ly (ASp 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
do 3 (img_apply Forall_cons; [img_try (lit_region)|]). img_apply Forall_nil.
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 YF2l.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof (YF0w.SX B ly X rd0 M l 2 8 _ _ eq_refl eq_refl ltac:(img_lia)) as DTS. unfold zdisjoint in DTS. cbn [fst snd] in DTS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
img_apply pairwise_disjoint_of_extents. unfold YF2l.REG0, YF2l.R_ROOT, YF2l.R_CNT, YF2l.R_JST, flit4, flit8, fatom8, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E2, EqT. unfold w64. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, QSTACK in *.
fold sp0. rewrite !unsigned_lit_small by img_lia.
unfold t_qc, t_cache, t_cache_stats. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg in hT1.
repeat split; first [clear hT1; img_lia | clear - hT1 CR0; img_lia].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms YF2l.FFQ).
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & _). pose proof HSP as [S1 S2].
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof q_facts as (Qa & Qb & Qc & Qd). pose proof cache_vals as (_ & _ & _ & C4 & C5). pose proof jst_val as [_ JR].
pose proof hit_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
assert (QLR : 0 <= QLv < ASAN_CEIL /\ QLv mod 8192 = 0).
{ unfold YF2l.QLv. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [img_try (ceil; unfold ASAN_CEIL; split; [img_lia | img_refl])|].
pose proof (last_facts lb initr Hrev) as (L1 & L2 & L3 & _). unfold YF2l.QLv in L1, L2, L3. rewrite Hrev in L1, L2, L3. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. split; [img_lia | img_try (img_exact L3)]. }
destruct QLR as [QLR QLA].
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hN1, hN2, S1, S2, U1, U2, QLR, F2, F4, F5, Qb, Qd.
assert (E2' : ew E0 2 = w64 sp0) by (img_try (rewrite E2; unfold sp0, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
cbn [YF2l.FFQ f_atoms atoms_ok]. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, QSTACK.
split. { img_apply (AF 2%nat sp0); [img_try (img_exact E2')| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 Hal; first [img_lia | img_change (2 ^ 4) with 16; img_exact Hal]. }
split. { img_apply (AF 32%nat T); [img_try (img_exact EqT)| | | |]. all: clear - CR0 hT1 hT2 TAL; first [img_lia | img_exact TAL]. }
split. { img_apply (AF 33%nat SB); [img_try (img_exact EqSB)| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [img_lia | img_exact SAL]. }
split. { img_apply (AF 34%nat u); [img_try (img_exact EqU)| | | |]. all: clear - CR0 U1 U2 U3 U4; first [img_lia | img_change (2 ^ 4) with 16; img_exact U3]. }
split. { img_apply (AF 35%nat nn); [img_try (img_exact EqN)| | | |]. all: clear - CR0 U4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 36%nat QSZv); [img_try (img_exact EqQSZ)| | | |]. all: clear - CR0 Qc; unfold YF2l.QSZv in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 37%nat QFv); [img_try (img_exact EqQF)| | | |]. all: clear - CR0 Qd; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 38%nat QLv); [img_try (img_exact EqQL)| | | |]. all: clear - CR0 QLR QLA; first [img_lia | img_change (2 ^ 13) with 8192; img_exact QLA]. }
split. { img_apply (AF 39%nat QBv); [img_try (img_exact EqQB)| | | |]. all: clear - CR0 Qa Qb U4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 40%nat cnt); [img_try (img_exact EqCNT)| | | |]. all: clear - CR0 C4; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 41%nat CPv); [img_try (img_exact EqCP)| | | |]. all: clear - CR0 F1 F2 F3; unfold YF2l.CPv; first [pose proof (Z.div_pos coff 16); pose proof (Z.div_lt_upper_bound coff 16 (2 ^ 27)); img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 42%nat jst); [img_try (img_exact EqJST)| | | |]. all: clear - CR0 JR; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 43%nat NBv); [img_try (img_exact EqNB)| | | |]. all: clear - CR0 F4 F5 F6 hP1 hP2 hSP1 hSP2; first [img_lia | img_change (2 ^ 13) with 8192; img_exact F6]. }
split; [|img_try (img_exact I)]. { img_apply (AF 44%nat CSLv); [img_try (img_exact EqCSL)| | | |]. all: clear - CR0 C4 C5 hT1 hT2 TAL; unfold YF2l.CSLv, t_cache in *;
first [img_lia | img_change (2 ^ 2) with 4; apply Z.mod_divide in TAL as [c Hc]; [|img_lia]; rewrite Hc; img_apply Z.mod_divide; [img_lia|]; exists (1024 * c + 536 + (cnt - 1)); img_lia]. }
Qed.
Lemma SEED_ok : st_ok tfxsegs E0 YF2l.SS0 (restrict (w_H W) (mkst regs (w64 (0x35dd8 + D_150)) mem (seg_rom tfxsegs))).
Proof.
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1 & Ha3 & Ha4 & _). rewrite (ts_tp _ TB) in Htp.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof HI as (hP1 & hP2 & hT1 & hT2 & _). ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in hT1, hT2, U1, U2.
rewrite restrict_mkst_fx. unfold YF2l.SS0, YF2l.SR0, sr_set. cbn [bv_eqb]. unfold YF2l.E0, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; img_exact Htp] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |]) | img_try (intros XX; discriminate) |].
+ cbn [sv_denot]. fold (YF2l.E0 ly regs u nn q cnt coff jst). rewrite EqT, Ha0. unfold w64. rewrite Zbv_add_unsigned. img_refl.
+ cbn [sv_denot]. fold (YF2l.E0 ly regs u nn q cnt coff jst). rewrite EqT, Ha1. unfold w64. rewrite Zbv_add_unsigned. img_refl.
+ cbn [sv_denot]. fold (YF2l.E0 ly regs u nn q cnt coff jst). rewrite EqU, Ha3. unfold w64, kChunkHeaderSize. rewrite Zbv_add_unsigned. img_refl.
+ cbn [sv_denot]. fold (YF2l.E0 ly regs u nn q cnt coff jst). rewrite EqN, Ha4. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0_ok.
- img_exact PAIRS_ok.
- split; [img_try (img_exact FACTS_ok) | img_try (split; img_exact I)].
Qed.
Theorem FH_ok : YF2l.free_hyps W ly regs mem u nn q cnt coff jst.
Proof.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & QL).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof u_facts as (U1 & U2 & U3 & U4). pose proof q_facts as QF. pose proof cache_vals as (C1 & C2 & C3 & C4 & C5). pose proof jst_val as [_ JR].
pose proof hit_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
constructor.
- img_exact LO.
- rewrite (ts_tp _ TB) in Htp. img_exact Htp.
- img_exact Hra.
- img_exact Hra4.
- split; [img_try (img_exact Hlo) | img_try (img_exact Hhi)].
- img_exact Hal.
- img_exact HPRES.
- split; [img_try (img_exact u_zone) | img_try (img_exact U3)].
- img_exact IMG.
- img_exact U4.
- img_exact QF.
- img_exact HNB.
- intros lb initr Hrev. pose proof (last_facts lb initr Hrev) as (L1 & L2 & L3 & L4 & L5 & _). splits; assumption.
- img_exact C4.
- intros _. splits; assumption.
- img_exact JR.
- img_exact SEED_ok.
Qed.
Local Notation WINq := (YF2l.WIN ly regs q cnt coff).
Local Notation S' := (YF0w.S' X k l).
Lemma enqueue_hit_eq : enqueue k X = IRet (tt, S').
Proof.
pose proof Hci as CI. clear - CI HNB Hl Hlne.
unfold enqueue, cache_alloc, init_cache_if_needed, refill_if_empty, get_pc, set_pc, get, put, modify, ret, bind. cbn [ibind].
rewrite HNB. cbn [ibind]. rewrite CI. cbn [ibind].
img_change (znth pclass0 kBatchClass (st_cache X)) with (cache X kBatchClass). rewrite Hl.
destruct l as [|x t]; [img_try (congruence)|]. cbn [ibind]. fold (cache X kBatchClass). rewrite Hl. cbn [ibind]. img_refl.
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
assert (C12 : 4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) by (img_try (clear - IC; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; img_lia)).
assert (D12 : 4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL) by (img_try (clear - ID; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; img_lia)). clear IC ID.
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
unfold YF2l.WIN, YF2l.WINT, YF2l.WINA in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[Hw|[[_ Hw]|[Hq Hw]]]].
- left. img_exact Hw.
- right; left. clear - Hw. unfold t_qc, t_cache, t_cache_stats, kThreadObjSize in *. img_lia.
- right; right. clear - Hw hN1 hN2 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. img_lia.
- right; right. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev.
+ exfalso. img_apply Hq. rewrite <- (rev_involutive (qc_list q)), Hrev. img_refl.
+ pose proof (HL lb initr eq_refl) as [L1 L2]. unfold YF2l.QLv in Hw, L1, L2. rewrite Hrev in Hw, L1, L2.
clear - Hw L1 L2 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. img_lia.
Qed.
Lemma WIN_dec : forall a, WINq a \/ ~ WINq a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (img_try (intros; img_lia)).
pose proof cache_vals as (_ & _ & _ & _ & C5).
assert (LQ : qc_list q = [] \/ qc_list q <> []) by (img_try (destruct (qc_list q); [img_try (left; img_refl) | img_try (right; discriminate)])).
unfold YF2l.WIN, YF2l.WINT, YF2l.WINA. fold sp0.
destruct (EM (sp0 - 64) sp0) as [C|C0]; [img_try (left; left; img_exact C)|].
destruct (EM (T + t_qc) (T + t_qc + 32)) as [C|C1]; [img_try (left; right; left; left; img_exact C)|].
destruct (EM (T + t_cache + 1920) (T + t_cache + 1924)) as [C|C2]; [img_try (left; right; left; right; left; img_exact C)|].
destruct (EM (T + t_cache_stats + 16) (T + t_cache_stats + 24)) as [C|C3]; [img_try (left; right; left; right; right; img_exact C)|].
destruct (EM NBv (NBv + 32)) as [C|C4]; [img_try (left; right; right; left; split; [img_exact C5 | img_exact C])|].
destruct LQ as [LQ|LQ].
- right. intros [X0|[[X1|[X2|X3]]|[[_ X4]|[X5 _]]]]; [img_try (img_exact (C0 X0)) | img_try (img_exact (C1 X1)) | img_try (img_exact (C2 X2)) | img_try (img_exact (C3 X3)) | img_try (img_exact (C4 X4)) | img_try (img_exact (X5 LQ))].
- destruct (EM QLv (QLv + 8)) as [C|C6]; [img_try (left; right; right; right; split; [img_exact LQ | img_exact C])|].
right. intros [X0|[[X1|[X2|X3]]|[[_ X4]|[_ X5]]]]; [img_try (img_exact (C0 X0)) | img_try (img_exact (C1 X1)) | img_try (img_exact (C2 X2)) | img_try (img_exact (C3 X3)) | img_try (img_exact (C4 X4)) | img_try (img_exact (C6 X5))].
Qed.
Definition low_okq {imgk : img} (a w : Z) : bool :=
((TFX_IMG_LO <=? a) && (a + w <=? TFX_IMG_END)) || ((SHADOW_OFF + TFX_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFX_IMG_END / 8)).
Definition const_loc_okq {imgk : img} (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => low_okq a w
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okq (TFX_TSD + o) w
| ATp o => low_okq (TFX_TP + o) w
| AInst o => low_okq (TFX_INST + o) w
| _ => false
end.
Lemma Tfx_const_locq : forallb const_loc_okq (Tfx_const ly) = true.
Proof. clear. img_case; vm_compute. all: img_refl. Qed.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Lemma CONST_OUT : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> ~ WINq (aeval B ly (c_at c) + i) /\ 0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). img_apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) Tfx_const_locq c Hc) as K. unfold const_loc_okq in K.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & [C1 C2] & [D1 D2]).
assert (ZN : forall a, ~ ((sp0 - 64 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINq a).
{ intros a Hn Hw. img_exact (Hn (WIN_zone a Hw)). }
assert (LOW : forall a, low_okq a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ WINq (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold low_okq in L.
split; [img_try (img_apply ZN)|]; clear - L Hi hP1 hT1 hS1 S1; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, QSTACK, kThreadObjSize in *;
img_change (65536 / 8) with 8192 in *; img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in *; img_lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [img_try (img_apply ZN)|]; clear - K Hi hT1 hT2 S1 S2 G_PT G_TS; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; img_lia.
- split; [img_try (img_apply ZN)|]; clear - K Hi C1 C2 S1 S2 G_PC G_TC G_CS; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; img_lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [img_try (img_apply ZN)|]; clear - K Hi D1 D2 S1 S2 G_PD G_TD G_DS; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; img_lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfxsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfxsegs H m (a + Z.of_nat kk) = Some (YG0h.le_byte v w kk).
Proof.
clear. intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. img_change (YG0h.le_byte v w kk) with (YP0g.le_byte v w kk). f_equal. img_apply unsigned_lit_small8.
unfold YP0g.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Lemma FINQH : forall W' c', YF2z.at_RETQ W ly regs mem md u nn q cnt coff W' c' -> enq_leaf B ly X W regs mem md k (tt, S') W' c'.
Proof.
intros W' c' HR.
pose proof ENQ as ENQ'. destruct ENQ' as (HAR & Hbud & Hbev & Hpev & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & HQL).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
destruct HR as (-> & regs' & mem' & mat & -> & CS & MEQ' & PRESW & VALS). cbv zeta in VALS.
destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & VL).
set (rd := aview tfxsegs (w_H W) mem) in *. set (rd' := aview tfxsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof HSP as HSP'. pose proof cache_vals as (_ & _ & _ & C4 & C5).
assert (ENB : NBv = SB + (region_off kBatchClass + last l 0)) by (img_try (unfold YF2l.NBv, coff; img_lia)).
assert (WD : forall a, WINq a -> YF0w.D ly X l sp0 a).
{ intros a Hw. unfold YF0w.D, YF0w.DT, YF0w.DN, YF0w.DL, YF0w.DS.
unfold YF2l.WIN, YF2l.WINT, YF2l.WINA in Hw. fold sp0 in Hw. rewrite ENB in Hw.
destruct Hw as [Hw|[Hw|[[_ Hw]|[Hq Hw]]]].
- do 3 right. clear - Hw. unfold QSTACK. img_lia.
- left. img_exact Hw.
- right; left. img_exact Hw.
- right; right; left. split; [img_try (img_exact Hq)|]. unfold YF0w.QLv. unfold YF2l.QLv in Hw. img_exact Hw. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF0w.D ly X l sp0 a -> rd' a = rd a).
{ intros a Ha ND. (subst rd rd'; cbv beta). img_apply aview_same. img_apply (MEQ' (Z_to_bv 64 a)). rewrite unsigned_lit_small by img_exact Ha. intros X'. img_exact (ND (WD a X')). }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. (subst rd rd'; cbv beta). unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [img_try (img_exact (Hv HN))|].
destruct (seg_rom tfxsegs x) eqn:ROM; [img_try (destruct (mem' x); discriminate)|].
destruct (mem' x) as [|] eqn:E'; [img_try (discriminate)|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [img_try (clear Hv) | img_try (img_exact (Hv eq_refl))].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
destruct (WIN_dec a') as [C|C].
- destruct (PRESW a' C) as [_ [bb Hb]]. unfold w64 in Hb. rewrite Ex in Hb. congruence.
- rewrite (MEQ' x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (img_try (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; img_lia)).
assert (Ux : bv_unsigned x = a) by (img_try ((subst x; cbv beta); img_apply unsigned_lit_small; img_exact Ha')).
destruct (WIN_dec a) as [C|C].
- exfalso. destruct (PRESW a C) as [Hh _]. unfold w64 in Hh. fold x in Hh. rewrite Hx in Hh. discriminate.
- img_apply (MEQ' x). rewrite Ux. img_exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfxsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd' (a' + Z.of_nat i) = Some (YG0h.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. (subst rd'; cbv beta). img_exact (val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (NEW_qs : forall i, (i < 8)%nat -> rd' (T + t_qc + Z.of_nat i) = Some (YG0h.le_byte (Z.of_nat (length (qc_list q)) + 1) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V1); [img_refl | img_try (unfold YF2l.QSZv; img_refl)]. }
assert (NEW_qf : forall i, (i < 8)%nat -> rd' (T + t_qc + 8 + Z.of_nat i) =
Some (YG0h.le_byte (match qc_list q with [] => SB + (region_off kBatchClass + last l 0) | b0 :: _ => SB + b_self b0 end) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V2); [img_refl|]. unfold YF2z.QF', YF2l.QFv. rewrite ENB. destruct (qc_list q); img_refl. }
assert (NEW_ql : forall i, (i < 8)%nat -> rd' (T + t_qc + 16 + Z.of_nat i) = Some (YG0h.le_byte (SB + (region_off kBatchClass + last l 0)) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V3); [img_refl | img_try (img_exact ENB)]. }
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (T + t_qc + 24 + Z.of_nat i) = Some (YG0h.le_byte (qc_bytes q + nn + kBatchBytes) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V4); [img_refl | img_try (unfold YF2l.QBv; img_refl)]. }
assert (NEW_cnt : forall i, (i < 4)%nat -> rd' (T + t_cache + 1920 + Z.of_nat i) = Some (YG0h.le_byte (Z.of_nat (length l) - 1) 4 i)).
{ img_apply (VM _ _ 4%nat _ _ V5); [img_refl | img_try (unfold cnt; img_refl)]. }
assert (NEW_n0 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + Z.of_nat i) = Some (YG0h.le_byte 0 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V6); [img_try (img_exact ENB) | img_refl]. }
assert (NEW_n8 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + 8 + Z.of_nat i) = Some (YG0h.le_byte (nn + kBatchBytes) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V7); [img_try (rewrite ENB; img_refl) | img_refl]. }
assert (NEW_n16 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + 16 + Z.of_nat i) = Some (YG0h.le_byte 1 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V8); [img_try (rewrite ENB; img_refl) | img_refl]. }
assert (NEW_n24 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + 24 + Z.of_nat i) = Some (YG0h.le_byte (u - 16) 8 i)).
{ img_apply (VM _ _ 8%nat _ _ V9); [img_try (rewrite ENB; img_refl) | img_refl]. }
assert (NEW_lnext : forall lb initr, rev (qc_list q) = lb :: initr ->
forall i, (i < 8)%nat -> rd' (SB + b_self lb + Z.of_nat i) = Some (YG0h.le_byte (SB + (region_off kBatchClass + last l 0)) 8 i)).
{ intros lb initr Hrev. img_apply (VM _ _ 8%nat _ _ (VL lb initr Hrev)); [| img_try (img_exact ENB)]. unfold YF2l.QLv. rewrite Hrev. img_refl. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ img_apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [img_try (img_exact (proj1 (Forall_forall _ _) (am_const B ly X _ M') c Hc))|].
intros i Hi. (subst rd rd'; cbv beta). destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as [X1 X2]. img_apply aview_same.
img_apply (MEQ' (Z_to_bv 64 _)). rewrite unsigned_lit_small by img_exact X2. img_exact X1. }
pose proof (YF0w.enq_fin_ARm B TB ly X rd rd' M' k Hk Hst Hnq HNB   Hci l Hl Hlne sp0 HSP' IMG AG VIS
NEW_qs NEW_qf NEW_ql NEW_qb NEW_cnt NEW_n0 NEW_n8 NEW_n16 NEW_n24 NEW_lnext CONST' Hbev) as MF.
exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md), (Some (region_off kBatchClass + last l 0)). split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. img_refl. }
split.
2:{ split; [img_refl|]. split; [img_try (img_exact HNB)|]. split; [img_refl|]. split; img_refl. }
split; [|img_try (split; [img_apply layout_le_refl | split; [img_apply wle_refl | split; [|split; [|split]]]])].
- split; [img_try (img_exact MF) | img_try (split; [|split; [|split]])].
+ eapply ALedger_same; [img_try (img_exact (YF0w.ALedger_S' ly X k l tfxsegs md LED)) | img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
+ destruct BUD as [BUD PIN]. split; [| img_try (img_exact (YF0w.asecA_S' ly X k l _ PIN))].
eapply Z.le_trans; [img_try (img_exact BUD)|]. rewrite <- (YF0w.abudget_S' X k l). img_apply Z.le_refl.
+ eapply amwf_same; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_exact MW)].
+ eapply (ahs_transfer tfxsegs B ly X _ (w_H W) mem mem' (al_img_env tfxsegs ly X md (am_layout B ly X _ M') LED) M' HSH VIS HSK).
* eapply (aclient_band_same_frames B ly X); [img_try (img_exact MF) | img_refl].
*   img_refl.
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. img_apply AG; [img_try (clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; img_lia)|].
pose proof HI as (hP1 & _ & hT1 & _ & hS1 & _ & _ & _ & hN1 & _ & hL).
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in hP1, hT1, hS1.
unfold YF0w.D, YF0w.DT, YF0w.DN, YF0w.DL, YF0w.DS. img_change (st_qthread X) with q. intros [Y|[Y|[[Hq Y]|Y]]].
-- clear - Y SBg hT1. unfold t_qc, t_cache, t_cache_stats in Y. img_lia.
-- rewrite <- ENB in Y. clear - Y SBg hP1 hN1. img_lia.
-- destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [img_try (exfalso; img_apply Hq; rewrite <- (rev_involutive (qc_list q)), Hrev; img_refl)|].
destruct (hL lb initr eq_refl) as [L1 _]. unfold YF2l.QLv in L1. unfold YF0w.QLv in Y. rewrite Hrev in L1, Y.
clear - Y SBg hP1 L1. img_lia.
-- clear - Y SBg hS1 HSP'. unfold QSTACK in *. img_lia.
- intros r Hr'. img_apply CS. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
clear - R. unfold CALLEE_SAVED.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; (subst r; cbv beta); cbn [In]; repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right]).
- img_apply same_io_wvb.
- intros a Ha NO NO' NS NE. img_apply AG; [img_try (img_exact Ha)|]. intros HD.
destruct (YF0w.D_owned B ly X rd M' k Hci l Hl Hlne sp0 HSP' a (proj1 Ha) HD) as [O|O]; [img_try (img_exact (NO O)) | img_try (img_apply NS; unfold ascratch, spZ; left; img_exact O)].
- intros a Ha. unfold spZ in Ha. fold sp0 in Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [Hb|Hb].
+ img_apply (apresent_same (w_H W) mem); [|img_try (img_apply HPRES; img_exact Ha)]. img_apply MEQ'. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _).
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha Usp HSP' hS1; unfold zone3, TFX_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; img_lia)). rewrite unsigned_lit_small by img_exact Ha'.
intros Hw. pose proof (WIN_zone a Hw) as Z3. pose proof GEO as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
clear - Z3 Ha Hb G_PT G_PS G_TS HSP' hT1 hT2 hP1 hP2. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *. img_lia.
+ img_apply PRESW. unfold YF2l.WIN. left. fold sp0. img_lia.
Qed.
Theorem tfx_enqueue_hit_arm :
amreal tfxsegs (enqueue k X) W (cfg_at tfxsegs A_Enqueue regs mem md) (enq_leaf B ly X W regs mem md k).
Proof.
rewrite enqueue_hit_eq. cbn [amreal]. pose proof cache_vals as (_ & _ & _ & _ & C5).
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
eapply SRr_mono.
- img_exact (YF2z.segQH W ly regs mem md u nn q cnt coff jst (m_vm_materialized md) FH_ok C5).
- intros W' c' _ HR. img_exact (FINQH W' c' HR).
Qed.
End h.
Theorem tfx_enqueue_hit {imgk : img} : forall B, TfxSyms B -> forall ly X W regs mem md k,
enq_pre B ly X W regs mem md k -> need_new_batch (st_qthread X) = true -> pc_chunks (cache X kBatchClass) <> [] ->
ly_tsd ly = TFX_TSD ->
amreal tfxsegs (enqueue k X) W (cfg_at tfxsegs A_Enqueue regs mem md) (enq_leaf B ly X W regs mem md k).
Proof.
intros B TB ly X W regs mem md k ENQ HNB Hne HTSD.
img_exact (tfx_enqueue_hit_arm B TB ly X W regs mem md k ENQ HNB (pc_chunks (cache X kBatchClass)) eq_refl Hne HTSD).
Qed.
End f.
