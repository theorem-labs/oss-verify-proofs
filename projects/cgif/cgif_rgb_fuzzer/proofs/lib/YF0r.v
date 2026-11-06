(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0b YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Lemma pairwise_nth {X} (R : X -> X -> Prop) : forall (l : list X) i j x y,
pairwise R l -> nth_error l i = Some x -> nth_error l j = Some y -> (i < j)%nat -> R x y.
Proof.
induction l as [|a t IH]; intros [|i] [|j] x y P Hi Hj Hij; cbn in *; try discriminate; try img_lia.
- injection Hi as <-. destruct P as [F _]. apply nth_error_In in Hj. img_exact (proj1 (Forall_forall _ _) F _ Hj).
- destruct P as [_ P]. eapply IH; eauto. img_lia.
Qed.
Lemma flat_map_mid {X Y} (f : X -> list Y) : forall l1 x y l2, f x = f y -> flat_map f (l1 ++ x :: l2) = flat_map f (l1 ++ y :: l2).
Proof. intros l1 x y l2 E. rewrite !flat_map_app. cbn. rewrite E. img_refl. Qed.
Lemma fold_ckn_app : forall l1 l2, fold_right (fun k acc => ck_n k + acc) 0 (l1 ++ l2) =
fold_right (fun k acc => ck_n k + acc) 0 l1 + fold_right (fun k acc => ck_n k + acc) 0 l2.
Proof. induction l1 as [|a t IH]; intros l2; cbn; [img_lia|]. rewrite IH. img_lia. Qed.
Lemma combine_snoc_from {X} : forall (l : list X) s x,
combine (seq s (S (length l))) (l ++ [x]) = combine (seq s (length l)) l ++ [((s + length l)%nat, x)].
Proof.
induction l as [|a t IH]; intros s x; [img_try (cbn; rewrite Nat.add_0_r; img_refl)|].
cbn [length]. rewrite <- (cons_seq (S (length t)) s), <- (cons_seq (length t) s). cbn [combine app]. rewrite IH, Nat.add_succ_r. img_refl.
Qed.
Lemma combine_snoc {X} : forall n (l : list X) x, length l = n ->
combine (seq 0 (S n)) (l ++ [x]) = combine (seq 0 n) l ++ [(n, x)].
Proof. intros n l x <-. img_exact (combine_snoc_from l 0 x). Qed.

Lemma batch_cells_snoc : forall l b b', b_self b' = b_self b ->
exists P, batch_cells (l ++ [b]) = P ++ batch_cells [b] /\ batch_cells (l ++ [b']) = P ++ batch_cells [b'] /\
(forall c, In c P -> exists b2, In b2 l /\ (In c (batch_cells [b2]) \/
(exists nx, In nx (map batch_exp (l ++ [b])) /\ c = c8 (batch_exp b2) nx))).
Proof.
induction l as [|b2 t IH]; intros b b' E.
- exists []. cbn. split; [img_refl|]. split; [img_refl|]. intros c [].
- destruct (IH b b' E) as (P & H1 & H2 & H3). cbn [batch_cells app].
assert (HD : match t ++ [b'] with [] => ANum 0 | b'0 :: _ => batch_exp b'0 end = match t ++ [b] with [] => ANum 0 | b0 :: _ => batch_exp b0 end).
{ destruct t; cbn; [img_try (unfold batch_exp; rewrite E)|]; img_refl. }
rewrite HD.
eexists (c8 (batch_exp b2) _ :: z8 (aoff (batch_exp b2) 8) (b_bytes b2) :: z8 (aoff (batch_exp b2) 16) (Z.of_nat (length (b_items b2))) ::
map (fun iv => c8 (aoff (batch_exp b2) (24 + 8 * Z.of_nat (fst iv))) (sptr_exp (ck_hdr (snd iv)))) (combine (seq 0 (length (b_items b2))) (b_items b2)) ++ P).
split; [|img_try (split)].
+ img_change (batch_cells (t ++ [b])) with (batch_cells (t ++ [b])). rewrite H1. cbn [app]. rewrite <- app_assoc. img_refl.
+ rewrite H2. cbn [app]. rewrite <- app_assoc. img_refl.
+ intros c Hc. cbn [app] in Hc. destruct Hc as [<-|[<-|[<-|Hc]]].
* exists b2. split; [img_try (left; img_refl)|]. right. eexists. split; [|img_refl]. destruct t as [|b3 t']; cbn; [img_try (right; left; img_refl) | img_try (right; left; img_refl)].
* exists b2. split; [img_try (left; img_refl)|]. left. cbn. right. left. img_refl.
* exists b2. split; [img_try (left; img_refl)|]. left. cbn. right. right. left. img_refl.
* apply in_app_iff in Hc as [Hc|Hc].
-- exists b2. split; [img_try (left; img_refl)|]. left. cbn [batch_cells]. right. right. right. rewrite app_nil_r. img_exact Hc.
-- destruct (H3 c Hc) as (b4 & Hin4 & Hb4). exists b4. split; [img_try (right; img_exact Hin4)|]. destruct Hb4 as [Y|(nx & X & ->)]; [img_try (left; img_exact Y)|].
right. exists nx. split; [|img_refl]. cbn. right. img_exact X.
Qed.
Section w. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma find_chunk_at_app : forall B ly l1 l2 g,
find_chunk_at B ly (l1 ++ l2) g = match find_chunk_at B ly l1 g with Some x => Some x | None => find_chunk_at B ly l2 g end.
Proof. intros B ly l1 l2 g. induction l1 as [|x t IH]; cbn; [img_refl|]. destruct (_ && _); [img_refl | img_try (img_exact IH)]. Qed.
Section c0. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (rd rd' : reader).
Hypothesis M : ARm B ly S rd.
Variables (k : chunk) (b : batch) (initr : list batch) (hb1 : Z).
Hypothesis Hk : In k (st_chunks S).
Hypothesis Hst : ck_state k = CAllocated.
Hypothesis Hrev : rev (qc_list (st_qthread S)) = b :: initr.
Hypothesis Hroom : Z.of_nat (length (b_items b)) < kBatchSlots.
Hypothesis Hhb1 : 0 <= hb1 < 256 /\ Z.land hb1 127 = 17.
Variables (z : Z) (tr : list Z).
Let s1 : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Let sd : astate := depot_after z tr s1.
Let k' : chunk := mkChunk (ck_beg k) (ck_req k) CQuarantined.
Let b' : batch := mkBatch (b_self b) (b_items b ++ [k']).
Definition S' : astate := set_qthread (qc_push (st_qthread S) k' None) (set_chunks (upd_chunk (st_chunks sd) k') sd).
Hypothesis Hev : aregime S.
Hypothesis AOK : aok s1 (KDepot tr) z.
Hypothesis HU : In tr (as_universe B).
Local Notation T := (ly_T ly).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Local Notation Bv := (ly_space ly + b_self b).
Local Notation BCv := (Z.of_nat (length (b_items b))).
Local Notation SLOTv := (ly_space ly + b_self b + 24 + 8 * Z.of_nat (length (b_items b))).
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp <= ly_stk_hi ly.
Hypothesis IMG : img_cover ly.
Definition DT (a : Z) : Prop := (T + t_qc <= a < T + t_qc + 32) \/ a = T + t_unwinding \/ (T + t_stats + 24 <= a < T + t_stats + 40).
Definition DK (a : Z) : Prop := (u - 16 <= a < u - 8) \/ (u <= a < u + 8).
Definition DB (a : Z) : Prop := (Bv + 8 <= a < Bv + 24) \/ (SLOTv <= a < SLOTv + 8).
Definition DS (a : Z) : Prop := sp - ASTACK <= a < sp.
Definition DI (a : Z) : Prop := (as_ialloc_lo B <= a < as_ialloc_hi B) \/ (as_ialloc_flag B <= a < as_ialloc_flag B + 4).
Definition DH (a : Z) : Prop := shadow_addr u <= a < shadow_addr u + (nn + 7) / 8.
Definition D (a : Z) : Prop := DT a \/ DK a \/ DB a \/ DS a \/ DI a \/ depot_footprint B ly a \/ DH a.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_hdr : forall i, (i < 4)%nat -> rd' (u - 16 + Z.of_nat i) = Some (YG0h.le_byte (3 + 256 * hb1) 4 i).
Hypothesis NEW_n : forall i, (i < 4)%nat -> rd' (u - 12 + Z.of_nat i) = Some (YG0h.le_byte nn 4 i).
Hypothesis NEW_qs : forall i, (i < 8)%nat -> rd' (T + t_qc + Z.of_nat i) = Some (YG0h.le_byte (Z.of_nat (length (qc_list (st_qthread S)))) 8 i).
Hypothesis NEW_qf : forall i, (i < 8)%nat -> rd' (T + t_qc + 8 + Z.of_nat i) =
Some (YG0h.le_byte (match qc_list (st_qthread S) with [] => 0 | b0 :: _ => ly_space ly + b_self b0 end) 8 i).
Hypothesis NEW_ql : forall i, (i < 8)%nat -> rd' (T + t_qc + 16 + Z.of_nat i) = Some (YG0h.le_byte Bv 8 i).
Hypothesis NEW_qb : forall i, (i < 8)%nat -> rd' (T + t_qc + 24 + Z.of_nat i) = Some (YG0h.le_byte (qc_bytes (st_qthread S) + nn) 8 i).
Hypothesis NEW_unw : rd' (T + t_unwinding) = Some 0.
Hypothesis NEW_bb : forall i, (i < 8)%nat -> rd' (Bv + 8 + Z.of_nat i) = Some (YG0h.le_byte (b_bytes b + nn) 8 i).
Hypothesis NEW_bc : forall i, (i < 8)%nat -> rd' (Bv + 16 + Z.of_nat i) = Some (YG0h.le_byte (BCv + 1) 8 i).
Hypothesis NEW_slot : forall i, (i < 8)%nat -> rd' (SLOTv + Z.of_nat i) = Some (YG0h.le_byte (u - 16) 8 i).
Hypothesis NEW_sh : forall a, DH a -> rd a <> None -> rd' a = Some shHeapFreed.
Hypothesis IAL : Forall (cell_holds B ly rd') (ialloc_cells B S') /\ Forall (range_zero B ly rd') (ialloc_zero B).
Hypothesis DEP : depot_mem_ok B ly sd rd'.
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
Ltac drop_mem := clear AG VIS NEW_hdr NEW_n NEW_qs NEW_qf NEW_ql NEW_qb NEW_unw NEW_bb NEW_bc NEW_slot NEW_sh IAL DEP CONST'.
Ltac drop_ev := clear Hev AOK HU.
Ltac geo := drop_mem; drop_ev.
Ltac geo' := geo.
Lemma S'_regions : st_regions S' = st_regions S.   Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); img_refl. Qed.
Lemma S'_cache : st_cache S' = st_cache S.         Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); img_refl. Qed.
Lemma S'_cinit : st_cache_inited S' = st_cache_inited S. Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); img_refl. Qed.
Lemma S'_secs : st_secs S' = st_secs S.             Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); img_refl. Qed.
Lemma S'_sec_arr : st_sec_arr S' = st_sec_arr S.    Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); img_refl. Qed.
Lemma S'_sec_res : st_sec_reserved S' = st_sec_reserved S. Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); img_refl. Qed.
Lemma S'_fs : st_fs S' = st_fs S.                   Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); img_refl. Qed.
Lemma S'_qglobal : st_qglobal S' = st_qglobal S.    Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); img_refl. Qed.
Lemma S'_qthread : st_qthread S' = qc_push (st_qthread S) k' None. Proof. geo'. img_refl. Qed.
Lemma sd_chunks : st_chunks sd = st_chunks S.       Proof. geo'. unfold sd, depot_after, s1; destruct (z =? 0); img_refl. Qed.
Lemma S'_chunks : st_chunks S' = upd_chunk (st_chunks S) k'. Proof. geo'. unfold S'. cbn [st_chunks set_qthread set_chunks]. rewrite sd_chunks. img_refl. Qed.
Lemma S'_depot : st_depot S' = st_depot sd.         Proof. geo'. img_refl. Qed.
Lemma S'_inited : st_internal_inited S' = true.     Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); img_refl. Qed.
Lemma reg' : forall c, reg S' c = reg S c.          Proof. geo'. intros c. unfold reg. rewrite S'_regions. img_refl. Qed.
Lemma cache' : forall c, cache S' c = cache S c.    Proof. geo'. intros c. unfold cache. rewrite S'_cache. img_refl. Qed.
Lemma frames' : frames S' = frames S.               Proof. geo'. unfold frames. rewrite S'_fs. img_refl. Qed.
Let WF : Wf (as_universe B) S := am_wf B ly S rd M.
Let LO : layout_ok ly := am_layout B ly S rd M.
Lemma KF : cfacts B ly S k. Proof. geo'. img_exact (chunk_facts B ly S rd k M Hk). Qed.
Lemma Hu : u = ck_base B ly k + ck_rz k. Proof. geo'. pose proof KF as (_ & _ & _ & G4 & _). img_exact G4. Qed.
Lemma k'_base : ck_base B ly k' = ck_base B ly k. Proof. geo'. img_refl. Qed.
Lemma k'_extent : ck_extent k' = ck_extent k. Proof. geo'. img_refl. Qed.
Lemma k'_rz : ck_rz k' = ck_rz k. Proof. geo'. img_refl. Qed.
Lemma k'_n : ck_n k' = ck_n k. Proof. geo'. img_refl. Qed.
Lemma ext_rounded : ck_rz k + (nn + 7) / 8 * 8 <= ck_extent k /\ 1 <= nn /\ 0 <= (nn + 7) / 8 /\ nn <= (nn + 7) / 8 * 8 < nn + 8.
Proof. geo'.
pose proof KF as (_ & _ & _ & _ & G5 & _ & G7 & G8 & GG). unfold ck_n.
pose proof (req_size_bounds (ck_req k) ltac:(img_lia)) as (Q1 & Q2 & Q3).
pose proof (rounded_size_bounds (ck_req k) ltac:(img_lia)) as [R1 R2].
assert (DV : (req_size (ck_req k) + 7) / 8 * 8 <= rounded_size (ck_req k) /\ req_size (ck_req k) <= (req_size (ck_req k) + 7) / 8 * 8 < req_size (ck_req k) + 8).
{ pose proof (Z.div_mod (req_size (ck_req k) + 7) 8 ltac:(img_lia)). pose proof (Z.mod_pos_bound (req_size (ck_req k) + 7) 8 ltac:(img_lia)).
apply Z.mod_divide in R2 as [q Hq]; [|img_lia]. nia. }
assert (RZX : ck_rz k + rounded_size (ck_req k) <= ck_extent k).
{ unfold ck_extent, ck_rz. destruct (from_primary (ck_req k)) eqn:P.
- pose proof (primary_geometry (ck_req k) ltac:(img_lia) P) as (_ & [_ P2] & _). unfold needed_size in P2. rewrite P in P2. unfold needed_primary in P2. img_lia.
- pose proof (secondary_geometry (ck_req k) ltac:(img_lia) P) as (_ & S2 & _ & [S4 _] & _). unfold needed_primary in S2.
pose proof (rz_size_bounds (ck_req k)). img_lia. }
pose proof (Z.div_pos (req_size (ck_req k) + 7) 8). img_lia.
Qed.
Lemma u_al8 : u mod 8 = 0 /\ ck_base B ly k mod 8 = 0 /\ ck_rz k mod 8 = 0.
Proof. geo'.
pose proof KF as (_ & _ & G3 & G4 & _ & G6 & _). rewrite Hu.
apply Z.mod_divide in G3 as [q Hq]; [|img_lia]. apply Z.mod_divide in G6 as [q' Hq']; [|img_lia]. rewrite Hq, Hq'.
splits; img_apply Z.mod_divide; try img_lia; [img_try (exists (2 * q + 2 * q')) | img_try (exists (2 * q)) | img_try (exists (2 * q'))]; img_lia.
Qed.
Lemma SPLIT : exists l1 l2, st_chunks S = l1 ++ k :: l2 /\ st_chunks S' = l1 ++ k' :: l2 /\
~ In (ck_beg k) (map ck_beg l1) /\ ~ In (ck_beg k) (map ck_beg l2).
Proof. geo'.
destruct (In_split_beg _ _ Hk (wf_chunks_nodup _ _ _ _ _ WF)) as (l1 & l2 & E & N1 & N2).
exists l1, l2. splits; try assumption. rewrite S'_chunks, E. img_apply upd_chunk_present; [img_refl | img_try (img_exact N1)].
Qed.
Lemma qlist : qc_list (st_qthread S) = rev initr ++ [b].
Proof. geo'. rewrite <- (rev_involutive (qc_list (st_qthread S))), Hrev. img_refl. Qed.
Lemma qlist' : qc_list (st_qthread S') = rev initr ++ [b'].
Proof. geo'. rewrite S'_qthread. cbn [qc_push qc_list]. rewrite Hrev. img_refl. Qed.
Lemma qbytes' : qc_bytes (st_qthread S') = qc_bytes (st_qthread S) + nn. Proof. geo'. img_refl. Qed.
Lemma all_batches_S : all_batches S = (rev initr ++ [b]) ++ qc_list (st_qglobal S).
Proof. geo'. unfold all_batches. rewrite qlist. img_refl. Qed.
Lemma all_batches_S' : all_batches S' = (rev initr ++ [b']) ++ qc_list (st_qglobal S).
Proof. geo'. unfold all_batches. rewrite qlist', S'_qglobal. img_refl. Qed.
Lemma Hb_in : In b (all_batches S).
Proof. geo'. rewrite all_batches_S. img_apply in_app_iff. left. img_apply in_app_iff. right. left. img_refl. Qed.
Lemma b'_bytes : b_bytes b' = b_bytes b + nn.
Proof. geo'. unfold b_bytes. cbn [b_items b']. rewrite fold_ckn_app. cbn [fold_right]. img_change (ck_n k') with nn. img_lia. Qed.
Lemma BC_len : (1 <= length (b_items b))%nat /\ BCv < kBatchSlots.
Proof. geo'.
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b Hb_in) as [L1 L2]. split; [img_try (img_exact L1) | img_try (img_exact Hroom)].
Qed.
Lemma sd_wf : WfP (as_universe B) 1 1 1 sd.
Proof. drop_mem.
pose proof (WfP_set_internal_inited _ 1 1 1 _ true (WfP_tick _ S WF Hev)) as W2. change (WfP (as_universe B) 1 1 1 s1) in W2.
unfold sd, depot_after. destruct (z =? 0) eqn:Ez; [img_try (img_exact W2)|]. apply Z.eqb_neq in Ez.
destruct AOK as [Z0|[_ MT]]; [img_lia|]. apply mem_trace_false in MT.
pose proof (wf_depot _ _ _ _ _ W2) as [ND INC].
img_apply (WfP_set_depot _ 1 1 1 s1 _ W2).
- img_apply NoDup_app_iff. splits; [img_try (img_exact ND) | img_try (constructor; [intros [] | constructor]) |]. intros x Hx [<-|[]]. img_exact (MT Hx).
- intros x Hx. apply in_app_iff in Hx as [Hx|[<-|[]]]; [img_try (img_exact (INC x Hx)) | img_try (img_exact HU)].
Qed.
Lemma WS' : Wf (as_universe B) S'.
Proof. drop_mem.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). pose proof sd_wf as W3.
assert (Esd : st_chunks sd = l1 ++ k :: l2) by (img_try (rewrite sd_chunks; img_exact E)).
pose proof (WfP_flip _ 1 1 1 sd l1 k l2 W3 Esd Hst) as W4. img_change (quar_of k) with k' in W4.
assert (QI : q_items (set_chunks (l1 ++ k' :: l2) sd) = q_items S) by (img_try (unfold sd, depot_after, s1; destruct (z =? 0); img_refl)).
assert (QT : st_qthread (set_chunks (l1 ++ k' :: l2) sd) = st_qthread S) by (img_try (unfold sd, depot_after, s1; destruct (z =? 0); img_refl)).
pose proof (WfP_qpush _ 1 1 1 (set_chunks (l1 ++ k' :: l2) sd) k' None W4 ltac:(img_lia) ltac:(img_try (cbn; img_apply in_app_iff; right; left; img_refl)) eq_refl) as W5.
rewrite QI, QT in W5. unfold S'. change (upd_chunk (st_chunks sd) k' = l1 ++ k' :: l2) in E'. rewrite E'.
img_apply (WfP_weaken _ 1 1 0); try img_lia. img_apply W5.
-
intros Hin. apply in_map_iff in Hin as (x & Ex & Hx). cbn [ck_beg k'] in Ex.
pose proof (proj1 (Forall_forall _ _) (wq_items _ (wf_quarantine _ _ _ _ _ WF)) x Hx) as [X1 X2].
destruct (In_split_beg _ _ Hk (wf_chunks_nodup _ _ _ _ _ WF)) as (m1 & m2 & Em & M1 & M2).
rewrite Em in X1. apply in_app_iff in X1 as [X1|[<-|X1]]; [img_try (img_apply M1) | img_try (rewrite Hst in X2; discriminate) | img_try (img_apply M2)]; rewrite <- Ex; img_apply in_map; img_exact X1.
- unfold need_new_batch. rewrite Hrev. img_apply Z.eqb_neq. img_lia.
-   img_exact I.
-   intros NB. exfalso. img_exact (NB eq_refl).
Qed.
Lemma batch_geom : forall b2, In b2 (all_batches S) ->
exists x, ly_space ly + b_self b2 = region_base ly kBatchClass + x /\ 0 <= x /\ x mod kBatchBytes = 0 /\
x + kBatchBytes <= rg_alloc_user (reg S kBatchClass) /\ rg_alloc_user (reg S kBatchClass) <= rg_mapped_user (reg S kBatchClass) <= 2 ^ 31 /\
In x (batch_offs S kBatchClass).
Proof. geo'.
intros b2 Hb2. pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
set (x := b_self b2 - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (img_try (rewrite batch_offs_24; img_apply in_map_iff; exists b2; auto)).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(img_try (rewrite !in_app_iff; tauto))) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(img_try (unfold kBatchClass; img_lia))) as MB.
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in X2, AA. unfold kUserMapSize, EV_MAX in MB. unfold kBatchBytes.
assert (XB : x + 8192 <= rg_alloc_user (reg S kBatchClass)).
{ apply Z.mod_divide in X2 as [q Hq]; [|img_lia]. apply Z.mod_divide in AA as [q' Hq']; [|img_lia]. assert (q < q') by nia. nia. }
exists x. splits; try assumption; try img_lia. unfold region_base. (subst x; cbv beta). img_lia.
Qed.
Lemma batches_nodup : List.NoDup (map b_self (all_batches S)).
Proof. geo'.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & ND & _).
rewrite batch_offs_24 in ND.
clear - ND. induction (all_batches S) as [|x t IH]; cbn in *; [img_try (constructor)|].
inversion ND as [|y l N1 N2]; (subst; cbv beta). constructor; [|img_try (img_exact (IH N2))].
intros Hin. img_apply N1. apply in_map_iff in Hin as (x' & E & Hx'). img_apply in_map_iff. exists x'. split; [img_lia | img_try (img_exact Hx')].
Qed.
Lemma batches_apart : forall b1 b2, In b1 (all_batches S) -> In b2 (all_batches S) -> b_self b1 <> b_self b2 ->
zdisjoint (ly_space ly + b_self b1, kBatchBytes) (ly_space ly + b_self b2, kBatchBytes).
Proof. geo'.
intros b1 b2 H1 H2 NE. destruct (batch_geom b1 H1) as (x1 & E1 & P1 & A1 & _). destruct (batch_geom b2 H2) as (x2 & E2 & P2 & A2 & _).
unfold zdisjoint, kBatchBytes in *. cbn [fst snd]. rewrite E1, E2.
apply Z.mod_divide in A1 as [q1 Hq1]; [|img_lia]. apply Z.mod_divide in A2 as [q2 Hq2]; [|img_lia].
assert (q1 <> q2) by (img_try (intros ->; img_apply NE; img_lia)). nia.
Qed.
Lemma batch_vs_chunk : forall b2 x, In b2 (all_batches S) -> In x (st_chunks S) ->
zdisjoint (ly_space ly + b_self b2, kBatchBytes) (ck_base B ly x, ck_extent x).
Proof. geo'.
intros b2 x Hb2 Hx. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & INB).
pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & _ & NDx).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (ck_beg x) as [|o|r o|c p] eqn:Ebx; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
+ pose proof (In_chunk_offs S x o Hx Ebx) as IK. rewrite Ec in *. set (xk := o - region_off kBatchClass) in *.
assert (CS : class_size kBatchClass = 8192) by img_refl. rewrite CS in *.
assert (xk <> xb). { intros E. img_apply (NDx xk); [img_try (img_exact IK) | img_try (rewrite E; img_exact INB)]. }
unfold kBatchBytes in *. apply Z.mod_divide in Gxm as [q1 Hq1]; [|img_lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|img_lia].
assert (q1 <> q2) by (img_try (intros E; (subst; cbv beta); img_lia)). nia.
+ pose proof (region_in_prim ly (prim_class o) LO ltac:(img_lia)) as (R1' & R2' & _).
unfold region_base, kBatchBytes in *. rewrite !region_off_eq in * by (img_try (unfold kBatchClass; img_lia)). unfold kBatchClass in *.
destruct (Z.lt_ge_cases (prim_class o) 24).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
* pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as DJ.
unfold zdisjoint, kPage, kBatchBytes in *. cbn [fst snd] in DJ. unfold region_base in *. img_lia.
Qed.
Lemma SX : forall i j x y, nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x y.
Proof. geo'.
intros i j x y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- img_exact (pairwise_nth zdisjoint _ i j x y (lo_disj _ LO) Hi Hj H).
- img_apply zdisjoint_sym. img_apply (pairwise_nth zdisjoint _ j i y x (lo_disj _ LO) Hj Hi). img_lia.
Qed.
Lemma SECX : forall e j y, In e (sec_extents ly S) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof. geo'.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He).
eapply nth_error_In. img_exact Hj.
Qed.
Lemma ext_zone : forall y, In y (st_chunks S) ->
(exists c, 1 <= c <= 30 /\ region_base ly c <= ck_base B ly y /\ ck_base B ly y + ck_extent y <= region_base ly c + 2 ^ 31 /\
ly_prim ly <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ly_prim ly + kPrimResvSize) \/
(exists r, ck_beg y = PSec r kPage /\ ck_base B ly y = ly_sec ly r + kPage /\ In (ly_sec ly r, ck_extent y + kPage) (sec_extents ly S)).
Proof. geo'.
intros y Hy. pose proof (chunk_facts B ly S rd y M Hy) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal & Gm).
pose proof (region_in_prim ly (prim_class o) LO ltac:(img_lia)) as (R1 & R2 & _). exists (prim_class o). splits; img_lia.
- right. destruct GG as (-> & _ & Gbase & Gext & Gin & _). exists r. splits; [img_refl | img_lia |].
replace (ck_extent y + kPage) with (sec_map_size (ck_req y)) by img_lia. img_exact Gin.
Qed.
Lemma anyX : forall y j e, In y (st_chunks S) -> nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> zdisjoint (ck_base B ly y, ck_extent y) e.
Proof. geo'.
intros y j e Hy Hj Hne. destruct (ext_zone y Hy) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- pose proof (SX 0 j _ e eq_refl Hj ltac:(img_lia)) as DJ. unfold zdisjoint in DJ |- *. cbn [fst snd] in DJ |- *. img_lia.
- pose proof (SECX _ j e Xin Hj) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. img_lia.
Qed.
Lemma KX : forall j y, nth_error (static_extents ly) j = Some y -> (j <> 0)%nat -> zdisjoint (ck_base B ly k, ck_extent k) y.
Proof. geo'. intros j y Hj Hne. img_exact (anyX k j y Hk Hj Hne). Qed.
Lemma secmap_vs_chunk : forall x y r o, In x (st_chunks S) -> In y (st_chunks S) -> ck_beg x = PSec r o -> ck_beg x <> ck_beg y ->
zdisjoint (ly_sec ly r, sec_map_size (ck_req x)) (ck_base B ly y, ck_extent y).
Proof. geo'.
intros x y r o Hx Hy Ebx Hne.
pose proof (chunk_facts B ly S rd x M Hx) as (_ & _ & _ & _ & _ & _ & _ & _ & GG). rewrite Ebx in GG. destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (chunk_facts B ly S rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GK).
destruct (ck_beg y) as [|o'|r' o'|c' p'] eqn:Eby; try solve [destruct GK].
- img_apply zdisjoint_sym. img_exact (prim_vs_secmap B ly S rd y o' _ M Hy Eby Gin).
- destruct GK as (-> & _ & Kbase & Kext & Kin & _).
pose proof (secmaps_disjoint B ly S rd x y r kPage r' kPage M Hx Hy Ebx Eby ltac:(img_try (rewrite Eby; img_exact Hne))) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. img_lia.
Qed.
Lemma zdisjoint_of_pointwise : forall a s (e : Z * Z), 0 < s -> 0 < snd e -> (forall x, a <= x < a + s -> ~ in_zr x e) -> zdisjoint (a, s) e.
Proof. clear_all. intros a s [c t] Hs Ht H. unfold zdisjoint. unfold in_zr in H. cbn [fst snd] in *.
destruct (Z_lt_le_dec (Z.max a c) (a + s)); [|img_lia]. destruct (Z_lt_le_dec (Z.max a c) (c + t)); [|img_lia].
exfalso. img_apply (H (Z.max a c)); img_lia.
Qed.
Lemma ZCH : forall x, In x (st_chunks S) -> zone3 (ck_base B ly x) (ck_extent x).
Proof. geo'.
intros x Hx. pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req x) ltac:(img_try (clear - G7; img_lia))) as (_ & Q1 & _).
img_apply (zone3_intro ly (ck_base B ly x) (ck_extent x) IMG ltac:(img_try (clear - G5 G8 Q1; img_lia)) G1).
img_apply zdisjoint_of_pointwise; [img_try (clear - G5 G8 Q1; img_lia) | img_try (img_exact (proj1 (proj2 (lo_img _ LO)))) |].
intros y Hy. img_exact (proj1 (chunk_apart B ly S rd x y M Hx Hy)).
Qed.
Lemma HIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) kPtrArrayResv /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) kFakeStackSize /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) kNodesBlockSize /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) kStoreBlockSize /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
zone3 (ck_base B ly k) (ck_extent k) /\ ck_base B ly k + ck_extent k <= ASAN_CEIL /\ 16 <= ck_rz k /\
kHighMemBeg <= Bv /\ Bv + kBatchBytes <= ASAN_CEIL /\ ly_stk_lo ly mod 4096 = 0 /\
ly_prim ly <= Bv /\ Bv + kBatchBytes <= ly_space ly + kSpaceSize.
Proof. geo'.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD.
assert (Z3 : forall i x sz, nth_error (owned_extents ly) i = Some (x, sz) -> 0 <= sz -> zone3 x sz).
{ intros i x sz He Hsz. img_apply (zone3_intro ly x sz IMG Hsz (Forall_nth_f _ _ i _ HA He)).
assert (L : (i < 8)%nat) by (img_try (destruct (Nat.lt_ge_cases i 8) as [X|X]; [img_try (img_exact X)|]; assert (X' : nth_error (owned_extents ly) i = None) by (img_apply nth_error_None; cbn; img_lia); rewrite X' in He; discriminate)).
img_exact (pairwise_ij_f _ _ i (8 - i) _ _ HD ltac:(img_try (unfold static_extents; rewrite nth_error_app1 by (cbn; img_lia); img_exact He))
ltac:(img_try (unfold static_extents; rewrite nth_error_app2 by (cbn; img_lia); replace (i + Datatypes.S (8 - i) - length (owned_extents ly))%nat with 1%nat by (cbn; img_lia); img_refl))). }
pose proof (Z3 1%nat _ _ eq_refl ltac:(img_try (unfold kPtrArrayResv; img_lia))) as ZQ. pose proof (Z3 2%nat _ _ eq_refl ltac:(img_try (unfold kThreadObjSize; img_lia))) as ZT.
pose proof (Z3 3%nat _ _ eq_refl ltac:(img_try (unfold kFakeStackSize; img_lia))) as ZF. pose proof (Z3 4%nat _ _ eq_refl ltac:(img_try (unfold kNodesBlockSize; img_lia))) as ZNB.
pose proof (Z3 5%nat _ _ eq_refl ltac:(img_try (unfold kStoreBlockSize; img_lia))) as ZSB. pose proof (Z3 6%nat _ _ eq_refl ltac:(img_lia)) as ZC. clear Z3 HA HD.
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
pose proof KF as (G1 & G2 & _ & _ & G5 & _).
pose proof ext_rounded as (ER & NN1 & NN2 & NN3).
pose proof (ZCH k Hk) as ZK.
destruct (batch_geom b Hb_in) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & R3 & R4 & R5).
unfold page_aligned in *.
split; [img_lia|]. split; [img_lia|]. split; [img_try (img_exact ZQ)|]. split; [img_try (clear - ZQ; unfold zone3 in ZQ; img_lia)|].
split; [img_try (img_exact ZT)|]. split; [img_try (clear - ZT; unfold zone3 in ZT; img_lia)|]. split; [img_try (img_exact ZF)|]. split; [img_try (clear - ZF; unfold zone3 in ZF; img_lia)|].
split; [img_try (img_exact ZNB)|]. split; [img_try (clear - ZNB; unfold zone3 in ZNB; img_lia)|]. split; [img_try (img_exact ZSB)|]. split; [img_try (clear - ZSB; unfold zone3 in ZSB; img_lia)|].
split; [img_try (img_exact ZC)|]. split; [img_try (clear - ZC; unfold zone3 in ZC; img_lia)|].
clear ZQ ZT ZF ZNB ZSB ZC. split; [img_lia|]. split; [img_lia|]. split; [img_lia|]. split; [img_lia|].
split; [img_try (img_exact ZK)|]. split; [img_lia|]. split; [img_lia|].
unfold region_base, kBatchBytes, kSpaceSize in *. rewrite region_off_eq in * by (img_try (unfold kBatchClass; img_lia)). unfold kBatchClass in *.
clear ZK. splits; img_lia.
Qed.
Lemma LOWD : forall a, DI a \/ (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) -> TFX_IMG_LO <= a < TFX_IMG_END.
Proof. geo'.
intros a Ha. unfold DI in Ha. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB), (ts_depot _ TB), (ts_store _ TB) in Ha.
unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_DEPOT, TFX_STORE, d_map1, TFX_IMG_LO, TFX_IMG_END in *. img_lia.
Qed.
Lemma D_cases : forall a, D a ->
(T <= a < T + kThreadObjSize /\ DT a) \/ (ck_base B ly k <= a < ck_base B ly k + ck_extent k /\ DK a) \/
(Bv <= a < Bv + kBatchBytes /\ DB a) \/ (ly_stk_lo ly <= a < ly_stk_hi ly) \/ (TFX_IMG_LO <= a < TFX_IMG_END) \/
(ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) \/
(kLowShadowBeg <= a < kHighMemBeg /\ DH a).
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof ext_rounded as (ER & NN1 & NN2 & NN3). pose proof BC_len as [BL1 BL2].
destruct Ha as [X|[X|[X|[X|[X|[X|X]]]]]].
- left. split; [|img_try (img_exact X)]. unfold DT, t_qc, t_unwinding, t_stats, kThreadObjSize in *. img_lia.
- right; left. split; [|img_try (img_exact X)]. unfold DK in X. rewrite Hu in X. img_lia.
- do 2 right; left. split; [|img_try (img_exact X)]. unfold DB in X. unfold kBatchSlots, kBatchBytes in *. img_lia.
- do 3 right; left. unfold DS, ASTACK in *. img_lia.
- do 4 right; left. img_apply LOWD. left. img_exact X.
- unfold depot_footprint in X. destruct X as [X|[X|[X|X]]]; [img_try (do 4 right; left; img_apply LOWD; tauto) | img_try (tauto) | img_try (tauto) | img_try (do 4 right; left; img_apply LOWD; tauto)].
- do 7 right. split; [|img_try (img_exact X)]. unfold DH in X. rewrite Hu in X.
destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZK & K2 & RZ16 & _). clear - X ZK K2 RZ16 ER NN1 NN2 NN3.
ceil; unfold zone3, shadow_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
split.
+ pose proof (Z.div_pos (ck_base B ly k + ck_rz k) 8 ltac:(img_lia) ltac:(img_lia)). img_lia.
+ assert (LE : ck_base B ly k + ck_rz k + (nn + 7) / 8 * 8 <= 140737479966720) by img_lia.
assert (Y : (ck_base B ly k + ck_rz k + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (img_try (img_apply Z.div_le_mono; [img_lia | img_try (img_exact LE)])).
rewrite Z.div_add in Y by img_lia. img_change (140737479966720 / 8) with 17592184995840 in Y. img_lia.
Qed.
Ltac zget HI x sz Z := assert (Z : zone3cases x sz) by (img_try (clear - HI; unfold zone3 in HI; tauto)); unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in Z.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ D a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. img_apply AG; assumption. Qed.
Ltac zd H := let X := fresh "ZD" in pose proof H as X; unfold zdisjoint in X; cbn [fst snd] in X; unfold kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize in X; img_lia.
Lemma ok_Q : okr (ly_Q ly) kPtrArrayResv.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_Q ly) kPtrArrayResv ZZ. ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X _]|[[X _]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try img_lia.
- zd (SX 1 2 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (KX 1 _ eq_refl ltac:(img_lia)).
- zd (SX 0 1 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 1 8 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 1 4 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 1 5 _ _ eq_refl eq_refl ltac:(img_lia)).
Qed.
Lemma ok_F : okr (ly_F ly) kFakeStackSize.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_F ly) kFakeStackSize ZZ. ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X _]|[[X _]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try img_lia.
- zd (SX 3 2 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (KX 3 _ eq_refl ltac:(img_lia)).
- zd (SX 0 3 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 3 8 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 3 4 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 3 5 _ _ eq_refl eq_refl ltac:(img_lia)).
Qed.
Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ DT a -> ok a.
Proof. geo'.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X _]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try img_lia.
- img_exact (ND Y).
- zd (KX 2 _ eq_refl ltac:(img_lia)).
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 2 8 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 2 4 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 2 5 _ _ eq_refl eq_refl ltac:(img_lia)).
Qed.
Lemma ok_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) -> ~ (Bv <= a < Bv + kBatchBytes) -> ok a.
Proof. geo'.
intros a Ha NK NB. pose proof HIGH as HI. ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X _]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try img_lia.
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 0 8 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 0 4 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (SX 0 5 _ _ eq_refl eq_refl ltac:(img_lia)).
Qed.
Lemma ok_k : forall a, ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ DK a -> ok a.
Proof. geo'.
intros a Ha ND. pose proof HIGH as HI. zget HI (ck_base B ly k) (ck_extent k) ZZ. ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X Y]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try img_lia.
- zd (KX 2 _ eq_refl ltac:(img_lia)).
- img_exact (ND Y).
- zd (batch_vs_chunk b k Hb_in Hk).
- zd (KX 8 _ eq_refl ltac:(img_lia)).
- zd (KX 4 _ eq_refl ltac:(img_lia)).
- zd (KX 5 _ eq_refl ltac:(img_lia)).
Qed.
Lemma ok_other : forall x a, In x (st_chunks S) -> ck_beg x <> ck_beg k -> ck_base B ly x <= a < ck_base B ly x + ck_extent x -> ok a.
Proof. geo'.
intros x a Hx Hne Ha. pose proof (chunks_disjoint B ly S rd x k M Hx Hk Hne) as DJ.
pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg x) as [|o|r o|c p] eqn:Ebx; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) LO ltac:(img_lia)) as (R1 & R2 & _).
img_apply ok_prim; [img_lia | img_try (zd DJ) | img_try (zd (batch_vs_chunk b x Hb_in Hx))].
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (ZCH x Hx) as ZX. pose proof ZX as (_ & _ & ZZ). unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in ZZ.
pose proof HIGH as HI. ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd, kPage in *. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X Y]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try img_lia.
+ zd (SECX _ 2 _ Gin eq_refl).
+ zd DJ.
+ zd (SECX _ 0 _ Gin eq_refl).
+ zd (SECX _ 8 _ Gin eq_refl).
+ zd (SECX _ 4 _ Gin eq_refl).
+ zd (SECX _ 5 _ Gin eq_refl).
Qed.
Lemma ok_secpage : forall x r o a, In x (st_chunks S) -> ck_beg x = PSec r o -> ly_sec ly r <= a < ly_sec ly r + kPage -> ok a.
Proof. geo'.
intros x r o a Hx Ebx Ha.
pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Ebx in GG.
destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof HIGH as HI. pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) _ Gin) as (_ & IA & _).
pose proof (req_size_bounds (ck_req x) ltac:(img_lia)) as (_ & Q2 & _).
pose proof (zone3_intro ly (ly_sec ly r) (sec_map_size (ck_req x)) IMG ltac:(img_try (clear - Gext G5 G8 Q2; unfold kPage in *; img_lia)) IA (SECX _ 9 _ Gin eq_refl)) as (_ & _ & ZZ).
cbn [fst snd] in ZZ, IA. destruct IA as [I1 I2]. unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in ZZ.
ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd, kPage in *. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X Y]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try img_lia.
- zd (SECX _ 2 _ Gin eq_refl).
-
destruct (sptr_eqb (ck_beg k) (PSec r 4096)) eqn:E.
+ apply sptr_eqb_spec in E. pose proof KF as (_ & _ & _ & _ & _ & _ & _ & _ & GK). rewrite E in GK. destruct GK as (_ & _ & Kbase & _). unfold kPage in Kbase. img_lia.
+ assert (Hne : ck_beg x <> ck_beg k) by (img_try (rewrite Ebx; intros E'; rewrite <- E', sptr_eqb_refl in E; discriminate)).
zd (secmap_vs_chunk x k r _ Hx Hk Ebx Hne).
- pose proof (SECX _ 0 _ Gin eq_refl). zd H.
- zd (SECX _ 8 _ Gin eq_refl).
- zd (SECX _ 4 _ Gin eq_refl).
- zd (SECX _ 5 _ Gin eq_refl).
Qed.
Lemma ok_b : forall a, Bv <= a < Bv + kBatchBytes -> ~ DB a -> ok a.
Proof. geo'.
intros a Ha ND. pose proof HIGH as HI. ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X Y]|[[X Y]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try img_lia.
- pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
destruct (batch_geom b Hb_in) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _). zd (SX 0 2 _ _ eq_refl eq_refl ltac:(img_lia)).
- zd (batch_vs_chunk b k Hb_in Hk).
- img_exact (ND Y).
- pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
destruct (batch_geom b Hb_in) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _). zd (SX 0 8 _ _ eq_refl eq_refl ltac:(img_lia)).
- pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
destruct (batch_geom b Hb_in) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _). zd (SX 0 4 _ _ eq_refl eq_refl ltac:(img_lia)).
- pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
destruct (batch_geom b Hb_in) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _). zd (SX 0 5 _ _ eq_refl eq_refl ltac:(img_lia)).
Qed.
Lemma ok_batch_other : forall b2 a, In b2 (all_batches S) -> b_self b2 <> b_self b ->
ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes -> ok a.
Proof. geo'.
intros b2 a Hb2 Hne Ha. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
img_apply ok_prim; [img_try (unfold kBatchBytes in *; img_lia) | img_try (zd (batch_vs_chunk b2 k Hb2 Hk)) | img_try (zd (batches_apart b2 b Hb2 Hb_in Hne))].
Qed.
Lemma ok_rinfo : okr (ly_rinfo ly) 4096.
Proof. geo'.
intros a Ha. unfold ly_rinfo, kRegionInfoOff in Ha. pose proof HIGH as HI. unfold kSpaceSize in HI.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (batch_geom b Hb_in) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1 & R2 & _).
img_apply ok_prim; [img_lia | | img_try (unfold region_base, kBatchBytes in *; rewrite region_off_eq in * by (unfold kBatchClass; img_lia); unfold kBatchClass in *; img_lia)].
destruct (ext_zone k Hk) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- unfold region_base in *. rewrite !region_off_eq in * by img_lia.
pose proof (Z.mul_le_mono_nonneg_r (c + 1) 32 (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_change (32 * 2 ^ 32) with (2 ^ 37) in H. img_lia.
- pose proof (SECX _ 0 _ Xin eq_refl) as DJ. unfold zdisjoint, kPage, kPrimResvSize in *. cbn [fst snd] in DJ. img_lia.
Qed.
Lemma ok_fa : forall c, 1 <= c <= 31 -> okr (fa_base ly c) kFreeArrayMax.
Proof. geo'.
intros c Hc a Ha. pose proof HIGH as HI. pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & R3 & R4 & R5). unfold fa_base, kFreeArrayOffset, kFreeArrayMax in *.
assert (E32 : region_base ly c = ly_space ly + region_off c) by img_refl.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (batch_geom b Hb_in) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(img_try (unfold kBatchClass; img_lia))) as (R1' & R2' & _).
img_apply ok_prim; [img_lia | |].
- destruct (ext_zone k Hk) as [(c' & Hc' & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
+ destruct (Z.eq_dec c' c) as [Ec|Hne].
* rewrite Ec in *. unfold region_base in *. img_lia.
* unfold region_base in *. rewrite !region_off_eq in * by img_lia.
destruct (Z.lt_ge_cases c' c).
-- pose proof (Z.mul_le_mono_nonneg_r (c' + 1) c (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
-- pose proof (Z.mul_le_mono_nonneg_r (c + 1) c' (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
+ pose proof (SECX _ 0 _ Xin eq_refl) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ. img_lia.
- unfold kBatchBytes in *. destruct (Z.eq_dec kBatchClass c) as [Ec|Hne].
+ rewrite <- Ec in *. unfold region_base in *. img_lia.
+ unfold region_base in *. rewrite !region_off_eq in * by (img_try (unfold kBatchClass; img_lia)). unfold kBatchClass in *.
destruct (Z.lt_ge_cases 24 c).
* pose proof (Z.mul_le_mono_nonneg_r (24 + 1) c (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
* pose proof (Z.mul_le_mono_nonneg_r (c + 1) 24 (2 ^ 32) ltac:(img_lia) ltac:(img_lia)). img_lia.
Qed.
Lemma ok_low : forall a, TFX_IMG_LO <= a < TFX_IMG_END -> ~ DI a -> ~ (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) -> ~ (as_store B <= a < as_store B + 64) -> ok a.
Proof. geo'.
intros a Ha N1 N2 N3. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZT. zget HI (ck_base B ly k) (ck_extent k) ZK. zget HI (ly_NB ly) kNodesBlockSize ZNB. zget HI (ly_SB ly) kStoreBlockSize ZSB. ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [img_lia|]. intros HD.
pose proof HD as HD0. apply D_cases in HD as [[X Y]|[[X Y]|[[X Y]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try img_lia.
destruct HD0 as [Y|[Y|[Y|[Y|[Y|[Y|Y]]]]]].
- unfold DT, t_qc, t_unwinding, t_stats in Y. img_lia.
- unfold DK in Y. rewrite Hu in Y. pose proof ext_rounded as (ER & NN1 & NN2 & NN3). img_lia.
- unfold DB in Y. pose proof BC_len. unfold kBatchSlots, kBatchBytes in *. img_lia.
- unfold DS, ASTACK in *. img_lia.
- img_exact (N1 Y).
- unfold depot_footprint in Y. destruct Y as [Y|[Y|[Y|Y]]]; [img_try (img_exact (N2 Y)) | img_lia | img_lia | img_try (img_exact (N3 Y))].
- unfold DH, shadow_addr, SHADOW_OFF in Y. rewrite Hu in Y.
pose proof (Z.div_pos (ck_base B ly k + ck_rz k) 8 ltac:(img_lia) ltac:(img_lia)). img_lia.
Qed.
Lemma ok_inst : okr (as_inst B) 3632.
Proof. geo'.
intros a Ha. rewrite (ts_inst _ TB) in Ha. img_apply ok_low; unfold DI; rewrite ?(ts_ial_lo _ TB), ?(ts_ial_hi _ TB), ?(ts_ial_flag _ TB), ?(ts_depot _ TB), ?(ts_store _ TB);
unfold TFX_INST, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_DEPOT, TFX_STORE, d_map1, TFX_IMG_LO, TFX_IMG_END in *; img_lia.
Qed.
Lemma ok_hshadow : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ DH a -> ok a.
Proof. geo'.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_Q ly) kPtrArrayResv ZQ. zget HI (ly_T ly) kThreadObjSize ZT. zget HI (ly_F ly) kFakeStackSize ZF.
zget HI (ck_base B ly k) (ck_extent k) ZK. zget HI (ly_NB ly) kNodesBlockSize ZNB. zget HI (ly_SB ly) kStoreBlockSize ZSB. zget HI (ly_C ly) 256 ZC. ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [img_lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X Y]|[[X Y]|[X|[X|[X|[X|[X Y]]]]]]]]; ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try img_lia. img_exact (ND Y).
Qed.
Definition cell_in (lo len : Z) (c : acell) : Prop :=
lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len.
Lemma cell_xfer : forall c, cell_holds B ly rd c ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> ok (aeval B ly (c_at c) + j)) -> cell_holds B ly rd' c.
Proof. intros c Hc Hok. eapply (cell_holds_agree B ly rd rd' c Hc). intros j Hj. apply AGok, Hok, Hj. Qed.
Lemma cells_xfer : forall L lo len, okr lo len -> Forall (cell_in lo len) L -> Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd') L.
Proof.
intros L lo len OK IN OLD. img_apply Forall_forall. intros c Hc. img_apply cell_xfer; [img_try (img_exact (proj1 (Forall_forall _ _) OLD c Hc))|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN c Hc) as [H1 H2]. img_apply OK. img_lia.
Qed.
Lemma OLD : forall c, In c (acells B ly S) -> cell_holds B ly rd c.
Proof. intros c Hc. img_exact (proj1 (Forall_forall _ _) (am_cells B ly S rd M) c Hc). Qed.
Ltac old_in := img_apply Forall_forall; intros ? HIN; img_apply OLD; unfold acells; rewrite !in_app_iff.
Lemma EA : forall y d, In y (st_chunks S) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. geo'.
intros y d Hy. pose proof (chunk_facts B ly S rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma EA2 : forall y d d', In y (st_chunks S) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. geo'.
intros y d d' Hy. pose proof (chunk_facts B ly S rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma EA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. geo'. img_refl. Qed.
Lemma hdr_addr : forall y, In y (st_chunks S) -> aeval B ly (sptr_exp (ck_hdr y)) = ck_base B ly y + ck_rz y - kChunkHeaderSize.
Proof. geo'.
intros y Hy. pose proof (chunk_facts B ly S rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_hdr, ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; img_lia.
Qed.
Lemma hdr_bytes : YG0h.le_byte (3 + 256 * hb1) 4 0 = 3 /\ YG0h.le_byte (3 + 256 * hb1) 4 1 = hb1 /\
YG0h.le_byte (3 + 256 * hb1) 4 2 = 0 /\ YG0h.le_byte (3 + 256 * hb1) 4 3 = 0.
Proof. geo.
destruct Hhb1 as [R _]. unfold YG0h.le_byte. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
rewrite (Z.mod_small _ 4294967296) by img_lia.
img_change (8 * Z.of_nat 0) with 0. img_change (8 * Z.of_nat 1) with 8. img_change (8 * Z.of_nat 2) with 16. img_change (8 * Z.of_nat 3) with 24.
rewrite !Z.shiftr_div_pow2 by img_lia. img_change (2 ^ 0) with 1. img_change (2 ^ 8) with 256. img_change (2 ^ 16) with 65536. img_change (2 ^ 24) with 16777216.
rewrite Z.div_1_r. splits.
- rewrite (Z.mul_comm 256 hb1), Z_mod_plus_full. img_refl.
- rewrite Z.add_comm, (Z.mul_comm 256 hb1), Z_div_plus_full_l by img_lia. img_change (3 / 256) with 0. rewrite Z.add_0_r. img_apply Z.mod_small. img_lia.
- rewrite Z.div_small by img_lia. img_refl.
- rewrite Z.div_small by img_lia. img_refl.
Qed.
Ltac fcons := img_apply Forall_cons; [img_try (split; cbn; img_lia)|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S') (zseq 1 31)).
Proof.
img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold region_cells. rewrite reg'.
img_apply (cells_xfer _ _ _ ok_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fcons. img_apply Forall_nil.
- old_in. left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; img_lia) | img_try (img_exact HIN)].
Qed.
Lemma okr_cache : okr (T + t_cache + 80) (80 * 31).
Proof. geo'. intros a Ha. img_apply ok_T; unfold DT, t_cache, t_qc, t_unwinding, t_stats, kThreadObjSize in *; img_lia. Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S') (zseq 1 31)).
Proof.
img_apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold cache_cells. rewrite cache', S'_cinit.
img_apply (cells_xfer _ _ _ okr_cache).
- pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c ltac:(img_lia)) as (_ & _ & _ & K4 & _).
unfold cell_in, t_cache. destruct (st_cache_inited S).
+ destruct WC as [PM PL]. repeat fcons. img_apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. img_lia.
+ repeat fcons. img_apply Forall_nil.
- old_in. right; left. img_apply in_flat_map. exists c. split; [img_try (img_apply In_zseq; img_lia) |]. unfold cache_cells. img_exact HIN.
Qed.
Lemma cells_chunk_other : forall x, In x (st_chunks S) -> ck_beg x <> ck_beg k -> Forall (cell_holds B ly rd') (chunk_cells x).
Proof.
intros x Hx Hne. pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
img_apply (cells_xfer _ (ck_base B ly x) (ck_extent x)); [img_try (intros a Ha; img_exact (ok_other x a Hx Hne Ha)) | |].
- pose proof (req_size_bounds (ck_req x) ltac:(img_lia)) as (_ & Q2 & _).
unfold chunk_cells, kChunkHeaderSize, cell_in. img_apply Forall_app. split.
+ repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(EA2 x), ?(EA x), ?EA0 by img_exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; img_lia)|]). img_apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz x) 16); [img_try (img_apply Forall_nil)|].
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; rewrite ?(EA2 x), ?(EA x), ?EA0 by img_exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; img_lia)|]). img_apply Forall_nil.
- old_in. do 2 right; left. img_apply in_flat_map. exists x. split; [img_try (img_exact Hx) | img_try (img_exact HIN)].
Qed.
Lemma cells_chunk_k : Forall (cell_holds B ly rd') (chunk_cells k').
Proof.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof hdr_bytes as (HB0 & HB1 & HB2 & HB3). destruct Hhb1 as [_ HM].
assert (Hk' : forall d, aeval B ly (aoff (sptr_exp (ck_beg k')) d) = ck_base B ly k + d) by (img_try (intros d; img_exact (EA k d Hk))).
assert (Hk'2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k')) d) d') = ck_base B ly k + d + d') by (img_try (intros d d'; img_exact (EA2 k d d' Hk))).
unfold chunk_cells. rewrite k'_rz, k'_n. unfold kChunkHeaderSize. img_apply Forall_app. split.
- assert (EU : ck_base B ly k + (ck_rz k - 16) = u - 16) by (img_try (rewrite Hu; img_lia)).
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1]. rewrite Hk', EU. img_change (aeval B ly (ANum (hdr_state k'))) with 3.
intros kk Hkk. rewrite NEW_hdr by img_lia. destruct kk; [|img_lia]. rewrite HB0. img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w]. rewrite Hk'2, EU. exists hb1. split; [|img_try (img_exact HM)].
img_change (u - 16 + 1) with (u - 16 + Z.of_nat 1). rewrite (NEW_hdr 1%nat) by img_lia. rewrite HB1. img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z2 c2]. rewrite Hk'2, EU. img_change (aeval B ly (ANum 0)) with 0. intros kk Hkk.
replace (u - 16 + 2 + Z.of_nat kk) with (u - 16 + Z.of_nat (2 + kk)) by img_lia. rewrite NEW_hdr by img_lia.
destruct kk as [|[|]]; cbn [Nat.add]; [img_try (rewrite HB2; img_refl) | img_try (rewrite HB3; img_refl) | img_lia]. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z4 c4]. rewrite Hk'2, EU. img_change (aeval B ly (ANum nn)) with nn. intros kk Hkk.
replace (u - 16 + 4 + Z.of_nat kk) with (u - 12 + Z.of_nat kk) by img_lia. rewrite NEW_n by img_lia. img_refl. }
img_apply Forall_nil.
- destruct (Z.eqb_spec (ck_rz k) 16) as [E16|N16]; [img_try (img_apply Forall_nil)|].
assert (32 <= ck_rz k). { pose proof G6 as G6'. apply Z.mod_divide in G6' as [q Hq]; [|img_lia]. img_lia. }
assert (OKM : okr (ck_base B ly k) 16).
{ pose proof ext_rounded as (ER & NN1 & NN2 & NN3). intros a Ha. img_apply ok_k; [img_lia|]. unfold DK. rewrite Hu. img_lia. }
img_apply (cells_xfer _ _ _ OKM).
+ unfold cell_in. img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; rewrite (EA0 k'), k'_base; cbn; img_lia)|].
img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; rewrite Hk'; cbn; img_lia)|]. img_apply Forall_nil.
+
assert (OLDK : Forall (cell_holds B ly rd) (chunk_cells k)).
{ old_in. do 2 right; left. img_apply in_flat_map. exists k. split; [img_try (img_exact Hk) | img_try (img_exact HIN)]. }
unfold chunk_cells, kChunkHeaderSize in OLDK. apply Forall_app in OLDK as [_ OLDK]. destruct (Z.eqb_spec (ck_rz k) 16); [img_lia|]. img_exact OLDK.
Qed.
Lemma cells_chunks : forall l1 l2, st_chunks S = l1 ++ k :: l2 -> ~ In (ck_beg k) (map ck_beg l1) -> ~ In (ck_beg k) (map ck_beg l2) ->
Forall (cell_holds B ly rd') (flat_map chunk_cells (l1 ++ k' :: l2)).
Proof.
intros l1 l2 E N1 N2. rewrite flat_map_app. cbn [flat_map]. rewrite !Forall_app. splits.
- img_apply Forall_flat_map'. intros x Hx. img_apply cells_chunk_other; [img_try (rewrite E; img_apply in_app_iff; left; img_exact Hx) | img_try (intros Ex; img_apply N1; rewrite <- Ex; img_apply in_map; img_exact Hx)].
- img_exact cells_chunk_k.
- img_apply Forall_flat_map'. intros x Hx. img_apply cells_chunk_other; [img_try (rewrite E; img_apply in_app_iff; right; right; img_exact Hx) | img_try (intros Ex; img_apply N2; rewrite <- Ex; img_apply in_map; img_exact Hx)].
Qed.
Lemma cells_sec : forall l1 l2, st_chunks S = l1 ++ k :: l2 -> Forall (cell_holds B ly rd') (sec_cells S').
Proof.
intros l1 l2 E. pose proof SPLIT as (l1' & l2' & E0 & E' & _).
pose proof (wf_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells S)) by (img_try (old_in; do 3 right; left; img_exact HIN)).
unfold sec_cells in OLDS |- *. rewrite S'_sec_res, S'_sec_arr, E'. rewrite (flat_map_mid _ l1' k' k l2') by img_refl. rewrite <- E0.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof ok_inst as OKI.
img_apply Forall_cons; [img_apply (cell_xfer _ O1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_reserved; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_n; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O3); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_sec_mutex; img_lia|].
img_apply Forall_app. split.
- img_apply (cells_xfer _ _ _ ok_Q); [|img_try (img_exact O4)]. img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. img_lia.
- img_apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) O5 c Hc) as Oc. apply in_flat_map in Hc as (x & Hx & Hc).
destruct (ck_beg x) as [|o|r o|c' p] eqn:Ebx; try solve [destruct Hc].
assert (OKP : okr (ly_sec ly r) 32) by (img_try (intros a Ha; eapply (ok_secpage x r o a Hx Ebx); unfold kPage; img_lia)).
img_apply (cell_xfer _ Oc). intros j Hj. img_apply OKP. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; img_lia.
Qed.
Lemma batch_cells_within : forall l c, In c (batch_cells l) ->
exists b2, In b2 l /\ cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) c.
Proof. geo'.
induction l as [|b2 t IH]; intros c Hc; [img_try (destruct Hc)|]. cbn [batch_cells] in Hc.
destruct Hc as [<-|[<-|[<-|Hc]]]; try (exists b2; split; [img_try (left; img_refl) | img_try (unfold cell_in; cbn; img_lia)]).
apply in_app_iff in Hc as [Hc|Hc].
- apply in_map_iff in Hc as ([i x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. exists b2. split; [img_try (left; img_refl) | img_try (unfold cell_in; cbn; img_lia)].
- destruct (IH c Hc) as (b3 & H3 & R3). exists b3. split; [img_try (right; img_exact H3) | img_try (img_exact R3)].
Qed.
Lemma self_ne : forall b2, In b2 (rev initr) \/ In b2 (qc_list (st_qglobal S)) -> In b2 (all_batches S) /\ b_self b2 <> b_self b.
Proof. geo'.
intros b2 Hb2. pose proof batches_nodup as ND. rewrite all_batches_S in ND |- *. rewrite !map_app in ND. cbn [map] in ND.
split; [img_try (rewrite !in_app_iff; cbn; tauto)|].
rewrite <- app_assoc in ND. apply NoDup_app_iff in ND as (N1 & N2 & N3). cbn in N2. inversion N2 as [|y l N4 N5]; (subst; cbv beta).
intros E. destruct Hb2 as [Hb2|Hb2].
- img_apply (N3 (b_self b2)); [img_try (img_apply in_map; img_exact Hb2) | img_try (left; symmetry; img_exact E)].
- img_apply N4. rewrite <- E. img_apply in_map. img_exact Hb2.
Qed.
Lemma okr_batch_other : forall b2, In b2 (rev initr) \/ In b2 (qc_list (st_qglobal S)) -> okr (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))).
Proof. geo'.
intros b2 Hb2 a Ha. destruct (self_ne b2 Hb2) as [IN NE].
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 IN) as [L1 L2]. unfold kBatchSlots in L2.
img_apply (ok_batch_other b2 a IN NE). unfold kBatchBytes. img_lia.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S').
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells S)) by (img_try (old_in; do 4 right; left; img_exact HIN)).
pose proof ok_inst as OKI. pose proof BC_len as [BL1 BL2].
unfold quar_cells, qc_cells in OLDQ |- *. rewrite S'_qglobal, qlist', qbytes'. rewrite qlist in OLDQ.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
img_apply Forall_cons; [img_apply (cell_xfer _ O1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_cmutex; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ O2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_rmutex; img_lia|].
img_apply Forall_app. split.
-
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8]. intros kk Hkk. cbn [aeval]. rewrite NEW_qs by img_exact Hkk. rewrite qlist, !length_app. img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w c8]. intros kk Hkk. cbn [aeval aoff].
replace (T + (t_qc + 8)) with (T + t_qc + 8) by img_lia. rewrite NEW_qf by img_exact Hkk. rewrite qlist. do 2 f_equal.
destruct (rev initr); img_refl. }
img_apply Forall_cons. { rewrite rev_app_distr. cbn [rev app cell_holds c_at c_val c_w c8 aeval aoff batch_exp b_self b']. intros kk Hkk.
replace (T + (t_qc + 16)) with (T + t_qc + 16) by img_lia. rewrite NEW_ql by img_exact Hkk. img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff]. intros kk Hkk.
replace (T + (t_qc + 24)) with (T + t_qc + 24) by img_lia. rewrite NEW_qb by img_exact Hkk. img_refl. }
destruct (batch_cells_snoc (rev initr) b b' eq_refl) as (P & EP & EP' & HP). rewrite EP in OT. rewrite EP'. apply Forall_app in OT as [OP OB]. img_apply Forall_app. split.
+
img_apply Forall_forall. intros c Hc. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OP c Hc)). destruct (HP c Hc) as (b2 & I2 & Hb2).
destruct Hb2 as [C2|(nx & _ & ->)].
* destruct (batch_cells_within [b2] c C2) as (b3 & [<-|[]] & [R1 R2]). intros j Hj. img_apply (okr_batch_other b2 (or_introl I2)). img_lia.
* intros j Hj. cbn in Hj |- *. img_apply (okr_batch_other b2 (or_introl I2)).
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 (proj1 (self_ne b2 (or_introl I2)))) as [L1 _]. img_lia.
+
cbn [batch_cells app]. rewrite app_nil_r. cbn [batch_cells app] in OB. rewrite app_nil_r in OB.
apply Forall_cons_iff in OB as [OB1 OB]. apply Forall_cons_iff in OB as [_ OB]. apply Forall_cons_iff in OB as [_ OB].
assert (OKB : forall a, Bv <= a < Bv + 8 \/ Bv + 24 <= a < SLOTv -> ok a).
{ intros a Ha. img_apply ok_b; [img_try (unfold kBatchSlots, kBatchBytes in *; img_lia)|]. unfold DB. img_lia. }
img_apply Forall_cons. { img_apply (cell_xfer _ OB1). intros j Hj. img_apply OKB. cbn in Hj |- *. img_lia. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff batch_exp b_self b']. intros kk Hkk.
replace (ly_space ly + (b_self b + 8)) with (Bv + 8) by img_lia. rewrite NEW_bb by img_exact Hkk. rewrite b'_bytes. img_refl. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval aoff batch_exp b_self b_items b']. intros kk Hkk.
replace (ly_space ly + (b_self b + 16)) with (Bv + 16) by img_lia. rewrite NEW_bc by img_exact Hkk.
rewrite length_app. cbn [length]. do 2 f_equal. img_lia. }
cbn [b_items b_self b']. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, (combine_snoc _ _ _ eq_refl), map_app. cbn [map fst snd]. img_apply Forall_app. split.
* img_apply Forall_forall. intros c Hc. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OB c Hc)).
apply in_map_iff in Hc as ([i x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. intros j Hj. img_apply OKB. cbn in Hj |- *. img_lia.
* img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. cbn [cell_holds c_at c_val c_w c8 aeval aoff batch_exp b_self b']. intros kk Hkk.
replace (ly_space ly + (b_self b + (24 + 8 * BCv)) + Z.of_nat kk) with (SLOTv + Z.of_nat kk) by img_lia.
rewrite NEW_slot by img_exact Hkk. img_change (ck_hdr k') with (ck_hdr k). rewrite (hdr_addr k Hk). rewrite Hu. unfold kChunkHeaderSize. do 2 f_equal; img_lia.
-
apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
img_apply Forall_cons; [img_apply (cell_xfer _ G1); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G2); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G3); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_cons; [img_apply (cell_xfer _ G4); intros j Hj; img_apply OKI; cbn in Hj |- *; unfold o_q_size; img_lia|].
img_apply Forall_forall. intros c Hc. img_apply (cell_xfer _ (proj1 (Forall_forall _ _) OG c Hc)).
destruct (batch_cells_within _ c Hc) as (b2 & I2 & [R1 R2]). intros j Hj. img_apply (okr_batch_other b2 (or_intror I2)). img_lia.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S').
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells S)) by (img_try (old_in; do 5 right; left; img_exact HIN)).
unfold fs_cells in OLDF |- *. rewrite S'_fs. img_apply (cells_xfer _ _ _ ok_F); [|img_try (img_exact OLDF)].
unfold cell_in, kFakeStackSize. fcons. fcons.
img_apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. img_lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S').
Proof. destruct DEP as (D1 & _ & _). unfold depot_cells, depot_ids, depot_frames in D1 |- *. rewrite S'_depot. img_exact D1. Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|img_lia].
cbn [Z.of_nat]. rewrite Z.add_0_r, NEW_unw. img_refl.
Qed.
Lemma cells_all : Forall (cell_holds B ly rd') (acells B ly S').
Proof.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). unfold acells. rewrite E'.
rewrite !Forall_app. splits.
- img_exact cells_regions.
- img_exact cells_caches.
- img_exact (cells_chunks l1 l2 E N1 N2).
- img_exact (cells_sec l1 l2 E).
- img_exact cells_quar.
- img_exact cells_fs.
- img_exact cells_depot.
- img_exact (proj1 IAL).
- img_exact cells_thread.
Qed.
Lemma fa' : fa_entries_ok ly rd' S'.
Proof.
intros c i v Hc Hi Hv kk Hkk. rewrite reg' in Hi, Hv. rewrite AGok; [img_try (img_exact (am_fa B ly S rd M c i v Hc Hi Hv kk Hkk))|].
pose proof (wf_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
img_apply (ok_fa c Hc). img_lia.
Qed.
Lemma flags' : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hc Hp. rewrite frames'. rewrite AGok; [img_try (img_exact (am_flags B ly S rd M cid pos Hc Hp))|].
pose proof (flag_off_bounds cid pos Hc Hp) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *. img_apply ok_F. unfold kFakeStackSize. img_lia.
Qed.
Lemma depot' : depot_ok B ly rd' S'.
Proof. destruct DEP as (_ & D2 & _). unfold depot_ok, depot_ids, depot_traces in D2 |- *. rewrite S'_depot. img_exact D2. Qed.
Lemma fa_poison' : fa_poison_ranges ly S' = fa_poison_ranges ly S.
Proof. geo'.
pose proof SPLIT as (l1 & l2 & E & E' & _). unfold fa_poison_ranges, reg. rewrite S'_regions, E', E.
rewrite (flat_map_mid _ l1 k' k l2) by img_refl. img_refl.
Qed.
Lemma sec_extents' : sec_extents ly S' = sec_extents ly S.
Proof. geo'.
pose proof SPLIT as (l1 & l2 & E & E' & _). unfold sec_extents. rewrite E', E. rewrite (flat_map_mid _ l1 k' k l2) by img_refl. img_refl.
Qed.
Lemma asecA_S' : forall A, asecA ly S A -> asecA ly S' A.
Proof. intros A H e He. rewrite sec_extents' in He. img_exact (H e He). Qed.
Lemma hs_bounds : forall g, 4096 <= g -> g + 8 <= kHighMemEnd -> kLowShadowBeg <= shadow_addr g < kHighMemBeg.
Proof. geo'.
intros g H1 H2. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
pose proof (Z.div_le_mono 4096 g 8 ltac:(img_lia) H1) as X. img_change (4096 / 8) with 512 in X.
pose proof (Z.div_le_mono g (140737488355328 - 8) 8 ltac:(img_lia) ltac:(img_lia)) as Y. img_change ((140737488355328 - 8) / 8) with 17592186044415 in Y. img_lia.
Qed.
Lemma DH_iff : forall g, g mod 8 = 0 -> (DH (shadow_addr g) <-> u <= g < u + (nn + 7) / 8 * 8).
Proof. geo'.
intros g Hg. pose proof u_al8 as (U8 & _ & _). unfold DH, shadow_addr.
apply Z.mod_divide in Hg as [c Hc]; [|img_lia]. apply Z.mod_divide in U8 as [a Ha]; [|img_lia]. rewrite Hc, Ha.
rewrite !Z_div_mult by img_lia. pose proof ext_rounded as (_ & _ & NN2 & _). nia.
Qed.
Lemma fa_poison_high : forall lo len g, In (lo, len) (fa_poison_ranges ly S) -> lo <= g < lo + len -> 4096 <= g /\ g < ASAN_CEIL.
Proof. geo'.
intros lo len g Hin Hg. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LO ltac:(img_lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c ltac:(img_lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c WF ltac:(img_lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
unfold kHighMemBeg in *. destruct Hin as [E|[E|[]]]; injection E as <- <-; img_lia.
- pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3. ceil. unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *. img_lia.
Qed.
Lemma shadow' : shadow_ok B ly rd' S'.
Proof.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof ext_rounded as (ER & NN1 & NN2 & NN3). pose proof u_al8 as (U8 & B8 & R8).
intros g v Hg8 HS'. pose proof (am_shadow B ly S rd M g) as SH.
unfold ashadow in HS', SH. rewrite E', fa_poison' in HS'. rewrite E in SH.
rewrite find_chunk_at_app in HS', SH. cbn [find_chunk_at] in HS', SH. rewrite k'_base, k'_extent in HS'.
assert (OTHER : forall x, In x (st_chunks S) -> ck_beg x <> ck_beg k -> ck_base B ly x <= g < ck_base B ly x + ck_extent x ->
rd (shadow_addr g) = Some v -> rd' (shadow_addr g) = Some v).
{ intros x Hx Hne Hgx Hrd. pose proof (chunk_facts B ly S rd x M Hx) as (X1 & X2 & _).
rewrite AGok; [img_try (img_exact Hrd)|]. img_apply ok_hshadow; [img_try (img_apply hs_bounds; ceil; unfold in_app, zone3, ASAN_CEIL, kHighMemEnd in *; img_lia)|]. intros HD. apply (DH_iff g Hg8) in HD.
pose proof (chunks_disjoint B ly S rd x k M Hx Hk Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. rewrite Hu in HD. img_lia. }
destruct (find_chunk_at B ly l1 g) as [x|] eqn:F1.
- apply find_chunk_at_In in F1 as [Hx Hgx].
img_apply (OTHER x); [img_try (rewrite E; img_apply in_app_iff; left; img_exact Hx) | img_try (intros Ex; img_apply N1; rewrite <- Ex; img_apply in_map; img_exact Hx) | img_try (img_exact Hgx) | img_try (img_exact (SH v Hg8 HS'))].
- destruct ((ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k)) eqn:TK.
+
apply andb_prop in TK as [T1 T2]. apply Z.leb_le in T1. apply Z.ltb_lt in T2.
apply Z.mod_divide in Hg8 as [c Hc]; [|img_lia]. apply Z.mod_divide in B8 as [b0 Hb0]; [|img_lia]. apply Z.mod_divide in R8 as [r0 Hr0]; [|img_lia].
assert (J : (g - ck_base B ly k) / 8 = c - b0). { rewrite Hc, Hb0. replace (c * 8 - b0 * 8) with ((c - b0) * 8) by img_lia. img_apply Z_div_mult. img_lia. }
assert (RU : ck_rz k / 8 = r0). { rewrite Hr0. img_apply Z_div_mult. img_lia. }
rewrite k'_base in HS'. rewrite J in HS', SH. unfold chunk_granule in HS', SH. rewrite k'_rz, k'_n, RU in HS'. rewrite RU, Hst in SH. cbn [ck_state k'] in HS'.
set (q := (nn + 7) / 8) in *.
destruct (c - b0 <? r0) eqn:C1.
*   apply Z.ltb_lt in C1. injection HS' as <-. rewrite AGok; [img_try (img_exact (SH _ ltac:(rewrite Hc; img_apply Z_mod_mult) eq_refl))|].
img_apply ok_hshadow; [img_try (img_apply hs_bounds; ceil; unfold in_app, zone3, ASAN_CEIL, kHighMemEnd in *; img_lia)|]. intros HD. apply (DH_iff g ltac:(img_try (rewrite Hc; img_apply Z_mod_mult))) in HD. rewrite Hu in HD. nia.
* apply Z.ltb_ge in C1. destruct (c - b0 <? r0 + q) eqn:C2.
--   apply Z.ltb_lt in C2. injection HS' as <-. img_apply NEW_sh; [img_try (img_apply (DH_iff g ltac:(rewrite Hc; img_apply Z_mod_mult)); rewrite Hu; nia)|].
rewrite (SH (if c - b0 <? r0 + nn / 8 then shAddressable else if (c - b0 =? r0 + nn / 8) && negb (nn mod 8 =? 0) then nn mod 8 else shHeapLeftRz));
[img_try (discriminate) | img_try (rewrite Hc; img_apply Z_mod_mult) | img_refl].
--   apply Z.ltb_ge in C2. injection HS' as <-.
assert (OLDV : rd (shadow_addr g) = Some shHeapLeftRz).
{ img_apply SH; [img_try (rewrite Hc; img_apply Z_mod_mult)|].
assert (F1' : c - b0 <? r0 + nn / 8 = false). { img_apply Z.ltb_ge. (subst q; cbv beta). pose proof (Z.div_le_mono nn (nn + 7) 8 ltac:(img_lia) ltac:(img_lia)). img_lia. }
rewrite F1'. destruct (Z.eqb_spec (nn mod 8) 0) as [Z0|NZ]; cbn [negb andb]; [img_try (rewrite Bool.andb_false_r; img_refl)|].
replace (c - b0 =? r0 + nn / 8) with false; [img_refl|]. symmetry. img_apply Z.eqb_neq. (subst q; cbv beta).
pose proof (Z.div_mod nn 8 ltac:(img_lia)) as DM. pose proof (Z.mod_pos_bound nn 8 ltac:(img_lia)) as MB.
pose proof (Z.div_mod (nn + 7) 8 ltac:(img_lia)) as DM'. pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(img_lia)) as MB'. nia. }
rewrite AGok; [img_try (img_exact OLDV)|]. img_apply ok_hshadow; [img_try (img_apply hs_bounds; ceil; unfold in_app, zone3, ASAN_CEIL, kHighMemEnd in *; img_lia)|]. intros HD.
apply (DH_iff g ltac:(img_try (rewrite Hc; img_apply Z_mod_mult))) in HD. rewrite Hu in HD. nia.
+
assert (NK : ~ (ck_base B ly k <= g < ck_base B ly k + ck_extent k)).
{ intros X. assert (TT : (ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k) = true) by (img_try (img_apply andb_true_intro; split; [img_try (img_apply Z.leb_le) | img_try (img_apply Z.ltb_lt)]; img_lia)). rewrite TT in TK. discriminate. }
destruct (find_chunk_at B ly l2 g) as [x|] eqn:F2.
* apply find_chunk_at_In in F2 as [Hx Hgx].
img_apply (OTHER x); [img_try (rewrite E; img_apply in_app_iff; right; right; img_exact Hx) | img_try (intros Ex; img_apply N2; rewrite <- Ex; img_apply in_map; img_exact Hx) | img_try (img_exact Hgx) | img_try (img_exact (SH v Hg8 HS'))].
* destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|img_try (discriminate)].
pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg). pose proof (fa_poison_high lo len g Hin Hg) as [Y1 Y2].
rewrite AGok; [img_try (img_exact (SH v Hg8 HS'))|]. img_apply ok_hshadow; [img_try (img_apply hs_bounds; ceil; unfold in_app, zone3, ASAN_CEIL, kHighMemEnd in *; img_lia)|]. intros HD. apply (DH_iff g Hg8) in HD. rewrite Hu in HD. img_lia.
Qed.
Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (am_zshadow B ly S rd M) as ZS. unfold zshadow_ok in ZS |- *. img_apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGok; [img_try (img_exact Z0)|]. pose proof HIGH as HI. pose proof ext_rounded as (ER & _).
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in Hi |- *.
-
pose proof (lo_top _ LO) as (_ & _ & _ & T4 & T5 & _). unfold page_aligned in T5. apply Z.mod_divide in T5 as [s0 Hs0]; [|img_lia].
assert (E8 : shadow_addr (ly_stk_lo ly) + i = shadow_addr (ly_stk_lo ly + 8 * i)).
{ unfold shadow_addr. rewrite Hs0. replace (s0 * 4096) with ((512 * s0) * 8) by img_lia. replace (512 * s0 * 8 + 8 * i) with ((512 * s0 + i) * 8) by img_lia. rewrite !Z_div_mult by img_lia. img_lia. }
rewrite E8. pose proof (Z.mul_div_le (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(img_lia)).
img_apply ok_hshadow; [img_try (img_apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; img_lia)|].
intros HD. apply (DH_iff (ly_stk_lo ly + 8 * i) ltac:(img_try (rewrite Hs0; replace (s0 * 4096 + 8 * i) with ((512 * s0 + i) * 8) by img_lia; img_apply Z_mod_mult))) in HD.
rewrite Hu in HD. pose proof (KX 8 _ eq_refl ltac:(img_lia)) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. img_lia.
-
rewrite (ts_zsh _ TB) in Hr. unfold Tfx_zero_shadow in Hr.
assert (R8 : exists lo len, r = (lo, len) /\ lo mod 8 = 0 /\ TFX_IMG_LO <= lo /\ lo + len <= TFX_IMG_END).
{ destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; eexists _, _; (split; [img_refl|]); unfold TFX_IMG_LO, TFX_IMG_END; (split; [img_refl|]); img_lia. }
destruct R8 as (lo & len & -> & L8 & L1 & L2). cbn [fst snd] in Hi |- *. clear Hr.
apply Z.mod_divide in L8 as [c Hc]; [|img_lia].
assert (E8 : shadow_addr lo + i = shadow_addr (lo + 8 * i)).
{ unfold shadow_addr. rewrite Hc. replace (c * 8 + 8 * i) with ((c + i) * 8) by img_lia. rewrite !Z_div_mult by img_lia. img_lia. }
rewrite E8. pose proof (Z.mul_div_le len 8 ltac:(img_lia)).
img_apply ok_hshadow; [img_try (img_apply hs_bounds; unfold TFX_IMG_LO, TFX_IMG_END, kHighMemEnd in *; img_lia)|].
intros HD. apply (DH_iff (lo + 8 * i) ltac:(img_try (rewrite Hc; replace (c * 8 + 8 * i) with ((c + i) * 8) by img_lia; img_apply Z_mod_mult))) in HD.
rewrite Hu in HD. zget HI (ck_base B ly k) (ck_extent k) ZK. pose proof ext_rounded as (ER' & NN1 & NN2 & NN3). pose proof KF as (_ & _ & _ & _ & G5 & _).
ceil. unfold TFX_IMG_LO, TFX_IMG_END, ASAN_CEIL in *. img_lia.
Qed.
Lemma vis_keep : forall L, Forall (range_vis B ly rd) L -> Forall (range_vis B ly rd') L.
Proof. intros L H. img_exact (Forall_range_vis_keep B ly rd rd' L VIS H). Qed.
Lemma vis_sub : forall r r', range_vis B ly rd r' -> aeval B ly (fst r') <= aeval B ly (fst r) ->
aeval B ly (fst r) + snd r <= aeval B ly (fst r') + snd r' -> range_vis B ly rd' r.
Proof.
intros r r' V H1 H2 i Hi. img_apply VIS. replace (aeval B ly (fst r) + i) with (aeval B ly (fst r') + (aeval B ly (fst r) + i - aeval B ly (fst r'))) by img_lia.
img_apply V. img_lia.
Qed.
Lemma junk' : Forall (range_vis B ly rd') (ajunk B ly S').
Proof.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). pose proof (am_junk B ly S rd M) as J. pose proof (am_client B ly S rd M) as CL.
unfold ajunk in J |- *. unfold quar_junk in J |- *. rewrite all_batches_S in J. rewrite all_batches_S', E'. rewrite E in J.
unfold cache_junk, cache, sec_junk in J |- *. rewrite S'_cinit, S'_cache, S'_sec_arr, S'_sec_res, E'. rewrite E in J.
rewrite (flat_map_mid (fun k0 : chunk => match ck_beg k0 with PSec r _ => [(ASec r 32, kPage - 32)] | _ => [] end) l1 k' k l2) by img_refl.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J]. apply Forall_app in J as [J6 J]. apply Forall_app in J as [J7 J].
img_apply Forall_cons; [img_try (intros i Hi; img_apply VIS; img_exact (J1 i Hi))|].
img_apply Forall_cons; [img_try (intros i Hi; img_apply VIS; img_exact (J2 i Hi))|].
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J3))|]. img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J4))|].
img_apply Forall_app. split.
{
rewrite flat_map_app in J5 |- *. cbn [flat_map] in J5 |- *. apply Forall_app in J5 as [J5a J5]. apply Forall_app in J5 as [J5k J5b].
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J5a))|]. img_apply Forall_app. split; [|img_try (img_exact (vis_keep _ J5b))].
unfold chunk_junk in J5k |- *. rewrite k'_rz, k'_n, k'_extent. cbn [ck_state k']. rewrite Hst in J5k.
apply Forall_app in J5k as [Ja J5k]. apply Forall_app in J5k as [Jb J5k]. apply Forall_app in J5k as [_ Jd].
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ Ja))|]. img_apply Forall_app. split; [img_try (img_exact (vis_keep _ Jb))|]. img_apply Forall_app. split; [|img_try (img_exact (vis_keep _ Jd))].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (vis_sub _ (sptr_exp (ck_user k), ck_n k)).
- img_apply (proj1 (Forall_forall _ _) CL). unfold aclient. img_apply in_app_iff. left. img_apply in_flat_map. exists k. split; [img_try (img_exact Hk)|]. unfold chunk_user. rewrite Hst. left. img_refl.
- cbn [fst snd]. img_change (sptr_exp (ck_beg k')) with (sptr_exp (ck_beg k)). rewrite (EA k _ Hk). fold (sptr_addr B ly (ck_user k)). rewrite Hu. img_lia.
- cbn [fst snd]. img_change (sptr_exp (ck_beg k')) with (sptr_exp (ck_beg k)). rewrite (EA k _ Hk). fold (sptr_addr B ly (ck_user k)). rewrite Hu. img_lia. }
img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J6))|].
img_apply Forall_app. split.
{
rewrite !flat_map_app in J7 |- *. cbn [flat_map] in J7 |- *. rewrite app_nil_r in J7 |- *.
apply Forall_app in J7 as [J7a J7]. apply Forall_app in J7a as [J7i J7b].
img_apply Forall_app. split; [|img_try (img_exact (vis_keep _ J7))]. img_apply Forall_app. split; [img_try (img_exact (vis_keep _ J7i))|].
unfold batch_junk in J7b |- *. img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. apply Forall_cons_iff in J7b as [J7b _].
img_apply (vis_sub _ _ J7b); cbn -[Z.add Z.mul Z.sub Z.of_nat]; rewrite length_app; cbn [length]; unfold kBatchBytes; img_lia. }
img_exact (vis_keep _ J).
Qed.
Lemma areas' : Forall (range_vis B ly rd') (aareas S').
Proof.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). pose proof (am_areas B ly S rd M) as A.
unfold aareas, reg in A |- *. rewrite S'_regions, S'_sec_res, E'. rewrite E in A.
rewrite (flat_map_mid _ l1 k' k l2) by img_refl. img_exact (vis_keep _ A).
Qed.
Lemma client' : Forall (range_vis B ly rd') (aclient S').
Proof.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). pose proof (am_client B ly S rd M) as A.
unfold aclient in A |- *. rewrite frames', E'. rewrite E in A. rewrite flat_map_app in A |- *. cbn [flat_map] in A |- *.
unfold chunk_user at 2. cbn [ck_state k'].
img_apply vis_keep. img_apply Forall_forall. intros r Hr. img_apply (proj1 (Forall_forall _ _) A). rewrite !in_app_iff in Hr |- *. cbn [In] in Hr. tauto.
Qed.
Lemma placed' : sec_placed ly S'.
Proof. unfold sec_placed. rewrite sec_extents'. img_exact (am_placed B ly S rd M). Qed.
Theorem free_fin_ARm : ARm B ly S' rd'.
Proof.
constructor.
- img_exact WS'.
- img_exact (am_universe B ly S rd M).
- img_exact (am_syms B ly S rd M).
- img_exact LO.
- img_exact placed'.
- img_exact CONST'.
- img_exact (am_const_owned B ly S rd M).
- img_exact cells_all.
- img_exact fa'.
- img_exact flags'.
- img_exact depot'.
- img_exact shadow'.
- img_exact zshadow'.
- img_exact junk'.
- img_exact areas'.
- img_exact client'.
- img_exact (proj2 IAL).
- img_exact (am_tsd B ly S rd M).
- img_exact (am_static_img B ly S rd M).
Qed.
Lemma sec_live' : sec_live_bytes S' = sec_live_bytes S.
Proof. geo'.
pose proof SPLIT as (l1 & l2 & E & E' & _). unfold sec_live_bytes. rewrite E', E.
img_apply sec_live_bytes_begs; rewrite !map_app; img_refl.
Qed.
Lemma prim_committed' : prim_committed S' = prim_committed S.
Proof. geo'. unfold prim_committed. rewrite S'_regions. img_refl. Qed.
Lemma ALedger_S' : forall segs md, ALedger segs ly S md -> ALedger segs ly S' md.
Proof. geo'.
intros segs md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14].
constructor; try assumption.
- destruct L4 as (pieces & P1 & P2). exists pieces. split; [|img_try (img_exact P2)].
unfold prim_pieces_ok, cut_ok, prim_hole_at, reg in P1 |- *. rewrite S'_regions. img_exact P1.
- rewrite sec_extents'. img_exact L7.
- rewrite sec_extents'. img_exact L8.
- rewrite prim_committed', sec_extents', S'_sec_res. img_exact L9.
- rewrite sec_extents'. img_exact L12.
Qed.
Lemma abudget_le : abudget S <= abudget S'.
Proof. geo'.
unfold abudget, sec_hulls. rewrite sec_live', S'_secs  . replace (st_nev S') with (st_nev S + 1); [img_try (unfold EV_A; img_lia)|].
unfold S', sd, depot_after, s1. destruct (z =? 0); img_refl.
Qed.
Lemma qtight_S' : qc_bytes (st_qthread S) + nn <= kQuarantineCacheMax -> qtight S -> qtight S'.
Proof. geo'.
intros Hc (T1 & T2 & T3). pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2).
unfold qtight. rewrite qbytes', S'_qglobal. split; [img_try (img_exact Hc)|]. split; [img_try (img_exact T2)|].
unfold quar_n in *. rewrite E in T3. rewrite E', !quar_nl_split in *.
replace (is_alloc k) with true in T3 by (img_try (unfold is_alloc; rewrite Hst; img_refl)). replace (is_alloc k') with false by img_refl.
rewrite queued_n_eq in *. rewrite qlist in T3. rewrite qlist', S'_qglobal, !items_n_flat_app in *.
cbn [flat_map b_items] in *. (subst b'; cbv beta). cbn [b_items] in *. rewrite !app_nil_r, items_n_app, items_n_cons, items_n_nil in *.
rewrite k'_n. img_lia.
Qed.
Lemma own_ext_quar : forall S0 rd0 x a, ARm B ly S0 rd0 -> In x (st_chunks S0) -> ck_state x = CQuarantined ->
ck_base B ly x <= a < ck_base B ly x + ck_extent x -> aowned B ly S0 a.
Proof. geo'.
intros S0 rd0 x a M0 Hx Hq Ha. pose proof (chunk_facts B ly S0 rd0 x M0 Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (NB : forall y, In y (st_chunks S0) -> ck_state y = CAllocated ->
~ (ck_base B ly y + ck_rz y <= a < ck_base B ly y + ck_rz y + req_size (ck_req y))).
{ intros y Hy Hsy Hr. pose proof (user_in_extent B ly S0 rd0 y a M0 Hy Hr) as HE.
assert (Hne : ck_beg y <> ck_beg x).
{ intros Eq. destruct (In_split_beg _ _ Hx (wf_chunks_nodup _ _ _ _ _ (am_wf _ _ _ _ M0))) as (l1 & l2 & E & N1 & N2).
rewrite E in Hy. apply in_app_iff in Hy as [X|[<-|X]]; [img_try (img_apply N1) | img_try (rewrite Hq in Hsy; discriminate) | img_try (img_apply N2)]; rewrite <- Eq; img_apply in_map; img_exact X. }
pose proof (chunks_disjoint B ly S0 rd0 y x M0 Hy Hx Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. img_lia. }
pose proof (am_layout _ _ _ _ M0) as LO0.
destruct (ck_beg x) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) LO0 ltac:(img_lia)) as (R1 & R2 & _).
eapply own_prim_nonuser; [img_try (img_exact M0) | img_lia | img_try (img_exact NB)].
- destruct GG as (-> & _ & Gbase & Gext & Gin & Gal & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M0)) _ Gin) as (_ & [I1 I2] & _). cbn [fst snd] in I1, I2.
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M0)) Gin
ltac:(img_try (unfold static_extents, owned_extents; cbn; tauto))) as DJ.
eapply own_ext; [img_try (img_exact M0) | img_try (right; img_apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req x)); split; [img_exact Gin | unfold in_zr, kPage in *; cbn; img_lia]) | img_try (img_exact NB) |].
unfold zdisjoint, kFakeFramesOff, kPage in *. cbn [fst snd] in DJ. img_lia.
Qed.
Lemma D_owned : ARm B ly S' rd' -> forall a, 0 <= a -> D a -> aowned B ly S a \/ aowned B ly S' a \/ DS a.
Proof. drop_mem. drop_ev.
intros M' a Ha0 HD. pose proof HIGH as HI. pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof ext_rounded as (ER & NN1 & NN2 & NN3).
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2).
destruct HD as [X|[X|[X|[X|[X|[X|X]]]]]].
- left. eapply (own_core B ly S rd (T, kThreadObjSize) a M); [img_try (unfold core_extents; cbn; tauto)|]. cbn [fst snd]. unfold DT, t_qc, t_unwinding, t_stats, kThreadObjSize in *. img_lia.
-
right; left. img_apply (own_ext_quar S' rd' k' a M'); [img_try (rewrite E'; img_apply in_app_iff; right; left; img_refl) | img_refl |].
rewrite k'_base, k'_extent. unfold DK in X. rewrite Hu in X. img_lia.
- left. eapply own_batch; [img_try (img_exact M) | img_try (img_exact Hb_in) |]. unfold DB in X. pose proof BC_len. unfold kBatchSlots, kBatchBytes in *. img_lia.
- right; right. img_exact X.
- left. img_apply (own_static B ly S rd a M). rewrite (ts_owned _ TB). unfold DI in X. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB) in X.
img_apply Exists_exists. exists ((0xa6b58 + D_10c0), (0x5cc810 + D_10c0) - (0xa6b58 + D_10c0)). split; [img_try (unfold Tfx_owned_static; cbn; tauto)|]. unfold in_zr, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG in *. cbn [fst snd]. img_lia.
- left. unfold depot_footprint in X. destruct X as [X|[X|[X|X]]].
+ img_apply (own_static B ly S rd a M). rewrite (ts_owned _ TB). rewrite (ts_depot _ TB) in X.
img_apply Exists_exists. exists ((0xa6b58 + D_10c0), (0x5cc810 + D_10c0) - (0xa6b58 + D_10c0)). split; [img_try (unfold Tfx_owned_static; cbn; tauto)|]. unfold in_zr, TFX_DEPOT, d_map1 in *. cbn [fst snd]. img_lia.
+ eapply (own_core B ly S rd (ly_NB ly, kNodesBlockSize) a M); [img_try (unfold core_extents; cbn; tauto) | img_try (cbn [fst snd]; img_exact X)].
+ eapply (own_core B ly S rd (ly_SB ly, kStoreBlockSize) a M); [img_try (unfold core_extents; cbn; tauto) | img_try (cbn [fst snd]; img_exact X)].
+ img_apply (own_static B ly S rd a M). rewrite (ts_owned _ TB). rewrite (ts_store _ TB) in X.
img_apply Exists_exists. exists ((0xa6b58 + D_10c0), (0x5cc810 + D_10c0) - (0xa6b58 + D_10c0)). split; [img_try (unfold Tfx_owned_static; cbn; tauto)|]. unfold in_zr, TFX_STORE in *. cbn [fst snd]. img_lia.
-
left. pose proof u_al8 as (U8 & _ & _). apply Z.mod_divide in U8 as [a0 Hua]; [|img_lia].
unfold DH, shadow_addr in X. rewrite Hua, Z_div_mult in X by img_lia.
replace a with (shadow_addr ((a0 + (a - (SHADOW_OFF + a0))) * 8)).
2:{ unfold shadow_addr. rewrite Z_div_mult by img_lia. img_lia. }
destruct (extent_zone B ly S rd k M Hk) as [[Z1 Z2]|(m & len & Zin & Z1 & Z2)].
+ eapply own_shadow_prim; [img_try (img_exact M)|]. rewrite Hu in *. nia.
+ eapply own_shadow_sec; [img_try (img_exact M) | img_try (img_exact Zin) |]. rewrite Hu in *. unfold kPage in *. nia.
Qed.
End c0.
End w.
