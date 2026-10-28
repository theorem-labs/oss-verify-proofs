(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0l YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AF0x AFl0 AFeq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Lemma pairwise_nth {X} (R : X -> X -> Prop) : forall (l : list X) i j x y,
pairwise R l -> nth_error l i = Some x -> nth_error l j = Some y -> (i < j)%nat -> R x y.
Proof.
induction l as [|a t IH]; intros [|i] [|j] x y P Hi Hj Hij; cbn in *; try discriminate; try lia.
- injection Hi as <-. destruct P as [F _]. apply nth_error_In in Hj. exact (proj1 (Forall_forall _ _) F _ Hj).
- destruct P as [_ P]. eapply IH; eauto. lia.
Qed.
Lemma flat_map_mid {X Y} (f : X -> list Y) : forall l1 x y l2, f x = f y -> flat_map f (l1 ++ x :: l2) = flat_map f (l1 ++ y :: l2).
Proof. intros l1 x y l2 E. rewrite !flat_map_app. cbn. rewrite E. reflexivity. Qed.
Lemma fold_ckn_app : forall l1 l2, fold_right (fun k acc => ck_n k + acc) 0 (l1 ++ l2) =
fold_right (fun k acc => ck_n k + acc) 0 l1 + fold_right (fun k acc => ck_n k + acc) 0 l2.
Proof. induction l1 as [|a t IH]; intros l2; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma combine_snoc_from {X} : forall (l : list X) s x,
combine (seq s (S (length l))) (l ++ [x]) = combine (seq s (length l)) l ++ [((s + length l)%nat, x)].
Proof.
induction l as [|a t IH]; intros s x; [cbn; rewrite Nat.add_0_r; reflexivity|].
cbn [length]. rewrite <- (cons_seq (S (length t)) s), <- (cons_seq (length t) s). cbn [combine app]. rewrite IH, Nat.add_succ_r. reflexivity.
Qed.
Lemma combine_snoc {X} : forall n (l : list X) x, length l = n ->
combine (seq 0 (S n)) (l ++ [x]) = combine (seq 0 n) l ++ [(n, x)].
Proof. intros n l x <-. exact (combine_snoc_from l 0 x). Qed.
Lemma NoDup_map_In {X Y} (f : X -> Y) : forall l a b, List.NoDup (map f l) -> In a l -> In b l -> f a = f b -> a = b.
Proof.
induction l as [|x t IH]; intros a b ND Ha Hb E; [destruct Ha|]. cbn in ND. inversion ND as [|y l' N1 N2]; subst.
destruct Ha as [<-|Ha], Hb as [<-|Hb]; [reflexivity | exfalso | exfalso | exact (IH a b N2 Ha Hb E)].
- apply N1. rewrite E. apply in_map. exact Hb.
- apply N1. rewrite <- E. apply in_map. exact Ha.
Qed.
Lemma batch_cells_snoc : forall l b b', b_self b' = b_self b ->
exists P, batch_cells (l ++ [b]) = P ++ batch_cells [b] /\ batch_cells (l ++ [b']) = P ++ batch_cells [b'] /\
(forall c, In c P -> exists b2, In b2 l /\ (In c (batch_cells [b2]) \/
(exists nx, In nx (map batch_exp (l ++ [b])) /\ c = c8 (batch_exp b2) nx))).
Proof.
induction l as [|b2 t IH]; intros b b' E.
- exists []. cbn. split; [reflexivity|]. split; [reflexivity|]. intros c [].
- destruct (IH b b' E) as (P & H1 & H2 & H3). cbn [batch_cells app].
assert (HD : match t ++ [b'] with [] => ANum 0 | b'0 :: _ => batch_exp b'0 end = match t ++ [b] with [] => ANum 0 | b0 :: _ => batch_exp b0 end).
{ destruct t; cbn; [unfold batch_exp; rewrite E|]; reflexivity. }
rewrite HD.
eexists (c8 (batch_exp b2) _ :: z8 (aoff (batch_exp b2) 8) (b_bytes b2) :: z8 (aoff (batch_exp b2) 16) (Z.of_nat (length (b_items b2))) ::
map (fun iv => c8 (aoff (batch_exp b2) (24 + 8 * Z.of_nat (fst iv))) (sptr_exp (ck_hdr (snd iv)))) (combine (seq 0 (length (b_items b2))) (b_items b2)) ++ P).
split; [|split].
+ change (batch_cells (t ++ [b])) with (batch_cells (t ++ [b])). rewrite H1. cbn [app]. rewrite <- app_assoc. reflexivity.
+ rewrite H2. cbn [app]. rewrite <- app_assoc. reflexivity.
+ intros c Hc. cbn [app] in Hc. destruct Hc as [<-|[<-|[<-|Hc]]].
* exists b2. split; [left; reflexivity|]. right. eexists. split; [|reflexivity]. destruct t as [|b3 t']; cbn; [right; left; reflexivity | right; left; reflexivity].
* exists b2. split; [left; reflexivity|]. left. cbn. right. left. reflexivity.
* exists b2. split; [left; reflexivity|]. left. cbn. right. right. left. reflexivity.
* apply in_app_iff in Hc as [Hc|Hc].
-- exists b2. split; [left; reflexivity|]. left. cbn [batch_cells]. right. right. right. rewrite app_nil_r. exact Hc.
-- destruct (H3 c Hc) as (b4 & Hin4 & Hb4). exists b4. split; [right; exact Hin4|]. destruct Hb4 as [Y|(nx & X & ->)]; [left; exact Y|].
right. exists nx. split; [|reflexivity]. cbn. right. exact X.
Qed.
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma find_chunk_at_app : forall B ly l1 l2 g,
find_chunk_at B ly (l1 ++ l2) g = match find_chunk_at B ly l1 g with Some x => Some x | None => find_chunk_at B ly l2 g end.
Proof. intros B ly l1 l2 g. induction l1 as [|x t IH]; cbn; [reflexivity|]. destruct (_ && _); [reflexivity | exact IH]. Qed.
Section c0.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (rd rd' : reader).
Hypothesis M : ARm B ly S rd.
Variables (k : chunk) (hb1 : Z).
Hypothesis Hk : In k (st_chunks S).
Hypothesis Hst : ck_state k = CAllocated.
Hypothesis Hhb1 : 0 <= hb1 < 256 /\ Z.land hb1 127 = 17.
Variables (z : Z) (tr : list Z).
Let s1 : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Let sd : astate := depot_after z tr s1.
Let k' : chunk := mkChunk (ck_beg k) (ck_req k) CQuarantined.
Definition S' : astate := set_chunks (upd_chunk (st_chunks sd) k') sd.
Hypothesis Hev : aregime S.
Hypothesis AOK : aok s1 (KDepot tr) z.
Hypothesis HU : In tr (as_universe B).
Local Notation T := (ly_T ly).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp <= ly_stk_hi ly.
Hypothesis IMG : img_cover ly.
Definition DT (a : Z) : Prop := a = T + t_unwinding \/ (T + t_stats + 24 <= a < T + t_stats + 40).
Definition DK (a : Z) : Prop := (u - 16 <= a < u - 8) \/ (u <= a < u + 8).
Definition DS (a : Z) : Prop := sp - ASTACK <= a < sp.
Definition DI (a : Z) : Prop := (as_ialloc_lo B <= a < as_ialloc_hi B) \/ (as_ialloc_flag B <= a < as_ialloc_flag B + 4).
Definition DH (a : Z) : Prop := shadow_addr u <= a < shadow_addr u + (nn + 7) / 8.
Definition D (a : Z) : Prop := DT a \/ DK a \/ DS a \/ DI a \/ depot_footprint B ly a \/ DH a.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ D a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_hdr : forall i, (i < 4)%nat -> rd' (u - 16 + Z.of_nat i) = Some (YG0f.le_byte (3 + 256 * hb1) 4 i).
Hypothesis NEW_n : forall i, (i < 4)%nat -> rd' (u - 12 + Z.of_nat i) = Some (YG0f.le_byte nn 4 i).
Hypothesis NEW_unw : rd' (T + t_unwinding) = Some 0.
Hypothesis NEW_sh : forall a, DH a -> rd a <> None -> rd' a = Some shHeapFreed.
Hypothesis IAL : Forall (cell_holds B ly rd') (ialloc_cells B S') /\ Forall (range_zero B ly rd') (ialloc_zero B).
Hypothesis DEP : depot_mem_ok B ly sd rd'.
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
Ltac drop_mem := clear AG VIS NEW_hdr NEW_n NEW_unw NEW_sh IAL DEP CONST'.
Ltac drop_ev := clear Hev AOK HU.
Ltac geo := drop_mem; drop_ev.
Ltac geo' := geo.
Lemma S'_regions : st_regions S' = st_regions S.   Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); reflexivity. Qed.
Lemma S'_cache : st_cache S' = st_cache S.         Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); reflexivity. Qed.
Lemma S'_cinit : st_cache_inited S' = st_cache_inited S. Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); reflexivity. Qed.
Lemma S'_secs : st_secs S' = st_secs S.             Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); reflexivity. Qed.
Lemma S'_sec_arr : st_sec_arr S' = st_sec_arr S.    Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); reflexivity. Qed.
Lemma S'_sec_res : st_sec_reserved S' = st_sec_reserved S. Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); reflexivity. Qed.
Lemma S'_fs : st_fs S' = st_fs S.                   Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); reflexivity. Qed.
Lemma S'_qglobal : st_qglobal S' = st_qglobal S.    Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); reflexivity. Qed.
Lemma S'_qthread : st_qthread S' = st_qthread S. Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); reflexivity. Qed.
Lemma sd_chunks : st_chunks sd = st_chunks S.       Proof. geo'. unfold sd, depot_after, s1; destruct (z =? 0); reflexivity. Qed.
Lemma S'_chunks : st_chunks S' = upd_chunk (st_chunks S) k'. Proof. geo'. unfold S'. cbn [st_chunks set_chunks]. rewrite sd_chunks. reflexivity. Qed.
Lemma S'_depot : st_depot S' = st_depot sd.         Proof. geo'. reflexivity. Qed.
Lemma S'_inited : st_internal_inited S' = true.     Proof. geo'. unfold S', sd, depot_after, s1; destruct (z =? 0); reflexivity. Qed.
Lemma reg' : forall c, reg S' c = reg S c.          Proof. geo'. intros c. unfold reg. rewrite S'_regions. reflexivity. Qed.
Lemma cache' : forall c, cache S' c = cache S c.    Proof. geo'. intros c. unfold cache. rewrite S'_cache. reflexivity. Qed.
Lemma frames' : frames S' = frames S.               Proof. geo'. unfold frames. rewrite S'_fs. reflexivity. Qed.
Let WF : Wf (as_universe B) S := am_wf B ly S rd M.
Let LO : layout_ok ly := am_layout B ly S rd M.
Lemma KF : cfacts B ly S k. Proof. geo'. exact (chunk_facts B ly S rd k M Hk). Qed.
Lemma Hu : u = ck_base B ly k + ck_rz k. Proof. geo'. pose proof KF as (_ & _ & _ & G4 & _). exact G4. Qed.
Lemma k'_base : ck_base B ly k' = ck_base B ly k. Proof. geo'. reflexivity. Qed.
Lemma k'_extent : ck_extent k' = ck_extent k. Proof. geo'. reflexivity. Qed.
Lemma k'_rz : ck_rz k' = ck_rz k. Proof. geo'. reflexivity. Qed.
Lemma k'_n : ck_n k' = ck_n k. Proof. geo'. reflexivity. Qed.
Lemma ext_rounded : ck_rz k + (nn + 7) / 8 * 8 <= ck_extent k /\ 1 <= nn /\ 0 <= (nn + 7) / 8 /\ nn <= (nn + 7) / 8 * 8 < nn + 8.
Proof. geo'.
pose proof KF as (_ & _ & _ & _ & G5 & _ & G7 & G8 & GG). unfold ck_n.
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
pose proof (rounded_size_bounds (ck_req k) ltac:(lia)) as [R1 R2].
assert (DV : (req_size (ck_req k) + 7) / 8 * 8 <= rounded_size (ck_req k) /\ req_size (ck_req k) <= (req_size (ck_req k) + 7) / 8 * 8 < req_size (ck_req k) + 8).
{ pose proof (Z.div_mod (req_size (ck_req k) + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (req_size (ck_req k) + 7) 8 ltac:(lia)).
apply Z.mod_divide in R2 as [q Hq]; [|lia]. nia. }
assert (RZX : ck_rz k + rounded_size (ck_req k) <= ck_extent k).
{ unfold ck_extent, ck_rz. destruct (from_primary (ck_req k)) eqn:P.
- pose proof (primary_geometry (ck_req k) ltac:(lia) P) as (_ & [_ P2] & _). unfold needed_size in P2. rewrite P in P2. unfold needed_primary in P2. lia.
- pose proof (secondary_geometry (ck_req k) ltac:(lia) P) as (_ & S2 & _ & [S4 _] & _). unfold needed_primary in S2.
pose proof (rz_size_bounds (ck_req k)). lia. }
pose proof (Z.div_pos (req_size (ck_req k) + 7) 8). lia.
Qed.
Lemma u_al8 : u mod 8 = 0 /\ ck_base B ly k mod 8 = 0 /\ ck_rz k mod 8 = 0.
Proof. geo'.
pose proof KF as (_ & _ & G3 & G4 & _ & G6 & _). rewrite Hu.
apply Z.mod_divide in G3 as [q Hq]; [|lia]. apply Z.mod_divide in G6 as [q' Hq']; [|lia]. rewrite Hq, Hq'.
splits; apply Z.mod_divide; try lia; [exists (2 * q + 2 * q') | exists (2 * q) | exists (2 * q')]; lia.
Qed.
Lemma SPLIT : exists l1 l2, st_chunks S = l1 ++ k :: l2 /\ st_chunks S' = l1 ++ k' :: l2 /\
~ In (ck_beg k) (map ck_beg l1) /\ ~ In (ck_beg k) (map ck_beg l2).
Proof. geo'.
destruct (In_split_beg _ _ Hk (wf_chunks_nodup _ _ _ _ _ WF)) as (l1 & l2 & E & N1 & N2).
exists l1, l2. splits; try assumption. rewrite S'_chunks, E. apply upd_chunk_present; [reflexivity | exact N1].
Qed.
Lemma all_batches_S' : all_batches S' = all_batches S.
Proof. geo'. unfold all_batches. rewrite S'_qthread, S'_qglobal. reflexivity. Qed.
Lemma q_items_S' : q_items S' = q_items S.
Proof. geo'. unfold q_items. rewrite all_batches_S'. reflexivity. Qed.
Lemma sd_wf : WfP (as_universe B) 1 1 1 sd.
Proof. drop_mem.
pose proof (WfP_set_internal_inited _ 1 1 1 _ true (WfP_tick _ S WF Hev)) as W2. change (WfP (as_universe B) 1 1 1 s1) in W2.
unfold sd, depot_after. destruct (z =? 0) eqn:Ez; [exact W2|]. apply Z.eqb_neq in Ez.
destruct AOK as [Z0|[_ MT]]; [lia|]. apply mem_trace_false in MT.
pose proof (wf_depot _ _ _ _ _ W2) as [ND INC].
apply (WfP_set_depot _ 1 1 1 s1 _ W2).
- apply NoDup_app_iff. splits; [exact ND | constructor; [intros [] | constructor] |]. intros x Hx [<-|[]]. exact (MT Hx).
- intros x Hx. apply in_app_iff in Hx as [Hx|[<-|[]]]; [exact (INC x Hx) | exact HU].
Qed.
Lemma WS' : Wf (as_universe B) S'.
Proof. drop_mem.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). pose proof sd_wf as W3.
assert (Esd : st_chunks sd = l1 ++ k :: l2) by (rewrite sd_chunks; exact E).
pose proof (WfP_flip _ 1 1 1 sd l1 k l2 W3 Esd Hst) as W4. change (quar_of k) with k' in W4.
unfold S'. change (upd_chunk (st_chunks sd) k' = l1 ++ k' :: l2) in E'. rewrite E'.
apply (WfP_weaken _ 1 1 1); try lia. exact W4.
Qed.
Lemma batch_geom : forall b2, In b2 (all_batches S) ->
exists x, ly_space ly + b_self b2 = region_base ly kBatchClass + x /\ 0 <= x /\ x mod kBatchBytes = 0 /\
x + kBatchBytes <= rg_alloc_user (reg S kBatchClass) /\ rg_alloc_user (reg S kBatchClass) <= rg_mapped_user (reg S kBatchClass) <= 2 ^ 31 /\
In x (batch_offs S kBatchClass).
Proof. geo'.
intros b2 Hb2. pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b2 - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b2; auto).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA. unfold kUserMapSize, EV_MAX in MB. unfold kBatchBytes.
assert (XB : x + 8192 <= rg_alloc_user (reg S kBatchClass)).
{ apply Z.mod_divide in X2 as [q Hq]; [|lia]. apply Z.mod_divide in AA as [q' Hq']; [|lia]. assert (q < q') by nia. nia. }
exists x. splits; try assumption; try lia. unfold region_base. subst x. lia.
Qed.
Lemma batches_nodup : List.NoDup (map b_self (all_batches S)).
Proof. geo'.
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & ND & _).
rewrite batch_offs_24 in ND.
clear - ND. induction (all_batches S) as [|x t IH]; cbn in *; [constructor|].
inversion ND as [|y l N1 N2]; subst. constructor; [|exact (IH N2)].
intros Hin. apply N1. apply in_map_iff in Hin as (x' & E & Hx'). apply in_map_iff. exists x'. split; [lia | exact Hx'].
Qed.
Lemma batches_apart : forall b1 b2, In b1 (all_batches S) -> In b2 (all_batches S) -> b_self b1 <> b_self b2 ->
zdisjoint (ly_space ly + b_self b1, kBatchBytes) (ly_space ly + b_self b2, kBatchBytes).
Proof. geo'.
intros b1 b2 H1 H2 NE. destruct (batch_geom b1 H1) as (x1 & E1 & P1 & A1 & _). destruct (batch_geom b2 H2) as (x2 & E2 & P2 & A2 & _).
unfold zdisjoint, kBatchBytes in *. cbn [fst snd]. rewrite E1, E2.
apply Z.mod_divide in A1 as [q1 Hq1]; [|lia]. apply Z.mod_divide in A2 as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros ->; apply NE; lia). nia.
Qed.
Lemma batch_vs_chunk : forall b2 x, In b2 (all_batches S) -> In x (st_chunks S) ->
zdisjoint (ly_space ly + b_self b2, kBatchBytes) (ck_base B ly x, ck_extent x).
Proof. geo'.
intros b2 x Hb2 Hx. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & INB).
pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wr_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _). apply NoDup_app_iff in ND as (_ & _ & NDx).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (ck_beg x) as [|o|r o|c p] eqn:Ebx; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
+ pose proof (In_chunk_offs S x o Hx Ebx) as IK. rewrite Ec in *. set (xk := o - region_off kBatchClass) in *.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in *.
assert (xk <> xb). { intros E. apply (NDx xk); [exact IK | rewrite E; exact INB]. }
unfold kBatchBytes in *. apply Z.mod_divide in Gxm as [q1 Hq1]; [|lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|lia].
assert (q1 <> q2) by (intros E; subst; lia). nia.
+ pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1' & R2' & _).
unfold region_base, kBatchBytes in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass in *.
destruct (Z.lt_ge_cases (prim_class o) 24).
* pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
* pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
unfold zdisjoint, kPage, kBatchBytes in *. cbn [fst snd] in DJ. unfold region_base in *. lia.
Qed.
Lemma SX : forall i j x y, nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x y.
Proof. geo'.
intros i j x y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- exact (pairwise_nth zdisjoint _ i j x y (lo_disj _ LO) Hi Hj H).
- apply zdisjoint_sym. apply (pairwise_nth zdisjoint _ j i y x (lo_disj _ LO) Hj Hi). lia.
Qed.
Lemma SECX : forall e j y, In e (sec_extents ly S) -> nth_error (static_extents ly) j = Some y -> zdisjoint e y.
Proof. geo'.
intros e j y He Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly S) (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M)) He).
eapply nth_error_In. exact Hj.
Qed.
Lemma ext_zone : forall y, In y (st_chunks S) ->
(exists c, 1 <= c <= 30 /\ region_base ly c <= ck_base B ly y /\ ck_base B ly y + ck_extent y <= region_base ly c + 2 ^ 31 /\
ly_prim ly <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ly_prim ly + kPrimResvSize) \/
(exists r, ck_beg y = PSec r kPage /\ ck_base B ly y = ly_sec ly r + kPage /\ In (ly_sec ly r, ck_extent y + kPage) (sec_extents ly S)).
Proof. geo'.
intros y Hy. pose proof (chunk_facts B ly S rd y M Hy) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal & Gm).
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _). exists (prim_class o). splits; lia.
- right. destruct GG as (-> & _ & Gbase & Gext & Gin & _). exists r. splits; [reflexivity | lia |].
replace (ck_extent y + kPage) with (sec_map_size (ck_req y)) by lia. exact Gin.
Qed.
Lemma anyX : forall y j e, In y (st_chunks S) -> nth_error (static_extents ly) j = Some e -> (j <> 0)%nat -> zdisjoint (ck_base B ly y, ck_extent y) e.
Proof. geo'.
intros y j e Hy Hj Hne. destruct (ext_zone y Hy) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- pose proof (SX 0 j _ e eq_refl Hj ltac:(lia)) as DJ. unfold zdisjoint in DJ |- *. cbn [fst snd] in DJ |- *. lia.
- pose proof (SECX _ j e Xin Hj) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. lia.
Qed.
Lemma KX : forall j y, nth_error (static_extents ly) j = Some y -> (j <> 0)%nat -> zdisjoint (ck_base B ly k, ck_extent k) y.
Proof. geo'. intros j y Hj Hne. exact (anyX k j y Hk Hj Hne). Qed.
Lemma secmap_vs_chunk : forall x y r o, In x (st_chunks S) -> In y (st_chunks S) -> ck_beg x = PSec r o -> ck_beg x <> ck_beg y ->
zdisjoint (ly_sec ly r, sec_map_size (ck_req x)) (ck_base B ly y, ck_extent y).
Proof. geo'.
intros x y r o Hx Hy Ebx Hne.
pose proof (chunk_facts B ly S rd x M Hx) as (_ & _ & _ & _ & _ & _ & _ & _ & GG). rewrite Ebx in GG. destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (chunk_facts B ly S rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GK).
destruct (ck_beg y) as [|o'|r' o'|c' p'] eqn:Eby; try solve [destruct GK].
- apply zdisjoint_sym. exact (prim_vs_secmap B ly S rd y o' _ M Hy Eby Gin).
- destruct GK as (-> & _ & Kbase & Kext & Kin & _).
pose proof (secmaps_disjoint B ly S rd x y r kPage r' kPage M Hx Hy Ebx Eby ltac:(rewrite Eby; exact Hne)) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. lia.
Qed.
Lemma zdisjoint_of_pointwise : forall a s (e : Z * Z), 0 < s -> 0 < snd e -> (forall x, a <= x < a + s -> ~ in_zr x e) -> zdisjoint (a, s) e.
Proof. clear_all. intros a s [c t] Hs Ht H. unfold zdisjoint. unfold in_zr in H. cbn [fst snd] in *.
destruct (Z_lt_le_dec (Z.max a c) (a + s)); [|lia]. destruct (Z_lt_le_dec (Z.max a c) (c + t)); [|lia].
exfalso. apply (H (Z.max a c)); lia.
Qed.
Lemma ZCH : forall x, In x (st_chunks S) -> zone3 (ck_base B ly x) (ck_extent x).
Proof. geo'.
intros x Hx. pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req x) ltac:(clear - G7; lia)) as (_ & Q1 & _).
apply (zone3_intro ly (ck_base B ly x) (ck_extent x) IMG ltac:(clear - G5 G8 Q1; lia) G1).
apply zdisjoint_of_pointwise; [clear - G5 G8 Q1; lia | exact (proj1 (proj2 (lo_img _ LO))) |].
intros y Hy. exact (proj1 (chunk_apart B ly S rd x y M Hx Hy)).
Qed.
Lemma HIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) (kPtrArrayResv) /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) (kFakeStackSize) /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) (kNodesBlockSize) /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) (kStoreBlockSize) /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) (256) /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
zone3 (ck_base B ly k) (ck_extent k) /\ ck_base B ly k + ck_extent k <= ASAN_CEIL /\ 16 <= ck_rz k /\ ly_stk_lo ly mod 4096 = 0.
Proof. geo'.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD.
assert (Z3 : forall i x sz, nth_error (owned_extents ly) i = Some (x, sz) -> 0 <= sz -> zone3 x sz).
{ intros i x sz He Hsz. apply (zone3_intro ly x sz IMG Hsz (Forall_nth_f _ _ i _ HA He)).
assert (L : (i < 8)%nat) by (destruct (Nat.lt_ge_cases i 8) as [X|X]; [exact X|]; assert (X' : nth_error (owned_extents ly) i = None) by (apply nth_error_None; cbn; lia); rewrite X' in He; discriminate).
exact (pairwise_ij_f _ _ i (8 - i) _ _ HD ltac:(unfold static_extents; rewrite nth_error_app1 by (cbn; lia); exact He)
ltac:(unfold static_extents; rewrite nth_error_app2 by (cbn; lia); replace (i + Datatypes.S (8 - i) - length (owned_extents ly))%nat with 1%nat by (cbn; lia); reflexivity)). }
pose proof (Z3 1%nat _ _ eq_refl ltac:(unfold kPtrArrayResv; lia)) as ZQ. pose proof (Z3 2%nat _ _ eq_refl ltac:(unfold kThreadObjSize; lia)) as ZT.
pose proof (Z3 3%nat _ _ eq_refl ltac:(unfold kFakeStackSize; lia)) as ZF. pose proof (Z3 4%nat _ _ eq_refl ltac:(unfold kNodesBlockSize; lia)) as ZNB.
pose proof (Z3 5%nat _ _ eq_refl ltac:(unfold kStoreBlockSize; lia)) as ZSB. pose proof (Z3 6%nat _ _ eq_refl ltac:(lia)) as ZC. clear Z3 HA HD.
pose proof ZQ as (ZQ1 & ZQ2 & _). pose proof ZT as (ZT1 & ZT2 & _). pose proof ZF as (ZF1 & ZF2 & _). pose proof ZNB as (ZNB1 & ZNB2 & _). pose proof ZSB as (ZSB1 & ZSB2 & _). pose proof ZC as (ZC1 & ZC2 & _).
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
pose proof KF as (G1 & G2 & _ & _ & G5 & _).
pose proof ext_rounded as (ER & NN1 & NN2 & NN3).
pose proof (ZCH k Hk) as ZK.
unfold page_aligned in *.
split; [lia|]. split; [lia|]. split; [exact ZQ|]. split; [clear - ZQ; unfold zone3 in ZQ; lia|].
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|]. split; [exact ZF|]. split; [clear - ZF; unfold zone3 in ZF; lia|].
split; [exact ZNB|]. split; [clear - ZNB; unfold zone3 in ZNB; lia|]. split; [exact ZSB|]. split; [clear - ZSB; unfold zone3 in ZSB; lia|].
split; [exact ZC|]. split; [clear - ZC; unfold zone3 in ZC; lia|].
clear ZQ ZT ZF ZNB ZSB ZC. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact ZK|]. split; [lia|]. split; [lia|].
clear ZK. first [assumption | lia].
Qed.
Lemma LOWD : forall a, DI a \/ (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) -> TFIB_IMG_LO <= a < TFIB_IMG_END.
Proof. geo'.
intros a Ha. unfold DI in Ha. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB), (ts_depot _ TB), (ts_store _ TB) in Ha.
unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_DEPOT, TFIB_STORE, d_map1, TFIB_IMG_LO, TFIB_IMG_END in *. lia.
Qed.
Lemma D_cases : forall a, D a ->
(T <= a < T + kThreadObjSize /\ DT a) \/ (ck_base B ly k <= a < ck_base B ly k + ck_extent k /\ DK a) \/
(0 = 1 /\ 0 = 1) \/ (ly_stk_lo ly <= a < ly_stk_hi ly) \/ (TFIB_IMG_LO <= a < TFIB_IMG_END) \/
(ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) \/
(kLowShadowBeg <= a < kHighMemBeg /\ DH a).
Proof. geo.
intros a Ha. pose proof HIGH as HI. pose proof ext_rounded as (ER & NN1 & NN2 & NN3).
destruct Ha as [X|[X|[X|[X|[X|X]]]]].
- left. split; [|exact X]. unfold DT, t_qc, t_unwinding, t_stats, kThreadObjSize in *. lia.
- right; left. split; [|exact X]. unfold DK in X. rewrite Hu in X. lia.
- do 3 right; left. unfold DS, ASTACK in *. lia.
- do 4 right; left. apply LOWD. left. exact X.
- unfold depot_footprint in X. destruct X as [X|[X|[X|X]]]; [do 4 right; left; apply LOWD; tauto | tauto | tauto | do 4 right; left; apply LOWD; tauto].
- do 7 right. split; [|exact X]. unfold DH in X. rewrite Hu in X.
destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZK & K2 & RZ16 & _). clear - X ZK K2 RZ16 ER NN1 NN2 NN3.
ceil; unfold zone3, shadow_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
split.
+ pose proof (Z.div_pos (ck_base B ly k + ck_rz k) 8 ltac:(lia) ltac:(lia)). lia.
+ assert (LE : ck_base B ly k + ck_rz k + (nn + 7) / 8 * 8 <= 140737479966720) by lia.
assert (Y : (ck_base B ly k + ck_rz k + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; [lia | exact LE]).
rewrite Z.div_add in Y by lia. change (140737479966720 / 8) with 17592184995840 in Y. lia.
Qed.
Ltac zget HI x sz Z := assert (Z : zone3cases x sz) by (clear - HI; unfold zone3 in HI; tauto); unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in Z.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ D a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.
Lemma AGok : forall a, ok a -> rd' a = rd a. Proof. intros a [H1 H2]. apply AG; assumption. Qed.
Ltac zd H := let X := fresh "ZD" in pose proof H as X; unfold zdisjoint in X; cbn [fst snd] in X; unfold kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize in X; lia.
Lemma ok_Q : okr (ly_Q ly) kPtrArrayResv.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_Q ly) kPtrArrayResv ZZ. ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [lia|]. intros HD.
apply D_cases in HD as [[X _]|[[X _]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try lia.
- zd (SX 1 2 _ _ eq_refl eq_refl ltac:(lia)).
- zd (KX 1 _ eq_refl ltac:(lia)).
- zd (SX 1 8 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 1 4 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 1 5 _ _ eq_refl eq_refl ltac:(lia)).
Qed.
Lemma ok_F : okr (ly_F ly) kFakeStackSize.
Proof. geo'.
intros a Ha. pose proof HIGH as HI. zget HI (ly_F ly) kFakeStackSize ZZ. ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [lia|]. intros HD.
apply D_cases in HD as [[X _]|[[X _]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try lia.
- zd (SX 3 2 _ _ eq_refl eq_refl ltac:(lia)).
- zd (KX 3 _ eq_refl ltac:(lia)).
- zd (SX 3 8 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 3 4 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 3 5 _ _ eq_refl eq_refl ltac:(lia)).
Qed.
Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ DT a -> ok a.
Proof. geo'.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZZ. ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X _]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try lia.
- exact (ND Y).
- zd (KX 2 _ eq_refl ltac:(lia)).
- zd (SX 2 8 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 2 4 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 2 5 _ _ eq_refl eq_refl ltac:(lia)).
Qed.
Lemma ok_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) -> ok a.
Proof. geo'.
intros a Ha NK. pose proof HIGH as HI. ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X _]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try lia.
- zd (SX 0 2 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 0 8 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 0 4 _ _ eq_refl eq_refl ltac:(lia)).
- zd (SX 0 5 _ _ eq_refl eq_refl ltac:(lia)).
Qed.
Lemma ok_k : forall a, ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ DK a -> ok a.
Proof. geo'.
intros a Ha ND. pose proof HIGH as HI. zget HI (ck_base B ly k) (ck_extent k) ZZ. ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X Y]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try lia.
- zd (KX 2 _ eq_refl ltac:(lia)).
- exact (ND Y).
- zd (KX 8 _ eq_refl ltac:(lia)).
- zd (KX 4 _ eq_refl ltac:(lia)).
- zd (KX 5 _ eq_refl ltac:(lia)).
Qed.
Lemma ok_other : forall x a, In x (st_chunks S) -> ck_beg x <> ck_beg k -> ck_base B ly x <= a < ck_base B ly x + ck_extent x -> ok a.
Proof. geo'.
intros x a Hx Hne Ha. pose proof (chunks_disjoint B ly S rd x k M Hx Hk Hne) as DJ.
pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg x) as [|o|r o|c p] eqn:Ebx; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1 & R2 & _).
apply ok_prim; [lia | zd DJ].
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (ZCH x Hx) as ZX. pose proof ZX as (_ & _ & ZZ). unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in ZZ.
pose proof HIGH as HI. ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd, kPage in *. split; [lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X Y]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try lia.
+ zd (SECX _ 2 _ Gin eq_refl).
+ zd DJ.
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
pose proof (req_size_bounds (ck_req x) ltac:(lia)) as (_ & Q2 & _).
pose proof (zone3_intro ly (ly_sec ly r) (sec_map_size (ck_req x)) IMG ltac:(clear - Gext G5 G8 Q2; unfold kPage in *; lia) IA (SECX _ 9 _ Gin eq_refl)) as (_ & _ & ZZ).
cbn [fst snd] in ZZ, IA. destruct IA as [I1 I2]. unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg in ZZ.
ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd, kPage in *. split; [lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X Y]|[[X _]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try lia.
- zd (SECX _ 2 _ Gin eq_refl).
-
destruct (sptr_eqb (ck_beg k) (PSec r 4096)) eqn:E.
+ apply sptr_eqb_spec in E. pose proof KF as (_ & _ & _ & _ & _ & _ & _ & _ & GK). rewrite E in GK. destruct GK as (_ & _ & Kbase & _). unfold kPage in Kbase. lia.
+ assert (Hne : ck_beg x <> ck_beg k) by (rewrite Ebx; intros E'; rewrite <- E', sptr_eqb_refl in E; discriminate).
zd (secmap_vs_chunk x k r _ Hx Hk Ebx Hne).
- zd (SECX _ 8 _ Gin eq_refl).
- zd (SECX _ 4 _ Gin eq_refl).
- zd (SECX _ 5 _ Gin eq_refl).
Qed.
Lemma ok_batch_other : forall b2 a, In b2 (all_batches S) ->
ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes -> ok a.
Proof. geo'.
intros b2 a Hb2 Ha. destruct (batch_geom b2 Hb2) as (xb & Eb & Pb & Ab & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
apply ok_prim; [unfold kBatchBytes in *; lia | zd (batch_vs_chunk b2 k Hb2 Hk)].
Qed.
Lemma ok_rinfo : okr (ly_rinfo ly) 4096.
Proof. geo'.
intros a Ha. unfold ly_rinfo, kRegionInfoOff in Ha. pose proof HIGH as HI. unfold kSpaceSize in HI.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
apply ok_prim; [lia |].
destruct (ext_zone k Hk) as [(c & Hc & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
- unfold region_base in *. rewrite !region_off_eq in * by lia.
pose proof (Z.mul_le_mono_nonneg_r (c + 1) 32 (2 ^ 32) ltac:(lia) ltac:(lia)). change (32 * 2 ^ 32) with (2 ^ 37) in H. lia.
- pose proof (SECX _ 0 _ Xin eq_refl) as DJ. unfold zdisjoint, kPage, kPrimResvSize in *. cbn [fst snd] in DJ. lia.
Qed.
Lemma ok_fa : forall c, 1 <= c <= 31 -> okr (fa_base ly c) kFreeArrayMax.
Proof. geo'.
intros c Hc a Ha. pose proof HIGH as HI. pose proof (region_in_prim ly c LO Hc) as (R1 & R2 & R3 & R4 & R5). unfold fa_base, kFreeArrayOffset, kFreeArrayMax in *.
assert (E32 : region_base ly c = ly_space ly + region_off c) by reflexivity.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
apply ok_prim; [lia |].
destruct (ext_zone k Hk) as [(c' & Hc' & X1 & X2 & X3 & X4)|(r & Ebk & Xb & Xin)].
+ destruct (Z.eq_dec c' c) as [Ec|Hne].
* rewrite Ec in *. unfold region_base in *. lia.
* unfold region_base in *. rewrite !region_off_eq in * by lia.
destruct (Z.lt_ge_cases c' c).
-- pose proof (Z.mul_le_mono_nonneg_r (c' + 1) c (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
-- pose proof (Z.mul_le_mono_nonneg_r (c + 1) c' (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
+ pose proof (SECX _ 0 _ Xin eq_refl) as DJ. unfold zdisjoint, kPage in *. cbn [fst snd] in DJ. lia.
Qed.
Lemma ok_low : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ~ DI a -> ~ (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) -> ~ (as_store B <= a < as_store B + 64) -> ok a.
Proof. geo'.
intros a Ha N1 N2 N3. pose proof HIGH as HI. zget HI (ly_T ly) kThreadObjSize ZT. zget HI (ck_base B ly k) (ck_extent k) ZK. zget HI (ly_NB ly) kNodesBlockSize ZNB. zget HI (ly_SB ly) kStoreBlockSize ZSB. ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [lia|]. intros HD.
pose proof HD as HD0. apply D_cases in HD as [[X Y]|[[X Y]|[[X Y]|[X|[X|[X|[X|[X _]]]]]]]]; ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try lia.
destruct HD0 as [Y|[Y|[Y|[Y|[Y|Y]]]]].
- unfold DT, t_qc, t_unwinding, t_stats in Y. lia.
- unfold DK in Y. rewrite Hu in Y. pose proof ext_rounded as (ER & NN1 & NN2 & NN3). lia.
- unfold DS, ASTACK in *. lia.
- exact (N1 Y).
- unfold depot_footprint in Y. destruct Y as [Y|[Y|[Y|Y]]]; [exact (N2 Y) | lia | lia | exact (N3 Y)].
- unfold DH, shadow_addr, SHADOW_OFF in Y. rewrite Hu in Y.
pose proof (Z.div_pos (ck_base B ly k + ck_rz k) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma ok_inst : okr (as_inst B) 3632.
Proof. geo'.
intros a Ha. rewrite (ts_inst _ TB) in Ha. apply ok_low; unfold DI; rewrite ?(ts_ial_lo _ TB), ?(ts_ial_hi _ TB), ?(ts_ial_flag _ TB), ?(ts_depot _ TB), ?(ts_store _ TB);
unfold TFIB_INST, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_DEPOT, TFIB_STORE, d_map1, TFIB_IMG_LO, TFIB_IMG_END in *; lia.
Qed.
Lemma ok_hshadow : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ DH a -> ok a.
Proof. geo'.
intros a Ha ND. pose proof HIGH as HI. zget HI (ly_Q ly) kPtrArrayResv ZQ. zget HI (ly_T ly) kThreadObjSize ZT. zget HI (ly_F ly) kFakeStackSize ZF.
zget HI (ck_base B ly k) (ck_extent k) ZK. zget HI (ly_NB ly) kNodesBlockSize ZNB. zget HI (ly_SB ly) kStoreBlockSize ZSB. zget HI (ly_C ly) 256 ZC. ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *. split; [lia|]. intros HD.
apply D_cases in HD as [[X Y]|[[X Y]|[[X Y]|[X|[X|[X|[X|[X Y]]]]]]]]; ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kFakeStackSize, kHighMemBeg, ASAN_CEIL, kImgEnd, kHighShadowBeg, kHighMemEnd in *; try lia. exact (ND Y).
Qed.
Definition cell_in (lo len : Z) (c : acell) : Prop :=
lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len.
Lemma cell_xfer : forall c, cell_holds B ly rd c ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> ok (aeval B ly (c_at c) + j)) -> cell_holds B ly rd' c.
Proof. intros c Hc Hok. eapply (cell_holds_agree B ly rd rd' c Hc). intros j Hj. apply AGok, Hok, Hj. Qed.
Lemma cells_xfer : forall L lo len, okr lo len -> Forall (cell_in lo len) L -> Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd') L.
Proof.
intros L lo len OK IN OLD. apply Forall_forall. intros c Hc. apply cell_xfer; [exact (proj1 (Forall_forall _ _) OLD c Hc)|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN c Hc) as [H1 H2]. apply OK. lia.
Qed.
Lemma OLD : forall c, In c (acells B ly S) -> cell_holds B ly rd c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (am_cells B ly S rd M) c Hc). Qed.
Ltac old_in := apply Forall_forall; intros ? HIN; apply OLD; unfold acells; rewrite !in_app_iff.
Lemma EA : forall y d, In y (st_chunks S) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. geo'.
intros y d Hy. pose proof (chunk_facts B ly S rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA2 : forall y d d', In y (st_chunks S) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. geo'.
intros y d d' Hy. pose proof (chunk_facts B ly S rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia.
Qed.
Lemma EA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. geo'. reflexivity. Qed.
Lemma hdr_addr : forall y, In y (st_chunks S) -> aeval B ly (sptr_exp (ck_hdr y)) = ck_base B ly y + ck_rz y - kChunkHeaderSize.
Proof. geo'.
intros y Hy. pose proof (chunk_facts B ly S rd y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
unfold ck_hdr, ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia.
Qed.
Lemma hdr_bytes : YG0f.le_byte (3 + 256 * hb1) 4 0 = 3 /\ YG0f.le_byte (3 + 256 * hb1) 4 1 = hb1 /\
YG0f.le_byte (3 + 256 * hb1) 4 2 = 0 /\ YG0f.le_byte (3 + 256 * hb1) 4 3 = 0.
Proof. geo.
destruct Hhb1 as [R _]. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
rewrite (Z.mod_small _ 4294967296) by lia.
change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 0) with 1. change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216.
rewrite Z.div_1_r. splits.
- rewrite (Z.mul_comm 256 hb1), Z_mod_plus_full. reflexivity.
- rewrite Z.add_comm, (Z.mul_comm 256 hb1), Z_div_plus_full_l by lia. change (3 / 256) with 0. rewrite Z.add_0_r. apply Z.mod_small. lia.
- rewrite Z.div_small by lia. reflexivity.
- rewrite Z.div_small by lia. reflexivity.
Qed.
Ltac fcons := apply Forall_cons; [split; cbn; lia|].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S') (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold region_cells. rewrite reg'.
apply (cells_xfer _ _ _ ok_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fcons. apply Forall_nil.
- old_in. left. apply in_flat_map. exists c. split; [apply In_zseq; lia | exact HIN].
Qed.
Lemma okr_cache : okr (T + t_cache + 80) (80 * 31).
Proof. geo'. intros a Ha. apply ok_T; unfold DT, t_cache, t_qc, t_unwinding, t_stats, kThreadObjSize in *; lia. Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S') (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold cache_cells. rewrite cache', S'_cinit.
apply (cells_xfer _ _ _ okr_cache).
- pose proof (wf_classes _ _ _ _ _ WF c ltac:(lia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _).
unfold cell_in, t_cache. destruct (st_cache_inited S).
+ destruct WC as [PM PL]. repeat fcons. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
+ repeat fcons. apply Forall_nil.
- old_in. right; left. apply in_flat_map. exists c. split; [apply In_zseq; lia |]. unfold cache_cells. exact HIN.
Qed.
Lemma cells_chunk_other : forall x, In x (st_chunks S) -> ck_beg x <> ck_beg k -> Forall (cell_holds B ly rd') (chunk_cells x).
Proof.
intros x Hx Hne. pose proof (chunk_facts B ly S rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
apply (cells_xfer _ (ck_base B ly x) (ck_extent x)); [intros a Ha; exact (ok_other x a Hx Hne Ha) | |].
- pose proof (req_size_bounds (ck_req x) ltac:(lia)) as (_ & Q2 & _).
unfold chunk_cells, kChunkHeaderSize, cell_in. apply Forall_app. split.
+ repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(EA2 x), ?(EA x), ?EA0 by exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz x) 16); [apply Forall_nil|].
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?(EA2 x), ?(EA x), ?EA0 by exact Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
- old_in. do 2 right; left. apply in_flat_map. exists x. split; [exact Hx | exact HIN].
Qed.
Lemma cells_chunk_k : Forall (cell_holds B ly rd') (chunk_cells k').
Proof.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof hdr_bytes as (HB0 & HB1 & HB2 & HB3). destruct Hhb1 as [_ HM].
assert (Hk' : forall d, aeval B ly (aoff (sptr_exp (ck_beg k')) d) = ck_base B ly k + d) by (intros d; exact (EA k d Hk)).
assert (Hk'2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k')) d) d') = ck_base B ly k + d + d') by (intros d d'; exact (EA2 k d d' Hk)).
unfold chunk_cells. rewrite k'_rz, k'_n. unfold kChunkHeaderSize. apply Forall_app. split.
- assert (EU : ck_base B ly k + (ck_rz k - 16) = u - 16) by (rewrite Hu; lia).
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1]. rewrite Hk', EU. change (aeval B ly (ANum (hdr_state k'))) with 3.
intros kk Hkk. rewrite NEW_hdr by lia. destruct kk; [|lia]. rewrite HB0. reflexivity. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w]. rewrite Hk'2, EU. exists hb1. split; [|exact HM].
change (u - 16 + 1) with (u - 16 + Z.of_nat 1). rewrite (NEW_hdr 1%nat) by lia. rewrite HB1. reflexivity. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z2 c2]. rewrite Hk'2, EU. change (aeval B ly (ANum 0)) with 0. intros kk Hkk.
replace (u - 16 + 2 + Z.of_nat kk) with (u - 16 + Z.of_nat (2 + kk)) by lia. rewrite NEW_hdr by lia.
destruct kk as [|[|]]; cbn [Nat.add]; [rewrite HB2; reflexivity | rewrite HB3; reflexivity | lia]. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z4 c4]. rewrite Hk'2, EU. change (aeval B ly (ANum nn)) with nn. intros kk Hkk.
replace (u - 16 + 4 + Z.of_nat kk) with (u - 12 + Z.of_nat kk) by lia. rewrite NEW_n by lia. reflexivity. }
apply Forall_nil.
- destruct (Z.eqb_spec (ck_rz k) 16) as [E16|N16]; [apply Forall_nil|].
assert (32 <= ck_rz k). { pose proof G6 as G6'. apply Z.mod_divide in G6' as [q Hq]; [|lia]. lia. }
assert (OKM : okr (ck_base B ly k) 16).
{ pose proof ext_rounded as (ER & NN1 & NN2 & NN3). intros a Ha. apply ok_k; [lia|]. unfold DK. rewrite Hu. lia. }
apply (cells_xfer _ _ _ OKM).
+ unfold cell_in. apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite (EA0 k'), k'_base; cbn; lia|].
apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite Hk'; cbn; lia|]. apply Forall_nil.
+
assert (OLDK : Forall (cell_holds B ly rd) (chunk_cells k)).
{ old_in. do 2 right; left. apply in_flat_map. exists k. split; [exact Hk | exact HIN]. }
unfold chunk_cells, kChunkHeaderSize in OLDK. apply Forall_app in OLDK as [_ OLDK]. destruct (Z.eqb_spec (ck_rz k) 16); [lia|]. exact OLDK.
Qed.
Lemma cells_chunks : forall l1 l2, st_chunks S = l1 ++ k :: l2 -> ~ In (ck_beg k) (map ck_beg l1) -> ~ In (ck_beg k) (map ck_beg l2) ->
Forall (cell_holds B ly rd') (flat_map chunk_cells (l1 ++ k' :: l2)).
Proof.
intros l1 l2 E N1 N2. rewrite flat_map_app. cbn [flat_map]. rewrite !Forall_app. splits.
- apply Forall_flat_map'. intros x Hx. apply cells_chunk_other; [rewrite E; apply in_app_iff; left; exact Hx | intros Ex; apply N1; rewrite <- Ex; apply in_map; exact Hx].
- exact cells_chunk_k.
- apply Forall_flat_map'. intros x Hx. apply cells_chunk_other; [rewrite E; apply in_app_iff; right; right; exact Hx | intros Ex; apply N2; rewrite <- Ex; apply in_map; exact Hx].
Qed.
Lemma cells_sec : forall l1 l2, st_chunks S = l1 ++ k :: l2 -> Forall (cell_holds B ly rd') (sec_cells S').
Proof.
intros l1 l2 E. pose proof SPLIT as (l1' & l2' & E0 & E' & _).
pose proof (wf_secondary _ _ _ _ _ WF) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells S)) by (old_in; do 3 right; left; exact HIN).
unfold sec_cells in OLDS |- *. rewrite S'_sec_res, S'_sec_arr, E'. rewrite (flat_map_mid _ l1' k' k l2') by reflexivity. rewrite <- E0.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS]. apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof ok_inst as OKI.
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_reserved; lia|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_n; lia|].
apply Forall_cons; [apply (cell_xfer _ O3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_mutex; lia|].
apply Forall_app. split.
- apply (cells_xfer _ _ _ ok_Q); [|exact O4]. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) O5 c Hc) as Oc. apply in_flat_map in Hc as (x & Hx & Hc).
destruct (ck_beg x) as [|o|r o|c' p] eqn:Ebx; try solve [destruct Hc].
assert (OKP : okr (ly_sec ly r) 32) by (intros a Ha; eapply (ok_secpage x r o a Hx Ebx); unfold kPage; lia).
apply (cell_xfer _ Oc). intros j Hj. apply OKP. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; lia.
Qed.
Lemma batch_cells_within : forall l c, In c (batch_cells l) ->
exists b2, In b2 l /\ cell_in (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) c.
Proof. geo'.
induction l as [|b2 t IH]; intros c Hc; [destruct Hc|]. cbn [batch_cells] in Hc.
destruct Hc as [<-|[<-|[<-|Hc]]]; try (exists b2; split; [left; reflexivity | unfold cell_in; cbn; lia]).
apply in_app_iff in Hc as [Hc|Hc].
- apply in_map_iff in Hc as ([i x] & <- & Hix). apply in_combine_l in Hix. apply in_seq in Hix. exists b2. split; [left; reflexivity | unfold cell_in; cbn; lia].
- destruct (IH c Hc) as (b3 & H3 & R3). exists b3. split; [right; exact H3 | exact R3].
Qed.
Lemma okr_batch : forall b2, In b2 (all_batches S) -> okr (ly_space ly + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))).
Proof. geo'.
intros b2 Hb2 a Ha. pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) b2 Hb2) as [L1 L2]. unfold kBatchSlots in L2.
apply (ok_batch_other b2 a Hb2). unfold kBatchBytes. lia.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S').
Proof.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells S)) by (old_in; do 4 right; left; exact HIN).
pose proof ok_inst as OKI.
assert (OKQ : okr (T + t_qc) 32) by (intros a Ha; apply ok_T; unfold DT, t_qc, t_unwinding, t_stats, kThreadObjSize in *; lia).
unfold quar_cells, qc_cells in OLDQ |- *. rewrite S'_qglobal, S'_qthread.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
apply Forall_cons; [apply (cell_xfer _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_cmutex; lia|].
apply Forall_cons; [apply (cell_xfer _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_rmutex; lia|].
apply Forall_app. split.
- apply Forall_cons; [apply (cell_xfer _ O3); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O4); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O5); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_cons; [apply (cell_xfer _ O6); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
apply Forall_forall. intros c Hc. apply (cell_xfer _ (proj1 (Forall_forall _ _) OT c Hc)).
destruct (batch_cells_within _ c Hc) as (b2 & I2 & [R1 R2]). intros j Hj.
apply (okr_batch b2); [unfold all_batches; apply in_app_iff; left; exact I2 | lia].
- apply Forall_cons; [apply (cell_xfer _ G1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_cons; [apply (cell_xfer _ G4); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
apply Forall_forall. intros c Hc. apply (cell_xfer _ (proj1 (Forall_forall _ _) OG c Hc)).
destruct (batch_cells_within _ c Hc) as (b2 & I2 & [R1 R2]). intros j Hj.
apply (okr_batch b2); [unfold all_batches; apply in_app_iff; right; exact I2 | lia].
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S').
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells S)) by (old_in; do 5 right; left; exact HIN).
unfold fs_cells in OLDF |- *. rewrite S'_fs. apply (cells_xfer _ _ _ ok_F); [|exact OLDF].
unfold cell_in, kFakeStackSize. fcons. fcons.
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S').
Proof. destruct DEP as (D1 & _ & _). unfold depot_cells, depot_ids, depot_frames in D1 |- *. rewrite S'_depot. exact D1. Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. apply Forall_cons; [|apply Forall_nil]. cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r, NEW_unw. reflexivity.
Qed.
Lemma cells_all : Forall (cell_holds B ly rd') (acells B ly S').
Proof.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). unfold acells. rewrite E'.
rewrite !Forall_app. splits.
- exact cells_regions.
- exact cells_caches.
- exact (cells_chunks l1 l2 E N1 N2).
- exact (cells_sec l1 l2 E).
- exact cells_quar.
- exact cells_fs.
- exact cells_depot.
- exact (proj1 IAL).
- exact cells_thread.
Qed.
Lemma fa' : fa_entries_ok ly rd' S'.
Proof.
intros c i v Hc Hi Hv kk Hkk. rewrite reg' in Hi, Hv. rewrite AGok; [exact (am_fa B ly S rd M c i v Hc Hi Hv kk Hkk)|].
pose proof (wf_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
apply (ok_fa c Hc). lia.
Qed.
Lemma flags' : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hc Hp. rewrite frames'. rewrite AGok; [exact (am_flags B ly S rd M cid pos Hc Hp)|].
pose proof (flag_off_bounds cid pos Hc Hp) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *. apply ok_F. unfold kFakeStackSize. lia.
Qed.
Lemma depot' : depot_ok B ly rd' S'.
Proof. destruct DEP as (_ & D2 & _). unfold depot_ok, depot_ids, depot_traces in D2 |- *. rewrite S'_depot. exact D2. Qed.
Lemma fa_poison' : fa_poison_ranges ly S' = fa_poison_ranges ly S.
Proof. geo'.
pose proof SPLIT as (l1 & l2 & E & E' & _). unfold fa_poison_ranges, reg. rewrite S'_regions, E', E.
rewrite (flat_map_mid _ l1 k' k l2) by reflexivity. reflexivity.
Qed.
Lemma sec_extents' : sec_extents ly S' = sec_extents ly S.
Proof. geo'.
pose proof SPLIT as (l1 & l2 & E & E' & _). unfold sec_extents. rewrite E', E. rewrite (flat_map_mid _ l1 k' k l2) by reflexivity. reflexivity.
Qed.
Lemma asecA_S' : forall A, asecA ly S A -> asecA ly S' A.
Proof. intros A H e He. rewrite sec_extents' in He. exact (H e He). Qed.
Lemma hs_bounds : forall g, 4096 <= g -> g + 8 <= kHighMemEnd -> kLowShadowBeg <= shadow_addr g < kHighMemBeg.
Proof. geo'.
intros g H1 H2. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
pose proof (Z.div_le_mono 4096 g 8 ltac:(lia) H1) as X. change (4096 / 8) with 512 in X.
pose proof (Z.div_le_mono g (140737488355328 - 8) 8 ltac:(lia) ltac:(lia)) as Y. change ((140737488355328 - 8) / 8) with 17592186044415 in Y. lia.
Qed.
Lemma DH_iff : forall g, g mod 8 = 0 -> (DH (shadow_addr g) <-> u <= g < u + (nn + 7) / 8 * 8).
Proof. geo'.
intros g Hg. pose proof u_al8 as (U8 & _ & _). unfold DH, shadow_addr.
apply Z.mod_divide in Hg as [c Hc]; [|lia]. apply Z.mod_divide in U8 as [a Ha]; [|lia]. rewrite Hc, Ha.
rewrite !Z_div_mult by lia. pose proof ext_rounded as (_ & _ & NN2 & _). nia.
Qed.
Lemma fa_poison_high : forall lo len g, In (lo, len) (fa_poison_ranges ly S) -> lo <= g < lo + len -> 4096 <= g /\ g < ASAN_CEIL.
Proof. geo'.
intros lo len g Hin Hg. unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c ltac:(lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _]. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3.
pose proof (mapped_user_bound (as_universe B) 0 0 0 S c WF ltac:(lia)) as MB. unfold kUserMapSize, EV_MAX, kFreeArrayMax in *.
unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
unfold kHighMemBeg in *. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
- pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M)) (lo, len) Hin) as (_ & [I1 I2] & I3). cbn [fst snd] in I1, I2, I3. ceil. unfold ASAN_CEIL, kHighMemBeg, kLowShadowBeg in *. lia.
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
rewrite AGok; [exact Hrd|]. apply ok_hshadow; [apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; lia|]. intros HD. apply (DH_iff g Hg8) in HD.
pose proof (chunks_disjoint B ly S rd x k M Hx Hk Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. rewrite Hu in HD. lia. }
destruct (find_chunk_at B ly l1 g) as [x|] eqn:F1.
- apply find_chunk_at_In in F1 as [Hx Hgx].
apply (OTHER x); [rewrite E; apply in_app_iff; left; exact Hx | intros Ex; apply N1; rewrite <- Ex; apply in_map; exact Hx | exact Hgx | exact (SH v Hg8 HS')].
- destruct ((ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k)) eqn:TK.
+
apply andb_prop in TK as [T1 T2]. apply Z.leb_le in T1. apply Z.ltb_lt in T2.
apply Z.mod_divide in Hg8 as [c Hc]; [|lia]. apply Z.mod_divide in B8 as [b0 Hb0]; [|lia]. apply Z.mod_divide in R8 as [r0 Hr0]; [|lia].
assert (J : (g - ck_base B ly k) / 8 = c - b0). { rewrite Hc, Hb0. replace (c * 8 - b0 * 8) with ((c - b0) * 8) by lia. apply Z_div_mult. lia. }
assert (RU : ck_rz k / 8 = r0). { rewrite Hr0. apply Z_div_mult. lia. }
rewrite k'_base in HS'. rewrite J in HS', SH. unfold chunk_granule in HS', SH. rewrite k'_rz, k'_n, RU in HS'. rewrite RU, Hst in SH. cbn [ck_state k'] in HS'.
set (q := (nn + 7) / 8) in *.
destruct (c - b0 <? r0) eqn:C1.
*   apply Z.ltb_lt in C1. injection HS' as <-. rewrite AGok; [exact (SH _ ltac:(rewrite Hc; apply Z_mod_mult) eq_refl)|].
apply ok_hshadow; [apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; lia|]. intros HD. apply (DH_iff g ltac:(rewrite Hc; apply Z_mod_mult)) in HD. rewrite Hu in HD. nia.
* apply Z.ltb_ge in C1. destruct (c - b0 <? r0 + q) eqn:C2.
--   apply Z.ltb_lt in C2. injection HS' as <-. apply NEW_sh; [apply (DH_iff g ltac:(rewrite Hc; apply Z_mod_mult)); rewrite Hu; nia|].
rewrite (SH (if c - b0 <? r0 + nn / 8 then shAddressable else if (c - b0 =? r0 + nn / 8) && negb (nn mod 8 =? 0) then nn mod 8 else shHeapLeftRz));
[discriminate | rewrite Hc; apply Z_mod_mult | reflexivity].
--   apply Z.ltb_ge in C2. injection HS' as <-.
assert (OLDV : rd (shadow_addr g) = Some shHeapLeftRz).
{ apply SH; [rewrite Hc; apply Z_mod_mult|].
assert (F1' : c - b0 <? r0 + nn / 8 = false). { apply Z.ltb_ge. subst q. pose proof (Z.div_le_mono nn (nn + 7) 8 ltac:(lia) ltac:(lia)). lia. }
rewrite F1'. destruct (Z.eqb_spec (nn mod 8) 0) as [Z0|NZ]; cbn [negb andb]; [rewrite Bool.andb_false_r; reflexivity|].
replace (c - b0 =? r0 + nn / 8) with false; [reflexivity|]. symmetry. apply Z.eqb_neq. subst q.
pose proof (Z.div_mod nn 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound nn 8 ltac:(lia)) as MB.
pose proof (Z.div_mod (nn + 7) 8 ltac:(lia)) as DM'. pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(lia)) as MB'. nia. }
rewrite AGok; [exact OLDV|]. apply ok_hshadow; [apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; lia|]. intros HD.
apply (DH_iff g ltac:(rewrite Hc; apply Z_mod_mult)) in HD. rewrite Hu in HD. nia.
+
assert (NK : ~ (ck_base B ly k <= g < ck_base B ly k + ck_extent k)).
{ intros X. assert (TT : (ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k) = true) by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). rewrite TT in TK. discriminate. }
destruct (find_chunk_at B ly l2 g) as [x|] eqn:F2.
* apply find_chunk_at_In in F2 as [Hx Hgx].
apply (OTHER x); [rewrite E; apply in_app_iff; right; right; exact Hx | intros Ex; apply N2; rewrite <- Ex; apply in_map; exact Hx | exact Hgx | exact (SH v Hg8 HS')].
* destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg). pose proof (fa_poison_high lo len g Hin Hg) as [Y1 Y2].
rewrite AGok; [exact (SH v Hg8 HS')|]. apply ok_hshadow; [apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, ASAN_CEIL, kHighMemEnd in *; lia|]. intros HD. apply (DH_iff g Hg8) in HD. rewrite Hu in HD. lia.
Qed.
Lemma zshadow' : zshadow_ok B ly rd'.
Proof.
pose proof (am_zshadow B ly S rd M) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGok; [exact Z0|]. pose proof HIGH as HI. pose proof ext_rounded as (ER & _).
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in Hi |- *.
-
pose proof (lo_top _ LO) as (_ & _ & _ & T4 & T5 & _). unfold page_aligned in T5. apply Z.mod_divide in T5 as [s0 Hs0]; [|lia].
assert (E8 : shadow_addr (ly_stk_lo ly) + i = shadow_addr (ly_stk_lo ly + 8 * i)).
{ unfold shadow_addr. rewrite Hs0. replace (s0 * 4096) with ((512 * s0) * 8) by lia. replace (512 * s0 * 8 + 8 * i) with ((512 * s0 + i) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
rewrite E8. pose proof (Z.mul_div_le (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
apply ok_hshadow; [apply hs_bounds; ceil; unfold in_app, zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia|].
intros HD. apply (DH_iff (ly_stk_lo ly + 8 * i) ltac:(rewrite Hs0; replace (s0 * 4096 + 8 * i) with ((512 * s0 + i) * 8) by lia; apply Z_mod_mult)) in HD.
rewrite Hu in HD. pose proof (KX 8 _ eq_refl ltac:(lia)) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
-
rewrite (ts_zsh _ TB) in Hr. unfold Tfib_zero_shadow in Hr.
assert (R8 : exists lo len, r = (lo, len) /\ lo mod 8 = 0 /\ TFIB_IMG_LO <= lo /\ lo + len <= TFIB_IMG_END).
{ destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; eexists _, _; (split; [reflexivity|]); unfold TFIB_IMG_LO, TFIB_IMG_END; (split; [reflexivity|]); lia. }
destruct R8 as (lo & len & -> & L8 & L1 & L2). cbn [fst snd] in Hi |- *. clear Hr.
apply Z.mod_divide in L8 as [c Hc]; [|lia].
assert (E8 : shadow_addr lo + i = shadow_addr (lo + 8 * i)).
{ unfold shadow_addr. rewrite Hc. replace (c * 8 + 8 * i) with ((c + i) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
rewrite E8. pose proof (Z.mul_div_le len 8 ltac:(lia)).
apply ok_hshadow; [apply hs_bounds; unfold TFIB_IMG_LO, TFIB_IMG_END, kHighMemEnd in *; lia|].
intros HD. apply (DH_iff (lo + 8 * i) ltac:(rewrite Hc; replace (c * 8 + 8 * i) with ((c + i) * 8) by lia; apply Z_mod_mult)) in HD.
rewrite Hu in HD. zget HI (ck_base B ly k) (ck_extent k) ZK. pose proof ext_rounded as (ER' & NN1 & NN2 & NN3). pose proof KF as (_ & _ & _ & _ & G5 & _).
ceil. unfold TFIB_IMG_LO, TFIB_IMG_END, ASAN_CEIL in *. lia.
Qed.
Lemma vis_keep : forall L, Forall (range_vis B ly rd) L -> Forall (range_vis B ly rd') L.
Proof. intros L H. exact (Forall_range_vis_keep B ly rd rd' L VIS H). Qed.
Lemma vis_sub : forall r r', range_vis B ly rd r' -> aeval B ly (fst r') <= aeval B ly (fst r) ->
aeval B ly (fst r) + snd r <= aeval B ly (fst r') + snd r' -> range_vis B ly rd' r.
Proof.
intros r r' V H1 H2 i Hi. apply VIS. replace (aeval B ly (fst r) + i) with (aeval B ly (fst r') + (aeval B ly (fst r) + i - aeval B ly (fst r'))) by lia.
apply V. lia.
Qed.
Lemma junk' : Forall (range_vis B ly rd') (ajunk B ly S').
Proof.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). pose proof (am_junk B ly S rd M) as J. pose proof (am_client B ly S rd M) as CL.
unfold ajunk in J |- *. unfold quar_junk in J |- *. rewrite all_batches_S', E'. rewrite E in J.
unfold cache_junk, cache, sec_junk in J |- *. rewrite S'_cinit, S'_cache, S'_sec_arr, S'_sec_res, E'. rewrite E in J.
rewrite (flat_map_mid (fun k0 : chunk => match ck_beg k0 with PSec r _ => [(ASec r 32, kPage - 32)] | _ => [] end) l1 k' k l2) by reflexivity.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J]. apply Forall_app in J as [J6 J]. apply Forall_app in J as [J7 J].
apply Forall_cons; [intros i Hi; apply VIS; exact (J1 i Hi)|].
apply Forall_cons; [intros i Hi; apply VIS; exact (J2 i Hi)|].
apply Forall_app. split; [exact (vis_keep _ J3)|]. apply Forall_app. split; [exact (vis_keep _ J4)|].
apply Forall_app. split.
{
rewrite flat_map_app in J5 |- *. cbn [flat_map] in J5 |- *. apply Forall_app in J5 as [J5a J5]. apply Forall_app in J5 as [J5k J5b].
apply Forall_app. split; [exact (vis_keep _ J5a)|]. apply Forall_app. split; [|exact (vis_keep _ J5b)].
unfold chunk_junk in J5k |- *. rewrite k'_rz, k'_n, k'_extent. cbn [ck_state k']. rewrite Hst in J5k.
apply Forall_app in J5k as [Ja J5k]. apply Forall_app in J5k as [Jb J5k]. apply Forall_app in J5k as [_ Jd].
apply Forall_app. split; [exact (vis_keep _ Ja)|]. apply Forall_app. split; [exact (vis_keep _ Jb)|]. apply Forall_app. split; [|exact (vis_keep _ Jd)].
apply Forall_cons; [|apply Forall_nil].
apply (vis_sub _ (sptr_exp (ck_user k), ck_n k)).
- apply (proj1 (Forall_forall _ _) CL). unfold aclient. apply in_app_iff. left. apply in_flat_map. exists k. split; [exact Hk|]. unfold chunk_user. rewrite Hst. left. reflexivity.
- cbn [fst snd]. change (sptr_exp (ck_beg k')) with (sptr_exp (ck_beg k)). rewrite (EA k _ Hk). fold (sptr_addr B ly (ck_user k)). rewrite Hu. lia.
- cbn [fst snd]. change (sptr_exp (ck_beg k')) with (sptr_exp (ck_beg k)). rewrite (EA k _ Hk). fold (sptr_addr B ly (ck_user k)). rewrite Hu. lia. }
apply Forall_app. split; [exact (vis_keep _ J6)|].
apply Forall_app. split; [exact (vis_keep _ J7) | exact (vis_keep _ J)].
Qed.
Lemma areas' : Forall (range_vis B ly rd') (aareas S').
Proof.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). pose proof (am_areas B ly S rd M) as A.
unfold aareas, reg in A |- *. rewrite S'_regions, S'_sec_res, E'. rewrite E in A.
rewrite (flat_map_mid _ l1 k' k l2) by reflexivity. exact (vis_keep _ A).
Qed.
Lemma client' : Forall (range_vis B ly rd') (aclient S').
Proof.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). pose proof (am_client B ly S rd M) as A.
unfold aclient in A |- *. rewrite frames', E'. rewrite E in A. rewrite flat_map_app in A |- *. cbn [flat_map] in A |- *.
unfold chunk_user at 2. cbn [ck_state k'].
apply vis_keep. apply Forall_forall. intros r Hr. apply (proj1 (Forall_forall _ _) A). rewrite !in_app_iff in Hr |- *. cbn [In] in Hr. tauto.
Qed.
Lemma placed' : sec_placed ly S'.
Proof. unfold sec_placed. rewrite sec_extents'. exact (am_placed B ly S rd M). Qed.
Theorem free_mid_ARm : ARm B ly S' rd'.
Proof.
constructor.
- exact WS'.
- exact (am_universe B ly S rd M).
- exact (am_syms B ly S rd M).
- exact LO.
- exact placed'.
- exact CONST'.
- exact (am_const_owned B ly S rd M).
- exact cells_all.
- exact fa'.
- exact flags'.
- exact depot'.
- exact shadow'.
- exact zshadow'.
- exact junk'.
- exact areas'.
- exact client'.
- exact (proj2 IAL).
- exact (am_tsd B ly S rd M).
- exact (am_static_img B ly S rd M).
Qed.
Lemma sec_live' : sec_live_bytes S' = sec_live_bytes S.
Proof. geo'.
pose proof SPLIT as (l1 & l2 & E & E' & _). unfold sec_live_bytes. rewrite E', E.
apply sec_live_bytes_begs; rewrite !map_app; reflexivity.
Qed.
Lemma prim_committed' : prim_committed S' = prim_committed S.
Proof. geo'. unfold prim_committed. rewrite S'_regions. reflexivity. Qed.
Lemma quar_S' : quar_n S' = quar_n S + nn /\ queued_n S' = queued_n S.
Proof. geo'.
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). unfold quar_n, queued_n, q_items, all_batches.
rewrite E, E', !quar_nl_split, S'_qthread, S'_qglobal.
replace (is_alloc k) with true by (unfold is_alloc; rewrite Hst; reflexivity). replace (is_alloc k') with false by reflexivity.
rewrite k'_n. lia.
Qed.
Lemma qloose_S' : qtight S -> qloose S'.
Proof. geo'.
intros (T1 & T2 & T3). pose proof quar_S' as [Q1 Q2].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [CKn _]. pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & _ & R3).
unfold qloose. rewrite S'_qthread, S'_qglobal, Q1, Q2. unfold ck_n, kQuarantineCacheMax, kQuarantineMax, MALLOC_MAX in *. lia.
Qed.
Lemma ALedger_S' : forall segs md, ALedger segs ly S md -> ALedger segs ly S' md.
Proof. geo'.
intros segs md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14]. constructor; try assumption.
- destruct L4 as (pieces & P1 & P2). exists pieces. split; [|exact P2].
unfold prim_pieces_ok, cut_ok, prim_hole_at, reg in P1 |- *. rewrite S'_regions. exact P1.
- rewrite sec_extents'. exact L7.
- rewrite sec_extents'. exact L8.
- rewrite prim_committed', sec_extents', S'_sec_res. exact L9.
- rewrite sec_extents'. exact L12.
Qed.
Lemma abudget_le : abudget S <= abudget S'.
Proof. geo'.
unfold abudget, sec_hulls. rewrite sec_live', S'_secs  . replace (st_nev S') with (st_nev S + 1); [unfold EV_A; lia|].
unfold S', sd, depot_after, s1. destruct (z =? 0); reflexivity.
Qed.
Lemma S'_nev : st_nev S' = st_nev S + 1.
Proof. geo'. unfold S', sd, depot_after, s1. destruct (z =? 0); reflexivity. Qed.
Lemma abudget_step : abudget S' = abudget S + EV_A.
Proof. geo'. unfold abudget, sec_hulls. rewrite sec_live', S'_nev, S'_secs  . lia. Qed.
Lemma ameter_S' : ameter S' = ameter S + EV_A.
Proof.
geo'. pose proof prim_committed' as E1. pose proof S'_sec_res as E2. pose proof sec_live' as E3. pose proof abudget_step as E4.
clear - E1 E2 E3 E4. unfold ameter. rewrite E1, E2, E3, E4. lia.
Qed.
Lemma rroom_S' : mroom S -> rroom S'.
Proof using B ly S rd M k Hk Hst z tr. intros R. pose proof ameter_S' as E. clear - R E. unfold mroom, rroom, VM_HEAD, RF_HEAD, EV_A in *. lia. Qed.
Lemma prim_user_mapped' : prim_user_mapped S' = prim_user_mapped S.
Proof. geo'. unfold prim_user_mapped, reg. rewrite S'_regions. reflexivity. Qed.
Lemma k'_fresh_items : ~ In (ck_beg k') (map ck_beg (q_items S')).
Proof. geo'.
rewrite q_items_S'. intros Hin. apply in_map_iff in Hin as (x & Ex & Hx). cbn [ck_beg k'] in Ex.
pose proof (proj1 (Forall_forall _ _) (wq_items _ (wf_quarantine _ _ _ _ _ WF)) x Hx) as [X1 X2].
destruct (In_split_beg _ _ Hk (wf_chunks_nodup _ _ _ _ _ WF)) as (m1 & m2 & Em & M1 & M2).
rewrite Em in X1. apply in_app_iff in X1 as [X1|[<-|X1]]; [apply M1 | rewrite Hst in X2; discriminate | apply M2]; rewrite <- Ex; apply in_map; exact X1.
Qed.
Lemma k'_in : In k' (st_chunks S').
Proof. geo'. pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). rewrite E'. apply in_app_iff. right. left. reflexivity. Qed.
Lemma class_elems_S' : forall c, class_elems S' c = class_elems S c.
Proof. geo'.
intros c. pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2). unfold class_elems, reg, cache. rewrite S'_regions, S'_cache.
rewrite (chunk_offs_begs S S') by (rewrite E, E', !map_app; reflexivity).
unfold batch_offs, all_batches. rewrite S'_qthread, S'_qglobal. reflexivity.
Qed.
Lemma room_S' : forall c, 1 <= c <= 31 ->
fa_room (rg_alloc_user (reg S' c)) (length (class_elems S' c)) (2 + 2 * (EV_MAX - st_nev S')) (rg_mapped_fa (reg S' c)).
Proof. geo'.
intros c Hc. unfold reg. rewrite S'_regions, class_elems_S', S'_nev. change (znth region0 c (st_regions S)) with (reg S c).
pose proof (bslack_le c 0 ltac:(lia)). eapply fa_room_xfer; [exact (wf_fa_room _ _ _ _ _ WF c Hc) | lia | apply Z.le_refl].
Qed.
Lemma refill_reg_S' : forall c, 1 <= c <= 31 -> refill_reg S' c.
Proof. drop_mem. clear AOK HU.
intros c Hc. pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2).
apply (refill_reg_tick S S' c Hev Hc S'_nev S'_secs).
- rewrite E, E', !length_app. reflexivity.
- apply cdef_ext; [unfold reg; rewrite S'_regions; reflexivity | rewrite class_elems_S'; reflexivity].
- unfold nrecZ. rewrite (chunk_offs_begs S S') by (rewrite E, E', !map_app; reflexivity). unfold batch_offs, all_batches. rewrite S'_qthread, S'_qglobal. reflexivity.
- rewrite prim_user_mapped', S'_nev. pose proof (wf_prim_ev _ _ _ _ _ WF). lia.
Qed.
Lemma owned_S' : forall a, aowned B ly S' a -> aowned B ly S a \/ (u <= a < u + nn).
Proof. geo'.
intros a [U NC]. pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2).
assert (U0 : let a0 := a in
Exists (in_zr a0) (as_owned_static B) \/ Exists (in_zr a0) (owned_extents ly) \/ in_zr a0 (ly_C ly, 256) \/ Exists (in_zr a0) (sec_extents ly S) \/
Exists (fun r => in_zr a0 (shadow_addr (fst r), (snd r + 7) / 8)) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone])).
{ cbv zeta. rewrite <- sec_extents'. exact U. }
cbv zeta in U0.
destruct (Z_lt_le_dec a u) as [L|L]; [| destruct (Z_lt_le_dec a (u + nn)) as [L'|L']; [right; lia |]];
left; split; [exact U0 | | exact U0 |]; intros C; apply NC; unfold aclient_byte in C |- *; rewrite frames';
(destruct C as [(y & Hy & Hsy & Hr)|C]; [left | right; exact C]);
rewrite E in Hy; rewrite E'; apply in_app_iff in Hy as [Hy|[<-|Hy]];
first [ exists y; split; [apply in_app_iff; left; exact Hy | split; [exact Hsy | exact Hr]]
| exists y; split; [apply in_app_iff; right; right; exact Hy | split; [exact Hsy | exact Hr]]
| exfalso; lia ].
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
rewrite E in Hy. apply in_app_iff in Hy as [X|[<-|X]]; [apply N1 | rewrite Hq in Hsy; discriminate | apply N2]; rewrite <- Eq; apply in_map; exact X. }
pose proof (chunks_disjoint B ly S0 rd0 y x M0 Hy Hx Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia. }
pose proof (am_layout _ _ _ _ M0) as LO0.
destruct (ck_beg x) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
pose proof (region_in_prim ly (prim_class o) LO0 ltac:(lia)) as (R1 & R2 & _).
eapply own_prim_nonuser; [exact M0 | lia | exact NB].
- destruct GG as (-> & _ & Gbase & Gext & Gin & Gal & _).
pose proof (proj1 (Forall_forall _ _) (proj1 (am_placed _ _ _ _ M0)) _ Gin) as (_ & [I1 I2] & _). cbn [fst snd] in I1, I2.
pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl (proj2 (am_placed _ _ _ _ M0)) Gin
ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
eapply own_ext; [exact M0 | right; apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req x)); split; [exact Gin | unfold in_zr, kPage in *; cbn; lia] | exact NB |].
unfold zdisjoint, kFakeFramesOff, kPage in *. cbn [fst snd] in DJ. lia.
Qed.
Lemma D_owned : ARm B ly S' rd' -> forall a, 0 <= a -> D a -> aowned B ly S a \/ aowned B ly S' a \/ DS a.
Proof. drop_mem. drop_ev.
intros M' a Ha0 HD. pose proof HIGH as HI. pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof ext_rounded as (ER & NN1 & NN2 & NN3).
pose proof SPLIT as (l1 & l2 & E & E' & N1 & N2).
destruct HD as [X|[X|[X|[X|[X|X]]]]].
- left. eapply (own_core B ly S rd (T, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|]. cbn [fst snd]. unfold DT, t_qc, t_unwinding, t_stats, kThreadObjSize in *. lia.
-
right; left. apply (own_ext_quar S' rd' k' a M'); [rewrite E'; apply in_app_iff; right; left; reflexivity | reflexivity |].
rewrite k'_base, k'_extent. unfold DK in X. rewrite Hu in X. lia.
- right; right. exact X.
- left. apply (own_static B ly S rd a M). rewrite (ts_owned _ TB). unfold DI in X. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB) in X.
apply Exists_exists. exists (0xa5850, 0x5c8650 - 0xa5850). split; [unfold Tfib_owned_static; cbn; tauto|]. unfold in_zr, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. cbn [fst snd]. lia.
- left. unfold depot_footprint in X. destruct X as [X|[X|[X|X]]].
+ apply (own_static B ly S rd a M). rewrite (ts_owned _ TB). rewrite (ts_depot _ TB) in X.
apply Exists_exists. exists (0xa5850, 0x5c8650 - 0xa5850). split; [unfold Tfib_owned_static; cbn; tauto|]. unfold in_zr, TFIB_DEPOT, d_map1 in *. cbn [fst snd]. lia.
+ eapply (own_core B ly S rd (ly_NB ly, kNodesBlockSize) a M); [unfold core_extents; cbn; tauto | cbn [fst snd]; exact X].
+ eapply (own_core B ly S rd (ly_SB ly, kStoreBlockSize) a M); [unfold core_extents; cbn; tauto | cbn [fst snd]; exact X].
+ apply (own_static B ly S rd a M). rewrite (ts_owned _ TB). rewrite (ts_store _ TB) in X.
apply Exists_exists. exists (0xa5850, 0x5c8650 - 0xa5850). split; [unfold Tfib_owned_static; cbn; tauto|]. unfold in_zr, TFIB_STORE in *. cbn [fst snd]. lia.
-
left. pose proof u_al8 as (U8 & _ & _). apply Z.mod_divide in U8 as [a0 Hua]; [|lia].
unfold DH, shadow_addr in X. rewrite Hua, Z_div_mult in X by lia.
replace a with (shadow_addr ((a0 + (a - (SHADOW_OFF + a0))) * 8)).
2:{ unfold shadow_addr. rewrite Z_div_mult by lia. lia. }
destruct (extent_zone B ly S rd k M Hk) as [[Z1 Z2]|(m & len & Zin & Z1 & Z2)].
+ eapply own_shadow_prim; [exact M|]. rewrite Hu in *. nia.
+ eapply own_shadow_sec; [exact M | exact Zin |]. rewrite Hu in *. unfold kPage in *. nia.
Qed.
End c0.
End w.
