(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma list_find_index_spec : forall {A} (f : A -> bool) l i0 i,
  list_find_index f l i0 = Some i -> exists x, (i0 <= i)%nat /\ nth_error l (i - i0) = Some x /\ f x = true.
Proof.
  intros A f l. induction l as [|y l IH]; intros i0 i H; cbn in H; [discriminate|].
  destruct (f y) eqn:FY.
  - injection H as <-. exists y. rewrite Nat.sub_diag. cbn. auto.
  - destruct (IH _ _ H) as (x & LE & NTH & FX). exists x. split; [lia|]. split; [|exact FX].
    replace (i - i0)%nat with (S (i - S i0))%nat by lia. cbn. exact NTH.
Qed.

Lemma list_find_index_some : forall {A} (f : A -> bool) l i0 x,
  In x l -> f x = true -> list_find_index f l i0 <> None.
Proof.
  intros A f l. induction l as [|y l IH]; intros i0 x Hin FX; cbn; [destruct Hin|].
  destruct (f y) eqn:FY; [discriminate|]. destruct Hin as [->|Hin]; [congruence|]. eapply IH; eauto.
Qed.

Lemma nth_error_split' : forall {A} (l : list A) i x, nth_error l i = Some x ->
  exists l1 l2, l = l1 ++ x :: l2 /\ length l1 = i.
Proof. intros A l i x H. destruct (nth_error_split l i H) as (l1 & l2 & H1 & H2). exists l1, l2. auto. Qed.

Lemma list_set_app : forall {A} (l1 l2 : list A) x v, list_set (l1 ++ x :: l2) (length l1) v = l1 ++ v :: l2.
Proof. intros A l1. induction l1 as [|y l1 IH]; intros l2 x v; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma removelast_app_single : forall {A} (l : list A) x, removelast (l ++ [x]) = l.
Proof. intros A l x. rewrite removelast_eq. apply removelast_last. Qed.

(* [comment removed for export] *)
Lemma swap_remove_perm : forall {A} (l : list A) i h,
  nth_error l i = Some h -> Permutation (h :: removelast (list_set l i (List.last l h))) l.
Proof.
  intros A l i h H. destruct (nth_error_split' l i h H) as (l1 & l2 & -> & <-).
  assert (CASES : l2 = [] \/ exists l2' z, l2 = l2' ++ [z]).
  { destruct l2 as [|u v]; [left; reflexivity| right]. destruct (exists_last (l := u :: v) ltac:(discriminate)) as (l2' & z & EQ). exists l2', z. exact EQ. }
  destruct CASES as [->|(l2' & z & ->)].
  - rewrite last_last. rewrite list_set_app. rewrite removelast_app_single. apply Permutation_cons_append.
  - replace (l1 ++ h :: l2' ++ [z]) with ((l1 ++ h :: l2') ++ [z]) by (rewrite <- app_assoc; reflexivity).
    rewrite last_last. rewrite <- app_assoc. cbn. rewrite list_set_app.
    replace (l1 ++ z :: l2' ++ [z]) with ((l1 ++ z :: l2') ++ [z]) by (rewrite <- app_assoc; reflexivity).
    rewrite removelast_app_single.
    apply Permutation_sym. rewrite app_comm_cons.
    replace (l1 ++ h :: l2' ++ [z]) with (l1 ++ h :: (l2' ++ [z])) by reflexivity.
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
    rewrite app_assoc. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|]. apply Permutation_middle.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition scan_step (m : Z) (acc : Z) (c : secchunk) : Z :=
  if (sc_map_beg c <=? m) && (acc <? sc_map_beg c) then sc_map_beg c else acc.

Lemma scan_max : forall m l a,
  let M := fold_left (scan_step m) l a in
  a <= M /\ (M = a \/ exists c, In c l /\ M = sc_map_beg c /\ sc_map_beg c <= m)
  /\ (forall c, In c l -> sc_map_beg c <= m -> sc_map_beg c <= M).
Proof.
  intros m l. induction l as [|c l IH]; intros a; cbn.
  - split; [lia|]. split; [left; reflexivity|]. intros c [].
  - set (a' := scan_step m a c). specialize (IH a'). cbn zeta in IH. destruct IH as (I1 & I2 & I3).
    assert (STEP : (a' = a /\ (sc_map_beg c <= m -> sc_map_beg c <= a)) \/ (a' = sc_map_beg c /\ sc_map_beg c <= m /\ a < sc_map_beg c)).
    { subst a'. unfold scan_step. destruct (sc_map_beg c <=? m) eqn:H1; destruct (a <? sc_map_beg c) eqn:H2; cbn.
      - right. apply Z.leb_le in H1. apply Z.ltb_lt in H2. auto.
      - left. apply Z.ltb_ge in H2. auto.
      - left. apply Z.leb_gt in H1. split; [reflexivity| lia].
      - left. apply Z.leb_gt in H1. split; [reflexivity| lia]. }
    split; [destruct STEP as [[EQ _]|(EQ & _ & LT)]; lia|]. split.
    + destruct I2 as [I2|(c0 & Hc0 & X & Y)].
      * destruct STEP as [[EQ _]|(EQ & LE & LT)]; [left; congruence|]. right. exists c. split; [left; reflexivity|]. split; [congruence| exact LE].
      * right. exists c0. split; [right; exact Hc0|]. auto.
    + intros c0 [<-|Hc0] LE.
      * destruct STEP as [[EQ IMP]|(EQ & _ & LT)]; [specialize (IMP LE); lia| lia].
      * exact (I3 c0 Hc0 LE).
Qed.

Lemma NoDup_map_inj_In : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros x y ND Hx Hy EQ; [destruct Hx|].
  cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; [reflexivity| | | exact (IH x y ND' Hx Hy EQ)].
  - exfalso. apply NI. rewrite EQ. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- EQ. apply in_map. exact Hx.
Qed.

Section WF.
Variable E : aenv.
Variable P : list Z.
Variable D : list batch.
Local Notation SB := (ae_space_beg E).
Notation AWF := (AWf E P D).

(* [comment removed for export] *)
Lemma sec_chunk_entry : forall s m cm, AWF s -> as_chunks s !! m = Some cm -> cm_prim cm = None ->
  exists sc, In sc (as_sec s) /\ cm_alloc_beg cm = sc_map_beg sc + kPageSize /\ sc_map_size sc = map_size (cm_n cm)
             /\ sc_map_beg sc + kPageSize <= m /\ m + 8 < sc_map_beg sc + sc_map_size sc
             /\ (sc_map_beg sc + sc_map_size sc <= SB \/ SB + kSpaceSize <= sc_map_beg sc)
             /\ 0 < sc_map_beg sc /\ in_primary SB m = false.   (* [comment removed for export] *)
Proof.
  intros s m cm WF Hcm PC. pose proof WF as X. destruct X as ((_ & HB & RS & _) & WR & WC & [K1 _] & WQ & (_ & _ & S3 & _) & WD).
  destruct (K1 _ _ Hcm) as (A & B & C & D0 & _). rewrite PC in D0. destruct D0 as (_ & sc & Hsc & Hab & Hms & _).
  exists sc. destruct (S3 sc Hsc) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  unfold cm_chunk_beg, cm_user_beg, kChunkHeaderSize in A. rewrite C in A.
  change (16 * 2 ^ rz_log (cm_n cm)) with (rz_size (cm_n cm)) in A. pose proof (rz_size_pos (cm_n cm)) as RP.
  pose proof (map_size_facts (cm_n cm)) as (_ & MG & M2). pose proof (needed_ge (cm_n cm)) as NG. rewrite <- Hms in MG, M2.
  split; [exact Hsc|]. split; [exact Hab|]. split; [exact Hms|]. unfold kPageSize in *.
  split; [lia|]. split; [lia|]. split; [exact P6|]. split; [unfold app_mem in P2; rewrite kHighMemBeg_val in P2; lia|].
  unfold in_primary. rewrite kHighMemBeg_val in *. unfold kSpaceSize in *.
  destruct P6; [apply andb_false_intro1; apply Z.leb_gt; lia| apply andb_false_intro2; apply Z.ltb_ge; lia].
Qed.

Lemma sec_block_begin_ok : forall s m cm, AWF s -> as_chunks s !! m = Some cm -> cm_prim cm = None ->
  sec_block_begin s m = cm_alloc_beg cm.
Proof.
  intros s m cm WF Hcm PC.
  destruct (sec_chunk_entry s m cm WF Hcm PC) as (sc & Hsc & Hab & Hms & L1 & L2 & OUT & HBsc & NP).
  pose proof WF as X. destruct X as (_ & _ & _ & _ & _ & (_ & _ & S3 & S4 & S5) & _).
  unfold kPageSize in *.
  unfold sec_block_begin.
  change (fun acc c => if (sc_map_beg c <=? m) && (acc <? sc_map_beg c) then sc_map_beg c else acc) with (scan_step m).
  pose proof (scan_max m (as_sec s) 0) as SM. cbn zeta in SM. destruct SM as (M1 & M2 & M3).
  set (M := fold_left (scan_step m) (as_sec s) 0) in *.
  assert (LE : sc_map_beg sc <= M) by (apply M3; [exact Hsc| lia]).
  assert (EQM : M = sc_map_beg sc).
  { destruct M2 as [M2|(c & Hc & HM & Hcm')]; [lia|].
    destruct (S3 c Hc) as (_ & _ & _ & SZc & _).
    assert (c = sc \/ c <> sc) as [->|NE] by (destruct (Z.eq_dec (sc_map_beg c) (sc_map_beg sc)) as [EQ|NE];
      [left; exact (NoDup_map_inj_In _ _ _ _ S4 Hc Hsc EQ)| right; congruence]); [exact HM|].
    destruct (S5 c sc Hc Hsc NE) as [X|X]; lia. }
  rewrite EQM. replace (sc_map_beg sc =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (list_find_index (fun c => sc_map_beg c =? sc_map_beg sc) (as_sec s) 0) as [i|] eqn:FI.
  2:{ exfalso. eapply (list_find_index_some (fun c => sc_map_beg c =? sc_map_beg sc)); [exact Hsc| apply Z.eqb_refl| exact FI]. }
  destruct (list_find_index_spec _ _ _ _ FI) as (x & _ & NTH & FX). rewrite Nat.sub_0_r in NTH. rewrite NTH.
  apply Z.eqb_eq in FX. pose proof (NoDup_map_inj_In _ _ _ _ S4 (nth_error_In _ _ NTH) Hsc FX) as ->.
  replace (m <? sc_map_beg sc + sc_map_size sc) with true by (symmetry; apply Z.ltb_lt; lia). unfold kPageSize; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma large_dealloc_spec : forall s0 sc,
  AWF s0 -> In sc (as_sec s0) ->
  (forall cb cm, as_chunks s0 !! cb = Some cm -> cm_prim cm = None -> cm_alloc_beg cm <> sc_map_beg sc + kPageSize) ->
  hoare (fun s => s = s0) (large_dealloc (sc_map_beg sc + kPageSize))
    (fun s' _ => AWF s' /\ as_chunks s' = as_chunks s0 /\ as_tq s' = as_tq s0 /\ as_gq s' = as_gq s0
                 /\ as_regions s' = as_regions s0 /\ as_cache s' = as_cache s0 /\ as_cache_inited s' = as_cache_inited s0
                 /\ Permutation (sc :: as_sec s') (as_sec s0)).
Proof.
  intros s0 sc WF Hsc NOREF. unfold large_dealloc. apply hoare_get_bind. intros s ->.
  replace (sc_map_beg sc + kPageSize - kPageSize) with (sc_map_beg sc) by lia.
  pose proof WF as X. destruct X as (WE & WR & WC & WCH & WQ & (S1 & S2 & S3 & S4 & S5) & WD).
  destruct (list_find_index (fun c => sc_map_beg c =? sc_map_beg sc) (as_sec s0) 0) as [i|] eqn:FI.
  2:{ exfalso. eapply (list_find_index_some (fun c => sc_map_beg c =? sc_map_beg sc)); [exact Hsc| apply Z.eqb_refl| exact FI]. }
  destruct (list_find_index_spec _ _ _ _ FI) as (x & _ & NTH & FX). rewrite Nat.sub_0_r in NTH. rewrite NTH.
  apply Z.eqb_eq in FX. pose proof (NoDup_map_inj_In _ _ _ _ S4 (nth_error_In _ _ NTH) Hsc FX) as ->. clear FX.
  pose proof (swap_remove_perm (as_sec s0) i sc NTH) as PERM.
  set (sec' := removelast (list_set (as_sec s0) i (List.last (as_sec s0) sc))) in *.
  apply hoare_upd_bind. apply hoare_pre. intros s1 (s & -> & ->). set (s1 := upd_glob _ _ _).
  assert (HS1 : as_sec s1 = sec') by reflexivity.
  assert (SUB : forall c, In c sec' -> In c (as_sec s0) /\ c <> sc).
  { intros c Hc. split; [eapply Permutation_in; [exact PERM| right; exact Hc]|].
    intros ->. pose proof (Permutation_NoDup (Permutation_map sc_map_beg (Permutation_sym PERM)) S4) as ND. cbn in ND.
    inversion ND as [|? ? NI]; subst. apply NI. apply in_map. exact Hc. }
  assert (SUP : forall c, In c (as_sec s0) -> c <> sc -> In c sec').
  { intros c Hc NE. pose proof (Permutation_in _ (Permutation_sym PERM) Hc) as [<-|H]; [congruence| exact H]. }
  assert (WF1 : AWF s1).
  { split; [exact WE|]. split; [eapply wf_regions_same; [|exact WR]; reflexivity|].
    split; [eapply wf_cache_same; [| | |exact WC]; reflexivity|].
    split.
    { destruct WCH as [K1 K2]. split; [| exact K2]. intros cb cm H. destruct (K1 _ _ H) as (A & B & C & D0 & E0).
      unfold wf_chunk. split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [|exact E0].
      destruct (cm_prim cm) eqn:PC; [exact D0|]. destruct D0 as (D1 & sc' & Hsc' & Hab' & X). split; [exact D1|]. exists sc'.
      split; [| split; [exact Hab'| exact X]]. rewrite HS1. apply SUP; [exact Hsc'|]. intros ->. exact (NOREF cb cm H PC Hab'). }
    split; [eapply wf_quarantine_same; [..|exact WQ]; reflexivity|].
    split; [|exact WD].
    unfold wf_secondary, n_chunks. rewrite !HS1. change (as_ptr_committed s1) with (as_ptr_committed s0).
    assert (LEN : Z.of_nat (length sec') + 1 = Z.of_nat (length (as_sec s0))).
    { pose proof (Permutation_length PERM) as L. cbn in L. lia. }
    split; [destruct S1 as [[S1a S1b]|S1a]; [rewrite S1b in Hsc; destruct Hsc| right; exact S1a]|].
    split; [unfold n_chunks in S2; lia|].
    split; [intros c Hc; apply S3; exact (proj1 (SUB c Hc))|].
    split; [| intros a b Ha Hb NE; apply S5; [exact (proj1 (SUB a Ha))| exact (proj1 (SUB b Hb))| exact NE]].
    pose proof (Permutation_NoDup (Permutation_map sc_map_beg (Permutation_sym PERM)) S4) as ND. cbn in ND. inversion ND; assumption. }
  eapply hoare_bind; [apply (poison_zero_frame (fun s => s = s1)); reflexivity|]. intros []. apply hoare_pre. intros s ->.
  apply hoare_upd_bind. apply hoare_pre. intros s2 (s & -> & ->). set (s2 := upd_ts _ s1).
  eapply hoare_conseq; [apply (call_munmap_frame (fun s => s = s2))| intros s H; exact H|].
  intros s [] ->. split; [eapply AWf_same_core; [apply same_core_upd_ts| exact WF1]|].
  repeat (split; [reflexivity|]). change (as_sec s2) with sec'. exact PERM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma carved_class_of_addr : forall s c a, 1 <= c <= kLargestClassID -> wf_env E -> wf_regions E s -> carved E s c a ->
  in_primary SB a = true /\ ((a - SB) / kRegionSize) mod kNumClasses = c.
Proof.
  intros s c a Hc (_ & HB & RS & _) WR CV. pose proof (carved_range E s c a Hc WR CV) as [R1 R2].
  pose proof (class_size_mod c Hc) as [_ SZ]. destruct CV as (k & Hk & -> & Hk1).
  rewrite kHighMemBeg_val in HB.
  unfold region_beg, kFreeArrayOffset, kRegionSize, kLargestClassID, kNumClasses, kSpaceSize, in_primary in *.
  assert (KS : 0 <= k * class_size c < 2^32) by nia.
  split.
  - apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; unfold kSpaceSize; nia.
  - replace (SB + c * 2 ^ 32 + k * class_size c - SB) with (k * class_size c + c * 2^32) by lia.
    rewrite Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Lemma upd_dead_id : forall s, upd_dead (fun d => d) s = s.
Proof. intros s; destruct s; reflexivity. Qed.

Lemma qcb_recycle_spec : forall s0 m cm i j,
  AWF s0 -> as_chunks s0 !! m = Some cm -> cm_state cm = CQuarantined i j ->
  (forall b, In b (as_tq s0 ++ as_gq s0) -> ~ In m (b_items b)) ->
  hoare (fun s => s = s0) (qcb_recycle E m)
    (fun s' _ => AWF s' /\ as_chunks s' = delete m (as_chunks s0) /\ as_tq s' = as_tq s0 /\ as_gq s' = as_gq s0).
Proof.
  intros s0 m cm i j WF Hcm ST NIN. unfold qcb_recycle. apply hoare_get_bind. intros s ->. rewrite Hcm, ST.
  pose proof WF as X. destruct X as (WE & WR & WC & [K1 K2] & WQ & WS & WD).
  set (s1 := upd_ts (ts_on_real_free (cm_n cm)) s0).
  assert (WF1 : AWF s1) by (eapply AWf_same_core; [apply same_core_upd_ts| exact WF]).
  assert (Hcm1 : as_chunks s1 !! m = Some cm) by exact Hcm.
  destruct (cm_prim cm) as [c|] eqn:PC.
  - (* [comment removed for export] *)
    pose proof (prim_chunk_geometry E P D s0 m cm c WF Hcm PC) as GEO. cbn zeta in GEO.
    destruct GEO as (IP & DIVc & MODc & BEG & MU & POS). rewrite IP, MODc.
    pose proof (chunk_beg_loc E P D s0 m cm WF Hcm) as LOC. rewrite PC in LOC. destruct LOC as (Hc & CV & _).
    unfold acheck at 1. replace (negb (c =? 0) && negb (c =? 31)) with true
      by (symmetry; apply andb_true_intro; split; apply negb_true_iff; apply Z.eqb_neq; unfold kLargestClassID in Hc; lia).
    eapply hoare_bind with (Q := fun s p => s = s0 /\ p = cm_alloc_beg cm).
    { eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s0); auto|]. intros []. apply hoare_ret. intros s ->.
      split; [reflexivity|]. rewrite DIVc. replace (_ <=? _) with true by (symmetry; apply Z.leb_le; exact MU). exact BEG. }
    intros p. apply hoare_pre. intros s [-> ->].
    destruct (carved_class_of_addr s0 c (cm_alloc_beg cm) Hc WE WR CV) as [IPa CLa]. rewrite IPa.
    unfold acheck. rewrite Z.eqb_refl. cbn beta iota.
    match goal with |- context [c =? ?x] => replace (c =? x) with true by (symmetry; apply Z.eqb_eq; symmetry; exact CLa) end.
    eapply hoare_bind with (Q := fun s _ => s = s0).
    { eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s0); auto|]. intros []. apply hoare_ret. auto. }
    intros []. apply hoare_upd_bind. apply hoare_pre. intros s (s' & -> & ->). fold s1.
    replace (cm_alloc_beg cm =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite CLa.
    apply hoare_upd_bind. apply hoare_pre. intros s (s' & -> & ->).
    set (s2 := upd_dead _ (upd_chunks _ s1)).
    assert (NIN1 : forall b, In b (as_tq s1 ++ as_gq s1) -> ~ In m (b_items b)) by exact NIN.
    assert (WF2 : AWF s2) by (apply AWf_delete_chunk; [exact WF1| exact NIN1]).
    assert (AV2 : avail E D s2 c (cm_alloc_beg cm)) by (apply (deleted_block_avail E P D s1 m cm c); [exact WF1| exact Hcm1| exact PC]).
    eapply hoare_conseq; [apply (local_dealloc_spec E P D s2 c (cm_alloc_beg cm) Hc WF2 AV2)| auto|].
    intros s [] (WF3 & (HK & HT & HG & _) & _). split; [exact WF3|]. rewrite HK, HT, HG. repeat split; reflexivity.
  - (* [comment removed for export] *)
    destruct (sec_chunk_entry s0 m cm WF Hcm PC) as (sc & Hsc & Hab & Hms & L1 & L2 & OUT & HBsc & NP). rewrite NP.
    pose proof (sec_block_begin_ok s0 m cm WF Hcm PC) as SBB.
    eapply hoare_bind; [apply hoare_ret with (Q := fun s p => s = s0 /\ p = cm_alloc_beg cm); intros s ->; auto|].
    intros p. apply hoare_pre. intros s [-> ->].
    assert (IPa : in_primary SB (cm_alloc_beg cm) = false).
    { rewrite Hab. unfold in_primary. unfold kSpaceSize, kPageSize in *.
      destruct OUT; [apply andb_false_intro1; apply Z.leb_gt; lia| apply andb_false_intro2; apply Z.ltb_ge; lia]. }
    rewrite IPa.
    eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s0); auto|]. intros [].
    apply hoare_upd_bind. apply hoare_pre. intros s (s' & -> & ->). fold s1.
    replace (cm_alloc_beg cm =? 0) with false by (symmetry; apply Z.eqb_neq; unfold kPageSize in *; lia).
    unfold acheck. rewrite Z.eqb_refl.
    eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s1); auto|]. intros [].
    eapply hoare_bind; [apply hoare_ret with (Q := fun s _ => s = s1); auto|]. intros [].
    apply hoare_upd_bind. apply hoare_pre. intros s (s' & -> & ->).
    set (s2 := upd_chunks (delete m) s1).
    assert (ES2 : s2 = upd_dead (fun d => d) (upd_chunks (delete m) s1)) by (symmetry; apply upd_dead_id).
    assert (WF2 : AWF s2) by (rewrite ES2; apply AWf_delete_chunk; [exact WF1| exact NIN]).
    assert (Hsc2 : In sc (as_sec s2)) by exact Hsc.
    assert (NOREF : forall cb cm', as_chunks s2 !! cb = Some cm' -> cm_prim cm' = None -> cm_alloc_beg cm' <> sc_map_beg sc + kPageSize).
    { intros cb cm' H PC' EQ. cbn in H. destruct (Z.eq_dec cb m) as [->|NE]; [rewrite lookup_delete_eq in H; discriminate|].
      rewrite lookup_delete_ne in H by auto. apply (K2 cb cm' m cm H Hcm NE). rewrite EQ, Hab. reflexivity. }
    rewrite Hab.
    eapply hoare_conseq; [apply (large_dealloc_spec s2 sc WF2 Hsc2 NOREF)| auto|].
    intros s [] (WF3 & HK & HT & HG & _). split; [exact WF3|]. rewrite HK, HT, HG. repeat split; reflexivity.
Qed.

End WF.
End RC__1.
