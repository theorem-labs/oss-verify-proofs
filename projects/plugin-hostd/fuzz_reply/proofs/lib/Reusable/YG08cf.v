(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YG08cf.v, sha256 e1dafd546d7506a4fb6fa7703b7bf85061f3f6486a42126bf27cc1f335244217 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Theorem Labs, 2026-10: fuzz_preset's second allocator instance (suffix cf), the VM BUDGET on live state.
   cgif's YG08.v bounds the budget through the event counter, and both branches are false here:
   - vm_budget_slack (YG08.v:151-164), small branch: `st_nev s <= EV_MAX`, with prim_committed_bound
     (:46, `prim_user_mapped <= kUserMapSize * EV_MAX`) and sec_hulls <= HULL_MAX * EV_MAX (:157);
   - its big branch: `st_nev s <= EV_BIG = 2 ^ 17` (YG01.v:306, :310-311).
   Preset makes about 3.0e7 allocator events per harness call and fuzz_reply 6.7e7.
   This file bounds the budget on LIVE state only. The ceiling is CF_MAX (YGcfNames.v:297). The credit is what
   abudget_cf counts: A_BASE_CF + prim_committed + 8 * st_sec_reserved + sec_live_bytes + the hulls of the
   LIVE secondaries + the errbuf capacity. Each term is bounded by a field of WfP_cf, with no st_nev:
   - prim_committed: wrc_mapped_bound (<= kFreeArrayOffset) and wrc_fa_bound (<= kFreeArrayMax) per class;
   - st_sec_reserved: the secondary invariant's reserved bound (<= kPtrArrayEntriesPerCommit);
   - sec_live_bytes and the live hulls: live bytes (wfc_live), the quarantine (qloose) and the number of live
     secondaries (<= the length of st_sec_arr <= kPtrArrayEntriesPerCommit);
   - the errbuf capacity: the length bound of every st_secs entry (<= cf_nob <= 2 ^ 30).
   abudget_cf and mroom_cf are YG0ncf.v's, sec_live_hulls and cf_hull YGcfNames.v's; this file bounds them and defines none.
   NOT restated here: al_eager, meter_room, mroom_slack, rroom_slack (YG08.v:136-141, :165-189). They are
   ledger lemmas over ALedger, and the cf ledger ALedger_cf lives in YG0ncf.v.
   cgif's YG08.v is NOT edited. The state-only lemmas of YG08.v (sec_map_size_bound, sum_bytes_items,
   alloc_n, sec_bytes, reqbytes) are used from it as they are. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0n YG08 YG09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. Request sizes. cf_malloc_max replaces cgif's MALLOC_MAX = 2 ^ 28; CfParams   *)
(*    bounds it only through cf_sizes_ok and cf_nob_ok, so its range is derived.  *)
Lemma sec_map_size_ge : forall n, 0 <= n -> n + 16 <= sec_map_size n.
Proof.
intros n Hn. unfold sec_map_size, needed_size.
pose proof (needed_primary_bounds n Hn) as (N1 & _). pose proof (rz_size_bounds n) as [R1 _].
pose proof (req_size_bounds n Hn) as (_ & _ & Q & _).
pose proof (round_up_ge (needed_primary n) kPage ltac:(unfold kPage; lia)) as [[U1 _] _].
pose proof (round_up_ge (needed_primary n + rz_size n) kPage ltac:(unfold kPage; lia)) as [[U2 _] _].
destruct (from_primary n); unfold kPage in *; lia.
Qed.

Lemma sec_map_size_nonneg : forall n, 0 <= n -> 0 <= sec_map_size n.
Proof. intros n Hn. pose proof (sec_map_size_ge n Hn). lia. Qed.

Lemma sec_map_size_page : forall n, 0 <= n -> kPage <= sec_map_size n.
Proof.
intros n Hn. unfold sec_map_size, needed_size.
pose proof (needed_primary_bounds n Hn) as (N1 & _). pose proof (rz_size_bounds n) as [R1 _].
pose proof (req_size_bounds n Hn) as (_ & Q & _).
pose proof (round_up_ge (needed_primary n) kPage ltac:(unfold kPage; lia)) as [[U1 _] _].
pose proof (round_up_ge (needed_primary n + rz_size n) kPage ltac:(unfold kPage; lia)) as [[U2 _] _].
destruct (from_primary n); lia.
Qed.

Section SIZES.
Context {cp : CfParams}.

Lemma cf_malloc_max_bound : cf_malloc_max + 15 <= 2 ^ 30.
Proof.
pose proof cf_malloc_max_pos as P. pose proof cf_nob_ok as N.
assert (H1 : 0 <= cf_malloc_max - 1 < cf_malloc_max) by lia. pose proof (cf_sizes_ok _ H1) as S.
assert (H2 : 0 <= cf_malloc_max - 1) by lia. pose proof (sec_map_size_ge _ H2). lia.
Qed.

Lemma cf_nob_nonneg : 0 <= cf_nob.
Proof.
pose proof cf_malloc_max_pos as P. assert (H1 : 0 <= 0 < cf_malloc_max) by lia. pose proof (cf_sizes_ok _ H1) as S.
assert (H2 : 0 <= 0) by lia. pose proof (sec_map_size_nonneg _ H2). lia.
Qed.
End SIZES.

(* ---------------------------------------------------------------------------- *)
(* 2. The live-state bounds, over WfP_cf at any slack.                          *)
Section BOUNDS.
Context {cp : CfParams}.

(* cgif's prim_committed_bound (YG08.v:46) needs st_nev <= EV_MAX and its _any form (:65) bounds a class
   by kUserMapSize * EV_MAX. Here each of classes 1..31 holds at most kFreeArrayOffset of user map and
   kFreeArrayMax of free array, and class 0 is region0. *)
Lemma prim_committed_bound_cf : forall U pp cc bb s, WfP_cf U pp cc bb s ->
0 <= prim_committed s <= 31 * (kFreeArrayOffset + kFreeArrayMax).
Proof.
intros U pp cc bb s W.
pose proof (wfc_len_regions _ _ _ _ _ W) as LR. pose proof (wfc_reg0 _ _ _ _ _ W) as R0.
assert (B : forall j, (1 <= j < length (st_regions s))%nat ->
0 <= rg_mapped_user (nth j (st_regions s) region0) + rg_mapped_fa (nth j (st_regions s) region0)
<= kFreeArrayOffset + kFreeArrayMax).
{ intros j Hj. rewrite LR in Hj.
pose proof (wfc_classes _ _ _ _ _ W (Z.of_nat j) ltac:(lia)) as C. unfold wf_class_cf, reg, znth in C. rewrite Nat2Z.id in C.
pose proof (wrc_fa _ _ _ _ _ _ C) as [F1 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ C) as F2.
pose proof (wrc_mapped_bound _ _ _ _ _ _ C) as M. pose proof (wrc_alloc _ _ _ _ _ _ C). lia. }
unfold prim_committed. unfold reg, znth in R0. change (Z.to_nat 0) with 0%nat in R0.
destruct (st_regions s) as [|r0 rest]; [discriminate LR|]. cbn [nth] in R0. subst r0.
cbn [length] in LR. injection LR as LR.
assert (G : forall l, (forall j, (j < length l)%nat ->
0 <= rg_mapped_user (nth j l region0) + rg_mapped_fa (nth j l region0) <= kFreeArrayOffset + kFreeArrayMax) ->
0 <= fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 l
<= (kFreeArrayOffset + kFreeArrayMax) * Z.of_nat (length l)).
{ intros l Hl. induction l as [|r t IH]; [cbn; lia|]. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
pose proof (Hl 0%nat ltac:(cbn; lia)) as H0. cbn in H0. specialize (IH ltac:(intros j Hj; apply (Hl (S j)); cbn; lia)). lia. }
specialize (G rest ltac:(intros j Hj; exact (B (S j) ltac:(cbn [length]; lia)))).
rewrite LR in G. cbn [fold_right region0 rg_mapped_user rg_mapped_fa]. lia.
Qed.

(* cgif's nsec_le_arr (YG09.v:12) over WfP_cf. *)
Lemma nsec_le_arr_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> nsec_l (st_chunks s) <= Z.of_nat (length (st_sec_arr s)).
Proof.
intros U pp cc bb s W. pose proof (wsc_arr_chunks _ (wfc_secondary _ _ _ _ _ W)) as Sac.
pose proof (wfc_chunks_nodup _ _ _ _ _ W) as ND. pose proof (wfc_chunks _ _ _ _ _ W) as CK.
set (idx := fun l : list chunk => flat_map (fun k => match ck_beg k with PSec r _ => [r] | _ => [] end) l).
assert (L : forall l, nsec_l l = Z.of_nat (length (idx l))).
{ induction l as [|k t IH]; [reflexivity|]. unfold nsec_l, idx in *. cbn [fold_right flat_map]. rewrite length_app, Nat2Z.inj_add, <- IH.
destruct (ck_beg k); cbn [length]; lia. }
rewrite L. apply Nat2Z.inj_le. apply NoDup_incl_length.
- assert (G : forall l, Forall (chunk_ok_cf s) l -> NoDup (map ck_beg l) -> NoDup (idx l) /\ (forall r, In r (idx l) -> In (PSec r kPage) (map ck_beg l))).
{ induction l as [|k t IH]; intros Hc Hn; [split; [constructor | intros r []]|].
inversion Hc as [|k' t' Hk Ht]; subst. cbn [map] in Hn. inversion Hn as [|b' m' Hni Hnt]; subst. destruct (IH Ht Hnt) as [I1 I2].
unfold idx in *. cbn [flat_map map]. destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; cbn [app].
- split; [exact I1 | intros r Hr; right; exact (I2 r Hr)].
- split; [exact I1 | intros r Hr; right; exact (I2 r Hr)].
- destruct Hk as [_ Hk]. rewrite Eb in Hk. destruct Hk as (_ & -> & _). split.
+ constructor; [|exact I1]. intros Hin. apply Hni. exact (I2 r Hin).
+ intros r' [<-|Hr]; [left; reflexivity | right; exact (I2 r' Hr)].
- split; [exact I1 | intros r Hr; right; exact (I2 r Hr)]. }
exact (proj1 (G _ CK ND)).
- intros r Hr. apply Sac. unfold idx in Hr. apply in_flat_map in Hr as (k & Hk & Hr).
destruct (ck_beg k) as [|off|r' o|cid pos] eqn:Eb; try destruct Hr as [<-|[]]; try destruct Hr.
pose proof (proj1 (Forall_forall _ _) CK k Hk) as [_ Hok]. rewrite Eb in Hok. destruct Hok as (_ & -> & _). exists k. auto.
Qed.

Lemma sec_arr_reserved_cf : forall U pp cc bb s, WfP_cf U pp cc bb s ->
Z.of_nat (length (st_sec_arr s)) <= st_sec_reserved s <= kPtrArrayEntriesPerCommit /\ 0 <= st_sec_reserved s.
Proof.
intros U pp cc bb s W. pose proof (wsc_reserved _ (wfc_secondary _ _ _ _ _ W)) as R1.
pose proof (wsc_reserved_al _ (wfc_secondary _ _ _ _ _ W)) as R2. lia.
Qed.

(* cgif's sec_reserved_bound (YG08.v:117) over WfP_cf. *)
Lemma sec_reserved_bound_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> 0 <= 8 * st_sec_reserved s <= 2 ^ 17.
Proof.
intros U pp cc bb s W. pose proof (sec_arr_reserved_cf U pp cc bb s W) as R. unfold kPtrArrayEntriesPerCommit in R. lia.
Qed.

(* cgif's sec_extents_sizes64P / sec_extents_sizes64 (YG08.v:122, :134), for al_eager's cf form. The upper
   bound comes from cf_sizes_ok (sec_map_size n <= cf_nob <= 2 ^ 30), not from MALLOC_MAX. *)
Lemma sec_extents_sizes64P_cf : forall U pp cc bb ly s, WfP_cf U pp cc bb s ->
Forall (fun e => 4096 <= snd e < 2 ^ 64) (sec_extents ly s).
Proof.
intros U pp cc bb ly s W. pose proof (wfc_chunks _ _ _ _ _ W) as CK. unfold sec_extents. apply Forall_forall. intros e He.
apply in_flat_map in He as (k & Hk & He). pose proof (proj1 (Forall_forall _ _) CK k Hk) as [Hn _].
destruct (ck_beg k) as [|o|r o|c p]; try destruct He as [<-|[]]; try destruct He. cbn [snd].
pose proof (sec_map_size_page (ck_req k) ltac:(lia)). pose proof (cf_sizes_ok (ck_req k) Hn). pose proof cf_nob_ok.
unfold kPage in *. lia.
Qed.

Lemma sec_extents_sizes64_cf : forall U ly s, Wf_cf U s -> Forall (fun e => 0 <= snd e < 2 ^ 64) (sec_extents ly s).
Proof. intros U ly s W. eapply Forall_impl; [|exact (sec_extents_sizes64P_cf U 0 0 0 ly s W)]. cbv beta. intros e H. lia. Qed.
End BOUNDS.

(* The secondary bytes, chunk by chunk. cgif's sec_bytes_le / sec_bytes_le_sec (YG08.v:26, :95) charge every
   ALLOCATED chunk, primary ones included, through alloc_n_le (:35), whose `+ length l` term is the chunk
   count and grows with events. This form charges only the secondary chunks: an allocated one costs its
   request plus one, a quarantined one is inside quar_nl, and each pays at most 2 ^ 14 of rounding. *)
Lemma sec_bytes_le_cf : forall l, Forall (fun k => 0 <= ck_req k) l ->
sec_bytes l <= reqbytes l + quar_nl l + (2 ^ 14 + 1) * nsec_l l.
Proof.
intros l H. induction H as [|k t Hk Ht IH]; [cbn; lia|].
unfold sec_bytes, reqbytes, quar_nl, nsec_l in *. cbn [fold_right].
pose proof (sec_map_size_bound (ck_req k) Hk) as B. pose proof (req_size_bounds (ck_req k) Hk) as (E & Q1 & Q2).
unfold ck_n in *. destruct (ck_beg k); destruct (is_alloc k); lia.
Qed.

Lemma sec_bytes_nonneg : forall l, Forall (fun k => 0 <= ck_req k) l -> 0 <= sec_bytes l.
Proof.
intros l H. induction H as [|k t Hk Ht IH]; [cbn; lia|].
unfold sec_bytes in *. cbn [fold_right]. pose proof (sec_map_size_nonneg (ck_req k) Hk).
destruct (ck_beg k); cbv beta iota; lia.
Qed.

(* The hulls of the LIVE secondaries, the fold of YGcfNames.v's sec_live_hulls over any chunk list: unlike
   cgif's sec_hulls (YG01.v:286), which sums over st_secs and so over every secondary ever mapped, it counts
   only the chunks that still hold a secondary. *)
Lemma live_hulls_le : forall l, Forall (fun k => 0 <= ck_req k) l ->
0 <= fold_right (fun k acc => match ck_beg k with
| PSec _ _ => Z.max 0 (sec_map_size (ck_req k) / 8 + 8192) + acc
| _ => acc end) 0 l
<= sec_bytes l / 8 + 8192 * nsec_l l.
Proof.
intros l H. induction H as [|k t Hk Ht IH]; [cbn; lia|].
unfold sec_bytes, nsec_l in *. cbn [fold_right]. pose proof (sec_map_size_nonneg (ck_req k) Hk) as N.
pose proof (Z.div_pos (sec_map_size (ck_req k)) 8 N ltac:(lia)) as D.
destruct (ck_beg k); cbv beta iota; lia.
Qed.

Lemma last_in_cons {A : Type} : forall (l : list A) a d, In (last (a :: l) d) (a :: l).
Proof.
induction l as [|b t IH]; intros a d; [left; reflexivity|].
change (last (a :: b :: t) d) with (last (b :: t) d). right. apply IH.
Qed.

Section LIVE.
Context {cp : CfParams}.

Lemma sec_bytes_live_cf : forall U pp cc bb s, WfP_cf U pp cc bb s ->
0 <= sec_live_bytes s <= blocks_bytes s + quar_n s + (2 ^ 14 + 1) * Z.of_nat (length (st_sec_arr s)).
Proof.
intros U pp cc bb s W. pose proof (wfc_chunks _ _ _ _ _ W) as CK.
assert (R0 : Forall (fun k => 0 <= ck_req k) (st_chunks s)) by (eapply Forall_impl; [|exact CK]; intros k [Hk _]; lia).
pose proof (sec_bytes_le_cf _ R0) as B1. pose proof (sec_bytes_nonneg _ R0) as B0. pose proof (nsec_le_arr_cf U pp cc bb s W) as B2.
change (sec_bytes (st_chunks s)) with (sec_live_bytes s) in B1, B0. change (reqbytes (st_chunks s)) with (blocks_bytes s) in B1.
change (quar_nl (st_chunks s)) with (quar_n s) in B1. lia.
Qed.

(* The quarantine's chunks, from qloose (YG01.v:339-340) and the batch byte counts. *)
Lemma quar_n_loose_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> qloose s -> quar_n s <= 2 ^ 29 + 2 ^ 31.
Proof.
intros U pp cc bb s W (T1 & T2 & T3). pose proof (wfc_quarantine _ _ _ _ _ W) as Q.
assert (QN : queued_n s <= qc_bytes (st_qthread s) + qc_bytes (st_qglobal s)).
{ rewrite (wq_bytes_t _ Q), (wq_bytes_g _ Q), !sum_bytes_items. unfold queued_n, q_items, all_batches. rewrite flat_map_app, items_n_app.
unfold kBatchBytes. lia. }
lia.
Qed.

(* cgif's sec_live_bound (YG08.v:81, premise st_nev <= EV_MAX) and sec_live_bound_big (:102, premise
   length (st_chunks s) <= 2 ^ 23) in one event-free form. *)
Theorem sec_bytes_bound_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> qloose s -> 0 <= sec_live_bytes s <= SEC_LIVE_MAX.
Proof.
intros U pp cc bb s W QL. pose proof (sec_bytes_live_cf U pp cc bb s W) as B.
pose proof (quar_n_loose_cf U pp cc bb s W QL). pose proof (wfc_live _ _ _ _ _ W).
pose proof (sec_arr_reserved_cf U pp cc bb s W).
unfold SEC_LIVE_MAX, LIVE_MAX, kPtrArrayEntriesPerCommit in *. lia.
Qed.

Theorem live_hulls_bound_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> qloose s ->
0 <= sec_live_hulls s <= SEC_LIVE_MAX / 8 + 8192 * kPtrArrayEntriesPerCommit.
Proof.
intros U pp cc bb s W QL. pose proof (wfc_chunks _ _ _ _ _ W) as CK.
assert (R0 : Forall (fun k => 0 <= ck_req k) (st_chunks s)) by (eapply Forall_impl; [|exact CK]; intros k [Hk _]; lia).
pose proof (live_hulls_le _ R0) as H. pose proof (nsec_le_arr_cf U pp cc bb s W) as N.
pose proof (sec_arr_reserved_cf U pp cc bb s W) as R. pose proof (sec_bytes_bound_cf U pp cc bb s W QL) as SB.
change (sec_bytes (st_chunks s)) with (sec_live_bytes s) in H. unfold sec_live_hulls.
pose proof (Z.div_le_mono (sec_live_bytes s) SEC_LIVE_MAX 8 ltac:(lia) (proj2 SB)). lia.
Qed.

(* The errbuf capacity is the length of a st_secs entry, or 0. *)
Theorem errb_cap_bound_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> 0 <= errb_cap_cf s <= cf_nob.
Proof.
intros U pp cc bb s W. pose proof (wsc_lens _ (wfc_secondary _ _ _ _ _ W)) as L. pose proof cf_nob_nonneg as N.
unfold errb_cap_cf, errb_e.
destruct (filter is_errb_cap (st_secs s)) as [|a l] eqn:E; [cbn [last sm_len]; lia|].
assert (Hin : In (last (a :: l) (mkSec 0 ERRB_CAP_TAG false)) (filter is_errb_cap (st_secs s)))
by (rewrite E; apply last_in_cons).
apply filter_In in Hin as [Hin _]. pose proof (proj1 (Forall_forall _ _) L _ Hin) as B. cbv beta in B. lia.
Qed.
End LIVE.

(* ---------------------------------------------------------------------------- *)
(* 3. The budget. ABUDGET_CF_MAX adds the bound of each term of abudget_cf (YG0ncf.v): *)
(*    A_BASE_CF; prim_committed (31 classes); prim_committed / 8, the primary's      *)
(*    shadow (the same bound / 8); 8 * st_sec_reserved; sec_live_bytes; cgif's       *)
(*    the unit's hull term cf_hull (YGcfNames.v), at most CF_HULL_MAX under the unit's *)
(*    cf_hull_ok (a NAMED premise below: preset's run meter, reply's kf count); the   *)
(*    errbuf capacity                                                                 *)
(*    (<= cf_nob <= 2 ^ 30). One constant serves every unit.                          *)
Definition ABUDGET_CF_MAX : Z :=
A_BASE_CF + 31 * (kFreeArrayOffset + kFreeArrayMax) + 31 * (kFreeArrayOffset + kFreeArrayMax) / 8
+ 8 * kPtrArrayEntriesPerCommit + SEC_LIVE_MAX + CF_HULL_MAX + 2 ^ 30.

Lemma ABUDGET_CF_MAX_val : ABUDGET_CF_MAX = 357019287552.
Proof. vm_compute. reflexivity. Qed.

Lemma ABUDGET_CF_MAX_slack : ABUDGET_CF_MAX + VM_SLACK <= CF_MAX.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Section BUDGET.
Context {cp : CfParams}.

Theorem abudget_bound_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> qloose s -> cf_hull_ok s ->
abudget_cf s <= ABUDGET_CF_MAX.
Proof.
intros U pp cc bb s W QL HT. unfold abudget_cf.
pose proof (prim_committed_bound_cf U pp cc bb s W) as PC. pose proof (sec_arr_reserved_cf U pp cc bb s W).
pose proof (sec_bytes_bound_cf U pp cc bb s W QL).
pose proof (errb_cap_bound_cf U pp cc bb s W). pose proof cf_nob_ok.
pose proof (live_hulls_bound_cf U pp cc bb s W QL) as LH.
assert (V : SEC_LIVE_MAX / 8 + 8192 * kPtrArrayEntriesPerCommit = 2818572288) by (vm_compute; reflexivity).
pose proof (cf_hull_bound s HT ltac:(lia)).
(* the primary's shadow: the committed bound / 8 *)
pose proof (Z.div_le_mono (prim_committed s) (31 * (kFreeArrayOffset + kFreeArrayMax)) 8 ltac:(lia) (proj2 PC)) as PC8.
unfold ABUDGET_CF_MAX, CF_HULL_MAX in *. lia.
Qed.

(* cgif's vm_budget_slack (YG08.v:151): the same slack VM_SLACK, with no regime premise. *)
Theorem vm_budget_slack_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> qloose s -> cf_hull_ok s ->
abudget_cf s + VM_SLACK <= CF_MAX.
Proof.
intros U pp cc bb s W QL HT. pose proof (abudget_bound_cf U pp cc bb s W QL HT). pose proof ABUDGET_CF_MAX_slack. lia.
Qed.

(* cgif's mtr_ok_of_regime (YG08.v:192): room for m <= 2 ^ 36 more bytes under the ceiling. With
   CF_MAX = ASAN_VM_LMIN - VM_HEAD - E_BASE this is mtr_ok's inequality for ameter_cf = E_BASE + abudget_cf. *)
Theorem abudget_room_cf : forall U pp cc bb s m, WfP_cf U pp cc bb s -> qloose s -> cf_hull_ok s ->
0 <= m <= 2 ^ 36 -> abudget_cf s + m <= CF_MAX.
Proof.
intros U pp cc bb s m W QL HT Hm. pose proof (vm_budget_slack_cf U pp cc bb s W QL HT). unfold VM_SLACK in *. lia.
Qed.

(* cgif's mroom_of_regime (YG08.v:194), on live state with the run row. *)
Theorem abudget_ceiling_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> qloose s -> cf_hull_ok s ->
abudget_cf s <= CF_MAX.
Proof. intros U pp cc bb s W QL HT. pose proof (abudget_room_cf U pp cc bb s 0 W QL HT ltac:(lia)). lia. Qed.

Theorem mroom_cf_of_live : forall U pp cc bb s, WfP_cf U pp cc bb s -> qloose s -> cf_hull_ok s ->
mroom_cf s.
Proof. intros U pp cc bb s W QL HT. apply mroom_cf_CF_MAX. exact (abudget_ceiling_cf U pp cc bb s W QL HT). Qed.
End BUDGET.
