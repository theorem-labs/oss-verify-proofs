(* CARRIED from commit 13dada94373d48ba230c171e98126b88ba98118e,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfRoomFree.v, sha256 c977bf56bdd6d584323329ec4e5c06ad5df7cc2f63e1350bba89d84e1b8ddf87 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change made here is the module
   prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30 (free_cf's size test, Quarantine::Put): the charge rules of section 6-9 take free_small (free_cf's enqueue side, ck_n <= kQuarantineMax): rf_free_inner (tree with free_cf's size test), rf_free, free_step_q_cf, free_room_keep_nonew_cf, free_charge_cf, free_step_slots_cf, free_step_bytes_cf, free_run's frun_step. STATEMENT CHANGES (premise added); no consumer outside this file. *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the ROOM STEPS THAT COST
   NOTHING, over YGcfRoomKeep.v's ROOM_cf_k S k (STATE FIRST, then the headroom k).
   YGcfRoomStep.v's charges (RK_malloc = RK_free = 1) are the worst case of one call. This file proves
   when a call is FREE of charge, and how often a charged call can happen in a run.

   MALLOC. A primary request of a class c <> kBatchClass touches only class c's region, cache and free
   array (cache_alloc_cf -> refill_if_empty_cf -> get_from_allocator_cf c -> populate_cf c ->
   map_more_user_cf c / ensure_free_array c): no sec_alloc, so st_sec_arr is UNCHANGED; never class
   kBatchClass, so its mapped user size is UNCHANGED. The error buffer grows only in map_more_user_cf's
   class-full arm (errb_report_cf), and that arm returns false, after which populate_cf, then
   get_from_allocator_cf, then cache_alloc_cf return false / None / None and malloc_cf returns PNull.
   So a returning NON-NULL primary malloc of such a class costs NO headroom at all, and a NULL one costs
   only the one report (100 bytes of error buffer), not a secondary and not a batch map.

   FREE. A free costs one unit because its enqueue may allocate one quarantine batch from class
   kBatchClass. enqueue (YG00.v:451-460) does that only when need_new_batch (st_qthread s) holds: the
   thread cache's batch list is empty or its last batch holds kBatchSlots = 1,021 items. So a free from a
   state with a slot left in the last batch costs NOTHING (free_room_keep_nonew_cf), and the per-free
   charge is fcharge p s (0 or 1, free_charge_cf). Over a run of frees (free_run) the charges are
   counted by the slot measure slots_left and the quarantine's bytes: 1,021 charges need 1,021 frees
   (free_run_count), and a thread-cache transfer, which reopens the count, needs kQuarantineCacheMax =
   2^20 bytes of quarantine (free_run_bytes). free_run_charge_bound is the closed form.
   No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG02 YG04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfPath YGcfAmx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre YGcfRoomKeep YGcfRoomStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* 0. Two all-paths rules YGcfRoomStep.v does not have.                           *)
Lemma ipost_and : forall {A} (t : itree astate A) (P Q : A -> Prop),
ipost t P -> ipost t Q -> ipost t (fun a => P a /\ Q a).
Proof.
intros A t P Q. induction t as [a | q sn k IH | pc | f]; cbn [ipost]; intros HP HQ.
- split; [exact HP | exact HQ].
- intros z. exact (IH z (HP z) (HQ z)).
- exact I.
- exact I.
Qed.

Section RF. Context {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 1. The frame of a step that touches neither class kBatchClass nor the           *)
(*    secondary: rf_fr. rf_eq adds "and not the error buffer".                     *)
Definition rf_fr (s s' : astate) : Prop :=
length (st_regions s') = length (st_regions s) /\ st_cache s' = st_cache s /\
st_cache_inited s' = st_cache_inited s /\ st_sec_arr s' = st_sec_arr s /\
reg s' kBatchClass = reg s kBatchClass.

Definition rf_eq (s s' : astate) : Prop := rf_fr s s' /\ errb_size_cf s' = errb_size_cf s.

Lemma rf_fr_refl : forall s, rf_fr s s.
Proof. intros s. unfold rf_fr. rk_splits; reflexivity. Qed.

Lemma rf_fr_trans : forall s1 s2 s3, rf_fr s1 s2 -> rf_fr s2 s3 -> rf_fr s1 s3.
Proof.
intros s1 s2 s3 (A1 & B1 & C1 & D1 & E1) (A2 & B2 & C2 & D2 & E2). unfold rf_fr. rk_splits; congruence.
Qed.

Lemma rf_fr_of_fields : forall s s', st_regions s' = st_regions s -> st_cache s' = st_cache s ->
st_cache_inited s' = st_cache_inited s -> st_sec_arr s' = st_sec_arr s -> rf_fr s s'.
Proof. intros s s' R C I A. unfold rf_fr, reg. rewrite R, C, I, A. rk_splits; reflexivity. Qed.

Lemma rf_fr_of_nosec : forall s s', rk_nosec s s' -> rf_fr s s'.
Proof. intros s s' (A & B & C & D). apply rf_fr_of_fields; assumption. Qed.

Lemma rf_eq_refl : forall s, rf_eq s s.
Proof. intros s. split; [apply rf_fr_refl | reflexivity]. Qed.

Lemma rf_eq_trans : forall s1 s2 s3, rf_eq s1 s2 -> rf_eq s2 s3 -> rf_eq s1 s3.
Proof.
intros s1 s2 s3 (F1 & E1) (F2 & E2). split; [exact (rf_fr_trans _ _ _ F1 F2) | congruence].
Qed.

Lemma rf_fr_of_eq : forall s s', rf_eq s s' -> rf_fr s s'.
Proof. intros s s' (F & _). exact F. Qed.

Lemma rf_eq_set_region : forall c r s, 0 <= c -> c <> kBatchClass ->
rf_eq s (set_regions (zupd c r (st_regions s)) s).
Proof.
intros c r s Hc Hn. split; [|reflexivity]. unfold rf_fr.
rewrite (reg_upd_other s c kBatchClass r Hc ltac:(unfold kBatchClass; lia) Hn).
split; [exact (zupd_length c r (st_regions s))|]. rk_splits; reflexivity.
Qed.

Lemma rf_eq_of_efa : forall c s s', c <> kBatchClass -> rk_efa c s s' -> rf_eq s s'.
Proof.
intros c s s' Hn (L & O & _ & _ & _ & C & In & Se & Sa). split.
- unfold rf_fr. rewrite (O kBatchClass ltac:(unfold kBatchClass; lia) (fun E => Hn (eq_sym E))).
  rk_splits; [exact L | exact C | exact In | exact Sa | reflexivity].
- unfold errb_size_cf. rewrite Se. reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The class-c chain of malloc_cf, c <> kBatchClass: the error buffer grows     *)
(*    ONLY on a path whose result is false / None.                                *)
Lemma rf_set_exh : forall c s, 0 <= c -> c <> kBatchClass ->
ipost (set_exh_cf c s) (fun r => rf_eq s (snd r)).
Proof.
intros c s Hc Hn. unfold set_exh_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_set_region. cbn [snd]. apply rf_eq_set_region; assumption.
Qed.

Lemma rf_clear_exh : forall c s, 0 <= c -> c <> kBatchClass ->
ipost (clear_exh_cf c s) (fun r => rf_eq s (snd r)).
Proof.
intros c s Hc Hn. unfold clear_exh_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_set_region. cbn [snd]. apply rf_eq_set_region; assumption.
Qed.

Lemma rf_mmu : forall c need s, 0 <= c -> c <> kBatchClass ->
ipost (map_more_user_cf c need s) (fun r => rf_fr s (snd r) /\ (fst r = true -> rf_eq s (snd r))).
Proof.
intros c need s Hc Hn.
unfold map_more_user_cf. destruct (Z.eqb_spec c kBatchClass) as [E|_]; [contradiction|]. cbv beta iota zeta.
apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- rk_if.
  + apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. destruct (aGranted z); cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [fst snd].
      split; [apply rf_fr_of_eq | intros _]; apply rf_eq_set_region; assumption.
    * apply rk_bind. eapply ipost_mono with (P := fun r => rf_fr s (snd r)).
      2:{ destruct (aDestroyed z); cbv beta iota.
          - apply rk_set_region. cbn [snd]. apply rf_fr_of_eq. apply rf_eq_set_region; assumption.
          - apply rk_ret. cbn [snd]. apply rf_fr_refl. }
      intros [u s1] H1. cbn [fst snd] in *. apply rk_ret. cbn [fst snd].
      split; [exact H1 | intros Hf; discriminate Hf].
  + apply rk_bind. eapply ipost_mono; [|apply rk_errb_report]. intros [u s1] [N1 _]. cbn [fst snd] in *.
    apply rk_bind. eapply ipost_mono; [|apply rf_set_exh; assumption]. intros [u2 s2] C2. cbn [fst snd] in *.
    apply rk_ret. cbn [fst snd]. split; [|intros Hf; discriminate Hf].
    eapply rf_fr_trans; [apply rf_fr_of_nosec; exact N1 | exact (rf_fr_of_eq _ _ C2)].
- apply rk_ret. cbn [fst snd]. split; [apply rf_fr_refl | intros _; apply rf_eq_refl].
Qed.

Lemma rf_populate : forall c need s, 0 <= c -> c <> kBatchClass -> (Z.to_nat c < length (st_regions s))%nat ->
ipost (populate_cf c need s) (fun r => rf_fr s (snd r) /\ (fst r = true -> rf_eq s (snd r))).
Proof.
intros c need s Hc Hn Hl.
unfold populate_cf. destruct (Z.eqb_spec c kBatchClass) as [E|_]; [contradiction|]. cbv beta iota zeta.
apply rk_bind. eapply ipost_mono; [|apply rf_mmu; assumption]. intros [ok s1] [F1 E1]. cbn [fst snd] in *.
pose proof F1 as (L1 & _).
destruct ok; cbn [negb]; cbv beta iota.
- specialize (E1 eq_refl).
  apply rk_bind. apply rk_get_region. cbn [fst snd].
  apply rk_bind. eapply ipost_mono; [|apply rk_efa_path; [exact Hc | rewrite L1; exact Hl]].
  intros [ok2 s2] E2. cbn [fst snd] in *.
  pose proof (rf_eq_of_efa _ _ _ Hn E2) as Q2.
  destruct ok2; cbn [negb]; cbv beta iota.
  + apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_bind. apply rk_set_region. cbn [fst snd].
    apply rk_bind. eapply ipost_mono; [|apply rf_clear_exh; assumption]. intros [u4 s4] Q4. cbn [fst snd] in *.
    apply rk_ret. cbn [fst snd]. split; [apply rf_fr_of_eq | intros _];
    (eapply rf_eq_trans; [exact E1|]; eapply rf_eq_trans; [exact Q2|];
     eapply rf_eq_trans; [|exact Q4]; apply rf_eq_set_region; assumption).
  + apply rk_ret. cbn [fst snd]. split; [|intros Hf; discriminate Hf].
    apply rf_fr_of_eq. eapply rf_eq_trans; [exact E1 | exact Q2].
- apply rk_ret. cbn [fst snd]. split; [exact F1 | intros Hf; discriminate Hf].
Qed.

Lemma rf_gfa : forall c n s, 0 <= c -> c <> kBatchClass -> (Z.to_nat c < length (st_regions s))%nat ->
ipost (get_from_allocator_cf c n s) (fun r => rf_fr s (snd r) /\ (fst r <> None -> rf_eq s (snd r))).
Proof.
intros c n s Hc Hn Hl. unfold get_from_allocator_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rf_fr s (snd r) /\ (fst r = true -> rf_eq s (snd r))).
2:{ rk_if; [apply rf_populate; assumption
          | apply rk_ret; cbn [fst snd]; split; [apply rf_fr_refl | intros _; apply rf_eq_refl]]. }
intros [ok s1] [F1 E1]. cbn [fst snd] in *.
pose proof F1 as (L1 & _).
destruct ok; cbn [negb]; cbv beta iota.
- specialize (E1 eq_refl).
  apply rk_bind. apply rk_get_region. cbn [fst snd]. rk_if.
  + apply rk_ret. cbn [fst snd]. split; [exact F1 | intros Hf; exfalso; apply Hf; reflexivity].
  + match goal with |- context [fa_pop_n ?f ?a ?b ?l ?acc] => destruct (fa_pop_n f a b l acc) as [[tops rest]|] end;
    cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [fst snd].
      split; [apply rf_fr_of_eq | intros _];
      (eapply rf_eq_trans; [exact E1 | apply rf_eq_set_region; assumption]).
    * apply rk_fail.
- apply rk_ret. cbn [fst snd]. split; [exact F1 | intros Hf; exfalso; apply Hf; reflexivity].
Qed.

(* refill_if_empty_cf: if class c's cache is non-empty afterwards, nothing was reported. *)
Lemma rf_refill : forall c s, 0 <= c -> c <> kBatchClass -> (Z.to_nat c < length (st_regions s))%nat ->
ipost (refill_if_empty_cf c s) (fun r => st_sec_arr (snd r) = st_sec_arr s /\
reg (snd r) kBatchClass = reg s kBatchClass /\
(pc_chunks (cache (snd r) c) <> [] -> errb_size_cf (snd r) = errb_size_cf s)).
Proof.
intros c s Hc Hn Hl. unfold refill_if_empty_cf. apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s c)) as [|x l] eqn:Ep; cbv beta iota.
- apply rk_bind. eapply ipost_mono; [|apply rf_gfa; assumption]. intros [got s1] [F1 E1]. cbn [fst snd] in *.
  pose proof F1 as (L1 & C1 & I1 & A1 & R1).
  destruct got as [tops|]; cbv beta iota.
  + destruct (E1 ltac:(discriminate)) as [_ Eb1].
    apply rk_set_pc. cbn [snd]. split; [exact A1|]. split; [exact R1 | intros _; exact Eb1].
  + apply rk_ret. cbn [snd]. split; [exact A1|]. split; [exact R1|].
    intros HC. exfalso. apply HC. unfold cache. rewrite C1. exact Ep.
- apply rk_ret. cbn [snd]. split; [reflexivity|]. split; [reflexivity | intros _; reflexivity].
Qed.

Lemma rf_cache_alloc : forall c s, 0 <= c <= 31 -> c <> kBatchClass -> room_shape_cf s ->
ipost (cache_alloc_cf c s) (fun r => st_sec_arr (snd r) = st_sec_arr s /\
reg (snd r) kBatchClass = reg s kBatchClass /\ (fst r <> None -> errb_size_cf (snd r) = errb_size_cf s)).
Proof.
intros c s Hc Hn IV. unfold cache_alloc_cf.
apply rk_bind. eapply ipost_mono; [|apply rk_init; exact IV].
intros [u s1] (I1 & R1 & S1 & A1 & _ & _). cbn [fst snd] in *.
assert (Eb1 : errb_size_cf s1 = errb_size_cf s) by (unfold errb_size_cf; rewrite S1; reflexivity).
assert (Rg1 : reg s1 kBatchClass = reg s kBatchClass) by (unfold reg; rewrite R1; reflexivity).
pose proof I1 as (Lr1 & _).
assert (Hl1 : (Z.to_nat c < length (st_regions s1))%nat) by (rewrite Lr1; lia).
apply rk_bind. eapply ipost_mono; [|apply rf_refill; [lia | exact Hn | exact Hl1]].
intros [u2 s2] (A2 & R2 & E2). cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s2 c)) as [|x l] eqn:Ep; cbv beta iota zeta.
- apply rk_ret. cbn [fst snd]. split; [transitivity (st_sec_arr s1); [exact A2 | exact A1]|].
  split; [transitivity (reg s1 kBatchClass); [exact R2 | exact Rg1]|].
  intros Hf; exfalso; apply Hf; reflexivity.
- apply rk_bind. apply rk_set_pc. cbn [fst snd]. apply rk_ret. cbn [fst snd].
  split; [transitivity (st_sec_arr s1); [exact A2 | exact A1]|].
  split; [transitivity (reg s1 kBatchClass); [exact R2 | exact Rg1]|].
  intros _. transitivity (errb_size_cf s1); [apply E2; discriminate | exact Eb1].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. malloc_cf on a primary request of a class other than kBatchClass.            *)
Theorem rf_malloc_primary : forall n tr s, room_shape_cf s -> from_primary n = true ->
chunk_class n <> kBatchClass ->
ipost (malloc_cf n tr s) (fun r => st_sec_arr (snd r) = st_sec_arr s /\
reg (snd r) kBatchClass = reg s kBatchClass /\ (fst r <> PNull -> errb_size_cf (snd r) = errb_size_cf s)).
Proof.
intros n tr s IV Fp Hn. pose proof (chunk_class_ok n Fp) as Hcc.
unfold malloc_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
set (s0 := set_nev (st_nev s + 1) s).
assert (N0 : rk_nt s s0) by (unfold rk_nt; rk_splits; reflexivity).
assert (I0 : room_shape_cf s0) by exact (rk_nt_inv _ _ N0 IV).
apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => st_sec_arr (snd r) = st_sec_arr s /\
  reg (snd r) kBatchClass = reg s kBatchClass /\ (fst r <> None -> errb_size_cf (snd r) = errb_size_cf s)).
- intros [ob s2] (A2 & R2 & E2). cbn [fst snd] in *. cbv zeta.
  destruct ob as [beg|]; cbv beta iota.
  + specialize (E2 ltac:(discriminate)).
    apply rk_bind. eapply ipost_mono; [|apply rk_depot]. intros [u3 s3] N3. cbn [fst snd] in *.
    apply rk_bind. eapply ipost_mono with (P := fun r => rk_nt s3 (snd r)).
    2:{ rk_if.
        - apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
          rk_if; [apply rk_ret; cbn [snd]; apply rk_nt_refl | apply rk_spin].
        - apply rk_ret. cbn [snd]. apply rk_nt_refl. }
    intros [u4 s4] N4. cbn [fst snd] in *.
    apply rk_bind. apply rk_modify. cbn [fst snd]. apply rk_ret. cbn [fst snd].
    pose proof (rk_nt_meas _ _ (rk_nt_trans _ _ _ N3 N4)) as (Rm & Em & Am).
    split; [transitivity (st_sec_arr s2); [exact Am | exact A2]|].
    split; [transitivity (reg s2 kBatchClass); [exact Rm | exact R2]|].
    intros _. transitivity (errb_size_cf s2); [exact Em | exact E2].
  + apply rk_ret. cbn [fst snd]. split; [exact A2|]. split; [exact R2|].
    intros Hf; exfalso; apply Hf; reflexivity.
- rewrite Fp. cbv beta iota.
  apply rk_bind. eapply ipost_mono; [|apply (rf_cache_alloc (chunk_class n) s0 ltac:(lia) Hn I0)].
  intros [o s2] (A2 & R2 & E2). cbn [fst snd] in *.
  apply rk_ret. cbn [fst snd]. destruct o as [off|]; cbv beta iota.
  + split; [exact A2|]. split; [exact R2 | intros _; apply E2; discriminate].
  + split; [exact A2|]. split; [exact R2 | intros Hf; exfalso; apply Hf; reflexivity].
Qed.

Theorem malloc_primary_step_cf : forall n tr s trc p s', room_shape_cf s -> from_primary n = true ->
chunk_class n <> kBatchClass -> apath (malloc_cf n tr s) trc (p, s') ->
st_sec_arr s' = st_sec_arr s /\ reg s' kBatchClass = reg s kBatchClass /\
(p <> PNull -> errb_size_cf s' = errb_size_cf s).
Proof.
intros n tr s trc p s' IV Fp Hn Hp.
exact (ipost_apath _ _ _ _ (rf_malloc_primary n tr s IV Fp Hn) Hp).
Qed.

(* A returning non-null primary malloc of a class other than kBatchClass costs NOTHING. *)
Theorem malloc_room_keep_primary_cf : forall k n tr s trc p s', room_shape_cf s -> from_primary n = true ->
chunk_class n <> kBatchClass -> ROOM_cf_k s k -> apath (malloc_cf n tr s) trc (p, s') -> p <> PNull ->
ROOM_cf_k s' k.
Proof.
intros k n tr s trc p s' IV Fp Hn R Hp HP.
destruct (malloc_primary_step_cf n tr s trc p s' IV Fp Hn Hp) as (A & Rg & E).
unfold ROOM_cf_k, ERRB_ROOM_k in *. rewrite A, Rg, (E HP). exact R.
Qed.

(* The PNull companion: the one class-full report, 100 bytes of error buffer; no secondary and no
   batch map, so the charge is the error buffer's alone. *)
Theorem malloc_room_keep_primary_null_cf : forall k n tr s trc p s', room_shape_cf s ->
from_primary n = true -> chunk_class n <> kBatchClass -> ROOM_cf_k s (Datatypes.S k) ->
apath (malloc_cf n tr s) trc (p, s') -> p = PNull -> ROOM_cf_k s' k.
Proof.
intros k n tr s trc p s' IV Fp Hn R Hp HP.
destruct (malloc_primary_step_cf n tr s trc p s' IV Fp Hn Hp) as (A & Rg & _).
destruct (malloc_step_cf n tr s trc p s' IV Hp) as (_ & _ & Eb & _).
unfold ROOM_cf_k, ERRB_ROOM_k in *. rewrite A, Rg. unfold kUserMapSize, kFreeArrayOffset, kPage in *.
split; [lia | split; lia].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The thread quarantine cache. enqueue and the drain's transfer are the only   *)
(*    writers of st_qthread; every other step of free_cf keeps it.                 *)
Definition qpr (s s' : astate) : Prop := st_qthread s' = st_qthread s.

Lemma qpr_refl : forall s, qpr s s.
Proof. intros s. reflexivity. Qed.
Lemma qpr_trans : forall s1 s2 s3, qpr s1 s2 -> qpr s2 s3 -> qpr s1 s3.
Proof. intros s1 s2 s3 A B. unfold qpr in *. congruence. Qed.

Lemma qpr_efa : forall c need sof s, ipost (ensure_free_array c need sof s) (fun r => qpr s (snd r)).
Proof.
intros c need sof s. unfold ensure_free_array. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- apply rk_ret. cbn [snd]. apply qpr_refl.
- apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
  destruct (aGranted z); cbv beta iota.
  + apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd]. reflexivity.
  + apply rk_bind. eapply ipost_mono with (P := fun r => qpr s (snd r)).
    2:{ destruct (aDestroyed z); cbv beta iota;
        [apply rk_set_region; cbn [snd]; reflexivity | apply rk_ret; cbn [snd]; apply qpr_refl]. }
    intros [u s1] H1. cbn [fst snd] in *.
    destruct sof; cbv beta iota; [apply rk_spin | apply rk_ret; exact H1].
Qed.

Lemma qpr_mmu : forall c need s, ipost (map_more_user c need s) (fun r => qpr s (snd r)).
Proof.
intros c need s. unfold map_more_user. cbv beta iota zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
  destruct (aGranted z); cbv beta iota.
  + apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd]. reflexivity.
  + apply rk_bind. eapply ipost_mono with (P := fun r => qpr s (snd r)).
    2:{ destruct (aDestroyed z); cbv beta iota;
        [apply rk_set_region; cbn [snd]; reflexivity | apply rk_ret; cbn [snd]; apply qpr_refl]. }
    intros [u s1] H1. cbn [fst snd] in *. apply rk_ret. cbn [snd]. exact H1.
- apply rk_ret. cbn [snd]. apply qpr_refl.
Qed.

Lemma qpr_populate : forall c need s, ipost (populate c need s) (fun r => qpr s (snd r)).
Proof.
intros c need s. unfold populate. cbv beta iota zeta.
apply rk_bind. eapply ipost_mono; [|apply qpr_mmu]. intros [ok s1] H1. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd].
  apply rk_bind. eapply ipost_mono; [|apply qpr_efa]. intros [ok2 s2] H2. cbn [fst snd] in *.
  destruct ok2; cbn [negb]; cbv beta iota.
  + apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_bind. apply rk_set_region. cbn [fst snd].
    apply rk_ret. cbn [snd]. exact (qpr_trans _ _ _ H1 H2).
  + apply rk_ret. cbn [snd]. exact (qpr_trans _ _ _ H1 H2).
- apply rk_ret. cbn [snd]. exact H1.
Qed.

Lemma qpr_gfa : forall c n s, ipost (get_from_allocator c n s) (fun r => qpr s (snd r)).
Proof.
intros c n s. unfold get_from_allocator. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => qpr s (snd r)).
2:{ rk_if; [apply qpr_populate | apply rk_ret; cbn [snd]; apply qpr_refl]. }
intros [ok s1] H1. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd]. rk_if.
  + apply rk_ret. cbn [snd]. exact H1.
  + match goal with |- context [fa_pop_n ?f ?a ?b ?l ?acc] => destruct (fa_pop_n f a b l acc) as [[tops rest]|] end;
    cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd]. exact H1.
    * apply rk_fail.
- apply rk_ret. cbn [snd]. exact H1.
Qed.

Lemma qpr_init : forall s, ipost (init_cache_if_needed s) (fun r => qpr s (snd r)).
Proof.
intros s. unfold init_cache_if_needed. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (st_cache_inited s); cbv beta iota; [apply rk_ret | apply rk_put]; cbn [snd]; reflexivity.
Qed.

Lemma qpr_refill : forall c s, ipost (refill_if_empty c s) (fun r => qpr s (snd r)).
Proof.
intros c s. unfold refill_if_empty. apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s c)) as [|x l]; cbv beta iota.
- apply rk_bind. eapply ipost_mono; [|apply qpr_gfa]. intros [got s1] H1. cbn [fst snd] in *.
  destruct got as [tops|]; cbv beta iota.
  + apply rk_set_pc. cbn [snd]. exact H1.
  + apply rk_ret. cbn [snd]. exact H1.
- apply rk_ret. cbn [snd]. apply qpr_refl.
Qed.

Lemma qpr_calloc : forall c s, ipost (cache_alloc c s) (fun r => qpr s (snd r)).
Proof.
intros c s. unfold cache_alloc. apply rk_bind. eapply ipost_mono; [|apply qpr_init].
intros [u s1] H1. cbn [fst snd] in *.
apply rk_bind. eapply ipost_mono; [|apply qpr_refill]. intros [u2 s2] H2. cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s2 c)) as [|x l]; cbv beta iota zeta.
- apply rk_ret. cbn [snd]. exact (qpr_trans _ _ _ H1 H2).
- apply rk_bind. apply rk_set_pc. cbn [fst snd]. apply rk_ret. cbn [snd]. exact (qpr_trans _ _ _ H1 H2).
Qed.

Lemma qpr_rta : forall c offs s, ipost (return_to_allocator c offs s) (fun r => qpr s (snd r)).
Proof.
intros c offs s. unfold return_to_allocator. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono; [|apply qpr_efa]. intros [u s1] H1. cbn [fst snd] in *.
apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_set_region. cbn [snd]. exact H1.
Qed.

Lemma qpr_cdealloc : forall c off s, ipost (cache_dealloc c off s) (fun r => qpr s (snd r)).
Proof.
intros c off s. unfold cache_dealloc. cbv zeta. apply rk_bind. eapply ipost_mono; [|apply qpr_init].
intros [u s1] H1. cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => qpr s1 (snd r)).
2:{ rk_if.
    - apply rk_bind. eapply ipost_mono; [|apply qpr_rta]. intros [u2 s2] H2. cbn [fst snd] in *.
      apply rk_set_pc. cbn [snd]. exact H2.
    - apply rk_ret. cbn [snd]. apply qpr_refl. }
intros [u3 s3] H3. cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd]. apply rk_set_pc. cbn [snd]. exact (qpr_trans _ _ _ H1 H3).
Qed.

Lemma qpr_sdealloc : forall r s, ipost (sec_dealloc r s) (fun x => qpr s (snd x)).
Proof.
intros r s. unfold sec_dealloc. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (nth_error (st_secs s) r) as [sm|] eqn:En; cbv beta iota; [|apply rk_fail].
destruct (index_of (st_sec_arr s) r 0%nat) as [i|]; cbv beta iota; [|apply rk_fail].
apply rk_bind. eapply ipost_mono with (P := fun x => snd x = s).
2:{ rk_if.
    - apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. rk_if; [apply rk_ret; reflexivity | apply rk_spin].
    - apply rk_ret. reflexivity. }
intros [u s1] E1. cbn [fst snd] in *. subst s1.
apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. apply rk_modify. cbn [snd]. cbv zeta. reflexivity.
Qed.

Lemma qpr_rchunk : forall k s, ipost (recycle_chunk k s) (fun r => qpr s (snd r)).
Proof.
intros k s. unfold recycle_chunk. apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
apply rk_bind. apply rk_put. cbn [fst snd].
destruct (ck_beg k) as [|off|r o|cid pos]; cbv beta iota.
- apply rk_fail.
- eapply ipost_mono; [|apply qpr_cdealloc]. intros [u s1] H1. cbn [snd] in *. exact H1.
- eapply ipost_mono; [|apply qpr_sdealloc]. intros [u s1] H1. cbn [snd] in *. exact H1.
- apply rk_fail.
Qed.

Lemma qpr_ritems : forall fuel items s, ipost (recycle_items fuel items s) (fun r => qpr s (snd r)).
Proof.
induction fuel as [|f IH]; intros [|k t] s; cbn [recycle_items].
- apply rk_ret. cbn [snd]. apply qpr_refl.
- apply rk_fail.
- apply rk_ret. cbn [snd]. apply qpr_refl.
- apply rk_bind. eapply ipost_mono; [|apply qpr_rchunk]. intros [u s1] H1. cbn [fst snd] in *.
  eapply ipost_mono; [|apply IH]. intros [u2 s2] H2. cbn [snd] in *. exact (qpr_trans _ _ _ H1 H2).
Qed.

Lemma qpr_drecycle : forall fuel bs s, ipost (do_recycle fuel bs s) (fun r => qpr s (snd r)).
Proof.
induction fuel as [|f IH]; intros [|b t] s; cbn [do_recycle].
- apply rk_ret. cbn [snd]. apply qpr_refl.
- apply rk_fail.
- apply rk_ret. cbn [snd]. apply qpr_refl.
- apply rk_bind. eapply ipost_mono; [|apply qpr_ritems]. intros [u s1] H1. cbn [fst snd] in *.
  apply rk_bind. eapply ipost_mono; [|apply qpr_cdealloc]. intros [u2 s2] H2. cbn [fst snd] in *.
  eapply ipost_mono; [|apply IH]. intros [u3 s3] H3. cbn [snd] in *.
  exact (qpr_trans _ _ _ H1 (qpr_trans _ _ _ H2 H3)).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. The slot measure of the thread cache: the free slots of its LAST batch      *)
(*    (kBatchSlots = 1,021 per batch), 0 when it holds no batch.                   *)
Definition slots_q (q : qcache) : nat :=
match rev (qc_list q) with [] => 0%nat | b :: _ => (1021 - length (b_items b))%nat end.
Definition slots_left (s : astate) : nat := slots_q (st_qthread s).

(* Every batch of the thread cache holds between 1 and kBatchSlots items. *)
Definition qt_wf_q (q : qcache) : Prop :=
match rev (qc_list q) with [] => True | b :: _ => (1 <= length (b_items b) <= 1021)%nat end.
Definition qt_wf (s : astate) : Prop := qt_wf_q (st_qthread s).

Definition qempty_q (q : qcache) : bool := match qc_list q with [] => true | _ => false end.

Lemma qempty_qc0 : qempty_q qc0 = true.
Proof. reflexivity. Qed.
Lemma slots_qc0 : slots_q qc0 = 0%nat.
Proof. reflexivity. Qed.
Lemma wf_qc0 : qt_wf_q qc0.
Proof. exact I. Qed.

Lemma slots_q_le : forall q, qt_wf_q q -> (slots_q q <= 1020)%nat.
Proof.
intros q W. unfold qt_wf_q in W. unfold slots_q.
destruct (rev (qc_list q)) as [|b t]; cbv beta iota in W |- *; lia.
Qed.

(* A slot left means no new batch; with the shape above, the converse holds too. *)
Lemma slots_pos_nonew : forall q, (1 <= slots_q q)%nat -> need_new_batch q = false.
Proof.
intros q H. unfold slots_q in H. unfold need_new_batch.
destruct (rev (qc_list q)) as [|b t]; cbv beta iota in H |- *; [exfalso; lia|].
apply Z.eqb_neq. unfold kBatchSlots. lia.
Qed.

Lemma nonew_slots_pos : forall q, qt_wf_q q -> need_new_batch q = false -> (1 <= slots_q q)%nat.
Proof.
intros q W H. unfold qt_wf_q in W. unfold need_new_batch in H. unfold slots_q.
destruct (rev (qc_list q)) as [|b t]; cbv beta iota in W, H |- *; [discriminate H|].
apply Z.eqb_neq in H. unfold kBatchSlots in H. lia.
Qed.

Lemma new_slots_zero : forall q, qt_wf_q q -> need_new_batch q = true -> slots_q q = 0%nat.
Proof.
intros q W H. unfold qt_wf_q in W. unfold need_new_batch in H. unfold slots_q.
destruct (rev (qc_list q)) as [|b t]; cbv beta iota in W, H |- *; [reflexivity|].
apply Z.eqb_eq in H. unfold kBatchSlots in H. lia.
Qed.

(* What qc_push (YG00.v:438-445) does to the three measures. *)
Lemma qc_bytes_push : forall q k nb, qc_bytes (qc_push q k nb) =
qc_bytes q + ck_n k + (match nb with Some _ => kBatchBytes | None => 0 end).
Proof. intros q k [bb|]; cbn [qc_push qc_bytes]; lia. Qed.

Lemma qempty_push_some : forall q k bb, qempty_q (qc_push q k (Some bb)) = false.
Proof. intros q k bb. unfold qempty_q. cbn [qc_push qc_list]. destruct (qc_list q); reflexivity. Qed.

Lemma qempty_push_none : forall q k, need_new_batch q = false -> qempty_q (qc_push q k None) = false.
Proof.
intros q k H. unfold need_new_batch in H. unfold qempty_q. cbn [qc_push qc_list].
destruct (rev (qc_list q)) as [|lb initr]; [discriminate H|]. destruct (rev initr); reflexivity.
Qed.

Lemma slots_push_some : forall q k bb, slots_q (qc_push q k (Some bb)) = 1020%nat.
Proof.
intros q k bb. unfold slots_q. cbn [qc_push qc_list]. rewrite rev_app_distr.
cbn [rev app b_items length]. reflexivity.
Qed.

Lemma slots_push_none : forall q k, need_new_batch q = false ->
slots_q (qc_push q k None) = (slots_q q - 1)%nat.
Proof.
intros q k H. unfold need_new_batch in H. unfold slots_q. cbn [qc_push qc_list].
destruct (rev (qc_list q)) as [|lb initr]; [discriminate H|].
rewrite rev_app_distr, rev_involutive. cbn [rev app b_items]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma wf_push_some : forall q k bb, qt_wf_q (qc_push q k (Some bb)).
Proof.
intros q k bb. unfold qt_wf_q. cbn [qc_push qc_list]. rewrite rev_app_distr.
cbn [rev app b_items length]. lia.
Qed.

Lemma wf_push_none : forall q k, qt_wf_q q -> need_new_batch q = false -> qt_wf_q (qc_push q k None).
Proof.
intros q k W H. unfold need_new_batch in H. unfold qt_wf_q in *. cbn [qc_push qc_list].
destruct (rev (qc_list q)) as [|lb initr]; [discriminate H|].
rewrite rev_app_distr, rev_involutive. cbn [rev app b_items]. rewrite length_app. cbn [length].
apply Z.eqb_neq in H. unfold kBatchSlots in H. cbv beta iota in W. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 6. One free: what it does to the thread cache.                                  *)
(* The enqueue pushes the quarantined chunk, with a NEW batch exactly when          *)
(* need_new_batch holds; then the drain either keeps the cache or transfers it      *)
(* whole to the global one (leaving qc0), and only when it passes                   *)
(* kQuarantineCacheMax = 2^20 bytes. *)
Definition qev (p : sptr) (s : astate) (q' : qcache) : Prop :=
exists (k : chunk) (nb : option Z),
find_user (st_chunks s) p = Some k /\
(need_new_batch (st_qthread s) = false -> nb = None) /\
(need_new_batch (st_qthread s) = true -> nb <> None) /\
(q' = qc_push (st_qthread s) (mkChunk (ck_beg k) (ck_req k) CQuarantined) nb \/
 (q' = qc0 /\ kQuarantineCacheMax <
   qc_bytes (qc_push (st_qthread s) (mkChunk (ck_beg k) (ck_req k) CQuarantined) nb))).

Lemma qev_cong : forall p s s2 q, st_chunks s2 = st_chunks s -> st_qthread s2 = st_qthread s ->
qev p s2 q -> qev p s q.
Proof.
intros p s s2 q C Q (k & nb & F & A & B & D). exists k. exists nb.
rewrite <- C, <- Q. split; [exact F|]. split; [exact A|]. split; [exact B | exact D].
Qed.

Lemma rf_depot : forall tr s, ipost (depot_put tr s)
(fun r => rk_nt s (snd r) /\ st_qthread (snd r) = st_qthread s /\ st_chunks (snd r) = st_chunks s).
Proof.
intros tr s. unfold depot_put. apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
rk_if.
- apply rk_ret. cbn [snd]. split; [apply rk_nt_refl | split; reflexivity].
- apply rk_bind. apply rk_get. cbn [fst snd].
  apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_put. cbn [snd]. split; [unfold rk_nt; rk_splits; reflexivity | split; reflexivity].
Qed.

Lemma rf_enqueue : forall k s, room_shape_cf s -> ipost (enqueue k s) (fun r =>
(exists nb, st_qthread (snd r) = qc_push (st_qthread s) k nb /\
   (need_new_batch (st_qthread s) = false -> nb = None) /\
   (need_new_batch (st_qthread s) = true -> nb <> None)) /\
st_sec_arr (snd r) = st_sec_arr s /\ errb_size_cf (snd r) = errb_size_cf s /\
rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize /\
(need_new_batch (st_qthread s) = false -> reg (snd r) kBatchClass = reg s kBatchClass)).
Proof.
intros k s IV. assert (KU : 0 <= kUserMapSize) by (unfold kUserMapSize; lia).
unfold enqueue. apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r =>
  st_qthread (snd r) = st_qthread s /\ st_sec_arr (snd r) = st_sec_arr s /\
  errb_size_cf (snd r) = errb_size_cf s /\
  rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize /\
  (need_new_batch (st_qthread s) = false -> fst r = None /\ reg (snd r) kBatchClass = reg s kBatchClass) /\
  (need_new_batch (st_qthread s) = true -> fst r <> None)).
2:{ destruct (need_new_batch (st_qthread s)) eqn:NB; cbv beta iota.
    - apply rk_bind.
      eapply ipost_mono; [|apply (ipost_and _ _ _ (rk_cache_alloc24 s IV) (qpr_calloc kBatchClass s))].
      intros [ob s1] [(I1 & S1 & A1 & M1) Q1]. cbn [fst snd] in *.
      destruct ob as [off|]; cbv beta iota; [|apply rk_spin].
      apply rk_ret. cbn [fst snd].
      assert (Eb1 : errb_size_cf s1 = errb_size_cf s) by (unfold errb_size_cf; rewrite S1; reflexivity).
      split; [exact Q1|]. split; [exact A1|]. split; [exact Eb1|]. split; [exact M1|].
      split; [intros Hf; discriminate Hf | intros _; discriminate].
    - apply rk_ret. cbn [fst snd].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      split; [intros _; split; reflexivity | intros Hf; discriminate Hf]. }
intros [nb s2] (Q2 & A2 & E2 & M2 & N2 & P2). cbn [fst snd] in *.
apply rk_modify. cbn [snd].
split.
- exists nb. rewrite Q2. split; [reflexivity|].
  split; [intros H; exact (proj1 (N2 H)) | exact P2].
- split; [exact A2|]. split; [exact E2|]. split; [exact M2 | intros H; exact (proj2 (N2 H))].
Qed.

Lemma rf_drain_q : forall s, ipost (maybe_drain_cf s) (fun r =>
st_qthread (snd r) = st_qthread s \/
(st_qthread (snd r) = qc0 /\ kQuarantineCacheMax < qc_bytes (st_qthread s))).
Proof.
intros s. unfold maybe_drain_cf. cbv zeta. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (Z.leb_spec (qc_bytes (st_qthread s)) kQuarantineCacheMax) as [Hle|Hgt]; cbv beta iota.
- apply rk_ret. cbn [snd]. left. reflexivity.
- apply rk_bind. apply rk_put. cbn [fst snd].
  rk_if.
  + apply rk_ret. cbn [snd]. right. split; [reflexivity | lia].
  + do 2 (match goal with |- context [match ?x with _ => _ end] => destruct x end).
    apply rk_bind. apply rk_modify. cbn [fst snd].
    eapply ipost_mono; [|apply qpr_drecycle]. intros [u s3] H3. cbn [snd] in *.
    right. split; [unfold qpr in H3; rewrite H3; reflexivity | lia].
Qed.

(* free_cf's enqueue side (its size test, Quarantine::Put): the block at p is at most kQuarantineMax. A block above it
   is recycled at once (a Theorem Labs lane's change 2026-10-30): it maps no batch and is not covered by this section's rules. *)
Definition free_small (p : sptr) (s : astate) : Prop :=
forall k, find_user (st_chunks s) p = Some k -> ck_n k <= kQuarantineMax.

Lemma rf_free_inner : forall p tr s, room_shape_cf s -> free_small p s ->
ipost ((s0 <- get ;;
  match find_user (st_chunks s0) p with
  | None => fail (FModel 11)
  | Some k =>
    (if match ck_state k with CAllocated => true | _ => false end then ret tt else fail (FModel 12)) ;;
    depot_put tr ;;
    let k' := mkChunk (ck_beg k) (ck_req k) CQuarantined in
    modify (fun s1 => set_chunks (upd_chunk (st_chunks s1) k') s1) ;;
    (if ck_n k' <=? kQuarantineMax then enqueue k' else recycle_chunk k') ;;
    maybe_drain_cf
  end) s)
(fun r => (length (st_sec_arr (snd r)) <= length (st_sec_arr s))%nat /\
errb_size_cf (snd r) = errb_size_cf s /\
rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize /\
(need_new_batch (st_qthread s) = false ->
   rg_mapped_user (reg (snd r) kBatchClass) = rg_mapped_user (reg s kBatchClass)) /\
qev p s (st_qthread (snd r))).
Proof.
intros p tr s IV HS. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (find_user (st_chunks s) p) as [k|] eqn:EF; cbv beta iota; [|apply rk_fail].
apply rk_bind. eapply ipost_mono with (P := fun r => snd r = s).
2:{ destruct (ck_state k); cbv beta iota; [apply rk_ret; reflexivity | apply rk_fail]. }
intros [u3 s3] E3. cbn [fst snd] in *. subst s3.
apply rk_bind. eapply ipost_mono; [|apply rf_depot]. intros [u4 s4] (N4 & Q4 & C4). cbn [fst snd] in *. cbv zeta.
apply rk_bind. apply rk_modify. cbn [fst snd].
match goal with |- context [if ?c then _ else _] => destruct c eqn:QS end;
  [|exfalso; apply Z.leb_gt in QS; pose proof (HS k EF) as HK; unfold ck_n in QS, HK; cbn [ck_req] in QS; lia].
set (s5 := set_chunks (upd_chunk (st_chunks s4) (mkChunk (ck_beg k) (ck_req k) CQuarantined)) s4).
assert (N5 : rk_nt s s5) by (eapply rk_nt_trans; [exact N4 | unfold rk_nt; rk_splits; reflexivity]).
assert (Q5 : st_qthread s5 = st_qthread s) by exact Q4.
pose proof (rk_nt_meas _ _ N5) as (R5 & Eb5 & Sa5).
apply rk_bind. eapply ipost_mono; [|apply rf_enqueue; exact (rk_nt_inv _ _ N5 IV)].
intros [u6 s6] ((nb & Q6 & NB6a & NB6b) & A6 & E6 & M6 & P6). cbn [fst snd] in *.
eapply ipost_mono; [|apply (ipost_and _ _ _ (rk_drain_fr s6) (rf_drain_q s6))].
intros [u7 s7] [(F7 & L7 & E7) D7]. cbn [snd] in *.
rewrite Q5 in Q6, NB6a, NB6b, P6. rewrite R5 in M6, P6.
split; [rewrite A6, Sa5 in L7; exact L7|].
split; [congruence|].
split; [rewrite (F7 kBatchClass); lia|].
split; [intros H; rewrite (F7 kBatchClass); rewrite (P6 H); reflexivity|].
exists k. exists nb. split; [exact EF|]. split; [exact NB6a|]. split; [exact NB6b|].
destruct D7 as [D|(D1 & D2)].
- left. rewrite D. exact Q6.
- right. split; [exact D1 | rewrite Q6 in D2; exact D2].
Qed.

Definition pnull (p : sptr) : bool := match p with PNull => true | _ => false end.

Theorem rf_free : forall p tr s, room_shape_cf s -> free_small p s -> ipost (free_cf p tr s) (fun r =>
(length (st_sec_arr (snd r)) <= length (st_sec_arr s))%nat /\ errb_size_cf (snd r) = errb_size_cf s /\
rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize /\
(need_new_batch (st_qthread s) = false ->
   rg_mapped_user (reg (snd r) kBatchClass) = rg_mapped_user (reg s kBatchClass)) /\
((pnull p = true /\ st_qthread (snd r) = st_qthread s) \/
 (pnull p = false /\ qev p s (st_qthread (snd r))))).
Proof.
intros p tr s IV HS. assert (KU : 0 <= kUserMapSize) by (unfold kUserMapSize; lia).
unfold free_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
set (s0 := set_nev (st_nev s + 1) s).
assert (N0 : rk_nt s s0) by (unfold rk_nt; rk_splits; reflexivity).
apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rk_nt s0 (snd r) /\
  st_qthread (snd r) = st_qthread s /\ st_chunks (snd r) = st_chunks s).
2:{ rk_if;
    [ apply rk_ret; cbn [snd]; (split; [apply rk_nt_refl | split; reflexivity])
    | apply rk_modify; cbn [snd]; (split; [unfold rk_nt; rk_splits; reflexivity | split; reflexivity])]. }
intros [u s2] (N2 & Q2 & C2). cbn [fst snd] in *.
pose proof (rk_nt_trans _ _ _ N0 N2) as N2'.
pose proof (rk_nt_inv _ _ N2' IV) as I2. pose proof (rk_nt_meas _ _ N2') as (R2 & E2 & A2).
assert (HS2 : free_small p s2) by (intros k Hk; apply HS; rewrite <- C2; exact Hk).
destruct p as [|off|r o|cid pos]; cbv beta iota.
- apply rk_ret. cbn [snd]. rewrite R2, E2, A2.
  split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [intros _; reflexivity|].
  left. split; [reflexivity | exact Q2].
- eapply ipost_mono; [|apply (rf_free_inner (PPrim off) tr s2 I2 HS2)].
  intros [u3 s3] (L & E & M & P & QE). cbn [snd] in *.
  rewrite R2 in M, P. rewrite E2 in E. rewrite A2 in L. rewrite Q2 in P.
  split; [exact L|]. split; [exact E|]. split; [exact M|]. split; [exact P|].
  right. split; [reflexivity | exact (qev_cong _ _ _ _ C2 Q2 QE)].
- eapply ipost_mono; [|apply (rf_free_inner (PSec r o) tr s2 I2 HS2)].
  intros [u3 s3] (L & E & M & P & QE). cbn [snd] in *.
  rewrite R2 in M, P. rewrite E2 in E. rewrite A2 in L. rewrite Q2 in P.
  split; [exact L|]. split; [exact E|]. split; [exact M|]. split; [exact P|].
  right. split; [reflexivity | exact (qev_cong _ _ _ _ C2 Q2 QE)].
- eapply ipost_mono; [|apply (rf_free_inner (PFake cid pos) tr s2 I2 HS2)].
  intros [u3 s3] (L & E & M & P & QE). cbn [snd] in *.
  rewrite R2 in M, P. rewrite E2 in E. rewrite A2 in L. rewrite Q2 in P.
  split; [exact L|]. split; [exact E|]. split; [exact M|]. split; [exact P|].
  right. split; [reflexivity | exact (qev_cong _ _ _ _ C2 Q2 QE)].
Qed.

Theorem free_step_q_cf : forall p tr s trc s', room_shape_cf s -> free_small p s -> apath (free_cf p tr s) trc (tt, s') ->
(length (st_sec_arr s') <= length (st_sec_arr s))%nat /\ errb_size_cf s' = errb_size_cf s /\
rg_mapped_user (reg s' kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize /\
(need_new_batch (st_qthread s) = false ->
   rg_mapped_user (reg s' kBatchClass) = rg_mapped_user (reg s kBatchClass)) /\
((pnull p = true /\ st_qthread s' = st_qthread s) \/ (pnull p = false /\ qev p s (st_qthread s'))).
Proof. intros p tr s trc s' IV HS Hp. exact (ipost_apath _ _ _ _ (rf_free p tr s IV HS) Hp). Qed.

(* ---------------------------------------------------------------------------- *)
(* 7. The free that costs nothing, and the per-free charge.                        *)
Theorem free_room_keep_nonew_cf : forall k p tr s trc s', room_shape_cf s -> free_small p s ->
need_new_batch (st_qthread s) = false -> ROOM_cf_k s k -> apath (free_cf p tr s) trc (tt, s') ->
ROOM_cf_k s' k.
Proof.
intros k p tr s trc s' IV HS NB R Hp.
destruct (free_step_q_cf p tr s trc s' IV HS Hp) as (L & E & _ & P & _).
unfold ROOM_cf_k, ERRB_ROOM_k in *. rewrite E, (P NB). split; [lia | split; lia].
Qed.

Theorem free_room_keep_null_cf : forall k tr s trc s', ROOM_cf_k s k ->
apath (free_cf PNull tr s) trc (tt, s') -> ROOM_cf_k s' k.
Proof.
intros k tr s trc s' R Hp. pose proof (ipost_apath _ _ _ _ (rk_free_null tr s) Hp) as N. cbn [snd] in N.
pose proof (rk_nt_meas _ _ N) as (Rg & E & A). unfold ROOM_cf_k, ERRB_ROOM_k in *.
rewrite Rg, E, A. exact R.
Qed.

(* The charge of ONE free: a batch can be allocated only by a free of a real block
   that opens a new batch. *)
Definition fcharge (p : sptr) (s : astate) : nat :=
if pnull p then 0%nat else (if need_new_batch (st_qthread s) then 1%nat else 0%nat).

Definition ftrans (p : sptr) (s' : astate) : nat :=
if pnull p then 0%nat else (if qempty_q (st_qthread s') then 1%nat else 0%nat).

Theorem free_charge_cf : forall k p tr s trc s', room_shape_cf s -> free_small p s ->
ROOM_cf_k s (fcharge p s + k) -> apath (free_cf p tr s) trc (tt, s') -> ROOM_cf_k s' k.
Proof.
intros k p tr s trc s' IV HS R Hp. unfold fcharge in R.
destruct p as [|off|r o|cid pos]; cbn [pnull] in R; cbv beta iota in R.
- exact (free_room_keep_null_cf k tr s trc s' R Hp).
- destruct (need_new_batch (st_qthread s)) eqn:NB; cbv beta iota in R;
  [exact (free_room_keep_cf k (PPrim off) tr s trc s' IV R Hp)
  |exact (free_room_keep_nonew_cf k (PPrim off) tr s trc s' IV HS NB R Hp)].
- destruct (need_new_batch (st_qthread s)) eqn:NB; cbv beta iota in R;
  [exact (free_room_keep_cf k (PSec r o) tr s trc s' IV R Hp)
  |exact (free_room_keep_nonew_cf k (PSec r o) tr s trc s' IV HS NB R Hp)].
- destruct (need_new_batch (st_qthread s)) eqn:NB; cbv beta iota in R;
  [exact (free_room_keep_cf k (PFake cid pos) tr s trc s' IV R Hp)
  |exact (free_room_keep_nonew_cf k (PFake cid pos) tr s trc s' IV HS NB R Hp)].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 8. The slot and byte facts of one free.                                         *)
Lemma qev_slots : forall p s q', qt_wf_q (st_qthread s) -> qev p s q' ->
qt_wf_q q' /\
(q' = qc0 \/
 ((need_new_batch (st_qthread s) = false -> slots_q q' = (slots_q (st_qthread s) - 1)%nat) /\
  (need_new_batch (st_qthread s) = true -> slots_q q' = 1020%nat) /\ qempty_q q' = false)).
Proof.
intros p s q' W (k & nb & _ & A & B & D).
destruct D as [D|(D1 & _)]; [|rewrite D1; split; [exact wf_qc0 | left; reflexivity]].
destruct nb as [bb|].
- assert (NB : need_new_batch (st_qthread s) = true).
  { destruct (need_new_batch (st_qthread s)) eqn:E; [reflexivity|]. exfalso. discriminate (A eq_refl). }
  rewrite D. split; [apply wf_push_some|]. right.
  split; [intros H; rewrite NB in H; discriminate H|].
  split; [intros _; apply slots_push_some | apply qempty_push_some].
- assert (NB : need_new_batch (st_qthread s) = false).
  { destruct (need_new_batch (st_qthread s)) eqn:E; [exfalso; exact (B eq_refl eq_refl) | reflexivity]. }
  rewrite D. split; [apply wf_push_none; assumption|]. right.
  split; [intros _; apply slots_push_none; exact NB|].
  split; [intros H; rewrite NB in H; discriminate H | apply qempty_push_none; exact NB].
Qed.

Theorem free_step_slots_cf : forall p tr s trc s', room_shape_cf s -> free_small p s -> qt_wf s ->
apath (free_cf p tr s) trc (tt, s') ->
qt_wf s' /\ (fcharge p s = 0%nat -> ((slots_left s <= slots_left s' + 1)%nat \/ ftrans p s' = 1%nat))
        /\ (fcharge p s = 1%nat -> (slots_left s' = 1020%nat \/ ftrans p s' = 1%nat)).
Proof.
intros p tr s trc s' IV HS W Hp.
destruct (free_step_q_cf p tr s trc s' IV HS Hp) as (_ & _ & _ & _ & QD).
pose proof (slots_q_le (st_qthread s) W) as SL.
unfold qt_wf, slots_left, ftrans, fcharge in *.
destruct QD as [(PN & QE)|(PN & QE)].
- rewrite PN, QE. cbv beta iota.
  split; [exact W|]. split; [intros _; left; lia | intros Hf; discriminate Hf].
- destruct (qev_slots p s (st_qthread s') W QE) as (W' & CASE). rewrite PN. cbv beta iota.
  split; [exact W'|].
  destruct CASE as [E0|(F0 & F1 & NE)].
  + rewrite E0, qempty_qc0. cbv beta iota.
    split; [intros _; right; reflexivity | intros _; right; reflexivity].
  + rewrite NE. cbv beta iota. split.
    * intros HC. destruct (need_new_batch (st_qthread s)) eqn:NB; cbv beta iota in HC;
      [discriminate HC|]. left. rewrite (F0 eq_refl). lia.
    * intros HC. destruct (need_new_batch (st_qthread s)) eqn:NB; cbv beta iota in HC;
      [left; exact (F1 eq_refl) | discriminate HC].
Qed.

(* The walk's own bound on the freed block: the model's ck_n of the block at p. *)
Definition free_bnd (b : Z) (p : sptr) (s : astate) : Prop :=
forall k, find_user (st_chunks s) p = Some k -> 0 <= ck_n k <= b.

Theorem free_step_bytes_cf : forall b p tr s trc s', room_shape_cf s -> free_small p s -> free_bnd b p s -> 0 <= b ->
apath (free_cf p tr s) trc (tt, s') ->
(ftrans p s' = 0%nat -> qc_bytes (st_qthread s') <= qc_bytes (st_qthread s) + (b + kBatchBytes)) /\
(ftrans p s' = 1%nat -> qc_bytes (st_qthread s') = 0 /\
                        kQuarantineCacheMax < qc_bytes (st_qthread s) + (b + kBatchBytes)) /\
(0 <= qc_bytes (st_qthread s) -> 0 <= qc_bytes (st_qthread s')).
Proof.
intros b p tr s trc s' IV HS BD Hb Hp.
destruct (free_step_q_cf p tr s trc s' IV HS Hp) as (_ & _ & _ & _ & QD).
assert (KB : 0 < kBatchBytes) by (unfold kBatchBytes; lia).
unfold ftrans.
destruct QD as [(PN & QE)|(PN & (k & nb & EF & A & B & D))].
- rewrite PN, QE. cbv beta iota.
  split; [intros _; lia|]. split; [intros Hf; discriminate Hf | intros H; exact H].
- destruct (BD k EF) as (Kn0 & Knb). rewrite PN. cbv beta iota.
  assert (CKN : ck_n (mkChunk (ck_beg k) (ck_req k) CQuarantined) = ck_n k) by reflexivity.
  assert (EP : qc_bytes (qc_push (st_qthread s) (mkChunk (ck_beg k) (ck_req k) CQuarantined) nb)
             <= qc_bytes (st_qthread s) + (b + kBatchBytes)).
  { rewrite qc_bytes_push, CKN. destruct nb; lia. }
  assert (EN : 0 <= qc_bytes (st_qthread s) ->
    0 <= qc_bytes (qc_push (st_qthread s) (mkChunk (ck_beg k) (ck_req k) CQuarantined) nb)).
  { intros H. rewrite qc_bytes_push, CKN. destruct nb; lia. }
  destruct D as [D|(D1 & D2)].
  + assert (NE : qempty_q (st_qthread s') = false).
    { rewrite D. destruct nb as [bb|]; [apply qempty_push_some|].
      apply qempty_push_none.
      destruct (need_new_batch (st_qthread s)) eqn:E; [exfalso; exact (B eq_refl eq_refl) | reflexivity]. }
    rewrite NE. cbv beta iota.
    split; [intros _; rewrite D; exact EP|].
    split; [intros Hf; discriminate Hf | intros H; rewrite D; exact (EN H)].
  + rewrite D1, qempty_qc0. cbv beta iota.
    split; [intros Hf; discriminate Hf|].
    split; [intros _; split; [reflexivity | lia] | intros _; cbn [qc_bytes qc0]; lia].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 9. A RUN of frees: n frees, c of them charged, t of them emptying the thread    *)
(*    cache (a transfer). room_shape_cf and the block bound are the walk's own, per *)
(*    call; nothing else is assumed.                                               *)
Inductive free_run (b : Z) : astate -> nat -> nat -> nat -> astate -> Prop :=
| frun_nil : forall s, free_run b s 0%nat 0%nat 0%nat s
| frun_step : forall s p tr trc s1 n c t s2,
    room_shape_cf s -> free_small p s -> free_bnd b p s -> apath (free_cf p tr s) trc (tt, s1) ->
    free_run b s1 n c t s2 ->
    free_run b s (S n) (fcharge p s + c)%nat (ftrans p s1 + t)%nat s2.

Theorem free_run_room_cf : forall b s n c t s', free_run b s n c t s' ->
forall k, ROOM_cf_k s (c + k) -> ROOM_cf_k s' k.
Proof.
intros b s n c t s' H. induction H as [s | s p tr trc s1 n c t s2 IV HSm BD Hp H IH]; intros k R.
- exact R.
- apply IH. apply (free_charge_cf (c + k) p tr s trc s1 IV HSm); [|exact Hp].
  rewrite Nat.add_assoc. exact R.
Qed.

Theorem free_run_wf_cf : forall b s n c t s', free_run b s n c t s' -> qt_wf s -> qt_wf s'.
Proof.
intros b s n c t s' H. induction H as [s | s p tr trc s1 n c t s2 IV HSm BD Hp H IH]; intros W.
- exact W.
- apply IH. exact (proj1 (free_step_slots_cf p tr s trc s1 IV HSm W Hp)).
Qed.

(* 1,021 charged frees need 1,021 frees each, unless the thread cache is transferred. *)
Theorem free_run_count_cf : forall b s n c t s', free_run b s n c t s' -> qt_wf s ->
(1021 * c + slots_left s <= n + 1020 + 1021 * t)%nat.
Proof.
intros b s n c t s' H. induction H as [s | s p tr trc s1 n c t s2 IV HSm BD Hp H IH]; intros W.
- pose proof (slots_q_le (st_qthread s) W) as SL. unfold slots_left. lia.
- destruct (free_step_slots_cf p tr s trc s1 IV HSm W Hp) as (W1 & C0 & C1).
  specialize (IH W1). pose proof (slots_q_le (st_qthread s) W) as SL. unfold slots_left in *.
  assert (FC : fcharge p s = 0%nat \/ fcharge p s = 1%nat).
  { unfold fcharge. destruct (pnull p); [left; reflexivity|].
    destruct (need_new_batch (st_qthread s)); [right; reflexivity | left; reflexivity]. }
  destruct FC as [FC|FC]; rewrite FC.
  + destruct (C0 FC) as [HS|HT]; [lia | rewrite HT; lia].
  + assert (Z0 : slots_q (st_qthread s) = 0%nat).
    { unfold fcharge in FC. destruct (pnull p); [discriminate FC|].
      destruct (need_new_batch (st_qthread s)) eqn:NB; [|discriminate FC].
      exact (new_slots_zero (st_qthread s) W NB). }
    destruct (C1 FC) as [HS|HT]; [rewrite HS in IH; lia | rewrite HT; lia].
Qed.

(* Each transfer needs kQuarantineCacheMax bytes of quarantine. *)
Theorem free_run_bytes_cf : forall b s n c t s', 0 <= b -> free_run b s n c t s' ->
0 <= qc_bytes (st_qthread s) ->
kQuarantineCacheMax * Z.of_nat t <= qc_bytes (st_qthread s) + Z.of_nat n * (b + kBatchBytes).
Proof.
intros b s n c t s' Hb H. induction H as [s | s p tr trc s1 n c t s2 IV HSm BD Hp H IH]; intros Q0.
- cbn [Z.of_nat]. unfold kQuarantineCacheMax. lia.
- destruct (free_step_bytes_cf b p tr s trc s1 IV HSm BD Hb Hp) as (B0 & B1 & BN).
  specialize (IH (BN Q0)). rewrite Nat2Z.inj_succ, Z.mul_succ_l.
  assert (FT : ftrans p s1 = 0%nat \/ ftrans p s1 = 1%nat).
  { unfold ftrans. destruct (pnull p); [left; reflexivity|].
    destruct (qempty_q (st_qthread s1)); [right; reflexivity | left; reflexivity]. }
  unfold kQuarantineCacheMax, kBatchBytes in *.
  destruct FT as [FT|FT]; rewrite FT.
  + specialize (B0 FT). rewrite Nat.add_0_l. lia.
  + destruct (B1 FT) as (BZ & BG). rewrite BZ in IH. rewrite Nat2Z.inj_add. cbn [Z.of_nat]. lia.
Qed.

(* The closed form a walk carries over a sequence of frees: with N frees of blocks of
   at most b bytes from a state with Q quarantined bytes in the thread cache,
   2^20 * 1,021 * C <= 2^20 * (N + 1,020) + 1,021 * (Q + N * (b + 8,192)),
   that is C <= N / 1,021 + N * (b + 8,192) / 2^20 + 1 (up to the constants). *)
Corollary free_run_charge_bound_cf : forall b s n c t s', 0 <= b -> qt_wf s ->
0 <= qc_bytes (st_qthread s) -> free_run b s n c t s' ->
kQuarantineCacheMax * (1021 * Z.of_nat c) <=
kQuarantineCacheMax * (Z.of_nat n + 1020) + 1021 * (qc_bytes (st_qthread s) + Z.of_nat n * (b + kBatchBytes)).
Proof.
intros b s n c t s' Hb W Q0 H.
pose proof (free_run_count_cf b s n c t s' H W) as HC.
pose proof (free_run_bytes_cf b s n c t s' Hb H Q0) as HB.
remember (Z.of_nat n * (b + kBatchBytes)) as X eqn:EX. clear EX.
unfold kQuarantineCacheMax in *. lia.
Qed.

End RF.
