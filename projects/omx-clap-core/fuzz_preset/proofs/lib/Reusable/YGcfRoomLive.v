(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30 (free_cf's size test, Quarantine::Put): rl_free_rff and c24_free cover free_cf's recycle side (rff_rchunk / rk_rchunk_fr); statements unchanged. *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the NON-PRIMARY ROOM AS A STATE
   INVARIANT, room_live_cf. Model and invariant lemmas only; no function is proved (rule 24). No address.
   WHY: ROOM_cf_k S k (YGcfRoomKeep.v:26-28) charges a whole kUserMapSize map of class kBatchClass per remaining call,
   so it is false for k > K_INIT = 14,335 in every state, while one LLVMFuzzerTestOneInput call charges at least
   9,696 and the harness runs it 1 to 4 times; a SUMMED per-call budget is unsatisfiable, so the non-primary room
   (the secondary count, the error buffer, the batch class) is a state invariant that each allocator call keeps.
   PRIMARY room (classes 1-30) is c-frame-alloc's room_at (PresetRoom.v); the two are complementary.
   room_live_cf S has three conjuncts, each with the headroom of RK_realloc = 2 calls:
   (a) length (st_sec_arr S) + 2 < cf_sec_live_max. Kept from Wf_cf + qtight at the call's start through
       sec_arr_bound_cf (st_sec_arr <= live_sec_blocks + QSEC_MAX), under the program's live-set premise
       rl_sec_ok: sec_cnt S (the live non-primary requests, = live_sec_blocks S by live_sec_blocks_req, the chunk ->
       request map) <= Lsec with Lsec + QSEC_MAX + 3 < cf_sec_live_max; a free adds no entry.
   (b) errb_size_cf S + 100 * rpot_all S <= ERRB_MAX_cf = 6,000, with a per-class report potential rpot in {0,1,2}.
       A report appends at most exh_len1 + exh_len2 c <= 100 bytes (exh_report_le_100) and is gated by the class's
       exhausted byte, which clear_exh_cf re-opens at the end of every successful populate_cf. It is still bounded:
       a refusal needs rg_mapped_user = kFreeArrayOffset (need * class_size <= 65,536 < kUserMapSize, and both are
       multiples of kUserMapSize: rl_full_of_refusal), and populate_cf carves ALL the uncarved room
       (new_cnt = (mapped - alloc) / size, YG00cf.v:189), so a full class has at most one more success and at most
       2 reports. Hence 2 reports x 30 reporting classes (class kBatchClass keeps cgif's arm and never reports)
       x 100 B. The brief's bound 100 * (31 + sum_c (kUserMapSize + kMaxSize) / class_size c), about 2.19 MB,
       was true but loose: it assumed one record per later success, while a success carves every uncarved record.
   (c) rg_mapped_user (reg S kBatchClass) + 3 * kUserMapSize <= kFreeArrayOffset: the class-24 HIGH-WATER mark that
       ROOM_cf's batch_room_cf reads (YG00cf.v:349-350); it never falls. Class kBatchClass maps only with an empty
       cache, an empty free array and no uncarved record (its refill target is max_cached 24 / 2 = 1), so by
       Compl0 the new mapped size is below kBatchBytes * (n24 S + 1) + kUserMapSize, n24 = the class's chunk
       records + the quarantine's batch objects at the call's start (m24_bound); under Wf_cf + qtight,
       n24 S <= ccnt24 S + N24Q (n24_bound, PresetRoom.v's room_ok terms), ccnt24 S = the live class-24 requests,
       under the premise rl_b24_ok. A bound from Wf_cf alone
       (batches_bound_cf, <= 458,752 = the whole class) does NOT give batch_room_cf.
   Results: room_live_room_k (ROOM_cf_k S RK_realloc), room_live_room (ROOM_cf S), room_live_cf_init_gen, the keeps
   room_live_malloc_keep / room_live_free_keep / room_live_realloc_keep / room_live_realloc_null_keep (and the
   acall_pre_cf forms RL_*_step), room_live_call_keep over one harness call rl_call (malloc_cf, free_cf, the realloc
   tree, realloc(NULL, n)), the fake-frame laws room_live_set_fs / room_live_stack_free (by conversion: room_live_cf
   reads no fake-stack field), and room_live_cf_step_gen, the driver-phase form (at most 3 live blocks); the parameter
   premise rl_param_ok
   (QSEC_MAX + 6 < cf_sec_live_max) holds for preset (16,000) and reply (8,192). The live-set premises are stated
   over L := map snd (blocks S), the form PresetLiveSec.v's live_sec_state / live_c24_state conclude. The preset
   statements under h-pre-b1's names are in lib/A/CfRoomLivePreset.v. ROOM_cf_k, RK_* and K_INIT are not changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK11 YM05 YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG02 YG04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfPath YGcfAmx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcfRoomKeep YGcfRoomStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0ncf YG0dcf ReallocP YGcfRealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfSecBound YG02cf YG03cf YG07cf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* 0. Constants.                                                                  *)
Definition ERRB_MAX_cf : Z := 6000.

(* The quarantine's class-kBatchClass chunks and batch objects, at most (PresetRoom.room_ok's terms). *)
Definition N24Q : Z := PresetRoom.QT / (PresetRoom.lo kBatchClass + 8) + PresetRoom.QT / kBatchBytes.

(* ---------------------------------------------------------------------------- *)
(* 1. The per-class report potential.                                             *)
(* 2 while the class is not full; once full, 1 if the exhausted byte is clear plus 1 if an uncarved record is left. *)
Definition rpot_of (c m a : Z) (e : bool) : Z :=
  if c =? kBatchClass then 0
  else if m <? kFreeArrayOffset then 2
  else (if e then 0 else 1) + (if class_size c <=? m - a then 1 else 0).

Definition rpot (s : astate) (c : Z) : Z :=
  rpot_of c (rg_mapped_user (reg s c)) (rg_alloc_user (reg s c)) (exh_mem_cf s c).

Fixpoint rsum (s : astate) (l : list Z) : Z :=
  match l with [] => 0 | c :: t => rpot s c + rsum s t end.

Definition rl_classes : list Z := map Z.of_nat (seq 1 31).
Definition rpot_all (s : astate) : Z := rsum s rl_classes.
Definition rl_phi (s : astate) : Z := errb_size_cf s + 100 * rpot_all s.

Lemma rpot_of_bounds : forall c m a e, 0 <= rpot_of c m a e <= 2.
Proof.
intros c m a e. unfold rpot_of. destruct (c =? kBatchClass); [lia|]. destruct (m <? kFreeArrayOffset); [lia|].
destruct e, (class_size c <=? m - a); lia.
Qed.

Lemma rpot_bounds : forall s c, 0 <= rpot s c <= 2.
Proof. intros s c. apply rpot_of_bounds. Qed.

Lemma rsum_nonneg : forall s l, 0 <= rsum s l.
Proof. intros s l. induction l as [|c t IH]; cbn [rsum]; [lia|]. pose proof (rpot_bounds s c). lia. Qed.

Lemma rpot_all_nonneg : forall s, 0 <= rpot_all s.
Proof. intros s. apply rsum_nonneg. Qed.

Lemma rsum_ext : forall s s' l, (forall c, In c l -> rpot s' c = rpot s c) -> rsum s' l = rsum s l.
Proof.
intros s s' l H. induction l as [|c t IH]; cbn [rsum]; [reflexivity|].
rewrite (H c (or_introl eq_refl)), IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma rsum_one : forall s s' c0 l, NoDup l -> In c0 l -> (forall c, In c l -> c <> c0 -> rpot s' c = rpot s c) ->
  rsum s' l - rpot s' c0 = rsum s l - rpot s c0.
Proof.
intros s s' c0 l Hnd. induction Hnd as [|c t Hnin Hnd IH]; intros Hin H; [destruct Hin|].
cbn [rsum]. destruct Hin as [<-|Hin].
- rewrite (rsum_ext s s' t); [lia|]. intros x Hx. apply H; [right; exact Hx|]. intros E. subst x. exact (Hnin Hx).
- assert (Hc : c <> c0) by (intros E; subst; exact (Hnin Hin)).
  rewrite (H c (or_introl eq_refl) Hc). specialize (IH Hin (fun x Hx Hne => H x (or_intror Hx) Hne)). lia.
Qed.

Lemma in_rl_classes : forall c, In c rl_classes <-> 1 <= c <= 31.
Proof.
intros c. unfold rl_classes. rewrite in_map_iff. split.
- intros (k & <- & Hk). apply in_seq in Hk. lia.
- intros Hc. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma rl_classes_nodup : NoDup rl_classes.
Proof.
unfold rl_classes. generalize (seq_NoDup 31 1). generalize (seq 1 31). intros l H.
induction H as [|x l Hx H IH]; cbn [map]; [constructor|]. constructor; [|exact IH].
rewrite in_map_iff. intros (y & E & Hy). apply Hx. replace x with y by lia. exact Hy.
Qed.

Lemma rpot_reg : forall s s' c, reg s' c = reg s c -> rpot s' c = rpot s c.
Proof. intros s s' c E. unfold rpot, exh_mem_cf. rewrite E. reflexivity. Qed.

Lemma rpot_24 : forall s, rpot s kBatchClass = 0.
Proof. intros s. unfold rpot, rpot_of. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma rpot_all_init : rpot_all init_state = 60.
Proof. vm_compute. reflexivity. Qed.

Lemma rl_phi_eq : forall s s', st_regions s' = st_regions s -> errb_size_cf s' = errb_size_cf s -> rl_phi s' = rl_phi s.
Proof.
intros s s' R E. unfold rl_phi, rpot_all. rewrite E, (rsum_ext s s'); [reflexivity|].
intros c _. apply rpot_reg. unfold reg. rewrite R. reflexivity.
Qed.

Lemma rl_phi_frame24 : forall s s', (forall x, 1 <= x -> x <> kBatchClass -> reg s' x = reg s x) ->
  errb_size_cf s' = errb_size_cf s -> rl_phi s' = rl_phi s.
Proof.
intros s s' F E. unfold rl_phi, rpot_all. rewrite E, (rsum_ext s s'); [reflexivity|].
intros c Hc. apply in_rl_classes in Hc. destruct (Z.eq_dec c kBatchClass) as [->|Hne].
- rewrite !rpot_24. reflexivity.
- apply rpot_reg. apply F; lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. Region updates and the exhausted byte.                                     *)
Lemma reg_upd_ne : forall s c r x, 1 <= x -> c <> x -> reg (set_regions (zupd c r (st_regions s)) s) x = reg s x.
Proof. intros s c r x Hx Hne. unfold reg, znth, zupd. cbn [st_regions set_regions]. apply nth_lupd_other. lia. Qed.

Lemma exh_add_other : forall h l, fst h <> EXH_HOLE ->
  existsb (fun h' => fst h' =? EXH_HOLE) (add_hole h l) = existsb (fun h' => fst h' =? EXH_HOLE) l.
Proof.
intros [o w] l Ho. cbn [fst] in Ho. unfold add_hole. cbn [existsb fst].
rewrite (proj2 (Z.eqb_neq o EXH_HOLE) Ho). cbn [orb].
induction l as [|h t IH]; [reflexivity|]. cbn [filter].
destruct (Z.eqb_spec (fst h) o) as [E|E]; cbn [negb existsb].
- rewrite IH, E, (proj2 (Z.eqb_neq o EXH_HOLE) Ho). reflexivity.
- rewrite IH. reflexivity.
Qed.

Lemma exh_del_other : forall o l, o <> EXH_HOLE ->
  existsb (fun h' => fst h' =? EXH_HOLE) (del_hole o l) = existsb (fun h' => fst h' =? EXH_HOLE) l.
Proof.
intros o l Ho. unfold del_hole. induction l as [|h t IH]; [reflexivity|]. cbn [filter].
destruct (Z.eqb_spec (fst h) o) as [E|E]; cbn [negb existsb].
- rewrite IH, E, (proj2 (Z.eqb_neq o EXH_HOLE) Ho). reflexivity.
- rewrite IH. reflexivity.
Qed.

(* A refused map leaves a class whose mapped size is kFreeArrayOffset: both are multiples of kUserMapSize. *)
Lemma rl_full_of_refusal : forall m, 0 <= m <= kFreeArrayOffset -> m mod kUserMapSize = 0 ->
  kFreeArrayOffset < m + kUserMapSize -> m = kFreeArrayOffset.
Proof.
intros m Hm Hal Hr. pose proof (Z.div_mod m kUserMapSize ltac:(unfold kUserMapSize; lia)) as D.
rewrite Hal in D. unfold kUserMapSize, kFreeArrayOffset in *. lia.
Qed.

(* A primary need is at most one kUserMapSize map. *)
Lemma rl_map_size : forall t, 0 < t <= kUserMapSize -> round_up t kUserMapSize = kUserMapSize.
Proof.
intros t Ht. pose proof (round_up_ge t kUserMapSize ltac:(unfold kUserMapSize; lia)) as [[H1 H2] H3].
pose proof (Z.div_mod (round_up t kUserMapSize) kUserMapSize ltac:(unfold kUserMapSize; lia)) as D.
rewrite H3 in D. unfold kUserMapSize in *. lia.
Qed.

(* A successful carve takes every uncarved record and clears the byte: the potential does not rise. *)
Lemma rpot_of_carve : forall c m a need, c <> kBatchClass -> 0 < class_size c -> 1 <= need ->
  a + need * class_size c <= m -> forall e,
  rpot_of c m (a + (m - a) / class_size c * class_size c) false <= rpot_of c m a e.
Proof.
intros c m a need H24 Hs Hn Hm e. unfold rpot_of.
rewrite (proj2 (Z.eqb_neq c kBatchClass) H24).
destruct (m <? kFreeArrayOffset); [lia|].
pose proof (Z.div_mod (m - a) (class_size c) ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (m - a) (class_size c) Hs) as B.
assert (Hge : class_size c <= m - a) by nia.
rewrite (proj2 (Z.leb_le _ _) Hge).
replace (class_size c <=? m - (a + (m - a) / class_size c * class_size c)) with false.
- destruct e; lia.
- symmetry. apply Z.leb_gt. nia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. All-paths helpers.                                                          *)
Lemma rl_ipost_and {A} (t : itree astate A) : forall (P Q : A -> Prop), ipost t P -> ipost t Q -> ipost t (fun a => P a /\ Q a).
Proof.
induction t as [a | q sn k IH | pc | f]; cbn [ipost]; intros P Q H1 H2.
- split; assumption.
- intros z. exact (IH z P Q (H1 z) (H2 z)).
- exact I.
- exact I.
Qed.

Lemma rl_apath_ibind {A B} : forall (t : itree astate A) (k : A -> itree astate B) tr b,
  apath (ibind t k) tr b -> exists tr1 tr2 a, apath t tr1 a /\ apath (k a) tr2 b.
Proof.
induction t as [a | q sn c IH | pc | f]; intros k tr b H; cbn [ibind] in H.
- exists [], tr, a. split; [reflexivity | exact H].
- destruct tr as [|[q' z] tr']; cbn [apath] in H; [destruct H|]. destruct H as (Eq & Hok & H).
  destruct (IH z k tr' b H) as (tr1 & tr2 & a & H1 & H2).
  exists ((q', z) :: tr1), tr2, a. split; [cbn [apath]; split; [exact Eq|]; split; [exact Hok | exact H1] | exact H2].
- destruct tr; cbn [apath] in H; destruct H.
- destruct tr; cbn [apath] in H; destruct H.
Qed.

Lemma rl_apath_ret {A} : forall (a : A) s tr r, apath (ret a s) tr r -> r = (a, s).
Proof. intros a s tr r H. destruct tr; cbn [apath ret] in H; [symmetry; exact H | destruct H]. Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. Frames: cgif's cache_alloc on a class c touches no other class's region,   *)
(*    and no step touches a region it does not name.                            *)
Definition rfr (c : Z) (s s' : astate) : Prop :=
  length (st_regions s') = length (st_regions s) /\ (forall x, 1 <= x -> x <> c -> reg s' x = reg s x) /\
  st_secs s' = st_secs s.

Lemma rfr_refl : forall c s, rfr c s s.
Proof. intros c s. split; [reflexivity|]. split; [intros; reflexivity | reflexivity]. Qed.

Lemma rfr_trans : forall c s1 s2 s3, rfr c s1 s2 -> rfr c s2 s3 -> rfr c s1 s3.
Proof.
intros c s1 s2 s3 (L1 & F1 & S1) (L2 & F2 & S2). split; [congruence|].
split; [intros x Hx Hn; rewrite F2, F1 by assumption; reflexivity | congruence].
Qed.

Lemma rfr_same : forall c s s', st_regions s' = st_regions s -> st_secs s' = st_secs s -> rfr c s s'.
Proof. intros c s s' R E. split; [rewrite R; reflexivity|]. split; [intros x _ _; unfold reg; rewrite R; reflexivity | exact E]. Qed.

Lemma rfr_set_region : forall c r s, rfr c s (set_regions (zupd c r (st_regions s)) s).
Proof.
intros c r s. split; [cbn [st_regions set_regions]; apply zupd_length|].
split; [intros x Hx Hne; apply reg_upd_ne; lia | reflexivity].
Qed.

Lemma rfr_efa : forall c need sof s, ipost (ensure_free_array c need sof s) (fun r => rfr c s (snd r)).
Proof.
intros c need sof s. unfold ensure_free_array. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- apply rk_ret. cbn [snd]. apply rfr_refl.
- apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
  destruct (aGranted z); cbv beta iota.
  + apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd]. apply rfr_set_region.
  + apply rk_bind. eapply ipost_mono with (P := fun r => rfr c s (snd r)).
    2:{ destruct (aDestroyed z); cbv beta iota;
        [apply rk_set_region; cbn [snd]; apply rfr_set_region | apply rk_ret; cbn [snd]; apply rfr_refl]. }
    intros [u s1] H1. cbn [fst snd] in *. destruct sof; cbv beta iota; [apply rk_spin | apply rk_ret; exact H1].
Qed.

Lemma rfr_mmu : forall c need s, ipost (map_more_user c need s) (fun r => rfr c s (snd r)).
Proof.
intros c need s. unfold map_more_user. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
  destruct (aGranted z); cbv beta iota.
  + apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd]. apply rfr_set_region.
  + apply rk_bind. eapply ipost_mono with (P := fun r => rfr c s (snd r)).
    2:{ destruct (aDestroyed z); cbv beta iota;
        [apply rk_set_region; cbn [snd]; apply rfr_set_region | apply rk_ret; cbn [snd]; apply rfr_refl]. }
    intros [u s1] H1. cbn [fst snd] in *. apply rk_ret. exact H1.
- apply rk_ret. cbn [snd]. apply rfr_refl.
Qed.

Lemma rfr_populate : forall c need s, ipost (populate c need s) (fun r => rfr c s (snd r)).
Proof.
intros c need s. unfold populate. cbv zeta.
apply rk_bind. eapply ipost_mono; [|apply rfr_mmu]. intros [ok s1] H1. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota; [|apply rk_ret; exact H1].
apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono; [|apply rfr_efa]. intros [ok2 s2] H2. cbn [fst snd] in *.
destruct ok2; cbn [negb]; cbv beta iota; [|apply rk_ret; exact (rfr_trans _ _ _ _ H1 H2)].
apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_bind. apply rk_set_region. cbn [fst snd].
apply rk_ret. cbn [snd]. exact (rfr_trans _ _ _ _ (rfr_trans _ _ _ _ H1 H2) (rfr_set_region _ _ _)).
Qed.

Lemma rfr_gfa : forall c n s, ipost (get_from_allocator c n s) (fun r => rfr c s (snd r)).
Proof.
intros c n s. unfold get_from_allocator. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rfr c s (snd r)).
2:{ rk_if; [apply rfr_populate | apply rk_ret; cbn [snd]; apply rfr_refl]. }
intros [ok s1] H1. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota; [|apply rk_ret; exact H1].
apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if; [apply rk_ret; exact H1|].
match goal with |- context [fa_pop_n ?f ?a ?b ?l ?acc] => destruct (fa_pop_n f a b l acc) as [[tops rest]|] end;
cbv beta iota; [|apply rk_fail].
apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
exact (rfr_trans _ _ _ _ H1 (rfr_set_region _ _ _)).
Qed.

Lemma rfr_init : forall c s, ipost (init_cache_if_needed s) (fun r => rfr c s (snd r)).
Proof.
intros c s. unfold init_cache_if_needed. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (st_cache_inited s); cbv beta iota;
[apply rk_ret; cbn [snd]; apply rfr_refl | apply rk_put; cbn [snd]; apply rfr_same; reflexivity].
Qed.

Lemma rfr_cache_alloc : forall c s, ipost (cache_alloc c s) (fun r => rfr c s (snd r)).
Proof.
intros c s. unfold cache_alloc. apply rk_bind. eapply ipost_mono; [|apply rfr_init]. intros [u s1] H1. cbn [fst snd] in *.
apply rk_bind. eapply ipost_mono with (P := fun r => rfr c s1 (snd r)).
2:{ unfold refill_if_empty. apply rk_bind. apply rk_get_pc. cbn [fst snd].
    destruct (pc_chunks (cache s1 c)); cbv beta iota; [|apply rk_ret; cbn [snd]; apply rfr_refl].
    apply rk_bind. eapply ipost_mono; [|apply rfr_gfa]. intros [got s2] H2. cbn [fst snd] in *.
    destruct got; cbv beta iota.
    - apply rk_set_pc. cbn [snd]. exact (rfr_trans _ _ _ _ H2 (rfr_same _ _ _ eq_refl eq_refl)).
    - apply rk_ret. exact H2. }
intros [u2 s2] H2. cbn [fst snd] in *. pose proof (rfr_trans _ _ _ _ H1 H2) as H12.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s2 c)); cbv beta iota zeta; [apply rk_ret; exact H12|].
apply rk_bind. apply rk_set_pc. cbn [fst snd]. apply rk_ret. cbn [snd].
exact (rfr_trans _ _ _ _ H12 (rfr_same _ _ _ eq_refl eq_refl)).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. The error buffer: one class's populate_cf, as a unit, does not raise        *)
(*    errb + 100 * rpot of that class, and touches no other class.              *)
Definition rb (c : Z) (s s' : astate) : Prop :=
  length (st_regions s') = length (st_regions s) /\
  (forall x, 1 <= x -> x <> c -> reg s' x = reg s x) /\
  0 <= errb_size_cf s' /\
  errb_size_cf s' + 100 * rpot s' c <= errb_size_cf s + 100 * rpot s c /\
  (0 <= rg_mapped_fa (reg s c) -> 0 <= rg_mapped_fa (reg s' c)).

Lemma rb_refl : forall c s, 0 <= errb_size_cf s -> rb c s s.
Proof.
intros c s H. split; [reflexivity|]. split; [intros; reflexivity|]. split; [exact H|]. split; [lia | intros F; exact F].
Qed.

Lemma rb_trans : forall c s1 s2 s3, rb c s1 s2 -> rb c s2 s3 -> rb c s1 s3.
Proof.
intros c s1 s2 s3 (L1 & F1 & E1 & P1 & M1) (L2 & F2 & E2 & P2 & M2).
split; [congruence|]. split; [intros x Hx Hn; rewrite F2, F1 by assumption; reflexivity|].
split; [exact E2|]. split; [lia | intros H; exact (M2 (M1 H))].
Qed.

Lemma rb_same : forall c s s', st_regions s' = st_regions s -> st_secs s' = st_secs s -> 0 <= errb_size_cf s -> rb c s s'.
Proof.
intros c s s' R E He. assert (Er : forall x, reg s' x = reg s x) by (intros x; unfold reg; rewrite R; reflexivity).
assert (Eb : errb_size_cf s' = errb_size_cf s) by (unfold errb_size_cf; rewrite E; reflexivity).
split; [rewrite R; reflexivity|]. split; [intros x _ _; apply Er|]. rewrite Eb. split; [exact He|].
split; [rewrite (rpot_reg s s' c (Er c)); lia | rewrite Er; intros H; exact H].
Qed.

Lemma rb_set_le : forall c r s, 1 <= c -> (Z.to_nat c < length (st_regions s))%nat -> 0 <= errb_size_cf s ->
  rpot_of c (rg_mapped_user r) (rg_alloc_user r) (existsb (fun h => fst h =? EXH_HOLE) (rg_holes r)) <= rpot s c ->
  (0 <= rg_mapped_fa (reg s c) -> 0 <= rg_mapped_fa r) ->
  rb c s (set_regions (zupd c r (st_regions s)) s).
Proof.
intros c r s Hc Hl He Hp Hf.
assert (Er : reg (set_regions (zupd c r (st_regions s)) s) c = r) by (apply reg_upd_same; [lia | exact Hl]).
split; [cbn [st_regions set_regions]; apply zupd_length|].
split; [intros x Hx Hne; apply reg_upd_ne; lia|].
change (errb_size_cf (set_regions (zupd c r (st_regions s)) s)) with (errb_size_cf s).
split; [exact He|]. split.
- assert (Rp : rpot (set_regions (zupd c r (st_regions s)) s) c =
    rpot_of c (rg_mapped_user r) (rg_alloc_user r) (existsb (fun h => fst h =? EXH_HOLE) (rg_holes r)))
    by (unfold rpot, exh_mem_cf; rewrite Er; reflexivity).
  lia.
- rewrite Er. exact Hf.
Qed.

Lemma rb_set_same : forall c r s, 1 <= c -> (Z.to_nat c < length (st_regions s))%nat -> 0 <= errb_size_cf s ->
  rg_mapped_user r = rg_mapped_user (reg s c) -> rg_alloc_user r = rg_alloc_user (reg s c) ->
  rg_holes r = rg_holes (reg s c) -> rg_mapped_fa r = rg_mapped_fa (reg s c) ->
  rb c s (set_regions (zupd c r (st_regions s)) s).
Proof.
intros c r s Hc Hl He E1 E2 E3 E4. apply rb_set_le; try assumption.
- rewrite E1, E2, E3. unfold rpot, exh_mem_cf. lia.
- rewrite E4. intros H; exact H.
Qed.

Lemma rl_phi_rb : forall c s s', 1 <= c <= 31 -> rb c s s' -> rl_phi s' <= rl_phi s.
Proof.
intros c s s' Hc (L & F & E & P & M). unfold rl_phi, rpot_all.
assert (H : rsum s' rl_classes - rpot s' c = rsum s rl_classes - rpot s c).
{ apply rsum_one; [exact rl_classes_nodup | exact (proj2 (in_rl_classes c) Hc)|].
  intros x Hx Hne. apply in_rl_classes in Hx. apply rpot_reg. apply F; lia. }
lia.
Qed.

(* The carve-and-clear tail of a successful populate_cf. *)
Lemma rb_carve_clear : forall c y y2 s3 s4 cnt need,
  1 <= c <= 31 -> c <> kBatchClass -> (Z.to_nat c < length (st_regions y2))%nat -> 0 < class_size c -> 1 <= need ->
  length (st_regions y2) = length (st_regions y) -> (forall w, 0 <= w -> w <> c -> reg y2 w = reg y w) ->
  errb_size_cf y2 = errb_size_cf y -> 0 <= errb_size_cf y -> 0 <= rg_mapped_fa (reg y2 c) ->
  rg_mapped_user (reg y2 c) = rg_mapped_user (reg y c) -> rg_alloc_user (reg y2 c) = rg_alloc_user (reg y c) ->
  rg_alloc_user (reg y c) + need * class_size c <= rg_mapped_user (reg y c) ->
  cnt = (rg_mapped_user (reg y c) - rg_alloc_user (reg y c)) / class_size c ->
  s3 = set_regions (zupd c (mkRegion (rg_mapped_user (reg y2 c)) (rg_alloc_user (reg y2 c) + cnt * class_size c)
         (rg_mapped_fa (reg y2 c)) (FRun (rg_alloc_user (reg y2 c)) cnt :: rg_free (reg y2 c)) (rg_holes (reg y2 c)))
         (st_regions y2)) y2 ->
  s4 = set_regions (zupd c (mkRegion (rg_mapped_user (reg s3 c)) (rg_alloc_user (reg s3 c)) (rg_mapped_fa (reg s3 c))
         (rg_free (reg s3 c)) (del_hole EXH_HOLE (rg_holes (reg s3 c)))) (st_regions s3)) s3 ->
  rb c y s4.
Proof.
intros c y y2 s3 s4 cnt need Hc H24 Hl Ks Hn L2 F2 E2 He FA2 Mp Al Hm Hcnt E3 E4.
assert (L3 : (Z.to_nat c < length (st_regions s3))%nat)
  by (rewrite E3; cbn [st_regions set_regions]; rewrite zupd_length; exact Hl).
assert (R3 : reg s3 c = mkRegion (rg_mapped_user (reg y2 c)) (rg_alloc_user (reg y2 c) + cnt * class_size c)
         (rg_mapped_fa (reg y2 c)) (FRun (rg_alloc_user (reg y2 c)) cnt :: rg_free (reg y2 c)) (rg_holes (reg y2 c)))
  by (rewrite E3; apply reg_upd_same; [lia | exact Hl]).
assert (R4 : reg s4 c = mkRegion (rg_mapped_user (reg y2 c)) (rg_alloc_user (reg y2 c) + cnt * class_size c)
         (rg_mapped_fa (reg y2 c)) (FRun (rg_alloc_user (reg y2 c)) cnt :: rg_free (reg y2 c))
         (del_hole EXH_HOLE (rg_holes (reg y2 c)))).
{ rewrite E4. rewrite reg_upd_same by (first [lia | exact L3]). rewrite R3. reflexivity. }
assert (F4 : forall w, 1 <= w -> w <> c -> reg s4 w = reg y w).
{ intros w Hw Hne. rewrite E4. rewrite reg_upd_ne by lia. rewrite E3. rewrite reg_upd_ne by lia. apply F2; lia. }
assert (L4 : length (st_regions s4) = length (st_regions y)).
{ rewrite E4. cbn [st_regions set_regions]. rewrite zupd_length, E3. cbn [st_regions set_regions]. rewrite zupd_length. exact L2. }
assert (Eb4 : errb_size_cf s4 = errb_size_cf y) by (rewrite E4, E3; exact E2).
assert (P4 : rpot s4 c = rpot_of c (rg_mapped_user (reg y c)) (rg_alloc_user (reg y c) + cnt * class_size c) false).
{ unfold rpot, exh_mem_cf. rewrite R4. cbn [rg_mapped_user rg_alloc_user rg_holes]. rewrite del_hole_exh, Mp, Al. reflexivity. }
split; [exact L4|]. split; [exact F4|]. rewrite Eb4. split; [exact He|]. split.
- rewrite P4, Hcnt. unfold rpot.
  pose proof (rpot_of_carve c (rg_mapped_user (reg y c)) (rg_alloc_user (reg y c)) need H24 Ks Hn Hm (exh_mem_cf y c)). lia.
- rewrite R4. cbn [rg_mapped_fa]. intros _. exact FA2.
Qed.

(* The class facts Wf_cf gives. *)
Lemma rl_cls_facts {cp : CfParams} : forall U s c, Wf_cf U s -> 1 <= c <= 31 ->
  (0 <= rg_alloc_user (reg s c) <= rg_mapped_user (reg s c)) /\ rg_mapped_user (reg s c) <= kFreeArrayOffset /\
  rg_mapped_user (reg s c) mod kUserMapSize = 0 /\ 0 <= rg_mapped_fa (reg s c) /\ 0 <= fa_len (rg_free (reg s c)) /\
  (st_cache_inited s = true -> pc_max (cache s c) = max_cached c).
Proof.
intros U s c W Hc. pose proof (wfc_classes _ _ _ _ _ W c Hc) as CL. unfold wf_class_cf in CL.
split; [exact (wrc_alloc _ _ _ _ _ _ CL)|]. split; [exact (wrc_mapped_bound _ _ _ _ _ _ CL)|].
split; [exact (wrc_mapped_al _ _ _ _ _ _ CL)|]. split; [exact (proj1 (wrc_fa _ _ _ _ _ _ CL))|].
split; [exact (fa_len_nonneg _ (wrc_runs _ _ _ _ _ _ CL))|].
intros Ei. pose proof (wrc_cache _ _ _ _ _ _ CL) as HC. rewrite Ei in HC. exact (proj1 HC).
Qed.

Section B. Context {ci : CfImg}.

(* A report adds nothing when the class's byte is set. *)
Lemma rl_errb_report : forall c s, ipost (errb_report_cf c s)
  (fun r => rk_nosec s (snd r) /\ (0 <= errb_size_cf s -> 0 <= errb_size_cf (snd r) <=
     errb_size_cf s + (if exh_mem_cf s c then 0 else exh_len1 + exh_len2 c))).
Proof.
intros c s. pose proof (exh_len2_nonneg c) as X. unfold errb_report_cf. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (exh_mem_cf s c); cbv beta iota.
- apply rk_ret. cbn [snd]. split; [unfold rk_nosec; rk_splits; reflexivity | lia].
- apply rk_bind. eapply ipost_mono; [|apply rk_errb_append; unfold exh_len1; lia]. intros [u s1] [F1 E1]. cbn [fst snd] in *.
  eapply ipost_mono; [|apply rk_errb_append; exact X]. intros [u2 s2] [F2 E2]. cbn [snd] in *.
  split; [eapply rk_nosec_trans; [exact F1 | exact F2]|]. intros H0. unfold exh_len1 in *.
  specialize (E1 H0). specialize (E2 ltac:(lia)). lia.
Qed.

(* ensure_free_array keeps the class's counts and, at a non-negative free-array size, its byte. *)
Lemma rl_efa : forall c need sof s, 0 <= c -> (Z.to_nat c < length (st_regions s))%nat -> 0 <= rg_mapped_fa (reg s c) ->
  ipost (ensure_free_array c need sof s) (fun r => rk_efa c s (snd r) /\
    exh_mem_cf (snd r) c = exh_mem_cf s c /\ 0 <= rg_mapped_fa (reg (snd r) c)).
Proof.
intros c need sof s Hc Hl Hfa. unfold ensure_free_array. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
destruct (4 * need <=? rg_mapped_fa (reg s c)) eqn:Ek; cbv beta iota.
- apply rk_ret. cbn [snd]. split; [apply rk_efa_refl | split; [reflexivity | exact Hfa]].
- apply Z.leb_gt in Ek.
  apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
  destruct (aGranted z); cbv beta iota.
  + apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
    split; [apply rk_efa_set; try assumption; reflexivity|].
    unfold exh_mem_cf. rewrite !reg_upd_same by assumption. cbn [rg_holes rg_mapped_fa].
    split; [apply exh_del_other; unfold EXH_HOLE, kFreeArrayOffset; lia|].
    pose proof (round_up_ge (4 * need) kFreeArrayMapSize ltac:(unfold kFreeArrayMapSize; lia)) as [[R1 R2] _]. lia.
  + apply rk_bind. eapply ipost_mono with (P := fun r => rk_efa c s (snd r) /\
      exh_mem_cf (snd r) c = exh_mem_cf s c /\ 0 <= rg_mapped_fa (reg (snd r) c)).
    2:{ destruct (aDestroyed z); cbv beta iota.
        - apply rk_set_region. cbn [snd]. split; [apply rk_efa_set; try assumption; reflexivity|].
          unfold exh_mem_cf. rewrite !reg_upd_same by assumption. cbn [rg_holes rg_mapped_fa].
          split; [apply exh_add_other; cbn [fst]; unfold EXH_HOLE, kFreeArrayOffset; lia | exact Hfa].
        - apply rk_ret. cbn [snd]. split; [apply rk_efa_refl | split; [reflexivity | exact Hfa]]. }
    intros [u s1] H1. cbn [fst snd] in *. destruct sof; cbv beta iota; [apply rk_spin | apply rk_ret; exact H1].
Qed.

(* map_more_user_cf on a class other than kBatchClass. A refusal needs a full class (rl_full_of_refusal); its
   report is paid by the potential: the byte is set, so rpot falls by 1 exactly when the report prints. *)
Lemma rl_mmu_cf : forall c need x, 1 <= c <= 31 -> c <> kBatchClass ->
  (Z.to_nat c < length (st_regions x))%nat ->
  0 <= rg_alloc_user (reg x c) <= rg_mapped_user (reg x c) -> rg_mapped_user (reg x c) <= kFreeArrayOffset ->
  rg_mapped_user (reg x c) mod kUserMapSize = 0 -> 1 <= need -> need * class_size c <= kUserMapSize ->
  0 <= errb_size_cf x ->
  ipost (map_more_user_cf c need x) (fun r => rb c x (snd r) /\
    rg_alloc_user (reg (snd r) c) = rg_alloc_user (reg x c) /\
    (fst r = true -> rg_alloc_user (reg x c) + need * class_size c <= rg_mapped_user (reg (snd r) c))).
Proof.
intros c need x Hc H24 Hl [Ha0 Ham] Hmb Hal Hn Hns He.
pose proof (class_ok c Hc) as (Ks & _).
assert (HE : exh_len1 + exh_len2 c <= 100) by (apply exh_report_le_100; lia).
pose proof (exh_len2_nonneg c) as X2.
assert (Hc24 : (c =? kBatchClass) = false) by (apply Z.eqb_neq; exact H24).
unfold map_more_user_cf. rewrite Hc24. cbv beta iota zeta.
apply rk_bind. apply rk_get_region. cbn [fst snd].
destruct (Z.ltb_spec (rg_mapped_user (reg x c)) (rg_alloc_user (reg x c) + need * class_size c)) as [Hlt|Hge];
cbv beta iota.
- rewrite (rl_map_size (rg_alloc_user (reg x c) + need * class_size c - rg_mapped_user (reg x c))) by lia.
  destruct (Z.leb_spec (rg_mapped_user (reg x c) + kUserMapSize) kFreeArrayOffset) as [Hfit|Hfull]; cbv beta iota.
  + assert (R2 : rpot x c = 2).
    { unfold rpot, rpot_of. rewrite Hc24.
      replace (rg_mapped_user (reg x c) <? kFreeArrayOffset) with true; [reflexivity|].
      symmetry. apply Z.ltb_lt. unfold kUserMapSize in *. lia. }
    apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
    destruct (aGranted z); cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [fst snd].
      split; [apply rb_set_le; [lia | exact Hl | exact He | rewrite R2; apply (proj2 (rpot_of_bounds _ _ _ _)) |
        cbn [rg_mapped_fa]; intros H; exact H]|].
      rewrite reg_upd_same by lia. cbn [rg_alloc_user rg_mapped_user]. split; [reflexivity | intros _; lia].
    * apply rk_bind. eapply ipost_mono with (P := fun r => rb c x (snd r) /\
        rg_alloc_user (reg (snd r) c) = rg_alloc_user (reg x c)).
      2:{ destruct (aDestroyed z); cbv beta iota.
          - apply rk_set_region. cbn [snd].
            split; [apply rb_set_le; [lia | exact Hl | exact He | rewrite R2; apply (proj2 (rpot_of_bounds _ _ _ _)) |
              cbn [rg_mapped_fa]; intros H; exact H]|].
            rewrite reg_upd_same by lia. reflexivity.
          - apply rk_ret. cbn [snd]. split; [apply rb_refl; exact He | reflexivity]. }
      intros [u s1] [B1 A1]. cbn [fst snd] in *. apply rk_ret. cbn [fst snd].
      split; [exact B1|]. split; [exact A1 | intros H; discriminate H].
  + assert (Efull : rg_mapped_user (reg x c) = kFreeArrayOffset) by (apply rl_full_of_refusal; [lia | exact Hal | exact Hfull]).
    apply rk_bind. eapply ipost_mono; [|apply rl_errb_report]. intros [u s1] [N1 E1]. cbn [fst snd] in *.
    pose proof N1 as (R1 & C1 & I1 & A1).
    assert (Rg1 : forall w, reg s1 w = reg x w) by (intros w; unfold reg; rewrite R1; reflexivity).
    unfold set_exh_cf. apply rk_bind. apply rk_bind. apply rk_get_region. cbn [fst snd].
    apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [fst snd].
    match goal with |- context [set_regions (zupd c ?r (st_regions s1)) s1] =>
      set (y := set_regions (zupd c r (st_regions s1)) s1);
      assert (Ey : reg y c = r) by (apply reg_upd_same; [lia | rewrite R1; exact Hl]) end.
    assert (Fy : forall w, 1 <= w -> w <> c -> reg y w = reg x w)
      by (intros w Hw Hne; unfold y; rewrite reg_upd_ne by lia; apply Rg1).
    assert (Ly : length (st_regions y) = length (st_regions x))
      by (unfold y; cbn [st_regions set_regions]; rewrite zupd_length, R1; reflexivity).
    assert (Eby : errb_size_cf y = errb_size_cf s1) by reflexivity.
    assert (Py : rpot y c = rpot_of c (rg_mapped_user (reg x c)) (rg_alloc_user (reg x c)) true).
    { unfold rpot, exh_mem_cf. rewrite Ey. cbn [rg_mapped_user rg_alloc_user rg_holes]. rewrite add_hole_exh, Rg1. reflexivity. }
    specialize (E1 He).
    split; [split; [exact Ly|]; split; [exact Fy|]; rewrite Eby; split; [lia|]; split|].
    * rewrite Py. unfold rpot, rpot_of. rewrite Hc24, Efull, Z.ltb_irrefl.
      destruct (exh_mem_cf x c); destruct (class_size c <=? kFreeArrayOffset - rg_alloc_user (reg x c)); lia.
    * rewrite Ey. cbn [rg_mapped_fa]. rewrite Rg1. intros H; exact H.
    * rewrite Ey. cbn [rg_alloc_user]. rewrite Rg1. split; [reflexivity | intros H; discriminate H].
- apply rk_ret. cbn [fst snd]. split; [apply rb_refl; exact He|]. split; [reflexivity | intros _; lia].
Qed.

Lemma rl_populate_cf : forall c need x, 1 <= c <= 31 -> c <> kBatchClass ->
  (Z.to_nat c < length (st_regions x))%nat ->
  0 <= rg_alloc_user (reg x c) <= rg_mapped_user (reg x c) -> rg_mapped_user (reg x c) <= kFreeArrayOffset ->
  rg_mapped_user (reg x c) mod kUserMapSize = 0 -> 0 <= rg_mapped_fa (reg x c) ->
  1 <= need -> need * class_size c <= kUserMapSize -> 0 <= errb_size_cf x ->
  ipost (populate_cf c need x) (fun r => rb c x (snd r)).
Proof.
intros c need x Hc H24 Hl Ha Hmb Hal Hfa Hn Hns He.
pose proof (class_ok c Hc) as (Ks & _).
assert (Hc24 : (c =? kBatchClass) = false) by (apply Z.eqb_neq; exact H24).
unfold populate_cf. rewrite Hc24. cbv beta iota zeta.
apply rk_bind. eapply ipost_mono; [|apply rl_mmu_cf; assumption]. intros [ok y] (B1 & A1 & T1). cbn [fst snd] in *.
pose proof B1 as (L1 & F1 & E1 & P1 & M1).
destruct ok; cbn [negb]; cbv beta iota.
2:{ apply rk_ret. cbn [snd]. exact B1. }
specialize (T1 eq_refl).
apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono; [|apply (rl_efa c _ false y); [lia | rewrite L1; exact Hl | exact (M1 Hfa)]].
intros [ok2 y2] (EF & X2 & FA2). cbn [fst snd] in *.
pose proof EF as (L2 & O2 & Mp2 & Al2 & Fr2 & C2 & In2 & Se2 & Sa2).
assert (Eb2 : errb_size_cf y2 = errb_size_cf y) by (unfold errb_size_cf; rewrite Se2; reflexivity).
destruct ok2; cbn [negb]; cbv beta iota.
2:{ apply rk_ret. cbn [snd]. eapply rb_trans; [exact B1|].
    split; [exact L2|]. split; [intros w Hw Hne; apply O2; lia|]. rewrite Eb2. split; [exact E1|].
    split; [|intros _; exact FA2].
    assert (Rp : rpot y2 c = rpot y c) by (unfold rpot; rewrite Mp2, Al2, X2; reflexivity). lia. }
apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. apply rk_set_region. cbn [fst snd].
apply rk_bind. unfold clear_exh_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
eapply rb_trans; [exact B1|].
eapply (rb_carve_clear c y y2); [exact Hc | exact H24 | rewrite L2, L1; exact Hl | exact Ks | exact Hn | exact L2 |
  exact O2 | exact Eb2 | exact E1 | exact FA2 | exact Mp2 | exact Al2 | rewrite A1; exact T1 | reflexivity | reflexivity |
  reflexivity].
Qed.

Lemma rl_gfa_cf : forall c n x, 1 <= c <= 31 -> c <> kBatchClass -> (Z.to_nat c < length (st_regions x))%nat ->
  0 <= rg_alloc_user (reg x c) <= rg_mapped_user (reg x c) -> rg_mapped_user (reg x c) <= kFreeArrayOffset ->
  rg_mapped_user (reg x c) mod kUserMapSize = 0 -> 0 <= rg_mapped_fa (reg x c) ->
  0 <= fa_len (rg_free (reg x c)) -> n * class_size c <= kUserMapSize -> 0 <= errb_size_cf x ->
  ipost (get_from_allocator_cf c n x) (fun r => rb c x (snd r)).
Proof.
intros c n x Hc H24 Hl Ha Hmb Hal Hfa Hf0 Hns He. pose proof (class_ok c Hc) as (Ks & _).
unfold get_from_allocator_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rb c x (snd r)).
2:{ destruct (Z.ltb_spec (fa_len (rg_free (reg x c))) n) as [Hlt|Hge]; cbv beta iota.
    - apply rl_populate_cf; try assumption; nia.
    - apply rk_ret. cbn [snd]. apply rb_refl. exact He. }
intros [ok y] B1. cbn [fst snd] in *. pose proof B1 as (L1 & F1 & E1 & P1 & M1).
destruct ok; cbn [negb]; cbv beta iota; [|apply rk_ret; cbn [snd]; exact B1].
apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if; [apply rk_ret; cbn [snd]; exact B1|].
match goal with |- context [fa_pop_n ?f ?a ?b ?l ?acc] => destruct (fa_pop_n f a b l acc) as [[tops rest]|] end;
cbv beta iota; [|apply rk_fail].
apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
eapply rb_trans; [exact B1|]. apply rb_set_same; [lia | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

Lemma rl_refill_cf : forall c x, 1 <= c <= 31 -> c <> kBatchClass -> (Z.to_nat c < length (st_regions x))%nat ->
  0 <= rg_alloc_user (reg x c) <= rg_mapped_user (reg x c) -> rg_mapped_user (reg x c) <= kFreeArrayOffset ->
  rg_mapped_user (reg x c) mod kUserMapSize = 0 -> 0 <= rg_mapped_fa (reg x c) ->
  0 <= fa_len (rg_free (reg x c)) -> pc_max (cache x c) / 2 * class_size c <= kUserMapSize -> 0 <= errb_size_cf x ->
  ipost (refill_if_empty_cf c x) (fun r => rb c x (snd r)).
Proof.
intros c x Hc H24 Hl Ha Hmb Hal Hfa Hf0 Hpm He.
unfold refill_if_empty_cf. apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache x c)) as [|w l]; cbv beta iota.
- apply rk_bind. eapply ipost_mono; [|apply rl_gfa_cf; assumption]. intros [got y] B1. cbn [fst snd] in *.
  destruct got as [tops|]; cbv beta iota.
  + apply rk_set_pc. cbn [snd]. eapply rb_trans; [exact B1|].
    apply rb_same; [reflexivity | reflexivity | exact (proj1 (proj2 (proj2 B1)))].
  + apply rk_ret. cbn [snd]. exact B1.
- apply rk_ret. cbn [snd]. apply rb_refl. exact He.
Qed.

Lemma rl_cache_alloc_cf : forall c x, 1 <= c <= 31 -> c <> kBatchClass -> length (st_regions x) = 32%nat ->
  0 <= rg_alloc_user (reg x c) <= rg_mapped_user (reg x c) -> rg_mapped_user (reg x c) <= kFreeArrayOffset ->
  rg_mapped_user (reg x c) mod kUserMapSize = 0 -> 0 <= rg_mapped_fa (reg x c) -> 0 <= fa_len (rg_free (reg x c)) ->
  (st_cache_inited x = true -> pc_max (cache x c) = max_cached c) -> 0 <= errb_size_cf x ->
  ipost (cache_alloc_cf c x) (fun r => rb c x (snd r)).
Proof.
intros c x Hc H24 Lr Ha Hmb Hal Hfa Hf0 Hpc He.
pose proof (class_ok c Hc) as (Ks & _ & _ & _ & _ & Kc).
assert (Hl : (Z.to_nat c < length (st_regions x))%nat) by (rewrite Lr; lia).
unfold cache_alloc_cf. apply rk_bind.
eapply ipost_mono with (P := fun r => st_regions (snd r) = st_regions x /\ st_secs (snd r) = st_secs x /\
  pc_max (cache (snd r) c) = max_cached c).
2:{ unfold init_cache_if_needed. apply rk_bind. apply rk_get. cbn [fst snd].
    destruct (st_cache_inited x) eqn:Ei; cbv beta iota.
    - apply rk_ret. cbn [snd]. split; [reflexivity | split; [reflexivity | exact (Hpc eq_refl)]].
    - apply rk_put. cbn [snd]. split; [reflexivity | split; [reflexivity|]].
      rewrite cache_after_init by lia. reflexivity. }
intros [u x1] (R1 & S1 & P1). cbn [fst snd] in *.
assert (Rg1 : forall w, reg x1 w = reg x w) by (intros w; unfold reg; rewrite R1; reflexivity).
assert (Eb1 : errb_size_cf x1 = errb_size_cf x) by (unfold errb_size_cf; rewrite S1; reflexivity).
assert (B1 : rb c x x1) by (apply rb_same; assumption).
apply rk_bind. eapply ipost_mono; [|apply rl_refill_cf; [lia | exact H24 | rewrite R1; exact Hl | rewrite Rg1; exact Ha |
  rewrite Rg1; exact Hmb | rewrite Rg1; exact Hal | rewrite Rg1; exact Hfa | rewrite Rg1; exact Hf0 |
  rewrite P1; unfold kMaxSize, kUserMapSize in *; lia | rewrite Eb1; exact He]].
intros [u2 x2] B2. cbn [fst snd] in *. pose proof (rb_trans _ _ _ _ B1 B2) as B12.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache x2 c)) as [|w l]; cbv beta iota zeta.
- apply rk_ret. cbn [snd]. exact B12.
- apply rk_bind. apply rk_set_pc. cbn [fst snd]. apply rk_ret. cbn [snd].
  eapply rb_trans; [exact B12|]. apply rb_same; [reflexivity | reflexivity | exact (proj1 (proj2 (proj2 B12)))].
Qed.

(* malloc_cf: errb + 100 * rpot_all does not rise. *)
Theorem rl_malloc_phi {cp : CfParams} : forall U n tr s, Wf_cf U s ->
  ipost (malloc_cf n tr s) (fun r => rl_phi (snd r) <= rl_phi s).
Proof.
intros U n tr s W.
pose proof (room_shape_cf_of_WfP_cf _ _ _ _ _ W) as IV. pose proof IV as (Lr & Lc & _ & _ & _ & He).
unfold malloc_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rl_phi (snd r) <= rl_phi s).
- intros [ob s2] H2. cbn [fst snd] in *. cbv zeta.
  destruct ob as [beg|]; cbv beta iota; [|apply rk_ret; exact H2].
  apply rk_bind. eapply ipost_mono; [|apply rk_depot]. intros [u3 s3] N3. cbn [fst snd] in *.
  apply rk_bind. eapply ipost_mono with (P := fun r => rk_nt s3 (snd r)).
  2:{ rk_if.
      - apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. rk_if; [apply rk_ret; cbn [snd]; apply rk_nt_refl | apply rk_spin].
      - apply rk_ret. cbn [snd]. apply rk_nt_refl. }
  intros [u4 s4] N4. cbn [fst snd] in *. apply rk_bind. apply rk_modify. cbn [fst snd]. apply rk_ret. cbn [snd].
  pose proof (rk_nt_trans _ _ _ N3 N4) as (R5 & _ & _ & S5 & _).
  apply (Z.le_trans _ (rl_phi s2)); [|exact H2]. apply Z.eq_le_incl. apply rl_phi_eq.
  + cbn [st_regions set_chunks]. exact R5.
  + unfold errb_size_cf. cbn [st_secs set_chunks]. rewrite S5. reflexivity.
- destruct (from_primary n) eqn:Fp; cbv beta iota.
  + pose proof (chunk_class_ok n Fp) as Hc.
    apply rk_bind.
    destruct (Z.eq_dec (chunk_class n) kBatchClass) as [E24|N24].
    * rewrite E24, cache_alloc_cf_24. eapply ipost_mono; [|apply rfr_cache_alloc].
      intros [o s2] (_ & F2 & S2). cbn [fst snd] in *. apply rk_ret. cbn [snd].
      apply Z.eq_le_incl. rewrite (rl_phi_frame24 (set_nev (st_nev s + 1) s) s2 F2); [reflexivity|].
      unfold errb_size_cf. rewrite S2. reflexivity.
    * destruct (rl_cls_facts U s (chunk_class n) W ltac:(lia)) as (Ha & Hmb & Hal & Hfa & Hf0 & Hpc).
      eapply ipost_mono; [|apply rl_cache_alloc_cf; [lia | exact N24 | exact Lr | exact Ha | exact Hmb | exact Hal |
        exact Hfa | exact Hf0 | exact Hpc | exact He]].
      intros [o s2] B2. cbn [fst snd] in *. apply rk_ret. cbn [snd].
      exact (rl_phi_rb (chunk_class n) (set_nev (st_nev s + 1) s) s2 ltac:(lia) B2).
  + eapply ipost_mono; [|apply rk_sec_alloc; exact Fp]. intros [ob s2] (R2 & _ & _ & E2 & _). cbn [fst snd] in *.
    apply Z.eq_le_incl. rewrite (rl_phi_eq (set_nev (st_nev s + 1) s) s2 R2 E2). reflexivity.
Qed.

End B.

(* ---------------------------------------------------------------------------- *)
(* 6. free_cf keeps rpot of every reporting class: it never maps a user region   *)
(*    of one, and its free-array maps keep the class's byte.                     *)
Definition rl_fa_ok (s : astate) : Prop := forall x, 1 <= x <= 31 -> x <> kBatchClass -> 0 <= rg_mapped_fa (reg s x).

Definition rff (s s' : astate) : Prop :=
  length (st_regions s') = length (st_regions s) /\
  (forall x, 1 <= x <= 31 -> x <> kBatchClass -> rpot s' x = rpot s x) /\ rl_fa_ok s'.

Lemma rff_refl : forall s, rl_fa_ok s -> rff s s.
Proof. intros s H. split; [reflexivity|]. split; [intros; reflexivity | exact H]. Qed.

Lemma rff_trans : forall s1 s2 s3, rff s1 s2 -> rff s2 s3 -> rff s1 s3.
Proof.
intros s1 s2 s3 (L1 & P1 & F1) (L2 & P2 & F2). split; [congruence|].
split; [intros x Hx Hn; rewrite P2, P1 by assumption; reflexivity | exact F2].
Qed.

Lemma rff_same : forall s s', st_regions s' = st_regions s -> rl_fa_ok s -> rff s s'.
Proof.
intros s s' R H. assert (Er : forall x, reg s' x = reg s x) by (intros x; unfold reg; rewrite R; reflexivity).
split; [rewrite R; reflexivity|]. split; [intros x _ _; apply rpot_reg; apply Er|].
intros x Hx Hn. rewrite Er. apply H; assumption.
Qed.

Lemma rff_of_rfr24 : forall s s', rfr kBatchClass s s' -> rl_fa_ok s -> rff s s'.
Proof.
intros s s' (L & F & _) Hf. split; [exact L|]. split.
- intros x Hx Hn. apply rpot_reg. apply F; lia.
- intros x Hx Hn. rewrite F by lia. apply Hf; assumption.
Qed.

Lemma rff_set_fields : forall c r s, length (st_regions s) = 32%nat -> rl_fa_ok s ->
  rg_mapped_user r = rg_mapped_user (reg s c) -> rg_alloc_user r = rg_alloc_user (reg s c) ->
  rg_holes r = rg_holes (reg s c) -> rg_mapped_fa r = rg_mapped_fa (reg s c) ->
  rff s (set_regions (zupd c r (st_regions s)) s).
Proof.
intros c r s Lr Hf E1 E2 E3 E4.
assert (G : forall x, 1 <= x <= 31 -> x <> kBatchClass ->
  rpot (set_regions (zupd c r (st_regions s)) s) x = rpot s x /\ 0 <= rg_mapped_fa (reg (set_regions (zupd c r (st_regions s)) s) x)).
{ intros x Hx Hn. destruct (Z.eq_dec x c) as [->|Hxc].
  - unfold rpot, exh_mem_cf. rewrite reg_upd_same by (first [lia | rewrite Lr; lia]).
    rewrite E1, E2, E3, E4. split; [reflexivity | apply Hf; assumption].
  - rewrite reg_upd_ne by lia. split; [apply rpot_reg; apply reg_upd_ne; lia | apply Hf; assumption]. }
split; [cbn [st_regions set_regions]; apply zupd_length|].
split; [intros x Hx Hn; exact (proj1 (G x Hx Hn)) | intros x Hx Hn; exact (proj2 (G x Hx Hn))].
Qed.

Section F. Context {ci : CfImg}.

Lemma rff_efa : forall c need sof s, length (st_regions s) = 32%nat -> rl_fa_ok s ->
  ipost (ensure_free_array c need sof s) (fun r => rff s (snd r)).
Proof.
intros c need sof s Lr Hf.
destruct (Z.eq_dec c kBatchClass) as [E|Hne];
[|destruct (Z_le_dec 1 c) as [H1|H1]; [destruct (Z_le_dec c 31) as [H2|H2]|]].
2:{ eapply ipost_mono; [|apply rl_ipost_and; [apply rl_efa; [lia | rewrite Lr; lia | apply Hf; lia] | apply rfr_efa]].
    intros [b s'] [(EF & X & FA) (L & F & _)]. cbn [snd] in *. pose proof EF as (_ & _ & Mp & Al & _).
    split; [exact L|]. split.
    - intros x Hx Hn. destruct (Z.eq_dec x c) as [->|Hxc].
      + unfold rpot. rewrite Mp, Al, X. reflexivity.
      + apply rpot_reg. apply F; lia.
    - intros x Hx Hn. destruct (Z.eq_dec x c) as [->|Hxc]; [exact FA | rewrite F by lia; apply Hf; assumption]. }
all: eapply ipost_mono; [|apply rfr_efa]; intros [b s'] (L & F & _); cbn [snd] in *;
  split; [exact L|]; split; [intros x Hx Hn; apply rpot_reg; apply F; lia | intros x Hx Hn; rewrite F by lia; apply Hf; assumption].
Qed.

Lemma rff_rta : forall c offs s, length (st_regions s) = 32%nat -> rl_fa_ok s ->
  ipost (return_to_allocator c offs s) (fun r => rff s (snd r)).
Proof.
intros c offs s Lr Hf. unfold return_to_allocator. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono; [|apply rff_efa; assumption]. intros [u s1] R1. cbn [fst snd] in *.
pose proof R1 as (L1 & _ & F1).
apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_set_region. cbn [snd].
eapply rff_trans; [exact R1|]. apply rff_set_fields; [congruence | exact F1 | reflexivity | reflexivity | reflexivity | reflexivity].
Qed.

Lemma rl_init_regions : forall s, ipost (init_cache_if_needed s) (fun r => st_regions (snd r) = st_regions s).
Proof.
intros s. unfold init_cache_if_needed. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (st_cache_inited s); cbv beta iota; [apply rk_ret | apply rk_put]; reflexivity.
Qed.

Lemma rff_cdealloc : forall c off s, length (st_regions s) = 32%nat -> rl_fa_ok s ->
  ipost (cache_dealloc c off s) (fun r => rff s (snd r)).
Proof.
intros c off s Lr Hf. unfold cache_dealloc. cbv zeta. apply rk_bind.
eapply ipost_mono; [|apply rl_init_regions]. intros [u s1] R1. cbn [fst snd] in *.
pose proof (rff_same s s1 R1 Hf) as Q1. pose proof Q1 as (L1 & _ & F1). rewrite Lr in L1.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rff s1 (snd r)).
2:{ rk_if.
    - apply rk_bind. eapply ipost_mono; [|apply rff_rta; assumption]. intros [u2 s2] R2. cbn [fst snd] in *.
      apply rk_set_pc. cbn [snd]. eapply rff_trans; [exact R2|]. apply rff_same; [reflexivity | exact (proj2 (proj2 R2))].
    - apply rk_ret. cbn [snd]. apply rff_refl. exact F1. }
intros [u3 s3] R3. cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd]. apply rk_set_pc. cbn [snd].
eapply rff_trans; [exact (rff_trans _ _ _ Q1 R3)|]. apply rff_same; [reflexivity | exact (proj2 (proj2 R3))].
Qed.

Lemma rl_sdealloc_regions : forall r s, ipost (sec_dealloc r s) (fun x => st_regions (snd x) = st_regions s).
Proof.
intros r s. unfold sec_dealloc. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (nth_error (st_secs s) r) as [sm|]; cbv beta iota; [|apply rk_fail].
destruct (index_of (st_sec_arr s) r 0%nat) as [i|]; cbv beta iota; [|apply rk_fail].
apply rk_bind. eapply ipost_mono with (P := fun x => snd x = s).
2:{ rk_if.
    - apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. rk_if; [apply rk_ret; reflexivity | apply rk_spin].
    - apply rk_ret. reflexivity. }
intros [u s1] E1. cbn [fst snd] in *. subst s1.
apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. apply rk_modify. cbn [snd]. reflexivity.
Qed.

Lemma rff_rchunk : forall k s, length (st_regions s) = 32%nat -> rl_fa_ok s ->
  ipost (recycle_chunk k s) (fun r => rff s (snd r)).
Proof.
intros k s Lr Hf. unfold recycle_chunk. apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
apply rk_bind. apply rk_put. cbn [fst snd].
destruct (ck_beg k) as [|off|r o|cid pos]; cbv beta iota.
- apply rk_fail.
- eapply ipost_mono; [|apply rff_cdealloc; [exact Lr | exact Hf]]. intros [u s1] H1. cbn [snd] in *. exact H1.
- eapply ipost_mono; [|apply rl_sdealloc_regions]. intros [u s1] H1. cbn [snd] in *.
  apply rff_same; [exact H1 | exact Hf].
- apply rk_fail.
Qed.

Lemma rff_ritems : forall fuel items s, length (st_regions s) = 32%nat -> rl_fa_ok s ->
  ipost (recycle_items fuel items s) (fun r => rff s (snd r)).
Proof.
induction fuel as [|f IH]; intros [|k t] s Lr Hf; cbn [recycle_items].
- apply rk_ret. cbn [snd]. apply rff_refl. exact Hf.
- apply rk_fail.
- apply rk_ret. cbn [snd]. apply rff_refl. exact Hf.
- apply rk_bind. eapply ipost_mono; [|apply rff_rchunk; assumption]. intros [u s1] H1. cbn [fst snd] in *.
  pose proof H1 as (L1 & _ & F1). rewrite Lr in L1.
  eapply ipost_mono; [|apply IH; assumption]. intros [u2 s2] H2. cbn [snd] in *. exact (rff_trans _ _ _ H1 H2).
Qed.

Lemma rff_drecycle : forall fuel bs s, length (st_regions s) = 32%nat -> rl_fa_ok s ->
  ipost (do_recycle fuel bs s) (fun r => rff s (snd r)).
Proof.
induction fuel as [|f IH]; intros [|b t] s Lr Hf; cbn [do_recycle].
- apply rk_ret. cbn [snd]. apply rff_refl. exact Hf.
- apply rk_fail.
- apply rk_ret. cbn [snd]. apply rff_refl. exact Hf.
- apply rk_bind. eapply ipost_mono; [|apply rff_ritems; assumption]. intros [u s1] H1. cbn [fst snd] in *.
  pose proof H1 as (L1 & _ & F1). rewrite Lr in L1.
  apply rk_bind. eapply ipost_mono; [|apply rff_cdealloc; assumption]. intros [u2 s2] H2. cbn [fst snd] in *.
  pose proof H2 as (L2 & _ & F2). rewrite L1 in L2.
  eapply ipost_mono; [|apply IH; assumption]. intros [u3 s3] H3. cbn [snd] in *.
  exact (rff_trans _ _ _ H1 (rff_trans _ _ _ H2 H3)).
Qed.

Lemma rff_drain : forall s, length (st_regions s) = 32%nat -> rl_fa_ok s ->
  ipost (maybe_drain_cf s) (fun r => rff s (snd r)).
Proof.
intros s Lr Hf. unfold maybe_drain_cf. cbv zeta. apply rk_bind. apply rk_get. cbn [fst snd].
rk_if.
- apply rk_ret. cbn [snd]. apply rff_refl. exact Hf.
- apply rk_bind. apply rk_put. cbn [fst snd].
  rk_if.
  + apply rk_ret. cbn [snd]. apply rff_same; [reflexivity | exact Hf].
  + do 2 (match goal with |- context [match ?x with _ => _ end] => destruct x end).
    apply rk_bind. apply rk_modify. cbn [fst snd].
    eapply ipost_mono; [|apply rff_drecycle; [exact Lr | exact Hf]]. intros [u s3] H3. cbn [snd] in *. exact H3.
Qed.

Lemma rff_enqueue : forall k s, length (st_regions s) = 32%nat -> rl_fa_ok s ->
  ipost (enqueue k s) (fun r => rff s (snd r)).
Proof.
intros k s Lr Hf. unfold enqueue. apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rff s (snd r)).
2:{ rk_if.
    - apply rk_bind. eapply ipost_mono; [|apply rfr_cache_alloc]. intros [ob s1] H1. cbn [fst snd] in *.
      destruct ob as [off|]; cbv beta iota; [apply rk_ret; cbn [snd]; exact (rff_of_rfr24 _ _ H1 Hf) | apply rk_spin].
    - apply rk_ret. cbn [snd]. apply rff_refl. exact Hf. }
intros [nb s2] H2. cbn [fst snd] in *. apply rk_modify. cbn [snd].
eapply rff_trans; [exact H2|]. apply rff_same; [reflexivity | exact (proj2 (proj2 H2))].
Qed.

Theorem rl_free_rff : forall p tr s, length (st_regions s) = 32%nat -> rl_fa_ok s ->
  ipost (free_cf p tr s) (fun r => rff s (snd r)).
Proof.
intros p tr s Lr Hf. unfold free_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => st_regions (snd r) = st_regions s).
2:{ rk_if; [apply rk_ret; reflexivity | apply rk_modify; reflexivity]. }
intros [u s2] R2. cbn [fst snd] in *.
pose proof (rff_same s s2 R2 Hf) as Q2. pose proof Q2 as (L2 & _ & F2). rewrite Lr in L2.
destruct p as [|off|r o|cid pos]; cbv beta iota; [apply rk_ret; cbn [snd]; exact Q2| | |].
all: apply rk_bind; apply rk_get; cbn [fst snd];
  match goal with |- context [find_user ?l ?q] => destruct (find_user l q) as [k|] end; cbv beta iota; [|apply rk_fail];
  apply rk_bind; eapply ipost_mono with (P := fun r => snd r = s2);
  [| destruct (ck_state k); cbv beta iota; [apply rk_ret; reflexivity | apply rk_fail]];
  intros [u3 s3] E3; cbn [fst snd] in *; subst s3;
  apply rk_bind; eapply ipost_mono; [|apply rk_depot]; intros [u4 s4] N4; cbn [fst snd] in *; cbv zeta;
  pose proof N4 as (R4 & _);
  apply rk_bind; apply rk_modify; cbn [fst snd];
  (* free_cf's size test (Quarantine::Put): enqueue, or recycle at once; both keep rff *)
  match goal with |- context [if ?c then _ else _] => destruct c end; cbv beta iota;
  (match goal with |- ipost (bind (?f ?kk) _ ?s5) _ =>
     assert (R5 : st_regions s5 = st_regions s2) by (cbn [st_regions set_chunks]; exact R4) end;
   apply rk_bind; eapply ipost_mono; [|first [apply rff_enqueue | apply rff_rchunk];
     [rewrite R5; exact L2 | exact (proj2 (proj2 (rff_same _ _ R5 F2)))]];
   intros [u6 s6] H6; cbn [fst snd] in *;
   pose proof H6 as (L6 & _ & F6); rewrite R5, L2 in L6;
   eapply ipost_mono; [|apply rff_drain; [exact L6 | exact F6]]; intros [u7 s7] H7; cbn [snd] in *;
   exact (rff_trans _ _ _ Q2 (rff_trans _ _ _ (rff_same _ _ R5 F2) (rff_trans _ _ _ H6 H7)))).
Qed.

End F.

(* ---------------------------------------------------------------------------- *)
(* 7. The batch class: a call maps class kBatchClass only from an empty cache and  *)
(*    an empty free array, to below its carved size + kBatchBytes + kUserMapSize.  *)
Definition M24 (s s' : astate) : Prop :=
  rg_mapped_user (reg s' kBatchClass) = rg_mapped_user (reg s kBatchClass) \/
  (pc_chunks (cache s kBatchClass) = [] /\ fa_len (rg_free (reg s kBatchClass)) < 1 /\
   rg_mapped_user (reg s' kBatchClass) <= rg_alloc_user (reg s kBatchClass) + kBatchBytes + kUserMapSize).

Lemma M24_after : forall s s1 s2, M24 s s1 -> rg_mapped_user (reg s2 kBatchClass) = rg_mapped_user (reg s1 kBatchClass) -> M24 s s2.
Proof. intros s s1 s2 [M|(A & B & M)] E; unfold M24; rewrite E; [left; exact M | right; split; [exact A | split; [exact B | exact M]]]. Qed.

Lemma M24_before : forall s s0 s1, st_regions s0 = st_regions s -> st_cache s0 = st_cache s -> M24 s0 s1 -> M24 s s1.
Proof. intros s s0 s1 R C H. unfold M24, reg, cache in *. rewrite R, C in H. exact H. Qed.

Lemma c24_mmu : forall need x, length (st_regions x) = 32%nat -> need <= 1 ->
  ipost (map_more_user kBatchClass need x) (fun r =>
    rg_mapped_user (reg (snd r) kBatchClass) = rg_mapped_user (reg x kBatchClass) \/
    rg_mapped_user (reg (snd r) kBatchClass) <= rg_alloc_user (reg x kBatchClass) + kBatchBytes + kUserMapSize).
Proof.
intros need x Hl Hn. assert (Hsz : class_size kBatchClass = 8192) by reflexivity.
unfold map_more_user. cbv zeta. rewrite Hsz. apply rk_bind. apply rk_get_region. cbn [fst snd].
destruct (Z.ltb_spec (rg_mapped_user (reg x kBatchClass)) (rg_alloc_user (reg x kBatchClass) + need * 8192)) as [Hlt|Hge];
cbv beta iota.
- pose proof (round_up_ge (rg_alloc_user (reg x kBatchClass) + need * 8192 - rg_mapped_user (reg x kBatchClass))
    kUserMapSize ltac:(unfold kUserMapSize; lia)) as [[R1 R2] _].
  apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
  destruct (aGranted z); cbv beta iota.
  + apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd]. right.
    rewrite reg_upd_same by (first [unfold kBatchClass; lia | exact (rk_k24_lt _ Hl)]). cbn [rg_mapped_user].
    unfold kBatchBytes. lia.
  + apply rk_bind. eapply ipost_mono with (P := fun r => rg_mapped_user (reg (snd r) kBatchClass) = rg_mapped_user (reg x kBatchClass)).
    2:{ destruct (aDestroyed z); cbv beta iota.
        - apply rk_set_region. cbn [snd]. rewrite reg_upd_same by (first [unfold kBatchClass; lia | exact (rk_k24_lt _ Hl)]).
          reflexivity.
        - apply rk_ret. reflexivity. }
    intros [u s1] H1. cbn [fst snd] in *. apply rk_ret. cbn [snd]. left. exact H1.
- apply rk_ret. cbn [snd]. left. reflexivity.
Qed.

Lemma c24_populate : forall need x, length (st_regions x) = 32%nat -> need <= 1 ->
  ipost (populate kBatchClass need x) (fun r =>
    rg_mapped_user (reg (snd r) kBatchClass) = rg_mapped_user (reg x kBatchClass) \/
    rg_mapped_user (reg (snd r) kBatchClass) <= rg_alloc_user (reg x kBatchClass) + kBatchBytes + kUserMapSize).
Proof.
intros need x Hl Hn. unfold populate. cbv zeta.
apply rk_bind. eapply ipost_mono; [|apply rl_ipost_and; [apply c24_mmu; assumption | apply rfr_mmu]].
intros [ok y] [M1 F1]. cbn [fst snd] in *. pose proof F1 as (L1 & _ & _). rewrite Hl in L1.
destruct ok; cbn [negb]; cbv beta iota; [|apply rk_ret; exact M1].
apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono; [|apply rk_efa_path; [unfold kBatchClass; lia | exact (rk_k24_lt _ L1)]].
intros [ok2 y2] E2. cbn [fst snd] in *. pose proof E2 as (L2 & _ & Mp2 & _). rewrite L1 in L2.
destruct ok2; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_bind. apply rk_set_region. cbn [fst snd].
  apply rk_ret. cbn [snd].
  rewrite reg_upd_same by (first [unfold kBatchClass; lia | exact (rk_k24_lt _ L2)]). cbn [rg_mapped_user].
  rewrite Mp2. exact M1.
- apply rk_ret. cbn [snd]. rewrite Mp2. exact M1.
Qed.

Lemma c24_gfa : forall n x, length (st_regions x) = 32%nat -> 0 <= fa_len (rg_free (reg x kBatchClass)) -> n <= 1 ->
  ipost (get_from_allocator kBatchClass n x) (fun r =>
    rg_mapped_user (reg (snd r) kBatchClass) = rg_mapped_user (reg x kBatchClass) \/
    (fa_len (rg_free (reg x kBatchClass)) < n /\
     rg_mapped_user (reg (snd r) kBatchClass) <= rg_alloc_user (reg x kBatchClass) + kBatchBytes + kUserMapSize)).
Proof.
intros n x Hl Hf Hn. unfold get_from_allocator. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => length (st_regions (snd r)) = 32%nat /\ (
    rg_mapped_user (reg (snd r) kBatchClass) = rg_mapped_user (reg x kBatchClass) \/
    (fa_len (rg_free (reg x kBatchClass)) < n /\
     rg_mapped_user (reg (snd r) kBatchClass) <= rg_alloc_user (reg x kBatchClass) + kBatchBytes + kUserMapSize))).
2:{ destruct (Z.ltb_spec (fa_len (rg_free (reg x kBatchClass))) n) as [Hlt|Hge]; cbv beta iota.
    - eapply ipost_mono; [|apply rl_ipost_and; [apply c24_populate; [exact Hl | lia] | apply rfr_populate]].
      intros [ok y] [M1 F1]. cbn [snd] in *. split; [destruct F1 as (L1 & _); congruence|].
      destruct M1 as [M1|M1]; [left; exact M1 | right; split; [exact Hlt | exact M1]].
    - apply rk_ret. cbn [snd]. split; [exact Hl | left; reflexivity]. }
intros [ok y] [Ly M1]. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota; [|apply rk_ret; exact M1].
apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if; [apply rk_ret; exact M1|].
match goal with |- context [fa_pop_n ?f ?a ?b ?l ?acc] => destruct (fa_pop_n f a b l acc) as [[tops rest]|] end;
cbv beta iota; [|apply rk_fail].
apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
rewrite reg_upd_same by (first [unfold kBatchClass; lia | exact (rk_k24_lt _ Ly)]). cbn [rg_mapped_user]. exact M1.
Qed.

Lemma c24_refill : forall x, length (st_regions x) = 32%nat -> 0 <= fa_len (rg_free (reg x kBatchClass)) ->
  pc_max (cache x kBatchClass) = max_cached kBatchClass ->
  ipost (refill_if_empty kBatchClass x) (fun r => M24 x (snd r)).
Proof.
intros x Hl Hf Hp. unfold refill_if_empty. apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache x kBatchClass)) as [|w l] eqn:Ec; cbv beta iota; [|apply rk_ret; cbn [snd]; left; reflexivity].
rewrite Hp. change (max_cached kBatchClass / 2) with 1.
apply rk_bind. eapply ipost_mono; [|apply c24_gfa; [exact Hl | exact Hf | lia]].
intros [got y] M1. cbn [fst snd] in *.
assert (M1' : M24 x y).
{ destruct M1 as [M1|(A & M1)]; [left; exact M1 | right; split; [exact Ec | split; [exact A | exact M1]]]. }
destruct got as [tops|]; cbv beta iota; [apply rk_set_pc | apply rk_ret]; cbn [snd]; exact M1'.
Qed.

Section C. Context {ci : CfImg} {cp : CfParams}.

Lemma c24_cache_alloc : forall x, room_shape_cf x -> ipost (cache_alloc kBatchClass x) (fun r => M24 x (snd r)).
Proof.
intros x IV. pose proof IV as (Lr & Lc & P & A & F & E).
unfold cache_alloc. apply rk_bind.
eapply ipost_mono with (P := fun r => st_regions (snd r) = st_regions x /\
  pc_chunks (cache (snd r) kBatchClass) = pc_chunks (cache x kBatchClass) /\
  pc_max (cache (snd r) kBatchClass) = max_cached kBatchClass).
2:{ unfold init_cache_if_needed. apply rk_bind. apply rk_get. cbn [fst snd].
    destruct (st_cache_inited x) eqn:Ei; cbv beta iota.
    - apply rk_ret. cbn [snd]. split; [reflexivity | split; [reflexivity | exact (P eq_refl)]].
    - apply rk_put. cbn [snd]. rewrite cache_after_init by (unfold kBatchClass; lia).
      split; [reflexivity | split; reflexivity]. }
intros [u x1] (R1 & Ch1 & P1). cbn [fst snd] in *.
assert (Rg1 : forall w, reg x1 w = reg x w) by (intros w; unfold reg; rewrite R1; reflexivity).
apply rk_bind. eapply ipost_mono; [|apply c24_refill; [rewrite R1; exact Lr | rewrite Rg1; exact F | exact P1]].
intros [u2 x2] M2. cbn [fst snd] in *.
assert (M2' : M24 x x2) by (unfold M24 in *; rewrite !Rg1, Ch1 in M2; exact M2).
apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache x2 kBatchClass)) as [|w l]; cbv beta iota zeta.
- apply rk_ret. cbn [snd]. exact M2'.
- apply rk_bind. apply rk_set_pc. cbn [fst snd]. apply rk_ret. cbn [snd]. exact M2'.
Qed.

Theorem c24_malloc : forall n tr s, room_shape_cf s -> ipost (malloc_cf n tr s) (fun r => M24 s (snd r)).
Proof.
intros n tr s IV. unfold malloc_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
assert (I0 : room_shape_cf (set_nev (st_nev s + 1) s)) by exact IV.
apply rk_bind. eapply ipost_mono with (P := fun r => M24 s (snd r)).
- intros [ob s2] H2. cbn [fst snd] in *. cbv zeta.
  destruct ob as [beg|]; cbv beta iota; [|apply rk_ret; exact H2].
  apply rk_bind. eapply ipost_mono; [|apply rk_depot]. intros [u3 s3] N3. cbn [fst snd] in *.
  apply rk_bind. eapply ipost_mono with (P := fun r => rk_nt s3 (snd r)).
  2:{ rk_if.
      - apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. rk_if; [apply rk_ret; cbn [snd]; apply rk_nt_refl | apply rk_spin].
      - apply rk_ret. cbn [snd]. apply rk_nt_refl. }
  intros [u4 s4] N4. cbn [fst snd] in *. apply rk_bind. apply rk_modify. cbn [fst snd]. apply rk_ret. cbn [snd].
  pose proof (rk_nt_trans _ _ _ N3 N4) as (R5 & _).
  apply (M24_after s s2); [exact H2|]. unfold reg. cbn [st_regions set_chunks]. rewrite R5. reflexivity.
- destruct (from_primary n) eqn:Fp; cbv beta iota.
  + pose proof (chunk_class_ok n Fp) as Hc. apply rk_bind.
    destruct (Z.eq_dec (chunk_class n) kBatchClass) as [E24|N24].
    * rewrite E24, cache_alloc_cf_24. eapply ipost_mono; [|apply c24_cache_alloc; exact I0].
      intros [o s2] M2. cbn [fst snd] in *. apply rk_ret. cbn [snd]. exact M2.
    * eapply ipost_mono; [|apply rk_cache_alloc_cf_other; [lia | exact N24 | exact I0]].
      intros [o s2] (_ & _ & _ & M2). cbn [fst snd] in *. apply rk_ret. cbn [snd]. left. exact M2.
  + eapply ipost_mono; [|apply rk_sec_alloc; exact Fp]. intros [ob s2] (R2 & _). cbn [fst snd] in *.
    left. unfold reg. rewrite R2. reflexivity.
Qed.

Lemma c24_enqueue : forall k x, room_shape_cf x -> ipost (enqueue k x) (fun r => M24 x (snd r)).
Proof.
intros k x IV. unfold enqueue. apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => M24 x (snd r)).
2:{ rk_if.
    - apply rk_bind. eapply ipost_mono; [|apply c24_cache_alloc; exact IV]. intros [ob s1] M1. cbn [fst snd] in *.
      destruct ob as [off|]; cbv beta iota; [apply rk_ret; cbn [snd]; exact M1 | apply rk_spin].
    - apply rk_ret. cbn [snd]. left. reflexivity. }
intros [nb s2] M2. cbn [fst snd] in *. apply rk_modify. cbn [snd]. exact M2.
Qed.

Theorem c24_free : forall p tr s, room_shape_cf s -> ipost (free_cf p tr s) (fun r => M24 s (snd r)).
Proof.
intros p tr s IV. unfold free_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rk_nt s (snd r)).
2:{ rk_if; [apply rk_ret; cbn [snd]; unfold rk_nt; rk_splits; reflexivity |
            apply rk_modify; cbn [snd]; unfold rk_nt; rk_splits; reflexivity]. }
intros [u s2] N2. cbn [fst snd] in *.
destruct p as [|off|r o|cid pos]; cbv beta iota;
  [apply rk_ret; cbn [snd]; left; destruct N2 as (R2 & _); unfold reg; rewrite R2; reflexivity | | |].
all: apply rk_bind; apply rk_get; cbn [fst snd];
  match goal with |- context [find_user ?l ?q] => destruct (find_user l q) as [k|] end; cbv beta iota; [|apply rk_fail];
  apply rk_bind; eapply ipost_mono with (P := fun r => snd r = s2);
  [| destruct (ck_state k); cbv beta iota; [apply rk_ret; reflexivity | apply rk_fail]];
  intros [u3 s3] E3; cbn [fst snd] in *; subst s3;
  apply rk_bind; eapply ipost_mono; [|apply rk_depot]; intros [u4 s4] N4; cbn [fst snd] in *; cbv zeta;
  apply rk_bind; apply rk_modify; cbn [fst snd];
  (* free_cf's size test (Quarantine::Put): the enqueue side as before; the recycle side maps nothing *)
  match goal with |- context [if ?c then _ else _] => destruct c end; cbv beta iota;
  match goal with |- ipost (bind (?f ?kk) _ ?s5) _ =>
    assert (N5 : rk_nt s s5) by (eapply rk_nt_trans; [exact N2|]; eapply rk_nt_trans; [exact N4|];
      unfold rk_nt; rk_splits; reflexivity) end;
  [ apply rk_bind; eapply ipost_mono; [|apply c24_enqueue; exact (rk_nt_inv _ _ N5 IV)];
    intros [u6 s6] M6; cbn [fst snd] in *;
    eapply ipost_mono; [|apply rk_drain_fr]; intros [u7 s7] (F7 & _); cbn [snd] in *;
    pose proof N5 as (R5 & C5 & _);
    exact (M24_before s _ s7 R5 C5 (M24_after _ s6 s7 M6 (F7 kBatchClass)))
  | apply rk_bind; eapply ipost_mono; [|apply rk_rchunk_fr]; intros [u6 s6] (F6 & _); cbn [fst snd] in *;
    eapply ipost_mono; [|apply rk_drain_fr]; intros [u7 s7] (F7 & _); cbn [snd] in *;
    pose proof N5 as (R5 & _);
    left; rewrite (F7 kBatchClass), (F6 kBatchClass); unfold reg; rewrite R5; reflexivity ].
Qed.

End C.

(* By Compl0, an empty cache and free array leave the class's records all in use: the carved size is
   kBatchBytes * n24 s. *)
Definition n24 (s : astate) : Z := Z.of_nat (length (chunk_offs s kBatchClass) + length (all_batches s)).

Lemma m24_bound {cp : CfParams} : forall U s s', Wf_cf U s -> M24 s s' ->
  rg_mapped_user (reg s' kBatchClass) = rg_mapped_user (reg s kBatchClass) \/
  rg_mapped_user (reg s' kBatchClass) <= kBatchBytes * (n24 s + 1) + kUserMapSize.
Proof.
intros U s s' W [M|(Hpc & Hfa & M)]; [left; exact M|]. right.
assert (Hc : 1 <= kBatchClass <= 31) by (unfold kBatchClass; lia).
pose proof (wfc_compl0 _ _ _ _ _ W kBatchClass Hc) as C0. unfold cdef in C0.
pose proof (wfc_classes _ _ _ _ _ W kBatchClass Hc) as CL. unfold wf_class_cf in CL.
pose proof (fa_elems_length (class_size kBatchClass) (rg_free (reg s kBatchClass)) (wrc_runs _ _ _ _ _ _ CL)) as HF.
pose proof (fa_len_nonneg _ (wrc_runs _ _ _ _ _ _ CL)) as HF0.
rewrite class_elems_eq, !length_app, Hpc in C0. cbn [length] in C0.
assert (Hb : length (batch_offs s kBatchClass) = length (all_batches s))
  by (unfold batch_offs; rewrite Z.eqb_refl, length_map; reflexivity).
rewrite Hb in C0. unfold n24. change (class_size kBatchClass) with 8192 in *. unfold kBatchBytes in *. lia.
Qed.

(* The LIVE class-24 blocks only: the allocated chunks of st_chunks whose request is class 24 (map snd (blocks s)).
   The quarantined class-24 chunks and the batches are counted by n24 (above), not here; this comment said otherwise
   until 2026-10-29 (corrected on a Theorem Labs lane's internal file CCNT24-FREE.md measurement; the file header was right). *)
Definition ccnt24 (s : astate) : Z := Z.of_nat (PresetRoom.ccnt kBatchClass (map snd (blocks s))).

Section N. Context {ci : CfImg} {cp : CfParams}.

Lemma n24_bound : forall U s, Wf_cf U s -> qtight s -> n24 s <= ccnt24 s + N24Q.
Proof.
intros U s W T.
pose proof (YGcfRoom.chunk_offs_le U s kBatchClass W T) as Hco.
pose proof (YGcfRoom.quar_bytes_ok_cf U s W T) as (Hq1 & Hb0 & Hqn & Hq).
unfold YGcfRoom.room_of_cf in Hq1, Hb0, Hqn, Hq. cbn [PresetRoom.rs_quar PresetRoom.rs_batches] in Hq1, Hb0, Hqn, Hq.
pose proof (PresetRoom.ccnt_quar_le kBatchClass _ Hq1) as Hcq. pose proof (PresetRoom.lo_pos kBatchClass) as Hlo.
rewrite PresetRoom.zsum_map8 in Hcq. pose proof (PresetRoom.zsum_nonneg _ Hq1) as Hz.
assert (H8 : PresetRoom.zsum (map ck_n (q_items s)) + 8 * Z.of_nat (length (map ck_n (q_items s))) <= PresetRoom.QT)
  by (unfold PresetRoom.Q_BATCH, PresetRoom.Q_BATCH_BYTES in *; lia).
assert (Hqc : Z.of_nat (PresetRoom.ccnt kBatchClass (map ck_n (q_items s))) <= PresetRoom.QT / (PresetRoom.lo kBatchClass + 8))
  by (apply Z.div_le_lower_bound; nia).
assert (Hbc : Z.of_nat (length (all_batches s)) <= PresetRoom.QT / kBatchBytes)
  by (apply Z.div_le_lower_bound; unfold kBatchBytes, PresetRoom.Q_BATCH_BYTES in *; lia).
unfold n24, N24Q, ccnt24. lia.
Qed.

End N.

(* ---------------------------------------------------------------------------- *)
(* 7b. The chunk -> request map. The live requests are map snd (blocks S) (the     *)
(*     harness's L); a live secondary chunk is exactly a live request that is not  *)
(*     primary (chunk_ok_cf), so live_sec_blocks counts those requests.            *)
Definition rl_sec_req (n : Z) : bool := negb (PresetRoom.is_primary n).
Definition sec_cnt (s : astate) : Z := Z.of_nat (length (filter rl_sec_req (map snd (blocks s)))).

Lemma rl_filter_len {A} : forall (f : A -> bool) l, (length (filter f l) <= length l)%nat.
Proof. intros f l. induction l as [|x t IH]; cbn [filter]; [lia|]. destruct (f x); cbn [length]; lia. Qed.

Lemma live_sec_blocks_req {cp : CfParams} : forall U S, Wf_cf U S -> live_sec_blocks S = sec_cnt S.
Proof.
intros U S W. pose proof (wfc_chunks _ _ _ _ _ W) as HC.
unfold live_sec_blocks, sec_cnt, blocks. rewrite map_map. cbn [snd]. f_equal.
revert HC. generalize (st_chunks S) as l. intros l HC.
induction HC as [|k t Hk Ht IH]; [reflexivity|].
assert (Ea : is_alloc k = match ck_state k with CAllocated => true | _ => false end) by reflexivity.
destruct Hk as [_ Hk]. cbn [filter]. rewrite Ea.
destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; [destruct Hk | | | destruct Hk];
destruct Hk as [Hf _]; destruct (ck_state k); cbn [map filter length];
try (change (rl_sec_req (ck_req k)) with (negb (PresetRoom.is_primary (ck_req k)));
     rewrite YGcfRoom.is_primary_eq, Hf; cbn [negb length]); rewrite ?IH; reflexivity.
Qed.

Lemma sec_cnt_le_blocks : forall S, sec_cnt S <= Z.of_nat (length (blocks S)).
Proof.
intros S. unfold sec_cnt. pose proof (rl_filter_len rl_sec_req (map snd (blocks S))) as H. rewrite length_map in H. lia.
Qed.
(* ---------------------------------------------------------------------------- *)
(* 8. The invariant.                                                              *)
Section L. Context {cp : CfParams}.

Definition room_live_cf (S : astate) : Prop :=
  Z.of_nat (length (st_sec_arr S)) + Z.of_nat RK_realloc < cf_sec_live_max /\
  errb_size_cf S + 100 * rpot_all S <= ERRB_MAX_cf /\
  rg_mapped_user (reg S kBatchClass) + (Z.of_nat RK_realloc + 1) * kUserMapSize <= kFreeArrayOffset.

(* The program's live-set premises of the keeps, in the form PresetLiveSec.v's live_sec_state / live_c24_state
   conclude, at L := map snd (blocks S): the live secondary requests and the live class-24 requests. *)
Definition rl_sec_ok (Lsec : Z) (S : astate) : Prop := sec_cnt S <= Lsec /\ Lsec + QSEC_MAX + 3 < cf_sec_live_max.
Definition rl_b24_ok (L24 : Z) (S : astate) : Prop :=
  ccnt24 S <= L24 /\ kBatchBytes * (L24 + N24Q + 1) + 4 * kUserMapSize <= kFreeArrayOffset.

(* The one parameter premise of the initial and driver forms. *)
Definition rl_param_ok : Prop := QSEC_MAX + 6 < cf_sec_live_max.

Theorem room_live_room_k : forall S, room_live_cf S -> ROOM_cf_k S RK_realloc.
Proof.
intros S (A & Bq & C). pose proof (rpot_all_nonneg S) as P. pose proof cf_nob_lo as N.
unfold ROOM_cf_k. split; [exact A|]. split; [|exact C].
unfold ERRB_ROOM_k. change (Z.of_nat RK_realloc) with 2. unfold ERRB_MAX_cf, kPage in *. change (2 ^ 12) with 4096. lia.
Qed.

Theorem room_live_room : forall S, room_live_cf S -> ROOM_cf S.
Proof. intros S H. exact (RK_room S RK_realloc (room_live_room_k S H)). Qed.

(* room_live_cf reads no fake-stack field (only st_sec_arr, st_secs and st_regions): a frame-area step keeps it by
   conversion. *)
Lemma room_live_set_fs : forall S f, room_live_cf S -> room_live_cf (set_fs f S).
Proof. intros S f H. exact H. Qed.

Lemma room_live_stack_free : forall S c p, room_live_cf S -> room_live_cf (stack_free_state c p S).
Proof. intros S c p H. exact H. Qed.

Theorem room_live_cf_init_gen : rl_param_ok -> room_live_cf init_state.
Proof.
intros Hp. unfold rl_param_ok in Hp. rewrite QSEC_MAX_value in Hp.
unfold room_live_cf. rewrite rpot_all_init.
assert (Es : errb_size_cf init_state = 0) by reflexivity.
assert (Er : rg_mapped_user (reg init_state kBatchClass) = 0) by (rewrite reg_init; reflexivity).
rewrite Es, Er. cbn [st_sec_arr init_state length]. change (Z.of_nat RK_realloc) with 2.
unfold ERRB_MAX_cf, kUserMapSize, kFreeArrayOffset. lia.
Qed.

Lemma ccnt24_le_blocks : forall S, ccnt24 S <= Z.of_nat (length (blocks S)).
Proof.
intros S. unfold ccnt24, PresetRoom.ccnt.
assert (H : forall (f : Z -> bool) l, (length (filter f l) <= length l)%nat).
{ intros f l. induction l as [|x t IH]; cbn [filter]; [lia|]. destruct (f x); cbn [length]; lia. }
pose proof (H (PresetRoom.in_cls kBatchClass) (map snd (blocks S))) as H1. rewrite length_map in H1. lia.
Qed.

(* (c) across one call, from the M24 step fact. *)
Lemma rl_c_keep : forall U L24 S S', Wf_cf U S -> qtight S -> rl_b24_ok L24 S ->
  rg_mapped_user (reg S kBatchClass) + (Z.of_nat RK_realloc + 1) * kUserMapSize <= kFreeArrayOffset ->
  M24 S S' -> rg_mapped_user (reg S' kBatchClass) + (Z.of_nat RK_realloc + 1) * kUserMapSize <= kFreeArrayOffset.
Proof.
intros U L24 S S' W T [Hl Hb] C M.
pose proof (n24_bound U S W T) as N.
destruct (m24_bound U S S' W M) as [E|E]; [rewrite E; exact C|].
change (Z.of_nat RK_realloc) with 2 in *. unfold kBatchBytes, kUserMapSize, kFreeArrayOffset in *. lia.
Qed.

Section K. Context {ci : CfImg}.

(* ---------------------------------------------------------------------------- *)
(* 9. The keeps.                                                                  *)
Theorem room_live_malloc_keep : forall U Lsec L24 n tr S trc p S',
  Wf_cf U S -> qtight S -> rl_sec_ok Lsec S -> rl_b24_ok L24 S -> room_live_cf S ->
  apath (malloc_cf n tr S) trc (p, S') -> room_live_cf S'.
Proof.
intros U Lsec L24 n tr S trc p S' W T [Hls Hsec] HB (A & Bq & C) Hp.
pose proof (room_shape_cf_of_WfP_cf _ _ _ _ _ W) as IV.
destruct (malloc_step_cf n tr S trc p S' IV Hp) as (_ & L & _ & _).
pose proof (ipost_apath _ _ _ _ (rl_malloc_phi U n tr S W) Hp) as PB. cbn [snd] in PB.
pose proof (ipost_apath _ _ _ _ (c24_malloc n tr S IV) Hp) as MC. cbn [snd] in MC.
pose proof (sec_arr_bound_cf U 0 0 0 S W T) as SB. rewrite (live_sec_blocks_req U S W) in SB.
split; [|split].
- assert (Hb01 : (if from_primary n then 0 else 1) <= 1) by (destruct (from_primary n); lia).
  change (Z.of_nat RK_realloc) with 2 in *. lia.
- unfold rl_phi in PB. lia.
- exact (rl_c_keep U L24 S S' W T HB C MC).
Qed.

Theorem room_live_free_keep : forall U L24 p tr S trc S',
  Wf_cf U S -> qtight S -> rl_b24_ok L24 S -> room_live_cf S ->
  apath (free_cf p tr S) trc (tt, S') -> room_live_cf S'.
Proof.
intros U L24 p tr S trc S' W T HB (A & Bq & C) Hp.
pose proof (room_shape_cf_of_WfP_cf _ _ _ _ _ W) as IV. pose proof IV as (Lr & _).
destruct (free_step_cf p tr S trc S' IV Hp) as (L & E & _).
assert (Hf : rl_fa_ok S) by (intros x Hx Hn; exact (proj1 (proj2 (proj2 (proj2 (rl_cls_facts U S x W Hx)))))).
pose proof (ipost_apath _ _ _ _ (rl_free_rff p tr S Lr Hf) Hp) as (_ & P & _). cbn [snd] in P.
pose proof (ipost_apath _ _ _ _ (c24_free p tr S IV) Hp) as MC. cbn [snd] in MC.
assert (Ra : rpot_all S' = rpot_all S).
{ unfold rpot_all. apply rsum_ext. intros c Hc. apply in_rl_classes in Hc.
  destruct (Z.eq_dec c kBatchClass) as [->|Hne]; [rewrite !rpot_24; reflexivity | apply P; assumption]. }
split; [|split].
- lia.
- rewrite E, Ra. exact Bq.
- exact (rl_c_keep U L24 S S' W T HB C MC).
Qed.

(* free_cf PNull, the realloc tree's entry step, is a frame. *)
Lemma rl_free_null : forall tr s, ipost (free_cf PNull tr s) (fun r => snd r =
  if st_internal_inited s then set_nev (st_nev s + 1) s else set_internal_inited true (set_nev (st_nev s + 1) s)).
Proof.
intros tr s. unfold free_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. change (st_internal_inited (set_nev (st_nev s + 1) s)) with (st_internal_inited s).
destruct (st_internal_inited s); cbv beta iota.
- apply rk_ret. cbn [fst snd]. apply rk_ret. reflexivity.
- apply rk_modify. cbn [fst snd]. apply rk_ret. reflexivity.
Qed.

Theorem room_live_realloc_keep : forall U Lsec L24 p n tr S trc q S',
  universe_ok U -> admits U tr S -> 0 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
  Wf_cf U S -> qtight S -> rl_sec_ok Lsec S -> rl_b24_ok L24 S -> ccnt24 S < L24 -> room_live_cf S ->
  apath (realloc_tree_with malloc_cf free_cf p n tr S) trc (q, S') -> room_live_cf S'.
Proof.
intros U Lsec L24 p n tr S trc q S' HU Htr Hn Hlive W T HS HB Hlt R Hp.
unfold realloc_tree_with, YG00.bind in Hp.
destruct (rl_apath_ibind _ _ _ _ Hp) as (tr1 & tr2 & [u S1] & H1 & H2). cbv beta iota in H2.
pose proof (ipost_apath _ _ _ _ (rl_free_null tr S) H1) as E1. cbn [snd] in E1.
assert (X1 : Wf_cf U S1 /\ qtight S1 /\ room_live_cf S1 /\ rl_sec_ok Lsec S1 /\ rl_b24_ok L24 S1 /\
  ccnt24 S1 = ccnt24 S /\ blocks S1 = blocks S /\ blocks_bytes S1 = blocks_bytes S).
{ subst S1. destruct (st_internal_inited S).
  - split; [exact (WfP_cf_tick U 0 0 0 S W)|]. split; [exact T|]. split; [exact R|].
    split; [exact HS|]. split; [exact HB|]. split; [reflexivity|]. split; reflexivity.
  - split; [exact (WfP_cf_set_internal_inited_cf U 0 0 0 _ true (WfP_cf_tick U 0 0 0 S W))|].
    split; [exact T|]. split; [exact R|].
    split; [exact HS|]. split; [exact HB|]. split; [reflexivity|]. split; reflexivity. }
assert (DS1 : st_depot S1 = st_depot S) by (subst S1; destruct (st_internal_inited S); reflexivity).
clear E1. destruct X1 as (W1 & T1 & R1 & HS1 & HB1 & Cc1 & Bl1 & Bb1).
destruct (rl_apath_ibind _ _ _ _ H2) as (tr3 & tr4 & [q0 S2] & H3 & H4). cbv beta iota in H4.
pose proof (room_live_malloc_keep U Lsec L24 n tr S1 tr3 q0 S2 W1 T1 HS1 HB1 R1 H3) as R2.
pose proof (room_live_room S1 R1) as (Rs1 & Re1 & Rb1).
pose proof (malloc_cf_apath_post U S1 n tr tr3 (q0, S2) HU W1 Hn ltac:(rewrite Bb1; exact Hlive) (admits_keep U tr S S1 Htr (or_introl DS1)) Rs1 Re1 Rb1 H3) as MP.
unfold malloc_post_cf in MP. destruct MP as (W2 & _ & _ & _ & Bl2 & Q2).
destruct q0 as [|off|r o|cid pos]; cbv beta iota in H4;
  [apply rl_apath_ret in H4; injection H4 as _ E4; subst S'; exact R2 | | |].
all: destruct (rl_apath_ibind _ _ _ _ H4) as (tr5 & tr6 & [u5 S3] & H5 & H6);
  cbv beta iota in H6; apply rl_apath_ret in H6; injection H6 as _ E6; subst S';
  destruct u5;
  assert (HB2 : rl_b24_ok L24 S2) by
    (destruct HB as [_ Hb]; split; [|exact Hb];
     unfold ccnt24 in *; rewrite (proj1 Bl2), Bl1, map_app, PresetRoom.ccnt_app; cbn [map snd];
     unfold PresetRoom.ccnt at 2; cbn [filter]; destruct (PresetRoom.in_cls kBatchClass n); cbn [length]; lia);
  exact (room_live_free_keep U L24 p tr S2 tr5 S3 W2 (Q2 T1) HB2 R2 H5).
Qed.

(* realloc(NULL, n), ReallocP.v's realloc_null_tree_with: the entry free_cf PNull (a frame), then malloc_cf. *)
Theorem room_live_realloc_null_keep : forall U Lsec L24 n tr S trc q S',
  Wf_cf U S -> qtight S -> rl_sec_ok Lsec S -> rl_b24_ok L24 S -> room_live_cf S ->
  apath (realloc_null_tree_with malloc_cf free_cf n tr S) trc (q, S') -> room_live_cf S'.
Proof.
intros U Lsec L24 n tr S trc q S' W T HS HB R Hp.
unfold realloc_null_tree_with, YG00.bind in Hp.
destruct (rl_apath_ibind _ _ _ _ Hp) as (tr1 & tr2 & [u S1] & H1 & H2). cbv beta iota in H2.
pose proof (ipost_apath _ _ _ _ (rl_free_null tr S) H1) as E1. cbn [snd] in E1.
assert (X1 : Wf_cf U S1 /\ qtight S1 /\ room_live_cf S1 /\ rl_sec_ok Lsec S1 /\ rl_b24_ok L24 S1).
{ subst S1. destruct (st_internal_inited S).
  - split; [exact (WfP_cf_tick U 0 0 0 S W)|]. split; [exact T|]. split; [exact R|]. split; [exact HS | exact HB].
  - split; [exact (WfP_cf_set_internal_inited_cf U 0 0 0 _ true (WfP_cf_tick U 0 0 0 S W))|].
    split; [exact T|]. split; [exact R|]. split; [exact HS | exact HB]. }
destruct X1 as (W1 & T1 & R1 & HS1 & HB1).
exact (room_live_malloc_keep U Lsec L24 n tr S1 tr2 q S' W1 T1 HS1 HB1 R1 H2).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 10. A driver-phase step, generic: one malloc_cf or free_cf from a state with at  *)
(*     most 3 live blocks. h-pre-b1's names are in lib/A/CfRoomLivePreset.v.        *)
Definition rl_step (S S' : astate) : Prop :=
  (exists n tr trc p, apath (malloc_cf n tr S) trc (p, S')) \/ (exists p tr trc, apath (free_cf p tr S) trc (tt, S')).

Lemma rl_b24_three : kBatchBytes * (3 + N24Q + 1) + 4 * kUserMapSize <= kFreeArrayOffset.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Theorem room_live_cf_step_gen : rl_param_ok -> forall U S S', Wf_cf U S -> qtight S -> room_live_cf S ->
  (length (blocks S) <= 3)%nat -> rl_step S S' -> room_live_cf S'.
Proof.
intros Hp U S S' W T R Hb Hs. unfold rl_param_ok in Hp.
assert (HS : rl_sec_ok 3 S) by (split; [pose proof (sec_cnt_le_blocks S); lia | lia]).
assert (HB : rl_b24_ok 3 S) by (split; [pose proof (ccnt24_le_blocks S); lia | exact rl_b24_three]).
destruct Hs as [(n & tr & trc & p & H)|(p & tr & trc & H)].
- exact (room_live_malloc_keep U 3 3 n tr S trc p S' W T HS HB R H).
- exact (room_live_free_keep U 3 p tr S trc S' W T HB R H).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 10b. One allocator call of the harness: malloc_cf, free_cf, the realloc tree     *)
(*      (with the call premises its inner malloc_cf needs, the ones                 *)
(*      arealloc_realizes_cf's call carries) or realloc(NULL, n).                  *)
Definition rl_call (U : Univ) (S S' : astate) : Prop :=
  (exists n tr trc p, apath (malloc_cf n tr S) trc (p, S')) \/
  (exists p tr trc, apath (free_cf p tr S) trc (tt, S')) \/
  (exists p n tr trc q, universe_ok U /\ admits U tr S /\ 0 <= n < cf_malloc_max /\ blocks_bytes S + n <= LIVE_MAX /\
     apath (realloc_tree_with malloc_cf free_cf p n tr S) trc (q, S')) \/
  (exists n tr trc q, apath (realloc_null_tree_with malloc_cf free_cf n tr S) trc (q, S')).

(* The class-24 premise carries one more record of room (rl_b24_ok (L24 + 1)): a realloc holds its old and its
   new block at its inner free. *)
Theorem room_live_call_keep : forall U Lsec L24 S S', Wf_cf U S -> qtight S -> rl_sec_ok Lsec S ->
  ccnt24 S <= L24 -> rl_b24_ok (L24 + 1) S -> room_live_cf S -> rl_call U S S' -> room_live_cf S'.
Proof.
intros U Lsec L24 S S' W T HS Hc HB R
  [(n & tr & trc & p & H)|[(p & tr & trc & H)|[(p & n & tr & trc & q & HU & Htr & Hn & Hl & H)|(n & tr & trc & q & H)]]].
- exact (room_live_malloc_keep U Lsec (L24 + 1) n tr S trc p S' W T HS HB R H).
- exact (room_live_free_keep U (L24 + 1) p tr S trc S' W T HB R H).
- exact (room_live_realloc_keep U Lsec (L24 + 1) p n tr S trc q S' HU Htr Hn Hl W T HS HB ltac:(lia) R H).
- exact (room_live_realloc_null_keep U Lsec (L24 + 1) n tr S trc q S' W T HS HB R H).
Qed.

End K.
End L.

(* ---------------------------------------------------------------------------- *)
(* 11. The call-level keeps: Wf_cf, universe_ok and qtight come from acall_pre_cf,   *)
(*     as YGcfRoomStep.v's step lemmas take room_shape_cf.                          *)
Section STEP. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Lemma rl_of_acall_pre_cf : forall segs B ly S Hp W regs mem md ch, acall_pre_cf segs B ly S Hp W regs mem md ch ->
  Wf_cf (YG0f.as_universe B) S /\ universe_ok (YG0f.as_universe B) /\ qtight S.
Proof.
intros segs B ly S Hp W regs mem md ch H.
split; [exact (amc_wf _ _ _ _ _ (proj1 (proj1 H)))|]. split; [exact (amc_universe _ _ _ _ _ (proj1 (proj1 H)))|].
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QM & _). exact (proj1 QM).
Qed.

Lemma RL_malloc_step : forall segs B ly S Hp W regs mem md ch Lsec L24 n tr trc r,
  acall_pre_cf segs B ly S Hp W regs mem md ch -> rl_sec_ok Lsec S -> rl_b24_ok L24 S -> room_live_cf S ->
  apath (malloc_cf n tr S) trc r -> room_live_cf (snd r).
Proof.
intros segs B ly S Hp W regs mem md ch Lsec L24 n tr trc [p S'] Hpre HS HB R Hpa.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & _ & T).
exact (room_live_malloc_keep _ Lsec L24 n tr S trc p S' W0 T HS HB R Hpa).
Qed.

Lemma RL_free_step : forall segs B ly S Hp W regs mem md ch L24 p tr trc r,
  acall_pre_cf segs B ly S Hp W regs mem md ch -> rl_b24_ok L24 S -> room_live_cf S ->
  apath (free_cf p tr S) trc r -> room_live_cf (snd r).
Proof.
intros segs B ly S Hp W regs mem md ch L24 p tr trc [[] S'] Hpre HB R Hpa.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & _ & T).
exact (room_live_free_keep _ L24 p tr S trc S' W0 T HB R Hpa).
Qed.

Lemma RL_realloc_step : forall segs B ly S Hp W regs mem md ch Lsec L24 p n tr trc r,
  acall_pre_cf segs B ly S Hp W regs mem md ch -> admits (YG0f.as_universe B) tr S -> 0 <= n < cf_malloc_max ->
  blocks_bytes S + n <= LIVE_MAX -> rl_sec_ok Lsec S -> rl_b24_ok L24 S -> ccnt24 S < L24 -> room_live_cf S ->
  apath (realloc_tree_with malloc_cf free_cf p n tr S) trc r -> room_live_cf (snd r).
Proof.
intros segs B ly S Hp W regs mem md ch Lsec L24 p n tr trc [q S'] Hpre Htr Hn Hlive HS HB Hlt R Hpa.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & HU & T).
exact (room_live_realloc_keep _ Lsec L24 p n tr S trc q S' HU Htr Hn Hlive W0 T HS HB Hlt R Hpa).
Qed.

End STEP.
