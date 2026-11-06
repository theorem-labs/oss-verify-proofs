(* CARRIED from a working branch 3dd49fa29fa14b99e3c465cacbfe79a09756bb26,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfPath.v, sha256 8386a17af5e5a0f5ae89df855ce6a5fe2deed5fcfb15cb5da48738fee8121e65.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's second allocator instance (suffix cf), the PATH lemmas of malloc_cf
   (YG00cf.v). They say what a malloc_cf path that returns PNull looks like, and when no such path exists.
   They need no invariant preservation, only the path structure of malloc_cf and a SHAPE of the start state:
   - shape_cf S: 32 regions, 32 caches, and, once the caches are initialised, pc_max = max_cached c. Without
     it the statements are false: with st_regions S = [] the class-full arm's set_exh_cf writes nothing,
     so the flag stays clear; with st_cache_inited S = true and pc_max (cache S c) = 0, refill pops zero
     entries and malloc_cf returns PNull with the flag clear. shape_cf_of_WfP_cf derives it from WfP_cf.
   A path is cgif's apath (YG00.v:618-623) and "every answer granted" is cgif's gflag (YG0d.v:169-170),
   which is what c-asan's AllocG.alloc_leaf gives (`exists trc, apath (mt n tr S) trc r /\ gflag trc = true`).
   With every answer granted, the ONLY PNull path is map_more_user_cf's class-full arm (YG00cf.v:184):
   errb_report_cf c ;; set_exh_cf c ;; ret false. The errbuf steps touch only st_secs and st_nev.
   No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf YG01cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The predicate of every all-granted path, and its monadic rules.             *)
Definition gpost {A : Type} (t : itree astate A) (P : A -> Prop) : Prop :=
forall tr a, apath t tr a -> gflag tr = true -> P a.

Lemma gpost_mono {A} (t : itree astate A) (P Q : A -> Prop) :
(forall a, P a -> Q a) -> gpost t P -> gpost t Q.
Proof. intros HPQ H tr a Hp Hg. exact (HPQ a (H tr a Hp Hg)). Qed.

Lemma gpost_true {A} (t : itree astate A) : gpost t (fun _ => True).
Proof. intros tr a _ _. exact I. Qed.

Lemma gp_iret {A} (a : A) (P : A -> Prop) : P a -> gpost (IRet a) P.
Proof. intros H tr a' Hp _. destruct tr as [|x tr]; cbn [apath] in Hp; [rewrite <- Hp; exact H | destruct Hp]. Qed.

Lemma gp_ifail {A} (f : failure) (P : A -> Prop) : gpost (@IFail astate A f) P.
Proof. intros tr a Hp _. destruct tr; cbn [apath] in Hp; destruct Hp. Qed.

Lemma gp_ispin {A} (pc : Z) (P : A -> Prop) : gpost (@ISpin astate A pc) P.
Proof. intros tr a Hp _. destruct tr; cbn [apath] in Hp; destruct Hp. Qed.

Lemma gpost_ibind {A B} (t : itree astate A) : forall (k : A -> itree astate B) (P : B -> Prop),
gpost t (fun a => gpost (k a) P) -> gpost (ibind t k) P.
Proof.
induction t as [a | q snap c IH | pc | f]; intros k P H tr b Hp Hg.
- exact (H [] a eq_refl eq_refl tr b Hp Hg).
- destruct tr as [|[q' z] tr']; cbn [ibind apath] in Hp; [destruct Hp|].
destruct Hp as (-> & Hz & Hp). cbn [gflag] in Hg. apply andb_prop in Hg as [Hpz Hg].
assert (HH : gpost (c z) (fun a => gpost (k a) P)).
{ intros tr1 a1 Hp1 Hg1. apply (H ((q, z) :: tr1) a1).
- cbn [apath]. split; [reflexivity | split; assumption].
- cbn [gflag]. rewrite Hpz, Hg1. reflexivity. }
exact (IH z k P HH tr' b Hp Hg).
- destruct tr; cbn [ibind apath] in Hp; destruct Hp.
- destruct tr; cbn [ibind apath] in Hp; destruct Hp.
Qed.

Lemma gp_bind {A B} (m : M B) (k : B -> M A) (s : astate) (P : A * astate -> Prop) :
gpost (m s) (fun r => gpost (k (fst r) (snd r)) P) -> gpost (bind m k s) P.
Proof.
intros H. unfold bind. apply gpost_ibind. eapply gpost_mono; [|exact H]. intros [x s'] Hx. exact Hx.
Qed.

Lemma gp_ret {A} (a : A) s (P : A * astate -> Prop) : P (a, s) -> gpost (ret a s) P.
Proof. intros H. exact (gp_iret (a, s) P H). Qed.
Lemma gp_get s (P : astate * astate -> Prop) : P (s, s) -> gpost (get s) P.
Proof. intros H. exact (gp_iret (s, s) P H). Qed.
Lemma gp_put s s' (P : unit * astate -> Prop) : P (tt, s') -> gpost (put s' s) P.
Proof. intros H. exact (gp_iret (tt, s') P H). Qed.
Lemma gp_modify f s (P : unit * astate -> Prop) : P (tt, f s) -> gpost (modify f s) P.
Proof. intros H. exact (gp_iret (tt, f s) P H). Qed.
Lemma gp_tick s (P : unit * astate -> Prop) : P (tt, set_nev (st_nev s + 1) s) -> gpost (tick s) P.
Proof. intros H. exact (gp_iret (tt, set_nev (st_nev s + 1) s) P H). Qed.
Lemma gp_get_region c s (P : region * astate -> Prop) : P (reg s c, s) -> gpost (get_region c s) P.
Proof. intros H. exact (gp_iret (reg s c, s) P H). Qed.
Lemma gp_get_pc c s (P : pclass * astate -> Prop) : P (cache s c, s) -> gpost (get_pc c s) P.
Proof. intros H. exact (gp_iret (cache s c, s) P H). Qed.
Lemma gp_set_region c r s (P : unit * astate -> Prop) :
P (tt, set_regions (zupd c r (st_regions s)) s) -> gpost (set_region c r s) P.
Proof. intros H. exact (gp_iret (tt, set_regions (zupd c r (st_regions s)) s) P H). Qed.
Lemma gp_set_pc c p s (P : unit * astate -> Prop) :
P (tt, set_cache (zupd c p (st_cache s)) s) -> gpost (set_pc c p s) P.
Proof. intros H. exact (gp_iret (tt, set_cache (zupd c p (st_cache s)) s) P H). Qed.
Lemma gp_mcheck (b : bool) tag s (P : unit * astate -> Prop) : (b = true -> P (tt, s)) -> gpost (mcheck b tag s) P.
Proof. intros H. destruct b; [exact (gp_iret (tt, s) P (H eq_refl)) | exact (gp_ifail (FCheck tag) P)]. Qed.
Lemma gp_spin {A} pc s (P : A * astate -> Prop) : gpost (@spin A pc s) P.
Proof. exact (gp_ispin pc P). Qed.
Lemma gp_fail {A} f s (P : A * astate -> Prop) : gpost (@fail A f s) P.
Proof. exact (gp_ifail f P). Qed.
(* An all-granted path takes the progress answer of every ask. *)
Lemma gp_askz q s (P : Z * astate -> Prop) :
(forall z, aok s q z -> progz q z = true -> P (z, s)) -> gpost (askz q s) P.
Proof.
intros H tr a Hp Hg. unfold askz in Hp.
destruct tr as [|[q' z] tr']; cbn [apath] in Hp; [destruct Hp|].
destruct Hp as (-> & Hz & Hp). destruct tr' as [|x tr'']; cbn [apath] in Hp; [|destruct Hp].
cbn [gflag] in Hg. rewrite andb_true_r in Hg. rewrite <- Hp. exact (H z Hz Hg).
Qed.

(* The side conditions of reg_upd_same / cache_upd_same along a path. *)
Ltac lenside := first [ lia | (cbn [st_regions st_cache set_regions set_cache]; rewrite ?zupd_length; lia) ].

(* ---------------------------------------------------------------------------- *)
(* 2. Facts about the class and the start state.                                 *)
Lemma rz_size_pos : forall n, 0 < rz_size n.
Proof.
intros n. unfold rz_size.
assert (H : 0 <= rz_log n) by (unfold rz_log; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia).
rewrite Z.shiftl_mul_pow2 by exact H. pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) H). lia.
Qed.

Lemma chunk_class_ok : forall n, from_primary n = true -> 1 <= chunk_class n <= 30.
Proof.
intros n Fp. unfold chunk_class, needed_size. rewrite Fp.
pose proof Fp as H. unfold from_primary in H. apply Z.leb_le in H.
assert (H1 : 1 <= needed_primary n).
{ unfold needed_primary, rounded_size. pose proof (round_up_ge (Z.max n 8) 8 ltac:(lia)) as [[R _] _].
pose proof (rz_size_pos n). lia. }
exact (proj1 (class_id_ok _ (conj H1 H))).
Qed.

Definition shape_cf (S : astate) : Prop :=
length (st_regions S) = 32%nat /\ length (st_cache S) = 32%nat /\
(st_cache_inited S = true -> forall c, 1 <= c <= 31 -> pc_max (cache S c) = max_cached c).

(* What the class-full arm tests (YG00cf.v:172-174), as a failure and as a pass. *)
Definition arm_full (r : region) (c need : Z) : Prop :=
rg_mapped_user r < rg_alloc_user r + need * class_size c /\
kFreeArrayOffset < rg_mapped_user r + round_up (rg_alloc_user r + need * class_size c - rg_mapped_user r) kUserMapSize.
Definition arm_fits (r : region) (c need : Z) : Prop :=
rg_alloc_user r + need * class_size c <= rg_mapped_user r \/
rg_mapped_user r + round_up (rg_alloc_user r + need * class_size c - rg_mapped_user r) kUserMapSize <= kFreeArrayOffset.

(* The class-full refusal at the start state of a cache_alloc with refill target n'. *)
Definition cfc (s : astate) (c n' : Z) : Prop :=
c <> kBatchClass /\ pc_chunks (cache s c) = [] /\ fa_len (rg_free (reg s c)) < n' /\
arm_full (reg s c) c (n' - fa_len (rg_free (reg s c))).
Definition cfull_cf (S : astate) (c : Z) : Prop := cfc S c (max_cached c / 2).

(* The number of entries the refill asks the class-full arm to map for. *)
Definition cf_need (S : astate) (c : Z) : Z := max_cached c / 2 - fa_len (rg_free (reg S c)).

(* ROOM: any one of these keeps a primary malloc_cf off the class-full arm. *)
Definition room_at (S : astate) (c : Z) : Prop :=
c = kBatchClass \/ pc_chunks (cache S c) <> [] \/ cf_need S c <= 0 \/ arm_fits (reg S c) c (cf_need S c).
Definition room_cf (n : Z) (S : astate) : Prop := from_primary n = false \/ room_at S (chunk_class n).

(* Frames along a path. *)
Definition rcc_same (s s' : astate) : Prop :=
st_regions s' = st_regions s /\ st_cache s' = st_cache s /\ st_chunks s' = st_chunks s /\ st_cache_inited s' = st_cache_inited s.
Definition fr_same (s s' : astate) : Prop :=
st_chunks s' = st_chunks s /\ st_cache s' = st_cache s /\ length (st_regions s') = length (st_regions s).
Definition map_ok (s s' : astate) (c need : Z) : Prop :=
fr_same s s' /\ rg_alloc_user (reg s' c) = rg_alloc_user (reg s c) /\ rg_free (reg s' c) = rg_free (reg s c) /\
rg_alloc_user (reg s c) + need * class_size c <= rg_mapped_user (reg s' c).
Definition pop_post (s : astate) (c need : Z) (r : bool * astate) : Prop :=
fr_same s (snd r) /\
(fst r = true -> fa_len (rg_free (reg s c)) + need <= fa_len (rg_free (reg (snd r) c))) /\
(fst r = false -> c <> kBatchClass /\ exh_mem_cf (snd r) c = true /\ arm_full (reg s c) c need).

Lemma rcc_refl : forall s, rcc_same s s.
Proof. intros s. split; [reflexivity | split; [reflexivity | split; reflexivity]]. Qed.
Lemma rcc_trans : forall s1 s2 s3, rcc_same s1 s2 -> rcc_same s2 s3 -> rcc_same s1 s3.
Proof.
intros s1 s2 s3 (A1 & B1 & C1 & D1) (A2 & B2 & C2 & D2).
split; [congruence | split; [congruence | split; congruence]].
Qed.
Ltac rcc_triv := unfold rcc_same; split; [reflexivity | split; [reflexivity | split; reflexivity]].

Lemma fa_pop_n_len : forall fuel sz n l acc tops rest, fa_pop_n fuel sz n l acc = Some (tops, rest) ->
(length acc <= length tops)%nat /\ (0 < n -> (length acc < length tops)%nat).
Proof.
induction fuel as [|f IH]; intros sz n l acc tops rest H; cbn [fa_pop_n] in H; [discriminate H|].
destruct (Z.leb_spec n 0) as [Hle|Hgt].
- injection H as <- <-. rewrite length_rev. split; lia.
- destruct (fa_pop sz l) as [[off l']|]; [|discriminate H].
destruct (IH _ _ _ _ _ _ H) as [H1 _]. cbn [length] in H1. split; lia.
Qed.

Lemma fa_pop_n_nonempty : forall fuel sz n l tops rest,
fa_pop_n fuel sz n l [] = Some (tops, rest) -> 0 < n -> tops <> [].
Proof.
intros fuel sz n l tops rest H Hn E. destruct (fa_pop_n_len _ _ _ _ _ _ _ H) as [_ H2].
specialize (H2 Hn). subst tops. cbn [length] in H2. lia.
Qed.

Lemma map_granted_ok : forall s c need, 0 <= c -> (Z.to_nat c < length (st_regions s))%nat ->
rg_mapped_user (reg s c) < rg_alloc_user (reg s c) + need * class_size c ->
map_ok s (set_regions (zupd c (mkRegion (rg_mapped_user (reg s c) +
round_up (rg_alloc_user (reg s c) + need * class_size c - rg_mapped_user (reg s c)) kUserMapSize)
(rg_alloc_user (reg s c)) (rg_mapped_fa (reg s c)) (rg_free (reg s c))
(del_hole (rg_mapped_user (reg s c)) (rg_holes (reg s c)))) (st_regions s)) s) c need.
Proof.
intros s c need Hc Hl Hlt. unfold map_ok, fr_same. rewrite reg_upd_same by assumption.
cbn [rg_mapped_user rg_alloc_user rg_free st_chunks st_cache st_regions set_regions]. rewrite zupd_length.
pose proof (round_up_ge (rg_alloc_user (reg s c) + need * class_size c - rg_mapped_user (reg s c)) kUserMapSize
ltac:(unfold kUserMapSize; lia)) as [[R1 _] _].
split; [split; [reflexivity | split; reflexivity]|]. split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The steps, each over every all-granted path.                                *)
Lemma mmu_path : forall c need s, 0 <= c -> (Z.to_nat c < length (st_regions s))%nat ->
gpost (map_more_user c need s) (fun r => fst r = true /\ map_ok s (snd r) c need).
Proof.
intros c need s Hc Hl. unfold map_more_user. apply gp_bind. apply gp_get_region. cbn [fst snd].
destruct (Z.ltb_spec (rg_mapped_user (reg s c)) (rg_alloc_user (reg s c) + need * class_size c)) as [Hlt|Hge];
cbn [fst snd].
- apply gp_bind. apply gp_mcheck. intros _. cbn [fst snd].
apply gp_bind. apply gp_askz. intros z _ Hpz. cbn [progz] in Hpz. apply Z.eqb_eq in Hpz. subst z. cbn [fst snd].
change (aGranted 1) with true. cbn [fst snd].
apply gp_bind. apply gp_set_region. cbn [fst snd]. apply gp_ret. cbn [fst snd].
split; [reflexivity|]. apply map_granted_ok; assumption.
- apply gp_ret. cbn [fst snd]. split; [reflexivity|]. unfold map_ok, fr_same.
split; [split; [reflexivity | split; reflexivity]|]. split; [reflexivity|]. split; [reflexivity|]. exact Hge.
Qed.

Lemma efa_path : forall c need sof s, 0 <= c -> (Z.to_nat c < length (st_regions s))%nat ->
gpost (ensure_free_array c need sof s) (fun r => fst r = true /\ fr_same s (snd r) /\
rg_mapped_user (reg (snd r) c) = rg_mapped_user (reg s c) /\ rg_alloc_user (reg (snd r) c) = rg_alloc_user (reg s c) /\
rg_free (reg (snd r) c) = rg_free (reg s c)).
Proof.
intros c need sof s Hc Hl. unfold ensure_free_array. apply gp_bind. apply gp_get_region. cbn [fst snd].
destruct (Z.leb_spec (4 * need) (rg_mapped_fa (reg s c))); cbn [fst snd].
- apply gp_ret. cbn [fst snd]. unfold fr_same.
split; [reflexivity|]. split; [split; [reflexivity | split; reflexivity]|]. split; [reflexivity | split; reflexivity].
- apply gp_bind. apply gp_mcheck. intros _. cbn [fst snd].
apply gp_bind. apply gp_askz. intros z _ Hpz. cbn [progz] in Hpz. apply Z.eqb_eq in Hpz. subst z. cbn [fst snd].
change (aGranted 1) with true. cbn [fst snd].
apply gp_bind. apply gp_set_region. cbn [fst snd]. apply gp_ret. cbn [fst snd].
unfold fr_same. rewrite reg_upd_same by assumption.
cbn [rg_mapped_user rg_alloc_user rg_free st_chunks st_cache st_regions set_regions]. rewrite zupd_length.
split; [reflexivity|]. split; [split; [reflexivity | split; reflexivity]|]. split; [reflexivity | split; reflexivity].
Qed.

Section PATH.
Context {ci : CfImg}.

(* The errbuf steps touch neither the regions, the caches nor the chunks. *)
Lemma errb_map_rcc : forall want s, gpost (errb_map_cf want s) (fun r => rcc_same s (snd r)).
Proof.
intros want s. unfold errb_map_cf. cbn [fst snd]. apply gp_bind. apply gp_tick. cbn [fst snd].
apply gp_bind. apply gp_askz. intros z _ _. cbn [fst snd].
destruct (z =? 0); cbn [fst snd].
- apply gp_spin.
- apply gp_bind. unfold errb_retire. apply gp_modify. cbn [fst snd]. apply gp_modify. cbn [snd]. rcc_triv.
Qed.

Lemma errb_set_size_rcc : forall ns s, gpost (errb_set_size ns s) (fun r => rcc_same s (snd r)).
Proof. intros ns s. unfold errb_set_size. apply gp_modify. cbn [snd]. destruct (find_sz (st_secs s) 0); rcc_triv. Qed.

Lemma errb_append_rcc : forall len s, gpost (errb_append_cf len s) (fun r => rcc_same s (snd r)).
Proof.
intros len s. unfold errb_append_cf. apply gp_bind. apply gp_get. cbn [fst snd].
destruct (negb (errb_mapped_cf s)); cbn [fst snd].
- apply gp_bind. eapply gpost_mono; [|apply errb_map_rcc]. intros [u s1] H1. cbn [fst snd] in *.
apply gp_bind. apply gp_get. cbn [fst snd].
apply gp_bind. eapply gpost_mono with (P := fun r => rcc_same s1 (snd r)).
2:{ destruct (errb_cap_cf s1 <? len); cbn [fst snd]; [apply errb_map_rcc | apply gp_ret; cbn [snd]; apply rcc_refl]. }
intros [u2 s2] H2. cbn [fst snd] in *.
eapply gpost_mono; [|apply errb_set_size_rcc]. intros [u3 s3] H3. cbn [snd] in *.
eapply rcc_trans; [exact H1|]. eapply rcc_trans; [exact H2 | exact H3].
- apply gp_bind. eapply gpost_mono with (P := fun r => rcc_same s (snd r)).
2:{ destruct (errb_cap_cf s <? errb_size_cf s + len); cbn [fst snd]; [apply errb_map_rcc | apply gp_ret; cbn [snd]; apply rcc_refl]. }
intros [u2 s2] H2. cbn [fst snd] in *.
eapply gpost_mono; [|apply errb_set_size_rcc]. intros [u3 s3] H3. cbn [snd] in *.
eapply rcc_trans; [exact H2 | exact H3].
Qed.

Lemma errb_report_rcc : forall c s, gpost (errb_report_cf c s) (fun r => rcc_same s (snd r)).
Proof.
intros c s. unfold errb_report_cf. apply gp_bind. apply gp_get. cbn [fst snd].
destruct (exh_mem_cf s c); cbn [fst snd].
- apply gp_ret. cbn [snd]. apply rcc_refl.
- apply gp_bind. eapply gpost_mono; [|apply errb_append_rcc]. intros [u s1] H1. cbn [fst snd] in *.
eapply gpost_mono; [|apply errb_append_rcc]. intros [u2 s2] H2. cbn [snd] in *.
eapply rcc_trans; [exact H1 | exact H2].
Qed.

(* The cf arm: a refused map is impossible on an all-granted path, so false means class-full. *)
Lemma mmu_cf_path : forall c need s, 0 <= c -> c <> kBatchClass -> (Z.to_nat c < length (st_regions s))%nat ->
gpost (map_more_user_cf c need s) (fun r =>
(fst r = true -> map_ok s (snd r) c need) /\
(fst r = false -> fr_same s (snd r) /\ exh_mem_cf (snd r) c = true /\ arm_full (reg s c) c need)).
Proof.
intros c need s Hc N24 Hl. unfold map_more_user_cf.
destruct (Z.eqb_spec c kBatchClass) as [E|_]; [contradiction|]. cbn [fst snd].
apply gp_bind. apply gp_get_region. cbn [fst snd].
destruct (Z.ltb_spec (rg_mapped_user (reg s c)) (rg_alloc_user (reg s c) + need * class_size c)) as [Hlt|Hge];
cbn [fst snd].
- destruct (Z.leb_spec (rg_mapped_user (reg s c) +
round_up (rg_alloc_user (reg s c) + need * class_size c - rg_mapped_user (reg s c)) kUserMapSize) kFreeArrayOffset)
as [Hfit|Hover]; cbn [fst snd].
+ apply gp_bind. apply gp_askz. intros z _ Hpz. cbn [progz] in Hpz. apply Z.eqb_eq in Hpz. subst z. cbn [fst snd].
change (aGranted 1) with true. cbn [fst snd].
apply gp_bind. apply gp_set_region. cbn [fst snd]. apply gp_ret. cbn [fst snd].
split; [intros _; apply map_granted_ok; assumption | intros E; discriminate E].
+ apply gp_bind. eapply gpost_mono; [|apply errb_report_rcc]. intros [u s1] (R1 & C1 & K1 & I1). cbn [fst snd] in *.
assert (Hl1 : (Z.to_nat c < length (st_regions s1))%nat) by (rewrite R1; exact Hl).
apply gp_bind. unfold set_exh_cf. apply gp_bind. apply gp_get_region. cbn [fst snd].
apply gp_set_region. cbn [fst snd]. apply gp_ret. cbn [fst snd].
split; [intros E; discriminate E | intros _].
split; [|split].
* unfold fr_same. cbn [st_chunks st_cache st_regions set_regions]. rewrite zupd_length, R1.
split; [exact K1 | split; [exact C1 | reflexivity]].
* unfold exh_mem_cf. rewrite reg_upd_same by assumption. cbn [rg_holes]. apply add_hole_exh.
* split; assumption.
- apply gp_ret. cbn [fst snd]. split; [intros _ | intros E; discriminate E]. unfold map_ok, fr_same.
split; [split; [reflexivity | split; reflexivity]|]. split; [reflexivity|]. split; [reflexivity|]. exact Hge.
Qed.

(* cgif's populate, which class kBatchClass keeps: on an all-granted path it succeeds. *)
Lemma populate_path : forall c need s, 1 <= c <= 31 -> (Z.to_nat c < length (st_regions s))%nat ->
gpost (populate c need s) (fun r => fst r = true /\ pop_post s c need r).
Proof.
intros c need s Hc Hl. pose proof (class_ok c Hc) as (Ksz & _).
unfold populate. apply gp_bind. eapply gpost_mono; [|apply (mmu_path c need s ltac:(lia) Hl)].
intros [ok s1] [Eok ((K1 & C1 & L1) & A1 & F1 & M1)]. cbn [fst snd] in *. subst ok. cbn [negb fst snd].
assert (Hl1 : (Z.to_nat c < length (st_regions s1))%nat) by (rewrite L1; exact Hl).
apply gp_bind. apply gp_get_region. cbn [fst snd].
apply gp_bind. eapply gpost_mono; [|apply (efa_path c _ false s1 ltac:(lia) Hl1)].
intros [ok2 s2] (Eok2 & (K2 & C2 & L2) & M2 & A2 & F2). cbn [fst snd] in *. subst ok2. cbn [negb fst snd].
assert (Hl2 : (Z.to_nat c < length (st_regions s2))%nat) by (rewrite L2; exact Hl1).
apply gp_bind. apply gp_get_region. cbn [fst snd].
apply gp_bind. apply gp_set_region. cbn [fst snd]. apply gp_ret. cbn [fst snd].
split; [reflexivity|]. unfold pop_post, fr_same. cbn [fst snd].
rewrite !reg_upd_same by lenside.
cbn [rg_free rg_mapped_user rg_alloc_user fa_len st_chunks st_cache st_regions set_regions]. rewrite !zupd_length.
split; [split; [congruence | split; congruence]|].
split; [intros _ | intros E; discriminate E].
rewrite F2, F1.
assert (Hq : need <= (rg_mapped_user (reg s1 c) - rg_alloc_user (reg s1 c)) / class_size c).
{ apply Z.div_le_lower_bound; [exact Ksz|]. rewrite A1. nia. }
lia.
Qed.

Lemma populate_cf_path : forall c need s, 1 <= c <= 31 -> (Z.to_nat c < length (st_regions s))%nat ->
gpost (populate_cf c need s) (pop_post s c need).
Proof.
intros c need s Hc Hl. pose proof (class_ok c Hc) as (Ksz & _).
unfold populate_cf. destruct (Z.eqb_spec c kBatchClass) as [E24|N24]; cbn [fst snd].
- eapply gpost_mono; [|apply (populate_path c need s Hc Hl)]. intros r [_ H]. exact H.
- apply gp_bind. eapply gpost_mono; [|apply (mmu_cf_path c need s ltac:(lia) N24 Hl)].
intros [ok s1] [Ht Hf]. cbn [fst snd] in *. destruct ok; cbn [negb fst snd].
+ destruct (Ht eq_refl) as ((K1 & C1 & L1) & A1 & F1 & M1).
assert (Hl1 : (Z.to_nat c < length (st_regions s1))%nat) by (rewrite L1; exact Hl).
apply gp_bind. apply gp_get_region. cbn [fst snd].
apply gp_bind. eapply gpost_mono; [|apply (efa_path c _ false s1 ltac:(lia) Hl1)].
intros [ok2 s2] (Eok2 & (K2 & C2 & L2) & M2 & A2 & F2). cbn [fst snd] in *. subst ok2. cbn [negb fst snd].
assert (Hl2 : (Z.to_nat c < length (st_regions s2))%nat) by (rewrite L2; exact Hl1).
apply gp_bind. apply gp_get_region. cbn [fst snd].
apply gp_bind. apply gp_set_region. cbn [fst snd].
apply gp_bind. unfold clear_exh_cf. apply gp_bind. apply gp_get_region. cbn [fst snd].
apply gp_set_region. cbn [fst snd]. apply gp_ret. cbn [fst snd].
unfold pop_post, fr_same. cbn [fst snd].
rewrite !reg_upd_same by lenside.
cbn [rg_free rg_mapped_user rg_alloc_user rg_mapped_fa rg_holes fa_len st_chunks st_cache st_regions set_regions].
rewrite !zupd_length.
split; [split; [congruence | split; congruence]|].
split; [intros _ | intros E; discriminate E].
rewrite F2, F1.
assert (Hq : need <= (rg_mapped_user (reg s1 c) - rg_alloc_user (reg s1 c)) / class_size c).
{ apply Z.div_le_lower_bound; [exact Ksz|]. rewrite A1. nia. }
lia.
+ destruct (Hf eq_refl) as (FR & EX & AF). apply gp_ret. cbn [fst snd]. unfold pop_post. cbn [fst snd].
split; [exact FR|]. split; [intros E; discriminate E | intros _; split; [exact N24 | split; assumption]].
Qed.

Lemma gfa_cf_path : forall c n s, 1 <= c <= 31 -> 1 <= n -> (Z.to_nat c < length (st_regions s))%nat ->
gpost (get_from_allocator_cf c n s) (fun r => fr_same s (snd r) /\
match fst r with
| None => exh_mem_cf (snd r) c = true /\ c <> kBatchClass /\ fa_len (rg_free (reg s c)) < n /\
arm_full (reg s c) c (n - fa_len (rg_free (reg s c)))
| Some tops => tops <> []
end).
Proof.
intros c n s Hc Hn Hl. unfold get_from_allocator_cf. apply gp_bind. apply gp_get_region. cbn [fst snd].
apply gp_bind.
eapply gpost_mono with (P := fun r => fr_same s (snd r) /\
(fst r = true -> n <= fa_len (rg_free (reg (snd r) c))) /\
(fst r = false -> fa_len (rg_free (reg s c)) < n /\ c <> kBatchClass /\ exh_mem_cf (snd r) c = true /\
arm_full (reg s c) c (n - fa_len (rg_free (reg s c))))).
2:{ destruct (Z.ltb_spec (fa_len (rg_free (reg s c))) n) as [Hlt|Hge]; cbn [fst snd].
- eapply gpost_mono; [|apply (populate_cf_path c _ s Hc Hl)].
intros [ok s1] H. unfold pop_post in H. cbn [fst snd] in *. destruct H as (FR & Ht & Hf).
split; [exact FR|]. split.
+ intros E. specialize (Ht E). lia.
+ intros E. destruct (Hf E) as (N24 & EX & AF). exact (conj Hlt (conj N24 (conj EX AF))).
- apply gp_ret. cbn [fst snd]. split; [unfold fr_same; split; [reflexivity | split; reflexivity]|].
split; [intros _; lia | intros E; discriminate E]. }
intros [ok s1] (FR1 & Ht & Hf). cbn [fst snd] in *. destruct FR1 as (K1 & C1 & L1).
destruct ok; cbn [negb fst snd].
- specialize (Ht eq_refl).
apply gp_bind. apply gp_get_region. cbn [fst snd].
destruct (Z.ltb_spec (fa_len (rg_free (reg s1 c))) n) as [Hlt|_]; [exfalso; lia|]. cbn [fst snd].
match goal with |- context [fa_pop_n ?f ?a ?b ?l ?acc] => destruct (fa_pop_n f a b l acc) as [[tops rest]|] eqn:Ep end;
cbn [fst snd].
+ apply gp_bind. apply gp_set_region. cbn [fst snd]. apply gp_ret. cbn [fst snd].
split; [unfold fr_same; cbn [st_chunks st_cache st_regions set_regions]; rewrite zupd_length;
split; [exact K1 | split; [exact C1 | exact L1]]|].
exact (fa_pop_n_nonempty _ _ _ _ _ _ Ep ltac:(lia)).
+ apply gp_fail.
- destruct (Hf eq_refl) as (Hlt & N24 & EX & AF). apply gp_ret. cbn [fst snd].
unfold fr_same. split; [split; [exact K1 | split; [exact C1 | exact L1]]|]. exact (conj EX (conj N24 (conj Hlt AF))).
Qed.

Lemma refill_cf_path : forall c s, 1 <= c <= 31 -> (Z.to_nat c < length (st_regions s))%nat ->
(Z.to_nat c < length (st_cache s))%nat -> 1 <= pc_max (cache s c) / 2 ->
gpost (refill_if_empty_cf c s) (fun r => st_chunks (snd r) = st_chunks s /\
(pc_chunks (cache (snd r) c) = [] -> exh_mem_cf (snd r) c = true /\ cfc s c (pc_max (cache s c) / 2))).
Proof.
intros c s Hc Hl Hlc Hn. unfold refill_if_empty_cf. apply gp_bind. apply gp_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s c)) as [|x l] eqn:Epc; cbn [fst snd].
- apply gp_bind. eapply gpost_mono; [|apply (gfa_cf_path c _ s Hc Hn Hl)].
intros [got s1] ((K1 & C1 & L1) & Hg). cbn [fst snd] in *.
destruct got as [tops|]; cbn [fst snd] in Hg |- *.
+ apply gp_set_pc. cbn [fst snd]. split; [exact K1|].
rewrite cache_upd_same by (first [lia | (rewrite C1; exact Hlc)]). cbn [pc_chunks]. unfold cache_fill_order.
intros E. apply (f_equal (@rev Z)) in E. rewrite rev_involutive in E. cbn in E. contradiction.
+ apply gp_ret. cbn [fst snd]. split; [exact K1|]. intros _. destruct Hg as (EX & N24 & Hlt & AF).
split; [exact EX|]. unfold cfc. split; [exact N24|]. split; [exact Epc|]. split; assumption.
- apply gp_ret. cbn [fst snd]. split; [reflexivity|]. intros E. rewrite Epc in E. discriminate E.
Qed.

Lemma init_path : forall s, shape_cf s ->
gpost (init_cache_if_needed s) (fun r => st_regions (snd r) = st_regions s /\ st_chunks (snd r) = st_chunks s /\
length (st_cache (snd r)) = 32%nat /\ forall c, 1 <= c <= 31 -> cache (snd r) c = mkPC (max_cached c) (pc_chunks (cache s c))).
Proof.
intros s (Hlr & Hlc & Hpm). unfold init_cache_if_needed. apply gp_bind. apply gp_get. cbn [fst snd].
destruct (st_cache_inited s) eqn:Ei; cbn [fst snd].
- apply gp_ret. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hlc|].
intros c Hc. specialize (Hpm ltac:(first [exact Ei | reflexivity]) c Hc). revert Hpm. destruct (cache s c) as [pm pch].
cbn [pc_max pc_chunks].
intros ->. reflexivity.
- apply gp_put. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|].
split; [cbn [st_cache set_cache_inited set_cache]; apply length_init_caches|].
intros c Hc. apply cache_after_init. lia.
Qed.

Lemma cache_alloc_cf_path : forall c s, 1 <= c <= 31 -> shape_cf s ->
gpost (cache_alloc_cf c s) (fun r => fst r = None ->
st_chunks (snd r) = st_chunks s /\ exh_mem_cf (snd r) c = true /\ cfull_cf s c).
Proof.
intros c s Hc Hs. pose proof Hs as (Hlr & Hlc & _).
pose proof (class_ok c Hc) as (_ & _ & _ & Kmc & _).
unfold cache_alloc_cf. apply gp_bind. eapply gpost_mono; [|apply (init_path s Hs)].
intros [u s1] (R1 & K1 & L1 & E1). cbn [fst snd] in *.
specialize (E1 c Hc).
assert (G1 : reg s1 c = reg s c) by (unfold reg; rewrite R1; reflexivity).
assert (Hl1 : (Z.to_nat c < length (st_regions s1))%nat) by (rewrite R1, Hlr; lia).
assert (Hlc1 : (Z.to_nat c < length (st_cache s1))%nat) by (rewrite L1; lia).
assert (Hn1 : 1 <= pc_max (cache s1 c) / 2) by (rewrite E1; cbn [pc_max]; apply Z.div_le_lower_bound; lia).
apply gp_bind. eapply gpost_mono; [|exact (refill_cf_path c s1 Hc Hl1 Hlc1 Hn1)].
intros [u2 s2] (K2 & H2). cbn [fst snd] in *.
apply gp_bind. apply gp_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s2 c)) as [|x l] eqn:Ep2; cbn [fst snd].
- apply gp_ret. cbn [fst snd]. intros _. destruct (H2 ltac:(first [exact Ep2 | reflexivity])) as (EX & CF).
split; [congruence|]. split; [exact EX|].
unfold cfull_cf, cfc in *. rewrite E1, G1 in CF. cbn [pc_max pc_chunks] in CF. exact CF.
- apply gp_bind. apply gp_set_pc. cbn [fst snd]. apply gp_ret. cbn [fst snd]. intros E. discriminate E.
Qed.

Lemma sec_alloc_path : forall n s, gpost (sec_alloc n s) (fun r => exists beg, fst r = Some beg /\ beg <> PNull).
Proof.
intros n s. unfold sec_alloc. cbn [fst snd]. apply gp_bind. apply gp_askz. intros z _ Hpz.
cbn [progz] in Hpz. apply Z.eqb_eq in Hpz. subst z. cbn [fst snd].
change (1 =? 0) with false. cbn [fst snd].
apply gp_bind. apply gp_get. cbn [fst snd].
apply gp_bind. apply gp_mcheck. intros _. cbn [fst snd].
apply gp_bind. apply gp_put. cbn [fst snd].
apply gp_bind. eapply gpost_mono; [|apply gpost_true]. intros [u s3] _. cbn [fst snd].
apply gp_bind. apply gp_modify. cbn [fst snd]. apply gp_ret. cbn [fst snd].
eexists. split; [reflexivity | discriminate].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. malloc_cf.                                                                  *)
Lemma malloc_cf_gpost : forall n tr S, shape_cf S ->
gpost (malloc_cf n tr S) (fun r => fst r = PNull ->
blocks (snd r) = blocks S /\ st_chunks (snd r) = st_chunks S /\ from_primary n = true /\
exh_mem_cf (snd r) (chunk_class n) = true /\ cfull_cf S (chunk_class n)).
Proof.
intros n tr S Hs. unfold malloc_cf. apply gp_bind. apply gp_tick. cbn [fst snd].
apply gp_bind. apply gp_mcheck. intros _. cbn [fst snd].
assert (Hs0 : shape_cf (set_nev (st_nev S + 1) S)) by exact Hs.
destruct (from_primary n) eqn:Fp; cbn [fst snd].
- pose proof (chunk_class_ok n Fp) as Hc.
apply gp_bind. apply gp_bind.
eapply gpost_mono; [|exact (cache_alloc_cf_path (chunk_class n) _ ltac:(lia) Hs0)].
intros [o s1] Ho. cbn [fst snd] in *. apply gp_ret. cbn [fst snd].
destruct o as [off|]; cbn [fst snd].
+ apply gp_bind. eapply gpost_mono; [|apply gpost_true]. intros [u s2] _. cbn [fst snd].
apply gp_bind. eapply gpost_mono; [|apply gpost_true]. intros [u3 s3] _. cbn [fst snd].
apply gp_bind. apply gp_modify. cbn [fst snd]. apply gp_ret. cbn [fst snd].
intros E. cbv [ck_user padd ck_beg] in E. discriminate E.
+ apply gp_ret. cbn [fst snd]. intros _. destruct (Ho eq_refl) as (K1 & EX & CF).
split; [unfold blocks; rewrite K1; reflexivity|]. split; [exact K1|]. split; [first [reflexivity | exact Fp]|].
split; [exact EX | exact CF].
- apply gp_bind. eapply gpost_mono; [|apply sec_alloc_path]. intros [ob s1] (beg & Hob & Hb).
cbn [fst snd] in Hob. subst ob. cbn [fst snd].
apply gp_bind. eapply gpost_mono; [|apply gpost_true]. intros [u s2] _. cbn [fst snd].
apply gp_bind. eapply gpost_mono; [|apply gpost_true]. intros [u3 s3] _. cbn [fst snd].
apply gp_bind. apply gp_modify. cbn [fst snd]. apply gp_ret. cbn [fst snd].
intros E. destruct beg as [|off|r off|cid pos]; try (exfalso; exact (Hb eq_refl));
cbv [ck_user padd ck_beg] in E; discriminate E.
Qed.

(* A PNull path with every answer granted is the class-full refusal: no block and no
   chunk is added, the request is primary, its class's exhausted flag is set, and the
   class was full at the start state (the arm's own test failed). *)
Theorem malloc_cf_null_path_full : forall n tr S t S', shape_cf S ->
apath (malloc_cf n tr S) t (PNull, S') -> gflag t = true ->
blocks S' = blocks S /\ st_chunks S' = st_chunks S /\ from_primary n = true /\
exh_mem_cf S' (chunk_class n) = true /\ cfull_cf S (chunk_class n).
Proof.
intros n tr S t S' Hs Hp Hg. pose proof (malloc_cf_gpost n tr S Hs t (PNull, S') Hp Hg) as H.
cbv beta in H. exact (H eq_refl).
Qed.

Theorem malloc_cf_null_path : forall n tr S t S', shape_cf S ->
apath (malloc_cf n tr S) t (PNull, S') -> gflag t = true ->
blocks S' = blocks S /\ st_chunks S' = st_chunks S /\ from_primary n = true /\ exh_mem_cf S' (chunk_class n) = true.
Proof.
intros n tr S t S' Hs Hp Hg.
destruct (malloc_cf_null_path_full n tr S t S' Hs Hp Hg) as (A & B & C & D & _).
exact (conj A (conj B (conj C D))).
Qed.

(* Any PNull path: either some answer was refused, or it is the class-full refusal. *)
Theorem ml_malloc_ns_cf : forall n tr S t r, shape_cf S ->
apath (malloc_cf n tr S) t r -> fst r = PNull ->
gflag t = false \/ (from_primary n = true /\ exh_mem_cf (snd r) (chunk_class n) = true).
Proof.
intros n tr S t r Hs Hp Hnull. destruct (gflag t) eqn:Hg; [right | left; reflexivity].
pose proof (malloc_cf_gpost n tr S Hs t r Hp Hg) as H. cbv beta in H.
destruct (H Hnull) as (_ & _ & A & B & _). exact (conj A B).
Qed.

(* With room, an all-granted path returns a block. *)
Theorem malloc_cf_success_of_room : forall n tr S t r, shape_cf S ->
apath (malloc_cf n tr S) t r -> gflag t = true -> room_cf n S -> fst r <> PNull.
Proof.
intros n tr S t r Hs Hp Hg Hroom Hnull. destruct r as [p S']. cbn [fst] in Hnull. subst p.
destruct (malloc_cf_null_path_full n tr S t S' Hs Hp Hg) as (_ & _ & Fp & _ & CF).
unfold cfull_cf, cfc, arm_full in CF. destruct CF as (N24 & Hpc & Hlt & Hm & Hover).
unfold room_cf, room_at, arm_fits, cf_need in Hroom.
destruct Hroom as [Hf | [H24 | [Hpc' | [Hneed | [Hfit | Hfit]]]]].
- congruence.
- contradiction.
- contradiction.
- lia.
- lia.
- lia.
Qed.

End PATH.

(* ---------------------------------------------------------------------------- *)
(* 5. The start-state premises from the cf invariant.                            *)
Section FROMWF.
Context {cp : CfParams}.

Lemma shape_cf_of_WfP_cf : forall U pp cc bb S, WfP_cf U pp cc bb S -> shape_cf S.
Proof.
intros U pp cc bb S W. split; [exact (wfc_len_regions _ _ _ _ _ W)|]. split; [exact (wfc_len_cache _ _ _ _ _ W)|].
intros Hi c Hc. pose proof (wrc_cache _ _ _ _ _ _ (wfc_classes _ _ _ _ _ W c Hc)) as H.
rewrite Hi in H. destruct H as [H _]. exact H.
Qed.

(* Room in the form a caller holds: the class's next user map fits under kFreeArrayOffset. *)
Lemma room_cf_of_fit : forall U pp cc bb n S, WfP_cf U pp cc bb S ->
rg_mapped_user (reg S (chunk_class n)) + kUserMapSize <= kFreeArrayOffset -> room_cf n S.
Proof.
intros U pp cc bb n S W Hfit. unfold room_cf. destruct (from_primary n) eqn:Fp; [right | left; reflexivity].
pose proof (chunk_class_ok n Fp) as Hc. set (c := chunk_class n) in *.
pose proof (class_ok c ltac:(lia)) as (Ksz & _ & _ & Kmc & _ & Kmx).
pose proof (wfc_classes _ _ _ _ _ W c ltac:(lia)) as C. unfold wf_class_cf in C.
pose proof (wrc_alloc _ _ _ _ _ _ C) as [A0 A1].
pose proof (fa_len_nonneg _ (wrc_runs _ _ _ _ _ _ C)) as FL.
unfold room_at, arm_fits, cf_need. right; right; right; right.
assert (Hx : rg_alloc_user (reg S c) + (max_cached c / 2 - fa_len (rg_free (reg S c))) * class_size c -
rg_mapped_user (reg S c) <= kUserMapSize).
{ assert ((max_cached c / 2 - fa_len (rg_free (reg S c))) * class_size c <= max_cached c / 2 * class_size c)
by (apply Z.mul_le_mono_nonneg_r; lia).
unfold kUserMapSize, kMaxSize in *. lia. }
pose proof (round_up_le _ kUserMapSize kUserMapSize ltac:(unfold kUserMapSize; lia) Hx
ltac:(apply Z.mod_same; unfold kUserMapSize; lia)) as R.
lia.
Qed.

End FROMWF.
